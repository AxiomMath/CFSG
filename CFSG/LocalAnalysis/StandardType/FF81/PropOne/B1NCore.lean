module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLift

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne.B1Normal

theorem mulAut_ext_on_gens {B : Type*} [Group B] {S : Set B}
    (hS : Subgroup.closure S = ⊤) {f g : MulAut B} (h : ∀ x ∈ S, f x = g x) : f = g := by
  have hhom : f.toMonoidHom = g.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro x hx
    exact h x hx
  ext x
  exact DFunLike.congr_fun hhom x

theorem mulAut_comm_of_sign_on_gens {W : Type*} [Group W] {S : Set W}
    (hS : Subgroup.closure S = ⊤) {u v : MulAut W}
    (hu : ∀ x ∈ S, u x = x ∨ u x = x⁻¹) (hv : ∀ x ∈ S, v x = x ∨ v x = x⁻¹) :
    u * v = v * u := by
  apply mulAut_ext_on_gens hS
  intro x hx
  rcases hu x hx with h1 | h1 <;> rcases hv x hx with h2 | h2 <;>
    simp [MulAut.mul_apply, h1, h2]

theorem mulAut_mul_self_of_sign_on_gens {W : Type*} [Group W] {S : Set W}
    (hS : Subgroup.closure S = ⊤) {u : MulAut W}
    (hu : ∀ x ∈ S, u x = x ∨ u x = x⁻¹) : u * u = 1 := by
  apply mulAut_ext_on_gens hS
  intro x hx
  rcases hu x hx with h1 | h1 <;> simp [MulAut.mul_apply, h1]

def bG {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} : ↥(GGFF.Bt b z) :=
  ⟨b, GGFF.SettingCore.b_mem_Bt b z⟩

def zsG {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} (i : Fin 3) :
    ↥(GGFF.Bt b z) :=
  ⟨GGFF.zs z i, GGFF.SettingCore.zs_mem_Bt b z i⟩

private def gen4 {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} :
    Fin 4 → ↥(GGFF.Bt b z) := ![bG, zsG 0, zsG 1, zsG 2]

private lemma closure_gens {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} :
    (Subgroup.closure (Set.range (gen4 (b := b) (z := z))) : Subgroup ↥(GGFF.Bt b z)) = ⊤ := by
  have hset : Set.range (gen4 (b := b) (z := z)) =
      ((↑) : ↥(GGFF.Bt b z) → G) ⁻¹'
        ({b, GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [gen4, bG, zsG]
    · intro hx
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext h.symm⟩
      · exact ⟨2, Subtype.ext h.symm⟩
      · exact ⟨3, Subtype.ext h.symm⟩
  rw [hset, GGFF.SettingCore.Bt_eq_closure]
  exact Subgroup.closure_closure_coe_preimage

theorem closure_four_gens {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} :
    Subgroup.closure ({bG, zsG 0, zsG 1, zsG 2} : Set ↥(GGFF.Bt b z)) = ⊤ := by
  have hset : ({bG, zsG 0, zsG 1, zsG 2} : Set ↥(GGFF.Bt b z)) =
      Set.range (gen4 (b := b) (z := z)) := by
    ext x
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [gen4]
  rw [hset]
  exact closure_gens

theorem eq_one_of_eq_inv_of_pow_three {W : Type*} [Group W] {x : W} (h3 : x ^ 3 = 1)
    (h : x = x⁻¹) : x = 1 := by
  have h2 : x * x = 1 := by
    nth_rewrite 2 [h]
    exact mul_inv_cancel x
  calc x = x * (x * x) := by rw [h2, mul_one]
    _ = x ^ 3 := by rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, pow_two]
    _ = 1 := h3

theorem fix_of_fixes_inverts {W : Type*} [CommGroup W]
    (hpow : ∀ x : W, x ^ 3 = 1) {C₀ C₁ : Subgroup W} (hsup : C₀ ⊔ C₁ = ⊤)
    {u : MulAut W}
    (hu₀ : ∀ x ∈ C₀, u x = x) (hu₁ : ∀ x ∈ C₁, u x = x⁻¹) :
    ∀ x : W, u x = x ↔ x ∈ C₀ := by
  intro x
  constructor
  · intro hx
    have hxsup : x ∈ C₀ ⊔ C₁ := by rw [hsup]; exact Subgroup.mem_top x
    obtain ⟨a, ha, c, hc, rfl⟩ := (Subgroup.mem_sup (s := C₀) (t := C₁)).mp hxsup
    have hux : u (a * c) = a * c⁻¹ := by rw [map_mul, hu₀ a ha, hu₁ c hc]
    rw [hux] at hx
    have hcc : c = c⁻¹ := (mul_left_cancel hx).symm
    have hc1 : c = 1 := by
      have h2 : c * c = 1 := by
        nth_rewrite 2 [hcc]
        exact mul_inv_cancel c
      calc c = c * (c * c) := by rw [h2, mul_one]
        _ = c ^ 3 := by rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, pow_two]
        _ = 1 := hpow c
    simpa [hc1] using ha
  · intro hx
    exact hu₀ x hx

theorem inv_of_fixes_inverts {W : Type*} [CommGroup W]
    (hpow : ∀ x : W, x ^ 3 = 1) {C₀ C₁ : Subgroup W} (hsup : C₀ ⊔ C₁ = ⊤)
    {u : MulAut W}
    (hu₀ : ∀ x ∈ C₀, u x = x⁻¹) (hu₁ : ∀ x ∈ C₁, u x = x) :
    ∀ x : W, u x = x⁻¹ ↔ x ∈ C₀ := by
  intro x
  constructor
  · intro hx
    have hxsup : x ∈ C₀ ⊔ C₁ := by rw [hsup]; exact Subgroup.mem_top x
    obtain ⟨a, ha, c, hc, rfl⟩ := (Subgroup.mem_sup (s := C₀) (t := C₁)).mp hxsup
    have hux : u (a * c) = a⁻¹ * c := by rw [map_mul, hu₀ a ha, hu₁ c hc]
    rw [hux] at hx
    have hxinv : (a * c)⁻¹ = a⁻¹ * c⁻¹ := by rw [mul_inv_rev, mul_comm]
    rw [hxinv] at hx
    have hcc : c = c⁻¹ := mul_left_cancel hx
    have hc1 : c = 1 := by
      have h2 : c * c = 1 := by
        nth_rewrite 2 [hcc]
        exact mul_inv_cancel c
      calc c = c * (c * c) := by rw [h2, mul_one]
        _ = c ^ 3 := by rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, pow_two]
        _ = 1 := hpow c
    simpa [hc1] using ha
  · intro hx
    exact hu₀ x hx

theorem map_inv_of_closure {W : Type*} [CommGroup W] {S : Set W} {u : MulAut W}
    (h : ∀ s ∈ S, u s = s⁻¹) :
    ∀ x ∈ Subgroup.closure S, u x = x⁻¹ := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul a c ha hc iha ihc =>
      rw [map_mul, iha, ihc, mul_inv_rev, mul_comm]
  | inv a ha iha =>
      rw [map_inv, iha, inv_inv]

theorem map_fix_of_closure {W : Type*} [CommGroup W] {S : Set W} {u : MulAut W}
    (h : ∀ s ∈ S, u s = s) :
    ∀ x ∈ Subgroup.closure S, u x = x := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul a c ha hc iha ihc => rw [map_mul, iha, ihc]
  | inv a ha iha => rw [map_inv, iha]

theorem isElemAb_Bt {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    CFSG.RankThree.PartTwo.Sec21.FF79.IsElemAb 3 4 (GGFF.Bt b z) := by
  have hs := h.settingCore
  refine ⟨?_, hs.card_Bt⟩
  exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hs.isElemAbelian_Bt

theorem map_kernel_inv_mul {W : Type*} [Group W] {u y : MulAut W} {E : Subgroup W}
    (hcomm : y * u = u * y) (hker : ∀ x : W, x⁻¹ * u x = 1 ↔ x ∈ E) :
    Subgroup.map y E = E := by
  have hyinv : y⁻¹ * u = u * y⁻¹ := (show Commute y u from hcomm).inv_left
  have hu_y : ∀ x : W, u (y x) = y (u x) := by
    intro x
    rw [← MulAut.mul_apply W u y x, ← hcomm, MulAut.mul_apply]
  have hu_yinv : ∀ x : W, u (y⁻¹ x) = y⁻¹ (u x) := by
    intro x
    rw [← MulAut.mul_apply W u y⁻¹ x, ← hyinv, MulAut.mul_apply]
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨e, he, rfl⟩ := hz
    rw [← hker]
    calc
      (y e)⁻¹ * u (y e) = y (e⁻¹) * y (u e) := by rw [map_inv, hu_y]
      _ = y (e⁻¹ * u e) := by rw [← map_mul]
      _ = 1 := by rw [(hker e).mpr he, map_one]
  · intro z hz
    rw [Subgroup.mem_map]
    refine ⟨y⁻¹ z, ?_, by simp⟩
    rw [← hker]
    calc
      (y⁻¹ z)⁻¹ * u (y⁻¹ z) = y⁻¹ (z⁻¹) * y⁻¹ (u z) := by
        rw [map_inv, hu_yinv]
      _ = y⁻¹ (z⁻¹ * u z) := by rw [← map_mul]
      _ = 1 := by rw [(hker z).mpr hz, map_one]

theorem map_kernel_mul {W : Type*} [Group W] {u y : MulAut W} {E : Subgroup W}
    (hcomm : y * u = u * y) (hker : ∀ x : W, x * u x = 1 ↔ x ∈ E) :
    Subgroup.map y E = E := by
  have hyinv : y⁻¹ * u = u * y⁻¹ := (show Commute y u from hcomm).inv_left
  have hu_y : ∀ x : W, u (y x) = y (u x) := by
    intro x
    rw [← MulAut.mul_apply W u y x, ← hcomm, MulAut.mul_apply]
  have hu_yinv : ∀ x : W, u (y⁻¹ x) = y⁻¹ (u x) := by
    intro x
    rw [← MulAut.mul_apply W u y⁻¹ x, ← hyinv, MulAut.mul_apply]
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨e, he, rfl⟩ := hz
    rw [← hker]
    calc
      y e * u (y e) = y e * y (u e) := by rw [hu_y]
      _ = y (e * u e) := by rw [← map_mul]
      _ = 1 := by rw [(hker e).mpr he, map_one]
  · intro z hz
    rw [Subgroup.mem_map]
    refine ⟨y⁻¹ z, ?_, by simp⟩
    rw [← hker]
    calc
      y⁻¹ z * u (y⁻¹ z) = y⁻¹ z * y⁻¹ (u z) := by rw [hu_yinv]
      _ = y⁻¹ (z * u z) := by rw [← map_mul]
      _ = 1 := by rw [(hker z).mpr hz, map_one]

theorem BB_eq_Bt {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} :
    CFSG.RankThree.PartTwo.Sec21.FF81.Lift.BB b
      (GGFF.zs z 0) (GGFF.zs z 1) (GGFF.zs z 2) = GGFF.Bt b z := by
  rw [GGFF.SettingCore.Bt_eq_closure]

theorem normHom_apply_coe {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}
    (g : G) (hg : g ∈ nB b z) (a : ↥(GGFF.Bt b z)) :
    ((((GGFF.Bt b z).normalizerMonoidHom ⟨g, hg⟩) a : ↥(GGFF.Bt b z)) : G) =
      g * (a : G) * g⁻¹ := by
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem exists_move {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∃ σ : MulAut ↥(GGFF.Bt b z), σ ∈ (GGFF.Bt b z).normalizerMonoidHom.range ∧
      σ bG ∉ Subgroup.zpowers bG := by
  have hnot : ¬ nB b z ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    simpa [nB] using h.facts.not_nor
  obtain ⟨m, hmN, hmnot⟩ := Set.not_subset.mp hnot
  refine ⟨(GGFF.Bt b z).normalizerMonoidHom ⟨m, hmN⟩, ⟨⟨m, hmN⟩, rfl⟩, ?_⟩
  intro hmem
  apply hmnot
  have hmapzp : (Subgroup.zpowers (bG : ↥(GGFF.Bt b z))).map (GGFF.Bt b z).subtype =
      Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hmm : m * b * m⁻¹ ∈ Subgroup.zpowers b := by
    rw [← hmapzp]
    have hval : (((GGFF.Bt b z).normalizerMonoidHom ⟨m, hmN⟩ bG : ↥(GGFF.Bt b z)) : G) =
        m * b * m⁻¹ := normHom_apply_coe m hmN bG
    have := Subgroup.mem_map_of_mem (GGFF.Bt b z).subtype hmem
    simpa [hval] using this
  apply GGFF.mem_nor_of_conj_mem
  intro x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hx' : m * x * m⁻¹ = (m * b * m⁻¹) ^ k := by rw [← hk, conj_zpow]
  rw [hx']
  exact Subgroup.zpow_mem (Subgroup.zpowers b) hmm k

end CFSG.StandardType.FF81.PropOne.B1Normal

end
