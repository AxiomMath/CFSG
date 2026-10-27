module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem r3c_conj_mem_map_iff {N : Type} [Group N] (H : Subgroup N) (a y : N) :
    y ∈ H.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * y * a ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have e : a⁻¹ * (MulAut.conj a).toMonoidHom x * a = x := by
      show a⁻¹ * (a * x * a⁻¹) * a = x
      group
    rw [e]
    exact hx
  · intro hy
    refine ⟨a⁻¹ * y * a, hy, ?_⟩
    show a * (a⁻¹ * y * a) * a⁻¹ = y
    group

theorem r3c_mem_sup_mul {N : Type} [Group N] (a b : Subgroup N)
    (hab : ∀ x ∈ a, ∀ y ∈ b, x * y = y * x) {g : N} (hg : g ∈ a ⊔ b) :
    ∃ x ∈ a, ∃ y ∈ b, g = x * y := by
  let T : Subgroup N :=
    { carrier := {g | ∃ x ∈ a, ∃ y ∈ b, g = x * y}
      one_mem' := ⟨1, a.one_mem, 1, b.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x1, hx1, y1, hy1, rfl⟩ ⟨x2, hx2, y2, hy2, rfl⟩
        refine ⟨x1 * x2, a.mul_mem hx1 hx2, y1 * y2, b.mul_mem hy1 hy2, ?_⟩
        have h := hab x2 hx2 y1 hy1
        calc x1 * y1 * (x2 * y2) = x1 * (y1 * x2) * y2 := by simp only [mul_assoc]
          _ = x1 * (x2 * y1) * y2 := by rw [h]
          _ = x1 * x2 * (y1 * y2) := by simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, a.inv_mem hx, y⁻¹, b.inv_mem hy, ?_⟩
        rw [hab x hx y hy, mul_inv_rev] }
  have hT : a ⊔ b ≤ T :=
    sup_le (fun x hx => ⟨x, hx, 1, b.one_mem, by simp⟩)
      (fun y hy => ⟨1, a.one_mem, y, hy, by simp⟩)
  obtain ⟨x, hx, y, hy, hxy⟩ := hT hg
  exact ⟨x, hx, y, hy, hxy⟩

theorem r3c_pow_eq_one_of_isPGroup {N : Type} [Group N] {q : ℕ} {a : Subgroup N}
    (ha : IsPGroup q a) {x : N} (hx : x ∈ a) : ∃ k : ℕ, x ^ q ^ k = 1 := by
  obtain ⟨k, hk⟩ := ha ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem r3c_isPGroup_sup {N : Type} [Group N] {q : ℕ} {a b : Subgroup N}
    (ha : IsPGroup q a) (hb : IsPGroup q b) (hab : ∀ x ∈ a, ∀ y ∈ b, x * y = y * x) :
    IsPGroup q (a ⊔ b : Subgroup N) := by
  intro g
  obtain ⟨x, hx, y, hy, hxy⟩ := r3c_mem_sup_mul a b hab g.2
  obtain ⟨k1, hk1⟩ := r3c_pow_eq_one_of_isPGroup ha hx
  obtain ⟨k2, hk2⟩ := r3c_pow_eq_one_of_isPGroup hb hy
  have hxn : x ^ q ^ (k1 + k2) = 1 := by rw [pow_add, pow_mul, hk1, one_pow]
  have hyn : y ^ q ^ (k1 + k2) = 1 := by rw [add_comm, pow_add, pow_mul, hk2, one_pow]
  have key : (g : N) ^ q ^ (k1 + k2) = 1 := by
    rw [hxy, (show Commute x y from hab x hx y hy).mul_pow, hxn, hyn, mul_one]
  exact ⟨k1 + k2, Subtype.ext (by simpa using key)⟩

theorem r3c_isPGroup_sSup {N : Type} [Group N] {q : ℕ} {ι : Type*} (S : ι → Subgroup N)
    (hS : ∀ i, IsPGroup q (S i))
    (hc : ∀ i j, S i = S j ∨ ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) :
    ∀ ℬ : Set (Subgroup N), ℬ.Finite → ℬ ⊆ Set.range S → IsPGroup q (sSup ℬ : Subgroup N) := by
  intro ℬ hℬ
  refine Set.Finite.induction_on
    (motive := fun (ℬ : Set (Subgroup N)) (_ : ℬ.Finite) =>
      ℬ ⊆ Set.range S → IsPGroup q (sSup ℬ : Subgroup N))
    ℬ hℬ ?_ ?_
  · intro _
    rw [sSup_empty]
    exact IsPGroup.of_bot
  · intro a s has hs ih hsub
    have hs' : s ⊆ Set.range S := (Set.subset_insert a s).trans hsub
    have ha : a ∈ Set.range S := hsub (Set.mem_insert a s)
    obtain ⟨i, rfl⟩ := ha
    have hle : sSup s ≤ Subgroup.centralizer (S i : Set N) := by
      apply sSup_le
      intro B hB z hz
      obtain ⟨j, rfl⟩ := hs' hB
      rcases hc i j with h | h
      · exact absurd (by rw [h]; exact hB) has
      · exact Subgroup.mem_centralizer_iff.mpr (fun x hx => h x hx z hz)
    rw [sSup_insert]
    refine r3c_isPGroup_sup (hS i) (ih hs') ?_
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hle hy) x hx

theorem r3_isPGroup_iSup {N : Type} [Group N] [Finite N] {q : ℕ} {ι : Type*} (S : ι → Subgroup N)
    (hS : ∀ i, IsPGroup q (S i))
    (hc : ∀ i j, S i = S j ∨ ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) :
    IsPGroup q (⨆ i, S i : Subgroup N) := by
  haveI : Finite (Subgroup N) :=
    Finite.of_injective (fun H : Subgroup N => (H : Set N)) SetLike.coe_injective
  rw [← sSup_range]
  exact r3c_isPGroup_sSup S hS hc (Set.range S) (Set.toFinite _) (fun _ h => h)

theorem r3c_inv_mul_mem_normalizer {N : Type} [Group N] (J : Subgroup N) {a b : N}
    (hab : J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom) :
    a⁻¹ * b ∈ Subgroup.normalizer (J : Set N) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hB : h ∈ J ↔ b * h * b⁻¹ ∈ J.map (MulAut.conj b).toMonoidHom := by
    rw [r3c_conj_mem_map_iff]
    have e' : b⁻¹ * (b * h * b⁻¹) * b = h := by group
    rw [e']
  have e : a⁻¹ * b * h * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * h * b⁻¹) * a := by group
  show h ∈ J ↔ a⁻¹ * b * h * (a⁻¹ * b)⁻¹ ∈ J
  rw [e, hB, ← hab, r3c_conj_mem_map_iff]

theorem r3c_conj_mem_orbit {N : Type} [Group N] {S F : Subgroup N} {g : N} (hg : g ∈ F)
    {x : N} (hx : x ∈ ⨆ f : F, S.map (MulAut.conj (f : N)).toMonoidHom) :
    g * x * g⁻¹ ∈ ⨆ f : F, S.map (MulAut.conj (f : N)).toMonoidHom := by
  refine Subgroup.iSup_induction (fun f : F => S.map (MulAut.conj (f : N)).toMonoidHom)
    (C := fun y => g * y * g⁻¹ ∈ ⨆ f : F, S.map (MulAut.conj (f : N)).toMonoidHom) hx ?_ ?_ ?_
  · intro f y hy
    rw [r3c_conj_mem_map_iff] at hy
    refine Subgroup.mem_iSup_of_mem (⟨g * (f : N), F.mul_mem hg f.2⟩ : F) ?_
    rw [r3c_conj_mem_map_iff]
    show (g * (f : N))⁻¹ * (g * y * g⁻¹) * (g * (f : N)) ∈ S
    have e : (g * (f : N))⁻¹ * (g * y * g⁻¹) * (g * (f : N)) = (f : N)⁻¹ * y * (f : N) := by
      group
    rw [e]
    exact hy
  · show g * 1 * g⁻¹ ∈ _
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · intro y z hy hz
    show g * (y * z) * g⁻¹ ∈ _
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact mul_mem hy hz

theorem r3_orbit_two {N : Type} [Group N] [Finite N] {J S F : Subgroup N}
    (hJ : CFSG.IsComponent J) (hSJ : S ≤ J) (hS2 : IsPGroup 2 S)
    (hSF : F ⊓ Subgroup.normalizer (J : Set N) ≤ Subgroup.normalizer (S : Set N)) :
    ∃ T : Subgroup N, S ≤ T ∧ IsPGroup 2 T ∧ F ≤ Subgroup.normalizer (T : Set N) := by
  refine ⟨⨆ f : F, S.map (MulAut.conj (f : N)).toMonoidHom, ?_, ?_, ?_⟩
  · intro s hs
    refine Subgroup.mem_iSup_of_mem (1 : F) ?_
    rw [r3c_conj_mem_map_iff]
    simpa using hs
  · refine r3_isPGroup_iSup (fun f : F => S.map (MulAut.conj (f : N)).toMonoidHom)
      (fun f => IsPGroup.map hS2 (MulAut.conj (f : N)).toMonoidHom) ?_
    intro f f'
    try dsimp only
    have hJf := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (f : N)) hJ
    have hJf' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (f' : N)) hJ
    rcases CFSG.LocalCores.distinct_components_commute hJf hJf' with hJeq | hcomm
    · left
      have hN := r3c_inv_mul_mem_normalizer J hJeq
      have hgS := hSF (Subgroup.mem_inf.mpr ⟨F.mul_mem (F.inv_mem f.2) f'.2, hN⟩)
      rw [Subgroup.mem_normalizer_iff''] at hgS
      ext y
      rw [r3c_conj_mem_map_iff, r3c_conj_mem_map_iff]
      have h1 := hgS ((f : N)⁻¹ * y * (f : N))
      have e : ((f : N)⁻¹ * (f' : N))⁻¹ * ((f : N)⁻¹ * y * (f : N)) * ((f : N)⁻¹ * (f' : N))
          = (f' : N)⁻¹ * y * (f' : N) := by group
      rw [e] at h1
      exact h1
    · right
      intro x hx y hy
      have hxJ := Subgroup.map_mono hSJ hx
      have hyJ := Subgroup.map_mono hSJ hy
      have hcm := Subgroup.commutator_mem_commutator hxJ hyJ
      rw [hcomm, Subgroup.mem_bot] at hcm
      exact commutatorElement_eq_one_iff_mul_comm.mp hcm
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact r3c_conj_mem_orbit (S := S) hg hh
    · intro hh
      have h' := r3c_conj_mem_orbit (S := S) (F.inv_mem hg) hh
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [e] at h'
      exact h'

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3e_mem_map_conj {N : Type} [Group N] (K : Subgroup N) (a x : N) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem r3e_mem_normalizer_of_map_eq {N : Type} [Group N] {K : Subgroup N} {g : N}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set N) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key := r3e_mem_map_conj K g (g * x * g⁻¹)
  rw [h] at key
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e] at key
  exact key.symm

theorem r3_fix_of_odd {N : Type} [Group N] [Finite N]
    (h3 : ∀ J₀ J₁ J₂ : Subgroup N, CFSG.IsComponent J₀ → CFSG.IsComponent J₁ →
      CFSG.IsComponent J₂ → J₀ ≠ J₁ → J₀ ≠ J₂ → J₁ ≠ J₂ → False)
    {g : N} {n : ℕ} (hn : Odd n) (hg : g ^ n = 1) {J : Subgroup N} (hJ : CFSG.IsComponent J) :
    g ∈ Subgroup.normalizer (J : Set N) := by
  have hcomp : ∀ a : N, CFSG.IsComponent (J.map (MulAut.conj a).toMonoidHom) :=
    fun a => CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hJ
  by_cases h1 : J.map (MulAut.conj g).toMonoidHom = J
  · exact r3e_mem_normalizer_of_map_eq h1
  have h2 : J.map (MulAut.conj (g ^ 2)).toMonoidHom = J := by
    by_contra h2
    have h12 : J.map (MulAut.conj (g ^ 2)).toMonoidHom ≠ J.map (MulAut.conj g).toMonoidHom := by
      intro heq
      apply h1
      ext x
      have hx : g * x * g⁻¹ ∈ J.map (MulAut.conj (g ^ 2)).toMonoidHom ↔
          g * x * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := by rw [heq]
      rw [r3e_mem_map_conj, r3e_mem_map_conj] at hx
      have e1 : (g ^ 2)⁻¹ * (g * x * g⁻¹) * g ^ 2 = g⁻¹ * x * g := by group
      have e2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e1, e2] at hx
      rw [r3e_mem_map_conj]
      exact hx
    exact h3 J (J.map (MulAut.conj g).toMonoidHom) (J.map (MulAut.conj (g ^ 2)).toMonoidHom)
      hJ (hcomp g) (hcomp (g ^ 2)) (Ne.symm h1) (Ne.symm h2) (Ne.symm h12)
  have hg2 : g ^ 2 ∈ Subgroup.normalizer (J : Set N) := r3e_mem_normalizer_of_map_eq h2
  obtain ⟨m, rfl⟩ := hn
  have hgm : g ^ (2 * m) * g = 1 := by
    rw [← pow_succ]
    exact hg
  have hinv : (g ^ 2) ^ m = g⁻¹ := by
    rw [← pow_mul]
    exact mul_eq_one_iff_eq_inv.mp hgm
  have hmem : g⁻¹ ∈ Subgroup.normalizer (J : Set N) := by
    rw [← hinv]
    exact pow_mem hg2 m
  exact inv_mem_iff.mp hmem

theorem r3_comm_eq_of_not_centralize {N : Type} [Group N] [Finite N] {J Ū : Subgroup N}
    (hJ : CFSG.IsComponent J) (hŪ : Ū ≤ Subgroup.normalizer (J : Set N))
    (hne : ¬ Ū ≤ Subgroup.centralizer (J : Set N)) : ⁅J, Ū⁆ = J := by
  have hKJ : ⁅J, Ū⁆ ≤ J := by
    rw [Subgroup.commutator_le]
    intro j hj u hu
    have hconjmem : u * j⁻¹ * u⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hŪ hu) j⁻¹).mp (inv_mem hj)
    have e : ⁅j, u⁆ = j * (u * j⁻¹ * u⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hj hconjmem
  have hconj : ∀ x ∈ J, ∀ k ∈ ⁅J, Ū⁆, x * k * x⁻¹ ∈ ⁅J, Ū⁆ := by
    intro x hx
    have hS : ⁅J, Ū⁆ ≤ (⁅J, Ū⁆).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro j hj u hu
      show x * ⁅j, u⁆ * x⁻¹ ∈ ⁅J, Ū⁆
      have e : x * ⁅j, u⁆ * x⁻¹ = ⁅x * j, u⁆ * ⁅x, u⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hx hj) hu)
        (inv_mem (Subgroup.commutator_mem_commutator hx hu))
    intro k hk
    exact hS hk
  have hN : (Subgroup.subgroupOf ⁅J, Ū⁆ J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj g g.2 n hn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ.1 hN with htop | hcen
  · exact le_antisymm hKJ (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    have hcentral : ⁅J, Ū⁆ ≤ Subgroup.centralizer (J : Set N) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hkJ : k ∈ J := hKJ hk
      have hmem : (⟨k, hkJ⟩ : ↥J) ∈ Subgroup.subgroupOf ⁅J, Ū⁆ J :=
        Subgroup.mem_subgroupOf.mpr hk
      have hz := hcen hmem
      rw [Subgroup.mem_center_iff] at hz
      exact congrArg Subtype.val (hz ⟨j, hj⟩)
    have hbot : ⁅⁅J, Ū⁆, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
    have hPP : ⁅J, Ū⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hJ.1.1 hbot
    rw [Subgroup.commutator_comm] at hPP
    exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPP)

theorem r3_exists_comp_of_not_le_centralizer_layer {N : Type} [Group N] [Finite N] {Ū : Subgroup N}
    (h : ¬ Ū ≤ Subgroup.centralizer (CFSG.layer N : Set N)) :
    ∃ J : Subgroup N, CFSG.IsComponent J ∧ ¬ Ū ≤ Subgroup.centralizer (J : Set N) := by
  by_contra hcon
  push Not at hcon
  apply h
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hsub : CFSG.layer N ≤ Subgroup.centralizer {u} := by
    rw [CFSG.layer.eq_sSup]
    apply sSup_le
    intro K hK k hk
    have hu' : u ∈ Subgroup.centralizer (K : Set N) := hcon K hK hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu' k hk)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hx)

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem r3g0_two_dvd_card_of_component {N : Type} [Group N] [Finite N] {J : Subgroup N}
    (hJ : CFSG.IsComponent J) : 2 ∣ Nat.card J := by
  have hsimp := hJ.1.2.1
  have hnonab := hJ.1.2.2
  have h1 : 2 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.two_dvd_card_of_simple_nonabelian hsimp hnonab
  have h2 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥J :=
    Subgroup.index_dvd_card (H := Subgroup.center ↥J)
  exact h1.trans h2

theorem r3_sylow_two_ne_bot {N : Type} [Group N] [Finite N] {J T : Subgroup N}
    (hJ : CFSG.IsComponent J) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T J) : T ≠ ⊥ := by
  intro hTbot
  have hnd : ¬ 2 ∣ T.relIndex J := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
  rw [hTbot, Subgroup.relIndex_bot_left] at hnd
  exact hnd (r3g0_two_dvd_card_of_component hJ)

end CFSG.RankThree.PartTwo.Sec13.F135Last
