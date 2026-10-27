module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Quasithin.Vol2.Ch5Sec1Hall
import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.WBN

open CFSG.Open

variable {Y : Type} [Group Y]

@[expose] def InvertsByWeyl (M₁ M₂ : Subgroup Y) (m : ℕ) : Prop :=
  ∀ E : Subgroup Y, E ≤ M₁ ⊓ M₂ → (∀ e ∈ E, e ^ m = 1) →
    ∃ H : Subgroup Y, E ≤ H ∧ H ≤ M₁ ⊓ M₂ ∧ ∃ l : List Y,
      (∀ x ∈ l, (x ∈ M₁ ∨ x ∈ M₂) ∧ x ∈ Subgroup.normalizer (H : Set Y)) ∧
        ∀ e ∈ E, l.prod * e * l.prod⁻¹ = e⁻¹

theorem InvertsByWeyl.swap {M₁ M₂ : Subgroup Y} {m : ℕ} (h : InvertsByWeyl M₁ M₂ m) :
    InvertsByWeyl M₂ M₁ m := by
  intro E hE hm
  obtain ⟨H, hEH, hH, l, hl, hinv⟩ := h E (by rwa [inf_comm]) hm
  exact ⟨H, hEH, by rwa [inf_comm], l, fun x hx => by
    rcases hl x hx with ⟨hmem, hnorm⟩
    exact ⟨hmem.symm, hnorm⟩, hinv⟩

theorem InvertsByWeyl.map {Y' : Type} [Group Y'] (φ : Y ≃* Y') {M₁ M₂ : Subgroup Y} {m : ℕ}
    (h : InvertsByWeyl M₁ M₂ m) :
    InvertsByWeyl (M₁.map φ.toMonoidHom) (M₂.map φ.toMonoidHom) m := by
  intro E' hE' hmE'
  let E : Subgroup Y := E'.comap φ.toMonoidHom
  have hE : E ≤ M₁ ⊓ M₂ := by
    intro e he
    have hφe : φ e ∈ E' := he
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp (hE' hφe).1
      rwa [← φ.injective hme]
    · obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp (hE' hφe).2
      rwa [← φ.injective hme]
  have hmE : ∀ e ∈ E, e ^ m = 1 := by
    intro e he
    apply φ.injective
    rw [map_pow, map_one]
    exact hmE' (φ e) he
  obtain ⟨H, hEH, hHM, l, hl, hinv⟩ := h E hE hmE
  have hE'map : E.map φ.toMonoidHom = E' :=
    Subgroup.map_comap_eq_self_of_surjective φ.surjective E'
  refine ⟨H.map φ.toMonoidHom, ?_, ?_, l.map φ.toMonoidHom, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (by rwa [← hE'map] at hx)
    exact ⟨e, hEH he, rfl⟩
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ (hHM hh).1,
      Subgroup.mem_map_of_mem _ (hHM hh).2⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hymem, hynorm⟩ := hl y hy
    refine ⟨hymem.imp (Subgroup.mem_map_of_mem _) (Subgroup.mem_map_of_mem _), ?_⟩
    exact Subgroup.le_normalizer_map φ.toMonoidHom (Subgroup.mem_map_of_mem _ hynorm)
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (by rwa [← hE'map] at he')
    have h := hinv e he
    calc (l.map φ.toMonoidHom).prod * φ e * (l.map φ.toMonoidHom).prod⁻¹
        = φ (l.prod * e * l.prod⁻¹) := by
          rw [← map_list_prod, map_mul, map_mul, map_inv]
          simp
      _ = φ e⁻¹ := by rw [h]
      _ = (φ e)⁻¹ := map_inv _ _

theorem InvertsByWeyl.map_injective {Y' : Type} [Group Y'] (f : Y →* Y')
    (hf : Function.Injective f) {M₁ M₂ : Subgroup Y} {m : ℕ} (h : InvertsByWeyl M₁ M₂ m) :
    InvertsByWeyl (M₁.map f) (M₂.map f) m := by
  intro E' hE' hmE'
  let E : Subgroup Y := E'.comap f
  have hE'le : E' ≤ f.range := fun x hx => Subgroup.map_le_range f M₁ (hE' hx).1
  have hE'map : E.map f = E' := Subgroup.map_comap_eq_self hE'le
  have hE : E ≤ M₁ ⊓ M₂ := by
    intro e he
    have hfe : f e ∈ E' := he
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp (hE' hfe).1
      rwa [← hf hme]
    · obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp (hE' hfe).2
      rwa [← hf hme]
  have hmE : ∀ e ∈ E, e ^ m = 1 := by
    intro e he
    apply hf
    rw [map_pow, map_one]
    exact hmE' (f e) he
  obtain ⟨H, hEH, hHM, l, hl, hinv⟩ := h E hE hmE
  refine ⟨H.map f, ?_, ?_, l.map f, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (by rwa [← hE'map] at hx)
    exact ⟨e, hEH he, rfl⟩
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ (hHM hh).1,
      Subgroup.mem_map_of_mem _ (hHM hh).2⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hymem, hynorm⟩ := hl y hy
    refine ⟨hymem.imp (Subgroup.mem_map_of_mem _) (Subgroup.mem_map_of_mem _), ?_⟩
    exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem _ hynorm)
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (by rwa [← hE'map] at he')
    have h := hinv e he
    calc (l.map f).prod * f e * (l.map f).prod⁻¹
        = f (l.prod * e * l.prod⁻¹) := by
          rw [← map_list_prod, map_mul, map_mul, map_inv]
      _ = f e⁻¹ := by rw [h]
      _ = (f e)⁻¹ := map_inv _ _

private theorem exists_conj_pair_of_isYAmalgamPair {C : Type} [Group C] [Finite C]
    {U P₀ P₁ : Subgroup C} (hP : IsYAmalgamPair U P₀ P₁) {Y' : Type} [Group Y']
    (e : Y' ≃* C) {T M₁ M₂ : Subgroup Y'} (hY : IsYAmalgamPair T M₁ M₂) :
    ∃ c : C, T.map e.toMonoidHom = U.map (MulAut.conj c).toMonoidHom ∧
      ((M₁.map e.toMonoidHom = P₀.map (MulAut.conj c).toMonoidHom ∧
          M₂.map e.toMonoidHom = P₁.map (MulAut.conj c).toMonoidHom) ∨
        (M₁.map e.toMonoidHom = P₁.map (MulAut.conj c).toMonoidHom ∧
          M₂.map e.toMonoidHom = P₀.map (MulAut.conj c).toMonoidHom)) := by
  have h' := IsYAmalgamPair.map e hY
  obtain ⟨c, -, hc⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj
    (S := U) (S' := T.map e.toMonoidHom) (H := ⊤) hP.1 h'.1
  let φ : C ≃* C := (MulAut.conj c).symm
  have h'' := IsYAmalgamPair.map φ h'
  have hU : (T.map e.toMonoidHom).map φ.toMonoidHom = U := by
    rw [hc]
    exact CFSG.Quasithin.H13.Sec53F.Yam.map_symm_map (MulAut.conj c) U
  rw [hU] at h''
  obtain ⟨hM1, hN1⟩ := (h''.2.2 ((M₁.map e.toMonoidHom).map φ.toMonoidHom)).2 (Or.inl rfl)
  obtain ⟨hM2, hN2⟩ := (h''.2.2 ((M₂.map e.toMonoidHom).map φ.toMonoidHom)).2 (Or.inr rfl)
  have hne : (M₁.map e.toMonoidHom).map φ.toMonoidHom ≠
      (M₂.map e.toMonoidHom).map φ.toMonoidHom := h''.2.1
  have hEqOr : ∀ X : Subgroup C, IsMaximalTwoLocal X →
      Subgroup.normalizer (U : Set C) ≤ X → X = P₀ ∨ X = P₁ :=
    fun X hX hN => (hP.2.2 X).1 ⟨hX, hN⟩
  have key : ∀ M X : Subgroup C, M.map φ.toMonoidHom = X →
      M = X.map (MulAut.conj c).toMonoidHom := by
    intro M X hX
    rw [← hX]
    exact (CFSG.Quasithin.H13.Sec53F.Yam.map_symm_map φ M).symm
  refine ⟨c, hc, ?_⟩
  rcases hEqOr _ hM1 hN1 with a | a <;> rcases hEqOr _ hM2 hN2 with b | b
  · exact absurd (a.trans b.symm) hne
  · exact Or.inl ⟨key _ _ a, key _ _ b⟩
  · exact Or.inr ⟨key _ _ a, key _ _ b⟩
  · exact absurd (a.trans b.symm) hne

theorem InvertsByWeyl.of_isYAmalgamPair {C : Type} [Group C] [Finite C] {U P₀ P₁ : Subgroup C}
    (hP : IsYAmalgamPair U P₀ P₁) {m : ℕ} (h : InvertsByWeyl P₀ P₁ m)
    {Y' : Type} [Group Y'] (e : Y' ≃* C) {T M₁ M₂ : Subgroup Y'} (hY : IsYAmalgamPair T M₁ M₂) :
    InvertsByWeyl M₁ M₂ m := by
  obtain ⟨c, -, hM⟩ := exists_conj_pair_of_isYAmalgamPair hP e hY
  have hc : InvertsByWeyl (P₀.map (MulAut.conj c).toMonoidHom)
      (P₁.map (MulAut.conj c).toMonoidHom) m := InvertsByWeyl.map _ h
  have h' : InvertsByWeyl (M₁.map e.toMonoidHom) (M₂.map e.toMonoidHom) m := by
    rcases hM with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hc
    · rw [h1, h2]; exact hc.swap
  have := InvertsByWeyl.map e.symm h'
  simpa [Subgroup.map_map, MulEquiv.toMonoidHom_symm_comp_toMonoidHom,
    Subgroup.map_id] using this


theorem InvertsByWeyl.of_yamStd {C : Type} [Group C] [Finite C] {U P₀ P₁ : Subgroup C}
    (S : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁) {m : ℕ} (h : InvertsByWeyl P₀ P₁ m)
    {Y' : Type} [Group Y'] (e : Y' ≃* C) {T M₁ M₂ : Subgroup Y'} (hY : IsYAmalgamPair T M₁ M₂) :
    InvertsByWeyl M₁ M₂ m :=
  InvertsByWeyl.of_isYAmalgamPair S.isYAmalgamPair h e hY

@[expose] def AllInvertsByWeyl (P : ∀ (Y : Type) [Group Y], Prop) (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y], P Y → ∀ T M₁ M₂ : Subgroup Y, IsYAmalgamPair T M₁ M₂ →
    InvertsByWeyl M₁ M₂ m

private theorem torus_odd_card [Finite Y] {E : Subgroup Y} {m : ℕ} (hm : Odd m)
    (hmE : ∀ e ∈ E, e ^ m = 1) : Odd (Nat.card E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Nat.not_even_iff_odd.mp ?_
  intro heven
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (even_iff_two_dvd.mp heven)
  have hxpow : x ^ m = 1 := Subtype.ext (hmE (x : Y) x.2)
  have hdvd : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxpow
  rw [hx] at hdvd
  exact hm.not_two_dvd_nat hdvd

private theorem of_torus_exists_conj [Finite Y] {U H P₀ P₁ E : Subgroup Y}
    (hU : IsPGroup 2 U) (hUn : (U.subgroupOf (P₀ ⊓ P₁)).Normal)
    (hUH : U ⊔ H = P₀ ⊓ P₁) (hH : Odd (Nat.card H))
    (hE : E ≤ P₀ ⊓ P₁) (hEodd : Odd (Nat.card E)) (hEU : E ⊓ U = ⊥) :
    ∃ x ∈ U, E = ((E ⊔ U) ⊓ H).map (MulAut.conj x).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup Y := P₀ ⊓ P₁
  have hEB : E ≤ B := hE
  have hUB : U ≤ B := by
    change U ≤ P₀ ⊓ P₁
    rw [← hUH]
    exact le_sup_left
  have hHB : H ≤ B := by
    change H ≤ P₀ ⊓ P₁
    rw [← hUH]
    exact le_sup_right
  have hBnorm : B ≤ Subgroup.normalizer (U : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hUn
  have hEN : E ≤ Subgroup.normalizer (U : Set Y) := hEB.trans hBnorm
  have hHU : H ⊓ U = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨a, ha⟩ := hU.exists_card_eq
    rw [ha]
    exact (Nat.coprime_two_left.mpr hH).symm.pow_right a
  let K : Subgroup Y := E ⊔ U
  have hKleB : K ≤ B := sup_le hEB hUB
  have hKN : K ≤ Subgroup.normalizer (U : Set Y) := hKleB.trans hBnorm
  have hUKrel : U.relIndex K = Nat.card E := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := E) (K := U) hEN).2
    rw [show E ⊔ U = K from rfl, hEU, Subgroup.relIndex_bot_left] at h
    exact h
  have hHnormU : H ≤ Subgroup.normalizer (U : Set Y) := hHB.trans hBnorm
  have hKleHU : K ≤ H ⊔ U := by
    rw [sup_comm, hUH]
    exact hKleB
  have hKHU : U ⊔ (K ⊓ H) = K := by
    rw [sup_comm, Subgroup.inf_sup_assoc_of_le (H := H) (K := K) (N := U) hHnormU le_sup_right,
      inf_eq_left.mpr hKleHU]
  have hKHUbot : (K ⊓ H) ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf inf_le_right le_rfl).trans_eq hHU
  obtain ⟨x, hxU, hxconj⟩ :=
    CFSG.Quasithin.H13.exists_mem_conj_of_complements (G := Y) (P := U) (Y := K)
      (E₁ := K ⊓ H) (E₂ := E) (le_sup_right : U ≤ K) hKN hU (by rw [hUKrel]; exact hEodd)
      inf_le_left (by rw [inf_comm]; exact hKHUbot) hKHU le_sup_left
      (by rw [inf_comm]; exact hEU) (by rw [show K = E ⊔ U from rfl]; exact sup_comm U E)
  exact ⟨x, hxU, by simpa [K] using hxconj⟩

private theorem torus_conj_list_of_mem {U H P₀ P₁ E : Subgroup Y} {x : Y}
    (hUB : U ≤ P₀ ⊓ P₁) (hHB : H ≤ P₀ ⊓ P₁) (hxU : x ∈ U)
    (hxconj : E = ((E ⊔ U) ⊓ H).map (MulAut.conj x).toMonoidHom)
    (l₀ : List Y)
    (hl₀ : ∀ y ∈ l₀, (y ∈ P₀ ∨ y ∈ P₁) ∧ y ∈ Subgroup.normalizer (H : Set Y)) :
    ∃ (H' : Subgroup Y) (l : List Y), E ≤ H' ∧ H' ≤ P₀ ⊓ P₁ ∧
      (∀ y ∈ l, (y ∈ P₀ ∨ y ∈ P₁) ∧ y ∈ Subgroup.normalizer (H' : Set Y)) ∧
      l.prod = x * l₀.prod * x⁻¹ := by
  let B : Subgroup Y := P₀ ⊓ P₁
  let g : Y := x⁻¹
  have hgB : g ∈ B := B.inv_mem (hUB hxU)
  have hEH' : E ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hxconj]
    simpa [g] using (Subgroup.map_mono (inf_le_right : (E ⊔ U) ⊓ H ≤ H))
  let l : List Y := l₀.map (MulAut.conj g⁻¹).toMonoidHom
  have hlprod : l.prod = x * l₀.prod * x⁻¹ := by
    rw [show l.prod = (MulAut.conj g⁻¹).toMonoidHom l₀.prod from
      (map_list_prod (MulAut.conj g⁻¹).toMonoidHom l₀).symm]
    simp [g]
  refine ⟨H.map (MulAut.conj g⁻¹).toMonoidHom, l, hEH', ?_, ?_, hlprod⟩
  · rintro _ ⟨h, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact B.mul_mem (B.mul_mem (B.inv_mem hgB) (hHB hh)) hgB
  · intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hy₀P, hy₀N⟩ := hl₀ y₀ hy₀
    have hg₀ : g ∈ P₀ := (Subgroup.mem_inf.mp hgB).1
    have hg₁ : g ∈ P₁ := (Subgroup.mem_inf.mp hgB).2
    refine ⟨?_, Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hy₀N)⟩
    rcases hy₀P with h | h
    · left
      have hmem : g⁻¹ * y₀ * g ∈ P₀ :=
        P₀.mul_mem (P₀.mul_mem (P₀.inv_mem hg₀) h) hg₀
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmem
    · right
      have hmem : g⁻¹ * y₀ * g ∈ P₁ :=
        P₁.mul_mem (P₁.mul_mem (P₁.inv_mem hg₁) h) hg₁
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmem

private theorem torus_mem_of_mem_closure {X : Set Y} {H P₀ P₁ : Subgroup Y}
    (hX : ∀ x ∈ X, (x ∈ P₀ ∨ x ∈ P₁) ∧ x ∈ Subgroup.normalizer (H : Set Y))
    {y : Y} (hy : y ∈ X ∪ X⁻¹) :
    (y ∈ P₀ ∨ y ∈ P₁) ∧ y ∈ Subgroup.normalizer (H : Set Y) := by
  rcases hy with hyX | hyX
  · exact hX y hyX
  · obtain ⟨hyP, hyN⟩ := hX y⁻¹ (Set.mem_inv.mp hyX)
    refine ⟨?_, ?_⟩
    · rcases hyP with h | h
      · exact Or.inl (by simpa using P₀.inv_mem h)
      · exact Or.inr (by simpa using P₁.inv_mem h)
    · simpa using Subgroup.inv_mem (Subgroup.normalizer (H : Set Y)) hyN

theorem InvertsByWeyl.of_torus_closure [Finite Y] {U H P₀ P₁ : Subgroup Y} {m : ℕ} (hm : Odd m)
    (hU : IsPGroup 2 U) (hUn : (U.subgroupOf (P₀ ⊓ P₁)).Normal) (hUH : U ⊔ H = P₀ ⊓ P₁)
    (hH : Odd (Nat.card H)) {X : Set Y}
    (hX : ∀ x ∈ X, (x ∈ P₀ ∨ x ∈ P₁) ∧ x ∈ Subgroup.normalizer (H : Set Y))
    {w : Y} (hw : w ∈ Subgroup.closure X) (hinv : ∀ x ∈ H, x ^ m = 1 → w * x * w⁻¹ = x⁻¹) :
    InvertsByWeyl P₀ P₁ m := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hE hmE
  let B : Subgroup Y := P₀ ⊓ P₁
  have hUB : U ≤ B := by
    change U ≤ P₀ ⊓ P₁
    rw [← hUH]
    exact le_sup_left
  have hHB : H ≤ B := by
    change H ≤ P₀ ⊓ P₁
    rw [← hUH]
    exact le_sup_right
  have hEodd : Odd (Nat.card E) := torus_odd_card hm hmE
  have hEU : E ⊓ U = ⊥ := by
    rw [inf_comm]
    exact CFSG.Quasithin.H13.inf_eq_bot_of_odd_of_isPGroup hU hEodd
  obtain ⟨x, hxU, hxconj⟩ := of_torus_exists_conj hU hUn hUH hH hE hEodd hEU
  have hw' : w ∈ (Subgroup.closure X).toSubmonoid := hw
  rw [Subgroup.closure_toSubmonoid] at hw'
  obtain ⟨l₀, hl₀, hprod⟩ := Submonoid.exists_list_of_mem_closure hw'
  have hl₀' : ∀ y ∈ l₀, (y ∈ P₀ ∨ y ∈ P₁) ∧
      y ∈ Subgroup.normalizer (H : Set Y) :=
    fun y hy => torus_mem_of_mem_closure hX (hl₀ y hy)
  obtain ⟨H', l, hEH', hH'B, hl, hlprod⟩ :=
    torus_conj_list_of_mem hUB hHB hxU hxconj l₀ hl₀'
  refine ⟨H', hEH', hH'B, l, hl, ?_⟩
  intro e he
  have hlw : l.prod = x * w * x⁻¹ := by rw [hlprod, hprod]
  have heMap : e ∈ ((E ⊔ U) ⊓ H).map (MulAut.conj x).toMonoidHom := by
    rw [← hxconj]
    exact he
  obtain ⟨h, hh, hhe⟩ := Subgroup.mem_map.mp heMap
  have hxinv : x⁻¹ * e * x = h := by
    rw [← hhe]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hhm : h ^ m = 1 := by
    rw [← hxinv]
    simpa [hmE e he] using (conj_pow (a := x⁻¹) (b := e) (i := m))
  have hA := hinv h (Subgroup.mem_inf.mp hh).2 hhm
  have heq : x * h * x⁻¹ = e := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hhe
  have hgoal : l.prod * e * l.prod⁻¹ = x * (w * h * w⁻¹) * x⁻¹ := by
    rw [hlw, ← hxinv]
    group
  rw [hgoal, hA, ← heq]
  group

theorem InvertsByWeyl.of_torus [Finite Y] {U H P₀ P₁ : Subgroup Y} {m : ℕ} (hm : Odd m)
    (hU : IsPGroup 2 U) (hUn : (U.subgroupOf (P₀ ⊓ P₁)).Normal) (hUH : U ⊔ H = P₀ ⊓ P₁)
    (hH : Odd (Nat.card H)) {n₀ n₁ : Y} (h₀ : n₀ ∈ P₀) (h₁ : n₁ ∈ P₁)
    (hn₀ : n₀ ∈ Subgroup.normalizer (H : Set Y)) (hn₁ : n₁ ∈ Subgroup.normalizer (H : Set Y))
    (k : ℕ) (hinv : ∀ x ∈ H, x ^ m = 1 → (n₀ * n₁) ^ k * x * ((n₀ * n₁) ^ k)⁻¹ = x⁻¹) :
    InvertsByWeyl P₀ P₁ m := by
  refine InvertsByWeyl.of_torus_closure hm hU hUn hUH hH (X := {n₀, n₁})
    (w := (n₀ * n₁) ^ k) ?_ ?_ ?_
  · intro x hx
    rcases (by simpa using hx : x = n₀ ∨ x = n₁) with rfl | rfl
    · exact ⟨Or.inl h₀, hn₀⟩
    · exact ⟨Or.inr h₁, hn₁⟩
  · have hmem : n₀ * n₁ ∈ Subgroup.closure ({n₀, n₁} : Set Y) :=
      (Subgroup.closure ({n₀, n₁} : Set Y)).mul_mem
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    exact (Subgroup.closure ({n₀, n₁} : Set Y)).pow_mem hmem k
  · simpa using hinv

private theorem exists_conj_preimage_left {G : Type} [Group G] {P₁ P₂ : Subgroup G}
    {M₁ M₂ : Subgroup Y} (ψ1 : ↥P₁ ≃* ↥M₁) (ψ12 : ↥(P₁ ⊓ P₂) ≃* ↥(M₁ ⊓ M₂))
    (hcomm1 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ1 (Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) x) : ↥M₁) : Y))
    {H : Subgroup Y} (hHM : H ≤ M₁ ⊓ M₂) {x : Y} (hx : x ∈ M₁)
    (hxH : x ∈ Subgroup.normalizer (H : Set Y)) :
    ∃ p ∈ P₁ ⊔ P₂, ∀ y : ↥(P₁ ⊓ P₂), ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) ∈ H →
      ∃ hy : ((p : G) * (y : G) * (p : G)⁻¹) ∈ P₁ ⊓ P₂,
        ((ψ12 ⟨_, hy⟩ : ↥(M₁ ⊓ M₂)) : Y) =
          x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := by
  let x₁ : ↥M₁ := ⟨x, hx⟩
  let p : ↥P₁ := ψ1.symm x₁
  refine ⟨p, (le_sup_left : P₁ ≤ P₁ ⊔ P₂) p.2, ?_⟩
  intro y hyH
  have hzH : x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp hxH ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y)).mp hyH
  let z : ↥(M₁ ⊓ M₂) := ⟨x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹, hHM hzH⟩
  let w : ↥(P₁ ⊓ P₂) := ψ12.symm z
  have hz : ((z : ↥(M₁ ⊓ M₂)) : Y) = x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := rfl
  have hw : ψ12 w = z := MulEquiv.apply_symm_apply ψ12 z
  have hincl : Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) w =
      p * Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) y * p⁻¹ := by
    apply ψ1.injective
    apply Subtype.ext
    calc ((ψ1 (Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) w) : ↥M₁) : Y)
        = ((ψ12 w : ↥(M₁ ⊓ M₂)) : Y) := (hcomm1 w).symm
      _ = ((z : ↥(M₁ ⊓ M₂)) : Y) := by rw [hw]
      _ = x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := hz
      _ = ((ψ1 (p * Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) y * p⁻¹) :
            ↥M₁) : Y) := by
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hcomm1 y]
  have hval : (w : G) = (p : G) * (y : G) * (p : G)⁻¹ := by
    simpa using congrArg (fun t : ↥P₁ => (t : G)) hincl
  have hpP : (p : G) * (y : G) * (p : G)⁻¹ ∈ P₁ :=
    P₁.mul_mem (P₁.mul_mem p.2 (Subgroup.mem_inf.mp y.2).1) (P₁.inv_mem p.2)
  have hpP₂ : (p : G) * (y : G) * (p : G)⁻¹ ∈ P₂ := by
    rw [← hval]
    exact (Subgroup.mem_inf.mp w.2).2
  have hwsub : (⟨(p : G) * (y : G) * (p : G)⁻¹, ⟨hpP, hpP₂⟩⟩ :
      ↥(P₁ ⊓ P₂)) = w := Subtype.ext hval.symm
  refine ⟨⟨hpP, hpP₂⟩, ?_⟩
  rw [hwsub, hw]

private theorem exists_conj_preimage_right {G : Type} [Group G] {P₁ P₂ : Subgroup G}
    {M₁ M₂ : Subgroup Y} (ψ2 : ↥P₂ ≃* ↥M₂) (ψ12 : ↥(P₁ ⊓ P₂) ≃* ↥(M₁ ⊓ M₂))
    (hcomm2 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ2 (Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) x) : ↥M₂) : Y))
    {H : Subgroup Y} (hHM : H ≤ M₁ ⊓ M₂) {x : Y} (hx : x ∈ M₂)
    (hxH : x ∈ Subgroup.normalizer (H : Set Y)) :
    ∃ p ∈ P₁ ⊔ P₂, ∀ y : ↥(P₁ ⊓ P₂), ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) ∈ H →
      ∃ hy : ((p : G) * (y : G) * (p : G)⁻¹) ∈ P₁ ⊓ P₂,
        ((ψ12 ⟨_, hy⟩ : ↥(M₁ ⊓ M₂)) : Y) =
          x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := by
  let x₂ : ↥M₂ := ⟨x, hx⟩
  let p : ↥P₂ := ψ2.symm x₂
  refine ⟨p, (le_sup_right : P₂ ≤ P₁ ⊔ P₂) p.2, ?_⟩
  intro y hyH
  have hzH : x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp hxH ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y)).mp hyH
  let z : ↥(M₁ ⊓ M₂) := ⟨x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹, hHM hzH⟩
  let w : ↥(P₁ ⊓ P₂) := ψ12.symm z
  have hz : ((z : ↥(M₁ ⊓ M₂)) : Y) = x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := rfl
  have hw : ψ12 w = z := MulEquiv.apply_symm_apply ψ12 z
  have hincl : Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) w =
      p * Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) y * p⁻¹ := by
    apply ψ2.injective
    apply Subtype.ext
    calc ((ψ2 (Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) w) : ↥M₂) : Y)
        = ((ψ12 w : ↥(M₁ ⊓ M₂)) : Y) := (hcomm2 w).symm
      _ = ((z : ↥(M₁ ⊓ M₂)) : Y) := by rw [hw]
      _ = x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := hz
      _ = ((ψ2 (p * Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) y * p⁻¹) :
            ↥M₂) : Y) := by
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hcomm2 y]
  have hval : (w : G) = (p : G) * (y : G) * (p : G)⁻¹ := by
    simpa using congrArg (fun t : ↥P₂ => (t : G)) hincl
  have hpP₂ : (p : G) * (y : G) * (p : G)⁻¹ ∈ P₂ :=
    P₂.mul_mem (P₂.mul_mem p.2 (Subgroup.mem_inf.mp y.2).2) (P₂.inv_mem p.2)
  have hpP₁ : (p : G) * (y : G) * (p : G)⁻¹ ∈ P₁ := by
    rw [← hval]
    exact (Subgroup.mem_inf.mp w.2).1
  have hwsub : (⟨(p : G) * (y : G) * (p : G)⁻¹, ⟨hpP₁, hpP₂⟩⟩ :
      ↥(P₁ ⊓ P₂)) = w := Subtype.ext hval.symm
  refine ⟨⟨hpP₁, hpP₂⟩, ?_⟩
  rw [hwsub, hw]

private theorem exists_conj_preimage {G : Type} [Group G] {P₁ P₂ : Subgroup G}
    {M₁ M₂ : Subgroup Y} (ψ1 : ↥P₁ ≃* ↥M₁) (ψ2 : ↥P₂ ≃* ↥M₂)
    (ψ12 : ↥(P₁ ⊓ P₂) ≃* ↥(M₁ ⊓ M₂))
    (hcomm1 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ1 (Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) x) : ↥M₁) : Y))
    (hcomm2 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ2 (Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) x) : ↥M₂) : Y))
    {H : Subgroup Y} (hHM : H ≤ M₁ ⊓ M₂) {x : Y} (hx : x ∈ M₁ ∨ x ∈ M₂)
    (hxH : x ∈ Subgroup.normalizer (H : Set Y)) :
    ∃ p ∈ P₁ ⊔ P₂, ∀ y : ↥(P₁ ⊓ P₂), ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) ∈ H →
      ∃ hy : ((p : G) * (y : G) * (p : G)⁻¹) ∈ P₁ ⊓ P₂,
        ((ψ12 ⟨_, hy⟩ : ↥(M₁ ⊓ M₂)) : Y) =
          x * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := by
  rcases hx with hx | hx
  · exact exists_conj_preimage_left ψ1 ψ12 hcomm1 hHM hx hxH
  · exact exists_conj_preimage_right ψ2 ψ12 hcomm2 hHM hx hxH

private theorem exists_word_conj_preimage {G : Type} [Group G] {P₁ P₂ : Subgroup G}
    {M₁ M₂ : Subgroup Y} (ψ1 : ↥P₁ ≃* ↥M₁) (ψ2 : ↥P₂ ≃* ↥M₂)
    (ψ12 : ↥(P₁ ⊓ P₂) ≃* ↥(M₁ ⊓ M₂))
    (hcomm1 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ1 (Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) x) : ↥M₁) : Y))
    (hcomm2 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ2 (Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) x) : ↥M₂) : Y))
    {H : Subgroup Y} (hHM : H ≤ M₁ ⊓ M₂) (l : List Y)
    (hl : ∀ x ∈ l, (x ∈ M₁ ∨ x ∈ M₂) ∧ x ∈ Subgroup.normalizer (H : Set Y)) :
    ∃ w ∈ P₁ ⊔ P₂, ∀ y : ↥(P₁ ⊓ P₂), ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) ∈ H →
      ∃ hy : ((w : G) * (y : G) * (w : G)⁻¹) ∈ P₁ ⊓ P₂,
        ((ψ12 ⟨_, hy⟩ : ↥(M₁ ⊓ M₂)) : Y) =
          l.prod * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * l.prod⁻¹ := by
  induction l with
  | nil =>
      refine ⟨1, (P₁ ⊔ P₂).one_mem, ?_⟩
      intro y hyH
      have hy' : ((1 : G) * (y : G) * (1 : G)⁻¹) ∈ P₁ ⊓ P₂ := by simpa using y.2
      refine ⟨hy', ?_⟩
      have hsub : (⟨(1 : G) * (y : G) * (1 : G)⁻¹, hy'⟩ :
          ↥(P₁ ⊓ P₂)) = y := Subtype.ext (by simp)
      rw [hsub]
      simp
  | cons x l ih =>
      have hl' : ∀ a ∈ l, (a ∈ M₁ ∨ a ∈ M₂) ∧
          a ∈ Subgroup.normalizer (H : Set Y) :=
        fun a ha => hl a (List.mem_cons_of_mem x ha)
      obtain ⟨w, hwP, hw⟩ := ih hl'
      have hxhl := hl x (by simp)
      obtain ⟨p, hpP, hp⟩ := exists_conj_preimage ψ1 ψ2 ψ12 hcomm1 hcomm2 hHM
        hxhl.1 hxhl.2
      have hlNorm : l.prod ∈ Subgroup.normalizer (H : Set Y) :=
        Subgroup.list_prod_mem (K := Subgroup.normalizer (H : Set Y))
          (fun a ha => (hl' a ha).2)
      refine ⟨(p : G) * w, (P₁ ⊔ P₂).mul_mem hpP hwP, ?_⟩
      intro y hyH
      obtain ⟨hy1, hφ1⟩ := hw y hyH
      let y' : ↥(P₁ ⊓ P₂) := ⟨(w : G) * (y : G) * (w : G)⁻¹, hy1⟩
      have hzH : ((ψ12 y' : ↥(M₁ ⊓ M₂)) : Y) ∈ H := by
        rw [show ((ψ12 y' : ↥(M₁ ⊓ M₂)) : Y) =
            l.prod * ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) * l.prod⁻¹ from hφ1]
        exact (Subgroup.mem_normalizer_iff.mp hlNorm
          ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y)).mp hyH
      obtain ⟨hpp, hφp⟩ := hp y' hzH
      have hc : ((p : G) * w) * (y : G) * (((p : G) * w))⁻¹ =
          (p : G) * ((w : G) * (y : G) * (w : G)⁻¹) * (p : G)⁻¹ := by group
      have hmem : (((p : G) * w) * (y : G) * (((p : G) * w))⁻¹) ∈ P₁ ⊓ P₂ :=
        hc ▸ hpp
      refine ⟨hmem, ?_⟩
      let y'' : ↥(P₁ ⊓ P₂) :=
        ⟨(p : G) * ((w : G) * (y : G) * (w : G)⁻¹) * (p : G)⁻¹, hpp⟩
      have hsub : (⟨_, hmem⟩ : ↥(P₁ ⊓ P₂)) = y'' := Subtype.ext hc
      rw [hsub]
      have hφp' : ((ψ12 y'' : ↥(M₁ ⊓ M₂)) : Y) =
          x * ((ψ12 y' : ↥(M₁ ⊓ M₂)) : Y) * x⁻¹ := hφp
      rw [hφp', hφ1, List.prod_cons]
      group

theorem InvertsByWeyl.exists_inv_of_iso {G : Type} [Group G] {P₁ P₂ : Subgroup G}
    {M₁ M₂ : Subgroup Y} {m : ℕ} (h : InvertsByWeyl M₁ M₂ m)
    (Φ : (RankTwoAmalgam.ofSubgroups P₁ P₂).Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))
    {E : Subgroup G} (hE : E ≤ P₁ ⊓ P₂) (hm : ∀ e ∈ E, e ^ m = 1) :
    ∃ w ∈ P₁ ⊔ P₂, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹ := by
  classical
  let ψ1 : ↥P₁ ≃* ↥M₁ := CFSG.Quasithin.F1.isoφ1 Φ
  let ψ2 : ↥P₂ ≃* ↥M₂ := CFSG.Quasithin.F1.isoφ2 Φ
  let ψ12 : ↥(P₁ ⊓ P₂) ≃* ↥(M₁ ⊓ M₂) := CFSG.Quasithin.F1.isoφ12 Φ
  have hcomm1 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ1 (Subgroup.inclusion (inf_le_left : P₁ ⊓ P₂ ≤ P₁) x) : ↥M₁) : Y) := by
    intro x
    change ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
      ((ψ1 ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ : ↥M₁) : Y)
    simpa [ψ1, ψ12, CFSG.Quasithin.F1.isoφ1, CFSG.Quasithin.F1.isoφ12]
      using CFSG.Quasithin.F1.coe_isoφ12_eq_φ1 Φ x
  have hcomm2 : ∀ x : ↥(P₁ ⊓ P₂),
      ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
        ((ψ2 (Subgroup.inclusion (inf_le_right : P₁ ⊓ P₂ ≤ P₂) x) : ↥M₂) : Y) := by
    intro x
    change ((ψ12 x : ↥(M₁ ⊓ M₂)) : Y) =
      ((ψ2 ⟨x, (Subgroup.mem_inf.mp x.2).2⟩ : ↥M₂) : Y)
    simpa [ψ2, ψ12, CFSG.Quasithin.F1.isoφ2, CFSG.Quasithin.F1.isoφ12]
      using CFSG.Quasithin.F1.coe_isoφ12_eq_φ2 Φ x
  let E' : Subgroup Y :=
    ((E.subgroupOf (P₁ ⊓ P₂)).map ψ12.toMonoidHom).map (M₁ ⊓ M₂).subtype
  have hE' : E' ≤ M₁ ⊓ M₂ := Subgroup.map_subtype_le _
  have hmE' : ∀ e ∈ E', e ^ m = 1 := by
    rintro e ⟨a, ha, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    have hzE : (z : G) ∈ E := Subgroup.mem_subgroupOf.mp hz
    have hzpow : (z : ↥(P₁ ⊓ P₂)) ^ m = 1 := by
      apply Subtype.ext
      exact hm (z : G) hzE
    have hpow : (ψ12 z : ↥(M₁ ⊓ M₂)) ^ m = 1 := by
      rw [← map_pow, hzpow, map_one]
    simpa using congrArg (fun t : ↥(M₁ ⊓ M₂) => (t : Y)) hpow
  obtain ⟨H, hE'H, hHM, l, hl, hinv⟩ := h E' hE' hmE'
  obtain ⟨w, hwP, hw⟩ :=
    exists_word_conj_preimage ψ1 ψ2 ψ12 hcomm1 hcomm2 hHM l hl
  refine ⟨w, hwP, ?_⟩
  intro e he
  let y : ↥(P₁ ⊓ P₂) := ⟨e, hE he⟩
  have hyE' : ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) ∈ E' := by
    refine Subgroup.mem_map.mpr ⟨ψ12 y, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr he, rfl⟩
  have hyH : ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) ∈ H := hE'H hyE'
  obtain ⟨hy, hφ⟩ := hw y hyH
  have hinv' := hinv ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y) hyE'
  have hφinv : ((ψ12 ⟨_, hy⟩ : ↥(M₁ ⊓ M₂)) : Y) =
      ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y)⁻¹ := hφ.trans hinv'
  have hφy : ((ψ12 y⁻¹ : ↥(M₁ ⊓ M₂)) : Y) =
      ((ψ12 y : ↥(M₁ ⊓ M₂)) : Y)⁻¹ := by
    simpa using congrArg (fun t : ↥(M₁ ⊓ M₂) => (t : Y)) (map_inv ψ12 y)
  have hsub : (⟨_, hy⟩ : ↥(P₁ ⊓ P₂)) = y⁻¹ := by
    apply ψ12.injective
    apply Subtype.ext
    exact hφinv.trans hφy.symm
  have := congrArg (fun t : ↥(P₁ ⊓ P₂) => (t : G)) hsub
  simpa [y] using this

