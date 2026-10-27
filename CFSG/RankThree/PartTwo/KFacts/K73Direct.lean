module

public import CFSG.RankThree.PartTwo.KFacts.K73Recognition

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

theorem eq_prod_wreathBase_of_abelian {S : Subgroup (M3 × W33)}
    (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (h81 : 81 ≤ Nat.card S) :
    S = (⊤ : Subgroup M3).prod wreathBase := by
  let π : S →* W33 := (MonoidHom.snd M3 W33).comp S.subtype
  have hker : Nat.card π.ker ≤ 3 := by
    have hinj : Function.Injective (fun k : π.ker => ((k : S) : M3 × W33).1) := by
      intro k k' hkk'
      have h1 := MonoidHom.mem_ker.mp k.2
      have h2 := MonoidHom.mem_ker.mp k'.2
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hkk' (h1.trans h2.symm)
    calc Nat.card π.ker ≤ Nat.card M3 := Nat.card_le_card_of_injective _ hinj
      _ = 3 := by simp
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv] at hcard
  have h27 : 27 ≤ Nat.card π.range := by
    by_contra h
    have : Nat.card π.range * Nat.card π.ker ≤ 26 * 3 := Nat.mul_le_mul (by omega) hker
    omega
  have habR : ∀ x ∈ π.range, ∀ y ∈ π.range, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hab x x.2 y y.2))
  have hB := right_eq_one_of_abelian_of_card habR h27
  have hle : S ≤ (⊤ : Subgroup M3).prod wreathBase := by
    intro z hz
    refine ⟨Subgroup.mem_top _, ?_⟩
    exact mem_wreathBase.mpr (hB _ ⟨⟨z, hz⟩, rfl⟩)
  apply Subgroup.eq_of_le_of_card_ge hle
  have hprod : Nat.card ((⊤ : Subgroup M3).prod wreathBase) = 81 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top]
    have hB27 : Nat.card wreathBase = 27 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (RegularWreathProduct.rightHom : W33 →* M3).ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (fun q => ⟨⟨1, q⟩, rfl⟩)).toEquiv, card_wreath] at h
      have h3 : Nat.card M3 = 3 := by simp
      rw [h3] at h
      change Nat.card (RegularWreathProduct.rightHom : W33 →* M3).ker = 27
      omega
    rw [hB27]
    simp
  rw [hprod]
  exact h81

section Direct

variable {P : Type*} [Group P]

@[expose] def m3Hom {c : P} (hc : c ^ 3 = 1) : M3 →* P where
  toFun z := c ^ (Multiplicative.toAdd z).val
  map_one' := by
    show c ^ 0 = 1
    exact pow_zero c
  map_mul' z z' := pow_val_add hc (Multiplicative.toAdd z) (Multiplicative.toAdd z')

theorem m3_cases : ∀ z : M3, z = 1 ∨ (Multiplicative.toAdd z).val = 1 ∨
    (Multiplicative.toAdd z).val = 2 := by
  decide

theorem commute_of_mem_closure {c e t : P} (hce : Commute c e) (hct : Commute c t) {x : P}
    (hx : x ∈ Subgroup.closure ({e, t} : Set P)) : Commute c x := by
  have hle : Subgroup.closure ({e, t} : Set P) ≤ Subgroup.centralizer {c} := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hce.symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

namespace WreathData

variable {e t c : P} (h : WreathData e t)
include h

@[expose] def prodHom (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t) :
    M3 × W33 →* P :=
  (m3Hom hc3).noncommCoprod h.hom fun _ w =>
    (commute_of_mem_closure hce hct (h.range_hom ▸ ⟨w, rfl⟩)).pow_left _

theorem prodHom_apply (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t)
    (x : M3 × W33) :
    h.prodHom hc3 hce hct x = c ^ (Multiplicative.toAdd x.1).val * h.hom x.2 :=
  rfl

theorem prodHom_inr (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t) (w : W33) :
    h.prodHom hc3 hce hct (1, w) = h.hom w := by
  rw [prodHom_apply]
  show c ^ 0 * h.hom w = h.hom w
  rw [pow_zero, one_mul]

theorem prodHom_inl (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t) :
    h.prodHom hc3 hce hct (Multiplicative.ofAdd 1, 1) = c := by
  rw [prodHom_apply]
  show c ^ 1 * h.hom 1 = c
  rw [pow_one, map_one, mul_one]

theorem prodHom_injective (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t)
    (hcT : c ∉ Subgroup.closure ({e, t} : Set P)) :
    Function.Injective (h.prodHom hc3 hce hct) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨z, w⟩ hzw
  rw [prodHom_apply] at hzw
  have hmem : c ^ (Multiplicative.toAdd z).val ∈ Subgroup.closure ({e, t} : Set P) := by
    rw [eq_inv_of_mul_eq_one_left hzw, ← h.range_hom]
    exact Subgroup.inv_mem _ ⟨w, rfl⟩
  have hz : z = 1 := by
    rcases m3_cases z with hz | hz | hz
    · exact hz
    · rw [hz, pow_one] at hmem
      exact absurd hmem hcT
    · rw [hz] at hmem
      exfalso
      apply hcT
      have h4 : c = (c ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul]
      rw [h4]
      exact Subgroup.pow_mem _ hmem _
  subst hz
  have hw : h.hom w = 1 := by
    have h0 : c ^ (Multiplicative.toAdd (1 : M3)).val = 1 := pow_zero c
    rwa [h0, one_mul] at hzw
  have hw1 : w = 1 := h.hom_injective (hw.trans (map_one _).symm)
  rw [hw1]
  rfl

theorem range_prodHom (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t) :
    (h.prodHom hc3 hce hct).range = Subgroup.zpowers c ⊔ Subgroup.closure {e, t} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [prodHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _
      (Subgroup.mem_zpowers c) _)) (Subgroup.mem_sup_right (h.range_hom ▸ ⟨x.2, rfl⟩))
  · refine sup_le (Subgroup.zpowers_le.mpr ⟨_, h.prodHom_inl hc3 hce hct⟩) ?_
    rw [← h.range_hom]
    rintro _ ⟨w, rfl⟩
    exact ⟨(1, w), h.prodHom_inr hc3 hce hct w⟩

theorem map_prod_base (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t) :
    ((⊤ : Subgroup M3).prod wreathBase).map (h.prodHom hc3 hce hct) =
      Subgroup.zpowers c ⊔ eBase e t := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [prodHom_apply]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _
      (Subgroup.mem_zpowers c) _)) (Subgroup.mem_sup_right ?_)
    rw [← h.map_base]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_prod.mp hx).2
  · refine sup_le (Subgroup.zpowers_le.mpr ⟨_, Subgroup.mem_prod.mpr
      ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩, h.prodHom_inl hc3 hce hct⟩) ?_
    rw [← h.map_base]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(1, w), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hw⟩, h.prodHom_inr hc3 hce hct w⟩

theorem eq_of_abelian (hc3 : c ^ 3 = 1) (hce : Commute c e) (hct : Commute c t)
    (hcT : c ∉ Subgroup.closure ({e, t} : Set P)) {S : Subgroup P}
    (hS : S ≤ Subgroup.zpowers c ⊔ Subgroup.closure {e, t})
    (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (h81 : 81 ≤ Nat.card S) :
    S = Subgroup.zpowers c ⊔ eBase e t := by
  set φ := h.prodHom hc3 hce hct with hφ
  have hinj := h.prodHom_injective hc3 hce hct hcT
  have hmc : (S.comap φ).map φ = S := by
    rw [Subgroup.map_comap_eq, h.range_prodHom, inf_eq_right.mpr hS]
  have hcard : Nat.card (S.comap φ) = Nat.card S := by
    conv_rhs => rw [← hmc]
    rw [Subgroup.card_map_of_injective hinj]
  have hab' : ∀ x ∈ S.comap φ, ∀ y ∈ S.comap φ, x * y = y * x := by
    intro x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    exact hab _ hx _ hy
  have hS' := eq_prod_wreathBase_of_abelian hab' (hcard ▸ h81)
  rw [← hmc, hS', h.map_prod_base]

end WreathData

end Direct

end CFSG.RankThree.PartTwo.KFacts
