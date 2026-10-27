module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44ModelAut
public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Map
import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DynAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

theorem actsOnDynkinMod_equiv_iff {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (L : Subgroup G) (t : G) :
    ActsOnDynkinMod ⊥ (L.map e.toMonoidHom) (e t) ↔ ActsOnDynkinMod ⊥ L t := by
  constructor
  · intro h
    have h1 := W183L34.actsOnDynkinMod_map e.symm.toMonoidHom e.symm.injective h
    rw [Subgroup.map_map,
      show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from by
        ext x
        simp,
      Subgroup.map_id] at h1
    have h2 : e.symm.toMonoidHom (e t) = t := MulEquiv.symm_apply_apply e t
    rwa [h2] at h1
  · intro h
    exact W183L34.actsOnDynkinMod_map e.toMonoidHom e.injective h

namespace Sp44

open CFSG.GH74.KGroups
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b

theorem dynkin_exponent_odd {x : El} (hx : validB x = true)
    (h : ActsOnDynkinMod ⊥ (innAutOf S4) (autOf x)) : x.2 % 2 = 1 := by
  rcases Nat.even_or_odd x.2 with hev | hod
  · exfalso
    have hx2 : x.2 = 0 ∨ x.2 = 2 := by
      have hlt : x.2 < 4 := (validB_iff.mp hx).2.2
      have hmod : x.2 % 2 = 0 := Nat.even_iff.mp hev
      omega
    have hauto : autOf x = MulAut.conj (toS4 x.1 (validB_symp hx)) * minorAut GF4 ^ x.2 := by
      rw [autOf, dif_pos hx]
    have hcg : MulAut.conj (toS4 x.1 (validB_symp hx)) ∈ innAutOf S4 := ⟨_, rfl⟩
    rcases hx2 with h0 | h2
    · rw [h0, pow_zero, mul_one] at hauto
      exact w183finSp44dyn_not_actsOnDynkinMod_inner hcg (hauto ▸ h)
    · rw [h2] at hauto
      exact w183finSp44dyn_not_actsOnDynkinMod_minorAut_sq
        ((w183finSp44dyn_actsOnDynkinMod_mul_inner (t := minorAut GF4 ^ 2) hcg).mp
          (hauto ▸ h))
  · exact Nat.odd_iff.mp hod

theorem dynkin_generates_S4 {τ : MulAut S4} (h : ActsOnDynkinMod ⊥ (innAutOf S4) τ) :
    innAutOf S4 ⊔ Subgroup.zpowers τ = ⊤ := by
  obtain ⟨x, hx, rfl⟩ := autOf_surj τ
  have hodd : x.2 % 2 = 1 := dynkin_exponent_odd hx h
  have hx2 : x.2 = 1 ∨ x.2 = 3 := by
    have hlt : x.2 < 4 := (validB_iff.mp hx).2.2
    omega
  set ρ : MulAut S4 := minorAut GF4 with hρ
  have hord : orderOf ρ = 4 := by
    rw [hρ]
    have := orderOf_minorAut (K := GF4) (f := 2) (by norm_num)
      (by rw [Nat.card_eq_fintype_card]; decide)
    simpa using this
  have hρ4 : ρ ^ 4 = 1 := by
    have h := pow_orderOf_eq_one ρ
    rwa [hord] at h
  have hauto : autOf x = MulAut.conj (toS4 x.1 (validB_symp hx)) * ρ ^ x.2 := by
    rw [autOf, dif_pos hx]
  have hρmem : ρ ∈ innAutOf S4 ⊔ Subgroup.zpowers (autOf x) := by
    have hcg : MulAut.conj (toS4 x.1 (validB_symp hx)) ∈ innAutOf S4 :=
      ⟨toS4 x.1 (validB_symp hx), rfl⟩
    have hρj : ρ ^ x.2 ∈ innAutOf S4 ⊔ Subgroup.zpowers (autOf x) := by
      have heq : ρ ^ x.2 = (MulAut.conj (toS4 x.1 (validB_symp hx)))⁻¹ * autOf x := by
        rw [hauto]
        group
      rw [heq]
      exact mul_mem (inv_mem (Subgroup.mem_sup_left hcg))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rcases hx2 with h1 | h3
    · rw [h1, pow_one] at hρj
      exact hρj
    · rw [h3] at hρj
      have h8 : ρ ^ 8 = 1 := by
        rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hρ4, one_pow]
      have h9 : ρ ^ 9 = ρ := by
        rw [show (9 : ℕ) = 8 + 1 by norm_num, pow_add, h8, one_mul, pow_one]
      have hcube : ρ = (ρ ^ 3) ^ 3 := by
        rw [← pow_mul, show (3 : ℕ) * 3 = 9 by norm_num]
        exact h9.symm
      rw [hcube]
      exact pow_mem hρj 3
  rw [eq_top_iff]
  intro α _
  obtain ⟨g, m, hm, hα⟩ :=
    aut_eq_conj_mul_pow (K := GF4) (n := 2) (by norm_num)
      (by rw [Nat.card_eq_fintype_card]; decide) α
  rw [hα]
  refine mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) ?_
  exact Subgroup.zpowers_le.mpr hρmem (Subgroup.npow_mem_zpowers ρ m)

end Sp44

theorem sp44_dynkin_generates (M : Type) [Group M] (hM : IsSp4 M 2) (τ : MulAut M)
    (hτ : ActsOnDynkinMod ⊥ (innAutOf M) τ) : innAutOf M ⊔ Subgroup.zpowers τ = ⊤ := by
  obtain ⟨e⟩ := Sp44.isSp4_equiv_S4 hM
  let E : MulAut M ≃* MulAut Sp44.S4 := MulAut.congr e
  have hinn : (innAutOf M).map E.toMonoidHom = innAutOf Sp44.S4 := by
    change (CFSG.ComponentClassification.OuterAutomorphisms.inner M).map E.toMonoidHom =
      CFSG.ComponentClassification.OuterAutomorphisms.inner Sp44.S4
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hτ' : ActsOnDynkinMod ⊥ (innAutOf Sp44.S4) (E τ) := by
    have h := (actsOnDynkinMod_equiv_iff E (innAutOf M) τ).mpr hτ
    rwa [hinn] at h
  have hgen := Sp44.dynkin_generates_S4 hτ'
  have hmap : (innAutOf M ⊔ Subgroup.zpowers τ).map E.toMonoidHom =
      (⊤ : Subgroup (MulAut Sp44.S4)) := by
    rw [Subgroup.map_sup, hinn, MonoidHom.map_zpowers]
    exact hgen
  exact Subgroup.map_injective E.injective
    (hmap.trans (Subgroup.map_top_of_surjective _ E.surjective).symm)

end CFSG.LocalAnalysis.WeakClosure81

end
