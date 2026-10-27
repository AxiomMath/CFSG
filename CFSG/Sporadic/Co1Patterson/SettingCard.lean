module

public import CFSG.Sporadic.Co1Patterson.SettingOmega
public import CFSG.LargeExtraspecial.S45QOmegaMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Literature.FSmith

section Card

variable {M : Type} [Group M] {Q : Subgroup M}

theorem card_abelianization_of_card (hQ : IsExtraspecialPGroup 2 Q) (hcard : Nat.card Q = 2 ^ 9) :
    Nat.card (Additive (Abelianization Q)) = 2 ^ 8 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (_root_.commutator Q)
  rw [hQ.2.1, hQ.2.2.2, hcard] at h
  change Nat.card (Q ⧸ _root_.commutator Q) = 2 ^ 8
  rw [hQ.2.1]
  omega

theorem extraspecialConjOrth_eq_one_of_mem [Finite M] (hn : Q.Normal)
    (hQ : IsExtraspecialPGroup 2 Q) [Module (ZMod 2) (Additive (Abelianization Q))] {g : M}
    (hg : g ∈ Q) :
    extraspecialConjOrth hQ hn g = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  change Additive.ofMul (Abelianization.of (conjAut hn g x)) = Additive.ofMul (Abelianization.of x)
  have h : conjAut hn g x = ⟨g, hg⟩ * x * (⟨g, hg⟩ : Q)⁻¹ :=
    Subtype.ext (by rw [conjAut_apply]; rfl)
  rw [h, ofMul_of_mul, ofMul_of_mul, map_inv, ofMul_inv]
  abel

theorem le_of_normal_of_card [Finite M] (hn : Q.Normal) (hQ : IsExtraspecialPGroup 2 Q)
    (hC : centralizer (Q : Set M) ≤ Q) (hcard : Nat.card Q = 2 ^ 9)
    (hM : Nat.card M = 89181388800) (P : Subgroup M) (hP : P.Normal) (h2 : IsPGroup 2 P) :
    P ≤ Q := by
  let _ : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hQ
  set ρ := extraspecialConjOrth hQ hn with hρ
  have hker : ρ.ker = Q := le_antisymm (fun g hg => mem_of_extraspecialConjOrth_eq_one hQ hn hC hg)
    (fun g hg => extraspecialConjOrth_eq_one_of_mem hn hQ hg)
  have : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  have h8 : finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    have h := card_abelianization_of_card hQ hcard
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
    exact Nat.pow_right_injective le_rfl h
  have hR : Nat.card ρ.range = 174182400 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hker, hcard, hM] at h
    omega
  have : Finite ρ.range := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  have hnd := extraspecialQuadForm_nondegenerate hQ
  obtain ⟨-, hΩ⟩ := isPlusType_and_map_eq_omegaGroup_of_card hnd h8 ρ.range hR
  have hsimple : IsSimpleGroup ρ.range := by
    have := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_omegaGroup_of_six_le hnd (by omega)
    exact ((Subgroup.equivMapOfInjective ρ.range _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr hΩ)).isSimpleGroup
  have hPn : (P.map ρ.rangeRestrict).Normal := hP.map _ ρ.rangeRestrict_surjective
  rcases hsimple.eq_bot_or_eq_top_of_normal (P.map ρ.rangeRestrict) with h | h
  · rwa [Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict, hker] at h
  · exfalso
    have h2' : IsPGroup 2 (P.map ρ.rangeRestrict) := h2.map _
    rw [h] at h2'
    obtain ⟨k, hk⟩ := (h2'.of_equiv Subgroup.topEquiv).exists_card_eq
    rw [hR] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 174182400)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end Card

@[expose] noncomputable def settingOfCard {G : Type} [Group G] [Finite G] (z : G)
    (hz : orderOf z = 2) (Q : Subgroup (centralizer ({z} : Set G))) (hn : Q.Normal)
    (hQ : IsExtraspecialPGroup 2 Q)
    (hC : centralizer (Q : Set (centralizer ({z} : Set G))) ≤ Q) (hcard : Nat.card Q = 2 ^ 9)
    (hM : Nat.card (centralizer ({z} : Set G)) = 89181388800) : Setting G where
  z := z
  orderOf_z := hz
  Q := Q
  normal := hn
  extraspecial := hQ
  centralizer_le := hC
  le_of_normal := le_of_normal_of_card hn hQ hC hcard hM

end CFSG.Sporadic.Co1Patterson
