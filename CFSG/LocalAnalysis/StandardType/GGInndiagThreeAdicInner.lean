module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDARefute
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
import CFSG.GroupTheory.CenterlessInnerCentralizer
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB
open scoped Pointwise

section Group

variable {G : Type*} [Group G]

private theorem mul_card_dvd_card_of_not_mem_threeAdic {H K : Subgroup G} (hHK : H ≤ K)
    (hK : K ≤ Subgroup.normalizer (H : Set G)) {g : G} (hgK : g ∈ K) (hgH : g ∉ H) {p : ℕ}
    [Fact p.Prime] (hg : g ^ p = 1) : p * Nat.card H ∣ Nat.card K := by
  haveI : (H.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hK
  have hgp : (⟨g, hgK⟩ : ↥K) ^ p = 1 := Subtype.ext (by simpa using hg)
  have hp : orderOf (QuotientGroup.mk ⟨g, hgK⟩ : ↥K ⧸ H.subgroupOf K) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, hgp, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hgH
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf K),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
  exact mul_dvd_mul_right (hp ▸ orderOf_dvd_natCard _) _

private theorem three_mul_card_dvd_card_sup_threeAdic {J : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (J : Set G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) :
    3 * Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥(J ⊔ Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hxJ : x ∈ J
  · have hz : (⟨x, hxJ⟩ : ↥J) ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.2 fun l =>
      Subtype.ext (Subgroup.mem_centralizer_iff.1 hx l l.2)
    have h3 : orderOf (⟨⟨x, hxJ⟩, hz⟩ : Subgroup.center ↥J) = 3 :=
      orderOf_eq_prime (Subtype.ext (Subtype.ext (by simpa using hx3))) fun h => hx1 (by
        simpa using congrArg (fun z : Subgroup.center ↥J => ((z : ↥J) : G)) h)
    calc 3 * Nat.card (↥J ⧸ Subgroup.center ↥J)
        ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J) := by
          rw [mul_comm]
          exact mul_dvd_mul_left _ (h3 ▸ orderOf_dvd_natCard _)
      _ = Nat.card ↥J := (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
      _ ∣ _ := Subgroup.card_dvd_of_le le_sup_left
  · have hxN : x ∈ Subgroup.normalizer (J : Set G) := Subgroup.centralizer_le_normalizer _ hx
    exact (mul_dvd_mul_left 3 (Subgroup.card_quotient_dvd_card _)).trans
      (mul_card_dvd_card_of_not_mem_threeAdic le_sup_left
        (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hxN))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hxJ hx3)

theorem mem_sup_zpowers_of_threeAdic [Finite G] {J : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.centralizer (J : Set G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hy : y ∈ Subgroup.normalizer (J : Set G)) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hv : padicValNat 3 (Nat.card G) ≤
      padicValNat 3 (Nat.card (↥J ⧸ Subgroup.center ↥J)) + 1) :
    y ∈ J ⊔ Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hyM
  have hyx : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact Commute.zpow_left hxy k)
  have hyN : y ∈ Subgroup.normalizer ((J ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup J _ ⟨hy, hyx⟩
  have h2 := mul_card_dvd_card_of_not_mem_threeAdic le_sup_left
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hyN))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hyM hy3
  have h9 : 3 * (3 * Nat.card (↥J ⧸ Subgroup.center ↥J)) ∣ Nat.card G :=
    ((mul_dvd_mul_left 3 (three_mul_card_dvd_card_sup_threeAdic hx hx1 hx3)).trans h2).trans
      (Subgroup.card_subgroup_dvd_card _)
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hQ0 : Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 0 :=
    (Nat.pos_of_dvd_of_pos (Subgroup.card_quotient_dvd_card _) Nat.card_pos).ne'
  have hle := (padicValNat_dvd_iff_le hG0).mp ((pow_padicValNat_dvd (p := 3)).trans h9)
  rw [padicValNat.mul (by norm_num) (by positivity), padicValNat.mul (by norm_num) hQ0,
    padicValNat.self (by norm_num)] at hle
  omega

theorem mem_sup_centralizer_of_threeAdic [Finite G] {J : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.centralizer (J : Set G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hy : y ∈ Subgroup.normalizer (J : Set G)) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hv : padicValNat 3 (Nat.card G) ≤
      padicValNat 3 (Nat.card (↥J ⧸ Subgroup.center ↥J)) + 1) :
    y ∈ J ⊔ Subgroup.centralizer (J : Set G) :=
  sup_le_sup_left (Subgroup.zpowers_le.2 hx) J
    (mem_sup_zpowers_of_threeAdic hx hx1 hx3 hy hy3 hxy hv)

theorem ggInnerOn_conj_of_mem_sup_centralizer {J : Subgroup G} {y : G}
    (hy : y ∈ J ⊔ Subgroup.centralizer (J : Set G)) : GGInnerOn J (MulAut.conj y) := by
  have hy' : y ∈ (J : Set G) * (Subgroup.centralizer (J : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left J _ (Subgroup.centralizer_le_normalizer _)]
    exact hy
  obtain ⟨z, hz, c, hc, rfl⟩ := hy'
  refine ⟨z, hz, fun j hj => ?_⟩
  have hcj : c * j = j * c := (Subgroup.mem_centralizer_iff.1 hc j hj).symm
  calc MulAut.conj (z * c) j = z * (c * j) * c⁻¹ * z⁻¹ := by
        simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]
    _ = z * j * z⁻¹ := by rw [hcj]; group

end Group

private theorem center_eq_bot_threeAdic {R : Type} [Group R] (hR : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  rcases hR.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

theorem not_ggOutsideInndiag_of_threeAdic {R : Type} [Group R] [Finite R] {I : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) (hR : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    {s t : MulAut R} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (ht3 : t ^ 3 = 1) (hst : s * t = t * s)
    (hsI : s ∈ I) (htI : t ∈ I) {J₁ : Subgroup R} (hJ₁ : IsComponentOf J₁ (ggFix s))
    {P : LargeEvenMarkProp ↥J₁} (hM : LargeEvenMarking ↥J₁ P)
    (hv : padicValNat 3 (Nat.card R) ≤
      padicValNat 3 (Nat.card (↥J₁ ⧸ Subgroup.center ↥J₁)) + 1) :
    ¬ GGOutsideInndiag J₁ t := by
  intro hout
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot (center_eq_bot_threeAdic hR hna)
  obtain ⟨x, rfl⟩ := hI hsI
  obtain ⟨y, rfl⟩ := hI htI
  have hx : x ∈ Subgroup.centralizer (J₁ : Set R) := Subgroup.mem_centralizer_iff.2 fun l hl => by
    have h := mem_ggFix.1 (hJ₁.1 hl)
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hle : J₁.map (MulAut.conj y).toMonoidHom ≤ J₁ := by
    rintro _ ⟨l, hl, rfl⟩
    exact hout.1 l hl
  have hy : y ∈ Subgroup.normalizer (J₁ : Set R) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge)
  exact not_ggOutsideInndiag_of_innerOn hM (ggInnerOn_conj_of_mem_sup_centralizer
    (mem_sup_centralizer_of_threeAdic hx (fun h1 => hs1 (by rw [h1, map_one]))
      (hinj (by rw [map_pow, hs3, map_one])) hy (hinj (by rw [map_pow, ht3, map_one]))
      (hinj (by rw [map_mul, map_mul, hst])) hv)) hout

end CFSG.StandardType.SCFourCover

end
