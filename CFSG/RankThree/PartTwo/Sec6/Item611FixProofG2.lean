module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProof
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofG2
import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

namespace Res611Fix

theorem card_map_of_inf_ker_eq_bot {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {H : Subgroup X} (h : H ⊓ f.ker = ⊥) : Nat.card (H.map f) = Nat.card H := by
  have hinj : Function.Injective (f.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : (x : X) ∈ H ⊓ f.ker := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
    Subgroup.range_subtype]

theorem eq_one_of_sq_of_mem {X : Type*} [Group X] {Z : Subgroup X} (hZ : Nat.card Z = 3)
    {z : X} (hz : z ∈ Z) (hz2 : z ^ 2 = 1) : z = 1 := by
  have h3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ] at h
    simpa using congrArg Subtype.val h
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, hz2, inv_one, one_mul]

end Res611Fix

open Res611Fix

section Certs


theorem item611NotG2CoverT_holds :
    ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
      4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
        A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
        ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
          T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ → Item611CoverCase A L c → False := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE _ T hT hTL hTθ hcase
  obtain ⟨-, -, hZ3, hM, hinner⟩ := hcase
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEA : E ≤ A := hE.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.1.2
  have hCE9 := card_inf_centralizer_of_mem_fourGroupsMinus (Late.isE27_of_mem_partTwoE hE.1) hT
  obtain ⟨e, heCE, hec⟩ : ∃ e ∈ E ⊓ Subgroup.centralizer (T : Set G), e ∉ Subgroup.zpowers c := by
    by_contra hall
    push Not at hall
    have hle : E ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.zpowers c := fun x hx => hall x hx
    have h1 := Subgroup.card_le_of_le hle
    have hc3 : orderOf c = 3 := orderOf_eq_prime (hA3 c hcA) hc1
    rw [Nat.card_zpowers, hc3, hCE9] at h1
    omega
  have heA : e ∈ A := hEA heCE.1
  have heT : ∀ t ∈ T, e * t = t * e := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp heCE.2 t ht).symm
  obtain ⟨heN, l, hel⟩ := hinner e heA
  set θL := aschbacherSolvableCore 3 L with hθL
  set Z := Subgroup.center (L ⧸ θL) with hZdef
  set lb : L ⧸ θL := (l : L ⧸ θL) with hlb
  have hlbZ : lb ∉ Z := by
    intro hz
    apply hec
    have h1 : Res611Res4.thetaAct L ⟨e, heN⟩ = 1 := by
      rw [hel]
      ext y
      rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hz y).symm,
        mul_inv_cancel_right]
    have heC : e ∈ thetaQuotCentralizer L :=
      (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct heN).mpr h1
    rw [← hCA]
    exact ⟨heA, heC⟩
  have hlb3 : lb ^ 3 ∈ Z := by
    apply Sec12.mem_center_of_conj_eq_one
    rw [map_pow, ← hel, ← map_pow]
    have h1 : (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA3 e heA)
    rw [h1, map_one]
  have hcomm : ∀ t : L, (t : G) ∈ T → lb * (t : L ⧸ θL) = (t : L ⧸ θL) * lb := by
    intro t ht
    have h1 : Res611Res4.thetaAct L ⟨e, heN⟩ (t : L ⧸ θL) = (t : L ⧸ θL) := by
      rw [Res611Res4.thetaAct_mk]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe, heT t ht, mul_inv_cancel_right]
    rw [hel, MulAut.conj_apply] at h1
    calc lb * (t : L ⧸ θL) = (lb * (t : L ⧸ θL) * lb⁻¹) * lb := by group
      _ = (t : L ⧸ θL) * lb := by rw [h1]
  set ρ : L →* (L ⧸ θL) ⧸ Z := (QuotientGroup.mk' Z).comp (QuotientGroup.mk' θL) with hρ
  set x : (L ⧸ θL) ⧸ Z := QuotientGroup.mk' Z lb with hx
  set W := (T.subgroupOf L).map ρ with hW
  have hx1 : x ≠ 1 := fun h => hlbZ ((QuotientGroup.eq_one_iff _).mp h)
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hlb3
  obtain ⟨-, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
  have hker : T.subgroupOf L ⊓ ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htT, htk⟩
    have htT' : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp htT
    have htZ : (t : L ⧸ θL) ∈ Z := by
      have h1 : ρ t = 1 := htk
      simpa [hρ, QuotientGroup.eq_one_iff] using h1
    have ht2 : (t : L ⧸ θL) ^ 2 = 1 := by
      have h1 : t ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hTab.2 _ htT')
      rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
    have ht1 : (t : L ⧸ θL) = 1 := eq_one_of_sq_of_mem hZ3 htZ ht2
    have htθ : t ∈ θL := (QuotientGroup.eq_one_iff t).mp ht1
    have hmem : (t : G) ∈ T ⊓ inSubgroup (aschbacherSolvableCore 3) L := ⟨htT', ⟨t, htθ, rfl⟩⟩
    rw [hTθ, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hW4 : Nat.card W = 4 := by
    rw [hW, card_map_of_inf_ker_eq_bot ρ hker, ← hT4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  have hWab : CFSG.Assembly.IsElemAbelian 2 W := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a', ha', rfl⟩ := a
      obtain ⟨_, b', hb', rfl⟩ := b
      have hab : a' * b' = b' * a' := Subtype.ext (by
        have := congrArg Subtype.val (hTab.1.is_comm.comm
          (⟨a', Subgroup.mem_subgroupOf.mp ha'⟩ : T) ⟨b', Subgroup.mem_subgroupOf.mp hb'⟩)
        simpa using this)
      apply Subtype.ext
      change ρ a' * ρ b' = ρ b' * ρ a'
      rw [← map_mul, ← map_mul, hab]
    · rintro _ ⟨t, ht, rfl⟩
      rw [← map_pow]
      have h1 : t ^ 2 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hTab.2 _ (Subgroup.mem_subgroupOf.mp ht))
      rw [h1, map_one]
  have hWcomm : ∀ w ∈ W, x * w = w * x := by
    rintro _ ⟨t, ht, rfl⟩
    change QuotientGroup.mk' Z lb * QuotientGroup.mk' Z (t : L ⧸ θL) =
      QuotientGroup.mk' Z (t : L ⧸ θL) * QuotientGroup.mk' Z lb
    rw [← map_mul, ← map_mul, hcomm t (Subgroup.mem_subgroupOf.mp ht)]
  have h := kS611G2Cent_holds _ hM x hx1 hx3 W hWab hWcomm
  rw [hW4] at h
  omega

end Certs

end CFSG.RankThree.PartTwo.Sec6
