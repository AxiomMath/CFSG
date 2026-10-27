module

public import CFSG.RankThree.PartTwo.Sec21.HeringHullChain1

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringHull

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_inSubgroup_theta_iff_of_le {H : Subgroup G} (x : H) :
    (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) H ↔ x ∈ aschbacherSolvableCore 3 H :=
  Subgroup.mem_map_iff_mem H.subtype_injective

theorem card_quot_lt_of_llRel (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hG : TheoremFourHyp G)
    {A : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {a a' : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (ha'A : a' ∈ A) (ha'1 : a' ≠ 1) {Z K : Subgroup G} (hZ : Z ∈ thetaComponentsAt 3 a)
    (hK : K ∈ thetaComponentsAt 3 a') (hZK : llRel Z K) (ha : a ∉ thetaQuotCentralizer K) :
    Nat.card (Z ⧸ aschbacherSolvableCore 3 Z) < Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
  have hZp : Group.IsPerfect Z :=
    CFSG.RankThree.PartTwo.Sec6.isPerfect_of_mem_thetaComponentsAt hZ
  have hZC : Z ≤ Subgroup.centralizer ({a} : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.le_centralizer_of_mem_thetaComponentsAt hZ
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hAn ha'A ha'1 hK haA
  obtain ⟨ha'Z, hYK⟩ := residual_le_of_llRel h45 h48 hG hAe hAn haA ha1 ha'A ha'1 hZ hK hZK
  set Y : Subgroup G := inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer ({a'} : Set G))
    with hYdef
  have hYZ : Y ≤ Z :=
    (CFSG.RankThree.PartTwo.Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hYC : Y ≤ Subgroup.centralizer ({a} : Set G) := hYZ.trans hZC
  have hYN : Y ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Z : Set G) :=
    hYZ.trans (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta Z)
  have hZcov : Z ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) Z := by
    have hD3 : IsPGroup 3 (Subgroup.zpowers a') :=
      CFSG.RankThree.PartTwo.Sec6.isPGroup_zpowers_of_pow_three (hAe.2 a' ha'A)
    have hDC : Subgroup.zpowers a' ≤ thetaQuotCentralizer Z := Subgroup.zpowers_le.mpr ha'Z
    have h := CFSG.RankThree.PartTwo.Sec6.le_residual_inf_centralizer_sup_theta hZp hD3 hDC
    rw [CFSG.RankThree.PartTwo.Sec6.centralizer_zpowers_eq] at h
    exact h
  have hJθ : Y ⊓ inSubgroup (aschbacherSolvableCore 3) K ≤
      inSubgroup (aschbacherSolvableCore 3) Z := by
    set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) Z with hTdef
    set J : Subgroup G := Y ⊓ inSubgroup (aschbacherSolvableCore 3) K with hJdef
    have hTZ : T ≤ Z := CFSG.RankThree.PartTwo.Sec6.theta_le Z
    have hJZ : J ≤ Z := inf_le_left.trans hYZ
    have hJK : J ≤ inSubgroup (aschbacherSolvableCore 3) K := inf_le_right
    have hTsol : Group.IsSolvable T :=
      (CFSG.RankThree.PartTwo.Sec6.theta_solvable_and_not_dvd Z).1
    have hT3 : ¬ 3 ∣ Nat.card T := (CFSG.RankThree.PartTwo.Sec6.theta_solvable_and_not_dvd Z).2
    have hJ3 : ¬ 3 ∣ Nat.card J := fun h =>
      (CFSG.RankThree.PartTwo.Sec6.theta_solvable_and_not_dvd K).2
        (h.trans (Subgroup.card_dvd_of_le hJK))
    have hJsol : Group.IsSolvable J := by
      haveI : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) K) :=
        (CFSG.RankThree.PartTwo.Sec6.theta_solvable_and_not_dvd K).1
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJK)
        (Subgroup.inclusion_injective hJK)
    have hJT : J ≤ Subgroup.normalizer (T : Set G) :=
      hJZ.trans (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta Z)
    have hTN : T ≤ Subgroup.normalizer ((T ⊔ J : Subgroup G) : Set G) := by
      apply CFSG.RankThree.PartTwo.Sec6.le_normalizer_sup_of_conj
      · intro t ht x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
          (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta Z (hTZ ht)) x).mp hx)
      · intro t ht x hx
        have hxZ : x ∈ Z := hJZ hx
        have h1 : x⁻¹ * t * x ∈ T := by
          have h := (Subgroup.mem_normalizer_iff.mp
            (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta Z (Z.inv_mem hxZ)) t).mp ht
          simpa using h
        have hs : x⁻¹ * t * x * t⁻¹ ∈ T := T.mul_mem h1 (T.inv_mem ht)
        have e : t * x * t⁻¹ = x * (x⁻¹ * t * x * t⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hs)
    have hYJ : Y ≤ Subgroup.normalizer ((T ⊔ J : Subgroup G) : Set G) := by
      apply CFSG.RankThree.PartTwo.Sec6.le_normalizer_sup_of_conj
      · intro y hy x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
          (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta Z (hYZ hy)) x).mp hx)
      · intro y hy x hx
        have hx' := Subgroup.mem_inf.mp hx
        have h1 : y * x * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy hx'.1) (Y.inv_mem hy)
        have h2 : y * x * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K :=
          (Subgroup.mem_normalizer_iff.mp
            (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta K (hYK hy)) x).mp hx'.2
        exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
    have hZN : Z ≤ Subgroup.normalizer ((T ⊔ J : Subgroup G) : Set G) :=
      hZcov.trans (sup_le hYJ hTN)
    have hWZ : T ⊔ J ≤ Z := sup_le hTZ hJZ
    have hWsol : Group.IsSolvable (T ⊔ J : Subgroup G) :=
      CFSG.RankThree.PartTwo.Sec6.isSolvable_sup_of_le_normalizer hJT hTsol hJsol
    have hW3 : ¬ 3 ∣ Nat.card (T ⊔ J : Subgroup G) := by
      rw [sup_comm]
      exact CFSG.RankThree.PartTwo.Sec6.not_dvd_card_sup Nat.prime_three hJT hJ3 hT3
    exact (le_sup_right : J ≤ T ⊔ J).trans
      (CFSG.RankThree.PartTwo.Sec6.le_theta_of_normal hWZ hZN hWsol hW3)
  set f : Y →* Z ⧸ aschbacherSolvableCore 3 Z :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 Z)).comp (Subgroup.inclusion hYZ) with hfdef
  set g : Y →* K ⧸ aschbacherSolvableCore 3 K :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp (Subgroup.inclusion hYK) with hgdef
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 Z) q
    have hz : (z : G) ∈ (Y : Set G) * (inSubgroup (aschbacherSolvableCore 3) Z : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y _ hYN]
      exact hZcov z.2
    obtain ⟨y, hy, t, ht, hyt⟩ := Set.mem_mul.mp hz
    obtain ⟨t', ht', rfl⟩ := ht
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have e : (Subgroup.inclusion hYZ ⟨y, hy⟩)⁻¹ * z = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hyt]
      simp
    rw [e]
    exact ht'
  have hker : g.ker ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    rw [hgdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    rw [hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hθK : (y : G) ∈ inSubgroup (aschbacherSolvableCore 3) K :=
      (mem_inSubgroup_theta_iff_of_le (Subgroup.inclusion hYK y)).mpr hy
    exact (mem_inSubgroup_theta_iff_of_le (Subgroup.inclusion hYZ y)).mp
      (hJθ (Subgroup.mem_inf.mpr ⟨y.2, hθK⟩))
  have hne : g.range ≠ ⊤ := by
    intro htop
    obtain ⟨k, hkK, hk⟩ : ∃ k ∈ K,
        k⁻¹ * (a * k * a⁻¹) ∉ inSubgroup (aschbacherSolvableCore 3) K := by
      by_contra hcon
      refine ha (CFSG.RankThree.PartTwo.Sec6.mem_thetaQuotCentralizer_iff.mpr
        ⟨haK, fun l hl => ?_⟩)
      by_contra hl'
      exact hcon ⟨l, hl, hl'⟩
    have hmem : (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hkK⟩ :
        K ⧸ aschbacherSolvableCore 3 K) ∈ g.range := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
    rw [hgdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hy
    have ht' : (y : G)⁻¹ * k ∈ inSubgroup (aschbacherSolvableCore 3) K :=
      (mem_inSubgroup_theta_iff_of_le _).mpr hy
    have hyC : (y : G) * a = a * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYC y.2)
    have hay : a * (y : G) * a⁻¹ = (y : G) := by
      rw [← hyC, mul_inv_cancel_right]
    have hay' : a * (y : G)⁻¹ * a⁻¹ = (y : G)⁻¹ := by
      rw [show a * (y : G)⁻¹ * a⁻¹ = (a * (y : G) * a⁻¹)⁻¹ by group, hay]
    have key : k⁻¹ * (a * k * a⁻¹) = ((y : G)⁻¹ * k)⁻¹ * (a * ((y : G)⁻¹ * k) * a⁻¹) := by
      rw [show a * ((y : G)⁻¹ * k) * a⁻¹ = (a * (y : G)⁻¹ * a⁻¹) * (a * k * a⁻¹) by group,
        hay']
      group
    have hat : a * ((y : G)⁻¹ * k) * a⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThree.PartTwo.Sec6.normalizer_le_normalizer_theta K haK) _).mp ht'
    apply hk
    rw [key]
    exact (inSubgroup (aschbacherSolvableCore 3) K).mul_mem
      ((inSubgroup (aschbacherSolvableCore 3) K).inv_mem ht') hat
  have hidx1 : Nat.card (Z ⧸ aschbacherSolvableCore 3 Z) = f.ker.index := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm
  have hidx2 : g.ker.index = Nat.card g.range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have hlt : Nat.card g.range < Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
    have h := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
    rwa [Subgroup.card_top] at h
  calc Nat.card (Z ⧸ aschbacherSolvableCore 3 Z) = f.ker.index := hidx1
    _ ≤ g.ker.index := Subgroup.index_antitone hker
    _ = Nat.card g.range := hidx2
    _ < Nat.card (K ⧸ aschbacherSolvableCore 3 K) := hlt

end CFSG.RankThree.PartTwo.Sec21.HeringHull
