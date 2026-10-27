module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofThree
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res5ProofLin
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
public import CFSG.RankThree.PartTwo.Sec6.Item65UsedTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)

open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)

open scoped Pointwise

namespace Item2130Res5Proof

theorem exists_two_pow_of_sq_ne {H Q : Type*} [Group H] [Finite H] [Group Q] (π : H →* Q)
    (hπ : Function.Surjective π) {x : Q} (hx2 : x ^ 2 ≠ 1) (hx4 : x ^ 4 = 1) :
    ∃ (h : H) (a : ℕ), h ^ 2 ^ a = 1 ∧ π h ^ 2 ≠ 1 := by
  obtain ⟨h₀, rfl⟩ := hπ x
  obtain ⟨a, r, hr, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos h₀).ne' 2 (by norm_num)
  refine ⟨h₀ ^ r, a, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · obtain ⟨t, rfl⟩ : Odd r := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hr)
    rw [map_pow, ← pow_mul, show (2 * t + 1) * 2 = 4 * t + 2 by ring, pow_add, pow_mul, hx4,
      one_pow, one_mul]
    exact hx2

theorem card_eq_card_range_mul_card_ker {H Q : Type*} [Group H] [Group Q] (f : H →* Q) :
    Nat.card H = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

variable {K : Type} [Field K] [CharP K 2]

theorem sq_eq_one_of_conj {M : Type*} [Group M] (ι : M →* GL (Fin 3) K)
    (hι : Function.Injective ι) {β : MulAut M} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    {A : GL (Fin 3) K} (hβA : ∀ s, ι (β s) = A * ι s * A⁻¹) {s : M} (hs : β s = s) {a : ℕ}
    (hsa : s ^ 2 ^ a = 1) : s ^ 2 = 1 := by
  by_contra hs2
  have hAg : A * ι s = ι s * A := by
    have h1 := hβA s
    rw [hs] at h1
    calc A * ι s = A * ι s * A⁻¹ * A := by group
      _ = ι s * A := by rw [← h1]
  have hg : ι s ^ 2 ^ a = 1 := by rw [← map_pow, hsa, map_one]
  have hg2 : ι s ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro h
    exact hs2 (hι (h.trans (map_one ι).symm))
  obtain ⟨α, hα⟩ := exists_pow_four_eq_smul_one hAg hg hg2
  have hcen : ∀ X : GL (Fin 3) K, A ^ 4 * X = X * A ^ 4 := by
    intro X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hα, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hpow : ∀ k : ℕ, ∀ s', ι ((β ^ k) s') = A ^ k * ι s' * (A ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s'; simp
    | succ k ih =>
      intro s'
      rw [pow_succ', MulAut.mul_apply, hβA, ih, pow_succ']
      group
  have hβ4 : β ^ 4 = 1 := by
    ext s'
    apply hι
    rw [hpow 4 s', MulAut.one_apply, hcen, mul_inv_cancel_right]
  apply hβ1
  calc β = β ^ 4 * (β ^ 3)⁻¹ := by group
    _ = 1 := by rw [hβ4, hβ3, inv_one, mul_one]

end Item2130Res5Proof

open Item2130Res5Proof

variable {G : Type} [Group G] [Finite G]

namespace Item2130Res5Proof

theorem card_le_of_mem_thetaQuotCentralizer {Y I : Subgroup G} {c : G}
    (hcC : c ∈ Sec4.thetaQuotCentralizer Y) (hc3 : c ^ 3 = 1) (hYq : IsQuasisimple (lBar Y))
    (hZ : Nat.card (Subgroup.center (lBar Y)) = 3)
    (hI : I ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G))) :
    Nat.card (lBar Y) ≤ 3 * Nat.card (lBar I) ∨ Nat.card (lBar I) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hIW, hI'⟩ := mem_thetaComponentsIn_iff.mp hI
  set W := Y ⊓ Subgroup.centralizer ({c} : Set G) with hW
  have hWY : W ≤ Y := inf_le_left
  have hIY : I ≤ Y := hIW.trans hWY
  set θY := aschbacherSolvableCore 3 Y with hθY
  set π := QuotientGroup.mk' θY with hπ
  set ρ : W →* lBar Y := π.comp (Subgroup.inclusion hWY) with hρ
  have hρs : Function.Surjective ρ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective θY z
    have hy : (y : G) ∈ (W : Set G) * (inSubgroup (aschbacherSolvableCore 3) Y : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right W _
        (hWY.trans (Sec6.le_normalizer_theta Y))]
      exact Sec6.le_inf_centralizer_sup_theta hcC hc3 y.2
    obtain ⟨w, hw, t, ht, hwt⟩ := hy
    refine ⟨⟨w, hw⟩, ?_⟩
    change π (Subgroup.inclusion hWY ⟨w, hw⟩) = π y
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t', ht', rfl⟩ := ht
    have : (Subgroup.inclusion hWY ⟨w, hw⟩)⁻¹ * y = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hwt]
      simp
    rw [this]
    exact ht'
  set f : I →* lBar Y := π.comp (Subgroup.inclusion hIY) with hf
  have hrange : f.range = (I.subgroupOf W).map ρ := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i, hIW i.2⟩, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, Subgroup.mem_subgroupOf.mp hw⟩, rfl⟩
  have hsn : f.range.IsSubnormal := by
    rw [hrange]
    exact hI'.2.1.map hρs
  have hker : f.ker ≤ aschbacherSolvableCore 3 I := by
    intro i hi
    have h1 : Subgroup.inclusion hIY i ∈ θY := by
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hi
      exact hi
    have h2 : (i : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y ⊓ I :=
      ⟨⟨_, h1, rfl⟩, i.2⟩
    obtain ⟨t, ht, hti⟩ := Item2130Res4Proof.inf_theta_le_theta hIY h2
    have : t = i := Subtype.ext hti
    rwa [← this]
  have hcardI : Nat.card I = Nat.card f.range * Nat.card f.ker :=
    card_eq_card_range_mul_card_ker f
  have hcardIbar : Nat.card I = Nat.card (lBar I) * Nat.card (aschbacherSolvableCore 3 I) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hkerle : Nat.card f.ker ≤ Nat.card (aschbacherSolvableCore 3 I) :=
    Subgroup.card_le_of_le hker
  have hTpos : 0 < Nat.card (aschbacherSolvableCore 3 I) := Nat.card_pos
  rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hYq hsn with hc | htop
  ·
    right
    have h3 : Nat.card f.range ≤ 3 := (Subgroup.card_le_of_le hc).trans hZ.le
    have h4 : Nat.card (lBar I) * Nat.card (aschbacherSolvableCore 3 I) ≤
        3 * Nat.card (aschbacherSolvableCore 3 I) := by
      rw [← hcardIbar, hcardI]
      exact Nat.mul_le_mul h3 hkerle
    exact Nat.le_of_mul_le_mul_right h4 hTpos
  ·
    left
    have hfs : Function.Surjective f := MonoidHom.range_eq_top.mp htop
    set T := aschbacherSolvableCore 3 I with hT
    set X := T.map f with hX
    have hXn : X.Normal := Subgroup.Normal.map inferInstance f hfs
    have hXc : X ≤ Subgroup.center (lBar Y) := by
      rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hYq X with h | h
      · exact h
      · exfalso
        have hTs : Group.IsSolvable T :=
          (solvable_prime_complement_core_characterization (H := ↥I) Nat.prime_three).1
        have hfT : Function.Surjective (f.comp T.subtype) := by
          intro z
          have hz : z ∈ X := by rw [h]; exact Subgroup.mem_top z
          obtain ⟨t, ht, rfl⟩ := hz
          exact ⟨⟨t, ht⟩, rfl⟩
        have hsol : Group.IsSolvable (lBar Y) := Group.isSolvable_of_surjective hfT
        have : Nontrivial (lBar Y) := CFSG.LocalCores.isQuasisimple_nontrivial hYq
        have := hYq.1
        exact Group.IsPerfect.not_isSolvable (lBar Y) hsol
    have hX3 : Nat.card X ≤ 3 := (Subgroup.card_le_of_le hXc).trans hZ.le
    have hcardT : Nat.card T = Nat.card X * Nat.card f.ker := by
      have h1 := card_eq_card_range_mul_card_ker (f.comp T.subtype)
      have hr : (f.comp T.subtype).range = X := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have hk : Nat.card (f.comp T.subtype).ker = Nat.card f.ker := by
        have hk' : (f.comp T.subtype).ker = f.ker.subgroupOf T := by
          ext t
          simp [Subgroup.mem_subgroupOf]
        rw [hk']
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
      rw [h1, hr, hk]
    have hrange_card : Nat.card f.range = Nat.card (lBar Y) := by
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have h5 : Nat.card (lBar Y) * Nat.card f.ker = Nat.card (lBar I) * Nat.card X *
        Nat.card f.ker := by
      rw [← hrange_card, ← hcardI, hcardIbar, hcardT, mul_assoc]
    have h6 : Nat.card (lBar Y) = Nat.card (lBar I) * Nat.card X :=
      Nat.eq_of_mul_eq_mul_right hkpos h5
    rw [h6, mul_comm 3]
    exact Nat.mul_le_mul_left _ hX3

theorem three_mul_order_lt {q : ℕ} (hq : 2 ≤ q) (s : Bool) :
    3 * (q ^ 3 * (q ^ 2 - 1) * (cond s (q ^ 3 - 1) (q ^ 3 + 1))) <
      (q ^ 3) ^ 3 * ((q ^ 3) ^ 2 - 1) * (cond s ((q ^ 3) ^ 3 - 1) ((q ^ 3) ^ 3 + 1)) ∧
    3 < q ^ 3 * (q ^ 2 - 1) * (cond s (q ^ 3 - 1) (q ^ 3 + 1)) := by
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hq3 : 8 ≤ q ^ 3 := by nlinarith
  have hq6 : 64 ≤ q ^ 6 := by nlinarith
  have h9 : 64 * q ^ 3 ≤ (q ^ 3) ^ 3 := by
    rw [show (q ^ 3) ^ 3 = q ^ 6 * q ^ 3 by ring]
    exact Nat.mul_le_mul_right _ hq6
  have h6 : q ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
  have h33 : q ^ 3 ≤ (q ^ 3) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hc : 7 ≤ cond s (q ^ 3 - 1) (q ^ 3 + 1) := by
    cases s <;> simp <;> omega
  have hcle : cond s (q ^ 3 - 1) (q ^ 3 + 1) ≤ cond s ((q ^ 3) ^ 3 - 1) ((q ^ 3) ^ 3 + 1) := by
    cases s <;> simp <;> omega
  have hpos : 0 < q ^ 3 * (q ^ 2 - 1) * (cond s (q ^ 3 - 1) (q ^ 3 + 1)) := by
    have : 0 < q ^ 2 - 1 := by omega
    positivity
  refine ⟨?_, ?_⟩
  · calc 3 * (q ^ 3 * (q ^ 2 - 1) * (cond s (q ^ 3 - 1) (q ^ 3 + 1))) <
          64 * (q ^ 3 * (q ^ 2 - 1) * (cond s (q ^ 3 - 1) (q ^ 3 + 1))) := by omega
      _ = (64 * q ^ 3) * (q ^ 2 - 1) * (cond s (q ^ 3 - 1) (q ^ 3 + 1)) := by ring
      _ ≤ (q ^ 3) ^ 3 * ((q ^ 3) ^ 2 - 1) * (cond s ((q ^ 3) ^ 3 - 1) ((q ^ 3) ^ 3 + 1)) := by
          gcongr
  · calc 3 < 8 * 3 * 7 := by norm_num
      _ ≤ q ^ 3 * (q ^ 2 - 1) * (cond s (q ^ 3 - 1) (q ^ 3 + 1)) := by
          gcongr; omega

end Item2130Res5Proof

section Certs


theorem kSL3PiCubeField_holds : KSL3PiCubeField := by
  intro G _ _ Y c I m hm hc3 hcN hI hY hIm
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  obtain ⟨hIW, -⟩ := mem_thetaComponentsIn_iff.mp hI
  have hIY : I ≤ Y := hIW.trans inf_le_left
  by_cases hcC : c ∈ Sec4.thetaQuotCentralizer Y
  · exfalso
    have hYq : IsQuasisimple (lBar Y) :=
      KFacts.isQuasisimple_of_isSLThreePiAt_two_pow (by omega) hY
    have hZ : Nat.card (Subgroup.center (lBar Y)) = 3 :=
      KFacts.card_center_of_isSLThreePiAt_two_pow (by omega) hY
    have hle := card_le_of_mem_thetaQuotCentralizer hcC hc3' hYq hZ hI
    have hq2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hcube : 2 ^ (3 * m) = (2 ^ m) ^ 3 := by rw [← pow_mul, mul_comm]
    have hmod : 2 ^ (3 * m) % 3 = 2 ^ m % 3 := by
      rw [hcube, Nat.pow_mod]
      have : 2 ^ m % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases h : 2 ^ m % 3 <;> simp_all
    rcases card_of_isSLThreePiAt_two_pow (by omega : 1 ≤ 3 * m) hY with ⟨hY3, hYc⟩ | ⟨hY3, hYc⟩ <;>
      rcases card_of_isSLThreePiAt_two_pow hm hIm with ⟨hI3, hIc⟩ | ⟨hI3, hIc⟩
    · obtain ⟨h1, h2⟩ := three_mul_order_lt hq2 true
      rw [hYc, hIc, hcube] at hle
      simp only [Bool.cond_true] at h1 h2
      omega
    · omega
    · omega
    · obtain ⟨h1, h2⟩ := three_mul_order_lt hq2 false
      rw [hYc, hIc, hcube] at hle
      simp only [Bool.cond_false] at h1 h2
      omega
  have hθ1 : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) ≠ 1 := by
    intro h
    apply hcC
    exact ⟨⟨c, hcN⟩, MonoidHom.mem_ker.mpr h, rfl⟩
  obtain ⟨x, hx2, hx4⟩ := exists_sq_ne_one_of_isSLThreePiAt hm hIm
  obtain ⟨i, a, hia, hi2⟩ := exists_two_pow_of_sq_ne
    (QuotientGroup.mk' (aschbacherSolvableCore 3 I)) (QuotientGroup.mk'_surjective _) hx2 hx4
  set ybar : lBar Y := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (Subgroup.inclusion hIY i)
    with hybar
  have hyfix : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) ybar = ybar := by
    rw [hybar, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change c * (i : G) * c⁻¹ = i
    have hic : (i : G) ∈ Subgroup.centralizer ({c} : Set G) := (hIW i.2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hic
    rw [← hic, mul_inv_cancel_right]
  have hya : ybar ^ 2 ^ a = 1 := by rw [hybar, ← map_pow, ← map_pow, hia, map_one, map_one]
  have hy2 : ybar ^ 2 ≠ 1 := by
    intro h
    apply hi2
    rw [hybar, ← map_pow, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h1 : ((i ^ 2 : I) : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y ⊓ I :=
      ⟨⟨_, h, rfl⟩, (i ^ 2).2⟩
    obtain ⟨t, ht, hti⟩ := Item2130Res4Proof.inf_theta_le_theta hIY h1
    have : t = i ^ 2 := Subtype.ext hti
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← this]
    exact ht
  obtain ⟨F, _, _, ⟨hF, -, ⟨e₀⟩⟩ | ⟨hF, -, ⟨e₀⟩⟩⟩ := hY
  ·
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 3 * m)
      (by rw [← Nat.card_eq_fintype_card, hF])
    set e := e₀.trans (Sec4.slPiTrueEquiv (2 ^ (3 * m)) F) with he
    set β := KFacts.inducedAutHom Y e ⟨c, hcN⟩ with hβ
    have hβ3 : β ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one Y e hcN hc3'
    have hβ1 : β ≠ 1 := by
      intro h
      apply hθ1
      rw [hβ, KFacts.inducedAutHom_apply] at h
      exact (MulAut.congr e).injective (h.trans (map_one _).symm)
    have hs : β (e ybar) = e ybar := by
      rw [hβ, KFacts.inducedAutHom_apply, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hyfix]
    have hsa : (e ybar) ^ 2 ^ a = 1 := by rw [← map_pow, hya, map_one]
    have hs2 : (e ybar) ^ 2 ≠ 1 := by
      rw [← map_pow]
      intro h
      exact hy2 (e.injective (h.trans (map_one e).symm))
    have hconj : ∀ A : GL (Fin 3) F, β = slConjugation 3 F A → False := by
      intro A hA
      refine hs2 (sq_eq_one_of_conj Matrix.SpecialLinearGroup.toGL
        Matrix.SpecialLinearGroup.toGL_injective hβ3 hβ1 (A := A) (fun s => ?_) hs hsa)
      rw [hA, toGL_slConjugation]
    rcases KFacts.inducesKindSL_inner_or_diagonal_or_field Y le_rfl hcN hc3' e with h | h | h
    · exfalso
      obtain ⟨A, hA⟩ := KFacts.exists_eq_slConjugation_of_descendAut_mem
        ((KFacts.stdPinnedPSL 3 F).inn_le h)
      exact hconj A hA
    · exfalso
      obtain ⟨A, hA⟩ := KFacts.exists_eq_slConjugation_of_descendAut_mem h.1
      exact hconj A hA
    · exact .sl 3 F le_rfl ⟨e, hcN, h⟩
  ·
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * (3 * m))
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * m) F :=
      ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
    have hq2 : 2 < 2 ^ (3 * m) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
    set e := e₀.trans (Sec4.slPiFalseEquiv 2 (3 * m) F) with he
    set β := KFacts.inducedAutHom Y e ⟨c, hcN⟩ with hβ
    have hβ3 : β ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one Y e hcN hc3'
    have hβ1 : β ≠ 1 := by
      intro h
      apply hθ1
      rw [hβ, KFacts.inducedAutHom_apply] at h
      exact (MulAut.congr e).injective (h.trans (map_one _).symm)
    have hs : β (e ybar) = e ybar := by
      rw [hβ, KFacts.inducedAutHom_apply, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hyfix]
    have hsa : (e ybar) ^ 2 ^ a = 1 := by rw [← map_pow, hya, map_one]
    have hs2 : (e ybar) ^ 2 ≠ 1 := by
      rw [← map_pow]
      intro h
      exact hy2 (e.injective (h.trans (map_one e).symm))
    have hconj : ∀ τ, τ ∈ (KFacts.stdPinnedPSU3 hU).inndiag →
        τ = MulAut.congr (KFacts.suCenterEquiv hU hq2) (KFacts.centerDescend _ β) → False := by
      rintro _ ⟨A, rfl⟩ hA
      have hβA : β = KFacts.suConj hU A :=
        KFacts.eq_of_centerDescend_eq hU hq2 (by rw [Sec4.congr_centerDescend_suConj, hA])
      refine hs2 (sq_eq_one_of_conj (unitarySU 2 (3 * m) F 3).subtype
        Subtype.val_injective hβ3 hβ1 (A := (A : GL (Fin 3) F)) (fun s => ?_) hs hsa)
      rw [hβA]
      exact KFacts.coe_suConj A s
    rcases KFacts.inducesKindSU3_inner_or_diagonal_or_field (h := hU) Y hq2 hcN hc3' e with
      h | h | h
    · exact (hconj _ ((KFacts.stdPinnedPSU3 hU).inn_le h) rfl).elim
    · exact (hconj _ h.1 rfl).elim
    · exact .su3 hU hq2 ⟨e, hcN, h⟩

end Certs

end CFSG.RankThree.PartTwo.Sec21
