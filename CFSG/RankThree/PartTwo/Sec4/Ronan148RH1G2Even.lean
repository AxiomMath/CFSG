module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425G2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11

namespace G2Even

theorem odd_card_center_sl3 {F : Type} [Field F] [Finite F] :
    Odd (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    intro A
    refine ⟨1, ?_⟩
    obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp A.2
    have hr3 : r ^ 3 = 1 := by simpa using hr
    have h1 : ((A : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
      rw [← hA, ← map_pow, hr3, map_one]
    apply Subtype.ext
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, h1]
    rfl
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)


variable {F : Type} [Field F] [Finite F]

theorem good427_onFree_threeA
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 4 ≤ f) (hev : Even f)
    {z : adjointGroup .G2 F} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    Good427 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) ∧
      OnFree (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) z := by
  have hmod : 2 ^ f % 3 = 1 := by
    obtain ⟨m, rfl⟩ := hev
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have h31 : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  obtain ⟨m, φ, hφinj, hNC, hcomm⟩ := Ronan148H.exists_sl3_threeA h31 hzS hz3 hz1
  set x : adjointGroup .G2 F := m * z * m⁻¹ with hx
  let eR : Matrix.SpecialLinearGroup (Fin 3) F ≃* φ.range := MonoidHom.ofInjective hφinj
  have hRq : IsQuasisimple φ.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv eR
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  have hodd : Odd (Nat.card (Subgroup.center φ.range)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eR).toEquiv]
    exact odd_card_center_sl3
  have hcard : Nat.card φ.range = 2 ^ f * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) * 2 ^ (2 * f) := by
    rw [← Nat.card_congr eR.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL,
      CFSG.Open.StatedAPI.card_statedSL_three, hF]
    ring
  have h12 : 2 ^ (3 * f) ∣ Nat.card φ.range := by
    rw [← Nat.card_congr eR.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL,
      CFSG.Open.StatedAPI.card_statedSL_three, hF, ← pow_mul, mul_comm f 3]
    exact dvd_mul_right _ _
  have h2_12 : 2 ^ 12 ∣ Nat.card φ.range := (pow_dvd_pow 2 (by omega)).trans h12
  have hle : ∀ K : Subgroup (adjointGroup .G2 F),
      K ≤ Subgroup.centralizer ({x} : Set (adjointGroup .G2 F)) → Group.IsPerfect K →
        K ≤ φ.range := fun K hKC hKp =>
    Ronan148H.le_of_commutators_mem hKC (Subgroup.isPerfect_iff.mp hKp) hcomm
  obtain ⟨hG, hO⟩ := good427_onFree_of_perfect_le_qs (y := x) hNC hle hRq hodd
    (fun h60 => by rw [h60] at h2_12; norm_num at h2_12)
    (fun hON => by rw [hON] at h2_12; norm_num at h2_12)
  refine ⟨Good427.of_isConj (isConj_iff.mpr ⟨m, rfl⟩).symm hG, ?_⟩
  have h1 := hO.map (MulAut.conj m⁻¹)
  have he : (MulAut.conj m⁻¹) x = z := by
    rw [MulAut.conj_apply, hx]
    group
  rwa [he] at h1

theorem good427_onFree_threeB
    [CharP F 2] (h16 : 16 ≤ Nat.card F)
    {z : adjointGroup .G2 F} (hzM : z ∈ KS11Lie4Proof.g2LongSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    Good427 (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) ∧
      OnFree (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) z := by
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  obtain ⟨hcomm, -⟩ := KS11Lie4Proof.g2ThreeBCent_holds F hchar (by omega) z hzM hz3 hz1
  obtain ⟨hs, hna, hcard⟩ := G2.short_simple (F := F) (by omega)
  haveI := hs
  refine good427_onFree_of_derived_simple hz1 hna ?_
    (fun s hs' => KS11Lie4Proof.g2Short_commute_g2Long hs' hzM) hcomm
  rw [hcard]
  intro h
  have h256 : 256 ≤ Nat.card F ^ 2 := by nlinarith
  have : 16 * 255 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h16 (by omega)
  omega

theorem good427_onFree_inner
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 4 ≤ f) (hev : Even f)
    {x : adjointGroup .G2 F} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Good427 (Subgroup.centralizer ({x} : Set (adjointGroup .G2 F))) ∧
      OnFree (Subgroup.centralizer ({x} : Set (adjointGroup .G2 F))) x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  have h16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds F hchar (by omega) x hx3 hx1
  have hz3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hz1 : g * x * g⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
  have hz : Good427 (Subgroup.centralizer ({g * x * g⁻¹} : Set (adjointGroup .G2 F))) ∧
      OnFree (Subgroup.centralizer ({g * x * g⁻¹} : Set (adjointGroup .G2 F))) (g * x * g⁻¹) := by
    rcases hg with hS | hM
    · exact good427_onFree_threeA hF hf hev hS hz3 hz1
    · exact good427_onFree_threeB h16 hM hz3 hz1
  refine ⟨Good427.of_isConj (isConj_iff.mpr ⟨g⁻¹, by group⟩) hz.1, ?_⟩
  have h1 := hz.2.map (MulAut.conj g⁻¹)
  have he : (MulAut.conj g⁻¹) (g * x * g⁻¹) = x := by
    rw [MulAut.conj_apply]
    group
  rwa [he] at h1

end G2Even

namespace G2Even

section Field


variable {F : Type} [Field F] [Finite F]

theorem good427_field
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    {α : MulAut (adjointGroup .G2 F)} (hα3 : α ^ 3 = 1)
    (hout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α) : Good427 (Sec4.autFix α) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
  obtain ⟨φ, hφ, k, hαk⟩ :=
    CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hchar3 h4 hα3 hout
  obtain ⟨h3f, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF
      hφ
  obtain ⟨m, rfl⟩ := h3f
  have hm1 : 1 ≤ m := by omega
  have hcard : Nat.card (fixSubfield φ) = 2 ^ m := by
    have h := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow φ
    rw [hφ, hF, show 2 ^ (3 * m) = (2 ^ m) ^ 3 by rw [← pow_mul, mul_comm]] at h
    exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
  have hfixeq : Sec4.autFix (CFSG.RankThree.PartTwo.KFacts.g2FieldHom F φ) =
      (CFSG.RankThree.PartTwo.KFacts.g2Incl φ).range := by
    ext h
    rw [Sec4.mem_autFix, CFSG.RankThree.PartTwo.KFacts.mem_range_g2Incl_iff hchar φ]
  rw [hαk, autFix_conj_eq_map, hfixeq]
  refine Good427.map_mulEquiv _ ?_
  set E := (CFSG.RankThree.PartTwo.KFacts.g2Incl φ).range with hE
  let eE : adjointGroup .G2 (fixSubfield φ) ≃* E :=
    MonoidHom.ofInjective (CFSG.RankThree.PartTwo.KFacts.g2Incl_injective φ)
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hm2
  ·
    intro K hKE hKq _ hA5
    have hcardE : Nat.card E = 12096 := by
      rw [← Nat.card_congr eE.toEquiv,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hcard]
      rfl
    obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hA5
    have h5 : 5 ∣ Nat.card E := by
      refine (Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hKE))
      rw [ha]
      exact Dvd.dvd.mul_right (by norm_num) _
    rw [hcardE] at h5
    norm_num at h5
  · have h3k : 3 ≤ Nat.card (fixSubfield φ) := by
      rw [hcard]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hsimp := CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 h3k
    haveI : IsSimpleGroup E := eE.symm.isSimpleGroup
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield φ)
      h3k
    refine good427_of_le_simple le_rfl ?_ ?_ fun _ hKC _ => hKC
    · obtain ⟨-, -, a, b, hab⟩ := hq
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      refine ⟨eE a', eE b', fun h => hab ?_⟩
      have h1 : a' * b' = b' * a' := eE.injective (by rw [map_mul, map_mul, h])
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
    · rw [← Nat.card_congr eE.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
        hcard]
      intro h
      unfold CFSG.Open.ordG2 at h
      have hq4 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      have hA : 4096 ≤ (2 ^ m) ^ 6 := by
        calc 4096 = 4 ^ 6 := by norm_num
          _ ≤ (2 ^ m) ^ 6 := Nat.pow_le_pow_left hq4 6
      have hC : 16 ≤ (2 ^ m) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hq4 2
      have : 4096 * 1 * 1 ≤ (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hA (by omega)) (by omega)
      omega

theorem noCfgS427_g2
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 4 ≤ f) (hev : Even f) :
    NoCfgS427 (adjointGroup .G2 F) := by
  intro α hα3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 h1
  by_cases hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut α
  · obtain ⟨x, rfl, hx3, hx1⟩ := RonanKChevTwo.exists_conj_of_isInnerAut
      (RonanKChevTwo.conj_injective_of_center_eq_bot center_adjointGroup_eq_bot) hord hin
    rw [autFix_conj]
    exact (good427_onFree_inner hF hf hev hx3 hx1).1
  · exact good427_field hF (by omega) hα3 hin

end Field

end G2Even

open G2Even

section Rows


theorem rowOf427_g2_even
    : ∀ q : TauCeti.PrimePower, q.p = 2 → Even q.exponent →
    4 ≤ q.exponent → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowOf427 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 hev hf4 hq S _ _ hs hna ⟨eSX⟩
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 eSX
  rw [hq2] at hF
  let eG : S ≃* adjointGroup .G2 F := eA.trans (Ronan148H.adjointQuotientEquivG2 F)
  refine row427_of_noCfg_on ?_ ?_ ?_
  · intro L _ _ _ hL _ ⟨e'⟩
    exact G2.center_eq_bot_g2 (by rw [hF]; calc 5 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf4) hL ((e'.trans eSX).trans
        (eSX.symm.trans eG))
  · intro S' _ _ ⟨e'⟩
    exact NoCfgS427.of_mulEquiv (e'.trans eG) (noCfgS427_g2 hF hf4 hev)
  · intro S' _ _ ⟨e'⟩ y hy1 hy3
    have hx3 : (e'.trans eG) y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hx1 : (e'.trans eG) y ≠ 1 := by
      rw [Ne, map_eq_one_iff _ (e'.trans eG).injective]
      exact hy1
    have h1 := (good427_onFree_inner hF hf4 hev hx3 hx1).2.map (e'.trans eG).symm
    rwa [MulEquiv.symm_apply_apply] at h1

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
