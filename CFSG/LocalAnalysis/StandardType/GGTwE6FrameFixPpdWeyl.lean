module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusActPow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagExcPpd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.TwE6FrameFixPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley.RootCertificate
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.StandardType
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

private theorem factor_sq {F : Type} [CommRing F] (x : F) : (x - 1) * (x + 1) = x ^ 2 - 1 := by ring

private theorem factor_six {F : Type} [CommRing F] (x : F) :
    (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) = x ^ 6 + 1 := by ring

private theorem factor_D12 {F : Type} [CommRing F] (x : F) :
    1 - x + x ^ 3 - x ^ 5 + x ^ 6 = (x ^ 2 - x + 1) * (x ^ 4 - x ^ 2 + 1) := by ring

private theorem pow_four_sq {F : Type} [CommRing F] (x : F) : x ^ 4 = (x ^ 2) ^ 2 := by ring

private theorem dvd_D_twelve {r q : ℕ} (hr : r.Prime) (hq : orderOf (q : ZMod r) = 12) :
    (r : ℤ) ∣ 1 - (q : ℤ) + (q : ℤ) ^ 3 - (q : ℤ) ^ 5 + (q : ℤ) ^ 6 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h12 : (q : ZMod r) ^ 12 = 1 := by
    have h := pow_orderOf_eq_one (q : ZMod r)
    rwa [hq] at h
  have h6ne : (q : ZMod r) ^ 6 ≠ 1 := by
    intro h
    have hdvd : orderOf (q : ZMod r) ∣ 6 := orderOf_dvd_iff_pow_eq_one.2 h
    rw [hq] at hdvd
    omega
  have h6 : (q : ZMod r) ^ 6 = -1 := by
    have hsq : ((q : ZMod r) ^ 6) ^ 2 = 1 := by
      rw [← pow_mul, show 6 * 2 = 12 by norm_num, h12]
    have hfac : ((q : ZMod r) ^ 6 - 1) * ((q : ZMod r) ^ 6 + 1) = 0 := by
      rw [factor_sq, hsq, sub_self]
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h6ne
    · exact add_eq_zero_iff_eq_neg.mp h
  have h2ne : (q : ZMod r) ^ 2 + 1 ≠ 0 := by
    intro h
    have h4 : (q : ZMod r) ^ 4 = 1 := by
      rw [pow_four_sq, add_eq_zero_iff_eq_neg.mp h]
      exact neg_one_sq (R := ZMod r)
    have hdvd : orderOf (q : ZMod r) ∣ 4 := orderOf_dvd_iff_pow_eq_one.2 h4
    rw [hq] at hdvd
    omega
  have h4 : (q : ZMod r) ^ 4 - (q : ZMod r) ^ 2 + 1 = 0 := by
    have hfac : ((q : ZMod r) ^ 2 + 1) *
        ((q : ZMod r) ^ 4 - (q : ZMod r) ^ 2 + 1) = 0 := by
      rw [factor_six, h6]
      exact neg_add_cancel 1
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd h h2ne
    · exact h
  have hD : ((1 - (q : ℤ) + (q : ℤ) ^ 3 - (q : ℤ) ^ 5 + (q : ℤ) ^ 6 : ℤ) :
      ZMod r) = 0 := by
    push_cast
    rw [factor_D12, h4, mul_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hD

private def f3 : Fin Tag.E6.rank := ⟨3, by decide⟩
private def f4 : Fin Tag.E6.rank := ⟨4, by decide⟩
private def f1 : Fin Tag.E6.rank := ⟨1, by decide⟩

private def b6 : Fin Tag.E6.rank → ZMod 3 := vec3 (τ := .E6) e6ThreeStab6.vec

private theorem b6_f3 : b6 f3 = 0 := by decide +kernel
private theorem b6_f4 : b6 f4 = 0 := by decide +kernel

private def row61 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ := fun k l =>
  ([[0, 1, 0, 1, 1, 1], [1, 1, 2, 2, 2, 1], [0, -1, -1, -2, -1, -1],
    [-1, -1, -1, -1, -1, 0], [1, 1, 1, 1, 0, 0], [0, 0, 0, 1, 1, 0]].getD (k : ℕ) []).getD (l : ℕ) 0

private theorem row61_spec : ∀ k : Fin Tag.E6.rank,
    e6Certificate.tupleVec [33, 35, 71, 28, 4, 3]
      (reflect .E6 f4 (reflect .E6 f3 (Pi.single k 1))) = row61 k := by
  intro k
  fin_cases k <;> decide +kernel

private def v61 (q : ℤ) : Fin Tag.E6.rank → ℤ := fun k =>
  [1 - q + q ^ 2 - q ^ 4 + q ^ 5, -q + 2 * q ^ 2 - q ^ 3,
    -q ^ 3 + 2 * q ^ 4 - q ^ 5, q - 2 * q ^ 2 + 2 * q ^ 3 - q ^ 4,
    -q + q ^ 2 - q ^ 3, q ^ 3 - q ^ 4 + q ^ 5].getD (k : ℕ) 0

private theorem v61_spec (q : ℤ) : ∀ k : Fin Tag.E6.rank,
    v61 q k + q * (∑ l : Fin Tag.E6.rank, row61 k l * v61 q l) =
      if (k : ℕ) = 0 then 1 - q + q ^ 3 - q ^ 5 + q ^ 6 else 0 := by
  intro k
  change v61 q k + q * (∑ l : Fin 6, row61 k l * v61 q l) =
    if (k : ℕ) = 0 then 1 - q + q ^ 3 - q ^ 5 + q ^ 6 else 0
  rw [Fin.sum_univ_six]
  fin_cases k <;> simp [v61, row61] <;> ring

private theorem zpow_ne_one_of_not_dvd {K : Type} [Field K] {r : ℕ}
    {ζ : Kˣ} (hζ : orderOf ζ = r) {a : ℤ} (ha : ¬ (r : ℤ) ∣ a) : ζ ^ a ≠ 1 := by
  intro h
  refine ha ?_
  have hd : (orderOf ζ : ℤ) ∣ a := (orderOf_dvd_iff_zpow_eq_one).2 h
  rwa [hζ] at hd

private theorem weylAct_zpow_eq_of_dvd {K : Type} [Field K] {τ : Tag} {r : ℕ}
    {ζ : Kˣ} (hζ : orderOf ζ = r) (m : ℤ) {v : Fin τ.rank → ℤ} {w : WeylGroup τ}
    (hdiv : ∀ k : Fin τ.rank,
      (r : ℤ) ∣ v k - m * ∑ l : Fin τ.rank, (w⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)) l * v l) :
    weylAct w ((fun l : Fin τ.rank => ζ ^ v l) ^ m) = fun l => ζ ^ v l := by
  funext k
  change rootChar ((fun l : Fin τ.rank => ζ ^ v l) ^ m)
    (w⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)) = ζ ^ v k
  have hpow : (fun l : Fin τ.rank => ζ ^ v l) ^ m = fun l => ζ ^ (m * v l) := by
    funext l
    rw [Pi.pow_apply, ← zpow_mul]
    congr 1
    ring
  rw [hpow, CFSG.HardMathSupport.Timmesfeld.LangTorus.rootChar_zpow]
  have hdot : (fun l : Fin τ.rank => m * v l) ⬝ᵥ
      (w⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)) =
      m * ∑ l : Fin τ.rank, (w⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)) l * v l := by
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hdot]
  apply (zpow_eq_zpow_iff_modEq (x := ζ)).2
  rw [hζ, Int.modEq_iff_dvd]
  exact hdiv k

private theorem case_generic
    {K : Type} [Field K] {r q : ℕ} {ζ : Kˣ} (hζ : orderOf ζ = r)
    {b : Fin Tag.E6.rank → ZMod 3} {i j : Fin Tag.E6.rank}
    (hi : b i = 0) (hj : b j = 0)
    {T : List ℕ} {ω : WeylGroup Tag.E6} (hrep : e6Certificate.Represents T ω)
    {row : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hrow_spec : ∀ k : Fin Tag.E6.rank,
      e6Certificate.tupleVec T (reflect .E6 j (reflect .E6 i (Pi.single k 1))) = row k)
    {v : ℤ → Fin Tag.E6.rank → ℤ} {D : ℤ} (hD : (r : ℤ) ∣ D)
    (hv_spec : ∀ k : Fin Tag.E6.rank,
      v (q : ℤ) k + (q : ℤ) * (∑ l : Fin Tag.E6.rank, row k l * v (q : ℤ) l) =
        if (k : ℕ) = 0 then D else 0)
    {m : Fin Tag.E6.rank} (hvnz : (v (q : ℤ) m : ZMod r) ≠ 0) :
    ∃ u'' : WeylGroup Tag.E6, u'' * ω ∈ kernelWeylGroup (triChar b) ∧
      ∃ c'' : Fin Tag.E6.rank → Kˣ, (∀ i, c'' i ^ r = 1) ∧ c'' ≠ 1 ∧
        weylAct u'' (c'' ^ (-(q : ℤ))) = c'' := by
  classical
  have hsi : simple .E6 i ∈ kernelWeylGroup (triChar b) := by
    refine Subgroup.subset_closure ⟨1, i, ?_, by simp⟩
    rw [mem_kernelRoots_triChar]
    refine ⟨IsRoot.basis i, ?_⟩
    have h := triPairing_zsmul_single b (1 : ℤ) i
    rw [one_smul, Int.cast_one, mul_one] at h
    simpa using h.trans hi
  have hsj : simple .E6 j ∈ kernelWeylGroup (triChar b) := by
    refine Subgroup.subset_closure ⟨1, j, ?_, by simp⟩
    rw [mem_kernelRoots_triChar]
    refine ⟨IsRoot.basis j, ?_⟩
    have h := triPairing_zsmul_single b (1 : ℤ) j
    rw [one_smul, Int.cast_one, mul_one] at h
    simpa using h.trans hj
  set u'' : WeylGroup Tag.E6 := simple .E6 i * simple .E6 j * ω⁻¹ with hu''
  have hu''ω : u'' * ω = simple .E6 i * simple .E6 j := by
    rw [hu'']; group
  have hu''inv : u''⁻¹ = ω * simple .E6 j * simple .E6 i := by
    rw [hu'']
    simp only [mul_inv_rev, (coxeterSystem .E6).inv_simple]
    group
  have hrow : ∀ k : Fin Tag.E6.rank,
      u''⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) = row k := by
    intro k
    rw [hu''inv, mul_smul, mul_smul, simple_smul, simple_smul, ← tupleVec_eq hrep]
    exact hrow_spec k
  refine ⟨u'', ?_, ?_⟩
  · rw [hu''ω]
    exact mul_mem hsi hsj
  · refine ⟨fun l => ζ ^ v (q : ℤ) l, ?_, ?_, ?_⟩
    · intro l
      have hζr : ζ ^ r = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
      calc (ζ ^ v (q : ℤ) l) ^ r = (ζ ^ v (q : ℤ) l) ^ (r : ℤ) := by rw [zpow_natCast]
        _ = ζ ^ (v (q : ℤ) l * (r : ℤ)) := by rw [← zpow_mul]
        _ = (ζ ^ (r : ℤ)) ^ v (q : ℤ) l := by rw [zpow_mul']
        _ = (ζ ^ r) ^ v (q : ℤ) l := by rw [zpow_natCast]
        _ = 1 := by rw [hζr]; exact one_zpow _
    · intro hc
      have hnot : ¬ (r : ℤ) ∣ v (q : ℤ) m := by
        intro hd
        exact hvnz ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd)
      have hz : ζ ^ v (q : ℤ) m ≠ 1 := zpow_ne_one_of_not_dvd hζ hnot
      exact hz (congrFun hc m)
    · have hdiv : ∀ k : Fin Tag.E6.rank,
          (r : ℤ) ∣ v (q : ℤ) k - (-(q : ℤ)) *
            ∑ l : Fin Tag.E6.rank, (u''⁻¹ • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) l *
              v (q : ℤ) l := by
        intro k
        rw [hrow k]
        have hp := hv_spec k
        have heq : v (q : ℤ) k - (-(q : ℤ)) *
            (∑ l : Fin Tag.E6.rank, row k l * v (q : ℤ) l) =
            v (q : ℤ) k + (q : ℤ) * (∑ l : Fin Tag.E6.rank, row k l * v (q : ℤ) l) := by
          ring
        rw [heq, hp]
        by_cases hk : (k : ℕ) = 0
        · rw [if_pos hk]
          exact hD
        · rw [if_neg hk]
          exact dvd_zero _
      exact weylAct_zpow_eq_of_dvd hζ (-(q : ℤ)) hdiv

private theorem zmod_ne_zero_of_factor {r : ℕ} {a : ℤ} {f : ZMod r}
    (hcast : (a : ZMod r) = f) (hf : f ≠ 0) : (a : ZMod r) ≠ 0 := hcast ▸ hf

private theorem order_q_ne_zero {r q e : ℕ} [Fact r.Prime] (he : e ≠ 0)
    (hq : orderOf (q : ZMod r) = e) :
    (q : ZMod r) ≠ 0 := by
  intro h
  have h1 : (q : ZMod r) ^ e = 1 := by rw [← hq]; exact pow_orderOf_eq_one _
  rw [h] at h1
  rw [zero_pow he] at h1
  exact zero_ne_one h1

private theorem order_q_ne_one {r q e : ℕ} (he : e ≠ 1) (hq : orderOf (q : ZMod r) = e) :
    (q : ZMod r) ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hq
  omega

private theorem case6_T1
    {K : Type} [Field K] {r q : ℕ} (hr : r.Prime)
    (hq : orderOf (q : ZMod r) = 12) (ζ : Kˣ) (hζ : orderOf ζ = r)
    {ω : WeylGroup Tag.E6} (hrep : e6Certificate.Represents [33, 35, 71, 28, 4, 3] ω) :
    ∃ u'' : WeylGroup Tag.E6, u'' * ω ∈ kernelWeylGroup (triChar b6) ∧
      ∃ c'' : Fin Tag.E6.rank → Kˣ, (∀ i, c'' i ^ r = 1) ∧ c'' ≠ 1 ∧
        weylAct u'' (c'' ^ (-(q : ℤ))) = c'' := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : (q : ZMod r) ≠ 0 := order_q_ne_zero (by norm_num) hq
  have hq1 : (q : ZMod r) ≠ 1 := order_q_ne_one (by norm_num) hq
  have hv1 : v61 (q : ℤ) f1 = -(q : ℤ) * (1 - (q : ℤ)) ^ 2 := by
    have h : v61 (q : ℤ) f1 = -q + 2 * q ^ 2 - q ^ 3 := by simp [v61, f1]
    rw [h]
    ring
  have hcast : ((v61 (q : ℤ) f1 : ℤ) : ZMod r) =
      (-(q : ZMod r)) * (1 - (q : ZMod r)) ^ 2 := by
    rw [hv1]
    push_cast
    rfl
  have hvnz : (v61 (q : ℤ) f1 : ZMod r) ≠ 0 :=
    zmod_ne_zero_of_factor hcast (by
      exact mul_ne_zero (neg_ne_zero.mpr hq0)
        (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hq1))))
  exact case_generic hζ b6_f3 b6_f4 hrep row61_spec (dvd_D_twelve hr hq)
    (v61_spec (q : ℤ)) hvnz

private theorem factor_nine {F : Type} [CommRing F] (x : F) :
    (x ^ 3 + 1) * (x ^ 6 - x ^ 3 + 1) = x ^ 9 + 1 := by ring

private theorem pow_six_sq {F : Type} [CommRing F] (x : F) : x ^ 6 = (x ^ 3) ^ 2 := by ring

private theorem dvd_D_eighteen {r q : ℕ} (hr : r.Prime) (hq : orderOf (q : ZMod r) = 18) :
    (r : ℤ) ∣ 1 - (q : ℤ) ^ 3 + (q : ℤ) ^ 6 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h18 : (q : ZMod r) ^ 18 = 1 := by
    have h := pow_orderOf_eq_one (q : ZMod r)
    rwa [hq] at h
  have h9ne : (q : ZMod r) ^ 9 ≠ 1 := by
    intro h
    have hdvd : orderOf (q : ZMod r) ∣ 9 := orderOf_dvd_iff_pow_eq_one.2 h
    rw [hq] at hdvd
    omega
  have h9 : (q : ZMod r) ^ 9 = -1 := by
    have hsq : ((q : ZMod r) ^ 9) ^ 2 = 1 := by
      rw [← pow_mul, show 9 * 2 = 18 by norm_num, h18]
    have hfac : ((q : ZMod r) ^ 9 - 1) * ((q : ZMod r) ^ 9 + 1) = 0 := by
      rw [factor_sq, hsq, sub_self]
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h9ne
    · exact add_eq_zero_iff_eq_neg.mp h
  have h3ne : (q : ZMod r) ^ 3 + 1 ≠ 0 := by
    intro h
    have h6 : (q : ZMod r) ^ 6 = 1 := by
      rw [pow_six_sq, add_eq_zero_iff_eq_neg.mp h]
      exact neg_one_sq (R := ZMod r)
    have hdvd : orderOf (q : ZMod r) ∣ 6 := orderOf_dvd_iff_pow_eq_one.2 h6
    rw [hq] at hdvd
    omega
  have h6 : (q : ZMod r) ^ 6 - (q : ZMod r) ^ 3 + 1 = 0 := by
    have hfac : ((q : ZMod r) ^ 3 + 1) *
        ((q : ZMod r) ^ 6 - (q : ZMod r) ^ 3 + 1) = 0 := by
      rw [factor_nine, h9]
      exact neg_add_cancel 1
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd h h3ne
    · exact h
  have hD : ((1 - (q : ℤ) ^ 3 + (q : ℤ) ^ 6 : ℤ) : ZMod r) = 0 := by
    push_cast
    rw [show (1 - (q : ZMod r) ^ 3 + (q : ZMod r) ^ 6) =
      ((q : ZMod r) ^ 6 - (q : ZMod r) ^ 3 + 1) by ring, h6]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hD

private def row62 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ := fun k l =>
  ([[1, 1, 2, 3, 2, 1], [0, -1, -1, -1, 0, 0], [-1, 0, -1, -1, 0, 0],
    [0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 1], [1, 1, 1, 1, 1, 0]].getD (k : ℕ) []).getD (l : ℕ) 0

private theorem row62_spec : ∀ k : Fin Tag.E6.rank,
    e6Certificate.tupleVec [68, 51, 47, 5, 4, 28]
      (reflect .E6 f4 (reflect .E6 f3 (Pi.single k 1))) = row62 k := by
  intro k
  fin_cases k <;> decide +kernel

private def v62 (q : ℤ) : Fin Tag.E6.rank → ℤ := fun k =>
  [1 - 2 * q + q ^ 2 + q ^ 3 - q ^ 4, q ^ 2 - q ^ 3,
    q - q ^ 2 - q ^ 3 + 2 * q ^ 4 - q ^ 5, -q ^ 2 + 2 * q ^ 3 - 2 * q ^ 4 + q ^ 5,
    q ^ 2 - q ^ 3 + q ^ 4, -q + q ^ 2 - q ^ 3].getD (k : ℕ) 0

private theorem v62_spec (q : ℤ) : ∀ k : Fin Tag.E6.rank,
    v62 q k + q * (∑ l : Fin Tag.E6.rank, row62 k l * v62 q l) =
      if (k : ℕ) = 0 then 1 - q + q ^ 3 - q ^ 5 + q ^ 6 else 0 := by
  intro k
  change v62 q k + q * (∑ l : Fin 6, row62 k l * v62 q l) =
    if (k : ℕ) = 0 then 1 - q + q ^ 3 - q ^ 5 + q ^ 6 else 0
  rw [Fin.sum_univ_six]
  fin_cases k <;> simp [v62, row62] <;> ring

private theorem case6_T2
    {K : Type} [Field K] {r q : ℕ} (hr : r.Prime)
    (hq : orderOf (q : ZMod r) = 12) (ζ : Kˣ) (hζ : orderOf ζ = r)
    {ω : WeylGroup Tag.E6} (hrep : e6Certificate.Represents [68, 51, 47, 5, 4, 28] ω) :
    ∃ u'' : WeylGroup Tag.E6, u'' * ω ∈ kernelWeylGroup (triChar b6) ∧
      ∃ c'' : Fin Tag.E6.rank → Kˣ, (∀ i, c'' i ^ r = 1) ∧ c'' ≠ 1 ∧
        weylAct u'' (c'' ^ (-(q : ℤ))) = c'' := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : (q : ZMod r) ≠ 0 := order_q_ne_zero (by norm_num) hq
  have hq1 : (q : ZMod r) ≠ 1 := order_q_ne_one (by norm_num) hq
  have hv1 : v62 (q : ℤ) f1 = (q : ℤ) ^ 2 * (1 - (q : ℤ)) := by
    have h : v62 (q : ℤ) f1 = q ^ 2 - q ^ 3 := by simp [v62, f1]
    rw [h]; ring
  have hcast : ((v62 (q : ℤ) f1 : ℤ) : ZMod r) =
      (q : ZMod r) ^ 2 * (1 - (q : ZMod r)) := by
    rw [hv1]
    push_cast
    rfl
  have hvnz : (v62 (q : ℤ) f1 : ZMod r) ≠ 0 :=
    zmod_ne_zero_of_factor hcast (by
      exact mul_ne_zero (pow_ne_zero 2 hq0) (sub_ne_zero.mpr (Ne.symm hq1)))
  exact case_generic hζ b6_f3 b6_f4 hrep row62_spec (dvd_D_twelve hr hq)
    (v62_spec (q : ℤ)) hvnz

private def f0 : Fin Tag.E6.rank := ⟨0, by decide⟩
private def f2 : Fin Tag.E6.rank := ⟨2, by decide⟩

private def b7 : Fin Tag.E6.rank → ZMod 3 := vec3 (τ := .E6) e6ThreeStab7.vec

private theorem b7_f0 : b7 f0 = 0 := by decide +kernel
private theorem b7_f2 : b7 f2 = 0 := by decide +kernel

private def row71 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ := fun k l =>
  ([[-1, -2, -2, -3, -2, -1], [0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]].getD (k : ℕ) []).getD (l : ℕ) 0

private theorem row71_spec : ∀ k : Fin Tag.E6.rank,
    e6Certificate.tupleVec [1, 5, 68, 64, 2, 0]
      (reflect .E6 f2 (reflect .E6 f0 (Pi.single k 1))) = row71 k := by
  intro k
  fin_cases k <;> decide +kernel

private def v71 (q : ℤ) : Fin Tag.E6.rank → ℤ := fun k =>
  [1 + q, q ^ 2 + q ^ 3, -q ^ 3 - q ^ 4, -q ^ 5, q ^ 4 + q ^ 5, -q - q ^ 2].getD (k : ℕ) 0

private theorem v71_spec (q : ℤ) : ∀ k : Fin Tag.E6.rank,
    v71 q k + q * (∑ l : Fin Tag.E6.rank, row71 k l * v71 q l) =
      if (k : ℕ) = 0 then 1 - q ^ 3 + q ^ 6 else 0 := by
  intro k
  change v71 q k + q * (∑ l : Fin 6, row71 k l * v71 q l) =
    if (k : ℕ) = 0 then 1 - q ^ 3 + q ^ 6 else 0
  rw [Fin.sum_univ_six]
  fin_cases k <;> simp [v71, row71] <;> ring

private theorem case7_T1
    {K : Type} [Field K] {r q : ℕ} (hr : r.Prime)
    (hq : orderOf (q : ZMod r) = 18) (ζ : Kˣ) (hζ : orderOf ζ = r)
    {ω : WeylGroup Tag.E6} (hrep : e6Certificate.Represents [1, 5, 68, 64, 2, 0] ω) :
    ∃ u'' : WeylGroup Tag.E6, u'' * ω ∈ kernelWeylGroup (triChar b7) ∧
      ∃ c'' : Fin Tag.E6.rank → Kˣ, (∀ i, c'' i ^ r = 1) ∧ c'' ≠ 1 ∧
        weylAct u'' (c'' ^ (-(q : ℤ))) = c'' := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : (q : ZMod r) ≠ 0 := order_q_ne_zero (by norm_num) hq
  have hv3 : v71 (q : ℤ) f3 = -(q : ℤ) ^ 5 := by
    have h : v71 (q : ℤ) f3 = -q ^ 5 := by simp [v71, f3]
    exact h
  have hcast : ((v71 (q : ℤ) f3 : ℤ) : ZMod r) = -((q : ZMod r) ^ 5) := by
    rw [hv3]
    push_cast
    rfl
  have hvnz : (v71 (q : ℤ) f3 : ZMod r) ≠ 0 :=
    zmod_ne_zero_of_factor hcast (neg_ne_zero.mpr (pow_ne_zero 5 hq0))
  exact case_generic hζ b7_f0 b7_f2 hrep row71_spec (dvd_D_eighteen hr hq)
    (v71_spec (q : ℤ)) hvnz

private def row72 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ := fun k l =>
  ([[0, 0, 0, 0, -1, -1], [1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1],
    [-1, -1, -1, -2, -1, -1], [1, 1, 2, 3, 2, 1],
    [0, 1, 0, 0, 0, 0]].getD (k : ℕ) []).getD (l : ℕ) 0

private theorem row72_spec : ∀ k : Fin Tag.E6.rank,
    e6Certificate.tupleVec [5, 0, 4, 65, 68, 1]
      (reflect .E6 f2 (reflect .E6 f0 (Pi.single k 1))) = row72 k := by
  intro k
  fin_cases k <;> decide +kernel

private def v72 (q : ℤ) : Fin Tag.E6.rank → ℤ := fun k =>
  [1 - q ^ 2, -q + q ^ 3, -q ^ 3 + q ^ 5, q, -q + q ^ 4 - q ^ 5, q ^ 2 - q ^ 4].getD (k : ℕ) 0

private theorem v72_spec (q : ℤ) : ∀ k : Fin Tag.E6.rank,
    v72 q k + q * (∑ l : Fin Tag.E6.rank, row72 k l * v72 q l) =
      if (k : ℕ) = 0 then 1 - q ^ 3 + q ^ 6 else 0 := by
  intro k
  change v72 q k + q * (∑ l : Fin 6, row72 k l * v72 q l) =
    if (k : ℕ) = 0 then 1 - q ^ 3 + q ^ 6 else 0
  rw [Fin.sum_univ_six]
  fin_cases k <;> simp [v72, row72] <;> ring

private theorem case7_T2
    {K : Type} [Field K] {r q : ℕ} (hr : r.Prime)
    (hq : orderOf (q : ZMod r) = 18) (ζ : Kˣ) (hζ : orderOf ζ = r)
    {ω : WeylGroup Tag.E6} (hrep : e6Certificate.Represents [5, 0, 4, 65, 68, 1] ω) :
    ∃ u'' : WeylGroup Tag.E6, u'' * ω ∈ kernelWeylGroup (triChar b7) ∧
      ∃ c'' : Fin Tag.E6.rank → Kˣ, (∀ i, c'' i ^ r = 1) ∧ c'' ≠ 1 ∧
        weylAct u'' (c'' ^ (-(q : ℤ))) = c'' := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : (q : ZMod r) ≠ 0 := order_q_ne_zero (by norm_num) hq
  have hv3 : v72 (q : ℤ) f3 = (q : ℤ) := by simp [v72, f3]
  have hcast : ((v72 (q : ℤ) f3 : ℤ) : ZMod r) = (q : ZMod r) := by
    rw [hv3]
    push_cast
    rfl
  have hvnz : (v72 (q : ℤ) f3 : ZMod r) ≠ 0 :=
    zmod_ne_zero_of_factor hcast hq0
  exact case_generic hζ b7_f0 b7_f2 hrep row72_spec (dvd_D_eighteen hr hq)
    (v72_spec (q : ℤ)) hvnz

private theorem passing0 : e6ThreeStab0.passing e6Certificate = [List.range Tag.E6.rank] := by
  decide +kernel

private theorem passing6 : e6ThreeStab6.passing e6Certificate =
    [[33, 35, 71, 28, 4, 3], List.range Tag.E6.rank, [68, 51, 47, 5, 4, 28]] := by
  decide +kernel

private theorem passing7 : e6ThreeStab7.passing e6Certificate =
    [[1, 5, 68, 64, 2, 0], [5, 0, 4, 65, 68, 1], List.range Tag.E6.rank] := by
  decide +kernel

private theorem weylAct_one_right {K : Type} [Field K] {τ : Tag} (w : WeylGroup τ) :
    weylAct w (1 : Fin τ.rank → Kˣ) = 1 := by
  funext i
  change rootChar (1 : Fin τ.rank → Kˣ) (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) = 1
  simp [rootChar]

private theorem rho_eq_six_or_seven
    {ρ : ℕ} (hρ8 : ρ < 8) {S : StabCert3}
    (hSdef : S = e6ThreeStabs.getD ρ e6ThreeStab0)
    {bρ : Fin Tag.E6.rank → ZMod 3}
    {u0 ω v : WeylGroup Tag.E6} {T : List ℕ}
    (hT : T ∈ S.passing e6Certificate) (hrep : e6Certificate.Represents T ω)
    (hu0_not : u0 ∉ kernelWeylGroup (triChar bρ))
    (hv : v ∈ kernelWeylGroup (triChar bρ))
    (hu0inv : u0⁻¹ = ω * v⁻¹) : ρ = 6 ∨ ρ = 7 := by
  have hpass : ρ ≤ 5 → S.passing e6Certificate = [List.range Tag.E6.rank] := by
    intro hρ5
    have hρ6 : ρ < 6 := by omega
    interval_cases ρ
    · rw [hSdef]
      exact passing0
    · rw [hSdef]
      exact passing_conn_reps 1 (by simp)
    · rw [hSdef]
      exact passing_conn_reps 2 (by simp)
    · rw [hSdef]
      exact passing_conn_reps 3 (by simp)
    · rw [hSdef]
      exact passing_conn_reps 4 (by simp)
    · rw [hSdef]
      exact passing_conn_reps 5 (by simp)
  have hnot : ¬ ρ ≤ 5 := by
    intro hρ5
    have hp := hpass hρ5
    have hω1 : ω = 1 := by
      rw [hp] at hT
      simp only [List.mem_singleton] at hT
      subst hT
      exact represents_unique hrep (represents_one e6Certificate_check)
    have hinv : u0⁻¹ ∈ kernelWeylGroup (triChar bρ) := by
      rw [hu0inv, hω1, one_mul]
      exact inv_mem hv
    exact hu0_not (by simpa using inv_mem hinv)
  omega

private theorem transport
    {K : Type} [Field K] {a : Fin Tag.E6.rank → Kˣ}
    {b bρ : Fin Tag.E6.rank → ZMod 3} {u t u0 u'' : WeylGroup Tag.E6}
    (ht : IsCharConj (triChar bρ) (triChar b) t)
    (hu0 : u0 = t⁻¹ * u * t)
    (hu'' : u'' * u0⁻¹ ∈ kernelWeylGroup (triChar bρ))
    (hK_eq : kernelWeylGroup (triChar b) = kernelReflectionGroup a)
    {r q : ℕ} {c'' : Fin Tag.E6.rank → Kˣ}
    (hfix : weylAct u'' (c'' ^ (-(q : ℤ))) = c'')
    (hpow : ∀ i, c'' i ^ r = 1) (hne : c'' ≠ 1) :
    ∃ u' : WeylGroup Tag.E6, u' * u⁻¹ ∈ kernelReflectionGroup a ∧
      ∃ c : Fin Tag.E6.rank → Kˣ, (∀ i, c i ^ r = 1) ∧ c ≠ 1 ∧
        weylAct u' (c ^ (-(q : ℤ))) = c := by
  set u' : WeylGroup Tag.E6 := t * u'' * t⁻¹ with hu'
  have hcancel : ∀ x : Fin Tag.E6.rank → Kˣ, weylAct t⁻¹ (weylAct t x) = x := by
    intro x
    rw [← weylAct_mul, inv_mul_cancel, weylAct_one]
  have hmem : u' * u⁻¹ ∈ kernelWeylGroup (triChar b) := by
    rw [kernelWeylGroup_eq_map ht]
    refine ⟨u'' * u0⁻¹, hu'', ?_⟩
    rw [hu', hu0]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hpow' : c'' ^ r = 1 := funext hpow
  refine ⟨u', ?_, ?_⟩
  · rwa [hK_eq] at hmem
  · refine ⟨weylAct t c'', ?_, ?_, ?_⟩
    · intro i
      have hcr : (weylAct t c'') ^ r = 1 := by
        rw [← zpow_natCast, ← weylAct_zpow, zpow_natCast, hpow', weylAct_one_right]
      simpa using congrFun hcr i
    · intro hc1
      have hh := congrArg (weylAct t⁻¹) hc1
      rw [hcancel, weylAct_one_right] at hh
      exact hne hh
    · have hc_pow : (weylAct t c'') ^ (-(q : ℤ)) = weylAct t (c'' ^ (-(q : ℤ))) :=
        (weylAct_zpow t c'' (-(q : ℤ))).symm
      calc weylAct u' ((weylAct t c'') ^ (-(q : ℤ)))
          = weylAct t (weylAct u'' (weylAct t⁻¹ (weylAct t (c'' ^ (-(q : ℤ)))))) := by
              rw [hc_pow, hu', weylAct_mul, weylAct_mul]
        _ = weylAct t (weylAct u'' (c'' ^ (-(q : ℤ)))) := by rw [hcancel]
        _ = weylAct t c'' := by rw [hfix]

theorem exists_weylAct_eq_of_not_mem_kernelReflectionGroup
    {K : Type} [Field K] {a : Fin Tag.E6.rank → Kˣ} (ha3 : ∀ i, a i ^ 3 = 1)
    {u : WeylGroup Tag.E6} (hua : weylAct u a = a) (hu : u ∉ kernelReflectionGroup a) :
    ∃ e ∈ ggOutdiagExpsTwE6, ∀ r q : ℕ, r.Prime → orderOf (q : ZMod r) = e →
      ∀ ζ : Kˣ, orderOf ζ = r → ∃ u' : WeylGroup Tag.E6, u' * u⁻¹ ∈ kernelReflectionGroup a ∧
        ∃ c : Fin Tag.E6.rank → Kˣ, (∀ i, c i ^ r = 1) ∧ c ≠ 1 ∧
          weylAct u' (c ^ (-(q : ℤ))) = c := by
  classical
  have hroot : ∀ v : Fin Tag.E6.rank → ℤ, rootChar a v = rootChar a (u⁻¹ • v) := by
    intro v
    calc rootChar a v = rootChar (weylAct u a) v :=
          (congrArg (fun x => rootChar x v) hua).symm
      _ = rootChar a (u⁻¹ • v) := rootChar_weylAct u a v
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha3)
  obtain ⟨b, rfl⟩ : ∃ b : Fin Tag.E6.rank → ZMod 3, χ' = triChar b := ⟨_, eq_triChar χ'⟩
  have hS_eq : rootCharStabilizerSubgroup a = charStabilizer (triChar b) := by
    rw [show rootCharStabilizerSubgroup a = charStabilizer (rootCharHom3 a) from
      Subgroup.ext fun w => Iff.rfl]
    exact charStabilizer_congr_ker hker
  have hK_eq : kernelWeylGroup (triChar b) = kernelReflectionGroup a := by
    rw [show kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) from rfl]
    exact (kernelWeylGroup_congr_ker hker).symm
  have hu_stab : u ∈ charStabilizer (triChar b) := by
    rw [← hS_eq]
    show u ∈ rootCharStabilizer a
    intro v
    have h := hroot (u • v)
    rwa [inv_smul_smul] at h
  have hu_not : u ∉ kernelWeylGroup (triChar b) := by
    rw [hK_eq]
    exact hu
  obtain ⟨horbit, hstab⟩ := e6ThreeScCheck_spec
  have hvec := e6ThreeStabs_vec
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 horbit (triChar b)
  have hlen : ρ < e6ThreeStabs.length := by
    rw [← List.length_map StabCert3.vec, hvec]
    exact hρ
  have hρ8 : ρ < 8 := hρ
  set S := e6ThreeStabs[ρ] with hSdef
  have hSv : S.vec = e6ThreeReps.getD ρ [] := by
    rw [List.getD_eq_getElem _ _ hρ, hSdef]
    have h := congrArg (fun l => l[ρ]?) hvec
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hρ,
      Option.map_some, Option.some.injEq] at h
    exact h
  obtain ⟨hScheck, -⟩ := hstab S (List.getElem_mem hlen)
  rw [← hSv] at ht
  set bρ := vec3 (τ := .E6) S.vec with hbρ
  set u0 : WeylGroup Tag.E6 := t⁻¹ * u * t with hu0
  have hu0_stab : u0 ∈ charStabilizer (triChar bρ) :=
    (charStabilizer_iff_of_isCharConj ht).1 hu_stab
  have hu0_not : u0 ∉ kernelWeylGroup (triChar bρ) := by
    intro hmem
    have hmem' : t * u0 * t⁻¹ ∈ (kernelWeylGroup (triChar bρ)).map
        (MulAut.conj t).toMonoidHom := ⟨u0, hmem, rfl⟩
    rw [← kernelWeylGroup_eq_map ht] at hmem'
    have hgroup : t * u0 * t⁻¹ = u := by rw [hu0]; group
    rw [hgroup] at hmem'
    exact hu_not hmem'
  obtain ⟨v, hv, hωmem⟩ := exists_mul_mem_kernelPosStabilizer (inv_mem hu0_stab)
  set ω : WeylGroup Tag.E6 := u0⁻¹ * v with hω
  obtain ⟨T, hT, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check hScheck hωmem
  have hu0inv_eq : u0⁻¹ = ω * v⁻¹ := by
    rw [hω]
    group
  have hSdefD : S = e6ThreeStabs.getD ρ e6ThreeStab0 := by
    rw [hSdef, List.getD_eq_getElem _ _ hlen]
    rfl
  have hρ67 : ρ = 6 ∨ ρ = 7 :=
    rho_eq_six_or_seven hρ8 hSdefD hT hrep hu0_not hv hu0inv_eq
  rcases hρ67 with rfl | rfl
  · have hS6 : S = e6ThreeStab6 := by rw [hSdef]; rfl
    rw [hS6] at hScheck hT
    have hbρ6 : bρ = b6 := by rw [hbρ, hS6]; rfl
    rw [passing6] at hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    refine ⟨12, by simp [ggOutdiagExpsTwE6], ?_⟩
    intro r q hr hq ζ hζ
    rcases hT with rfl | rfl | rfl
    · obtain ⟨u'', hu''mem, c'', hc''pow, hc''ne, hc''fix⟩ :=
        case6_T1 hr hq ζ hζ (ω := ω) hrep
      have hu''mem' : u'' * ω ∈ kernelWeylGroup (triChar bρ) := by rwa [hbρ6]
      have hu''u0 : u'' * u0⁻¹ ∈ kernelWeylGroup (triChar bρ) := by
        have heq : u'' * u0⁻¹ = (u'' * ω) * v⁻¹ := by rw [hω]; group
        rw [heq]
        exact mul_mem hu''mem' (inv_mem hv)
      exact transport ht hu0 hu''u0 hK_eq hc''fix hc''pow hc''ne
    · exfalso
      have hω1 : ω = 1 := represents_unique hrep (represents_one e6Certificate_check)
      have hinv : u0⁻¹ ∈ kernelWeylGroup (triChar bρ) := by
        rw [hu0inv_eq, hω1, one_mul]
        exact inv_mem hv
      exact hu0_not (by simpa using inv_mem hinv)
    · obtain ⟨u'', hu''mem, c'', hc''pow, hc''ne, hc''fix⟩ :=
        case6_T2 hr hq ζ hζ (ω := ω) hrep
      have hu''mem' : u'' * ω ∈ kernelWeylGroup (triChar bρ) := by rwa [hbρ6]
      have hu''u0 : u'' * u0⁻¹ ∈ kernelWeylGroup (triChar bρ) := by
        have heq : u'' * u0⁻¹ = (u'' * ω) * v⁻¹ := by rw [hω]; group
        rw [heq]
        exact mul_mem hu''mem' (inv_mem hv)
      exact transport ht hu0 hu''u0 hK_eq hc''fix hc''pow hc''ne
  · have hS7 : S = e6ThreeStab7 := by rw [hSdef]; rfl
    rw [hS7] at hScheck hT
    have hbρ7 : bρ = b7 := by rw [hbρ, hS7]; rfl
    rw [passing7] at hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    refine ⟨18, by simp [ggOutdiagExpsTwE6], ?_⟩
    intro r q hr hq ζ hζ
    rcases hT with rfl | rfl | rfl
    · obtain ⟨u'', hu''mem, c'', hc''pow, hc''ne, hc''fix⟩ :=
        case7_T1 hr hq ζ hζ (ω := ω) hrep
      have hu''mem' : u'' * ω ∈ kernelWeylGroup (triChar bρ) := by rwa [hbρ7]
      have hu''u0 : u'' * u0⁻¹ ∈ kernelWeylGroup (triChar bρ) := by
        have heq : u'' * u0⁻¹ = (u'' * ω) * v⁻¹ := by rw [hω]; group
        rw [heq]
        exact mul_mem hu''mem' (inv_mem hv)
      exact transport ht hu0 hu''u0 hK_eq hc''fix hc''pow hc''ne
    · obtain ⟨u'', hu''mem, c'', hc''pow, hc''ne, hc''fix⟩ :=
        case7_T2 hr hq ζ hζ (ω := ω) hrep
      have hu''mem' : u'' * ω ∈ kernelWeylGroup (triChar bρ) := by rwa [hbρ7]
      have hu''u0 : u'' * u0⁻¹ ∈ kernelWeylGroup (triChar bρ) := by
        have heq : u'' * u0⁻¹ = (u'' * ω) * v⁻¹ := by rw [hω]; group
        rw [heq]
        exact mul_mem hu''mem' (inv_mem hv)
      exact transport ht hu0 hu''u0 hK_eq hc''fix hc''pow hc''ne
    · exfalso
      have hω1 : ω = 1 := represents_unique hrep (represents_one e6Certificate_check)
      have hinv : u0⁻¹ ∈ kernelWeylGroup (triChar bρ) := by
        rw [hu0inv_eq, hω1, one_mul]
        exact inv_mem hv
      exact hu0_not (by simpa using inv_mem hinv)

end CFSG.StandardType.TwE6FrameFixPpd
