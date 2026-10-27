module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNSylow
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMinkowski
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylReflectionOfFixedPoints
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

private theorem ggKGNL_torus_commute
    {τ : Tag} {L : Type} [Field L] (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    {h h' : ModGL τ L} (hh : h ∈ twistedTorusOf n Φ) (hh' : h' ∈ twistedTorusOf n Φ) :
    Commute h h' := by
  have h1 : h ∈ torusGroup τ L := (mem_twistedTorusOf.1 hh).1
  have h2 : h' ∈ torusGroup τ L := (mem_twistedTorusOf.1 hh').1
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h1)
    (torusGroup_le_diagonalGroup h2)

private theorem ggKGNL_p_frameDiag_mem_torus
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {p : ℕ} [NeZero p]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hιeq : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (s : Fin τ.rank → ZMod p) :
    ExcFrames.frameDiag ζ hζ s ∈
      twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
        (Units.map (entrywiseHom Fr)) := by
  classical
  let n : ModGL τ (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w
  let Φ : ModGL τ (AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K) :=
    Units.map (entrywiseHom Fr)
  let t : ModGL τ (AlgebraicClosure K) := ExcFrames.frameDiag ζ hζ s
  have hB : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) = g0 * t * g0⁻¹ :=
    hιeq s
  have hbase : Φ (baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) := by
    simpa [Φ] using units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr
      ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K)
  have h1 : Φ (g0 * t * g0⁻¹) = g0 * t * g0⁻¹ := by
    rw [← hB]; exact hbase
  rw [map_mul, map_mul, map_inv] at h1
  rw [show Φ g0 = g0 * n from by simpa [Φ, n] using hg0] at h1
  have h2 : g0 * (n * Φ t * n⁻¹) * g0⁻¹ = g0 * t * g0⁻¹ := by
    simpa only [mul_inv_rev, mul_assoc] using h1
  have hfix : n * Φ t * n⁻¹ = t := mul_left_cancel (mul_right_cancel h2)
  rw [mem_twistedTorusOf]
  refine ⟨?_, ?_⟩
  · exact CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _
  · simpa [n, Φ, t] using hfix

private theorem ggKGNL_p_torusAct_neg
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hτ : τ = .E7 ∨ τ = .E8)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hιeq : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (hpq : p ∣ Nat.card K + 1) (s : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p w s = -s := by
  classical
  let n : ModGL τ (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w
  let Φ : ModGL τ (AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K) :=
    Units.map (entrywiseHom Fr)
  let t : ModGL τ (AlgebraicClosure K) := ExcFrames.frameDiag ζ hζ s
  have hfix : n * Φ t * n⁻¹ = t := by
    have hmem := ggKGNL_p_frameDiag_mem_torus hFr hg0 hζ hιeq s
    simpa [n, Φ, t] using (mem_twistedTorusOf.1 hmem).2
  have hΦt : Φ t = t ^ Nat.card K := by
    simp only [t, Φ, ExcFrames.frameDiag]
    rw [CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr, ← rootDiagUnit_pow]
  have hpow : ∀ (u : Fin τ.rank → ZMod p) (m : ℕ),
      (ExcFrames.frameDiag ζ hζ u) ^ m = ExcFrames.frameDiag ζ hζ (m • u) := by
    intro u m
    induction m with
    | zero => rw [pow_zero, zero_nsmul, ExcFrames.frameDiag_zero]
    | succ m ih => rw [pow_succ, ih, ← ExcFrames.frameDiag_add, ← succ_nsmul]
  have hkey : n * Φ t * n⁻¹ =
      ExcFrames.frameDiag ζ hζ (Nat.card K • TableBExc.torusAct τ p w s) := by
    rw [hΦt, ← conj_pow]
    rw [show n * t * n⁻¹ = ExcFrames.frameDiag ζ hζ (TableBExc.torusAct τ p w s) by
      simpa [n, t] using
        ExcFrames.canonicalRep_conj_frameDiag (τ := τ) (ζ := ζ) hζ w s]
    rw [hpow]
  have hframe : ExcFrames.frameDiag ζ hζ (Nat.card K • TableBExc.torusAct τ p w s) =
      ExcFrames.frameDiag ζ hζ s := hkey.symm.trans hfix
  have hinj : Function.Injective (ExcFrames.frameDiag (τ := τ) ζ hζ) :=
    ExcFrames.frameDiag_injective hζo hζ
      (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr hτ) hp2)
  have hqs : Nat.card K • TableBExc.torusAct τ p w s = s := hinj hframe
  have hq : ((Nat.card K : ℕ) : ZMod p) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have h1 : (Nat.card K : ZMod p) • TableBExc.torusAct τ p w s = s := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hqs
  rw [hq] at h1
  rw [neg_one_smul] at h1
  exact neg_eq_iff_eq_neg.mp h1

private theorem ggKGNL_modMat_weylMatrix_eq_neg_one_of_torusAct
    {τ : Tag} {p : ℕ} [NeZero p]
    {w : WeylGroup τ}
    (h : ∀ s : Fin τ.rank → ZMod p, TableBExc.torusAct τ p w s = -s) :
    modMat p (weylMatrix w) = -1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [torusAct_eq_weylMatrix_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at h1
  change (weylLatticeMatrix τ w).map (Int.castRingHom (ZMod p)) i j =
    (-1 : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p)) i j
  rw [h1, Pi.neg_apply, Pi.single_apply, Matrix.neg_apply, Matrix.one_apply]

private theorem ggKGNL_eq_w0_of_torusAct_neg
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp3 : 3 ≤ p)
    {w : WeylGroup τ}
    (h : ∀ s : Fin τ.rank → ZMod p, TableBExc.torusAct τ p w s = -s) :
    ExcIsLongest τ w := by
  have hw0_exists : ∃ w0 : WeylGroup τ, ∀ u : Fin τ.rank → ℤ, w0 • u = -u := by
    rcases hτ with rfl | rfl
    · exact CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.exists_weyl_neg_E7
    · exact CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.exists_weyl_neg_E8
  obtain ⟨w0, hw0⟩ := hw0_exists
  have hw0mat : weylMatrix w0 = -1 := by
    ext i j
    have h1 := congrFun (hw0 (Pi.single j 1 : Fin τ.rank → ℤ)) i
    rw [weylMatrix_apply, h1, Pi.neg_apply, Pi.single_apply, Matrix.neg_apply, Matrix.one_apply]
  have hmod : modMat p (weylMatrix w) = -1 :=
    ggKGNL_modMat_weylMatrix_eq_neg_one_of_torusAct h
  have hw0inv : weylMatrix w0⁻¹ = -1 := by
    have h1 : weylMatrix w0 * weylMatrix w0⁻¹ = 1 := by
      rw [← weylMatrix_mul, mul_inv_cancel, weylMatrix_one]
    rw [hw0mat] at h1
    have h2 := congrArg (fun M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ => (-1) * M) h1
    simpa [mul_assoc, neg_mul_neg, one_mul, mul_one] using h2
  have hmod_mul : modMat p (weylMatrix (w * w0⁻¹)) = 1 := by
    rw [weylMatrix_mul]
    rw [show modMat p (weylMatrix w * weylMatrix w0⁻¹) =
        modMat p (weylMatrix w) * modMat p (weylMatrix w0⁻¹) by
      simp only [modMat, Matrix.map_mul]]
    rw [hmod, hw0inv]
    have hneg : modMat p (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) = -1 := by
      ext i j
      simp [modMat, Matrix.neg_apply, Matrix.one_apply]
    rw [hneg, neg_mul_neg, one_mul]
  have heq : w * w0⁻¹ = 1 :=
    ExcFramesHalf.eq_one_of_modMat_weylMatrix_eq_one hτ hp3 hmod_mul
  have hw : w = w0 := by
    have h1 := congrArg (· * w0) heq
    simpa [mul_assoc] using h1
  rw [hw]
  intro α hα hpos i
  have h1 := congrFun (hw0 α) i
  rw [h1, Pi.neg_apply]
  exact neg_nonpos.mpr (hpos i)

theorem excFrame_of_langFrameData_with_coordinates
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hpq : p ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E)
    (hsc : ∀ g : adjointGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E)
    (hL : Irred937.LangFrameData τ p K E) :
    ∃ (F : ExcFrame τ K p E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K),
      (p ∣ Nat.card K - 1 → F.w = 1) ∧
      (p ∣ Nat.card K + 1 → ExcIsLongest τ F.w) ∧
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ v : WeylGroup τ, v * F.w = F.w * v) ∧
      (∀ s : Fin τ.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (ι (Multiplicative.ofAdd s) : ModGL τ K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcentral, hζo, hιinj, hιrange, hιeq⟩ := hL
  have hp3 : 3 ≤ p := by
    have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hlong : ExcIsLongest τ w :=
    ggKGNL_eq_w0_of_torusAct_neg hτ hp3
      (fun s => ggKGNL_p_torusAct_neg hp2 hτ hFr hg0 hζ hζo hιeq hpq s)
  let D : LangDatum τ (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hframe_mem : ∀ s : Fin τ.rank → ZMod p,
      ExcFrames.frameDiag ζ hζ s ∈ D.torus := by
    intro s
    have h := ggKGNL_p_frameDiag_mem_torus hFr hg0 hζ hιeq s
    simpa [D, LangDatum.ofFrobenius, LangDatum.torus] using h
  have hmem : ∀ x : adjointGroup τ K, x ∈ E ↔ x ^ p = 1 ∧
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 ∈
        D.torus := by
    intro x
    constructor
    · intro hx
      refine ⟨hE.2 x hx, ?_⟩
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hιrange ▸ hx)
      let s : Fin τ.rank → ZMod p := Multiplicative.toAdd m
      have hxeq : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹ := by
        rw [← hm]
        exact hιeq s
      rw [hxeq]
      have h1 : g0⁻¹ * (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) * g0 =
          ExcFrames.frameDiag ζ hζ s := by group
      rw [h1]
      exact hframe_mem s
    · rintro ⟨hx5, hxT⟩
      refine hsc x ?_ hx5
      intro e he
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hιrange ▸ he)
      let s : Fin τ.rank → ZMod p := Multiplicative.toAdd m
      have heeq : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹ := by
        rw [← hm]
        exact hιeq s
      have heT : ExcFrames.frameDiag ζ hζ s ∈ D.torus := hframe_mem s
      have hcommT : (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL τ K) * g0) *
          (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0) =
          (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0) *
          (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0) := by
        rw [heeq]
        have h1 : g0⁻¹ * (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) * g0 =
            ExcFrames.frameDiag ζ hζ s := by group
        rw [h1]
        exact (ggKGNL_torus_commute D.n D.Φ heT hxT).eq
      have hcommB : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) := by
        have h := congrArg (fun t => g0 * t * g0⁻¹) hcommT
        calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)
            = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (e : ModGL τ K) * g0 *
                (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (x : ModGL τ K) * g0)) * g0⁻¹ := by group
          _ = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (x : ModGL τ K) * g0 *
                (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (e : ModGL τ K) * g0)) * g0⁻¹ := by rw [hcommT]
          _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) := by group
      apply Subtype.ext
      apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommB.symm
  refine ⟨{ D := D, w := w, q_eq := rfl, frob := ?_, n_eq := rfl, mem_iff := hmem },
    Fr, ζ, hζ, ι₀, ?_, ?_, hFr, (fun _ => rfl), hζo, hιinj, hιrange, hcentral, hιeq⟩
  · exact ⟨Fr, ⟨hFr, fun _ => rfl⟩⟩
  · intro hpm1
    exfalso
    have hcard_pos : 0 < Nat.card K := Nat.card_pos (α := K)
    have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
    have hdvd2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpq hpm1
      rwa [hsub] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  · intro _
    exact hlong

theorem excFrame_of_langFrameData
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hpq : p ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E)
    (hsc : ∀ g : adjointGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E)
    (hL : Irred937.LangFrameData τ p K E) :
    ∃ F : ExcFrame τ K p E, (p ∣ Nat.card K - 1 → F.w = 1) ∧
      (p ∣ Nat.card K + 1 → ExcIsLongest τ F.w) := by
  obtain ⟨F, Fr, ζ, hζ, ι, hsplit, hplus, -⟩ :=
    excFrame_of_langFrameData_with_coordinates hτ hp2 hpq hE hsc hL
  exact ⟨F, hsplit, hplus⟩

theorem excSCTorusInput_nonsplit_three_five
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (hpq : p ∣ Nat.card K + 1) :
    ExcSCTorusInput τ K p (τ.rank - 1) := by
  intro E hE _ hr hsc
  have : Fact p.Prime := by
    rcases hp35 with rfl | rfl <;> exact ⟨by norm_num⟩
  have hp2 : p ≠ 2 := by
    rcases hp35 with rfl | rfl <;> norm_num
  have hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E := by
    intro x hx hx5
    rw [Subgroup.mem_centralizer_iff] at hx
    exact hsc x (fun e he => (hx e he).symm) hx5
  have hL := Irred937.exists_langFrame_of_sc (τ := τ) (p := p) hτ hp35 K hpq E hE hr hSC
  exact excFrame_of_langFrameData (τ := τ) (p := p) (K := K) (E := E) hτ hp2 hpq hE hsc hL

end CFSG.StandardType

end
