module


public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeLangWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6SplitNormalizer
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutFrame
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools

public noncomputable section

namespace CFSG.StandardType.E6RelativeLangWeyl

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE



theorem automorphism_frame_action {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} {E : Subgroup (adjointGroup .E6 K)} (F : ExcFrame .E6 K p E)
    (hp : p.Prime) (hp5 : 5 ≤ p) (ζ : (AlgebraicClosure K)ˣ)
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (hlong : ExcIsLongest .E6 F.w) (α : MulAut (adjointGroup .E6 K))
    (hα : ∀ x, α x ∈ E ↔ x ∈ E) :
    ∃ (c : (ZMod p)ˣ) (u : WeylGroup Tag.F4), ∀ s : Fin Tag.F4.rank → ZMod p,
      α (pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s)) =
        pFrame F hp ζ hζo hζ hpq hlong
          (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct Tag.F4 p u s)) := by
  classical
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
  haveI : ExpChar L 2 := ExpChar.prime Nat.prime_two
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hf : 1 ≤ (f : ℕ) := by
    rcases Nat.eq_zero_or_pos (f : ℕ) with h0 | h
    · exfalso
      rw [h0, pow_zero] at hcard'
      have h2 : 1 < Nat.card K := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      exact (lt_irrefl 1 (hcard' ▸ h2))
    · exact h
  obtain ⟨g, a, σ, ε, hαnf⟩ :=
    (CFSG.LieType.Chevalley.ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 α
  obtain ⟨s, hs, hσpow, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_frobenius_pow_eq hf hcard' σ
  have hcomp : (iterateFrobenius L 2 s).comp ι = ι.comp σ.toRingHom := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change iterateFrobenius L 2 s (algebraMap K L c) = algebraMap K L (σ c)
    rw [hσpow c, map_pow, iterateFrobenius_def]
  let Frs : L →+* L := iterateFrobenius L 2 s
  have hp2 : p ≠ 2 := by omega
  have hcop2 : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega)
  have hcop : Nat.Coprime (2 ^ s) p := hcop2.pow_left s
  let c : (ZMod p)ˣ := ZMod.unitOfCoprime (2 ^ s) hcop
  have hcval : (c : ZMod p) = ((2 ^ s : ℕ) : ZMod p) := by
    dsimp [c]
  let aL : Fin Tag.E6.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i)
  let QL : ModGL .E6 L := exactQ .E6 L (ε : ℕ)
  let baseG : ModGL .E6 L := baseChangeGL ι (g : ModGL .E6 K)
  let dL : ModGL .E6 L := rootDiagUnit .E6 aL
  let FrG : ModGL .E6 L := Units.map (entrywiseHom Frs) F.D.g0
  let x : ModGL .E6 L := F.D.g0⁻¹ * (baseG * dL) * QL * FrG * QL⁻¹
  let x0 : ModGL .E6 L := x * QL
  have hQbase : baseChangeGL ι (exactQ .E6 K ε) = QL := by
    rw [show exactQ .E6 K ε = (diagramMap TwistTag.E6 K) ^ (ε : ℕ) from rfl,
      show QL = (diagramMap TwistTag.E6 L) ^ (ε : ℕ) from rfl]
    exact (map_pow (baseChangeGL ι) (diagramMap TwistTag.E6 K) (ε : ℕ)).trans
      (by rw [baseChangeGL_diagramMap])
  have hσbase : ∀ y : ModGL .E6 K,
      baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) y) =
        Units.map (entrywiseHom Frs) (baseChangeGL ι y) := by
    intro y
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, ← hcomp,
      ← baseChangeGL_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL]
  have hframeV : ∀ u : Fin Tag.F4.rank → ZMod p,
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u) ∈
        ExcFrames.e6SplitTorsion L p := by
    intro u
    obtain ⟨b, hb, h05, h24, hframe⟩ :=
      ExcFrames.frameDiag_twE6SplitTheta_eq_rootDiagUnit hζ u
    exact ⟨b, hb, h05, h24, hframe⟩
  have hFrS_d : ∀ u : Fin Tag.F4.rank → ZMod p,
      Units.map (entrywiseHom Frs) (ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p u)) =
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p ((c : ZMod p) • u)) := by
    intro u
    have hpow : Units.map (entrywiseHom Frs)
        (ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u)) =
        ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u) ^ (2 ^ s) := by
      let b : Fin Tag.E6.rank → Lˣ := TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord Tag.E6 p (ExcFrames.twE6SplitTheta p u))
      change Units.map (entrywiseHom Frs) (rootDiagUnit Tag.E6 b) =
        rootDiagUnit Tag.E6 b ^ (2 ^ s)
      rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_rootDiagUnit, rootDiagUnit_pow]
      congr 1
    have hθ : ExcFrames.twE6SplitTheta p ((c : ZMod p) • u) =
        (2 ^ s : ℕ) • ExcFrames.twE6SplitTheta p u := by
      rw [ExcFrames.twE6SplitTheta_smul, hcval, Nat.cast_smul_eq_nsmul]
    exact hpow.trans
      ((NoTvAut.frameDiag_nsmul (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p u) (2 ^ s)).symm.trans
          (congrArg (ExcFrames.frameDiag (τ := Tag.E6) ζ hζ) hθ.symm))
  have hQd_forward : ∀ u : Fin Tag.F4.rank → ZMod p,
      QL * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u) * QL⁻¹ =
        ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u) := by
    intro u
    fin_cases ε
    · change (1 : ModGL .E6 L) * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p u) * 1⁻¹ = _
      rw [inv_one, one_mul, mul_one]
    · let P : ModGL Tag.E6 L := diagramMap TwistTag.E6 L
      have hQ : QL = P := by
        change P ^ 1 = P
        exact pow_one _
      let d : ModGL Tag.E6 L :=
        ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u)
      have hd : (d : ModGL TwistTag.E6.tag L) ∈
          twistedFixedGroup TwistTag.E6 L (RingHom.id L) :=
        graphFixedRootGroup_le TwistTag.E6 L (RingHom.id L)
          (ExcFrames.frameDiag_twE6SplitTheta_mem hζ (by rfl) u)
      have hcomm : P * d = d * P := diagramMap_mul_of_mem_twistedFixedGroup hd
      rw [hQ]
      change P * d * P⁻¹ = d
      rw [hcomm, mul_inv_cancel_right]
  have hbaseα : ∀ u : Fin Tag.F4.rank → ZMod p,
      baseChangeGL ι ((α (pFrame F hp ζ hζo hζ hpq hlong
        (Multiplicative.ofAdd u)) : adjointGroup .E6 K) : ModGL .E6 K) =
      F.D.g0 * (x0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p ((c : ZMod p) • u)) * x0⁻¹) * F.D.g0⁻¹ := by
    intro u
    have h1 := congrArg (baseChangeGL ι) (hαnf (pFrame F hp ζ hζo hζ hpq hlong
      (Multiplicative.ofAdd u)))
    simp only [map_mul, map_inv] at h1
    rw [baseChangeGL_rootDiagUnit, hQbase, hσbase] at h1
    rw [pFrame_baseChange F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd u)] at h1
    simp only [map_mul, map_inv] at h1
    rw [hFrS_d] at h1
    have hgroup : baseG * dL * QL * FrG *
        ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p ((c : ZMod p) • u)) *
          FrG⁻¹ * QL⁻¹ * dL⁻¹ * baseG⁻¹ =
        F.D.g0 * (x0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
          (ExcFrames.twE6SplitTheta p ((c : ZMod p) • u)) * x0⁻¹) * F.D.g0⁻¹ := by
      dsimp only [x0, x, FrG]
      group
    rw [h1]
    exact hgroup
  have hEbase : ∀ e ∈ E, ∃ d ∈ ExcFrames.e6SplitTorsion L p,
      baseChangeGL ι (e : ModGL .E6 K) = F.D.g0 * d * F.D.g0⁻¹ := by
    intro e he
    have he' : e ∈ (pFrame F hp ζ hζo hζ hpq hlong).range := by
      rwa [pFrame_range F hp hp5 ζ hζo hζ hpq hlong]
    obtain ⟨u, rfl⟩ := he'
    refine ⟨ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
      (ExcFrames.twE6SplitTheta p u.toAdd), hframeV u.toAdd, ?_⟩
    exact pFrame_baseChange F hp ζ hζo hζ hpq hlong u
  have hx0_action : ∀ u : Fin Tag.F4.rank → ZMod p,
      x0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u) * x0⁻¹ =
      x * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u) * x⁻¹ := by
    intro u
    calc
      x0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p u) * x0⁻¹
          = x * (QL * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
              (ExcFrames.twE6SplitTheta p u) * QL⁻¹) * x⁻¹ := by
            dsimp only [x0]
            group
      _ = x * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
            (ExcFrames.twE6SplitTheta p u) * x⁻¹ := by
            rw [hQd_forward u]
  have hxV : ∀ v ∈ ExcFrames.e6SplitTorsion L p,
      x * v * x⁻¹ ∈ ExcFrames.e6SplitTorsion L p := by
    intro v hv
    obtain ⟨a0, ha0p, h05, h24, rfl⟩ := hv
    obtain ⟨u0, hu0⟩ := ExcFrames.exists_frameDiag_twE6SplitTheta_eq hp5 hζo hζ ha0p h05 h24
    let u1 : Fin Tag.F4.rank → ZMod p := ((c⁻¹ : (ZMod p)ˣ) : ZMod p) • u0
    have hcu1 : (c : ZMod p) • u1 = u0 := by
      dsimp only [u1]
      rw [smul_smul]
      rw [show (((c : (ZMod p)ˣ) : ZMod p) *
        (((c⁻¹ : (ZMod p)ˣ) : ZMod p))) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]
    have hmemE : α (pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd u1)) ∈ E :=
      (hα _).mpr (pFrame_mem F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd u1))
    obtain ⟨d, hd, hd_eq⟩ := hEbase _ hmemE
    have hbase_u1 := hbaseα u1
    have hxd0 : x0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p ((c : ZMod p) • u1)) * x0⁻¹ = d := by
      have h := hbase_u1.symm.trans hd_eq
      exact mul_left_cancel (mul_right_cancel h)
    have hxd : x * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p ((c : ZMod p) • u1)) * x⁻¹ = d := by
      rw [← hx0_action ((c : ZMod p) • u1)]
      exact hxd0
    rw [hcu1] at hxd
    have hu0' : ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p u0) = rootDiagUnit Tag.E6 a0 := hu0
    rw [hu0'] at hxd
    rw [hxd]
    exact hd
  have hxadj : x ∈ adjointGroup .E6 L := by
    have hFrG : FrG ∈ adjointGroup .E6 L :=
      CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup Frs F.D.g0_mem
    have hP : QL * FrG * QL⁻¹ ∈ adjointGroup .E6 L := by
      fin_cases ε
      · simp [QL, exactQ]
        exact hFrG
      · have hQ : QL = diagramMap TwistTag.E6 L := by
          change (diagramMap TwistTag.E6 L : ModGL Tag.E6 L) ^ 1 = _
          exact pow_one _
        rw [hQ]
        exact CFSG.LieType.Chevalley.E6GraphLevi.diagramMap_conj_mem_adjointGroup' hFrG
    have h1 : F.D.g0⁻¹ * (baseG * dL) ∈ adjointGroup .E6 L :=
      mul_mem (inv_mem F.D.g0_mem)
        (mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι g.2)
          (CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_of_any
            (rootDiagUnit_mem_torusGroup aL)))
    have hxsplit : x = (F.D.g0⁻¹ * (baseG * dL)) * (QL * FrG * QL⁻¹) := by
      dsimp only [x]
      group
    rw [hxsplit]
    exact mul_mem h1 hP
  obtain ⟨u, hu⟩ :=
    ExcFrames.exists_foldedWeyl_of_normalizes_e6SplitTorsion hp5 hζo hζ hxadj hxV
  have hact : ∀ t : Fin Tag.F4.rank → ZMod p,
      x * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p ((c : ZMod p) • t)) * x⁻¹ =
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p ((c : ZMod p) • TableBExc.torusAct Tag.F4 p u t)) := by
    intro t
    have hs : TableBExc.torusAct Tag.F4 p u ((c : ZMod p) • t) =
        (c : ZMod p) • TableBExc.torusAct Tag.F4 p u t := by
      simpa only [NoTvAut.torusActHom_apply] using
        ZMod.map_smul (NoTvAut.torusActHom Tag.F4 p u) (c : ZMod p) t
    exact (hu ((c : ZMod p) • t)).trans
      (congrArg (fun v => ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p v)) hs)
  refine ⟨c, u, fun t => ?_⟩
  apply Subtype.ext
  apply baseChangeGL_injective ι
  rw [hbaseα t, hx0_action, hact t]
  exact (pFrame_baseChange F hp ζ hζo hζ hpq hlong
    (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct Tag.F4 p u t))).symm


end CFSG.StandardType.E6RelativeLangWeyl
