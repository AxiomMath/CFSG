module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignLevi
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative

private theorem frameCoord_smul
    {τ : Tag} {p : ℕ} (c : ZMod p) (s : Fin τ.rank → ZMod p) :
    ExcFrames.frameCoord τ p (c • s) = c • ExcFrames.frameCoord τ p s := by
  funext i
  simp only [ExcFrames.frameCoord, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_phiTwoTorus
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1) {g0 : ModGL τ (AlgebraicClosure K)}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K} (hι₀ : Function.Injective ι₀)
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) :
    ∃ T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K,
      Function.Injective T ∧ T.range = ι₀.range ∧
      ∀ t : Fin τ.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
          g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  classical
  let f : (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) :=
    { toFun := ExcFrames.frameCoord τ p
      map_zero' := ExcFrames.frameCoord_zero
      map_add' := ExcFrames.frameCoord_add }
  have hfinj : Function.Injective f := ExcFrames.frameCoord_injective hdet
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  let e : (Fin τ.rank → ZMod p) ≃+ (Fin τ.rank → ZMod p) :=
    AddEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K :=
    ι₀.comp (AddEquiv.toMultiplicative e.symm).toMonoidHom
  have hTapply : ∀ t : Fin τ.rank → ZMod p, T (ofAdd t) = ι₀ (ofAdd (e.symm t)) := fun _ => rfl
  have he : ∀ t : Fin τ.rank → ZMod p, ExcFrames.frameCoord τ p (e.symm t) = t := by
    intro t
    change f (e.symm t) = t
    exact AddEquiv.apply_symm_apply e t
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x y hxy
    exact (AddEquiv.toMultiplicative e.symm).injective (hι₀ hxy)
  · rw [show T = ι₀.comp (AddEquiv.toMultiplicative e.symm).toMonoidHom from rfl,
      MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
        (AddEquiv.toMultiplicative e.symm).surjective, Subgroup.map_top]
  · intro t
    rw [hTapply t, hbase (e.symm t), ExcFrames.frameDiag, he t]

theorem conj_phiTwoTorus
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [NeZero p] {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {g0 : ModGL τ (AlgebraicClosure K)}
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {v : WeylGroup τ} {n : adjointGroup τ K}
    (hn : baseChangeGL (algebraMap K (AlgebraicClosure K)) ((n : adjointGroup τ K) : ModGL τ K) =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹)
    (t : Fin τ.rank → ZMod p) :
    n * T (ofAdd t) * n⁻¹ = T (ofAdd (TableBExc.E6Three.adAct τ p v t)) := by
  refine Subtype.ext ?_
  refine baseChangeGL_injective (τ := τ) (f := algebraMap K (AlgebraicClosure K)) ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  rw [hn, hT t, hT (TableBExc.E6Three.adAct τ p v t)]
  calc
    (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹) *
        (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹) *
          (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹)⁻¹
        = g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v *
            rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹) * g0⁻¹ := by
          group
    _ = g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ
          (TableBExc.E6Three.adAct τ p v t)) * g0⁻¹ := by
          rw [canonicalRep_conj_rootDiagUnit, TableBExc.E6Three.weylTuple_zetaVec]

private theorem frobenius_baseChangeGL
    {τ : Tag} {K : Type} [Field K]
    [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (y : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
  have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, hFr, ← map_pow]
    congr 1
    letI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  calc
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) y)
        = baseChangeGL Fr (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) :=
          units_map_entrywiseHom_eq_baseChangeGL Fr _
    _ = baseChangeGL (Fr.comp (algebraMap K (AlgebraicClosure K))) y :=
          baseChangeGL_baseChangeGL (f := algebraMap K (AlgebraicClosure K)) Fr y
    _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by rw [hcomp]

private theorem frobenius_frameDiag
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    Units.map (entrywiseHom Fr) (ExcFrames.frameDiag ζ hζ s) =
      ExcFrames.frameDiag ζ hζ ((Nat.card K : ZMod p) • s) := by
  rw [ExcFrames.frameDiag, ExcFrames.frameDiag]
  refine Units.ext ?_
  rw [Units.coe_map]
  change entrywise Fr (rootDiag (TableBExc.E6Three.zetaVec ζ hζ
      (ExcFrames.frameCoord τ p s))) =
    rootDiag (TableBExc.E6Three.zetaVec ζ hζ
      (ExcFrames.frameCoord τ p ((Nat.card K : ZMod p) • s)))
  rw [entrywise_rootDiag]
  congr 1
  funext i
  have hmap : ∀ u : (AlgebraicClosure K)ˣ, Units.map Fr.toMonoidHom u = u ^ Nat.card K := by
    intro u
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hFr (u : AlgebraicClosure K)
  rw [hmap]
  rw [frameCoord_smul]
  change (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
      (.ofAdd (ExcFrames.frameCoord τ p s i))) ^ Nat.card K =
    CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
      (.ofAdd (((Nat.card K : ZMod p) • ExcFrames.frameCoord τ p s) i))
  rw [← zpow_natCast (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
      (.ofAdd (ExcFrames.frameCoord τ p s i))) (Nat.card K)]
  rw [TableBExc.E6Three.zmodPowHom_zpow]
  congr 1
  push_cast
  rw [Pi.smul_apply, smul_eq_mul]

theorem torusAct_eq_neg_of_langFrame
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] [Finite K] (hpq : p ∣ Nat.card K + 1)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (s : Fin τ.rank → ZMod p) : TableBExc.torusAct τ p w s = -s := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hq : (Nat.card K : ZMod p) = -1 := by
    have h1 : (Nat.card K : ZMod p) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact (ZMod.natCast_eq_zero_iff (Nat.card K + 1) p).2 hpq
    exact add_eq_zero_iff_eq_neg.mp h1
  have hfix : g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹ =
      g0 * ExcFrames.frameDiag ζ hζ
        (TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s)) * g0⁻¹ := by
    calc
      g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹
          = baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((ι₀ (ofAdd s) : adjointGroup τ K) : ModGL τ K) := (hbase s).symm
      _ = Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((ι₀ (ofAdd s) : adjointGroup τ K) : ModGL τ K)) :=
            (frobenius_baseChangeGL hFr _).symm
      _ = Units.map (entrywiseHom Fr)
              (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) := by rw [hbase s]
      _ = Units.map (entrywiseHom Fr) g0 *
            Units.map (entrywiseHom Fr) (ExcFrames.frameDiag ζ hζ s) *
              (Units.map (entrywiseHom Fr) g0)⁻¹ := by simp only [map_mul, map_inv]
      _ = (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) *
            ExcFrames.frameDiag ζ hζ ((Nat.card K : ZMod p) • s) *
              (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ := by
            rw [hg0, frobenius_frameDiag hFr hζ s]
      _ = g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
            ExcFrames.frameDiag ζ hζ ((Nat.card K : ZMod p) • s) *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ := by
            group
      _ = g0 * ExcFrames.frameDiag ζ hζ
            (TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s)) * g0⁻¹ := by
            rw [ExcFrames.canonicalRep_conj_frameDiag]
  have hframe : ExcFrames.frameDiag ζ hζ s =
      ExcFrames.frameDiag ζ hζ (TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s)) := by
    calc
      ExcFrames.frameDiag ζ hζ s
          = g0⁻¹ * (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) * g0 := by group
      _ = g0⁻¹ * (g0 * ExcFrames.frameDiag ζ hζ
            (TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s)) * g0⁻¹) * g0 := by
            rw [hfix]
      _ = ExcFrames.frameDiag ζ hζ
            (TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s)) := by group
  have hs : s = TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s) :=
    ExcFrames.frameDiag_injective hζo hζ hdet hframe
  have hlin : TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s) =
      (Nat.card K : ZMod p) • TableBExc.torusAct τ p w s := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact map_nsmul (NoTvAut.torusActHom τ p w) (Nat.card K) s
  have hs' : s = -TableBExc.torusAct τ p w s := by
    calc
      s = TableBExc.torusAct τ p w ((Nat.card K : ZMod p) • s) := hs
      _ = (Nat.card K : ZMod p) • TableBExc.torusAct τ p w s := hlin
      _ = -TableBExc.torusAct τ p w s := by
            rw [hq]
            ext i
            simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
            exact neg_one_mul _
  have hA : -s = TableBExc.torusAct τ p w s := neg_eq_iff_eq_neg.mpr hs'
  exact hA.symm

private theorem smul_eq_neg_of_torusAct_eq_neg_aux
    {τ : Tag} {p : ℕ} [NeZero p] {w : WeylGroup τ}
    (hw : ∀ s : Fin τ.rank → ZMod p, TableBExc.torusAct τ p w s = -s)
    (hcongr : ∀ {δ δ' : Fin τ.rank → ℤ}, IsRoot τ δ → IsRoot τ δ' →
      (∀ i, (p : ℤ) ∣ CFSG.LieType.Steinberg.Adjoint.iform δ' (Pi.single i 1) -
        CFSG.LieType.Steinberg.Adjoint.iform δ (Pi.single i 1)) → δ' = δ)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : w • β = -β := by
  let s : Fin τ.rank → ZMod p := TableBExc.redMod τ p β
  have hlift : TableBExc.redMod τ p (TableBExc.liftMod τ p s) =
      TableBExc.redMod τ p β := by
    rw [TableBExc.redMod_liftMod]
  have hs : TableBExc.torusAct τ p w s = TableBExc.redMod τ p (w • β) :=
    TableBExc.redMod_smul_eq w hlift
  have hneg : TableBExc.redMod τ p (w • β) = -TableBExc.redMod τ p β := by
    rw [← hs, hw s]
  have hdvd : ∀ j, (p : ℤ) ∣ (w • β + β) j := by
    intro j
    have h := congrFun hneg j
    simp only [TableBExc.redMod, Pi.neg_apply] at h
    have h0 : (((w • β + β) j : ℤ) : ZMod p) = 0 := by
      rw [show (w • β + β) j = (w • β) j + β j from rfl, Int.cast_add, h]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0
  have hiform : ∀ i, (p : ℤ) ∣ CFSG.LieType.Steinberg.Adjoint.iform (w • β) (Pi.single i 1) -
      CFSG.LieType.Steinberg.Adjoint.iform (-β) (Pi.single i 1) := by
    intro i
    have hdiv : (p : ℤ) ∣
        CFSG.LieType.Steinberg.Adjoint.iform (w • β + β) (Pi.single i 1) := by
      rw [CFSG.LieType.Steinberg.Adjoint.iform]
      refine Finset.dvd_sum fun j _ => Finset.dvd_sum fun l _ => ?_
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (hdvd j) _) _
    have hgoal : CFSG.LieType.Steinberg.Adjoint.iform (w • β) (Pi.single i 1) -
        CFSG.LieType.Steinberg.Adjoint.iform (-β) (Pi.single i 1) =
        CFSG.LieType.Steinberg.Adjoint.iform (w • β + β) (Pi.single i 1) := by
      rw [iform_neg_left, sub_neg_eq_add]
      rw [CFSG.LieType.Steinberg.Adjoint.iform, CFSG.LieType.Steinberg.Adjoint.iform,
        CFSG.LieType.Steinberg.Adjoint.iform]
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hgoal]
    exact hdiv
  exact hcongr (IsRoot.neg hβ) (IsRoot.smul hβ w) hiform

theorem smul_eq_neg_of_torusAct_eq_neg
    {τ : Tag} {p : ℕ}
    (hτ : τ = .E7 ∨ τ = .E8) [NeZero p] (hp3 : 3 ≤ p)
    {w : WeylGroup τ} (hw : ∀ s : Fin τ.rank → ZMod p, TableBExc.torusAct τ p w s = -s)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : w • β = -β := by
  rcases hτ with rfl | rfl
  · exact smul_eq_neg_of_torusAct_eq_neg_aux hw
      (fun hδ hδ' h => CFSG.SeitzReduction.E7Pilot.eq_of_dvd_iform_sub hp3 hδ hδ' h) hβ
  · exact smul_eq_neg_of_torusAct_eq_neg_aux hw
      (fun hδ hδ' h => CFSG.SeitzReduction.E8Pilot.eq_of_dvd_iform_sub hp3 hδ hδ' h) hβ

end CFSG.StandardType.PhiTwoRootGen

end
