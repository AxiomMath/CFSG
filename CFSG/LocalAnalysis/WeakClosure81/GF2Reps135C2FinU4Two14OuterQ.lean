module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14OuterMod
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14FrobGraph
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Swap
import all CFSG.HardMathSupport.U4FF.ClassLocData

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped Matrix MatrixGroups
open CFSG.HardMathSupport.U4FF (SU4 Tmod TIdx Trep Trep_apply hwv UpperU LowerU
  Tmod_fixed_and_irreducible span_orbit_eq_top)
open CFSG.QuasithinUnique.Setup.X7 (fixedSub mem_fixedSub)

open CFSG.HardMathSupport.U4FF (locData bitF ambDim fsOf locM ambRepF locR locSpec locValid f2
  frobTw twistHom Tmod_eq TmodΦ_apply kronDep_apply)
open Matrix

private abbrev w183AmbI : Type := Fin (ambDim (fsOf true false true))

private abbrev w183LocI : Type := Fin (locM true false true)

private theorem w183LocM : locM true false true = 14 := by decide +kernel

private def w183Sel (v : Fin 4 → Fin 14) : Fin 4 → w183LocI := fun i => Fin.cast w183LocM (v i)

private def w183Tau : Matrix w183AmbI w183AmbI (ZMod 2) := finU4SwapMat (ZMod 2)

private def w183B : Matrix w183AmbI w183LocI (ZMod 2) :=
  (locData true false true).bcols.toMat (ambDim (fsOf true false true)) (locM true false true)

private def w183Pm : Matrix w183LocI w183AmbI (ZMod 2) :=
  (locData true false true).pmcols.toMat (locM true false true) (ambDim (fsOf true false true))

private def w183Z : w183AmbI → ZMod 2 := fun x => bitF (locData true false true).z x

private def w183Zeta : w183AmbI → ZMod 2 := fun x => bitF (locData true false true).zeta x

private def w183Pi : Matrix w183AmbI w183AmbI (ZMod 2) :=
  w183B * w183Pm + vecMulVec w183Z w183Zeta

private def w183P : Matrix w183LocI w183LocI (ZMod 2) := w183Pm * w183Tau * w183B

private def w183Amb (g : SL(4, ZMod 2)) : Matrix w183AmbI w183AmbI (ZMod 2) :=
  ambRepF (ZMod 2) (fsOf true false true) g

private def w183Q1 : Matrix w183LocI w183LocI (ZMod 2) :=
  w183Pm * (w183Amb (finU4J (ZMod 2)) * w183B) * w183P

private def w183Qz : Matrix w183LocI w183LocI (ZMod 2) :=
  w183Pm * (w183Amb (finU4Z1 (ZMod 2)) * w183B) * w183Q1

private theorem w183Pi_tauB : w183Pi * (w183Tau * w183B) = w183Tau * w183B := by
  decide +kernel

private theorem w183Tau_z : w183Tau *ᵥ w183Z = w183Z := by decide +kernel

private theorem w183Q1_invol : w183Q1 * w183Q1 = 1 := by decide +kernel

private theorem w183Qz_invol : w183Qz * w183Qz = 1 := by decide +kernel

private def w183RowP : Fin 4 → w183LocI := w183Sel ![0, 1, 2, 5]

private def w183RowQ1 : Fin 4 → w183LocI := w183Sel ![0, 1, 3, 7]

private def w183ColQ1 : Fin 4 → w183LocI := w183Sel ![0, 1, 3, 7]

private theorem w183Q1_minor : (w183Q1 - 1).submatrix w183RowQ1 w183ColQ1 = 1 := by
  decide +kernel

private theorem w183Q1_rank : 4 ≤ (w183Q1 - 1).rank := by
  have h : ((w183Q1 - 1).submatrix w183RowQ1 w183ColQ1).rank ≤ (w183Q1 - 1).rank :=
    Matrix.rank_submatrix_le _ _ _
  rw [w183Q1_minor, Matrix.rank_one, Fintype.card_fin] at h
  exact h

private def w183RowQz : Fin 4 → w183LocI := w183Sel ![0, 1, 4, 12]

private def w183ColQz : Fin 4 → w183LocI := w183Sel ![0, 1, 2, 7]

private theorem w183Qz_minor : (w183Qz - 1).submatrix w183RowQz w183ColQz = 1 := by
  decide +kernel

private theorem w183Qz_rank : 4 ≤ (w183Qz - 1).rank := by
  have h : ((w183Qz - 1).submatrix w183RowQz w183ColQz).rank ≤ (w183Qz - 1).rank :=
    Matrix.rank_submatrix_le _ _ _
  rw [w183Qz_minor, Matrix.rank_one, Fintype.card_fin] at h
  exact h

private def w183Eq : TIdx finU4Label ≃ w183LocI := Equiv.piUnique _

private theorem w183Tmod_eq {K : Type} [Field K] [Finite K]
    [CharP K 2] {E : Type} [Field E] [CharP E 2] [Algebra K E] (x : SU4 K 1) :
    Tmod K finU4Label E x =
      (locR true false true E (twistHom 1 (frobTw K E 0) x)).submatrix w183Eq w183Eq := by
  ext p q
  rw [Tmod_eq, TmodΦ_apply, kronDep_apply, Matrix.submatrix_apply, Fin.prod_univ_one]
  rfl

private theorem w183Tau_map {E : Type} [Field E] [CharP E 2] :
    w183Tau.map (f2 E) = finU4SwapMat E := by
  ext x y
  simp [w183Tau, finU4SwapMat, apply_ite]

private theorem w183P_intertwines {E : Type} [Field E]
    [CharP E 2] (g : SL(4, E)) :
    w183P.map (f2 E) * locR true false true E g =
      locR true false true E (Matrix.SpecialLinearGroup.transpose g⁻¹) * w183P.map (f2 E) := by
  set S := locSpec true false true (locValid true false true).1 with hS
  have hB : S.Pik E * (finU4SwapMat E * S.Bk E) = finU4SwapMat E * S.Bk E := by
    have h := congrArg (fun M => M.map (f2 E)) w183Pi_tauB
    simp only [Matrix.map_mul, w183Tau_map] at h
    rw [S.Pik_eq_map]
    exact h
  have hz : finU4SwapMat E *ᵥ S.zk E = S.zk E := by
    have h := CFSG.HardMathSupport.U4FF.map_mulVec' (f2 E) w183Tau w183Z
    rw [w183Tau_z, w183Tau_map] at h
    exact h
  have key := locMat_swap_intertwines S (finU4SwapMat E) (finU4SwapMat_mul_self E) hB hz
    (finU4SwapMat_mul_ambRepF_mul E g)
  have hP : w183P.map (f2 E) = S.Pmk E * finU4SwapMat E * S.Bk E := by
    rw [w183P, Matrix.map_mul, Matrix.map_mul, w183Tau_map]
    rfl
  rw [hP]
  exact key

private theorem w183Q1_map {E : Type} [Field E] [CharP E 2] :
    w183Q1.map (f2 E) = locR true false true E (finU4J E) * w183P.map (f2 E) := by
  have hJ := ambRepF_natDual_map (f2 E) (finU4J (ZMod 2))
  rw [finU4J_map] at hJ
  have hA : (w183Amb (finU4J (ZMod 2))).map (f2 E) =
      ambRepF E (fsOf true false true) (finU4J E) := hJ
  rw [w183Q1, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hA]
  rfl

private theorem w183Qz_map {E : Type} [Field E] [CharP E 2] :
    w183Qz.map (f2 E) = locR true false true E (finU4Z1 E * finU4J E) * w183P.map (f2 E) := by
  have hZ := ambRepF_natDual_map (f2 E) (finU4Z1 (ZMod 2))
  rw [finU4Z1_map] at hZ
  have hA : (w183Amb (finU4Z1 (ZMod 2))).map (f2 E) =
      ambRepF E (fsOf true false true) (finU4Z1 E) := hZ
  have hloc : locR true false true E (finU4Z1 E) = w183Pm.map (f2 E) *
      (ambRepF E (fsOf true false true) (finU4Z1 E) * w183B.map (f2 E)) := rfl
  rw [w183Qz, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hA, w183Q1_map, map_mul, hloc]
  simp only [Matrix.mul_assoc]

private theorem w183_intertwine_of_conj {E : Type} [Field E]
    [CharP E 2] {W g h : SL(4, E)}
    (hW : h * W = W * Matrix.SpecialLinearGroup.transpose g⁻¹) :
    (locR true false true E W * w183P.map (f2 E)) * locR true false true E g =
      locR true false true E h * (locR true false true E W * w183P.map (f2 E)) := by
  calc (locR true false true E W * w183P.map (f2 E)) * locR true false true E g
      = locR true false true E W * (w183P.map (f2 E) * locR true false true E g) :=
        Matrix.mul_assoc _ _ _
    _ = locR true false true E W * (locR true false true E
          (Matrix.SpecialLinearGroup.transpose g⁻¹) * w183P.map (f2 E)) := by
        rw [w183P_intertwines g]
    _ = locR true false true E (W * Matrix.SpecialLinearGroup.transpose g⁻¹) *
          w183P.map (f2 E) := by rw [map_mul, Matrix.mul_assoc]
    _ = locR true false true E (h * W) * w183P.map (f2 E) := by rw [hW]
    _ = locR true false true E h * (locR true false true E W * w183P.map (f2 E)) := by
        rw [map_mul, Matrix.mul_assoc]

private theorem w183_intertwine_one {K : Type} [Field K]
    [Finite K] [CharP K 2] (E : Type) [Field E] [CharP E 2] [Algebra K E] (x y : SU4 K 1)
    (hxy : FinU4FrobPair (1 : Matrix (Fin 4) (Fin 4) K) x y) :
    (w183Q1.submatrix w183Eq w183Eq).map (ZMod.castHom (dvd_refl 2) E) * Tmod K finU4Label E x =
      Tmod K finU4Label E y *
        (w183Q1.submatrix w183Eq w183Eq).map (ZMod.castHom (dvd_refl 2) E) := by
  set φ := frobTw K E 0 with hφ
  have hW : twistHom 1 φ y * finU4J E =
      finU4J E * Matrix.SpecialLinearGroup.transpose (twistHom 1 φ x)⁻¹ :=
    finU4FrobPair_conj φ hxy (by simp) (finU4J E)
      (by rw [Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.one_mul]; rfl)
  have key := w183_intertwine_of_conj hW
  rw [← w183Q1_map] at key
  change (w183Q1.submatrix w183Eq w183Eq).map (f2 E) * Tmod K finU4Label E x =
    Tmod K finU4Label E y * (w183Q1.submatrix w183Eq w183Eq).map (f2 E)
  rw [w183Tmod_eq, w183Tmod_eq, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, key]

private theorem w183_intertwine_z {K : Type} [Field K]
    [Finite K] [CharP K 2] (E : Type) [Field E] [CharP E 2] [Algebra K E] (x y : SU4 K 1)
    (hxy : FinU4FrobPair (finU4ZMat K) x y) :
    (w183Qz.submatrix w183Eq w183Eq).map (ZMod.castHom (dvd_refl 2) E) * Tmod K finU4Label E x =
      Tmod K finU4Label E y *
        (w183Qz.submatrix w183Eq w183Eq).map (ZMod.castHom (dvd_refl 2) E) := by
  set φ := frobTw K E 0 with hφ
  have hW : twistHom 1 φ y * (finU4Z1 E * finU4J E) =
      (finU4Z1 E * finU4J E) * Matrix.SpecialLinearGroup.transpose (twistHom 1 φ x)⁻¹ :=
    finU4FrobPair_conj φ hxy (by rw [finU4ZMat_map]; exact finU4ZMat_mul_self E)
      (finU4Z1 E * finU4J E)
      (by rw [Matrix.SpecialLinearGroup.coe_mul, finU4ZMat_map]; rfl)
  have key := w183_intertwine_of_conj hW
  rw [← w183Qz_map] at key
  change (w183Qz.submatrix w183Eq w183Eq).map (f2 E) * Tmod K finU4Label E x =
    Tmod K finU4Label E y * (w183Qz.submatrix w183Eq w183Eq).map (f2 E)
  rw [w183Tmod_eq, w183Tmod_eq, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, key]

theorem finU4_explicit_intertwiner {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {Z : Matrix (Fin 4) (Fin 4) K}
    (hZ : Z = 1 ∨ Z = finU4ZMat K) :
    ∃ Q : Matrix (TIdx finU4Label) (TIdx finU4Label) (ZMod 2),
      (∀ (E : Type) [Field E] [CharP E 2] [Algebra K E] (x y : SU4 K 1), FinU4FrobPair Z x y →
        Q.map (ZMod.castHom (dvd_refl 2) E) * Tmod K finU4Label E x =
          Tmod K finU4Label E y * Q.map (ZMod.castHom (dvd_refl 2) E)) ∧
      Q * Q = 1 ∧ 4 ≤ (Q - 1).rank := by
  classical
  have hQ1 : (w183Q1.submatrix w183Eq w183Eq) * (w183Q1.submatrix w183Eq w183Eq) = 1 := by
    rw [Matrix.submatrix_mul_equiv, w183Q1_invol, Matrix.submatrix_one_equiv]
  have hQz : (w183Qz.submatrix w183Eq w183Eq) * (w183Qz.submatrix w183Eq w183Eq) = 1 := by
    rw [Matrix.submatrix_mul_equiv, w183Qz_invol, Matrix.submatrix_one_equiv]
  have hr1 : 4 ≤ (w183Q1.submatrix w183Eq w183Eq - 1).rank := by
    have h : w183Q1.submatrix w183Eq w183Eq - 1 = (w183Q1 - 1).submatrix w183Eq w183Eq := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply]
    rw [h, Matrix.rank_submatrix]
    exact w183Q1_rank
  have hrz : 4 ≤ (w183Qz.submatrix w183Eq w183Eq - 1).rank := by
    have h : w183Qz.submatrix w183Eq w183Eq - 1 = (w183Qz - 1).submatrix w183Eq w183Eq := by
      ext i j
      simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply]
    rw [h, Matrix.rank_submatrix]
    exact w183Qz_rank
  rcases hZ with rfl | rfl
  · exact ⟨w183Q1.submatrix w183Eq w183Eq,
      fun E _ _ _ x y hxy => w183_intertwine_one E x y hxy, hQ1, hr1⟩
  · exact ⟨w183Qz.submatrix w183Eq w183Eq,
      fun E _ _ _ x y hxy => w183_intertwine_z E x y hxy, hQz, hrz⟩

theorem finU4_commutant_scalar {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {E : Type} [Field E] [CharP E 2] [Algebra K E]
    (M : Matrix (TIdx finU4Label) (TIdx finU4Label) E)
    (hM : ∀ x : SU4 K 1, M * Tmod K finU4Label E x = Tmod K finU4Label E x * M) :
    ∃ c : E, M = c • 1 := by
  classical
  obtain ⟨hfix, -⟩ := Tmod_fixed_and_irreducible (K := K) (k := E) (n := 1) hK finU4Label
  have hspan := span_orbit_eq_top (K := K) (k := E) (n := 1) hK finU4Label
  have hMv_fix : M *ᵥ hwv finU4Label E ∈ fixedSub (Trep K finU4Label E) (UpperU K 1) := by
    intro u hu
    have hcomm := hM u
    have huv : Tmod K finU4Label E u *ᵥ hwv finU4Label E = hwv finU4Label E := by
      have h := mem_fixedSub.mp (by rw [hfix]; exact Submodule.mem_span_singleton_self _) u hu
      rwa [Trep_apply] at h
    rw [Trep_apply, Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, huv]
  have hMv_span : M *ᵥ hwv finU4Label E ∈ Submodule.span E {hwv finU4Label E} := by
    rw [← hfix]; exact hMv_fix
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hMv_span
  let f : (TIdx finU4Label → E) →ₗ[E] (TIdx finU4Label → E) :=
    Matrix.mulVecLin M - c • (LinearMap.id : (TIdx finU4Label → E) →ₗ[E] (TIdx finU4Label → E))
  refine ⟨c, ?_⟩
  have hkey : ∀ u : ↥(LowerU K 1),
      f (Trep K finU4Label E (u : SU4 K 1) (hwv finU4Label E)) = 0 := by
    intro u
    have hcomm := hM (u : SU4 K 1)
    rw [Trep_apply]
    show M *ᵥ (Tmod K finU4Label E (u : SU4 K 1) *ᵥ hwv finU4Label E) -
      c • (Tmod K finU4Label E (u : SU4 K 1) *ᵥ hwv finU4Label E) = 0
    have h1 : M *ᵥ (Tmod K finU4Label E (u : SU4 K 1) *ᵥ hwv finU4Label E) =
        c • (Tmod K finU4Label E (u : SU4 K 1) *ᵥ hwv finU4Label E) := by
      rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hc.symm, Matrix.mulVec_smul]
    rw [h1, sub_self]
  have hzero : f = 0 := by
    apply LinearMap.ext
    intro w
    rw [LinearMap.zero_apply]
    have hmem : w ∈ Submodule.span E (Set.range fun u : ↥(LowerU K 1) =>
        Trep K finU4Label E (u : SU4 K 1) (hwv finU4Label E)) := by
      rw [hspan]; exact Submodule.mem_top
    have hle : Submodule.span E (Set.range fun u : ↥(LowerU K 1) =>
        Trep K finU4Label E (u : SU4 K 1) (hwv finU4Label E)) ≤
        LinearMap.ker f := by
      rw [Submodule.span_le]
      rintro x ⟨u, rfl⟩
      exact hkey u
    exact hle hmem
  have hpoint : ∀ w : TIdx finU4Label → E, M *ᵥ w = c • w := by
    intro w
    have h := congrArg (fun g : (TIdx finU4Label → E) →ₗ[E] (TIdx finU4Label → E) => g w) hzero
    rw [LinearMap.zero_apply] at h
    change M *ᵥ w - c • w = 0 at h
    exact sub_eq_zero.mp h
  apply Matrix.ext_of_mulVec_single
  intro j
  trans c • Pi.single j (1 : E)
  · exact hpoint (Pi.single j 1)
  · rw [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem finU4_intertwiner_rank {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {Z : Matrix (Fin 4) (Fin 4) K}
    (hZ : Z = 1 ∨ Z = finU4ZMat K) {E : Type} [Field E] [Finite E] [CharP E 2] [Algebra K E]
    (N : Matrix (TIdx finU4Label) (TIdx finU4Label) E)
    (hN : ∀ x : SU4 K 1, ∃ y : SU4 K 1, FinU4FrobPair Z x y ∧
      N * Tmod K finU4Label E x = Tmod K finU4Label E y * N)
    (hN2 : N * N = 1) : 4 ≤ (N - 1).rank := by
  obtain ⟨Q, hQ, hQ2, hQr⟩ := finU4_explicit_intertwiner hK hZ
  set QE := Q.map (ZMod.castHom (dvd_refl 2) E) with hQE
  have hQE2 : QE * QE = 1 := by
    rw [hQE, ← Matrix.map_mul, hQ2, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcomm : ∀ x : SU4 K 1,
      (QE * N) * Tmod K finU4Label E x = Tmod K finU4Label E x * (QE * N) := by
    intro x
    obtain ⟨y, hxy, hNx⟩ := hN x
    have h1 : QE * Tmod K finU4Label E x = Tmod K finU4Label E y * QE := hQ E x y hxy
    have h2 : QE * Tmod K finU4Label E y = Tmod K finU4Label E x * QE := by
      calc QE * Tmod K finU4Label E y
          = QE * Tmod K finU4Label E y * (QE * QE) := by rw [hQE2, mul_one]
        _ = QE * (Tmod K finU4Label E y * QE) * QE := by simp only [mul_assoc]
        _ = QE * (QE * Tmod K finU4Label E x) * QE := by rw [← h1]
        _ = Tmod K finU4Label E x * QE := by
          rw [← mul_assoc, hQE2, one_mul]
    calc QE * N * Tmod K finU4Label E x
        = QE * (N * Tmod K finU4Label E x) := by rw [mul_assoc]
      _ = QE * (Tmod K finU4Label E y * N) := by rw [hNx]
      _ = (QE * Tmod K finU4Label E y) * N := by rw [mul_assoc]
      _ = (Tmod K finU4Label E x * QE) * N := by rw [h2]
      _ = Tmod K finU4Label E x * (QE * N) := by rw [mul_assoc]
  obtain ⟨c, hc⟩ := finU4_commutant_scalar hK (QE * N) hcomm
  have hNeq : N = c • QE := by
    calc N = QE * (QE * N) := by rw [← mul_assoc, hQE2, one_mul]
      _ = QE * (c • 1) := by rw [hc]
      _ = c • QE := by rw [mul_smul_comm, mul_one]
  have hcc : c * c = 1 := by
    have h : N * N = (c * c) • (QE * QE) := by
      rw [hNeq, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hN2, hQE2] at h
    have h' := congrFun (congrFun h (Classical.arbitrary _)) (Classical.arbitrary _)
    simpa using h'.symm
  have hc1 : c = 1 := by
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have h3 : (c + 1) * (c + 1) = 0 := by
      linear_combination hcc + (c + 1) * h2
    have h4 := mul_self_eq_zero.mp h3
    linear_combination h4 - h2
  rw [hNeq, hc1, one_smul]
  have hsub : QE - 1 = (Q - 1).map (ZMod.castHom (dvd_refl 2) E) := by
    rw [hQE, Matrix.map_sub _ (fun a b => map_sub _ a b),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hsub, finU4_rank_map_zmod_two]
  exact hQr

end CFSG.LocalAnalysis.WeakClosure81
