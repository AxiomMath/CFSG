module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSLAct
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDConversePSL
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.Classical2 CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

theorem carrierSL_natCast_ne_zero {L : Type} [Field L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (p : L) ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm

theorem carrierSL_fieldEquiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n) : Nonempty (GaloisField 2 n ≃+* K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (by omega)
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, hK]

private theorem slMap_comp_symm {F K : Type} [Field F] [Field K] (e : F ≃+* K) {n : ℕ}
    (A : SL(n, K)) :
    Matrix.SpecialLinearGroup.map (e : F →+* K)
      (Matrix.SpecialLinearGroup.map (e.symm : K →+* F) A) = A := by
  apply Subtype.ext
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact e.apply_symm_apply (A i j)

private theorem conjSLn_eq_conjSL {F : Type} [Field F] {m : ℕ}
    (A : GL (Fin (m + 1)) F) (y : SL(m + 1, F)) :
    conjSLn A y = InnerDiagA.conjSL A y := by
  apply Subtype.ext
  rw [coe_conjSLn, InnerDiagA.coe_conjSL]

private theorem sl_map_conjSLn {F K : Type} [Field F] [Field K] (e : F ≃+* K) {m : ℕ}
    (M : GL (Fin (m + 1)) K) (y : SL(m + 1, F)) :
    Matrix.SpecialLinearGroup.map (e : F →+* K)
      (conjSLn (Matrix.GeneralLinearGroup.map (e.symm : K →+* F) M) y) =
      conjSLn M (Matrix.SpecialLinearGroup.map (e : F →+* K) y) := by
  set N : GL (Fin (m + 1)) F := Matrix.GeneralLinearGroup.map (e.symm : K →+* F) M
  have hA : (((N : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
      ⇑(e : F →+* K)) =
      (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    ext i j
    simp [N, Matrix.GeneralLinearGroup.map_apply]
  have hB : (((y : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map ⇑(e : F →+* K)) =
      ((Matrix.SpecialLinearGroup.map (e : F →+* K) y :
        SL(m + 1, K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hC : (((N⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
      ⇑(e : F →+* K)) =
      ((M⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    have hunit : Matrix.GeneralLinearGroup.map (e : F →+* K) N⁻¹ = M⁻¹ := by
      rw [map_inv]
      congr 1
      apply Units.ext
      ext i j
      simp [N, Matrix.GeneralLinearGroup.map_apply]
    have hmat : ((↑(Matrix.GeneralLinearGroup.map (e : F →+* K) N⁻¹) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K)) =
        ((M⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :=
      congrArg (fun X : GL (Fin (m + 1)) K =>
        (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) hunit
    have hmap : (((N⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
        ⇑(e : F →+* K)) =
        ((↑(Matrix.GeneralLinearGroup.map (e : F →+* K) N⁻¹) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K)) := by
      ext i j
      rw [Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply]
    rw [hmap, hmat]
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_conjSLn,
    coe_conjSLn, Matrix.map_mul, Matrix.map_mul, hA, hB, hC]

private theorem sl_map_conjSL {F K : Type} [Field F] [Field K] (e : F ≃+* K) {m : ℕ}
    (M : GL (Fin (m + 1)) K) (y : SL(m + 1, F)) :
    Matrix.SpecialLinearGroup.map (e : F →+* K)
      (InnerDiagA.conjSL (Matrix.GeneralLinearGroup.map (e.symm : K →+* F) M) y) =
      conjSLn M (Matrix.SpecialLinearGroup.map (e : F →+* K) y) := by
  rw [← conjSLn_eq_conjSL]
  exact sl_map_conjSLn e M y

theorem carrierSL_transport {F K X : Type} [Field F] [Field K] [Group X] (e : F ≃+* K) {m : ℕ}
    (f : SL(m + 1, K) →* X) (hfker : f.ker ≤ Subgroup.center SL(m + 1, K)) :
    (f.comp (Matrix.SpecialLinearGroup.map (e : F →+* K))).range = f.range ∧
      (f.comp (Matrix.SpecialLinearGroup.map (e : F →+* K))).ker ≤
        Subgroup.center SL(m + 1, F) ∧
      ∀ (b : X) (M : GL (Fin (m + 1)) K), (∀ Y, b⁻¹ * f Y * b = f (conjSLn M Y)) →
        ∀ y, b⁻¹ * (f.comp (Matrix.SpecialLinearGroup.map (e : F →+* K))) y * b =
          (f.comp (Matrix.SpecialLinearGroup.map (e : F →+* K)))
            (InnerDiagA.conjSL
              (Matrix.GeneralLinearGroup.map (e.symm : K →+* F) M) y) := by
  classical
  let me : SL(m + 1, F) →* SL(m + 1, K) := Matrix.SpecialLinearGroup.map (e : F →+* K)
  have hleft : ∀ x : SL(m + 1, F),
      Matrix.SpecialLinearGroup.map (e.symm : K →+* F)
        (Matrix.SpecialLinearGroup.map (e : F →+* K) x) = x := by
    intro x
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hinj : Function.Injective me := by
    intro x y h
    have h' := congrArg (Matrix.SpecialLinearGroup.map (e.symm : K →+* F)) h
    dsimp only [me] at h'
    rw [hleft x, hleft y] at h'
    exact h'
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact ⟨me y, rfl⟩
    · rintro _ ⟨A, rfl⟩
      exact ⟨Matrix.SpecialLinearGroup.map (e.symm : K →+* F) A,
        by simp only [MonoidHom.comp_apply, slMap_comp_symm e A]⟩
  · intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    apply hinj
    rw [map_mul, map_mul]
    have hmem : me y ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have hy' : (f.comp me) y = 1 := MonoidHom.mem_ker.mp hy
      simpa only [MonoidHom.comp_apply] using hy'
    exact (Subgroup.mem_center_iff.mp (hfker hmem)) (me z)
  · intro b M hb y
    change b⁻¹ * f (me y) * b =
      f (me (InnerDiagA.conjSL
        (Matrix.GeneralLinearGroup.map (e.symm : K →+* F) M) y))
    rw [hb (me y)]
    congr 1
    exact (sl_map_conjSL e M y).symm

section Model


theorem carrierSL_nu_eq {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ν = compRank (componentRoots (rootCharHom a) i) + 1 := by
  have h := CFSG.StandardType.TablePThreeKG.compRank_frameRoots_eq
    (Ψ := componentRoots (rootCharHom a) i) hψ hκ hnorm hΨ hn hν
  omega

theorem carrierSL_exp_pos {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {h : ℕ} (hq : S.D.q = 2 ^ h) : 0 < h := by
  by_contra hh
  have h0 : h = 0 := Nat.eq_zero_of_not_pos hh
  have hlt : 1 < S.D.q := S.hqpow.1.one_lt
  rw [h0, pow_zero] at hq
  omega

theorem carrierSL_ggU_facts {m g : ℕ} (hm : 2 ≤ m) (hg : 0 < g) :
    StandardReturnAt (ggU .PSL (m + 1) g) g ∧ Finite (ggU .PSL (m + 1) g).K ∧
      Group.IsPerfect (ggU .PSL (m + 1) g).K ∧
      CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .PSL (m + 1) g).K ∧
      ∃ β ∈ (ggU .PSL (m + 1) g).D.roots, GGLongRoot (ggU .PSL (m + 1) g).D β := by
  have hne1 : (m + 1, 2 ^ g) ≠ (2, 2) := by
    intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  have hne2 : (m + 1, 2 ^ g) ≠ (2, 3) := by
    intro h
    have h3 : 2 ^ g = 3 := congrArg Prod.snd h
    have hdvd : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
    rw [h3] at hdvd
    omega
  have hm0 : 0 < m := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Or.inl ⟨.PSL, m + 1, Or.inl rfl, ?_, rfl⟩
    change Nat.Prime 2 ∧ 1 ≤ g ∧ 2 ≤ m + 1 ∧ (m + 1, 2 ^ g) ≠ (2, 2) ∧
      (m + 1, 2 ^ g) ≠ (2, 3)
    exact ⟨Nat.prime_two, by omega, by omega, hne1, hne2⟩
  · change Finite (SL(m + 1, GaloisField 2 g))
    infer_instance
  · change Group.IsPerfect (SL(m + 1, GaloisField 2 g))
    exact (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup
      (n := m + 1) (K := GaloisField 2 g) (by omega)).1
  · change CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (SL(m + 1, GaloisField 2 g))
    exact CFSG.SeitzReduction.LinearPilot.oddCentralSplit_specialLinearGroup
      (m := m) (F := GaloisField 2 g)
  · let k : Fin m := ⟨0, hm0⟩
    let β : Fin m → ℤ := Pi.single k 1
    have hβ : β ∈ (SpecialLinear.rootDatum m (GaloisField 2 g)).roots := by
      change β ∈ roots (SpecialLinear.isFiniteType_A m) ∅
      rw [SpecialLinear.roots_eq]
      refine ⟨k.castSucc, k.succ, ?_, ?_⟩
      · intro h
        have hv := congrArg Fin.val h
        simp at hv
      · exact SpecialLinear.toStd_single m k
    refine ⟨β, ?_, ?_⟩
    · change β ∈ (ggU .PSL (m + 1) g).D.roots
      exact hβ
    · change GGLongRoot (SpecialLinear.rootDatum m (GaloisField 2 g)) β
      exact CFSG.StandardType.LieKnownR2.PSL.ggLongRoot_of_mem_roots
        (m := m) (F := GaloisField 2 g) hm0 hβ

theorem carrierSL_cover {m g : ℕ} {K X : Type} [Field K] [Group X]
    (e : GaloisField 2 g ≃+* K) (f : SL(m + 1, K) →* X)
    (hfker : f.ker ≤ Subgroup.center SL(m + 1, K)) (P : X → Prop)
    (hact : ∀ b, P b → ∃ M : GL (Fin (m + 1)) K, ∀ Y, b⁻¹ * f Y * b = f (conjSLn M Y)) :
    ∃ φ : (ggU .PSL (m + 1) g).K →* X, φ.range = f.range ∧
      φ.ker ≤ Subgroup.center (ggU .PSL (m + 1) g).K ∧
      ∀ b, P b → GGPsiInnerDiag (ggU .PSL (m + 1) g).D φ b := by
  let φ : (ggU .PSL (m + 1) g).K →* X :=
    f.comp (Matrix.SpecialLinearGroup.map (e : GaloisField 2 g →+* K))
  have htr := carrierSL_transport e f hfker
  refine ⟨φ, htr.1, htr.2.1, ?_⟩
  intro b hb
  obtain ⟨M, hM⟩ := hact b hb
  exact CFSG.StandardType.ClassicalPosition.ggPsiInnerDiag_of_conjSL φ (htr.2.2 b M hM)

theorem rckCarrierSL_holds :
    RCKCarrierSL := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hkind h2 hn hQS
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp
      (carrierSL_natCast_ne_zero hp hp2) hTp i h2 hn
  have hνr := carrierSL_nu_eq i hν hψ hκ hnorm hΨ hn
  obtain ⟨π, hπ⟩ := splitShape_of_twistKind_inner S hT i hkind hν hψ hκ hnorm hΨ
  have hh : 0 < h := carrierSL_exp_pos S hq
  obtain ⟨σQ, hσQ, z, hz, f, hfrange, hfker, hfact⟩ :=
    split_exists_hom_act S hT i hν hψ hΨ π hπ Nat.prime_two inferInstance hh hq
  have hs0 : 0 < componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    (outer_componentOrbitLength_spec S hT i).1
  have hhs : 0 < h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    Nat.mul_pos hh hs0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKfin, hKcard⟩ := finite_card_fixSubfield (L := GGL) (r := 2)
    (n := h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) hhs σQ hσQ
  obtain ⟨e⟩ := carrierSL_fieldEquiv hhs hKcard
  have hQ2 : 2 ≤ 2 ^ (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hhs
  subst hνr
  obtain ⟨hstd, hfin, hperf, hodd, hlong⟩ := carrierSL_ggU_facts (m :=
    compRank (componentRoots (rootCharHom a) i))
    (g := h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) h2 hhs
  obtain ⟨φ, hφrange, hφker, hφact⟩ := carrierSL_cover e f hfker (· ∈ S.D.torus)
    fun b hb => exists_conjSLn_of_mem_torus_split S hT i hν hψ hΨ hQ2 σQ hσQ hz f hfrange
      hfact hb
  exact ⟨_, φ, rfl, hstd, hφrange.trans hfrange, hφker, hfin, hperf, hodd, hlong, hφact⟩

end Model

end CFSG.StandardType.RCKRP

end
