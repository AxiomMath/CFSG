module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcEndPow
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcLang
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcL44
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcPSatData
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcG2Three
public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.Blueprint.SourceExceptionalRootData
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FourHI
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KF.F128Cyclic
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section LatticeLang

open Matrix

@[expose] def zact {n : Type*} [Fintype n] {D : Type*} [AddCommGroup D] (B : Matrix n n ℤ) (x : n → D) :
    n → D :=
  fun i => ∑ j, B i j • x j

theorem zact_mul {n : Type*} [Fintype n] {D : Type*} [AddCommGroup D] (B C : Matrix n n ℤ)
    (x : n → D) : zact (B * C) x = zact B (zact C x) := by
  funext i
  simp only [zact, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem zact_smul_one {n : Type*} [Fintype n] [DecidableEq n] {D : Type*} [AddCommGroup D]
    (c : ℤ) (x : n → D) : zact (c • (1 : Matrix n n ℤ)) x = c • x := by
  funext i
  simp [zact, Matrix.smul_apply, Matrix.one_apply, ite_smul]

theorem zact_surjective_of_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {D : Type*}
    [AddCommGroup D] (hD : ∀ c : ℤ, c ≠ 0 → ∀ y : D, ∃ x : D, c • x = y) (B : Matrix n n ℤ)
    (hB : B.det ≠ 0) (y : n → D) : ∃ x : n → D, zact B x = y := by
  choose y' hy' using fun i => hD B.det hB (y i)
  refine ⟨zact B.adjugate y', ?_⟩
  rw [← zact_mul, Matrix.mul_adjugate, zact_smul_one]
  funext i
  exact hy' i

theorem det_smul_sub_one_ne_zero {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℤ)
    {N : ℕ} (hN : C ^ N = 1) (c : ℤ) (hc : c ^ N ≠ 1) : (c • C - 1).det ≠ 0 := by
  intro h0
  set C' : Matrix n n ℚ := (Int.castRingHom ℚ).mapMatrix C with hC'
  have hmap : (Int.castRingHom ℚ).mapMatrix (c • C - 1) = (c : ℚ) • C' - 1 := by
    ext i j
    rw [hC', RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : ((c : ℚ) • C' - 1).det = 0 := by
    rw [← hmap, ← RingHom.map_det, h0, map_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h1 : (c : ℚ) • (C' *ᵥ v) = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, Matrix.smul_mulVec] at hv
    exact hv
  have hk : ∀ k : ℕ, ((c : ℚ) ^ k) • ((C' ^ k) *ᵥ v) = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, mul_smul, ← Matrix.mulVec_smul, h1, ih]
  have hCN : C' ^ N = 1 := by
    rw [hC', ← map_pow, hN, map_one]
  have h2 := hk N
  rw [hCN, Matrix.one_mulVec] at h2
  have h3 : ((c : ℚ) ^ N - 1) • v = 0 := by rw [sub_smul, one_smul, h2, sub_self]
  have hcq : (c : ℚ) ^ N - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hc
  exact hv0 ((smul_eq_zero.1 h3).resolve_left hcq)

end LatticeLang

@[expose] def diagKer (τ : Tag) (L : Type) [Field L] (Ψ : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ L) where
  carrier := {g | ∃ t : Fin τ.rank → Lˣ, g = rootDiagUnit τ t ∧
    ∀ α ∈ Ψ, FourGroupChevalley.rootChar t α = 1}
  one_mem' := ⟨1, rootDiagUnit_one.symm, fun α _ => by
    simp [FourGroupChevalley.rootChar]⟩
  mul_mem' := by
    rintro _ _ ⟨t, rfl, ht⟩ ⟨t', rfl, ht'⟩
    refine ⟨t * t', (rootDiagUnit_mul t t').symm, fun α hα => ?_⟩
    have h1 := ht α hα
    have h2 := ht' α hα
    simp only [FourGroupChevalley.rootChar, Pi.mul_apply, mul_zpow,
      Finset.prod_mul_distrib] at h1 h2 ⊢
    rw [h1, h2, one_mul]
  inv_mem' := by
    rintro _ ⟨t, rfl, ht⟩
    refine ⟨t⁻¹, rootDiagUnit_inv t, fun α hα => ?_⟩
    have h1 := ht α hα
    simp only [FourGroupChevalley.rootChar, Pi.inv_apply, inv_zpow,
      Finset.prod_inv_distrib] at h1 ⊢
    rw [h1, inv_one]

theorem lemma44_frame_of_le
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3D : τ = .D4 → p ≠ 3) (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1)
    (hst : familyStabilizerSubgroup a ≤ CFSG.HardMathSupport.C14Lattice.familyReflectionGroup a)
    (e : ℕ) (Q : ModGL τ L)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hQτ : Q ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q = (h ▸ diagramMap t L ^ j) * n)
    (hfix : ∀ i, frobTwistGL τ L 2 e Q (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i)) :
    ∃ (γ : diagKer τ L (familyKernel a) →* diagKer τ L (familyKernel a)) (m : ℕ),
      0 < m ∧ ¬ p ∣ m ∧ (∀ z, γ^[m] z = z) ∧
      ∀ z : diagKer τ L (familyKernel a), (frobTwistGL τ L 2 e Q z : ModGL τ L) = γ (z ^ 2 ^ e) := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨A, hA, hAroot, -, -, -⟩ := CFSG.HardMathSupport.C14W1.exists_lattice_map Q hQT
  obtain ⟨o, ho0, hpo, w₀, hw₀⟩ := C14L44.exists_pow_weyl hp hp2 h3D Q A hA hQτ
  set q : ℕ := 2 ^ e with hq
  have hinj := CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' (τ := τ) (K := L)
  have hFr : ∀ t : Fin τ.rank → Lˣ,
      (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom (t i)) = t ^ q := by
    intro t; funext i; apply Units.ext; simp [iterateFrobenius_def, q]
  have hFz : ∀ t, frobTwistGL τ L 2 e Q (rootDiagUnit τ t) = Q * rootDiagUnit τ t ^ q * Q⁻¹ := by
    intro t
    rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map, hFr,
      CFSG.HardMathSupport.C14W1.rootDiagUnit_pow']
  have hap : ∀ i, a i ^ p = 1 := fun i => funext fun j => ha i j
  have hcopq : Nat.Coprime q p :=
    Nat.Coprime.pow_left e ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, q * c' ≡ 1 [MOD p] := by
    refine ⟨(((q : ZMod p)⁻¹ : ZMod p)).val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one q hcopq
  have hpowmod : ∀ (x : Fin τ.rank → Lˣ), x ^ p = 1 → ∀ m n : ℕ, m ≡ n [MOD p] → x ^ m = x ^ n :=
    fun x hx m n hmn => pow_eq_pow_iff_modEq.2 (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx) hmn)
  have hAa : ∀ i, C14Torus.tmap A (a i) = a i ^ c' := by
    intro i
    have h1 : C14Torus.tmap A (a i) ^ q = a i := by
      apply hinj
      rw [← C14Torus.tmap_pow, ← hA, CFSG.HardMathSupport.C14W1.rootDiagUnit_pow', ← hFz]
      exact hfix i
    have h2 : C14Torus.tmap A (a i) ^ p = 1 := by
      rw [← C14Torus.tmap_pow, hap i, C14Torus.tmap_one]
    calc C14Torus.tmap A (a i) = C14Torus.tmap A (a i) ^ (q * c') := by
          conv_lhs => rw [← pow_one (C14Torus.tmap A (a i))]
          exact hpowmod _ h2 _ _ hc'.symm
      _ = a i ^ c' := by rw [pow_mul, h1]
  have hAja : ∀ j i, C14Torus.tmap (A ^ j) (a i) = a i ^ (c' ^ j) := by
    intro j i
    induction j with
    | zero => rw [pow_zero, pow_zero, pow_one, C14Torus.tmap_one_left]
    | succ j ih =>
      rw [pow_succ, ← C14Torus.tmap_tmap, ih, C14Torus.tmap_pow, hAa, ← pow_mul,
        pow_succ']
  have hAΨ : ∀ α ∈ familyKernel a, A *ᵥ α ∈ familyKernel a := by
    rintro α ⟨hα, hαa⟩
    refine ⟨hAroot α hα, fun i => ?_⟩
    rw [← C14Torus.rootChar_tmap, hAa, C14Torus.rootChar_pow_left, hαa i, one_pow]
  have hn' : 0 < orderOf w₀ := orderOf_pos w₀
  obtain ⟨s, m', hpm', hsm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn'.ne' p hp.ne_one
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hsm; omega
  have hpowW : ∀ k v, (A ^ (o * k)) *ᵥ v = (w₀ ^ k) • v := by
    intro k
    induction k with
    | zero => intro v; rw [mul_zero, pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ k ih =>
      intro v
      rw [Nat.mul_succ, pow_add, ← Matrix.mulVec_mulVec, hw₀, ih, pow_succ, mul_smul]
  set u := w₀ ^ m' with hu
  have hup : u ^ p ^ s = 1 := by
    rw [hu, ← pow_mul, mul_comm, ← hsm, pow_orderOf_eq_one]
  have hA1 : A ^ (o * m' * p ^ s) = 1 := by
    ext j i
    have h1 := congrFun (hpowW (m' * p ^ s) (Pi.single i 1)) j
    rw [← mul_assoc, pow_mul w₀, ← hu, hup, one_smul] at h1
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using h1
  have hustab : u ∈ familyStabilizerSubgroup a := by
    rw [mem_familyStabilizerSubgroup]
    intro i v
    have hx : a i ^ (c' ^ (o * m')) = a i := by
      have h1 := hAja (o * m' * p ^ s) i
      rw [hA1, C14Torus.tmap_one_left] at h1
      rw [pow_mul c' (o * m') (p ^ s)] at h1
      conv_rhs => rw [h1]
      refine hpowmod _ (hap i) _ _ ?_
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      exact (ZMod.pow_card_pow _).symm
    rw [← hpowW m' v, ← C14Torus.rootChar_tmap, hAja, hx]
  have hurefl := hst hustab
  have hZfix : ∀ t : Fin τ.rank → Lˣ, (∀ α ∈ familyKernel a, rootChar t α = 1) →
      C14Torus.tmap (A ^ (o * m')) t = t := by
    intro t ht
    refine C14Torus.ext_rootChar fun i => ?_
    rw [C14Torus.rootChar_tmap, hpowW,
      C14L44.rootChar_smul_of_mem_familyReflectionGroup a hurefl ht]
  have hmem : ∀ z ∈ diagKer τ L (familyKernel a), Q * z * Q⁻¹ ∈ diagKer τ L (familyKernel a) := by
    rintro _ ⟨t, rfl, ht⟩
    refine ⟨C14Torus.tmap A t, hA t, fun α hα => ?_⟩
    rw [C14Torus.rootChar_tmap]
    exact ht _ (hAΨ α hα)
  let γ : diagKer τ L (familyKernel a) →* diagKer τ L (familyKernel a) :=
    { toFun := fun z => ⟨Q * z * Q⁻¹, hmem z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hγit : ∀ j (z : diagKer τ L (familyKernel a)) (t : Fin τ.rank → Lˣ),
      (z : ModGL τ L) = rootDiagUnit τ t →
      ((γ^[j] z : diagKer τ L (familyKernel a)) : ModGL τ L) =
        rootDiagUnit τ (C14Torus.tmap (A ^ j) t) := by
    intro j z t hz
    induction j with
    | zero => rw [Function.iterate_zero_apply, pow_zero, C14Torus.tmap_one_left, hz]
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      change Q * ((γ^[j] z : diagKer τ L (familyKernel a)) : ModGL τ L) * Q⁻¹ = _
      rw [ih, hA, C14Torus.tmap_tmap, pow_succ]
  refine ⟨γ, o * m', Nat.mul_pos ho0 hm'0, fun h => ?_, fun z => ?_, fun z => ?_⟩
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpo h
    · exact hpm' h
  · obtain ⟨_, t, rfl, ht⟩ := z
    apply Subtype.ext
    rw [hγit _ _ t rfl, hZfix t ht]
  · obtain ⟨_, t, rfl, ht⟩ := z
    change frobTwistGL τ L 2 e Q (rootDiagUnit τ t) = Q * (rootDiagUnit τ t ^ 2 ^ e) * Q⁻¹
    rw [hFz]

theorem lemma44_frame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} [Finite ι]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h3D : τ = .D4 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1) (e : ℕ)
    (Q : ModGL τ L)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hQτ : Q ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q = (h ▸ diagramMap t L ^ j) * n)
    (hfix : ∀ i, frobTwistGL τ L 2 e Q (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i)) :
    ∃ (γ : diagKer τ L (familyKernel a) →* diagKer τ L (familyKernel a)) (m : ℕ),
      0 < m ∧ ¬ p ∣ m ∧ (∀ z, γ^[m] z = z) ∧
      ∀ z : diagKer τ L (familyKernel a), (frobTwistGL τ L 2 e Q z : ModGL τ L) = γ (z ^ 2 ^ e) :=
  lemma44_frame_of_le hp hp2 h3D a ha
    (CFSG.HardMathSupport.C14Lattice.familyStabilizer_le_reflection hp
      (CFSG.HardMathSupport.C14Lattice.not_dvd_or_sylowCert τ hp hp2 h3 h5) ha) e Q hQT hQτ hfix

theorem lemma45_frame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} [Finite ι]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h3D : τ = .D4 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1) (e : ℕ)
    (Q : ModGL τ L)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hQτ : Q ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q = (h ▸ diagramMap t L ^ j) * n)
    (hfix : ∀ i, frobTwistGL τ L 2 e Q (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i)) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ z ∈ diagKer τ L (familyKernel a), (∃ n : ℕ, z ^ p ^ n = 1) →
      (endPow (frobTwistGL τ L 2 e Q) p) z = z →
      (frobTwistGL τ L 2 e Q z) ^ 2 ^ (e * (p * k)) = z ^ 2 ^ e := by
  obtain ⟨γ, m, hm0, hpm, hγ, hF⟩ :=
    lemma44_frame hp hp2 h3 h3D h5 a ha e Q hQT hQτ hfix
  have hcomm : ∀ x y : diagKer τ L (familyKernel a), x * y = y * x := by
    rintro ⟨_, t, rfl, -⟩ ⟨_, t', rfl, -⟩
    apply Subtype.ext
    change rootDiagUnit τ t * rootDiagUnit τ t' = rootDiagUnit τ t' * rootDiagUnit τ t
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm t]
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p * k ≡ 1 [MOD m] := by
    refine ⟨(((p : ZMod m)⁻¹ : ZMod m)).val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    haveI : NeZero m := ⟨hm0.ne'⟩
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one p hcop
  refine ⟨k + m, by omega, fun z hz hzp hzF => ?_⟩
  have hk' : p * (k + m) ≡ 1 [MOD m] := by
    have : p * (k + m) = p * k + m * p := by ring
    rw [this]
    exact (Nat.ModEq.add_right_cancel' 0 (by simpa using hk : p * k + 0 ≡ 1 + 0 [MOD m])).add
      (Nat.modEq_zero_iff_dvd.2 (dvd_mul_right m p)) |>.trans (by simp [Nat.ModEq])
  set w : diagKer τ L (familyKernel a) := ⟨z, hz⟩
  have hit : ∀ n (y : diagKer τ L (familyKernel a)), ((fun y => γ (y ^ 2 ^ e))^[n] y : ModGL τ L) =
      (frobTwistGL τ L 2 e Q)^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hF]
  have hzF' : (fun y => γ (y ^ 2 ^ e))^[p] w = w := by
    apply Subtype.ext
    rw [hit, ← endPow_apply]
    exact hzF
  have key := power_map_of_shape γ hγ hk' w hzF'
  have h1 := congrArg Subtype.val key
  have h2 : (frobTwistGL τ L 2 e Q) z = ((γ (w ^ 2 ^ e) : diagKer τ L (familyKernel a)) :
      ModGL τ L) := hF w
  rw [h2, pow_mul]
  simpa using h1

theorem lemma46_frame_gen





    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1) (e : ℕ) (he : 1 ≤ e) (Q : ModGL τ L)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hfix : ∀ i, frobTwistGL τ L 2 e Q (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    (hsat : ∀ v : Fin τ.rank → ℤ, p • v ∈ AddSubgroup.closure (familyKernel a) →
      v ∈ AddSubgroup.closure (familyKernel a))
    (y : ModGL τ L) (hy : y ∈ diagKer τ L (familyKernel a)) (hyp : ∃ n : ℕ, y ^ p ^ n = 1)
    (hyF : frobTwistGL τ L 2 e Q y = y) :
    ∃ z ∈ diagKer τ L (familyKernel a), (∃ n : ℕ, z ^ p ^ n = 1) ∧
      (endPow (frobTwistGL τ L 2 e Q) p) z = z ∧
      ((List.range p).map fun i => (endPow (frobTwistGL τ L 2 e Q) i) z).prod = y := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨A, hA, hAroot, N, hN0, hAN⟩ := CFSG.HardMathSupport.C14W1.exists_lattice_map Q hQT
  set q : ℕ := 2 ^ e with hq
  set B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := (q : ℤ) • A with hB
  have hFr : ∀ t : Fin τ.rank → Lˣ,
      (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom (t i)) = t ^ q := by
    intro t; funext i; apply Units.ext; simp [iterateFrobenius_def, q]
  have hFd : ∀ t, frobTwistGL τ L 2 e Q (rootDiagUnit τ t) =
      rootDiagUnit τ (C14Torus.tmap B t) := by
    intro t
    rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map, hFr, hA]
    congr 1
    rw [← zpow_natCast, ← C14Torus.tmap_smul_one, C14Torus.tmap_tmap, smul_mul_assoc,
      one_mul]
  have hinj := CFSG.HardMathSupport.C14W1.rootDiagUnit_injective' (τ := τ) (K := L)
  have hBfix : ∀ i, C14Torus.tmap B (a i) = a i := fun i => hinj (by rw [← hFd]; exact hfix i)
  have hap : ∀ i, a i ^ p = 1 := fun i => funext fun j => ha i j
  have hcopq : Nat.Coprime q p :=
    Nat.Coprime.pow_left e ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hAΨ : ∀ α ∈ familyKernel a, A *ᵥ α ∈ familyKernel a := by
    rintro α ⟨hα, hαa⟩
    refine ⟨hAroot α hα, fun i => ?_⟩
    have h1 : rootChar (a i) (A *ᵥ α) ^ q = 1 := by
      have := congrArg (fun t => rootChar t α) (hBfix i)
      rw [C14Torus.rootChar_tmap, hαa i, hB, Matrix.smul_mulVec,
        C14Torus.rootChar_zsmul, zpow_natCast] at this
      exact this
    have h2 : rootChar (a i) (A *ᵥ α) ^ p = 1 := by
      rw [← C14Torus.rootChar_pow_left, hap i, C14Torus.rootChar_one_left]
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hcopq, pow_one] at this
  set Ncl := AddSubgroup.closure (familyKernel a) with hNcl
  have hBN : ∀ α ∈ Ncl, B *ᵥ α ∈ Ncl := by
    intro α hα
    induction hα using AddSubgroup.closure_induction with
    | mem x hx =>
      rw [hB, Matrix.smul_mulVec]
      exact Ncl.zsmul_mem (AddSubgroup.subset_closure (hAΨ x hx)) _
    | zero => rw [Matrix.mulVec_zero]; exact Ncl.zero_mem
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Ncl.add_mem hx hy
    | neg x _ hx => rw [Matrix.mulVec_neg]; exact Ncl.neg_mem hx
  have hchar : ∀ s : Fin τ.rank → Lˣ, (∀ α ∈ familyKernel a, rootChar s α = 1) →
      ∀ α ∈ Ncl, rootChar s α = 1 := by
    intro s hs α hα
    induction hα using AddSubgroup.closure_induction with
    | mem x hx => exact hs x hx
    | zero => exact rootChar_zero s
    | add x y _ _ hx hy => rw [rootChar_add, hx, hy, one_mul]
    | neg x _ hx => rw [C14Torus.rootChar_neg, hx, inv_one]
  obtain ⟨s, rfl, hs⟩ := hy
  have hsp : ∃ n : ℕ, s ^ p ^ n = 1 := by
    obtain ⟨n, hn⟩ := hyp
    exact ⟨n, hinj (by rw [CFSG.HardMathSupport.C14W1.rootDiagUnit_pow', hn,
      CFSG.HardMathSupport.C14W1.rootDiagUnit_one'])⟩
  have hsZ : s ∈ C14Torus.zp p Ncl := C14Torus.mem_zp.2 ⟨hchar s hs, hsp⟩
  have hsB : C14Torus.tmap B s = s := hinj (by rw [← hFd]; exact hyF)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Lˣ, IsPrimitiveRoot ζ p := by
    haveI : NeZero (p : L) := ⟨fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff L 2 p).1 h)).symm⟩
    obtain ⟨m, hm⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := p)
    exact ⟨(hm.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.1 (by rw [IsUnit.unit_spec]; exact hm)⟩
  have hdet : (B ^ p - 1).det ≠ 0 := by
    have hBp : B ^ p = ((q : ℤ) ^ p) • A ^ p := by rw [hB, smul_pow]
    rw [hBp]
    refine det_smul_sub_one_ne_zero (A ^ p) (N := N)
      (by rw [← pow_mul, mul_comm, pow_mul, hAN, one_pow]) _ ?_
    rw [← pow_mul]
    have h1 : (1 : ℤ) < (q : ℤ) := by
      rw [hq]; push_cast; exact one_lt_pow₀ (by norm_num) (by omega)
    exact (one_lt_pow₀ h1 (Nat.mul_pos hp.pos hN0).ne').ne'
  obtain ⟨z₀, hz₀, hz₀F, hz₀prod⟩ := C14Torus.zp_norm_surjective hζ hsat B hBN hdet hsZ hsB
  have hit : ∀ i t, (endPow (frobTwistGL τ L 2 e Q) i) (rootDiagUnit τ t) =
      rootDiagUnit τ (C14Torus.tmap (B ^ i) t) := by
    intro i t
    rw [endPow_apply, ← C14Torus.tmap_pow_left]
    induction i generalizing t with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hFd, ih]
  obtain ⟨hz₀c, n₀, hn₀⟩ := C14Torus.mem_zp.1 hz₀
  refine ⟨rootDiagUnit τ z₀, ⟨z₀, rfl, fun α hα => hz₀c α (AddSubgroup.subset_closure hα)⟩,
    ⟨n₀, by rw [← CFSG.HardMathSupport.C14W1.rootDiagUnit_pow', hn₀,
      CFSG.HardMathSupport.C14W1.rootDiagUnit_one']⟩, by rw [hit, hz₀F], ?_⟩
  have hprod : ∀ n, ((List.range n).map fun i =>
      (endPow (frobTwistGL τ L 2 e Q) i) (rootDiagUnit τ z₀)).prod =
      rootDiagUnit τ (∏ i ∈ Finset.range n, C14Torus.tmap (B ^ i) z₀) := by
    intro n
    induction n with
    | zero => simp [CFSG.HardMathSupport.C14W1.rootDiagUnit_one']
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ,
        CFSG.HardMathSupport.C14W1.rootDiagUnit_mul']
      simp [hit]
  rw [hprod, hz₀prod]

theorem familyKernel_pSaturated





    {τ : Tag} {ι : Type} {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5)
    (hG2 : τ = .G2 → p ≠ 3) (a : ι → Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ)
    (hv : p • v ∈ AddSubgroup.closure (familyKernel a)) :
    v ∈ AddSubgroup.closure (familyKernel a) :=
  CFSG.HardMathSupport.C14PSat.familyKernel_pSaturated hp hp2 h3 h5 hG2 a v hv

theorem familyKernel_empty_G2_three






    {K : Type} [Field K] {ι : Type}
    (a : ι → Fin Tag.G2.rank → Kˣ) (ha : ∀ i j, a i j ^ 3 = 1)
    (hcard : 9 ≤ Nat.card (Subgroup.closure (Set.range fun i => rootDiagUnit Tag.G2 (a i)))) :
    familyKernel a = ∅ :=
  CFSG.HardMathSupport.C14G2Three.familyKernel_empty_G2_three a ha hcard

end CFSG.HardMathSupport.C14Exc
