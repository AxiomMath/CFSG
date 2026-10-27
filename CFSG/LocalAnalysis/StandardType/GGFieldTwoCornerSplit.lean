module

public import CFSG.LocalAnalysis.StandardType.GGFieldTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldTwoCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKLocal
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACoreUni
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.LocalAnalysis.GLTheoremA.T263.SK
open TableBU TablePThreeKG CFSG.RankThree.PartOne.KCUnitaryModel
open Polynomial Module Matrix

private theorem ltrca_ca1
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hset : GGFieldTwoCornerSetting p B Bs x L D J y K) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNLocalCore 3 (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) ∧
      GGTPNMarked 3 (fun _ lab => lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel))
        (ggAutsOf K Bs hN) := by
  obtain ⟨hc, hL, hK, hn, hJK, hp3, hl, _hlabJ⟩ := hset
  subst hp3
  have hS : LargeEvenSStar 3 B x L := hc.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hBBs : B ≤ Bs := hc.2.1.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := ggInnerDiagOn_le_normalizer hK
  have hx : x ∈ Subgroup.normalizer (K : Set G) := hN (hBBs hxB)
  have hloc : GGTPNLocalCore 3 (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩)
      (J.subgroupOf K) :=
    ggTPNTrLocalCore_holds G 3 B Bs x L D J y K hc hL hK hn hJK hN hx
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hΛ51 : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    norm_num [LargeEvenInLambda2]
  have hmark₁ := ggInnerDiagOn_relabel hrig hK hΛ51 hl
  have hhalf : LargeEvenHalfSplit 3 (⟨.twA, 5, 1⟩ : LargeEvenLabel)
      (Subgroup.center ↥K = ⊥) :=
    Or.inl (Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by decide, by norm_num⟩))
  have hmark : GGTPNMarked 3 (fun _ lab => lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel))
      (ggAutsOf K Bs hN) := by
    unfold GGTPNMarked
    refine largeEvenMarking_mono ?_ hmark₁
    rintro lab R _ I F θ ⟨hlab_eq, _hBs, h3⟩
    subst hlab_eq
    exact ⟨rfl, hhalf, ggInducedInn_of_clause3 hN θ h3⟩
  exact ⟨hN, hx, hloc, hmark⟩

private theorem ltrca_marking {p : ℕ} {X : Type} [Group X] {A : Subgroup (MulAut X)}
    {labX : LargeEvenLabel} (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    commutator X = ⊤ ∧ LargeEvenInLambda2 labX := by
  rw [GGTPNMarked, LargeEvenMarking] at hm
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hm
  obtain ⟨R, _, I, F, -, -, θ₀, hlabX, -, -⟩ := largeEvenRawDatum_exists hraw
  subst hlabX
  exact ⟨hcomm, hlab⟩

private theorem ltrca_exists_unitary_model {p : ℕ} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {labX : LargeEvenLabel} (hA : labX.tag = .twA)
    (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ labX.n) ^ 2 ∧
      ∃ θ : X ⧸ Subgroup.center X ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (labX.rank + 1)) K (2 ^ labX.n)),
        GGInducedInn A θ (LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (labX.rank + 1)) K (2 ^ labX.n)))
          (LargeEvenGUSet (Fin (labX.rank + 1)) K (2 ^ labX.n))) := by
  classical
  rw [GGTPNMarked, LargeEvenMarking] at hm
  obtain ⟨-, lab, hlab, hraw⟩ := hm
  obtain ⟨t, l, n⟩ := labX
  subst hA
  obtain ⟨R, _, I, F, -, -, θ₀, hlab, -, -⟩ := largeEvenRawDatum_exists hraw
  subst hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfin, hcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hhalf, hind⟩ := hQ
  exact ⟨K, hKfield, hKfin, hcard, θ, hind⟩

private theorem ltrca_exists_unitary_lift {p N n : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] {A : Subgroup (MulAut X)} {σ : MulAut X}
    (hUF : UnitaryFieldData 2 n K)
    {θ : X ⧸ Subgroup.center X ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    (hind : GGInducedInn A θ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      (LargeEvenGUSet (Fin N) K (2 ^ n))))
    (hσA : σ ∈ A) :
    ∃ d ∈ primeFormUnitary hUF (idGram K N), IsConjBy d (ggInducedAut θ σ) := by
  classical
  have hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer (d := N) hUF
  obtain ⟨M, hM, hMeq⟩ := TableB.exists_eq_projConj hS (hind σ hσA)
  obtain ⟨u, hu⟩ := TableBU63.exists_unitary_of_gu (n := n) (d := N) hUF hM
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin N) u * M, hu, ?_⟩
  intro g g' hgg'
  rw [hMeq]
  show (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      ((LargeEvenSUGroup (Fin N) K (2 ^ n)).normalizerMonoidHom ⟨M, hS hM⟩ g) =
    (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n))) g'
  congr 1
  apply Subtype.ext
  show M * (g : GL (Fin N) K) * M⁻¹ = (g' : GL (Fin N) K)
  rw [hgg', InndiagSU.scalar_mul_conj]

private theorem ltrca_projConj_eq_of_isConjBy {N n : ℕ} {K : Type} [Field K] {d : GL (Fin N) K}
    (hN : d ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)))
    {δ' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))}
    (hδ : IsConjBy d δ') :
    δ' = TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨d, hN⟩ := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ n))) x
  show δ' ((g : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))) =
    TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨d, hN⟩
      (g : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))
  rw [TableB.projConj_mk]
  exact hδ g _ rfl

private theorem ltrca_pow_scalar_of_isConjBy {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hN3 : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    {δ' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))}
    (hδ : IsConjBy d δ') (hδp : δ' ^ p = 1) :
    ∃ c : Kˣ, d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
  classical
  have hdGU : d ∈ LargeEvenGUSet (Fin N) K (2 ^ n) :=
    TableBUD.mem_guSet_of_mem_primeFormUnitary hUF hd
  have hN : d ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer (d := N) hUF hdGU
  have hδeq := ltrca_projConj_eq_of_isConjBy hN hδ
  have hpow : TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n))
      (⟨d, hN⟩ ^ p) = 1 := by
    rw [map_pow, ← hδeq, hδp]
  have hscal := TableBUE.mem_scalars_of_projConj_eq_one (h := hUF) hK hN3 hNq hp hpq hpow
  rw [largeEvenScalars_def] at hscal
  obtain ⟨c, hc⟩ := hscal
  refine ⟨c, ?_⟩
  change Matrix.GeneralLinearGroup.scalar (Fin N) c = d ^ p at hc
  exact hc.symm

private theorem ltrca_two_pow_le_of_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) : 2 ≤ 2 ^ n := by
  have h1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hpq
      norm_num at hpq
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpq)
    · exact h
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1

private theorem ltrca_two_pow_sq_sub_one (n : ℕ) :
    (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  rw [mul_comm, ← Nat.sq_sub_sq (2 ^ n) 1]

private theorem ltrca_primaryFactor_linear {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1)
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) :
    ∃ μ : K, a = X - C μ := by
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hcard, ltrca_two_pow_sq_sub_one n]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartOne.S15K.exists_isPrimitiveRoot_of_dvd hp hpK
  exact exists_eq_X_sub_C_of_mem_primaryFactors hp.ne_zero hω hdp ha

private theorem ltrca_primaryFactor_selfDual {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1)
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) :
    dualPoly hUF.bar a = a := by
  obtain ⟨μ, rfl⟩ := ltrca_primaryFactor_linear hUF hcard hp hp2 hpq hdp ha
  have hxp : ((Matrix.GeneralLinearGroup.toLin d : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)) ^ p = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.toLin d) ^ p = 1 := by
      rw [← map_pow, hdp, map_one]
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hdvd : (X - C μ : K[X]) ∣ X ^ p - C (1 : K) := by
    refine (mem_primaryFactors.mp ha).2.2.trans (minpoly.dvd K _ ?_)
    rw [map_sub, map_pow, aeval_X, aeval_C, hxp, map_one, sub_self]
  have hμp : μ ^ p = 1 := by
    have hroot : (X ^ p - C (1 : K)).IsRoot μ := dvd_iff_isRoot.mp hdvd
    exact sub_eq_zero.mp (by simpa using hroot)
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hμp
    exact zero_ne_one hμp
  obtain ⟨k, hk⟩ := hpq
  have hμq1 : μ ^ (2 ^ n + 1) = 1 := by rw [hk, pow_mul, hμp, one_pow]
  have hbar : hUF.bar μ = μ ^ (2 ^ n) := hUF.bar_apply μ
  have hbar0 : hUF.bar μ ≠ 0 := by rw [hbar]; exact pow_ne_zero _ hμ0
  rw [RankThree.PartOne.KCUnitaryBlock.dualPoly_X_sub_C hbar0, hbar]
  congr 2
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hμq1])

private theorem ltrca_primaryFactor_natDegree {p N n : ℕ} {K : Type} [Field K]
    [Finite K] (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1)
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) :
    a.natDegree = 1 := by
  obtain ⟨μ, rfl⟩ := ltrca_primaryFactor_linear hUF hcard hp hp2 hpq hdp ha
  simp

private theorem ltrca_selfDual_block_field {ℓ f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData ℓ f K} {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    {x : LinearMap.GeneralLinearGroup K V}
    (hq : 2 ≤ ℓ ^ f) (H : UnitaryPrimaryData h.bar B x)
    {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly h.bar (a : K[X]) = a) (hdeg : (a : K[X]).natDegree = 1)
    (ha : IsGoodBlock h x a) :
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = ℓ ^ f ∧
          4 ≤ Fintype.card F ∧
          Nonempty (↥(specialBlock B x (a : K[X])) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (ℓ ^ f) ^ 2 ∧
        3 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) ∧
        (primaryMultiplicity (x : Module.End K V) (a : K[X]), ℓ ^ f) ≠ (3, 2) ∧
        Nonempty (↥(specialBlock B x (a : K[X])) ≃*
          ↥(StatedSU (primaryMultiplicity (x : Module.End K V) (a : K[X])) (ℓ ^ f) E))) := by
  classical
  haveI : Finite K := h.finite
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  obtain ⟨hE, Hf, hHf, hHfl, Φ, -, -⟩ :=
    exists_selfDual_specialBlock_mulEquiv_sesqSpecialUnitary H hself
      (CFSG.RankThree.PartOne.selfDualPrimaryBlock H a hself)
  have hnum := isGoodBlock_numeric hq hself ha
  have hcardE : Fintype.card (AdjoinRoot (a : K[X])) = (ℓ ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hE.card_eq_sq, hdeg, mul_one]
  rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
  · have hm2 : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by
      have hb := ha.1
      omega
    have hV : Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := hm2
    obtain ⟨e2⟩ :=
      CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
    haveI : Finite hE.fixedField := inferInstance
    letI : Fintype hE.fixedField := Fintype.ofFinite _
    have hcardF : Fintype.card hE.fixedField = ℓ ^ f := by
      rw [← Nat.card_eq_fintype_card, hE.card_fixedField, hdeg, mul_one]
    have h4 : 4 ≤ Fintype.card hE.fixedField := by
      rw [hcardF]
      simpa [hdeg] using hnum.1 hm2
    exact Or.inl ⟨hm2, hE.fixedField, inferInstance, inferInstance, hcardF, h4, ⟨Φ.trans e2⟩⟩
  · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
    obtain ⟨e3⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))))
        (Fin (Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
      (fun i j => by rw [hb i j, Matrix.one_apply])
    refine Or.inr ⟨AdjoinRoot (a : K[X]), inferInstance, inferInstance, hcardE, hm, ?_, ?_⟩
    · intro hc
      have h1 : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 3 := congrArg Prod.fst hc
      have h2 : ℓ ^ f = 2 := congrArg Prod.snd hc
      have h3 : 3 ≤ ℓ ^ f := by simpa [hdeg] using hnum.2 h1
      omega
    · rw [← show ℓ ^ (f * (a : K[X]).natDegree) = ℓ ^ f from by rw [hdeg, mul_one]]
      exact ⟨(Φ.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)⟩

private theorem ltrca_conjHom_scalar_mul {N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) {d : GL (Fin N) K}
    (hd : d ∈ primeFormUnitary hUF (idGram K N)) {u : Kˣ} (hu : hUF.norm (u : K) = 1) :
    primeFormConjHom hUF (idGram K N)
        ⟨Matrix.GeneralLinearGroup.scalar (Fin N) u * d,
          Subgroup.mul_mem _ (scalar_mem_primeFormUnitary_one (h := hUF) (n := N) hu) hd⟩ =
      primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [primeFormConjHom_mk, primeFormConjHom_mk]
    congr 1
    exact Subtype.ext (InndiagSU.scalar_mul_conj u d (g : GL (Fin N) K))

private theorem ltrca_pow_norm {p n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {b : K} (hb0 : b ≠ 0) {c : K}
    (hbc : b ^ p = c) (hcn : hUF.norm c = 1) :
    b ^ (2 ^ n + 1) = 1 := by
  classical
  have hn : 1 ≤ n := hUF.one_le
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  letI : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 2 ^ n * 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, hcard, pow_two]
  have hbcard : b ^ (2 ^ n * 2 ^ n - 1) = 1 := by
    simpa only [hFcard] using FiniteField.pow_card_sub_one_eq_one b hb0
  have hcq : c ^ (2 ^ n + 1) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hcn
    rw [pow_succ, mul_comm]
    exact hcn
  have hzp : (b ^ (2 ^ n + 1)) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hbc, hcq]
  have hmul : (2 ^ n + 1) * (2 ^ n - 1) = 2 ^ n * 2 ^ n - 1 := by
    calc (2 ^ n + 1) * (2 ^ n - 1) = (2 ^ n) ^ 2 - 1 ^ 2 :=
          (Nat.sq_sub_sq (2 ^ n) 1).symm
      _ = 2 ^ n * 2 ^ n - 1 := by rw [one_pow, pow_two]
  have hzq : (b ^ (2 ^ n + 1)) ^ (2 ^ n - 1) = 1 := by
    rw [← pow_mul, hmul]
    exact hbcard
  have hcop : Nat.Coprime p (2 ^ n - 1) := by
    refine (hp.coprime_iff_not_dvd).mpr ?_
    intro hdvd
    have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpq hdvd
    have hsub : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [hsub] at h2
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    exact ne_two_of_dvd_two_pow_add_one hn hpq hp2
  have hord : orderOf (b ^ (2 ^ n + 1)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_iff_pow_eq_one.mpr hzp) (orderOf_dvd_iff_pow_eq_one.mpr hzq)
  exact orderOf_eq_one_iff.mp hord

private theorem ltrca_rescale {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} {c : Kˣ}
    (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hcn : hUF.norm (c : K) = 1)
    (hb : ∃ b : K, b ^ p = (c : K)) :
    ∃ (d' : GL (Fin N) K) (hd' : d' ∈ primeFormUnitary hUF (idGram K N)) (u : Kˣ),
      d' ^ p = 1 ∧ d' = Matrix.GeneralLinearGroup.scalar (Fin N) u * d ∧
        primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩ =
          primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ := by
  obtain ⟨b, hb⟩ := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : (0 : K) ^ p = (c : K) := hb
    rw [zero_pow hp.ne_zero] at h0
    exact c.ne_zero h0.symm
  let u : Kˣ := Units.mk0 b hb0
  have hu : (u : K) = b := rfl
  have hunion : b ^ (2 ^ n + 1) = 1 := ltrca_pow_norm hUF hcard hp hpq hb0 hb hcn
  have hbnorm : hUF.norm (b : K) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
    exact hunion
  have hunorm : hUF.norm ((u⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val,
      CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq hUF, hu, hbnorm, inv_one]
  have hbup : u ^ p = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, hb]
  have hsu : Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹ ∈
      primeFormUnitary hUF (idGram K N) :=
    scalar_mem_primeFormUnitary_one (h := hUF) (n := N) hunorm
  let d' : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹ * d
  have hd' : d' ∈ primeFormUnitary hUF (idGram K N) := Subgroup.mul_mem _ hsu hd
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹) d :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin N) u⁻¹) d).symm
  have hd'p : d' ^ p = 1 := by
    calc d' ^ p = (Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹) ^ p * d ^ p := by
          change (Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹ * d) ^ p = _
          rw [hcomm.mul_pow]
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) ((u⁻¹) ^ p) *
            Matrix.GeneralLinearGroup.scalar (Fin N) c := by rw [← map_pow, hdp]
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) ((u⁻¹) ^ p * c) := by rw [← map_mul]
      _ = 1 := by
            rw [inv_pow, hbup, inv_mul_cancel, map_one]
  have hconj : primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩ =
      primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ :=
    ltrca_conjHom_scalar_mul (hUF := hUF) (hd := hd) (u := u⁻¹) hunorm
  exact ⟨d', hd', u⁻¹, hd'p, rfl, hconj⟩

private theorem ltrca_split_component {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a})
    (haT : T = unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d)
      (a₀.1 : K[X])) :
    ((primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
          (a₀.1 : K[X]) = 2 ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
          4 ≤ Fintype.card F ∧
          ∃ g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (3 ≤ primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
            Module.End K (Fin N → K)) (a₀.1 : K[X]) ∧
        (primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
            (a₀.1 : K[X]), 2 ^ n) ≠ (3, 2) ∧
        ∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (2 ^ n) ^ 2 ∧
          ∃ g : ↥(StatedSU (primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
              Module.End K (Fin N → K)) (a₀.1 : K[X])) (2 ^ n) E) →* ↥T,
            Function.Surjective g ∧
              g.ker ≤ Subgroup.center ↥(StatedSU (primaryMultiplicity
                (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
                  (a₀.1 : K[X])) (2 ^ n) E))) := by
  classical
  have H : UnitaryPrimaryData hUF.bar (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd hp hp2 (by rw [hdp, map_one])
  have hq : 2 ≤ 2 ^ n := ltrca_two_pow_le_of_dvd hp hp2 hpq
  subst haT
  have hdega : (a₀.1 : K[X]).natDegree = 1 :=
    ltrca_primaryFactor_natDegree hUF hcard hp hp2 hpq hdp a₀.1.2
  have hselfa : dualPoly hUF.bar (a₀.1 : K[X]) = a₀.1 :=
    ltrca_primaryFactor_selfDual hUF hcard hp hp2 hpq hdp a₀.1.2
  obtain ⟨hsub, hkernel⟩ :=
    subgroupMap_mk'_surjective_ker_le_center hUF (x := Matrix.GeneralLinearGroup.toLin d) a₀
  let ψ : ↥(specialBlock (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X])) →*
      ↥(unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X])) :=
    (MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars hUF N))
      (unitaryPreimageBlock hUF (x := Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X]))).comp
      (specialBlockEquiv hUF H a₀ hq a₀.2).symm.toMonoidHom
  have hψsurj : Function.Surjective ψ :=
    hsub.comp (specialBlockEquiv hUF H a₀ hq a₀.2).symm.surjective
  have hψker : ψ.ker ≤ Subgroup.center ↥(specialBlock (idForm hUF N)
      (Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X])) := by
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hkernel).trans
      (Subgroup.comap_center_le_center (f := (specialBlockEquiv hUF H a₀ hq a₀.2).symm.toMonoidHom)
        (specialBlockEquiv hUF H a₀ hq a₀.2).symm.injective)
  rcases ltrca_selfDual_block_field (B := idForm hUF N) hq H hselfa hdega a₀.2 with
    ⟨hm2, F, hF, hFt, hcardF, h4, ⟨e⟩⟩ | ⟨E, hE, hEt, hcardE, hm, hne, ⟨e⟩⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    refine Or.inl ⟨hm2, F, hF, hFt, hcardF, h4, ψ.comp e.symm.toMonoidHom,
      hψsurj.comp e.symm.surjective, ?_⟩
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hψker).trans
      (Subgroup.comap_center_le_center (f := e.symm.toMonoidHom) e.symm.injective)
  · letI : Field E := hE
    letI : Fintype E := hEt
    refine Or.inr ⟨hm, hne, E, hE, hEt, hcardE, ψ.comp e.symm.toMonoidHom,
      hψsurj.comp e.symm.surjective, ?_⟩
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hψker).trans
      (Subgroup.comap_center_le_center (f := e.symm.toMonoidHom) e.symm.injective)

private theorem ltrca_nonSplit_label_A {p N n : ℕ} {K F : Type} [Field K] [Finite K]
    [Field F] [Fintype F] (hUF : UnitaryFieldData 2 n K) (hnp3 : 3 ≤ n * p)
    (hcardF : Fintype.card F = 2 ^ (n * p))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    {g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    LargeEvenInLambda2 ⟨.A, 1, p * n⟩ ∧
      GGHasLabel ⟨.A, 1, p * n⟩ (↥T ⧸ Subgroup.center ↥T) := by
  have hcardF' : Nat.card F = 2 ^ (n * p) := by
    rw [Nat.card_eq_fintype_card, hcardF]
  have h4F : 4 ≤ Nat.card F := by
    rw [hcardF']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨CFSG.Timmesfeld.Bridge.RootMany.commutator_SL2_eq_top
      (m := n * p) (by omega) hcardF'⟩
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central g hg hperf hgk
  let eZ : (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ≃*
      StatedProj (StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  have hadm : StatedLieAdmissible .PSL 2 2 (n * p) := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro h1
      have h' : 2 ^ (n * p) = 2 := (Prod.mk.inj h1).2
      omega
    · intro h1
      have h' : 2 ^ (n * p) = 3 := (Prod.mk.inj h1).2
      have hdvd : 2 ∣ 2 ^ (n * p) := dvd_pow_self 2 (by omega)
      rw [h'] at hdvd
      norm_num at hdvd
  have hSC : StatedClassicalModel (↥T ⧸ Subgroup.center ↥T) .PSL 2 2 (n * p) :=
    ⟨hadm, F, inferInstance, inferInstance, hcardF', ⟨e1.symm.trans eZ⟩⟩
  exact ⟨by simpa [Nat.mul_comm] using largeEvenInLambda2_typeA hSC,
    by simpa [Nat.mul_comm] using ggHasLabel_typeA hSC⟩

private theorem ltrca_split_label_twA {a n : ℕ} {R S : Type} [Group R] [Group S]
    {E : Type} [Field E] [Fintype E]
    (hE : Fintype.card E = (2 ^ n) ^ 2) (hn : 1 ≤ n) (h3a : 3 ≤ a)
    (hane : (a, 2 ^ n) ≠ (3, 2))
    {g : ↥(StatedSU a (2 ^ n) E) →* S}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center ↥(StatedSU a (2 ^ n) E))
    (e : R ≃* (S ⧸ Subgroup.center S)) :
    LargeEvenInLambda2 ⟨.twA, a - 1, n⟩ ∧ GGHasLabel ⟨.twA, a - 1, n⟩ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEnat : Nat.card E = (2 ^ n) ^ 2 := by
    rw [Nat.card_eq_fintype_card]; exact hE
  have hqSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := n) (F := E) hEnat h3a hane
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central
    g hg hqSU.1.1 hgk
  let e2 : (↥(StatedSU a (2 ^ n) E) ⧸
      Subgroup.center ↥(StatedSU a (2 ^ n) E)) ≃*
      StatedProj (StatedSU a (2 ^ n) E) :=
    QuotientGroup.quotientMulEquivOfEq hqSU.2
  have hb : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
  have eT : S ⧸ Subgroup.center S ≃*
      StatedProj (StatedSU (a - 1 + 1) (2 ^ n) E) := by
    rw [hb]; exact e1.symm.trans e2
  have hlabS : GGHasLabel ⟨.twA, a - 1, n⟩ (S ⧸ Subgroup.center S) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (b := a - 1) (m := n)
      hEnat eT
  have hΛ : LargeEvenInLambda2 ⟨.twA, a - 1, n⟩ := by
    refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA
      (b := a - 1) (m := n) hn (by omega) ?_
    intro hb2
    have ha3 : a = 3 := by omega
    by_contra hn2
    have hn1 : n = 1 := by omega
    exact hane (by rw [ha3, hn1]; norm_num)
  exact ⟨hΛ, ggHasLabel_of_mulEquiv e.symm hlabS⟩

private theorem ltrca_ker_proj_eq_center {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) :
    (TablePThreeKG.proj θ).ker = Subgroup.center X := by
  rw [show TablePThreeKG.proj θ =
      (θ : X ⧸ Subgroup.center X →* R).comp
        (QuotientGroup.mk' (Subgroup.center X)) from rfl,
    MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X))
      (θ : X ⧸ Subgroup.center X →* R) θ.injective,
    QuotientGroup.ker_mk']

private theorem ltrca_component_map_proj {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {σ : MulAut X} {J : Subgroup X}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup σ))
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) :
    CFSG.Assembly.IsComponentOf (J.map (TablePThreeKG.proj θ))
      (ggAutFixedSubgroup (ggInducedAut θ σ)) ∧
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map (TablePThreeKG.proj θ)) ⧸ Subgroup.center ↥(J.map (TablePThreeKG.proj θ))) := by
  have hcomp := TablePThreeKG.leafRComp_holds X hX R θ σ
  refine ⟨hcomp.1 J hJ, ?_⟩
  have hker : ((TablePThreeKG.proj θ).subgroupMap J).ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : TablePThreeKG.proj θ (x : X) = 1 := by
      have h1 := congrArg Subtype.val hx
      rw [MonoidHom.subgroupMap_apply_coe] at h1
      simpa using h1
    have hxX : (x : X) ∈ Subgroup.center X := by
      rw [← ltrca_ker_proj_eq_center θ]
      exact MonoidHom.mem_ker.mpr hx1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hxX) (y : X)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central
    ((TablePThreeKG.proj θ).subgroupMap J)
    ((TablePThreeKG.proj θ).subgroupMap_surjective J) ⟨hJ.2.2.1⟩ hker

private theorem ltrca_component_primeForm {p N n : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hX : commutator X = ⊤) (hN1 : 1 ≤ N)
    (hloc : GGTPNLocalCore p A σ J)
    (hUF : UnitaryFieldData 2 n K)
    {θ : X ⧸ Subgroup.center X ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    (hind : GGInducedInn A θ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      (LargeEvenGUSet (Fin N) K (2 ^ n))))
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) :
    ∃ (Jbar : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))))
      (T : Subgroup (primeFormP hUF (idGram K N))),
      CFSG.Assembly.IsComponentOf Jbar (ggAutFixedSubgroup (ggInducedAut θ σ)) ∧
      T = Jbar.map (InndiagSU.projEquiv hUF hN1).toMonoidHom ∧
      CFSG.Open.IsComponentOf T
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥T ⧸ Subgroup.center ↥T) := by
  classical
  let e : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ≃*
      primeFormP hUF (idGram K N) := InndiagSU.projEquiv hUF hN1
  let δ' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) := ggInducedAut θ σ
  let Jbar : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) :=
    J.map (TablePThreeKG.proj θ)
  let T : Subgroup (primeFormP hUF (idGram K N)) := Jbar.map e.toMonoidHom
  have hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup σ) := hloc.2.2.2.1
  obtain ⟨hJbar, hisoJ⟩ := ltrca_component_map_proj hX hJ θ
  have hfix : Subgroup.map e.toMonoidHom (ggAutFixedSubgroup δ') =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩) := by
    ext y
    rw [Subgroup.mem_map_equiv]
    have h := TablePThreeKG.uni_cube_fixSubgroup_projEquiv hUF hN1 hdconj hd (e.symm y)
    simpa only [e, MulEquiv.apply_symm_apply] using h
  have hfixcongr : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.congr e δ') =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
    exact hfix
  have hcomp : CFSG.Assembly.IsComponentOf T
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr e δ')) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
    refine ⟨Subgroup.map_mono hJbar.1, CFSG.Assembly.IsSubnormal.map e.toMonoidHom hJbar.2.1, ?_⟩
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective Jbar e.toMonoidHom e.injective).symm hJbar.2.2
  have hT : CFSG.Open.IsComponentOf T
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) := by
    rw [← hfixcongr, ← CFSG.Assembly.isComponentOf_iff_open]
    exact hcomp
  let eJ : Jbar ≃* Jbar.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective Jbar e.toMonoidHom e.injective
  have hcenter : (Subgroup.center Jbar).map eJ.toMonoidHom =
      Subgroup.center (Jbar.map e.toMonoidHom) := Subgroup.map_center_eq eJ
  exact ⟨Jbar, T, hJbar, rfl, hT, ⟨hisoJ.some.trans (QuotientGroup.congr _ _ eJ hcenter)⟩⟩

private theorem ltrca_ca2 {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore 3 A σ J)
    (hmk : GGTPNMarked 3 (fun _ lab => lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel)) A) :
    (∃ k : ℕ, 3 ≤ k ∧ GGHasLabel (⟨.twA, k, 1⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J)) ∨
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨hcomm, hΛX⟩ := ltrca_marking hmk
  obtain ⟨K, hFld, hFin, hcard, θ, hind⟩ :=
    ltrca_exists_unitary_model (labX := (⟨.twA, 5, 1⟩ : LargeEvenLabel)) rfl hmk
  letI : Field K := hFld
  letI : Finite K := hFin
  have hcard' : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hcard
  have hUF : UnitaryFieldData 2 1 K := unitaryFieldData_of_card hcard' (by norm_num)
  have hσA : σ ∈ A := hloc.2.1
  have hσ3 : σ ^ 3 = 1 := hloc.1.2 σ hσA
  have hδ3 : (ggInducedAut θ σ) ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  obtain ⟨d, hd, hdconj⟩ :=
    ltrca_exists_unitary_lift (p := 3) (N := 6) (n := 1) hUF hind hσA
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hN3 : 3 ≤ 6 := by norm_num
  have hNq : (6, 2 ^ 1) ≠ (3, 2) := by norm_num
  obtain ⟨c, hdp⟩ :=
    ltrca_pow_scalar_of_isConjBy hUF hcard' hN3 hNq Nat.prime_three hpq hd hdconj hδ3
  obtain ⟨Jbar, T, hJbar, hTeq, hT, hequiv⟩ :=
    ltrca_component_primeForm (p := 3) (N := 6) (n := 1) hcomm (by norm_num) hloc hUF hind hd hdconj
  by_cases hsplit : ∃ b : K, b ^ 3 = (c : K)
  ·
    have hc_mem : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈
        primeFormUnitary hUF (idGram K 6) := by
      rw [← hdp]
      exact Subgroup.pow_mem _ hd 3
    have hcn : hUF.norm (c : K) = 1 :=
      norm_eq_one_of_scalar_mem_primeFormUnitary hUF (by norm_num) 1 hc_mem
    obtain ⟨d', hd', u, hd'p, hd'eq, hconj⟩ :=
      ltrca_rescale (p := 3) (N := 6) (n := 1) hUF hcard' Nat.prime_three hpq hd hdp hcn hsplit
    have hδ' : IsConjBy d' (ggInducedAut θ σ) := by
      intro h h' hrel
      refine hdconj h h' ?_
      show (h' : GL (Fin 6) K) = d * (h : GL (Fin 6) K) * d⁻¹
      rw [hrel, hd'eq]
      exact InndiagSU.scalar_mul_conj u d (h : GL (Fin 6) K)
    have hT' : CFSG.Open.IsComponentOf T
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (primeFormConjHom hUF (idGram K 6) ⟨d', hd'⟩)) := by
      rw [hconj]; exact hT
    have hq : 2 ≤ 2 ^ 1 := by norm_num
    have H : UnitaryPrimaryData hUF.bar (idForm hUF 6) (Matrix.GeneralLinearGroup.toLin d') :=
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
        hUF hd' Nat.prime_three (by norm_num) (by rw [hd'p, map_one])
    obtain ⟨a₀, ha₀⟩ := exists_good_primaryFactor_of_component hq ⟨d', hd'⟩ rfl H T hT'
    rcases ltrca_split_component (p := 3) (N := 6) (n := 1) hUF hcard'
        Nat.prime_three (by norm_num) hpq hd' hd'p a₀ ha₀ with
      ⟨hm2, F, hF, hFt, hFcard, h4, g, hg, hgk⟩ | ⟨h3m, hane, E, hE, hEt, hEcard, g, hg, hgk⟩
    · letI : Field F := hF
      letI : Fintype F := hFt
      exfalso
      have h2 : Fintype.card F = 2 := by simpa using hFcard
      omega
    · letI : Field E := hE
      letI : Fintype E := hEt
      have hane3 : primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d' :
          Module.End K (Fin 6 → K)) (a₀.1 : K[X]) ≠ 3 := by
        intro h3
        exact hane (by rw [h3]; norm_num)
      have hlabT : GGHasLabel (⟨.twA,
          primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d' : Module.End K (Fin 6 → K))
            (a₀.1 : K[X]) - 1, 1⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) :=
        (ltrca_split_label_twA (a := primaryMultiplicity
            (Matrix.GeneralLinearGroup.toLin d' : Module.End K (Fin 6 → K)) (a₀.1 : K[X]))
          (n := 1) (R := ↥J ⧸ Subgroup.center ↥J) (S := ↥T)
          (by simpa using hEcard) (by norm_num) h3m hane hg hgk hequiv.some).2
      exact Or.inl ⟨primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d' :
        Module.End K (Fin 6 → K)) (a₀.1 : K[X]) - 1, by omega, hlabT⟩
  ·
    have hc : ∀ b : K, b ^ 3 ≠ (c : K) := fun b hb => hsplit ⟨b, hb⟩
    obtain ⟨-, -, -, hcases⟩ :=
      unitary_fieldType_component (p := 3) (ℓ := 2) (f := 1) (n := 6)
        Nat.prime_three hUF (by norm_num) ⟨d, hd⟩ hdp hc hT
    rcases hcases with ⟨-, F, hF, hFt, hFcard, g, hg, hgk⟩ | ⟨h3Np, -⟩
    · letI : Field F := hF
      letI : Fintype F := hFt
      have hlabT : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥T ⧸ Subgroup.center ↥T) :=
        (ltrca_nonSplit_label_A (hUF := hUF) (p := 3) (N := 6) (n := 1) (F := F)
          (by norm_num) (by simpa using hFcard) hg hgk).2
      exact Or.inr (ggHasLabel_of_mulEquiv hequiv.some.symm hlabT)
    · omega

private theorem ltrca_not_iso_twA {k : ℕ} (hk : 3 ≤ k) {lab : LargeEvenLabel}
    (h : GGTPNRankOne lab) : ¬ GGLabelIso lab (⟨.twA, k, 1⟩ : LargeEvenLabel) := by
  intro hiso
  unfold GGLabelIso at hiso
  rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · rw [h1] at h
    simpa [GGTPNRankOne] using h
  · obtain ⟨-, ht, -⟩ := h1
    exact absurd ht (by simp)
  · obtain ⟨-, h2⟩ := h1
    exact absurd h2 (by simp)
  · obtain ⟨-, h2⟩ := h1
    exact absurd h2 (by simp)
  · obtain ⟨h1a, h2⟩ := h1
    have hn : lab.n = 1 := by
      simpa using (congrArg (fun l : LargeEvenLabel => l.n) h2).symm
    rw [hn] at h1a
    rw [h1a] at h
    simpa [GGTPNRankOne] using h
  · obtain ⟨-, h2⟩ := h1
    exact absurd h2 (by simp)
  · obtain ⟨-, h2⟩ := h1
    exact absurd h2 (by simp)
  · obtain ⟨h1a, -⟩ := h1
    exact absurd h1a (by simp)

private theorem ltrca_ca3
    {Q : Type} [Group Q]
    (hclass : (∃ k : ℕ, 3 ≤ k ∧ GGHasLabel (⟨.twA, k, 1⟩ : LargeEvenLabel) Q) ∨
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) Q)
    (hlab : ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGTPNRankOne lab ∧
      GGHasLabel lab Q) :
    GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) Q := by
  rcases hclass with ⟨k, hk, hkQ⟩ | h13
  · obtain ⟨lab, hΛ, hrk, hlabQ⟩ := hlab
    have hΛk : LargeEvenInLambda2 (⟨.twA, k, 1⟩ : LargeEvenLabel) := by
      simp only [LargeEvenInLambda2]
      omega
    exact absurd (ggLabelRigidInput_holds lab (⟨.twA, k, 1⟩ : LargeEvenLabel) Q hΛ hΛk
      hlabQ hkQ) (ltrca_not_iso_twA hk hrk)
  · exact h13

theorem ggFieldTwoCorner_rankOne :
    GGFieldTwoCornerRankOne := by
  intro G _ _ p B Bs x L D J y K hset hlab
  obtain ⟨hN, hx, hloc, hmk⟩ := ltrca_ca1 hset
  exact ltrca_ca3 (ltrca_ca2 hloc hmk) hlab

theorem ggFieldTwoCorner_of_split (ha : GGFieldTwoCornerRankOne) (hb : GGFieldTwoCornerNoSL28) :
    GGFieldTwoCorner := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn hJK hp3 hl hlab lab hΛ hhas hrk
  have hset : GGFieldTwoCornerSetting p B Bs x L D J y K :=
    ⟨hc, hL, hK, hn, hJK, hp3, hl, hlab⟩
  exact hb G p B Bs x L D J y K hset (ha G p B Bs x L D J y K hset ⟨lab, hΛ, hrk, hhas⟩)

end CFSG.StandardType

end
