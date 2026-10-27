module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaH
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusModel
public import CFSG.RankThree.GF2n.Smith81.OrthE2Natural
public import CFSG.Adapters.Certificate43Check
import CFSG.RankThree.OrthogonalInvolutions.DicksonReflect
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.LeviAssembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpModel
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Quasithin.Background.C31Steps
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Quasithin.EmptyFaithful.R3c20A
public import CFSG.Quasithin.EmptyFaithful.SBc5Aut
public import CFSG.Quasithin.EmptyFaithful.SzN17Abs
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Blk
public import CFSG.Quasithin.Vol2.KGFactC31HSCases
public import CFSG.Quasithin.Vol2.KGFactC31HSMod
public import CFSG.Quasithin.Vol2.KGFactC31Hat
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec45
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import Certificates.Certificate9530

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.Open
  CFSG.ComponentClassification.RankTwoOddLie Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

private theorem rckGL3_centerPPrime_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {p : ℕ} (h : CenterPPrime H p) : CenterPPrime G p := by
  intro z hz hz2
  refine e.injective ?_
  rw [map_one]
  refine h (e z) ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨g, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz g).symm]
  · rw [← map_pow, hz2, map_one]

theorem rckGL1_eq_one_of_pow_two_eq_one_of_centerPPrime {G : Type*} [Group G]
    (h : CenterPPrime G 2) : ∀ {z : G}, z ∈ Subgroup.center G →
      ∀ n : ℕ, z ^ (2 ^ n) = 1 → z = 1 := by
  intro z hz n
  induction n generalizing z with
  | zero => intro hz2; simpa using hz2
  | succ n ih =>
    intro hz2
    have hz2' : (z ^ 2) ^ (2 ^ n) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hz2
    have hzc : z ^ 2 ∈ Subgroup.center G := pow_mem hz 2
    exact h z hz (ih hzc hz2')

private theorem rckGL1_conj_pow_apply {G : Type*} [Group G] {k y z : G}
    (hz : z ∈ Subgroup.center G) (h : k * y * k⁻¹ = z * y) (n : ℕ) :
    ((MulAut.conj k) ^ n) y = z ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul]
    have hzpow : (MulAut.conj k) (z ^ n) = z ^ n := by
      rw [MulAut.conj_apply]
      have hzc : z ^ n ∈ Subgroup.center G := pow_mem hz n
      have hcomm := Subgroup.mem_center_iff.mp hzc k
      rw [hcomm]; group
    rw [hzpow, MulAut.conj_apply, h, pow_succ]
    group

private theorem rckGL1_exists_pow_two_eq_one_of_mem_pCoreOf {X : Type*} [Group X]
    {H : Subgroup X} {k : X} (hk : k ∈ pCoreOf 2 H) :
    ∃ b : ℕ, k ^ (2 ^ b) = 1 := by
  have hP : IsPGroup 2 (pCoreOf 2 H) := by
    change IsPGroup 2 ((pCore 2 ↥H).map H.subtype)
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  obtain ⟨b, hb⟩ := hP ⟨k, hk⟩
  exact ⟨b, by simpa using congrArg (Subtype.val) hb⟩

private theorem rckGL1_pCoreOf_le {X : Type*} [Group X] (H : Subgroup X) :
    pCoreOf 2 H ≤ H := by
  intro k hk
  rw [pCoreOf] at hk
  obtain ⟨a, _ha, hak⟩ := Subgroup.mem_map.mp hk
  rw [← hak]
  exact a.property

private theorem rckGL2_scalar_of_commute_su {F : Type} [Field F] [Finite F] [CharP F 2]
    {g n : ℕ} (hF : Nat.card F = (2 ^ g) ^ 2) (hg : 1 ≤ g) {B : GL (Fin n) F}
    (hB : ∀ u : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) n,
      B * (u : GL (Fin n) F) = (u : GL (Fin n) F) * B) :
    ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨P, hP⟩ := Unitary.exists_wittMatrix (p := 2) (f := g) hF n
  set N : GL (Fin n) F := P * B * P⁻¹ with hNdef
  have hcomm : ∀ g' ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 g F n,
      N * g' = g' * N := by
    intro g' hg'
    let e : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) n ≃*
        CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 g F n :=
      (Unitary.conjEquiv P hP).trans
        (MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU (p := 2) (f := g) hF n))
    let u : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) n := e.symm ⟨g', hg'⟩
    have hgu : (e u : GL (Fin n) F) = g' := by
      have h := MulEquiv.apply_symm_apply e ⟨g', hg'⟩
      exact congrArg Subtype.val h
    have hcu : (e u : GL (Fin n) F) = P * (u : GL (Fin n) F) * P⁻¹ := by
      change ((MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU (p := 2) (f := g) hF n))
          (Unitary.conjEquiv P hP u) : GL (Fin n) F) = P * (u : GL (Fin n) F) * P⁻¹
      rw [MulEquiv.subgroupCongr_apply, Unitary.coe_conjEquiv]
    have hg_eq : g' = P * (u : GL (Fin n) F) * P⁻¹ := hgu ▸ hcu
    have hu : (u : GL (Fin n) F) = P⁻¹ * g' * P := by rw [hg_eq]; group
    have key1 : N * g' = P * (B * (u : GL (Fin n) F)) * P⁻¹ := by rw [hNdef, hu]; group
    have key2 : g' * N = P * ((u : GL (Fin n) F) * B) * P⁻¹ := by rw [hg_eq, hNdef]; group
    calc N * g' = P * (B * (u : GL (Fin n) F)) * P⁻¹ := key1
      _ = P * ((u : GL (Fin n) F) * B) * P⁻¹ := by rw [hB u]
      _ = g' * N := key2.symm
  have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 g F :=
    ⟨Nat.prime_two, hg, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ g + 1 ≠ 1 by
    have := Nat.one_le_two_pow (n := g); omega)
  have hNmem := TableBUE.mem_scalars_of_commute (n := g) (d := n) (p := q) hUFD hqprime hqdvd hcomm
  rw [CFSG.Assembly.largeEvenScalars_def] at hNmem
  obtain ⟨c, hc⟩ := hNmem
  refine ⟨c, ?_⟩
  have hBexpr : B = P⁻¹ * N * P := by rw [hNdef]; group
  rw [hBexpr, ← hc]
  rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem rckGL2_centerPPrime_su {F : Type} [Field F] [Finite F] [CharP F 2]
    {g n : ℕ} (hF : Nat.card F = (2 ^ g) ^ 2) (hg : 1 ≤ g) (hn : 1 ≤ n) :
    CenterPPrime (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) n) 2 := by
  intro z hz hz2
  have hB : ∀ u : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 g) n,
      (z : GL (Fin n) F) * (u : GL (Fin n) F) = (u : GL (Fin n) F) * (z : GL (Fin n) F) := by
    intro u
    have h := (Subgroup.mem_center_iff.mp hz u).symm
    simpa using congrArg Subtype.val h
  obtain ⟨c, hc⟩ := rckGL2_scalar_of_commute_su hF hg hB
  have hz2' : ((z : GL (Fin n) F)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one]
  rw [hc] at hz2'
  have hz2'' : Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ 2) = 1 := by
    rw [map_pow]
    exact hz2'
  have hc2F : (c : F) ^ 2 = 1 := by
    have h := congrArg (fun M : GL (Fin n) F =>
      (M : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩) hz2''
    simpa only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      Units.val_pow_eq_pow_val] using h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 : c = 1 := Units.ext (eq_one_of_pow_eq_one_of_charP (p := 2) hc2F)
  exact Subtype.ext (by rw [hc, hc1, map_one, Subgroup.coe_one])

private theorem rckGL2_minus_rank_zero {K : Type} [Field K] {b c : K} {m : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : m ≤ 1)
    {γ : Fin (Spin.Twisted.minusDatum m hirr).rank → ℤ}
    (hγ : GGLongRoot (Spin.Twisted.minusDatum m hirr) γ) : False := by
  obtain ⟨w, γ₀, hγ₀, -, -⟩ := hγ
  rw [Spin.Twisted.minusDatum_roots, Spin.rootsB_eq] at hγ₀
  rcases hγ₀ with ⟨i, -, -, -, -, -, -⟩ | ⟨i, -, -, -⟩
  · have := i.isLt; omega
  · have := i.isLt; omega

theorem rckGL4_centerPPrime_spinMinus_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CenterPPrime (spinGroup (quadMinus 2 K b c)) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  haveI := CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.charP_shortField (b := b) (c := c)
  have hQ : (polarBilin (quadMinus 2 K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  haveI : Algebra.IsCentral K (CliffordAlgebra (quadMinus 2 K b c)) :=
    isCentral_cliffordAlgebra_quadMinus (n := 2) (b := b) (c := c) hirr
  have hinj : Function.Injective (spinAction (quadMinus 2 K b c)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact ker_spinAction_eq_bot_of_isCentral _ CharTwo.two_eq_zero
  let L : Subgroup (spinGroup (quadMinus 2 K b c)) :=
    rankOne (minusDatum 2 hirr).rootGroup (0 : Fin (2 - 1))
  have hspin_le_omega : (spinAction (quadMinus 2 K b c)).range ≤
      omegaGroup (quadMinus 2 K b c) hQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hl, hev, hnorm, hx⟩ := exists_list_of_spinGroup x
    rw [hx]
    exact CFSG.RankThree.OrthogonalInvolutions.prod_reflect_mem_omegaGroup _ _ l hl hev
  have hcardL : Nat.card ↥L = Nat.card ↥(omegaGroup (quadMinus 2 K b c) hQ) := by
    have hLcard : Nat.card ↥L = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
      dsimp only [L]
      haveI := CFSG.LieType.Universal.Spin.Twisted.finite_shortField (b := b) (c := c)
      let e := CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.shortEquiv
        (n := 2) (hirr := hirr) (i := (0 : Fin (2 - 1))) (by norm_num)
      rw [← Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartOne.KCOrthogonal.card_sl2 (F := ShortField b c),
        CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.card_shortField]
      ring_nf
    have homega : Nat.card ↥(omegaGroup (quadMinus 2 K b c) hQ) =
        Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
      have hO := CFSG.RankThree.GF2n.Smith81.card_orth_two_minus (K := K) hirr
      have hri := relIndex_omegaGroup (quadMinus 2 K b c) hQ
      have hle := omegaGroup_le (quadMinus 2 K b c) hQ
      have hcard := Subgroup.card_mul_index ((omegaGroup (quadMinus 2 K b c) hQ).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)))
      rw [show ((omegaGroup (quadMinus 2 K b c) hQ).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c))).index = 2 from hri] at hcard
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
      have hE := commutator_orthogonalGroup_quadMinus_of_two_le (K := K) (n := 2) (le_refl 2) hirr
      have hmap := statedOmega_quadMinus_eq_map_of_two_le (K := K) (n := 2) (le_refl 2) hirr
      rw [← hE] at hmap
      have h1 : Nat.card (StatedOmega (StatedQuadMinus 2 K b c)) =
          Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c),
            TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)⁆ := by
        rw [hmap]
        exact Subgroup.card_map_of_injective
          (f := (toLinEquiv (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K).symm.toMonoidHom)
          (MulEquiv.injective _)
      have h2 : Nat.card ↥(omegaGroup (quadMinus 2 K b c) hQ) =
          Nat.card (StatedOmega (StatedQuadMinus 2 K b c)) := by
        rw [h1]
        omega
      rw [h2, CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
        CFSG.SeitzReduction.F4Pilot.ordSL_two]
      ring_nf
    rw [hLcard, homega]
  have hLtop : L = ⊤ := by
    have hLmap_le : L.map (spinAction (quadMinus 2 K b c)) ≤
        omegaGroup (quadMinus 2 K b c) hQ :=
      (Subgroup.map_le_range (spinAction (quadMinus 2 K b c)) L).trans hspin_le_omega
    have hcard : Nat.card ↥(L.map (spinAction (quadMinus 2 K b c))) =
        Nat.card ↥(omegaGroup (quadMinus 2 K b c) hQ) := by
      rw [Subgroup.card_map_of_injective hinj, hcardL]
    have hLeq : L.map (spinAction (quadMinus 2 K b c)) = omegaGroup (quadMinus 2 K b c) hQ :=
      Subgroup.eq_of_le_of_card_ge hLmap_le hcard.ge
    have hrange_eq : (spinAction (quadMinus 2 K b c)).range =
        L.map (spinAction (quadMinus 2 K b c)) := by
      apply le_antisymm
      · intro x hx
        rw [hLeq]
        exact hspin_le_omega hx
      · exact Subgroup.map_le_range (spinAction (quadMinus 2 K b c)) L
    have hmap_top : L.map (spinAction (quadMinus 2 K b c)) =
        (⊤ : Subgroup (spinGroup (quadMinus 2 K b c))).map (spinAction (quadMinus 2 K b c)) := by
      rw [← MonoidHom.range_eq_map, hrange_eq]
    exact Subgroup.map_injective hinj hmap_top
  have e : Matrix.SpecialLinearGroup (Fin 2) (ShortField b c) ≃*
      spinGroup (quadMinus 2 K b c) :=
    (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.shortEquiv 2 hirr 0 (by norm_num)).trans
      ((MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv)
  exact rckGL3_centerPPrime_of_mulEquiv e.symm
    (centerPPrime_specialLinear 1 (ShortField b c))

theorem rckGL1_centerPPrime_ggU
    {t : StatedLieTag} (ht : GGPosTag t) {m g : ℕ} (hg : 1 ≤ g)
    (hPM : t = .POmegaMinus → 2 ≤ m) :
    CenterPPrime (ggU t m g).K 2 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    cases m with
    | zero =>
      change CenterPPrime (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2)) 2
      exact centerPPrime_specialLinear 0 (ZMod 2)
    | succ m' =>
      change CenterPPrime (Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 g)) 2
      exact centerPPrime_specialLinear m' (GaloisField 2 g)
  ·
    have hF : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 := card_galoisField_two_mul 2 g hg
    have e : ggU .PSU m g = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * g)) 2 g) m, Unitary.rootDatum hF m⟩ := by
      simp only [ggU, lieUniversal, hg, ↓reduceDIte]
    rw [e]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    ·
      subst hm0
      intro z _ _
      exact Subsingleton.elim z 1
    ·
      exact rckGL2_centerPPrime_su hF hg hmpos
  ·
    change CenterPPrime ↥(StatedSp m (GaloisField 2 g)) 2
    exact centerPPrime_statedSp m (GaloisField 2 g)
  ·
    by_cases hm : 3 ≤ m
    · have e : ggU .POmegaPlus m g = ⟨spinGroup (Spin.quadPlus m (GaloisField 2 g)),
          Spin.plusDatum m (GaloisField 2 g) hm⟩ := by
        simp only [ggU, lieUniversal, dif_pos hm]
      rw [e]
      have hcenter := CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo
        (K := GaloisField 2 g) hm
      intro z hz _
      rw [hcenter, Subgroup.mem_bot] at hz
      exact hz
    · have e : ggU .POmegaPlus m g = trivialUniversal := by
        simp only [ggU, lieUniversal, dif_neg hm]
      rw [e]
      change CenterPPrime (Matrix.SpecialLinearGroup (Fin 1) (ZMod 2)) 2
      exact centerPPrime_specialLinear 0 (ZMod 2)
  ·
    have hm2 : 2 ≤ m := hPM rfl
    by_cases hm : 4 ≤ m
    · have e : ggU .POmegaMinus m g = ⟨spinGroup (Spin.quadMinus m (GaloisField 2 g)
          (minusCoeffs 2 g).1 (minusCoeffs 2 g).2),
          Spin.Twisted.minusDatum m (minusCoeffs_irr 2 g)⟩ := by
        simp only [ggU, lieUniversal]
      rw [e]
      have hcenter := CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
        (F := GaloisField 2 g) hm (minusCoeffs_irr 2 g)
      intro z hz _
      rw [hcenter, Subgroup.mem_bot] at hz
      exact hz
    ·
      have e : ggU .POmegaMinus m g = ⟨spinGroup (Spin.quadMinus m (GaloisField 2 g)
            (minusCoeffs 2 g).1 (minusCoeffs 2 g).2),
            Spin.Twisted.minusDatum m (minusCoeffs_irr 2 g)⟩ := by
        simp only [ggU, lieUniversal]
      rw [e]
      have hm23 : m = 2 ∨ m = 3 := by omega
      rcases hm23 with rfl | rfl
      ·
        exact rckGL4_centerPPrime_spinMinus_two (minusCoeffs_irr 2 g)
      ·
        have hF : Nat.card (GaloisField 2 g) = 2 ^ g := GaloisField.card 2 g (by omega)
        have hK : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 :=
          card_galoisField_two_mul 2 g hg
        obtain ⟨_, eSU, -⟩ := CFSG.RankThree.PartOne.CTP.SU4Even.exists_equiv_su_four_even
          (F := GaloisField 2 g) (K := GaloisField 2 (2 * g)) (f := g) hF hK
          (minusCoeffs_irr 2 g)
        exact rckGL3_centerPPrime_of_mulEquiv eSU
          (rckGL2_centerPPrime_su (F := GaloisField 2 (2 * g)) (g := g) (n := 4)
            hK hg (by norm_num))
  ·
    exact centerPPrime_adjoint .F4 (GaloisField 2 g)
  ·
    exact centerPPrime_e6 (GaloisField 2 g)
  ·
    exact centerPPrime_e7 (GaloisField 2 g)
  ·
    exact centerPPrime_adjoint .E8 (GaloisField 2 g)
  ·
    exact centerPPrime_fixedGroup (CFSG.LieType.Steinberg.Exceptional.frobQ 2 g)
      (CFSG.LieType.Steinberg.Exceptional.frobQ_frobQ 2 g hg)

theorem rckGL1_centerPPrime_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g) :
    CenterPPrime (triD4Universal F σ).K 2 := by
  have hq : 2 ≤ 2 ^ g := Nat.le_self_pow (by have := hF.1; omega) 2
  have hcenter : Subgroup.center (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) = ⊥ :=
    CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card hq hF.2.1 hF.2.2
  change CenterPPrime ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) 2
  intro z hz _
  rw [hcenter, Subgroup.mem_bot] at hz
  exact hz

private theorem rckGL1_long_ggU
    (hH : RCKLemmaHLong) {X : Type} [Group X] [Finite X] {K R : Subgroup X}
    {t' : StatedLieTag} {m g : ℕ} {β : Fin (ggU t' m g).D.rank → ℤ} (ht : GGPosTag t')
    (hg : 1 ≤ g) (hβ : GGLongRoot (ggU t' m g).D β) (hvia : GGRootVia (ggU t' m g) K R β)
    {r : X} (hr : r ∈ R) (hr1 : r ≠ 1) :
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤
      Subgroup.centralizer (R : Set X) := by
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hvia
  have hPM : t' = .POmegaMinus → 2 ≤ m := by
    intro htPM
    by_contra hm
    push Not at hm
    subst htPM
    exact rckGL2_minus_rank_zero (minusCoeffs_irr 2 g) (by omega) hβ
  intro k hk
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  have hkH : k ∈ K ⊓ Subgroup.centralizer ({r} : Set X) :=
    rckGL1_pCoreOf_le (K ⊓ Subgroup.centralizer ({r} : Set X)) hk
  have hkr : k * r = r * k := Subgroup.mem_centralizer_singleton_iff.mp hkH.2
  have hkK : k ∈ K := hkH.1
  have hkrange : k ∈ φ.range := hφrange ▸ hkK
  obtain ⟨k', hk'eq⟩ := hkrange
  rw [hR] at hs hr
  obtain ⟨y', hy'mem, hy's⟩ := Subgroup.mem_map.mp hs
  obtain ⟨x', hx'mem, hx'eq⟩ := Subgroup.mem_map.mp hy'mem
  obtain ⟨y, hymem, hyr⟩ := Subgroup.mem_map.mp hr
  obtain ⟨x, hxmem, hxeq⟩ := Subgroup.mem_map.mp hymem
  have hxeq' : u * x * u⁻¹ = y := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxeq
  have hx'eq' : u * x' * u⁻¹ = y' := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx'eq
  have hx1 : x ≠ 1 := by
    intro hx0
    apply hr1
    rw [← hyr, ← hxeq', hx0]
    simp
  set z : (ggU t' m g).K := k' * y * k'⁻¹ * y⁻¹ with hzdef
  have hzker : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hzdef, hk'eq, hyr]
    have h1 : k * r * k⁻¹ = r := by rw [hkr]; group
    rw [h1, mul_inv_cancel]
  have hzcenter : z ∈ Subgroup.center (ggU t' m g).K := hφker hzker
  have hzy : k' * y * k'⁻¹ = z * y := by rw [hzdef]; group
  obtain ⟨b, hkb⟩ := rckGL1_exists_pow_two_eq_one_of_mem_pCoreOf hk
  have hk'pow_ker : k' ^ (2 ^ b) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk'eq, hkb]
  have hk'pow_center : k' ^ (2 ^ b) ∈ Subgroup.center (ggU t' m g).K := hφker hk'pow_ker
  have hconj := rckGL1_conj_pow_apply hzcenter hzy (2 ^ b)
  have hconj_triv : ((MulAut.conj k') ^ (2 ^ b)) y = y := by
    rw [← map_pow, MulAut.conj_apply]
    have hcomm := Subgroup.mem_center_iff.mp hk'pow_center y
    rw [← hcomm]; group
  rw [hconj_triv] at hconj
  have hzpow : z ^ (2 ^ b) = 1 := by
    have h : (1 : (ggU t' m g).K) * y = z ^ (2 ^ b) * y := by simpa using hconj
    exact (mul_right_cancel h).symm
  have hz1 : z = 1 := rckGL1_eq_one_of_pow_two_eq_one_of_centerPPrime
    (rckGL1_centerPPrime_ggU ht hg hPM) hzcenter b hzpow
  have hk'y : k' * y = y * k' := by
    have h1 : k' * y * k'⁻¹ = y := by rw [hzy, hz1, one_mul]
    calc k' * y = k' * y * k'⁻¹ * k' := by group
      _ = y * k' := by rw [h1]
  have hcomm_x : (u⁻¹ * k' * u) * x = x * (u⁻¹ * k' * u) := by
    have h := hk'y
    rw [← hxeq'] at h
    calc (u⁻¹ * k' * u) * x = u⁻¹ * (k' * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * x * u⁻¹) * k') * u := by rw [h]
      _ = x * (u⁻¹ * k' * u) := by group
  have hux_mem : u⁻¹ * k' * u ∈ Subgroup.centralizer ({x} : Set (ggU t' m g).K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm_x
  have hux_root : u⁻¹ * k' * u ∈
      Subgroup.centralizer ((ggU t' m g).D.rootGroup β : Set (ggU t' m g).K) :=
    (hH.1 t' m g β ht hg hβ) x hxmem hx1 hux_mem
  have hx'comm : x' * (u⁻¹ * k' * u) = (u⁻¹ * k' * u) * x' :=
    Subgroup.mem_centralizer_iff.mp hux_root x' hx'mem
  have hk'y' : k' * y' = y' * k' := by
    have h := hx'comm.symm
    calc k' * y' = u * (u⁻¹ * k' * u * x') * u⁻¹ := by rw [← hx'eq']; group
      _ = u * (x' * (u⁻¹ * k' * u)) * u⁻¹ := by rw [h]
      _ = y' * k' := by rw [← hx'eq']; group
  rw [← hk'eq, ← hy's, ← map_mul, ← map_mul, hk'y']

private theorem rckGL1_long_triD4
    (hH : RCKLemmaHLong) {X : Type} [Group X] [Finite X] {K R : Subgroup X}
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ}
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hF : TriField F σ g)
    (hβ : GGLongRoot (triD4Universal F σ).D β)
    (hvia : GGRootVia (triD4Universal F σ) K R β) {r : X} (hr : r ∈ R) (hr1 : r ≠ 1) :
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤
      Subgroup.centralizer (R : Set X) := by
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hvia
  intro k hk
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  have hkH : k ∈ K ⊓ Subgroup.centralizer ({r} : Set X) :=
    rckGL1_pCoreOf_le (K ⊓ Subgroup.centralizer ({r} : Set X)) hk
  have hkr : k * r = r * k := Subgroup.mem_centralizer_singleton_iff.mp hkH.2
  have hkK : k ∈ K := hkH.1
  have hkrange : k ∈ φ.range := hφrange ▸ hkK
  obtain ⟨k', hk'eq⟩ := hkrange
  rw [hR] at hs hr
  obtain ⟨y', hy'mem, hy's⟩ := Subgroup.mem_map.mp hs
  obtain ⟨x', hx'mem, hx'eq⟩ := Subgroup.mem_map.mp hy'mem
  obtain ⟨y, hymem, hyr⟩ := Subgroup.mem_map.mp hr
  obtain ⟨x, hxmem, hxeq⟩ := Subgroup.mem_map.mp hymem
  have hxeq' : u * x * u⁻¹ = y := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxeq
  have hx'eq' : u * x' * u⁻¹ = y' := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx'eq
  have hx1 : x ≠ 1 := by
    intro hx0
    apply hr1
    rw [← hyr, ← hxeq', hx0]
    simp
  set z : (triD4Universal F σ).K := k' * y * k'⁻¹ * y⁻¹ with hzdef
  have hzker : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hzdef, hk'eq, hyr]
    have h1 : k * r * k⁻¹ = r := by rw [hkr]; group
    rw [h1, mul_inv_cancel]
  have hzcenter : z ∈ Subgroup.center (triD4Universal F σ).K := hφker hzker
  have hzy : k' * y * k'⁻¹ = z * y := by rw [hzdef]; group
  obtain ⟨b, hkb⟩ := rckGL1_exists_pow_two_eq_one_of_mem_pCoreOf hk
  have hk'pow_ker : k' ^ (2 ^ b) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk'eq, hkb]
  have hk'pow_center : k' ^ (2 ^ b) ∈ Subgroup.center (triD4Universal F σ).K :=
    hφker hk'pow_ker
  have hconj := rckGL1_conj_pow_apply hzcenter hzy (2 ^ b)
  have hconj_triv : ((MulAut.conj k') ^ (2 ^ b)) y = y := by
    rw [← map_pow, MulAut.conj_apply]
    have hcomm := Subgroup.mem_center_iff.mp hk'pow_center y
    rw [← hcomm]; group
  rw [hconj_triv] at hconj
  have hzpow : z ^ (2 ^ b) = 1 := by
    have h : (1 : (triD4Universal F σ).K) * y = z ^ (2 ^ b) * y := by simpa using hconj
    exact (mul_right_cancel h).symm
  have hz1 : z = 1 := rckGL1_eq_one_of_pow_two_eq_one_of_centerPPrime
    (rckGL1_centerPPrime_triD4 hF) hzcenter b hzpow
  have hk'y : k' * y = y * k' := by
    have h1 : k' * y * k'⁻¹ = y := by rw [hzy, hz1, one_mul]
    calc k' * y = k' * y * k'⁻¹ * k' := by group
      _ = y * k' := by rw [h1]
  have hcomm_x : (u⁻¹ * k' * u) * x = x * (u⁻¹ * k' * u) := by
    have h := hk'y
    rw [← hxeq'] at h
    calc (u⁻¹ * k' * u) * x = u⁻¹ * (k' * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * x * u⁻¹) * k') * u := by rw [h]
      _ = x * (u⁻¹ * k' * u) := by group
  have hux_mem : u⁻¹ * k' * u ∈ Subgroup.centralizer ({x} : Set (triD4Universal F σ).K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm_x
  have hux_root : u⁻¹ * k' * u ∈
      Subgroup.centralizer ((triD4Universal F σ).D.rootGroup β : Set (triD4Universal F σ).K) :=
    (hH.2 F σ g β hF hβ) x hxmem hx1 hux_mem
  have hx'comm : x' * (u⁻¹ * k' * u) = (u⁻¹ * k' * u) * x' :=
    Subgroup.mem_centralizer_iff.mp hux_root x' hx'mem
  have hk'y' : k' * y' = y' * k' := by
    have h := hx'comm.symm
    calc k' * y' = u * (u⁻¹ * k' * u * x') * u⁻¹ := by rw [← hx'eq']; group
      _ = u * (x' * (u⁻¹ * k' * u)) * u⁻¹ := by rw [h]
      _ = y' * k' := by rw [← hx'eq']; group
  rw [← hk'eq, ← hy's, ← map_mul, ← map_mul, hk'y']

theorem rckK2NbrRootSub_of
    (hH : RCKLemmaHLong) (hS : RCKK2NbrRootSubShort) : RCKK2NbrRootSub := by
  intro X _ _ K R hpos r hr hr1
  rcases hpos with ⟨t', m, g, β, ht, hg, hβmem, hlong, hvia⟩ | ⟨F, _hFld, _hFin, σ, g, β, hTF, hβ, hvia⟩
  · rcases hlong with hlong | ⟨hshort, h2β⟩
    · exact rckGL1_long_ggU hH ht hg hlong hvia hr hr1
    · by_cases hL : GGLongRoot (ggU t' m g).D β
      · exact rckGL1_long_ggU hH ht hg hL hvia hr hr1
      · exact hS X K R t' m g β ht hg hβmem hL hshort h2β hvia r hr hr1
  · exact rckGL1_long_triD4 hH hTF hβ hvia hr hr1

end CFSG.StandardType.RCKC1
