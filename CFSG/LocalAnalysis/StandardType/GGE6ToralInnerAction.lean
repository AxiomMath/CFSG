module

public import CFSG.LocalAnalysis.StandardType.GGExcToralInnerAction
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.RankThree.Chevalley.G2CyclotomicTori
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest

public noncomputable section

namespace CFSG.StandardType.E6ToralInner

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableBExc CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.E6Descent


noncomputable abbrev e6DiagramMap (K : Type) [Field K] : ModGL Tag.E6 K :=
  diagramMap TwistTag.E6 K

theorem finite_fixed_le_map_adjointGroup_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK3 : 3 ∣ Nat.card K + 1) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (X : Subgroup (ModGL .E6 (AlgebraicClosure K)))
    [Finite X] (hXC : X ≤ adjointGroup .E6 (AlgebraicClosure K))
    (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    X ≤ (adjointGroup .E6 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have h3q : ¬ 3 ∣ Nat.card K - 1 := by
    intro h
    have hsub : 3 ∣ (Nat.card K + 1) - (Nat.card K - 1) :=
      Nat.dvd_sub hK3 h
    have h2 : 3 ∣ 2 := by
      rwa [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] at hsub
    norm_num at h2
  have hmain := CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect_card_units
    (τ := .E6) (K := K) (L := AlgebraicClosure K) 3 (Or.inl ⟨rfl, rfl⟩) Fr hFr X hXC hXF
  have hd3 : ((adjointGroup .E6 K).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).relIndex X ∣ 3 := hmain.1
  have hdq : ((adjointGroup .E6 K).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).relIndex X ∣
        (Nat.card K - 1) ^ 6 := hmain.2.2.2
  have hcop : Nat.Coprime 3 ((Nat.card K - 1) ^ 6) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3q).pow_right 6
  have hrel : ((adjointGroup .E6 K).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))).relIndex X = 1 := by
    have hdvd : ((adjointGroup .E6 K).map
        (baseChangeGL (algebraMap K (AlgebraicClosure K)))).relIndex X ∣ 1 := by
      have h := Nat.dvd_gcd hd3 hdq
      rwa [hcop.gcd_eq_one] at h
    exact Nat.dvd_one.1 hdvd
  exact Subgroup.relIndex_eq_one.1 hrel

theorem exists_rational_of_frob_fixed_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    [Fact (Nat.Prime 2)] [CharP (AlgebraicClosure K) 2] (hK3 : 3 ∣ Nat.card K + 1)
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : ModGL .E6 (AlgebraicClosure K)}
    (hy : y ∈ adjointGroup .E6 (AlgebraicClosure K))
    (hF : entrywiseFrobGL .E6 (AlgebraicClosure K) 2 f y = y) :
    ∃ r ∈ adjointGroup .E6 K, baseChangeGL (algebraMap K (AlgebraicClosure K)) r = y := by
  let X : Subgroup (ModGL .E6 (AlgebraicClosure K)) :=
    adjointGroup .E6 (AlgebraicClosure K) ⊓
      (entrywiseFrobGL .E6 (AlgebraicClosure K) 2 f).eqLocus (MonoidHom.id _)
  haveI : Finite X := Set.Finite.to_subtype
    ((finite_setOf_entrywiseFrobGL_eq (τ := .E6) (k := AlgebraicClosure K) 2 hf).subset
      fun g hg => (Subgroup.mem_inf.1 hg).2)
  have hFr : ∀ c : AlgebraicClosure K,
      iterateFrobenius (AlgebraicClosure K) 2 f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
  obtain ⟨r, hr, hry⟩ := finite_fixed_le_map_adjointGroup_E6 hK3
    (iterateFrobenius (AlgebraicClosure K) 2 f) hFr X inf_le_left
    (fun x hx => (Subgroup.mem_inf.1 hx).2) (Subgroup.mem_inf.2 ⟨hy, hF⟩)
  exact ⟨r, hr, hry⟩

theorem exists_weyl_of_inverted_family {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin (Tag.E6.rank) → Lˣ) (hexp : ∀ i j, a i j ^ 3 = 1)
    {q : ℕ} (hq : 3 ∣ q + 1) {y : ModGL .E6 L}
    (hy : y ∈ adjointGroup .E6 L)
    (hconj : ∀ i, y * rootDiagUnit .E6 ((a i)⁻¹) * y⁻¹ = rootDiagUnit .E6 (a i)) :
    ∃ w : WeylGroup .E6, ∀ i v, rootChar (a i) (w • v) = rootChar (a i) v ^ q := by
  have hy' : y ∈ (adjointGroup .E6 L : Set (ModGL .E6 L)) := hy
  rw [(bruhat_decomposition .E6 L).1, Set.mem_iUnion] at hy'
  obtain ⟨w, hw⟩ := hy'
  refine ⟨w, fun i v => ?_⟩
  have hD : rootDiagUnit .E6 (a i) =
      canonicalRep (coxeterSystem .E6) L w * rootDiagUnit .E6 ((a i)⁻¹) *
        (canonicalRep (coxeterSystem .E6) L w)⁻¹ :=
    rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell (a i) ((a i)⁻¹) hw (hconj i)
  have hchar : rootChar (a i) (w • v) = rootChar ((a i)⁻¹) v :=
    (rootDiagUnit_eq_conj_canonicalRep_iff (a i) ((a i)⁻¹) w).1 hD v
  rw [hchar]
  have hinv : rootChar ((a i)⁻¹) v = (rootChar (a i) v)⁻¹ := by
    simp only [rootChar, Pi.inv_apply, inv_zpow', zpow_neg, Finset.prod_inv_distrib]
  rw [hinv]
  have hχ3 : rootChar (a i) v ^ 3 = 1 :=
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one (hexp i) v
  obtain ⟨k, hk⟩ := hq
  have hqinv : rootChar (a i) v ^ q = (rootChar (a i) v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc rootChar (a i) v ^ q * rootChar (a i) v
        = rootChar (a i) v ^ (q + 1) := (pow_succ _ _).symm
      _ = rootChar (a i) v ^ (3 * k) := by rw [hk]
      _ = (rootChar (a i) v ^ 3) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hχ3, one_pow]
  exact hqinv.symm

theorem psi_conj_rootDiagUnit {L : Type} [Field L] (b : Fin (Tag.E6.rank) → Lˣ)
    (hb : ∀ i, b i ^ 3 = 1) :
    (canonicalRep (coxeterSystem .E6) L twE6W0)⁻¹ *
      e6DiagramMap L *
      rootDiagUnit .E6 b *
      ((canonicalRep (coxeterSystem .E6) L twE6W0)⁻¹ *
        e6DiagramMap L)⁻¹ =
      (rootDiagUnit .E6 b)⁻¹ := by
  set n0 : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L twE6W0 with hn0
  set P : ModGL .E6 L := e6DiagramMap L with hP
  have hPd : P * rootDiagUnit .E6 b * P⁻¹ =
      rootDiagUnit .E6 (fun i => b (e6Rho.symm i)) := by
    have h := diagramMap_mul_rootDiagUnit (K := L) (t := TwistTag.E6) b
    have h' : e6DiagramMap L * rootDiagUnit .E6 b =
        rootDiagUnit .E6 (fun i => b (e6Rho.symm i)) * e6DiagramMap L := by
      convert h using 2 <;> rfl
    calc P * rootDiagUnit .E6 b * P⁻¹ = (P * rootDiagUnit .E6 b) * P⁻¹ := rfl
      _ = (rootDiagUnit .E6 (fun i => b (e6Rho.symm i)) * P) * P⁻¹ := by rw [hP, h']
      _ = rootDiagUnit .E6 (fun i => b (e6Rho.symm i)) := by group
  have hconj : rootDiagUnit .E6 (fun i => b (e6Rho.symm i)) =
      n0 * rootDiagUnit .E6 b⁻¹ * n0⁻¹ := by
    rw [rootDiagUnit_eq_conj_canonicalRep_iff]
    intro v
    have hneg : rootChar (fun i => b (e6Rho.symm i)) (twE6W0 • v) =
        (rootChar (fun i => b (e6Rho.symm i)) (permLattice e6Rho v))⁻¹ := by
      rw [twE6W0_smul, CFSG.RankThree.Classical2.rootChar_neg']
    rw [hneg, rootChar_permLattice]
    have hsym : (fun i => (fun j => b (e6Rho.symm j)) (e6Rho i)) = b := by
      funext i
      exact congrArg b (Equiv.symm_apply_apply e6Rho i)
    rw [hsym]
    simp only [rootChar, Pi.inv_apply, inv_zpow', zpow_neg, Finset.prod_inv_distrib]
  calc (n0⁻¹ * P) * rootDiagUnit .E6 b * (n0⁻¹ * P)⁻¹
      = n0⁻¹ * (P * rootDiagUnit .E6 b * P⁻¹) * n0 := by group
    _ = n0⁻¹ * rootDiagUnit .E6 (fun i => b (e6Rho.symm i)) * n0 := by rw [hPd]
    _ = n0⁻¹ * (n0 * rootDiagUnit .E6 b⁻¹ * n0⁻¹) * n0 := by rw [hconj]
    _ = rootDiagUnit .E6 b⁻¹ := by group
    _ = (rootDiagUnit .E6 b)⁻¹ := by rw [rootDiagUnit_inv]

theorem psi_commute_canonicalRep {L : Type} [Field L] [CharP L 2]
    (u : WeylGroup .E6) :
    (canonicalRep (coxeterSystem .E6) L twE6W0)⁻¹ *
      e6DiagramMap L *
      canonicalRep (coxeterSystem .E6) L u *
      ((canonicalRep (coxeterSystem .E6) L twE6W0)⁻¹ *
        e6DiagramMap L)⁻¹ =
      canonicalRep (coxeterSystem .E6) L u := by
  set n0 : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L twE6W0 with hn0
  set P : ModGL .E6 L := e6DiagramMap L with hP
  have hPu : P * canonicalRep (coxeterSystem .E6) L u * P⁻¹ =
      canonicalRep (coxeterSystem .E6) L (TwistedDiag.delta u) := by
    have h : twistHom TwistTag.E6 L (RingHom.id L) (canonicalRep (coxeterSystem .E6) L u) =
        canonicalRep (coxeterSystem .E6) L (TwistedDiag.delta u) := by
      exact twistHom_canonicalRep (t := TwistTag.E6) (K := L) (σ := RingHom.id L) u
    have h' : P * canonicalRep (coxeterSystem .E6) L u * P⁻¹ =
        twistHom TwistTag.E6 L (RingHom.id L) (canonicalRep (coxeterSystem .E6) L u) := by
      rw [← conj_diagramMap_eq_twistHom, hP]
      rfl
    rw [h', h]
  have hcancel : n0⁻¹ * canonicalRep (coxeterSystem .E6) L (TwistedDiag.delta u) * n0 =
      canonicalRep (coxeterSystem .E6) L u := by
    have hn0inv : canonicalRep (coxeterSystem .E6) L twE6W0⁻¹ = n0⁻¹ := by
      have h := CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo
        (R := L) twE6W0 twE6W0⁻¹
      rw [mul_inv_cancel, canonicalRep_one] at h
      exact eq_inv_of_mul_eq_one_right h.symm
    have hmul : canonicalRep (coxeterSystem .E6) L (twE6W0⁻¹ * TwistedDiag.delta u) =
        n0⁻¹ * canonicalRep (coxeterSystem .E6) L (TwistedDiag.delta u) := by
      rw [CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, hn0inv]
    have hmul2 : canonicalRep (coxeterSystem .E6) L
        ((twE6W0⁻¹ * TwistedDiag.delta u) * twE6W0) =
        (n0⁻¹ * canonicalRep (coxeterSystem .E6) L (TwistedDiag.delta u)) * n0 := by
      rw [CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo, hmul, hn0]
    rw [← hmul2]
    have hw : (twE6W0⁻¹ * TwistedDiag.delta u) * twE6W0 = u := by
      simpa [TwistedDiag.twE6W0_inv] using TwistedDiag.w0_mul_delta_mul_w0_inv u
    rw [hw]
  calc (n0⁻¹ * P) * canonicalRep (coxeterSystem .E6) L u * (n0⁻¹ * P)⁻¹
      = n0⁻¹ * (P * canonicalRep (coxeterSystem .E6) L u * P⁻¹) * n0 := by group
    _ = n0⁻¹ * canonicalRep (coxeterSystem .E6) L (TwistedDiag.delta u) * n0 := by rw [hPu]
    _ = canonicalRep (coxeterSystem .E6) L u := hcancel

theorem rootDiagUnit_mem_adjointGroup_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK3 : 3 ∣ Nat.card K + 1) (a : Fin (Tag.E6.rank) → Kˣ) :
    rootDiagUnit .E6 a ∈ adjointGroup .E6 K := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have h3q : ¬ 3 ∣ Nat.card K - 1 := by
    intro h
    have hsub : 3 ∣ (Nat.card K + 1) - (Nat.card K - 1) :=
      Nat.dvd_sub hK3 h
    have h2 : 3 ∣ 2 := by
      rwa [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] at hsub
    norm_num at h2
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3q).symm
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_adjointGroup_of_roots
    (τ := .E6) (L := K) ?_
  intro j
  have hbij : Function.Bijective (fun u : Kˣ => u ^ 3) := hcop.pow_left_bijective
  obtain ⟨u, hu⟩ := hbij.surjective (a j)
  refine ⟨u, ?_⟩
  rw [det_cartan_E6]
  exact hu

theorem exists_conj_eq_of_toral_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK3 : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian 3 E)
    (hT : ExcFramesHalf.IsToralSubgroup .E6 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E6 K).subtype)))
    (β : MulAut (adjointGroup .E6 K)) :
    ∃ r : adjointGroup .E6 K, ∀ x ∈ E, β x = r * x * r⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have hq3 : 3 ∣ 2 ^ (f : ℕ) + 1 := by rwa [hK] at hK3
  let F : ModGL .E6 (AlgebraicClosure K) →* ModGL .E6 (AlgebraicClosure K) :=
    entrywiseFrobGL .E6 (AlgebraicClosure K) 2 (f : ℕ)
  have hFbc : ∀ y : ModGL .E6 (AlgebraicClosure K),
      F y = baseChangeGL (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ)) y := fun y => rfl
  have hbcinj : Function.Injective
      (baseChangeGL (τ := .E6) (algebraMap K (AlgebraicClosure K))) :=
    baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  have hcomp : (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ)).comp
      (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
    apply RingHom.ext
    intro t
    change iterateFrobenius (AlgebraicClosure K) 2 f (algebraMap K (AlgebraicClosure K) t) =
      algebraMap K (AlgebraicClosure K) t
    rw [iterateFrobenius_def, ← map_pow, ← hKf]
    exact congrArg (algebraMap K (AlgebraicClosure K)) (FiniteField.pow_card t)
  have hFix : ∀ y : ModGL .E6 K,
      F (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
    intro y
    rw [hFbc, baseChangeGL_baseChangeGL, hcomp]
  obtain ⟨g, hg, hgT⟩ := hT
  have hmemT : ∀ x : E, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .E6 K) : ModGL .E6 K) * g ∈ torusGroup .E6 (AlgebraicClosure K) :=
    fun x => hgT _ (Subgroup.mem_map_of_mem _ x.2)
  choose a ha using fun x : E =>
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup (hmemT x)
  have hgx : ∀ x : E, g * rootDiagUnit .E6 (a x) * g⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E6 K) : ModGL .E6 K) := by
    intro x
    rw [ha x]
    group
  have hexp : ∀ (x : E) j, a x j ^ 3 = 1 := by
    intro x
    have hpow : rootDiagUnit .E6 (a x ^ 3) = rootDiagUnit .E6 1 := by
      rw [show rootDiagUnit .E6 (a x ^ 3) = rootDiagUnit .E6 (a x) ^ 3 from
        (rootDiagUnitHom .E6 (AlgebraicClosure K)).map_pow (a x) 3, ha x, rootDiagUnit_one,
        show g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E6 K) : ModGL .E6 K) * g =
          (MulAut.conj g⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E6 K) : ModGL .E6 K)) by
          simp only [MulAut.conj_apply, inv_inv],
        ← map_pow, ← map_pow, ← Subgroup.coe_pow, hE.2 x x.2, OneMemClass.coe_one, map_one,
        map_one]
    exact fun j => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective hpow) j
  have hFixD : ∀ x : E, F (g * rootDiagUnit .E6 (a x) * g⁻¹) =
      g * rootDiagUnit .E6 (a x) * g⁻¹ := fun x => by
    rw [hgx x]
    exact hFix _
  have hFroot : ∀ x : E, F (rootDiagUnit .E6 (a x)) =
      rootDiagUnit .E6 ((a x) ^ (2 ^ (f : ℕ))) := by
    intro x
    rw [show F (rootDiagUnit .E6 (a x)) = rootDiagUnit .E6
        (fun i => Units.map (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ)).toMonoidHom
          (a x i)) from
      CFSG.LieType.AlgebraicGroups.entrywiseFrobGL_rootDiagUnit_eq_map
        (τ := .E6) (k := AlgebraicClosure K) 2 (f : ℕ) (a x)]
    rfl
  have hpow_inv : ∀ x : E, (a x) ^ (2 ^ (f : ℕ)) = (a x)⁻¹ := by
    intro x
    funext j
    obtain ⟨k, hk⟩ := hq3
    apply eq_inv_of_mul_eq_one_left
    calc a x j ^ (2 ^ (f : ℕ)) * a x j = a x j ^ (2 ^ (f : ℕ) + 1) := (pow_succ _ _).symm
      _ = a x j ^ (3 * k) := by rw [hk]
      _ = (a x j ^ 3) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hexp x j, one_pow]
  have hFD : ∀ x : E, F (rootDiagUnit .E6 (a x)) = (rootDiagUnit .E6 (a x))⁻¹ := by
    intro x
    rw [hFroot x, hpow_inv x]
    exact (rootDiagUnit_inv (a x)).symm
  have hyG : g⁻¹ * F g ∈ adjointGroup .E6 (AlgebraicClosure K) :=
    mul_mem (inv_mem hg) (entrywiseFrobGL_mem 2 (f : ℕ) hg)
  have hconj_y : ∀ x : E, (g⁻¹ * F g) * rootDiagUnit .E6 ((a x)⁻¹) * (g⁻¹ * F g)⁻¹ =
      rootDiagUnit .E6 (a x) := by
    intro x
    have h := hFixD x
    rw [map_mul, map_mul, map_inv, hFD x] at h
    calc (g⁻¹ * F g) * rootDiagUnit .E6 ((a x)⁻¹) * (g⁻¹ * F g)⁻¹
        = g⁻¹ * (F g * (rootDiagUnit .E6 (a x))⁻¹ * (F g)⁻¹) * g := by
            rw [rootDiagUnit_inv]; group
      _ = g⁻¹ * (g * rootDiagUnit .E6 (a x) * g⁻¹) * g := by rw [h]
      _ = rootDiagUnit .E6 (a x) := by group
  obtain ⟨w, hw⟩ := exists_weyl_of_inverted_family (L := AlgebraicClosure K) a
    (fun x j => hexp x j) (q := 2 ^ (f : ℕ)) hq3 hyG hconj_y
  have hcop : Nat.Coprime 3 (2 ^ (f : ℕ)) := Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨v, -, g₁, hg₁, hFg₁, hg₁x⟩ :=
    CFSG.StandardType.ExcElemToral.exists_lang_conj_of_family_twisted_stab
      (τ := .E6) (L := AlgebraicClosure K) 2 hf a hcop (fun x j => hexp x j) hw hg
      (fun x => by rw [hgx x]; exact hFix _)
  obtain ⟨n, hn⟩ : ∃ n : ModGL .E6 (AlgebraicClosure K),
      n = canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) v *
        canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) w := ⟨_, rfl⟩
  rw [← hn] at hFg₁
  have hg₁φ : ∀ x : E, g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E6 K) : ModGL .E6 K) :=
    fun x => (hg₁x x).trans (hgx x)
  have hnG : n ∈ adjointGroup .E6 (AlgebraicClosure K) := by
    rw [hn]
    exact mul_mem (canonicalRep_mem_adjointGroup _ _ _) (canonicalRep_mem_adjointGroup _ _ _)
  have hFn : F n = n := by
    rw [hFbc n, hn, map_mul, baseChangeGL_canonicalRep, baseChangeGL_canonicalRep]
  have hFixg₁ : ∀ x : E, F (g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹) =
      g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹ := by
    intro x
    rw [hg₁φ x]
    exact hFix _
  have hconj_n : ∀ x : E, n * rootDiagUnit .E6 ((a x)⁻¹) * n⁻¹ =
      rootDiagUnit .E6 (a x) := by
    intro x
    have h := hFixg₁ x
    rw [map_mul, map_mul, map_inv, hFg₁, hFD x] at h
    calc n * rootDiagUnit .E6 ((a x)⁻¹) * n⁻¹
        = g₁⁻¹ * ((g₁ * n) * (rootDiagUnit .E6 (a x))⁻¹ * (g₁ * n)⁻¹) * g₁ := by
            rw [rootDiagUnit_inv]; group
      _ = g₁⁻¹ * (g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹) * g₁ := by rw [h]
      _ = rootDiagUnit .E6 (a x) := by group
  have hnD : ∀ x : E, n * rootDiagUnit .E6 (a x) * n⁻¹ =
      (rootDiagUnit .E6 (a x))⁻¹ := by
    intro x
    have h := hconj_n x
    have h2 : (n * rootDiagUnit .E6 ((a x)⁻¹) * n⁻¹)⁻¹ =
        (rootDiagUnit .E6 (a x))⁻¹ := congrArg Inv.inv h
    simpa only [mul_inv_rev, inv_inv, rootDiagUnit_inv, mul_assoc] using h2
  have hFy₁ : F (g₁ * n * g₁⁻¹) = g₁ * n * g₁⁻¹ := by
    rw [map_mul, map_mul, map_inv, hFg₁, hFn]
    group
  obtain ⟨r₁, hr₁, hr₁y⟩ := exists_rational_of_frob_fixed_E6 hK3 hf hK
    (y := g₁ * n * g₁⁻¹) (mul_mem (mul_mem hg₁ hnG) (inv_mem hg₁)) hFy₁
  have hinv : ∀ x : E, r₁ * ((x : adjointGroup .E6 K) : ModGL .E6 K) * r₁⁻¹ =
      ((x : adjointGroup .E6 K) : ModGL .E6 K)⁻¹ := by
    intro x
    apply hbcinj
    rw [map_mul, map_mul, map_inv, map_inv, hr₁y, ← hg₁φ x]
    calc (g₁ * n * g₁⁻¹) * (g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹) * (g₁ * n * g₁⁻¹)⁻¹
        = g₁ * (n * rootDiagUnit .E6 (a x) * n⁻¹) * g₁⁻¹ := by group
      _ = (g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹)⁻¹ := by rw [hnD x]; group
  have hfield : ∀ δ : K ≃+* K, ∃ r ∈ adjointGroup .E6 K, ∃ m : ℕ, (m = 1 ∨ m = 2) ∧
      ∀ x : E, Units.map (entrywiseHom δ.toRingHom)
          ((x : adjointGroup .E6 K) : ModGL .E6 K) =
        (r : ModGL .E6 K) * (((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m) *
          (r : ModGL .E6 K)⁻¹ := by
    intro δ
    obtain ⟨δ', hδι⟩ : ∃ δ' : AlgebraicClosure K ≃+* AlgebraicClosure K, ∀ c : K,
        δ' (algebraMap K (AlgebraicClosure K) c) = algebraMap K (AlgebraicClosure K) (δ c) :=
      ⟨IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) δ,
        IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) δ⟩
    have hDφ : ∀ y : ModGL .E6 K,
        baseChangeGL δ'.toRingHom (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (baseChangeGL δ.toRingHom y) := by
      intro y
      have hc : δ'.toRingHom.comp (algebraMap K (AlgebraicClosure K)) =
          (algebraMap K (AlgebraicClosure K)).comp δ.toRingHom := RingHom.ext fun c => hδι c
      rw [baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc]
    have hDF : ∀ y : ModGL .E6 (AlgebraicClosure K),
        baseChangeGL δ'.toRingHom (F y) = F (baseChangeGL δ'.toRingHom y) := by
      intro y
      have hc : δ'.toRingHom.comp (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ)) =
          (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ)).comp δ'.toRingHom :=
        RingHom.ext fun c => by simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
      rw [hFbc, hFbc, baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc]
    have hDn : baseChangeGL δ'.toRingHom n = n := by
      rw [hn, map_mul, baseChangeGL_canonicalRep, baseChangeGL_canonicalRep]
    obtain ⟨ζ, hζ⟩ := CFSG.StandardType.ExcToralInner.exists_orderOf_eq_three K
    obtain ⟨m, hm12, hm⟩ :=
      CFSG.StandardType.ExcToralInner.exists_units_map_eq_pow_three hζ δ'.toRingHom
    have hDd : ∀ x : E, baseChangeGL δ'.toRingHom (rootDiagUnit .E6 (a x)) =
        rootDiagUnit .E6 (a x) ^ m := by
      intro x
      rw [baseChangeGL_rootDiagUnit, show rootDiagUnit .E6 (a x) ^ m =
        rootDiagUnit .E6 (a x ^ m) from
          ((rootDiagUnitHom .E6 (AlgebraicClosure K)).map_pow (a x) m).symm]
      congr 1
      funext j
      exact hm (a x j) (hexp x j)
    have hy₂ : baseChangeGL δ'.toRingHom g₁ * g₁⁻¹ ∈
        adjointGroup .E6 (AlgebraicClosure K) :=
      mul_mem (baseChangeGL_mem_adjointGroup _ hg₁) (inv_mem hg₁)
    have hFy₂ : F (baseChangeGL δ'.toRingHom g₁ * g₁⁻¹) =
        baseChangeGL δ'.toRingHom g₁ * g₁⁻¹ := by
      rw [map_mul, map_inv, ← hDF, hFg₁, map_mul, hDn]
      group
    obtain ⟨r₂, hr₂, hr₂y⟩ := exists_rational_of_frob_fixed_E6 hK3 hf hK hy₂ hFy₂
    have hδx : ∀ x : E, Units.map (entrywiseHom δ.toRingHom)
        ((x : adjointGroup .E6 K) : ModGL .E6 K) =
          (r₂ : ModGL .E6 K) * (((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m) *
            (r₂ : ModGL .E6 K)⁻¹ := by
      intro x
      rw [units_map_entrywiseHom_eq_baseChangeGL]
      apply hbcinj
      rw [← hDφ, map_mul, map_mul, map_inv, map_pow, hr₂y, ← hg₁φ x, map_mul, map_mul, map_inv,
        hDd x, conj_pow]
      group
    exact ⟨r₂, hr₂, m, hm12, hδx⟩
  obtain ⟨g', a', δ, ε, hβx⟩ :=
    (CFSG.LieType.Chevalley.ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 β
  have hda' : rootDiagUnit .E6 a' ∈ adjointGroup .E6 K :=
    rootDiagUnit_mem_adjointGroup_E6 hK3 a'
  obtain ⟨r₂, hr₂, m, hm12, hδx⟩ := hfield δ
  let P : ModGL .E6 (AlgebraicClosure K) := e6DiagramMap (AlgebraicClosure K)
  let n0 : ModGL .E6 (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) twE6W0
  let Ψ : ModGL .E6 (AlgebraicClosure K) := n0⁻¹ * P
  have hΨd : ∀ b : Fin (Tag.E6.rank) → (AlgebraicClosure K)ˣ, (∀ i, b i ^ 3 = 1) →
      Ψ * rootDiagUnit .E6 b * Ψ⁻¹ = (rootDiagUnit .E6 b)⁻¹ := by
    intro b hb
    exact psi_conj_rootDiagUnit b hb
  have hΨu : ∀ u : WeylGroup .E6,
      Ψ * canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) u * Ψ⁻¹ =
        canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) u := by
    intro u
    exact psi_commute_canonicalRep u
  have hn0G : n0 ∈ adjointGroup .E6 (AlgebraicClosure K) :=
    canonicalRep_mem_adjointGroup _ _ _
  have hΨnorm : ∀ y ∈ adjointGroup .E6 (AlgebraicClosure K),
      Ψ * y * Ψ⁻¹ ∈ adjointGroup .E6 (AlgebraicClosure K) := by
    intro y hy
    have hP : P * y * P⁻¹ ∈ adjointGroup .E6 (AlgebraicClosure K) := by
      have h := twistHom_mem_adjointGroup (t := TwistTag.E6) (K := AlgebraicClosure K)
        (σ := RingHom.id (AlgebraicClosure K)) (g := y) hy
      have h' : twistHom TwistTag.E6 (AlgebraicClosure K)
          (RingHom.id (AlgebraicClosure K)) y = P * y * P⁻¹ := by
        rw [← conj_diagramMap_eq_twistHom]
        rfl
      rwa [h'] at h
    have hEq : Ψ * y * Ψ⁻¹ = n0⁻¹ * (P * y * P⁻¹) * n0 := by dsimp [Ψ]; group
    rw [hEq]
    exact mul_mem (mul_mem (inv_mem hn0G) hP) hn0G
  have hPbcK : e6DiagramMap (AlgebraicClosure K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (e6DiagramMap K) := by
    dsimp [e6DiagramMap]
    exact (baseChangeGL_diagramMap (f := algebraMap K (AlgebraicClosure K))
      (t := TwistTag.E6)).symm
  have hFP0 : F (e6DiagramMap (AlgebraicClosure K)) = e6DiagramMap (AlgebraicClosure K) := by
    rw [hFbc]
    calc baseChangeGL (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ))
          (e6DiagramMap (AlgebraicClosure K))
        = baseChangeGL (iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ))
            (baseChangeGL (algebraMap K (AlgebraicClosure K)) (e6DiagramMap K)) := by
            rw [hPbcK]
      _ = baseChangeGL ((iterateFrobenius (AlgebraicClosure K) 2 (f : ℕ)).comp
            (algebraMap K (AlgebraicClosure K))) (e6DiagramMap K) := by
            rw [baseChangeGL_baseChangeGL]
      _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (e6DiagramMap K) := by rw [hcomp]
      _ = e6DiagramMap (AlgebraicClosure K) := hPbcK.symm
  have hFP : F P = P := hFP0
  have hFn0 : F n0 = n0 := by
    rw [hFbc]
    exact baseChangeGL_canonicalRep _ twE6W0
  have hFΨ : F Ψ = Ψ := by
    dsimp [Ψ]
    rw [map_mul, map_inv, hFn0, hFP]
  let r₃ : ModGL .E6 (AlgebraicClosure K) := Ψ * g₁ * Ψ⁻¹ * n * g₁⁻¹
  have hr₃G : r₃ ∈ adjointGroup .E6 (AlgebraicClosure K) := by
    dsimp [r₃]
    exact mul_mem (mul_mem (hΨnorm g₁ hg₁) hnG) (inv_mem hg₁)
  have hΨn : Ψ * n * Ψ⁻¹ = n := by
    rw [hn]
    calc Ψ * (canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) v *
          canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) w) * Ψ⁻¹
        = (Ψ * canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) v * Ψ⁻¹) *
            (Ψ * canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) w * Ψ⁻¹) := by group
      _ = canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) v *
            canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) w := by rw [hΨu v, hΨu w]
  have hcomm : n * Ψ⁻¹ = Ψ⁻¹ * n := by
    have h1 : Ψ * n = n * Ψ := by
      calc Ψ * n = (Ψ * n * Ψ⁻¹) * Ψ := by group
        _ = n * Ψ := by rw [hΨn]
    calc n * Ψ⁻¹ = Ψ⁻¹ * (Ψ * n) * Ψ⁻¹ := by group
      _ = Ψ⁻¹ * (n * Ψ) * Ψ⁻¹ := by rw [h1]
      _ = Ψ⁻¹ * n := by group
  have hFr₃ : F r₃ = r₃ := by
    calc F r₃ = F (Ψ * g₁ * Ψ⁻¹ * n * g₁⁻¹) := rfl
      _ = F Ψ * F g₁ * (F Ψ)⁻¹ * F n * (F g₁)⁻¹ := by simp only [map_mul, map_inv]
      _ = Ψ * (g₁ * n) * Ψ⁻¹ * n * (g₁ * n)⁻¹ := by rw [hFΨ, hFg₁, hFn]
      _ = Ψ * g₁ * Ψ⁻¹ * n * g₁⁻¹ := by
            calc Ψ * (g₁ * n) * Ψ⁻¹ * n * (g₁ * n)⁻¹
                = (Ψ * g₁) * (n * Ψ⁻¹) * g₁⁻¹ := by group
              _ = (Ψ * g₁) * (Ψ⁻¹ * n) * g₁⁻¹ := by rw [hcomm]
              _ = Ψ * g₁ * Ψ⁻¹ * n * g₁⁻¹ := by group
  obtain ⟨r₃', hr₃', hr₃'y⟩ := exists_rational_of_frob_fixed_E6 hK3 hf hK hr₃G hFr₃
  let n0K : ModGL .E6 K := canonicalRep (coxeterSystem .E6) K twE6W0
  have hn0KG : n0K ∈ adjointGroup .E6 K := canonicalRep_mem_adjointGroup _ _ _
  let s : ModGL .E6 K := n0K * (r₃' : ModGL .E6 K)
  have hs : s ∈ adjointGroup .E6 K := mul_mem hn0KG hr₃'
  have hsbc : baseChangeGL (algebraMap K (AlgebraicClosure K)) s = n0 * r₃ := by
    dsimp [s, n0K]
    rw [map_mul, baseChangeGL_canonicalRep, hr₃'y]
  have hPconj : ∀ x : E, e6DiagramMap K * ((x : adjointGroup .E6 K) : ModGL .E6 K) *
      (e6DiagramMap K)⁻¹ =
        s * ((x : adjointGroup .E6 K) : ModGL .E6 K) * s⁻¹ := by
    intro x
    have hPKbar : P * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .E6 K) : ModGL .E6 K) * P⁻¹ =
          (n0 * r₃) * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E6 K) : ModGL .E6 K) * (n0 * r₃)⁻¹ := by
      have hΨD : Ψ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E6 K) : ModGL .E6 K) * Ψ⁻¹ =
          r₃ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E6 K) : ModGL .E6 K) * r₃⁻¹ := by
        rw [← hg₁φ x]
        calc Ψ * (g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹) * Ψ⁻¹
            = (Ψ * g₁ * Ψ⁻¹) * (Ψ * rootDiagUnit .E6 (a x) * Ψ⁻¹) *
                (Ψ * g₁ * Ψ⁻¹)⁻¹ := by group
          _ = (Ψ * g₁ * Ψ⁻¹) * (rootDiagUnit .E6 (a x))⁻¹ * (Ψ * g₁ * Ψ⁻¹)⁻¹ := by
                rw [hΨd (a x) (fun j => hexp x j)]
          _ = (Ψ * g₁ * Ψ⁻¹) * (n * rootDiagUnit .E6 (a x) * n⁻¹) *
                (Ψ * g₁ * Ψ⁻¹)⁻¹ := by rw [← hnD x]
          _ = r₃ * (g₁ * rootDiagUnit .E6 (a x) * g₁⁻¹) * r₃⁻¹ := by dsimp [r₃]; group
      have hP_eq : P = n0 * Ψ := by dsimp [Ψ]; group
      calc P * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup .E6 K) : ModGL .E6 K) * P⁻¹
          = (n0 * Ψ) * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((x : adjointGroup .E6 K) : ModGL .E6 K) * (n0 * Ψ)⁻¹ := by rw [hP_eq]
        _ = n0 * (Ψ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((x : adjointGroup .E6 K) : ModGL .E6 K) * Ψ⁻¹) * n0⁻¹ := by group
        _ = n0 * (r₃ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((x : adjointGroup .E6 K) : ModGL .E6 K) * r₃⁻¹) * n0⁻¹ := by rw [hΨD]
        _ = (n0 * r₃) * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((x : adjointGroup .E6 K) : ModGL .E6 K) * (n0 * r₃)⁻¹ := by group
    apply hbcinj
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    have hPbc : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e6DiagramMap K) = P := by
      dsimp [P, e6DiagramMap]
      exact baseChangeGL_diagramMap (f := algebraMap K (AlgebraicClosure K)) (t := TwistTag.E6)
    rw [hPbc, hsbc]
    exact hPKbar
  have hQx : ∀ x : E, e6DiagramMap K ^ (ε : ℕ) *
      ((x : adjointGroup .E6 K) : ModGL .E6 K) * (e6DiagramMap K ^ (ε : ℕ))⁻¹ =
        s ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) * (s ^ (ε : ℕ))⁻¹ := by
    intro x
    fin_cases ε
    · simp
    · simpa using hPconj x
  have hPconjPow : ∀ x : E, e6DiagramMap K ^ (ε : ℕ) *
      ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m * (e6DiagramMap K ^ (ε : ℕ))⁻¹ =
        s ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m * (s ^ (ε : ℕ))⁻¹ := by
    intro x
    calc e6DiagramMap K ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m *
          (e6DiagramMap K ^ (ε : ℕ))⁻¹
        = (e6DiagramMap K ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) *
            (e6DiagramMap K ^ (ε : ℕ))⁻¹) ^ m := (conj_pow).symm
      _ = (s ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) * (s ^ (ε : ℕ))⁻¹) ^ m := by
            rw [hQx x]
      _ = s ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m * (s ^ (ε : ℕ))⁻¹ :=
            conj_pow
  have htP : e6DiagramMap K * (r₂ : ModGL .E6 K) * (e6DiagramMap K)⁻¹ ∈
      adjointGroup .E6 K := by
    have h := twistHom_mem_adjointGroup (t := TwistTag.E6) (K := K)
      (σ := RingHom.id K) (g := (r₂ : ModGL .E6 K)) hr₂
    have h' : twistHom TwistTag.E6 K (RingHom.id K) (r₂ : ModGL .E6 K) =
        e6DiagramMap K * (r₂ : ModGL .E6 K) * (e6DiagramMap K)⁻¹ := by
      rw [← conj_diagramMap_eq_twistHom]
      rfl
    rwa [h'] at h
  let tε : ModGL .E6 K := e6DiagramMap K ^ (ε : ℕ) * (r₂ : ModGL .E6 K) *
    (e6DiagramMap K ^ (ε : ℕ))⁻¹
  have htε : tε ∈ adjointGroup .E6 K := by
    dsimp [tε]
    fin_cases ε
    · simpa using hr₂
    · simpa using htP
  have hQε : exactQ .E6 K ε = e6DiagramMap K ^ (ε : ℕ) := by
    fin_cases ε <;> rfl
  have hβx' : ∀ x : E, (β x : ModGL .E6 K) =
      (g' : ModGL .E6 K) * rootDiagUnit .E6 a' * e6DiagramMap K ^ (ε : ℕ) *
        Units.map (entrywiseHom δ.toRingHom) ((x : adjointGroup .E6 K) : ModGL .E6 K) *
        (e6DiagramMap K ^ (ε : ℕ))⁻¹ * (rootDiagUnit .E6 a')⁻¹ * (g' : ModGL .E6 K)⁻¹ := by
    intro x
    have h := hβx (x : adjointGroup .E6 K)
    rwa [hQε] at h
  let A : ModGL .E6 K := (g' : ModGL .E6 K) * rootDiagUnit .E6 a' * tε * s ^ (ε : ℕ)
  have hA : A ∈ adjointGroup .E6 K := by
    dsimp [A]
    exact mul_mem (mul_mem (mul_mem g'.2 hda') htε) (pow_mem hs _)
  have hβK : ∀ x : E, (β x : ModGL .E6 K) =
      A * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m * A⁻¹ := by
    intro x
    have hQxpow := hPconjPow x
    calc (β x : ModGL .E6 K)
        = (g' : ModGL .E6 K) * rootDiagUnit .E6 a' * e6DiagramMap K ^ (ε : ℕ) *
            ((r₂ : ModGL .E6 K) * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m *
              (r₂ : ModGL .E6 K)⁻¹) *
            (e6DiagramMap K ^ (ε : ℕ))⁻¹ * (rootDiagUnit .E6 a')⁻¹ * (g' : ModGL .E6 K)⁻¹ := by
            rw [hβx' x, hδx x]
      _ = (g' : ModGL .E6 K) * rootDiagUnit .E6 a' *
            (e6DiagramMap K ^ (ε : ℕ) * (r₂ : ModGL .E6 K) *
              (e6DiagramMap K ^ (ε : ℕ))⁻¹) *
            (e6DiagramMap K ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m *
              (e6DiagramMap K ^ (ε : ℕ))⁻¹) *
            (e6DiagramMap K ^ (ε : ℕ) * (r₂ : ModGL .E6 K) *
              (e6DiagramMap K ^ (ε : ℕ))⁻¹)⁻¹ *
            (rootDiagUnit .E6 a')⁻¹ * (g' : ModGL .E6 K)⁻¹ := by group
      _ = (g' : ModGL .E6 K) * rootDiagUnit .E6 a' * tε *
            (s ^ (ε : ℕ) * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m * (s ^ (ε : ℕ))⁻¹) *
            tε⁻¹ * (rootDiagUnit .E6 a')⁻¹ * (g' : ModGL .E6 K)⁻¹ := by
            rw [hQxpow]
      _ = A * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ m * A⁻¹ := by dsimp [A, tε]; group
  rcases hm12 with hm | hm
  · have hβK1 : ∀ x : E, (β x : ModGL .E6 K) =
        A * ((x : adjointGroup .E6 K) : ModGL .E6 K) * A⁻¹ := by
      intro x
      simpa [hm] using hβK x
    refine ⟨⟨A, hA⟩, fun x hx => ?_⟩
    apply Subtype.ext
    rw [hβK1 ⟨x, hx⟩]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  · have hβK2 : ∀ x : E, (β x : ModGL .E6 K) =
        A * ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ 2 * A⁻¹ := by
      intro x
      simpa [hm] using hβK x
    refine ⟨⟨A * r₁, mul_mem hA hr₁⟩, fun x hx => ?_⟩
    apply Subtype.ext
    rw [hβK2 ⟨x, hx⟩]
    have hx3 : ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hE.2 x hx, OneMemClass.coe_one]
    have hx2 : ((x : adjointGroup .E6 K) : ModGL .E6 K) ^ 2 =
        ((x : adjointGroup .E6 K) : ModGL .E6 K)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx3])
    rw [hx2, ← hinv ⟨x, hx⟩]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end CFSG.StandardType.E6ToralInner
