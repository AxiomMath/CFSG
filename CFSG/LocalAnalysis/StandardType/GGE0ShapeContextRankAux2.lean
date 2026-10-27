module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutEsix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem exists_units_map_eq_of_perm_alg {ℓ f : ℕ} {K : Type} [Field K] [Finite K]
    {Ω : Type} [Field Ω] [Algebra K Ω]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {b : Fin TwistTag.E6.tag.rank → Ωˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map Fr.toMonoidHom (b i)) :
    ∃ l : Fin TwistTag.E6.tag.rank → Kˣ,
      ∀ i, Units.map (algebraMap K Ω).toMonoidHom (l i) = b i := by
  have hperm2 : TwistTag.E6.perm ^ 2 = 1 := TwistTag.perm_pow_order TwistTag.E6
  have hperm2_apply : ∀ i : Fin TwistTag.E6.tag.rank,
      TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
    intro i
    have h2 : (TwistTag.E6.perm * TwistTag.E6.perm) i = i := by
      rw [← pow_two, hperm2]
      rfl
    rwa [Equiv.Perm.mul_apply] at h2
  have hFr2 : ∀ c : Ω, Fr (Fr c) = c ^ (ℓ ^ f * ℓ ^ f) := fun c => by
    rw [hFr, hFr, ← pow_mul]
  have hself : ∀ i, (b i : Ω) = Fr (Fr (b i)) := by
    intro i
    have e1 : (b (TwistTag.E6.perm i) : Ω) = Fr (b i : Ω) := by
      simpa using congrArg Units.val (hb i)
    have e2 : (b i : Ω) = Fr (b (TwistTag.E6.perm i) : Ω) := by
      have h := hb (TwistTag.E6.perm i)
      rw [hperm2_apply i] at h
      simpa using congrArg Units.val h
    calc (b i : Ω) = Fr (b (TwistTag.E6.perm i) : Ω) := e2
      _ = Fr (Fr (b i : Ω)) := congrArg Fr e1
  have hpow : ∀ i, (b i : Ω) ^ Nat.card K = (b i : Ω) := by
    intro i
    have hb' : (b i : Ω) = (b i : Ω) ^ (ℓ ^ f * ℓ ^ f) := by
      calc (b i : Ω) = Fr (Fr (b i)) := hself i
        _ = (b i : Ω) ^ (ℓ ^ f * ℓ ^ f) := hFr2 (b i)
    rw [hK, show (ℓ ^ f) ^ 2 = ℓ ^ f * ℓ ^ f by ring]
    exact hb'.symm
  choose c hc using fun i =>
    mem_range_algebraMap_of_pow_card_eq (k := K) (L := Ω) (hpow i)
  have hcne : ∀ i, c i ≠ 0 := fun i h0 => (b i).ne_zero (by rw [← hc i, h0, map_zero])
  refine ⟨fun i => Units.mk0 (c i) (hcne i), fun i => ?_⟩
  ext
  simpa using hc i

private theorem graphFixedTorus_le_map_twistedE6DiagGL_alg
    {ℓ f : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Ω : Type} [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    graphFixedTorus TwistTag.E6 Ω Fr ≤
      (twistedE6DiagGL K σ).map (baseChangeGL (algebraMap K Ω)) := by
  intro t ht
  obtain ⟨htT, htF⟩ := Subgroup.mem_inf.1 ht
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (K := Ω) htT
  have htF' : rootDiagUnit TwistTag.E6.tag b ∈
      twistedFixedGroup TwistTag.E6 Ω Fr := by rwa [← hb]
  have htw : twistHom TwistTag.E6 Ω Fr
      (rootDiagUnit TwistTag.E6.tag b) = rootDiagUnit TwistTag.E6.tag b :=
    ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := Ω)
      (σ := Fr)).1 htF').2
  have hbcompat : ∀ i, b (TwistTag.E6.perm i) = Units.map Fr.toMonoidHom (b i) :=
    fun i => compat_of_twistHom_rootDiagUnit htw i
  obtain ⟨l, hl⟩ := exists_units_map_eq_of_perm_alg hK Fr hFr hbcompat
  have hl_val : ∀ i, algebraMap K Ω (l i : K) = (b i : Ω) :=
    fun i => congrArg Units.val (hl i)
  have hcomp : ∀ c : K, Fr (algebraMap K Ω c) = algebraMap K Ω (σ c) := fun c => by
    rw [hFr, hσ, map_pow]
  have hlcompat : ∀ i, l (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (l i) := by
    intro i
    apply Units.ext
    apply (algebraMap K Ω).injective
    calc (algebraMap K Ω) (l (TwistTag.E6.perm i) : K)
        = (b (TwistTag.E6.perm i) : Ω) := hl_val (TwistTag.E6.perm i)
      _ = Fr (b i : Ω) := congrArg Units.val (hbcompat i)
      _ = Fr ((algebraMap K Ω) (l i : K)) := by rw [hl_val i]
      _ = (algebraMap K Ω) (σ (l i : K)) := hcomp (l i : K)
  obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom) hlcompat
  have hmem : rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ∈
      twistedE6DiagGL K σ :=
    ⟨u, rfl⟩
  have hbase : baseChangeGL (algebraMap K Ω)
      (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) =
      rootDiagUnit TwistTag.E6.tag b := by
    rw [baseChangeGL_rootDiagUnit, hu]
    exact congrArg (rootDiagUnit TwistTag.E6.tag) (funext hl)
  rw [hb]
  exact ⟨_, hmem, hbase⟩

theorem twistedFixedGroup_le_map_inndiag_alg
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    twistedFixedGroup TwistTag.E6 Ω Fr ≤
      (twistedE6InndiagGL K σ).map (baseChangeGL (algebraMap K Ω)) := by
  obtain ⟨-, hmul, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      hℓ hf K hK σ.toRingHom hσ Ω Fr hFr
  have hT_le : graphFixedTorus TwistTag.E6 Ω Fr ≤
      (twistedE6InndiagGL K σ).map (baseChangeGL (algebraMap K Ω)) := by
    change graphFixedTorus TwistTag.E6 Ω Fr ≤
      (twistedE6RootGroup K σ ⊔ twistedE6DiagGL K σ).map (baseChangeGL (algebraMap K Ω))
    exact (graphFixedTorus_le_map_twistedE6DiagGL_alg hK σ hσ Fr hFr).trans
      (Subgroup.map_mono le_sup_right)
  have hC_le : ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K Ω))) ≤
      (twistedE6InndiagGL K σ).map (baseChangeGL (algebraMap K Ω)) := by
    change ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K Ω))) ≤
      (twistedE6RootGroup K σ ⊔ twistedE6DiagGL K σ).map (baseChangeGL (algebraMap K Ω))
    exact Subgroup.map_mono le_sup_left
  have hle : twistedFixedGroup TwistTag.E6 Ω Fr ≤
      graphFixedTorus TwistTag.E6 Ω Fr ⊔
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
          (baseChangeGL (algebraMap K Ω)) := by
    intro y hy
    have hy' : y ∈ (twistedFixedGroup TwistTag.E6 Ω Fr : Set _) := hy
    rw [hmul] at hy'
    obtain ⟨t, ht, c, hc, rfl⟩ := hy'
    exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hc)
  exact hle.trans (sup_le hT_le hC_le)

end CFSG.StandardType
