module

public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenLevi
public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
public import CFSG.Blueprint.Catalog
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
import CFSG.RankThree.PartTwo.Census.Criteria
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.D4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly
  CFSG.Assembly.RankThreeEven

theorem exists_conj_le_graphFixedParabolicLevi (t : TwistTag) (k : Type) [Field k] [Finite k]
    (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p) (σ : k ≃+* k)
    (hσ : σ ^ t.order = 1) (A : Subgroup (ModGL t.tag k))
    (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom) (hAp : IsPGroup p A)
    (R : Subgroup (ModGL t.tag k)) (hRC : R ≤ graphFixedRootGroup t k σ.toRingHom)
    (hRr : IsPGroup r R) (hR : R ≠ ⊥)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL t.tag k))) :
    ∃ x ∈ graphFixedRootGroup t k σ.toRingHom, ∃ J : Set (Fin t.foldedTag.rank),
      J ≠ Set.univ ∧
        A.map (MulAut.conj x).toMonoidHom ≤ graphFixedParabolicLevi t k σ.toRingHom J := by
  have := finite_modGL (τ := t.tag) (K := k)
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      r R hRC hRr hR
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL t.tag k, g' = g := ⟨g, rfl⟩
  have hgC : g' ∈ graphFixedRootGroup t k σ.toRingHom := hg
  have hJ' : ((RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l :
      Set (Fin t.foldedTag.rank)) ≠ Set.univ := hJ
  set J : Set (Fin t.foldedTag.rank) := (RootWeightDatum.fixed t σ hσ : RootWeightDatum k).face l
  change {x : ModGL t.tag k | x ∈ graphFixedRootGroup t k σ.toRingHom ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule t.tag k)) = F c} =
    ((graphFixedParabolic t k σ.toRingHom J).map (MulAut.conj g').toMonoidHom :
      Set (ModGL t.tag k)) at hset
  have hA1 : A.map (MulAut.conj g'⁻¹).toMonoidHom ≤ graphFixedParabolic t k σ.toRingHom J := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem := (Set.ext_iff.1 hset a).1
      (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hmem
  have hindex : ¬ p ∣ ((graphFixedParabolicLevi t k σ.toRingHom J).subgroupOf
      (graphFixedParabolic t k σ.toRingHom J)).index := by
    rw [graphFixedParabolicLevi_index_eq]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfin, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors t k σ J
    exact not_dvd_card_of_isPGroup hrp (hfin r)
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1 (hAp.map _) hindex
  have hyC : y ∈ graphFixedRootGroup t k σ.toRingHom :=
    graphFixedParabolic_le t k σ.toRingHom J hy
  have hmap : A.map (MulAut.conj (y * g'⁻¹)).toMonoidHom =
      (A.map (MulAut.conj g'⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  exact ⟨y * g'⁻¹, mul_mem hyC (inv_mem hgC), J, hJ', hmap ▸ hyA⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem localRank_three_graphFixedRootGroup (σ : K ≃+* K) (hσ : σ ^ TwistTag.D4.order = 1) :
    localRank 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ 2 := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  obtain ⟨L, hL, hLr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3
    Nat.prime_three C (by change 0 < localRank 3 C; omega)
  change CFSG.Assembly.pRank 3 L = localRank 3 C at hLr
  obtain ⟨E, hEL, hE, hEc⟩ : ∃ E : Subgroup C, E ≤ L ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ CFSG.Assembly.pRank 3 L :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three L
  obtain ⟨P, hP, hP2, rfl⟩ := hL
  set E' := E.map C.subtype
  set P' := P.map C.subtype
  have hE'C : E' ≤ C := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hP'C : P' ≤ C := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hP'2 : IsPGroup 2 P' := hP2.map _
  have hP'1 : P' ≠ ⊥ := fun h => hP ((Subgroup.map_eq_bot_iff_of_injective _
    Subtype.val_injective).1 h)
  have hE'N : E' ≤ Subgroup.normalizer (P' : Set (ModGL TwistTag.D4.tag K)) := by
    rintro _ ⟨e, he, rfl⟩
    have hen := hEL he
    rw [Subgroup.mem_normalizer_iff] at hen ⊢
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e * y * e⁻¹, (hen y).1 hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hxy' : (y : ModGL TwistTag.D4.tag K) =
          (e : ModGL TwistTag.D4.tag K) * x * (e : ModGL TwistTag.D4.tag K)⁻¹ := hxy
      have hx : x ∈ C := by
        have hxe : x = (e : ModGL TwistTag.D4.tag K)⁻¹ * (y : ModGL TwistTag.D4.tag K) *
            (e : ModGL TwistTag.D4.tag K) := by
          rw [hxy']
          group
        rw [hxe]
        exact mul_mem (mul_mem (inv_mem e.2) y.2) e.2
      refine ⟨⟨x, hx⟩, (hen ⟨x, hx⟩).2 ?_, rfl⟩
      have : e * ⟨x, hx⟩ * e⁻¹ = y := Subtype.ext hxy.symm
      rw [this]
      exact hy
  have hE'3 : IsPGroup 3 E' := by
    rintro ⟨_, ⟨e, he, rfl⟩⟩
    exact ⟨1, Subtype.ext (by simpa using congrArg Subtype.val (hE.2 e he))⟩
  obtain ⟨x, -, J, hJ, hxE⟩ := exists_conj_le_graphFixedParabolicLevi TwistTag.D4 K 2 3
    (by norm_num) σ hσ E' hE'C hE'3 P' hP'C hP'2 hP'1 hE'N
  have hE'' : IsElemAbelian 3 (E'.map (MulAut.conj x).toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨_, ⟨e₁, he₁, rfl⟩, rfl⟩⟩ := a
      obtain ⟨_, ⟨_, ⟨e₂, he₂, rfl⟩, rfl⟩⟩ := b
      have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype] at h ⊢
      have h' : (e₁ : ModGL TwistTag.D4.tag K) * e₂ = e₂ * e₁ := congrArg Subtype.val h
      calc x * ↑e₁ * x⁻¹ * (x * ↑e₂ * x⁻¹) = x * (↑e₁ * ↑e₂) * x⁻¹ := by group
        _ = x * (↑e₂ * ↑e₁) * x⁻¹ := by rw [h']
        _ = x * ↑e₂ * x⁻¹ * (x * ↑e₁ * x⁻¹) := by group
    · rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
      have h3 : (e : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
        simpa using congrArg Subtype.val (hE.2 e he)
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, h3, mul_one, mul_inv_cancel]
  have h9 := card_le_nine_of_le_graphFixedParabolicLevi hJ hE'' hxE
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective,
    Subgroup.card_map_of_injective Subtype.val_injective, hEc] at h9
  have hr : 3 ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (P : Set C)) := by omega
  have : 3 ^ 3 ≤ 3 ^ CFSG.Assembly.pRank 3 (Subgroup.normalizer (P : Set C)) :=
    Nat.pow_le_pow_right (by norm_num) hr
  omega

def derivedCentralQuotientEquiv {M : Type} [Group M] {H : Subgroup M} (hperf : ⁅H, H⁆ = H)
    (hZ : Subgroup.center H = ⊥) : CFSG.Blueprint.DerivedCentralQuotient H ≃* H := by
  let e₁ : ↥⁅H, H⁆ ≃* H := MulEquiv.subgroupCongr hperf
  have hZ' : Subgroup.center ↥⁅H, H⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ Subgroup.center H :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := e₁.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
    rw [hZ, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e₁.injective (hz'.trans (map_one e₁).symm))
  exact (QuotientGroup.quotientMulEquivOfEq hZ').trans (QuotientGroup.quotientBot.trans e₁)

theorem localRank_three_derivedCentralQuotient (f : ℕ) (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    localRank 3 (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ)) ≤
      2 := by
  have hchar : ringChar K = 2 := ringChar.eq K 2
  let σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσσ : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  have hσ3 : ∀ c, σ' (σ' (σ' c)) = c := fun c => by
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    have : Fintype K := Fintype.ofFinite K
    have hc := FiniteField.pow_card c
    rw [Fintype.card_eq_nat_card, hK] at hc
    convert hc using 2
    ring
  have hσ' : σ' ^ TwistTag.D4.order = 1 := by
    refine RingEquiv.ext fun c => ?_
    exact hσ3 c
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
  have hΓ := twistedFixedGroup_eq_graphFixedRootGroup_triality σ' hσ3 (Or.inl hchar)
  have hperf := commutator_graphFixedRootGroup_triality_char_two hchar σ' hσ3 h4
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ'
  rw [hσσ] at hΓ hperf hZ
  have e : CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ) ≃*
      graphFixedRootGroup TwistTag.D4 K σ := by
    rw [hΓ]
    exact derivedCentralQuotientEquiv hperf hZ
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three, ← hσσ]
  exact localRank_three_graphFixedRootGroup σ' hσ'

end CFSG.RankThree.PartTwo.Census.Carrier.D4Even
