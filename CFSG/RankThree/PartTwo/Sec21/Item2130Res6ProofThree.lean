module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofAct
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFixMat
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res5ProofLThree
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Matrix
open Item211Proof Item211Res2Proof Item2130Res5Proof

namespace Item2130Res6Proof

variable {G : Type} [Group G] [Finite G]

theorem slAct_trans_apply {Y A : Subgroup G} (hAL : A ≤ Subgroup.normalizer (Y : Set G))
    {Φ₀ : lBar Y ≃* lOne Y A}
    (hΦ₀ : ∀ l : Y, (Φ₀ (l : lBar Y) : QuotX Y A) = piX Y A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {S : Type*} [Group S] (e : lBar Y ≃* S) {a : G} (haA : a ∈ A) (z : lBar Y) :
    slAct (Φ₀.symm.trans e) ⟨piX Y A ⟨a, Subgroup.mem_sup_right haA⟩,
        mem_normalizer_lOne hAL _⟩ (e z) = e (barHom Y ⟨a, hAL haA⟩ z) := by
  rw [slAct_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
    ← lEquiv_conj hΦ₀ haA (hAL haA) (mem_normalizer_lOne hAL _) z, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  rfl

omit [Finite G] in
theorem piX_pow_three {Y A : Subgroup G} (hAL : A ≤ Subgroup.normalizer (Y : Set G)) {a : G}
    (haA : a ∈ A) (ha3 : a ^ 3 = 1) :
    (⟨piX Y A ⟨a, Subgroup.mem_sup_right haA⟩, mem_normalizer_lOne hAL _⟩ :
      Subgroup.normalizer ((lOne Y A : Subgroup (QuotX Y A)) : Set (QuotX Y A))) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
  have : (⟨a, Subgroup.mem_sup_right haA⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  rw [this, map_one]

variable {A E U L U₀ Y : Subgroup G} {c b : G}

theorem exists_actsVia_c_projImage
    (hAL : A ≤ Subgroup.normalizer (Y : Set G))
    (hNF : ∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧ ¬ KFacts.InducesStdKind Y x .graphField)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (e : lBar Y ≃* projImage (slPi π 3 (p ^ f) K)) (hcA : c ∈ A) (hc3 : c ^ 3 = 1) :
    ∃ y ∈ glPi π 3 (p ^ f) K,
      ActsVia Y ((projImage (slPi π 3 (p ^ f) K)).subtype.comp e.toMonoidHom) c y := by
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  rcases pslAct_pgl_or_field hK hq2 (theta_lOne_eq_bot Φ₀) (Φ₀.symm.trans e) _
      (piX_pow_three hAL hcA hc3) with ⟨y, hy, hys⟩ | ⟨hkind, -⟩
  · refine ⟨y, hy, hAL hcA, fun z => ?_⟩
    have h1 := hys (e z)
    rw [slAct_trans_apply hAL hΦ₀ e hcA z] at h1
    exact h1
  · exact ((hNF c hcA).1 (inducesStdKind_of_lOne hAL hΦ₀ hcA hkind)).elim

theorem exists_actsVia_c_slPi
    [Group.IsPerfect (lBar Y)]
    (hAL : A ≤ Subgroup.normalizer (Y : Set G))
    (hNF : ∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧ ¬ KFacts.InducesStdKind Y x .graphField)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq2 : 2 < p ^ f)
    (e : lBar Y ≃* slPi π 3 (p ^ f) K) (hcA : c ∈ A) (hc3 : c ^ 3 = 1) :
    ∃ y ∈ glPi π 3 (p ^ f) K,
      ActsVia Y ((ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).comp
        ((slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom)) c y := by
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have : Group.IsPerfect (lOne Y A) :=
    Group.IsPerfect.ofSurjective (f := Φ₀.toMonoidHom) Φ₀.surjective
  rcases slAct_pgl_or_field hK hq2 (theta_lOne_eq_bot Φ₀) (Φ₀.symm.trans e) _
      (piX_pow_three hAL hcA hc3) with ⟨y, hy, hys⟩ | ⟨hkind, -⟩
  · refine ⟨y, hy, hAL hcA, fun z => ?_⟩
    have h1 := hys (e z)
    rw [slAct_trans_apply hAL hΦ₀ e hcA z] at h1
    change ProjGenLinGroup.mk ((e (barHom Y ⟨c, hAL hcA⟩ z) : slPi π 3 (p ^ f) K) :
        GL (Fin 3) K) = ProjGenLinGroup.mk y *
      ProjGenLinGroup.mk ((e z : slPi π 3 (p ^ f) K) : GL (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹
    rw [h1, map_mul, map_mul, map_inv]
  · exact ((hNF c hcA).1 (inducesStdKind_of_lOne hAL hΦ₀ hcA hkind)).elim

theorem false_of_type3_model (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] {ε : lBar Y →* ProjGenLinGroup (Fin 3) K}
    (hM : IsBarModel Y π p f K ε) (hodd : Odd (Nat.card (oThreePrime (Outer (lBar Y)))))
    {a : G} (haA : a ∈ A) {ya : GL (Fin 3) K} (hyaH : ya ∈ glPi π 3 (p ^ f) K)
    (hya3 : Type123 π (p ^ f) K ya 3) (hya : ActsVia Y ε a ya) {yc : GL (Fin 3) K}
    (hycH : yc ∈ glPi π 3 (p ^ f) K) (hyc : ActsVia Y ε c yc) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK := hM.field
  have hq := hM.modThree
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hqY : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hqY.1
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) := hM.isPerfect
  have hle : ε.range ≤ projImage (slPi π 3 (p ^ f) K) := hM.range_eq.le
  have hge : projImage (slPi π 3 (p ^ f) K) ≤ ε.range := hM.range_eq.ge
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hEA : E ≤ A := hcfg.pair.mem_E.2
  have hcA : c ∈ A := hEA hpairs.1.1
  have hbA : b ∈ A := hC.b_mem.1
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hcK : c ∉ Y ⊔ thetaQuotCentralizer Y := by
    intro hcK
    have hAK : A ≤ Y ⊔ thetaQuotCentralizer Y := le_of_forall_conj hcfg hcK fun b' hb' => by
      obtain ⟨w, hw, -, hwc⟩ := Choice2130.exists_conj hcfg hC hb'
      exact ⟨w, Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨hw, normalizer_le_normalizer_thetaQuotCentralizer Y hw⟩, hwc⟩
    obtain ⟨l, hl, hal⟩ := exists_actsVia_of_mem_sup hle (hAK haA)
    obtain ⟨ζ, hζ⟩ := ActsVia.inv_mul_mem hK hq hge hya hal
    refine not_inner_of_type3 hK hq hyaH hya3 ⟨l, hl, fun m _ => ?_⟩
    set sc := GeneralLinearGroup.scalar (Fin 3) ζ with hsc
    have hl' : l = ya * sc := by rw [hζ]; group
    have hc : m * sc = sc * m := commute_of_mem_statedScalars ⟨ζ, rfl⟩ m
    rw [hl']
    calc ya * m * ya⁻¹ = ya * (m * sc) * sc⁻¹ * ya⁻¹ := by group
      _ = ya * (sc * m) * sc⁻¹ * ya⁻¹ := by rw [hc]
      _ = ya * sc * m * (ya * sc)⁻¹ := by group
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by
    simpa using (hcfg.pair.mem_E.1.1.2 g g.2))⟩
  have hEN : E ≤ Subgroup.normalizer (Y : Set G) :=
    hC.three_norm E hE3 (hEA.trans hAC)
  have hU04 : Nat.card U₀ = 4 := hC.u_mem.1.2.2
  have hU02 : IsPGroup 2 U₀ := IsPGroup.of_card (n := 2) (by rw [hU04]; norm_num)
  have hEU : ⁅E, U₀⁆ = U₀ := by rw [Subgroup.commutator_comm]; exact hC.u_mem.2.symm
  have hU0K : U₀ ≤ Y ⊔ thetaQuotCentralizer Y :=
    le_sup_thetaQuotCentralizer_of_odd hodd hE3 hEN hC.u_norm hU02 hEU
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hyc3 : yc ^ 3 ∈ StatedScalars (Fin 3) K := pow_mem_of_actsVia hK hq hge hyc hc3
  have hycZ : yc ∉ zPi π 3 (p ^ f) K := fun h => hcK (Subgroup.mem_sup_right
    (hyc.mem_thetaQuotCentralizer hM.faithful (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)))
  have hyc3' : yc ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hycH 3, hyc3⟩
  have hac : a * c = c * a :=
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨c, hcA⟩)
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (yc : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    rcases type123_exhaust hK hq hycH hycZ hyc3' with h1 | h2 | h3
    ·
      exfalso
      obtain ⟨l, hl, hlm⟩ := exists_inner_of_type1 hK hq hycH h1
      have hlyc : l⁻¹ * yc ∈ StatedScalars (Fin 3) K :=
        mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => by
          have := hlm m hm
          calc l⁻¹ * yc * m = l⁻¹ * (yc * m * yc⁻¹) * yc := by group
            _ = l⁻¹ * (l * m * l⁻¹) * yc := by rw [this]
            _ = m * (l⁻¹ * yc) := by group
      have hycl : yc⁻¹ * l ∈ StatedScalars (Fin 3) K := by
        have := inv_mem hlyc
        rwa [mul_inv_rev, inv_inv] at this
      exact hcK (mem_sup_of_actsVia hge hM.faithful hyc hl hycl)
    ·
      exact (false_of_type2_of_commMod hK hq h2 hya3.2.2
        (commMod_of_commute hK hq hge hya hyc hac)).elim
    · exact h3.2.2
  have hYc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A c hpairs.2.2.1)
  have hU0C : U₀ ≤ thetaQuotCentralizer Y := by
    intro u hu
    obtain ⟨l, -, hul⟩ := exists_actsVia_of_mem_sup hle (hU0K hu)
    have hu2 : u ^ 2 = 1 := hC.u_mem.1.2.1.2 u hu
    have hl2 : l ^ 2 ∈ StatedScalars (Fin 3) K := pow_mem_of_actsVia hK hq hge hul hu2
    have huc : u * c = c * u :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYc (hC.u_le hu))
    obtain ⟨μ, hμ⟩ := commMod_of_commute hK hq hge hul hyc huc
    have hconj : l * yc * l⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * yc := by
      rw [hμ]
      group
    have hμ1 := Sec16.Proof1613Fix.eq_one_of_conj_eq_scalar_mul_of_sq hconj hl2
    rw [hμ1, map_one, one_mul] at hconj
    have hlyc : l * yc = yc * l := by
      calc l * yc = l * yc * l⁻¹ * l := by group
        _ = yc * l := by rw [hconj]
    exact hul.mem_thetaQuotCentralizer hM.faithful
      (mem_statedScalars_of_commute_of_sq hirr hlyc hl2)
  exact not_le_thetaQuotCentralizer hqY hC.y_comm_u hU0C

end Item2130Res6Proof

open Item2130Res6Proof

theorem item2130CaseTypeThree_holds :
    Item2130CaseTypeThree := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY hSL hH hNF ha3
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, haA, ha3⟩ := ha3
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hbA : b ∈ A := hC.b_mem.1
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hAL : A ≤ Subgroup.normalizer (Y : Set G) := hC.three_norm A hA hAC
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hqY : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have : Group.IsPerfect (lBar Y) := hqY.1
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  rcases ha3 with ⟨hx, π, p, f, K, _, hK, hq, e, y, hy, hy3, hey⟩ |
      ⟨hx, π, p, f, K, _, hK, hq, e, y, hy, hy3, hey⟩
  ·
    have hq2 := two_lt_of_projImage hK hq hqY e
    obtain ⟨yc, hycH, hyc⟩ := exists_actsVia_c_projImage hAL hNF hK hq2 e hcA hc3
    exact false_of_type3_model hcfg hC (isBarModel_projImage hK hq hq2 e)
      (odd_oThreePrime_of_projImage hK hq2 e) haA hy hy3 ⟨hx, hey⟩ hycH hyc
  ·
    have hq2 := two_lt_of_slPi hK hq hqY e
    obtain ⟨yc, hycH, hyc⟩ := exists_actsVia_c_slPi hAL hNF hK hq2 e hcA hc3
    refine false_of_type3_model hcfg hC (isBarModel_slPi hK hq hq2 e)
      (odd_oThreePrime_of_slPi hK hq2 e) haA hy hy3 ⟨hx, fun z => ?_⟩ hycH hyc
    change ProjGenLinGroup.mk ((e (thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨a, hx⟩) z) :
        slPi π 3 (p ^ f) K) : GL (Fin 3) K) = ProjGenLinGroup.mk y *
      ProjGenLinGroup.mk ((e z : slPi π 3 (p ^ f) K) : GL (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹
    rw [hey z, map_mul, map_mul, map_inv]

end CFSG.RankThree.PartTwo.Sec21
