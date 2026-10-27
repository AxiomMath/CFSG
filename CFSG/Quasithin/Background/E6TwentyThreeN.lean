module

public import CFSG.Quasithin.Background.E6TwentyThreeM
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Basic

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623A6Over : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L U₀ X Y : Subgroup G) (g : G)
    (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → E3.rParam V = 1 →
    U ≤ V → E3.mQuot V U = 1 → ¬ Subgroup.centralizer (U : Set G) ≤ M →
    CharTwo (Subgroup.centralizer (U : Set G)) →
    IsChi0Block (Subgroup.centralizer (U : Set G)) L → IsAltType L 3 → ¬ L ≤ M →
    U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) = ⊥ →
    U₀ < U → E3.mQuot V U₀ ≤ 2 →
    IsComponentIn X (Subgroup.centralizer (U₀ : Set G)) →
    Nonempty (↥X ≃* alternatingGroup (Fin 6)) → L ≤ X →
    g ∈ M ⊓ Subgroup.normalizer (V : Set G) → ¬ CFSG.conjugate L g ≤ X →
    IsComponentIn Y (Subgroup.centralizer ((U₀ ⊓ CFSG.conjugate U g : Subgroup G) : Set G)) →
    (Y.subgroupOf
      (Subgroup.centralizer ((U₀ ⊓ CFSG.conjugate U g : Subgroup G) : Set G))).Normal →
    X < Y → ¬ U₀ ≤ Subgroup.centralizer (Y : Set G) → False

section Three

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_three_alt6 {H X : Subgroup G} (e : ↥X ≃* alternatingGroup (Fin 6))
    (hXH : X ≤ H) (hr : CFSG.Open.pRank 3 H ≤ 2) {y : G} (hyH : y ∈ H)
    (hyN : y ∈ Subgroup.normalizer (X : Set G)) (hy3 : y ^ 3 = 1) : y ∈ X := by
  obtain ⟨z, hzX, hz⟩ := exists_mem_of_pow_three_alt6 e hyN hy3
  have hcC : z⁻¹ * y ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := hz g hg
    calc g * (z⁻¹ * y) = z⁻¹ * (z * g * z⁻¹) * y := by group
      _ = z⁻¹ * (y * g * y⁻¹) * y := by rw [h1]
      _ = z⁻¹ * y * g := by group
  have hyz : y * z = z * y := by
    have h1 := hz z hzX
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = (z * z * z⁻¹) * y := by rw [h1]
      _ = z * y := by group
  have hc3 : (z⁻¹ * y) ^ 3 = 1 := by
    have hcomm : Commute z⁻¹ y := Commute.inv_left (show Commute z y from hyz.symm)
    have hpow : (z⁻¹ * y) ^ 3 = z⁻¹ ^ 3 * y ^ 3 := hcomm.mul_pow 3
    rw [hy3, mul_one] at hpow
    have hmemX : (z⁻¹ * y) ^ 3 ∈ X := by
      rw [hpow]
      exact X.pow_mem (inv_mem hzX) 3
    have hmemC : (z⁻¹ * y) ^ 3 ∈ Subgroup.centralizer (X : Set G) :=
      Subgroup.pow_mem _ hcC 3
    exact eq_one_of_centralizes_alt (by norm_num) e hmemX fun g hg =>
      Subgroup.mem_centralizer_iff.1 hmemC g hg
  have hc1 := eq_one_of_mem_centralizer_alt6 e hXH hr (mul_mem (inv_mem (hXH hzX)) hyH) hcC hc3
  rw [inv_mul_eq_one] at hc1
  rw [← hc1]
  exact hzX

end Three

theorem e623A6Detour_of_over (h311 : Theorem311Stmt) (hI31 : AS_I_3_1_three)
    (hO : E623A6Over) : E623A6Detour := by
  intro G _ _ T M V U L U₀ X g hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀U hU₀q hX hXA6 hLX
    hg hgX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hXA6
  have := h.simple
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have h15 : HypE615 hV M := Or.inr hm
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr1).2
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := hg.2
  have hU₀V : U₀ ≤ V := hU₀U.le.trans hUV
  set U₁ := U₀ ⊓ CFSG.conjugate U g with hU₁def
  have hU₁V : U₁ ≤ V := inf_le_left.trans hU₀V
  have hU₁1 : U₁ ≠ ⊥ := by
    intro h0
    have h1 := mQuot_inf_le (U := U₀) (U' := CFSG.conjugate U g) hV2
    rw [← hU₁def, h0, mQuot_conjugate hgN] at h1
    omega
  set H₀ := Subgroup.centralizer (U₀ : Set G) with hH₀def
  set H₁ := Subgroup.centralizer (U₁ : Set G) with hH₁def
  have hH₀H₁ : H₀ ≤ H₁ := Subgroup.centralizer_le inf_le_left
  have hXq : CFSG.IsQuasisimple ↥X := BenderBranch.isQuasisimple_of_isComponentIn hX
  have hXH₀ : X ≤ H₀ := hX.1
  have hXH₁ : X ≤ H₁ := hXH₀.trans hH₀H₁
  have hr3 : CFSG.Open.pRank 3 H₁ ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.centralizer_le_normalizer _)).trans
      ((A1b.pRank_le_evenRank Nat.prime_three (by norm_num)
        ⟨U₁, hU₁1, hV2.to_le hU₁V, rfl⟩).trans h.qtke.2.2)
  have hm3 : CFSG.Open.pRank 3 X = 2 := by
    refine le_antisymm ((CFSG.SectionRank.pRank_mono (by norm_num) hXH₁).trans hr3) ?_
    obtain ⟨P, hPX, hP3, hP9⟩ := CFSG.QuasithinUnique.exists_elemAbelian_nine e
    exact CFSG.SectionRank.le_pRank (by norm_num) hPX hP3 (by rw [hP9]; norm_num)
  have hq : QTKECore G := qtkeCore_of_cat h.nonabelian h.qtke
  have hU₀H₁ : U₀ ≤ H₁ := fun u hu => Subgroup.mem_centralizer_iff.2 fun w hw =>
    hVc _ (hU₁V hw) _ (hU₀V hu)
  have hpc : pCoreOf 2 H₁ ≠ ⊥ := by
    intro h0
    apply hU₁1
    refine le_bot_iff.1 (h0 ▸ C1.le_pCoreOf_of_normalized ?_
      (Subgroup.centralizer_le_normalizer _) (hV2.to_le hU₁V))
    exact fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' => hVc _ (hU₁V hw') _ (hU₁V hw)
  have hK1 : CFSG.SectionRank.IsSQTKCat ↥H₁ := hq.1 H₁ hpc
  have hX2 : Id2519.IsTwoComponentIn X (H₁ ⊓ Subgroup.centralizer (U₀ : Set G)) := by
    rw [inf_eq_right.2 hH₀H₁]
    exact Id2519.isTwoComponentIn_of_isComponentIn hX (two_dvd_card_of_isQuasisimple hXq)
  obtain ⟨Y, hY2, hXY, hYn, -, hYq⟩ := hI31 G H₁ U₀ X hK1 hU₀H₁ (hV2.to_le hU₀V) hX2 hm3
  have hYc : IsComponentIn Y H₁ := Id2519.isComponentIn_of_mem_cComp hY2.1 hYq
  have hYN : H₁ ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYc.1).1 hYn
  have hXneY : X ≠ Y := by
    intro hXYeq
    apply hgX
    have hLgH₁ : CFSG.conjugate L g ≤ H₁ := by
      rintro _ ⟨l, hl, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨hu₀, w, hw, rfl⟩ := hu
      have hlw : l * w = w * l :=
        (Subgroup.mem_centralizer_iff.mp (hLb.1.2.1 hl) w hw).symm
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * w * g * (g⁻¹ * l * g) = g⁻¹ * (w * l) * g := by group
        _ = g⁻¹ * (l * w) * g := by rw [hlw]
        _ = g⁻¹ * l * g * (g⁻¹ * w * g) := by group
    have hs : IsShort2 (CFSG.conjugate L g) := Lin2.IsShort2.map_equiv hLb.1.1 (MulAut.conj g⁻¹)
    have h3' : IsAltType (CFSG.conjugate L g) 3 :=
      AppCS2.isAltType_map_equiv hL3 (MulAut.conj g⁻¹)
    refine le_of_forall_pow_three_mem hs h3' fun y hy hy3 => ?_
    have hyN : y ∈ Subgroup.normalizer (X : Set G) := by
      rw [hXYeq]
      exact hYN (hLgH₁ hy)
    exact mem_of_pow_three_alt6 e hXH₁ hr3 (hLgH₁ hy) hyN hy3
  have hXltY : X < Y := lt_of_le_of_ne hXY hXneY
  have hYU₀ : ¬ U₀ ≤ Subgroup.centralizer (Y : Set G) := by
    intro hle
    have hYH₀ : Y ≤ H₀ := fun y hy => Subgroup.mem_centralizer_iff.2 fun u hu =>
      (Subgroup.mem_centralizer_iff.1 (hle hu) y hy).symm
    have hYc' : IsComponentIn Y H₀ := BenderBranch.isComponentIn_of_le hYc hYH₀ hH₀H₁
    rcases BenderBranch.eq_or_commute_of_isComponentIn hX hYc' with heq | hcomm
    · exact hXneY heq
    · have hperf : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp hXq.1
      have hbot : X = ⊥ := by
        rw [← hperf, eq_bot_iff, ← hcomm]
        exact Subgroup.commutator_mono le_rfl hXY
      exact (Subgroup.nontrivial_iff_ne_bot X).mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hXq) hbot
  exact hO G T M V U L U₀ X Y g hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀U hU₀q hX ⟨e⟩ hLX
    hg hgX hYc hYn hXltY hYU₀

end CFSG.Quasithin.E6
