module

public import CFSG.Milestones.ASVolI.C5Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Frat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppELoc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCExcl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppELin2
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian

public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_data (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G}
    (hKi : Ki ∈ conjSubgroupsBy TH K₁) :
    IsMinimalParabolic (R ⊓ Subgroup.normalizer (Ki : Set G))
        (Ki ⊔ (R ⊓ Subgroup.normalizer (Ki : Set G))) ∧
      IsChi0Block (Ki ⊔ (R ⊓ Subgroup.normalizer (Ki : Set G))) Ki ∧
      ⁅Ki, thompsonJ (R ⊓ Subgroup.normalizer (Ki : Set G))⁆ = Ki ∧
      baum (R ⊓ Subgroup.normalizer (Ki : Set G)) = baum R ∧
      baum R ≤ Subgroup.normalizer (Ki : Set G) := by
  have hyp1 := hset.hyp1
  have cfg := hset.config
  obtain ⟨N, hmin⟩ := burnsideC5h_p1_minParabolic hset (burnsideC5h_c54_one h116 hset) Ki hKi
  set Ri : Subgroup G := R ⊓ Subgroup.normalizer (Ki : Set G) with hRi
  have hS1 : baum R ≤ Subgroup.normalizer (Ki : Set G) := burnsideC5h_c54_one h116 hset Ki hKi
  have hSR : baum R ≤ R := C1GN.baum_le R
  have hSRi : baum R ≤ Ri := le_inf hSR hS1
  have hJRi : thompsonJ R ≤ Ri := (C5.thompsonJ_le_baum' R).trans hSRi
  have hRiR : Ri ≤ R := inf_le_left
  have hJeq : thompsonJ Ri = thompsonJ R := burnsideC5h_p2_thompsonJ_eq hJRi hRiR
  have hbeq : baum Ri = baum R := burnsideC5h_p2_baum_eq hJRi hRiR hSRi
  have hth : ⁅Ki, thompsonJ Ri⁆ = Ki := by
    rw [hJeq]
    obtain ⟨t, ht, rfl⟩ := hKi
    refine burnsideC5h_p2_comm_conj cfg.comm_J ?_
    exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ R
      (hyp1.TH_le.trans hyp1.R_norm ht)
  have hshort : IsShort2 Ki := (burnsideC5h_c54_isBlock2 hset hKi).1
  have hHiN : Ki ⊔ Ri ≤ Subgroup.normalizer (Ki : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hblk : IsChi0Block (Ki ⊔ Ri) Ki :=
    ⟨⟨hshort, le_sup_left,
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHiN).isSubnormal⟩,
      (burnsideC5h_c54_isChi0Block hset hKi).2⟩
  exact ⟨burnsideC5h_p2_isMinimalParabolic hmin, hblk, hth, hbeq, hS1⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_rank1 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G}
    (hKi : Ki ∈ conjSubgroupsBy TH K₁)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type Ki n) ∨ IsAltType Ki 3) :
    ∃ (q : ℕ) (W : Subgroup G), 2 ≤ q ∧
      C5.Rank1 (baum R) (pCoreOf 2 (Ki ⊔ baum R)) (blockU Ki) W q ∧
      (blockU Ki ⊓ Subgroup.centralizer (Ki : Set G)).relIndex (blockU Ki) = q ^ 2 ∧
      (∀ y ∈ Subgroup.normalizer (baum R : Set G),
        ¬ conjSubgroup (blockU Ki) y ≤ pCoreOf 2 (Ki ⊔ baum R) →
        ¬ conjSubgroup (blockU Ki) y⁻¹ ≤ pCoreOf 2 (Ki ⊔ baum R) →
        ∃ k ∈ Ki, Ki ≤ conjSubgroup (blockU Ki) y ⊔
          conjSubgroup (conjSubgroup (blockU Ki) y) k) := by
  obtain ⟨hmin, hblk, hth, hbeq, hS1⟩ := burnsideC5x_data h116 hset hKi
  have hnat : NaturalConcl (R ⊓ Subgroup.normalizer (Ki : Set G))
      (Ki ⊔ (R ⊓ Subgroup.normalizer (Ki : Set G))) Ki := by
    rcases hL with hl | h3
    · exact C56.natural_Lin2 hmin hblk hl hth rfl inf_le_right
    · exact C56.natural_A3 hmin hblk h3 hth rfl inf_le_right
  unfold NaturalConcl at hnat
  rw [hbeq] at hnat
  obtain ⟨q, W, hq2, hWU, hidxQ, hidxW, hcent, hcomm, hZ, hgen, -⟩ := hnat
  have hP1 := burnsideC5h_p1_minParabolic hset (burnsideC5h_c54_one h116 hset)
  obtain ⟨-, -, -, hUQ, hQ⟩ := burnsideC5h_p2_lin2A3 h116 hset hP1 Ki hKi hL
  have hshort : IsShort2 Ki := (burnsideC5h_c54_isBlock2 hset hKi).1
  rw [← hQ] at hidxQ hgen
  refine ⟨q, W, hq2, ⟨hUQ, ?_, ?_, ?_, hQ, hWU, hidxQ, hidxW, by omega, ?_, hcomm,
    (C1.elemAb2_blockU hshort).1⟩, hZ, hgen⟩
  · rw [hQ]; exact inf_le_left
  · exact le_sup_right.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  · exact fun g hg => C1.mem_normalizer_blockU (hS1 hg)
  · rw [← hQ] at hcent; exact hcent

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_x_normalizer {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {x : G} (hx : x ∈ M₀) :
    x ∈ Subgroup.normalizer (R : Set G) ∧ x ∈ Subgroup.normalizer (baum R : Set G) :=
  ⟨hset.hyp1.R_norm hx, normalizer_le_normalizer_baum R (hset.hyp1.R_norm hx)⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_not_le_Q {G : Type} [Group G] {B U Q : Subgroup G} {x : G}
    (hQ : Q = B ⊓ Subgroup.centralizer (U : Set G)) (hne : ⁅U, conjSubgroup U x⁆ ≠ ⊥) :
    ¬ conjSubgroup U x ≤ Q ∧ ¬ conjSubgroup U x⁻¹ ≤ Q := by
  constructor
  · intro h
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have : v ∈ Subgroup.centralizer (U : Set G) := (hQ ▸ h hv).2
    exact (Subgroup.mem_centralizer_iff.mp this u hu).symm
  · intro h
    apply hne
    have h1 := C5.conjSubgroup_mono h x
    rw [C5.conjSubgroup_inv_conjSubgroup, hQ, C5.conjSubgroup_inf, C5.conjSubgroup_centralizer]
      at h1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    exact (h1 hu).2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
@[expose] def burnsideC5x_P1 {G : Type} [Group G] (R K₁ : Subgroup G) (x : G) : Prop :=
  pCoreOf 2 (K₁ ⊔ baum R) = blockU K₁ ⊔ (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) ∧
    baum R ⊓ Subgroup.centralizer (K₁ : Set G) ≤
      pCoreOf 2 (K₁ ⊔ baum R) ⊓ Subgroup.centralizer (rconj x (blockU K₁) : Set G)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
@[expose] def burnsideC5x_P2 {G : Type} [Group G] (R K₁ : Subgroup G) (x : G) : Prop :=
  (baum R : Set G) = (rconj x (blockU K₁) : Set G) * (pCoreOf 2 (K₁ ⊔ baum R) : Set G) ∧
    (baum R : Set G) = (pCoreOf 2 (K₁ ⊔ baum R) : Set G) *
      (rconj x (pCoreOf 2 (K₁ ⊔ baum R)) : Set G) ∧
    ⁅blockU K₁, baum R⁆ = ⁅blockU K₁, rconj x (blockU K₁)⁆ ∧
    ⁅blockU K₁, rconj x (blockU K₁)⁆ =
      blockU K₁ ⊓ Subgroup.centralizer (rconj x (blockU K₁) : Set G) ∧
    blockU K₁ ⊓ Subgroup.centralizer (rconj x (blockU K₁) : Set G) =
      blockU K₁ ⊓ rconj x (blockU K₁)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
@[expose] def burnsideC5x_P3 {G : Type} [Group G] (R K₁ : Subgroup G) (x : G) : Prop :=
  rconj x ⁅blockU K₁, baum R⁆ = ⁅blockU K₁, baum R⁆

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_lin2A3_123 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) :
    burnsideC5x_P1 R K₁ x ∧ burnsideC5x_P2 R K₁ x ∧ burnsideC5x_P3 R K₁ x := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem hL
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, hx2⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hKQ : K₁ ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) :=
    le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  have hUxN : conjSubgroup (blockU K₁) x ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) :=
    (hrk.conj_le_B hxB).trans hrk.B_le_normQ
  have e1 := hrk.sup_Q_conj hxB hx2
  obtain ⟨hc1, hc2⟩ := hrk.commutator_conj hxB hx1 hx2
  have hc3 := hrk.inf_centralizer_conj hxB hx1
  have hc4 := hrk.conj_W hxB hx1 hx2
  obtain ⟨hD, hDx⟩ := hrk.Q_eq_sup_centralizer hxB hx1 hUK hKQ hZ (hgen x hxB hx1 hx2)
  have hQC : pCoreOf 2 (K₁ ⊔ baum R) ⊓ Subgroup.centralizer (K₁ : Set G) =
      baum R ⊓ Subgroup.centralizer (K₁ : Set G) := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hy, hc⟩
      exact ⟨hrk.Q_le_B hy, hc⟩
    · rintro ⟨hy, hc⟩
      refine ⟨?_, hc⟩
      rw [hrk.Q_eq]
      exact ⟨hy, Subgroup.centralizer_le hUK hc⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hQC]; exact hD
  · intro d hd
    rw [← hQC] at hd
    have h1 := hDx hd
    rw [hrk.conj_Q_eq hxB] at h1
    exact ⟨hd.1, h1.2⟩
  · have := Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup (blockU K₁) x)
      (pCoreOf 2 (K₁ ⊔ baum R)) hUxN
    rw [e1] at this
    exact this
  · have hQN : pCoreOf 2 (K₁ ⊔ baum R) ≤ Subgroup.normalizer
        ((conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x : Subgroup G) : Set G) :=
      hrk.Q_le_B.trans (hrk.B_le_normQ_conj hxB)
    have := Subgroup.coe_mul_of_left_le_normalizer_right (pCoreOf 2 (K₁ ⊔ baum R))
      (conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x) hQN
    have hsup : pCoreOf 2 (K₁ ⊔ baum R) ⊔ conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x = baum R := by
      refine le_antisymm (sup_le hrk.Q_le_B ?_) ?_
      · rw [hrk.conj_Q_eq hxB]; exact inf_le_left
      · calc baum R = conjSubgroup (blockU K₁) x ⊔ pCoreOf 2 (K₁ ⊔ baum R) := e1.symm
          _ ≤ _ := sup_le (le_sup_of_le_right (C5.conjSubgroup_mono hrk.U_le_Q x)) le_sup_left
    rw [hsup] at this
    exact this
  · exact hrk.comm_UB.trans hc1.symm
  · exact hc1.trans hc3.symm
  · exact hc3.trans hc2.symm
  · show conjSubgroup ⁅blockU K₁, baum R⁆ x = ⁅blockU K₁, baum R⁆
    rw [hrk.comm_UB]; exact hc4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
@[expose] def burnsideC5x_P4 {G : Type} [Group G] (R K₁ : Subgroup G) (x : G) : Prop :=
  rconj x ((frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype) =
    (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_frattini_symm {G : Type} [Group G] [Finite G] {Q U D C : Subgroup G} {x : G}
    (hQ2 : IsPGroup 2 ↥Q) (hQx2 : IsPGroup 2 ↥(conjSubgroup Q x)) (hU : C5.ElemAb2 U)
    (hDQ : D ≤ Q) (hCQ : C ≤ Q) (hCQx : C ≤ conjSubgroup Q x)
    (hQD : Q = U ⊔ D) (hUD : ∀ u ∈ U, ∀ d ∈ D, u * d = d * u)
    (hQC : Q = U ⊔ C) (hUC : ∀ u ∈ U, ∀ c ∈ C, u * c = c * u)
    (hQxC : conjSubgroup Q x = conjSubgroup U x ⊔ C)
    (hUxC : ∀ u ∈ conjSubgroup U x, ∀ c ∈ C, u * c = c * u) :
    conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf D) x =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf D := by
  have hUx := hU.conjSubgroup x
  have hD' : CFSG.QuasithinUnique.DoubleA3.frattiniOf Q =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf D := by
    refine AppCS2.frattiniOf_eq_of_mul hQ2 hDQ hU.1 hU.2 hUD fun e he => ?_
    rw [hQD] at he
    exact C5.mem_sup_of_commute hUD he
  have hC' : CFSG.QuasithinUnique.DoubleA3.frattiniOf Q =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf C := by
    refine AppCS2.frattiniOf_eq_of_mul hQ2 hCQ hU.1 hU.2 hUC fun e he => ?_
    rw [hQC] at he
    exact C5.mem_sup_of_commute hUC he
  have hCx : CFSG.QuasithinUnique.DoubleA3.frattiniOf (conjSubgroup Q x) =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf C := by
    refine AppCS2.frattiniOf_eq_of_mul hQx2 hCQx hUx.1 hUx.2 hUxC fun e he => ?_
    rw [hQxC] at he
    exact C5.mem_sup_of_commute hUxC he
  calc conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf D) x
      = conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf Q) x := by rw [hD']
    _ = CFSG.QuasithinUnique.DoubleA3.frattiniOf (conjSubgroup Q x) :=
        AppCS2.conjSubgroup_frattiniOf Q x
    _ = CFSG.QuasithinUnique.DoubleA3.frattiniOf C := hCx
    _ = CFSG.QuasithinUnique.DoubleA3.frattiniOf Q := hC'.symm
    _ = CFSG.QuasithinUnique.DoubleA3.frattiniOf D := hD'

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_lin2A3_4 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) :
    burnsideC5x_P4 R K₁ x := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem hL
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, hx2⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  obtain ⟨⟨hP1a, -⟩, -⟩ := burnsideC5x_lin2A3_123 h116 hset hx hL
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hR2 : IsPGroup 2 R := hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le
  have hB2 : IsPGroup 2 (baum R) := hR2.to_le (C1GN.baum_le R)
  have hrk' := AppE.Rank1.rank1_conj hrk hxB
  have hQxB : conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x ≤ baum R := by
    rw [hrk.conj_Q_eq hxB]; exact inf_le_left
  have hx1' : ¬ conjSubgroup (conjSubgroup (blockU K₁) x) x⁻¹ ≤
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x := by
    intro h
    apply hx2
    have h1 := C5.conjSubgroup_mono h x⁻¹
    rwa [C5.conjSubgroup_conjSubgroup_inv, C5.conjSubgroup_conjSubgroup_inv] at h1
  obtain ⟨-, hQC⟩ := hrk.relIndex_inf_conj hxB hx1
  obtain ⟨-, hQxC⟩ := hrk'.relIndex_inf_conj (x := x⁻¹) (inv_mem hxB) hx1'
  rw [C5.conjSubgroup_conjSubgroup_inv] at hQxC
  rw [inf_comm] at hQxC
  have hD : baum R ⊓ Subgroup.centralizer (K₁ : Set G) ≤ pCoreOf 2 (K₁ ⊔ baum R) := by
    rw [hP1a]; exact le_sup_right
  exact burnsideC5x_frattini_symm (hB2.to_le hrk.Q_le_B) (hB2.to_le hQxB)
    (C1.elemAb2_blockU hshort) hD inf_le_left inf_le_right hP1a
    (fun u hu d hd => (Subgroup.mem_centralizer_iff.mp hd.2 u (hUK hu)))
    hQC.symm (fun u hu c hc => hrk.Q_cent c hc.1 u hu)
    hQxC.symm (fun u hu c hc => hrk'.Q_cent c hc.2 u hu)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_mem_rconj {G : Type} [Group G] {x y : G} {K : Subgroup G} :
    y ∈ rconj x K ↔ x * y * x⁻¹ ∈ K := by
  unfold CFSG.ASVolI.ChC.rconj
  rw [CFSG.Quasithin.mem_conjByElt]
  simp

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_facts {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) :
    TH ≤ Subgroup.normalizer (K₁ : Set G) ∧ oTwoUpper H = K₁ ∧ H = TH ⊔ K₁ := by
  have hTHN : TH ≤ Subgroup.normalizer (K₁ : Set G) := fun t ht =>
    C2Eleven.mem_normalizer_iff_conjByElt.mpr (hs1 t ht)
  have hK : oTwoUpper H = K₁ := by
    rw [hset.config.prod]
    apply le_antisymm
    · exact iSup₂_le fun t ht => (hs1 t ht).le
    · have := le_iSup₂ (f := fun (t : G) (_ : t ∈ TH) => conjByElt t K₁) 1 TH.one_mem
      rwa [burnsideC5h_c54_conjByElt_one] at this
  refine ⟨hTHN, hK, ?_⟩
  have hHKT : TH ⊔ oTwoUpper H = H := by
    rw [← CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hset.hyp1.sylow
  rw [hK] at hHKT
  exact hHKT.symm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_RN {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) :
    R ≤ Subgroup.normalizer (K₁ : Set G) := fun r hr =>
  (burnsideC5x_s1_facts hset hs1).1 (hset.hyp1.R_le hr)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_Q_le {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) :
    pCoreOf 2 (K₁ ⊔ baum R) ≤ pCoreOf 2 H := by
  obtain ⟨hTHN, hK, hHeq⟩ := burnsideC5x_s1_facts hset hs1
  have hyp1 := hset.hyp1
  have hBTH : baum R ≤ TH := (C1GN.baum_le R).trans hyp1.R_le
  have hKH : K₁ ≤ H := hset.config.chi0.1.2.1
  have hTHH : TH ≤ H := hyp1.sylow.1
  have hQH : pCoreOf 2 (K₁ ⊔ baum R) ≤ H :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (sup_le hKH (hBTH.trans hTHH))
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) := by
    rw [hHeq]
    refine sup_le (fun t ht => ?_) (le_sup_left.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _))
    have htB : t ∈ Subgroup.normalizer (baum R : Set G) :=
      normalizer_le_normalizer_baum R (hyp1.R_norm (hyp1.TH_le ht))
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K₁ ⊔ baum R)
      (C1.mem_normalizer_sup (hTHN ht) htB)
  exact C1.le_pCoreOf_of_normalized hQH hHQ
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_exists_goodX (h54 : C_5_4) (h55 : C_5_5) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) : ∃ x : G, GoodX H M₀ K₁ x := by
  have h5 := h55 G H M₀ TH R K₁ hset
  have hex : ∃ y ∈ M₀, ∃ z ∈ blockU K₁, y * z * y⁻¹ ∉ pCoreOf 2 H := by
    by_contra hcon
    push Not at hcon
    exact h5 (CFSG.Quasithin.conjClosure_le fun y hy z hz => hcon y hy z hz)
  obtain ⟨y, hy, z, hz, hyz⟩ := hex
  have hx : y⁻¹ ∈ M₀ := inv_mem hy
  have hnot : ¬ rconj y⁻¹ (blockU K₁) ≤ pCoreOf 2 H := by
    intro h
    apply hyz
    apply h
    rw [burnsideC5x_mem_rconj]
    have e : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
    rw [e]; exact hz
  refine ⟨y⁻¹, hx, hnot, ?_⟩
  intro hne
  apply hnot
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨-, -, -, hUQ, hQ⟩ := (h54 G H M₀ TH R K₁ hset).1 K₁ hK₁mem
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx
  have hUB : blockU K₁ ≤ baum R := hUQ.trans (hQ ▸ inf_le_left)
  have h1 : conjSubgroup (blockU K₁) y⁻¹ ≤ baum R := by
    have := C5.conjSubgroup_mono hUB y⁻¹
    rwa [C5.conjSubgroup_eq_self hxB] at this
  have h2 : conjSubgroup (blockU K₁) y⁻¹ ≤ Subgroup.centralizer (blockU K₁ : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hne
  have h3 : conjSubgroup (blockU K₁) y⁻¹ ≤ pCoreOf 2 (K₁ ⊔ baum R) := by
    rw [hQ]; exact le_inf h1 h2
  exact h3.trans (burnsideC5x_s1_Q_le hset hs1)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_not_mem_normalizer {G : Type} [Group G] [Finite G] {K₁ : Subgroup G} {x : G}
    (hshort : IsShort2 K₁) (hne : ⁅blockU K₁, rconj x (blockU K₁)⁆ ≠ ⊥) :
    x ∉ Subgroup.normalizer (K₁ : Set G) := by
  intro hx
  apply hne
  have : rconj x (blockU K₁) = blockU K₁ :=
    C5.conjSubgroup_eq_self (C1.mem_normalizer_blockU hx)
  rw [this, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (C1.elemAb2_blockU hshort).1 v hv u hu

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_c57_frattini {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {x : G} (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hmax : IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (K₁ : Set G)))
    (hx : GoodX H M₀ K₁ x) (h4 : burnsideC5x_P4 R K₁ x) :
    (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥ := by
  obtain ⟨hTHN, hK, hHeq⟩ := burnsideC5x_s1_facts hset hs1
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hyp1 := hset.hyp1
  set D := baum R ⊓ Subgroup.centralizer (K₁ : Set G) with hD
  set X := CFSG.QuasithinUnique.DoubleA3.frattiniOf D with hX
  have hXD : X ≤ D := Subgroup.map_subtype_le _
  have hXR : X ≤ R := hXD.trans (inf_le_left.trans (C1GN.baum_le R))
  have hND : ∀ m ∈ M₀, m ∈ Subgroup.normalizer (K₁ : Set G) →
      m ∈ Subgroup.normalizer (D : Set G) := fun m hm hmK =>
    C5.mem_normalizer_inf (normalizer_le_normalizer_baum R (hyp1.R_norm hm))
      (C5.mem_normalizer_centralizer hmK)
  have hNX : ∀ m ∈ M₀, m ∈ Subgroup.normalizer (K₁ : Set G) →
      m ∈ Subgroup.normalizer (X : Set G) := fun m hm hmK =>
    CFSG.QuasithinUnique.DoubleA3.mem_normalizer_frattiniOf (hND m hm hmK)
  have hK₁X : K₁ ≤ Subgroup.normalizer (X : Set G) := by
    have : K₁ ≤ Subgroup.centralizer (X : Set G) := fun k hk => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hXD hy).2 k hk).symm
    exact this.trans (Subgroup.centralizer_le_normalizer _)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hHeq]
    exact sup_le (fun t ht => hNX t (hyp1.TH_le ht) (hTHN ht)) hK₁X
  have hxN : x ∈ Subgroup.normalizer (X : Set G) :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h4
  have hxK : x ∉ Subgroup.normalizer (K₁ : Set G) :=
    burnsideC5x_not_mem_normalizer hshort hx.2.2
  have hlt : M₀ ⊓ Subgroup.normalizer (K₁ : Set G) < M₀ ⊓ Subgroup.normalizer (X : Set G) := by
    refine lt_of_le_of_ne (fun m hm => ⟨hm.1, hNX m hm.1 hm.2⟩) fun h => hxK ?_
    have : x ∈ M₀ ⊓ Subgroup.normalizer (X : Set G) := ⟨hx.1, hxN⟩
    rw [← h] at this
    exact this.2
  have hM₀X : M₀ ≤ Subgroup.normalizer (X : Set G) := by
    have := hmax.2 _ hlt inf_le_left
    intro m hm
    have hm' : m ∈ M₀ ⊓ Subgroup.normalizer (X : Set G) := by rw [this]; exact hm
    exact hm'.2
  by_contra hne
  exact hset.hyp2 X hXR hne (sup_le hM₀X hHX)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
@[expose] def burnsideC5x_S1Str {G : Type} [Group G] (R K₁ : Subgroup G) (x : G) : Prop :=
  IsMaxElemAbelian R (pCoreOf 2 (K₁ ⊔ baum R)) ∧
    (∀ A : Subgroup G, IsMaxElemAbelian R A → R ≤ Subgroup.normalizer (A : Set G) →
      A = pCoreOf 2 (K₁ ⊔ baum R) ∨ A = rconj x (pCoreOf 2 (K₁ ⊔ baum R))) ∧
    rconj x (pCoreOf 2 (K₁ ⊔ baum R)) ≠ pCoreOf 2 (K₁ ⊔ baum R) ∧
    (baum R : Set G) = (pCoreOf 2 (K₁ ⊔ baum R) : Set G) *
      (rconj x (pCoreOf 2 (K₁ ⊔ baum R)) : Set G) ∧
    (((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) →
      AFam (baum R) = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R))}) ∧
    (IsAltType K₁ 5 →
      ∃ (A : Subgroup G) (r : G), r ∈ R ⊓ K₁ ∧ r ∉ baum R ∧
        (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A = 2 ∧
        AFam R = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R)), A, rconj r A})

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_AFam_eq {G : Type} [Group G] [Finite G] {R B : Subgroup G} (hBR : B ≤ R)
    (hA : ∀ A, IsMaxElemAbelian R A → A ≤ B) : AFam B = AFam R := by
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian R
  have hA₀B : A₀ ≤ B := hA A₀ hA₀
  ext A
  constructor
  · intro hAB
    have h1 : Nat.card A₀ ≤ Nat.card A := hAB.2.2 A₀ hA₀B hA₀.2.1
    have h2 : Nat.card A ≤ Nat.card A₀ := hA₀.2.2 A (hAB.1.trans hBR) hAB.2.1
    exact ⟨hAB.1.trans hBR, hAB.2.1, fun B' hB' hB'e => (hA₀.2.2 B' hB' hB'e).trans h1⟩
  · intro hAR
    exact ⟨hA A hAR, hAR.2.1, fun B' hB' hB'e => hAR.2.2 B' (hB'.trans hBR) hB'e⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5x_elemAb_of_frattini {G : Type} [Group G] [Finite G] {D : Subgroup G}
    (hD2 : IsPGroup 2 ↥D) (h : (frattini ↥D).map D.subtype = ⊥) : C5.ElemAb2 D := by
  have hF : CFSG.QuasithinUnique.DoubleA3.frattiniOf D = ⊥ := h
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have h1 := CFSG.QuasithinUnique.DoubleA3.commutator_le_frattiniOf hD2
      (Subgroup.commutator_mem_commutator ha hb)
    rw [hF, Subgroup.mem_bot, commutatorElement_def] at h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · have h1 := AppCS2.sq_mem_frattiniOf hD2 ha
    rwa [hF, Subgroup.mem_bot] at h1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_lin2A3_S1Str (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3)
    (hfr : (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥) :
    burnsideC5x_S1Str R K₁ x := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem hL
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, hx2⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  obtain ⟨⟨hP1a, hP1b⟩, ⟨-, hP2b, -⟩, -⟩ := burnsideC5x_lin2A3_123 h116 hset hx hL
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hR2 : IsPGroup 2 R := hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le
  have hBR : baum R ≤ R := C1GN.baum_le R
  have hB2 : IsPGroup 2 (baum R) := hR2.to_le hBR
  have hD2 : C5.ElemAb2 (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) :=
    burnsideC5x_elemAb_of_frattini (hB2.to_le inf_le_left) hfr
  have hDx : baum R ⊓ Subgroup.centralizer (K₁ : Set G) ≤
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x := by
    rw [hrk.conj_Q_eq hxB]
    intro d hd
    exact ⟨hd.1, (hP1b hd).2⟩
  have hDc : ∀ u ∈ blockU K₁, ∀ a ∈ baum R ⊓ Subgroup.centralizer (K₁ : Set G), u * a = a * u :=
    fun u hu a ha => Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu)
  have hA : ∀ A, IsMaxElemAbelian R A → A ≤ baum R := fun A hA =>
    (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ R).trans (C5.thompsonJ_le_baum' R)
  obtain ⟨hQmax, hQxmax, hQxeq, hall, hBeq, hJ⟩ := hrk.A_R_structure hBR hA hq2
    (C1.blockU_sq hshort) hxB hx1 hx2 hP1a hDc hD2 hDx
  have hAF : AFam R = {pCoreOf 2 (K₁ ⊔ baum R), conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x} := by
    ext A
    exact hall A
  refine ⟨hQmax, fun A hA' _ => (hall A).mp hA', ?_, hP2b, fun _ => ?_, fun h5 => ?_⟩
  · intro heq
    have heq' : conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x = pCoreOf 2 (K₁ ⊔ baum R) := heq
    apply hx1
    have := C5.conjSubgroup_mono hrk.U_le_Q x
    rw [heq'] at this
    exact this
  · rw [burnsideC5x_AFam_eq hBR hA]
    exact hAF
  · exfalso
    rcases hL with ⟨n, hn, hl⟩ | h3
    · exact AppC.not_lin2_of_alt5 hshort h5 hn hl
    · exact AppC.not_alt3_of_alt5 h5 h3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_c57_assembly {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hmax : IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (K₁ : Set G)))
    (hex : ∃ x : G, GoodX H M₀ K₁ x)
    (hP4 : ∀ x : G, GoodX H M₀ K₁ x → burnsideC5x_P4 R K₁ x)
    (hSt : ∀ x : G, GoodX H M₀ K₁ x →
      (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥ →
      burnsideC5x_S1Str R K₁ x) :
    (M₀ ⊓ Subgroup.normalizer (K₁ : Set G)).relIndex M₀ = 2 ∧
    (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥ ∧
    (∀ x ∈ M₀, x ∉ Subgroup.normalizer (K₁ : Set G) →
      (baum R : Set G) = (pCoreOf 2 (K₁ ⊔ baum R) : Set G) *
        (rconj x (pCoreOf 2 (K₁ ⊔ baum R)) : Set G)) ∧
    (((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) →
      ∀ x ∈ M₀, x ∉ Subgroup.normalizer (K₁ : Set G) →
        AFam (baum R) = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R))}) ∧
    (IsAltType K₁ 5 →
      ∀ x ∈ M₀, x ∉ Subgroup.normalizer (K₁ : Set G) →
        ∃ (A : Subgroup G) (r : G), r ∈ R ⊓ K₁ ∧ r ∉ baum R ∧
          AFam R = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R)), A,
            rconj r A}) := by
  obtain ⟨x₀, hx₀⟩ := hex
  have hfr := burnsideC5x_c57_frattini hset hs1 hmax hx₀ (hP4 x₀ hx₀)
  obtain ⟨hQmax, hinv, hne, hSQ, hd, he⟩ := hSt x₀ hx₀ hfr
  obtain ⟨hTHN, hK, hHeq⟩ := burnsideC5x_s1_facts hset hs1
  have hyp1 := hset.hyp1
  set Q := pCoreOf 2 (K₁ ⊔ baum R) with hQ
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hNQ : ∀ m ∈ Subgroup.normalizer (K₁ : Set G), m ∈ Subgroup.normalizer (R : Set G) →
      m ∈ Subgroup.normalizer (Q : Set G) := fun m hmK hmR =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K₁ ⊔ baum R)
      (C1.mem_normalizer_sup hmK (normalizer_le_normalizer_baum R hmR))
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := fun r hr =>
    hNQ r (hTHN (hyp1.R_le hr)) (Subgroup.le_normalizer hr)
  have hΓ : ∀ m ∈ M₀, conjSubgroup Q m = Q ∨ conjSubgroup Q m = conjSubgroup Q x₀ := by
    intro m hm
    have hmR : m ∈ Subgroup.normalizer (R : Set G) := hyp1.R_norm hm
    exact hinv _ (C56.isMaxElemAbelian_conjSubgroup hQmax hmR) (C5.le_normalizer_conj hmR hRQ)
  have hne' : conjSubgroup Q x₀ ≠ Q := hne
  set N := M₀ ⊓ Subgroup.normalizer (K₁ : Set G) with hN
  set M := M₀ ⊓ Subgroup.normalizer (Q : Set G) with hM
  have hNM : N ≤ M := fun n hn => ⟨hn.1, hNQ n hn.2 (hyp1.R_norm hn.1)⟩
  have hx₀M : x₀ ∉ M := fun h => hne' (C5.conjSubgroup_eq_self h.2)
  have hNeq : N = M := by
    by_contra hneq
    have hlt : N < M := lt_of_le_of_ne hNM hneq
    have hMeq : M = M₀ := hmax.2 M hlt inf_le_left
    apply hx₀M
    rw [hMeq]
    exact hx₀.1
  have hx₀N : x₀ ∉ N := hNeq ▸ hx₀M
  have hconj : ∀ m ∈ M₀, m ∉ N → conjSubgroup Q m = conjSubgroup Q x₀ := by
    intro m hm hmN
    rcases hΓ m hm with h | h
    · exact absurd (hNeq ▸ (⟨hm, CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h⟩ : m ∈ M)) hmN
    · exact h
  have hsq : x₀ * x₀ ∈ N := by
    have hx₀sq : x₀ * x₀ ∈ M₀ := mul_mem hx₀.1 hx₀.1
    by_contra hcon
    have h1 := hconj _ hx₀sq hcon
    apply hne'
    have h2 : conjSubgroup (conjSubgroup Q x₀) x₀ = conjSubgroup Q x₀ := by
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]; exact h1
    have h3 := congrArg (fun A => conjSubgroup A x₀⁻¹) h2
    simp only [C5.conjSubgroup_conjSubgroup_inv] at h3
    exact h3
  have hconjK : ∀ x ∈ M₀, x ∉ Subgroup.normalizer (K₁ : Set G) →
      rconj x Q = rconj x₀ Q := fun x hx hxK => hconj x hx fun hxN => hxK hxN.2
  have hidx : N.relIndex M₀ = 2 := by
    show (N.subgroupOf M₀).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x₀, hx₀.1⟩, fun b => ?_⟩
    by_cases hb : (b : G) ∈ N
    · refine Or.inr ⟨Subgroup.mem_subgroupOf.mpr hb, fun h => hx₀N ?_⟩
      have h' : (b : G) * x₀ ∈ N := Subgroup.mem_subgroupOf.mp h
      have := N.mul_mem (N.inv_mem hb) h'
      simpa using this
    · refine Or.inl ⟨Subgroup.mem_subgroupOf.mpr ?_, fun h => hb (Subgroup.mem_subgroupOf.mp h)⟩
      have hb1 := hconj b b.2 hb
      have hQsq : conjSubgroup Q (x₀ * x₀) = Q :=
        CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr (hNeq ▸ hsq).2
      have h2 : conjSubgroup Q ((b : G) * x₀) = Q := by
        rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hb1,
          CFSG.Quasithin.conjSubgroup_conjSubgroup]
        exact hQsq
      have hmem : (b : G) * x₀ ∈ M := ⟨mul_mem b.2 hx₀.1,
        CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h2⟩
      rw [← hNeq] at hmem
      exact hmem
  refine ⟨hidx, hfr, fun x hx hxK => ?_, fun hL x hx hxK => ?_, fun h5 x hx hxK => ?_⟩
  · rw [hconjK x hx hxK]; exact hSQ
  · rw [hconjK x hx hxK]; exact hd hL
  · rw [hconjK x hx hxK]
    obtain ⟨A, r, h1, h2, -, h3⟩ := he h5
    exact ⟨A, r, h1, h2, h3⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_Q_eq_sup_centralizer {G : Type} [Group G] [Finite G] {B Q U K : Subgroup G}
    {q : ℕ} {x : G} (hx : x ∈ Subgroup.normalizer (B : Set G))
    (hQeq : Q = B ⊓ Subgroup.centralizer (U : Set G)) (hUQ : U ≤ Q) (hq0 : q ≠ 0)
    (hq1 : (Q ⊓ conjSubgroup Q x).relIndex Q = q) (hUK : U ≤ K)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hZ : (U ⊓ Subgroup.centralizer (K : Set G)).relIndex U = q ^ 2)
    (hgen : ∃ k ∈ K, K ≤ conjSubgroup U x ⊔ conjSubgroup (conjSubgroup U x) k) :
    Q = U ⊔ (Q ⊓ Subgroup.centralizer (K : Set G)) ∧
      Q ⊓ Subgroup.centralizer (K : Set G) ≤ conjSubgroup Q x := by
  obtain ⟨k, hkK, hgen⟩ := hgen
  have hk : k ∈ Subgroup.normalizer (Q : Set G) := hKQ hkK
  have hQB : Q ≤ B := hQeq ▸ inf_le_left
  have hconjQ : conjSubgroup Q x =
      B ⊓ Subgroup.centralizer ((conjSubgroup U x : Subgroup G) : Set G) := by
    rw [hQeq, C5.conjSubgroup_inf, C5.conjSubgroup_eq_self hx, C5.conjSubgroup_centralizer]
  set X₁ := Q ⊓ conjSubgroup Q x with hX₁
  set C := Q ⊓ Subgroup.centralizer (K : Set G) with hC
  set Y₂ := Q ⊓ Subgroup.centralizer
    ((conjSubgroup (conjSubgroup U x) k : Subgroup G) : Set G) with hY₂
  have hX₁c : X₁ = Q ⊓ Subgroup.centralizer ((conjSubgroup U x : Subgroup G) : Set G) := by
    rw [hX₁, hconjQ]
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hyQ, -, hyc⟩; exact ⟨hyQ, hyc⟩
    · rintro ⟨hyQ, hyc⟩; exact ⟨hyQ, hQB hyQ, hyc⟩
  have hY₂eq : conjSubgroup X₁ k = Y₂ := by
    rw [hX₁c, C5.conjSubgroup_inf, C5.conjSubgroup_eq_self hk, C5.conjSubgroup_centralizer]
  have hq2 : Y₂.relIndex Q = q := by
    have := C5.relIndex_conjSubgroup X₁ Q k
    rwa [C5.conjSubgroup_eq_self hk, hY₂eq, hq1] at this
  have hleC : X₁ ⊓ Y₂ ≤ C := by
    intro c hc
    refine ⟨hc.1.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hcc : c ∈ Subgroup.centralizer ((conjSubgroup U x : Subgroup G) : Set G) := by
      rw [hX₁c] at hc; exact hc.1.2
    have hcc2 : c ∈ Subgroup.centralizer
        ((conjSubgroup (conjSubgroup U x) k : Subgroup G) : Set G) := hc.2.2
    have : conjSubgroup U x ⊔ conjSubgroup (conjSubgroup U x) k ≤
        Subgroup.centralizer ({c} : Set G) := by
      refine sup_le (fun p hp => ?_) (fun p hp => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hcc p hp)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hcc2 p hp)
    exact Subgroup.mem_centralizer_singleton_iff.mp (this (hgen hy))
  have hrel : (X₁ ⊓ Y₂).relIndex Q ≤ q * q := by
    calc (X₁ ⊓ Y₂).relIndex Q ≤ X₁.relIndex Q * Y₂.relIndex Q := Subgroup.relIndex_inf_le
      _ = q * q := by rw [hq1, hq2]
  have hCle : C.relIndex Q ≤ q * q := (C5.relIndex_le_of_le_left hleC Q).trans hrel
  have hUN : U ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    C5.mem_normalizer_inf (hKQ (hUK hg)) (C5.le_normalizer_centralizer_self K (hUK hg))
  have hCU : C ⊓ U = U ⊓ Subgroup.centralizer (K : Set G) := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hyc⟩, hyU⟩; exact ⟨hyU, hyc⟩
    · rintro ⟨hyU, hyc⟩; exact ⟨⟨hUQ hyU, hyc⟩, hyU⟩
  have hb : C.relIndex (U ⊔ C) = q ^ 2 := by
    rw [C5.relIndex_sup_eq_of_le_normalizer hUN, ← Subgroup.inf_relIndex_right C U, hCU, hZ]
  have hsup : U ⊔ C ≤ Q := sup_le hUQ inf_le_left
  have hle : C.relIndex (U ⊔ C) ≤ C.relIndex Q := C5.relIndex_le_of_le le_sup_right hsup
  have hCq : C.relIndex Q = q ^ 2 := le_antisymm (by rw [sq]; exact hCle) (hb ▸ hle)
  have hCfin : C.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite (H := C.subgroupOf Q)
  have hQ : U ⊔ C = Q := C5.eq_of_relIndex_eq le_sup_right hsup (hb.trans hCq.symm) hCfin
  have hmul := Subgroup.relIndex_mul_relIndex (X₁ ⊓ Y₂) C Q hleC inf_le_left
  have hpos : 0 < (X₁ ⊓ Y₂).relIndex C :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (X₁ ⊓ Y₂).subgroupOf C))
  have hqq : 0 < q * q := Nat.mul_pos (Nat.pos_of_ne_zero hq0) (Nat.pos_of_ne_zero hq0)
  have h1 : (X₁ ⊓ Y₂).relIndex C = 1 := by
    rw [hCq, sq] at hmul
    have h3 : (X₁ ⊓ Y₂).relIndex C * (q * q) ≤ 1 * (q * q) := by rw [hmul, one_mul]; exact hrel
    have := Nat.le_of_mul_le_mul_right h3 hqq
    omega
  have hCle' : C ≤ X₁ ⊓ Y₂ := Subgroup.relIndex_eq_one.mp h1
  exact ⟨hQ.symm, hCle'.trans (inf_le_left.trans inf_le_right)⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideC5x_comm_inv_ne {G : Type} [Group G] {U : Subgroup G} {x : G}
    (hne : ⁅U, conjSubgroup U x⁆ ≠ ⊥) : ⁅U, conjSubgroup U x⁻¹⁆ ≠ ⊥ := by
  intro h
  apply hne
  have h2 : conjSubgroup ⁅U, conjSubgroup U x⁻¹⁆ x = conjSubgroup ⊥ x :=
    congrArg (fun A => conjSubgroup A x) h
  rw [C5.conjSubgroup_commutator, C5.conjSubgroup_inv_conjSubgroup] at h2
  have hb : conjSubgroup (⊥ : Subgroup G) x = ⊥ := Subgroup.map_bot _
  rw [hb, Subgroup.commutator_comm] at h2
  exact h2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped commutatorElement in
theorem burnsideC5x_commZ (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G}
    (hKi : Ki ∈ conjSubgroupsBy TH K₁)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type Ki n) ∨ IsAltType Ki 3) :
    ∀ y ∈ baum R, y ∉ pCoreOf 2 (Ki ⊔ baum R) → ∀ u ∈ blockU Ki,
      ⁅u, y⁆ ∈ blockU Ki ⊓ Subgroup.centralizer (Ki : Set G) → ⁅u, y⁆ = 1 := by
  have hshort : IsShort2 Ki := (burnsideC5h_c54_isBlock2 hset hKi).1
  have hP1 := burnsideC5h_p1_minParabolic hset (burnsideC5h_c54_one h116 hset)
  obtain ⟨hsyl, hlin, hA3, hUQ, hQ⟩ := burnsideC5h_p2_lin2A3 h116 hset hP1 Ki hKi hL
  rcases hL with ⟨n, hn, hl⟩ | h3
  · have hset' := hlin ⟨n, hn, hl⟩
    have hBTQ : baum R ≤ (baum R ⊓ Ki) ⊔ pCoreOf 2 (Ki ⊔ baum R) := by
      intro b hb
      have : b ∈ (baum R : Set G) := hb
      rw [hset'] at this
      obtain ⟨t, ht, q, hq, rfl⟩ := this
      exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hq)
    have hLQ : Ki ≤ Subgroup.normalizer (pCoreOf 2 (Ki ⊔ baum R) : Set G) :=
      le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
    exact AppE.lin2_B_commutator_inf_Z hshort (by omega) hl hsyl hQ hBTQ hLQ
  · obtain ⟨-, hU4, -, -, -, hcen, -⟩ := hshort.alt3_structure h3
    have hbot : blockU Ki ⊓ Subgroup.centralizer (Ki : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      refine hcen g ((Setup.Campbell.blockU_le_self_of_isShort2 hshort) hg.1) fun l hl => ?_
      exact (Subgroup.mem_centralizer_iff.mp hg.2 l hl).symm
    intro y hy hyQ u hu hZ
    rw [hbot] at hZ
    exact Subgroup.mem_bot.mp hZ

theorem burnsideC5x_union_subgroups {G : Type} [Group G] {A Q T : Subgroup G}
    (h : ∀ b ∈ A, b ∈ Q ∨ b ∈ T) : A ≤ Q ∨ A ≤ T := by
  by_cases hAQ : A ≤ Q
  · exact Or.inl hAQ
  right
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have haT : a ∈ T := (h a haA).resolve_left haQ
  intro b hbA
  rcases h b hbA with hbQ | hbT
  · have habQ : a * b ∉ Q := fun hab => haQ (by simpa using Q.mul_mem hab (Q.inv_mem hbQ))
    have habT : a * b ∈ T := (h (a * b) (A.mul_mem haA hbA)).resolve_left habQ
    simpa using T.mul_mem (T.inv_mem haT) habT
  · exact hbT

open CFSG.Quasithin CFSG.QuasithinUnique in
open scoped commutatorElement in
theorem burnsideC5x_sq_mem {G : Type} [Group G] [Finite G] {B Q U W D Y Z : Subgroup G} {q : ℕ}
    {x : G} (h : C5.Rank1 B Q U W q) (hx : x ∈ Subgroup.normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hY : ∀ d ∈ D, d ^ 2 ∈ Y) (hUYZ : ∀ u ∈ U, u ∈ Y → u ∈ Z)
    (hcommZ : ∀ y ∈ B, y ∉ Q → ∀ u ∈ U, ⁅u, y⁆ ∈ Z → ⁅u, y⁆ = 1)
    (hDx : ∀ d ∈ D, ∀ v ∈ conjSubgroup U x, d * v = v * d)
    {b : G} (hbB : b ∈ B) (hb2 : b ^ 2 ∈ Y) : b ∈ Q ∨ b ∈ D ⊔ conjSubgroup U x := by
  obtain ⟨u', hu', u₁, hu₁, d, hd, rfl⟩ := h.mem_B_decomp hx hx2 hD hDc hbB
  have hu'B : u' ∈ B := h.conj_le_B hx hu'
  have hu₁B : u₁ ∈ B := h.U_le_B hu₁
  have hdQ : d ∈ Q := hD ▸ Subgroup.mem_sup_right hd
  have hu'2 : u' ^ 2 = 1 := ((C5.ElemAb2.conjSubgroup ⟨h.U_comm, hU2⟩ x)).2 u' hu'
  have hu₁2 := hU2 u₁ hu₁
  have hcd : Commute (u' * u₁) d := by
    have h1 : u' * d = d * u' := (hDx d hd u' hu').symm
    have h2 : u₁ * d = d * u₁ := hDc u₁ hu₁ d hd
    have h1' : Commute u' d := h1
    have h2' : Commute u₁ d := h2
    exact h1'.mul_left h2'
  have hsq : (u' * (u₁ * d)) ^ 2 = (u' * u₁) ^ 2 * d ^ 2 := by
    rw [← mul_assoc]
    exact Commute.mul_pow hcd 2
  have hc2 : (u' * u₁) ^ 2 ∈ Y := by
    have h3 := Y.mul_mem hb2 (Y.inv_mem (hY d hd))
    rw [hsq] at h3
    simpa using h3
  have hinv1 : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu'2)
  have hinv2 : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu₁2)
  have hcomm_eq : ⁅u', u₁⁆ = (u' * u₁) ^ 2 := by
    rw [commutatorElement_def, hinv1, hinv2, pow_two, mul_assoc, mul_assoc, ← mul_assoc u₁]
  have hcU : ⁅u', u₁⁆ ∈ U := by
    have hm : u' * u₁ * u'⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (h.B_le_normU hu'B) u₁).mp hu₁
    rw [commutatorElement_def]
    exact U.mul_mem hm (U.inv_mem hu₁)
  have hZmem : ⁅u', u₁⁆ ∈ Z := hUYZ _ hcU (hcomm_eq ▸ hc2)
  by_cases hu'Q : u' ∈ Q
  · left
    exact Q.mul_mem hu'Q (Q.mul_mem (h.U_le_Q hu₁) hdQ)
  · right
    have hZ' : ⁅u₁, u'⁆ ∈ Z := by
      rw [← commutatorElement_inv u' u₁]
      exact Z.inv_mem hZmem
    have h1 := hcommZ u' hu'B hu'Q u₁ hu₁ hZ'
    have h2 : u₁ * u' = u' * u₁ := by
      rw [commutatorElement_def] at h1
      calc u₁ * u' = (u₁ * u' * u₁⁻¹ * u'⁻¹) * (u' * u₁) := by group
        _ = u' * u₁ := by rw [h1, one_mul]
    have hW : u₁ ∈ W := (h.cent_y u' hu'B hu'Q u₁ hu₁).mpr h2
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hu')
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right (h.W_le_conj hx hx1 hx2 hW))
        (Subgroup.mem_sup_left hd))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise commutatorElement in
theorem burnsideC5x_lin2A3_gamma (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) {m : G}
    (hmB : m ∈ Subgroup.normalizer (baum R : Set G))
    (hmY : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) m =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) :
    conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = pCoreOf 2 (K₁ ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem hL
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, hx2⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  obtain ⟨⟨hP1a, hP1b⟩, -⟩ := burnsideC5x_lin2A3_123 h116 hset hx hL
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hR2 : IsPGroup 2 R := hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le
  have hB2 : IsPGroup 2 (baum R) := hR2.to_le (C1GN.baum_le R)
  set D := baum R ⊓ Subgroup.centralizer (K₁ : Set G) with hDdef
  set Q := pCoreOf 2 (K₁ ⊔ baum R) with hQdef
  set Y := CFSG.QuasithinUnique.DoubleA3.frattiniOf D with hYdef
  have hDx : ∀ d ∈ D, ∀ v ∈ conjSubgroup (blockU K₁) x, d * v = v * d := by
    intro d hd v hv
    have h1 := hP1b hd
    exact (Subgroup.mem_centralizer_iff.mp h1.2 v hv).symm
  have hDc : ∀ u ∈ blockU K₁, ∀ a ∈ D, u * a = a * u := fun u hu a ha =>
    Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu)
  have hD2 : IsPGroup 2 ↥D := hB2.to_le inf_le_left
  have hY : ∀ d ∈ D, d ^ 2 ∈ Y := fun d hd => AppCS2.sq_mem_frattiniOf hD2 hd
  have hYD : Y ≤ D := Subgroup.map_subtype_le _
  have hUYZ : ∀ u ∈ blockU K₁, u ∈ Y → u ∈ blockU K₁ ⊓ Subgroup.centralizer (K₁ : Set G) :=
    fun u hu huY => ⟨hu, (hYD huY).2⟩
  have hcommZ := burnsideC5x_commZ h116 hset hK₁mem hL
  have hsqmem : ∀ b ∈ baum R, b ^ 2 ∈ Y → b ∈ Q ∨ b ∈ D ⊔ conjSubgroup (blockU K₁) x := fun b hb hb2 =>
    burnsideC5x_sq_mem hrk hxB hx1 hx2 hP1a hDc (C1.blockU_sq hshort) hY hUYZ hcommZ hDx hb hb2
  have hDUx : D ⊓ conjSubgroup (blockU K₁) x = D ⊓ blockU K₁ := by
    apply le_antisymm
    · intro y hy
      have hyQ : y ∈ Q := hP1a ▸ Subgroup.mem_sup_right hy.1
      have : y ∈ conjSubgroup (blockU K₁) x ⊓ Q := ⟨hy.2, hyQ⟩
      rw [hrk.inf_Q_conj hxB hx2, hrk.conj_W hxB hx1 hx2] at this
      exact ⟨hy.1, hrk.W_le_U this⟩
    · intro y hy
      refine ⟨hy.1, ?_⟩
      have hyc : y ∈ Subgroup.centralizer ((conjSubgroup (blockU K₁) x : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun v hv => (hDx y hy.1 v hv).symm
      have : y ∈ blockU K₁ ⊓ Subgroup.centralizer ((conjSubgroup (blockU K₁) x : Subgroup G) : Set G) :=
        ⟨hy.2, hyc⟩
      rw [hrk.inf_centralizer_conj hxB hx1] at this
      exact hrk.W_le_conj hxB hx1 hx2 this
  have hcardT : Nat.card ↥(D ⊔ conjSubgroup (blockU K₁) x) = Nat.card ↥Q := by
    have e1 := B2F.card_sup_mul_card_inf_of_commute
      (A := D) (B := conjSubgroup (blockU K₁) x) hDx
    have e2 := B2F.card_sup_mul_card_inf_of_commute
      (A := blockU K₁) (B := D) hDc
    rw [hDUx, C5.card_conjSubgroup] at e1
    rw [inf_comm] at e2
    have hpos : 0 < Nat.card ↥(D ⊓ blockU K₁) := Nat.card_pos
    rw [← hP1a] at e2
    have : Nat.card ↥(D ⊔ conjSubgroup (blockU K₁) x) * Nat.card ↥(D ⊓ blockU K₁) =
        Nat.card ↥Q * Nat.card ↥(D ⊓ blockU K₁) := by
      rw [e1, mul_comm (Nat.card ↥D), e2]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hTQx : D ⊔ conjSubgroup (blockU K₁) x ≤ conjSubgroup Q x := by
    refine sup_le (fun d hd => ?_) (C5.conjSubgroup_mono hrk.U_le_Q x)
    rw [hrk.conj_Q_eq hxB]
    exact ⟨hd.1, (hP1b hd).2⟩
  have hTQx' : D ⊔ conjSubgroup (blockU K₁) x = conjSubgroup Q x :=
    Subgroup.eq_of_le_of_card_ge hTQx (by rw [hcardT, C5.card_conjSubgroup])
  have hQm : ∀ b ∈ conjSubgroup Q m, b ∈ Q ∨ b ∈ D ⊔ conjSubgroup (blockU K₁) x := by
    intro b hb
    have hbB : b ∈ baum R := by
      have := C5.conjSubgroup_mono hrk.Q_le_B m
      rw [C5.conjSubgroup_eq_self hmB] at this
      exact this hb
    refine hsqmem b hbB ?_
    have hb' : m * b * m⁻¹ ∈ Q := mem_conjSubgroup_iff.1 hb
    obtain ⟨u, hu, d, hd, hud⟩ := C5.mem_sup_of_commute hDc (hP1a ▸ hb')
    have h2 : (m * b * m⁻¹) ^ 2 = d ^ 2 := by
      rw [hud]
      have hc : Commute u d := hDc u hu d hd
      rw [hc.mul_pow, C1.blockU_sq hshort u hu, one_mul]
    have hb2 : b ^ 2 ∈ conjSubgroup Y m := by
      rw [mem_conjSubgroup_iff]
      have : m * b ^ 2 * m⁻¹ = (m * b * m⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
      rw [this, h2]
      exact hY d hd
    rwa [hmY] at hb2
  rcases burnsideC5x_union_subgroups hQm with h | h
  · left
    exact Subgroup.eq_of_le_of_card_ge h (by rw [C5.card_conjSubgroup])
  · right
    rw [← hTQx']
    exact Subgroup.eq_of_le_of_card_ge h (by rw [hcardT, C5.card_conjSubgroup])

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise commutatorElement in
theorem burnsideC5x_even_of_sq {G : Type} [Group G] [Finite G] {Q : Subgroup G} {x : G}
    (hne : conjSubgroup Q x ≠ Q) (hsq : x * x ∈ Subgroup.normalizer (Q : Set G)) :
    Even (orderOf x) := by
  rcases Nat.even_or_odd (orderOf x) with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := h
    apply hne
    apply C5.conjSubgroup_eq_self
    have hx : x = (x * x) ^ (k + 1) := by
      have h1 : x ^ (orderOf x) = 1 := pow_orderOf_eq_one x
      calc x = x ^ (orderOf x + 1) := by rw [pow_succ, h1, one_mul]
        _ = (x * x) ^ (k + 1) := by rw [hk, ← pow_two, ← pow_mul]; congr 1
    rw [hx]
    exact Subgroup.pow_mem _ hsq _

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise commutatorElement in
theorem burnsideC5x_lin2A3_5 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) : Even (orderOf x) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem hL
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, hx2⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  have h4 := burnsideC5x_lin2A3_4 h116 hset hx hL
  have hY1 : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) x =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) := h4
  have hY2 : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) (x * x) =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hY1, hY1]
  have hne : conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x ≠ pCoreOf 2 (K₁ ⊔ baum R) := by
    intro heq
    apply hx1
    have := C5.conjSubgroup_mono hrk.U_le_Q x
    rw [heq] at this
    exact this
  refine burnsideC5x_even_of_sq hne ?_
  rcases burnsideC5x_lin2A3_gamma h116 hset hx hL (m := x * x) (mul_mem hxB hxB) hY2 with h | h
  · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h
  · exfalso
    apply hne
    have h2 : conjSubgroup (conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) (x * x)) x⁻¹ =
        conjSubgroup (conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x) x⁻¹ :=
      congrArg (fun A => conjSubgroup A x⁻¹) h
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_right,
      C5.conjSubgroup_conjSubgroup_inv] at h2
    exact h2

section A5

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.QuasithinUnique.A5.Delta5
open scoped commutatorElement

structure burnsideC5x_A5Cfg {G : Type} [Group G] [Finite G] (R K : Subgroup G) where
  short : IsShort2 K
  alt5 : IsAltType K 5
  R2 : IsPGroup 2 R
  RN : R ≤ Subgroup.normalizer (K : Set G)
  P : AppC.A5Pi K
  hB : P.im (baum R) = Estd
  hR : P.im R = Dstd
  hX : P.im (K ⊔ baum R) = ⊤
  Q_eq : pCoreOf 2 (K ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU K : Set G)
  Q_UD : pCoreOf 2 (K ⊔ baum R) = blockU K ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G))
  U_inf_D : blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) = ⊥

theorem burnsideC5x_a5_std {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (h : burnsideC5h_p3_Setting L S) (P : AppC.A5Pi L) :
    ∃ P' : AppC.A5Pi L, P'.im (baum S) = Estd ∧ P'.im S = Dstd ∧ P'.im (L ⊔ baum S) = ⊤ := by
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq, hD8, -, htop, hJn, -⟩ :=
    burnsideC5h_p3_a5_core h P
  obtain ⟨ρ, hρ1, hρ2⟩ := swaps_conj τ₁ τ₂ hτ₁ hτ₂ hdisj
  have hcl : (Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5)))).map
      (MulAut.conj ρ).toMonoidHom = Estd := by
    rw [MonoidHom.map_closure, ← closure_swaps]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · exact Or.inl hρ1
      · exact Or.inr hρ2
    · rintro (rfl | rfl)
      · exact ⟨τ₁, Or.inl rfl, hρ1⟩
      · exact ⟨τ₂, Or.inr rfl, hρ2⟩
  have hJ' : (P.conj ρ).im (thompsonJ S) = Estd := by rw [AppC.A5Pi.im_conj, hJeq, hcl]
  have hB' : (P.conj ρ).im (baum S) = Estd := by rw [AppC.A5Pi.im_conj, hBeq, hcl]
  have hnorm' : ∀ d ∈ (P.conj ρ).im S, ∀ j ∈ (P.conj ρ).im (thompsonJ S),
      d * j * d⁻¹ ∈ (P.conj ρ).im (thompsonJ S) := by
    intro d hd j hj'
    rw [AppC.A5Pi.im_conj] at hd hj' ⊢
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.1 hj'
    refine Subgroup.mem_map.2 ⟨d₀ * j₀ * d₀⁻¹, hJn d₀ hd₀ j₀ hj₀, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hle : (P.conj ρ).im S ≤ Dstd := by
    intro d hd
    rw [mem_Dstd, mem_Dset]
    intro x hx
    have := hnorm' d hd x (by rw [hJ']; exact hx)
    rwa [hJ'] at this
  have hcard : Nat.card ((P.conj ρ).im S) = 8 := by
    rw [AppC.A5Pi.im_conj, Subgroup.card_map_of_injective (MulAut.conj ρ).injective, hD8]
  refine ⟨P.conj ρ, hB', ?_, ?_⟩
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [Dstd_card, hcard])
  · rw [AppC.A5Pi.im_conj, htop, Subgroup.map_top_of_surjective _ (MulAut.conj ρ).surjective]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_a5cfg (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hRN : R ≤ Subgroup.normalizer (K₁ : Set G)) (h5 : IsAltType K₁ 5) :
    Nonempty (burnsideC5x_A5Cfg R K₁) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  have hyp1 := hset.hyp1
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hR2 : IsPGroup 2 R := hyp1.sylow.2.1.to_le hyp1.R_le
  have hsyl : IsSylowTwoOf R (K₁ ⊔ R) := by
    have := burnsideC5h_p3_sylow hset hK₁mem
    rwa [inf_eq_left.mpr hRN] at this
  have hsetting : burnsideC5h_p3_Setting K₁ R :=
    ⟨hshort, h5, hRN, hsyl, hset.config.comm_J⟩
  obtain ⟨P⟩ := AppC.nonempty_a5pi hshort h5
  obtain ⟨P', hB, hR, hX⟩ := burnsideC5x_a5_std hsetting P
  obtain ⟨⟨⟨hQUD, hUD, -⟩, -, -⟩, -, hQeq⟩ :=
    burnsideC5h_p3_a5_unconditional h116 hset K₁ hK₁mem h5
  exact ⟨⟨hshort, h5, hR2, hRN, P', hB, hR, hX, hQeq, hQUD, hUD⟩⟩

theorem burnsideC5x_card_fix_normal (K : Subgroup (Equiv.Perm (Fin 5))) (hK : K ≤ Estd)
    (hne : K ≠ ⊥) (hnorm : ∀ d ∈ Dstd, ∀ g ∈ K, d * g * d⁻¹ ∈ K) :
    Nat.card (AppC.FixΔ K) = 4 := by
  have hsq : ∀ a ∈ K, a * a = 1 := fun a ha => AppC.Eset_sq a ((mem_Estd a).1 (hK ha))
  have hcm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    AppC.Eset_comm a ((mem_Estd a).1 (hK ha)) b ((mem_Estd b).1 (hK hb))
  obtain ⟨a, haK, b, hbK, hab, -, hfix⟩ := AppC.exists_four_card K hsq hcm
  have haE := (mem_Estd a).1 (hK haK)
  have hbE := (mem_Estd b).1 (hK hbK)
  have h1 : AppC.four a b ≠ {1} := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro g hg
    have := (hab g).1 hg
    rw [h, Finset.mem_singleton] at this
    simp [this]
  have h2 : ∀ d ∈ Dset, ∀ g ∈ AppC.four a b, d * g * d⁻¹ ∈ AppC.four a b := by
    intro d hd g hg
    exact (hab _).1 (hnorm d ((mem_Dstd d).2 hd) g ((hab g).2 hg))
  rw [hfix]
  have key : ∀ a ∈ Eset, ∀ b ∈ Eset, AppC.four a b ≠ {1} →
      (∀ d ∈ Dset, ∀ g ∈ AppC.four a b, d * g * d⁻¹ ∈ AppC.four a b) →
        (AppC.fixOf a b).card = 4 := by decide +kernel
  exact key a haE b hbE h1 h2

theorem burnsideC5x_closure_four :
    Subgroup.closure ({Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 1 2, Equiv.swap 3 4} :
      Set (Equiv.Perm (Fin 5))) = ⊤ := by
  apply top_unique
  intro σ _
  have h := Equiv.Perm.mclosure_swap_castSucc_succ 4
  have hσ : σ ∈ Submonoid.closure
      (Set.range fun i : Fin 4 => Equiv.swap i.castSucc i.succ) := by rw [h]; trivial
  have hle : Submonoid.closure (Set.range fun i : Fin 4 => Equiv.swap i.castSucc i.succ) ≤
      (Subgroup.closure ({Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 1 2, Equiv.swap 3 4} :
        Set (Equiv.Perm (Fin 5)))).toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  exact hle hσ

theorem burnsideC5x_E_sup_conj :
    Estd ⊔ Estd.map (MulAut.conj (finRotate 5)).toMonoidHom = ⊤ := by
  have e1 : (finRotate 5) * Equiv.swap 0 1 * (finRotate 5)⁻¹ = Equiv.swap 1 2 := by decide +kernel
  have e2 : (finRotate 5) * Equiv.swap 2 3 * (finRotate 5)⁻¹ = Equiv.swap 3 4 := by decide +kernel
  have h1 : Estd.map (MulAut.conj (finRotate 5)).toMonoidHom =
      Subgroup.closure ({Equiv.swap 1 2, Equiv.swap 3 4} : Set (Equiv.Perm (Fin 5))) := by
    rw [← closure_swaps, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, e1, e2]
  rw [h1, ← closure_swaps, ← Subgroup.closure_union, ← burnsideC5x_closure_four]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

@[expose] def burnsideC5x_YCls {G : Type} [Group G] (Y A : Subgroup G) : Prop :=
  (∀ a ∈ A, a ^ 2 ∈ Y) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ Y

theorem burnsideC5x_normal_E (K : Subgroup (Equiv.Perm (Fin 5))) (hK : K ≤ Estd)
    (hnorm : ∀ d ∈ Dstd, ∀ g ∈ K, d * g * d⁻¹ ∈ K) :
    Nat.card K = 1 ∨ Nat.card K = 4 ∨ Nat.card K * Nat.card (AppC.FixΔ K) < 16 := by
  have hsq : ∀ a ∈ K, a * a = 1 := fun a ha => AppC.Eset_sq a ((mem_Estd a).1 (hK ha))
  have hcm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    AppC.Eset_comm a ((mem_Estd a).1 (hK ha)) b ((mem_Estd b).1 (hK hb))
  obtain ⟨a, haK, b, hbK, hab, hcard, hfix⟩ := AppC.exists_four_card K hsq hcm
  have haE := (mem_Estd a).1 (hK haK)
  have hbE := (mem_Estd b).1 (hK hbK)
  have h2 : ∀ d ∈ Dset, ∀ g ∈ AppC.four a b, d * g * d⁻¹ ∈ AppC.four a b := by
    intro d hd g hg
    exact (hab _).1 (hnorm d ((mem_Dstd d).2 hd) g ((hab g).2 hg))
  have key : ∀ a ∈ Eset, ∀ b ∈ Eset,
      (∀ d ∈ Dset, ∀ g ∈ AppC.four a b, d * g * d⁻¹ ∈ AppC.four a b) →
        (AppC.four a b).card = 1 ∨ (AppC.four a b).card = 4 ∨
          (AppC.four a b).card * (AppC.fixOf a b).card < 16 := by decide +kernel
  rw [hcard, hfix]
  exact key a haE b hbE h2

theorem burnsideC5x_YCls_conj {G : Type} [Group G] {Y A : Subgroup G}
    (h : burnsideC5x_YCls Y A) (y : G) :
    burnsideC5x_YCls (conjSubgroup Y y) (conjSubgroup A y) := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · rw [mem_conjSubgroup_iff] at ha ⊢
    have : y * a ^ 2 * y⁻¹ = (y * a * y⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
    rw [this]
    exact h.1 _ ha
  · rw [mem_conjSubgroup_iff] at ha hb ⊢
    have : y * (a * b * a⁻¹ * b⁻¹) * y⁻¹ =
        (y * a * y⁻¹) * (y * b * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * b * y⁻¹)⁻¹ := by group
    rw [this]
    exact h.2 _ ha _ hb

theorem burnsideC5x_YCls_of_UD {G : Type} [Group G] [Finite G] {Q U D : Subgroup G}
    (hQ : Q = U ⊔ D) (hUc : ∀ q ∈ Q, ∀ u ∈ U, q * u = u * q) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hUD : ∀ u ∈ U, ∀ d ∈ D, u * d = d * u) (hD2 : IsPGroup 2 ↥D) :
    burnsideC5x_YCls (CFSG.QuasithinUnique.DoubleA3.frattiniOf D) Q := by
  have hDQ : D ≤ Q := hQ ▸ le_sup_right
  have h1 : ∀ q ∈ Q, ∀ u ∈ U, u * q * u⁻¹ = q := fun q hq u hu => by
    have := hUc q hq u hu
    calc u * q * u⁻¹ = (q * u) * u⁻¹ := by rw [this]
      _ = q := by group
  constructor
  · intro a ha
    rw [hQ] at ha
    obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute hUD ha
    have hc : Commute u d := hUD u hu d hd
    rw [hc.mul_pow, hU2 u hu, one_mul]
    exact AppCS2.sq_mem_frattiniOf hD2 hd
  · intro a ha b hb
    rw [hQ] at ha hb
    obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute hUD ha
    obtain ⟨u', hu', d', hd', rfl⟩ := C5.mem_sup_of_commute hUD hb
    have hdQ : d ∈ Q := hDQ hd
    have hd'Q : d' ∈ Q := hDQ hd'
    have hgQ : d * (u' * d') * d⁻¹ ∈ Q := by
      have hu'Q : u' ∈ Q := hQ ▸ Subgroup.mem_sup_left hu'
      exact Q.mul_mem (Q.mul_mem hdQ (Q.mul_mem hu'Q hd'Q)) (Q.inv_mem hdQ)
    have hcQ : d * d' * d⁻¹ * d'⁻¹ ∈ Q :=
      Q.mul_mem (Q.mul_mem (Q.mul_mem hdQ hd'Q) (Q.inv_mem hdQ)) (Q.inv_mem hd'Q)
    have e : (u * d) * (u' * d') * (u * d)⁻¹ * (u' * d')⁻¹ = d * d' * d⁻¹ * d'⁻¹ := by
      have hdu : d * u' = u' * d := hUc d hdQ u' hu'
      calc (u * d) * (u' * d') * (u * d)⁻¹ * (u' * d')⁻¹
          = u * (d * (u' * d') * d⁻¹) * u⁻¹ * (u' * d')⁻¹ := by group
        _ = (d * (u' * d') * d⁻¹) * (u' * d')⁻¹ := by rw [h1 _ hgQ u hu]
        _ = u' * (d * d' * d⁻¹ * d'⁻¹) * u'⁻¹ := by
          calc d * (u' * d') * d⁻¹ * (u' * d')⁻¹ = (d * u') * d' * d⁻¹ * d'⁻¹ * u'⁻¹ := by group
            _ = (u' * d) * d' * d⁻¹ * d'⁻¹ * u'⁻¹ := by rw [hdu]
            _ = u' * (d * d' * d⁻¹ * d'⁻¹) * u'⁻¹ := by group
        _ = d * d' * d⁻¹ * d'⁻¹ := h1 _ hcQ u' hu'
    rw [e]
    have := CFSG.QuasithinUnique.DoubleA3.commutator_le_frattiniOf hD2
      (Subgroup.commutator_mem_commutator hd hd')
    rwa [commutatorElement_def] at this

theorem burnsideC5x_relIndex_two {G : Type} [Group G] [Finite G] {M₁ Q : Subgroup G} {x : G}
    (hx : x ∈ M₁) (hne : conjSubgroup Q x ≠ Q)
    (hΓ : ∀ m ∈ M₁, conjSubgroup Q m = Q ∨ conjSubgroup Q m = conjSubgroup Q x) :
    (M₁ ⊓ Subgroup.normalizer (Q : Set G)).relIndex M₁ = 2 := by
  set N := M₁ ⊓ Subgroup.normalizer (Q : Set G) with hN
  have hx₀N : x ∉ N := fun h => hne (C5.conjSubgroup_eq_self h.2)
  have hsq : x * x ∈ N := by
    have hxsq : x * x ∈ M₁ := mul_mem hx hx
    refine ⟨hxsq, ?_⟩
    rcases hΓ _ hxsq with h | h
    · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h
    · exfalso
      apply hne
      have h2 : conjSubgroup (conjSubgroup Q (x * x)) x⁻¹ =
          conjSubgroup (conjSubgroup Q x) x⁻¹ := congrArg (fun A => conjSubgroup A x⁻¹) h
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_right,
        C5.conjSubgroup_conjSubgroup_inv] at h2
      exact h2
  show (N.subgroupOf M₁).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hx⟩, fun b => ?_⟩
  by_cases hb : (b : G) ∈ N
  · refine Or.inr ⟨Subgroup.mem_subgroupOf.mpr hb, fun h => hx₀N ?_⟩
    have h' : (b : G) * x ∈ N := Subgroup.mem_subgroupOf.mp h
    have := N.mul_mem (N.inv_mem hb) h'
    simpa using this
  · refine Or.inl ⟨Subgroup.mem_subgroupOf.mpr ?_, fun h => hb (Subgroup.mem_subgroupOf.mp h)⟩
    have hb1 : conjSubgroup Q b = conjSubgroup Q x := (hΓ b b.2).resolve_left fun h =>
      hb ⟨b.2, CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h⟩
    have hQsq : conjSubgroup Q (x * x) = Q :=
      CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hsq.2
    have h2 : conjSubgroup Q ((b : G) * x) = Q := by
      rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hb1,
        CFSG.Quasithin.conjSubgroup_conjSubgroup]
      exact hQsq
    exact ⟨mul_mem b.2 hx, CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h2⟩

namespace burnsideC5x_A5Cfg

variable {G : Type} [Group G] [Finite G] {R K : Subgroup G} (C : burnsideC5x_A5Cfg R K)

include C in
theorem hBR : baum R ≤ R := C1GN.baum_le R

include C in
theorem hBN : baum R ≤ Subgroup.normalizer (K : Set G) := C.hBR.trans C.RN

include C in
theorem hU : IsElemAbelian 2 (blockU K) := AppC.isElemAbelian_blockU C.short

include C in
theorem card_U : Nat.card ↥(blockU K) = 16 := C.P.card_blockU

include C in
theorem hUQ : blockU K ≤ pCoreOf 2 (K ⊔ baum R) := C.Q_UD ▸ le_sup_left

include C in
theorem hQB : pCoreOf 2 (K ⊔ baum R) ≤ baum R := C.Q_eq ▸ inf_le_left

include C in
theorem hUB : blockU K ≤ baum R := C.hUQ.trans C.hQB

include C in
theorem hDQ : baum R ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 (K ⊔ baum R) :=
  C.Q_UD ▸ le_sup_right

include C in
theorem hRU : R ≤ Subgroup.normalizer (blockU K : Set G) := fun r hr =>
  C1.mem_normalizer_blockU (C.RN hr)

include C in
theorem Q_comm_U {q u : G} (hq : q ∈ pCoreOf 2 (K ⊔ baum R)) (hu : u ∈ blockU K) :
    q * u = u * q := by
  have : q ∈ baum R ⊓ Subgroup.centralizer (blockU K : Set G) := C.Q_eq ▸ hq
  exact (Subgroup.mem_centralizer_iff.mp this.2 u hu).symm

include C in
theorem U_comm_D {u d : G} (hu : u ∈ blockU K) (hd : d ∈ baum R ⊓ Subgroup.centralizer (K : Set G)) :
    u * d = d * u :=
  (Subgroup.mem_centralizer_iff.mp hd.2 u (Setup.Campbell.blockU_le_self_of_isShort2 C.short hu))

include C in
theorem mem_Q_iff {a : G} (haB : a ∈ baum R) :
    a ∈ pCoreOf 2 (K ⊔ baum R) ↔ C.P.pf a = 1 := by
  have haN : a ∈ Subgroup.normalizer (K : Set G) := C.hBN haB
  rw [C.Q_eq, C.P.pf_eq haN, C.P.hker ⟨a, haN⟩]
  constructor
  · rintro ⟨-, hc⟩ u hu
    have := Subgroup.mem_centralizer_iff.mp hc u hu
    calc a * u * a⁻¹ = (u * a) * a⁻¹ := by rw [this]
      _ = u := by group
  · intro h
    refine ⟨haB, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have := h u hu
    calc u * a = (a * u * a⁻¹) * a := by rw [this]
      _ = a * u := by group

include C in
theorem im_le {A : Subgroup G} (hA : A ≤ baum R) : C.P.im A ≤ Estd := by
  rw [← C.hB]; exact C.P.im_mono hA

include C in
theorem card_Q : Nat.card ↥(pCoreOf 2 (K ⊔ baum R)) =
    16 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  have h := B2F.card_sup_mul_card_inf_of_commute
    (fun u hu d hd => C.U_comm_D hu hd :
      ∀ u ∈ blockU K, ∀ d ∈ baum R ⊓ Subgroup.centralizer (K : Set G), u * d = d * u)
  rw [C.U_inf_D, Subgroup.card_bot, C.card_U] at h
  rw [C.Q_UD]
  omega

include C in
theorem card_fix_of_normalized {A : Subgroup G} (hAB : A ≤ baum R)
    (hRA : R ≤ Subgroup.normalizer (A : Set G)) (hne : C.P.im A ≠ ⊥) :
    Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) = 4 := by
  rw [C.P.card_fix (hAB.trans C.hBN)]
  refine burnsideC5x_card_fix_normal _ (C.im_le hAB) hne ?_
  intro d hd g hg
  rw [← C.hR] at hd
  obtain ⟨r, hr, rfl⟩ := (C.P.mem_im).1 hd
  obtain ⟨a, ha, rfl⟩ := (C.P.mem_im).1 hg
  refine (C.P.mem_im).2 ⟨r * a * r⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.mp (hRA hr) a).mp ha
  simpa using this

include C in
theorem im_ne_bot {A : Subgroup G} (hAB : A ≤ baum R)
    (hAQ : ¬ A ≤ pCoreOf 2 (K ⊔ baum R)) : C.P.im A ≠ ⊥ := by
  intro hbot
  apply hAQ
  intro a ha
  have h1 : C.P.pf a ∈ C.P.im A := (C.P.mem_im_pf (hAB.trans C.hBN)).2 ⟨a, ha, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (C.mem_Q_iff (hAB ha)).2 h1

include C in
theorem conj_le_B {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G)) :
    conjSubgroup (blockU K) x ≤ baum R := by
  have := C5.conjSubgroup_mono C.hUB x
  rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum R hxR)] at this

include C in
theorem card_conj_inf {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    Nat.card ↥(conjSubgroup (blockU K) x ⊓ Subgroup.centralizer (blockU K : Set G)) = 4 := by
  have hxiB : x⁻¹ ∈ Subgroup.normalizer (baum R : Set G) :=
    inv_mem (normalizer_le_normalizer_baum R hxR)
  obtain ⟨-, hx2⟩ := burnsideC5x_not_le_Q C.Q_eq hne
  have hVB' : conjSubgroup (blockU K) x⁻¹ ≤ baum R := by
    have := C5.conjSubgroup_mono C.hUB x⁻¹
    rwa [C5.conjSubgroup_eq_self hxiB] at this
  have hRV' := C5.le_normalizer_conj (inv_mem hxR) C.hRU
  have h4 := C.card_fix_of_normalized hVB' hRV' (C.im_ne_bot hVB' hx2)
  rw [← h4, ← C5.card_conjSubgroup (blockU K ⊓
    Subgroup.centralizer ((conjSubgroup (blockU K) x⁻¹ : Subgroup G) : Set G)) x,
    C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_inv_conjSubgroup]

include C in
theorem im_conj_eq {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    C.P.im (conjSubgroup (blockU K) x) = Estd := by
  have hVB := C.conj_le_B hxR
  have h5 := C.card_conj_inf hxR hne
  have h6 := C.P.card_im_mul (hVB.trans C.hBN)
  rw [h5, C5.card_conjSubgroup, C.card_U] at h6
  have h7 : Nat.card (C.P.im (conjSubgroup (blockU K) x)) = 4 := by omega
  exact Subgroup.eq_of_le_of_card_ge (C.im_le hVB) (by rw [h7, Estd_card])

include C in
theorem sup_Q_conj {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    conjSubgroup (blockU K) x ⊔ pCoreOf 2 (K ⊔ baum R) = baum R := by
  have hVB := C.conj_le_B hxR
  refine le_antisymm (sup_le hVB C.hQB) fun b hb => ?_
  have hbE : C.P.pf b ∈ C.P.im (conjSubgroup (blockU K) x) := by
    rw [C.im_conj_eq hxR hne, ← C.hB]
    exact (C.P.mem_im_pf C.hBN).2 ⟨b, hb, rfl⟩
  obtain ⟨v, hv, hvb⟩ := (C.P.mem_im_pf (hVB.trans C.hBN)).1 hbE
  have hq : v⁻¹ * b ∈ pCoreOf 2 (K ⊔ baum R) := by
    refine (C.mem_Q_iff (mul_mem (inv_mem (hVB hv)) hb)).2 ?_
    rw [C.P.pf_mul (inv_mem (C.hBN (hVB hv))) (C.hBN hb), C.P.pf_inv (C.hBN (hVB hv)), hvb,
      inv_mul_cancel]
  have : b = v * (v⁻¹ * b) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hq)

theorem burnsideC5x_fix_comm_E : ∀ σ ∈ Eset, ∀ τ ∈ Eset, ∀ w : Fin 5 → ZMod 2,
    pact τ (w + pact σ w) = w + pact σ w := by decide +kernel

include C in
theorem bf_comm {u b : G} (hu : u ∈ blockU K) (hb : b ∈ baum R) :
    C.P.bf (u * b * u⁻¹ * b⁻¹) = C.P.bf u + vact (C.P.pf b) (C.P.bf u) := by
  have hU2 := C1.blockU_sq C.short
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2 u hu)
  have hbN := C.hBN hb
  have hm : b * u⁻¹ * b⁻¹ ∈ blockU K := AppC.PiData.conj_mem_U hbN (inv_mem hu)
  have e : u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) := by group
  rw [e, C.P.bf_mul hu hm, C.P.bf_conj hbN (inv_mem hu), hinv]

include C in
theorem comm_UB_eq : ⁅blockU K, baum R⁆ = blockU K ⊓ Subgroup.centralizer (baum R : Set G) := by
  have hU2 := C1.blockU_sq C.short
  have hinvU : ∀ u ∈ blockU K, u⁻¹ = u := fun u hu =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2 u hu)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u hu b hb
    have hbN := C.hBN hb
    have hm : b * u⁻¹ * b⁻¹ ∈ blockU K := AppC.PiData.conj_mem_U hbN (inv_mem hu)
    have hcU : ⁅u, b⁆ ∈ blockU K := by
      have e : ⁅u, b⁆ = u * (b * u⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]; exact mul_mem hu hm
    refine ⟨hcU, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyN := C.hBN hy
    have hc := C.bf_comm hu hb
    have : ⁅u, b⁆ = u * b * u⁻¹ * b⁻¹ := rfl
    have hσB : C.P.pf b ∈ C.P.im (baum R) := (C.P.mem_im_pf C.hBN).2 ⟨b, hb, rfl⟩
    have hτB : C.P.pf y ∈ C.P.im (baum R) := (C.P.mem_im_pf C.hBN).2 ⟨y, hy, rfl⟩
    rw [C.hB] at hσB hτB
    have hσ : C.P.pf b ∈ Eset := (mem_Estd _).1 hσB
    have hτ : C.P.pf y ∈ Eset := (mem_Estd _).1 hτB
    refine (C.P.comm_iff hyN hcU).2 ?_
    rw [this, hc]
    apply Subtype.ext
    exact burnsideC5x_fix_comm_E _ hσ _ hτ (C.P.bf u).1
  · intro u hu
    obtain ⟨huU, huC⟩ := hu
    have hfix : ∀ σ ∈ Eset, pact σ (C.P.bf u).1 = (C.P.bf u).1 := by
      intro σ hσ
      have : σ ∈ C.P.im (baum R) := by rw [C.hB]; exact (mem_Estd _).2 hσ
      obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf C.hBN).1 this
      have h1 := (C.P.comm_iff (C.hBN hy) huU).1
        (Subgroup.mem_centralizer_iff.1 huC y hy)
      exact congrArg Subtype.val h1
    obtain ⟨t, htE, w, hwe, hw⟩ := AppC.fix_comm _ (C.P.bf u).2 hfix
    have htB : t ∈ C.P.im (baum R) := by rw [C.hB]; exact (mem_Estd _).2 htE
    obtain ⟨b, hb, hbt⟩ := (C.P.mem_im_pf C.hBN).1 htB
    obtain ⟨u₀, hu₀, hu₀w⟩ := C.P.bf_surj ⟨w, (mem_evenWeight_iff w).2 hwe⟩
    have hc := C.bf_comm hu₀ hb
    have hcU : b * u₀ * b⁻¹ * u₀⁻¹ ∈ blockU K := by
      have hm : b * u₀ * b⁻¹ ∈ blockU K := AppC.PiData.conj_mem_U (C.hBN hb) hu₀
      exact mul_mem hm (inv_mem hu₀)
    have hbf : C.P.bf (b * u₀ * b⁻¹ * u₀⁻¹) = C.P.bf u := by
      have hinv : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2 u₀ hu₀)
      have hm : b * u₀ * b⁻¹ ∈ blockU K := AppC.PiData.conj_mem_U (C.hBN hb) hu₀
      rw [C.P.bf_mul hm (inv_mem hu₀), C.P.bf_conj (C.hBN hb) hu₀, hinv, hbt, hu₀w]
      apply Subtype.ext
      show pact t w + w = (C.P.bf u).1
      exact hw
    have heq : b * u₀ * b⁻¹ * u₀⁻¹ = u := C.P.bf_inj hcU huU hbf
    rw [Subgroup.commutator_comm]
    rw [← heq]
    exact Subgroup.commutator_mem_commutator hb hu₀

include C in
theorem hBU : baum R ≤ Subgroup.normalizer (blockU K : Set G) := fun b hb =>
  C1.mem_normalizer_blockU (C.hBN hb)

include C in
theorem card_W : Nat.card ↥(blockU K ⊓ Subgroup.centralizer (baum R : Set G)) = 4 := by
  refine C.card_fix_of_normalized le_rfl (fun r hr =>
    normalizer_le_normalizer_baum R (Subgroup.le_normalizer hr)) ?_
  rw [C.hB]
  intro h
  have := Estd_card
  rw [h, Subgroup.card_bot] at this
  omega

include C in
theorem inf_C_conj {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    blockU K ⊓ Subgroup.centralizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) =
      blockU K ⊓ Subgroup.centralizer (baum R : Set G) := by
  have hVB := C.conj_le_B hxR
  apply le_antisymm
  · rintro u ⟨huU, huC⟩
    refine ⟨huU, ?_⟩
    have hle : conjSubgroup (blockU K) x ⊔ pCoreOf 2 (K ⊔ baum R) ≤
        Subgroup.centralizer ({u} : Set G) := by
      refine sup_le (fun v hv => ?_) (fun q hq => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp huC v hv)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (C.Q_comm_U hq huU)
    rw [C.sup_Q_conj hxR hne] at hle
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  · rintro u ⟨huU, huC⟩
    exact ⟨huU, Subgroup.centralizer_le hVB huC⟩

include C in
theorem hBQ : baum R ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ baum R) : Set G) :=
  le_sup_right.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)

include C in
theorem conj_Q_eq {x : G} (hxB : x ∈ Subgroup.normalizer (baum R : Set G)) :
    conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x =
      baum R ⊓ Subgroup.centralizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := by
  rw [C.Q_eq, C5.conjSubgroup_inf, C5.conjSubgroup_eq_self hxB, C5.conjSubgroup_centralizer]

include C in
theorem idx_Q : (pCoreOf 2 (K ⊔ baum R)).relIndex (baum R) = 4 := by
  have h1 := C.P.card_im_mul (C.hBN)
  rw [C.hB, Estd_card, ← C.Q_eq] at h1
  have h2 := C5.card_eq_card_mul_relIndex C.hQB
  have hpos : 0 < Nat.card ↥(pCoreOf 2 (K ⊔ baum R)) := Nat.card_pos
  have : Nat.card ↥(pCoreOf 2 (K ⊔ baum R)) * 4 =
      Nat.card ↥(pCoreOf 2 (K ⊔ baum R)) *
        (pCoreOf 2 (K ⊔ baum R)).relIndex (baum R) := by
    rw [← h2, ← h1]; ring
  exact (Nat.eq_of_mul_eq_mul_left hpos this).symm

include C in
theorem idx_W : (blockU K ⊓ Subgroup.centralizer (baum R : Set G)).relIndex (blockU K) = 4 := by
  have h2 := C5.card_eq_card_mul_relIndex
    (inf_le_left : blockU K ⊓ Subgroup.centralizer (baum R : Set G) ≤ blockU K)
  rw [C.card_U, C.card_W] at h2
  omega

include C in
theorem commutator_conj {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    ⁅blockU K, conjSubgroup (blockU K) x⁆ =
        blockU K ⊓ Subgroup.centralizer (baum R : Set G) ∧
      blockU K ⊓ conjSubgroup (blockU K) x =
        blockU K ⊓ Subgroup.centralizer (baum R : Set G) := by
  have hxB : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hxR
  have hVB := C.conj_le_B hxR
  have hBV : baum R ≤ Subgroup.normalizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) :=
    C5.le_normalizer_conj hxB C.hBU
  have hVN : conjSubgroup (blockU K) x ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ baum R) : Set G) :=
    hVB.trans C.hBQ
  have hle1 : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≤
      blockU K ⊓ Subgroup.centralizer (baum R : Set G) :=
    C.comm_UB_eq ▸ Subgroup.commutator_mono le_rfl hVB
  have hle2 : blockU K ⊓ Subgroup.centralizer (baum R : Set G) ≤
      ⁅blockU K, conjSubgroup (blockU K) x⁆ := by
    rw [← C.comm_UB_eq, Subgroup.commutator_le]
    intro u hu b hb
    have hbmem : b ∈ ((conjSubgroup (blockU K) x ⊔ pCoreOf 2 (K ⊔ baum R) : Subgroup G) :
        Set G) := by rw [C.sup_Q_conj hxR hne]; exact hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN] at hbmem
    obtain ⟨a, ha, q', hq', rfl⟩ := hbmem
    have hc : Commute q' u := (C.Q_comm_U hq' hu)
    have e : ⁅u, a * q'⁆ = ⁅u, a⁆ := by
      have h1 : q' * u⁻¹ = u⁻¹ * q' := (Commute.inv_right hc).eq
      calc ⁅u, a * q'⁆ = u * a * (q' * u⁻¹) * q'⁻¹ * a⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = u * a * (u⁻¹ * q') * q'⁻¹ * a⁻¹ := by rw [h1]
        _ = ⁅u, a⁆ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hu ha
  have hWeq : ⁅blockU K, conjSubgroup (blockU K) x⁆ =
      blockU K ⊓ Subgroup.centralizer (baum R : Set G) := le_antisymm hle1 hle2
  refine ⟨hWeq, le_antisymm ?_ ?_⟩
  · intro u hu
    rw [← C.inf_C_conj hxR hne]
    refine ⟨hu.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact ((C1.elemAb2_blockU C.short).conjSubgroup x).1 y hy u hu.2
  · intro w hw
    have hw' : w ∈ ⁅blockU K, conjSubgroup (blockU K) x⁆ := hWeq ▸ hw
    refine ⟨hw.1, ?_⟩
    have : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≤ conjSubgroup (blockU K) x := by
      rw [Subgroup.commutator_le]
      intro u hu a ha
      have hUV : u ∈ Subgroup.normalizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) :=
        hBV (C.hUB hu)
      have h1 : u * a * u⁻¹ ∈ conjSubgroup (blockU K) x :=
        (Subgroup.mem_normalizer_iff.mp hUV a).mp ha
      have h2 : u * a * u⁻¹ * a⁻¹ ∈ conjSubgroup (blockU K) x :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ha)
      simpa [commutatorElement_def, mul_assoc] using h2
    exact this hw'

include C in
theorem conj_W {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    conjSubgroup (blockU K ⊓ Subgroup.centralizer (baum R : Set G)) x =
      blockU K ⊓ Subgroup.centralizer (baum R : Set G) := by
  have hxB : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hxR
  have hVB := C.conj_le_B hxR
  obtain ⟨hc1, hc2⟩ := C.commutator_conj hxR hne
  have hWV : blockU K ⊓ Subgroup.centralizer (baum R : Set G) ≤ conjSubgroup (blockU K) x := by
    rw [← hc2]; exact inf_le_right
  have hWQ : blockU K ⊓ Subgroup.centralizer (baum R : Set G) ≤
      conjSubgroup (blockU K) x ⊓ Subgroup.centralizer (blockU K : Set G) :=
    le_inf hWV (fun w hw => Subgroup.centralizer_le C.hUB hw.2)
  have hcard : conjSubgroup (blockU K) x ⊓ Subgroup.centralizer (blockU K : Set G) =
      blockU K ⊓ Subgroup.centralizer (baum R : Set G) :=
    (Subgroup.eq_of_le_of_card_ge hWQ (by rw [C.card_W, C.card_conj_inf hxR hne])).symm
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_eq_self hxB]
  apply le_antisymm
  · intro w hw
    have hwU : w ∈ conjSubgroup (blockU K) x ⊓ Subgroup.centralizer (blockU K : Set G) :=
      ⟨hw.1, Subgroup.centralizer_le C.hUB hw.2⟩
    rw [hcard] at hwU
    exact hwU
  · intro w hw
    exact ⟨hWV hw, hw.2⟩

include C in
theorem relIndex_inf_conj {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
        (pCoreOf 2 (K ⊔ baum R)) = 4 ∧
      blockU K ⊔ (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) =
        pCoreOf 2 (K ⊔ baum R) := by
  have hxB : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hxR
  have hQx_le : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x ≤ baum R := by
    rw [C.conj_Q_eq hxB]; exact inf_le_left
  have hBQx : baum R ≤ Subgroup.normalizer
      ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x : Subgroup G) : Set G) :=
    C5.le_normalizer_conj hxB C.hBQ
  have hQN : pCoreOf 2 (K ⊔ baum R) ≤ Subgroup.normalizer
      ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x : Subgroup G) : Set G) := C.hQB.trans hBQx
  have hA : (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
      (pCoreOf 2 (K ⊔ baum R)) ≤ 4 := by
    have e1 : (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
        (pCoreOf 2 (K ⊔ baum R)) = (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
          (pCoreOf 2 (K ⊔ baum R) ⊔ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) :=
      C5.relIndex_inf_eq_of_le_normalizer hQN
    have e2 : (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex (baum R) = 4 := by
      have := C5.relIndex_conjSubgroup (pCoreOf 2 (K ⊔ baum R)) (baum R) x
      rwa [C5.conjSubgroup_eq_self hxB, C.idx_Q] at this
    rw [e1, ← e2]
    exact C5.relIndex_le_of_le le_sup_right (sup_le C.hQB hQx_le)
  have hCU : (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) ⊓ blockU K =
      blockU K ⊓ Subgroup.centralizer (baum R : Set G) := by
    refine le_antisymm ?_ ?_
    · rintro v ⟨⟨-, hvQx⟩, hvU⟩
      rw [← C.inf_C_conj hxR hne]
      refine ⟨hvU, ?_⟩
      rw [C.conj_Q_eq hxB] at hvQx
      exact hvQx.2
    · intro w hw
      have hwU : w ∈ blockU K := hw.1
      have hw' : w ∈ blockU K ⊓ Subgroup.centralizer
          ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := by
        rw [C.inf_C_conj hxR hne]; exact hw
      refine ⟨⟨C.hUQ hwU, ?_⟩, hwU⟩
      rw [C.conj_Q_eq hxB]
      exact ⟨C.hUB hwU, hw'.2⟩
  have hUC : blockU K ≤ Subgroup.normalizer
      ((pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x : Subgroup G) :
        Set G) := fun g hg =>
    C5.mem_normalizer_inf (C.hBQ (C.hUB hg)) (hBQx (C.hUB hg))
  have hb : (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
      (blockU K ⊔ (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x)) = 4 := by
    rw [C5.relIndex_sup_eq_of_le_normalizer hUC,
      ← Subgroup.inf_relIndex_right (pCoreOf 2 (K ⊔ baum R) ⊓
        conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) (blockU K), hCU, C.idx_W]
  have hsup : blockU K ⊔ (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) ≤
      pCoreOf 2 (K ⊔ baum R) := sup_le C.hUQ inf_le_left
  have hle : (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
      (blockU K ⊔ (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x)) ≤
      (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
        (pCoreOf 2 (K ⊔ baum R)) := C5.relIndex_le_of_le le_sup_right hsup
  have hq : (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).relIndex
      (pCoreOf 2 (K ⊔ baum R)) = 4 := le_antisymm hA (hb ▸ hle)
  refine ⟨hq, C5.eq_of_relIndex_eq le_sup_right hsup (hb.trans hq.symm) ?_⟩
  exact Subgroup.index_ne_zero_of_finite
    (H := (pCoreOf 2 (K ⊔ baum R) ⊓ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x).subgroupOf
      (pCoreOf 2 (K ⊔ baum R)))

include C in
theorem im_conjSubgroup {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (K : Set G)) {k : G}
    (hk : k ∈ Subgroup.normalizer (K : Set G)) :
    C.P.im (conjSubgroup A k) = (C.P.im A).map (MulAut.conj (C.P.pf k)⁻¹).toMonoidHom := by
  have hAk : conjSubgroup A k ≤ Subgroup.normalizer (K : Set G) := by
    have := C5.conjSubgroup_mono hA k
    rwa [C5.conjSubgroup_normalizer, C5.conjSubgroup_eq_self hk] at this
  ext σ
  rw [Subgroup.mem_map]
  constructor
  · intro hσ
    obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hAk).1 hσ
    have hyN := hAk hy
    have hya : k * y * k⁻¹ ∈ A := mem_conjSubgroup_iff.1 hy
    refine ⟨C.P.pf (k * y * k⁻¹), (C.P.mem_im_pf hA).2 ⟨_, hya, rfl⟩, ?_⟩
    rw [C.P.pf_mul (mul_mem hk hyN) (inv_mem hk), C.P.pf_mul hk hyN, C.P.pf_inv hk]
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (C.P.mem_im_pf hA).1 hτ
    have haN := hA ha
    have hyk : k⁻¹ * a * k ∈ conjSubgroup A k := by
      rw [mem_conjSubgroup_iff]
      have : k * (k⁻¹ * a * k) * k⁻¹ = a := by group
      rw [this]; exact ha
    refine (C.P.mem_im_pf hAk).2 ⟨k⁻¹ * a * k, hyk, ?_⟩
    rw [C.P.pf_mul (mul_mem (inv_mem hk) haN) hk, C.P.pf_mul (inv_mem hk) haN, C.P.pf_inv hk]
    simp [MulAut.conj_apply, mul_assoc]

include C in
theorem exists_k {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    ∃ k ∈ K, K ≤ conjSubgroup (blockU K) x ⊔ conjSubgroup (conjSubgroup (blockU K) x) k := by
  have hxB : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hxR
  have hVB := C.conj_le_B hxR
  have hgalt : (finRotate 5)⁻¹ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
  obtain ⟨ℓ, hℓ⟩ := C.P.hα ⟨(finRotate 5)⁻¹, hgalt⟩
  have hkK : (ℓ : G) ∈ K := ℓ.2
  have hkN : (ℓ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have hpk : C.P.pf (ℓ : G) = (finRotate 5)⁻¹ := by
    rw [C.P.pf_eq hkN]
    have := C.P.hπα (ℓ : G) ℓ.2
    rw [this, hℓ]
  refine ⟨ℓ, hkK, ?_⟩
  set k : G := (ℓ : G) with hk
  set V := conjSubgroup (blockU K) x with hV
  have hVN : V ≤ Subgroup.normalizer (K : Set G) := hVB.trans C.hBN
  have hVkN : conjSubgroup V k ≤ Subgroup.normalizer (K : Set G) := by
    have := C5.conjSubgroup_mono hVN k
    rwa [C5.conjSubgroup_normalizer, C5.conjSubgroup_eq_self hkN] at this
  set L' := V ⊔ conjSubgroup V k with hL'
  have hLN : L' ≤ Subgroup.normalizer (K : Set G) := sup_le hVN hVkN
  have himV : C.P.im V = Estd := C.im_conj_eq hxR hne
  have himVk : C.P.im (conjSubgroup V k) = Estd.map (MulAut.conj (finRotate 5)).toMonoidHom := by
    rw [C.im_conjSubgroup hVN hkN, himV, hpk, inv_inv]
  have hLtop : C.P.im L' = ⊤ := by
    have h1 : C.P.im V ⊔ C.P.im (conjSubgroup V k) ≤ C.P.im L' :=
      sup_le (C.P.im_mono le_sup_left) (C.P.im_mono le_sup_right)
    rw [himV, himVk, burnsideC5x_E_sup_conj] at h1
    exact eq_top_iff.2 h1
  have hKBk : conjSubgroup (K ⊔ baum R) k = K ⊔ baum R :=
    C5.conjSubgroup_eq_self (Subgroup.le_normalizer (Subgroup.mem_sup_left hkK))
  have hL'KB : L' ≤ K ⊔ baum R := by
    refine sup_le (hVB.trans le_sup_right) ?_
    have := C5.conjSubgroup_mono (hVB.trans (le_sup_right : baum R ≤ K ⊔ baum R)) k
    rwa [hKBk] at this
  have hB2 : IsPGroup 2 (baum R) := C.R2.to_le C.hBR
  have hXN : K ⊔ baum R ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer C.hBN
  have hXeq : (K ⊔ baum R) ⊓ Subgroup.centralizer (blockU K : Set G) = pCoreOf 2 (K ⊔ baum R) :=
    C1.inf_centralizer_blockU_eq C.short le_sup_left hXN
      (fun g hg => C1.exists_pow_mem_of_mem_sup hB2 C.hBN hg)
  have hKLQ : K ≤ L' ⊔ pCoreOf 2 (K ⊔ baum R) := by
    intro g₀ hg₀
    have hg₀N : g₀ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hg₀
    have h1 : C.P.pf g₀ ∈ C.P.im L' := by rw [hLtop]; trivial
    obtain ⟨l, hl, hlg⟩ := (C.P.mem_im_pf hLN).1 h1
    have hlN := hLN hl
    have hz : g₀ * l⁻¹ ∈ (K ⊔ baum R) ⊓ Subgroup.centralizer (blockU K : Set G) := by
      have hg₀KB : g₀ ∈ K ⊔ baum R := Subgroup.mem_sup_left hg₀
      have hlKB : l⁻¹ ∈ K ⊔ baum R := (K ⊔ baum R).inv_mem (hL'KB hl)
      refine ⟨(K ⊔ baum R).mul_mem hg₀KB hlKB, ?_⟩
      have hzN : g₀ * l⁻¹ ∈ Subgroup.normalizer (K : Set G) := mul_mem hg₀N (inv_mem hlN)
      have hpz : C.P.pf (g₀ * l⁻¹) = 1 := by
        rw [C.P.pf_mul hg₀N (inv_mem hlN), C.P.pf_inv hlN, hlg, mul_inv_cancel]
      have h2 := (C.P.hker ⟨g₀ * l⁻¹, hzN⟩).1 (by rw [← C.P.pf_eq hzN]; exact hpz)
      refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      have := h2 u hu
      calc u * (g₀ * l⁻¹) = ((g₀ * l⁻¹) * u * (g₀ * l⁻¹)⁻¹) * (g₀ * l⁻¹) := by rw [this]
        _ = (g₀ * l⁻¹) * u := by group
    rw [hXeq] at hz
    have : g₀ = (g₀ * l⁻¹) * l := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hl)
  have hkQ : k ∈ Subgroup.normalizer (pCoreOf 2 (K ⊔ baum R) : Set G) :=
    (le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _))
      hkK
  have hBV : baum R ≤ Subgroup.normalizer (V : Set G) := C5.le_normalizer_conj hxB C.hBU
  have hQV : pCoreOf 2 (K ⊔ baum R) ≤ Subgroup.normalizer (V : Set G) := C.hQB.trans hBV
  have hQL : pCoreOf 2 (K ⊔ baum R) ≤ Subgroup.normalizer (L' : Set G) := fun q hq =>
    C1.mem_normalizer_sup (hQV hq) (C5.le_normalizer_conj hkQ hQV hq)
  exact C56.le_of_le_sup_isPGroup C.short (hB2.to_le C.hQB) hQL hKLQ

include C in
theorem part123 {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    burnsideC5x_P1 R K x ∧ burnsideC5x_P2 R K x ∧ burnsideC5x_P3 R K x := by
  have hxB : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hxR
  have hVB := C.conj_le_B hxR
  have hUK : blockU K ≤ K := (C1.blockU_le_blockQ C.short).trans (C1.blockQ_le K)
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ baum R) : Set G) :=
    le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  have hZ : (blockU K ⊓ Subgroup.centralizer (K : Set G)).relIndex (blockU K) = 4 ^ 2 := by
    have h0 : blockU K ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
      AppC.blockZ_eq_bot_of_alt5 C.short C.alt5
    rw [h0, Subgroup.relIndex_bot_left, C.card_U]
    norm_num
  obtain ⟨hD, hDx⟩ := burnsideC5x_Q_eq_sup_centralizer hxB C.Q_eq C.hUQ (q := 4) (by norm_num)
    (C.relIndex_inf_conj hxR hne).1 hUK hKQ hZ (C.exists_k hxR hne)
  have hQC : pCoreOf 2 (K ⊔ baum R) ⊓ Subgroup.centralizer (K : Set G) =
      baum R ⊓ Subgroup.centralizer (K : Set G) := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hy, hc⟩
      exact ⟨C.hQB hy, hc⟩
    · rintro ⟨hy, hc⟩
      refine ⟨?_, hc⟩
      rw [C.Q_eq]
      exact ⟨hy, Subgroup.centralizer_le hUK hc⟩
  have hVN : conjSubgroup (blockU K) x ≤ Subgroup.normalizer
      (pCoreOf 2 (K ⊔ baum R) : Set G) := hVB.trans C.hBQ
  have e1 := C.sup_Q_conj hxR hne
  obtain ⟨hc1, hc2⟩ := C.commutator_conj hxR hne
  have hc3 := C.inf_C_conj hxR hne
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hQC]; exact hD
  · intro d hd
    rw [← hQC] at hd
    have h1 := hDx hd
    rw [C.conj_Q_eq hxB] at h1
    exact ⟨hd.1, h1.2⟩
  · have := Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup (blockU K) x)
      (pCoreOf 2 (K ⊔ baum R)) hVN
    rw [e1] at this
    exact this
  · have hQN : pCoreOf 2 (K ⊔ baum R) ≤ Subgroup.normalizer
        ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x : Subgroup G) : Set G) :=
      C.hQB.trans (C5.le_normalizer_conj hxB C.hBQ)
    have := Subgroup.coe_mul_of_left_le_normalizer_right (pCoreOf 2 (K ⊔ baum R))
      (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) hQN
    have hsup : pCoreOf 2 (K ⊔ baum R) ⊔ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x = baum R := by
      refine le_antisymm (sup_le C.hQB ?_) ?_
      · rw [C.conj_Q_eq hxB]; exact inf_le_left
      · calc baum R = conjSubgroup (blockU K) x ⊔ pCoreOf 2 (K ⊔ baum R) := e1.symm
          _ ≤ _ := sup_le (le_sup_of_le_right (C5.conjSubgroup_mono C.hUQ x)) le_sup_left
    rw [hsup] at this
    exact this
  · exact C.comm_UB_eq.trans hc1.symm
  · exact hc1.trans hc3.symm
  · exact hc3.trans hc2.symm
  · show conjSubgroup ⁅blockU K, baum R⁆ x = ⁅blockU K, baum R⁆
    rw [C.comm_UB_eq]; exact C.conj_W hxR hne

include C in
theorem part4 {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) : burnsideC5x_P4 R K x := by
  have hxB : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hxR
  have hVB := C.conj_le_B hxR
  obtain ⟨⟨hP1a, -⟩, -⟩ := C.part123 hxR hne
  have hB2 : IsPGroup 2 (baum R) := C.R2.to_le C.hBR
  have hUK : blockU K ≤ K := (C1.blockU_le_blockQ C.short).trans (C1.blockQ_le K)
  have hQxB : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x ≤ baum R := by
    rw [C.conj_Q_eq hxB]; exact inf_le_left
  obtain ⟨-, hQC⟩ := C.relIndex_inf_conj hxR hne
  obtain ⟨-, hQxC⟩ := C.relIndex_inf_conj (inv_mem hxR) (burnsideC5x_comm_inv_ne hne)
  have hQxC' : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x =
      conjSubgroup (blockU K) x ⊔ (pCoreOf 2 (K ⊔ baum R) ⊓
        conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) := by
    have h2 := congrArg (fun A => conjSubgroup A x) hQxC
    simp only [C5.conjSubgroup_sup, C5.conjSubgroup_inf, CFSG.Quasithin.conjSubgroup_conjSubgroup,
      inv_mul_cancel, CFSG.Quasithin.conjSubgroup_one] at h2
    rw [inf_comm] at h2
    exact h2.symm
  have hD : baum R ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 (K ⊔ baum R) := C.hDQ
  exact burnsideC5x_frattini_symm (hB2.to_le C.hQB) (hB2.to_le hQxB)
    (C1.elemAb2_blockU C.short) hD inf_le_left inf_le_right hP1a
    (fun u hu d hd => C.U_comm_D hu hd) hQC.symm
    (fun u hu c hc => (C.Q_comm_U hc.1 hu).symm) hQxC'
    (fun u hu c hc => by
      have h1 : c ∈ baum R ⊓ Subgroup.centralizer
          ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := by
        rw [← C.conj_Q_eq hxB]; exact hc.2
      exact Subgroup.mem_centralizer_iff.mp h1.2 u hu)

include C in
theorem V_inf_C {x : G} (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥) :
    conjSubgroup (blockU K) x ⊓ Subgroup.centralizer (blockU K : Set G) =
      blockU K ⊓ Subgroup.centralizer (baum R : Set G) := by
  obtain ⟨hc1, hc2⟩ := C.commutator_conj hxR hne
  have hWV : blockU K ⊓ Subgroup.centralizer (baum R : Set G) ≤ conjSubgroup (blockU K) x := by
    rw [← hc2]; exact inf_le_right
  have hWQ : blockU K ⊓ Subgroup.centralizer (baum R : Set G) ≤
      conjSubgroup (blockU K) x ⊓ Subgroup.centralizer (blockU K : Set G) :=
    le_inf hWV (fun w hw => Subgroup.centralizer_le C.hUB hw.2)
  exact (Subgroup.eq_of_le_of_card_ge hWQ (by rw [C.card_W, C.card_conj_inf hxR hne])).symm

include C in
theorem conj_mem_D {s d : G} (hs : s ∈ baum R) (hd : d ∈ baum R ⊓ Subgroup.centralizer (K : Set G)) :
    s * d * s⁻¹ ∈ baum R ⊓ Subgroup.centralizer (K : Set G) :=
  (Subgroup.mem_normalizer_iff.mp (C5.mem_normalizer_inf
    (Subgroup.le_normalizer hs) (C5.mem_normalizer_centralizer (C.hBN hs))) d).mp hd

include C in
theorem exists_UD {q : G} (hq : q ∈ pCoreOf 2 (K ⊔ baum R)) :
    ∃ u ∈ blockU K, ∃ d ∈ baum R ⊓ Subgroup.centralizer (K : Set G), q = u * d := by
  rw [C.Q_UD] at hq
  exact C5.mem_sup_of_commute (fun u hu d hd => C.U_comm_D hu hd) hq

include C in
theorem UD_unique {u u' d d' : G} (hu : u ∈ blockU K) (hu' : u' ∈ blockU K)
    (hd : d ∈ baum R ⊓ Subgroup.centralizer (K : Set G))
    (hd' : d' ∈ baum R ⊓ Subgroup.centralizer (K : Set G)) (h : u * d = u' * d') :
    u = u' ∧ d = d' := by
  have h1 : u'⁻¹ * u = d' * d⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * d) * d⁻¹ := by group
      _ = u'⁻¹ * (u' * d') * d⁻¹ := by rw [h]
      _ = d' * d⁻¹ := by group
  have hU : u'⁻¹ * u ∈ blockU K := mul_mem (inv_mem hu') hu
  have hD : u'⁻¹ * u ∈ baum R ⊓ Subgroup.centralizer (K : Set G) := by
    rw [h1]
    exact mul_mem hd' (inv_mem hd)
  have h2 : u'⁻¹ * u ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) := ⟨hU, hD⟩
  rw [C.U_inf_D, Subgroup.mem_bot] at h2
  have hue : u = u' := by
    calc u = u' * (u'⁻¹ * u) := by group
      _ = u' := by rw [h2, mul_one]
  refine ⟨hue, ?_⟩
  subst hue
  exact mul_left_cancel h

include C in
theorem aU_spec {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAB : A ≤ baum R) :
    IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (blockU K : Set G)) ⊔ blockU K) ∧
      Nat.card ↥A ≤ Nat.card ↥((A ⊓ Subgroup.centralizer (blockU K : Set G)) ⊔ blockU K) ∧
      (A ⊓ Subgroup.centralizer (blockU K : Set G)) ⊔ blockU K ≤ pCoreOf 2 (K ⊔ baum R) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAB.trans C.hBN
  set K' := A ⊓ Subgroup.centralizer (blockU K : Set G) with hK'
  have hKe : IsElemAbelian 2 K' := B2F.isElemAbelian_mono inf_le_left hA
  have hcomm : ∀ k ∈ K', ∀ u ∈ blockU K, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hB1e := B2F.isElemAbelian_sup_of_commute hKe C.hU hcomm
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(K' ⊓ blockU K) ≤
      Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA ha hx.1.1
  have h4 := C.P.card_im_mul hAN
  have h5 := C.P.card_fix hAN
  have h6 := C.card_U
  have h7 := AppC.card_mul_fix_le (C.P.im A) (C.P.im_elemAbelian hA).1 (C.P.im_elemAbelian hA).2
  have hbpos : 0 < Nat.card ↥(K' ⊓ blockU K) := Nat.card_pos
  rw [h5] at h3
  set p := Nat.card (C.P.im A)
  set f := Nat.card (AppC.FixΔ (C.P.im A))
  set b := Nat.card ↥(K' ⊓ blockU K)
  set a := Nat.card ↥(K' ⊔ blockU K)
  set k := Nat.card ↥K'
  have h8 : Nat.card A ≤ a := by
    rw [← h4]
    have hab : a * b = k * 16 := by rw [h2, h6]
    have h9 : (k * p) * b ≤ a * b := by
      calc (k * p) * b ≤ (k * p) * f := Nat.mul_le_mul_left _ h3
        _ = k * (p * f) := by ring
        _ ≤ k * 16 := Nat.mul_le_mul_left _ h7
        _ = a * b := hab.symm
    have := Nat.le_of_mul_le_mul_right h9 hbpos
    nlinarith
  refine ⟨hB1e, h8, sup_le ?_ C.hUQ⟩
  intro x hx
  rw [C.Q_eq]
  exact ⟨hAB hx.1, hx.2⟩

include C in
theorem Q_isMax' (hQ : C5.ElemAb2 (pCoreOf 2 (K ⊔ baum R))) :
    IsMaxElemAbelian (baum R) (pCoreOf 2 (K ⊔ baum R)) :=
  ⟨C.hQB, C5.isElemAbelian_two_iff.mpr hQ, fun B' hBB hBe => by
    obtain ⟨-, hcard, hle⟩ := C.aU_spec hBe hBB
    exact hcard.trans (Subgroup.card_le_of_le hle)⟩

include C in
theorem exists_r (hsyl : IsSylowTwoOf (R ⊓ K) K) : ∃ r ∈ R ⊓ K, C.P.pf r ∉ Eset := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpc : pCoreOf 2 K ≤ R ⊓ K := B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  set T : Subgroup ↥K := (R ⊓ K).subgroupOf K with hT
  have hT2 : IsPGroup 2 ↥T := hsyl.2.1.comap_of_injective K.subtype K.subtype_injective
  have hker : C.P.α.ker ≤ T := fun y hy => by
    rw [C.P.hαk] at hy; exact hpc ⟨y, hy, rfl⟩
  have hT'2 : IsPGroup 2 ↥(T.map C.P.α) := hT2.map C.P.α
  have hidx : (T.map C.P.α).index = T.index := by
    rw [Subgroup.index_map, sup_eq_left.mpr hker, MonoidHom.range_eq_top.mpr C.P.hα,
      Subgroup.index_top, mul_one]
  have hodd : ¬ 2 ∣ (T.map C.P.α).index := by rw [hidx]; exact hsyl.2.2
  have h60 := Subgroup.card_mul_index (T.map C.P.α)
  rw [AppC.card_alt5] at h60
  obtain ⟨n, hn⟩ := hT'2.exists_card_eq
  rw [hn] at h60
  have hn2 : n = 2 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso
      interval_cases n
      · simp at h60; omega
      · simp at h60; omega
    · by_contra hne
      have h3 : 3 ≤ n := by omega
      have h8 : 8 ∣ 60 := by
        have : 2 ^ 3 ∣ 2 ^ n * (T.map C.P.α).index := Dvd.dvd.mul_right (pow_dvd_pow 2 h3) _
        rw [h60] at this; simpa using this
      omega
  have hcard4 : Nat.card ↥(T.map C.P.α) = 4 := by rw [hn, hn2]; norm_num
  set F : Finset (Equiv.Perm (Fin 5)) := Eset.filter fun σ => Equiv.Perm.sign σ = 1 with hF
  have hFcard : F.card = 2 := by decide +kernel
  have hle : Nat.card ↥(T.map C.P.α) ≤ Nat.card ↥F := by
    refine Nat.card_le_card_of_injective (fun a => ⟨(a.1 : Equiv.Perm (Fin 5)), ?_⟩) ?_
    · obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.1 a.2
      have h1 : C.P.pf (t : G) ∈ Eset := hcon (t : G) (Subgroup.mem_subgroupOf.1 ht)
      have h2 : C.P.pf (t : G) = ((C.P.α t : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
        rw [C.P.pf_eq (Subgroup.le_normalizer t.2)]
        exact C.P.hπα (t : G) t.2
      rw [hF, Finset.mem_filter]
      refine ⟨?_, Equiv.Perm.mem_alternatingGroup.1 a.1.2⟩
      rw [← hta, ← h2]
      exact h1
    · intro a b hab
      exact Subtype.ext (Subtype.ext (by simpa using hab))
  rw [Nat.card_eq_fintype_card (α := ↥F), Fintype.card_coe, hFcard, hcard4] at hle
  omega

theorem burnsideC5x_cent_E : ∀ σ ∈ Dset, (∀ τ ∈ Eset, σ * τ = τ * σ) → σ ∈ Eset := by
  decide +kernel

include C in
theorem SC {P : Subgroup G} (hCRU : R ⊓ Subgroup.centralizer (blockU K : Set G) = P) :
    ∀ r ∈ R, (∀ b ∈ baum R, ⁅r, b⁆ ∈ P) → r ∈ baum R ⊔ P := by
  intro r hr hcomm
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := C.RN hr
  have hπr : C.P.pf r ∈ Dset := by
    have : C.P.pf r ∈ C.P.im R := (C.P.mem_im_pf C.RN).2 ⟨r, hr, rfl⟩
    rw [C.hR] at this
    exact (mem_Dstd _).1 this
  have hker1 : ∀ c ∈ P, C.P.pf c = 1 := fun c hc => by
    have hcR : c ∈ R ⊓ Subgroup.centralizer (blockU K : Set G) := hCRU ▸ hc
    have hcN := C.RN hcR.1
    rw [C.P.pf_eq hcN, C.P.hker ⟨c, hcN⟩]
    intro u hu
    have := Subgroup.mem_centralizer_iff.mp hcR.2 u hu
    calc c * u * c⁻¹ = (u * c) * c⁻¹ := by rw [this]
      _ = u := by group
  have hcomm' : ∀ τ ∈ Eset, C.P.pf r * τ = τ * C.P.pf r := by
    intro τ hτ
    have hτB : τ ∈ C.P.im (baum R) := by rw [C.hB]; exact (mem_Estd τ).2 hτ
    obtain ⟨b, hb, rfl⟩ := (C.P.mem_im_pf C.hBN).1 hτB
    have hbN := C.hBN hb
    have h1 := hker1 _ (hcomm b hb)
    have e : C.P.pf (r * b * r⁻¹ * b⁻¹) =
        C.P.pf r * C.P.pf b * (C.P.pf r)⁻¹ * (C.P.pf b)⁻¹ := by
      rw [C.P.pf_mul (mul_mem (mul_mem hrN hbN) (inv_mem hrN)) (inv_mem hbN),
        C.P.pf_mul (mul_mem hrN hbN) (inv_mem hrN), C.P.pf_mul hrN hbN, C.P.pf_inv hrN,
        C.P.pf_inv hbN]
    have h2 : ⁅C.P.pf r, C.P.pf b⁆ = 1 := by
      rw [commutatorElement_def, ← e]; exact h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hπE : C.P.pf r ∈ Eset := burnsideC5x_cent_E _ hπr hcomm'
  have hπB : C.P.pf r ∈ C.P.im (baum R) := by rw [C.hB]; exact (mem_Estd _).2 hπE
  obtain ⟨b, hb, hbr⟩ := (C.P.mem_im_pf C.hBN).1 hπB
  have hbN := C.hBN hb
  have hrb : r * b⁻¹ ∈ P := by
    have hmem : r * b⁻¹ ∈ R ⊓ Subgroup.centralizer (blockU K : Set G) := by
      refine ⟨R.mul_mem hr (R.inv_mem (C.hBR hb)), ?_⟩
      have hN : r * b⁻¹ ∈ Subgroup.normalizer (K : Set G) := mul_mem hrN (inv_mem hbN)
      have hp1 : C.P.pf (r * b⁻¹) = 1 := by
        rw [C.P.pf_mul hrN (inv_mem hbN), C.P.pf_inv hbN, hbr, mul_inv_cancel]
      have := (C.P.hker ⟨r * b⁻¹, hN⟩).1 (by rw [← C.P.pf_eq hN]; exact hp1)
      refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      have h3 := this u hu
      calc u * (r * b⁻¹) = ((r * b⁻¹) * u * (r * b⁻¹)⁻¹) * (r * b⁻¹) := by rw [h3]
        _ = (r * b⁻¹) * u := by group
    rwa [hCRU] at hmem
  have : r = (r * b⁻¹) * b := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hrb) (Subgroup.mem_sup_left hb)

include C in
theorem hRQ : R ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ baum R) : Set G) := fun r hr =>
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ baum R)
    (C1.mem_normalizer_sup (C.RN hr) (normalizer_le_normalizer_baum R (Subgroup.le_normalizer hr)))

include C in
theorem inf_cent_U_eq {A : Subgroup G} (hAB : A ≤ baum R) :
    A ⊓ Subgroup.centralizer (blockU K : Set G) = A ⊓ pCoreOf 2 (K ⊔ baum R) := by
  ext a
  constructor
  · rintro ⟨haA, haC⟩
    exact ⟨haA, by rw [C.Q_eq]; exact ⟨hAB haA, haC⟩⟩
  · rintro ⟨haA, haQ⟩
    exact ⟨haA, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U haQ hu).symm⟩

include C in
theorem im_normalized {A : Subgroup G} (hRA : R ≤ Subgroup.normalizer (A : Set G)) :
    ∀ d ∈ Dstd, ∀ g ∈ C.P.im A, d * g * d⁻¹ ∈ C.P.im A := by
  intro d hd g hg
  rw [← C.hR] at hd
  obtain ⟨r, hr, rfl⟩ := (C.P.mem_im).1 hd
  obtain ⟨a, ha, rfl⟩ := (C.P.mem_im).1 hg
  refine (C.P.mem_im).2 ⟨r * a * r⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.mp (hRA hr) a).mp ha
  simpa using this

include C in
theorem Kpp_le {Y A : Subgroup G} (hYD : Y ≤ baum R ⊓ Subgroup.centralizer (K : Set G))
    (hAB : A ≤ baum R) (hA : burnsideC5x_YCls Y A) :
    A ⊓ pCoreOf 2 (K ⊔ baum R) ≤
      (blockU K ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  intro q hq
  obtain ⟨u, hu, d, hd, rfl⟩ := C.exists_UD hq.2
  have huC : u ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have he : a * (u * d) * a⁻¹ * (u * d)⁻¹ ∈ baum R ⊓ Subgroup.centralizer (K : Set G) :=
      hYD (hA.2 a ha _ hq.1)
    have h2 : (a * u * a⁻¹) * (a * d * a⁻¹) =
        u * (((a * (u * d) * a⁻¹ * (u * d)⁻¹) * d)) := by
      have hcomm : (a * (u * d) * a⁻¹ * (u * d)⁻¹) * u = u * (a * (u * d) * a⁻¹ * (u * d)⁻¹) :=
        (C.U_comm_D hu he).symm
      calc (a * u * a⁻¹) * (a * d * a⁻¹) = a * (u * d) * a⁻¹ := by group
        _ = ((a * (u * d) * a⁻¹ * (u * d)⁻¹) * u) * d := by group
        _ = (u * (a * (u * d) * a⁻¹ * (u * d)⁻¹)) * d := by rw [hcomm]
        _ = u * (((a * (u * d) * a⁻¹ * (u * d)⁻¹) * d)) := by group
    have h3 := C.UD_unique (AppC.PiData.conj_mem_U (C.hBN (hAB ha)) hu) hu
      (C.conj_mem_D (hAB ha) hd) (mul_mem he hd) h2
    calc a * u = (a * u * a⁻¹) * a := by group
      _ = u * a := by rw [h3.1]
  exact mul_mem (Subgroup.mem_sup_left ⟨hu, huC⟩) (Subgroup.mem_sup_right hd)

include C in
theorem card_le_YCls {Y A : Subgroup G} (hYD : Y ≤ baum R ⊓ Subgroup.centralizer (K : Set G))
    (hAB : A ≤ baum R) (hA : burnsideC5x_YCls Y A) :
    Nat.card ↥A ≤ Nat.card ↥(C.P.im A) * Nat.card ↥(AppC.FixΔ (C.P.im A)) *
      Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAB.trans C.hBN
  have hKQ : A ⊓ Subgroup.centralizer (blockU K : Set G) = A ⊓ pCoreOf 2 (K ⊔ baum R) := by
    ext a
    constructor
    · rintro ⟨haA, haC⟩
      exact ⟨haA, by rw [C.Q_eq]; exact ⟨hAB haA, haC⟩⟩
    · rintro ⟨haA, haQ⟩
      exact ⟨haA, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U haQ hu).symm⟩
  have h1 := C.P.card_im_mul hAN
  rw [hKQ] at h1
  have h2 := C.P.card_fix hAN
  have hX1 := B2F.card_sup_mul_card_inf_of_commute
    (A := blockU K ⊓ Subgroup.centralizer (A : Set G))
    (B := baum R ⊓ Subgroup.centralizer (K : Set G))
    (fun u hu d hd => C.U_comm_D hu.1 hd)
  have hinf : (blockU K ⊓ Subgroup.centralizer (A : Set G)) ⊓
      (baum R ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have : y ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) := ⟨hy.1.1, hy.2⟩
    rwa [C.U_inf_D] at this
  rw [hinf, Subgroup.card_bot, mul_one, h2] at hX1
  have hkx := Subgroup.card_le_of_le (C.Kpp_le hYD hAB hA)
  calc Nat.card ↥A = Nat.card ↥(C.P.im A) * Nat.card ↥(A ⊓ pCoreOf 2 (K ⊔ baum R)) := h1.symm
    _ ≤ Nat.card ↥(C.P.im A) * (Nat.card ↥(AppC.FixΔ (C.P.im A)) *
        Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G))) :=
        Nat.mul_le_mul_left _ (hkx.trans hX1.le)
    _ = _ := by ring

end burnsideC5x_A5Cfg

namespace burnsideC5x_A5Cfg

variable {G : Type} [Group G] [Finite G] {R K : Subgroup G}

structure Good (C : burnsideC5x_A5Cfg R K) (x : G) : Prop where
  hxR : x ∈ Subgroup.normalizer (R : Set G)
  hne : ⁅blockU K, conjSubgroup (blockU K) x⁆ ≠ ⊥

structure Mate (C : burnsideC5x_A5Cfg R K) (x : G) : Prop extends Good C x where
  hD : C5.ElemAb2 (baum R ⊓ Subgroup.centralizer (K : Set G))

namespace Good

variable {C : burnsideC5x_A5Cfg R K} {x : G} (m : Good C x)

include m in
theorem hxB : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R m.hxR

include m in
theorem V_inf_Q_le_U {e : G} (hV : e ∈ conjSubgroup (blockU K) x)
    (hQ : e ∈ pCoreOf 2 (K ⊔ baum R)) : e ∈ blockU K := by
  have hC : e ∈ conjSubgroup (blockU K) x ⊓ Subgroup.centralizer (blockU K : Set G) :=
    ⟨hV, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U hQ hu).symm⟩
  rw [C.V_inf_C m.hxR m.hne] at hC
  exact hC.1

include m in
theorem D_comm_V {d v : G} (hd : d ∈ baum R ⊓ Subgroup.centralizer (K : Set G))
    (hv : v ∈ conjSubgroup (blockU K) x) : d * v = v * d := by
  have hvB := C.conj_le_B m.hxR hv
  have hdN : d ∈ Subgroup.normalizer (blockU K : Set G) := C.hBU hd.1
  have hD' : ∀ s ∈ baum R, ∀ e ∈ baum R ⊓ Subgroup.centralizer (K : Set G),
      s * e * s⁻¹ ∈ baum R ⊓ Subgroup.centralizer (K : Set G) := fun s hs e he =>
    (Subgroup.mem_normalizer_iff.mp (C5.mem_normalizer_inf
      (Subgroup.le_normalizer hs) (C5.mem_normalizer_centralizer (C.hBN hs))) e).mp he
  have h1 : d * v * d⁻¹ * v⁻¹ ∈ baum R ⊓ Subgroup.centralizer (K : Set G) := by
    have := mul_mem hd.1 hvB
    have h3 := hD' v hvB d⁻¹ (inv_mem hd)
    have h4 := mul_mem hd h3
    simpa [mul_assoc] using h4
  have h2 : d * v * d⁻¹ * v⁻¹ ∈ conjSubgroup (blockU K) x := by
    have hBV : baum R ≤ Subgroup.normalizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) :=
      C5.le_normalizer_conj m.hxB C.hBU
    have h3 := (Subgroup.mem_normalizer_iff.1 (hBV hd.1) v).1 hv
    exact mul_mem h3 (inv_mem hv)
  have h4 : d * v * d⁻¹ * v⁻¹ ∈ pCoreOf 2 (K ⊔ baum R) := C.hDQ h1
  have h5 := m.V_inf_Q_le_U h2 h4
  have h6 : d * v * d⁻¹ * v⁻¹ ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) := ⟨h5, h1⟩
  rw [C.U_inf_D, Subgroup.mem_bot] at h6
  calc d * v = (d * v * d⁻¹ * v⁻¹) * (v * d) := by group
    _ = v * d := by rw [h6, one_mul]

include m in
theorem V_inf_D : conjSubgroup (blockU K) x ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  have hyU := m.V_inf_Q_le_U hy.1 (C.hDQ hy.2)
  have : y ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) := ⟨hyU, hy.2⟩
  rwa [C.U_inf_D] at this

end Good

namespace Mate

variable {C : burnsideC5x_A5Cfg R K} {x : G} (m : Mate C x)

include m in
theorem Q_elem : C5.ElemAb2 (pCoreOf 2 (K ⊔ baum R)) := by
  have := C5.ElemAb2.sup (C1.elemAb2_blockU C.short) m.hD
    (fun u hu d hd => C.U_comm_D hu hd)
  rwa [← C.Q_UD] at this

end Mate

namespace Good

variable {C : burnsideC5x_A5Cfg R K} {x : G} (m : Good C x)

include m in
theorem Qx_eq : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x =
    conjSubgroup (blockU K) x ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  obtain ⟨⟨-, hP1b⟩, -⟩ := C.part123 m.hxR m.hne
  have hVB := C.conj_le_B m.hxR
  have hVQx : conjSubgroup (blockU K) x ≤ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x :=
    C5.conjSubgroup_mono C.hUQ x
  have hDQx : baum R ⊓ Subgroup.centralizer (K : Set G) ≤
      conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x := by
    intro d hd
    rw [C.conj_Q_eq m.hxB]
    exact ⟨hd.1, (hP1b hd).2⟩
  apply le_antisymm
  · obtain ⟨-, hQxC⟩ := C.relIndex_inf_conj (inv_mem m.hxR) (burnsideC5x_comm_inv_ne m.hne)
    have h2 := congrArg (fun A => conjSubgroup A x) hQxC
    simp only [C5.conjSubgroup_sup, C5.conjSubgroup_inf, CFSG.Quasithin.conjSubgroup_conjSubgroup,
      inv_mul_cancel, CFSG.Quasithin.conjSubgroup_one] at h2
    rw [inf_comm] at h2
    rw [← h2]
    refine sup_le le_sup_left ?_
    intro c hc
    obtain ⟨hcQ, hcQx⟩ := hc
    rw [C.Q_UD] at hcQ
    obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute (fun u hu d hd => C.U_comm_D hu hd) hcQ
    have hdQx := hDQx hd
    have hu' : u ∈ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x := by
      have := Subgroup.mul_mem _ hcQx (Subgroup.inv_mem _ hdQx)
      simpa [mul_assoc] using this
    rw [C.conj_Q_eq m.hxB] at hu'
    have hu'' : u ∈ blockU K ⊓ Subgroup.centralizer
        ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := ⟨hu, hu'.2⟩
    rw [C.inf_C_conj m.hxR m.hne, ← (C.commutator_conj m.hxR m.hne).2] at hu''
    exact mul_mem (Subgroup.mem_sup_left hu''.2) (Subgroup.mem_sup_right hd)
  · exact sup_le hVQx hDQx

include m in
theorem card_VD : Nat.card ↥(conjSubgroup (blockU K) x ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G))) =
    16 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  have h := B2F.card_sup_mul_card_inf_of_commute
    (A := conjSubgroup (blockU K) x) (B := baum R ⊓ Subgroup.centralizer (K : Set G))
    (fun v hv d hd => (m.D_comm_V hd hv).symm)
  rw [m.V_inf_D, Subgroup.card_bot, C5.card_conjSubgroup, C.card_U] at h
  omega

include m in
theorem exists_vud {a : G} (haB : a ∈ baum R) (hπ : C.P.pf a ∈ Eset) :
    ∃ v ∈ conjSubgroup (blockU K) x, ∃ u ∈ blockU K,
      ∃ d ∈ baum R ⊓ Subgroup.centralizer (K : Set G),
      a = v * u * d ∧ C.P.pf v = C.P.pf a := by
  have hVB := C.conj_le_B m.hxR
  have hπ' : C.P.pf a ∈ C.P.im (conjSubgroup (blockU K) x) := by
    rw [C.im_conj_eq m.hxR m.hne]; exact (mem_Estd _).2 hπ
  obtain ⟨v, hv, hvπ⟩ := (C.P.mem_im_pf (hVB.trans C.hBN)).1 hπ'
  have hq : v⁻¹ * a ∈ pCoreOf 2 (K ⊔ baum R) := by
    refine (C.mem_Q_iff (mul_mem (inv_mem (hVB hv)) haB)).2 ?_
    rw [C.P.pf_mul (inv_mem (C.hBN (hVB hv))) (C.hBN haB), C.P.pf_inv (C.hBN (hVB hv)), hvπ,
      inv_mul_cancel]
  rw [C.Q_UD] at hq
  obtain ⟨u, hu, d, hd, hud⟩ := C5.mem_sup_of_commute (fun u hu d hd => C.U_comm_D hu hd) hq
  refine ⟨v, hv, u, hu, d, hd, ?_, hvπ⟩
  calc a = v * (v⁻¹ * a) := by group
    _ = v * (u * d) := by rw [hud]
    _ = v * u * d := by group

end Good

namespace Mate

variable {C : burnsideC5x_A5Cfg R K} {x : G} (m : Mate C x)

include m in
theorem Q_isMax : IsMaxElemAbelian (baum R) (pCoreOf 2 (K ⊔ baum R)) := C.Q_isMax' m.Q_elem

include m in
theorem card_eq_Q {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A) :
    Nat.card ↥A = Nat.card ↥(pCoreOf 2 (K ⊔ baum R)) :=
  le_antisymm (m.Q_isMax.2.2 A hA.1 hA.2.1) (hA.2.2 _ C.hQB (C5.isElemAbelian_two_iff.mpr m.Q_elem))

include m in
theorem Qx_isMax : IsMaxElemAbelian (baum R) (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) :=
  C56.isMaxElemAbelian_conjSubgroup m.Q_isMax m.hxB

include m in
theorem G_spec {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A) :
    A ⊓ pCoreOf 2 (K ⊔ baum R) =
        (blockU K ⊓ Subgroup.centralizer (A : Set G)) ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) ∧
      Nat.card ↥(C.P.im A) * Nat.card ↥(AppC.FixΔ (C.P.im A)) = 16 := by
  have hAS := hA.1
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAS.trans C.hBN
  have hKX : A ⊓ pCoreOf 2 (K ⊔ baum R) ≤
      (blockU K ⊓ Subgroup.centralizer (A : Set G)) ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
    intro q hq
    obtain ⟨u, hu, d, hd, rfl⟩ := C.exists_UD hq.2
    have huC : u ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hcomm : a * (u * d) = (u * d) * a := B2F.isElemAbelian_comm hA.2.1 ha hq.1
      have h1 : (a * u * a⁻¹) * (a * d * a⁻¹) = u * d := by
        calc (a * u * a⁻¹) * (a * d * a⁻¹) = a * (u * d) * a⁻¹ := by group
          _ = u * d := by rw [hcomm]; group
      have h2 := C.UD_unique (AppC.PiData.conj_mem_U (C.hBN (hAS ha)) hu) hu
        (C.conj_mem_D (hAS ha) hd) hd h1
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [h2.1]
    exact mul_mem (Subgroup.mem_sup_left ⟨hu, huC⟩) (Subgroup.mem_sup_right hd)
  set X := (blockU K ⊓ Subgroup.centralizer (A : Set G)) ⊔
    (baum R ⊓ Subgroup.centralizer (K : Set G)) with hX
  have hKQ : A ⊓ Subgroup.centralizer (blockU K : Set G) = A ⊓ pCoreOf 2 (K ⊔ baum R) := by
    ext a
    constructor
    · rintro ⟨haA, haC⟩
      exact ⟨haA, by rw [C.Q_eq]; exact ⟨hAS haA, haC⟩⟩
    · rintro ⟨haA, haQ⟩
      exact ⟨haA, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U haQ hu).symm⟩
  have h1 := C.P.card_im_mul hAN
  rw [hKQ] at h1
  have h2 := C.P.card_fix hAN
  have hcardA : Nat.card ↥A = 16 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) :=
    (m.card_eq_Q hA).trans C.card_Q
  have hf := AppC.card_mul_fix_le (C.P.im A) (C.P.im_elemAbelian hA.2.1).1
    (C.P.im_elemAbelian hA.2.1).2
  have hX1 := B2F.card_sup_mul_card_inf_of_commute
    (A := blockU K ⊓ Subgroup.centralizer (A : Set G)) (B := baum R ⊓ Subgroup.centralizer (K : Set G))
    (fun u hu d hd => C.U_comm_D hu.1 hd)
  have hinf : (blockU K ⊓ Subgroup.centralizer (A : Set G)) ⊓
      (baum R ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have : y ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) := ⟨hy.1.1, hy.2⟩
    rwa [C.U_inf_D] at this
  rw [hinf, Subgroup.card_bot, mul_one] at hX1
  have hkx : Nat.card ↥(A ⊓ pCoreOf 2 (K ⊔ baum R)) ≤ Nat.card ↥X := Subgroup.card_le_of_le hKX
  have hppos : 0 < Nat.card ↥(C.P.im A) := Nat.card_pos
  have hdpos : 0 < Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  set p := Nat.card ↥(C.P.im A)
  set k := Nat.card ↥(A ⊓ pCoreOf 2 (K ⊔ baum R))
  set f := Nat.card ↥(AppC.FixΔ (C.P.im A))
  set d := Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G))
  set xx := Nat.card ↥X
  rw [h2] at hX1
  have hpk : p * k = 16 * d := by rw [← hcardA, ← h1]
  have hpx : p * xx = p * f * d := by rw [hX1]; ring
  have hchain : p * f * d ≤ 16 * d := Nat.mul_le_mul_right d hf
  have hpf : p * f = 16 := by
    have : p * k ≤ p * xx := Nat.mul_le_mul_left p hkx
    have h3 : 16 * d ≤ p * f * d := by rw [← hpx, ← hpk]; exact this
    have h4 : p * f * d = 16 * d := le_antisymm hchain h3
    exact Nat.eq_of_mul_eq_mul_right hdpos h4
  refine ⟨Subgroup.eq_of_le_of_card_ge hKX ?_, hpf⟩
  have h5 : p * xx = p * k := by rw [hpx, hpf, hpk]
  exact (Nat.eq_of_mul_eq_mul_left hppos h5).le

include m in
theorem D_le_of_isMax {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A) :
    baum R ⊓ Subgroup.centralizer (K : Set G) ≤ A := by
  intro d hd
  have h : d ∈ A ⊓ pCoreOf 2 (K ⊔ baum R) := by
    rw [(m.G_spec hA).1]
    exact Subgroup.mem_sup_right hd
  exact h.1

include m in
theorem fixU_le_of_isMax {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A) :
    blockU K ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
  intro u hu
  have h : u ∈ A ⊓ pCoreOf 2 (K ⊔ baum R) := by
    rw [(m.G_spec hA).1]
    exact Subgroup.mem_sup_left hu
  exact h.1

include m in
theorem type_cases {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A) :
    (∀ g, g ∈ C.P.im A ↔ g = 1) ∨ (∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = Equiv.swap 0 1) ∨
      (∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = Equiv.swap 2 3) ∨ (∀ g, g ∈ C.P.im A ↔ g ∈ Eset) :=
  AppC.classify_P (C.P.im A) ((C.im_le hA.1).trans Estd_le_Dstd) (C.P.im_elemAbelian hA.2.1).1
    (C.P.im_elemAbelian hA.2.1).2 (m.G_spec hA).2

include m in
theorem eq_Q_of_type_bot {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A)
    (h : ∀ g, g ∈ C.P.im A ↔ g = 1) : A = pCoreOf 2 (K ⊔ baum R) := by
  have hle : A ≤ pCoreOf 2 (K ⊔ baum R) := by
    intro a ha
    have : C.P.pf a ∈ C.P.im A := (C.P.mem_im_pf (hA.1.trans C.hBN)).2 ⟨a, ha, rfl⟩
    exact (C.mem_Q_iff (hA.1 ha)).2 ((h _).1 this)
  exact Subgroup.eq_of_le_of_card_ge hle (m.card_eq_Q hA).ge

omit [Finite G] in
theorem comm_of_sq {v u : G} (h : (v * u) ^ 2 = 1) (hv : v ^ 2 = 1) (hu : u ^ 2 = 1) :
    v * u = u * v := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv)
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu)
  have h2 : (v * u)⁻¹ = v * u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h)
  rw [mul_inv_rev, hv', hu'] at h2
  exact h2.symm

omit [Finite G] in
theorem eq_one_or_of_mem_zpowers {v x : G} (hv : v ^ 2 = 1) (hx : x ∈ Subgroup.zpowers v) :
    x = 1 ∨ x = v := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hv
  have key : v ^ n = v ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, hv2, one_zpow, mul_one]
  rw [key]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

include m in
theorem V_comm {a b : G} (ha : a ∈ conjSubgroup (blockU K) x) (hb : b ∈ conjSubgroup (blockU K) x) :
    a * b = b * a := ((C1.elemAb2_blockU C.short).conjSubgroup x).1 a ha b hb

include m in
theorem V_sq {a : G} (ha : a ∈ conjSubgroup (blockU K) x) : a ^ 2 = 1 :=
  ((C1.elemAb2_blockU C.short).conjSubgroup x).2 a ha

include m in
theorem V_elem : IsElemAbelian 2 (conjSubgroup (blockU K) x) :=
  C5.isElemAbelian_two_iff.mpr ((C1.elemAb2_blockU C.short).conjSubgroup x)

include m in
theorem pf_ne_one {v : G} (hπ : C.P.pf v = Equiv.swap 0 1) : v ≠ 1 := by
  intro h
  rw [h, C.P.pf_eq (one_mem _)] at hπ
  have h1 : C.P.π ⟨1, one_mem _⟩ = 1 := map_one C.P.π
  rw [h1] at hπ
  exact absurd hπ.symm (by decide)

@[expose] def Yv (K R : Subgroup G) (v : G) : Subgroup G :=
  (blockU K ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) ⊔
    Subgroup.zpowers v

include m in
theorem X'_spec {v : G} (hv : v ∈ conjSubgroup (blockU K) x) (hπ : C.P.pf v = Equiv.swap 0 1) :
    IsElemAbelian 2 ((blockU K ⊓ Subgroup.centralizer ({v} : Set G)) ⊔
        (baum R ⊓ Subgroup.centralizer (K : Set G))) ∧
      Nat.card ↥((blockU K ⊓ Subgroup.centralizer ({v} : Set G)) ⊔
        (baum R ⊓ Subgroup.centralizer (K : Set G))) =
        8 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := C.hBN (C.conj_le_B m.hxR hv)
  have hcomm : ∀ a ∈ blockU K ⊓ Subgroup.centralizer ({v} : Set G),
      ∀ d ∈ baum R ⊓ Subgroup.centralizer (K : Set G), a * d = d * a :=
    fun a ha d hd => C.U_comm_D ha.1 hd
  refine ⟨B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left C.hU)
    (C5.isElemAbelian_two_iff.mpr m.hD) hcomm, ?_⟩
  have h := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : (blockU K ⊓ Subgroup.centralizer ({v} : Set G)) ⊓
      (baum R ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have : y ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) := ⟨hy.1.1, hy.2⟩
    rwa [C.U_inf_D] at this
  rw [hinf, Subgroup.card_bot, mul_one] at h
  have hc := C.P.card_fix_set ({v} : Set G) (Set.singleton_subset_iff.2 hvN)
  have hset : Nat.card {w : evenWeight 5 // ∀ y ∈ ({v} : Set G),
      vact (C.P.pf y) w = w} = 8 := by
    rw [← AppC.card_vfix_t1]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    simp [hπ]
  rw [hset] at hc
  rw [h, hc]

include m in
theorem Yv_isMax {v : G} (hv : v ∈ conjSubgroup (blockU K) x)
    (hπ : C.P.pf v = Equiv.swap 0 1) :
    IsMaxElemAbelian (baum R) (Yv K R v) ∧
      (Yv K R v ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex (Yv K R v) = 2 := by
  have hvS : v ∈ baum R := C.conj_le_B m.hxR hv
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := C.hBN hvS
  have hv2 : v ^ 2 = 1 := m.V_sq hv
  obtain ⟨hXe, hXc⟩ := m.X'_spec hv hπ
  set X' := (blockU K ⊓ Subgroup.centralizer ({v} : Set G)) ⊔
    (baum R ⊓ Subgroup.centralizer (K : Set G)) with hX'
  have hXQ : X' ≤ pCoreOf 2 (K ⊔ baum R) := sup_le (inf_le_left.trans C.hUQ) C.hDQ
  have hXv : ∀ a ∈ X', a * v = v * a := by
    intro a ha
    have hle : X' ≤ Subgroup.centralizer ({v} : Set G) := by
      refine sup_le inf_le_right fun d hd => ?_
      exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (m.D_comm_V hd hv).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) v (Set.mem_singleton v)).symm
  have hzp : Subgroup.zpowers v ≤ Subgroup.centralizer (X' : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 hXv)
  have hcomm2 : ∀ a ∈ X', ∀ b ∈ Subgroup.zpowers v, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hzp hb) a ha
  have hzpe : IsElemAbelian 2 (Subgroup.zpowers v) :=
    B2F.isElemAbelian_mono (Subgroup.zpowers_le.2 hv) m.V_elem
  have hYe : IsElemAbelian 2 (Yv K R v) :=
    B2F.isElemAbelian_sup_of_commute hXe hzpe hcomm2
  have hinf : X' ⊓ Subgroup.zpowers v = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    rcases eq_one_or_of_mem_zpowers hv2 hy.2 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      have hvQ : v ∈ pCoreOf 2 (K ⊔ baum R) := hXQ (h ▸ hy.1)
      have := (C.mem_Q_iff hvS).1 hvQ
      rw [hπ] at this
      exact absurd this (by decide)
  have hcardz : Nat.card ↥(Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hv2 (m.pf_ne_one hπ)
  have hY := B2F.card_sup_mul_card_inf_of_commute hcomm2
  rw [hinf, Subgroup.card_bot, mul_one, hcardz, hXc] at hY
  have hYcard : Nat.card ↥(Yv K R v) = 16 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
    show Nat.card ↥(X' ⊔ Subgroup.zpowers v) = _
    omega
  have hYS : Yv K R v ≤ baum R :=
    sup_le (hXQ.trans C.hQB) (Subgroup.zpowers_le.2 hvS)
  have hmax : IsMaxElemAbelian (baum R) (Yv K R v) :=
    ⟨hYS, hYe, fun B' hBS hBe => by
      obtain ⟨-, hcard, hle⟩ := C.aU_spec hBe hBS
      have h1 := hcard.trans (Subgroup.card_le_of_le hle)
      rw [C.card_Q] at h1
      omega⟩
  refine ⟨hmax, ?_⟩
  have hYN : Yv K R v ≤ Subgroup.normalizer (K : Set G) := hYS.trans C.hBN
  have h1 := C.P.card_im_mul hYN
  have hKQ : Yv K R v ⊓ Subgroup.centralizer (blockU K : Set G) =
      Yv K R v ⊓ pCoreOf 2 (K ⊔ baum R) := by
    ext a
    constructor
    · rintro ⟨haA, haC⟩
      exact ⟨haA, by rw [C.Q_eq]; exact ⟨hYS haA, haC⟩⟩
    · rintro ⟨haA, haQ⟩
      exact ⟨haA, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U haQ hu).symm⟩
  rw [hKQ] at h1
  have hge : 8 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) ≤
      Nat.card ↥(Yv K R v ⊓ pCoreOf 2 (K ⊔ baum R)) := by
    rw [← hXc]
    exact Subgroup.card_le_of_le (le_inf (le_sup_left : X' ≤ Yv K R v) hXQ)
  have hne : C.P.im (Yv K R v) ≠ ⊥ := by
    intro hbot
    have hv' : Equiv.swap (0 : Fin 5) 1 ∈ C.P.im (Yv K R v) :=
      (C.P.mem_im_pf hYN).2 ⟨v, Subgroup.mem_sup_right (Subgroup.mem_zpowers v), hπ⟩
    rw [hbot] at hv'
    exact absurd (Subgroup.mem_bot.1 hv') (by decide)
  have hlt : 1 < Nat.card ↥(C.P.im (Yv K R v)) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hdpos : 0 < Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  rw [hYcard] at h1
  have hKle : Nat.card ↥(Yv K R v ⊓ pCoreOf 2 (K ⊔ baum R)) ≤
      8 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
    by_contra hcon
    push Not at hcon
    have := Nat.mul_le_mul hlt hcon
    linarith
  have hKeq : Nat.card ↥(Yv K R v ⊓ pCoreOf 2 (K ⊔ baum R)) =
      8 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) :=
    le_antisymm hKle hge
  have hidx := C5.card_eq_card_mul_relIndex
    (inf_le_left : Yv K R v ⊓ pCoreOf 2 (K ⊔ baum R) ≤ Yv K R v)
  rw [hYcard, hKeq] at hidx
  have h8 : 8 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) * 2 =
      8 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) *
        (Yv K R v ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex (Yv K R v) := by
    rw [← hidx]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h8).symm

include m in
theorem cent_U_V : blockU K ⊓ Subgroup.centralizer
    ((conjSubgroup (blockU K) x : Subgroup G) : Set G) = blockU K ⊓ conjSubgroup (blockU K) x :=
  (C.inf_C_conj m.hxR m.hne).trans (C.commutator_conj m.hxR m.hne).2.symm

include m in
theorem fix_mem {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = Equiv.swap 0 1) {w : G}
    (hw : w ∈ conjSubgroup (blockU K) x) (hπ : C.P.pf w = Equiv.swap 0 1) {u : G}
    (hu : u ∈ blockU K) (hc : w * u = u * w) : u ∈ A := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.1.trans C.hBN
  have hwN := C.hBN (C.conj_le_B m.hxR hw)
  have h1 : vact (C.P.pf w) (C.P.bf u) = C.P.bf u := (C.P.comm_iff hwN hu).1 hc
  have : u ∈ blockU K ⊓ Subgroup.centralizer (A : Set G) := by
    refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyN := hAN hy
    have hpy : C.P.pf y ∈ C.P.im A := (C.P.mem_im_pf hAN).2 ⟨y, hy, rfl⟩
    rcases (hty _).1 hpy with h | h
    · exact C.Q_comm_U ((C.mem_Q_iff (hA.1 hy)).2 h) hu
    · exact (C.P.comm_iff hyN hu).2 (by rw [h, ← hπ]; exact h1)
  exact m.fixU_le_of_isMax hA this

include m in
theorem Yv_le {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = Equiv.swap 0 1) {v : G}
    (hv : v ∈ conjSubgroup (blockU K) x) (hπ : C.P.pf v = Equiv.swap 0 1) : Yv K R v ≤ A := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.1.trans C.hBN
  have hD := m.D_le_of_isMax hA
  have hvA : v ∈ A := by
    have ht1 : Equiv.swap (0 : Fin 5) 1 ∈ C.P.im A := (hty _).2 (Or.inr rfl)
    obtain ⟨a, haA, hpa⟩ := (C.P.mem_im_pf hAN).1 ht1
    obtain ⟨v', hv', u', hu', d', hd', rfl, hpv'⟩ :=
      m.exists_vud (hA.1 haA) (by rw [hpa]; exact AppC.t1_mem_Eset)
    have hvu : v' * u' ∈ A := by
      have := mul_mem haA (inv_mem (hD hd'))
      simpa [mul_assoc] using this
    have hpv'1 : C.P.pf v' = Equiv.swap 0 1 := by rw [hpv', hpa]
    have hcom : v' * u' = u' * v' :=
      comm_of_sq (hA.2.1.2 _ hvu) (m.V_sq hv') (C.hU.2 u' hu')
    have hu'A : u' ∈ A := m.fix_mem hA hty hv' hpv'1 hu' hcom
    have hv'A : v' ∈ A := by
      have := mul_mem hvu (inv_mem hu'A)
      simpa [mul_assoc] using this
    have hwV : v * v'⁻¹ ∈ conjSubgroup (blockU K) x := mul_mem hv (inv_mem hv')
    have hvS := C.conj_le_B m.hxR hv
    have hv'S := C.conj_le_B m.hxR hv'
    have hw1 : C.P.pf (v * v'⁻¹) = 1 := by
      rw [C.P.pf_mul (C.hBN hvS) (inv_mem (C.hBN hv'S)), C.P.pf_inv (C.hBN hv'S), hπ, hpv'1,
        mul_inv_cancel]
    have hwQ := (C.mem_Q_iff (mul_mem hvS (inv_mem hv'S))).2 hw1
    have hwU : v * v'⁻¹ ∈ blockU K := m.V_inf_Q_le_U hwV hwQ
    have hwC : v * v'⁻¹ ∈ Subgroup.centralizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := by
      have : v * v'⁻¹ ∈ blockU K ⊓ conjSubgroup (blockU K) x := ⟨hwU, hwV⟩
      rw [← m.cent_U_V] at this
      exact this.2
    have hcw : v' * (v * v'⁻¹) = (v * v'⁻¹) * v' := Subgroup.mem_centralizer_iff.1 hwC v' hv'
    have hwA : v * v'⁻¹ ∈ A := m.fix_mem hA hty hv' hpv'1 hwU hcw
    have := mul_mem hwA hv'A
    simpa [mul_assoc] using this
  refine sup_le (sup_le (fun u hu => ?_) hD) (Subgroup.zpowers_le.2 hvA)
  exact m.fix_mem hA hty hv hπ hu.1 (Subgroup.mem_centralizer_iff.1 hu.2 v (Set.mem_singleton v))

include m in
theorem eq_Yv_of_type_t1 {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = Equiv.swap 0 1) {v : G}
    (hv : v ∈ conjSubgroup (blockU K) x) (hπ : C.P.pf v = Equiv.swap 0 1) : A = Yv K R v := by
  have hle := m.Yv_le hA hty hv hπ
  have hcard : Nat.card ↥A ≤ Nat.card ↥(Yv K R v) := by
    rw [m.card_eq_Q hA, m.card_eq_Q (m.Yv_isMax hv hπ).1]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

include m in
theorem eq_VD_of_type_E {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g ∈ Eset) :
    A = conjSubgroup (blockU K) x ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.1.trans C.hBN
  have hVN : conjSubgroup (blockU K) x ≤ Subgroup.normalizer (K : Set G) :=
    (C.conj_le_B m.hxR).trans C.hBN
  have hD := m.D_le_of_isMax hA
  have hex : ∀ g ∈ Eset, ∃ v ∈ conjSubgroup (blockU K) x, ∃ u ∈ blockU K,
      v * u ∈ A ∧ C.P.pf v = g := by
    intro g hg
    have hgA : g ∈ C.P.im A := (hty g).2 hg
    obtain ⟨a, haA, hpa⟩ := (C.P.mem_im_pf hAN).1 hgA
    obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := m.exists_vud (hA.1 haA) (by rw [hpa]; exact hg)
    refine ⟨v, hv, u, hu, ?_, by rw [hpv, hpa]⟩
    have := mul_mem haA (inv_mem (hD hd))
    rw [hadec] at this
    simpa [mul_assoc] using this
  have hfixu : ∀ v ∈ conjSubgroup (blockU K) x, ∀ u ∈ blockU K, v * u ∈ A →
      vact (C.P.pf v) (C.P.bf u) = C.P.bf u := by
    intro v hv u hu hvu
    have hcom := comm_of_sq (hA.2.1.2 _ hvu) (m.V_sq hv) (C.hU.2 u hu)
    exact (C.P.comm_iff (hVN hv) hu).1 hcom
  obtain ⟨v₁, hv₁, u₁, hu₁, h₁A, hp₁⟩ := hex (Equiv.swap 0 1) AppC.t1_mem_Eset
  obtain ⟨v₂, hv₂, u₂, hu₂, h₂A, hp₂⟩ := hex (Equiv.swap 2 3) AppC.t2_mem_Eset
  have hf₁ := hfixu v₁ hv₁ u₁ hu₁ h₁A
  have hf₂ := hfixu v₂ hv₂ u₂ hu₂ h₂A
  rw [hp₁] at hf₁
  rw [hp₂] at hf₂
  have hcomm12 : (v₁ * u₁) * (v₂ * u₂) = (v₂ * u₂) * (v₁ * u₁) :=
    B2F.isElemAbelian_comm hA.2.1 h₁A h₂A
  have hrel := (C.P.comm_vu (hVN hv₁) (hVN hv₂) hu₁ hu₂ (m.V_comm hv₁ hv₂)).1 hcomm12
  rw [hp₁, hp₂, Equiv.swap_inv, Equiv.swap_inv] at hrel
  have hrel' : pact (Equiv.swap 2 3) (C.P.bf u₁).1 + (C.P.bf u₂).1 =
      pact (Equiv.swap 0 1) (C.P.bf u₂).1 + (C.P.bf u₁).1 := congrArg Subtype.val hrel
  obtain ⟨hF1, hF2⟩ := AppC.E_comm _ _ hrel'
  have hF1' : ∀ σ ∈ Eset, vact σ (C.P.bf u₁) = C.P.bf u₁ := fun σ hσ =>
    Subtype.ext (AppC.fixE_of _ (congrArg Subtype.val hf₁) hF1 σ hσ)
  have hF2' : ∀ σ ∈ Eset, vact σ (C.P.bf u₂) = C.P.bf u₂ := fun σ hσ =>
    Subtype.ext (AppC.fixE_of _ hF2 (congrArg Subtype.val hf₂) σ hσ)
  have hle : A ≤ conjSubgroup (blockU K) x ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
    intro a ha
    have hpa : C.P.pf a ∈ Eset := (hty _).1 ((C.P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩)
    obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := m.exists_vud (hA.1 ha) hpa
    have hvu : v * u ∈ A := by
      have := mul_mem ha (inv_mem (hD hd))
      rw [hadec] at this
      simpa [mul_assoc] using this
    have hpvE : C.P.pf v ∈ Eset := by rw [hpv]; exact hpa
    have hinvE : (C.P.pf v)⁻¹ ∈ Eset := Eset_inv _ hpvE
    have hfix1 : vact (Equiv.swap 0 1) (C.P.bf u) = C.P.bf u := by
      have hcom : (v * u) * (v₁ * u₁) = (v₁ * u₁) * (v * u) :=
        B2F.isElemAbelian_comm hA.2.1 hvu h₁A
      have h := (C.P.comm_vu (hVN hv) (hVN hv₁) hu hu₁ (m.V_comm hv hv₁)).1 hcom
      rw [hp₁, Equiv.swap_inv, hF1' _ hinvE] at h
      rw [add_comm (C.P.bf u₁) (C.P.bf u)] at h
      exact add_right_cancel h
    have hfix2 : vact (Equiv.swap 2 3) (C.P.bf u) = C.P.bf u := by
      have hcom : (v * u) * (v₂ * u₂) = (v₂ * u₂) * (v * u) :=
        B2F.isElemAbelian_comm hA.2.1 hvu h₂A
      have h := (C.P.comm_vu (hVN hv) (hVN hv₂) hu hu₂ (m.V_comm hv hv₂)).1 hcom
      rw [hp₂, Equiv.swap_inv, hF2' _ hinvE] at h
      rw [add_comm (C.P.bf u₂) (C.P.bf u)] at h
      exact add_right_cancel h
    have hallE : ∀ σ ∈ Eset, vact σ (C.P.bf u) = C.P.bf u := fun σ hσ =>
      Subtype.ext (AppC.fixE_of _ (congrArg Subtype.val hfix1) (congrArg Subtype.val hfix2) σ hσ)
    have huC : u ∈ Subgroup.centralizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
      have hwE : C.P.pf w ∈ Eset := by
        have : C.P.pf w ∈ C.P.im (conjSubgroup (blockU K) x) := (C.P.mem_im_pf hVN).2 ⟨w, hw, rfl⟩
        rw [C.im_conj_eq m.hxR m.hne] at this
        exact (mem_Estd _).1 this
      exact (C.P.comm_iff (hVN hw) hu).2 (hallE _ hwE)
    have huV : u ∈ conjSubgroup (blockU K) x := by
      have : u ∈ blockU K ⊓ Subgroup.centralizer
          ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := ⟨hu, huC⟩
      rw [m.cent_U_V] at this
      exact this.2
    rw [hadec]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hv huV)) (Subgroup.mem_sup_right hd)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [m.card_VD, ← C.card_Q, ← m.card_eq_Q hA]

include m in
theorem pf_r {r : G} (hrR : r ∈ R) (hrK : r ∈ K) (hrE : C.P.pf r ∉ Eset) :
    (C.P.pf r)⁻¹ * Equiv.swap 0 1 * C.P.pf r = Equiv.swap 2 3 ∧
      (C.P.pf r)⁻¹ * Equiv.swap 2 3 * C.P.pf r = Equiv.swap 0 1 := by
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := C.RN hrR
  have hD : C.P.pf r ∈ Dset := by
    have : C.P.pf r ∈ C.P.im R := (C.P.mem_im_pf C.RN).2 ⟨r, hrR, rfl⟩
    rw [C.hR] at this
    exact (mem_Dstd _).1 this
  have hsign : Equiv.Perm.sign (C.P.pf r) = 1 := by
    have h := C.P.hπα r hrK
    rw [C.P.pf_eq hrN]
    have h' : C.P.π ⟨r, hrN⟩ = ((C.P.α ⟨r, hrK⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := h
    rw [h']
    exact Equiv.Perm.mem_alternatingGroup.1 (C.P.α ⟨r, hrK⟩).2
  exact AppC.conj_swap_of _ hD hsign hrE

include m in
theorem eq_conj_Yv_of_type_t2 {r : G} (hrR : r ∈ R) (hrK : r ∈ K) (hrE : C.P.pf r ∉ Eset)
    {A : Subgroup G} (hA : IsMaxElemAbelian (baum R) A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = Equiv.swap 2 3) {v : G}
    (hv : v ∈ conjSubgroup (blockU K) x) (hπ : C.P.pf v = Equiv.swap 0 1) :
    A = conjSubgroup (Yv K R v) r := by
  obtain ⟨hσ1, hσ2⟩ := m.pf_r hrR hrK hrE
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := C.RN hrR
  have hrNB : r⁻¹ ∈ Subgroup.normalizer (baum R : Set G) :=
    inv_mem (normalizer_le_normalizer_baum R (Subgroup.le_normalizer hrR))
  have hA' : IsMaxElemAbelian (baum R) (conjSubgroup A r⁻¹) :=
    C56.isMaxElemAbelian_conjSubgroup hA hrNB
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.1.trans C.hBN
  have hA'N : conjSubgroup A r⁻¹ ≤ Subgroup.normalizer (K : Set G) := hA'.1.trans C.hBN
  have hty' : ∀ g, g ∈ C.P.im (conjSubgroup A r⁻¹) ↔ g = 1 ∨ g = Equiv.swap 0 1 := by
    intro g
    constructor
    · intro hg
      obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hA'N).1 hg
      have hy' : r⁻¹ * y * r ∈ A := by
        have := mem_conjSubgroup_iff.1 hy
        simpa using this
      have hyN : y ∈ Subgroup.normalizer (K : Set G) := hA'N hy
      have hb : C.P.pf (r⁻¹ * y * r) = (C.P.pf r)⁻¹ * C.P.pf y * C.P.pf r := by
        rw [C.P.pf_mul (mul_mem (inv_mem hrN) hyN) hrN, C.P.pf_mul (inv_mem hrN) hyN,
          C.P.pf_inv hrN]
      have hbA : C.P.pf (r⁻¹ * y * r) ∈ C.P.im A := (C.P.mem_im_pf hAN).2 ⟨_, hy', rfl⟩
      have e : C.P.pf y = C.P.pf r * C.P.pf (r⁻¹ * y * r) * (C.P.pf r)⁻¹ := by
        rw [hb]; group
      rcases (hty _).1 hbA with h | h
      · left
        rw [e, h]; group
      · right
        have e2 : Equiv.swap (0 : Fin 5) 1 = C.P.pf r * Equiv.swap 2 3 * (C.P.pf r)⁻¹ := by
          rw [← hσ1]; group
        rw [e, h, ← e2]
    · rintro (rfl | rfl)
      · exact one_mem _
      · have ht2 : Equiv.swap (2 : Fin 5) 3 ∈ C.P.im A := (hty _).2 (Or.inr rfl)
        obtain ⟨b, hbA, hbp⟩ := (C.P.mem_im_pf hAN).1 ht2
        have hbN : b ∈ Subgroup.normalizer (K : Set G) := hAN hbA
        refine (C.P.mem_im_pf hA'N).2 ⟨r * b * r⁻¹, ?_, ?_⟩
        · rw [mem_conjSubgroup_iff]
          have : r⁻¹ * (r * b * r⁻¹) * r⁻¹⁻¹ = b := by group
          rw [this]; exact hbA
        · rw [C.P.pf_mul (mul_mem hrN hbN) (inv_mem hrN), C.P.pf_mul hrN hbN, C.P.pf_inv hrN, hbp,
            ← hσ1]
          group
  have heq := m.eq_Yv_of_type_t1 hA' hty' hv hπ
  rw [← heq]
  exact (C5.conjSubgroup_inv_conjSubgroup A r).symm

include m in
theorem S1Str_a5 (hsyl : IsSylowTwoOf (R ⊓ K) K) : burnsideC5x_S1Str R K x := by
  have hAB_le : ∀ A, IsMaxElemAbelian R A → A ≤ baum R := fun A hA =>
    (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ R).trans (C5.thompsonJ_le_baum' R)
  have hFam : AFam (baum R) = AFam R := burnsideC5x_AFam_eq C.hBR hAB_le
  have hRB : ∀ A, IsMaxElemAbelian R A ↔ IsMaxElemAbelian (baum R) A := fun A => by
    have := Set.ext_iff.mp hFam A
    exact this.symm
  have hxB := m.hxB
  obtain ⟨-, ⟨-, hP2b, -⟩, -⟩ := C.part123 m.hxR m.hne
  obtain ⟨hx1, -⟩ := burnsideC5x_not_le_Q C.Q_eq m.hne
  have hdD : (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) ∈ Dset := by decide +kernel
  have hd1 : (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) * Equiv.swap 0 1 *
      (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3)⁻¹ = Equiv.swap 2 3 := by decide +kernel
  have hd2 : (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) * Equiv.swap 2 3 *
      (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3)⁻¹ = Equiv.swap 0 1 := by decide +kernel
  have hdR : ∃ r₀ ∈ R, C.P.pf r₀ = Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3 := by
    have : (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) ∈ C.P.im R := by
      rw [C.hR]; exact (mem_Dstd _).2 hdD
    exact (C.P.mem_im_pf C.RN).1 this
  have hinv : ∀ A, IsMaxElemAbelian (baum R) A → R ≤ Subgroup.normalizer (A : Set G) →
      A = pCoreOf 2 (K ⊔ baum R) ∨ A = conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x := by
    intro A hA hRA
    obtain ⟨r₀, hr₀R, hr₀⟩ := hdR
    have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.1.trans C.hBN
    have hconj : ∀ g ∈ C.P.im A, (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) * g *
        (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3)⁻¹ ∈ C.P.im A := by
      intro g hg
      obtain ⟨a', ha', rfl⟩ := (C.P.mem_im_pf hAN).1 hg
      have hr₀N := C.RN hr₀R
      have ha'N := hAN ha'
      refine (C.P.mem_im_pf hAN).2 ⟨r₀ * a' * r₀⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hRA hr₀R) a').mp ha'
      · rw [C.P.pf_mul (mul_mem hr₀N ha'N) (inv_mem hr₀N), C.P.pf_mul hr₀N ha'N,
          C.P.pf_inv hr₀N, hr₀]
    rcases m.type_cases hA with h | h | h | h
    · exact Or.inl (m.eq_Q_of_type_bot hA h)
    · exfalso
      have h1 : Equiv.swap (0 : Fin 5) 1 ∈ C.P.im A := (h _).2 (Or.inr rfl)
      have h2 := hconj _ h1
      rw [hd1] at h2
      rcases (h _).1 h2 with h3 | h3
      · exact absurd h3 (by decide)
      · exact absurd h3 (by decide)
    · exfalso
      have h1 : Equiv.swap (2 : Fin 5) 3 ∈ C.P.im A := (h _).2 (Or.inr rfl)
      have h2 := hconj _ h1
      rw [hd2] at h2
      rcases (h _).1 h2 with h3 | h3
      · exact absurd h3 (by decide)
      · exact absurd h3 (by decide)
    · exact Or.inr (show A = conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x by
        rw [m.Qx_eq]; exact m.eq_VD_of_type_E hA h)
  have hne' : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x ≠ pCoreOf 2 (K ⊔ baum R) := by
    intro heq
    apply hx1
    have := C5.conjSubgroup_mono C.hUQ x
    rw [heq] at this
    exact this
  refine ⟨(hRB _).2 m.Q_isMax, fun A hA hRA => hinv A ((hRB A).1 hA) hRA, hne', hP2b,
    fun hL => ?_, fun h5 => ?_⟩
  · exfalso
    rcases hL with ⟨n, hn, hl⟩ | h3
    · exact AppC.not_lin2_of_alt5 C.short C.alt5 hn hl
    · exact AppC.not_alt3_of_alt5 C.alt5 h3
  · obtain ⟨r, hrRK, hrE⟩ := C.exists_r hsyl
    have hrB : r ∉ baum R := fun hrB => hrE ((mem_Estd _).1 (by
      rw [← C.hB]; exact (C.P.mem_im_pf C.hBN).2 ⟨r, hrB, rfl⟩))
    have hV1 : Equiv.swap (0 : Fin 5) 1 ∈ C.P.im (conjSubgroup (blockU K) x) := by
      rw [C.im_conj_eq m.hxR m.hne]; exact (mem_Estd _).2 AppC.t1_mem_Eset
    obtain ⟨v, hv, hvπ⟩ := (C.P.mem_im_pf ((C.conj_le_B m.hxR).trans C.hBN)).1 hV1
    have hrNB : r ∈ Subgroup.normalizer (baum R : Set G) :=
      normalizer_le_normalizer_baum R (Subgroup.le_normalizer hrRK.1)
    refine ⟨Yv K R v, r, hrRK, hrB, (m.Yv_isMax hv hvπ).2, ?_⟩
    ext A
    simp only [AFam, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hA
      have hAB := (hRB A).1 hA
      rcases m.type_cases hAB with h | h | h | h
      · exact Or.inl (m.eq_Q_of_type_bot hAB h)
      · exact Or.inr (Or.inr (Or.inl (m.eq_Yv_of_type_t1 hAB h hv hvπ)))
      · exact Or.inr (Or.inr (Or.inr
          (m.eq_conj_Yv_of_type_t2 hrRK.1 hrRK.2 hrE hAB h hv hvπ)))
      · exact Or.inr (Or.inl (show A = conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x by
          rw [m.Qx_eq]; exact m.eq_VD_of_type_E hAB h))
    · rintro (rfl | rfl | rfl | rfl)
      · exact (hRB _).2 m.Q_isMax
      · exact (hRB _).2 m.Qx_isMax
      · exact (hRB _).2 (m.Yv_isMax hv hvπ).1
      · exact (hRB _).2 (C56.isMaxElemAbelian_conjSubgroup (m.Yv_isMax hv hvπ).1 hrNB)

include m in
theorem pCore_le_blockU : pCoreOf 2 K ≤ blockU K := by
  have hshort := C.short
  have hUK : blockU K ≤ K := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K)
  have hVN : conjSubgroup (blockU K) x ≤ Subgroup.normalizer (K : Set G) :=
    (C.conj_le_B m.hxR).trans C.hBN
  have hzE : AppC.zA ∈ Eset := by decide +kernel
  have hzV : AppC.zA ∈ C.P.im (conjSubgroup (blockU K) x) := by
    rw [C.im_conj_eq m.hxR m.hne]; exact (mem_Estd _).2 hzE
  obtain ⟨t₀, ht₀V, ht₀z⟩ := (C.P.mem_im_pf hVN).1 hzV
  have ht₀B : t₀ ∈ baum R := C.conj_le_B m.hxR ht₀V
  have ht₀N : t₀ ∈ Subgroup.normalizer (K : Set G) := C.hBN ht₀B
  have ht₀2 : t₀ * t₀ = 1 := by
    have := m.V_sq ht₀V
    rwa [pow_two] at this
  obtain ⟨ℓ₀, hℓ₀⟩ := C.P.hα ⟨AppC.zA, Equiv.Perm.mem_alternatingGroup.2 AppC.zA_sign⟩
  have hℓ₀N : (ℓ₀ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer ℓ₀.2
  have hpℓ₀ : C.P.pf (ℓ₀ : G) = AppC.zA := by
    rw [C.P.pf_eq hℓ₀N, C.P.hπα (ℓ₀ : G) ℓ₀.2, hℓ₀]
  have hℓ₀inv : (ℓ₀ : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hℓ₀N
  have hyN : (ℓ₀ : G)⁻¹ * t₀ ∈ Subgroup.normalizer (K : Set G) := mul_mem hℓ₀inv ht₀N
  have hypf : C.P.pf ((ℓ₀ : G)⁻¹ * t₀) = 1 := by
    rw [C.P.pf_mul hℓ₀inv ht₀N, C.P.pf_inv hℓ₀N, hpℓ₀, ht₀z, inv_mul_cancel]
  have hyC : ∀ u ∈ blockU K, ((ℓ₀ : G)⁻¹ * t₀) * u = u * ((ℓ₀ : G)⁻¹ * t₀) := by
    intro u hu
    have hypf' := hypf
    rw [C.P.pf_eq hyN] at hypf'
    have h2 := (C.P.hker ⟨_, hyN⟩).1 hypf' u hu
    calc ((ℓ₀ : G)⁻¹ * t₀) * u = (((ℓ₀ : G)⁻¹ * t₀) * u * ((ℓ₀ : G)⁻¹ * t₀)⁻¹) *
          ((ℓ₀ : G)⁻¹ * t₀) := by group
      _ = u * ((ℓ₀ : G)⁻¹ * t₀) := by rw [h2]
  have hB2 : IsPGroup 2 (baum R) := C.R2.to_le C.hBR
  have hXN : K ⊔ baum R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer C.hBN
  have hXeq : (K ⊔ baum R) ⊓ Subgroup.centralizer (blockU K : Set G) = pCoreOf 2 (K ⊔ baum R) :=
    C1.inf_centralizer_blockU_eq C.short le_sup_left hXN
      (fun g hg => C1.exists_pow_mem_of_mem_sup hB2 C.hBN hg)
  have hyX : (ℓ₀ : G)⁻¹ * t₀ ∈ (K ⊔ baum R) ⊓ Subgroup.centralizer (blockU K : Set G) :=
    ⟨(K ⊔ baum R).mul_mem ((K ⊔ baum R).inv_mem (Subgroup.mem_sup_left ℓ₀.2))
      (Subgroup.mem_sup_right ht₀B),
      Subgroup.mem_centralizer_iff.2 fun u hu => (hyC u hu).symm⟩
  rw [hXeq, C.Q_UD] at hyX
  obtain ⟨u, hu, d, hd, hud⟩ := C5.mem_sup_of_commute (fun u hu d hd => C.U_comm_D hu hd) hyX
  have huK : u ∈ K := hUK hu
  have hdd : d * d = 1 := by
    have := m.hD.2 d hd
    rwa [pow_two] at this
  have hℓ2 : ((ℓ₀ : G) * u) * ((ℓ₀ : G) * u) = 1 := by
    set ℓ : G := (ℓ₀ : G) * u with hℓdef
    have htd : t₀ = ℓ * d := by
      calc t₀ = (ℓ₀ : G) * ((ℓ₀ : G)⁻¹ * t₀) := by group
        _ = (ℓ₀ : G) * (u * d) := by rw [hud]
        _ = ℓ * d := by rw [hℓdef]; group
    have hℓK : ℓ ∈ K := K.mul_mem ℓ₀.2 huK
    have hdc : d * ℓ = ℓ * d := (Subgroup.mem_centralizer_iff.1 hd.2 ℓ hℓK).symm
    calc ℓ * ℓ = ℓ * ℓ * (d * d) := by rw [hdd, mul_one]
      _ = ℓ * (ℓ * d) * d := by group
      _ = ℓ * (d * ℓ) * d := by rw [hdc]
      _ = (ℓ * d) * (ℓ * d) := by group
      _ = t₀ * t₀ := by rw [← htd]
      _ = 1 := ht₀2
  have hmem : ∀ q ∈ C.P.α.ker, (q : G) ∈ blockQ K := fun q hq => by
    rw [C.P.hαk] at hq
    exact (AppC.mem_pCore_iff_mem_blockQ q).1 hq
  have hN : ((blockU K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).mpr (C1.le_normalizer_blockU K)
  have hqQ : ∀ q ∈ C.P.α.ker, (q : G) ∈ pCoreOf 2 (K ⊔ baum R) := fun q hq => by
    have hq' := hmem q hq
    have hle : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ baum R) := by
      refine C1.le_pCoreOf_of_normalized
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K).trans le_sup_left) ?_
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K)
      refine sup_le (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K)
        (fun b hb => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (C.hBN hb))
    exact hle hq'
  have key := AppC.central_cover_trivial (Λ := ↥K) C.short.1 C.P.α C.P.hα
    ((blockU K).subgroupOf K)
    (fun u hu => by
      rw [MonoidHom.mem_ker]
      have hu' : u ∈ C.P.α.ker := by
        rw [C.P.hαk]
        exact (AppC.mem_pCore_iff_mem_blockQ u).2
          (C1.blockU_le_blockQ C.short (Subgroup.mem_subgroupOf.1 hu))
      exact hu')
    (fun q hq => by
      apply Subtype.ext
      have := m.Q_elem.2 (q : G) (hqQ q hq)
      simpa [pow_two] using this)
    (fun q hq g => Subgroup.mem_subgroupOf.2 (C1.commutator_mem_blockU (hmem q hq) g.2))
    (ℓ₀ * ⟨u, huK⟩) (by apply Subtype.ext; exact hℓ2)
    (by
      have hu' : (⟨u, huK⟩ : ↥K) ∈ C.P.α.ker := by
        rw [C.P.hαk]
        exact (AppC.mem_pCore_iff_mem_blockQ _).2
          (C1.blockU_le_blockQ C.short hu)
      rw [map_mul, MonoidHom.mem_ker.1 hu', mul_one, hℓ₀])
  intro q hq
  have hqK : q ∈ K := C1.blockQ_le K hq
  have hk : (⟨q, hqK⟩ : ↥K) ∈ C.P.α.ker := by
    rw [C.P.hαk]
    exact (AppC.mem_pCore_iff_mem_blockQ _).2 hq
  exact Subgroup.mem_subgroupOf.1 (key hk)

end Mate

namespace Good

variable {C : burnsideC5x_A5Cfg R K} {x : G} (m : Good C x)

include m in
theorem V_sq {a : G} (ha : a ∈ conjSubgroup (blockU K) x) : a ^ 2 = 1 :=
  ((C1.elemAb2_blockU C.short).conjSubgroup x).2 a ha

include m in
theorem V_comm {a b : G} (ha : a ∈ conjSubgroup (blockU K) x)
    (hb : b ∈ conjSubgroup (blockU K) x) : a * b = b * a :=
  ((C1.elemAb2_blockU C.short).conjSubgroup x).1 a ha b hb

include m in
theorem cent_U_V : blockU K ⊓ Subgroup.centralizer
    ((conjSubgroup (blockU K) x : Subgroup G) : Set G) = blockU K ⊓ conjSubgroup (blockU K) x :=
  (C.inf_C_conj m.hxR m.hne).trans (C.commutator_conj m.hxR m.hne).2.symm

include m in
theorem VU_sq {v u : G} (hv : v ∈ conjSubgroup (blockU K) x) (hu : u ∈ blockU K) :
    (v * u) ^ 2 ∈ blockU K := by
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := C.hBN (C.conj_le_B m.hxR hv)
  have hm : v * u * v⁻¹ ∈ blockU K := AppC.PiData.conj_mem_U hvN hu
  have hv2 : v * v = 1 := by rw [← pow_two]; exact m.V_sq hv
  have : (v * u) ^ 2 = (v * u * v⁻¹) * u := by
    calc (v * u) ^ 2 = v * u * (v * u) := by rw [pow_two]
      _ = (v * u * v⁻¹) * (v * v) * u := by group
      _ = (v * u * v⁻¹) * u := by rw [hv2, mul_one]
  rw [this]
  exact mul_mem hm hu

include m in
theorem comm_VU_mem_U {v u v' u' : G} (hv : v ∈ conjSubgroup (blockU K) x) (hu : u ∈ blockU K)
    (hv' : v' ∈ conjSubgroup (blockU K) x) (hu' : u' ∈ blockU K) :
    (v * u) * (v' * u') * (v * u)⁻¹ * (v' * u')⁻¹ ∈ blockU K := by
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := C.hBN (C.conj_le_B m.hxR hv)
  have hv'N : v' ∈ Subgroup.normalizer (K : Set G) := C.hBN (C.conj_le_B m.hxR hv')
  have hvv'N : v * v' ∈ Subgroup.normalizer (K : Set G) := mul_mem hvN hv'N
  have hu₃ : (v'⁻¹ * u * v') * u' ∈ blockU K := by
    have := AppC.PiData.conj_mem_U (inv_mem hv'N) hu
    simpa using mul_mem this hu'
  have hu₄ : (v⁻¹ * u' * v) * u ∈ blockU K := by
    have := AppC.PiData.conj_mem_U (inv_mem hvN) hu'
    simpa using mul_mem this hu
  have hcomm : v * v' = v' * v := m.V_comm hv hv'
  have h3 : (v * u) * (v' * u') = (v * v') * ((v'⁻¹ * u * v') * u') := by group
  have h4 : (v' * u') * (v * u) = (v * v') * ((v⁻¹ * u' * v) * u) := by
    calc (v' * u') * (v * u) = (v' * v) * ((v⁻¹ * u' * v) * u) := by group
      _ = (v * v') * ((v⁻¹ * u' * v) * u) := by rw [← hcomm]
  have e : (v * u) * (v' * u') * (v * u)⁻¹ * (v' * u')⁻¹ =
      (v * v') * (((v'⁻¹ * u * v') * u') * ((v⁻¹ * u' * v) * u)⁻¹) * (v * v')⁻¹ := by
    calc (v * u) * (v' * u') * (v * u)⁻¹ * (v' * u')⁻¹
        = ((v * u) * (v' * u')) * ((v' * u') * (v * u))⁻¹ := by group
      _ = ((v * v') * ((v'⁻¹ * u * v') * u')) * ((v * v') * ((v⁻¹ * u' * v) * u))⁻¹ := by
          rw [← h3, ← h4]
      _ = _ := by group
  rw [e]
  exact AppC.PiData.conj_mem_U hvv'N (mul_mem hu₃ (inv_mem hu₄))

include m in
theorem le_VD_of_comm {A : Subgroup G} (hAB : A ≤ baum R)
    (hty : ∀ g, g ∈ C.P.im A ↔ g ∈ Eset)
    (hDA : baum R ⊓ Subgroup.centralizer (K : Set G) ≤ A)
    (hsq : ∀ v ∈ conjSubgroup (blockU K) x, ∀ u ∈ blockU K, v * u ∈ A → (v * u) ^ 2 = 1)
    (hcm : ∀ v ∈ conjSubgroup (blockU K) x, ∀ u ∈ blockU K, v * u ∈ A →
      ∀ v' ∈ conjSubgroup (blockU K) x, ∀ u' ∈ blockU K, v' * u' ∈ A →
        (v * u) * (v' * u') = (v' * u') * (v * u)) :
    A ≤ conjSubgroup (blockU K) x ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAB.trans C.hBN
  have hVN : conjSubgroup (blockU K) x ≤ Subgroup.normalizer (K : Set G) :=
    (C.conj_le_B m.hxR).trans C.hBN
  have hex : ∀ g ∈ Eset, ∃ v ∈ conjSubgroup (blockU K) x, ∃ u ∈ blockU K,
      v * u ∈ A ∧ C.P.pf v = g := by
    intro g hg
    have hgA : g ∈ C.P.im A := (hty g).2 hg
    obtain ⟨a, haA, hpa⟩ := (C.P.mem_im_pf hAN).1 hgA
    obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := m.exists_vud (hAB haA) (by rw [hpa]; exact hg)
    refine ⟨v, hv, u, hu, ?_, by rw [hpv, hpa]⟩
    have := mul_mem haA (inv_mem (hDA hd))
    rw [hadec] at this
    simpa [mul_assoc] using this
  have hfixu : ∀ v ∈ conjSubgroup (blockU K) x, ∀ u ∈ blockU K, v * u ∈ A →
      vact (C.P.pf v) (C.P.bf u) = C.P.bf u := by
    intro v hv u hu hvu
    have hcom := Mate.comm_of_sq (hsq v hv u hu hvu) (m.V_sq hv) (C.hU.2 u hu)
    exact (C.P.comm_iff (hVN hv) hu).1 hcom
  obtain ⟨v₁, hv₁, u₁, hu₁, h₁A, hp₁⟩ := hex (Equiv.swap 0 1) AppC.t1_mem_Eset
  obtain ⟨v₂, hv₂, u₂, hu₂, h₂A, hp₂⟩ := hex (Equiv.swap 2 3) AppC.t2_mem_Eset
  have hf₁ := hfixu v₁ hv₁ u₁ hu₁ h₁A
  have hf₂ := hfixu v₂ hv₂ u₂ hu₂ h₂A
  rw [hp₁] at hf₁
  rw [hp₂] at hf₂
  have hcomm12 : (v₁ * u₁) * (v₂ * u₂) = (v₂ * u₂) * (v₁ * u₁) :=
    hcm v₁ hv₁ u₁ hu₁ h₁A v₂ hv₂ u₂ hu₂ h₂A
  have hrel := (C.P.comm_vu (hVN hv₁) (hVN hv₂) hu₁ hu₂ (m.V_comm hv₁ hv₂)).1 hcomm12
  rw [hp₁, hp₂, Equiv.swap_inv, Equiv.swap_inv] at hrel
  have hrel' : pact (Equiv.swap 2 3) (C.P.bf u₁).1 + (C.P.bf u₂).1 =
      pact (Equiv.swap 0 1) (C.P.bf u₂).1 + (C.P.bf u₁).1 := congrArg Subtype.val hrel
  obtain ⟨hF1, hF2⟩ := AppC.E_comm _ _ hrel'
  have hF1' : ∀ σ ∈ Eset, vact σ (C.P.bf u₁) = C.P.bf u₁ := fun σ hσ =>
    Subtype.ext (AppC.fixE_of _ (congrArg Subtype.val hf₁) hF1 σ hσ)
  have hF2' : ∀ σ ∈ Eset, vact σ (C.P.bf u₂) = C.P.bf u₂ := fun σ hσ =>
    Subtype.ext (AppC.fixE_of _ hF2 (congrArg Subtype.val hf₂) σ hσ)
  intro a ha
  have hpa : C.P.pf a ∈ Eset := (hty _).1 ((C.P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩)
  obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := m.exists_vud (hAB ha) hpa
  have hvu : v * u ∈ A := by
    have := mul_mem ha (inv_mem (hDA hd))
    rw [hadec] at this
    simpa [mul_assoc] using this
  have hpvE : C.P.pf v ∈ Eset := by rw [hpv]; exact hpa
  have hinvE : (C.P.pf v)⁻¹ ∈ Eset := Eset_inv _ hpvE
  have hfix1 : vact (Equiv.swap 0 1) (C.P.bf u) = C.P.bf u := by
    have hcom : (v * u) * (v₁ * u₁) = (v₁ * u₁) * (v * u) :=
      hcm v hv u hu hvu v₁ hv₁ u₁ hu₁ h₁A
    have h := (C.P.comm_vu (hVN hv) (hVN hv₁) hu hu₁ (m.V_comm hv hv₁)).1 hcom
    rw [hp₁, Equiv.swap_inv, hF1' _ hinvE] at h
    rw [add_comm (C.P.bf u₁) (C.P.bf u)] at h
    exact add_right_cancel h
  have hfix2 : vact (Equiv.swap 2 3) (C.P.bf u) = C.P.bf u := by
    have hcom : (v * u) * (v₂ * u₂) = (v₂ * u₂) * (v * u) :=
      hcm v hv u hu hvu v₂ hv₂ u₂ hu₂ h₂A
    have h := (C.P.comm_vu (hVN hv) (hVN hv₂) hu hu₂ (m.V_comm hv hv₂)).1 hcom
    rw [hp₂, Equiv.swap_inv, hF2' _ hinvE] at h
    rw [add_comm (C.P.bf u₂) (C.P.bf u)] at h
    exact add_right_cancel h
  have hallE : ∀ σ ∈ Eset, vact σ (C.P.bf u) = C.P.bf u := fun σ hσ =>
    Subtype.ext (AppC.fixE_of _ (congrArg Subtype.val hfix1) (congrArg Subtype.val hfix2) σ hσ)
  have huC : u ∈ Subgroup.centralizer ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    have hwE : C.P.pf w ∈ Eset := by
      have : C.P.pf w ∈ C.P.im (conjSubgroup (blockU K) x) :=
        (C.P.mem_im_pf hVN).2 ⟨w, hw, rfl⟩
      rw [C.im_conj_eq m.hxR m.hne] at this
      exact (mem_Estd _).1 this
    exact (C.P.comm_iff (hVN hw) hu).2 (hallE _ hwE)
  have huV : u ∈ conjSubgroup (blockU K) x := by
    have : u ∈ blockU K ⊓ Subgroup.centralizer
        ((conjSubgroup (blockU K) x : Subgroup G) : Set G) := ⟨hu, huC⟩
    rw [m.cent_U_V] at this
    exact this.2
  rw [hadec]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem hv huV)) (Subgroup.mem_sup_right hd)

include m in
theorem gamma_Y {Y : Subgroup G} (hYD : Y ≤ baum R ⊓ Subgroup.centralizer (K : Set G))
    (hYQ : burnsideC5x_YCls Y (pCoreOf 2 (K ⊔ baum R))) {y : G}
    (hy : y ∈ Subgroup.normalizer (R : Set G)) (hyY : conjSubgroup Y y = Y) :
    conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y = pCoreOf 2 (K ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y = conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x := by
  have hyB : y ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hy
  have hBB : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y ≤ baum R := by
    have := C5.conjSubgroup_mono C.hQB y
    rwa [C5.conjSubgroup_eq_self hyB] at this
  have hBN : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y ≤ Subgroup.normalizer (K : Set G) :=
    hBB.trans C.hBN
  have hBcard : Nat.card ↥(conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y) =
      16 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [C5.card_conjSubgroup]; exact C.card_Q
  have hBY : burnsideC5x_YCls Y (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y) := by
    have := burnsideC5x_YCls_conj hYQ y
    rwa [hyY] at this
  have hRB : R ≤ Subgroup.normalizer
      ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y : Subgroup G) : Set G) :=
    C5.le_normalizer_conj hy C.hRQ
  have hnorm := C.im_normalized hRB
  have hdpos : 0 < Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  have hle := C.card_le_YCls hYD hBB hBY
  rcases burnsideC5x_normal_E _ (C.im_le hBB) hnorm with h1 | h4 | h16
  ·
    left
    have hbot : C.P.im (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y) = ⊥ :=
      Subgroup.card_eq_one.1 h1
    have hBQ : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y ≤ pCoreOf 2 (K ⊔ baum R) := by
      intro b hb
      have : C.P.pf b ∈ C.P.im (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y) :=
        (C.P.mem_im_pf hBN).2 ⟨b, hb, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (C.mem_Q_iff (hBB hb)).2 this
    exact Subgroup.eq_of_le_of_card_ge hBQ (by rw [C5.card_conjSubgroup])
  ·
    right
    have hπE : C.P.im (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y) = Estd :=
      Subgroup.eq_of_le_of_card_ge (C.im_le hBB) (by rw [h4, Estd_card])
    have hty : ∀ g, g ∈ C.P.im (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y) ↔ g ∈ Eset :=
      fun g => by rw [hπE]; exact mem_Estd g
    have hfix4 : Nat.card ↥(AppC.FixΔ (C.P.im (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y))) = 4 := by
      rw [hπE, ← C.hB, ← C.P.card_fix C.hBN]
      exact C.card_W
    have hKB := C.Kpp_le hYD hBB hBY
    have hX : Nat.card ↥((blockU K ⊓ Subgroup.centralizer
        ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y : Subgroup G) : Set G)) ⊔
          (baum R ⊓ Subgroup.centralizer (K : Set G))) =
        4 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
      have h := B2F.card_sup_mul_card_inf_of_commute
        (A := blockU K ⊓ Subgroup.centralizer
          ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y : Subgroup G) : Set G))
        (B := baum R ⊓ Subgroup.centralizer (K : Set G))
        (fun u hu d hd => C.U_comm_D hu.1 hd)
      have hinf : (blockU K ⊓ Subgroup.centralizer
          ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y : Subgroup G) : Set G)) ⊓
            (baum R ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
        refine eq_bot_iff.2 fun z hz => ?_
        have : z ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) := ⟨hz.1.1, hz.2⟩
        rwa [C.U_inf_D] at this
      rw [hinf, Subgroup.card_bot, mul_one, C.P.card_fix hBN, hfix4] at h
      exact h
    have hkB : Nat.card ↥(conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y ⊓ pCoreOf 2 (K ⊔ baum R)) =
        4 * Nat.card ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) := by
      have h1' := C.P.card_im_mul hBN
      rw [C.inf_cent_U_eq hBB, h4, hBcard] at h1'
      omega
    have hEq : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y ⊓ pCoreOf 2 (K ⊔ baum R) =
        (blockU K ⊓ Subgroup.centralizer
          ((conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y : Subgroup G) : Set G)) ⊔
          (baum R ⊓ Subgroup.centralizer (K : Set G)) :=
      Subgroup.eq_of_le_of_card_ge hKB (by rw [hX, hkB])
    have hDB : baum R ⊓ Subgroup.centralizer (K : Set G) ≤
        conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y := by
      intro d hd
      have : d ∈ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y ⊓ pCoreOf 2 (K ⊔ baum R) := by
        rw [hEq]; exact Subgroup.mem_sup_right hd
      exact this.1
    have hsq : ∀ v ∈ conjSubgroup (blockU K) x, ∀ u ∈ blockU K,
        v * u ∈ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y → (v * u) ^ 2 = 1 := by
      intro v hv u hu hvu
      have h2 : (v * u) ^ 2 ∈ blockU K := m.VU_sq hv hu
      have h3 : (v * u) ^ 2 ∈ blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) :=
        ⟨h2, hYD (hBY.1 _ hvu)⟩
      rw [C.U_inf_D, Subgroup.mem_bot] at h3
      exact h3
    have hcm : ∀ v ∈ conjSubgroup (blockU K) x, ∀ u ∈ blockU K,
        v * u ∈ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y →
        ∀ v' ∈ conjSubgroup (blockU K) x, ∀ u' ∈ blockU K,
          v' * u' ∈ conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y →
          (v * u) * (v' * u') = (v' * u') * (v * u) := by
      intro v hv u hu hvu v' hv' u' hu' hvu'
      have h2 := m.comm_VU_mem_U hv hu hv' hu'
      have h3 : (v * u) * (v' * u') * (v * u)⁻¹ * (v' * u')⁻¹ ∈
          blockU K ⊓ (baum R ⊓ Subgroup.centralizer (K : Set G)) :=
        ⟨h2, hYD (hBY.2 _ hvu _ hvu')⟩
      rw [C.U_inf_D, Subgroup.mem_bot] at h3
      calc (v * u) * (v' * u')
          = ((v * u) * (v' * u') * (v * u)⁻¹ * (v' * u')⁻¹) * ((v' * u') * (v * u)) := by group
        _ = (v' * u') * (v * u) := by rw [h3, one_mul]
    have hle2 := m.le_VD_of_comm hBB hty hDB hsq hcm
    rw [← m.Qx_eq] at hle2
    exact Subgroup.eq_of_le_of_card_ge hle2 (by rw [C5.card_conjSubgroup, C5.card_conjSubgroup])
  · exfalso
    rw [hBcard] at hle
    nlinarith [h16, hdpos, hle]

include m in
theorem P_le_sup_inf_conj {P : Subgroup G} (hPR : P ≤ R)
    (hRP : R ≤ Subgroup.normalizer (P : Set G)) (hUP : blockU K ≤ P)
    (hQP : pCoreOf 2 (K ⊔ baum R) ≤ P) (hPU : ∀ p ∈ P, ∀ u ∈ blockU K, u * p = p * u)
    (hSC : ∀ r ∈ R, (∀ b ∈ baum R, ⁅r, b⁆ ∈ P) → r ∈ baum R ⊔ P) :
    P ≤ blockU K ⊔ (P ⊓ conjSubgroup P x) := by
  intro p hp
  have hpR : p ∈ R := hPR hp
  have hBR : baum R ≤ R := C.hBR
  have hRUx := C5.le_normalizer_conj m.hxR C.hRU
  have hRPx := C5.le_normalizer_conj m.hxR hRP
  have hUxPx : conjSubgroup (blockU K) x ≤ conjSubgroup P x := C5.conjSubgroup_mono hUP x
  have hQxPx : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x ≤ conjSubgroup P x :=
    C5.conjSubgroup_mono hQP x
  have hDx : baum R ⊓ Subgroup.centralizer (K : Set G) ≤
      conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x := by
    rw [m.Qx_eq]; exact le_sup_right
  have key : ∀ b' ∈ baum R, ⁅p, b'⁆ ∈ conjSubgroup P x := by
    intro b' hb'
    have hπ : C.P.pf b' ∈ Eset := (mem_Estd _).1
      (C.im_le le_rfl ((C.P.mem_im_pf C.hBN).2 ⟨b', hb', rfl⟩))
    obtain ⟨v, hv, u₁, hu₁, d, hd, hb'eq, -⟩ := m.exists_vud hb' hπ
    have hb'eq' : b' = v * (u₁ * d) := by rw [hb'eq]; group
    have hc : ⁅p, u₁⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hPU p hp u₁ hu₁).symm
    have e1 : ⁅p, u₁ * d⁆ = ⁅p, u₁⁆ * (u₁ * ⁅p, d⁆ * u₁⁻¹) := by
      simp only [commutatorElement_def]; group
    have e2 : ⁅p, v * (u₁ * d)⁆ = ⁅p, v⁆ * (v * ⁅p, u₁ * d⁆ * v⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hb'eq', e2, e1, hc, one_mul]
    have hvP : v ∈ conjSubgroup P x := hUxPx hv
    have hdP : d ∈ conjSubgroup P x := hQxPx (hDx hd)
    have m1 : ⁅p, v⁆ ∈ conjSubgroup P x := by
      have h1 : p * v * p⁻¹ ∈ conjSubgroup (blockU K) x :=
        (Subgroup.mem_normalizer_iff.mp (hRUx hpR) v).mp hv
      exact Subgroup.mul_mem _ (hUxPx h1) (Subgroup.inv_mem _ hvP)
    have m2 : ⁅p, d⁆ ∈ conjSubgroup P x := by
      have h1 : p * d * p⁻¹ ∈ conjSubgroup P x :=
        (Subgroup.mem_normalizer_iff.mp (hRPx hpR) d).mp hdP
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hdP)
    have hu₁R : u₁ ∈ R := hPR (hUP hu₁)
    have m3 : u₁ * ⁅p, d⁆ * u₁⁻¹ ∈ conjSubgroup P x :=
      (Subgroup.mem_normalizer_iff.mp (hRPx hu₁R) _).mp m2
    exact Subgroup.mul_mem _ m1
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hvP m3) (Subgroup.inv_mem _ hvP))
  have hrR : x * p * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp m.hxR p).mp hpR
  have hS2 : ∀ b ∈ baum R, ⁅x * p * x⁻¹, b⁆ ∈ P := by
    intro b hb
    have hb' : x⁻¹ * b * x ∈ baum R := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem m.hxB) b).mp hb
      simpa using this
    have e : ⁅x * p * x⁻¹, b⁆ = x * ⁅p, x⁻¹ * b * x⁆ * x⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mem_conjSubgroup_iff.mp (key _ hb')
  have hBP : baum R ≤ Subgroup.normalizer (P : Set G) := hBR.trans hRP
  obtain ⟨b₂, hb₂, p₂, hp₂, hr⟩ := C5.mem_sup_of_le_normalizer hBP (hSC _ hrR hS2)
  have hb₃ : x⁻¹ * b₂ * x ∈ baum R := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem m.hxB) b₂).mp hb₂
    simpa using this
  have hp₃ : x⁻¹ * p₂ * x ∈ conjSubgroup P x := by
    rw [mem_conjSubgroup_iff]; simpa [mul_assoc] using hp₂
  have hpeq : p = (x⁻¹ * b₂ * x) * (x⁻¹ * p₂ * x) := by
    calc p = x⁻¹ * (x * p * x⁻¹) * x := by group
      _ = x⁻¹ * (b₂ * p₂) * x := by rw [hr]
      _ = (x⁻¹ * b₂ * x) * (x⁻¹ * p₂ * x) := by group
  have hQN : pCoreOf 2 (K ⊔ baum R) ≤ Subgroup.normalizer
      ((conjSubgroup (blockU K) x : Subgroup G) : Set G) :=
    C.hQB.trans (C5.le_normalizer_conj m.hxB C.hBU)
  have hb₃' : x⁻¹ * b₂ * x ∈ pCoreOf 2 (K ⊔ baum R) ⊔ conjSubgroup (blockU K) x := by
    rw [sup_comm, C.sup_Q_conj m.hxR m.hne]; exact hb₃
  obtain ⟨q₀, hq₀, u'', hu'', hb₃eq⟩ := C5.mem_sup_of_le_normalizer hQN hb₃'
  have hq₀' := hq₀
  rw [C.Q_UD] at hq₀'
  obtain ⟨u₁, hu₁, d, hd, rfl⟩ := C5.mem_sup_of_commute (fun u hu d hd => C.U_comm_D hu hd) hq₀'
  have hy : d * u'' * (x⁻¹ * p₂ * x) ∈ conjSubgroup P x :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQxPx (hDx hd)) (hUxPx hu'')) hp₃
  have hpeq' : p = u₁ * (d * u'' * (x⁻¹ * p₂ * x)) := by
    rw [hpeq, hb₃eq]; simp [mul_assoc]
  have hyP : d * u'' * (x⁻¹ * p₂ * x) ∈ P := by
    have : d * u'' * (x⁻¹ * p₂ * x) = u₁⁻¹ * p := by rw [hpeq']; simp
    rw [this]
    exact P.mul_mem (P.inv_mem (hUP hu₁)) hp
  rw [hpeq']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁) (Subgroup.mem_sup_right ⟨hyP, hy⟩)

end Good

end burnsideC5x_A5Cfg

end A5

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_a5_gamma (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hRN : R ≤ Subgroup.normalizer (K₁ : Set G)) (hx : GoodX H M₀ K₁ x) (h5 : IsAltType K₁ 5) {y : G}
    (hy : y ∈ Subgroup.normalizer (R : Set G))
    (hyY : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) y =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) :
    conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) y = pCoreOf 2 (K₁ ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) y = conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x := by
  obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset hRN h5
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := hset.hyp1.R_norm hx.1
  have m : burnsideC5x_A5Cfg.Good C x := ⟨hxR, hx.2.2⟩
  have hD2 : IsPGroup 2 ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G)) :=
    (C.R2.to_le C.hBR).to_le inf_le_left
  have hYQ := burnsideC5x_YCls_of_UD C.Q_UD (fun q hq u hu => C.Q_comm_U hq hu)
    (C1.blockU_sq C.short) (fun u hu d hd => C.U_comm_D hu hd) hD2
  exact m.gamma_Y (Subgroup.map_subtype_le _) hYQ hy hyY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_a5_P4 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hRN : R ≤ Subgroup.normalizer (K₁ : Set G)) (hx : GoodX H M₀ K₁ x) (h5 : IsAltType K₁ 5) :
    burnsideC5x_P4 R K₁ x := by
  obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset hRN h5
  exact C.part4 (hset.hyp1.R_norm hx.1) hx.2.2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_a5_5 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hRN : R ≤ Subgroup.normalizer (K₁ : Set G)) (hx : GoodX H M₀ K₁ x) (h5 : IsAltType K₁ 5) :
    Even (orderOf x) := by
  obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset hRN h5
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := hset.hyp1.R_norm hx.1
  have h4 : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) x =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) :=
    C.part4 hxR hx.2.2
  have hY2 : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) (x * x) =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, h4, h4]
  have hne : conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x ≠ pCoreOf 2 (K₁ ⊔ baum R) := by
    intro heq
    apply (burnsideC5x_not_le_Q C.Q_eq hx.2.2).1
    have := C5.conjSubgroup_mono C.hUQ x
    rw [heq] at this
    exact this
  refine burnsideC5x_even_of_sq hne ?_
  rcases burnsideC5x_a5_gamma h116 hset hRN hx h5 (y := x * x) (mul_mem hxR hxR) hY2 with h | h
  · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h
  · exfalso
    apply hne
    have h2 : conjSubgroup (conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) (x * x)) x⁻¹ =
        conjSubgroup (conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x) x⁻¹ :=
      congrArg (fun A => conjSubgroup A x⁻¹) h
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_right,
      C5.conjSubgroup_conjSubgroup_inv] at h2
    exact h2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_a5_S1Str (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hRN : R ≤ Subgroup.normalizer (K₁ : Set G)) (hx : GoodX H M₀ K₁ x) (h5 : IsAltType K₁ 5)
    (hfr : (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥) :
    burnsideC5x_S1Str R K₁ x := by
  obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset hRN h5
  have hD2 : C5.ElemAb2 (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) :=
    burnsideC5x_elemAb_of_frattini ((C.R2.to_le C.hBR).to_le inf_le_left) hfr
  have hsyl : IsSylowTwoOf (R ⊓ K₁) K₁ := by
    have := burnsideC5h_p1_isSylow_inf hset (TH.one_mem)
    rwa [burnsideC5h_c54_conjByElt_one] at this
  exact burnsideC5x_A5Cfg.Mate.S1Str_a5
    (⟨⟨hset.hyp1.R_norm hx.1, hx.2.2⟩, hD2⟩ : burnsideC5x_A5Cfg.Mate C x) hsyl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_P4 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hx : GoodX H M₀ K₁ x) : burnsideC5x_P4 R K₁ x := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · exact burnsideC5x_lin2A3_4 h116 hset hx (Or.inl hL)
  · exact burnsideC5x_lin2A3_4 h116 hset hx (Or.inr h3)
  · exact burnsideC5x_a5_P4 h116 hset (burnsideC5x_s1_RN hset hs1) hx h5

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_gamma (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hx : GoodX H M₀ K₁ x) {y : G}
    (hy : y ∈ Subgroup.normalizer (R : Set G))
    (hyY : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) y =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) :
    conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) y = pCoreOf 2 (K₁ ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) y = conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · exact burnsideC5x_lin2A3_gamma h116 hset hx (Or.inl hL)
      (normalizer_le_normalizer_baum R hy) hyY
  · exact burnsideC5x_lin2A3_gamma h116 hset hx (Or.inr h3)
      (normalizer_le_normalizer_baum R hy) hyY
  · exact burnsideC5x_a5_gamma h116 hset (burnsideC5x_s1_RN hset hs1) hx h5 hy hyY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_hne (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hx : GoodX H M₀ K₁ x) :
    conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x ≠ pCoreOf 2 (K₁ ⊔ baum R) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inl hL)
    intro heq
    apply (burnsideC5x_not_le_Q hrk.Q_eq hx.2.2).1
    have := C5.conjSubgroup_mono hrk.U_le_Q x
    rw [heq] at this
    exact this
  · obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inr h3)
    intro heq
    apply (burnsideC5x_not_le_Q hrk.Q_eq hx.2.2).1
    have := C5.conjSubgroup_mono hrk.U_le_Q x
    rw [heq] at this
    exact this
  · obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset (burnsideC5x_s1_RN hset hs1) h5
    intro heq
    apply (burnsideC5x_not_le_Q C.Q_eq hx.2.2).1
    have := C5.conjSubgroup_mono C.hUQ x
    rw [heq] at this
    exact this

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_not_sylow (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hx : GoodX H M₀ K₁ x) : ¬ IsSylowTwoOf TH M₀ := by
  intro hsyl
  obtain ⟨hTHN, hK, hHeq⟩ := burnsideC5x_s1_facts hset hs1
  have hyp1 := hset.hyp1
  have hP4 := burnsideC5x_s1_P4 h116 hset hs1 hx
  set D := baum R ⊓ Subgroup.centralizer (K₁ : Set G) with hD
  set Y := CFSG.QuasithinUnique.DoubleA3.frattiniOf D with hY
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hP4
  set M₁ := M₀ ⊓ Subgroup.normalizer (Y : Set G) with hM₁
  have hxM₁ : x ∈ M₁ := ⟨hx.1, hxY⟩
  have hne := burnsideC5x_s1_hne h116 hset hs1 hx
  have hΓ : ∀ m ∈ M₁, conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = pCoreOf 2 (K₁ ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x :=
    fun m hm => burnsideC5x_s1_gamma h116 hset hs1 hx (hyp1.R_norm hm.1)
      (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hm.2)
  have hidx := burnsideC5x_relIndex_two hxM₁ hne hΓ
  have hND : ∀ m ∈ M₀, m ∈ Subgroup.normalizer (K₁ : Set G) →
      m ∈ Subgroup.normalizer (D : Set G) := fun m hm hmK =>
    C5.mem_normalizer_inf (normalizer_le_normalizer_baum R (hyp1.R_norm hm))
      (C5.mem_normalizer_centralizer hmK)
  have hTHM₁ : TH ≤ M₁ := fun t ht =>
    ⟨hyp1.TH_le ht, CFSG.QuasithinUnique.DoubleA3.mem_normalizer_frattiniOf
      (hND t (hyp1.TH_le ht) (hTHN ht))⟩
  have hNQ : ∀ t ∈ TH, t ∈ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) := fun t ht =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K₁ ⊔ baum R)
      (C1.mem_normalizer_sup (hTHN ht)
        (normalizer_le_normalizer_baum R (hyp1.R_norm (hyp1.TH_le ht))))
  have hTHN₁ : TH ≤ M₁ ⊓ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) :=
    fun t ht => ⟨hTHM₁ ht, hNQ t ht⟩
  have hN₁M₁ : M₁ ⊓ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) ≤ M₁ := inf_le_left
  have hM₁M₀ : M₁ ≤ M₀ := inf_le_left
  have h1 := Subgroup.relIndex_mul_relIndex TH
    (M₁ ⊓ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G)) M₀ hTHN₁ (hN₁M₁.trans hM₁M₀)
  have h2 := Subgroup.relIndex_mul_relIndex
    (M₁ ⊓ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G)) M₁ M₀ hN₁M₁ hM₁M₀
  rw [hidx] at h2
  apply hsyl.2.2
  have : 2 ∣ TH.relIndex M₀ := by
    rw [← h1, ← h2]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  exact this

theorem burnsideC5x_le_of_relIndex_two {G : Type} [Group G] {T M N : Subgroup G}
    (hTM : T ≤ M) (hidx : T.relIndex M = 2) (hTN : T ≤ N) {x : G} (hxM : x ∈ M) (hxN : x ∈ N)
    (hxT : x ∉ T) : M ≤ N := by
  have h1 := Subgroup.relIndex_mul_relIndex T (M ⊓ N) M (le_inf hTM hTN) inf_le_left
  rw [hidx] at h1
  have hne : T.relIndex (M ⊓ N) ≠ 1 := fun h =>
    hxT ((Subgroup.relIndex_eq_one.mp h) ⟨hxM, hxN⟩)
  have h2 : T.relIndex (M ⊓ N) = 2 := by
    have hd : T.relIndex (M ⊓ N) ∣ 2 := ⟨_, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h hne
    · exact h
  rw [h2] at h1
  have h3 : (M ⊓ N).relIndex M = 1 := by omega
  exact fun g hg => (Subgroup.relIndex_eq_one.mp h3 hg).2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_x_not_mem_TH {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {x : G} (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hx : GoodX H M₀ K₁ x) : x ∉ TH := by
  intro hxT
  obtain ⟨hTHN, hK, hHeq⟩ := burnsideC5x_s1_facts hset hs1
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hyp1 := hset.hyp1
  have hKH : K₁ ≤ H := hset.config.chi0.1.2.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hHU : H ≤ Subgroup.normalizer (blockU K₁ : Set G) := by
    rw [hHeq]
    exact sup_le (fun t ht => C1.mem_normalizer_blockU (hTHN ht))
      (fun k hk => C1.mem_normalizer_blockU (Subgroup.le_normalizer hk))
  have hUO : blockU K₁ ≤ pCoreOf 2 H :=
    C1.le_pCoreOf_of_normalized (hUK.trans hKH) hHU (C1.isPGroup_blockU hshort)
  have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H
      (Subgroup.le_normalizer (hyp1.sylow.1 hxT))
  apply hx.2.1
  have := C5.conjSubgroup_mono hUO x
  rwa [C5.conjSubgroup_eq_self hxN] at this

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_noCommon {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {x : G} (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x) {X : Subgroup G} (hXR : X ≤ R)
    (hTHX : TH ≤ Subgroup.normalizer (X : Set G)) (hKX : K₁ ≤ Subgroup.normalizer (X : Set G))
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  obtain ⟨hTHN, hK, hHeq⟩ := burnsideC5x_s1_facts hset hs1
  have hM₀X : M₀ ≤ Subgroup.normalizer (X : Set G) :=
    burnsideC5x_le_of_relIndex_two hset.hyp1.TH_le hidx hTHX hx.1 hxX
      (burnsideC5x_x_not_mem_TH hset hs1 hx)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hHeq]; exact sup_le hTHX hKX
  by_contra hne
  exact hset.hyp2 X hXR hne (sup_le hM₀X hHX)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_TH_normalizes_D {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) :
    TH ≤ Subgroup.normalizer ((baum R ⊓ Subgroup.centralizer (K₁ : Set G) : Subgroup G) : Set G) :=
  fun t ht => C5.mem_normalizer_inf
    (normalizer_le_normalizer_baum R (hset.hyp1.R_norm (hset.hyp1.TH_le ht)))
    (C5.mem_normalizer_centralizer ((burnsideC5x_s1_facts hset hs1).1 ht))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_frattini {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {x : G} (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x) (h4 : burnsideC5x_P4 R K₁ x) :
    (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥ := by
  have hND := burnsideC5x_s1_TH_normalizes_D hset hs1
  set D := baum R ⊓ Subgroup.centralizer (K₁ : Set G) with hD
  have hXD : CFSG.QuasithinUnique.DoubleA3.frattiniOf D ≤ D := Subgroup.map_subtype_le _
  refine burnsideC5x_s1_noCommon hset hs1 hidx hx
    (hXD.trans (inf_le_left.trans (C1GN.baum_le R))) (fun t ht =>
      CFSG.QuasithinUnique.DoubleA3.mem_normalizer_frattiniOf (hND ht)) ?_
    (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h4)
  intro k hk
  have : K₁ ≤ Subgroup.centralizer (CFSG.QuasithinUnique.DoubleA3.frattiniOf D : Set G) :=
    fun k hk => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hXD hy).2 k hk).symm
  exact Subgroup.centralizer_le_normalizer _ (this hk)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_TH_conj_mem {G : Type} [Group G] {M₀ TH : Subgroup G}
    (hTH : TH ≤ M₀) (hidx : TH.relIndex M₀ = 2) {m : G} (hm : m ∈ M₀) :
    m ∈ Subgroup.normalizer (TH : Set G) := by
  have hN : (TH.subgroupOf M₀).Normal := Subgroup.normal_of_index_eq_two hidx
  have hfwd : ∀ m ∈ M₀, ∀ t ∈ TH, m * t * m⁻¹ ∈ TH := fun m hm t ht => by
    have h1 : (⟨m, hm⟩ : M₀) * ⟨t, hTH ht⟩ * (⟨m, hm⟩ : M₀)⁻¹ ∈ TH.subgroupOf M₀ :=
      hN.conj_mem ⟨t, hTH ht⟩ (Subgroup.mem_subgroupOf.mpr ht) ⟨m, hm⟩
    exact Subgroup.mem_subgroupOf.mp h1
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => hfwd m hm t ht, fun ht => ?_⟩
  have := hfwd m⁻¹ (M₀.inv_mem hm) _ ht
  simpa [mul_assoc] using this

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_inf_conj {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {x : G} (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x) :
    (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) ⊓
      rconj x (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) = ⊥ := by
  have hND := burnsideC5x_s1_TH_normalizes_D hset hs1
  have hTHM := hset.hyp1.TH_le
  have hxsq : x * x ∈ TH := by
    have := Subgroup.mul_self_mem_of_index_two (H := TH.subgroupOf M₀) hidx ⟨x, hx.1⟩
    exact Subgroup.mem_subgroupOf.mp this
  set D := baum R ⊓ Subgroup.centralizer (K₁ : Set G) with hD
  have hDR : D ≤ R := inf_le_left.trans (C1GN.baum_le R)
  have hTHDx : TH ≤ Subgroup.normalizer ((conjSubgroup D x : Subgroup G) : Set G) := by
    intro t ht
    have hxN : x ∈ Subgroup.normalizer (TH : Set G) :=
      burnsideC5x_TH_conj_mem hTHM hidx hx.1
    have := C5.le_normalizer_conj hxN hND
    exact this ht
  have key : D ⊓ conjSubgroup D x = ⊥ := by
    refine burnsideC5x_s1_noCommon hset hs1 hidx hx (inf_le_left.trans hDR)
      (fun t ht => C5.mem_normalizer_inf (hND ht) (hTHDx ht)) ?_ ?_
    · intro k hk
      have : K₁ ≤ Subgroup.centralizer ((D ⊓ conjSubgroup D x : Subgroup G) : Set G) :=
        fun k hk => by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (Subgroup.mem_centralizer_iff.mp hy.1.2 k hk).symm
      exact Subgroup.centralizer_le_normalizer _ (this hk)
    · rw [← CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_inf,
        CFSG.Quasithin.conjSubgroup_conjSubgroup,
        C5.conjSubgroup_eq_self (hND hxsq), inf_comm]
  exact key

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_sylow {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) :
    R ≤ Subgroup.normalizer (K₁ : Set G) ∧ IsSylowTwoOf R (K₁ ⊔ R) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨hTHN, -, -⟩ := burnsideC5x_s1_facts hset hs1
  have hRN : R ≤ Subgroup.normalizer (K₁ : Set G) := fun r hr => hTHN (hset.hyp1.R_le hr)
  refine ⟨hRN, ?_⟩
  have := burnsideC5h_p3_sylow hset hK₁mem
  rwa [inf_eq_left.mpr hRN] at this

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_CRU {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) :
    R ⊓ Subgroup.centralizer (blockU K₁ : Set G) = pCoreOf 2 (K₁ ⊔ R) := by
  obtain ⟨hRN, hsyl⟩ := burnsideC5x_s1_sylow hset hs1
  exact C56.baum_inf_centralizer_eq hset.config.chi0.1.1 (hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le)
    hRN hsyl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped commutatorElement in
theorem burnsideC5x_lin2A3_SC (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) :
    ∀ r ∈ R, (∀ b ∈ baum R, ⁅r, b⁆ ∈ pCoreOf 2 (K₁ ⊔ R)) → r ∈ baum R ⊔ pCoreOf 2 (K₁ ⊔ R) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨hmin, hblk, hth, hbeq, hS1⟩ := burnsideC5x_data h116 hset hK₁mem
  obtain ⟨hRN, -⟩ := burnsideC5x_s1_sylow hset hs1
  have hnat : NaturalConcl (R ⊓ Subgroup.normalizer (K₁ : Set G))
      (K₁ ⊔ (R ⊓ Subgroup.normalizer (K₁ : Set G))) K₁ := by
    rcases hL with hl | h3
    · exact C56.natural_Lin2 hmin hblk hl hth rfl inf_le_right
    · exact C56.natural_A3 hmin hblk h3 hth rfl inf_le_right
  unfold NaturalConcl at hnat
  rw [hbeq, inf_eq_left.mpr hRN] at hnat
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hSC⟩ := hnat
  exact hSC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_Pfacts {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) :
    pCoreOf 2 (K₁ ⊔ R) ≤ R ∧ R ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ R) : Set G) ∧
      K₁ ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ R) : Set G) ∧
      TH ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ R) : Set G) ∧
      blockU K₁ ≤ pCoreOf 2 (K₁ ⊔ R) ∧ pCoreOf 2 (K₁ ⊔ baum R) ≤ pCoreOf 2 (K₁ ⊔ R) ∧
      (∀ p ∈ pCoreOf 2 (K₁ ⊔ R), ∀ u ∈ blockU K₁, u * p = p * u) ∧
      R ≤ Subgroup.normalizer (blockU K₁ : Set G) := by
  obtain ⟨hTHN, -, -⟩ := burnsideC5x_s1_facts hset hs1
  obtain ⟨hRN, hsyl⟩ := burnsideC5x_s1_sylow hset hs1
  have hCRU := burnsideC5x_s1_CRU hset hs1
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hyp1 := hset.hyp1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hKQ : K₁ ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) :=
    le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  have hBR : baum R ≤ R := C1GN.baum_le R
  have hKRN : K₁ ⊔ R ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ R) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hRU : R ≤ Subgroup.normalizer (blockU K₁ : Set G) := fun r hr =>
    C1.mem_normalizer_blockU (hRN hr)
  have hRQ : R ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) := fun r hr =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K₁ ⊔ baum R)
      (C1.mem_normalizer_sup (hRN hr) (normalizer_le_normalizer_baum R (Subgroup.le_normalizer hr)))
  refine ⟨fun g hg => hsyl.pCoreOf_le hg, le_sup_right.trans hKRN, le_sup_left.trans hKRN,
    fun t ht => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K₁ ⊔ R)
      (C1.mem_normalizer_sup (hTHN ht) (hyp1.R_norm (hyp1.TH_le ht))), ?_, ?_, ?_, hRU⟩
  · refine C1.le_pCoreOf_of_normalized (hUK.trans le_sup_left) ?_ (C1.isPGroup_blockU hshort)
    exact sup_le (C1.le_normalizer_blockU K₁) hRU
  · refine C1.le_pCoreOf_of_normalized
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (sup_le_sup_left hBR K₁)) ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    exact sup_le hKQ hRQ
  · intro p hp u hu
    exact Subgroup.mem_centralizer_iff.mp (hCRU ▸ hp : p ∈ R ⊓ Subgroup.centralizer
      (blockU K₁ : Set G)).2 u hu

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise commutatorElement in
theorem burnsideC5x_s1_P_tail {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {x : G} (hset : SetC53 H M₀ TH R K₁) (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁)
    (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x)
    (hQeq : pCoreOf 2 (K₁ ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU K₁ : Set G))
    (hQmax : IsMaxElemAbelian R (pCoreOf 2 (K₁ ⊔ baum R)))
    (h1 : pCoreOf 2 (K₁ ⊔ R) ≤ blockU K₁ ⊔
      (pCoreOf 2 (K₁ ⊔ R) ⊓ conjSubgroup (pCoreOf 2 (K₁ ⊔ R)) x))
    (h2 : pCoreOf 2 (K₁ ⊔ R) ≤ blockU K₁ ⊔
      (pCoreOf 2 (K₁ ⊔ R) ⊓ conjSubgroup (pCoreOf 2 (K₁ ⊔ R)) x⁻¹)) :
    pCoreOf 2 (K₁ ⊔ R) = pCoreOf 2 (K₁ ⊔ baum R) ∧ C5.ElemAb2 (pCoreOf 2 (K₁ ⊔ baum R)) := by
  obtain ⟨hPR, hRP, hKP, hTHP, hUP, hQP, hPU, hRU⟩ := burnsideC5x_s1_Pfacts hset hs1
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hU2 := C1.blockU_sq hshort
  set P := pCoreOf 2 (K₁ ⊔ R) with hP
  set Q := pCoreOf 2 (K₁ ⊔ baum R) with hQdef
  have e1 : P = blockU K₁ ⊔ (P ⊓ conjSubgroup P x) := le_antisymm h1 (sup_le hUP inf_le_left)
  have e2 : P = blockU K₁ ⊔ (P ⊓ conjSubgroup P x⁻¹) := le_antisymm h2 (sup_le hUP inf_le_left)
  have hcomm : ∀ A : Subgroup G, A ≤ P → ∀ u ∈ blockU K₁, ∀ a ∈ A, u * a = a * u :=
    fun A hA u hu a ha => hPU a (hA ha) u hu
  have s1 : C5.sqSub P = C5.sqSub (P ⊓ conjSubgroup P x) := by
    conv_lhs => rw [e1]
    exact C5.sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  have s2 : C5.sqSub P = C5.sqSub (P ⊓ conjSubgroup P x⁻¹) := by
    conv_lhs => rw [e2]
    exact C5.sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  have hxsq : conjSubgroup (C5.sqSub P) x = C5.sqSub P := by
    calc conjSubgroup (C5.sqSub P) x = conjSubgroup (C5.sqSub (P ⊓ conjSubgroup P x⁻¹)) x := by
          rw [← s2]
      _ = C5.sqSub (conjSubgroup (P ⊓ conjSubgroup P x⁻¹) x) := C5.conjSubgroup_sqSub _ _
      _ = C5.sqSub (P ⊓ conjSubgroup P x) := by
          rw [C5.conjSubgroup_inf, CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
            CFSG.Quasithin.conjSubgroup_one, inf_comm]
      _ = C5.sqSub P := s1.symm
  have hsq_eq_bot : C5.sqSub P = ⊥ := by
    refine burnsideC5x_s1_noCommon hset hs1 hidx hx (C5.sqSub_le_self.trans hPR)
      (fun g hg => ?_) (fun g hg => ?_)
      (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hxsq)
    · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp
        (C5.conjSubgroup_sqSub_of_mem_normalizer (hTHP hg))
    · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp
        (C5.conjSubgroup_sqSub_of_mem_normalizer (hKP hg))
  have hP2 : ∀ p ∈ P, p ^ 2 = 1 := C5.sqSub_eq_bot_iff.mp hsq_eq_bot
  have hPe : C5.ElemAb2 P := ⟨C5.comm_of_sq_eq_one hP2, hP2⟩
  have hOmega : omegaOneCenterOf (thompsonJ R) ≤ Q := by
    rw [(omegaOne_centralizer_thompsonJ R).2]
    exact iInf₂_le Q hQmax
  have hQP' : Q ≤ P := hQP
  have hPB : P ≤ baum R := by
    intro p hp
    refine ⟨hPR hp, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (hPe.1 z (hQP (hOmega hz)) p hp)
  have hPQ : P = Q := by
    refine le_antisymm ?_ hQP
    intro p hp
    rw [hQeq]
    exact ⟨hPB hp, Subgroup.mem_centralizer_iff.mpr fun u hu => hPU p hp u hu⟩
  exact ⟨hPQ, hPQ ▸ hPe⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise commutatorElement in
theorem burnsideC5x_lin2A3_P (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3)
    (hfr : (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥) :
    pCoreOf 2 (K₁ ⊔ R) = pCoreOf 2 (K₁ ⊔ baum R) ∧ C5.ElemAb2 (pCoreOf 2 (K₁ ⊔ baum R)) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem hL
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, hx2⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  obtain ⟨hPR, hRP, hKP, hTHP, hUP, hQP, hPU, hRU⟩ := burnsideC5x_s1_Pfacts hset hs1
  have hSC := burnsideC5x_lin2A3_SC h116 hset hs1 hL
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hKQ : K₁ ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) :=
    le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  have hBR : baum R ≤ R := C1GN.baum_le R
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (baum R : Set G) := inv_mem hxB
  have hx1' : ¬ conjSubgroup (blockU K₁) x⁻¹⁻¹ ≤ pCoreOf 2 (K₁ ⊔ baum R) := by
    rw [inv_inv]; exact hx1
  obtain ⟨hD, hDx⟩ := hrk.Q_eq_sup_centralizer hxB hx1 hUK hKQ hZ (hgen x hxB hx1 hx2)
  obtain ⟨-, hDx'⟩ := hrk.Q_eq_sup_centralizer hxinv hx2 hUK hKQ hZ (hgen x⁻¹ hxinv hx2 hx1')
  have hDc : ∀ u ∈ blockU K₁, ∀ a ∈ pCoreOf 2 (K₁ ⊔ baum R) ⊓ Subgroup.centralizer (K₁ : Set G),
      u * a = a * u := fun u hu a ha => Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu)
  have hU2 := C1.blockU_sq hshort
  have h1 := hrk.P_le_sup_inf_conj hPR hxR hxB hx2 hD hDc hDx hRU hRP hUP hQP hBR hPU hSC
  have h2 := hrk.P_le_sup_inf_conj (x := x⁻¹) hPR (inv_mem hxR) hxinv hx1' hD hDc hDx' hRU hRP
    hUP hQP hBR hPU hSC
  exact burnsideC5x_s1_P_tail hset hs1 hidx hx hrk.Q_eq
    ((burnsideC5x_lin2A3_S1Str h116 hset hx hL hfr).1) h1 h2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise commutatorElement in
theorem burnsideC5x_a5_P (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x)
    (h5 : IsAltType K₁ 5)
    (hfr : (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥) :
    pCoreOf 2 (K₁ ⊔ R) = pCoreOf 2 (K₁ ⊔ baum R) ∧ C5.ElemAb2 (pCoreOf 2 (K₁ ⊔ baum R)) := by
  obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset (burnsideC5x_s1_RN hset hs1) h5
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := hset.hyp1.R_norm hx.1
  have m : burnsideC5x_A5Cfg.Good C x := ⟨hxR, hx.2.2⟩
  have m' : burnsideC5x_A5Cfg.Good C x⁻¹ := ⟨inv_mem hxR, burnsideC5x_comm_inv_ne hx.2.2⟩
  obtain ⟨hPR, hRP, hKP, hTHP, hUP, hQP, hPU, hRU⟩ := burnsideC5x_s1_Pfacts hset hs1
  have hCRU := burnsideC5x_s1_CRU hset hs1
  have hSC := C.SC hCRU
  have h1 := m.P_le_sup_inf_conj hPR hRP hUP hQP hPU hSC
  have h2 := m'.P_le_sup_inf_conj hPR hRP hUP hQP hPU hSC
  exact burnsideC5x_s1_P_tail hset hs1 hidx hx C.Q_eq
    ((burnsideC5x_a5_S1Str h116 hset (burnsideC5x_s1_RN hset hs1) hx h5 hfr).1) h1 h2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_s1_123 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hx : GoodX H M₀ K₁ x) :
    burnsideC5x_P1 R K₁ x ∧ burnsideC5x_P2 R K₁ x ∧ burnsideC5x_P3 R K₁ x := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · exact burnsideC5x_lin2A3_123 h116 hset hx (Or.inl hL)
  · exact burnsideC5x_lin2A3_123 h116 hset hx (Or.inr h3)
  · obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset (burnsideC5x_s1_RN hset hs1) h5
    exact C.part123 (hset.hyp1.R_norm hx.1) hx.2.2

open scoped Pointwise in
theorem burnsideC5x_set_swap {G : Type} [Group G] {A B S : Subgroup G}
    (h : (S : Set G) = (A : Set G) * (B : Set G)) : (S : Set G) = (B : Set G) * (A : Set G) := by
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ (S : Set G) := S.inv_mem hg
    rw [h] at hg'
    obtain ⟨a, ha, b, hb, hab⟩ := hg'
    refine ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, ?_⟩
    have hab' : a * b = g⁻¹ := hab
    have : g = (a * b)⁻¹ := by rw [hab']; simp
    rw [this, mul_inv_rev]
  · rintro ⟨b, hb, a, ha, rfl⟩
    have hA : a ∈ (S : Set G) := by rw [h]; exact ⟨a, ha, 1, B.one_mem, mul_one a⟩
    have hB : b ∈ (S : Set G) := by rw [h]; exact ⟨1, A.one_mem, b, hb, one_mul b⟩
    exact S.mul_mem hB hA

theorem burnsideC5x_gaschutz_split {G : Type*} [Group G] [Finite G]
    {H V T K0 : Subgroup G} (hVH : V ≤ H) (hVT : V ≤ T) (hTH : T ≤ H)
    (hVn : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V)
    (hVp : IsPGroup 2 V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hT2 : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf H).index)
    (hK0T : K0 ≤ T) (hK0V : V ⊓ K0 = ⊥)
    (hdec : ∀ t ∈ T, ∃ v ∈ V, ∃ k ∈ K0, v * k = t) :
    ∃ A : Subgroup G, A ≤ H ∧ A ⊓ V = ⊥ ∧ V ⊔ A = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := V.subgroupOf H with hN
  have hNn : N.Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
    (by simpa using hVn g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hNc : IsMulCommutative N := ⟨⟨fun a b => by
    have h := hVc _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hNp : IsPGroup 2 N := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  have hTsub : IsPGroup 2 (T.subgroupOf H) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hPc : ((hTsub.toSylow hidx : Sylow 2 H) : Subgroup H) = T.subgroupOf H :=
    IsPGroup.toSylow_coe hTsub hidx
  obtain ⟨A₀, hA₁, hA₂⟩ := (CFSG.Quasithin.gaschutz hNp (hTsub.toSylow hidx)).mpr
    ⟨K0.subgroupOf H, by
      rw [hPc]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hK0T (Subgroup.mem_subgroupOf.mp hx)),
     by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxK⟩
      have hv : (x : G) ∈ V ⊓ K0 :=
        ⟨Subgroup.mem_subgroupOf.mp hxN, Subgroup.mem_subgroupOf.mp hxK⟩
      rw [hK0V, Subgroup.mem_bot] at hv
      rw [Subgroup.mem_bot]
      exact Subtype.ext hv,
     by
      rw [hPc]
      apply le_antisymm
      · apply sup_le
        · intro x hx
          exact Subgroup.mem_subgroupOf.mpr (hVT (Subgroup.mem_subgroupOf.mp hx))
        · intro x hx
          exact Subgroup.mem_subgroupOf.mpr (hK0T (Subgroup.mem_subgroupOf.mp hx))
      · intro x hx
        obtain ⟨v, hv, k, hk, hvk⟩ := hdec x hx
        have e : (⟨v, hVH hv⟩ : H) * ⟨k, hTH (hK0T hk)⟩ = x := Subtype.ext hvk
        rw [← e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hv))
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hk))⟩
  refine ⟨A₀.map H.subtype, Subgroup.map_subtype_le A₀, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxV⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxA
    have hkN : k ∈ N := Subgroup.mem_subgroupOf.mpr hxV
    have hk1 : k ∈ N ⊓ A₀ := ⟨hkN, hk⟩
    rw [hA₁, Subgroup.mem_bot] at hk1
    rw [Subgroup.mem_bot, hk1, map_one]
  · apply le_antisymm (sup_le hVH (Subgroup.map_subtype_le A₀))
    intro x hx
    have htop : (⟨x, hx⟩ : H) ∈ N ⊔ A₀ := by
      rw [hA₂]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp htop
    have e : (n : G) * (k : G) = x := congrArg Subtype.val hnk
    rw [← e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hn))
      (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_lin2_pCore (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hx : GoodX H M₀ K₁ x) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n)
    (hfr : (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥) :
    pCoreOf 2 K₁ ≤ blockU K₁ := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inl hn)
  have hP1 := burnsideC5h_p1_minParabolic hset (burnsideC5h_c54_one h116 hset)
  obtain ⟨hsylK, hlin, -, hUQ, hQ⟩ := burnsideC5h_p2_lin2A3 h116 hset hP1 K₁ hK₁mem (Or.inl hn)
  have hSeq := hlin hn
  obtain ⟨hxR, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, hx2⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  obtain ⟨⟨hP1a, hP1b⟩, ⟨hP2a, -, -, -, -⟩, -⟩ := burnsideC5x_lin2A3_123 h116 hset hx (Or.inl hn)
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hKQ : K₁ ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) :=
    le_sup_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
  have hR2 : IsPGroup 2 R := hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le
  have hB2 : IsPGroup 2 (baum R) := hR2.to_le (C1GN.baum_le R)
  have hD2 : C5.ElemAb2 (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) :=
    burnsideC5x_elemAb_of_frattini (hB2.to_le inf_le_left) hfr
  have hDc : ∀ u ∈ blockU K₁, ∀ a ∈ baum R ⊓ Subgroup.centralizer (K₁ : Set G), u * a = a * u :=
    fun u hu a ha => Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu)
  have hQ2 : C5.ElemAb2 (pCoreOf 2 (K₁ ⊔ baum R)) := by
    have := C5.ElemAb2.sup (C1.elemAb2_blockU hshort) hD2 (fun u hu d hd => hDc u hu d hd)
    rwa [← hP1a] at this
  set S := baum R with hS
  set Q := pCoreOf 2 (K₁ ⊔ baum R) with hQdef
  set U := blockU K₁ with hU
  set V := conjSubgroup U x with hV
  set D := baum R ⊓ Subgroup.centralizer (K₁ : Set G) with hD
  have hQS : Q ≤ S := hrk.Q_le_B
  have hVS : V ≤ S := hrk.conj_le_B hxB
  have hVN : V ≤ Subgroup.normalizer (Q : Set G) := hVS.trans hrk.B_le_normQ
  have hSN : S ≤ Subgroup.normalizer (Q : Set G) := hrk.B_le_normQ
  set M := K₁ ⊔ Q with hM
  have hMN : M ≤ Subgroup.normalizer (Q : Set G) := sup_le hKQ Subgroup.le_normalizer
  have hQM : Q ≤ M := le_sup_right
  set T := S ⊓ K₁ with hT
  have hTK : T ≤ K₁ := inf_le_right
  have hTQ : T ⊔ Q = S := by
    refine le_antisymm (sup_le inf_le_left hQS) fun g hg => ?_
    have hg' : g ∈ (S : Set G) := hg
    rw [hSeq] at hg'
    obtain ⟨a, ha, q', hq', rfl⟩ := hg'
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hq')
  have hSM : S ≤ M := by
    rw [← hTQ]; exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hidx : ¬ 2 ∣ (S.subgroupOf M).index := by
    have e1 : Q.relIndex (K₁ ⊔ Q) = Q.relIndex K₁ := C5.relIndex_sup_eq_of_le_normalizer hKQ
    have e2 : Q.relIndex (T ⊔ Q) = Q.relIndex T :=
      C5.relIndex_sup_eq_of_le_normalizer (hTK.trans hKQ)
    rw [hTQ] at e2
    have hQK : Q ⊓ K₁ ≤ T := fun g hg => ⟨hQS hg.1, hg.2⟩
    have hQT : Q ⊓ T = Q ⊓ K₁ := le_antisymm (inf_le_inf_left Q hTK) (le_inf inf_le_left hQK)
    have h1 := Subgroup.relIndex_mul_relIndex Q S M hQS hSM
    have h2 := Subgroup.relIndex_mul_relIndex (Q ⊓ K₁) T K₁ hQK hTK
    have h3 : (Q ⊓ K₁).relIndex K₁ = Q.relIndex K₁ := Subgroup.inf_relIndex_right Q K₁
    have h4 : (Q ⊓ K₁).relIndex T = Q.relIndex T := by
      rw [← hQT]; exact Subgroup.inf_relIndex_right Q T
    rw [h3, h4] at h2
    have hpos : 0 < Q.relIndex S :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Q.subgroupOf S))
    have hSMT : S.relIndex M = T.relIndex K₁ := by
      have h5 : Q.relIndex S * S.relIndex M = Q.relIndex S * T.relIndex K₁ := by
        calc Q.relIndex S * S.relIndex M = Q.relIndex M := h1
          _ = Q.relIndex (K₁ ⊔ Q) := rfl
          _ = Q.relIndex K₁ := e1
          _ = Q.relIndex T * T.relIndex K₁ := h2.symm
          _ = Q.relIndex S * T.relIndex K₁ := by rw [e2]
      exact Nat.eq_of_mul_eq_mul_left hpos h5
    have hodd : ¬ 2 ∣ (T.subgroupOf K₁).index := hsylK.2.2
    intro hdvd
    apply hodd
    have e3 : (S.subgroupOf M).index = S.relIndex M := rfl
    have e4 : (T.subgroupOf K₁).index = T.relIndex K₁ := rfl
    rw [e4, ← hSMT, ← e3]
    exact hdvd
  have hVe : IsElemAbelian 2 V :=
    C5.isElemAbelian_two_iff.mpr ((C1.elemAb2_blockU hshort).conjSubgroup x)
  obtain ⟨C₀, hC₀V, -, hdisj, hsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
    Nat.prime_two hVe (inf_le_left : V ⊓ Q ≤ V) (bot_le : ⊥ ≤ V) (inf_bot_eq _)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a :=
    ((C1.elemAb2_blockU hshort).conjSubgroup x).1
  have hdec : ∀ t ∈ S, ∃ v ∈ Q, ∃ k ∈ C₀, v * k = t := by
    intro t ht
    have ht' : t ∈ (S : Set G) := ht
    rw [hP2a] at ht'
    obtain ⟨v₀, hv₀, q₀, hq₀, rfl⟩ := ht'
    have hv₀' : v₀ ∈ (V ⊓ Q) ⊔ C₀ := by rw [hsup]; exact hv₀
    obtain ⟨w, hw, c, hc, hwc⟩ := C5.mem_sup_of_commute (A := V ⊓ Q) (B := C₀)
      (fun a ha b hb => hVc a ha.1 b (hC₀V hb)) hv₀'
    have hcq : c * q₀ * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hVN (hC₀V hc)) q₀).mp hq₀
    refine ⟨w * (c * q₀ * c⁻¹), Q.mul_mem hw.2 hcq, c, hc, ?_⟩
    calc w * (c * q₀ * c⁻¹) * c = w * c * q₀ := by group
      _ = v₀ * q₀ := by rw [← hwc]
  have hC₀Q : Q ⊓ C₀ = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    have : g ∈ (V ⊓ Q) ⊓ C₀ := ⟨⟨hC₀V hg.2, hg.1⟩, hg.2⟩
    rw [hdisj] at this
    exact this
  obtain ⟨H₀, hH₀M, hH₀Q, hQH⟩ := burnsideC5x_gaschutz_split hQM hQS hSM
    (fun h hh v hv => (Subgroup.mem_normalizer_iff.mp (hMN hh) v).mp hv)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) hQ2.1 hB2 hidx
    (hC₀V.trans hVS) hC₀Q hdec
  have hH₀N : H₀ ≤ Subgroup.normalizer (Q : Set G) := hH₀M.trans hMN
  have hMprod : ∀ m ∈ M, ∃ h ∈ H₀, ∃ q ∈ Q, m = h * q := by
    intro m hm
    have h2 : m ∈ ((H₀ ⊔ Q : Subgroup G) : Set G) := by
      show m ∈ (H₀ ⊔ Q : Subgroup G)
      rw [sup_comm, hQH]; exact hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H₀ Q hH₀N] at h2
    obtain ⟨h, hh, q, hq, rfl⟩ := h2
    exact ⟨h, hh, q, hq, rfl⟩
  have hDQ : D ≤ Q := by
    rw [hP1a]; exact le_sup_right
  have hDM : ∀ m ∈ M, ∀ d ∈ D, m * d = d * m := by
    intro m hm d hd
    have : M ≤ Subgroup.centralizer (D : Set G) := by
      refine sup_le (fun k hk => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
        (fun q hq => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
      · exact (Subgroup.mem_centralizer_iff.mp hy.2 k hk).symm
      · exact hQ2.1 y (hDQ hy) q hq
    exact (Subgroup.mem_centralizer_iff.mp (this hm) d hd).symm
  set L₀ := U ⊔ H₀ with hL₀
  have hUQ' : U ≤ Q := hrk.U_le_Q
  have hL₀M : L₀ ≤ M := sup_le (hUQ'.trans hQM) hH₀M
  have hKl : ∀ k ∈ K₁, ∃ l ∈ L₀, ∃ d ∈ D, k = l * d := by
    intro k hk
    obtain ⟨h, hh, q, hq, rfl⟩ := hMprod k (Subgroup.mem_sup_left hk)
    rw [hP1a] at hq
    obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute hDc hq
    exact ⟨h * u, L₀.mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu), d, hd,
      by group⟩
  have hconjL : ∀ g ∈ K₁, ∀ y ∈ L₀, g * y * g⁻¹ ∈ L₀ := by
    intro g hg y hy
    obtain ⟨l, hl, d, hd, rfl⟩ := hKl g hg
    have hdy : d * y = y * d := (hDM y (hL₀M hy) d hd).symm
    have : l * d * y * (l * d)⁻¹ = l * y * l⁻¹ := by
      calc l * d * y * (l * d)⁻¹ = l * (d * y) * d⁻¹ * l⁻¹ := by group
        _ = l * (y * d) * d⁻¹ * l⁻¹ := by rw [hdy]
        _ = l * y * l⁻¹ := by group
    rw [this]
    exact L₀.mul_mem (L₀.mul_mem hl hy) (L₀.inv_mem hl)
  have hN₁ : (L₀.subgroupOf K₁).Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
    (by simpa using hconjL g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hD2p : IsPGroup 2 ↥D := hB2.to_le inf_le_left
  have hpg : IsPGroup 2 (↥K₁ ⧸ L₀.subgroupOf K₁) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨l, hl, d, hd, hkld⟩ := hKl (k : G) k.2
      obtain ⟨m, hm⟩ := hD2p ⟨d, hd⟩
      refine ⟨m, ?_⟩
      have hdm : d ^ (2 ^ m) = 1 := congrArg Subtype.val hm
      have hc : Commute l d := hDM l (hL₀M hl) d hd
      show (((k ^ 2 ^ m : ↥K₁)) : ↥K₁ ⧸ L₀.subgroupOf K₁) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show (k : G) ^ 2 ^ m ∈ L₀
      rw [hkld, hc.mul_pow, hdm, mul_one]
      exact L₀.pow_mem hl _
  have hN₁top := hshort.1 (L₀.subgroupOf K₁) hpg
  have hKL : K₁ ≤ L₀ := fun k hk => by
    have : (⟨k, hk⟩ : ↥K₁) ∈ L₀.subgroupOf K₁ := by rw [hN₁top]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hUN : M ≤ Subgroup.normalizer (U : Set G) := by
    refine sup_le (C1.le_normalizer_blockU K₁) (fun q hq => ?_)
    have hq' : q ∈ S ⊓ Subgroup.centralizer (U : Set G) := hrk.Q_eq ▸ hq
    exact Subgroup.centralizer_le_normalizer _ hq'.2
  have hH₀U : H₀ ≤ Subgroup.normalizer (U : Set G) := hH₀M.trans hUN
  intro z hz
  have hzK : z ∈ K₁ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K₁ hz
  have hzQ : z ∈ Q := by
    have hle : pCoreOf 2 K₁ ≤ pCoreOf 2 (K₁ ⊔ baum R) := by
      refine C1.le_pCoreOf_of_normalized
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K₁).trans le_sup_left) ?_
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K₁)
      refine sup_le (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K₁)
        (fun b hb => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁
          (burnsideC5h_c54_one h116 hset K₁ hK₁mem hb))
    exact hle hz
  have hzL : z ∈ (H₀ ⊔ U : Subgroup G) := by
    rw [sup_comm]; exact hKL hzK
  have hzL' : z ∈ ((H₀ ⊔ U : Subgroup G) : Set G) := hzL
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H₀ U hH₀U] at hzL'
  obtain ⟨h, hh, u, hu, rfl⟩ := hzL'
  have hhQ : h ∈ Q := by
    have : h = (h * u) * u⁻¹ := by group
    rw [this]
    exact Q.mul_mem hzQ (Q.inv_mem (hUQ' hu))
  have : h ∈ H₀ ⊓ Q := ⟨hh, hhQ⟩
  rw [hH₀Q, Subgroup.mem_bot] at this
  rw [this]
  simpa using hu

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_s1_key (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x)
    (hfr : (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥) :
    burnsideC5x_S1Str R K₁ x ∧ pCoreOf 2 (K₁ ⊔ R) = pCoreOf 2 (K₁ ⊔ baum R) ∧
      pCoreOf 2 K₁ ≤ blockU K₁ ∧ pCoreOf 2 (K₁ ⊔ baum R) ≤ baum R := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inl hL)
    exact ⟨burnsideC5x_lin2A3_S1Str h116 hset hx (Or.inl hL) hfr,
      (burnsideC5x_lin2A3_P h116 hset hs1 hidx hx (Or.inl hL) hfr).1,
      burnsideC5x_lin2_pCore h116 hset hx hL hfr, hrk.Q_le_B⟩
  · obtain ⟨q, W, hq2, hrk, hZ, hgen⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inr h3)
    refine ⟨burnsideC5x_lin2A3_S1Str h116 hset hx (Or.inr h3) hfr,
      (burnsideC5x_lin2A3_P h116 hset hs1 hidx hx (Or.inr h3) hfr).1, ?_, hrk.Q_le_B⟩
    have := (hshort.alt3_structure h3).1
    exact this.le
  · obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset (burnsideC5x_s1_RN hset hs1) h5
    have hxR : x ∈ Subgroup.normalizer (R : Set G) := hset.hyp1.R_norm hx.1
    have hD2 : C5.ElemAb2 (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) :=
      burnsideC5x_elemAb_of_frattini ((C.R2.to_le C.hBR).to_le inf_le_left) hfr
    have m : burnsideC5x_A5Cfg.Mate C x := ⟨⟨hxR, hx.2.2⟩, hD2⟩
    exact ⟨burnsideC5x_a5_S1Str h116 hset (burnsideC5x_s1_RN hset hs1) hx h5 hfr,
      (burnsideC5x_a5_P h116 hset hs1 hidx hx h5 hfr).1, m.pCore_le_blockU, C.hQB⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
@[expose] def burnsideC5x_Concl7 {G : Type} [Group G] [Finite G]
    (H M₀ TH R K₁ : Subgroup G) (x : G) : Prop :=
  (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) = pCoreOf 2 (oTwoUpper H) ∧
  (frattini ↥(baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))).map
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)).subtype = ⊥ ∧
  (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊓
      rconj x (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) = ⊥ ∧
  baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) =
    R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ∧
  pCoreOf 2 (oTwoUpper H ⊔ R) =
    (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) ∧
  IsMaxElemAbelian R ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G)) ∧
  (baum R : Set G) =
    (((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Subgroup G) : Set G) *
      (rconj x (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) ∧
  baum R = thompsonJ R ∧
  ((((∀ t ∈ TH, conjByElt t K₁ = K₁) ∧
      ((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) ∧
      AFam R = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R))}) ∨
    ((∀ t ∈ TH, conjByElt t K₁ = K₁) ∧ IsAltType K₁ 5 ∧
      ∃ (A : Subgroup G) (r : G), r ∈ R ⊓ K₁ ∧ r ∉ baum R ∧
        (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A = 2 ∧
        AFam R = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R)), A, rconj r A})) ∨
    ((∃ t ∈ TH, conjByElt t K₁ ≠ K₁) ∧
      (baum R : Set G) =
        ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) *
          (rconj x (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) *
          ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) ∧
      {A | A ∈ AFam R ∧ TH ≤ Subgroup.normalizer (A : Set G)} =
        {(baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
            (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G),
          (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
            rconj x (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G)}))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_s1_7 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hidx : TH.relIndex M₀ = 2) (hx : GoodX H M₀ K₁ x) :
    burnsideC5x_Concl7 H M₀ TH R K₁ x := by
  obtain ⟨hTHN, hK, hHeq⟩ := burnsideC5x_s1_facts hset hs1
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hP4 := burnsideC5x_s1_P4 h116 hset hs1 hx
  have hfr := burnsideC5x_s1_frattini hset hs1 hidx hx hP4
  obtain ⟨hS, hPQ, hG1, hQB⟩ := burnsideC5x_s1_key h116 hset hs1 hidx hx hfr
  obtain ⟨⟨hP1a, hP1b⟩, ⟨hP2a, hP2b, hP2c, hP2d, hP2e⟩, hP3⟩ :=
    burnsideC5x_s1_123 h116 hset hs1 hx
  obtain ⟨hQmax, hinv, hne, hSQ, hd, he⟩ := hS
  have hiSup : (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) = blockU K₁ := by
    refine le_antisymm (iSup₂_le fun Ki hKi => ?_) (le_iSup₂ (f := fun (Ki : Subgroup G)
      (_ : Ki ∈ conjSubgroupsBy TH K₁) => blockU Ki) K₁ hK₁mem)
    obtain ⟨t, ht, rfl⟩ := hKi
    exact (congrArg blockU (hs1 t ht)).le
  have hBR : baum R ≤ R := C1GN.baum_le R
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := hset.hyp1.R_norm hx.1
  have hA : ∀ A, IsMaxElemAbelian R A → A ≤ baum R := fun A hA =>
    (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ R).trans (C5.thompsonJ_le_baum' R)
  have hCRU := burnsideC5x_s1_CRU hset hs1
  unfold burnsideC5x_Concl7
  rw [hiSup, hK]
  refine ⟨le_antisymm (C1.blockU_le_blockQ hshort) hG1, hfr,
    burnsideC5x_s1_inf_conj hset hs1 hidx hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine le_antisymm (inf_le_inf_right _ hBR) (fun c hc => ⟨?_, hc.2⟩)
    have hcU : c ∈ R ⊓ Subgroup.centralizer (blockU K₁ : Set G) :=
      ⟨hc.1, Subgroup.centralizer_le hUK hc.2⟩
    rw [hCRU, hPQ] at hcU
    exact hQB hcU
  · rw [hPQ, hP1a, sup_comm]
  · rw [sup_comm, ← hP1a]; exact hQmax
  · rw [sup_comm, ← hP1a]; exact burnsideC5x_set_swap hP2a
  · refine le_antisymm ?_ (C5.thompsonJ_le_baum' R)
    intro b hb
    have hb' : b ∈ (baum R : Set G) := hb
    rw [hSQ] at hb'
    obtain ⟨q, hq, q', hq', rfl⟩ := hb'
    have h1 : pCoreOf 2 (K₁ ⊔ baum R) ≤ thompsonJ R := le_iSup₂_of_le _ hQmax le_rfl
    have h2 : rconj x (pCoreOf 2 (K₁ ⊔ baum R)) ≤ thompsonJ R :=
      le_iSup₂_of_le _ (C56.isMaxElemAbelian_conjSubgroup hQmax hxR) le_rfl
    exact (thompsonJ R).mul_mem (h1 hq) (h2 hq')
  · left
    rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
    · left
      refine ⟨hs1, Or.inl hL, ?_⟩
      rw [← burnsideC5x_AFam_eq hBR hA]
      exact hd (Or.inl hL)
    · left
      refine ⟨hs1, Or.inr h3, ?_⟩
      rw [← burnsideC5x_AFam_eq hBR hA]
      exact hd (Or.inr h3)
    · right
      exact ⟨hs1, h5, he h5⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_1to5 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hRN : IsAltType K₁ 5 → R ≤ Subgroup.normalizer (K₁ : Set G)) :
    burnsideC5x_P1 R K₁ x ∧ burnsideC5x_P2 R K₁ x ∧ burnsideC5x_P3 R K₁ x ∧
      burnsideC5x_P4 R K₁ x ∧ Even (orderOf x) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · obtain ⟨h1, h2, h3'⟩ := burnsideC5x_lin2A3_123 h116 hset hx (Or.inl hL)
    exact ⟨h1, h2, h3', burnsideC5x_lin2A3_4 h116 hset hx (Or.inl hL),
      burnsideC5x_lin2A3_5 h116 hset hx (Or.inl hL)⟩
  · obtain ⟨h1, h2, h3'⟩ := burnsideC5x_lin2A3_123 h116 hset hx (Or.inr h3)
    exact ⟨h1, h2, h3', burnsideC5x_lin2A3_4 h116 hset hx (Or.inr h3),
      burnsideC5x_lin2A3_5 h116 hset hx (Or.inr h3)⟩
  · obtain ⟨C⟩ := burnsideC5x_a5cfg h116 hset (hRN h5) h5
    obtain ⟨h1, h2, h3'⟩ := C.part123 (hset.hyp1.R_norm hx.1) hx.2.2
    exact ⟨h1, h2, h3', C.part4 (hset.hyp1.R_norm hx.1) hx.2.2,
      burnsideC5x_a5_5 h116 hset (hRN h5) hx h5⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
@[expose] def burnsideC5x_Concl {G : Type} [Group G] [Finite G]
    (H M₀ TH R K₁ : Subgroup G) (x : G) : Prop :=
  burnsideC5x_P1 R K₁ x ∧ burnsideC5x_P2 R K₁ x ∧ burnsideC5x_P3 R K₁ x ∧
    burnsideC5x_P4 R K₁ x ∧ Even (orderOf x) ∧
    (IsSylowTwoOf TH M₀ →
      (∃ t ∈ TH, conjByElt t K₁ ≠ K₁) ∧
      ∃ x' : G, GoodX H M₀ K₁ x' ∧
        x' ∈ Subgroup.normalizer ((TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
          Set G) ∧ x' ^ 2 ∈ TH ⊓ Subgroup.normalizer (blockU K₁ : Set G)) ∧
    (TH.relIndex M₀ = 2 → burnsideC5x_Concl7 H M₀ TH R K₁ x)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped Pointwise in
theorem burnsideC5x_s1_C56 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁)
    (hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁) (hx : GoodX H M₀ K₁ x) :
    burnsideC5x_Concl H M₀ TH R K₁ x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := burnsideC5x_1to5 h116 hset hx
    (fun _ => burnsideC5x_s1_RN hset hs1)
  exact ⟨h1, h2, h3, h4, h5,
    fun hsyl => absurd hsyl (burnsideC5x_s1_not_sylow h116 hset hs1 hx),
    fun hidx => burnsideC5x_s1_7 h116 hset hs1 hidx hx⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_C56_of_concl
    (h : ∀ (G : Type) [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G) (x : G),
      SetC53 H M₀ TH R K₁ → GoodX H M₀ K₁ x → burnsideC5x_Concl H M₀ TH R K₁ x) : C_5_6 :=
  h

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC5x_C56_of_s2 (h116 : C_1_16)
    (h : ∀ (G : Type) [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G) (x : G),
      SetC53 H M₀ TH R K₁ → GoodX H M₀ K₁ x → (∃ t ∈ TH, conjByElt t K₁ ≠ K₁) →
        burnsideC5x_Concl H M₀ TH R K₁ x) : C_5_6 := by
  refine burnsideC5x_C56_of_concl fun G _ _ H M₀ TH R K₁ x hset hx => ?_
  by_cases hs1 : ∀ t ∈ TH, conjByElt t K₁ = K₁
  · exact burnsideC5x_s1_C56 h116 hset hs1 hx
  · push Not at hs1
    exact h G H M₀ TH R K₁ x hset hx hs1

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_5_7
    : C_5_7 := by
  intro G _ _ H M₀ TH R K₁ hset hs1 hmax
  have h116 : C_1_16 := as_C_1_16
  have h54 : C_5_4 := as_C_5_4
  have h55 : C_5_5 := as_C_5_5
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  have htype := (burnsideC5h_c54_isChi0Block hset hK₁mem).2
  refine burnsideC5x_c57_assembly hset hs1 hmax (burnsideC5x_s1_exists_goodX h54 h55 hset hs1)
    ?_ ?_
  · intro x hx
    rcases htype with hL | h3 | h5
    · exact burnsideC5x_lin2A3_4 h116 hset hx (Or.inl hL)
    · exact burnsideC5x_lin2A3_4 h116 hset hx (Or.inr h3)
    · exact burnsideC5x_a5_P4 h116 hset (burnsideC5x_s1_RN hset hs1) hx h5
  · intro x hx hfr
    rcases htype with hL | h3 | h5
    · exact burnsideC5x_lin2A3_S1Str h116 hset hx (Or.inl hL) hfr
    · exact burnsideC5x_lin2A3_S1Str h116 hset hx (Or.inr h3) hfr
    · exact burnsideC5x_a5_S1Str h116 hset (burnsideC5x_s1_RN hset hs1) hx h5 hfr

end

end CFSG.ASVolI
