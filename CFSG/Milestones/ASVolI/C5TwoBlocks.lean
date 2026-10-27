module

public import CFSG.Milestones.ASVolI.C5Maximal

public section

namespace CFSG.ASVolI

open CFSG.Open
section PartBurnsideC56Base

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement

theorem burnsideC56_b_mem_self {G : Type} [Group G] (TH K₁ : Subgroup G) :
    K₁ ∈ conjSubgroupsBy TH K₁ :=
  ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩

theorem burnsideC56_b_mem_conj {G : Type} [Group G] {TH K₁ : Subgroup G} {t : G} (ht : t ∈ TH) :
    conjByElt t K₁ ∈ conjSubgroupsBy TH K₁ := ⟨t, ht, rfl⟩

structure burnsideC56_Two {G : Type} [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G) (t : G) :
    Prop where
  set : SetC53 H M₀ TH R K₁
  ht : t ∈ TH
  hne : conjByElt t K₁ ≠ K₁

namespace burnsideC56_Two

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t : G}
  (h : burnsideC56_Two H M₀ TH R K₁ t)
include h

theorem conj_cases {a : G} (ha : a ∈ TH) : conjByElt a K₁ = K₁ ∨ conjByElt a K₁ = conjByElt t K₁ := by
  rcases h.set.config.card_le 1 TH.one_mem t h.ht a ha with h1 | h1 | h1
  · rw [burnsideC5h_c54_conjByElt_one] at h1
    exact absurd h1.symm h.hne
  · rw [burnsideC5h_c54_conjByElt_one] at h1
    exact Or.inl h1.symm
  · exact Or.inr h1.symm

theorem mem_cases {L : Subgroup G} (hL : L ∈ conjSubgroupsBy TH K₁) : L = K₁ ∨ L = conjByElt t K₁ := by
  obtain ⟨a, ha, rfl⟩ := hL
  exact h.conj_cases ha

theorem K₂_le_centralizer : conjByElt t K₁ ≤ Subgroup.centralizer (K₁ : Set G) := by
  have := h.set.config.commute t h.ht 1 TH.one_mem (by
    rw [burnsideC5h_c54_conjByElt_one]; exact h.hne)
  rwa [burnsideC5h_c54_conjByElt_one] at this

theorem K₁_le_centralizer : K₁ ≤ Subgroup.centralizer (conjByElt t K₁ : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (Subgroup.mem_centralizer_iff.mp (h.K₂_le_centralizer hb) a ha).symm

theorem comm {a b : G} (ha : a ∈ K₁) (hb : b ∈ conjByElt t K₁) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (h.K₂_le_centralizer hb) a ha)

theorem oTwoUpper_eq : oTwoUpper H = K₁ ⊔ conjByElt t K₁ := by
  rw [h.set.config.prod]
  refine le_antisymm (iSup₂_le fun a ha => ?_) (sup_le ?_ ?_)
  · rcases h.conj_cases ha with h1 | h1
    · rw [h1]; exact le_sup_left
    · rw [h1]; exact le_sup_right
  · have := le_iSup₂ (f := fun (a : G) (_ : a ∈ TH) => conjByElt a K₁) 1 TH.one_mem
    rwa [burnsideC5h_c54_conjByElt_one] at this
  · exact le_iSup₂ (f := fun (a : G) (_ : a ∈ TH) => conjByElt a K₁) t h.ht

theorem iSup_eq : (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) =
    blockU K₁ ⊔ blockU (conjByElt t K₁) := by
  refine le_antisymm (iSup₂_le fun L hL => ?_) (sup_le ?_ ?_)
  · rcases h.mem_cases hL with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ conjSubgroupsBy TH K₁) => blockU L) K₁
      (burnsideC56_b_mem_self TH K₁)
  · exact le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ conjSubgroupsBy TH K₁) => blockU L) _
      (burnsideC56_b_mem_conj h.ht)

theorem mem_normalizer₂ {a : G} (ha : a ∈ TH) (haN : a ∈ Subgroup.normalizer (K₁ : Set G)) :
    a ∈ Subgroup.normalizer (conjByElt t K₁ : Set G) := by
  rw [C2Eleven.mem_normalizer_iff_conjByElt]
  have hat : a * t ∈ TH := mul_mem ha h.ht
  rw [C116Two.conjByElt_mul]
  rcases h.conj_cases hat with h1 | h1
  · exfalso
    apply h.hne
    have h2 : conjByElt a K₁ = K₁ := C2Eleven.mem_normalizer_iff_conjByElt.mp haN
    have h3 : conjByElt a⁻¹ (conjByElt (a * t) K₁) = conjByElt a⁻¹ K₁ := by rw [h1]
    rw [C116Two.conjByElt_mul, ← mul_assoc, inv_mul_cancel, one_mul] at h3
    rw [h3]
    have h4 : conjByElt a⁻¹ (conjByElt a K₁) = conjByElt a⁻¹ K₁ := by rw [h2]
    rw [C116Two.conjByElt_inv_conjByElt] at h4
    exact h4.symm
  · exact h1

theorem conj_eq_of_not_mem {a : G} (ha : a ∈ TH) (haN : a ∉ Subgroup.normalizer (K₁ : Set G)) :
    conjByElt a K₁ = conjByElt t K₁ := by
  rcases h.conj_cases ha with h1 | h1
  · exact absurd (C2Eleven.mem_normalizer_iff_conjByElt.mpr h1) haN
  · exact h1

theorem conj₂_eq_of_not_mem {a : G} (ha : a ∈ TH) (haN : a ∉ Subgroup.normalizer (K₁ : Set G)) :
    conjByElt a (conjByElt t K₁) = K₁ := by
  rw [C116Two.conjByElt_mul]
  rcases h.conj_cases (mul_mem ha h.ht) with h1 | h1
  · exact h1
  · exfalso
    have h2 := h.conj_eq_of_not_mem ha haN
    have h3 : conjByElt a (conjByElt t K₁) = conjByElt t K₁ := by
      rw [C116Two.conjByElt_mul]; exact h1
    apply haN
    rw [C2Eleven.mem_normalizer_iff_conjByElt]
    rw [← h2] at h3
    have h4 : conjByElt a⁻¹ (conjByElt a (conjByElt a K₁)) = conjByElt a⁻¹ (conjByElt a K₁) := by
      rw [h3]
    rw [C116Two.conjByElt_inv_conjByElt, C116Two.conjByElt_inv_conjByElt] at h4
    exact h4

theorem config₂ : BlockConfig H TH R (conjByElt t K₁) := by
  have cfg := h.set.config
  refine ⟨burnsideC5h_c54_isChi0Block h.set (burnsideC56_b_mem_conj h.ht),
    burnsideC5h_p1_comm_J h.set h.ht, ?_, ?_, ?_⟩
  · rw [cfg.prod]
    refine le_antisymm (iSup₂_le fun a ha => ?_) (iSup₂_le fun a ha => ?_)
    · have e : conjByElt a K₁ = conjByElt (a * t⁻¹) (conjByElt t K₁) := by
        rw [C116Two.conjByElt_mul, mul_assoc, inv_mul_cancel, mul_one]
      rw [e]
      exact le_iSup₂ (f := fun (b : G) (_ : b ∈ TH) => conjByElt b (conjByElt t K₁)) (a * t⁻¹)
        (mul_mem ha (inv_mem h.ht))
    · rw [C116Two.conjByElt_mul]
      exact le_iSup₂ (f := fun (b : G) (_ : b ∈ TH) => conjByElt b K₁) (a * t) (mul_mem ha h.ht)
  · intro a ha b hb c hc
    simp only [C116Two.conjByElt_mul]
    exact cfg.card_le _ (mul_mem ha h.ht) _ (mul_mem hb h.ht) _ (mul_mem hc h.ht)
  · intro a ha b hb hab
    simp only [C116Two.conjByElt_mul] at hab ⊢
    exact cfg.commute _ (mul_mem ha h.ht) _ (mul_mem hb h.ht) hab

theorem set₂ : SetC53 H M₀ TH R (conjByElt t K₁) := ⟨h.set.hyp1, h.set.hyp2, h.config₂⟩

end burnsideC56_Two

theorem burnsideC56_b_conjByElt_commutator {G : Type} [Group G] (g : G) (A B : Subgroup G) :
    conjByElt g ⁅A, B⁆ = ⁅conjByElt g A, conjByElt g B⁆ :=
  Subgroup.map_commutator _ _ _

theorem burnsideC56_b_conjByElt_eq_bot {G : Type} [Group G] (g : G) {A : Subgroup G} :
    conjByElt g A = ⊥ ↔ A = ⊥ := by
  constructor
  · intro hA
    have := congrArg (conjByElt g⁻¹) hA
    rw [C116Two.conjByElt_inv_conjByElt] at this
    rw [this]
    exact Subgroup.map_bot _
  · rintro rfl
    exact Subgroup.map_bot _

theorem burnsideC56_b_centralizer_sup {G : Type} [Group G] (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  refine le_antisymm (le_inf (Subgroup.centralizer_le (SetLike.coe_mono le_sup_left))
    (Subgroup.centralizer_le (SetLike.coe_mono le_sup_right))) ?_
  rintro c ⟨hA, hB⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hle : A ⊔ B ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hA a ha)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hB b hb)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

theorem burnsideC56_b_c54 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G}
    (hKi : Ki ∈ conjSubgroupsBy TH K₁) :
    baum R ≤ Subgroup.normalizer (Ki : Set G) ∧ blockU Ki ≤ pCoreOf 2 (Ki ⊔ baum R) ∧
      pCoreOf 2 (Ki ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU Ki : Set G) := by
  have hS1 := burnsideC5h_c54_one h116 hset
  refine ⟨hS1 Ki hKi, ?_⟩
  rcases (burnsideC5h_c54_isChi0Block hset hKi).2 with hL | h3 | h5
  · obtain ⟨-, -, -, hUQ, hQ⟩ := burnsideC5h_p2_lin2A3 h116 hset
      (burnsideC5h_p1_minParabolic hset hS1) Ki hKi (Or.inl hL)
    exact ⟨hUQ, hQ⟩
  · obtain ⟨-, -, -, hUQ, hQ⟩ := burnsideC5h_p2_lin2A3 h116 hset
      (burnsideC5h_p1_minParabolic hset hS1) Ki hKi (Or.inr h3)
    exact ⟨hUQ, hQ⟩
  · obtain ⟨-, hUQ, hQ⟩ := burnsideC5h_p3_a5_unconditional h116 hset Ki hKi h5
    exact ⟨hUQ, hQ⟩

theorem burnsideC56_b_U_le_S (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G}
    (hKi : Ki ∈ conjSubgroupsBy TH K₁) : blockU Ki ≤ baum R := by
  obtain ⟨-, hUQ, hQ⟩ := burnsideC56_b_c54 h116 hset hKi
  exact hUQ.trans (hQ ▸ inf_le_left)

theorem burnsideC56_b_U_le_K {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G} (hKi : Ki ∈ conjSubgroupsBy TH K₁) :
    blockU Ki ≤ Ki :=
  Setup.Campbell.blockU_le_self_of_isShort2 (burnsideC5h_c54_isBlock2 hset hKi).1

theorem burnsideC56_b_conj_U_le_S (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G}
    (hKi : Ki ∈ conjSubgroupsBy TH K₁) {y : G} (hy : y ∈ M₀) :
    conjSubgroup (blockU Ki) y ≤ baum R := by
  have := C5.conjSubgroup_mono (burnsideC56_b_U_le_S h116 hset hKi) y
  rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum R (hset.hyp1.R_norm hy))] at this

theorem burnsideC56_b_pCore_inf_le {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) :
    pCoreOf 2 H ⊓ (oTwoUpper H ⊔ R) ≤
      R ⊓ Subgroup.centralizer ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) := by
  rw [burnsideC5h_c54_four_second as_C_1_11 hset]
  have hKRH : oTwoUpper H ⊔ R ≤ H :=
    sup_le (oTwoUpper_le H) (hset.hyp1.R_le.trans hset.hyp1.sylow.1)
  refine C1.le_pCoreOf_of_normalized inf_le_right (fun g hg => ?_)
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le inf_le_left)
  exact C5.mem_normalizer_inf
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (hKRH hg))
    (Subgroup.le_normalizer hg)

theorem burnsideC56_b_goodX (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {Ki : Subgroup G}
    (hKi : Ki ∈ conjSubgroupsBy TH K₁) {y : G} (hy : y ∈ M₀)
    (hne : ⁅blockU Ki, rconj y (blockU Ki)⁆ ≠ ⊥) : GoodX H M₀ Ki y := by
  refine ⟨hy, fun hle => hne ?_, hne⟩
  have hUyR : rconj y (blockU Ki) ≤ R :=
    (burnsideC56_b_conj_U_le_S h116 hset hKi hy).trans (C1GN.baum_le R)
  have h1 : rconj y (blockU Ki) ≤ pCoreOf 2 H ⊓ (oTwoUpper H ⊔ R) :=
    le_inf hle (hUyR.trans le_sup_right)
  have h2 := h1.trans (burnsideC56_b_pCore_inf_le hset)
  have hUU : blockU Ki ≤ (⨆ Kj ∈ conjSubgroupsBy TH K₁, blockU Kj : Subgroup G) :=
    le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ conjSubgroupsBy TH K₁) => blockU L) Ki hKi
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp (h2 hv).2 u (hUU hu) |>.symm

theorem burnsideC56_b_goodX_inv (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {y : G} (hy : GoodX H M₀ K₁ y) :
    GoodX H M₀ K₁ y⁻¹ :=
  burnsideC56_b_goodX h116 hset (burnsideC56_b_mem_self TH K₁) (inv_mem hy.1)
    (burnsideC5x_comm_inv_ne hy.2.2)

theorem burnsideC56_b_U_le_pCoreK {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) :
    (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) ≤ pCoreOf 2 (oTwoUpper H) := by
  rw [← burnsideC5h_c54_commutator_eq hset, Subgroup.commutator_le]
  intro p hp k hk
  have hkN := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2
    (oTwoUpper H) hk
  have h1 : k * p⁻¹ * k⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
    (Subgroup.mem_normalizer_iff.mp hkN p⁻¹).mp (inv_mem hp)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
  exact mul_mem hp h1

theorem burnsideC56_b_pCoreK_le {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := by
  refine C1.le_pCoreOf_of_normalized
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (oTwoUpper_le H)) ?_
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  exact (le_normalizer_oTwoUpper H).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H))

theorem burnsideC56_b_x_not_mem_TH {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {x : G} (hx : GoodX H M₀ K₁ x) : x ∉ TH := by
  intro hxT
  have hUO : blockU K₁ ≤ pCoreOf 2 H :=
    (le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ conjSubgroupsBy TH K₁) => blockU L) K₁
      (burnsideC56_b_mem_self TH K₁)).trans
      ((burnsideC56_b_U_le_pCoreK hset).trans (burnsideC56_b_pCoreK_le H))
  have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H
      (Subgroup.le_normalizer (hset.hyp1.sylow.1 hxT))
  apply hx.2.1
  have := C5.conjSubgroup_mono hUO x
  rwa [C5.conjSubgroup_eq_self hxN] at this

theorem burnsideC56_b_H_eq {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) : TH ⊔ oTwoUpper H = H := by
  rw [← CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper]
  exact sup_twoResidual_eq hset.hyp1.sylow

theorem burnsideC56_b_sq_mem {G : Type} [Group G] {M₀ TH : Subgroup G}
    (hidx : TH.relIndex M₀ = 2) {x : G} (hx : x ∈ M₀) : x * x ∈ TH := by
  have := Subgroup.mul_self_mem_of_index_two (H := TH.subgroupOf M₀) hidx ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem burnsideC56_b_noCommon {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) (hidx : TH.relIndex M₀ = 2) {x : G} (hx : GoodX H M₀ K₁ x)
    {X : Subgroup G} (hXR : X ≤ R) (hTHX : TH ≤ Subgroup.normalizer (X : Set G))
    (hKX : oTwoUpper H ≤ Subgroup.normalizer (X : Set G))
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  have hM₀X : M₀ ≤ Subgroup.normalizer (X : Set G) :=
    burnsideC5x_le_of_relIndex_two hset.hyp1.TH_le hidx hTHX hx.1 hxX
      (burnsideC56_b_x_not_mem_TH hset hx)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [← burnsideC56_b_H_eq hset]
    exact sup_le hTHX hKX
  by_contra hne
  exact hset.hyp2 X hXR hne (sup_le hM₀X hHX)

theorem burnsideC56_b_x_norm_TH {G : Type} [Group G] {M₀ TH : Subgroup G} (hTH : TH ≤ M₀)
    (hidx : TH.relIndex M₀ = 2) {x : G} (hx : x ∈ M₀) :
    x ∈ Subgroup.normalizer (TH : Set G) :=
  burnsideC5x_TH_conj_mem hTH hidx hx

namespace burnsideC56_Two

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t : G}
  (h : burnsideC56_Two H M₀ TH R K₁ t)
include h

theorem U₂_eq : blockU (conjByElt t K₁) = conjByElt t (blockU K₁) :=
  C116Two.blockU_conjByElt t K₁

theorem U₂_le_D₁ (h116 : C_1_16) :
    blockU (conjByElt t K₁) ≤ baum R ⊓ Subgroup.centralizer (K₁ : Set G) :=
  le_inf (burnsideC56_b_U_le_S h116 h.set (burnsideC56_b_mem_conj h.ht))
    ((burnsideC56_b_U_le_K h.set (burnsideC56_b_mem_conj h.ht)).trans h.K₂_le_centralizer)

theorem U₁_le_D₂ (h116 : C_1_16) :
    blockU K₁ ≤ baum R ⊓ Subgroup.centralizer (conjByElt t K₁ : Set G) :=
  le_inf (burnsideC56_b_U_le_S h116 h.set (burnsideC56_b_mem_self TH K₁))
    ((burnsideC56_b_U_le_K h.set (burnsideC56_b_mem_self TH K₁)).trans h.K₁_le_centralizer)

theorem U_comm {a b : G} (ha : a ∈ blockU K₁) (hb : b ∈ blockU (conjByElt t K₁)) :
    a * b = b * a :=
  h.comm (burnsideC56_b_U_le_K h.set (burnsideC56_b_mem_self TH K₁) ha)
    (burnsideC56_b_U_le_K h.set (burnsideC56_b_mem_conj h.ht) hb)

theorem goodX₂ (h116 : C_1_16) (hidx : TH.relIndex M₀ = 2) {x : G} (hx : GoodX H M₀ K₁ x)
    (hD : baum R ⊓ Subgroup.centralizer (K₁ : Set G) ≤
      Subgroup.centralizer (rconj x (blockU K₁) : Set G)) :
    GoodX H M₀ (conjByElt t K₁) x := by
  set U₁ := blockU K₁ with hU₁
  have hxN : x ∈ Subgroup.normalizer (TH : Set G) :=
    burnsideC5x_TH_conj_mem h.set.hyp1.TH_le hidx hx.1
  set a : G := x * t⁻¹ * x⁻¹ with ha
  have haT : a ∈ TH := (Subgroup.mem_normalizer_iff.mp hxN t⁻¹).mp (inv_mem h.ht)
  have hc : ⁅conjByElt t U₁, conjByElt t (rconj x U₁)⁆ ≠ ⊥ := by
    intro hbot
    apply hx.2.2
    rw [← burnsideC56_b_conjByElt_commutator] at hbot
    exact (burnsideC56_b_conjByElt_eq_bot t).mp hbot
  have e1 : conjByElt t (rconj x U₁) = rconj x (conjByElt a⁻¹ U₁) := by
    ext g
    simp only [burnsideC5x_mem_rconj, mem_conjByElt, ha]
    constructor <;> intro hg <;> convert hg using 1 <;> group
  rw [← h.U₂_eq, e1, ← C116Two.blockU_conjByElt] at hc
  have haT' : a⁻¹ ∈ TH := inv_mem haT
  rcases h.conj_cases haT' with h1 | h1
  · exfalso
    rw [h1] at hc
    apply hc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (h.U₂_le_D₁ h116).trans hD
  · rw [h1] at hc
    exact burnsideC56_b_goodX h116 h.set (burnsideC56_b_mem_conj h.ht) hx.1 hc

end burnsideC56_Two

end PartBurnsideC56Base

section PartBurnsideC56Seven

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

@[expose] def burnsideC56_H14 {G : Type} [Group G] [Finite G] (H M₀ TH R : Subgroup G) : Prop :=
  ∀ (K : Subgroup G) (y : G), SetC53 H M₀ TH R K → GoodX H M₀ K y →
    burnsideC5x_P1 R K y ∧ burnsideC5x_P2 R K y ∧ burnsideC5x_P3 R K y ∧ burnsideC5x_P4 R K y

section Blk

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K : Subgroup G} {y : G}

theorem burnsideC56_s_S_norm_U (h116 : C_1_16) (hset : SetC53 H M₀ TH R K) :
    baum R ≤ Subgroup.normalizer (blockU K : Set G) := fun s hs =>
  C1.mem_normalizer_blockU ((burnsideC56_b_c54 h116 hset (burnsideC56_b_mem_self TH K)).1 hs)

theorem burnsideC56_s_S_norm_Uy (h116 : C_1_16) (hset : SetC53 H M₀ TH R K) (hy : y ∈ M₀) :
    baum R ≤ Subgroup.normalizer ((conjSubgroup (blockU K) y : Subgroup G) : Set G) :=
  C5.le_normalizer_conj (normalizer_le_normalizer_baum R (hset.hyp1.R_norm hy))
    (burnsideC56_s_S_norm_U h116 hset)

theorem burnsideC56_s_U_elem (hset : SetC53 H M₀ TH R K) : C5.ElemAb2 (blockU K) :=
  C1.elemAb2_blockU hset.config.chi0.1.1

theorem burnsideC56_s_D_comm_U (hset : SetC53 H M₀ TH R K) {u d : G} (hu : u ∈ blockU K)
    (hd : d ∈ baum R ⊓ Subgroup.centralizer (K : Set G)) : u * d = d * u :=
  Subgroup.mem_centralizer_iff.mp hd.2 u (burnsideC56_b_U_le_K hset (burnsideC56_b_mem_self TH K) hu)

theorem burnsideC56_s_D_le_C (h1 : burnsideC5x_P1 R K y) :
    baum R ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.centralizer ((conjSubgroup (blockU K) y : Subgroup G) : Set G) :=
  fun _ hd => (h1.2 hd).2

theorem burnsideC56_s_decomp (hset : SetC53 H M₀ TH R K) (h1 : burnsideC5x_P1 R K y)
    (h2 : burnsideC5x_P2 R K y) {s : G} (hs : s ∈ baum R) :
    ∃ v ∈ conjSubgroup (blockU K) y, ∃ u ∈ blockU K,
      ∃ d ∈ baum R ⊓ Subgroup.centralizer (K : Set G), s = v * u * d := by
  have hs' : s ∈ (baum R : Set G) := hs
  rw [h2.1] at hs'
  obtain ⟨v, hv, q, hq, rfl⟩ := hs'
  have hq' : q ∈ blockU K ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← h1.1]; exact hq
  obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute
    (fun u hu d hd => burnsideC56_s_D_comm_U hset hu hd) hq'
  exact ⟨v, hv, u, hu, d, hd, by group⟩

theorem burnsideC56_s_E_eq_inf (h2 : burnsideC5x_P2 R K y) :
    ⁅blockU K, baum R⁆ = blockU K ⊓ conjSubgroup (blockU K) y :=
  h2.2.2.1.trans (h2.2.2.2.1.trans h2.2.2.2.2)

theorem burnsideC56_s_E_eq_C (h2 : burnsideC5x_P2 R K y) :
    ⁅blockU K, baum R⁆ = blockU K ⊓ Subgroup.centralizer
      ((conjSubgroup (blockU K) y : Subgroup G) : Set G) :=
  h2.2.2.1.trans h2.2.2.2.1

theorem burnsideC56_s_E_eq_comm (h2 : burnsideC5x_P2 R K y) :
    ⁅blockU K, baum R⁆ = ⁅blockU K, conjSubgroup (blockU K) y⁆ :=
  h2.2.2.1

theorem burnsideC56_s_E_le_Z (hset : SetC53 H M₀ TH R K) (h1 : burnsideC5x_P1 R K y)
    (h2 : burnsideC5x_P2 R K y) :
    ⁅blockU K, baum R⁆ ≤ Subgroup.centralizer (baum R : Set G) := by
  intro e he
  have heU : e ∈ blockU K := (burnsideC56_s_E_eq_inf h2 ▸ he : e ∈ blockU K ⊓ _).1
  have heC : e ∈ Subgroup.centralizer ((conjSubgroup (blockU K) y : Subgroup G) : Set G) :=
    (burnsideC56_s_E_eq_C h2 ▸ he : e ∈ blockU K ⊓ _).2
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨v, hv, u, hu, d, hd, rfl⟩ := burnsideC56_s_decomp hset h1 h2 hs
  have c1 : Commute v e := Subgroup.mem_centralizer_iff.mp heC v hv
  have c2 : Commute u e := (burnsideC56_s_U_elem hset).1 u hu e heU
  have c3 : Commute d e := (burnsideC56_s_D_comm_U hset heU hd).symm
  exact ((c1.mul_left c2).mul_left c3).eq

theorem burnsideC56_s_D_le_C_sup (hset : SetC53 H M₀ TH R K) (h1 : burnsideC5x_P1 R K y) :
    baum R ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.centralizer ((blockU K ⊔ conjSubgroup (blockU K) y : Subgroup G) : Set G) := by
  rw [burnsideC56_b_centralizer_sup]
  refine le_inf (fun d hd => ?_) (burnsideC56_s_D_le_C h1)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact burnsideC56_s_D_comm_U hset hu hd

theorem burnsideC56_s_CS (h116 : C_1_16) (hset : SetC53 H M₀ TH R K) (h1 : burnsideC5x_P1 R K y)
    (h2 : burnsideC5x_P2 R K y) :
    baum R ⊓ Subgroup.centralizer ((blockU K ⊔ conjSubgroup (blockU K) y : Subgroup G) : Set G) =
      ⁅blockU K, baum R⁆ ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  obtain ⟨-, hUQ, hQ⟩ := burnsideC56_b_c54 h116 hset (burnsideC56_b_mem_self TH K)
  have hUS : blockU K ≤ baum R := hUQ.trans (hQ ▸ inf_le_left)
  apply le_antisymm
  · rintro c ⟨hcS, hcC⟩
    rw [burnsideC56_b_centralizer_sup] at hcC
    have hcQ : c ∈ blockU K ⊔ (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
      rw [← h1.1, hQ]; exact ⟨hcS, hcC.1⟩
    obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute
      (fun u hu d hd => burnsideC56_s_D_comm_U hset hu hd) hcQ
    have huC : u ∈ Subgroup.centralizer ((conjSubgroup (blockU K) y : Subgroup G) : Set G) := by
      have : u = (u * d) * d⁻¹ := by group
      rw [this]
      exact mul_mem hcC.2 (inv_mem (burnsideC56_s_D_le_C h1 hd))
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hd)
    rw [burnsideC56_s_E_eq_C h2]
    exact ⟨hu, huC⟩
  · refine sup_le (fun e he => ⟨?_, ?_⟩) (fun d hd => ⟨hd.1, burnsideC56_s_D_le_C_sup hset h1 hd⟩)
    · exact hUS (burnsideC56_s_E_eq_inf h2 ▸ he : e ∈ blockU K ⊓ _).1
    · have he' : e ∈ blockU K ⊓ Subgroup.centralizer
          ((conjSubgroup (blockU K) y : Subgroup G) : Set G) := burnsideC56_s_E_eq_C h2 ▸ he
      rw [burnsideC56_b_centralizer_sup]
      refine Subgroup.mem_inf.mpr ⟨?_, he'.2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (burnsideC56_s_U_elem hset).1 u hu e he'.1

end Blk

end PartBurnsideC56Seven

section PartBurnsideC56Pair

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

namespace burnsideC56_Two

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t : G}
  (h : burnsideC56_Two H M₀ TH R K₁ t)
include h

theorem D_eq : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) =
    (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) ⊓
      (baum R ⊓ Subgroup.centralizer (conjByElt t K₁ : Set G)) := by
  rw [h.oTwoUpper_eq, burnsideC56_b_centralizer_sup]
  ext g
  simp only [Subgroup.mem_inf]
  tauto

theorem mem_D {d : G} : d ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ↔
    d ∈ baum R ⊓ Subgroup.centralizer (K₁ : Set G) ∧
      d ∈ baum R ⊓ Subgroup.centralizer (conjByElt t K₁ : Set G) := by
  rw [h.D_eq]; exact Subgroup.mem_inf

theorem conjByElt_U {a : G} (ha : a ∈ TH) :
    conjByElt a (blockU K₁ ⊔ blockU (conjByElt t K₁)) = blockU K₁ ⊔ blockU (conjByElt t K₁) := by
  have hsup : conjByElt a (blockU K₁ ⊔ blockU (conjByElt t K₁)) =
      conjByElt a (blockU K₁) ⊔ conjByElt a (blockU (conjByElt t K₁)) := Subgroup.map_sup _ _ _
  rw [hsup, ← C116Two.blockU_conjByElt, ← C116Two.blockU_conjByElt]
  by_cases haN : a ∈ Subgroup.normalizer (K₁ : Set G)
  · rw [C2Eleven.mem_normalizer_iff_conjByElt.mp haN,
      C2Eleven.mem_normalizer_iff_conjByElt.mp (h.mem_normalizer₂ ha haN)]
  · rw [h.conj_eq_of_not_mem ha haN, h.conj₂_eq_of_not_mem ha haN, sup_comm]

theorem TH_norm_U : TH ≤ Subgroup.normalizer
    ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) := fun a ha =>
  C2Eleven.mem_normalizer_iff_conjByElt.mpr (h.conjByElt_U ha)

theorem TH_norm_D : TH ≤ Subgroup.normalizer
    ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) := fun a ha =>
  C5.mem_normalizer_inf
    (normalizer_le_normalizer_baum R (h.set.hyp1.R_norm (h.set.hyp1.TH_le ha)))
    (C5.mem_normalizer_centralizer (le_normalizer_oTwoUpper H (h.set.hyp1.sylow.1 ha)))

theorem D_le_CU : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤
    Subgroup.centralizer ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) := by
  intro d hd
  have hle : blockU K₁ ⊔ blockU (conjByElt t K₁) ≤ oTwoUpper H := by
    rw [h.oTwoUpper_eq]
    exact sup_le_sup (burnsideC56_b_U_le_K h.set (burnsideC56_b_mem_self TH K₁))
      (burnsideC56_b_U_le_K h.set (burnsideC56_b_mem_conj h.ht))
  exact Subgroup.centralizer_le (SetLike.coe_mono hle) hd.2

end burnsideC56_Two

section Pair

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t y : G}

structure burnsideC56_PairY (H M₀ TH R K₁ : Subgroup G) (t y : G) : Prop where
  two : burnsideC56_Two H M₀ TH R K₁ t
  h116 : C_1_16
  good₁ : GoodX H M₀ K₁ y
  good₂ : GoodX H M₀ (conjByElt t K₁) y
  p1₁ : burnsideC5x_P1 R K₁ y
  p2₁ : burnsideC5x_P2 R K₁ y
  p3₁ : burnsideC5x_P3 R K₁ y
  p1₂ : burnsideC5x_P1 R (conjByElt t K₁) y
  p2₂ : burnsideC5x_P2 R (conjByElt t K₁) y
  p3₂ : burnsideC5x_P3 R (conjByElt t K₁) y

namespace burnsideC56_PairY

variable (p : burnsideC56_PairY H M₀ TH R K₁ t y)
include p

theorem comm_V₁_U₂ {v u : G} (hv : v ∈ conjSubgroup (blockU K₁) y)
    (hu : u ∈ blockU (conjByElt t K₁)) : v * u = u * v :=
  (Subgroup.mem_centralizer_iff.mp (burnsideC56_s_D_le_C p.p1₁ (p.two.U₂_le_D₁ p.h116 hu)) v hv)

theorem comm_U₁_V₂ {u v : G} (hu : u ∈ blockU K₁)
    (hv : v ∈ conjSubgroup (blockU (conjByElt t K₁)) y) : u * v = v * u :=
  (Subgroup.mem_centralizer_iff.mp (burnsideC56_s_D_le_C p.p1₂ (p.two.U₁_le_D₂ p.h116 hu)) v hv).symm

theorem comm_V₁_V₂ {v w : G} (hv : v ∈ conjSubgroup (blockU K₁) y)
    (hw : w ∈ conjSubgroup (blockU (conjByElt t K₁)) y) : v * w = w * v := by
  rw [mem_conjSubgroup_iff] at hv hw
  have := p.two.U_comm hv hw
  have e : y * (v * w) * y⁻¹ = y * (w * v) * y⁻¹ := by
    calc y * (v * w) * y⁻¹ = (y * v * y⁻¹) * (y * w * y⁻¹) := by group
      _ = (y * w * y⁻¹) * (y * v * y⁻¹) := this
      _ = y * (w * v) * y⁻¹ := by group
  simpa using e

theorem le_C₁ : blockU (conjByElt t K₁) ⊔ conjSubgroup (blockU (conjByElt t K₁)) y ≤
    Subgroup.centralizer ((blockU K₁ ⊔ conjSubgroup (blockU K₁) y : Subgroup G) : Set G) := by
  rw [burnsideC56_b_centralizer_sup]
  refine sup_le (le_inf (fun u hu => ?_) (fun u hu => ?_)) (le_inf (fun v hv => ?_) (fun v hv => ?_))
  · rw [Subgroup.mem_centralizer_iff]; intro a ha; exact p.two.U_comm ha hu
  · rw [Subgroup.mem_centralizer_iff]; intro a ha; exact p.comm_V₁_U₂ ha hu
  · rw [Subgroup.mem_centralizer_iff]; intro a ha; exact p.comm_U₁_V₂ ha hv
  · rw [Subgroup.mem_centralizer_iff]; intro a ha; exact p.comm_V₁_V₂ ha hv

theorem le_C₂ : blockU K₁ ⊔ conjSubgroup (blockU K₁) y ≤
    Subgroup.centralizer ((blockU (conjByElt t K₁) ⊔ conjSubgroup (blockU (conjByElt t K₁)) y :
      Subgroup G) : Set G) :=
  Subgroup.le_centralizer_iff.mp p.le_C₁

theorem E₁_le_U₁ : ⁅blockU K₁, baum R⁆ ≤ blockU K₁ := fun _ he =>
  (burnsideC56_s_E_eq_inf p.p2₁ ▸ he : _ ∈ blockU K₁ ⊓ _).1

theorem E₂_le_U₂ : ⁅blockU (conjByElt t K₁), baum R⁆ ≤ blockU (conjByElt t K₁) := fun _ he =>
  (burnsideC56_s_E_eq_inf p.p2₂ ▸ he : _ ∈ blockU (conjByElt t K₁) ⊓ _).1

theorem decomp {s : G} (hs : s ∈ baum R) :
    ∃ v₁ ∈ conjSubgroup (blockU K₁) y, ∃ u₁ ∈ blockU K₁,
      ∃ v₂ ∈ conjSubgroup (blockU (conjByElt t K₁)) y, ∃ u₂ ∈ blockU (conjByElt t K₁),
        ∃ d ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G),
          s = v₁ * u₁ * (v₂ * u₂ * d) := by
  have hset₁ := p.two.set
  have hset₂ := p.two.set₂
  obtain ⟨v₁, hv₁, u₁, hu₁, d₁, hd₁, rfl⟩ := burnsideC56_s_decomp hset₁ p.p1₁ p.p2₁ hs
  obtain ⟨v₂, hv₂, u₂, hu₂, d₂, hd₂, hd₁eq⟩ := burnsideC56_s_decomp hset₂ p.p1₂ p.p2₂ hd₁.1
  have hvu : v₂ * u₂ ∈ Subgroup.centralizer
      ((blockU K₁ ⊔ conjSubgroup (blockU K₁) y : Subgroup G) : Set G) :=
    p.le_C₁ (mul_mem (Subgroup.mem_sup_right hv₂) (Subgroup.mem_sup_left hu₂))
  have hd₂C : d₂ ∈ baum R ⊓ Subgroup.centralizer
      ((blockU K₁ ⊔ conjSubgroup (blockU K₁) y : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hd₂.1, ?_⟩
    have : d₂ = (v₂ * u₂)⁻¹ * d₁ := by rw [hd₁eq]; group
    rw [this]
    exact mul_mem (inv_mem hvu) (burnsideC56_s_D_le_C_sup hset₁ p.p1₁ hd₁)
  rw [burnsideC56_s_CS p.h116 hset₁ p.p1₁ p.p2₁] at hd₂C
  obtain ⟨e₁, he₁, d, hd, hd₂eq⟩ := C5.mem_sup_of_commute
    (fun e he d hd => burnsideC56_s_D_comm_U hset₁ (p.E₁_le_U₁ he) hd) hd₂C
  have hdD : d ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
    rw [p.two.mem_D]
    refine ⟨hd, hd.1, ?_⟩
    have : d = e₁⁻¹ * d₂ := by rw [hd₂eq]; group
    rw [this]
    exact (mul_mem (inv_mem (p.two.U₁_le_D₂ p.h116 (p.E₁_le_U₁ he₁))) hd₂).2
  have hZ := burnsideC56_s_E_le_Z hset₁ p.p1₁ p.p2₁ he₁
  have hc : Commute e₁ (v₂ * u₂) :=
    (Subgroup.mem_centralizer_iff.mp hZ (v₂ * u₂) (mul_mem
      (burnsideC56_b_conj_U_le_S p.h116 hset₁ (burnsideC56_b_mem_conj p.two.ht) p.good₂.1 hv₂)
      (burnsideC56_b_U_le_S p.h116 hset₁ (burnsideC56_b_mem_conj p.two.ht) hu₂))).symm
  refine ⟨v₁, hv₁, u₁ * e₁, mul_mem hu₁ (p.E₁_le_U₁ he₁), v₂, hv₂, u₂, hu₂, d, hdD, ?_⟩
  rw [hd₁eq, hd₂eq]
  calc v₁ * u₁ * (v₂ * u₂ * (e₁ * d)) = v₁ * u₁ * ((v₂ * u₂) * e₁ * d) := by group
    _ = v₁ * u₁ * (e₁ * (v₂ * u₂) * d) := by rw [hc.eq]
    _ = v₁ * (u₁ * e₁) * (v₂ * u₂ * d) := by group

theorem decomp' {s : G} (hs : s ∈ baum R) :
    ∃ v ∈ conjSubgroup (blockU K₁) y ⊔ conjSubgroup (blockU (conjByElt t K₁)) y,
      ∃ u ∈ blockU K₁ ⊔ blockU (conjByElt t K₁),
        ∃ d ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G), s = v * u * d := by
  obtain ⟨v₁, hv₁, u₁, hu₁, v₂, hv₂, u₂, hu₂, d, hd, rfl⟩ := p.decomp hs
  refine ⟨v₁ * v₂, mul_mem (Subgroup.mem_sup_left hv₁) (Subgroup.mem_sup_right hv₂),
    u₁ * u₂, mul_mem (Subgroup.mem_sup_left hu₁) (Subgroup.mem_sup_right hu₂), d, hd, ?_⟩
  have hc : u₁ * v₂ = v₂ * u₁ := p.comm_U₁_V₂ hu₁ hv₂
  calc v₁ * u₁ * (v₂ * u₂ * d) = v₁ * (u₁ * v₂) * u₂ * d := by group
    _ = v₁ * (v₂ * u₁) * u₂ * d := by rw [hc]
    _ = v₁ * v₂ * (u₁ * u₂) * d := by group

theorem D_le_CV : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤
    Subgroup.centralizer ((conjSubgroup (blockU K₁) y ⊔
      conjSubgroup (blockU (conjByElt t K₁)) y : Subgroup G) : Set G) := by
  intro d hd
  rw [p.two.mem_D] at hd
  rw [burnsideC56_b_centralizer_sup]
  exact ⟨burnsideC56_s_D_le_C p.p1₁ hd.1, burnsideC56_s_D_le_C p.p1₂ hd.2⟩

theorem CSU : baum R ⊓ Subgroup.centralizer
    ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) =
      (blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) := by
  have hset₁ := p.two.set
  have hset₂ := p.two.set₂
  obtain ⟨-, hUQ₁, hQ₁⟩ := burnsideC56_b_c54 p.h116 hset₁ (burnsideC56_b_mem_self TH K₁)
  obtain ⟨-, hUQ₂, hQ₂⟩ := burnsideC56_b_c54 p.h116 hset₂
    (burnsideC56_b_mem_self TH (conjByElt t K₁))
  apply le_antisymm
  · intro c hc
    obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.mp hc
    rw [burnsideC56_b_centralizer_sup] at hcC
    have hc1 : c ∈ blockU K₁ ⊔ (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) := by
      rw [← p.p1₁.1, hQ₁]; exact ⟨hcS, hcC.1⟩
    obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ := C5.mem_sup_of_commute
      (fun u hu d hd => burnsideC56_s_D_comm_U hset₁ hu hd) hc1
    have hd₁C : d₁ ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) := by
      have : d₁ = u₁⁻¹ * (u₁ * d₁) := by group
      rw [this]
      refine mul_mem (inv_mem ?_) hcC.2
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (p.two.U_comm hu₁ ha).symm
    have hc2 : d₁ ∈ blockU (conjByElt t K₁) ⊔
        (baum R ⊓ Subgroup.centralizer (conjByElt t K₁ : Set G)) := by
      rw [← p.p1₂.1, hQ₂]; exact ⟨hd₁.1, hd₁C⟩
    obtain ⟨u₂, hu₂, d₂, hd₂, rfl⟩ := C5.mem_sup_of_commute
      (fun u hu d hd => burnsideC56_s_D_comm_U hset₂ hu hd) hc2
    have hdD : d₂ ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
      rw [p.two.mem_D]
      refine ⟨Subgroup.mem_inf.mpr ⟨hd₂.1, ?_⟩, hd₂⟩
      have : d₂ = u₂⁻¹ * (u₂ * d₂) := by group
      rw [this]
      exact (mul_mem (inv_mem (p.two.U₂_le_D₁ p.h116 hu₂)) hd₁).2
    rw [← mul_assoc]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (Subgroup.mem_sup_left hu₁)
      (Subgroup.mem_sup_right hu₂))) (Subgroup.mem_sup_right hdD)
  · refine sup_le (fun u hu => Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      (fun d hd => Subgroup.mem_inf.mpr ⟨hd.1, p.two.D_le_CU hd⟩)
    · exact sup_le (burnsideC56_b_U_le_S p.h116 hset₁ (burnsideC56_b_mem_self TH K₁))
        (burnsideC56_b_U_le_S p.h116 hset₁ (burnsideC56_b_mem_conj p.two.ht)) hu
    ·
      have hab : ∀ a ∈ blockU K₁ ⊔ blockU (conjByElt t K₁),
          ∀ b ∈ blockU K₁ ⊔ blockU (conjByElt t K₁), a * b = b * a := by
        have := C5.ElemAb2.sup (burnsideC56_s_U_elem hset₁) (burnsideC56_s_U_elem hset₂)
          (fun a ha b hb => p.two.U_comm ha hb)
        exact this.1
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hab a ha u hu

theorem CS : baum R ⊓ Subgroup.centralizer (((blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
      (conjSubgroup (blockU K₁) y ⊔ conjSubgroup (blockU (conjByElt t K₁)) y) : Subgroup G) :
        Set G) =
      (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) := by
  have hset₁ := p.two.set
  have hset₂ := p.two.set₂
  have hsplit : ∀ c, c ∈ Subgroup.centralizer (((blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
      (conjSubgroup (blockU K₁) y ⊔ conjSubgroup (blockU (conjByElt t K₁)) y) : Subgroup G) :
        Set G) ↔
      c ∈ Subgroup.centralizer ((blockU K₁ ⊔ conjSubgroup (blockU K₁) y : Subgroup G) : Set G) ∧
      c ∈ Subgroup.centralizer ((blockU (conjByElt t K₁) ⊔
        conjSubgroup (blockU (conjByElt t K₁)) y : Subgroup G) : Set G) := by
    intro c
    simp only [burnsideC56_b_centralizer_sup, Subgroup.mem_inf]
    tauto
  apply le_antisymm
  · intro c hc
    obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.mp hc
    rw [hsplit] at hcC
    have hc1 : c ∈ baum R ⊓ Subgroup.centralizer
        ((blockU K₁ ⊔ conjSubgroup (blockU K₁) y : Subgroup G) : Set G) := ⟨hcS, hcC.1⟩
    rw [burnsideC56_s_CS p.h116 hset₁ p.p1₁ p.p2₁] at hc1
    obtain ⟨e₁, he₁, d₁, hd₁, rfl⟩ := C5.mem_sup_of_commute
      (fun e he d hd => burnsideC56_s_D_comm_U hset₁ (p.E₁_le_U₁ he) hd) hc1
    have hd₁C : d₁ ∈ baum R ⊓ Subgroup.centralizer ((blockU (conjByElt t K₁) ⊔
        conjSubgroup (blockU (conjByElt t K₁)) y : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hd₁.1, ?_⟩
      have : d₁ = e₁⁻¹ * (e₁ * d₁) := by group
      rw [this]
      exact mul_mem (inv_mem (p.le_C₂ (Subgroup.mem_sup_left (p.E₁_le_U₁ he₁)))) hcC.2
    rw [burnsideC56_s_CS p.h116 hset₂ p.p1₂ p.p2₂] at hd₁C
    obtain ⟨e₂, he₂, d₂, hd₂, rfl⟩ := C5.mem_sup_of_commute
      (fun e he d hd => burnsideC56_s_D_comm_U hset₂ (p.E₂_le_U₂ he) hd) hd₁C
    have hdD : d₂ ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
      rw [p.two.mem_D]
      refine ⟨Subgroup.mem_inf.mpr ⟨hd₂.1, ?_⟩, hd₂⟩
      have : d₂ = e₂⁻¹ * (e₂ * d₂) := by group
      rw [this]
      exact (mul_mem (inv_mem (p.two.U₂_le_D₁ p.h116 (p.E₂_le_U₂ he₂))) hd₁).2
    rw [← mul_assoc]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (Subgroup.mem_sup_left he₁)
      (Subgroup.mem_sup_right he₂))) (Subgroup.mem_sup_right hdD)
  · have hSall : (blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
        (conjSubgroup (blockU K₁) y ⊔ conjSubgroup (blockU (conjByElt t K₁)) y) ≤ baum R :=
      sup_le (sup_le (burnsideC56_b_U_le_S p.h116 hset₁ (burnsideC56_b_mem_self TH K₁))
        (burnsideC56_b_U_le_S p.h116 hset₁ (burnsideC56_b_mem_conj p.two.ht)))
        (sup_le (burnsideC56_b_conj_U_le_S p.h116 hset₁ (burnsideC56_b_mem_self TH K₁) p.good₁.1)
          (burnsideC56_b_conj_U_le_S p.h116 hset₁ (burnsideC56_b_mem_conj p.two.ht) p.good₂.1))
    refine sup_le (sup_le (fun e he => Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      (fun e he => Subgroup.mem_inf.mpr ⟨?_, ?_⟩)) (fun d hd => Subgroup.mem_inf.mpr ⟨hd.1, ?_⟩)
    · exact burnsideC56_b_U_le_S p.h116 hset₁ (burnsideC56_b_mem_self TH K₁) (p.E₁_le_U₁ he)
    · exact Subgroup.centralizer_le (SetLike.coe_mono hSall)
        (burnsideC56_s_E_le_Z hset₁ p.p1₁ p.p2₁ he)
    · exact burnsideC56_b_U_le_S p.h116 hset₁ (burnsideC56_b_mem_conj p.two.ht) (p.E₂_le_U₂ he)
    · exact Subgroup.centralizer_le (SetLike.coe_mono hSall)
        (burnsideC56_s_E_le_Z hset₂ p.p1₂ p.p2₂ he)
    · rw [burnsideC56_b_centralizer_sup]
      exact ⟨p.two.D_le_CU hd, p.D_le_CV hd⟩

end burnsideC56_PairY

end Pair

end PartBurnsideC56Pair

section PartBurnsideC56S7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

structure burnsideC56_S7 {G : Type} [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G) (t x : G) :
    Prop where
  two : burnsideC56_Two H M₀ TH R K₁ t
  h116 : C_1_16
  h14 : burnsideC56_H14 H M₀ TH R
  hx : GoodX H M₀ K₁ x
  hidx : TH.relIndex M₀ = 2

namespace burnsideC56_S7

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
  (h : burnsideC56_S7 H M₀ TH R K₁ t x)
include h

theorem good₂ : GoodX H M₀ (conjByElt t K₁) x :=
  h.two.goodX₂ h.h116 h.hidx h.hx (burnsideC56_s_D_le_C (h.h14 K₁ x h.two.set h.hx).1)

theorem good₁' : GoodX H M₀ K₁ x⁻¹ := burnsideC56_b_goodX_inv h.h116 h.two.set h.hx

theorem good₂' : GoodX H M₀ (conjByElt t K₁) x⁻¹ :=
  burnsideC56_b_goodX_inv h.h116 h.two.set₂ h.good₂

theorem pairX : burnsideC56_PairY H M₀ TH R K₁ t x := by
  obtain ⟨a1, a2, a3, -⟩ := h.h14 K₁ x h.two.set h.hx
  obtain ⟨b1, b2, b3, -⟩ := h.h14 _ x h.two.set₂ h.good₂
  exact ⟨h.two, h.h116, h.hx, h.good₂, a1, a2, a3, b1, b2, b3⟩

theorem pairX' : burnsideC56_PairY H M₀ TH R K₁ t x⁻¹ := by
  obtain ⟨a1, a2, a3, -⟩ := h.h14 K₁ x⁻¹ h.two.set h.good₁'
  obtain ⟨b1, b2, b3, -⟩ := h.h14 _ x⁻¹ h.two.set₂ h.good₂'
  exact ⟨h.two, h.h116, h.good₁', h.good₂', a1, a2, a3, b1, b2, b3⟩

theorem sq_mem : x * x ∈ TH := burnsideC56_b_sq_mem h.hidx h.hx.1

theorem x_norm_TH : x ∈ Subgroup.normalizer (TH : Set G) :=
  burnsideC56_b_x_norm_TH h.two.set.hyp1.TH_le h.hidx h.hx.1

theorem conj_conj_U :
    conjSubgroup (conjSubgroup (blockU K₁ ⊔ blockU (conjByElt t K₁)) x) x =
      blockU K₁ ⊔ blockU (conjByElt t K₁) := by
  rw [conjSubgroup_conjSubgroup]
  exact C5.conjSubgroup_eq_self (h.two.TH_norm_U h.sq_mem)

theorem conj_E : conjSubgroup (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) x =
    ⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆ := by
  rw [C5.conjSubgroup_sup]
  have e1 : conjSubgroup ⁅blockU K₁, baum R⁆ x = ⁅blockU K₁, baum R⁆ := h.pairX.p3₁
  have e2 : conjSubgroup ⁅blockU (conjByElt t K₁), baum R⁆ x = ⁅blockU (conjByElt t K₁), baum R⁆ :=
    h.pairX.p3₂
  rw [e1, e2]

theorem conj_U : conjSubgroup (blockU K₁ ⊔ blockU (conjByElt t K₁)) x =
    conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x :=
  C5.conjSubgroup_sup _ _ _

theorem conj_CS :
    conjSubgroup (baum R ⊓ Subgroup.centralizer (((blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
      (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x) : Subgroup G) :
        Set G)) x =
      baum R ⊓ Subgroup.centralizer (((blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
        (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x) : Subgroup G) :
          Set G) := by
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self
    (normalizer_le_normalizer_baum R (h.two.set.hyp1.R_norm h.hx.1)), C5.conjSubgroup_centralizer,
    C5.conjSubgroup_sup, ← h.conj_U, h.conj_conj_U, sup_comm]

theorem ED_conj :
    (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
        conjSubgroup (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) x =
      (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) := by
  have hCS := h.pairX.CS
  have := h.conj_CS
  rw [hCS, C5.conjSubgroup_sup, h.conj_E] at this
  exact this

theorem E_elem : C5.ElemAb2 (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) := by
  have hU := C5.ElemAb2.sup (burnsideC56_s_U_elem h.two.set) (burnsideC56_s_U_elem h.two.set₂)
    (fun a ha b hb => h.two.U_comm ha hb)
  have hle : ⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆ ≤
      blockU K₁ ⊔ blockU (conjByElt t K₁) := sup_le_sup h.pairX.E₁_le_U₁ h.pairX.E₂_le_U₂
  exact ⟨fun a ha b hb => hU.1 a (hle ha) b (hle hb), fun a ha => hU.2 a (hle ha)⟩

theorem E_le_Z : ⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆ ≤
    Subgroup.centralizer (baum R : Set G) :=
  sup_le (burnsideC56_s_E_le_Z h.two.set h.pairX.p1₁ h.pairX.p2₁)
    (burnsideC56_s_E_le_Z h.two.set₂ h.pairX.p1₂ h.pairX.p2₂)

theorem S_two : IsPGroup 2 (baum R) :=
  (h.two.set.hyp1.sylow.2.1.to_le h.two.set.hyp1.R_le).to_le (C1GN.baum_le R)

theorem frattini_ED {D' : Subgroup G} (hD'S : D' ≤ baum R) :
    CFSG.QuasithinUnique.DoubleA3.frattiniOf
        ((⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔ D') =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf D' := by
  have hES : ⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆ ≤ baum R :=
    sup_le (h.pairX.E₁_le_U₁.trans (burnsideC56_b_U_le_S h.h116 h.two.set
      (burnsideC56_b_mem_self TH K₁)))
      (h.pairX.E₂_le_U₂.trans (burnsideC56_b_U_le_S h.h116 h.two.set
        (burnsideC56_b_mem_conj h.two.ht)))
  have hWD : ∀ w ∈ ⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆, ∀ d ∈ D',
      w * d = d * w := fun w hw d hd =>
    (Subgroup.mem_centralizer_iff.mp (h.E_le_Z hw) d (hD'S hd)).symm
  refine AppCS2.frattiniOf_eq_of_mul (h.S_two.to_le (sup_le hES hD'S)) le_sup_right
    h.E_elem.1 h.E_elem.2 hWD fun e he => ?_
  obtain ⟨w, hw, d, hd, rfl⟩ := C5.mem_sup_of_commute hWD he
  exact ⟨w, hw, d, hd, rfl⟩

theorem frattini_conj :
    conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))) x =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) := by
  have hDxS : conjSubgroup (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) x ≤ baum R := by
    have := C5.conjSubgroup_mono (inf_le_left : baum R ⊓ Subgroup.centralizer
      (oTwoUpper H : Set G) ≤ baum R) x
    rwa [C5.conjSubgroup_eq_self
      (normalizer_le_normalizer_baum R (h.two.set.hyp1.R_norm h.hx.1))] at this
  rw [AppCS2.conjSubgroup_frattiniOf, ← h.frattini_ED hDxS, h.ED_conj, h.frattini_ED inf_le_left]

theorem noCommon {X : Subgroup G} (hXR : X ≤ R) (hTHX : TH ≤ Subgroup.normalizer (X : Set G))
    (hKX : oTwoUpper H ≤ Subgroup.normalizer (X : Set G))
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) : X = ⊥ :=
  burnsideC56_b_noCommon h.two.set h.hidx h.hx hXR hTHX hKX hxX

theorem K_norm_of_le_D {X : Subgroup G}
    (hXD : X ≤ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) :
    oTwoUpper H ≤ Subgroup.normalizer (X : Set G) := by
  intro k hk
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact (Subgroup.mem_centralizer_iff.mp (hXD hd).2 k hk).symm

theorem frattini_eq_bot : CFSG.QuasithinUnique.DoubleA3.frattiniOf
    (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) = ⊥ := by
  have hYD : CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ≤
      baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := Subgroup.map_subtype_le _
  refine h.noCommon (hYD.trans (inf_le_left.trans (C1GN.baum_le R))) (fun a ha => ?_)
    (h.K_norm_of_le_D hYD) (conjSubgroup_eq_iff_mem_normalizer.mp h.frattini_conj)
  exact CFSG.QuasithinUnique.DoubleA3.mem_normalizer_frattiniOf (h.two.TH_norm_D ha)

theorem D_elem : C5.ElemAb2 (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) :=
  burnsideC5x_elemAb_of_frattini (h.S_two.to_le inf_le_left) h.frattini_eq_bot

theorem D_inf_conj : (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊓
    rconj x (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) = ⊥ := by
  set D := baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) with hD
  have hTHD := h.two.TH_norm_D
  have hTHDx : TH ≤ Subgroup.normalizer ((conjSubgroup D x : Subgroup G) : Set G) :=
    C5.le_normalizer_conj h.x_norm_TH hTHD
  refine h.noCommon (inf_le_left.trans (inf_le_left.trans (C1GN.baum_le R)))
    (fun a ha => C5.mem_normalizer_inf (hTHD ha) (hTHDx ha)) (h.K_norm_of_le_D inf_le_left) ?_
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  show conjSubgroup (D ⊓ conjSubgroup D x) x = D ⊓ conjSubgroup D x
  rw [C5.conjSubgroup_inf, conjSubgroup_conjSubgroup, C5.conjSubgroup_eq_self (hTHD h.sq_mem),
    inf_comm]

theorem V₁_inf_C : conjSubgroup (blockU K₁) x ⊓ Subgroup.centralizer (blockU K₁ : Set G) =
    ⁅blockU K₁, baum R⁆ := by
  have e1 := burnsideC56_s_E_eq_C h.pairX'.p2₁
  have e2 : conjSubgroup ⁅blockU K₁, baum R⁆ x = ⁅blockU K₁, baum R⁆ := h.pairX.p3₁
  rw [← e2]
  conv_rhs => rw [e1]
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_inv_conjSubgroup]

theorem V₂_inf_C : conjSubgroup (blockU (conjByElt t K₁)) x ⊓
    Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) = ⁅blockU (conjByElt t K₁), baum R⁆ := by
  have e1 := burnsideC56_s_E_eq_C h.pairX'.p2₂
  have e2 : conjSubgroup ⁅blockU (conjByElt t K₁), baum R⁆ x =
      ⁅blockU (conjByElt t K₁), baum R⁆ := h.pairX.p3₂
  rw [← e2]
  conv_rhs => rw [e1]
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_inv_conjSubgroup]

theorem U_inf : blockU K₁ ⊓ blockU (conjByElt t K₁) = ⊥ := by
  set U₁ := blockU K₁ with hU₁
  set U₂ := blockU (conjByElt t K₁) with hU₂
  have hU₁K := burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_self TH K₁)
  have hU₂K := burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_conj h.two.ht)
  have hU₁S := burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_self TH K₁)
  refine h.noCommon (inf_le_left.trans (hU₁S.trans (C1GN.baum_le R))) (fun a ha => ?_) ?_ ?_
  ·
    rw [C2Eleven.mem_normalizer_iff_conjByElt]
    have hinf : conjByElt a (U₁ ⊓ U₂) = conjByElt a U₁ ⊓ conjByElt a U₂ :=
      Subgroup.map_inf _ _ _ (MulAut.conj a).injective
    rw [hinf, hU₁, hU₂, ← C116Two.blockU_conjByElt, ← C116Two.blockU_conjByElt]
    by_cases haN : a ∈ Subgroup.normalizer (K₁ : Set G)
    · rw [C2Eleven.mem_normalizer_iff_conjByElt.mp haN,
        C2Eleven.mem_normalizer_iff_conjByElt.mp (h.two.mem_normalizer₂ ha haN)]
    · rw [h.two.conj_eq_of_not_mem ha haN, h.two.conj₂_eq_of_not_mem ha haN, inf_comm]
  · rw [h.two.oTwoUpper_eq]
    refine sup_le (fun k hk => C5.mem_normalizer_inf
      (C1.mem_normalizer_blockU (Subgroup.le_normalizer hk)) ?_) (fun k hk => C5.mem_normalizer_inf
      ?_ (C1.mem_normalizer_blockU (Subgroup.le_normalizer hk)))
    · exact Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (SetLike.coe_mono hU₂K) (h.two.K₁_le_centralizer hk))
    · exact Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (SetLike.coe_mono hU₁K) (h.two.K₂_le_centralizer hk))
  · rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hle : conjSubgroup (U₁ ⊓ U₂) x ≤ U₁ ⊓ U₂ := by
      rw [C5.conjSubgroup_inf]
      intro v hv
      have h1 : v ∈ conjSubgroup U₁ x ⊓ Subgroup.centralizer (U₁ : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨hv.1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact h.pairX.comm_U₁_V₂ hu hv.2
      have h2 : v ∈ conjSubgroup U₂ x ⊓ Subgroup.centralizer (U₂ : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨hv.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (h.pairX.comm_V₁_U₂ hv.1 hu).symm
      rw [h.V₁_inf_C] at h1
      rw [h.V₂_inf_C] at h2
      exact ⟨h.pairX.E₁_le_U₁ h1, h.pairX.E₂_le_U₂ h2⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [C5.card_conjSubgroup])

theorem E_inf : ⁅blockU K₁, baum R⁆ ⊓ ⁅blockU (conjByElt t K₁), baum R⁆ = ⊥ :=
  le_bot_iff.mp (h.U_inf ▸ inf_le_inf h.pairX.E₁_le_U₁ h.pairX.E₂_le_U₂)

end burnsideC56_S7

end PartBurnsideC56S7

section PartBurnsideC56AR

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

theorem burnsideC56_ar_nat {k c m M : ℕ} (hk : k ≤ c) (hm : m ≤ M)
    (hkm : k * m = c * M) (hm0 : 0 < m) (hc0 : 0 < c) : k = c ∧ m = M := by
  have h1 : c * m ≤ c * M := Nat.mul_le_mul_left c hm
  have h2 : k * m ≤ c * m := Nat.mul_le_mul_right m hk
  have h3 : c * m = c * M := le_antisymm h1 (hkm ▸ h2)
  have hmM : m = M := Nat.eq_of_mul_eq_mul_left hc0 h3
  subst hmM
  exact ⟨Nat.eq_of_mul_eq_mul_right hm0 hkm, rfl⟩

namespace burnsideC56_S7

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
  (h : burnsideC56_S7 H M₀ TH R K₁ t x)
include h

theorem U_elem : C5.ElemAb2 (blockU K₁ ⊔ blockU (conjByElt t K₁)) :=
  C5.ElemAb2.sup (burnsideC56_s_U_elem h.two.set) (burnsideC56_s_U_elem h.two.set₂)
    (fun a ha b hb => h.two.U_comm ha hb)

theorem V_elem : C5.ElemAb2 (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x) :=
  C5.ElemAb2.sup ((burnsideC56_s_U_elem h.two.set).conjSubgroup x)
    ((burnsideC56_s_U_elem h.two.set₂).conjSubgroup x)
    (fun a ha b hb => h.pairX.comm_V₁_V₂ ha hb)

theorem U_le_S : blockU K₁ ⊔ blockU (conjByElt t K₁) ≤ baum R :=
  sup_le (burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_self TH K₁))
    (burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_conj h.two.ht))

theorem V_le_S : conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x ≤ baum R :=
  sup_le (burnsideC56_b_conj_U_le_S h.h116 h.two.set (burnsideC56_b_mem_self TH K₁) h.hx.1)
    (burnsideC56_b_conj_U_le_S h.h116 h.two.set (burnsideC56_b_mem_conj h.two.ht) h.hx.1)

theorem D_comm_U {d u : G} (hd : d ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))
    (hu : u ∈ blockU K₁ ⊔ blockU (conjByElt t K₁)) : d * u = u * d :=
  (Subgroup.mem_centralizer_iff.mp (h.two.D_le_CU hd) u hu).symm

theorem A₀_elem : C5.ElemAb2 ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
    (blockU K₁ ⊔ blockU (conjByElt t K₁))) :=
  C5.ElemAb2.sup h.D_elem h.U_elem (fun d hd u hu => h.D_comm_U hd hu)

theorem D_le_Z : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤
    Subgroup.centralizer (baum R : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨v, hv, u, hu, d', hd', rfl⟩ := h.pairX.decomp' hs
  have c1 : Commute v d := (Subgroup.mem_centralizer_iff.mp (h.pairX.D_le_CV hd) v hv)
  have c2 : Commute u d := (h.D_comm_U hd hu).symm
  have c3 : Commute d' d := h.D_elem.1 d' hd' d hd
  exact ((c1.mul_left c2).mul_left c3).eq

theorem A₀_eq : (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
    (blockU K₁ ⊔ blockU (conjByElt t K₁)) =
      baum R ⊓ Subgroup.centralizer ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) := by
  rw [h.pairX.CSU, sup_comm]

theorem A₀_le_S : (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
    (blockU K₁ ⊔ blockU (conjByElt t K₁)) ≤ baum R := by
  rw [h.A₀_eq]; exact inf_le_left

theorem Z_eq : baum R ⊓ Subgroup.centralizer (baum R : Set G) =
    (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) := by
  apply le_antisymm
  · rw [← h.pairX.CS]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_mono (sup_le h.U_le_S h.V_le_S)))
  · refine sup_le (le_inf ?_ h.E_le_Z) (le_inf inf_le_left h.D_le_Z)
    exact (sup_le_sup h.pairX.E₁_le_U₁ h.pairX.E₂_le_U₂).trans h.U_le_S

theorem E_le_V : ⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆ ≤
    conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x := by
  refine sup_le_sup (fun e he => ?_) (fun e he => ?_)
  · exact ((burnsideC56_s_E_eq_inf h.pairX.p2₁) ▸ he : e ∈ blockU K₁ ⊓ _).2
  · exact ((burnsideC56_s_E_eq_inf h.pairX.p2₂) ▸ he : e ∈ blockU (conjByElt t K₁) ⊓ _).2

theorem x_norm_S : x ∈ Subgroup.normalizer (baum R : Set G) :=
  normalizer_le_normalizer_baum R (h.two.set.hyp1.R_norm h.hx.1)

theorem A₀_conj : conjSubgroup ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
    (blockU K₁ ⊔ blockU (conjByElt t K₁))) x =
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x) := by
  set D := baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) with hD
  set U := blockU K₁ ⊔ blockU (conjByElt t K₁) with hU
  set V := conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x with hV
  have hUV : conjSubgroup U x = V := C5.conjSubgroup_sup _ _ _
  have hZx : conjSubgroup (baum R ⊓ Subgroup.centralizer (baum R : Set G)) x =
      baum R ⊓ Subgroup.centralizer (baum R : Set G) := by
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, C5.conjSubgroup_eq_self h.x_norm_S]
  rw [C5.conjSubgroup_sup, hUV]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    have h1 : conjSubgroup D x ≤ conjSubgroup (baum R ⊓ Subgroup.centralizer (baum R : Set G)) x :=
      C5.conjSubgroup_mono (le_inf inf_le_left h.D_le_Z) x
    rw [hZx, h.Z_eq] at h1
    exact h1.trans (sup_le (h.E_le_V.trans le_sup_right) le_sup_left)
  · refine sup_le ?_ le_sup_right
    have h1 : D ≤ conjSubgroup (baum R ⊓ Subgroup.centralizer (U : Set G)) x := by
      rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self h.x_norm_S, C5.conjSubgroup_centralizer,
        hUV]
      exact le_inf inf_le_left (h.pairX.D_le_CV)
    rw [← h.A₀_eq, C5.conjSubgroup_sup, hUV] at h1
    exact h1

theorem TH_norm_A₀ : TH ≤ Subgroup.normalizer
    (((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)) : Subgroup G) : Set G) := fun a ha =>
  C1.mem_normalizer_sup (h.two.TH_norm_D ha) (h.two.TH_norm_U ha)

theorem TH_norm_B₀ : TH ≤ Subgroup.normalizer
    (((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x) : Subgroup G) :
        Set G) := by
  rw [← h.A₀_conj]
  exact C5.le_normalizer_conj h.x_norm_TH h.TH_norm_A₀

theorem Q_inf : pCoreOf 2 (K₁ ⊔ baum R) ⊓ pCoreOf 2 (conjByElt t K₁ ⊔ baum R) =
    (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)) := by
  rw [h.A₀_eq, (burnsideC56_b_c54 h.h116 h.two.set (burnsideC56_b_mem_self TH K₁)).2.2,
    (burnsideC56_b_c54 h.h116 h.two.set₂ (burnsideC56_b_mem_self TH (conjByElt t K₁))).2.2,
    burnsideC56_b_centralizer_sup]
  ext g
  simp only [Subgroup.mem_inf]
  tauto

theorem S_norm_A₀ : baum R ≤ Subgroup.normalizer
    (((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)) : Subgroup G) : Set G) := by
  rw [h.A₀_eq]
  intro s hs
  exact C5.mem_normalizer_inf (Subgroup.le_normalizer hs) (C5.mem_normalizer_centralizer
    (C1.mem_normalizer_sup (burnsideC56_s_S_norm_U h.h116 h.two.set hs)
      (burnsideC56_s_S_norm_U h.h116 h.two.set₂ hs)))

theorem U_uniq {u₁ u₁' u₂ u₂' : G} (h1 : u₁ ∈ blockU K₁) (h1' : u₁' ∈ blockU K₁)
    (h2 : u₂ ∈ blockU (conjByElt t K₁)) (h2' : u₂' ∈ blockU (conjByElt t K₁))
    (he : u₁ * u₂ = u₁' * u₂') : u₁ = u₁' ∧ u₂ = u₂' := by
  have hm : u₁'⁻¹ * u₁ = u₂' * u₂⁻¹ := by
    calc u₁'⁻¹ * u₁ = u₁'⁻¹ * (u₁ * u₂) * u₂⁻¹ := by group
      _ = u₁'⁻¹ * (u₁' * u₂') * u₂⁻¹ := by rw [he]
      _ = u₂' * u₂⁻¹ := by group
  have hx : u₁'⁻¹ * u₁ ∈ blockU K₁ ⊓ blockU (conjByElt t K₁) :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem h1') h1, by rw [hm]; exact mul_mem h2' (inv_mem h2)⟩
  rw [h.U_inf, Subgroup.mem_bot] at hx
  have e1 : u₁ = u₁' := by
    calc u₁ = u₁' * (u₁'⁻¹ * u₁) := by group
      _ = u₁' := by rw [hx, mul_one]
  subst e1
  exact ⟨rfl, mul_left_cancel he⟩

theorem CA₀ {A : Subgroup G} (hAS : A ≤ baum R) :
    ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁))) ⊓ Subgroup.centralizer (A : Set G) =
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        ((blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊓ Subgroup.centralizer (A : Set G)) := by
  have hDA : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤
      Subgroup.centralizer (A : Set G) :=
    h.D_le_Z.trans (Subgroup.centralizer_le (SetLike.coe_mono hAS))
  apply le_antisymm
  · intro c hc
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨d, hd, u, hu, rfl⟩ := C5.mem_sup_of_commute (fun d hd u hu => h.D_comm_U hd hu) hc1
    have huC : u ∈ Subgroup.centralizer (A : Set G) := by
      have : u = d⁻¹ * (d * u) := by group
      rw [this]
      exact mul_mem (inv_mem (hDA hd)) hc2
    exact mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right ⟨hu, huC⟩)
  · exact sup_le (le_inf le_sup_left hDA) (inf_le_inf_right _ le_sup_right)

theorem CU {A : Subgroup G} (hAS : A ≤ baum R) :
    (blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊓ Subgroup.centralizer (A : Set G) =
      (blockU K₁ ⊓ Subgroup.centralizer (A : Set G)) ⊔
        (blockU (conjByElt t K₁) ⊓ Subgroup.centralizer (A : Set G)) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := C5.mem_sup_of_commute
      (fun a ha b hb => h.two.U_comm ha hb) hc1
    have key : ∀ a ∈ A, a * u₁ * a⁻¹ = u₁ ∧ a * u₂ * a⁻¹ = u₂ := by
      intro a ha
      have haS := hAS ha
      have m1 : a * u₁ * a⁻¹ ∈ blockU K₁ :=
        (Subgroup.mem_normalizer_iff.mp (burnsideC56_s_S_norm_U h.h116 h.two.set haS) u₁).mp hu₁
      have m2 : a * u₂ * a⁻¹ ∈ blockU (conjByElt t K₁) :=
        (Subgroup.mem_normalizer_iff.mp (burnsideC56_s_S_norm_U h.h116 h.two.set₂ haS) u₂).mp hu₂
      have hca : a * (u₁ * u₂) * a⁻¹ = u₁ * u₂ := by
        have := Subgroup.mem_centralizer_iff.mp hc2 a ha
        rw [this]; group
      have e : (a * u₁ * a⁻¹) * (a * u₂ * a⁻¹) = u₁ * u₂ := by rw [← hca]; group
      exact h.U_uniq m1 hu₁ m2 hu₂ e
    have hc1' : u₁ ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := (key a ha).1
      calc a * u₁ = (a * u₁ * a⁻¹) * a := by group
        _ = u₁ * a := by rw [this]
    have hc2' : u₂ ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := (key a ha).2
      calc a * u₂ = (a * u₂ * a⁻¹) * a := by group
        _ = u₂ * a := by rw [this]
    exact mul_mem (Subgroup.mem_sup_left ⟨hu₁, hc1'⟩) (Subgroup.mem_sup_right ⟨hu₂, hc2'⟩)
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

theorem card_sup_of_inf {X Y : Subgroup G} (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hXY : X ⊓ Y = ⊥) : Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have := B2F.card_sup_mul_card_inf_of_commute hc
  rw [hXY, Subgroup.card_bot, mul_one] at this
  exact this

theorem card_A₀ {A : Subgroup G} (hAS : A ≤ baum R) :
    Nat.card ↥((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁))) =
      Nat.card ↥(((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        (blockU K₁ ⊔ blockU (conjByElt t K₁))) ⊓ Subgroup.centralizer (A : Set G)) *
        ((blockU K₁ ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K₁) *
          (blockU (conjByElt t K₁) ⊓ Subgroup.centralizer (A : Set G)).relIndex
            (blockU (conjByElt t K₁))) := by
  set D := baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) with hD
  set U₁ := blockU K₁ with hU₁
  set U₂ := blockU (conjByElt t K₁) with hU₂
  set C := Subgroup.centralizer (A : Set G) with hC
  have hDA : D ≤ C := h.D_le_Z.trans (Subgroup.centralizer_le (SetLike.coe_mono hAS))
  have hU : Nat.card ↥(U₁ ⊔ U₂) = Nat.card U₁ * Nat.card U₂ :=
    h.card_sup_of_inf (fun a ha b hb => h.two.U_comm ha hb) h.U_inf
  have hCU : Nat.card ↥((U₁ ⊓ C) ⊔ (U₂ ⊓ C)) = Nat.card ↥(U₁ ⊓ C) * Nat.card ↥(U₂ ⊓ C) :=
    h.card_sup_of_inf (fun a ha b hb => h.two.U_comm ha.1 hb.1)
      (le_bot_iff.mp (h.U_inf ▸ inf_le_inf inf_le_left inf_le_left))
  have h1 := B2F.card_sup_mul_card_inf_of_commute (A := D) (B := U₁ ⊔ U₂)
    (fun d hd u hu => h.D_comm_U hd hu)
  have h2 := B2F.card_sup_mul_card_inf_of_commute (A := D) (B := (U₁ ⊔ U₂) ⊓ C)
    (fun d hd u hu => h.D_comm_U hd hu.1)
  have hinf : D ⊓ ((U₁ ⊔ U₂) ⊓ C) = D ⊓ (U₁ ⊔ U₂) := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hDA))
  rw [hinf, h.CU hAS, hCU] at h2
  rw [hU] at h1
  rw [h.CA₀ hAS, h.CU hAS]
  have hr1 := C5.card_eq_card_mul_relIndex (inf_le_left : U₁ ⊓ C ≤ U₁)
  have hr2 := C5.card_eq_card_mul_relIndex (inf_le_left : U₂ ⊓ C ≤ U₂)
  have hpos : 0 < Nat.card ↥(D ⊓ (U₁ ⊔ U₂)) := Nat.card_pos
  have hpos1 : 0 < Nat.card ↥(U₁ ⊓ C) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(U₂ ⊓ C) := Nat.card_pos
  set a := Nat.card ↥(D ⊔ (U₁ ⊔ U₂))
  set b := Nat.card ↥(D ⊔ ((U₁ ⊓ C) ⊔ (U₂ ⊓ C)))
  set ι := Nat.card ↥(D ⊓ (U₁ ⊔ U₂))
  set δ := Nat.card D
  set f₁ := Nat.card ↥(U₁ ⊓ C)
  set f₂ := Nat.card ↥(U₂ ⊓ C)
  set r₁ := (U₁ ⊓ C).relIndex U₁
  set r₂ := (U₂ ⊓ C).relIndex U₂
  rw [hr1, hr2] at h1
  have e : a * ι * (f₁ * f₂) = b * (r₁ * r₂) * ι * (f₁ * f₂) := by
    calc a * ι * (f₁ * f₂) = δ * (f₁ * r₁ * (f₂ * r₂)) * (f₁ * f₂) := by rw [h1]
      _ = (δ * (f₁ * f₂)) * (r₁ * r₂) * (f₁ * f₂) := by ring
      _ = b * ι * (r₁ * r₂) * (f₁ * f₂) := by rw [← h2]
      _ = b * (r₁ * r₂) * ι * (f₁ * f₂) := by ring
  have hpos' : 0 < ι * (f₁ * f₂) := Nat.mul_pos hpos (Nat.mul_pos hpos1 hpos2)
  have e2 : a * (ι * (f₁ * f₂)) = (b * (r₁ * r₂)) * (ι * (f₁ * f₂)) := by
    rw [← mul_assoc, e]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos' e2

theorem offender {A : Subgroup G} (hAS : A ≤ baum R) (hA : C5.ElemAb2 A)
    (hpb₁ : (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A ≤
      (blockU K₁ ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K₁))
    (hpb₂ : (A ⊓ pCoreOf 2 (conjByElt t K₁ ⊔ baum R)).relIndex A ≤
      (blockU (conjByElt t K₁) ⊓ Subgroup.centralizer (A : Set G)).relIndex
        (blockU (conjByElt t K₁))) :
    Nat.card A ≤ Nat.card ↥((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁))) ∧
    (Nat.card A = Nat.card ↥((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁))) →
      A ⊓ ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        (blockU K₁ ⊔ blockU (conjByElt t K₁))) =
        ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (blockU K₁ ⊔ blockU (conjByElt t K₁))) ⊓ Subgroup.centralizer (A : Set G) ∧
      (A ⊓ ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        (blockU K₁ ⊔ blockU (conjByElt t K₁)))).relIndex A =
        (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A *
          (A ⊓ pCoreOf 2 (conjByElt t K₁ ⊔ baum R)).relIndex A ∧
      (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A =
        (blockU K₁ ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K₁) ∧
      (A ⊓ pCoreOf 2 (conjByElt t K₁ ⊔ baum R)).relIndex A =
        (blockU (conjByElt t K₁) ⊓ Subgroup.centralizer (A : Set G)).relIndex
          (blockU (conjByElt t K₁))) := by
  set A₀ := (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
    (blockU K₁ ⊔ blockU (conjByElt t K₁)) with hA₀
  set Q₁ := pCoreOf 2 (K₁ ⊔ baum R) with hQ₁
  set Q₂ := pCoreOf 2 (conjByElt t K₁ ⊔ baum R) with hQ₂
  have hkc : A ⊓ A₀ ≤ A₀ ⊓ Subgroup.centralizer (A : Set G) := by
    intro g hg
    refine ⟨hg.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact hA.1 a ha g hg.1
  have hinfQ : A ⊓ A₀ = (A ⊓ Q₁) ⊓ (A ⊓ Q₂) := by
    rw [hA₀, ← h.Q_inf]
    ext g; simp only [Subgroup.mem_inf]; tauto
  have hm : (A ⊓ A₀).relIndex A ≤ (A ⊓ Q₁).relIndex A * (A ⊓ Q₂).relIndex A := by
    rw [hinfQ]; exact Subgroup.relIndex_inf_le
  have hcard := C5.card_eq_card_mul_relIndex (inf_le_left : A ⊓ A₀ ≤ A)
  have hA₀c := h.card_A₀ hAS
  have hk := Subgroup.card_le_of_le hkc
  set k := Nat.card ↥(A ⊓ A₀)
  set c := Nat.card ↥(A₀ ⊓ Subgroup.centralizer (A : Set G))
  set m := (A ⊓ A₀).relIndex A
  set a₁ := (A ⊓ Q₁).relIndex A
  set a₂ := (A ⊓ Q₂).relIndex A
  set r₁ := (blockU K₁ ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K₁)
  set r₂ := (blockU (conjByElt t K₁) ⊓ Subgroup.centralizer (A : Set G)).relIndex
    (blockU (conjByElt t K₁))
  have hm0 : 0 < m := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
    (H := (A ⊓ A₀).subgroupOf A))
  have ha₁0 : 0 < a₁ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
    (H := (A ⊓ Q₁).subgroupOf A))
  have ha₂0 : 0 < a₂ := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
    (H := (A ⊓ Q₂).subgroupOf A))
  have hc0 : 0 < c := Nat.card_pos
  have hrr : a₁ * a₂ ≤ r₁ * r₂ := Nat.mul_le_mul hpb₁ hpb₂
  have hmr : m ≤ r₁ * r₂ := hm.trans hrr
  have hle : k * m ≤ c * (r₁ * r₂) := Nat.mul_le_mul hk hmr
  refine ⟨by rw [hcard, hA₀c]; exact hle, fun heq => ?_⟩
  rw [hcard, hA₀c] at heq
  obtain ⟨hkc', hmr'⟩ := burnsideC56_ar_nat hk hmr heq hm0 hc0
  have h12 : a₁ * a₂ = r₁ * r₂ := le_antisymm hrr (hmr' ▸ hm)
  have ha₁ : a₁ = r₁ := by
    by_contra hne
    have hlt : a₁ < r₁ := lt_of_le_of_ne hpb₁ hne
    have : a₁ * a₂ < r₁ * r₂ := Nat.mul_lt_mul_of_lt_of_le hlt hpb₂ (lt_of_lt_of_le ha₂0 hpb₂)
    omega
  have ha₂ : a₂ = r₂ := by
    rw [ha₁] at h12
    exact Nat.eq_of_mul_eq_mul_left (ha₁ ▸ ha₁0) h12
  refine ⟨Subgroup.eq_of_le_of_card_ge hkc (le_of_eq hkc'.symm), ?_, ha₁, ha₂⟩
  rw [hmr', ← ha₁, ← ha₂]

theorem Q₂_eq : pCoreOf 2 (conjByElt t K₁ ⊔ baum R) = conjByElt t (pCoreOf 2 (K₁ ⊔ baum R)) := by
  rw [(burnsideC56_b_c54 h.h116 h.two.set₂ (burnsideC56_b_mem_self TH (conjByElt t K₁))).2.2,
    (burnsideC56_b_c54 h.h116 h.two.set (burnsideC56_b_mem_self TH K₁)).2.2]
  have htS : t ∈ Subgroup.normalizer (baum R : Set G) :=
    normalizer_le_normalizer_baum R (h.two.set.hyp1.R_norm (h.two.set.hyp1.TH_le h.two.ht))
  have e1 : conjByElt t (baum R) = baum R := C2Eleven.mem_normalizer_iff_conjByElt.mp htS
  have e2 : conjByElt t (baum R ⊓ Subgroup.centralizer (blockU K₁ : Set G)) =
      conjByElt t (baum R) ⊓ conjByElt t (Subgroup.centralizer (blockU K₁ : Set G)) :=
    Subgroup.map_inf _ _ _ (MulAut.conj t).injective
  rw [e2, e1, ← C116Two.centralizer_conjByElt, ← C116Two.blockU_conjByElt]

theorem le_Q_iff {A : Subgroup G} (hTH : TH ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ pCoreOf 2 (K₁ ⊔ baum R) ↔ A ≤ pCoreOf 2 (conjByElt t K₁ ⊔ baum R) := by
  have hAt : conjByElt t A = A := C2Eleven.mem_normalizer_iff_conjByElt.mp (hTH h.two.ht)
  have hAt' : conjByElt t⁻¹ A = A :=
    C2Eleven.mem_normalizer_iff_conjByElt.mp (hTH (inv_mem h.two.ht))
  rw [h.Q₂_eq]
  constructor
  · intro hle
    rw [← hAt]
    exact Subgroup.map_mono hle
  · intro hle
    have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hle
    change conjByElt t⁻¹ A ≤ conjByElt t⁻¹ (conjByElt t (pCoreOf 2 (K₁ ⊔ baum R))) at this
    rwa [hAt', C116Two.conjByElt_inv_conjByElt] at this

theorem le_S_of_max {A : Subgroup G} (hA : IsMaxElemAbelian R A) : A ≤ baum R :=
  (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ R).trans (C5.thompsonJ_le_baum' R)

theorem A₀_max
    (hpb : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K)) :
    IsMaxElemAbelian R ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁))) := by
  refine ⟨h.A₀_le_S.trans (C1GN.baum_le R), C5.isElemAbelian_two_iff.mpr h.A₀_elem,
    fun B hBR hBe => ?_⟩
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian R
  have hAS := h.le_S_of_max hA
  have h1 : Nat.card B ≤ Nat.card A := hA.2.2 B hBR hBe
  exact h1.trans (h.offender hAS (C5.isElemAbelian_two_iff.mp hA.2.1)
    (hpb K₁ h.two.set A hAS) (hpb _ h.two.set₂ A hAS)).1

theorem B₀_max
    (hpb : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K)) :
    IsMaxElemAbelian R ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x)) := by
  rw [← h.A₀_conj]
  exact C56.isMaxElemAbelian_conjSubgroup (h.A₀_max hpb) (h.two.set.hyp1.R_norm h.hx.1)

theorem core
    (hpb : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K))
    (hpbeq : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      TH ≤ Subgroup.normalizer (A : Set G) →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A =
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) →
      A ≤ pCoreOf 2 (K ⊔ baum R) ∨ A ⊔ pCoreOf 2 (K ⊔ baum R) = baum R)
    {A : Subgroup G} (hA : IsMaxElemAbelian R A) (hTH : TH ≤ Subgroup.normalizer (A : Set G)) :
    A = (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        (blockU K₁ ⊔ blockU (conjByElt t K₁)) ∨
      (A ⊔ ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (blockU K₁ ⊔ blockU (conjByElt t K₁))) = baum R ∧
        A ⊓ ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (blockU K₁ ⊔ blockU (conjByElt t K₁))) =
          (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
            (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))) := by
  set A₀ := (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
    (blockU K₁ ⊔ blockU (conjByElt t K₁)) with hA₀
  set Q₁ := pCoreOf 2 (K₁ ⊔ baum R) with hQ₁
  set Q₂ := pCoreOf 2 (conjByElt t K₁ ⊔ baum R) with hQ₂
  have hA₀max := h.A₀_max hpb
  have hAS := h.le_S_of_max hA
  have hAe : C5.ElemAb2 A := C5.isElemAbelian_two_iff.mp hA.2.1
  have hcard : Nat.card A = Nat.card A₀ :=
    le_antisymm (hA₀max.2.2 A hA.1 hA.2.1) (hA.2.2 A₀ hA₀max.1 hA₀max.2.1)
  obtain ⟨hE1, hE2, hE3, hE4⟩ := (h.offender hAS hAe (hpb K₁ h.two.set A hAS)
    (hpb _ h.two.set₂ A hAS)).2 hcard
  have hA₀S := h.A₀_le_S
  have hQ₁S : Q₁ ≤ baum R := by
    rw [hQ₁, (burnsideC56_b_c54 h.h116 h.two.set (burnsideC56_b_mem_self TH K₁)).2.2]
    exact inf_le_left
  have hQ₂S : Q₂ ≤ baum R := by
    rw [hQ₂, (burnsideC56_b_c54 h.h116 h.two.set₂ (burnsideC56_b_mem_self TH (conjByElt t K₁))).2.2]
    exact inf_le_left
  have hA₀Q : A₀ = Q₁ ⊓ Q₂ := h.Q_inf.symm
  by_cases hq : A ≤ Q₁ ∨ A ≤ Q₂
  · left
    have hq₁ : A ≤ Q₁ := hq.elim id (h.le_Q_iff hTH).mpr
    have hq₂ : A ≤ Q₂ := (h.le_Q_iff hTH).mp hq₁
    have hle : A ≤ A₀ := hA₀Q ▸ le_inf hq₁ hq₂
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  · push Not at hq
    right
    have hs₁ : A ⊔ Q₁ = baum R :=
      (hpbeq K₁ h.two.set A hAS hTH hE3).resolve_left hq.1
    have hs₂ : A ⊔ Q₂ = baum R :=
      (hpbeq _ h.two.set₂ A hAS hTH hE4).resolve_left hq.2
    have hAN : A ≤ Subgroup.normalizer (A₀ : Set G) := hAS.trans h.S_norm_A₀
    have hAQ₁ : A ≤ Subgroup.normalizer (Q₁ : Set G) := hAS.trans
      (le_sup_right.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _))
    have hAQ₂ : A ≤ Subgroup.normalizer (Q₂ : Set G) := hAS.trans
      (le_sup_right.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _))
    have ha₁ : (A ⊓ Q₁).relIndex A = Q₁.relIndex (baum R) := by
      rw [C5.relIndex_inf_eq_of_le_normalizer hAQ₁, hs₁]
    have ha₂ : (A ⊓ Q₂).relIndex A = Q₂.relIndex (baum R) := by
      rw [C5.relIndex_inf_eq_of_le_normalizer hAQ₂, hs₂]
    have hm : (A ⊓ A₀).relIndex A = A₀.relIndex (A ⊔ A₀) := C5.relIndex_inf_eq_of_le_normalizer hAN
    have hsup : A ⊔ A₀ = baum R := by
      have hle1 : A₀.relIndex (baum R) ≤ Q₁.relIndex (baum R) * Q₂.relIndex (baum R) := by
        rw [hA₀Q]; exact Subgroup.relIndex_inf_le
      have hle2 : A₀.relIndex (A ⊔ A₀) ≤ A₀.relIndex (baum R) :=
        C5.relIndex_le_of_le le_sup_right (sup_le hAS hA₀S)
      have heq : A₀.relIndex (A ⊔ A₀) = A₀.relIndex (baum R) := by
        refine le_antisymm hle2 ?_
        rw [← hm, hE2, ha₁, ha₂]; exact hle1
      exact C5.eq_of_relIndex_eq le_sup_right (sup_le hAS hA₀S) heq
        (Subgroup.index_ne_zero_of_finite (H := A₀.subgroupOf (baum R)))
    refine ⟨hsup, ?_⟩
    rw [hE1]
    apply le_antisymm
    · intro c hc
      obtain ⟨hcA₀, hcC⟩ := Subgroup.mem_inf.mp hc
      have hcS : c ∈ Subgroup.centralizer (baum R : Set G) := by
        rw [← hsup, burnsideC56_b_centralizer_sup]
        refine Subgroup.mem_inf.mpr ⟨hcC, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact h.A₀_elem.1 a ha c hcA₀
      have : c ∈ baum R ⊓ Subgroup.centralizer (baum R : Set G) := ⟨hA₀S hcA₀, hcS⟩
      rwa [h.Z_eq] at this
    · intro c hc
      have hcZ : c ∈ baum R ⊓ Subgroup.centralizer (baum R : Set G) := by rw [h.Z_eq]; exact hc
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.centralizer_le (SetLike.coe_mono hAS) hcZ.2⟩
      have hED : (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
          (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ≤ A₀ :=
        sup_le ((sup_le_sup h.pairX.E₁_le_U₁ h.pairX.E₂_le_U₂).trans le_sup_right) le_sup_left
      exact hED hc

theorem central {z s : G} (hz : z ∈ (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))) (hs : s ∈ baum R) :
    Commute s z := by
  rw [← h.Z_eq] at hz
  exact Subgroup.mem_centralizer_iff.mp hz.2 s hs

theorem no_diagonal {A : Subgroup G} (hAS : A ≤ baum R) (hAe : C5.ElemAb2 A)
    (hsup : A ⊔ ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁))) = baum R)
    (hinf : A ⊓ ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x)) =
      (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)))
    {b b₂ : G} (hb : b ∈ conjSubgroup (blockU K₁) x)
    (hbC : blockU K₁ ⊓ Subgroup.centralizer ({b} : Set G) = ⁅blockU K₁, baum R⁆)
    (hb₂ : b₂ ∈ conjSubgroup (blockU (conjByElt t K₁)) x)
    (hb₂C : blockU (conjByElt t K₁) ⊓ Subgroup.centralizer ({b₂} : Set G) =
      ⁅blockU (conjByElt t K₁), baum R⁆) : False := by
  set D := baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) with hD
  set U₁ := blockU K₁ with hU₁
  set U₂ := blockU (conjByElt t K₁) with hU₂
  set E₁ := ⁅blockU K₁, baum R⁆ with hE₁
  set E₂ := ⁅blockU (conjByElt t K₁), baum R⁆ with hE₂
  set A₀ := D ⊔ (U₁ ⊔ U₂) with hA₀
  have hAN : A ≤ Subgroup.normalizer (A₀ : Set G) := hAS.trans h.S_norm_A₀
  have hbS : b ∈ baum R := h.V_le_S (Subgroup.mem_sup_left hb)
  have hb₂S : b₂ ∈ baum R := h.V_le_S (Subgroup.mem_sup_right hb₂)
  have hU₁S : U₁ ≤ baum R := burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_self TH K₁)
  have hU₂S : U₂ ≤ baum R :=
    burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_conj h.two.ht)
  have hU₁e := burnsideC56_s_U_elem h.two.set
  have hU₂e := burnsideC56_s_U_elem h.two.set₂
  have hEZ₁ : ∀ e ∈ E₁, ∀ s ∈ baum R, Commute s e := fun e he s hs =>
    h.central (Subgroup.mem_sup_left (Subgroup.mem_sup_left he)) hs
  have hEZ₂ : ∀ e ∈ E₂, ∀ s ∈ baum R, Commute s e := fun e he s hs =>
    h.central (Subgroup.mem_sup_left (Subgroup.mem_sup_right he)) hs
  have hDZ : ∀ d ∈ D, ∀ s ∈ baum R, Commute s d := fun d hd s hs =>
    h.central (Subgroup.mem_sup_right hd) hs
  have hdec : ∀ g ∈ baum R, ∃ a ∈ A, ∃ d ∈ D, ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂,
      a = g * (d * (u₁ * u₂)) := by
    intro g hg
    have hg' : g ∈ A ⊔ A₀ := by rw [hsup]; exact hg
    obtain ⟨a, ha, w, hw, hgaw⟩ := C5.mem_sup_of_le_normalizer hAN hg'
    obtain ⟨d, hd, u, hu, hwu⟩ := C5.mem_sup_of_commute (fun d hd u hu => h.D_comm_U hd hu)
      (inv_mem hw)
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := C5.mem_sup_of_commute
      (fun a ha b hb => h.two.U_comm ha hb) hu
    exact ⟨a, ha, d, hd, u₁, hu₁, u₂, hu₂, by rw [← hwu, hgaw]; group⟩
  obtain ⟨a, ha, d, hd, u₁, hu₁, u₂, hu₂, haeq⟩ := hdec b hbS
  obtain ⟨a₂, ha₂, d₂, hd₂, v₁, hv₁, v₂, hv₂, ha₂eq⟩ := hdec b₂ hb₂S
  have hdS : d ∈ baum R := hd.1
  have hd₂S : d₂ ∈ baum R := hd₂.1
  have hb2 : b ^ 2 = 1 := h.V_elem.2 b (Subgroup.mem_sup_left hb)
  have hb₂2 : b₂ ^ 2 = 1 := h.V_elem.2 b₂ (Subgroup.mem_sup_right hb₂)
  have c_bu₂ : Commute b u₂ := h.pairX.comm_V₁_U₂ hb hu₂
  have c_u₁u₂ : Commute u₁ u₂ := h.two.U_comm hu₁ hu₂
  have hu₁E : u₁ ∈ E₁ := by
    have hcd : Commute d (u₁ * u₂) := (hDZ d hd _ (mul_mem (hU₁S hu₁) (hU₂S hu₂))).symm
    have e1 : a = (b * u₁) * (u₂ * d) := by
      rw [haeq, hcd.eq]; group
    have c1 : Commute (b * u₁) (u₂ * d) :=
      (c_bu₂.mul_left c_u₁u₂).mul_right
        ((hDZ d hd _ (mul_mem hbS (hU₁S hu₁))))
    have c2 : Commute u₂ d := hDZ d hd u₂ (hU₂S hu₂)
    have hsq : (b * u₁) ^ 2 = 1 := by
      have := hAe.2 a ha
      rw [e1, c1.mul_pow, c2.mul_pow, hU₂e.2 u₂ hu₂, h.D_elem.2 d hd, one_mul, mul_one] at this
      exact this
    have hc := burnsideC5x_A5Cfg.Mate.comm_of_sq hsq hb2 (hU₁e.2 u₁ hu₁)
    rw [← hbC]
    refine ⟨hu₁, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact hc
  have c_v₁b₂ : Commute v₁ b₂ := h.pairX.comm_U₁_V₂ hv₁ hb₂
  have c_v₁v₂ : Commute v₁ v₂ := h.two.U_comm hv₁ hv₂
  have hv₂E : v₂ ∈ E₂ := by
    have hcd : Commute d₂ (v₁ * v₂) := (hDZ d₂ hd₂ _ (mul_mem (hU₁S hv₁) (hU₂S hv₂))).symm
    have e1 : a₂ = (b₂ * v₂) * (v₁ * d₂) := by
      rw [ha₂eq, hcd.eq, c_v₁v₂.eq]; group
    have c1 : Commute (b₂ * v₂) (v₁ * d₂) :=
      (c_v₁b₂.symm.mul_left c_v₁v₂.symm).mul_right
        ((hDZ d₂ hd₂ _ (mul_mem hb₂S (hU₂S hv₂))))
    have c2 : Commute v₁ d₂ := hDZ d₂ hd₂ v₁ (hU₁S hv₁)
    have hsq : (b₂ * v₂) ^ 2 = 1 := by
      have := hAe.2 a₂ ha₂
      rw [e1, c1.mul_pow, c2.mul_pow, hU₁e.2 v₁ hv₁, h.D_elem.2 d₂ hd₂, one_mul, mul_one] at this
      exact this
    have hc := burnsideC5x_A5Cfg.Mate.comm_of_sq hsq hb₂2 (hU₂e.2 v₂ hv₂)
    rw [← hb₂C]
    refine ⟨hv₂, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact hc
  have hu₂E : u₂ ∈ E₂ := by
    have hzS : u₁ * d ∈ baum R := mul_mem (hU₁S hu₁) hdS
    have hz₂S : v₂ * d₂ ∈ baum R := mul_mem (hU₂S hv₂) hd₂S
    have hzc : ∀ s ∈ baum R, Commute s (u₁ * d) := fun s hs =>
      (hEZ₁ u₁ hu₁E s hs).mul_right (hDZ d hd s hs)
    have hz₂c : ∀ s ∈ baum R, Commute s (v₂ * d₂) := fun s hs =>
      (hEZ₂ v₂ hv₂E s hs).mul_right (hDZ d₂ hd₂ s hs)
    have hcd : Commute d (u₁ * u₂) := (hDZ d hd _ (mul_mem (hU₁S hu₁) (hU₂S hu₂))).symm
    have hcd₂ : Commute d₂ (v₁ * v₂) := (hDZ d₂ hd₂ _ (mul_mem (hU₁S hv₁) (hU₂S hv₂))).symm
    have e1 : a = (b * u₂) * (u₁ * d) := by
      rw [haeq, hcd.eq, c_u₁u₂.eq]; group
    have e2 : a₂ = (b₂ * v₁) * (v₂ * d₂) := by
      rw [ha₂eq, hcd₂.eq]; group
    have key : ∀ X Y z z₂ : G, Commute z Y → X * z * (Y * z₂) = (X * Y) * (z * z₂) := by
      intro X Y z z₂ hc
      calc X * z * (Y * z₂) = X * (z * Y) * z₂ := by group
        _ = X * (Y * z) * z₂ := by rw [hc.eq]
        _ = (X * Y) * (z * z₂) := by group
    have hcomm : (b * u₂) * (b₂ * v₁) = (b₂ * v₁) * (b * u₂) := by
      have h0 : a * a₂ = a₂ * a := hAe.1 a ha a₂ ha₂
      rw [e1, e2] at h0
      have hX : b * u₂ ∈ baum R := mul_mem hbS (hU₂S hu₂)
      have hY : b₂ * v₁ ∈ baum R := mul_mem hb₂S (hU₁S hv₁)
      rw [key _ _ _ _ (hzc _ hY).symm, key _ _ _ _ (hz₂c _ hX).symm,
        ((hz₂c _ hzS).eq : (u₁ * d) * (v₂ * d₂) = (v₂ * d₂) * (u₁ * d))] at h0
      exact mul_right_cancel h0
    set e := b * v₁ * b⁻¹ * v₁⁻¹ with he
    set f := u₂ * b₂ * u₂⁻¹ * b₂⁻¹ with hf
    have heE : e ∈ E₁ := by
      rw [hE₁, burnsideC56_s_E_eq_comm h.pairX.p2₁, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb hv₁
    have hfE : f ∈ E₂ := by
      rw [hE₂, burnsideC56_s_E_eq_comm h.pairX.p2₂]
      exact Subgroup.commutator_mem_commutator hu₂ hb₂
    have hW : b * b₂ * u₂ * v₁ ∈ baum R :=
      mul_mem (mul_mem (mul_mem hbS hb₂S) (hU₂S hu₂)) (hU₁S hv₁)
    have r1 : u₂ * b₂ = f * (b₂ * u₂) := by rw [hf]; group
    have r2 : v₁ * b = e⁻¹ * (b * v₁) := by rw [he]; group
    have c_bb₂ : Commute b b₂ := h.pairX.comm_V₁_V₂ hb hb₂
    have c_v₁u₂ : Commute v₁ u₂ := h.two.U_comm hv₁ hu₂
    have hfe : f = e⁻¹ := by
      have hL : (b * u₂) * (b₂ * v₁) = f * (b * b₂ * u₂ * v₁) := by
        calc (b * u₂) * (b₂ * v₁) = b * (u₂ * b₂) * v₁ := by group
          _ = b * (f * (b₂ * u₂)) * v₁ := by rw [r1]
          _ = (b * f) * (b₂ * u₂ * v₁) := by group
          _ = (f * b) * (b₂ * u₂ * v₁) := by rw [(hEZ₂ f hfE b hbS).eq]
          _ = f * (b * b₂ * u₂ * v₁) := by group
      have hR : (b₂ * v₁) * (b * u₂) = e⁻¹ * (b * b₂ * u₂ * v₁) := by
        have heS : ∀ s ∈ baum R, Commute s e⁻¹ := fun s hs => (hEZ₁ e heE s hs).inv_right
        calc (b₂ * v₁) * (b * u₂) = b₂ * (v₁ * b) * u₂ := by group
          _ = b₂ * (e⁻¹ * (b * v₁)) * u₂ := by rw [r2]
          _ = (b₂ * e⁻¹) * (b * v₁ * u₂) := by group
          _ = (e⁻¹ * b₂) * (b * v₁ * u₂) := by rw [(heS b₂ hb₂S).eq]
          _ = e⁻¹ * (b₂ * b * (v₁ * u₂)) := by group
          _ = e⁻¹ * (b * b₂ * (u₂ * v₁)) := by rw [c_bb₂.eq, c_v₁u₂.eq]
          _ = e⁻¹ * (b * b₂ * u₂ * v₁) := by group
      rw [hL, hR] at hcomm
      exact mul_right_cancel hcomm
    have hf1 : f = 1 := by
      have : f ∈ E₁ ⊓ E₂ := Subgroup.mem_inf.mpr ⟨by rw [hfe]; exact inv_mem heE, hfE⟩
      rw [h.E_inf, Subgroup.mem_bot] at this
      exact this
    have hc : u₂ * b₂ = b₂ * u₂ := by rw [r1, hf1, one_mul]
    rw [← hb₂C]
    refine ⟨hu₂, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact hc.symm
  have hED_B₀ : (E₁ ⊔ E₂) ⊔ D ≤ D ⊔ (conjSubgroup U₁ x ⊔ conjSubgroup U₂ x) :=
    sup_le (h.E_le_V.trans le_sup_right) le_sup_left
  have haB₀ : a ∈ D ⊔ (conjSubgroup U₁ x ⊔ conjSubgroup U₂ x) := by
    rw [haeq]
    refine mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hb)) ?_
    refine mul_mem (Subgroup.mem_sup_left hd) (mul_mem ?_ ?_)
    · exact hED_B₀ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu₁E))
    · exact hED_B₀ (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu₂E))
  have haZ : a ∈ (E₁ ⊔ E₂) ⊔ D := by rw [← hinf]; exact ⟨ha, haB₀⟩
  have hwZ : d * (u₁ * u₂) ∈ (E₁ ⊔ E₂) ⊔ D :=
    mul_mem (Subgroup.mem_sup_right hd) (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu₁E))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu₂E)))
  have hbZ : b ∈ (E₁ ⊔ E₂) ⊔ D := by
    have : b = a * (d * (u₁ * u₂))⁻¹ := by rw [haeq]; group
    rw [this]
    exact mul_mem haZ (inv_mem hwZ)
  apply h.hx.2.2
  have hU₁E : U₁ ≤ E₁ := by
    intro u hu
    rw [← hbC]
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact (h.central hbZ (hU₁S hu)).eq.symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  have := hU₁E hu
  rw [hE₁, burnsideC56_s_E_eq_C h.pairX.p2₁] at this
  exact this.2

theorem invariant_members
    (hpb : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K))
    (hpbeq : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      TH ≤ Subgroup.normalizer (A : Set G) →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A =
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) →
      A ≤ pCoreOf 2 (K ⊔ baum R) ∨ A ⊔ pCoreOf 2 (K ⊔ baum R) = baum R)
    (hb6 : ∀ (K : Subgroup G) (y : G), SetC53 H M₀ TH R K → GoodX H M₀ K y →
      ∃ b ∈ conjSubgroup (blockU K) y,
        blockU K ⊓ Subgroup.centralizer ({b} : Set G) = ⁅blockU K, baum R⁆) :
    {A | A ∈ AFam R ∧ TH ≤ Subgroup.normalizer (A : Set G)} =
      {(baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (blockU K₁ ⊔ blockU (conjByElt t K₁)),
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x)} := by
  ext A
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hA, hTH⟩
    have hA' : IsMaxElemAbelian R A := hA
    rcases h.core hpb hpbeq hA' hTH with h1 | ⟨hsup, hinf₀⟩
    · exact Or.inl h1
    · right
      have hxR : x⁻¹ ∈ Subgroup.normalizer (R : Set G) := inv_mem (h.two.set.hyp1.R_norm h.hx.1)
      have hA'max : IsMaxElemAbelian R (conjSubgroup A x⁻¹) :=
        C56.isMaxElemAbelian_conjSubgroup hA' hxR
      have hTH' : TH ≤ Subgroup.normalizer ((conjSubgroup A x⁻¹ : Subgroup G) : Set G) :=
        C5.le_normalizer_conj (inv_mem h.x_norm_TH) hTH
      rcases h.core hpb hpbeq hA'max hTH' with h2 | ⟨-, hinf'⟩
      · have := congrArg (fun X => conjSubgroup X x) h2
        simp only [C5.conjSubgroup_inv_conjSubgroup] at this
        rw [this, h.A₀_conj]
      · exfalso
        have hinfB : A ⊓ ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
            (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x)) =
            (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
              (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) := by
          have e0 : conjSubgroup (conjSubgroup A x⁻¹ ⊓ ((baum R ⊓ Subgroup.centralizer
              (oTwoUpper H : Set G)) ⊔ (blockU K₁ ⊔ blockU (conjByElt t K₁)))) x =
              conjSubgroup ((⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆) ⊔
                (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))) x := by rw [hinf']
          rw [C5.conjSubgroup_inf, C5.conjSubgroup_inv_conjSubgroup, h.A₀_conj,
            C5.conjSubgroup_sup (⁅blockU K₁, baum R⁆ ⊔ ⁅blockU (conjByElt t K₁), baum R⁆),
            h.conj_E, h.ED_conj] at e0
          exact e0
        obtain ⟨b, hb, hbC⟩ := hb6 K₁ x h.two.set h.hx
        obtain ⟨b₂, hb₂, hb₂C⟩ := hb6 _ x h.two.set₂ h.good₂
        exact h.no_diagonal (h.le_S_of_max hA') (C5.isElemAbelian_two_iff.mp hA'.2.1) hsup hinfB
          hb hbC hb₂ hb₂C
  · rintro (rfl | rfl)
    · exact ⟨h.A₀_max hpb, h.TH_norm_A₀⟩
    · exact ⟨h.B₀_max hpb, h.TH_norm_B₀⟩

end burnsideC56_S7

end PartBurnsideC56AR

section PartBurnsideC56Concl7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

namespace burnsideC56_S7

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
  (h : burnsideC56_S7 H M₀ TH R K₁ t x)
include h

theorem S_eq_sup : baum R = ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
    (blockU K₁ ⊔ blockU (conjByElt t K₁))) ⊔
      (conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x) := by
  apply le_antisymm
  · intro s hs
    obtain ⟨v, hv, u, hu, d, hd, rfl⟩ := h.pairX.decomp' hs
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hv)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd))
  · exact sup_le h.A₀_le_S h.V_le_S

theorem S_norm_V : baum R ≤ Subgroup.normalizer
    ((conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x : Subgroup G) :
      Set G) := fun s hs =>
  C1.mem_normalizer_sup (burnsideC56_s_S_norm_Uy h.h116 h.two.set h.hx.1 hs)
    (burnsideC56_s_S_norm_Uy h.h116 h.two.set₂ h.hx.1 hs)

theorem S_norm_D : baum R ≤ Subgroup.normalizer
    ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) := by
  intro s hs
  refine C5.mem_normalizer_inf (Subgroup.le_normalizer hs) (C5.mem_normalizer_centralizer ?_)
  rw [h.two.oTwoUpper_eq]
  exact C1.mem_normalizer_sup
    ((burnsideC56_b_c54 h.h116 h.two.set (burnsideC56_b_mem_self TH K₁)).1 hs)
    ((burnsideC56_b_c54 h.h116 h.two.set (burnsideC56_b_mem_conj h.two.ht)).1 hs)

theorem S_eq_mul : (baum R : Set G) =
    (((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)) : Subgroup G) : Set G) *
      ((conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x : Subgroup G) :
        Set G) := by
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (h.A₀_le_S.trans h.S_norm_V),
    ← h.S_eq_sup]

theorem S_eq_mul' : (baum R : Set G) =
    ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) *
      ((conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x : Subgroup G) :
        Set G) *
      ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) := by
  have hUS := h.U_le_S
  have hUV := Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUS.trans h.S_norm_V)
  rw [← hUV, ← Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((sup_le hUS h.V_le_S).trans h.S_norm_D)]
  congr 1
  refine h.S_eq_sup.trans (le_antisymm ?_ ?_)
  · exact sup_le (sup_le le_sup_right (le_sup_of_le_left le_sup_left))
      (le_sup_of_le_left le_sup_right)
  · exact sup_le (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
      (le_sup_of_le_left le_sup_left)

theorem S_eq_J
    (hpb : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K)) :
    baum R = thompsonJ R := by
  refine le_antisymm ?_ (C5.thompsonJ_le_baum' R)
  rw [h.S_eq_sup]
  refine sup_le (le_iSup₂_of_le _ (h.A₀_max hpb) le_rfl) ?_
  exact le_sup_right.trans (le_iSup₂_of_le _ (h.B₀_max hpb) le_rfl)

theorem concl7
    (hpb : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K))
    (hpbeq : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      TH ≤ Subgroup.normalizer (A : Set G) →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A =
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) →
      A ≤ pCoreOf 2 (K ⊔ baum R) ∨ A ⊔ pCoreOf 2 (K ⊔ baum R) = baum R)
    (hb6 : ∀ (K : Subgroup G) (y : G), SetC53 H M₀ TH R K → GoodX H M₀ K y →
      ∃ b ∈ conjSubgroup (blockU K) y,
        blockU K ⊓ Subgroup.centralizer ({b} : Set G) = ⁅blockU K, baum R⁆)
    (hP : pCoreOf 2 (oTwoUpper H ⊔ R) = (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)))
    (hCR : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) =
      R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))
    (hU : blockU K₁ ⊔ blockU (conjByElt t K₁) = pCoreOf 2 (oTwoUpper H)) :
    burnsideC5x_Concl7 H M₀ TH R K₁ x := by
  unfold burnsideC5x_Concl7
  rw [h.two.iSup_eq]
  have hrU : rconj x (blockU K₁ ⊔ blockU (conjByElt t K₁)) =
      conjSubgroup (blockU K₁) x ⊔ conjSubgroup (blockU (conjByElt t K₁)) x :=
    C5.conjSubgroup_sup _ _ _
  rw [hrU]
  exact ⟨hU, h.frattini_eq_bot, h.D_inf_conj, hCR, hP, h.A₀_max hpb, h.S_eq_mul, h.S_eq_J hpb,
    Or.inr ⟨⟨t, h.two.ht, h.two.hne⟩, h.S_eq_mul', h.invariant_members hpb hpbeq hb6⟩⟩

end burnsideC56_S7

end PartBurnsideC56Concl7

section PartBurnsideC56G1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

namespace burnsideC56_Two

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t : G}
  (h : burnsideC56_Two H M₀ TH R K₁ t)
include h

theorem t_not_mem : t ∉ Subgroup.normalizer (K₁ : Set G) := fun ht =>
  h.hne (C2Eleven.mem_normalizer_iff_conjByElt.mp ht)

theorem conj₂ : conjByElt t (conjByElt t K₁) = K₁ := h.conj₂_eq_of_not_mem h.ht h.t_not_mem

theorem swap : burnsideC56_Two H M₀ TH R (conjByElt t K₁) t := by
  refine ⟨h.set₂, h.ht, ?_⟩
  rw [h.conj₂]
  exact fun e => h.hne e.symm

end burnsideC56_Two

namespace burnsideC56_S7

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
  (h : burnsideC56_S7 H M₀ TH R K₁ t x)
include h

theorem swap : burnsideC56_S7 H M₀ TH R (conjByElt t K₁) t x :=
  ⟨h.two.swap, h.h116, h.h14, h.good₂, h.hidx⟩

theorem K₁_le_CU₂ : K₁ ≤ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) :=
  fun k hk => Subgroup.centralizer_le
    (SetLike.coe_mono (burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_conj h.two.ht)))
    (h.two.K₁_le_centralizer hk)

theorem V₁_le_CU₂ : conjSubgroup (blockU K₁) x ≤
    Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) := fun v hv => by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h.pairX.comm_V₁_U₂ hv hu).symm

theorem D₁_inf_CU₂ {d : G} (hd : d ∈ baum R ⊓ Subgroup.centralizer (K₁ : Set G))
    (hdC : d ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G)) :
    ∃ u ∈ blockU (conjByElt t K₁), ∃ e ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G),
      d = u * e := by
  obtain ⟨-, -, hQ₂⟩ := burnsideC56_b_c54 h.h116 h.two.set₂
    (burnsideC56_b_mem_self TH (conjByElt t K₁))
  have hdQ : d ∈ blockU (conjByElt t K₁) ⊔
      (baum R ⊓ Subgroup.centralizer (conjByElt t K₁ : Set G)) := by
    rw [← h.pairX.p1₂.1, hQ₂]; exact ⟨hd.1, hdC⟩
  obtain ⟨u, hu, e, he, rfl⟩ := C5.mem_sup_of_commute
    (fun u hu e he => burnsideC56_s_D_comm_U h.two.set₂ hu he) hdQ
  refine ⟨u, hu, e, ?_, rfl⟩
  rw [h.two.mem_D]
  refine ⟨Subgroup.mem_inf.mpr ⟨he.1, ?_⟩, he⟩
  have : e = u⁻¹ * (u * e) := by group
  rw [this]
  exact (mul_mem (inv_mem (h.two.U₂_le_D₁ h.h116 hu)) hd).2

theorem D₁_inf_CU₂_sq {d : G} (hd : d ∈ baum R ⊓ Subgroup.centralizer (K₁ : Set G))
    (hdC : d ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G)) : d * d = 1 := by
  obtain ⟨u, hu, e, he, rfl⟩ := h.D₁_inf_CU₂ hd hdC
  have hc : Commute u e := (h.D_comm_U he (Subgroup.mem_sup_right hu)).symm
  have h1 : (u * e) ^ 2 = 1 := by
    rw [hc.mul_pow, (burnsideC56_s_U_elem h.two.set₂).2 u hu, h.D_elem.2 e he, one_mul]
  rwa [pow_two] at h1

theorem Z_elem : C5.ElemAb2 (blockU (conjByElt t K₁) ⊔
    (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))) :=
  C5.ElemAb2.sup (burnsideC56_s_U_elem h.two.set₂) h.D_elem
    (fun u hu d hd => (h.D_comm_U hd (Subgroup.mem_sup_right hu)).symm)

theorem Z_le_CK₁ : blockU (conjByElt t K₁) ⊔ (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ≤
    Subgroup.centralizer (K₁ : Set G) := by
  refine sup_le ((burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_conj h.two.ht)).trans
    h.two.K₂_le_centralizer) fun d hd => ?_
  exact ((h.two.mem_D.mp hd).1).2

theorem Z_le_S : blockU (conjByElt t K₁) ⊔ (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ≤
    baum R :=
  sup_le (burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_conj h.two.ht)) inf_le_left

theorem QK_le : pCoreOf 2 (K₁ ⊔ baum R) ⊓ K₁ ≤
    blockU K₁ ⊔ (blockU (conjByElt t K₁) ⊔ (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))) := by
  intro q hq
  obtain ⟨hqQ, hqK⟩ := Subgroup.mem_inf.mp hq
  rw [h.pairX.p1₁.1] at hqQ
  obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute
    (fun u hu d hd => burnsideC56_s_D_comm_U h.two.set hu hd) hqQ
  have hdK : d ∈ K₁ := by
    have : d = u⁻¹ * (u * d) := by group
    rw [this]
    exact mul_mem (inv_mem (burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_self TH K₁) hu)) hqK
  have hdD : d ∈ baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
    rw [h.two.mem_D]
    exact ⟨hd, hd.1, h.two.K₁_le_centralizer hdK⟩
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (Subgroup.mem_sup_right hdD))

theorem V_le_KZ (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) :
    conjSubgroup (blockU K₁) x ≤
      K₁ ⊔ (blockU (conjByElt t K₁) ⊔ (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))) := by
  intro v hv
  have hvS := burnsideC56_b_conj_U_le_S h.h116 h.two.set (burnsideC56_b_mem_self TH K₁) h.hx.1 hv
  obtain ⟨-, hlin, -, -, -⟩ := burnsideC5h_p2_lin2A3 h.h116 h.two.set
    (burnsideC5h_p1_minParabolic h.two.set (burnsideC5h_c54_one h.h116 h.two.set)) K₁
    (burnsideC56_b_mem_self TH K₁) (Or.inl hn)
  have hv' : v ∈ (baum R : Set G) := hvS
  rw [hlin hn] at hv'
  obtain ⟨k, hk, q, hq, rfl⟩ := hv'
  have hq' : q ∈ blockU K₁ ⊔ (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) := by
    rw [← h.pairX.p1₁.1]; exact hq
  obtain ⟨u, hu, d, hd, rfl⟩ := C5.mem_sup_of_commute
    (fun u hu d hd => burnsideC56_s_D_comm_U h.two.set hu hd) hq'
  have hku : k * u ∈ K₁ :=
    mul_mem (Subgroup.mem_inf.mp hk).2 (burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_self TH K₁) hu)
  have hdC : d ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) := by
    have : d = (k * u)⁻¹ * (k * (u * d)) := by group
    rw [this]
    exact mul_mem (inv_mem (h.K₁_le_CU₂ hku)) (h.V₁_le_CU₂ hv)
  obtain ⟨u₂, hu₂, e, he, rfl⟩ := h.D₁_inf_CU₂ hd hdC
  show k * (u * (u₂ * e)) ∈ _
  have : k * (u * (u₂ * e)) = (k * u) * (u₂ * e) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hku) (Subgroup.mem_sup_right
    (mul_mem (Subgroup.mem_sup_left hu₂) (Subgroup.mem_sup_right he)))

end burnsideC56_S7

end PartBurnsideC56G1

section PartBurnsideC56Core

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

theorem burnsideC56_core_P_le {G : Type} [Group G] {R S P U V D : Subgroup G} {y : G}
    (hyR : y ∈ Subgroup.normalizer (R : Set G)) (hyS : y ∈ Subgroup.normalizer (S : Set G))
    (hdec : ∀ s ∈ S, ∃ v ∈ V, ∃ u ∈ U, ∃ d ∈ D, s = v * u * d)
    (hVP : V ≤ conjSubgroup P y) (hDP : D ≤ conjSubgroup P y)
    (hPR : P ≤ R) (hSR : S ≤ R) (hRP : R ≤ Subgroup.normalizer (P : Set G)) (hUP : U ≤ P)
    (hPU : ∀ p ∈ P, ∀ u ∈ U, u * p = p * u)
    (hSC : ∀ r ∈ R, (∀ b ∈ S, ⁅r, b⁆ ∈ P) → r ∈ S ⊔ P) :
    P ≤ U ⊔ (P ⊓ conjSubgroup P y) := by
  intro p hp
  have hpR : p ∈ R := hPR hp
  have hRPy : R ≤ Subgroup.normalizer ((conjSubgroup P y : Subgroup G) : Set G) :=
    C5.le_normalizer_conj hyR hRP
  have key : ∀ b' ∈ S, ⁅p, b'⁆ ∈ conjSubgroup P y := by
    intro b' hb'
    obtain ⟨v, hv, u, hu, d, hd, rfl⟩ := hdec b' hb'
    have hc : ⁅p, u⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hPU p hp u hu).symm
    have e2 : ⁅p, v * u * d⁆ = ⁅p, v⁆ * (v * ⁅p, u * d⁆ * v⁻¹) := by
      simp only [commutatorElement_def]; group
    have e1 : ⁅p, u * d⁆ = ⁅p, u⁆ * (u * ⁅p, d⁆ * u⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e2, e1, hc, one_mul]
    have hvP := hVP hv
    have hdP := hDP hd
    have m1 : ⁅p, v⁆ ∈ conjSubgroup P y := by
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hRPy hpR) v).mp hvP) (inv_mem hvP)
    have m2 : ⁅p, d⁆ ∈ conjSubgroup P y := by
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hRPy hpR) d).mp hdP) (inv_mem hdP)
    have m3 : u * ⁅p, d⁆ * u⁻¹ ∈ conjSubgroup P y :=
      (Subgroup.mem_normalizer_iff.mp (hRPy (hPR (hUP hu))) _).mp m2
    exact mul_mem m1 (mul_mem (mul_mem hvP m3) (inv_mem hvP))
  have hrR : y * p * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hyR p).mp hpR
  have hS2 : ∀ b ∈ S, ⁅y * p * y⁻¹, b⁆ ∈ P := by
    intro b hb
    have hb' : y⁻¹ * b * y ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyS) b).mp hb
      simpa using this
    have e : ⁅y * p * y⁻¹, b⁆ = y * ⁅p, y⁻¹ * b * y⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact CFSG.Quasithin.mem_conjSubgroup_iff.mp (key _ hb')
  obtain ⟨b₂, hb₂, p₂, hp₂, hr⟩ :=
    C5.mem_sup_of_le_normalizer (hSR.trans hRP) (hSC _ hrR hS2)
  have hb₃ : y⁻¹ * b₂ * y ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyS) b₂).mp hb₂
    simpa using this
  have hp₃ : y⁻¹ * p₂ * y ∈ conjSubgroup P y := by
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    have e : y * (y⁻¹ * p₂ * y) * y⁻¹ = p₂ := by group
    rw [e]
    exact hp₂
  obtain ⟨v, hv, u, hu, d, hd, hb₃eq⟩ := hdec _ hb₃
  have hpeq : p = u * ((u⁻¹ * v * u) * d * (y⁻¹ * p₂ * y)) := by
    calc p = y⁻¹ * (y * p * y⁻¹) * y := by group
      _ = y⁻¹ * (b₂ * p₂) * y := by rw [hr]
      _ = (y⁻¹ * b₂ * y) * (y⁻¹ * p₂ * y) := by group
      _ = v * u * d * (y⁻¹ * p₂ * y) := by rw [hb₃eq]
      _ = u * ((u⁻¹ * v * u) * d * (y⁻¹ * p₂ * y)) := by group
  have huR : u ∈ R := hPR (hUP hu)
  have hw : (u⁻¹ * v * u) * d * (y⁻¹ * p₂ * y) ∈ conjSubgroup P y := by
    have h1 : u⁻¹ * v * u ∈ conjSubgroup P y := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (hRPy (inv_mem huR)) v).mp (hVP hv)
      rwa [inv_inv] at h2
    exact mul_mem (mul_mem h1 (hDP hd)) hp₃
  have hwP : (u⁻¹ * v * u) * d * (y⁻¹ * p₂ * y) ∈ P := by
    have e : (u⁻¹ * v * u) * d * (y⁻¹ * p₂ * y) = u⁻¹ * p := by
      rw [hpeq]; group
    rw [e]
    exact mul_mem (inv_mem (hUP hu)) hp
  rw [hpeq]
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨hwP, hw⟩)

theorem burnsideC56_core_sqSub_conj {G : Type} [Group G] {P U : Subgroup G} {x : G}
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hUP : U ≤ P) (hPU : ∀ p ∈ P, ∀ u ∈ U, u * p = p * u)
    (h1 : P ≤ U ⊔ (P ⊓ conjSubgroup P x)) (h2 : P ≤ U ⊔ (P ⊓ conjSubgroup P x⁻¹)) :
    conjSubgroup (C5.sqSub P) x = C5.sqSub P := by
  have e1 : P = U ⊔ (P ⊓ conjSubgroup P x) := le_antisymm h1 (sup_le hUP inf_le_left)
  have e2 : P = U ⊔ (P ⊓ conjSubgroup P x⁻¹) := le_antisymm h2 (sup_le hUP inf_le_left)
  have hcomm : ∀ A : Subgroup G, A ≤ P → ∀ u ∈ U, ∀ a ∈ A, u * a = a * u :=
    fun A hA u hu a ha => hPU a (hA ha) u hu
  have s1 : C5.sqSub P = C5.sqSub (P ⊓ conjSubgroup P x) := by
    conv_lhs => rw [e1]
    exact C5.sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  have s2 : C5.sqSub P = C5.sqSub (P ⊓ conjSubgroup P x⁻¹) := by
    conv_lhs => rw [e2]
    exact C5.sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  calc conjSubgroup (C5.sqSub P) x = conjSubgroup (C5.sqSub (P ⊓ conjSubgroup P x⁻¹)) x := by
        rw [← s2]
    _ = C5.sqSub (conjSubgroup (P ⊓ conjSubgroup P x⁻¹) x) := C5.conjSubgroup_sqSub _ _
    _ = C5.sqSub (P ⊓ conjSubgroup P x) := by
        rw [C5.conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
          inf_comm]
    _ = C5.sqSub P := s1.symm

theorem burnsideC56_S7.core_P_eq_CRU {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {t x : G} (h : burnsideC56_S7 H M₀ TH R K₁ t x) :
    R ⊓ Subgroup.centralizer ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) =
      pCoreOf 2 (oTwoUpper H ⊔ R) := by
  rw [← h.two.iSup_eq]
  exact burnsideC5h_c54_four_second as_C_1_11 h.two.set

theorem burnsideC56_S7.core_U_le_S {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {t x : G} (h : burnsideC56_S7 H M₀ TH R K₁ t x) :
    blockU K₁ ⊔ blockU (conjByElt t K₁) ≤ baum R :=
  sup_le (burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_self TH K₁))
    (burnsideC56_b_U_le_S h.h116 h.two.set (burnsideC56_b_mem_conj h.two.ht))

theorem burnsideC56_S7.core_U_elem {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {t x : G} (h : burnsideC56_S7 H M₀ TH R K₁ t x) :
    C5.ElemAb2 (blockU K₁ ⊔ blockU (conjByElt t K₁)) :=
  C5.ElemAb2.sup (burnsideC56_s_U_elem h.two.set) (burnsideC56_s_U_elem h.two.set₂)
    (fun _ ha _ hb => h.two.U_comm ha hb)

theorem burnsideC56_S7.core_U_le_K {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {t x : G} (h : burnsideC56_S7 H M₀ TH R K₁ t x) :
    blockU K₁ ⊔ blockU (conjByElt t K₁) ≤ oTwoUpper H := by
  rw [h.two.oTwoUpper_eq]
  exact sup_le_sup (burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_self TH K₁))
    (burnsideC56_b_U_le_K h.two.set (burnsideC56_b_mem_conj h.two.ht))

theorem burnsideC56_S7.sc {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
    (h : burnsideC56_S7 H M₀ TH R K₁ t x)
    (hsc : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ r ∈ R ⊓ Subgroup.normalizer (K : Set G),
      (∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ Subgroup.centralizer (blockU K : Set G)) →
      ∃ s ∈ baum R, s⁻¹ * r ∈ Subgroup.centralizer (blockU K : Set G)) :
    ∀ r ∈ R, (∀ b ∈ baum R, ⁅r, b⁆ ∈ pCoreOf 2 (oTwoUpper H ⊔ R)) →
      r ∈ baum R ⊔ pCoreOf 2 (oTwoUpper H ⊔ R) := by
  intro r hr hcomm
  have hset₁ := h.two.set
  have hset₂ := h.two.set₂
  have hrTH : r ∈ TH := hset₁.hyp1.R_le hr
  have hSR : baum R ≤ R := C1GN.baum_le R
  have hcU : ∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ Subgroup.centralizer (blockU K₁ : Set G) ⊓
      Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) := by
    intro b hb
    have h1 := hcomm b hb
    rw [← h.core_P_eq_CRU, commutatorElement_def] at h1
    have h2 := h1.2
    rwa [burnsideC56_b_centralizer_sup] at h2
  have hrN : r ∈ Subgroup.normalizer (K₁ : Set G) := by
    by_contra hrN
    have hrN' : r⁻¹ ∉ Subgroup.normalizer (K₁ : Set G) := fun h' => hrN (inv_inv r ▸ inv_mem h')
    have hconj : conjByElt r⁻¹ K₁ = conjByElt t K₁ := h.two.conj_eq_of_not_mem (inv_mem hrTH) hrN'
    have hU : conjByElt r⁻¹ (blockU K₁) = blockU (conjByElt t K₁) := by
      rw [← hconj, C116Two.blockU_conjByElt]
    obtain ⟨u, hu, v, hv, huv⟩ :
        ∃ u ∈ blockU K₁, ∃ v ∈ conjSubgroup (blockU K₁) x, u * v ≠ v * u := by
      by_contra hcon
      push Not at hcon
      apply h.hx.2.2
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcon u hu v hv).symm
    have hvS : v ∈ baum R :=
      burnsideC56_b_conj_U_le_S h.h116 hset₁ (burnsideC56_b_mem_self TH K₁) h.hx.1 hv
    have h1 : r⁻¹ * u * r ∈ blockU (conjByElt t K₁) := by
      rw [← hU, mem_conjByElt, inv_inv]
      have e : r * (r⁻¹ * u * r) * r⁻¹ = u := by group
      rw [e]
      exact hu
    have hc1 : (r⁻¹ * u * r) * v = v * (r⁻¹ * u * r) := (h.pairX.comm_V₁_U₂ hv h1).symm
    have ha : Commute u (r * v * r⁻¹) := by
      show u * (r * v * r⁻¹) = (r * v * r⁻¹) * u
      calc u * (r * v * r⁻¹) = r * ((r⁻¹ * u * r) * v) * r⁻¹ := by group
        _ = r * (v * (r⁻¹ * u * r)) * r⁻¹ := by rw [hc1]
        _ = (r * v * r⁻¹) * u := by group
    have hc : Commute u (r * v * r⁻¹ * v⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hcU v hvS).1 u hu
    have hv' : Commute u v⁻¹ := by
      have e : v⁻¹ = (r * v * r⁻¹)⁻¹ * (r * v * r⁻¹ * v⁻¹) := by group
      rw [e]
      exact ha.inv_right.mul_right hc
    exact huv (Commute.inv_right_iff.mp hv')
  have hrN₂ : r ∈ Subgroup.normalizer (conjByElt t K₁ : Set G) := h.two.mem_normalizer₂ hrTH hrN
  obtain ⟨s₁, hs₁, hc₁⟩ := hsc K₁ hset₁ r ⟨hr, hrN⟩ fun b hb => (hcU b hb).1
  obtain ⟨s₂, hs₂, hc₂⟩ := hsc (conjByElt t K₁) hset₂ r ⟨hr, hrN₂⟩ fun b hb => (hcU b hb).2
  obtain ⟨-, -, hQ₁⟩ := burnsideC56_b_c54 h.h116 hset₁ (burnsideC56_b_mem_self TH K₁)
  obtain ⟨-, -, hQ₂⟩ := burnsideC56_b_c54 h.h116 hset₂ (burnsideC56_b_mem_self TH (conjByElt t K₁))
  have hs₁' : s₁ ∈ (baum R : Set G) := hs₁
  rw [h.pairX.p2₁.1] at hs₁'
  obtain ⟨v₁, hv₁, q₁, hq₁, rfl⟩ := Set.mem_mul.mp hs₁'
  have hs₂' : s₂ ∈ (baum R : Set G) := hs₂
  rw [h.pairX.p2₂.1] at hs₂'
  obtain ⟨v₂, hv₂, q₂, hq₂, rfl⟩ := Set.mem_mul.mp hs₂'
  have hq₁C : q₁ ∈ Subgroup.centralizer (blockU K₁ : Set G) := by
    have hq : q₁ ∈ pCoreOf 2 (K₁ ⊔ baum R) := hq₁
    rw [hQ₁] at hq
    exact hq.2
  have hq₂C : q₂ ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) := by
    have hq : q₂ ∈ pCoreOf 2 (conjByElt t K₁ ⊔ baum R) := hq₂
    rw [hQ₂] at hq
    exact hq.2
  have hw₁ : v₁⁻¹ * r ∈ Subgroup.centralizer (blockU K₁ : Set G) := by
    have e : v₁⁻¹ * r = q₁ * ((v₁ * q₁)⁻¹ * r) := by group
    rw [e]
    exact mul_mem hq₁C hc₁
  have hw₂ : v₂⁻¹ * r ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) := by
    have e : v₂⁻¹ * r = q₂ * ((v₂ * q₂)⁻¹ * r) := by group
    rw [e]
    exact mul_mem hq₂C hc₂
  have hv₁S : v₁ ∈ baum R :=
    burnsideC56_b_conj_U_le_S h.h116 hset₁ (burnsideC56_b_mem_self TH K₁) h.hx.1 hv₁
  have hv₂S : v₂ ∈ baum R :=
    burnsideC56_b_conj_U_le_S h.h116 hset₁ (burnsideC56_b_mem_conj h.two.ht) h.hx.1 hv₂
  have hv₂C : v₂⁻¹ ∈ Subgroup.centralizer (blockU K₁ : Set G) :=
    inv_mem (Subgroup.mem_centralizer_iff.mpr fun u hu => h.pairX.comm_U₁_V₂ hu hv₂)
  have hv₁C : v₁⁻¹ ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) :=
    inv_mem (Subgroup.mem_centralizer_iff.mpr fun u hu => (h.pairX.comm_V₁_U₂ hv₁ hu).symm)
  have hcomm₁₂ : v₁ * v₂ = v₂ * v₁ := h.pairX.comm_V₁_V₂ hv₁ hv₂
  have hP : (v₁ * v₂)⁻¹ * r ∈ pCoreOf 2 (oTwoUpper H ⊔ R) := by
    rw [← h.core_P_eq_CRU, burnsideC56_b_centralizer_sup]
    have hR' : (v₁ * v₂)⁻¹ * r ∈ R := mul_mem (inv_mem (mul_mem (hSR hv₁S) (hSR hv₂S))) hr
    have hC₁ : (v₁ * v₂)⁻¹ * r ∈ Subgroup.centralizer (blockU K₁ : Set G) := by
      have e : (v₁ * v₂)⁻¹ * r = v₂⁻¹ * (v₁⁻¹ * r) := by group
      rw [e]
      exact mul_mem hv₂C hw₁
    have hC₂ : (v₁ * v₂)⁻¹ * r ∈ Subgroup.centralizer (blockU (conjByElt t K₁) : Set G) := by
      have e : (v₁ * v₂)⁻¹ * r = v₁⁻¹ * (v₂⁻¹ * r) := by
        rw [hcomm₁₂]; group
      rw [e]
      exact mul_mem hv₁C hw₂
    exact Subgroup.mem_inf.mpr ⟨hR', Subgroup.mem_inf.mpr ⟨hC₁, hC₂⟩⟩
  have e : r = (v₁ * v₂) * ((v₁ * v₂)⁻¹ * r) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem hv₁S hv₂S)) (Subgroup.mem_sup_right hP)

theorem burnsideC56_S7.P_eq {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
    (h : burnsideC56_S7 H M₀ TH R K₁ t x)
    (hsc : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ r ∈ R ⊓ Subgroup.normalizer (K : Set G),
      (∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ Subgroup.centralizer (blockU K : Set G)) →
      ∃ s ∈ baum R, s⁻¹ * r ∈ Subgroup.centralizer (blockU K : Set G))
    (hA₀ : IsMaxElemAbelian R ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)))) :
    pCoreOf 2 (oTwoUpper H ⊔ R) = (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)) := by
  have hyp1 := h.two.set.hyp1
  have hSR : baum R ≤ R := C1GN.baum_le R
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := hyp1.R_norm h.hx.1
  have hxS : x ∈ Subgroup.normalizer (baum R : Set G) := normalizer_le_normalizer_baum R hxR
  have hPeq := h.core_P_eq_CRU
  have hUe := h.core_U_elem
  have hUR : blockU K₁ ⊔ blockU (conjByElt t K₁) ≤ R := h.core_U_le_S.trans hSR
  have hDR : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤ R := inf_le_left.trans hSR
  have hPR : pCoreOf 2 (oTwoUpper H ⊔ R) ≤ R := by
    rw [← hPeq]
    exact inf_le_left
  have hPU : ∀ p ∈ pCoreOf 2 (oTwoUpper H ⊔ R), ∀ u ∈ blockU K₁ ⊔ blockU (conjByElt t K₁),
      u * p = p * u := by
    intro p hp u hu
    rw [← hPeq] at hp
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hp).2 u hu
  have hUP : blockU K₁ ⊔ blockU (conjByElt t K₁) ≤ pCoreOf 2 (oTwoUpper H ⊔ R) := by
    rw [← hPeq]
    exact le_inf hUR fun u hu => Subgroup.mem_centralizer_iff.mpr fun w hw => hUe.1 w hw u hu
  have hDP : baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤
      pCoreOf 2 (oTwoUpper H ⊔ R) := by
    rw [← hPeq]
    exact le_inf hDR h.two.D_le_CU
  have hNP : oTwoUpper H ⊔ R ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H ⊔ R) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hRP : R ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H ⊔ R) : Set G) :=
    le_sup_right.trans hNP
  have hSC := h.sc hsc
  have hPy : ∀ y ∈ Subgroup.normalizer (R : Set G),
      conjSubgroup (pCoreOf 2 (oTwoUpper H ⊔ R)) y = R ⊓ Subgroup.centralizer
        ((conjSubgroup (blockU K₁) y ⊔ conjSubgroup (blockU (conjByElt t K₁)) y : Subgroup G) :
          Set G) := by
    intro y hy
    rw [← hPeq, C5.conjSubgroup_inf, C5.conjSubgroup_eq_self hy, C5.conjSubgroup_centralizer,
      C5.conjSubgroup_sup]
  have h1 : pCoreOf 2 (oTwoUpper H ⊔ R) ≤ (blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
      (pCoreOf 2 (oTwoUpper H ⊔ R) ⊓ conjSubgroup (pCoreOf 2 (oTwoUpper H ⊔ R)) x) := by
    refine burnsideC56_core_P_le hxR hxS (fun s hs => h.pairX.decomp' hs) ?_ ?_ hPR hSR hRP
      hUP hPU hSC
    · rw [← C5.conjSubgroup_sup]
      exact C5.conjSubgroup_mono hUP x
    · intro d hd
      rw [hPy x hxR]
      exact Subgroup.mem_inf.mpr ⟨hDR hd, h.pairX.D_le_CV hd⟩
  have h2 : pCoreOf 2 (oTwoUpper H ⊔ R) ≤ (blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
      (pCoreOf 2 (oTwoUpper H ⊔ R) ⊓ conjSubgroup (pCoreOf 2 (oTwoUpper H ⊔ R)) x⁻¹) := by
    refine burnsideC56_core_P_le (inv_mem hxR) (inv_mem hxS) (fun s hs => h.pairX'.decomp' hs)
      ?_ ?_ hPR hSR hRP hUP hPU hSC
    · rw [← C5.conjSubgroup_sup]
      exact C5.conjSubgroup_mono hUP x⁻¹
    · intro d hd
      rw [hPy x⁻¹ (inv_mem hxR)]
      exact Subgroup.mem_inf.mpr ⟨hDR hd, h.pairX'.D_le_CV hd⟩
  have hxsq := burnsideC56_core_sqSub_conj hUe.2 hUP hPU h1 h2
  have hTHP : TH ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H ⊔ R) : Set G) := fun a ha =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H ⊔ R)
      (C1.mem_normalizer_sup (le_normalizer_oTwoUpper H (hyp1.sylow.1 ha))
        (hyp1.R_norm (hyp1.TH_le ha)))
  have hsq : C5.sqSub (pCoreOf 2 (oTwoUpper H ⊔ R)) = ⊥ := by
    refine h.noCommon (C5.sqSub_le_self.trans hPR) (fun a ha => ?_) (fun k hk => ?_)
      (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hxsq)
    · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp
        (C5.conjSubgroup_sqSub_of_mem_normalizer (hTHP ha))
    · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp
        (C5.conjSubgroup_sqSub_of_mem_normalizer (hNP (Subgroup.mem_sup_left hk)))
  have hPab := C5.comm_of_sq_eq_one (C5.sqSub_eq_bot_iff.mp hsq)
  have hA₀P : (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)) ≤ pCoreOf 2 (oTwoUpper H ⊔ R) := sup_le hDP hUP
  have hOmega : omegaOneCenterOf (thompsonJ R) ≤
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        (blockU K₁ ⊔ blockU (conjByElt t K₁)) := by
    rw [(omegaOne_centralizer_thompsonJ R).2]
    exact iInf₂_le _ hA₀
  have hPS : pCoreOf 2 (oTwoUpper H ⊔ R) ≤ baum R := fun p hp =>
    ⟨hPR hp, Subgroup.mem_centralizer_iff.mpr fun z hz => hPab z (hA₀P (hOmega hz)) p hp⟩
  refine le_antisymm (fun p hp => ?_) hA₀P
  have hpC : p ∈ baum R ⊓ Subgroup.centralizer
      ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hPS hp, Subgroup.mem_centralizer_iff.mpr fun u hu => hPU p hp u hu⟩
  rw [h.pairX.CSU] at hpC
  have hle : (blockU K₁ ⊔ blockU (conjByElt t K₁)) ⊔
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ≤
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
        (blockU K₁ ⊔ blockU (conjByElt t K₁)) := sup_le le_sup_right le_sup_left
  exact hle hpC

theorem burnsideC56_S7.CR_eq {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
    (h : burnsideC56_S7 H M₀ TH R K₁ t x)
    (hP : pCoreOf 2 (oTwoUpper H ⊔ R) = (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁))) :
    baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) =
      R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
  refine le_antisymm (inf_le_inf_right _ (C1GN.baum_le R)) fun c hc => ?_
  obtain ⟨hcR, hcK⟩ := Subgroup.mem_inf.mp hc
  have hcU : c ∈ R ⊓ Subgroup.centralizer
      ((blockU K₁ ⊔ blockU (conjByElt t K₁) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hcR, Subgroup.centralizer_le (SetLike.coe_mono h.core_U_le_K) hcK⟩
  rw [h.core_P_eq_CRU, hP] at hcU
  exact Subgroup.mem_inf.mpr ⟨sup_le inf_le_left h.core_U_le_S hcU, hcK⟩

theorem burnsideC56_S7.U_eq_pCore {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    {t x : G} (h : burnsideC56_S7 H M₀ TH R K₁ t x)
    (hP : pCoreOf 2 (oTwoUpper H ⊔ R) = (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
      (blockU K₁ ⊔ blockU (conjByElt t K₁)))
    (hG₁ : pCoreOf 2 K₁ ≤ blockU K₁)
    (hG₂ : pCoreOf 2 (conjByElt t K₁) ≤ blockU (conjByElt t K₁)) :
    blockU K₁ ⊔ blockU (conjByElt t K₁) = pCoreOf 2 (oTwoUpper H) := by
  have hset₁ := h.two.set
  have hyp1 := hset₁.hyp1
  have hshort₁ : IsShort2 K₁ := hset₁.config.chi0.1.1
  have hshort₂ : IsShort2 (conjByElt t K₁) :=
    (burnsideC5h_c54_isBlock2 hset₁ (burnsideC56_b_mem_conj h.two.ht)).1
  refine le_antisymm (by rw [← h.two.iSup_eq]; exact burnsideC56_b_U_le_pCoreK hset₁)
    fun p hp => ?_
  have hKRN : oTwoUpper H ⊔ R ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) := by
    refine sup_le (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
      fun r hr => ?_
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)
      (le_normalizer_oTwoUpper H (hyp1.sylow.1 (hyp1.R_le hr)))
  have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (oTwoUpper H ⊔ R) :=
    C1.le_pCoreOf_of_normalized
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans le_sup_left) hKRN
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  have hpK : p ∈ oTwoUpper H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hp
  have hpP := hle hp
  rw [hP] at hpP
  obtain ⟨d, hd, u, hu, rfl⟩ := C5.mem_sup_of_commute
    (fun d hd u hu => (Subgroup.mem_centralizer_iff.mp (h.two.D_le_CU hd) u hu).symm) hpP
  have hdK : d ∈ oTwoUpper H := by
    have e : d = (d * u) * u⁻¹ := by group
    rw [e]
    exact mul_mem hpK (inv_mem (h.core_U_le_K hu))
  have hdC : d ∈ Subgroup.centralizer (oTwoUpper H : Set G) := (Subgroup.mem_inf.mp hd).2
  rw [h.two.oTwoUpper_eq] at hdK hdC
  rw [burnsideC56_b_centralizer_sup] at hdC
  obtain ⟨hdC₁, hdC₂⟩ := Subgroup.mem_inf.mp hdC
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ :=
    C5.mem_sup_of_commute (fun a ha b hb => h.two.comm ha hb) hdK
  have hk₁C : k₁ ∈ Subgroup.centralizer (K₁ : Set G) := by
    have e : k₁ = (k₁ * k₂) * k₂⁻¹ := by group
    rw [e]
    exact mul_mem hdC₁ (inv_mem (h.two.K₂_le_centralizer hk₂))
  have hk₂C : k₂ ∈ Subgroup.centralizer (conjByElt t K₁ : Set G) := by
    have e : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
    rw [e]
    exact mul_mem (inv_mem (h.two.K₁_le_centralizer hk₁)) hdC₂
  have hk₁U : k₁ ∈ blockU K₁ := hG₁ (hshort₁.2.1 (Subgroup.mem_inf.mpr ⟨hk₁,
    Subgroup.centralizer_le
      (SetLike.coe_mono (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K₁)) hk₁C⟩))
  have hk₂U : k₂ ∈ blockU (conjByElt t K₁) := hG₂ (hshort₂.2.1 (Subgroup.mem_inf.mpr ⟨hk₂,
    Subgroup.centralizer_le
      (SetLike.coe_mono (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _)) hk₂C⟩))
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hk₁U) (Subgroup.mem_sup_right hk₂U)) hu

end PartBurnsideC56Core

section PartBurnsideC56Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise commutatorElement

theorem burnsideC56_sylow_step {G : Type} [Group G] [Finite G] {M₀ TH T₁ M₁ N₁ : Subgroup G}
    (hsyl : IsSylowTwoOf TH M₀) (hT₁TH : T₁ ≤ TH) (hidxT : T₁.relIndex TH = 2)
    (hM₁M₀ : M₁ ≤ M₀) (hN₁M₁ : N₁ ≤ M₁) (hidxN : N₁.relIndex M₁ = 2) (hT₁N₁ : T₁ ≤ N₁) :
    ∃ x₀ ∈ M₁, x₀ ∉ N₁ ∧ x₀ ∈ Subgroup.normalizer (T₁ : Set G) ∧ x₀ * x₀ ∈ T₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁M₁ : T₁ ≤ M₁ := hT₁N₁.trans hN₁M₁
  have hT₁2 : IsPGroup 2 T₁ := hsyl.2.1.to_le hT₁TH
  have hT₁' : IsPGroup 2 (T₁.subgroupOf M₁) :=
    hT₁2.of_equiv (Subgroup.subgroupOfEquivOfLe hT₁M₁).symm
  obtain ⟨P, hP⟩ := hT₁'.exists_le_sylow
  set T₀ : Subgroup G := (P : Subgroup M₁).map M₁.subtype with hT₀
  have hT₀M₁ : T₀ ≤ M₁ := Subgroup.map_subtype_le _
  have hT₁T₀ : T₁ ≤ T₀ := fun t ht =>
    ⟨⟨t, hT₁M₁ ht⟩, hP (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hT₀2 : IsPGroup 2 T₀ := P.isPGroup'.map _
  have hT₀idx : ¬ 2 ∣ T₀.relIndex M₁ := by
    have h : T₀.subgroupOf M₁ = (P : Subgroup M₁) :=
      Subgroup.comap_map_eq_self_of_injective M₁.subtype_injective _
    show ¬ 2 ∣ (T₀.subgroupOf M₁).index
    rw [h]
    exact P.not_dvd_index
  have hcard : Nat.card T₀ ≤ Nat.card TH := by
    obtain ⟨a, ha⟩ := hT₀2.exists_card_eq
    have h1 : Nat.card T₀ ∣ Nat.card M₀ := Subgroup.card_dvd_of_le (hT₀M₁.trans hM₁M₀)
    rw [C5.card_eq_card_mul_relIndex hsyl.1, ha] at h1
    have hcop : Nat.Coprime (2 ^ a) (TH.relIndex M₀) :=
      (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hsyl.2.2).symm
    rw [ha]
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right h1)
  have hT₀N₁ : ¬ T₀ ≤ N₁ := by
    intro h
    apply hT₀idx
    rw [← Subgroup.relIndex_mul_relIndex T₀ N₁ M₁ h hN₁M₁, hidxN]
    exact Dvd.intro_left _ rfl
  obtain ⟨x₀, hx₀T₀, hx₀N₁⟩ := IsConcreteLE.not_le_iff_exists.mp hT₀N₁
  have hidx₀ : N₁.relIndex T₀ = 2 := by
    have hle : N₁.relIndex T₀ ≤ N₁.relIndex M₁ :=
      Subgroup.relIndex_le_of_le_right hT₀M₁ (by rw [hidxN]; exact two_ne_zero)
    have hne1 : N₁.relIndex T₀ ≠ 1 := fun h => hT₀N₁ (Subgroup.relIndex_eq_one.mp h)
    have hne0 : N₁.relIndex T₀ ≠ 0 := Subgroup.index_ne_zero_of_finite (H := N₁.subgroupOf T₀)
    omega
  have hcardInf : Nat.card T₀ = Nat.card (T₀ ⊓ N₁ : Subgroup G) * 2 := by
    have := C5.card_eq_card_mul_relIndex (inf_le_left : T₀ ⊓ N₁ ≤ T₀)
    rwa [Subgroup.inf_relIndex_left, hidx₀] at this
  have hcardTH : Nat.card TH = Nat.card T₁ * 2 := by
    have := C5.card_eq_card_mul_relIndex hT₁TH
    rwa [hidxT] at this
  have hT₁eq : T₁ = T₀ ⊓ N₁ :=
    Subgroup.eq_of_le_of_card_ge (le_inf hT₁T₀ hT₁N₁) (by omega)
  have hidxT₀ : T₁.relIndex T₀ = 2 := by
    rw [hT₁eq, Subgroup.inf_relIndex_left]
    exact hidx₀
  refine ⟨x₀, hT₀M₁ hx₀T₀, hx₀N₁, burnsideC5x_TH_conj_mem hT₁T₀ hidxT₀ hx₀T₀, ?_⟩
  have := Subgroup.mul_self_mem_of_index_two (H := T₁.subgroupOf T₀) hidxT₀ ⟨x₀, hx₀T₀⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem burnsideC56_T1_le_normalizer {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {t : G} (ht : t ∈ TH)
    (htU : t ∈ Subgroup.normalizer (blockU K₁ : Set G)) :
    t ∈ Subgroup.normalizer (K₁ : Set G) := by
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  rw [C2Eleven.mem_normalizer_iff_conjByElt]
  by_contra hne
  have hne' : conjByElt t K₁ ≠ conjByElt 1 K₁ := by
    rwa [burnsideC5h_c54_conjByElt_one]
  have hc := hset.config.commute t ht 1 TH.one_mem hne'
  rw [burnsideC5h_c54_conjByElt_one] at hc
  have hUt : blockU K₁ ≤ conjByElt t K₁ := by
    intro u hu
    rw [mem_conjByElt]
    have h1 : t⁻¹ * u * t⁻¹⁻¹ ∈ blockU K₁ :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem htU) u).mp hu
    rw [inv_inv] at h1
    exact hUK h1
  have hZ : blockU K₁ ≤ blockZ K₁ := le_inf le_rfl (hUt.trans hc)
  exact lt_irrefl _ (lt_of_lt_of_le hshort.2.2.2.2.1 hZ)

theorem burnsideC56_relIndex_normalizer_K {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hs2 : ∃ t ∈ TH, conjByElt t K₁ ≠ K₁) :
    (TH ⊓ Subgroup.normalizer (K₁ : Set G)).relIndex TH = 2 := by
  obtain ⟨t₀, ht₀, hne⟩ := hs2
  have hconj : ∀ g : G, conjSubgroup K₁ g = conjByElt g⁻¹ K₁ := fun g => rfl
  refine burnsideC5x_relIndex_two (x := t₀⁻¹) (inv_mem ht₀) ?_ ?_
  · rw [hconj, inv_inv]
    exact hne
  · intro m hm
    rw [hconj, hconj, inv_inv]
    rcases hset.config.card_le m⁻¹ (inv_mem hm) t₀ ht₀ 1 TH.one_mem with h | h | h
    · exact Or.inr h
    · exact Or.inl (h.trans (burnsideC5h_c54_conjByElt_one K₁))
    · exact absurd (h.trans (burnsideC5h_c54_conjByElt_one K₁)) hne

theorem burnsideC56_mem_N1 {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G}
    (hset : SetC53 H M₀ TH R K₁) {t : G} (ht : t ∈ TH)
    (htK : t ∈ Subgroup.normalizer (K₁ : Set G)) :
    t ∈ Subgroup.normalizer (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) : Set G) ∧
      t ∈ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) := by
  have htB : t ∈ Subgroup.normalizer (baum R : Set G) :=
    normalizer_le_normalizer_baum R (hset.hyp1.R_norm (hset.hyp1.TH_le ht))
  exact ⟨CFSG.QuasithinUnique.DoubleA3.mem_normalizer_frattiniOf
      (C5.mem_normalizer_inf htB (C5.mem_normalizer_centralizer htK)),
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K₁ ⊔ baum R)
      (C1.mem_normalizer_sup htK htB)⟩

theorem burnsideC56_comm_mem {G : Type} [Group G] {S U V Q D Y : Subgroup G}
    (hS : (S : Set G) = (V : Set G) * (Q : Set G)) (hQ : Q = U ⊔ D)
    (hUD : ∀ u ∈ U, ∀ d ∈ D, u * d = d * u) (hDV : ∀ d ∈ D, ∀ v ∈ V, v * d = d * v)
    (hDS : D ≤ S) (hDY : ∀ d ∈ D, ∀ d' ∈ D, d * d' * d⁻¹ * d'⁻¹ ∈ Y)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) {d s : G} (hd : d ∈ D) (hs : s ∈ S) :
    d * s * d⁻¹ * s⁻¹ ∈ Y := by
  have hs' : s ∈ (S : Set G) := hs
  rw [hS] at hs'
  obtain ⟨v, hv, q, hq, rfl⟩ := Set.mem_mul.mp hs'
  rw [hQ] at hq
  obtain ⟨u, hu, d', hd', rfl⟩ := C5.mem_sup_of_commute hUD hq
  have hdv : Commute d v := (hDV d hd v hv).symm
  have hdu : Commute d u := (hUD u hu d hd).symm
  have hw : d * (v * u) = v * u * d := (hdv.mul_right hdu).eq
  have hvu : v * u ∈ S := by
    have e : v * u = v * (u * d') * d'⁻¹ := by group
    rw [e]
    exact S.mul_mem hs (S.inv_mem (hDS hd'))
  have e : d * (v * (u * d')) * d⁻¹ * (v * (u * d'))⁻¹ =
      (v * u) * (d * d' * d⁻¹ * d'⁻¹) * (v * u)⁻¹ := by
    calc d * (v * (u * d')) * d⁻¹ * (v * (u * d'))⁻¹
        = d * (v * u) * d' * d⁻¹ * d'⁻¹ * (v * u)⁻¹ := by group
      _ = v * u * d * d' * d⁻¹ * d'⁻¹ * (v * u)⁻¹ := by rw [hw]
      _ = (v * u) * (d * d' * d⁻¹ * d'⁻¹) * (v * u)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hSY hvu) _).mp (hDY d hd d' hd')

theorem burnsideC56_conj_D_le {G : Type} [Group G] {S U Q D Y W : Subgroup G} {g : G}
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hUS : U ≤ S) (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hDS : D ≤ S) (hYW : Y ≤ W)
    (hDY : ∀ d ∈ D, ∀ s ∈ S, d * s * d⁻¹ * s⁻¹ ∈ Y)
    (hZ : ∀ e ∈ S, (∀ u ∈ U, ⁅u, e⁆ ∈ U ⊓ W) → e ∈ Q) :
    conjSubgroup D g ≤ Q := by
  intro e he
  rw [CFSG.Quasithin.mem_conjSubgroup_iff] at he
  have heq : g⁻¹ * (g * e * g⁻¹) * g = e := by group
  have heS : e ∈ S := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hgS) _).mp (hDS he)
    rw [inv_inv, heq] at h1
    exact h1
  refine hZ e heS fun u hu => ⟨?_, ?_⟩
  · have h1 : e * u⁻¹ * e⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hSU heS) u⁻¹).mp (inv_mem hu)
    have e1 : ⁅u, e⁆ = u * (e * u⁻¹ * e⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact U.mul_mem hu h1
  · apply hYW
    have hs : g * u * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hgS u).mp (hUS hu)
    have h1 := hDY _ he _ hs
    have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hgY) _).mp h1
    rw [inv_inv] at h2
    have e2 : ⁅u, e⁆ = (g⁻¹ * ((g * e * g⁻¹) * (g * u * g⁻¹) * (g * e * g⁻¹)⁻¹ *
        (g * u * g⁻¹)⁻¹) * g)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e2]
    exact Y.inv_mem h2

theorem burnsideC56_comm_ne_bot {G : Type} [Group G] [Finite G] {S U Q D : Subgroup G} {g : G}
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (hUS : U ≤ S)
    (hQ : Q = S ⊓ Subgroup.centralizer (U : Set G)) (hQUD : Q = U ⊔ D)
    (hDQ : conjSubgroup D g ≤ Q) (hgQ : g ∉ Subgroup.normalizer (Q : Set G)) :
    ⁅U, conjSubgroup U g⁆ ≠ ⊥ := by
  intro hbot
  apply hgQ
  have hUg : conjSubgroup U g ≤ Q := by
    rw [hQ]
    refine le_inf ?_ ?_
    · have h1 := C5.conjSubgroup_mono hUS g
      rwa [C5.conjSubgroup_eq_self hgS] at h1
    · rw [Subgroup.commutator_comm] at hbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hle : conjSubgroup Q g ≤ Q := by
    calc conjSubgroup Q g = conjSubgroup (U ⊔ D) g := by rw [← hQUD]
      _ = conjSubgroup U g ⊔ conjSubgroup D g := C5.conjSubgroup_sup U D g
      _ ≤ Q := sup_le hUg hDQ
  have heq : conjSubgroup Q g = Q :=
    Subgroup.eq_of_le_of_card_ge hle (C5.card_conjSubgroup Q g).ge
  exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp heq

theorem burnsideC56_not_le_pCore {G : Type} [Group G] [Finite G] {H R K U V W : Subgroup G}
    (hKRH : K ⊔ R ≤ H) (hVR : V ≤ R)
    (hCRU : R ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 (K ⊔ R))
    (hUW : U ≤ W) (hne : ⁅U, V⁆ ≠ ⊥) : ¬ V ≤ pCoreOf 2 H := by
  intro hle
  apply hne
  have hX : pCoreOf 2 H ⊓ (K ⊔ R) ≤ pCoreOf 2 (K ⊔ R) :=
    C1.le_pCoreOf_of_normalized inf_le_right
      (fun g hg => C5.mem_normalizer_inf
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (hKRH hg))
        (Subgroup.le_normalizer hg))
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have hVC : V ≤ Subgroup.centralizer (U : Set G) := by
    have h1 : V ≤ pCoreOf 2 (K ⊔ R) := (le_inf hle (hVR.trans le_sup_right)).trans hX
    rw [← hCRU] at h1
    exact (h1.trans inf_le_right).trans (Subgroup.centralizer_le hUW)
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVC

theorem burnsideC56_six_core {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hs2 : ∃ t ∈ TH, conjByElt t K₁ ≠ K₁) (hsyl : IsSylowTwoOf TH M₀)
    (hUQ : blockU K₁ ≤ pCoreOf 2 (K₁ ⊔ baum R))
    (hQeq : pCoreOf 2 (K₁ ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU K₁ : Set G))
    (hSN : baum R ≤ Subgroup.normalizer (K₁ : Set G))
    (hCRU : R ⊓ Subgroup.centralizer
        ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) =
      pCoreOf 2 (oTwoUpper H ⊔ R))
    (h1 : burnsideC5x_P1 R K₁ x) (h2 : burnsideC5x_P2 R K₁ x) (h4 : burnsideC5x_P4 R K₁ x)
    (hZ : ∀ e ∈ baum R, (∀ u ∈ blockU K₁,
        ⁅u, e⁆ ∈ blockU K₁ ⊓ Subgroup.centralizer (K₁ : Set G)) → e ∈ pCoreOf 2 (K₁ ⊔ baum R))
    (hΓ : ∀ m ∈ M₀, conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) m =
        CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) →
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = pCoreOf 2 (K₁ ⊔ baum R) ∨
        conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x) :
    ∃ x' : G, GoodX H M₀ K₁ x' ∧
      x' ∈ Subgroup.normalizer ((TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
        Set G) ∧ x' ^ 2 ∈ TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) := by
  have hyp1 := hset.hyp1
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hR2 : IsPGroup 2 R := hyp1.sylow.2.1.to_le hyp1.R_le
  have hSR : baum R ≤ R := C1GN.baum_le R
  have hQS : pCoreOf 2 (K₁ ⊔ baum R) ≤ baum R := hQeq ▸ inf_le_left
  have hUS : blockU K₁ ≤ baum R := hUQ.trans hQS
  have hDS : baum R ⊓ Subgroup.centralizer (K₁ : Set G) ≤ baum R := inf_le_left
  have hD2 : IsPGroup 2 ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G)) :=
    hR2.to_le (hDS.trans hSR)
  have hSU : baum R ≤ Subgroup.normalizer (blockU K₁ : Set G) := fun s hs =>
    C1.mem_normalizer_blockU (hSN hs)
  have hSY : baum R ≤ Subgroup.normalizer (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) : Set G) := fun s hs =>
    CFSG.QuasithinUnique.DoubleA3.mem_normalizer_frattiniOf
      (C5.mem_normalizer_inf (Subgroup.le_normalizer hs) (C5.mem_normalizer_centralizer (hSN hs)))
  have hYD : CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) ≤
      baum R ⊓ Subgroup.centralizer (K₁ : Set G) := Subgroup.map_subtype_le _
  have hxY : x ∈ Subgroup.normalizer (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) : Set G) :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h4
  have hne : conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x ≠ pCoreOf 2 (K₁ ⊔ baum R) := by
    intro heq
    apply (burnsideC5x_not_le_Q hQeq hx.2.2).1
    have h := C5.conjSubgroup_mono hUQ x
    rwa [heq] at h
  have hidxN := burnsideC5x_relIndex_two (M₁ := M₀ ⊓ Subgroup.normalizer
      (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) : Set G)) ⟨hx.1, hxY⟩ hne
    (fun m hm => hΓ m hm.1 (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hm.2))
  have hT₁K : TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) :=
    fun t ht => burnsideC56_T1_le_normalizer hset ht.1 ht.2
  have hT₁eq : TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) =
      TH ⊓ Subgroup.normalizer (K₁ : Set G) :=
    le_antisymm (le_inf inf_le_left hT₁K) fun t ht => ⟨ht.1, C1.mem_normalizer_blockU ht.2⟩
  have hidxT : (TH ⊓ Subgroup.normalizer (blockU K₁ : Set G)).relIndex TH = 2 := by
    rw [hT₁eq]
    exact burnsideC56_relIndex_normalizer_K hset hs2
  have hT₁N₁ : TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) ≤
      (M₀ ⊓ Subgroup.normalizer (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) : Set G)) ⊓
        Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) := by
    intro t ht
    obtain ⟨hY, hQ⟩ := burnsideC56_mem_N1 hset ht.1 (hT₁K ht)
    exact ⟨⟨hyp1.TH_le ht.1, hY⟩, hQ⟩
  obtain ⟨x₀, hx₀M₁, hx₀N₁, hx₀T, hx₀sq⟩ :=
    burnsideC56_sylow_step hsyl inf_le_left hidxT inf_le_left inf_le_left hidxN hT₁N₁
  have hx₀M₀ : x₀ ∈ M₀ := hx₀M₁.1
  have hx₀S : x₀ ∈ Subgroup.normalizer (baum R : Set G) :=
    normalizer_le_normalizer_baum R (hyp1.R_norm hx₀M₀)
  have hx₀Q : x₀ ∉ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ baum R) : Set G) :=
    fun h => hx₀N₁ ⟨hx₀M₁, h⟩
  have hcomm : ∀ d ∈ baum R ⊓ Subgroup.centralizer (K₁ : Set G), ∀ s ∈ baum R,
      d * s * d⁻¹ * s⁻¹ ∈ CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) := by
    intro d hd s hs
    refine burnsideC56_comm_mem h2.1 h1.1
      (fun u hu a ha => Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu))
      (fun a ha v hv => Subgroup.mem_centralizer_iff.mp (h1.2 ha).2 v hv) hDS
      (fun a ha b hb => ?_) hSY hd hs
    have h := CFSG.QuasithinUnique.DoubleA3.commutator_le_frattiniOf hD2
      (Subgroup.commutator_mem_commutator ha hb)
    rwa [commutatorElement_def] at h
  have hDx₀ : conjSubgroup (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) x₀ ≤
      pCoreOf 2 (K₁ ⊔ baum R) :=
    burnsideC56_conj_D_le hx₀S hx₀M₁.2 hUS hSU hDS (hYD.trans inf_le_right) hcomm hZ
  have ha : ⁅blockU K₁, rconj x₀ (blockU K₁)⁆ ≠ ⊥ :=
    burnsideC56_comm_ne_bot hx₀S hUS hQeq h1.1 hDx₀ hx₀Q
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  have hVR : rconj x₀ (blockU K₁) ≤ R := by
    have h := C5.conjSubgroup_mono hUS x₀
    rw [C5.conjSubgroup_eq_self hx₀S] at h
    exact h.trans hSR
  have hb : ¬ rconj x₀ (blockU K₁) ≤ pCoreOf 2 H :=
    burnsideC56_not_le_pCore (sup_le (oTwoUpper_le H) (hyp1.R_le.trans hyp1.sylow.1)) hVR hCRU
      (le_iSup₂_of_le K₁ hK₁mem le_rfl) ha
  exact ⟨x₀, ⟨hx₀M₀, hb, ha⟩, hx₀T, by rw [pow_two]; exact hx₀sq⟩

end PartBurnsideC56Six

section PartBurnsideC56A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

section BurnsideC56A5

open CFSG.QuasithinUnique.A5.Delta5

theorem burnsideC56_relIndex_ne_zero {G : Type} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite (H := H.subgroupOf K)

theorem burnsideC56_a5_cfg_of (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ R' : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5)
    (hJ : thompsonJ R ≤ R') (hB : baum R ≤ R')
    (hR' : R' ≤ R ⊓ Subgroup.normalizer (K₁ : Set G)) (hsyl : IsSylowTwoOf R' (K₁ ⊔ R')) :
    Nonempty (burnsideC5x_A5Cfg R' K₁) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  have hyp1 := hset.hyp1
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hR2 : IsPGroup 2 R := hyp1.sylow.2.1.to_le hyp1.R_le
  have hR'R : R' ≤ R := hR'.trans inf_le_left
  have hRN : R' ≤ Subgroup.normalizer (K₁ : Set G) := hR'.trans inf_le_right
  have hJeq : thompsonJ R' = thompsonJ R := burnsideC5h_p2_thompsonJ_eq hJ hR'R
  have hbeq : baum R' = baum R := burnsideC5h_p2_baum_eq hJ hR'R hB
  have hsetting : burnsideC5h_p3_Setting K₁ R' :=
    ⟨hshort, h5, hRN, hsyl, by rw [hJeq]; exact hset.config.comm_J⟩
  obtain ⟨P⟩ := AppC.nonempty_a5pi hshort h5
  obtain ⟨P', hBP, hRP, hXP⟩ := burnsideC5x_a5_std hsetting P
  obtain ⟨⟨⟨hQUD, hUD, -⟩, -, -⟩, -, hQeq⟩ :=
    burnsideC5h_p3_a5_unconditional h116 hset K₁ hK₁mem h5
  rw [← hbeq] at hQUD hUD hQeq
  exact ⟨⟨hshort, h5, hR2.to_le hR'R, hRN, P', hBP, hRP, hXP, hQeq, hQUD, hUD⟩⟩

theorem burnsideC56_a5_cfg_inf (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5) :
    Nonempty (burnsideC5x_A5Cfg (R ⊓ Subgroup.normalizer (K₁ : Set G)) K₁) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  have hB : baum R ≤ R ⊓ Subgroup.normalizer (K₁ : Set G) :=
    le_inf (C1GN.baum_le R) (burnsideC5h_c54_one h116 hset K₁ hK₁mem)
  exact burnsideC56_a5_cfg_of h116 hset h5 ((C5.thompsonJ_le_baum' R).trans hB) hB le_rfl
    (burnsideC5h_p3_sylow hset hK₁mem)

theorem burnsideC56_baum_inf (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) :
    baum (R ⊓ Subgroup.normalizer (K₁ : Set G)) = baum R := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  exact (burnsideC5x_data h116 hset hK₁mem).2.2.2.1

theorem burnsideC56_relIndex_conj {G : Type} [Group G] {R : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (baum R : Set G)) (g : G) :
    ((baum R ⊓ Subgroup.centralizer (baum R : Set G)) ⊓
        Subgroup.centralizer ({y * g * y⁻¹} : Set G)).relIndex
      (baum R ⊓ Subgroup.centralizer (baum R : Set G)) =
    ((baum R ⊓ Subgroup.centralizer (baum R : Set G)) ⊓
        Subgroup.centralizer ({g} : Set G)).relIndex
      (baum R ⊓ Subgroup.centralizer (baum R : Set G)) := by
  set Z := baum R ⊓ Subgroup.centralizer (baum R : Set G) with hZ
  have hyZ : y⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
    inv_mem (C5.mem_normalizer_inf hy (C5.mem_normalizer_centralizer hy))
  have h1 : conjSubgroup Z y⁻¹ = Z := C5.conjSubgroup_eq_self hyZ
  have h2 : conjSubgroup (Z ⊓ Subgroup.centralizer ({g} : Set G)) y⁻¹ =
      Z ⊓ Subgroup.centralizer ({y * g * y⁻¹} : Set G) := by
    rw [C5.conjSubgroup_inf, h1]
    congr 1
    ext b
    rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, inv_inv]
    constructor
    · intro h
      calc b * (y * g * y⁻¹) = y * ((y⁻¹ * b * y) * g) * y⁻¹ := by group
        _ = y * (g * (y⁻¹ * b * y)) * y⁻¹ := by rw [h]
        _ = y * g * y⁻¹ * b := by group
    · intro h
      calc y⁻¹ * b * y * g = y⁻¹ * (b * (y * g * y⁻¹)) * y := by group
        _ = y⁻¹ * (y * g * y⁻¹ * b) * y := by rw [h]
        _ = g * (y⁻¹ * b * y) := by group
  have h3 := C5.relIndex_conjSubgroup (Z ⊓ Subgroup.centralizer ({g} : Set G)) Z y⁻¹
  rw [h1, h2] at h3
  exact h3

theorem burnsideC56_Z_le {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) :
    baum R ⊓ Subgroup.centralizer (baum R : Set G) ≤
      (blockU K ⊓ Subgroup.centralizer (baum R : Set G)) ⊔
        (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
  intro z hz
  have hzQ : z ∈ pCoreOf 2 (K ⊔ baum R) := by
    rw [C.Q_eq]
    exact ⟨hz.1, Subgroup.centralizer_le C.hUB hz.2⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := C.exists_UD hzQ
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hu, ?_⟩))
    (Subgroup.mem_sup_right hd)
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hc : s * (u * d) * s⁻¹ = u * d := by
    have := Subgroup.mem_centralizer_iff.mp hz.2 s hs
    rw [this]; group
  have h2 : (s * u * s⁻¹) * (s * d * s⁻¹) = u * d := by
    rw [← hc]; group
  have h3 := C.UD_unique (AppC.PiData.conj_mem_U (C.hBN hs) hu) hu (C.conj_mem_D hs hd) hd h2
  calc s * u = (s * u * s⁻¹) * s := by group
    _ = u * s := by rw [h3.1]

theorem burnsideC56_z0_fixed : ∀ σ ∈ Dset, pact σ z0 = z0 := by decide +kernel

theorem burnsideC56_z0_even : isEven z0 := by decide +kernel

theorem burnsideC56_z0_ne : z0 ≠ 0 := by decide +kernel

theorem burnsideC56_relIndex_le_two {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {r : G} (hrR : r ∈ R) (hrK : r ∈ K) :
    ((baum R ⊓ Subgroup.centralizer (baum R : Set G)) ⊓
        Subgroup.centralizer ({r} : Set G)).relIndex
      (baum R ⊓ Subgroup.centralizer (baum R : Set G)) ≤ 2 := by
  set Z := baum R ⊓ Subgroup.centralizer (baum R : Set G) with hZ
  set E := blockU K ⊓ Subgroup.centralizer (baum R : Set G) with hE
  set D := baum R ⊓ Subgroup.centralizer (K : Set G) with hD
  set E' := E ⊓ Subgroup.centralizer ({r} : Set G) with hE'
  obtain ⟨u₀, hu₀, hbf⟩ := C.P.bf_surj ⟨z0, (mem_evenWeight_iff z0).2 burnsideC56_z0_even⟩
  have hfix : ∀ g ∈ Subgroup.normalizer (K : Set G), C.P.pf g ∈ Dset → g * u₀ = u₀ * g := by
    intro g hg hgD
    refine (C.P.comm_iff hg hu₀).2 ?_
    rw [hbf]
    exact Subtype.ext (burnsideC56_z0_fixed _ hgD)
  have hu₀E' : u₀ ∈ E' := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
      ⟨hu₀, Subgroup.mem_centralizer_iff.2 fun s hs => hfix s (C.hBN hs) ?_⟩, ?_⟩
    · have : C.P.pf s ∈ C.P.im (baum R) := (C.P.mem_im_pf C.hBN).2 ⟨s, hs, rfl⟩
      rw [C.hB] at this
      exact (mem_Dstd _).1 (Estd_le_Dstd this)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have : C.P.pf r ∈ C.P.im R := (C.P.mem_im_pf C.RN).2 ⟨r, hrR, rfl⟩
      rw [C.hR] at this
      exact (hfix r (C.RN hrR) ((mem_Dstd _).1 this)).symm
  have hu₀1 : u₀ ≠ 1 := by
    rintro rfl
    rw [C.P.bf_one] at hbf
    exact burnsideC56_z0_ne (congrArg Subtype.val hbf).symm
  have hE'ne : E' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hu₀E'
    exact hu₀1 hu₀E'
  have hE'card : 2 ≤ Nat.card E' := (Subgroup.one_lt_card_iff_ne_bot E').2 hE'ne
  have hEcard : Nat.card E = 4 := C.card_W
  have hE'E : E' ≤ E := inf_le_left
  have hX'r : E' ⊔ D ≤ Subgroup.centralizer ({r} : Set G) := by
    refine sup_le inf_le_right ?_
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hd.2 r hrK).symm
  have h1 : (Z ⊓ Subgroup.centralizer ({r} : Set G)).relIndex Z ≤ (E' ⊔ D).relIndex Z := by
    rw [← Subgroup.inf_relIndex_right (E' ⊔ D) Z]
    exact Subgroup.relIndex_le_of_le_left (fun g hg => ⟨hg.2, hX'r hg.1⟩)
      (burnsideC56_relIndex_ne_zero _ _)
  have h2 : (E' ⊔ D).relIndex Z ≤ (E' ⊔ D).relIndex (E ⊔ D) :=
    Subgroup.relIndex_le_of_le_right (burnsideC56_Z_le C) (burnsideC56_relIndex_ne_zero _ _)
  have hcomm : ∀ e ∈ E, ∀ d ∈ D, e * d = d * e := fun e he d hd => C.U_comm_D he.1 hd
  have hcomm' : ∀ e ∈ E', ∀ d ∈ D, e * d = d * e := fun e he d hd => C.U_comm_D he.1.1 hd
  have hinf : E ⊓ D = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    have : g ∈ blockU K ⊓ D := ⟨hg.1.1, hg.2⟩
    rwa [C.U_inf_D] at this
  have hinf' : E' ⊓ D = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    have : g ∈ E ⊓ D := ⟨hg.1.1, hg.2⟩
    rwa [hinf] at this
  have hc1 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hc2 := B2F.card_sup_mul_card_inf_of_commute hcomm'
  rw [hinf, Subgroup.card_bot, mul_one] at hc1
  rw [hinf', Subgroup.card_bot, mul_one] at hc2
  have h3 := C5.card_eq_card_mul_relIndex (sup_le_sup_right hE'E D)
  rw [hc1, hc2, hEcard] at h3
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have h4 : (E' ⊔ D).relIndex (E ⊔ D) ≤ 2 := by
    by_contra hcon
    have h3' : 3 ≤ (E' ⊔ D).relIndex (E ⊔ D) := by omega
    have h5 := Nat.mul_le_mul (Nat.mul_le_mul_right (Nat.card D) hE'card) h3'
    nlinarith
  exact h1.trans (h2.trans h4)

theorem burnsideC56_mem_normalizer {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ R₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (C : burnsideC5x_A5Cfg R₁ K₁)
    (hbeq : baum R₁ = baum R) {r : G} (hrR : r ∈ R)
    (hr : ((baum R ⊓ Subgroup.centralizer (baum R : Set G)) ⊓
        Subgroup.centralizer ({r} : Set G)).relIndex
      (baum R ⊓ Subgroup.centralizer (baum R : Set G)) ≤ 2) :
    r ∈ Subgroup.normalizer (K₁ : Set G) := by
  by_contra hrN
  have hne : conjByElt r K₁ ≠ K₁ := fun h => hrN (C2Eleven.mem_normalizer_iff_conjByElt.2 h)
  have hrT : r ∈ TH := hset.hyp1.R_le hrR
  have hK₂ : conjByElt r K₁ ≤ Subgroup.centralizer (K₁ : Set G) := by
    have := hset.config.commute r hrT 1 TH.one_mem (by rwa [burnsideC5h_c54_conjByElt_one])
    rwa [burnsideC5h_c54_conjByElt_one] at this
  set Z := baum R ⊓ Subgroup.centralizer (baum R : Set G) with hZ
  set E := blockU K₁ ⊓ Subgroup.centralizer (baum R : Set G) with hE
  have hEcard : Nat.card E = 4 := by
    have := C.card_W
    rw [hbeq] at this
    exact this
  have hUB : blockU K₁ ≤ baum R := by rw [← hbeq]; exact C.hUB
  have hEZ : E ≤ Z := fun e he => Subgroup.mem_inf.2 ⟨hUB he.1, he.2⟩
  set F := Z ⊓ Subgroup.centralizer ({r} : Set G) with hF
  have hidx : F.relIndex E ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hEZ (burnsideC56_relIndex_ne_zero _ _)).trans hr
  have hcard := C5.card_eq_card_mul_relIndex (inf_le_right : F ⊓ E ≤ E)
  rw [Subgroup.inf_relIndex_right, hEcard] at hcard
  have hne' : F ⊓ E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne'
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heU : e ∈ blockU K₁ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 he).2).1
  have her : e * r = r * e :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 he).1).2
  have heK₂ : e ∈ conjByElt r K₁ := by
    rw [mem_conjByElt]
    have : r⁻¹ * e * r = e := by
      calc r⁻¹ * e * r = r⁻¹ * (e * r) := by group
        _ = r⁻¹ * (r * e) := by rw [her]
        _ = e := by group
    rw [this]
    exact Setup.Campbell.blockU_le_self_of_isShort2 C.short heU
  have hZ0 : e ∈ blockZ K₁ := Subgroup.mem_inf.2 ⟨heU, hK₂ heK₂⟩
  rw [AppC.blockZ_eq_bot_of_alt5 C.short C.alt5, Subgroup.mem_bot] at hZ0
  exact he1' hZ0

@[expose] def burnsideC56_a5_Rpp {G : Type} [Group G] (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | g ∈ R ∧
    ((baum R ⊓ Subgroup.centralizer (baum R : Set G)) ⊓
        Subgroup.centralizer ({g} : Set G)).relIndex
      (baum R ⊓ Subgroup.centralizer (baum R : Set G)) ≤ 2}

theorem burnsideC56_a5_Rpp_le (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5) :
    burnsideC56_a5_Rpp R ≤ R ⊓ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨C₁⟩ := burnsideC56_a5_cfg_inf h116 hset h5
  have hbeq := burnsideC56_baum_inf h116 hset (K₁ := K₁)
  unfold burnsideC56_a5_Rpp
  rw [Subgroup.closure_le]
  rintro g ⟨hgR, hg⟩
  exact Subgroup.mem_inf.2 ⟨hgR, burnsideC56_mem_normalizer hset C₁ hbeq hgR hg⟩

theorem burnsideC56_a5_inf_le_Rpp (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5) :
    R ⊓ K₁ ≤ burnsideC56_a5_Rpp R := by
  obtain ⟨C₁⟩ := burnsideC56_a5_cfg_inf h116 hset h5
  have hbeq := burnsideC56_baum_inf h116 hset (K₁ := K₁)
  intro r hr
  obtain ⟨hrR, hrK⟩ := Subgroup.mem_inf.1 hr
  have h := burnsideC56_relIndex_le_two C₁ (r := r)
    (Subgroup.mem_inf.2 ⟨hrR, Subgroup.le_normalizer hrK⟩) hrK
  rw [hbeq] at h
  unfold burnsideC56_a5_Rpp
  exact Subgroup.subset_closure ⟨hrR, h⟩

theorem burnsideC56_a5_baum_le_Rpp {G : Type} [Group G] [Finite G] (R : Subgroup G) :
    baum R ≤ burnsideC56_a5_Rpp R := by
  intro s hs
  have h : (baum R ⊓ Subgroup.centralizer (baum R : Set G)) ⊓
      Subgroup.centralizer ({s} : Set G) = baum R ⊓ Subgroup.centralizer (baum R : Set G) := by
    refine inf_eq_left.2 fun z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.1 hz).2 s hs).symm
  unfold burnsideC56_a5_Rpp
  refine Subgroup.subset_closure ⟨C1GN.baum_le R hs, ?_⟩
  show ((baum R ⊓ Subgroup.centralizer (baum R : Set G)) ⊓
      Subgroup.centralizer ({s} : Set G)).relIndex
    (baum R ⊓ Subgroup.centralizer (baum R : Set G)) ≤ 2
  rw [h, Subgroup.relIndex_self]
  norm_num

theorem burnsideC56_a5_thompsonJ_le_Rpp {G : Type} [Group G] [Finite G] (R : Subgroup G) :
    thompsonJ R ≤ burnsideC56_a5_Rpp R :=
  (C5.thompsonJ_le_baum' R).trans (burnsideC56_a5_baum_le_Rpp R)

theorem burnsideC56_a5_Rpp_baum (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5) :
    baum (burnsideC56_a5_Rpp R) = baum R :=
  burnsideC5h_p2_baum_eq (burnsideC56_a5_thompsonJ_le_Rpp R)
    ((burnsideC56_a5_Rpp_le h116 hset h5).trans inf_le_left) (burnsideC56_a5_baum_le_Rpp R)

theorem burnsideC56_mem_normalizer_closure {G : Type} [Group G] {X : Set G} {y : G}
    (h : ∀ g, g ∈ X ↔ y * g * y⁻¹ ∈ X) :
    y ∈ Subgroup.normalizer ((Subgroup.closure X : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, MonoidHom.coe_coe, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (h a).1 ha
  · intro hg
    refine ⟨y⁻¹ * g * y, ?_, by group⟩
    rw [h]
    have e : y * (y⁻¹ * g * y) * y⁻¹ = g := by group
    rw [e]
    exact hg

theorem burnsideC56_a5_le_normalizer_Rpp {G : Type} [Group G] {M₀ R : Subgroup G}
    (hM : M₀ ≤ Subgroup.normalizer (R : Set G)) :
    M₀ ≤ Subgroup.normalizer (burnsideC56_a5_Rpp R : Set G) := by
  intro y hy
  have hyR := hM hy
  have hyB := normalizer_le_normalizer_baum R hyR
  unfold burnsideC56_a5_Rpp
  refine burnsideC56_mem_normalizer_closure fun g => ?_
  simp only [Set.mem_setOf_eq]
  rw [burnsideC56_relIndex_conj hyB g, ← Subgroup.mem_normalizer_iff.mp hyR g]

theorem burnsideC56_a5_Rpp_sylow (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5) :
    IsSylowTwoOf (burnsideC56_a5_Rpp R) (K₁ ⊔ burnsideC56_a5_Rpp R) := by
  have hle := burnsideC56_a5_Rpp_le h116 hset h5
  have hge := burnsideC56_a5_inf_le_Rpp h116 hset h5
  have hR2 : IsPGroup 2 R := hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le
  have hinf : K₁ ⊓ burnsideC56_a5_Rpp R = R ⊓ K₁ := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨hgK, hgR⟩ := Subgroup.mem_inf.1 hg
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hle hgR)).1, hgK⟩
    · exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hg).2, hge hg⟩
  have hsyl : IsSylowTwoOf (R ⊓ K₁) K₁ := by
    have := burnsideC5h_p1_isSylow_inf hset TH.one_mem
    rwa [burnsideC5h_c54_conjByElt_one] at this
  refine burnsideC5h_p1_isSylow_sup (hR2.to_le (hle.trans inf_le_left)) (hle.trans inf_le_right) ?_
  rw [hinf]
  exact hsyl

theorem burnsideC56_a5_cfg_Rpp (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5) :
    Nonempty (burnsideC5x_A5Cfg (burnsideC56_a5_Rpp R) K₁) :=
  burnsideC56_a5_cfg_of h116 hset h5 (burnsideC56_a5_thompsonJ_le_Rpp R)
    (burnsideC56_a5_baum_le_Rpp R) (burnsideC56_a5_Rpp_le h116 hset h5)
    (burnsideC56_a5_Rpp_sylow h116 hset h5)

theorem burnsideC56_P_congr {G : Type} [Group G] {R R' K : Subgroup G} (x : G)
    (h : baum R' = baum R) :
    (burnsideC5x_P1 R' K x ↔ burnsideC5x_P1 R K x) ∧
      (burnsideC5x_P2 R' K x ↔ burnsideC5x_P2 R K x) ∧
      (burnsideC5x_P3 R' K x ↔ burnsideC5x_P3 R K x) ∧
      (burnsideC5x_P4 R' K x ↔ burnsideC5x_P4 R K x) := by
  unfold burnsideC5x_P1 burnsideC5x_P2 burnsideC5x_P3 burnsideC5x_P4
  rw [h]
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem burnsideC56_gamma_cfg {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {x : G} (m : burnsideC5x_A5Cfg.Good C x) {y : G}
    (hy : y ∈ Subgroup.normalizer (R : Set G))
    (hyY : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K : Set G))) y =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K : Set G))) :
    conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y = pCoreOf 2 (K ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K ⊔ baum R)) y = conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x := by
  have hD2 : IsPGroup 2 ↥(baum R ⊓ Subgroup.centralizer (K : Set G)) :=
    (C.R2.to_le C.hBR).to_le inf_le_left
  have hYQ := burnsideC5x_YCls_of_UD C.Q_UD (fun q hq u hu => C.Q_comm_U hq hu)
    (C1.blockU_sq C.short) (fun u hu d hd => C.U_comm_D hu hd) hD2
  exact m.gamma_Y (Subgroup.map_subtype_le _) hYQ hy hyY

theorem burnsideC56_even_cfg {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {x : G} (m : burnsideC5x_A5Cfg.Good C x) : Even (orderOf x) := by
  have h4 : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K : Set G))) x =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K : Set G)) :=
    C.part4 m.hxR m.hne
  have hY2 : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
      (baum R ⊓ Subgroup.centralizer (K : Set G))) (x * x) =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, h4, h4]
  have hne : conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x ≠ pCoreOf 2 (K ⊔ baum R) := by
    intro heq
    apply (burnsideC5x_not_le_Q C.Q_eq m.hne).1
    have := C5.conjSubgroup_mono C.hUQ x
    rw [heq] at this
    exact this
  refine burnsideC5x_even_of_sq hne ?_
  rcases burnsideC56_gamma_cfg C m (y := x * x) (mul_mem m.hxR m.hxR) hY2 with h | h
  · exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp h
  · exfalso
    apply hne
    have h2 : conjSubgroup (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) (x * x)) x⁻¹ =
        conjSubgroup (conjSubgroup (pCoreOf 2 (K ⊔ baum R)) x) x⁻¹ :=
      congrArg (fun A => conjSubgroup A x⁻¹) h
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_right,
      C5.conjSubgroup_conjSubgroup_inv] at h2
    exact h2

theorem burnsideC56_a5_1to5 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (h5 : IsAltType K₁ 5) :
    burnsideC5x_P1 R K₁ x ∧ burnsideC5x_P2 R K₁ x ∧ burnsideC5x_P3 R K₁ x ∧
      burnsideC5x_P4 R K₁ x ∧ Even (orderOf x) := by
  obtain ⟨C⟩ := burnsideC56_a5_cfg_Rpp h116 hset h5
  have hbeq := burnsideC56_a5_Rpp_baum h116 hset h5
  have hxR : x ∈ Subgroup.normalizer (burnsideC56_a5_Rpp R : Set G) :=
    burnsideC56_a5_le_normalizer_Rpp hset.hyp1.R_norm hx.1
  have m : burnsideC5x_A5Cfg.Good C x := ⟨hxR, hx.2.2⟩
  obtain ⟨e1, e2, e3, e4⟩ := burnsideC56_P_congr (K := K₁) x hbeq
  obtain ⟨h1, h2, h3⟩ := C.part123 hxR hx.2.2
  exact ⟨e1.1 h1, e2.1 h2, e3.1 h3, e4.1 (C.part4 hxR hx.2.2), burnsideC56_even_cfg C m⟩

theorem burnsideC56_a5_gamma (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (h5 : IsAltType K₁ 5) {y : G} (hy : y ∈ M₀)
    (hyY : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) y =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) :
    conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) y = pCoreOf 2 (K₁ ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) y = conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x := by
  obtain ⟨C⟩ := burnsideC56_a5_cfg_Rpp h116 hset h5
  have hbeq := burnsideC56_a5_Rpp_baum h116 hset h5
  have hN := burnsideC56_a5_le_normalizer_Rpp hset.hyp1.R_norm
  have m : burnsideC5x_A5Cfg.Good C x := ⟨hN hx.1, hx.2.2⟩
  rw [← hbeq] at hyY ⊢
  exact burnsideC56_gamma_cfg C m (hN hy) hyY

end BurnsideC56A5

end PartBurnsideC56A5

section PartBurnsideC56Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

section BurnsideC56Blk

open CFSG.QuasithinUnique.A5.Delta5

theorem burnsideC56_blk_rank1_le {G : Type} [Group G] [Finite G] {B Q U W : Subgroup G} {q : ℕ}
    (hrk : C5.Rank1 B Q U W q) {A : Subgroup G} (hA : A ≤ B) : (A ⊓ Q).relIndex A ≤ q := by
  rw [C5.relIndex_inf_eq_of_le_normalizer (hA.trans hrk.B_le_normQ), ← hrk.idx_Q]
  exact C5.relIndex_le_of_le le_sup_right (sup_le hA hrk.Q_le_B)

theorem burnsideC56_blk_rank1_ge {G : Type} [Group G] [Finite G] {B Q U W : Subgroup G} {q : ℕ}
    (hrk : C5.Rank1 B Q U W q) {A : Subgroup G} (hA : A ≤ B) (hAQ : ¬ A ≤ Q) :
    q ≤ (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U := by
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have hle : U ⊓ Subgroup.centralizer (A : Set G) ≤ W := fun u hu =>
    (hrk.cent_y a (hA haA) haQ u (Subgroup.mem_inf.1 hu).1).2
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.1 hu).2 a haA).symm
  rw [← hrk.idx_W]
  exact Subgroup.relIndex_le_of_le_left hle (burnsideC56_relIndex_ne_zero _ _)

theorem burnsideC56_blk_rank1_pb {G : Type} [Group G] [Finite G] {B Q U W : Subgroup G} {q : ℕ}
    (hrk : C5.Rank1 B Q U W q) {A : Subgroup G} (hA : A ≤ B) :
    (A ⊓ Q).relIndex A ≤ (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U := by
  by_cases hAQ : A ≤ Q
  · rw [inf_eq_left.mpr hAQ, Subgroup.relIndex_self]
    exact Nat.one_le_iff_ne_zero.2 (burnsideC56_relIndex_ne_zero _ _)
  · exact (burnsideC56_blk_rank1_le hrk hA).trans (burnsideC56_blk_rank1_ge hrk hA hAQ)

theorem burnsideC56_blk_rank1_pb_eq {G : Type} [Group G] [Finite G] {B Q U W : Subgroup G}
    {q : ℕ} (hrk : C5.Rank1 B Q U W q) {A : Subgroup G} (hA : A ≤ B)
    (heq : (A ⊓ Q).relIndex A = (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U) :
    A ≤ Q ∨ A ⊔ Q = B := by
  by_cases hAQ : A ≤ Q
  · exact Or.inl hAQ
  · right
    have h1 := burnsideC56_blk_rank1_le hrk hA
    have h2 := burnsideC56_blk_rank1_ge hrk hA hAQ
    have h3 : (A ⊓ Q).relIndex A = q := le_antisymm h1 (by rw [heq]; exact h2)
    rw [C5.relIndex_inf_eq_of_le_normalizer (hA.trans hrk.B_le_normQ)] at h3
    refine C5.eq_of_relIndex_eq le_sup_right (sup_le hA hrk.Q_le_B) ?_ ?_
    · rw [h3, hrk.idx_Q]
    · rw [hrk.idx_Q]; exact hrk.q_ne_zero

theorem burnsideC56_blk_rank1_b6 {G : Type} [Group G] {B Q U W : Subgroup G} {q : ℕ}
    (hrk : C5.Rank1 B Q U W q) {b : G} (hbB : b ∈ B) (hbQ : b ∉ Q) :
    U ⊓ Subgroup.centralizer ({b} : Set G) = ⁅U, B⁆ := by
  rw [hrk.comm_UB]
  ext u
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hu, hub⟩
    exact (hrk.cent_y b hbB hbQ u hu).2 hub
  · intro hu
    exact ⟨hrk.W_le_U hu, (hrk.cent_y b hbB hbQ u (hrk.W_le_U hu)).1 hu⟩

theorem burnsideC56_blk_lin2A3_b6 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) :
    ∃ b ∈ conjSubgroup (blockU K₁) x,
      blockU K₁ ⊓ Subgroup.centralizer ({b} : Set G) = ⁅blockU K₁, baum R⁆ := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, -, hrk, -, -⟩ := burnsideC5x_rank1 h116 hset hK₁mem hL
  obtain ⟨-, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨hx1, -⟩ := burnsideC5x_not_le_Q hrk.Q_eq hx.2.2
  obtain ⟨b, hbV, hbQ⟩ := IsConcreteLE.not_le_iff_exists.mp hx1
  exact ⟨b, hbV, burnsideC56_blk_rank1_b6 hrk (hrk.conj_le_B hxB hbV) hbQ⟩

theorem burnsideC56_blk_lin2A3_sc (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) {r : G}
    (hr : r ∈ R ⊓ Subgroup.normalizer (K₁ : Set G))
    (hrb : ∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ Subgroup.centralizer (blockU K₁ : Set G)) :
    ∃ s ∈ baum R, s⁻¹ * r ∈ Subgroup.centralizer (blockU K₁ : Set G) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨hmin, hblk, hth, hbeq, hS1⟩ := burnsideC5x_data h116 hset hK₁mem
  have hnat : NaturalConcl (R ⊓ Subgroup.normalizer (K₁ : Set G))
      (K₁ ⊔ (R ⊓ Subgroup.normalizer (K₁ : Set G))) K₁ := by
    rcases hL with hl | h3
    · exact C56.natural_Lin2 hmin hblk hl hth rfl inf_le_right
    · exact C56.natural_A3 hmin hblk h3 hth rfl inf_le_right
  unfold NaturalConcl at hnat
  rw [hbeq] at hnat
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hSC⟩ := hnat
  set R₁ := R ⊓ Subgroup.normalizer (K₁ : Set G) with hR₁
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hR2 : IsPGroup 2 R := hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le
  have hsyl : IsSylowTwoOf R₁ (K₁ ⊔ R₁) := burnsideC5h_p3_sylow hset hK₁mem
  have hP : R₁ ⊓ Subgroup.centralizer (blockU K₁ : Set G) = pCoreOf 2 (K₁ ⊔ R₁) :=
    C56.baum_inf_centralizer_eq hshort (hR2.to_le inf_le_left) inf_le_right hsyl
  have hBR₁ : baum R ≤ R₁ := le_inf (C1GN.baum_le R) hS1
  have hmem : r ∈ baum R ⊔ pCoreOf 2 (K₁ ⊔ R₁) := hSC r hr fun b hb => by
    rw [← hP]
    exact Subgroup.mem_inf.2 ⟨R₁.mul_mem (R₁.mul_mem (R₁.mul_mem hr (hBR₁ hb)) (R₁.inv_mem hr))
      (R₁.inv_mem (hBR₁ hb)), hrb b hb⟩
  have hBP : baum R ≤ Subgroup.normalizer (pCoreOf 2 (K₁ ⊔ R₁) : Set G) := fun b hb =>
    (le_sup_right.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)) (hBR₁ hb)
  obtain ⟨s, hs, p, hp, hrsp⟩ := C5.mem_sup_of_le_normalizer hBP hmem
  refine ⟨s, hs, ?_⟩
  have e : s⁻¹ * r = p := by rw [hrsp]; group
  rw [e]
  rw [← hP] at hp
  exact (Subgroup.mem_inf.1 hp).2

theorem burnsideC56_blk_zA_fix : ∀ w : Fin 5 → ZMod 2, pact AppC.zA w = w →
    ∀ σ ∈ Eset, pact σ w = w := by
  decide +kernel

theorem burnsideC56_blk_a5_idx {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {A : Subgroup G} (hA : A ≤ baum R) :
    (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A = Nat.card (C.P.im A) ∧
      Nat.card (AppC.FixΔ (C.P.im A)) *
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) = 16 := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.trans C.hBN
  refine ⟨?_, ?_⟩
  · have h1 := C.P.card_im_mul hAN
    rw [C.inf_cent_U_eq hA] at h1
    have h2 := C5.card_eq_card_mul_relIndex (inf_le_left : A ⊓ pCoreOf 2 (K ⊔ baum R) ≤ A)
    have hpos : 0 < Nat.card ↥(A ⊓ pCoreOf 2 (K ⊔ baum R)) := Nat.card_pos
    have h3 : Nat.card ↥(A ⊓ pCoreOf 2 (K ⊔ baum R)) * Nat.card (C.P.im A) =
        Nat.card ↥(A ⊓ pCoreOf 2 (K ⊔ baum R)) * (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A := by
      rw [← h2, ← h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hpos h3).symm
  · have h1 := C.P.card_fix hAN
    have h2 := C5.card_eq_card_mul_relIndex
      (inf_le_left : blockU K ⊓ Subgroup.centralizer (A : Set G) ≤ blockU K)
    rw [C.card_U, h1] at h2
    exact h2.symm

theorem burnsideC56_blk_a5_pb {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {A : Subgroup G} (hA : A ≤ baum R) :
    (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
      (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) := by
  obtain ⟨h1, h2⟩ := burnsideC56_blk_a5_idx C hA
  have hle := C.im_le hA
  have hsq : ∀ a ∈ C.P.im A, a * a = 1 := fun a ha => AppC.Eset_sq a ((mem_Estd a).1 (hle ha))
  have hcm : ∀ a ∈ C.P.im A, ∀ b ∈ C.P.im A, a * b = b * a := fun a ha b hb =>
    AppC.Eset_comm a ((mem_Estd a).1 (hle ha)) b ((mem_Estd b).1 (hle hb))
  have h3 := AppC.card_mul_fix_le (C.P.im A) hsq hcm
  have hfpos : 0 < Nat.card (AppC.FixΔ (C.P.im A)) := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, zero_mul] at h2
    omega
  rw [h1]
  have h4 : Nat.card (C.P.im A) * Nat.card (AppC.FixΔ (C.P.im A)) ≤
      (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) *
        Nat.card (AppC.FixΔ (C.P.im A)) := by
    rw [mul_comm ((blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K)), h2]
    exact h3
  exact Nat.le_of_mul_le_mul_right h4 hfpos

theorem burnsideC56_blk_a5_pb_eq {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {A : Subgroup G} (hA : A ≤ baum R) {r : G} (hrR : r ∈ R)
    (hrK : r ∈ K) (hrE : C.P.pf r ∉ Eset) (hrA : r ∈ Subgroup.normalizer (A : Set G))
    (heq : (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A =
      (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K)) :
    A ≤ pCoreOf 2 (K ⊔ baum R) ∨ A ⊔ pCoreOf 2 (K ⊔ baum R) = baum R := by
  obtain ⟨h1, h2⟩ := burnsideC56_blk_a5_idx C hA
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.trans C.hBN
  have hle := C.im_le hA
  have hsq : ∀ a ∈ C.P.im A, a * a = 1 := fun a ha => AppC.Eset_sq a ((mem_Estd a).1 (hle ha))
  have hcm : ∀ a ∈ C.P.im A, ∀ b ∈ C.P.im A, a * b = b * a := fun a ha b hb =>
    AppC.Eset_comm a ((mem_Estd a).1 (hle ha)) b ((mem_Estd b).1 (hle hb))
  have hcard : Nat.card (C.P.im A) * Nat.card (AppC.FixΔ (C.P.im A)) = 16 := by
    rw [← h1, heq, mul_comm]; exact h2
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := C.RN hrR
  have hD : C.P.pf r ∈ Dset := by
    have : C.P.pf r ∈ C.P.im R := (C.P.mem_im_pf C.RN).2 ⟨r, hrR, rfl⟩
    rw [C.hR] at this
    exact (mem_Dstd _).1 this
  have hsign : Equiv.Perm.sign (C.P.pf r) = 1 := by
    have h := C.P.hπα r hrK
    rw [C.P.pf_eq hrN]
    have h' : C.P.π ⟨r, hrN⟩ =
        ((C.P.α ⟨r, hrK⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := h
    rw [h']
    exact Equiv.Perm.mem_alternatingGroup.1 (C.P.α ⟨r, hrK⟩).2
  obtain ⟨hσ1, hσ2⟩ := AppC.conj_swap_of _ hD hsign hrE
  have hconj : ∀ g ∈ C.P.im A, (C.P.pf r)⁻¹ * g * C.P.pf r ∈ C.P.im A := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := (C.P.mem_im_pf hAN).1 hg
    have haN := hAN ha
    refine (C.P.mem_im_pf hAN).2 ⟨r⁻¹ * a * r, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hrA) a).mp ha
      simpa using this
    · rw [C.P.pf_mul (mul_mem (inv_mem hrN) haN) hrN, C.P.pf_mul (inv_mem hrN) haN,
        C.P.pf_inv hrN]
  rcases AppC.classify_P (C.P.im A) (hle.trans Estd_le_Dstd) hsq hcm hcard with h | h | h | h
  · left
    intro a ha
    have : C.P.pf a ∈ C.P.im A := (C.P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩
    exact (C.mem_Q_iff (hA ha)).2 ((h _).1 this)
  · exfalso
    have h01 : Equiv.swap (0 : Fin 5) 1 ∈ C.P.im A := (h _).2 (Or.inr rfl)
    have h23 := hconj _ h01
    rw [hσ1] at h23
    rcases (h _).1 h23 with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · exfalso
    have h23 : Equiv.swap (2 : Fin 5) 3 ∈ C.P.im A := (h _).2 (Or.inr rfl)
    have h01 := hconj _ h23
    rw [hσ2] at h01
    rcases (h _).1 h01 with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · right
    refine le_antisymm (sup_le hA C.hQB) fun s hs => ?_
    have hsE : C.P.pf s ∈ C.P.im A :=
      (h _).2 ((mem_Estd _).1 (C.im_le le_rfl ((C.P.mem_im_pf C.hBN).2 ⟨s, hs, rfl⟩)))
    obtain ⟨a, ha, has⟩ := (C.P.mem_im_pf hAN).1 hsE
    have hq : a⁻¹ * s ∈ pCoreOf 2 (K ⊔ baum R) := by
      refine (C.mem_Q_iff (mul_mem (inv_mem (hA ha)) hs)).2 ?_
      rw [C.P.pf_mul (inv_mem (hAN ha)) (C.hBN hs), C.P.pf_inv (hAN ha), has, inv_mul_cancel]
    have e : s = a * (a⁻¹ * s) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hq)

theorem burnsideC56_blk_a5_b6 {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {x : G} (m : burnsideC5x_A5Cfg.Good C x) :
    ∃ b ∈ conjSubgroup (blockU K) x,
      blockU K ⊓ Subgroup.centralizer ({b} : Set G) = ⁅blockU K, baum R⁆ := by
  have hVN : conjSubgroup (blockU K) x ≤ Subgroup.normalizer (K : Set G) :=
    (C.conj_le_B m.hxR).trans C.hBN
  have hzE : AppC.zA ∈ Eset := by decide +kernel
  have hzV : AppC.zA ∈ C.P.im (conjSubgroup (blockU K) x) := by
    rw [C.im_conj_eq m.hxR m.hne]; exact (mem_Estd _).2 hzE
  obtain ⟨b, hbV, hbz⟩ := (C.P.mem_im_pf hVN).1 hzV
  have hbB : b ∈ baum R := C.conj_le_B m.hxR hbV
  refine ⟨b, hbV, ?_⟩
  rw [C.comm_UB_eq]
  apply le_antisymm
  · intro u hu
    obtain ⟨huU, hub⟩ := Subgroup.mem_inf.1 hu
    have hub' : b * u = u * b := (Subgroup.mem_centralizer_singleton_iff.1 hub).symm
    have hfix := (C.P.comm_iff (C.hBN hbB) huU).1 hub'
    rw [hbz] at hfix
    have hfixE : ∀ σ ∈ Eset, pact σ (C.P.bf u).1 = (C.P.bf u).1 :=
      burnsideC56_blk_zA_fix _ (congrArg Subtype.val hfix)
    refine Subgroup.mem_inf.2 ⟨huU, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    have hsE : C.P.pf s ∈ Eset :=
      (mem_Estd _).1 (C.im_le le_rfl ((C.P.mem_im_pf C.hBN).2 ⟨s, hs, rfl⟩))
    exact (C.P.comm_iff (C.hBN hs) huU).2 (Subtype.ext (hfixE _ hsE))
  · intro u hu
    obtain ⟨huU, huC⟩ := Subgroup.mem_inf.1 hu
    refine Subgroup.mem_inf.2 ⟨huU, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp huC b hbB).symm

theorem burnsideC56_blk_a5_sc {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {r : G} (hr : r ∈ R)
    (hrb : ∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ Subgroup.centralizer (blockU K : Set G)) :
    ∃ s ∈ baum R, s⁻¹ * r ∈ Subgroup.centralizer (blockU K : Set G) := by
  have hmem := C.SC (P := R ⊓ Subgroup.centralizer (blockU K : Set G)) rfl r hr (fun b hb => by
    rw [commutatorElement_def]
    exact Subgroup.mem_inf.2 ⟨R.mul_mem (R.mul_mem (R.mul_mem hr (C.hBR hb)) (R.inv_mem hr))
      (R.inv_mem (C.hBR hb)), hrb b hb⟩)
  have hBP : baum R ≤ Subgroup.normalizer
      ((R ⊓ Subgroup.centralizer (blockU K : Set G) : Subgroup G) : Set G) := fun b hb =>
    C5.mem_normalizer_inf (Subgroup.le_normalizer (C.hBR hb))
      (C5.mem_normalizer_centralizer (C.hBU hb))
  obtain ⟨s, hs, p, hp, hrsp⟩ := C5.mem_sup_of_le_normalizer hBP hmem
  refine ⟨s, hs, ?_⟩
  have e : s⁻¹ * r = p := by rw [hrsp]; group
  rw [e]
  exact (Subgroup.mem_inf.1 hp).2

theorem burnsideC56_blk_a5_pCore_cfg {G : Type} [Group G] [Finite G] {R K : Subgroup G}
    (C : burnsideC5x_A5Cfg R K) {x : G} (m : burnsideC5x_A5Cfg.Good C x) {W : Subgroup G}
    (hVW : conjSubgroup (blockU K) x ≤ Subgroup.centralizer (W : Set G))
    (hKW : K ≤ Subgroup.centralizer (W : Set G))
    (hD : ∀ d ∈ baum R ⊓ Subgroup.centralizer (K : Set G),
      d ∈ Subgroup.centralizer (W : Set G) → d * d = 1) :
    pCoreOf 2 K ≤ blockU K := by
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
  have hdW : d ∈ Subgroup.centralizer (W : Set G) := by
    have e : d = (u⁻¹ * (ℓ₀ : G)⁻¹) * t₀ := by
      calc d = u⁻¹ * (u * d) := by group
        _ = u⁻¹ * ((ℓ₀ : G)⁻¹ * t₀) := by rw [hud]
        _ = (u⁻¹ * (ℓ₀ : G)⁻¹) * t₀ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hKW huK)) (inv_mem (hKW ℓ₀.2))) (hVW ht₀V)
  have hdd : d * d = 1 := hD d hd hdW
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
  have hqsq : ∀ q ∈ C.P.α.ker, (q : G) * (q : G) = 1 := by
    intro q hq
    have hqK : (q : G) ∈ K := q.2
    obtain ⟨u', hu', d', hd', hq'⟩ := C.exists_UD (hqQ q hq)
    have hd'K : d' ∈ K := by
      have e : d' = u'⁻¹ * (q : G) := by rw [hq']; group
      rw [e]
      exact K.mul_mem (K.inv_mem (hUK hu')) hqK
    have hd'd' : d' * d' = 1 := hD d' hd' (hKW hd'K)
    have hu'u' : u' * u' = 1 := by
      have := C1.blockU_sq C.short u' hu'
      rwa [pow_two] at this
    have hc : u' * d' = d' * u' := C.U_comm_D hu' hd'
    rw [hq']
    calc u' * d' * (u' * d') = u' * (d' * u') * d' := by group
      _ = u' * (u' * d') * d' := by rw [hc]
      _ = (u' * u') * (d' * d') := by group
      _ = 1 := by rw [hu'u', hd'd', one_mul]
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
      exact hqsq q hq)
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

theorem burnsideC56_blk_pb (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {A : Subgroup G}
    (hA : A ≤ baum R) :
    (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A ≤
      (blockU K₁ ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K₁) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · obtain ⟨q, W, -, hrk, -, -⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inl hL)
    exact burnsideC56_blk_rank1_pb hrk hA
  · obtain ⟨q, W, -, hrk, -, -⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inr h3)
    exact burnsideC56_blk_rank1_pb hrk hA
  · obtain ⟨C⟩ := burnsideC56_a5_cfg_inf h116 hset h5
    have hbeq := burnsideC56_baum_inf h116 hset (K₁ := K₁)
    rw [← hbeq] at hA ⊢
    exact burnsideC56_blk_a5_pb C hA

theorem burnsideC56_blk_pb_eq (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {A : Subgroup G}
    (hA : A ≤ baum R) (hTH : TH ≤ Subgroup.normalizer (A : Set G))
    (heq : (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A =
      (blockU K₁ ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K₁)) :
    A ≤ pCoreOf 2 (K₁ ⊔ baum R) ∨ A ⊔ pCoreOf 2 (K₁ ⊔ baum R) = baum R := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · obtain ⟨q, W, -, hrk, -, -⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inl hL)
    exact burnsideC56_blk_rank1_pb_eq hrk hA heq
  · obtain ⟨q, W, -, hrk, -, -⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inr h3)
    exact burnsideC56_blk_rank1_pb_eq hrk hA heq
  · obtain ⟨C⟩ := burnsideC56_a5_cfg_inf h116 hset h5
    have hbeq := burnsideC56_baum_inf h116 hset (K₁ := K₁)
    have hsyl : IsSylowTwoOf ((R ⊓ Subgroup.normalizer (K₁ : Set G)) ⊓ K₁) K₁ := by
      have := burnsideC5h_p1_isSylow_inf hset TH.one_mem
      rw [burnsideC5h_c54_conjByElt_one] at this
      rwa [inf_assoc, inf_eq_right.mpr
        (Subgroup.le_normalizer : K₁ ≤ Subgroup.normalizer (K₁ : Set G))]
    obtain ⟨r, hrRK, hrE⟩ := C.exists_r hsyl
    have hrR₁ : r ∈ R ⊓ Subgroup.normalizer (K₁ : Set G) := (Subgroup.mem_inf.1 hrRK).1
    have hrR : r ∈ R := (Subgroup.mem_inf.1 hrR₁).1
    rw [← hbeq] at hA heq ⊢
    exact burnsideC56_blk_a5_pb_eq C hA hrR₁ (Subgroup.mem_inf.1 hrRK).2 hrE
      (hTH (hset.hyp1.R_le hrR)) heq

theorem burnsideC56_blk_b6 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x) :
    ∃ b ∈ conjSubgroup (blockU K₁) x,
      blockU K₁ ⊓ Subgroup.centralizer ({b} : Set G) = ⁅blockU K₁, baum R⁆ := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · exact burnsideC56_blk_lin2A3_b6 h116 hset hx (Or.inl hL)
  · exact burnsideC56_blk_lin2A3_b6 h116 hset hx (Or.inr h3)
  · obtain ⟨C⟩ := burnsideC56_a5_cfg_Rpp h116 hset h5
    have hbeq := burnsideC56_a5_Rpp_baum h116 hset h5
    have m : burnsideC5x_A5Cfg.Good C x :=
      ⟨burnsideC56_a5_le_normalizer_Rpp hset.hyp1.R_norm hx.1, hx.2.2⟩
    have h := burnsideC56_blk_a5_b6 C m
    rwa [hbeq] at h

theorem burnsideC56_blk_sc (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) {r : G}
    (hr : r ∈ R ⊓ Subgroup.normalizer (K₁ : Set G))
    (hrb : ∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ Subgroup.centralizer (blockU K₁ : Set G)) :
    ∃ s ∈ baum R, s⁻¹ * r ∈ Subgroup.centralizer (blockU K₁ : Set G) := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  rcases (burnsideC5h_c54_isChi0Block hset hK₁mem).2 with hL | h3 | h5
  · exact burnsideC56_blk_lin2A3_sc h116 hset (Or.inl hL) hr hrb
  · exact burnsideC56_blk_lin2A3_sc h116 hset (Or.inr h3) hr hrb
  · obtain ⟨C⟩ := burnsideC56_a5_cfg_inf h116 hset h5
    have hbeq := burnsideC56_baum_inf h116 hset (K₁ := K₁)
    have h := burnsideC56_blk_a5_sc C hr (fun b hb => hrb b (by rw [← hbeq]; exact hb))
    rwa [hbeq] at h

theorem burnsideC56_blk_a5_pCore (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) (h5 : IsAltType K₁ 5)
    {x : G} (hx : GoodX H M₀ K₁ x) {W : Subgroup G}
    (hVW : conjSubgroup (blockU K₁) x ≤ Subgroup.centralizer (W : Set G))
    (hKW : K₁ ≤ Subgroup.centralizer (W : Set G))
    (hD : ∀ d ∈ baum R ⊓ Subgroup.centralizer (K₁ : Set G),
      d ∈ Subgroup.centralizer (W : Set G) → d * d = 1) :
    pCoreOf 2 K₁ ≤ blockU K₁ := by
  obtain ⟨C⟩ := burnsideC56_a5_cfg_Rpp h116 hset h5
  have hbeq := burnsideC56_a5_Rpp_baum h116 hset h5
  have m : burnsideC5x_A5Cfg.Good C x :=
    ⟨burnsideC56_a5_le_normalizer_Rpp hset.hyp1.R_norm hx.1, hx.2.2⟩
  rw [← hbeq] at hD
  exact burnsideC56_blk_a5_pCore_cfg C m hVW hKW hD

theorem burnsideC56_blk_lin2_pCore (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁)
    (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) {x : G} (hx : GoodX H M₀ K₁ x)
    {Z : Subgroup G} (hZe : C5.ElemAb2 Z) (hZK : Z ≤ Subgroup.centralizer (K₁ : Set G))
    (hZS : Z ≤ baum R) (hVZ : conjSubgroup (blockU K₁) x ≤ K₁ ⊔ Z)
    (hQZ : pCoreOf 2 (K₁ ⊔ baum R) ⊓ K₁ ≤ blockU K₁ ⊔ Z) :
    pCoreOf 2 K₁ ≤ blockU K₁ := by
  have hK₁mem : K₁ ∈ conjSubgroupsBy TH K₁ :=
    ⟨1, TH.one_mem, (burnsideC5h_c54_conjByElt_one K₁).symm⟩
  obtain ⟨q, W, -, hrk, -, -⟩ := burnsideC5x_rank1 h116 hset hK₁mem (Or.inl hn)
  have hP1 := burnsideC5h_p1_minParabolic hset (burnsideC5h_c54_one h116 hset)
  obtain ⟨hsylK, -, -, -, -⟩ := burnsideC5h_p2_lin2A3 h116 hset hP1 K₁ hK₁mem (Or.inl hn)
  obtain ⟨-, hxB⟩ := burnsideC5x_x_normalizer hset hx.1
  obtain ⟨-, ⟨hP2a, -, -, -, -⟩, -⟩ := burnsideC5x_lin2A3_123 h116 hset hx (Or.inl hn)
  have hshort : IsShort2 K₁ := hset.config.chi0.1.1
  have hUK : blockU K₁ ≤ K₁ := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le K₁)
  have hR2 : IsPGroup 2 R := hset.hyp1.sylow.2.1.to_le hset.hyp1.R_le
  have hB2 : IsPGroup 2 (baum R) := hR2.to_le (C1GN.baum_le R)
  set S := baum R with hS
  set Q := pCoreOf 2 (K₁ ⊔ baum R) with hQdef
  set U := blockU K₁ with hU
  set Vx := conjSubgroup U x with hVx
  set V := U ⊔ Z with hV
  have hUZ : ∀ u ∈ U, ∀ z ∈ Z, u * z = z * u := fun u hu z hz =>
    Subgroup.mem_centralizer_iff.mp (hZK hz) u (hUK hu)
  have hVe : C5.ElemAb2 V := C5.ElemAb2.sup (C1.elemAb2_blockU hshort) hZe hUZ
  have hZQ : Z ≤ Q := fun z hz => by
    rw [hrk.Q_eq]
    exact Subgroup.mem_inf.2 ⟨hZS hz, Subgroup.centralizer_le hUK (hZK hz)⟩
  have hVQ : V ≤ Q := sup_le hrk.U_le_Q hZQ
  have hVS : V ≤ S := hVQ.trans hrk.Q_le_B
  have hKZ : K₁ ≤ Subgroup.normalizer (Z : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZK hz) k hk).symm)
  have hKV : K₁ ≤ Subgroup.normalizer (V : Set G) := fun k hk =>
    C1.mem_normalizer_sup (C1.le_normalizer_blockU K₁ hk) (hKZ hk)
  set M := K₁ ⊔ V with hM
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := sup_le hKV Subgroup.le_normalizer
  have hVM : V ≤ M := le_sup_right
  set A := S ⊓ K₁ with hA
  have hAK : A ≤ K₁ := inf_le_right
  set T := A ⊔ V with hT
  have hVT : V ≤ T := le_sup_right
  have hTS : T ≤ S := sup_le inf_le_left hVS
  have hTM : T ≤ M := sup_le (hAK.trans le_sup_left) le_sup_right
  have hidx : ¬ 2 ∣ (T.subgroupOf M).index := by
    have e1 : V.relIndex (K₁ ⊔ V) = V.relIndex K₁ := C5.relIndex_sup_eq_of_le_normalizer hKV
    have e2 : V.relIndex (A ⊔ V) = V.relIndex A :=
      C5.relIndex_sup_eq_of_le_normalizer (hAK.trans hKV)
    have hVK : V ⊓ K₁ ≤ A := fun g hg =>
      Subgroup.mem_inf.2 ⟨hVS (Subgroup.mem_inf.1 hg).1, (Subgroup.mem_inf.1 hg).2⟩
    have hVA : V ⊓ A = V ⊓ K₁ := le_antisymm (inf_le_inf_left V hAK) (le_inf inf_le_left hVK)
    have h1 := Subgroup.relIndex_mul_relIndex V T M hVT hTM
    have h2 := Subgroup.relIndex_mul_relIndex (V ⊓ K₁) A K₁ hVK hAK
    have h3 : (V ⊓ K₁).relIndex K₁ = V.relIndex K₁ := Subgroup.inf_relIndex_right V K₁
    have h4 : (V ⊓ K₁).relIndex A = V.relIndex A := by
      rw [← hVA]; exact Subgroup.inf_relIndex_right V A
    rw [h3, h4] at h2
    have hpos : 0 < V.relIndex T := Nat.pos_of_ne_zero (burnsideC56_relIndex_ne_zero _ _)
    have hTMA : T.relIndex M = A.relIndex K₁ := by
      have h5 : V.relIndex T * T.relIndex M = V.relIndex T * A.relIndex K₁ := by
        calc V.relIndex T * T.relIndex M = V.relIndex M := h1
          _ = V.relIndex (K₁ ⊔ V) := rfl
          _ = V.relIndex K₁ := e1
          _ = V.relIndex A * A.relIndex K₁ := h2.symm
          _ = V.relIndex T * A.relIndex K₁ := by rw [← e2]
      exact Nat.eq_of_mul_eq_mul_left hpos h5
    have hodd : ¬ 2 ∣ (A.subgroupOf K₁).index := hsylK.2.2
    intro hdvd
    apply hodd
    have e3 : (T.subgroupOf M).index = T.relIndex M := rfl
    have e4 : (A.subgroupOf K₁).index = A.relIndex K₁ := rfl
    rw [e4, ← hTMA, ← e3]
    exact hdvd
  have hVxS : Vx ≤ S := hrk.conj_le_B hxB
  have hVxe : IsElemAbelian 2 Vx :=
    C5.isElemAbelian_two_iff.mpr ((C1.elemAb2_blockU hshort).conjSubgroup x)
  obtain ⟨C₀, hC₀V, -, hdisj, hsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
    Nat.prime_two hVxe (inf_le_left : Vx ⊓ Q ≤ Vx) (bot_le : ⊥ ≤ Vx) (inf_bot_eq _)
  have hVxc : ∀ a ∈ Vx, ∀ b ∈ Vx, a * b = b * a :=
    ((C1.elemAb2_blockU hshort).conjSubgroup x).1
  have hC₀T : C₀ ≤ T := by
    intro c hc
    have hcVx := hC₀V hc
    obtain ⟨k, hk, z, hz, rfl⟩ := C5.mem_sup_of_commute
      (fun k hk z hz => Subgroup.mem_centralizer_iff.mp (hZK hz) k hk) (hVZ hcVx)
    have hkS : k ∈ S := by
      have e : k = (k * z) * z⁻¹ := by group
      rw [e]
      exact S.mul_mem (hVxS hcVx) (S.inv_mem (hZS hz))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hkS, hk⟩))
      (Subgroup.mem_sup_right (Subgroup.mem_sup_right hz))
  have hVC₀ : V ⊓ C₀ = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    have : g ∈ (Vx ⊓ Q) ⊓ C₀ :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hC₀V (Subgroup.mem_inf.1 hg).2,
        hVQ (Subgroup.mem_inf.1 hg).1⟩, (Subgroup.mem_inf.1 hg).2⟩
    rw [hdisj] at this
    exact this
  have hMQ : M ⊓ Q ≤ V := by
    intro g hg
    obtain ⟨hgM, hgQ⟩ := Subgroup.mem_inf.1 hg
    have hgM' : g ∈ ((K₁ ⊔ V : Subgroup G) : Set G) := hgM
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K₁ V hKV] at hgM'
    obtain ⟨k, hk, v, hv, rfl⟩ := hgM'
    have hkQ : k ∈ Q := by
      have e : k = (k * v) * v⁻¹ := by group
      rw [e]
      exact Q.mul_mem hgQ (Q.inv_mem (hVQ hv))
    exact V.mul_mem (hQZ (Subgroup.mem_inf.2 ⟨hkQ, hk⟩)) hv
  have hdec : ∀ t ∈ T, ∃ v ∈ V, ∃ k ∈ C₀, v * k = t := by
    intro t ht
    have htS : t ∈ (S : Set G) := hTS ht
    rw [hP2a] at htS
    obtain ⟨v₀, hv₀, q₀, hq₀, rfl⟩ := htS
    have hv₀' : v₀ ∈ (Vx ⊓ Q) ⊔ C₀ := by rw [hsup]; exact hv₀
    obtain ⟨w, hw, c, hc, hwc⟩ := C5.mem_sup_of_commute (A := Vx ⊓ Q) (B := C₀)
      (fun a ha b hb => hVxc a (Subgroup.mem_inf.1 ha).1 b (hC₀V hb)) hv₀'
    have hcq : c * q₀ * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hrk.B_le_normQ (hVxS (hC₀V hc))) q₀).mp hq₀
    have hwq : w * (c * q₀ * c⁻¹) ∈ Q := Q.mul_mem (Subgroup.mem_inf.1 hw).2 hcq
    have hwqT : w * (c * q₀ * c⁻¹) ∈ T := by
      have e : w * (c * q₀ * c⁻¹) = (v₀ * q₀) * c⁻¹ := by rw [hwc]; group
      rw [e]
      exact T.mul_mem ht (T.inv_mem (hC₀T hc))
    refine ⟨w * (c * q₀ * c⁻¹), hMQ (Subgroup.mem_inf.2 ⟨hTM hwqT, hwq⟩), c, hc, ?_⟩
    calc w * (c * q₀ * c⁻¹) * c = w * c * q₀ := by group
      _ = v₀ * q₀ := by rw [← hwc]
  obtain ⟨H₀, hH₀M, hH₀V, hVH⟩ := burnsideC5x_gaschutz_split hVM hVT hTM
    (fun h hh v hv => (Subgroup.mem_normalizer_iff.mp (hMN hh) v).mp hv)
    (hB2.to_le hVS) hVe.1 (hB2.to_le hTS) hidx hC₀T hVC₀ hdec
  have hH₀N : H₀ ≤ Subgroup.normalizer (V : Set G) := hH₀M.trans hMN
  have hMprod : ∀ g ∈ M, ∃ h ∈ H₀, ∃ v ∈ V, g = h * v := by
    intro g hg
    have h2 : g ∈ ((H₀ ⊔ V : Subgroup G) : Set G) := by
      show g ∈ (H₀ ⊔ V : Subgroup G)
      rw [sup_comm, hVH]; exact hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H₀ V hH₀N] at h2
    obtain ⟨h, hh, v, hv, rfl⟩ := h2
    exact ⟨h, hh, v, hv, rfl⟩
  have hZM : ∀ g ∈ M, ∀ z ∈ Z, g * z = z * g := by
    intro g hg z hz
    have hMC : M ≤ Subgroup.centralizer (Z : Set G) := by
      refine sup_le (fun k hk => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
        (fun v hv => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
      · exact (Subgroup.mem_centralizer_iff.mp (hZK hy) k hk).symm
      · exact hVe.1 y (Subgroup.mem_sup_right hy) v hv
    exact (Subgroup.mem_centralizer_iff.mp (hMC hg) z hz).symm
  set L₀ := U ⊔ H₀ with hL₀
  have hL₀M : L₀ ≤ M := sup_le (hUK.trans le_sup_left) hH₀M
  have hKl : ∀ k ∈ K₁, ∃ l ∈ L₀, ∃ z ∈ Z, k = l * z := by
    intro k hk
    obtain ⟨h, hh, v, hv, rfl⟩ := hMprod k (Subgroup.mem_sup_left hk)
    obtain ⟨u, hu, z, hz, rfl⟩ := C5.mem_sup_of_commute hUZ hv
    exact ⟨h * u, L₀.mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu), z, hz,
      by group⟩
  have hconjL : ∀ g ∈ K₁, ∀ y ∈ L₀, g * y * g⁻¹ ∈ L₀ := by
    intro g hg y hy
    obtain ⟨l, hl, z, hz, rfl⟩ := hKl g hg
    have hzy : z * y = y * z := (hZM y (hL₀M hy) z hz).symm
    have e : l * z * y * (l * z)⁻¹ = l * y * l⁻¹ := by
      calc l * z * y * (l * z)⁻¹ = l * (z * y) * z⁻¹ * l⁻¹ := by group
        _ = l * (y * z) * z⁻¹ * l⁻¹ := by rw [hzy]
        _ = l * y * l⁻¹ := by group
    rw [e]
    exact L₀.mul_mem (L₀.mul_mem hl hy) (L₀.inv_mem hl)
  have hN₁ : (L₀.subgroupOf K₁).Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
    (by simpa using hconjL g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hZ2 : IsPGroup 2 ↥Z := hB2.to_le hZS
  have hpg : IsPGroup 2 (↥K₁ ⧸ L₀.subgroupOf K₁) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨l, hl, z, hz, hklz⟩ := hKl (k : G) k.2
      obtain ⟨e, he⟩ := hZ2 ⟨z, hz⟩
      refine ⟨e, ?_⟩
      have hze : z ^ (2 ^ e) = 1 := congrArg Subtype.val he
      have hc : Commute l z := hZM l (hL₀M hl) z hz
      show (((k ^ 2 ^ e : ↥K₁)) : ↥K₁ ⧸ L₀.subgroupOf K₁) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show (k : G) ^ 2 ^ e ∈ L₀
      rw [hklz, hc.mul_pow, hze, mul_one]
      exact L₀.pow_mem hl _
  have hN₁top := hshort.1 (L₀.subgroupOf K₁) hpg
  have hKL : K₁ ≤ L₀ := fun k hk => by
    have : (⟨k, hk⟩ : ↥K₁) ∈ L₀.subgroupOf K₁ := by rw [hN₁top]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hUN : M ≤ Subgroup.normalizer (U : Set G) := by
    refine sup_le (C1.le_normalizer_blockU K₁) (fun v hv => ?_)
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun u hu =>
      hVe.1 u (Subgroup.mem_sup_left hu) v hv)
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
  have hzV : z ∈ V := hQZ (Subgroup.mem_inf.2 ⟨hzQ, hzK⟩)
  have hzL : z ∈ (H₀ ⊔ U : Subgroup G) := by
    rw [sup_comm]; exact hKL hzK
  have hzL' : z ∈ ((H₀ ⊔ U : Subgroup G) : Set G) := hzL
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H₀ U hH₀U] at hzL'
  obtain ⟨h, hh, u, hu, rfl⟩ := hzL'
  have hhV : h ∈ V := by
    have e : h = (h * u) * u⁻¹ := by group
    rw [e]
    exact V.mul_mem hzV (V.inv_mem (Subgroup.mem_sup_left hu))
  have hh1 : h ∈ H₀ ⊓ V := Subgroup.mem_inf.2 ⟨hh, hhV⟩
  rw [hH₀V, Subgroup.mem_bot] at hh1
  rw [hh1]
  simpa using hu

end BurnsideC56Blk

end PartBurnsideC56Blk

section PartBurnsideC56

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

theorem burnsideC56_1to5 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x) :
    burnsideC5x_P1 R K₁ x ∧ burnsideC5x_P2 R K₁ x ∧ burnsideC5x_P3 R K₁ x ∧
      burnsideC5x_P4 R K₁ x ∧ Even (orderOf x) := by
  by_cases h5 : IsAltType K₁ 5
  · exact burnsideC56_a5_1to5 h116 hset hx h5
  · exact burnsideC5x_1to5 h116 hset hx (fun h => absurd h h5)

theorem burnsideC56_h14 (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    (H M₀ TH R : Subgroup G) : burnsideC56_H14 H M₀ TH R := fun _ _ hset hy => by
  obtain ⟨h1, h2, h3, h4, -⟩ := burnsideC56_1to5 h116 hset hy
  exact ⟨h1, h2, h3, h4⟩

theorem burnsideC56_gamma (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    {m : G} (hm : m ∈ M₀)
    (hmY : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) m =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (baum R ⊓ Subgroup.centralizer (K₁ : Set G))) :
    conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = pCoreOf 2 (K₁ ⊔ baum R) ∨
      conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) m = conjSubgroup (pCoreOf 2 (K₁ ⊔ baum R)) x := by
  have hmS : m ∈ Subgroup.normalizer (baum R : Set G) :=
    normalizer_le_normalizer_baum R (hset.hyp1.R_norm hm)
  rcases (burnsideC5h_c54_isChi0Block hset (burnsideC56_b_mem_self TH K₁)).2 with hL | h3 | h5
  · exact burnsideC5x_lin2A3_gamma h116 hset hx (Or.inl hL) hmS hmY
  · exact burnsideC5x_lin2A3_gamma h116 hset hx (Or.inr h3) hmS hmY
  · exact burnsideC56_a5_gamma h116 hset hx h5 hm hmY

theorem burnsideC56_hZ (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} (hset : SetC53 H M₀ TH R K₁) :
    ∀ e ∈ baum R, (∀ u ∈ blockU K₁,
      ⁅u, e⁆ ∈ blockU K₁ ⊓ Subgroup.centralizer (K₁ : Set G)) → e ∈ pCoreOf 2 (K₁ ⊔ baum R) := by
  intro e he hcomm
  obtain ⟨-, -, hQ⟩ := burnsideC56_b_c54 h116 hset (burnsideC56_b_mem_self TH K₁)
  have hcent : (∀ u ∈ blockU K₁, ⁅u, e⁆ = 1) → e ∈ pCoreOf 2 (K₁ ⊔ baum R) := by
    intro h1
    rw [hQ]
    refine ⟨he, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp (h1 u hu)
  rcases (burnsideC5h_c54_isChi0Block hset (burnsideC56_b_mem_self TH K₁)).2 with hL | h3 | h5
  · by_contra hne
    exact hne (hcent fun u hu => burnsideC5x_commZ h116 hset (burnsideC56_b_mem_self TH K₁)
      (Or.inl hL) e he hne u hu (hcomm u hu))
  · by_contra hne
    exact hne (hcent fun u hu => burnsideC5x_commZ h116 hset (burnsideC56_b_mem_self TH K₁)
      (Or.inr h3) e he hne u hu (hcomm u hu))
  · refine hcent fun u hu => ?_
    have h0 : blockU K₁ ⊓ Subgroup.centralizer (K₁ : Set G) = ⊥ :=
      AppC.blockZ_eq_bot_of_alt5 hset.config.chi0.1.1 h5
    have := hcomm u hu
    rw [h0, Subgroup.mem_bot] at this
    exact this

theorem burnsideC56_six (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hs2 : ∃ t ∈ TH, conjByElt t K₁ ≠ K₁) :
    IsSylowTwoOf TH M₀ →
      (∃ t ∈ TH, conjByElt t K₁ ≠ K₁) ∧
      ∃ x' : G, GoodX H M₀ K₁ x' ∧
        x' ∈ Subgroup.normalizer ((TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
          Set G) ∧ x' ^ 2 ∈ TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) := by
  intro hsyl
  obtain ⟨hSN, hUQ, hQeq⟩ := burnsideC56_b_c54 h116 hset (burnsideC56_b_mem_self TH K₁)
  obtain ⟨h1, h2, -, h4, -⟩ := burnsideC56_1to5 h116 hset hx
  exact ⟨hs2, burnsideC56_six_core hset hx hs2 hsyl hUQ hQeq hSN
    (burnsideC5h_c54_four_second as_C_1_11 hset) h1 h2 h4 (burnsideC56_hZ h116 hset)
    (fun m hm hmY => burnsideC56_gamma h116 hset hx hm hmY)⟩

namespace burnsideC56_S7

variable {G : Type} [Group G] [Finite G] {H M₀ TH R K₁ : Subgroup G} {t x : G}
  (h : burnsideC56_S7 H M₀ TH R K₁ t x)
include h

theorem G1b : pCoreOf 2 K₁ ≤ blockU K₁ := by
  rcases (burnsideC5h_c54_isChi0Block h.two.set (burnsideC56_b_mem_self TH K₁)).2 with hL | h3 | h5
  · exact burnsideC56_blk_lin2_pCore h.h116 h.two.set hL h.hx h.Z_elem h.Z_le_CK₁ h.Z_le_S
      (h.V_le_KZ hL) h.QK_le
  · exact ((h.two.set.config.chi0.1.1).alt3_structure h3).1.le
  · exact burnsideC56_blk_a5_pCore h.h116 h.two.set h5 h.hx h.V₁_le_CU₂ h.K₁_le_CU₂
      (fun d hd hdC => h.D₁_inf_CU₂_sq hd hdC)

theorem seven : burnsideC5x_Concl7 H M₀ TH R K₁ x := by
  have hpb : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A ≤
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) :=
    fun _ hK _ hA => burnsideC56_blk_pb h.h116 hK hA
  have hpbeq : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ A : Subgroup G, A ≤ baum R →
      TH ≤ Subgroup.normalizer (A : Set G) →
      (A ⊓ pCoreOf 2 (K ⊔ baum R)).relIndex A =
        (blockU K ⊓ Subgroup.centralizer (A : Set G)).relIndex (blockU K) →
      A ≤ pCoreOf 2 (K ⊔ baum R) ∨ A ⊔ pCoreOf 2 (K ⊔ baum R) = baum R :=
    fun _ hK _ hA hTH heq => burnsideC56_blk_pb_eq h.h116 hK hA hTH heq
  have hb6 : ∀ (K : Subgroup G) (y : G), SetC53 H M₀ TH R K → GoodX H M₀ K y →
      ∃ b ∈ conjSubgroup (blockU K) y,
        blockU K ⊓ Subgroup.centralizer ({b} : Set G) = ⁅blockU K, baum R⁆ :=
    fun _ _ hK hy => burnsideC56_blk_b6 h.h116 hK hy
  have hsc : ∀ K : Subgroup G, SetC53 H M₀ TH R K → ∀ r ∈ R ⊓ Subgroup.normalizer (K : Set G),
      (∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ Subgroup.centralizer (blockU K : Set G)) →
      ∃ s ∈ baum R, s⁻¹ * r ∈ Subgroup.centralizer (blockU K : Set G) :=
    fun _ hK _ hr hrb => burnsideC56_blk_sc h.h116 hK hr hrb
  have hP := h.P_eq hsc (h.A₀_max hpb)
  exact h.concl7 hpb hpbeq hb6 hP (h.CR_eq hP) (h.U_eq_pCore hP h.G1b h.swap.G1b)

end burnsideC56_S7

theorem burnsideC56_s2_concl (h116 : C_1_16) {G : Type} [Group G] [Finite G]
    {H M₀ TH R K₁ : Subgroup G} {x : G} (hset : SetC53 H M₀ TH R K₁) (hx : GoodX H M₀ K₁ x)
    (hs2 : ∃ t ∈ TH, conjByElt t K₁ ≠ K₁) : burnsideC5x_Concl H M₀ TH R K₁ x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := burnsideC56_1to5 h116 hset hx
  obtain ⟨t, ht, hne⟩ := hs2
  exact ⟨h1, h2, h3, h4, h5, burnsideC56_six h116 hset hx ⟨t, ht, hne⟩,
    fun hidx => (⟨⟨hset, ht, hne⟩, h116, burnsideC56_h14 h116 H M₀ TH R, hx, hidx⟩ :
      burnsideC56_S7 H M₀ TH R K₁ t x).seven⟩

section

theorem as_C_5_6
    : C_5_6 :=
  burnsideC5x_C56_of_s2 as_C_1_16 fun _ _ _ _ _ _ _ _ _ hset hx hs2 =>
    burnsideC56_s2_concl as_C_1_16 hset hx hs2

end

end PartBurnsideC56

end CFSG.ASVolI
