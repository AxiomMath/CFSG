module

public import CFSG.Quasithin.EmptyFaithful.S151TCQ
public import CFSG.Quasithin.Vol2.Ch10SecKL7a

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch10.SecB.KL7 (act act_apply invariant_eq_bot_or_top M3 SL32)
open scoped commutatorElement

theorem case5_c134CQ_eq_blockZ {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hRN : R ≤ Subgroup.normalizer (L : Set G)) :
    c134CQ (L ⊔ R) L = blockZ L := by
  unfold c134CQ blockZ
  rw [c134Q_eq_blockU hperf hRN]

theorem irreducible_of_isMatrixBlockType_three {G : Type} [Group G] {L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (blockU L : Set G))
    (h : IsMatrixBlockType L (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) :
    blockZ L < blockU L ∧ ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L →
      L ≤ Subgroup.normalizer (W : Set G) → W = blockZ L ∨ W = blockU L := by
  obtain ⟨α, hα, -, β, hβ, hβker, hβeq⟩ := h
  have hZU : blockZ L ≤ blockU L := inf_le_left
  refine ⟨lt_of_le_of_ne hZU fun hZ => ?_, fun W hZW hWU hLW => ?_⟩
  ·
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd (Pi.single 0 1))
    have hu1 : β u = 1 := by
      refine MonoidHom.mem_ker.1 ?_
      rw [hβker, hZ]
      exact Subgroup.mem_subgroupOf.2 u.2
    rw [hu1] at hu
    have h0 := congrFun (congrArg Multiplicative.toAdd hu) 0
    revert h0
    decide
  ·
    let K : Subgroup M3 := (W.subgroupOf (blockU L)).map β
    have hKinv : ∀ γ : SL32, ∀ x ∈ K, act γ x ∈ K := by
      rintro γ x ⟨w, hw, rfl⟩
      obtain ⟨ℓ, rfl⟩ := hα γ
      have hℓU : (ℓ : G) * w * (ℓ : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.1 (hL ℓ.2) (w : G)).1 w.2
      have hℓW : (ℓ : G) * w * (ℓ : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (hLW ℓ.2) (w : G)).1 (Subgroup.mem_subgroupOf.1 hw)
      refine ⟨⟨(ℓ : G) * w * (ℓ : G)⁻¹, hℓU⟩, Subgroup.mem_subgroupOf.2 hℓW, ?_⟩
      rw [act_apply, ← hβeq ℓ w ⟨(ℓ : G) * w * (ℓ : G)⁻¹, hℓU⟩ rfl]
      rfl
    rcases invariant_eq_bot_or_top K hKinv with hbot | htop
    ·
      left
      refine le_antisymm (fun g hg => ?_) hZW
      have hgU : g ∈ blockU L := hWU hg
      have h1 : β ⟨g, hgU⟩ ∈ K := ⟨⟨g, hgU⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : (⟨g, hgU⟩ : ↥(blockU L)) ∈ β.ker := MonoidHom.mem_ker.2 h1
      rw [hβker] at h2
      exact Subgroup.mem_subgroupOf.1 h2
    ·
      right
      refine le_antisymm hWU (fun g hg => ?_)
      have h1 : β ⟨g, hg⟩ ∈ K := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨w, hw, hwg⟩ := h1
      have h2 : (⟨g, hg⟩ : ↥(blockU L)) * w⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwg]
        exact mul_inv_cancel _
      rw [hβker] at h2
      have h3 : g * (w : G)⁻¹ ∈ blockZ L := Subgroup.mem_subgroupOf.1 h2
      have h4 : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hw
      simpa using W.mul_mem (hZW h3) h4

theorem isMatrixBlockType_three_of_case5 {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (h5 : ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α ∧
      Nat.card ↥(c134CQ (L ⊔ R) L) = 2 ∧
      IsSumOfNaturalModulesVia L (c134Q (L ⊔ R) L) (c134CQ (L ⊔ R) L) α false 1) :
    IsMatrixBlockType L (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
  obtain ⟨α, hα, -, hsum⟩ := h5
  rw [case5_c134CQ_eq_blockZ hperf hRN, c134Q_eq_blockU hperf hRN] at hsum
  exact (isMatrixBlockType_iff_isNaturalSection L _ hsum.1).2
    ((isNaturalSection_iff_isSumOfNaturalModules_one _ _ hsum.2.1).2 ⟨α, hα.1, hα.2, hsum⟩)

theorem case5_irreducible {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (h5 : ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α ∧
      Nat.card ↥(c134CQ (L ⊔ R) L) = 2 ∧
      IsSumOfNaturalModulesVia L (c134Q (L ⊔ R) L) (c134CQ (L ⊔ R) L) α false 1) :
    blockZ L < blockU L ∧ ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L →
      L ≤ Subgroup.normalizer (W : Set G) → W = blockZ L ∨ W = blockU L := by
  have hmat := isMatrixBlockType_three_of_case5 hperf hRN h5
  obtain ⟨α, -, -, hsum⟩ := h5
  rw [case5_c134CQ_eq_blockZ hperf hRN, c134Q_eq_blockU hperf hRN] at hsum
  exact irreducible_of_isMatrixBlockType_three hsum.1 hmat

end CFSG.Quasithin.S151TC
