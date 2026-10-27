module

public import CFSG.RankThree.PartOne.K1320.RowData
public import CFSG.RankThree.PartOne.K1320.Assemble
public import CFSG.RankThree.PartOne.K1320.RowDistinct

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KF1320Sp' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f → E = A → ¬ IsLThreeTypeAt p L →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
    ∀ t₁ t₂ t₃ : MulAut E, Chain3 p E L t₁ t₂ t₃ →
      ∃ K₁ K₂ K₃ : Subgroup G, KFKt p E f t₁ K₁ ∧ KFKt p E f t₂ K₂ ∧ KFKt p E f t₃ K₃ ∧
        (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) ∧
        CentrallyLThree f ↥(K₃ ⊔ K₂) ∧ StatedClassicalModel ↥(K₂ ⊔ K₁) .PSp 2 2 f

theorem kf1320Sp'_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (h133 : S13K.KF133Two)
    (hDist : S13K.KFCommDistinct) (hRow7 : Row7Data) : KF1320Sp' := by
  intro G _ _ p A c L E f h hF hF13 hT hf1 hpf hmodel hEA _ hweyl t₁ t₂ t₃ hch
  obtain ⟨eX⟩ := hweyl
  have hp := h.prime
  obtain ⟨z, hz⟩ := exists_inverter h hF13 eX
  obtain ⟨hAt, hcen, hgen⟩ := hRow7 G p A c L E f h hF hF13 hT hEA hf1 hpf hmodel
  have hn8 : ¬ ∃ f' : ℕ, 1 ≤ f' ∧ p ∣ 2 ^ f' + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f' :=
    fun ⟨_, _, _, h4⟩ => not_psp_two_and_psl_four hmodel h4
  obtain ⟨w, hw, hs₁, hs₁L, hs₂, hs₂L, hord⟩ := chain_conj_into_L hp hch
  have hKA₁ : KFAt p E f t₁ := KFAt.of_conj hw (hAt _ hs₁ hs₁L)
  have hKA₂ : KFAt p E f t₂ := KFAt.of_conj hw (hAt _ hs₂ hs₂L)
  obtain ⟨w₃, hw₃, ht₃⟩ := chain_t₃_conj hch
  have hKA₃ : KFAt p E f t₃ := by rw [ht₃]; exact hKA₂.conj hw₃
  refine ⟨kZero p E t₁, kZero p E t₂, kZero p E t₃, kfKt_of_kfAt hKA₁, kfKt_of_kfAt hKA₂,
    kfKt_of_kfAt hKA₃, ?_, ?_, ?_⟩
  · exact chain_comm_clause hS h133 hDist h hF hF13 hT hEA hn8 hz hch hw hs₁ hs₁L
      (hAt _ hs₁ hs₁L) hKA₃ hpf
  · exact chain_pair_L3 hGA hS h133 h hF hF13 hT hEA hn8 hz hch hKA₂
      (PAIR22.pairLift_of_kfAt hKA₃)
  · have hLmod : StatedClassicalModel ↥L .PSp 2 2 f :=
      statedClassicalModel_of_equiv
        ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot) hmodel
    exact chain_sup_model hw (hgen _ hs₁ hs₁L _ hs₂ hs₂L hord) hLmod

end CFSG.RankThree.PartOne.K1320
