module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def rStarMV (M V : Subgroup G) : ℕ∞ :=
  ⨅ U ∈ {U : Subgroup G | U ≤ V ∧ ¬ normalizer (U : Set G) ≤ M}, (E3.mQuot V U : ℕ∞)

theorem rStarMV_le {M V U : Subgroup G} (hUV : U ≤ V) (hN : ¬ normalizer (U : Set G) ≤ M) :
    rStarMV M V ≤ E3.mQuot V U :=
  iInf₂_le U ⟨hUV, hN⟩

@[expose] def H3Cond (n : ℕ) (M V : Subgroup G) (g : G) : Prop :=
  ∀ A : Subgroup G, (∃ x : G, A = conjSubgroup V x) →
    V ⊓ conjSubgroup V g < V ⊓ A →
    max (E3.mQuot A M) (E3.mQuot V (normalizer (A : Set G))) < n →
    ⁅A ⊓ M, V ⊓ normalizer (A : Set G)⁆ ≤ V ⊓ conjSubgroup V g

structure Hyp612Sym (n : ℕ) (M V : Subgroup G) (g : G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  normalizer_eq : normalizer (V : Set G) = M
  lt_rStar : (n : ℕ∞) < rStarMV M V
  inCalO : InCalO n M ⊥ V g
  centralizer_le : V ⊓ centralizer ((BOf M V g : Subgroup G) : Set G) ≤ conjSubgroup V g
  mem_of_commutator_mem : ∀ b ∈ BOf M V g, b ∉ V → ∀ v ∈ V,
    ⁅v, b⁆ ∈ V ⊓ conjSubgroup V g → v ∈ conjSubgroup M g
  centralizer_le' : conjSubgroup V g ⊓ centralizer ((UOf M V g : Subgroup G) : Set G) ≤ V
  mem_of_commutator_mem' : ∀ a ∈ UOf M V g, a ∉ conjSubgroup V g → ∀ w ∈ conjSubgroup V g,
    ⁅w, a⁆ ∈ V ⊓ conjSubgroup V g → w ∈ M

structure Hyp612H3 (n : ℕ) (M V : Subgroup G) (g : G) : Prop extends Hyp612Sym n M V g where
  h3 : H3Cond n M V g

structure Hyp612 (n : ℕ) (M V : Subgroup G) (g : G) : Prop extends Hyp612H3 n M V g where
  not_inCalO1 : ¬ InCalO 1 M ⊥ V g

theorem inCalO_swap {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : InCalO n M V₀ V g) :
    InCalO n (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹ := by
  obtain ⟨hF, hD⟩ := h
  exact ⟨(oFirst_swap n M V₀ V g).2 hD,
    by simpa only [ODual, OFirst, conjSubgroup_conjSubgroup_inv, ne_eq,
      conjSubgroup_eq_bot_iff] using hF⟩

private theorem rStarMV_conjSubgroup_le (M V : Subgroup G) (g : G) :
    rStarMV (conjSubgroup M g) (conjSubgroup V g) ≤ rStarMV M V := by
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hN⟩ := hU
  have h2 : ¬ normalizer (conjSubgroup U g : Set G) ≤ conjSubgroup M g := by
    intro h
    apply hN
    rw [← conjSubgroup_normalizer] at h
    have := conjSubgroup_mono h g⁻¹
    rwa [conjSubgroup_conjSubgroup_inv, conjSubgroup_conjSubgroup_inv] at this
  have hle := rStarMV_le (conjSubgroup_mono hUV g) h2
  rwa [E3.mQuot_conjSubgroup] at hle

theorem rStarMV_conjSubgroup (M V : Subgroup G) (g : G) :
    rStarMV (conjSubgroup M g) (conjSubgroup V g) = rStarMV M V := by
  refine le_antisymm (rStarMV_conjSubgroup_le M V g) ?_
  have h := rStarMV_conjSubgroup_le (conjSubgroup M g) (conjSubgroup V g) g⁻¹
  rwa [conjSubgroup_conjSubgroup_inv, conjSubgroup_conjSubgroup_inv] at h

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem swap (h : Hyp612Sym n M V g) :
    Hyp612Sym n (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by
  have hi := inCalO_swap h.inCalO
  rw [E3.conjSubgroup_bot] at hi
  refine ⟨CFSG.Quasithin.E3.isElemAbelian_conjSubgroup h.elemAbelian g, ?_, ?_, hi,
    ?_, ?_, ?_, ?_⟩
  · rw [← conjSubgroup_normalizer, h.normalizer_eq]
  · rw [rStarMV_conjSubgroup]; exact h.lt_rStar
  · rw [BOf_swap, conjSubgroup_conjSubgroup_inv]; exact h.centralizer_le'
  · intro b hb hbV v hv hc
    rw [BOf_swap] at hb
    rw [conjSubgroup_conjSubgroup_inv, inf_comm] at hc
    rw [conjSubgroup_conjSubgroup_inv]
    exact h.mem_of_commutator_mem' b hb hbV v hv hc
  · rw [UOf_swap, conjSubgroup_conjSubgroup_inv]; exact h.centralizer_le
  · intro a ha haV w hw hc
    rw [UOf_swap] at ha
    rw [conjSubgroup_conjSubgroup_inv] at haV hw hc
    rw [inf_comm] at hc
    exact h.mem_of_commutator_mem a ha haV w hw hc

theorem le_M (h : Hyp612Sym n M V g) : V ≤ M := by
  rw [← h.normalizer_eq]
  exact Subgroup.le_normalizer

theorem conjV_le_conjM (h : Hyp612Sym n M V g) : conjSubgroup V g ≤ conjSubgroup M g :=
  conjSubgroup_mono h.le_M g

theorem not_conjV_le_M (h : Hyp612Sym n M V g) : ¬ conjSubgroup V g ≤ M :=
  h.inCalO.1.1

theorem not_V_le_conjM (h : Hyp612Sym n M V g) : ¬ V ≤ conjSubgroup M g :=
  h.inCalO.2.1

theorem mQuot_U_le (h : Hyp612Sym n M V g) : E3.mQuot V (UOf M V g) ≤ n := by
  have h1 := h.inCalO.1.2.1
  unfold E3.mQuot at h1 ⊢
  unfold UOf
  rwa [Subgroup.inf_relIndex_left]

theorem NOf_eq_inf (h : Hyp612Sym n M V g) : NOf M V g = V ⊓ conjSubgroup V g :=
  NOf_eq M V g h.le_M

theorem normalizer_U_le (h : Hyp612Sym n M V g) :
    normalizer ((UOf M V g : Subgroup G) : Set G) ≤ M := by
  by_contra hN
  have h1 := rStarMV_le (inf_le_left : UOf M V g ≤ V) hN
  have h2 : ((E3.mQuot V (UOf M V g) : ℕ) : ℕ∞) ≤ n := by exact_mod_cast h.mQuot_U_le
  exact absurd h.lt_rStar (not_lt.2 (h1.trans h2))

end Hyp612Sym

end CFSG.LocalAnalysis.WeakClosure81
