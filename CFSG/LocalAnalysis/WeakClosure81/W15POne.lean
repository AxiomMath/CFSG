module

public import CFSG.LocalAnalysis.WeakClosure81.W15EightC
public import CFSG.LocalAnalysis.WeakClosure81.W15POneCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem w15p_commutator_mem_of_relIndex_two {E D : Subgroup G} (hidx : D.relIndex E = 2)
    {m : G} (hmE : m ∈ normalizer (E : Set G)) (hmD : m ∈ normalizer (D : Set G))
    {x : G} (hx : x ∈ E) : ⁅m, x⁆ ∈ D := by
  have hidx' : (D.subgroupOf E).index = 2 := hidx
  have hmx : m * x * m⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hmE x).mp hx
  have key := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨m * x * m⁻¹, hmx⟩)
    (b := ⟨x⁻¹, E.inv_mem hx⟩)).mpr (by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ((Subgroup.mem_normalizer_iff.mp hmD x).symm.trans inv_mem_iff.symm))
  rw [commutatorElement_def]
  exact key

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem relIndex_inf_conjSubgroup_eq_two (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    (hgM : g ∉ M) : (V₀ ⊓ conjSubgroup M g).relIndex V₀ = 2 := by
  have hq : E3.mQuot V (conjSubgroup M g) = 1 := (h.fourteen_five_conj hI hS hg hgM).1
  have hV2 : (conjSubgroup M g).relIndex V = 2 := by
    have hdvd : (conjSubgroup M g).relIndex V ∣ Nat.card ↥V := Subgroup.relIndex_dvd_card _ _
    obtain ⟨n, hn⟩ := h.hyp.isPGroup.exists_card_eq
    rw [hn] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    unfold E3.mQuot at hq
    rw [hk, padicValNat.prime_pow] at hq
    rw [hk, hq]
    norm_num
  have hle := Subgroup.relIndex_le_of_le_right (H := conjSubgroup M g) h.hyp.h6.le
    (by rw [hV2]; norm_num)
  have hne1 : (conjSubgroup M g).relIndex V₀ ≠ 1 := by
    intro h1
    apply h.not_V_le_conj_M hI hS hg hgM
    rw [← h.sup_eq]
    exact sup_le ((h.U_le_inf_conj hg).1.trans inf_le_right) (Subgroup.relIndex_eq_one.1 h1)
  have hne0 : (conjSubgroup M g).relIndex V₀ ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_card (conjSubgroup M g) V₀
    rw [h0, zero_dvd_iff] at hd
    exact (Nat.card_pos (α := ↥V₀)).ne' hd
  rw [Subgroup.inf_relIndex_left]
  omega

theorem commutator_mem_v1Sub15 (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) {m : G} (hm : m ∈ M) {w : G} (hw : w ∈ V₀) :
    ⁅m, w⁆ ∈ v1Sub15 V₀ U := by
  have hmN : m ∈ normalizer (V₀ : Set G) := by
    rw [h.hyp.normalizer₀]
    exact hm
  refine (h.mem_v1Sub15_iff).2 ⟨?_, fun g hg hgM => ?_⟩
  · rw [commutatorElement_def]
    exact V₀.mul_mem ((Subgroup.mem_normalizer_iff.1 hmN w).1 hw) (V₀.inv_mem hw)
  · exact (Subgroup.mem_inf.1 (w15p_commutator_mem_of_relIndex_two
      (h.relIndex_inf_conjSubgroup_eq_two hI hS hg hgM) hmN
      ((h.fourteen_five_conj hI hS hg hgM).2.1 hm) hw)).2

theorem inf_conjSubgroup_eq_v1Sub15 (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    (hgM : g ∉ M) : V₀ ⊓ conjSubgroup M g = v1Sub15 V₀ U := by
  have hN : normalizer (V₀ : Set G) = M := h.hyp.normalizer₀
  have hDeq : nVSub V₀ g = V₀ ⊓ conjSubgroup M g := by
    rw [nVSub, ← E3.conjSubgroup_normalizer, hN]
  have hD : nVSub V₀ g ≠ V₀ := by
    rw [hDeq]
    intro heq
    have h2 := h.relIndex_inf_conjSubgroup_eq_two hI hS hg hgM
    rw [heq, Subgroup.relIndex_self] at h2
    norm_num at h2
  have hB : bSub V₀ g ≠ conjSubgroup V₀ g := by
    intro heq
    apply h.not_conj_V₀_le_M hI hS hg hgM
    rw [← heq, bSub, hN]
    exact inf_le_right
  have hOM : pCoreOf 2 (centralizer (U : Set G)) ≤ normalizer (V₀ : Set G) := by
    rw [hN]
    exact h.pCoreOf_le_S.trans h.S_le_M
  have hOg : conjSubgroup (pCoreOf 2 (centralizer (U : Set G))) g =
      pCoreOf 2 (centralizer (U : Set G)) := by
    ext y
    rw [mem_conjSubgroup_iff]
    exact conj_mem_pCoreOf_iff hg y
  have hcomm : ∀ m ∈ normalizer (V₀ : Set G), ∀ w ∈ V₀,
      ⁅m, w⁆ ∈ pCoreOf 2 (centralizer (U : Set G)) := by
    intro m hm w hw
    rw [hN] at hm
    exact v1Sub15_le_pCoreOf V₀ U (h.commutator_mem_v1Sub15 hI hS hm hw)
  have hle := nVSub_le_of_commutator_mem h.hyp.elemAbelian₀ h.hyp.isTI hD hB hOM hOg hcomm
  refine le_antisymm ?_ (h.v1Sub15_le_inf_conj hg)
  rw [← hDeq]
  exact le_inf inf_le_left hle

end Cex15

theorem w15Eight1_of_namedInputs (hI : NamedInputs15 G) :
    W15Eight1 G := by
  intro M V₀ V U S hS h
  obtain ⟨g, hg, hgM⟩ := SetLike.not_le_iff_exists.1 h.not_le
  rw [← h.inf_conjSubgroup_eq_v1Sub15 hI hS hg hgM]
  unfold E3.mQuot
  rw [h.relIndex_inf_conjSubgroup_eq_two hI hS hg hgM]
  exact padicValNat_self

end CFSG.LocalAnalysis.WeakClosure81
