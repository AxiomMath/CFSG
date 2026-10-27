module

public import CFSG.LocalAnalysis.WeakClosure81.W15EightB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def v1Sub15 (V₀ U : Subgroup G) : Subgroup G :=
  V₀ ⊓ pCoreOf 2 (centralizer (U : Set G))

theorem v1Sub15_le_left (V₀ U : Subgroup G) : v1Sub15 V₀ U ≤ V₀ := inf_le_left

theorem v1Sub15_le_pCoreOf (V₀ U : Subgroup G) :
    v1Sub15 V₀ U ≤ pCoreOf 2 (centralizer (U : Set G)) := inf_le_right

@[expose] def W15Eight1 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M V₀ V U S : Subgroup G, Std15 G → Cex15 M V₀ V U S → E3.mQuot V₀ (v1Sub15 V₀ U) = 1

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem v1Sub15_le_inf_conj (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    v1Sub15 V₀ U ≤ V₀ ⊓ conjSubgroup M g :=
  fun x hx => Subgroup.mem_inf.2 ⟨hx.1, h.pCoreOf_le_conj hg hx.2⟩

theorem mem_v1Sub15_iff (h : Cex15 M V₀ V U S) {x : G} :
    x ∈ v1Sub15 V₀ U ↔
      x ∈ V₀ ∧ ∀ g ∈ centralizer (U : Set G), g ∉ M → x ∈ conjSubgroup M g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := h.hyp
  constructor
  · intro hx
    exact ⟨hx.1, fun g hg _ => (h.v1Sub15_le_inf_conj hg hx).2⟩
  · rintro ⟨hxV₀, hconj⟩
    refine Subgroup.mem_inf.2 ⟨hxV₀, ?_⟩
    refine mem_pCoreOf_of_forall_closure_isPGroup (h.V₀_le_centralizer hxV₀) fun g hg => ?_
    have hyM : g * x * g⁻¹ ∈ M := by
      by_cases hgM : g ∈ M
      · exact M.mul_mem (M.mul_mem hgM (h.hyp.le_M (hH.h6.le hxV₀))) (M.inv_mem hgM)
      · exact mem_conjSubgroup_iff.1 (hconj g hg hgM)
    have hyV : g * x * g⁻¹ ∈ conjSubgroup V₀ g⁻¹ := by
      rw [mem_conjSubgroup_iff, show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group]
      exact hxV₀
    have hzp : IsPGroup 2 (Subgroup.zpowers (g * x * g⁻¹)) :=
      (E3.isPGroup_conjSubgroup (hH.isPGroup.to_le hH.h6.le) g⁻¹).to_le
        (Subgroup.zpowers_le.mpr hyV)
    have hnorm : Subgroup.zpowers (g * x * g⁻¹) ≤ normalizer (V₀ : Set G) := by
      rw [hH.normalizer₀]
      exact Subgroup.zpowers_le.mpr hyM
    have hsup : IsPGroup 2 ↥(Subgroup.zpowers (g * x * g⁻¹) ⊔ V₀ : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hzp (hH.isPGroup.to_le hH.h6.le) hnorm
    refine hsup.to_le ((Subgroup.closure_le (K := Subgroup.zpowers (g * x * g⁻¹) ⊔ V₀)).mpr ?_)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact Subgroup.mem_sup_right hxV₀
    · rw [hy]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem v1Sub15_ne_bot (hS : Std15 G) (h : Cex15 M V₀ V U S) : v1Sub15 V₀ U ≠ ⊥ := by
  intro hbot
  have hne : V₀ ⊓ centralizer (S : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot h.hyp.elemAbelian₀ h.hyp.ne_bot (h.isCalH hS) h.isSylowIn_inf
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ v1Sub15 V₀ U :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, h.inf_centralizer_le_pCoreOf hS hx⟩
  rw [hbot] at hx'
  exact hx'

theorem normal_v1Sub15 (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) : M ≤ normalizer (v1Sub15 V₀ U : Set G) := by
  have hfwd : ∀ m ∈ M, ∀ x ∈ v1Sub15 V₀ U, m * x * m⁻¹ ∈ v1Sub15 V₀ U := by
    intro m hm x hx
    obtain ⟨hxV₀, hconj⟩ := (h.mem_v1Sub15_iff).1 hx
    have hmN : m ∈ normalizer (V₀ : Set G) := by
      rw [h.hyp.normalizer₀]
      exact hm
    refine (h.mem_v1Sub15_iff).2 ⟨(Subgroup.mem_normalizer_iff.1 hmN x).1 hxV₀, fun g hg hgM => ?_⟩
    have hD : M ≤ normalizer ((V₀ ⊓ conjSubgroup M g : Subgroup G) : Set G) :=
      (h.fourteen_five_conj hI hS hg hgM).2.1
    have hxD : x ∈ V₀ ⊓ conjSubgroup M g := Subgroup.mem_inf.2 ⟨hxV₀, hconj g hg hgM⟩
    exact (Subgroup.mem_inf.1 ((Subgroup.mem_normalizer_iff.1 (hD hm) x).1 hxD)).2
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hfwd m hm x hx, fun hx => ?_⟩
  have h1 := hfwd m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using h1

theorem commutator_cTilde_le_v1Sub15 (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) : ⁅F11.CTilde M V₀ V, V⁆ ≤ v1Sub15 V₀ U := by
  refine Subgroup.commutator_le.2 fun c hc v hv => ?_
  refine (h.mem_v1Sub15_iff).2 ⟨?_, fun g hg hgM => ?_⟩
  · rw [commutatorElement_def]
    exact (FourteenTwo.mem_cTilde_iff_comm.1 hc).2.2 v hv
  · exact (Subgroup.mem_inf.1 ((h.fourteen_five_conj hI hS hg hgM).2.2
      (Subgroup.commutator_mem_commutator hc hv))).2

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
