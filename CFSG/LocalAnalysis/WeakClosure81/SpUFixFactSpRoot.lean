module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsC
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpElt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical

variable {k : ℕ} {F : Type} [Field F]

@[expose] noncomputable def spUFixRootSp (v : Fin k ⊕ Fin k → F) : Subgroup ↥(StatedSp k F) :=
  Subgroup.closure (Set.range (spTransvection v))

theorem mem_spUFixRootSp {v : Fin k ⊕ Fin k → F} {x : ↥(StatedSp k F)} :
    x ∈ spUFixRootSp v ↔ ∃ t : F, x = spTransvection v t := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨t, rfl⟩ := hy
        exact ⟨t, rfl⟩
    | one => exact ⟨0, (borel86_spn_spTransvection_param_zero v).symm⟩
    | mul y z hy hz ihy ihz =>
        obtain ⟨s, rfl⟩ := ihy
        obtain ⟨t, rfl⟩ := ihz
        exact ⟨s + t, spConf_transvection_mul v s t⟩
    | inv y hy ihy =>
        obtain ⟨t, rfl⟩ := ihy
        exact ⟨-t, spTransvection_inv v t⟩
  · rintro ⟨t, rfl⟩
    exact Subgroup.subset_closure ⟨t, rfl⟩

theorem spUFixRootSp_smul {c : F} (hc : c ≠ 0) (v : Fin k ⊕ Fin k → F) :
    spUFixRootSp (c • v) = spUFixRootSp v := by
  ext x
  rw [mem_spUFixRootSp, mem_spUFixRootSp]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨c * c * t, CFSG.RankThree.PartOne.CTP.spTransvection_smul c v t⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t / (c * c), ?_⟩
    rw [CFSG.RankThree.PartOne.CTP.spTransvection_smul,
      mul_div_cancel₀ t (mul_ne_zero hc hc)]

theorem exists_smul_of_spUFixRootSp_eq {v w : Fin k ⊕ Fin k → F} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : spUFixRootSp v = spUFixRootSp w) : ∃ c : F, w = c • v := by
  have hwmem : spTransvection w 1 ∈ spUFixRootSp v := by
    rw [h]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  obtain ⟨t, ht⟩ := (mem_spUFixRootSp (v := v)).1 hwmem
  obtain ⟨μ, hμ, hμeq, -⟩ :=
    borel86_spn_exists_smul_of_spTransvection_eq (a := w) (b := v) hw one_ne_zero ht.symm
  refine ⟨μ⁻¹, ?_⟩
  rw [hμeq, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem mul_self_of_mem_spUFixRootSp [CharP F 2] {v : Fin k ⊕ Fin k → F} {x : ↥(StatedSp k F)}
    (hx : x ∈ spUFixRootSp v) : x * x = 1 := by
  obtain ⟨t, rfl⟩ := (mem_spUFixRootSp (v := v)).1 hx
  rw [spConf_transvection_mul, CharTwo.add_self_eq_zero,
    borel86_spn_spTransvection_param_zero]

theorem commute_of_mem_spUFixRootSp {v w : Fin k ⊕ Fin k → F} (hvw : spForm k F v w = 0)
    {x y : ↥(StatedSp k F)} (hx : x ∈ spUFixRootSp v) (hy : y ∈ spUFixRootSp w) :
    x * y = y * x := by
  obtain ⟨s, rfl⟩ := (mem_spUFixRootSp (v := v)).1 hx
  obtain ⟨t, rfl⟩ := (mem_spUFixRootSp (v := w)).1 hy
  exact kFacts_spTransvection_comm_of_spForm_eq_zero hvw s t

theorem map_conj_spUFixRootSp (x : ↥(StatedSp k F)) (v : Fin k ⊕ Fin k → F) :
    (spUFixRootSp v).map (MulAut.conj x).toMonoidHom = spUFixRootSp (spEnd x v) := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rw [mem_spUFixRootSp] at hz ⊢
    obtain ⟨t, rfl⟩ := hz
    refine ⟨t, ?_⟩
    rw [← hyz]
    change x * spTransvection v t * x⁻¹ = spTransvection (spEnd x v) t
    exact CFSG.RankThree.PartOne.CTP.spTransvection_conj x v t
  · intro hy
    rw [mem_spUFixRootSp] at hy
    obtain ⟨t, rfl⟩ := hy
    rw [Subgroup.mem_map]
    exact ⟨spTransvection v t, (mem_spUFixRootSp).2 ⟨t, rfl⟩,
      by
        change x * spTransvection v t * x⁻¹ = spTransvection (spEnd x v) t
        exact CFSG.RankThree.PartOne.CTP.spTransvection_conj x v t⟩

theorem exists_spUFixRootSp_eq_map {a v : Fin k ⊕ Fin k → F} (ha : a ≠ 0) (hv : v ≠ 0) :
    ∃ x : ↥(StatedSp k F),
      spUFixRootSp v = (spUFixRootSp a).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := exists_spEnd_eq ha hv
  exact ⟨x, by rw [map_conj_spUFixRootSp, hx]⟩

theorem spUFix_exists_spForm_eq_zero_not_smul (hk : 2 ≤ k) {a : Fin k ⊕ Fin k → F}
    (ha : a ≠ 0) : ∃ v : Fin k ⊕ Fin k → F, spForm k F a v = 0 ∧ ∀ c : F, v ≠ c • a := by
  let f : (Fin k ⊕ Fin k → F) →ₗ[F] F := spForm k F a
  have hdim : Module.finrank F (Fin k ⊕ Fin k → F) = 2 * k := by
    rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
    omega
  have hrange : Module.finrank F (LinearMap.range f) ≤ 1 := by
    calc
      Module.finrank F (LinearMap.range f) ≤ Module.finrank F F := Submodule.finrank_le _
      _ = 1 := Module.finrank_self F
  have hker : 2 * k - 1 ≤ Module.finrank F (LinearMap.ker f) := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hdim] at h
    omega
  have hnot : ¬ (LinearMap.ker f : Set (Fin k ⊕ Fin k → F)) ⊆
      (Submodule.span F {a} : Set (Fin k ⊕ Fin k → F)) := by
    intro hle
    have hle' : LinearMap.ker f ≤ Submodule.span F {a} := fun x hx => hle hx
    have h1 : Module.finrank F (LinearMap.ker f) ≤ 1 := by
      calc
        Module.finrank F (LinearMap.ker f) ≤ Module.finrank F (Submodule.span F {a}) :=
          Submodule.finrank_mono hle'
        _ = 1 := by simpa using finrank_span_singleton (K := F) ha
    omega
  rw [Set.not_subset] at hnot
  obtain ⟨v, hvker, hvspan⟩ := hnot
  refine ⟨v, LinearMap.mem_ker.mp hvker, fun c hc => hvspan ?_⟩
  rw [hc]
  exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end
