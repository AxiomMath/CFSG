module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepFrame
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
public import CFSG.LocalAnalysis.StandardType.GGTBTorCartan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggAutomizer_sub_mem_span {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAX : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) {g : MulAut ↥Bs}
    (hg : g ∈ ggAutomizer X Bs) (w : V) :
    ggLin (p := p) ι g w - w ∈ Submodule.span (ZMod p) (Set.range h) := by
  rw [hAX] at hg
  refine Subgroup.closure_induction (p := fun g _ => ∀ w : V, ggLin (p := p) ι g w - w ∈
      Submodule.span (ZMod p) (Set.range h)) ?_ ?_ ?_ ?_ hg w
  · rintro _ ⟨i, rfl⟩ w
    rw [hφ i w, show w - α i w • h i - w = -(α i w • h i) by abel]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · intro w
    simp
  · intro g k _ _ hg hk w
    have h1 := hg (ggLin (p := p) ι k w)
    have h2 := hk w
    have hmul : ggLin (p := p) ι (g * k) w = ggLin (p := p) ι g (ggLin (p := p) ι k w) := by
      rw [map_mul]
      rfl
    have : ggLin (p := p) ι (g * k) w - w = (ggLin (p := p) ι g (ggLin (p := p) ι k w) -
        ggLin (p := p) ι k w) + (ggLin (p := p) ι k w - w) := by
      rw [hmul]
      abel
    rw [this]
    exact Submodule.add_mem _ h1 h2
  · intro g _ hg w
    have h1 := hg (ggLin (p := p) ι g⁻¹ w)
    have hinv : ggLin (p := p) ι g (ggLin (p := p) ι g⁻¹ w) = w := by
      have h0 : ggLin (p := p) ι (g * g⁻¹) w = ggLin (p := p) ι g (ggLin (p := p) ι g⁻¹ w) := by
        rw [map_mul]
        rfl
      rw [← h0, mul_inv_cancel, map_one]
      rfl
    have : ggLin (p := p) ι g⁻¹ w - w = -(ggLin (p := p) ι g (ggLin (p := p) ι g⁻¹ w) -
        ggLin (p := p) ι g⁻¹ w) := by
      rw [hinv]
      abel
    rw [this]
    exact Submodule.neg_mem _ h1

theorem ggBstarComm_le_span {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAX : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) {c : ↥Bs}
    (hc : c ∈ ggBstarComm X Bs) :
    ι (Additive.ofMul c) ∈ Submodule.span (ZMod p) (Set.range h) := by
  refine Subgroup.closure_induction (p := fun c _ => ι (Additive.ofMul c) ∈
      Submodule.span (ZMod p) (Set.range h)) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨b, φ', hφ', rfl⟩
    have h1 := ggAutomizer_sub_mem_span hφ hAX hφ' (ι (Additive.ofMul b))
    rw [ggLin_apply_ofMul] at h1
    have : ι (Additive.ofMul (b⁻¹ * φ' b)) = ι (Additive.ofMul (φ' b)) - ι (Additive.ofMul b) := by
      rw [ofMul_mul, ofMul_inv, map_add, map_neg]
      abel
    rw [this]
    exact h1
  · simp
  · intro a b _ _ ha hb
    rw [ofMul_mul, map_add]
    exact Submodule.add_mem _ ha hb
  · intro a _ ha
    rw [ofMul_inv, map_neg]
    exact Submodule.neg_mem _ ha

theorem ggIndep_x_notComm_of_dep (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 5 ≤ N)
    (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h) :
    x ∉ (ggBstarComm L Bs).map Bs.subtype := by
  classical
  haveI : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have F := ggXDatumA_frame hFix hp2 hH hx hN hpN e hML hCL hφ hpair hAL hdep
  have hnot := (ggDepA_relation F).2.1
  rintro ⟨c, hc, hcx⟩
  have hcx' : c = ⟨x, hx⟩ := Subtype.ext hcx
  have hmem := ggBstarComm_le_span hφ hAL hc
  rw [hcx'] at hmem
  apply hnot
  have hr : Set.range (fun i : Fin (N - 1) => h (e i)) = Set.range h := e.surjective.range_comp h
  rw [hr]
  exact hmem

theorem ggDep_notmem_span_nofix {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hdep : ¬ LinearIndependent (ZMod p) h) (hx : x ≠ 0) (hker : ∀ i, α i x = 0) :
    x ∉ Submodule.span (ZMod p) (Set.range h) := by
  classical
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  have hdA : ∀ i, ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * d k = 0 :=
    fun i => l6aF_A_mul_d hpN i
  have hd0 : d ≠ 0 := by
    intro hz
    have h1 := congrFun hz ⟨0, by omega⟩
    simp [d] at h1
  have hrel : ∑ i, d i • h i = 0 := by
    rw [Fintype.linearIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨c, hcsum, i0, hi0⟩ := hdep
    have hc0 : c ≠ 0 := fun hz => hi0 (by rw [hz]; rfl)
    have hcA : ∀ i, ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * c k = 0 := by
      intro i
      have hh := congrArg (α i) hcsum
      simp only [map_sum, map_smul, hpair, smul_eq_mul, map_zero] at hh
      calc ∑ k, (CartanMatrix.A (N - 1) i k : ZMod p) * c k
          = ∑ k, c k * (CartanMatrix.A (N - 1) i k : ZMod p) :=
            Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ = 0 := hh
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one c d hcA hdA hc0
    rw [hl]
    calc ∑ i, (l • c) i • h i
        = ∑ i, l • (c i • h i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul, mul_smul]
      _ = l • ∑ i, c i • h i := by rw [Finset.smul_sum]
      _ = 0 := by rw [hcsum, smul_zero]
  intro hmem
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hmem
  have ha0 : a ≠ 0 := by
    intro hz
    apply hx
    rw [← ha, hz]
    simp
  have haA : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * a k = 0 := by
    intro j
    have hh := congrArg (α j) ha
    simp only [map_sum, map_smul, hpair, smul_eq_mul, hker j] at hh
    calc ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * a k
        = ∑ k, a k * (CartanMatrix.A (N - 1) j k : ZMod p) :=
          Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = 0 := hh
  obtain ⟨l, hl⟩ := ggCartanA_ker_le_one a d haA hdA ha0
  have hl0 : l ≠ 0 := by
    intro hz
    apply hd0
    rw [hl, hz, zero_smul]
  apply hx
  rw [← ha]
  have hdiv : a = l⁻¹ • d := by
    rw [hl, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  rw [hdiv]
  calc ∑ i, (l⁻¹ • d) i • h i
      = ∑ i, l⁻¹ • (d i • h i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, mul_smul]
    _ = l⁻¹ • ∑ i, d i • h i := by rw [Finset.smul_sum]
    _ = 0 := by rw [hrel, smul_zero]

end CFSG.StandardType

end
