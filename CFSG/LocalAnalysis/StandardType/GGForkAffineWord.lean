module

public import CFSG.LocalAnalysis.StandardType.GGForkAffineDatum

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Word

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {N : Type} [Fintype N]
  [DecidableEq N] {X : Matrix N N ℤ}

private lemma sum_ite_root_eq (D : GGReflDatum p ι X) (j : N) :
    (∑ i, ((if i = j then 1 else 0 : ℤ) : ZMod p) • D.root i) = D.root j := by
  have hcongr : (∑ i, ((if i = j then 1 else 0 : ℤ) : ZMod p) • D.root i)
      = ∑ i, (if i = j then (1 : ZMod p) • D.root i else 0) :=
    Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  rw [hcongr, Finset.sum_ite_eq' Finset.univ j]
  simp

private lemma sum_ite_coroot_eq (D : GGReflDatum p ι X) (j : N) :
    (∑ i, ((if i = j then 1 else 0 : ℤ) : ZMod p) • D.coroot i) = D.coroot j := by
  have hcongr : (∑ i, ((if i = j then 1 else 0 : ℤ) : ZMod p) • D.coroot i)
      = ∑ i, (if i = j then (1 : ZMod p) • D.coroot i else 0) :=
    Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  rw [hcongr, Finset.sum_ite_eq' Finset.univ j]
  simp

private lemma sum_ggStepRoot_eq (D : GGReflDatum p ι X) (k : N) (c : N → ℤ) :
    (∑ i, (ggStepRoot X k c i : ZMod p) • D.root i)
      = (∑ i, (c i : ZMod p) • D.root i)
        - ((∑ i, c i * X i k : ℤ) : ZMod p) • D.root k := by
  set S : ZMod p := ((∑ j, c j * X j k : ℤ) : ZMod p) with hS
  have hstep : ∀ i, (ggStepRoot X k c i : ZMod p)
      = (c i : ZMod p) - (if i = k then S else 0) := by
    intro i
    rw [hS]
    unfold ggStepRoot
    rw [Int.cast_sub]
    split_ifs <;> simp
  calc (∑ i, (ggStepRoot X k c i : ZMod p) • D.root i)
      = ∑ i, (((c i : ZMod p) - (if i = k then S else 0)) • D.root i) :=
        Finset.sum_congr rfl fun i _ => by rw [hstep i]
    _ = (∑ i, (c i : ZMod p) • D.root i) - ∑ i, (if i = k then S else 0) • D.root i := by
        rw [show (∑ i, (↑(c i) - if i = k then S else 0) • D.root i)
              = ∑ i, ((c i : ZMod p) • D.root i
                  - (if i = k then S else 0) • D.root i) from
            Finset.sum_congr rfl fun i _ =>
              sub_smul (c i : ZMod p) (if i = k then S else 0) (D.root i)]
        rw [Finset.sum_sub_distrib]
    _ = (∑ i, (c i : ZMod p) • D.root i) - ∑ i, (if i = k then S • D.root i else 0) := by
        rw [show (∑ i, (if i = k then S else 0) • D.root i)
              = ∑ i, (if i = k then S • D.root i else 0) from
            Finset.sum_congr rfl fun i _ => by split_ifs <;> simp]
    _ = (∑ i, (c i : ZMod p) • D.root i) - S • D.root k := by
        rw [Finset.sum_ite_eq' Finset.univ k]
        simp

private lemma sum_ggStepCoroot_eq (D : GGReflDatum p ι X) (k : N) (d : N → ℤ) :
    (∑ i, (ggStepCoroot X k d i : ZMod p) • D.coroot i)
      = (∑ i, (d i : ZMod p) • D.coroot i)
        - ((∑ i, X k i * d i : ℤ) : ZMod p) • D.coroot k := by
  set S : ZMod p := ((∑ j, X k j * d j : ℤ) : ZMod p) with hS
  have hstep : ∀ i, (ggStepCoroot X k d i : ZMod p)
      = (d i : ZMod p) - (if i = k then S else 0) := by
    intro i
    rw [hS]
    unfold ggStepCoroot
    rw [Int.cast_sub]
    split_ifs <;> simp
  calc (∑ i, (ggStepCoroot X k d i : ZMod p) • D.coroot i)
      = ∑ i, (((d i : ZMod p) - (if i = k then S else 0)) • D.coroot i) :=
        Finset.sum_congr rfl fun i _ => by rw [hstep i]
    _ = (∑ i, (d i : ZMod p) • D.coroot i) - ∑ i, (if i = k then S else 0) • D.coroot i := by
        rw [show (∑ i, (↑(d i) - if i = k then S else 0) • D.coroot i)
              = ∑ i, ((d i : ZMod p) • D.coroot i
                  - (if i = k then S else 0) • D.coroot i) from
            Finset.sum_congr rfl fun i _ =>
              sub_smul (d i : ZMod p) (if i = k then S else 0) (D.coroot i)]
        rw [Finset.sum_sub_distrib]
    _ = (∑ i, (d i : ZMod p) • D.coroot i) - ∑ i, (if i = k then S • D.coroot i else 0) := by
        rw [show (∑ i, (if i = k then S else 0) • D.coroot i)
              = ∑ i, (if i = k then S • D.coroot i else 0) from
            Finset.sum_congr rfl fun i _ => by split_ifs <;> simp]
    _ = (∑ i, (d i : ZMod p) • D.coroot i) - S • D.coroot k := by
        rw [Finset.sum_ite_eq' Finset.univ k]
        simp

private lemma root_apply_coroot_eq (D : GGReflDatum p ι X) (k : N) (c : N → ℤ)
    (f : Module.Dual (ZMod p) V) (hf : f = ∑ i, (c i : ZMod p) • D.root i) :
    f (D.coroot k) = ((∑ i, c i * X i k : ℤ) : ZMod p) := by
  rw [hf]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, D.pair]
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Int.cast_mul]

private lemma coroot_apply_root_eq (D : GGReflDatum p ι X) (k : N) (d : N → ℤ)
    (x : V) (hx : x = ∑ i, (d i : ZMod p) • D.coroot i) :
    D.root k x = ((∑ i, X k i * d i : ℤ) : ZMod p) := by
  rw [hx]
  simp only [map_sum, LinearMap.map_smul, smul_eq_mul, D.pair]
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Int.cast_mul, mul_comm]

private lemma sub_smul_root_eq_sum_ggStepRoot (D : GGReflDatum p ι X) (k : N) (c : N → ℤ)
    (f : Module.Dual (ZMod p) V) (hf : f = ∑ i, (c i : ZMod p) • D.root i) :
    f - f (D.coroot k) • D.root k = ∑ i, (ggStepRoot X k c i : ZMod p) • D.root i := by
  have hfc := root_apply_coroot_eq D k c f hf
  rw [sum_ggStepRoot_eq D k c]
  simp only [← hf, ← hfc]

private lemma sub_smul_coroot_eq_sum_ggStepCoroot (D : GGReflDatum p ι X) (k : N) (d : N → ℤ)
    (x : V) (hx : x = ∑ i, (d i : ZMod p) • D.coroot i) :
    x - D.root k x • D.coroot k = ∑ i, (ggStepCoroot X k d i : ZMod p) • D.coroot i := by
  have hkx := coroot_apply_root_eq D k d x hx
  rw [sum_ggStepCoroot_eq D k d]
  simp only [← hx, ← hkx]

theorem GGReflDatum.exists_wordConj (D : GGReflDatum p ι X) (w : List N) (j : N) :
    ∃ ψ ∈ ggInduced ⊤ Bs, ∃ (x : V) (f : Module.Dual (ZMod p) V), f x = 2 ∧
      (∀ z, ggLin (p := p) ι ψ z = z - f z • x) ∧
      f = ∑ i, (ggWordRoot X w j i : ZMod p) • D.root i ∧
      x = ∑ i, (ggWordCoroot X w j i : ZMod p) • D.coroot i := by
  induction w with
  | nil =>
    refine ⟨D.refl j, D.mem j, D.coroot j, D.root j, ?_, ?_, ?_, ?_⟩
    · simp [D.pair, D.diag]
    · intro z
      exact D.lin j z
    · rw [show ggWordRoot X [] j = (fun i => if i = j then 1 else 0 : N → ℤ) from List.foldr_nil]
      exact (sum_ite_root_eq D j).symm
    · rw [show ggWordCoroot X [] j = (fun i => if i = j then 1 else 0 : N → ℤ) from List.foldr_nil]
      exact (sum_ite_coroot_eq D j).symm
  | cons k w ih =>
    obtain ⟨ψ, hψmem, x, f, hfx, hψlin, hf, hx⟩ := ih
    refine ⟨D.refl k * ψ * (D.refl k)⁻¹, ?_,
      x - D.root k x • D.coroot k, f - f (D.coroot k) • D.root k, ?_, ?_, ?_, ?_⟩
    · exact mul_mem_ggInduced (mul_mem_ggInduced (D.mem k) hψmem) (inv_mem_ggInduced (D.mem k))
    · have hgy : D.root k (D.coroot k) = 2 := by simp [D.pair, D.diag]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, LinearMap.map_smul,
        smul_eq_mul]
      rw [hfx, hgy]
      ring
    · intro z
      have hgy : D.root k (D.coroot k) = 2 := by simp [D.pair, D.diag]
      have h := ggLin_conj_reflection (p := p) ι hgy hψlin (D.lin k) z
      simpa [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using h
    · rw [show ggWordRoot X (k :: w) j = ggStepRoot X k (ggWordRoot X w j) from List.foldr_cons]
      exact sub_smul_root_eq_sum_ggStepRoot D k (ggWordRoot X w j) f hf
    · rw [show ggWordCoroot X (k :: w) j = ggStepCoroot X k (ggWordCoroot X w j) from
          List.foldr_cons]
      exact sub_smul_coroot_eq_sum_ggStepCoroot D k (ggWordCoroot X w j) x hx

end Word

end CFSG.StandardType
