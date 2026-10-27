module

public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeStar
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def dot3 (γ : Fin TwistTag.E6.tag.rank → ℤ) (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    ZMod 3 :=
  ∑ i, y i * (γ i : ZMod 3)

@[expose] def mod3 (γ : Fin TwistTag.E6.tag.rank → ℤ) : Fin TwistTag.E6.tag.rank → ZMod 3 :=
  fun i => (γ i : ZMod 3)

@[expose] def cartan3 (γ : Fin TwistTag.E6.tag.rank → ℤ) : Fin TwistTag.E6.tag.rank → ZMod 3 :=
  fun i => ((∑ j, TwistTag.E6.tag.cartan i j * γ j : ℤ) : ZMod 3)

@[expose] def starSet (y : Fin TwistTag.E6.tag.rank → ZMod 3) (g : Fin TwistTag.E6.tag.rank → ℤ) :
    Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  {δ | IsRoot TwistTag.E6.tag δ ∧ dot3 δ y = 0 ∧ iform g δ ≠ 0}

@[expose] def StarGood (y : Fin TwistTag.E6.tag.rank → ZMod 3) (g : Fin TwistTag.E6.tag.rank → ℤ) :
    Prop :=
  (∃ s : Fin 4 → Fin TwistTag.E6.tag.rank → ℤ, (∀ i, s i ∈ starSet y g) ∧
      LinearIndependent (ZMod 3) fun i => cartan3 (s i)) ∨
    ((∀ δ ∈ starSet y g, ∀ ε, IsRoot TwistTag.E6.tag ε → dot3 ε y = 0 → iform δ ε ≠ 0 →
        ε ∈ starSet y g) ∧
      ∃ d ∈ starSet y g, ∀ s ∈ starSet y g, mod3 s ∈ Submodule.span (ZMod 3) {mod3 g, mod3 d})

@[expose] def encY (y : Fin TwistTag.E6.tag.rank → ZMod 3) : List ℤ :=
  List.ofFn fun i => ((y i).val : ℤ)

theorem ofFn_six {α : Type*} (v : Fin TwistTag.E6.tag.rank → α) :
    List.ofFn v = [v (0 : Fin 6), v (1 : Fin 6), v (2 : Fin 6), v (3 : Fin 6), v (4 : Fin 6),
      v (5 : Fin 6)] :=
  rfl

theorem dt_ofFn (u v : Fin TwistTag.E6.tag.rank → ℤ) :
    dt (List.ofFn u) (List.ofFn v) = ∑ i, u i * v i := by
  rw [ofFn_six, ofFn_six]
  exact (Fin.sum_univ_six fun i => u i * v i).symm

theorem cv_ofFn_six (v : Fin 6 → ℤ) :
    cv (List.ofFn v) = List.ofFn fun i : Fin 6 => ∑ j : Fin 6, Tag.cartanE 6 i j * v j := by
  have e : ∀ {α : Type} (w : Fin 6 → α), List.ofFn w = [w 0, w 1, w 2, w 3, w 4, w 5] :=
    fun _ => rfl
  rw [e, e]
  simp only [cv, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_six, Tag.cartanE] <;> ring

theorem cv_ofFn (v : Fin TwistTag.E6.tag.rank → ℤ) :
    cv (List.ofFn v) = List.ofFn fun i => ∑ j, TwistTag.E6.tag.cartan i j * v j :=
  cv_ofFn_six v

theorem iform_eq_dt (u v : Fin TwistTag.E6.tag.rank → ℤ) :
    iform u v = dt (List.ofFn u) (cv (List.ofFn v)) := by
  rw [cv_ofFn, dt_ofFn, iform]
  simp only [Tag.symmetrizedCartan, show TwistTag.E6.tag.symmetrizer = 1 from rfl,
    Matrix.one_mul, Finset.mul_sum, mul_assoc]

theorem emod_three_eq_zero_iff (m : ℤ) : m % 3 = 0 ↔ (m : ZMod 3) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  omega

theorem dt_encY (δ : Fin TwistTag.E6.tag.rank → ℤ) (y : Fin TwistTag.E6.tag.rank → ZMod 3) :
    ((dt (List.ofFn δ) (encY y) : ℤ) : ZMod 3) = dot3 δ y := by
  simp [encY, dt_ofFn, dot3, mul_comm]

theorem length_of_mem_artifactRoots :
    ∀ r ∈ TwistTag.E6.tag.artifactRoots, r.length = 6 := by
  decide +kernel

theorem exists_ofFn_eq {r : List ℤ}
    (hr : r ∈ TwistTag.E6.tag.artifactRoots) :
    ∃ δ : Fin TwistTag.E6.tag.rank → ℤ, List.ofFn δ = r := by
  match r, length_of_mem_artifactRoots r hr with
  | [a, b, c, d, e, f], _ => exact ⟨![a, b, c, d, e, f], rfl⟩

variable {y : Fin TwistTag.E6.tag.rank → ZMod 3}
  {g : Fin TwistTag.E6.tag.rank → ℤ}

theorem mem_phi (ε : Fin TwistTag.E6.tag.rank → ℤ) :
    List.ofFn ε ∈ phi (encY y) ↔ IsRoot TwistTag.E6.tag ε ∧ dot3 ε y = 0 := by
  rw [phi, List.mem_filter, ← isRoot_iff_mem_artifactRoots, beq_iff_eq, emod_three_eq_zero_iff,
    dt_encY]

theorem mem_star (δ : Fin TwistTag.E6.tag.rank → ℤ) :
    List.ofFn δ ∈ star (encY y) (List.ofFn g) ↔ δ ∈ starSet y g := by
  rw [star, List.mem_filter, mem_phi, bne_iff_ne, ← iform_eq_dt, starSet, Set.mem_setOf_eq,
    and_assoc]

theorem exists_of_mem_star {r : List ℤ} (hr : r ∈ star (encY y) (List.ofFn g)) :
    ∃ δ ∈ starSet y g, List.ofFn δ = r := by
  obtain ⟨δ, rfl⟩ := exists_ofFn_eq (List.mem_filter.1 (List.mem_filter.1 hr).1).1
  exact ⟨δ, (mem_star δ).1 hr, rfl⟩

theorem linearIndependent_of_indep4 (u : Fin 4 → Fin TwistTag.E6.tag.rank → ℤ)
    (h : indep4 (List.ofFn (u 0)) (List.ofFn (u 1)) (List.ofFn (u 2)) (List.ofFn (u 3)) = true) :
    LinearIndependent (ZMod 3) fun i k => ((u i k : ℤ) : ZMod 3) := by
  refine Fintype.linearIndependent_iff.2 fun c hc i₀ => ?_
  by_contra hi₀
  have b0 := ZMod.val_lt (c 0); have b1 := ZMod.val_lt (c 1)
  have b2 := ZMod.val_lt (c 2); have b3 := ZMod.val_lt (c 3)
  set n := (c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val with hn
  have hn0 : n ≠ 0 := fun h0 => by
    have z : ∀ j : Fin 4, (c j).val = 0 := fun j => by
      fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
    exact hi₀ ((ZMod.val_eq_zero _).1 (z i₀))
  have h' := List.all_eq_true.1 h n (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true, beq_iff_eq, hn0, false_or] at h'
  have e0 : n % 3 = (c 0).val := by omega
  have e1 : n / 3 % 3 = (c 1).val := by omega
  have e2 : n / 9 % 3 = (c 2).val := by omega
  have e3 : n / 27 % 3 = (c 3).val := by omega
  rw [e0, e1, e2, e3, ofFn_six (u 0), ofFn_six (u 1), ofFn_six (u 2), ofFn_six (u 3)] at h'
  simp only [nz3, lc4, addv, smulv, List.map_cons, List.map_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h'
  have hck : ∀ k : Fin TwistTag.E6.tag.rank, (((c 0).val : ℤ) * u 0 k + (((c 1).val : ℤ) * u 1 k +
      (((c 2).val : ℤ) * u 2 k + ((c 3).val : ℤ) * u 3 k))) % 3 = 0 := fun k => by
    rw [emod_three_eq_zero_iff]
    have := congrFun hc k
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination this
  rcases h' with h0 | h0 | h0 | h0 | h0 | h0
  exacts [h0 (hck (0 : Fin 6)), h0 (hck (1 : Fin 6)), h0 (hck (2 : Fin 6)),
    h0 (hck (3 : Fin 6)), h0 (hck (4 : Fin 6)), h0 (hck (5 : Fin 6))]

theorem starGood_of_caseA (h : caseA (encY y) (List.ofFn g) = true) :
    ∃ s : Fin 4 → Fin TwistTag.E6.tag.rank → ℤ, (∀ i, s i ∈ starSet y g) ∧
      LinearIndependent (ZMod 3) fun i => cartan3 (s i) := by
  unfold caseA at h
  split at h
  · simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, hind⟩ := h
    obtain ⟨δ₀, hδ₀, rfl⟩ := exists_of_mem_star h₀
    obtain ⟨δ₁, hδ₁, rfl⟩ := exists_of_mem_star h₁
    obtain ⟨δ₂, hδ₂, rfl⟩ := exists_of_mem_star h₂
    obtain ⟨δ₃, hδ₃, rfl⟩ := exists_of_mem_star h₃
    rw [cv_ofFn, cv_ofFn, cv_ofFn, cv_ofFn] at hind
    refine ⟨![δ₀, δ₁, δ₂, δ₃], fun i => by fin_cases i <;> assumption, ?_⟩
    exact linearIndependent_of_indep4
      (fun i k => ∑ j, TwistTag.E6.tag.cartan k j * (![δ₀, δ₁, δ₂, δ₃] : Fin 4 → _) i j) hind
  · exact absurd h (by simp)

theorem mem_span_of_span2 {d s : Fin TwistTag.E6.tag.rank → ℤ}
    (h : span2 (List.ofFn g) (List.ofFn d) (List.ofFn s) = true) :
    mod3 s ∈ Submodule.span (ZMod 3) {mod3 g, mod3 d} := by
  simp only [span2, List.any_eq_true] at h
  obtain ⟨a, -, b, -, hab⟩ := h
  rw [ofFn_six g, ofFn_six d, ofFn_six s] at hab
  simp only [nz3, addv, smulv, List.map_cons, List.map_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.any_cons, List.any_nil, Bool.or_false, Bool.not_eq_true',
    Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hab
  have hk : ∀ k : Fin 6, (a * g k + b * d k - s k) % 3 = 0 := fun k => by
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hab
    fin_cases k <;> assumption
  have heq : mod3 s = (a : ZMod 3) • mod3 g + (b : ZMod 3) • mod3 d := funext fun k => by
    have := (emod_three_eq_zero_iff _).1 (hk k)
    push_cast at this
    simp only [mod3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -this
  rw [heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem starGood_of_caseB (h : caseB (encY y) (List.ofFn g) = true) :
    (∀ δ ∈ starSet y g, ∀ ε, IsRoot TwistTag.E6.tag ε → dot3 ε y = 0 → iform δ ε ≠ 0 →
        ε ∈ starSet y g) ∧
      ∃ d ∈ starSet y g, ∀ s ∈ starSet y g, mod3 s ∈ Submodule.span (ZMod 3) {mod3 g, mod3 d} := by
  simp only [caseB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨hcl, d, hd, hsp⟩ := h
  refine ⟨fun δ hδ ε hε hεy hδε => ?_, ?_⟩
  · rcases hcl _ ((mem_star δ).2 hδ) _ ((mem_phi ε).2 ⟨hε, hεy⟩) with h0 | hc
    · exact absurd ((iform_eq_dt δ ε).trans h0) hδε
    · exact (mem_star ε).1 hc
  · obtain ⟨δd, hδd, rfl⟩ := exists_of_mem_star hd
    exact ⟨δd, hδd, fun s hs => mem_span_of_span2 (hsp _ ((mem_star s).2 hs))⟩

theorem starGood_of_good (h : good (encY y) (List.ofFn g) = true) : StarGood y g := by
  rcases Bool.or_eq_true _ _ ▸ h with hA | hB
  · exact Or.inl (starGood_of_caseA hA)
  · exact Or.inr (starGood_of_caseB hB)

theorem starGood_single_zero (hy : y (0 : Fin 6) = 0) :
    StarGood y (Pi.single (0 : Fin 6) 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
  apply starGood_of_good
  have e₁ : encY y = [0, ((y (1 : Fin 6)).val : ℤ), ((y (2 : Fin 6)).val : ℤ),
      ((y (3 : Fin 6)).val : ℤ), ((y (4 : Fin 6)).val : ℤ), ((y (5 : Fin 6)).val : ℤ)] := by
    rw [encY, ofFn_six, hy]
    rfl
  have e₂ : List.ofFn (Pi.single (0 : Fin 6) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      [1, 0, 0, 0, 0, 0] := by
    decide
  rw [e₁, e₂]
  exact good_single_zero _ _ _ _ _

end CFSG.StandardType.TwE6NormThree

end
