module

public import CFSG.Monster.GMS.Griess13.Idempotents
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.Monster.GMS.Griess13

open Finset

section Orbits

theorem eqvGen_of_tree {α : Type*} {step : α → α → Prop} (S : Set α) (root : α) (depth : α → ℕ)
    (par : α → α) (hpar : ∀ w ∈ S, w ≠ root → par w ∈ S ∧ depth (par w) < depth w ∧
      step (par w) w) :
    ∀ w ∈ S, Relation.EqvGen step root w := by
  have key : ∀ n, ∀ w ∈ S, depth w = n → Relation.EqvGen step root w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw hdw
      by_cases hwr : w = root
      · subst hwr
        exact Relation.EqvGen.refl _
      · obtain ⟨hp, hlt, hstep⟩ := hpar w hw hwr
        exact (ih (depth (par w)) (hdw ▸ hlt) (par w) hp rfl).trans _ _ _
          (Relation.EqvGen.rel _ _ hstep)
  exact fun w hw => key _ w hw rfl

theorem eqvGen_of_trees {α : Type*} {step : α → α → Prop} (S : Set α) (cls : α → Fin 3)
    (root : Fin 3 → α) (depth : α → ℕ) (par : α → α)
    (hpar : ∀ w ∈ S, w ≠ root (cls w) →
      par w ∈ S ∧ cls (par w) = cls w ∧ depth (par w) < depth w ∧ step (par w) w) :
    ∀ w ∈ S, ∀ w' ∈ S, cls w = cls w' → Relation.EqvGen step w w' := by
  have key : ∀ n, ∀ w ∈ S, depth w = n → Relation.EqvGen step (root (cls w)) w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw hdw
      by_cases hwr : w = root (cls w)
      · rw [← hwr]
        exact Relation.EqvGen.refl _
      · obtain ⟨hp, hcls, hlt, hstep⟩ := hpar w hw hwr
        have := ih (depth (par w)) (hdw ▸ hlt) (par w) hp rfl
        rw [hcls] at this
        exact this.trans _ _ _ (Relation.EqvGen.rel _ _ hstep)
  intro w hw w' hw' hc
  have h1 := key _ w hw rfl
  have h2 := key _ w' hw' rfl
  rw [hc] at h1
  exact h1.symm.trans _ _ _ h2

end Orbits

theorem finiteDimensional_of_finrank_eq_24 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 24) : FiniteDimensional (ZMod 2) V :=
  Module.finite_of_finrank_pos (by omega)

section Counting

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

theorem piH_zero : piH ρ ι 0 = piE ρ ι := by
  rw [piH_def, piE_def, hyp_zero]

theorem finrank_range_piE_lt [FiniteDimensional (ZMod 2) V] (hnt : ∃ v, ρ (ι v) ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) < Module.finrank (ZMod 2) V := by
  refine lt_of_le_of_ne (Submodule.finrank_le _) fun h => ?_
  have htop : LinearMap.range (piE ρ ι) = ⊤ := Submodule.eq_top_of_finrank_eq h
  obtain ⟨v, hv⟩ := hnt
  apply hv
  ext x
  have hx : x ∈ LinearMap.range (piH ρ ι 0) := by rw [piH_zero, htop]; trivial
  rw [range_piH] at hx
  simpa using hx v (zero_dotProduct v)

theorem counting_arith {c₀ a b c : ℕ} (ha : Even a) (hb : Even b) (hc : Even c)
    (h : c₀ + (12 * a + 132 * b + 220 * c) = 24) :
    b = 0 ∧ c = 0 ∧ ((a = 2 ∧ c₀ = 0) ∨ (a = 0 ∧ c₀ = 24)) := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨c', rfl⟩ := hc
  have hb' : b' = 0 := by omega
  have hc' : c' = 0 := by omega
  subst hb' hc'
  have : a' ≤ 1 := by omega
  interval_cases a' <;> omega

theorem piE_eq_zero_and_finrank_eK [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 24) {R : Finset F3Vec} (hR : IsLineReps R)
    (cls : F3Vec → Fin 3) (h0 : (R.filter fun w => cls w = 0).card = 12)
    (h1 : (R.filter fun w => cls w = 1).card = 132)
    (h2 : (R.filter fun w => cls w = 2).card = 220)
    (hconst : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' →
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
        Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')))
    (hnt : ∃ v, ρ (ι v) ≠ 1) :
    piE ρ ι = 0 ∧ ∀ w ∈ R, Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
      if cls w = 0 then 2 else 0 := by
  classical
  set d : F3Vec → ℕ := fun w => Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) with hd
  have heven : ∀ w ∈ R, Even (d w) := fun w hw => by
    obtain ⟨v₀, hv₀⟩ := exists_dot_ne_zero (hR.ne_zero w hw)
    exact even_finrank_range_eK ρ ι hv₀
  have hex : ∀ k : Fin 3, ((R.filter fun w => cls w = k).card ≠ 0) →
      ∃ w ∈ R, cls w = k := fun k hk => by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hk)
    exact ⟨w, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  obtain ⟨w0, hw0R, hw0c⟩ := hex 0 (by omega)
  obtain ⟨w1, hw1R, hw1c⟩ := hex 1 (by omega)
  obtain ⟨w2, hw2R, hw2c⟩ := hex 2 (by omega)
  have hval : ∀ w ∈ R, ∀ (k : Fin 3) (w' : F3Vec), w' ∈ R → cls w' = k → cls w = k → d w = d w' :=
    fun w hw k w' hw' hk' hk => hconst w hw w' hw' (hk.trans hk'.symm)
  have hsplit : ∑ w ∈ R, d w = 12 * d w0 + 132 * d w1 + 220 * d w2 := by
    rw [← Finset.sum_fiberwise R cls d, Fin.sum_univ_three]
    have hk : ∀ (k : Fin 3) (w' : F3Vec), w' ∈ R → cls w' = k →
        ∑ w ∈ R.filter (fun w => cls w = k), d w = (R.filter fun w => cls w = k).card * d w' := by
      intro k w' hw' hk'
      rw [Finset.sum_congr rfl (g := fun _ => d w')
        (fun w hw => hval w (Finset.mem_filter.mp hw).1 k w' hw' hk' (Finset.mem_filter.mp hw).2),
        Finset.sum_const, smul_eq_mul]
    rw [hk 0 w0 hw0R hw0c, hk 1 w1 hw1R hw1c, hk 2 w2 hw2R hw2c, h0, h1, h2]
  have hdec := finrank_eq_finrank_range_piE_add_sum ρ ι hR
  rw [hV, hsplit] at hdec
  obtain ⟨hb, hc, hcase⟩ :=
    counting_arith (c₀ := Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)))
      (heven w0 hw0R) (heven w1 hw1R) (heven w2 hw2R) hdec.symm
  have hlt := finrank_range_piE_lt ρ ι hnt
  rw [hV] at hlt
  have ha : d w0 = 2 := by
    rcases hcase with ⟨ha, _⟩ | ⟨_, hc0⟩
    · exact ha
    · omega
  have hc0 : Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) = 0 := by
    rcases hcase with ⟨_, hc0⟩ | ⟨_, hc0⟩
    · exact hc0
    · omega
  refine ⟨?_, ?_⟩
  · have hbot : LinearMap.range (piE ρ ι) = ⊥ := Submodule.finrank_eq_zero.mp hc0
    exact LinearMap.range_eq_bot.mp hbot
  · intro w hw
    show d w = _
    have hcls : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hcls (cls w) with hk | hk | hk
    · have hif : (if cls w = 0 then 2 else 0 : ℕ) = 2 := by simp [hk]
      rw [hif, hval w hw 0 w0 hw0R hw0c hk]
      exact ha
    · have hif : (if cls w = 0 then 2 else 0 : ℕ) = 0 := by simp [hk]
      rw [hif, hval w hw 1 w1 hw1R hw1c hk]
      exact hb
    · have hif : (if cls w = 0 then 2 else 0 : ℕ) = 0 := by simp [hk]
      rw [hif, hval w hw 2 w2 hw2R hw2c hk]
      exact hc

end Counting

section Basis

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

theorem exists_coeffs_of_mem_range_eK {w₁ v₀ : F3Vec}
    (hdim : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2) (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0)
    {x : V} (hx : x ∈ LinearMap.range (eK ρ ι w₁)) (hx0 : x ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w₁)) :
    ∃ a b : ZMod 2, y = a • x + b • ρ (ι v₀) x := by
  have hTx : ρ (ι v₀) x ∈ LinearMap.range (eK ρ ι w₁) := apply_mem_range_eK ρ ι w₁ v₀ hx
  let bx : LinearMap.range (eK ρ ι w₁) := ⟨x, hx⟩
  let bTx : LinearMap.range (eK ρ ι w₁) := ⟨ρ (ι v₀) x, hTx⟩
  have hbx0 : bx ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hli : LinearIndependent (ZMod 2) ![bx, bTx] := by
    rw [LinearIndependent.pair_iff' hbx0]
    intro a ha
    have ha' : a • x = ρ (ι v₀) x := congrArg Subtype.val ha
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hcases a with rfl | rfl
    · rw [zero_smul] at ha'
      have h3 := apply_cube ρ ι v₀ x
      rw [← ha', map_zero, map_zero] at h3
      exact hx0 h3.symm
    · rw [one_smul] at ha'
      exact hx0 (eq_zero_of_apply_eq_self ρ ι hv₀ hx ha'.symm)
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) := by
    simp [hdim]
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hy' : (⟨y, hy⟩ : LinearMap.range (eK ρ ι w₁)) ∈
      Submodule.span (ZMod 2) (Set.range ![bx, bTx]) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hy'
  refine ⟨c 0, c 1, ?_⟩
  have := congrArg Subtype.val hc
  simpa [Fin.sum_univ_two, bx, bTx] using this.symm

omit [FiniteDimensional (ZMod 2) V] in
theorem sum_eK_eq_one_of_zero {R : Finset F3Vec} (hR : IsLineReps R) (hE : piE ρ ι = 0)
    {S : Finset F3Vec} (hS : S ⊆ R) (hzero : ∀ w ∈ R, w ∉ S → eK ρ ι w = 0) :
    ∑ w ∈ S, eK ρ ι w = 1 := by
  have h := sum_eK_add_piE ρ ι hR
  rw [hE, add_zero] at h
  rw [Finset.sum_subset hS hzero, h]

theorem exists_basis_of_blocks (hV : Module.finrank (ZMod 2) V = 24) {R : Finset F3Vec}
    (hR : IsLineReps R) (hE : piE ρ ι = 0) (w : Fin 12 → F3Vec) (hinj : Function.Injective w)
    (hwR : ∀ i, w i ∈ R) (hzero : ∀ w' ∈ R, (∀ i, w i ≠ w') → eK ρ ι w' = 0)
    {w₁ v₀ : F3Vec} (hdim : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2)
    (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V} (hx : x ∈ LinearMap.range (eK ρ ι w₁)) (hx0 : x ≠ 0)
    (r : Fin 12 → Γ) (A : Fin 12 → Matrix (Fin 6) (Fin 6) (ZMod 3)) (c : Fin 12 → ZMod 3)
    (hr : ∀ i, ConjAct ι (r i) (A i)) (hc : ∀ i, c i ≠ 0)
    (hwA : ∀ i, Matrix.vecMul (w i) (A i) = c i • w₁) :
    ∃ b : Module.Basis (Fin 12 × Fin 2) (ZMod 2) V,
      ∀ i j, b (i, j) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x) := by
  classical
  have hsum : ∑ i, eK ρ ι (w i) = 1 := by
    have h := sum_eK_eq_one_of_zero ρ ι hR hE (S := Finset.univ.image w)
      (fun w' hw' => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw'
        exact hwR i)
      (fun w' hw'R hw'S =>
        hzero w' hw'R fun i hi => hw'S (Finset.mem_image.mpr ⟨i, mem_univ _, hi⟩))
    rwa [Finset.sum_image (fun i _ j _ hij => hinj hij)] at h
  let bfam : Fin 12 × Fin 2 → V := fun p => ρ (r p.1) ((ρ (ι v₀) ^ (p.2 : ℕ)) x)
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range bfam) := by
    intro v _
    have hv : v = ∑ i, eK ρ ι (w i) v := by
      have := LinearMap.congr_fun hsum v
      simpa [LinearMap.sum_apply] using this.symm
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hmem : eK ρ ι (w i) v ∈ LinearMap.range (eK ρ ι (w i)) := ⟨v, rfl⟩
    rw [range_eK_eq_map ρ (hr i) (hc i) (hwA i)] at hmem
    obtain ⟨y, hy, hyv⟩ := hmem
    obtain ⟨a, b, rfl⟩ := exists_coeffs_of_mem_range_eK ρ ι hdim hv₀ hx hx0 hy
    rw [← hyv, map_add, map_smul, map_smul]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, 0), ?_⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, 1), ?_⟩))
    · simp [bfam]
    · simp [bfam]
  have hcard : Fintype.card (Fin 12 × Fin 2) = Module.finrank (ZMod 2) V := by
    simp [hV]
  refine ⟨basisOfTopLeSpanOfCardEqFinrank bfam hspan hcard, fun i j => ?_⟩
  simp [bfam]

theorem eK_eq_zero_of_finrank_eq_zero {w : F3Vec}
    (h : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) = 0) : eK ρ ι w = 0 :=
  LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)

theorem piE_eq_zero_and_finrank_eK_of_orbits (hV : Module.finrank (ZMod 2) V = 24)
    {R : Finset F3Vec} (hR : IsLineReps R) (cls : F3Vec → Fin 3)
    (h0 : (R.filter fun w => cls w = 0).card = 12)
    (h1 : (R.filter fun w => cls w = 1).card = 132)
    (h2 : (R.filter fun w => cls w = 2).card = 220) {κ : Type*} (g : κ → Γ)
    (A : κ → Matrix (Fin 6) (Fin 6) (ZMod 3)) (hg : ∀ k, ConjAct ι (g k) (A k))
    (horbit : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' → Relation.EqvGen
      (fun a b : F3Vec => ∃ k, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (A k) = c • a) w w')
    (hnt : ∃ v, ρ (ι v) ≠ 1) :
    piE ρ ι = 0 ∧ ∀ w ∈ R, Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
      if cls w = 0 then 2 else 0 :=
  piE_eq_zero_and_finrank_eK ρ ι hV hR cls h0 h1 h2
    (fun w hw w' hw' hcls => finrank_range_eK_eq_of_eqvGen ρ g A hg (horbit w hw w' hw' hcls)) hnt

theorem exists_basis_of_orbits (hV : Module.finrank (ZMod 2) V = 24)
    {R : Finset F3Vec} (hR : IsLineReps R) (cls : F3Vec → Fin 3)
    (h0 : (R.filter fun w => cls w = 0).card = 12)
    (h1 : (R.filter fun w => cls w = 1).card = 132)
    (h2 : (R.filter fun w => cls w = 2).card = 220)
    (hconst : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' →
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
        Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')))
    (hnt : ∃ v, ρ (ι v) ≠ 1) (w : Fin 12 → F3Vec) (hinj : Function.Injective w)
    (hwR : ∀ i, w i ∈ R) (hwcls : ∀ i, cls (w i) = 0) {w₁ v₀ : F3Vec} (hw₁R : w₁ ∈ R)
    (hw₁cls : cls w₁ = 0) (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V} (hx : x ∈ LinearMap.range (eK ρ ι w₁))
    (hx0 : x ≠ 0) (r : Fin 12 → Γ) (A : Fin 12 → Matrix (Fin 6) (Fin 6) (ZMod 3))
    (c : Fin 12 → ZMod 3) (hr : ∀ i, ConjAct ι (r i) (A i)) (hc : ∀ i, c i ≠ 0)
    (hwA : ∀ i, Matrix.vecMul (w i) (A i) = c i • w₁) :
    ∃ b : Module.Basis (Fin 12 × Fin 2) (ZMod 2) V,
      ∀ i j, b (i, j) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x) := by
  classical
  obtain ⟨hE, hdim⟩ := piE_eq_zero_and_finrank_eK ρ ι hV hR cls h0 h1 h2 hconst hnt
  have himg : Finset.univ.image w ⊆ R.filter (fun w' => cls w' = 0) := by
    intro w' hw'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw'
    exact Finset.mem_filter.mpr ⟨hwR i, hwcls i⟩
  have hcardimg : (Finset.univ.image w).card = 12 := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have heq : Finset.univ.image w = R.filter (fun w' => cls w' = 0) :=
    Finset.eq_of_subset_of_card_le himg (by rw [h0, hcardimg])
  refine exists_basis_of_blocks ρ ι hV hR hE w hinj hwR ?_ ?_ hv₀ hx hx0 r A c hr hc hwA
  · intro w' hw'R hw'
    apply eK_eq_zero_of_finrank_eq_zero
    rw [hdim w' hw'R]
    have hne : cls w' ≠ 0 := fun hc0 => by
      have hmem : w' ∈ Finset.univ.image w := by
        rw [heq]; exact Finset.mem_filter.mpr ⟨hw'R, hc0⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      exact hw' i hi
    simp [hne]
  · rw [hdim w₁ hw₁R]; simp [hw₁cls]

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_fixed_mem_range_eK {g : Γ} {A : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ConjAct ι g A) (hg2 : g * g = 1) {w : F3Vec} {c : ZMod 3} (hc : c ≠ 0)
    (hw : Matrix.vecMul w A = c • w) (hne : LinearMap.range (eK ρ ι w) ≠ ⊥) :
    ∃ x ∈ LinearMap.range (eK ρ ι w), x ≠ 0 ∧ ρ g x = x := by
  have hinv : ∀ y ∈ LinearMap.range (eK ρ ι w), ρ g y ∈ LinearMap.range (eK ρ ι w) := by
    intro y hy
    have := range_eK_eq_map ρ h hc hw
    rw [this]
    exact Submodule.mem_map_of_mem hy
  have hT2 : ∀ y : V, ρ g (ρ g y) = y := fun y => by
    have : ρ g * ρ g = 1 := by rw [← map_mul, hg2, map_one]
    simpa using LinearMap.congr_fun this y
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  by_cases hx : y + ρ g y = 0
  · refine ⟨y, hy, hy0, ?_⟩
    have h2 := add_self_eq_zero_of_zmod2 y
    exact add_left_cancel (hx.trans h2.symm)
  · refine ⟨y + ρ g y, Submodule.add_mem _ hy (hinv y hy), hx, ?_⟩
    rw [map_add, hT2, add_comm]

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_sq_of_mem_range_eK {w v₀ : F3Vec} (hv₀ : w ⬝ᵥ v₀ ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w)) :
    ρ (ι v₀) (ρ (ι v₀) y) = y + ρ (ι v₀) y := by
  have h := one_add_apply_eq_zero ρ ι hv₀ hy
  have h2 := add_self_eq_zero_of_zmod2 (y + ρ (ι v₀) y)
  exact add_left_cancel (h.trans h2.symm)

end Basis

end CFSG.Monster.GMS.Griess13
