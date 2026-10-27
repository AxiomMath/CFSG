module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkFix
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType

namespace WitSpBlk

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot WitClSp WitSpNs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {n : ℕ}

structure IsSwapFamily (v : StatedSp n K) {m : ℕ} (F₁ F₂ : Fin m → Fin n ⊕ Fin n → K) :
    Prop where
  o11 : ∀ i j, form (F₁ i) (F₁ j) = 0
  o12 : ∀ i j, form (F₁ i) (F₂ j) = 0
  o22 : ∀ i j, form (F₂ i) (F₂ j) = 0
  b11 : ∀ i j, form (F₁ i) (nilL v (F₁ j)) = 0
  b12 : ∀ i j, form (F₁ i) (nilL v (F₂ j)) = if i = j then 1 else 0
  b22 : ∀ i j, form (F₂ i) (nilL v (F₂ j)) = 0

namespace IsSwapFamily

variable {v : StatedSp n K} {m : ℕ} {F₁ F₂ : Fin m → Fin n ⊕ Fin n → K}

theorem zero (v : StatedSp n K) (F₁ F₂ : Fin 0 → Fin n ⊕ Fin n → K) : IsSwapFamily v F₁ F₂ :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0⟩

theorem o21 (h : IsSwapFamily v F₁ F₂) (i j : Fin m) : form (F₂ i) (F₁ j) = 0 := by
  rw [form_antisymm, h.o12, neg_zero]

theorem b21 [CharP K 2] (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) (i j : Fin m) :
    form (F₂ i) (nilL v (F₁ j)) = if j = i then 1 else 0 := by
  rw [form_nilL_comm hv, h.b12]

theorem nb11 (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) (i j : Fin m) :
    form (nilL v (F₁ i)) (F₁ j) = 0 := by
  rw [form_nilL_left hv, h.b11]

theorem nb12 (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) (i j : Fin m) :
    form (nilL v (F₁ i)) (F₂ j) = if i = j then 1 else 0 := by
  rw [form_nilL_left hv, h.b12]

theorem nb21 [CharP K 2] (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) (i j : Fin m) :
    form (nilL v (F₂ i)) (F₁ j) = if j = i then 1 else 0 := by
  rw [form_nilL_left hv, h.b21 hv]

theorem nb22 (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) (i j : Fin m) :
    form (nilL v (F₂ i)) (F₂ j) = 0 := by
  rw [form_nilL_left hv, h.b22]

@[expose] noncomputable def gen (v : StatedSp n K) (F₁ F₂ : Fin m → Fin n ⊕ Fin n → K) :
    Fin m ⊕ (Fin m ⊕ (Fin m ⊕ Fin m)) → Fin n ⊕ Fin n → K :=
  Sum.elim F₁ (Sum.elim F₂ (Sum.elim (fun i => nilL v (F₁ i)) (fun i => nilL v (F₂ i))))

theorem coeff_eq_zero [CharP K 2] (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂)
    (c : Fin m ⊕ (Fin m ⊕ (Fin m ⊕ Fin m)) → K)
    (hc : ∀ j, form (∑ x, c x • gen v F₁ F₂ x) (nilL v (F₂ j)) = 0 ∧
      form (∑ x, c x • gen v F₁ F₂ x) (nilL v (F₁ j)) = 0 ∧
      form (∑ x, c x • gen v F₁ F₂ x) (F₂ j) = 0 ∧ form (∑ x, c x • gen v F₁ F₂ x) (F₁ j) = 0) :
    ∀ x, c x = 0 := by
  have hnn : ∀ a b : Fin n ⊕ Fin n → K, form (nilL v a) (nilL v b) = 0 :=
    fun a b => form_nilL_nilL hv a b
  intro x
  rcases x with j | j | j | j
  · have := (hc j).1
    simpa [gen, form_add_left, form_sum_left, form_smul_left, Fintype.sum_sum_type, h.b12, h.b22,
      hnn] using this
  · have := (hc j).2.1
    simpa [gen, form_add_left, form_sum_left, form_smul_left, Fintype.sum_sum_type, h.b11,
      h.b21 hv, hnn] using this
  · have := (hc j).2.2.1
    simpa [gen, form_add_left, form_sum_left, form_smul_left, Fintype.sum_sum_type, h.o12, h.o22,
      h.nb12 hv, h.nb22 hv] using this
  · have := (hc j).2.2.2
    simpa [gen, form_add_left, form_sum_left, form_smul_left, Fintype.sum_sum_type, h.o11, h.o21,
      h.nb11 hv, h.nb21 hv] using this

theorem snoc [CharP K 2] (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) {a b : Fin n ⊕ Fin n → K}
    (hab : form a b = 0) (hQa : form a (nilL v a) = 0) (hQb : form b (nilL v b) = 0)
    (hβ : form a (nilL v b) = 1)
    (ha : ∀ i, form (F₁ i) a = 0 ∧ form (F₂ i) a = 0 ∧ form (nilL v (F₁ i)) a = 0 ∧
      form (nilL v (F₂ i)) a = 0)
    (hb : ∀ i, form (F₁ i) b = 0 ∧ form (F₂ i) b = 0 ∧ form (nilL v (F₁ i)) b = 0 ∧
      form (nilL v (F₂ i)) b = 0) :
    IsSwapFamily v (Fin.snoc (α := fun _ => Fin n ⊕ Fin n → K) F₁ a)
      (Fin.snoc (α := fun _ => Fin n ⊕ Fin n → K) F₂ b) := by
  have hrev : ∀ {x y : Fin n ⊕ Fin n → K}, form x y = 0 → form y x = 0 := fun hxy => by
    rw [form_antisymm, hxy, neg_zero]
  have hβl : ∀ x y : Fin n ⊕ Fin n → K, form x (nilL v y) = form (nilL v x) y :=
    fun x y => (form_nilL_left hv x y).symm
  have hβs : ∀ x y : Fin n ⊕ Fin n → K, form x (nilL v y) = form (nilL v y) x :=
    fun x y => by rw [form_nilL_comm hv, form_nilL_left hv]
  have hne : ∀ j : Fin m, Fin.last m ≠ Fin.castSucc j := fun j => (Fin.castSucc_ne_last j).symm
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_,
    fun i j => ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact form_self a
      | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hrev (ha j).1
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact (ha i).1
      | cast j => simp only [Fin.snoc_castSucc]; exact h.o11 i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact hab
      | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hrev (ha j).2.1
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact (hb i).1
      | cast j => simp only [Fin.snoc_castSucc]; exact h.o12 i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact form_self b
      | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hrev (hb j).2.1
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact (hb i).2.1
      | cast j => simp only [Fin.snoc_castSucc]; exact h.o22 i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact hQa
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hβs]
        exact (ha j).2.2.1
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hβl]
        exact (ha i).2.2.1
      | cast j => simp only [Fin.snoc_castSucc]; exact h.b11 i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, ↓reduceIte]; exact hβ
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc, hne j, ↓reduceIte]
        rw [hβs]
        exact (ha j).2.2.2
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last i, ↓reduceIte]
        rw [hβl]
        exact (hb i).2.2.1
      | cast j => simp only [Fin.snoc_castSucc, Fin.castSucc_inj]; exact h.b12 i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact hQb
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hβs]
        exact (hb j).2.2.2
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hβl]
        exact (hb i).2.2.2
      | cast j => simp only [Fin.snoc_castSucc]; exact h.b22 i j

end IsSwapFamily

theorem exists_swap_step [Finite K] [CharP K 2] {v : StatedSp n K} (hv : v * v = 1)
    {T : Submodule K (Fin n ⊕ Fin n → K)}
    (hT : T ⊓ (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal T = ⊥)
    (hNT : ∀ t ∈ T, nilL v t ∈ T) {k : ℕ}
    (hk : Module.finrank K (T.map (nilL v)) ≤ 2 * k)
    (hl : 2 * k + 3 ≤ Module.finrank K (LinearMap.range (nilL v))) :
    ∃ a ∈ (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal T,
      ∃ b ∈ (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal T,
        form a b = 0 ∧ form a (nilL v a) = 0 ∧ form b (nilL v b) = 0 ∧
          form a (nilL v b) = 1 := by
  classical
  set B := Matrix.toBilin' (Matrix.J (Fin n) K) with hB
  set Z := B.orthogonal T with hZ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hZT : ∀ z ∈ Z, ∀ t ∈ T, form t z = 0 := fun z hz => mem_orth_iff.mp hz
  have hNZ : ∀ z ∈ Z, nilL v z ∈ Z := fun z hz => mem_orth_iff.mpr fun t ht => by
    rw [← form_nilL_left hv]
    exact hZT z hz _ (hNT t ht)
  set H := Z ⊓ quadKer hv with hH
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ H, ∃ b ∈ H, form a (nilL v b) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₀, hZle⟩ : ∃ z₀, Z ≤ H ⊔ Submodule.span K {z₀} := by
      by_cases hall : ∀ z ∈ Z, form z (nilL v z) = 0
      · exact ⟨0, fun z hz => Submodule.mem_sup_left ⟨hz, hall z hz⟩⟩
      push Not at hall
      obtain ⟨z₀, hz₀, hQ⟩ := hall
      refine ⟨z₀, fun z hz => ?_⟩
      obtain ⟨c, hc⟩ := isSquare_of_charTwo' (form z (nilL v z) / form z₀ (nilL v z₀))
      have hmem : z - c • z₀ ∈ H := by
        refine ⟨Z.sub_mem hz (Z.smul_mem c hz₀), (mem_quadKer hv).mpr ?_⟩
        rw [sub_eq_add_neg, quad_add hv, ← neg_smul, quad_smul]
        have : (-c) ^ 2 * form z₀ (nilL v z₀) = form z (nilL v z) := by
          rw [neg_sq, sq, ← hc, div_mul_cancel₀ _ hQ]
        rw [this]
        linear_combination form z (nilL v z) * h2
      have := Submodule.add_mem_sup hmem
        (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z₀))
      simpa using this
    have hspan : ∀ y : Fin n ⊕ Fin n → K, Module.finrank K (Submodule.span K {y}) ≤ 1 :=
      fun y => by
        have h1 := finrank_span_le_card (R := K) ({y} : Set (Fin n ⊕ Fin n → K))
        rwa [Set.toFinset_singleton, Finset.card_singleton] at h1
    have hNH : H.map (nilL v) ≤ B.orthogonal (H ⊔ T) := by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_orth_iff.mpr fun x hx => ?_
      obtain ⟨h, hh, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
      rw [form_add_left, hcon h hh y hy, hZT _ (hNZ y hy.1) t ht, add_zero]
    have hdisj : H ⊓ T = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxH, hxT⟩
      have : x ∈ T ⊓ Z := ⟨hxT, hxH.1⟩
      rw [hT] at this
      exact this
    have e1 := Submodule.finrank_mono hNH
    rw [finrank_orth] at e1
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq H T
    rw [hdisj, finrank_bot, add_zero] at e2
    have e3 : Module.finrank K Z = 2 * n - Module.finrank K T := finrank_orth T
    have e4 : Module.finrank K T ≤ 2 * n := (Submodule.finrank_le T).trans_eq finrank_ambient
    have e5 := Submodule.finrank_mono hZle
    have e6 := Submodule.finrank_add_le_finrank_add_finrank H (Submodule.span K {z₀})
    have e7 := hspan z₀
    have hNZle : Z.map (nilL v) ≤ H.map (nilL v) ⊔ Submodule.span K {nilL v z₀} := by
      calc Z.map (nilL v) ≤ (H ⊔ Submodule.span K {z₀}).map (nilL v) := Submodule.map_mono hZle
        _ = H.map (nilL v) ⊔ (Submodule.span K {z₀}).map (nilL v) := Submodule.map_sup _ _ _
        _ = H.map (nilL v) ⊔ Submodule.span K {nilL v z₀} := by
          rw [Submodule.map_span, Set.image_singleton]
    have e8 := Submodule.finrank_mono hNZle
    have e9 := Submodule.finrank_add_le_finrank_add_finrank (H.map (nilL v))
      (Submodule.span K {nilL v z₀})
    have e10 := hspan (nilL v z₀)
    have hsup : T ⊔ Z = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_sup_add_finrank_inf_eq T Z
      rw [hT, finrank_bot, add_zero, e3] at this
      rw [this, finrank_ambient]
      omega
    have hrange : LinearMap.range (nilL v) = T.map (nilL v) ⊔ Z.map (nilL v) := by
      rw [LinearMap.range_eq_map, ← hsup, Submodule.map_sup]
    have e11 := Submodule.finrank_add_le_finrank_add_finrank (T.map (nilL v)) (Z.map (nilL v))
    rw [← hrange] at e11
    omega
  set c := form a (nilL v b) with hc
  set b' := b + (-(form a b / c)) • nilL v b with hb'
  have hb'Z : b' ∈ Z := Z.add_mem hb.1 (Z.smul_mem _ (hNZ b hb.1))
  have hNb' : nilL v b' = nilL v b := by
    rw [hb', map_add, map_smul, nilL_nilL hv, smul_zero, add_zero]
  have hQb' : form b' (nilL v b') = 0 := by
    rw [hb', quad_add hv, hb.2, quad_smul, nilL_nilL hv, form_zero_right, mul_zero, add_zero]
  have hab' : form a b' = 0 := by
    rw [hb', form_add_right, form_smul_right, ← hc, neg_mul, div_mul_cancel₀ _ hab,
      add_neg_cancel]
  refine ⟨c⁻¹ • a, Z.smul_mem _ ha.1, b', hb'Z, ?_, ?_, hQb', ?_⟩
  · rw [form_smul_left, hab', mul_zero]
  · rw [quad_smul, ha.2, mul_zero]
  · rw [hNb', form_smul_left, ← hc, inv_mul_cancel₀ hab]

namespace IsSwapFamily

variable {v : StatedSp n K} {m : ℕ} {F₁ F₂ : Fin m → Fin n ⊕ Fin n → K}

theorem gen_mem_span (x : Fin m ⊕ (Fin m ⊕ (Fin m ⊕ Fin m))) :
    gen v F₁ F₂ x ∈ Submodule.span K (Set.range (gen v F₁ F₂)) :=
  Submodule.subset_span ⟨x, rfl⟩

theorem span_gen [CharP K 2] (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) :
    Submodule.span K (Set.range (gen v F₁ F₂)) ⊓
        (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal
          (Submodule.span K (Set.range (gen v F₁ F₂))) = ⊥ ∧
      (∀ t ∈ Submodule.span K (Set.range (gen v F₁ F₂)),
        nilL v t ∈ Submodule.span K (Set.range (gen v F₁ F₂))) ∧
      Module.finrank K ((Submodule.span K (Set.range (gen v F₁ F₂))).map (nilL v)) ≤
        2 * m := by
  classical
  set T := Submodule.span K (Set.range (gen v F₁ F₂)) with hT
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro z ⟨hzT, hzO⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hzT
    have hO : ∀ t ∈ T, form (∑ x, c x • gen v F₁ F₂ x) t = 0 := fun t ht => by
      rw [form_antisymm, mem_orth_iff.mp hzO t ht, neg_zero]
    have hc := h.coeff_eq_zero hv c fun j =>
      ⟨hO _ (gen_mem_span (Sum.inr (Sum.inr (Sum.inr j)))),
        hO _ (gen_mem_span (Sum.inr (Sum.inr (Sum.inl j)))),
        hO _ (gen_mem_span (Sum.inr (Sum.inl j))), hO _ (gen_mem_span (Sum.inl j))⟩
    simp [hc]
  · have hle : T.map (nilL v) ≤ T := by
      rw [hT, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      rcases x with j | j | j | j
      · exact gen_mem_span (Sum.inr (Sum.inr (Sum.inl j)))
      · exact gen_mem_span (Sum.inr (Sum.inr (Sum.inr j)))
      · change nilL v (nilL v (F₁ j)) ∈ T
        rw [nilL_nilL hv]
        exact T.zero_mem
      · change nilL v (nilL v (F₂ j)) ∈ T
        rw [nilL_nilL hv]
        exact T.zero_mem
    exact fun t ht => hle ⟨t, ht, rfl⟩
  · have hle : T.map (nilL v) ≤ Submodule.span K
        (Set.range (Sum.elim (fun i => nilL v (F₁ i)) (fun i => nilL v (F₂ i)))) := by
      rw [hT, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      rcases x with j | j | j | j
      · exact Submodule.subset_span ⟨Sum.inl j, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
      · change nilL v (nilL v (F₁ j)) ∈ _
        rw [nilL_nilL hv]
        exact Submodule.zero_mem _
      · change nilL v (nilL v (F₂ j)) ∈ _
        rw [nilL_nilL hv]
        exact Submodule.zero_mem _
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_range_le_card (R := K)
      (Sum.elim (fun i => nilL v (F₁ i)) (fun i => nilL v (F₂ i)))
    rw [Fintype.card_sum, Fintype.card_fin] at h2
    unfold Set.finrank at h2
    omega

end IsSwapFamily

theorem exists_swap_family [Finite K] [CharP K 2] {v : StatedSp n K} (hv : v * v = 1) :
    ∀ d : ℕ, 2 * d + 1 ≤ Module.finrank K (LinearMap.range (nilL v)) →
      ∃ F₁ F₂ : Fin d → Fin n ⊕ Fin n → K, IsSwapFamily v F₁ F₂
  | 0, _ => ⟨Fin.elim0, Fin.elim0, IsSwapFamily.zero v _ _⟩
  | d + 1, hd => by
    obtain ⟨F₁, F₂, hF⟩ := exists_swap_family hv d (by omega)
    obtain ⟨hT, hNT, hk⟩ := hF.span_gen hv
    obtain ⟨a, ha, b, hb, hab, hQa, hQb, hβ⟩ := exists_swap_step hv hT hNT hk (by omega)
    have hgen : ∀ {z}, z ∈ (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal
        (Submodule.span K (Set.range (IsSwapFamily.gen v F₁ F₂))) → ∀ i,
        form (F₁ i) z = 0 ∧ form (F₂ i) z = 0 ∧ form (nilL v (F₁ i)) z = 0 ∧
          form (nilL v (F₂ i)) z = 0 := fun hz i =>
      ⟨mem_orth_iff.mp hz _ (IsSwapFamily.gen_mem_span (Sum.inl i)),
        mem_orth_iff.mp hz _ (IsSwapFamily.gen_mem_span (Sum.inr (Sum.inl i))),
        mem_orth_iff.mp hz _ (IsSwapFamily.gen_mem_span (Sum.inr (Sum.inr (Sum.inl i)))),
        mem_orth_iff.mp hz _ (IsSwapFamily.gen_mem_span (Sum.inr (Sum.inr (Sum.inr i))))⟩
    exact ⟨_, _, hF.snoc hv hab hQa hQb hβ (hgen ha) (hgen hb)⟩

theorem IsSpFamily.append {m : ℕ} {u₀ w₀ u₁ w₁ : Fin m → Fin n ⊕ Fin n → K}
    (h₀ : IsSpFamily u₀ w₀) (h₁ : IsSpFamily u₁ w₁)
    (c₁ : ∀ i j, form (u₀ i) (u₁ j) = 0) (c₂ : ∀ i j, form (u₀ i) (w₁ j) = 0)
    (c₃ : ∀ i j, form (w₀ i) (u₁ j) = 0) (c₄ : ∀ i j, form (w₀ i) (w₁ j) = 0) :
    IsSpFamily (fun k => Sum.elim u₀ u₁ (finSumFinEquiv.symm k))
      (fun k => Sum.elim w₀ w₁ (finSumFinEquiv.symm k)) := by
  have hrev : ∀ {x y : Fin n ⊕ Fin n → K}, form x y = 0 → form y x = 0 := fun hxy => by
    rw [form_antisymm, hxy, neg_zero]
  refine ⟨fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective k
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective l
    simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
    rcases x with i | i <;> rcases y with j | j
    · simp only [Sum.elim_inl, Sum.inl.injEq]
      exact h₀.pair i j
    · simp only [Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ↓reduceIte]
      exact c₂ i j
    · simp only [Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ↓reduceIte]
      exact hrev (c₃ j i)
    · simp only [Sum.elim_inr, Sum.inr.injEq]
      exact h₁.pair i j
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective k
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective l
    simp only [Equiv.symm_apply_apply]
    rcases x with i | i <;> rcases y with j | j
    · exact h₀.uu i j
    · exact c₁ i j
    · exact hrev (c₁ j i)
    · exact h₁.uu i j
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective k
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective l
    simp only [Equiv.symm_apply_apply]
    rcases x with i | i <;> rcases y with j | j
    · exact h₀.ww i j
    · exact c₄ i j
    · exact hrev (c₄ j i)
    · exact h₁.ww i j

namespace IsSwapFamily

variable [CharP K 2] {v : StatedSp n K} {m : ℕ} {F₁ F₂ : Fin m → Fin n ⊕ Fin n → K}

theorem isSpFamily (hv : v * v = 1) (h : IsSwapFamily v F₁ F₂) :
    IsSpFamily (fun k => Sum.elim F₂ (fun i => mat n K v *ᵥ F₂ i) (finSumFinEquiv.symm k))
      (fun k => Sum.elim (fun i => mat n K v *ᵥ F₁ i) F₁ (finSumFinEquiv.symm k)) := by
  have hnn : ∀ a b : Fin n ⊕ Fin n → K, form (nilL v a) (nilL v b) = 0 :=
    fun a b => form_nilL_nilL hv a b
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine IsSpFamily.append ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩ (fun i j => ?_) (fun i j => ?_)
    (fun i j => ?_) (fun i j => ?_)
  · rw [mulVec_eq_add_nilL, form_add_right, h.o21, h.b21 hv, zero_add]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij.symm]
    · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  · exact h.o22 i j
  · rw [mulVec_eq_add_nilL, mulVec_eq_add_nilL, form_add_left, form_add_right, form_add_right,
      h.o11, h.b11, h.nb11 hv, hnn, add_zero, add_zero]
  · rw [mulVec_eq_add_nilL, form_add_left, h.o21, h.nb21 hv, zero_add]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij.symm]
    · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  · rw [mulVec_eq_add_nilL, mulVec_eq_add_nilL, form_add_left, form_add_right, form_add_right,
      h.o22, h.b22, h.nb22 hv, hnn, add_zero, add_zero]
  · exact h.o11 i j
  · rw [mulVec_eq_add_nilL, form_add_right, h.o22, h.b22, add_zero]
  · exact h.o21 i j
  · rw [mulVec_eq_add_nilL, mulVec_eq_add_nilL, form_add_left, form_add_right, form_add_right,
      h.o12, h.b12, h.nb12 hv, hnn, zero_add, add_zero]
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      linear_combination h2
    · rw [ite_eq_right hij, add_zero]
  · rw [mulVec_eq_add_nilL, form_add_left, h.o11, h.nb11 hv, add_zero]

end IsSwapFamily

theorem blockSwap_castAdd {d : ℕ} (hdn : d + d ≤ n) (i : Fin d) :
    blockSwap n d (Fin.castLE hdn (Fin.castAdd d i)) = Fin.castLE hdn (Fin.natAdd d i) := by
  rw [blockSwap_apply, blockSwapFun, dite_eq_left ⟨by simp, by simp; omega⟩]
  ext
  simp only [Fin.val_castLE, Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem blockSwap_natAdd {d : ℕ} (hdn : d + d ≤ n) (i : Fin d) :
    blockSwap n d (Fin.castLE hdn (Fin.natAdd d i)) = Fin.castLE hdn (Fin.castAdd d i) := by
  rw [blockSwap_apply, blockSwapFun, dite_eq_right (by simp),
    dite_eq_left ⟨by simp, by simp; omega⟩]
  ext
  simp only [Fin.val_castLE, Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem mem_blockCoords_zero_one {d : ℕ} {t : Fin n ⊕ Fin n}
    (ht : t ∈ blockCoords n d 0 ∪ blockCoords n d 1) : (plane t : ℕ) < d + d := by
  rcases ht with ht | ht
  · have := ht.2
    simp only [zero_add, one_mul] at this
    omega
  · have := ht.2
    omega

theorem swap_of_family [CharP K 2] {v : StatedSp n K} (hv : v * v = 1) {d : ℕ}
    {F₁ F₂ : Fin d → Fin n ⊕ Fin n → K} (hF : IsSwapFamily v F₁ F₂) (hdn : d + d ≤ n) :
    ∃ g : StatedSp n K, (permSp K (blockSwap n d))⁻¹ * (g * v * g⁻¹) ∈
      suppGroup (blockCoords n d 0 ∪ blockCoords n d 1)ᶜ := by
  obtain ⟨A, hA⟩ := exists_sp_of_family hdn (hF.isSpFamily hv)
  set P := permSp K (blockSwap n d) with hP
  have hPcol : ∀ x, mat n K P *ᵥ Pi.single x 1 =
      Pi.single (Sum.map (blockSwap n d) (blockSwap n d) x) 1 := fun x =>
    WitClSp.mat_permSp_mulVec_single _ x
  have hPinv : ∀ x y, mat n K P *ᵥ Pi.single x 1 = Pi.single y 1 →
      mat n K P⁻¹ *ᵥ Pi.single y 1 = Pi.single x 1 := fun x y h => by
    rw [← h, mulVec_inv_mulVec]
  have hAinv : ∀ x (z : Fin n ⊕ Fin n → K), mat n K A *ᵥ Pi.single x 1 = z →
      mat n K A⁻¹ *ᵥ z = Pi.single x 1 := fun x z h => by
    rw [← h, mulVec_inv_mulVec]
  have hvv : ∀ z : Fin n ⊕ Fin n → K, mat n K v *ᵥ (mat n K v *ᵥ z) = z :=
    fun z => mulVec_mulVec_self hv z
  have hkey : ∀ (x : Fin d ⊕ Fin d) (t : Fin n ⊕ Fin n),
      (t = Sum.inl (Fin.castLE hdn (finSumFinEquiv x)) ∨
        t = Sum.inr (Fin.castLE hdn (finSumFinEquiv x))) →
      mat n K (P⁻¹ * (A⁻¹ * v * A⁻¹⁻¹)) *ᵥ Pi.single t 1 = Pi.single t 1 := by
    intro x t ht
    rw [inv_inv, map_mul, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    rcases x with i | i <;> rcases ht with rfl | rfl
    · have h1 := (hA (Fin.castAdd d i)).1
      have h2 := (hA (Fin.natAdd d i)).1
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Sum.elim_inl, Sum.elim_inr] at h1 h2
      rw [finSumFinEquiv_apply_left, h1, ← h2, hAinv _ _ rfl]
      exact hPinv _ _ (by rw [hPcol, Sum.map_inl, blockSwap_castAdd])
    · have h1 := (hA (Fin.castAdd d i)).2
      have h2 := (hA (Fin.natAdd d i)).2
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Sum.elim_inl, Sum.elim_inr] at h1 h2
      rw [finSumFinEquiv_apply_left, h1, hvv, ← h2, hAinv _ _ rfl]
      exact hPinv _ _ (by rw [hPcol, Sum.map_inr, blockSwap_castAdd])
    · have h1 := (hA (Fin.natAdd d i)).1
      have h2 := (hA (Fin.castAdd d i)).1
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Sum.elim_inl, Sum.elim_inr] at h1 h2
      rw [finSumFinEquiv_apply_right, h1, hvv, ← h2, hAinv _ _ rfl]
      exact hPinv _ _ (by rw [hPcol, Sum.map_inl, blockSwap_natAdd])
    · have h1 := (hA (Fin.natAdd d i)).2
      have h2 := (hA (Fin.castAdd d i)).2
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Sum.elim_inl, Sum.elim_inr] at h1 h2
      rw [finSumFinEquiv_apply_right, h1, ← h2, hAinv _ _ rfl]
      exact hPinv _ _ (by rw [hPcol, Sum.map_inr, blockSwap_natAdd])
  refine ⟨A⁻¹, ?_⟩
  rw [mem_suppGroup_iff (parClosed_union (parClosed_blockCoords n d 0)
    (parClosed_blockCoords n d 1)).compl]
  intro t ht r
  rw [Set.mem_compl_iff, not_not] at ht
  have hlt := mem_blockCoords_zero_one ht
  obtain ⟨x, hx⟩ := finSumFinEquiv.surjective (⟨plane t, hlt⟩ : Fin (d + d))
  have ht' : t = Sum.inl (Fin.castLE hdn (finSumFinEquiv x)) ∨
      t = Sum.inr (Fin.castLE hdn (finSumFinEquiv x)) := by
    rw [hx]
    rcases t with k | k
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [mat_apply_eq_mulVec, hkey x t ht', Pi.single_apply, Matrix.one_apply]

end WitSpBlk

open WitSpBlk CFSG.ClassicalInvolution.Models.SymplecticPairs in
theorem spBlockFixOrSwapInput_holds : SpBlockFixOrSwapInput := by
  intro K _ _ _ n d hd1 hd3 v hv
  by_cases hfix : n + d ≤ Module.finrank K (fixSpace v)
  · obtain ⟨x, y, hxy, hmem⟩ := exists_fix_family v d hfix
    obtain ⟨g, hg⟩ := fix_of_family (by omega) hxy hmem
    exact ⟨g, Or.inl hg⟩
  · have hker : LinearMap.ker (WitClSp.nilL v) = fixSpace v := by
      ext z
      rw [LinearMap.mem_ker, WitClSp.mem_fixSpace_iff_nilL]
    have hrk := LinearMap.finrank_range_add_finrank_ker (WitClSp.nilL v)
    rw [hker, WitClSp.finrank_ambient] at hrk
    obtain ⟨F₁, F₂, hF⟩ := exists_swap_family hv d (by omega)
    obtain ⟨g, hg⟩ := swap_of_family hv hF (by omega)
    exact ⟨g, Or.inr hg⟩

end CFSG.StandardType
