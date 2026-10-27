module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofAffine

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGForkShapeBCD {Λ : Type*} (C : Matrix Λ Λ ℤ) (b : Λ) : Prop :=
  ∃ (n : ℕ) (e : Fin (n + 3) ≃ Λ), e 0 = b ∧
    ((∀ i j, C (e i) (e j) = CartanMatrix.B (n + 3) i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.C (n + 3) i j) ∨
      (1 ≤ n ∧ ∀ i j, C (e i) (e j) = CartanMatrix.D (n + 3) i j))

section Rev

variable {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {p : ℕ} {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V] {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V} {ha : V}
  {αa : Module.Dual (ZMod p) V} {b c : Λ}

theorem ggChainPairing_rev (hF : GGForkPairing C b c h α ha αa) {ν : ℕ → Λ} {m : ℕ}
    (hb : ν 0 = b) (hc : ν 1 = c) (hinj : ∀ k l, k ≤ m → l ≤ m → ν k = ν l → k = l)
    (hA : ∀ k l, 1 ≤ k → k ≤ m → 1 ≤ l → l ≤ m →
      C (ν k) (ν l) = if k = l then 2 else if k + 1 = l ∨ l + 1 = k then -1 else 0) :
    GGChainPairing m (fun j => h (ν (m - j))) (fun j => α (ν (m - j))) ha αa ∧
      GGChainPairing m (fun j => h (ν (m - j))) (fun j => α (ν (m - j))) (h b) (α b) := by
  have hne : ∀ j, j < m → ν (m - j) ≠ b := fun j hj h' => by
    rw [← hb] at h'
    have := hinj _ _ (by omega) (by omega) h'
    omega
  have hcj : ∀ j, j < m → (ν (m - j) = c ↔ j + 1 = m) := fun j hj => by
    rw [← hc]
    constructor
    · intro h'
      have := hinj _ _ (by omega) (by omega) h'
      omega
    · intro h'
      rw [show m - j = 1 by omega]
  have hjj : ∀ j k, j < m → k < m → α (ν (m - j)) (h (ν (m - k))) =
      if j = k then 2 else if j + 1 = k ∨ k + 1 = j then -1 else 0 := by
    intro j k hj hk
    rw [hF.pair, hA _ _ (by omega) (by omega) (by omega) (by omega)]
    split_ifs <;> first | (exfalso; omega) | simp
  refine ⟨⟨hjj, fun j hj => ?_, fun j hj => ?_, hF.aa⟩, ⟨hjj, fun j hj => ?_, fun j hj => ?_,
    hF.self b⟩⟩
  · rw [hF.aR _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
  · rw [hF.aL _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
  · rw [hF.pair, hF.bR _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
      simp
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
      simp
  · rw [hF.pair, hF.bL _ (hne j hj)]
    by_cases h' : j + 1 = m
    · rw [ite_eq_left ((hcj j hj).mpr h'), ite_eq_left h']
      simp
    · rw [ite_eq_right (fun h'' => h' ((hcj j hj).mp h'')), ite_eq_right h']
      simp

theorem GGForkPairing.far_node (hF : GGForkPairing C b c h α ha αa) {ν : ℕ → Λ} {N k : ℕ}
    (hb : ν 0 = b) (hc : ν 1 = c) (hinj : ∀ k l, k ≤ N → l ≤ N → ν k = ν l → k = l)
    (hk2 : 2 ≤ k) (hkN : k ≤ N) :
    α (ν k) ha = 0 ∧ αa (h (ν k)) = 0 ∧ α (ν k) (h b) = 0 ∧ α b (h (ν k)) = 0 := by
  have hb' : ν k ≠ b := fun h' => by
    rw [← hb] at h'
    have := hinj _ _ hkN (by omega) h'
    omega
  have hc' : ν k ≠ c := fun h' => by
    rw [← hc] at h'
    have := hinj _ _ hkN (by omega) h'
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF.aR _ hb', ite_eq_right hc']
  · rw [hF.aL _ hb', ite_eq_right hc']
  · rw [hF.pair, hF.bR _ hb', ite_eq_right hc', Int.cast_zero]
  · rw [hF.pair, hF.bL _ hb', ite_eq_right hc', Int.cast_zero]

end Rev

section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
  {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V} {b c : Λ}

theorem ggFork_false_of_tailBC (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤) (hu : αa (h b) = 0)
    {n : ℕ} {ν : ℕ → Λ} (hb : ν 0 = b) (hc : ν 1 = c)
    (hinj : ∀ k l, k ≤ n + 2 → l ≤ n + 2 → ν k = ν l → k = l)
    (hsurj : ∀ i, ∃ k ≤ n + 2, ν k = i)
    (hA : ∀ k l, 1 ≤ k → k ≤ n + 1 → 1 ≤ l → l ≤ n + 1 →
      C (ν k) (ν l) = if k = l then 2 else if k + 1 = l ∨ l + 1 = k then -1 else 0)
    (htl : ∀ k, 1 ≤ k → k ≤ n → C (ν k) (ν (n + 2)) = 0 ∧ C (ν (n + 2)) (ν k) = 0)
    (hk : C (ν (n + 1)) (ν (n + 2)) * C (ν (n + 2)) (ν (n + 1)) = 2) : False := by
  have hv : α b ha = 0 := (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).1.mp hu
  obtain ⟨hPa, hPb⟩ := ggChainPairing_rev hF (m := n + 1) hb hc
    (fun k l hk hl => hinj k l (by omega) (by omega)) hA
  obtain ⟨hta, hat, htb, hbt⟩ := hF.far_node hb hc hinj (k := n + 2) (by omega) le_rfl
  have hhaS := (linearIndependent_ggOptFam.mp hind).2
  refine ggFork_affine_false_BC hp2 hNT ι (m := n + 1) (by omega)
    (φJ := fun j => φ (ν (n + 1 - j))) (φt := φ (ν (n + 2))) (fun j _ => hφ _) hφa (hφ b) (hφ _)
    hPa hPb (fun j _ w => hlin _ w) hlina (hlin b) (hlin _) (hF.self _)
    (k₁ := (C (ν (n + 1)) (ν (n + 2)) : ZMod p)) (k₂ := (C (ν (n + 2)) (ν (n + 1)) : ZMod p))
    (fun j hj => ?_) (fun j hj => ?_) ?_ hta hat htb hbt hu hv ?_ ?_
  · rw [hF.pair]
    split_ifs with hj0
    · subst hj0
      rfl
    · rw [(htl (n + 1 - j) (by omega) (by omega)).1, Int.cast_zero]
  · rw [hF.pair]
    split_ifs with hj0
    · subst hj0
      rfl
    · rw [(htl (n + 1 - j) (by omega) (by omega)).2, Int.cast_zero]
  · rw [← Int.cast_mul, hk]
    norm_num
  · rw [eq_top_iff, ← hspan]
    refine Submodule.span_mono ?_
    rintro _ ⟨γ, rfl⟩
    rcases γ with _ | i
    · exact Or.inl (Set.mem_insert _ _)
    · obtain ⟨k, hk, rfl⟩ := hsurj i
      rw [ggOptFam_some]
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · rw [show k = 0 by omega, hb]
        exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · rcases Nat.lt_or_ge k (n + 2) with hk2 | hk2
        · exact Or.inr ⟨n + 1 - k, Set.mem_Iio.mpr (by omega),
            congrArg (fun k => h (ν k)) (by omega : n + 1 - (n + 1 - k) = k)⟩
        · rw [show k = n + 2 by omega]
          exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · intro hmem
    refine hhaS (Submodule.span_mono ?_ hmem)
    rintro _ ((rfl | rfl) | ⟨j, -, rfl⟩)
    · exact ⟨b, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem ggFork_false_of_tailD (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤) (hu : αa (h b) = 0)
    {n : ℕ} (hn : 1 ≤ n) {ν : ℕ → Λ} (hb : ν 0 = b) (hc : ν 1 = c)
    (hinj : ∀ k l, k ≤ n + 2 → l ≤ n + 2 → ν k = ν l → k = l)
    (hsurj : ∀ i, ∃ k ≤ n + 2, ν k = i)
    (hA : ∀ k l, 1 ≤ k → k ≤ n → 1 ≤ l → l ≤ n →
      C (ν k) (ν l) = if k = l then 2 else if k + 1 = l ∨ l + 1 = k then -1 else 0)
    (htl : ∀ k, 1 ≤ k → k < n → C (ν k) (ν (n + 1)) = 0 ∧ C (ν (n + 1)) (ν k) = 0 ∧
      C (ν k) (ν (n + 2)) = 0 ∧ C (ν (n + 2)) (ν k) = 0)
    (hend : C (ν n) (ν (n + 1)) = -1 ∧ C (ν (n + 1)) (ν n) = -1 ∧ C (ν n) (ν (n + 2)) = -1 ∧
      C (ν (n + 2)) (ν n) = -1)
    (hts : C (ν (n + 1)) (ν (n + 2)) = 0 ∧ C (ν (n + 2)) (ν (n + 1)) = 0) : False := by
  have hv : α b ha = 0 := (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).1.mp hu
  obtain ⟨hPa, hPb⟩ := ggChainPairing_rev hF (m := n) hb hc
    (fun k l hk hl => hinj k l (by omega) (by omega)) hA
  obtain ⟨hta, hat, htb, hbt⟩ := hF.far_node hb hc hinj (k := n + 1) (by omega) (by omega)
  obtain ⟨hsa, has, hsb, hbs⟩ := hF.far_node hb hc hinj (k := n + 2) (by omega) le_rfl
  have hhaS := (linearIndependent_ggOptFam.mp hind).2
  refine ggFork_affine_false_D hp2 hNT ι (m := n) hn (φJ := fun j => φ (ν (n - j)))
    (φt := φ (ν (n + 1))) (φs := φ (ν (n + 2))) (fun j _ => hφ _) hφa (hφ b) (hφ _) (hφ _)
    hPa hPb (fun j _ w => hlin _ w) hlina (hlin b) (hlin _) (hlin _) (hF.self _) (hF.self _)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) ?_ ?_ hta hat htb hbt
    hsa has hsb hbs hu hv ?_ ?_
  · rw [hF.pair]
    split_ifs with hj0
    · subst hj0
      rw [Nat.sub_zero, hend.1, Int.cast_neg, Int.cast_one]
    · rw [(htl (n - j) (by omega) (by omega)).1, Int.cast_zero]
  · rw [hF.pair]
    split_ifs with hj0
    · subst hj0
      rw [Nat.sub_zero, hend.2.1, Int.cast_neg, Int.cast_one]
    · rw [(htl (n - j) (by omega) (by omega)).2.1, Int.cast_zero]
  · rw [hF.pair]
    split_ifs with hj0
    · subst hj0
      rw [Nat.sub_zero, hend.2.2.1, Int.cast_neg, Int.cast_one]
    · rw [(htl (n - j) (by omega) (by omega)).2.2.1, Int.cast_zero]
  · rw [hF.pair]
    split_ifs with hj0
    · subst hj0
      rw [Nat.sub_zero, hend.2.2.2, Int.cast_neg, Int.cast_one]
    · rw [(htl (n - j) (by omega) (by omega)).2.2.2, Int.cast_zero]
  · rw [hF.pair, hts.1, Int.cast_zero]
  · rw [hF.pair, hts.2, Int.cast_zero]
  · rw [eq_top_iff, ← hspan]
    refine Submodule.span_mono ?_
    rintro _ ⟨γ, rfl⟩
    rcases γ with _ | i
    · exact Or.inl (Set.mem_insert _ _)
    · obtain ⟨k, hk, rfl⟩ := hsurj i
      rw [ggOptFam_some]
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · rw [show k = 0 by omega, hb]
        exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · rcases Nat.lt_or_ge k (n + 1) with hk2 | hk2
        · exact Or.inr ⟨n - k, Set.mem_Iio.mpr (by omega),
            congrArg (fun k => h (ν k)) (by omega : n - (n - k) = k)⟩
        · rcases Nat.lt_or_ge k (n + 2) with hk3 | hk3
          · rw [show k = n + 1 by omega]
            exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
              (Set.mem_insert _ _)))
          · rw [show k = n + 2 by omega]
            exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
              (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  · intro hmem
    refine hhaS (Submodule.span_mono ?_ hmem)
    rintro _ ((rfl | rfl | rfl) | ⟨j, -, rfl⟩)
    · exact ⟨b, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

end GG

section Node

variable {Λ : Type*} {n : ℕ} {C : Matrix Λ Λ ℤ}

@[expose] def ggForkNode (e : Fin (n + 3) ≃ Λ) (k : ℕ) : Λ :=
  e ⟨min k (n + 2), by omega⟩

theorem ggForkNode_of_le (e : Fin (n + 3) ≃ Λ) {k : ℕ} (hk : k ≤ n + 2) :
    ggForkNode e k = e ⟨k, by omega⟩ := by
  simp [ggForkNode, Nat.min_eq_left hk]

theorem ggForkNode_zero (e : Fin (n + 3) ≃ Λ) : ggForkNode e 0 = e 0 := by
  rw [ggForkNode_of_le e (Nat.zero_le _)]
  rfl

theorem ggForkNode_inj (e : Fin (n + 3) ≃ Λ) (k l : ℕ) (hk : k ≤ n + 2) (hl : l ≤ n + 2)
    (h : ggForkNode e k = ggForkNode e l) : k = l := by
  rw [ggForkNode_of_le e hk, ggForkNode_of_le e hl] at h
  exact congrArg Fin.val (e.injective h)

theorem ggForkNode_surj (e : Fin (n + 3) ≃ Λ) (i : Λ) : ∃ k ≤ n + 2, ggForkNode e k = i := by
  have := (e.symm i).isLt
  exact ⟨e.symm i, by omega, by rw [ggForkNode_of_le e (by omega)]; simp⟩

theorem ggForkNode_B (e : Fin (n + 3) ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.B (n + 3) i j) {k l : ℕ} (hk : k ≤ n + 2)
    (hl : l ≤ n + 2) : C (ggForkNode e k) (ggForkNode e l) =
      if k = l then 2 else if k + 1 = l then (if l = n + 2 then -2 else -1)
        else if l + 1 = k then -1 else 0 := by
  rw [ggForkNode_of_le e hk, ggForkNode_of_le e hl, hC]
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

theorem ggForkNode_C (e : Fin (n + 3) ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.C (n + 3) i j) {k l : ℕ} (hk : k ≤ n + 2)
    (hl : l ≤ n + 2) : C (ggForkNode e k) (ggForkNode e l) =
      if k = l then 2 else if k + 1 = l then -1
        else if l + 1 = k then (if k = n + 2 then -2 else -1) else 0 := by
  rw [ggForkNode_of_le e hk, ggForkNode_of_le e hl, hC]
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

theorem ggForkNode_D (e : Fin (n + 3) ≃ Λ) (hn : 1 ≤ n)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D (n + 3) i j) {k l : ℕ} (hk : k ≤ n + 2)
    (hl : l ≤ n + 2) : C (ggForkNode e k) (ggForkNode e l) =
      if k = l then 2 else if (k + 1 = l ∧ l ≤ n) ∨ (l + 1 = k ∧ k ≤ n) ∨
        (k = n ∧ n + 1 ≤ l) ∨ (l = n ∧ n + 1 ≤ k) then -1 else 0 := by
  rw [ggForkNode_of_le e hk, ggForkNode_of_le e hl, hC]
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

end Node

section Shape

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
  {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V} {b c : Λ}

theorem ggFork_label_ne_zero_of_shapeBCD (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤)
    (hS : GGForkShapeBCD C b) : αa (h b) ≠ 0 := by
  intro hu
  obtain ⟨n, e, he0, hBC | hBC | ⟨hn, hD⟩⟩ := hS
  · have hnat := fun k l (hk : k ≤ n + 2) (hl : l ≤ n + 2) => ggForkNode_B e hBC hk hl
    have hb : ggForkNode e 0 = b := by rw [ggForkNode_zero, he0]
    have hc : ggForkNode e 1 = c := by
      obtain ⟨k, hk, hkc⟩ := ggForkNode_surj e c
      have h1 : C b c = -1 := by rw [hF.bL _ hF.ne.symm, ite_eq_left rfl]
      rw [← hb, ← hkc, hnat 0 k (by omega) hk] at h1
      rw [← hkc]
      congr 1
      split_ifs at h1 <;> first | omega | contradiction
    exact ggFork_false_of_tailBC hp2 hNT ι hF hφ hφa hlin hlina hind hspan hu hb hc
      (ggForkNode_inj e) (ggForkNode_surj e)
      (fun k l _ hk _ hl => by rw [hnat k l (by omega) (by omega)]; split_ifs <;> omega)
      (fun k _ hk => ⟨by rw [hnat k (n + 2) (by omega) le_rfl]; split_ifs <;> omega,
        by rw [hnat (n + 2) k le_rfl (by omega)]; split_ifs <;> omega⟩)
      (by rw [hnat (n + 1) (n + 2) (by omega) le_rfl, hnat (n + 2) (n + 1) le_rfl (by omega)]
          split_ifs <;> omega)
  · have hnat := fun k l (hk : k ≤ n + 2) (hl : l ≤ n + 2) => ggForkNode_C e hBC hk hl
    have hb : ggForkNode e 0 = b := by rw [ggForkNode_zero, he0]
    have hc : ggForkNode e 1 = c := by
      obtain ⟨k, hk, hkc⟩ := ggForkNode_surj e c
      have h1 : C b c = -1 := by rw [hF.bL _ hF.ne.symm, ite_eq_left rfl]
      rw [← hb, ← hkc, hnat 0 k (by omega) hk] at h1
      rw [← hkc]
      congr 1
      split_ifs at h1 <;> omega
    exact ggFork_false_of_tailBC hp2 hNT ι hF hφ hφa hlin hlina hind hspan hu hb hc
      (ggForkNode_inj e) (ggForkNode_surj e)
      (fun k l _ hk _ hl => by rw [hnat k l (by omega) (by omega)]; split_ifs <;> omega)
      (fun k _ hk => ⟨by rw [hnat k (n + 2) (by omega) le_rfl]; split_ifs <;> omega,
        by rw [hnat (n + 2) k le_rfl (by omega)]; split_ifs <;> omega⟩)
      (by rw [hnat (n + 1) (n + 2) (by omega) le_rfl, hnat (n + 2) (n + 1) le_rfl (by omega)]
          split_ifs <;> omega)
  · have hnat := fun k l (hk : k ≤ n + 2) (hl : l ≤ n + 2) => ggForkNode_D e hn hD hk hl
    have hb : ggForkNode e 0 = b := by rw [ggForkNode_zero, he0]
    have hc : ggForkNode e 1 = c := by
      obtain ⟨k, hk, hkc⟩ := ggForkNode_surj e c
      have h1 : C b c = -1 := by rw [hF.bL _ hF.ne.symm, ite_eq_left rfl]
      rw [← hb, ← hkc, hnat 0 k (by omega) hk] at h1
      rw [← hkc]
      congr 1
      split_ifs at h1
      simp only [false_and, false_or] at *
      omega
    exact ggFork_false_of_tailD hp2 hNT ι hF hφ hφa hlin hlina hind hspan hu hn hb hc
      (ggForkNode_inj e) (ggForkNode_surj e)
      (fun k l _ hk _ hl => by rw [hnat k l (by omega) (by omega)]; split_ifs <;> omega)
      (fun k _ hk => ⟨by rw [hnat k (n + 1) (by omega) (by omega)]; split_ifs <;> omega,
        by rw [hnat (n + 1) k (by omega) (by omega)]; split_ifs <;> omega,
        by rw [hnat k (n + 2) (by omega) le_rfl]; split_ifs <;> omega,
        by rw [hnat (n + 2) k le_rfl (by omega)]; split_ifs <;> omega⟩)
      ⟨by rw [hnat n (n + 1) (by omega) (by omega)]; split_ifs <;> omega,
        by rw [hnat (n + 1) n (by omega) (by omega)]; split_ifs <;> omega,
        by rw [hnat n (n + 2) (by omega) le_rfl]; split_ifs <;> omega,
        by rw [hnat (n + 2) n le_rfl (by omega)]; split_ifs <;> omega⟩
      ⟨by rw [hnat (n + 1) (n + 2) (by omega) le_rfl]; split_ifs <;> omega,
        by rw [hnat (n + 2) (n + 1) le_rfl (by omega)]; split_ifs <;> omega⟩

end Shape

end CFSG.StandardType
