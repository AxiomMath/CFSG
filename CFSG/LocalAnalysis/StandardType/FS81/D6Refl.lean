module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ReflAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

private abbrev d6RootType : Type := {e : Coords 7 // IsD6Root e}

private noncomputable instance d6RootTypeFintype : Fintype d6RootType := by
  classical
  exact Fintype.ofFinite _

private theorem card_d6RootType : Nat.card d6RootType = 126 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_isD6Root

theorem natCard_le_mul_natCard_range {α β : Type} [Fintype α] [Fintype β]
    (f : α → β) (n : ℕ)
    (h : ∀ b ∈ Set.range f, Nat.card {a : α // f a = b} ≤ n) :
    Nat.card α ≤ Nat.card (Set.range f) * n := by
  classical
  have hfib : ∀ b ∈ (Finset.univ : Finset α).image f,
      ((Finset.univ : Finset α).filter fun a => f a = b).card ≤ n := by
    intro b hb
    have hbr : b ∈ Set.range f := by
      obtain ⟨a, -, hfa⟩ := Finset.mem_image.mp hb
      exact ⟨a, hfa⟩
    have hle := h b hbr
    have hcard : ((Finset.univ : Finset α).filter fun a => f a = b).card =
        Nat.card {a : α // f a = b} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rwa [hcard]
  have hle := Finset.card_le_mul_card_image (Finset.univ : Finset α) n hfib
  have himg : Nat.card (Set.range f) = ((Finset.univ : Finset α).image f).card := by
    have hset : (Set.range f) = ((Finset.univ : Finset α).image f : Set β) := by
      ext b
      simp [Set.mem_range, Finset.mem_image]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  calc Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
    _ ≤ n * ((Finset.univ : Finset α).image f).card := hle
    _ = Nat.card (Set.range f) * n := by rw [← himg, mul_comm]


private theorem wt_eq_two_of_isD6Root_of_zero {e : Coords 7} (h : IsD6Root e) (h0 : e 0 = 0) :
    wt e = 2 := by
  rcases h with ⟨_, h1⟩ | ⟨h2, _⟩ | ⟨h7, _⟩
  · exact absurd h0 h1
  · exact h2
  · have hle := wt_le_of_apply_zero (n := 6) h0
    omega

private theorem d6Refl_single_zero_eq_diagonal :
    d6Refl (Pi.single (0 : Fin 7) 1) =
      Matrix.diagonal (fun i : Fin 7 => if i = 0 then (-1 : ZMod 3) else 1) := by
  ext i j
  rw [d6Refl, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst i
    by_cases hj : j = 0
    · subst j
      simp
      decide
    · simp [hj]
  · by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := fun h => hij h.symm
      simp [hij, hj]
    · simp [hij, hi]

private theorem d6Refl_single_zero_sq :
    d6Refl (Pi.single (0 : Fin 7) 1) * d6Refl (Pi.single (0 : Fin 7) 1) = 1 := by
  rw [d6Refl_single_zero_eq_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst i
    by_cases hi : j = 0
    · subst j
      decide
    · simp [hi]
  · simp [hij]

private theorem mem_realized_centralizer_of_mulVec_single_eq {G : Type} [Group G] {b₀ : G}
    {B : Basis3 G 7} (hB0 : B.b 0 = b₀)
    {A : Matrix (Fin 7) (Fin 7) (ZMod 3)} (hA : A ∈ B.realized ⊤)
    (hAe : A *ᵥ Pi.single (0 : Fin 7) 1 = Pi.single (0 : Fin 7) 1) :
    A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
  obtain ⟨g, -, hActs⟩ := hA
  refine ⟨g, ?_, hActs⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcol : (fun i => A i 0) = Pi.single (0 : Fin 7) 1 := by
    have h := hAe
    rw [Matrix.mulVec_single_one] at h
    rwa [Matrix.col_apply'] at h
  have hb0 : B.vec (Pi.single (0 : Fin 7) 1) = b₀ := by
    rw [Basis3.vec_single, hB0]
  have h0 := hActs 0
  rw [hB0, hcol, hb0] at h0
  calc g * b₀ = (g * b₀ * g⁻¹) * g := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = b₀ * g := by rw [h0]

theorem exists_mem_realized_mulVec_eq {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7}
    (hB : Adapted B b₀ K E) (hrec : RecOutD6 B b₀) {v : Coords 7} (hv : IsD6Root v) :
    ∃ A ∈ B.realized ⊤, A *ᵥ Pi.single (0 : Fin 7) 1 = v := by
  classical
  have hcardX : Nat.card ↥(B.realized ⊤) = 2903040 := by
    have hle : Nat.card ↥(B.realized ⊤) ≤ Nat.card ↥(ggAutomizer ⊤ B.span) := by
      rw [card_realized_eq_card_ggInduced (B := B) (F := B.span) rfl ⊤]
      have hsub : (ggInduced ⊤ B.span : Set (MulAut ↥B.span)) ⊆
          (ggAutomizer ⊤ B.span : Set (MulAut ↥B.span)) := Subgroup.subset_closure
      exact Nat.card_mono (Set.toFinite _) hsub
    have hle' : Nat.card ↥(B.realized ⊤) ≤ 2903040 := by
      calc Nat.card ↥(B.realized ⊤) ≤ Nat.card ↥(ggAutomizer ⊤ B.span) := hle
        _ = 2903040 := hrec.1
    refine le_antisymm hle' ?_
    rw [← hrec.1]
    exact B.card_ggAutomizer_le ⊤
  have hcardC : Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) ≤ 23040 := by
    have hsub := realized_centralizer_subset_evenFix0_D6 hstd hB hrec
    calc Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G)))
        = (B.realized (Subgroup.centralizer ({b₀} : Set G))).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ (evenFix0 6).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card ↥(evenFix0 6) := (Nat.card_coe_set_eq _).symm
      _ ≤ 23040 := card_evenFix0_le
  have hcardF : Nat.card (d6XType B) = 2903040 := hcardX
  have hfib : ∀ b ∈ Set.range (d6MapX B),
      Nat.card {A : d6XType B // d6MapX B A = b} ≤ 23040 := by
    intro b hb
    obtain ⟨A₀, hA₀b⟩ := Set.mem_range.mp hb
    obtain ⟨B₀, hB₀X, hA₀B₀, hB₀A₀⟩ := exists_inv_mem_realized (H := ⊤) A₀.2
    let φ : {A : d6XType B // d6MapX B A = b} → ↥(d6CX b₀ B) := fun A =>
      ⟨B₀ * A.1.1, by
        have hAX : A.1.1 ∈ d6X B := A.1.2
        have hBMX : B₀ * A.1.1 ∈ d6X B := mul_mem_realized hB₀X hAX
        have hf : d6Map (B₀ * A.1.1) = Pi.single (0 : Fin 7) 1 := by
          show (B₀ * A.1.1) *ᵥ Pi.single (0 : Fin 7) 1 = Pi.single (0 : Fin 7) 1
          rw [← Matrix.mulVec_mulVec]
          have hAb : A.1.1 *ᵥ Pi.single (0 : Fin 7) 1 = b := A.2
          have hA₀b' : A₀.1 *ᵥ Pi.single (0 : Fin 7) 1 = b := hA₀b
          rw [hAb, ← hA₀b', Matrix.mulVec_mulVec, hB₀A₀, Matrix.one_mulVec]
        exact mem_realized_centralizer_of_mulVec_single_eq hB.2.1 hBMX hf⟩
    have hφ : Function.Injective φ := by
      intro A A' h
      apply Subtype.ext
      apply Subtype.ext
      have h1 : B₀ * A.1.1 = B₀ * A'.1.1 := congrArg Subtype.val h
      calc A.1.1 = (A₀.1 * B₀) * A.1.1 := by rw [hA₀B₀, one_mul]
        _ = A₀.1 * (B₀ * A.1.1) := by rw [mul_assoc]
        _ = A₀.1 * (B₀ * A'.1.1) := by rw [h1]
        _ = (A₀.1 * B₀) * A'.1.1 := by rw [mul_assoc]
        _ = A'.1.1 := by rw [hA₀B₀, one_mul]
    calc Nat.card {A : d6XType B // d6MapX B A = b}
        ≤ Nat.card ↥(d6CX b₀ B) := Nat.card_le_card_of_injective φ hφ
      _ ≤ 23040 := hcardC
  have himg : Set.range (d6MapX B) ⊆ {e : Coords 7 | IsD6Root e} := by
    intro w hw
    obtain ⟨A, rfl⟩ := Set.mem_range.mp hw
    exact isD6Root_mulVec_of_mem_realized hstd hB hrec A.2 isD6Root_single_zero
  have hroots_card : Nat.card {e : Coords 7 // IsD6Root e} = 126 := card_d6RootType
  have hrange_le : Nat.card (Set.range (d6MapX B)) ≤ 126 := by
    calc Nat.card (Set.range (d6MapX B)) = (Set.range (d6MapX B)).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({e : Coords 7 | IsD6Root e}).ncard := Set.ncard_le_ncard himg
      _ = Nat.card {e : Coords 7 // IsD6Root e} := (Nat.card_coe_set_eq _).symm
      _ = 126 := hroots_card
  have hle := natCard_le_mul_natCard_range (d6MapX B) 23040 hfib
  have hge : 126 ≤ Nat.card (Set.range (d6MapX B)) := by
    have h := hle
    rw [hcardF] at h
    have h' : 126 * 23040 ≤ Nat.card (Set.range (d6MapX B)) * 23040 := by
      calc 126 * 23040 = 2903040 := by norm_num
        _ ≤ Nat.card (Set.range (d6MapX B)) * 23040 := h
    exact Nat.le_of_mul_le_mul_right h' (by norm_num)
  have hrange_card : Nat.card (Set.range (d6MapX B)) = 126 :=
    le_antisymm hrange_le hge
  have hrange_set : Set.range (d6MapX B) = {e : Coords 7 | IsD6Root e} := by
    apply Set.eq_of_subset_of_ncard_le himg
    have h1 : ({e : Coords 7 | IsD6Root e}).ncard = 126 := by
      rw [← Nat.card_coe_set_eq]
      change Nat.card {e : Coords 7 // IsD6Root e} = 126
      exact hroots_card
    have h2 : (Set.range (d6MapX B)).ncard = 126 := by
      rw [← Nat.card_coe_set_eq]
      exact hrange_card
    rw [h1, h2]
  have hvRange : v ∈ Set.range (d6MapX B) := by
    rw [hrange_set]
    exact hv
  obtain ⟨A, hAv⟩ := Set.mem_range.mp hvRange
  exact ⟨A.1, A.2, hAv⟩

theorem diagNeg_mem_realized {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) :
    Matrix.diagonal (fun i : Fin 7 => if i = 0 then (-1 : ZMod 3) else 1) ∈ B.realized ⊤ := by
  classical
  let e0 : Coords 7 := Pi.single (0 : Fin 7) 1
  have ht0 : d6Refl e0 = Matrix.diagonal (fun i : Fin 7 =>
      if i = 0 then (-1 : ZMod 3) else 1) := d6Refl_single_zero_eq_diagonal
  have hnege0 : IsD6Root (-e0) := by
    have h := isD6Root_d6Refl_single_zero (x := e0) isD6Root_single_zero
    have heq : d6Refl e0 *ᵥ e0 = -e0 := by
      rw [d6Refl_single_zero_mulVec]
      ext i
      by_cases hi : i = 0 <;> simp [e0, hi]
    rwa [heq] at h
  obtain ⟨A, hAX, hAe⟩ := exists_mem_realized_mulVec_eq hstd hB hrec hnege0
  obtain ⟨Bm, hBmX, hABm, hBmA⟩ := exists_inv_mem_realized (H := ⊤) hAX
  have hrowA : ∀ x : Coords 7, (A *ᵥ x) 0 = -x 0 := by
    intro x
    have h := d6Form_mulVec_of_mem_realized hstd hB hrec hAX x e0
    rw [hAe, d6Form_single_zero_right] at h
    have h' : d6Form (A *ᵥ x) (-e0) = (A *ᵥ x) 0 := by
      simp [d6Form, e0]
    rwa [h'] at h
  have hMcoord : ∀ (x : Coords 7) (i : Fin 7),
      ((d6Refl e0 * A) *ᵥ x) i = if i = 0 then x 0 else (A *ᵥ x) i := by
    intro x i
    rw [← Matrix.mulVec_mulVec, d6Refl_single_zero_mulVec]
    by_cases hi : i = 0
    · subst i
      simp [hrowA]
    · simp [hi]
  have hM0coord : ∀ x : Coords 7, ((d6Refl e0 * A) *ᵥ x) 0 = x 0 := by
    intro x
    rw [hMcoord]
    simp
  have hMroot : ∀ x : Coords 7, IsD6Root x → IsD6Root ((d6Refl e0 * A) *ᵥ x) := by
    intro x hx
    rw [← Matrix.mulVec_mulVec]
    exact isD6Root_d6Refl_single_zero
      (isD6Root_mulVec_of_mem_realized hstd hB hrec hAX hx)
  have hMe0 : (d6Refl e0 * A) *ᵥ Pi.single (0 : Fin 7) 1 =
      Pi.single (0 : Fin 7) 1 := by
    ext i
    rw [hMcoord]
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi, hAe, e0]
  have hM0 : ∀ i, (d6Refl e0 * A) i 0 = if i = 0 then 1 else 0 := by
    intro i
    have h := congrFun hMe0 i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at h
    exact h
  have hMrow : ∀ j : Fin 6, (d6Refl e0 * A) 0 j.succ = 0 := by
    intro j
    have h := hM0coord (Pi.single j.succ (1 : ZMod 3))
    rw [show (Pi.single j.succ (1 : ZMod 3) : Coords 7) 0 = 0 by
      simp [Pi.single_eq_of_ne (Fin.succ_ne_zero j).symm]] at h
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h
  have h2root : ∀ i j : Fin 6, i ≠ j →
      wt ((d6Refl e0 * A) *ᵥ (Pi.single i.succ (1 : ZMod 3) +
        Pi.single j.succ (1 : ZMod 3))) = 2 ∧
      wt ((d6Refl e0 * A) *ᵥ (Pi.single i.succ (1 : ZMod 3) -
        Pi.single j.succ (1 : ZMod 3))) = 2 := by
    intro i j hij
    constructor
    · refine wt_eq_two_of_isD6Root_of_zero
        (hMroot _ (isD6Root_single_add_single hij)) ?_
      rw [hM0coord]
      simp [Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm,
        Pi.single_eq_of_ne (Fin.succ_ne_zero j).symm]
    · refine wt_eq_two_of_isD6Root_of_zero
        (hMroot _ (isD6Root_single_sub_single hij)) ?_
      rw [hM0coord]
      simp [Pi.sub_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm,
        Pi.single_eq_of_ne (Fin.succ_ne_zero j).symm]
  have hMinv : ∃ N : Matrix (Fin 7) (Fin 7) (ZMod 3), N * (d6Refl e0 * A) = 1 := by
    refine ⟨Bm * d6Refl e0, ?_⟩
    rw [mul_assoc, ← mul_assoc (d6Refl e0) (d6Refl e0) A,
      d6Refl_single_zero_sq, one_mul, hBmA]
  obtain ⟨σ, s, hs, hσ0, hs0, hMeq⟩ :=
    exists_spMat_succ_of_wt_two (n := 6) (by norm_num) (d6Refl e0 * A) hMinv hM0 hMrow h2root
  let u : Coords 7 := fun _ => 1
  have hu : IsD6Root u := by
    right
    right
    constructor
    · rw [wt]
      have hf : (Finset.univ.filter fun i : Fin 7 => u i ≠ 0) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro i _
        simp [u]
      rw [hf, Finset.card_univ, Fintype.card_fin]
    · simp [u]
  have hMuroot : IsD6Root ((d6Refl e0 * A) *ᵥ u) := hMroot u hu
  have hMu : (d6Refl e0 * A) *ᵥ u = fun i => s (σ.symm i) := by
    rw [hMeq, spMat_mulVec]
    funext i
    simp [u]
  have hwtMu : wt ((d6Refl e0 * A) *ᵥ u) = 7 := by
    rw [hMu, wt]
    have hf : (Finset.univ.filter fun i : Fin 7 => s (σ.symm i) ≠ 0) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      rcases hs (σ.symm i) with h | h <;> rw [h] <;> decide
    rw [hf, Finset.card_univ, Fintype.card_fin]
  have hprodMu : ∏ i : Fin 6, ((d6Refl e0 * A) *ᵥ u) i.succ = 1 := by
    rcases hMuroot with ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨h7, hp⟩
    · omega
    · omega
    · exact hp
  rw [hMu] at hprodMu
  have hσsymm0 : σ.symm 0 = 0 := by
    have h := Equiv.symm_apply_apply σ 0
    rwa [hσ0] at h
  have hne : ∀ i : Fin 6, σ.symm i.succ ≠ 0 := by
    intro i hi
    have h1 : i.succ = σ 0 := by
      rw [← Equiv.apply_symm_apply σ i.succ, hi, hσ0]
    exact Fin.succ_ne_zero i (h1.trans hσ0)
  let f : Fin 6 → Fin 6 := fun i => (σ.symm i.succ).pred (hne i)
  have hf : ∀ i, (f i).succ = σ.symm i.succ := fun i => Fin.succ_pred _ _
  have hfinj : Function.Injective f := by
    intro i j hij
    have h1 : (f i).succ = (f j).succ := by rw [hij]
    rw [hf i, hf j] at h1
    exact Fin.succ_inj.mp (σ.symm.injective h1)
  let e : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  have he : ∀ i, (e i).succ = σ.symm i.succ := by
    intro i
    rw [show e i = f i from Equiv.ofBijective_apply f _ i, hf i]
  have h1 : ∏ i : Fin 6, s i.succ = ∏ i : Fin 6, s (e i).succ :=
    (Equiv.prod_comp e (fun j => s j.succ)).symm
  have h2 : ∏ i : Fin 6, s (e i).succ = ∏ i : Fin 6, s (σ.symm i.succ) :=
    Finset.prod_congr rfl fun i _ => by rw [he i]
  have hp : ∏ i : Fin 6, s i.succ = 1 := by
    rw [h1, h2, hprodMu]
  have hMeven : (d6Refl e0 * A) ∈ evenFix0 6 :=
    ⟨σ, s, hs, ⟨hσ0, hs0, hp⟩, hMeq⟩
  have hEqC : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 6 :=
    (realized_centralizer_eq_realized_D6 hstd hB hrec).1.trans
      (realized_centralizer_eq_realized_D6 hstd hB hrec).2
  have hMreal : (d6Refl e0 * A) ∈ B.realized ⊤ := by
    have hC : (d6Refl e0 * A) ∈
        B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
      rw [hEqC]
      exact hMeven
    exact realized_mono B le_top hC
  have ht0eq : d6Refl e0 = (d6Refl e0 * A) * Bm := by
    rw [mul_assoc, hABm, mul_one]
  have ht0X : d6Refl e0 ∈ B.realized ⊤ := by
    rw [ht0eq]
    exact mul_mem_realized hMreal hBmX
  rw [← ht0]
  exact ht0X

theorem d6Refl_mem_realized {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) {v : Coords 7} (hv : IsD6Root v) :
    d6Refl v ∈ B.realized ⊤ := by
  classical
  let e0 : Coords 7 := Pi.single (0 : Fin 7) 1
  obtain ⟨A, hAX, hAe⟩ := exists_mem_realized_mulVec_eq hstd hB hrec hv
  obtain ⟨Bm, hBmX, hABm, hBmA⟩ := exists_inv_mem_realized (H := ⊤) hAX
  have ht0X : d6Refl e0 ∈ B.realized ⊤ := by
    have h := diagNeg_mem_realized hstd hB hrec
    rwa [← d6Refl_single_zero_eq_diagonal] at h
  have hform : ∀ x : Coords 7, d6Form (Bm *ᵥ x) e0 = d6Form x v := by
    intro x
    have h := d6Form_mulVec_of_mem_realized hstd hB hrec hAX (Bm *ᵥ x) e0
    rw [Matrix.mulVec_mulVec, hABm, Matrix.one_mulVec, hAe] at h
    exact h.symm
  have hcoe : d6Refl v = A * d6Refl e0 * Bm := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    symm
    calc (A * d6Refl e0 * Bm) *ᵥ Pi.single i 1
        = A *ᵥ (d6Refl e0 *ᵥ (Bm *ᵥ Pi.single i 1)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = A *ᵥ ((Bm *ᵥ Pi.single i 1) -
            d6Form (Bm *ᵥ Pi.single i 1) e0 • e0) := by
          rw [d6Refl_mulVec]
      _ = A *ᵥ (Bm *ᵥ Pi.single i 1) -
            d6Form (Bm *ᵥ Pi.single i 1) e0 • (A *ᵥ e0) := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
      _ = Pi.single i 1 - d6Form (Pi.single i 1) v • v := by
          rw [Matrix.mulVec_mulVec, hABm, Matrix.one_mulVec, hAe, hform (Pi.single i 1)]
      _ = d6Refl v *ᵥ Pi.single i 1 := by
          rw [d6Refl_mulVec]
  rw [hcoe]
  exact mul_mem_realized (mul_mem_realized hAX ht0X) hBmX

end CFSG.StandardType.FrameRoute.FS81
