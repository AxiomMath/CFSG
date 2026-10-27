module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1
public import CFSG.Quasithin.Vol2.Asc94.TSModel2

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def rIdx (i : Fin 2) : Fin 5 := ⟨i.val, by have := i.isLt; omega⟩

@[expose] def cIdx (j : Fin 2) : Fin 5 := ⟨3 + j.val, by have := j.isLt; omega⟩

theorem rIdx_ne_two : ∀ i : Fin 2, rIdx i ≠ 2 := by decide

theorem cIdx_ne_two : ∀ j : Fin 2, (2 : Fin 5) ≠ cIdx j := by decide

theorem rIdx_ne_cIdx : ∀ i j : Fin 2, rIdx i ≠ cIdx j := by decide

theorem cIdx_sub (b : Fin 5) (hb : 3 ≤ b.val) (h : b.val - 3 < 2) :
    cIdx ⟨b.val - 3, h⟩ = b :=
  Fin.ext (by show 3 + (b.val - 3) = b.val; omega)

@[expose] def uC (x : Hc) : Fin 2 → ZMod 2 := fun i => cm x (rIdx i) 2

@[expose] def wC (x : Hc) : Fin 2 → ZMod 2 := fun j => cm x 2 (cIdx j)

@[expose] def zC (x : Hc) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => cm x (rIdx i) (cIdx j)

theorem cm_eq_sub_one_of_ne (x : Hc) {a b : Fin 5} (h : a ≠ b) :
    cm x a b = (cm x - 1) a b := by
  rw [Matrix.sub_apply, Matrix.one_apply_ne h]
  exact (sub_zero _).symm

theorem uC_apply (x : Hc) (i : Fin 2) : uC x i = (cm x - 1) (rIdx i) 2 :=
  cm_eq_sub_one_of_ne x (rIdx_ne_two i)

theorem wC_apply (x : Hc) (j : Fin 2) : wC x j = (cm x - 1) 2 (cIdx j) :=
  cm_eq_sub_one_of_ne x (cIdx_ne_two j)

theorem zC_apply (x : Hc) (i j : Fin 2) : zC x i j = (cm x - 1) (rIdx i) (cIdx j) :=
  cm_eq_sub_one_of_ne x (rIdx_ne_cIdx i j)

theorem cm_mul_sub_one {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    {x y : Hc} (hx : x ∈ patSub S hS) (hy : y ∈ patSub S hS) :
    cm (x * y) - 1 = (cm x - 1) + (cm y - 1) := by
  have hz := suppIn_mul_eq_zero hS ((mem_patSub hS).1 hx) ((mem_patSub hS).1 hy)
  have e : cm (x * y) - 1 = (cm x - 1) + (cm y - 1) + (cm x - 1) * (cm y - 1) := by
    rw [cm_mul]
    noncomm_ring
  rw [e, hz, add_zero]

theorem uC_mul {x y : Hc} (hx : x ∈ A1) (hy : y ∈ A1) : uC (x * y) = uC x + uC y := by
  funext i
  rw [Pi.add_apply, uC_apply, uC_apply, uC_apply, cm_mul_sub_one hSA hx hy, Matrix.add_apply]

theorem wC_mul {x y : Hc} (hx : x ∈ A2) (hy : y ∈ A2) : wC (x * y) = wC x + wC y := by
  funext j
  rw [Pi.add_apply, wC_apply, wC_apply, wC_apply, cm_mul_sub_one hSA2 hx hy, Matrix.add_apply]

theorem zC_mul {x y : Hc} (hx : x ∈ A1 ⊓ A2) (hy : y ∈ A1 ⊓ A2) :
    zC (x * y) = zC x + zC y := by
  ext i j
  rw [Matrix.add_apply, zC_apply, zC_apply, zC_apply,
    cm_mul_sub_one hSA (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hy).1, Matrix.add_apply]

theorem inv_eq_self_of_mem {S : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    {x : Hc} (hx : x ∈ patSub S hS) : x⁻¹ = x := by
  have hxx : cm x * cm x = 1 := sq_one_of_supp hS ((mem_patSub hS).1 hx)
  exact inv_eq_of_mul_eq_one_right (Hc_ext (by rw [cm_mul, cm_one]; exact hxx))

theorem suppIn_SA2_of_col {N : Mt} (hN : SuppIn SA N) (h : ∀ i : Fin 2, N (rIdx i) 2 = 0) :
    SuppIn SA2 N := by
  intro i j hij
  by_cases hA : i.val ≤ 1 ∧ 2 ≤ j.val
  · obtain ⟨hA1, hA2⟩ := hA
    have hj : j = 2 := by
      apply Fin.ext
      show j.val = 2
      by_contra hne
      exact hij ⟨by omega, by omega⟩
    rw [hj]
    have := i.isLt
    exact h ⟨i.val, by omega⟩
  · exact hN i j hA

theorem suppIn_SA_of_row {N : Mt} (hN : SuppIn SA2 N) (h : ∀ j : Fin 2, N 2 (cIdx j) = 0) :
    SuppIn SA N := by
  intro i j hij
  by_cases hB : i.val ≤ 2 ∧ 3 ≤ j.val
  · obtain ⟨hB1, hB2⟩ := hB
    have hi : i = 2 := by
      apply Fin.ext
      show i.val = 2
      by_contra hne
      exact hij ⟨by omega, by omega⟩
    subst hi
    have := j.isLt
    have hk := h ⟨j.val - 3, by omega⟩
    rwa [cIdx_sub j hB2 (by omega)] at hk
  · exact hN i j hB

theorem uC_eq_zero_iff {x : Hc} (hx : x ∈ A1) : uC x = 0 ↔ x ∈ A2 := by
  have hN : SuppIn SA (cm x - 1) := (mem_patSub hSA).1 hx
  rw [mem_A2]
  constructor
  · intro h
    apply suppIn_SA2_of_col hN
    intro i
    have h' := congrFun h i
    rw [uC_apply, Pi.zero_apply] at h'
    exact h'
  · intro h
    funext i
    rw [uC_apply, Pi.zero_apply]
    exact h (rIdx i) 2 (fun hh => absurd hh.2 (by decide))

theorem wC_eq_zero_iff {x : Hc} (hx : x ∈ A2) : wC x = 0 ↔ x ∈ A1 := by
  have hN : SuppIn SA2 (cm x - 1) := (mem_patSub hSA2).1 hx
  rw [show x ∈ A1 ↔ SuppIn SA (cm x - 1) from mem_patSub hSA]
  constructor
  · intro h
    apply suppIn_SA_of_row hN
    intro j
    have h' := congrFun h j
    rw [wC_apply, Pi.zero_apply] at h'
    exact h'
  · intro h
    funext j
    rw [wC_apply, Pi.zero_apply]
    exact h 2 (cIdx j) (fun hh => absurd hh.1 (by decide))

theorem mul_zero_of_row {S : Fin 5 → Fin 5 → Prop} {A B : Mt} (hA : SuppIn S A) (i j : Fin 5)
    (hi : ∀ k, ¬ S i k) : (A * B) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hA i k (hi k), zero_mul]

theorem mul_zero_of_col {S : Fin 5 → Fin 5 → Prop} {A B : Mt} (hB : SuppIn S B) (i j : Fin 5)
    (hj : ∀ k, ¬ S k j) : (A * B) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hB k j (hj k), mul_zero]

theorem suppIn_mul_zero' {S T : Fin 5 → Fin 5 → Prop} (h : ∀ i k j, S i k → T k j → False)
    {A B : Mt} (hA : SuppIn S A) (hB : SuppIn T B) : A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hs : S i k
  · rw [hB k j (fun ht => h i k j hs ht), mul_zero]
  · rw [hA i k hs, zero_mul]

theorem suppIn_of_sub {S T : Fin 5 → Fin 5 → Prop} (hST : ∀ i j, S i j → T i j) {N : Mt}
    (hN : SuppIn S N) : SuppIn T N :=
  fun i j hT => hN i j (fun hS => hT (hST i j hS))

abbrev SAB (i j : Fin 5) : Prop := i.val ≤ 1 ∧ 3 ≤ j.val

theorem SAB_sub_SA (i j : Fin 5) (h : SAB i j) : SA i j := ⟨h.1, by have := h.2; omega⟩

theorem SAB_sub_SA2 (i j : Fin 5) (h : SAB i j) : SA2 i j := ⟨by have := h.1; omega, h.2⟩

@[expose] def uE (v : Fin 2 → ZMod 2) : Mt :=
  Matrix.of fun i j => if h : j = 2 ∧ i.val < 2 then v ⟨i.val, h.2⟩ else 0

@[expose] def wE (w : Fin 2 → ZMod 2) : Mt :=
  Matrix.of fun i j => if h : i = 2 ∧ 3 ≤ j.val then
    w ⟨j.val - 3, by have := j.isLt; omega⟩ else 0

@[expose] def zE (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Mt :=
  Matrix.of fun i j => if h : i.val ≤ 1 ∧ 3 ≤ j.val then
    m ⟨i.val, by have := h.1; omega⟩ ⟨j.val - 3, by have := j.isLt; omega⟩ else 0

theorem uE_apply (v : Fin 2 → ZMod 2) (i : Fin 2) : uE v (rIdx i) 2 = v i := by
  have h : (2 : Fin 5) = 2 ∧ (rIdx i).val < 2 := ⟨rfl, i.isLt⟩
  show (if h' : (2 : Fin 5) = 2 ∧ (rIdx i).val < 2 then v ⟨(rIdx i).val, h'.2⟩ else 0) = v i
  exact dif_pos h

theorem wE_apply (w : Fin 2 → ZMod 2) (j : Fin 2) : wE w 2 (cIdx j) = w j := by
  have h : (2 : Fin 5) = 2 ∧ 3 ≤ (cIdx j).val := ⟨rfl, by show 3 ≤ 3 + j.val; omega⟩
  show (if h' : (2 : Fin 5) = 2 ∧ 3 ≤ (cIdx j).val then
    w ⟨(cIdx j).val - 3, by have := (cIdx j).isLt; omega⟩ else 0) = w j
  exact (dif_pos h).trans (congrArg w (Fin.ext (by show 3 + j.val - 3 = j.val; omega)))

theorem zE_apply (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) (i j : Fin 2) :
    zE m (rIdx i) (cIdx j) = m i j := by
  have h : (rIdx i).val ≤ 1 ∧ 3 ≤ (cIdx j).val :=
    ⟨by have := i.isLt; show i.val ≤ 1; omega, by show 3 ≤ 3 + j.val; omega⟩
  show (if h' : (rIdx i).val ≤ 1 ∧ 3 ≤ (cIdx j).val then
    m ⟨(rIdx i).val, by have := h'.1; omega⟩ ⟨(cIdx j).val - 3, by have := (cIdx j).isLt; omega⟩
    else 0) = m i j
  exact (dif_pos h).trans (congrArg₂ (fun a b : Fin 2 => m a b) (Fin.ext rfl)
    (Fin.ext (by show 3 + j.val - 3 = j.val; omega)))

theorem uE_zero (v : Fin 2 → ZMod 2) : SuppIn SA (uE v) := by
  intro i j hij
  have hne : ¬ (j = 2 ∧ i.val < 2) := fun h =>
    hij ⟨by have := h.2; omega, by rw [h.1]; decide⟩
  show (if h : j = 2 ∧ i.val < 2 then v ⟨i.val, h.2⟩ else 0) = 0
  exact dif_neg hne

theorem wE_supp (w : Fin 2 → ZMod 2) : SuppIn SA2 (wE w) := by
  intro i j hij
  have hne : ¬ (i = 2 ∧ 3 ≤ j.val) := fun h => hij ⟨by rw [h.1]; decide, h.2⟩
  show (if h : i = 2 ∧ 3 ≤ j.val then w ⟨j.val - 3, by have := j.isLt; omega⟩ else 0) = 0
  exact dif_neg hne

theorem zE_supp (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) : SuppIn SAB (zE m) := by
  intro i j hij
  show (if h : i.val ≤ 1 ∧ 3 ≤ j.val then
    m ⟨i.val, by have := h.1; omega⟩ ⟨j.val - 3, by have := j.isLt; omega⟩ else 0) = 0
  exact dif_neg hij

theorem fin5_A2_up : ∀ i j : Fin 5, j ≤ i → ¬ (i.val ≤ 2 ∧ 3 ≤ j.val) := by decide

theorem fin5_A2_zero : ∀ i : Fin 5, ¬ (i.val ≤ 2 ∧ 3 ≤ (0 : Fin 5).val) := by decide

theorem fin5_A2_four : ∀ j : Fin 5, ¬ ((4 : Fin 5).val ≤ 2 ∧ 3 ≤ j.val) := by decide

@[expose] def unipOfSA2 (N : Mt) (hN : SuppIn SA2 N) : Hc :=
  unipH N (fun i j hji => hN i j (fin5_A2_up i j hji))
    (fun i => hN i 0 (fin5_A2_zero i))
    (fun j => hN 4 j (fin5_A2_four j))

theorem cm_unipOfSA (N : Mt) (hN : SuppIn SA N) : cm (unipOfSA N hN) = 1 + N := rfl

theorem cm_unipOfSA2 (N : Mt) (hN : SuppIn SA2 N) : cm (unipOfSA2 N hN) = 1 + N := rfl

theorem sub_one_cm_unipOfSA (N : Mt) (hN : SuppIn SA N) : cm (unipOfSA N hN) - 1 = N := by
  rw [cm_unipOfSA]
  abel

theorem sub_one_cm_unipOfSA2 (N : Mt) (hN : SuppIn SA2 N) :
    cm (unipOfSA2 N hN) - 1 = N := by
  rw [cm_unipOfSA2]
  abel

theorem unipOfSA_mem_A1 (N : Mt) (hN : SuppIn SA N) : unipOfSA N hN ∈ A1 :=
  (mem_patSub hSA).2 (by rw [sub_one_cm_unipOfSA]; exact hN)

theorem unipOfSA_mem_A2_of (N : Mt) (hN : SuppIn SA N) (h2 : SuppIn SA2 N) :
    unipOfSA N hN ∈ A2 :=
  (mem_patSub hSA2).2 (by rw [sub_one_cm_unipOfSA]; exact h2)

theorem unipOfSA2_mem_A2 (N : Mt) (hN : SuppIn SA2 N) : unipOfSA2 N hN ∈ A2 :=
  (mem_patSub hSA2).2 (by rw [sub_one_cm_unipOfSA2]; exact hN)

theorem exists_uC (v : Fin 2 → ZMod 2) : ∃ x ∈ A1, uC x = v := by
  refine ⟨unipOfSA (uE v) (uE_zero v), unipOfSA_mem_A1 _ _, ?_⟩
  funext i
  rw [uC_apply, sub_one_cm_unipOfSA, uE_apply]

theorem exists_wC (v : Fin 2 → ZMod 2) : ∃ x ∈ A2, wC x = v := by
  refine ⟨unipOfSA2 (wE v) (wE_supp v), unipOfSA2_mem_A2 _ _, ?_⟩
  funext j
  rw [wC_apply, sub_one_cm_unipOfSA2, wE_apply]

theorem exists_zC (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) : ∃ x ∈ A1 ⊓ A2, zC x = m := by
  refine ⟨unipOfSA (zE m) (suppIn_of_sub SAB_sub_SA (zE_supp m)),
    Subgroup.mem_inf.2 ⟨unipOfSA_mem_A1 _ _,
      unipOfSA_mem_A2_of _ _ (suppIn_of_sub SAB_sub_SA2 (zE_supp m))⟩, ?_⟩
  ext i j
  rw [zC_apply, sub_one_cm_unipOfSA, zE_apply]

theorem cm_eq_one_add_zE {x : Hc} (hx : x ∈ A1 ⊓ A2) : cm x = 1 + zE (zC x) := by
  have hN1 : SuppIn SA (cm x - 1) := (mem_patSub hSA).1 (Subgroup.mem_inf.1 hx).1
  have hN2 : SuppIn SA2 (cm x - 1) := (mem_patSub hSA2).1 (Subgroup.mem_inf.1 hx).2
  ext a b
  rw [Matrix.add_apply]
  by_cases hab : a.val ≤ 1 ∧ 3 ≤ b.val
  · obtain ⟨ha1, hb3⟩ := hab
    have hne : a ≠ b := fun h => by have := congrArg Fin.val h; omega
    have hra : rIdx ⟨a.val, by omega⟩ = a := Fin.ext rfl
    have hcb : cIdx ⟨b.val - 3, by have := b.isLt; omega⟩ = b := cIdx_sub b hb3 _
    have hz : zE (zC x) a b = (cm x - 1) (rIdx ⟨a.val, by omega⟩)
        (cIdx ⟨b.val - 3, by have := b.isLt; omega⟩) := by
      show (if h' : a.val ≤ 1 ∧ 3 ≤ b.val then
        zC x ⟨a.val, by have := h'.1; omega⟩ ⟨b.val - 3, by have := b.isLt; omega⟩
        else 0) = _
      rw [dif_pos ⟨ha1, hb3⟩, zC_apply]
    rw [Matrix.one_apply_ne hne, zero_add, hz, hra, hcb, cm_eq_sub_one_of_ne x hne]
  · have hz : zE (zC x) a b = 0 := by
      show (if h' : a.val ≤ 1 ∧ 3 ≤ b.val then
        zC x ⟨a.val, by have := h'.1; omega⟩ ⟨b.val - 3, by have := b.isLt; omega⟩
        else 0) = 0
      exact dif_neg hab
    have h0 : cm x a b = (1 : Mt) a b := by
      by_cases hA : a.val ≤ 1 ∧ 2 ≤ b.val
      · have hB : ¬ (a.val ≤ 2 ∧ 3 ≤ b.val) := fun hB => hab ⟨hA.1, hB.2⟩
        have h := hN2 a b hB
        rw [Matrix.sub_apply] at h
        exact sub_eq_zero.1 h
      · have h := hN1 a b hA
        rw [Matrix.sub_apply] at h
        exact sub_eq_zero.1 h
    rw [hz, add_zero, h0]

theorem zC_injOn {x y : Hc} (hx : x ∈ A1 ⊓ A2) (hy : y ∈ A1 ⊓ A2) (h : zC x = zC y) :
    x = y :=
  Hc_ext (by rw [cm_eq_one_add_zE hx, cm_eq_one_add_zE hy, h])

theorem unip12_mem_A1 : unipS 1 2 (by decide) 1 ∈ A1 :=
  unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩

theorem unip23_mem_A2 : unipS 2 3 (by decide) 1 ∈ A2 :=
  unipS_mem_patSub hSA2 _ 1 ⟨by decide, by decide⟩

theorem centralizer_A1 : Subgroup.centralizer (A1 : Set Hc) = A1 := by
  apply le_antisymm
  · intro x hx
    have hxB : x ∈ ((Subgroup.centralizer ((A1 ⊓ U1 : Subgroup Hc) : Set Hc) :
        Subgroup Hc) : Set Hc) :=
      Subgroup.mem_centralizer_iff.2 fun b hb =>
        Subgroup.mem_centralizer_iff.1 hx b (Subgroup.mem_inf.1 hb).1
    rw [centralizer_B_eq] at hxB
    obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_mul.1 hxB
    have hcu : ∀ c ∈ A1, u * c = c * u := by
      intro c hc
      have e1 : c * (a * u) = a * u * c := Subgroup.mem_centralizer_iff.1 hx c hc
      have e2 : a * c = c * a := patSub_comm hSA ha hc
      have h3 : a * (u * c) = a * (c * u) := by
        calc a * (u * c) = a * u * c := (mul_assoc _ _ _).symm
          _ = c * (a * u) := e1.symm
          _ = c * a * u := (mul_assoc _ _ _).symm
          _ = a * c * u := by rw [e2]
          _ = a * (c * u) := mul_assoc _ _ _
      exact mul_left_cancel h3
    have hmat := congrArg cm (hcu _ unip12_mem_A1)
    rw [cm_mul, cm_mul, cm_unipS] at hmat
    have h01 := congrFun (congrFun hmat 0) 2
    rw [mul_add_single_apply, add_single_mul_apply] at h01
    have hu01 : cm u 0 1 = 0 := by simpa using h01
    have huA : u ∈ A1 := by
      refine (mem_patSub hSA).2 ?_
      have hU : SuppIn S1 (cm u - 1) := (mem_patSub hS1).1 hu
      intro i j hij
      by_cases hi : i = 0
      · subst hi
        have hfin : ∀ j : Fin 5, ¬ ((0 : Fin 5).val ≤ 1 ∧ 2 ≤ j.val) → j = 0 ∨ j = 1 := by
          decide
        rcases hfin j hij with rfl | rfl
        · simp [cm_00]
        · simp [hu01]
      · exact hU i j (fun h => hi h.1)
    exact A1.mul_mem ha huA
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact patSub_comm hSA hb ha

theorem centralizer_A2 : Subgroup.centralizer (A2 : Set Hc) = A2 := by
  apply le_antisymm
  · intro x hx
    have hy : sigma x ∈ Subgroup.centralizer (A1 : Set Hc) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have h := congrArg sigma (Subgroup.mem_centralizer_iff.1 hx (sigma c) (sigma_A1 hc))
      rw [map_mul, map_mul, sigma_sigma] at h
      exact h
    rw [centralizer_A1] at hy
    have h2 := sigma_A1 hy
    rwa [sigma_sigma] at h2
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact patSub_comm hSA2 hb ha

theorem centralizer_Jm : Subgroup.centralizer (Jm : Set Hc) = A1 ⊓ A2 := by
  apply le_antisymm
  · intro x hx
    have hA1 : x ∈ Subgroup.centralizer (A1 : Set Hc) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_iff.1 hx h (Subgroup.mem_sup_left (show h ∈ A1 from hh))
    have hA2 : x ∈ Subgroup.centralizer (A2 : Set Hc) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_iff.1 hx h (Subgroup.mem_sup_right (show h ∈ A2 from hh))
    rw [centralizer_A1] at hA1
    rw [centralizer_A2] at hA2
    exact Subgroup.mem_inf.2 ⟨hA1, hA2⟩
  · intro x hx
    have hx1 : x ∈ A1 := (Subgroup.mem_inf.1 hx).1
    have hx2 : x ∈ A2 := (Subgroup.mem_inf.1 hx).2
    have hle : A1 ⊔ A2 ≤ Subgroup.centralizer ({x} : Set Hc) := by
      apply sup_le
      · intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact patSub_comm hSA hk hx1
      · intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact patSub_comm hSA2 hk hx2
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem comm_matrix {N M : Mt} (hN : SuppIn SA N) (hM : SuppIn SA2 M) :
    (1 + N) * (1 + M) * (1 + N) * (1 + M) = 1 + N * M := by
  have hNN : N * N = 0 := suppIn_mul_eq_zero hSA hN hN
  have hMM : M * M = 0 := suppIn_mul_eq_zero hSA2 hM hM
  have hMN : M * N = 0 := suppIn_mul_zero' (S := SA2) (T := SA)
    (fun i k j h1 h2 => by have := h1.2; have := h2.1; omega) hM hN
  have hN1 : N * (N * M) = 0 := by rw [← mul_assoc, hNN, zero_mul]
  have hM1 : M * (N * M) = 0 := by rw [← mul_assoc, hMN, zero_mul]
  have hN2 : (N * M) * N = 0 := by rw [mul_assoc, hMN, mul_zero]
  have hN3 : (N * M) * M = 0 := by rw [mul_assoc, hMM, mul_zero]
  have hN4 : (N * M) * (N * M) = 0 := by rw [mul_assoc, hM1, mul_zero]
  have e : (1 + N) * (1 + M) = 1 + (N + M + N * M) := by noncomm_ring
  have hXX : (N + M + N * M) * (N + M + N * M) = N * M := by
    have e2 : (N + M + N * M) * (N + M + N * M) = N * N + N * M + N * (N * M) + M * N + M * M
        + M * (N * M) + (N * M) * N + (N * M) * M + (N * M) * (N * M) := by
      noncomm_ring
    rw [e2, hNN, hMN, hMM, hN1, hM1, hN2, hN3, hN4]
    simp
  have hc : (1 + (N + M + N * M)) * (1 + (N + M + N * M))
      = 1 + ((N + M + N * M) + (N + M + N * M)) + (N + M + N * M) * (N + M + N * M) := by
    noncomm_ring
  rw [show (1 + N) * (1 + M) * (1 + N) * (1 + M)
      = ((1 + N) * (1 + M)) * ((1 + N) * (1 + M)) by simp only [mul_assoc], e, hc,
    mat_add_self, add_zero, hXX]

theorem decomp_matrix {R E : Mt} (hEE : E * E = 0) :
    (1 + (R + R * E)) * (1 + E) = 1 + (R + E) := by
  have h2 : R * E + R * E = 0 := mat_add_self _
  calc (1 + (R + R * E)) * (1 + E) = 1 + (R + E) + (R * E + R * E) + R * (E * E) := by
        noncomm_ring
    _ = 1 + (R + E) := by
        rw [h2, hEE, mul_zero]
        simp

theorem mul_supp_SAB {N M : Mt} (hN : SuppIn SA N) (hM : SuppIn SA2 M) :
    SuppIn SAB (N * M) := by
  intro i j hij
  by_cases hi : i.val ≤ 1
  · have hj : ¬ 3 ≤ j.val := fun hj => hij ⟨hi, hj⟩
    exact mul_zero_of_col hM i j (fun k hk => hj hk.2)
  · exact mul_zero_of_row hN i j (fun k hk => hi hk.1)

theorem comm_coord {u w : Hc} (hu : u ∈ A1) (hw : w ∈ A2) :
    u * w * u⁻¹ * w⁻¹ ∈ A1 ⊓ A2 ∧ zC (u * w * u⁻¹ * w⁻¹) = Matrix.vecMulVec (uC u) (wC w) := by
  have hN : SuppIn SA (cm u - 1) := (mem_patSub hSA).1 hu
  have hM : SuppIn SA2 (cm w - 1) := (mem_patSub hSA2).1 hw
  have hu' : u⁻¹ = u := inv_eq_self_of_mem hSA hu
  have hw' : w⁻¹ = w := inv_eq_self_of_mem hSA2 hw
  have e1 : (1 : Mt) + (cm u - 1) = cm u := by abel
  have e2 : (1 : Mt) + (cm w - 1) = cm w := by abel
  have e3 : ∀ X : Mt, (1 : Mt) + X - 1 = X := fun X => by abel
  have hc : cm (u * w * u⁻¹ * w⁻¹) = 1 + (cm u - 1) * (cm w - 1) := by
    rw [hu', hw', cm_mul, cm_mul, cm_mul]
    have h := comm_matrix hN hM
    rw [e1, e2] at h
    exact h
  have hP := mul_supp_SAB hN hM
  have hmem : u * w * u⁻¹ * w⁻¹ ∈ A1 ⊓ A2 := by
    refine Subgroup.mem_inf.2 ⟨(mem_patSub hSA).2 ?_, (mem_patSub hSA2).2 ?_⟩
    · rw [hc, e3]
      exact suppIn_of_sub SAB_sub_SA hP
    · rw [hc, e3]
      exact suppIn_of_sub SAB_sub_SA2 hP
  refine ⟨hmem, ?_⟩
  ext i j
  rw [zC_apply, hc, e3, Matrix.mul_apply, Finset.sum_eq_single (2 : Fin 5)]
  · rw [Matrix.vecMulVec_apply, uC_apply, wC_apply]
  · intro k _ hk
    by_cases hk1 : k.val ≤ 1
    · rw [hN (rIdx i) k (fun h => by have := h.2; omega), zero_mul]
    · have hk2 : k.val ≠ 2 := fun h => hk (Fin.ext h)
      rw [hM k (cIdx j) (fun h => by have := h.1; omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_Jm_of_coords {t : Hc} (ht : t ∈ Tm)
    (h1 : ∀ u ∈ A1, uC (t * u * t⁻¹) = uC u) (h2 : ∀ w ∈ A2, wC (t * w * t⁻¹) = wC w) :
    t ∈ Jm := by
  have hz1 : ∀ a b : ZMod 2, a = a + b → b = 0 := by decide
  have hz2 : ∀ a b : ZMod 2, a + b = a → b = 0 := by decide
  have hdiag : ∀ s : Hc, s ∈ Tm → ∀ i : Fin 5, cm s i i = 1 := by
    intro s hs i
    have h := (mem_Tm.1 hs) i i (lt_irrefl i)
    rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h
    exact h
  have h01 : cm t 0 1 = 0 := by
    obtain ⟨c, hc⟩ : ∃ c : Hc, c = t * unipS 1 2 (by decide) 1 * t⁻¹ := ⟨_, rfl⟩
    have hcA : c ∈ A1 := by rw [hc]; exact A1_conj_Tm ht unip12_mem_A1
    have hcu : uC c = uC (unipS 1 2 (by decide) 1) := by
      rw [hc]; exact h1 _ unip12_mem_A1
    have hcomm : c * t = t * unipS 1 2 (by decide) 1 := by
      rw [hc, inv_mul_cancel_right]
    have hmat := congrArg cm hcomm
    rw [cm_mul, cm_mul, cm_unipS] at hmat
    have key := congrFun (congrFun hmat 0) 2
    rw [mul_add_single_apply] at key
    simp only [Matrix.mul_apply, Fin.sum_univ_five] at key
    have e00 : cm c 0 0 = 1 := cm_00 c
    have e01 : cm c 0 1 = 0 := by
      have h := (mem_patSub hSA).1 hcA 0 1 (by decide)
      rw [Matrix.sub_apply, Matrix.one_apply_ne (show (0 : Fin 5) ≠ 1 by decide)] at h
      exact sub_eq_zero.1 h
    have e02 : cm c 0 2 = 0 := by
      have h : cm c 0 2 = cm (unipS 1 2 (by decide) 1) 0 2 := congrFun hcu 0
      rw [h, cm_unipS]
      simp [Matrix.single_apply]
    have e32 : cm t 3 2 = 0 := Tm_entry_zero ht (by decide)
    have e42 : cm t 4 2 = 0 := Tm_entry_zero ht (by decide)
    simp [e00, e01, e02, e32, e42] at key
    first
      | exact key
      | exact hz1 _ _ key
      | exact hz2 _ _ key
      | simpa using key
  have h34 : cm t 3 4 = 0 := by
    obtain ⟨c, hc⟩ : ∃ c : Hc, c = t * unipS 2 3 (by decide) 1 * t⁻¹ := ⟨_, rfl⟩
    have hcA : c ∈ A2 := by rw [hc]; exact A2_conj_Tm ht unip23_mem_A2
    have hcw : wC c = wC (unipS 2 3 (by decide) 1) := by
      rw [hc]; exact h2 _ unip23_mem_A2
    have hcomm : c * t = t * unipS 2 3 (by decide) 1 := by
      rw [hc, inv_mul_cancel_right]
    have hmat := congrArg cm hcomm
    rw [cm_mul, cm_mul, cm_unipS] at hmat
    have key := congrFun (congrFun hmat 2) 4
    rw [mul_add_single_apply] at key
    simp only [Matrix.mul_apply, Fin.sum_univ_five] at key
    have hcT : c ∈ Tm := A2_le_Tm hcA
    have e23 : cm c 2 3 = 1 := by
      have h : cm c 2 3 = cm (unipS 2 3 (by decide) 1) 2 3 := congrFun hcw 0
      rw [h, cm_unipS]
      simp [Matrix.single_apply]
    have e24 : cm c 2 4 = 0 := by
      have h : cm c 2 4 = cm (unipS 2 3 (by decide) 1) 2 4 := congrFun hcw 1
      rw [h, cm_unipS]
      simp [Matrix.single_apply]
    have e20 : cm c 2 0 = 0 := Tm_entry_zero hcT (by decide)
    have e21 : cm c 2 1 = 0 := Tm_entry_zero hcT (by decide)
    have e22 : cm c 2 2 = 1 := hdiag c hcT 2
    have e44 : cm t 4 4 = 1 := cm_44 t
    simp [e20, e21, e22, e23, e24, e44] at key
    first
      | exact key
      | exact hz2 _ _ key
      | exact hz1 _ _ key
      | simpa using key
  obtain ⟨N, hN⟩ : ∃ N : Mt, N = cm t - 1 := ⟨_, rfl⟩
  have hcN : cm t = 1 + N := by
    rw [hN]
    abel
  have F1 : ∀ i j : Fin 5, j ≤ i → N i j = 0 := by
    intro i j hji
    rw [hN]
    exact (mem_Tm.1 ht) i j (not_lt.2 hji)
  have F2 : N 0 1 = 0 := by
    simp [hN, h01]
  have F3 : N 3 4 = 0 := by
    simp [hN, h34]
  have hfin : ∀ i j : Fin 5, ¬ (i.val ≤ 1 ∧ 2 ≤ j.val) → ¬ (i = 2 ∧ 3 ≤ j.val) → i < j →
      (i = 0 ∧ j = 1) ∨ (i = 3 ∧ j = 4) := by
    decide
  have hzero : ∀ i j : Fin 5, ¬ (i.val ≤ 1 ∧ 2 ≤ j.val) → ¬ (i = 2 ∧ 3 ≤ j.val) →
      N i j = 0 := by
    intro i j h1 h2
    by_cases hij : j ≤ i
    · exact F1 i j hij
    · rcases hfin i j h1 h2 (not_le.1 hij) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact F2
      · exact F3
  obtain ⟨E, hE⟩ : ∃ E : Mt, E = Matrix.of fun i j => if i = 2 ∧ 3 ≤ j.val then N i j else 0 :=
    ⟨_, rfl⟩
  have hEapp : ∀ i j : Fin 5, E i j = if i = 2 ∧ 3 ≤ j.val then N i j else 0 := by
    intro i j
    simp only [hE, Matrix.of_apply]
  have hEsupp : SuppIn SA2 E := by
    intro i j hij
    have hne : ¬ (i = 2 ∧ 3 ≤ j.val) := fun h => hij ⟨by rw [h.1]; decide, h.2⟩
    rw [hEapp, if_neg hne]
  obtain ⟨R, hR⟩ : ∃ R : Mt, R = N - E := ⟨_, rfl⟩
  have hRsupp : SuppIn SA R := by
    intro i j hij
    rw [hR, Matrix.sub_apply]
    by_cases h : i = 2 ∧ 3 ≤ j.val
    · rw [hEapp, if_pos h, sub_self]
    · rw [hEapp, if_neg h]
      exact (sub_zero _).trans (hzero i j hij h)
  have hEE : E * E = 0 := suppIn_mul_eq_zero hSA2 hEsupp hEsupp
  have hRE : SuppIn SA (R + R * E) := by
    intro i j hij
    have hRij : R i j = 0 := hRsupp i j hij
    have hRE0 : (R * E) i j = 0 := by
      by_cases hi : i.val ≤ 1
      · have hj : j.val < 2 := by
          by_contra hj
          exact hij ⟨hi, by omega⟩
        exact mul_zero_of_col hEsupp i j (fun k hk => by have := hk.2; omega)
      · exact mul_zero_of_row hRsupp i j (fun k hk => hi hk.1)
    rw [Matrix.add_apply, hRij, hRE0, add_zero]
  have hA := unipOfSA_mem_A1 (R + R * E) hRE
  have hB := unipOfSA2_mem_A2 E hEsupp
  have hprod : cm (unipOfSA (R + R * E) hRE * unipOfSA2 E hEsupp) = cm t := by
    rw [cm_mul, cm_unipOfSA, cm_unipOfSA2, decomp_matrix hEE, hcN, hR, sub_add_cancel]
  have hteq : t = unipOfSA (R + R * E) hRE * unipOfSA2 E hEsupp := Hc_ext hprod.symm
  show t ∈ A1 ⊔ A2
  rw [hteq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hA) (Subgroup.mem_sup_right hB)

end CFSG.Quasithin.A94.L52
