module

public import CFSG.Foundations.Basic
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Six

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open Equiv CFSG.QuasithinUnique.Borel252.A6

@[expose] def zA : P6 := swap 0 2 * swap 1 3

@[expose] def zB : P6 := swap 4 5

@[expose] def x0 : P6 := swap 0 1 * swap 1 4

theorem zB_mul_self : zB * zB = 1 := by decide

theorem zB_inv : zB⁻¹ = zB := inv_eq_of_mul_eq_one_right zB_mul_self

theorem sign_zB : Perm.sign zB = -1 := Perm.sign_swap (by decide)

theorem zB_not_mem : zB ∉ A6s := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_zB]
  decide

theorem x0_mem : x0 ∈ A6s := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem enc_zB_comm_d0 : ∀ r ∈ d0L, R6.enc zB * r = r * R6.enc zB := by decide +kernel

theorem enc_va_comm : ∀ r ∈ vaL, ∀ s ∈ vaL, r * s = s * r := by decide +kernel

theorem enc_vb_comm : ∀ r ∈ vbL, ∀ s ∈ vbL, r * s = s * r := by decide +kernel

theorem enc_va_vb : ∀ r ∈ vaL, r ∈ vbL → r = 1 ∨ r = R6.enc zA := by decide +kernel

theorem enc_zA : R6.enc zA ∈ vaL ∧ R6.enc zA ∈ vbL := by decide +kernel

theorem enc_d0_prod : ∀ r ∈ d0L, ∀ s ∈ d0L, r ∉ vaL → s ∉ vbL → r * r = 1 → s * s = 1 →
    (r * s) * (r * s) ≠ 1 := by decide +kernel

@[expose] def extL (L : List R6) (r : R6) : Bool := decide (r ∈ L) || decide (r * R6.enc zB ∈ L)

theorem enc_s06_prod : ∀ r ∈ d0L ++ d0L.map (· * R6.enc zB), ∀ s ∈ d0L ++ d0L.map (· * R6.enc zB),
    extL vaL r = false → extL vbL s = false → r * r = 1 → s * s = 1 → (r * s) * (r * s) ≠ 1 := by
  decide +kernel

theorem enc_eq_iff {x y : P6} : x = y ↔ R6.enc x = R6.enc y := ⟨congrArg _, fun h => R6.enc_inj h⟩

theorem mul_self_iff {x : P6} : x * x = 1 ↔ R6.enc x * R6.enc x = 1 := by
  rw [enc_eq_iff, R6.enc_mul, R6.enc_one]

theorem zB_comm_D0 {d : P6} (hd : d ∈ D0) : zB * d = d * zB := by
  rw [enc_eq_iff, R6.enc_mul, R6.enc_mul]
  exact enc_zB_comm_d0 _ ((mem_D0 d).1 hd)

theorem zA_mem_VA : zA ∈ VA := (mem_VA zA).2 enc_zA.1

theorem zA_mem_VB : zA ∈ VB := (mem_VB zA).2 enc_zA.2

theorem zB_comm_of_mul_mem {y : P6} (hy : y * zB ∈ D0) : zB * y = y * zB := by
  have h := zB_comm_D0 hy
  calc zB * y = zB * (y * zB) * zB := by rw [mul_assoc, mul_assoc, zB_mul_self, mul_one]
    _ = y * zB * zB * zB := by rw [h]
    _ = y * zB := by rw [mul_assoc y zB zB, zB_mul_self, mul_one]

@[expose] def extZ (X : Subgroup P6) (hX : X ≤ D0) : Subgroup P6 where
  carrier := {x | x ∈ X ∨ x * zB ∈ X}
  one_mem' := Or.inl X.one_mem
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (X.mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact X.mul_mem hx hy)
    · refine Or.inr ?_
      have h : x * y * zB = x * zB * y := by rw [mul_assoc, ← zB_comm_D0 (hX hy), ← mul_assoc]
      rw [h]
      exact X.mul_mem hx hy
    · refine Or.inl ?_
      have h : x * y = x * zB * (y * zB) := by
        rw [mul_assoc x zB, ← mul_assoc zB y zB, zB_comm_of_mul_mem (hX hy), mul_assoc y zB zB,
          zB_mul_self, mul_one]
      rw [h]
      exact X.mul_mem hx hy
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (X.inv_mem hx)
    · refine Or.inr ?_
      have hc := zB_comm_of_mul_mem (hX hx)
      have h : x⁻¹ * zB = (x * zB)⁻¹ := by
        rw [mul_inv_rev, zB_inv]
        calc x⁻¹ * zB = x⁻¹ * (zB * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * zB) * x⁻¹ := by rw [hc]
          _ = zB * x⁻¹ := by group
      rw [h]
      exact X.inv_mem hx

variable {X Y : Subgroup P6} {hX : X ≤ D0} {hY : Y ≤ D0}

theorem zB_mem_extZ : zB ∈ extZ X hX := Or.inr (by rw [zB_mul_self]; exact X.one_mem)

theorem extZ_mono (h : X ≤ Y) : extZ X hX ≤ extZ Y hY := fun _ hx => hx.imp (@h _) (@h _)

theorem mem_of_mem_extZ_of_mem {x : P6} (hx : x ∈ extZ X hX) (hev : x ∈ A6s) : x ∈ X := by
  rcases hx with hx | hx
  · exact hx
  · exfalso
    apply zB_not_mem
    have h : zB = x⁻¹ * (x * zB) := by group
    rw [h]
    exact A6s.mul_mem (A6s.inv_mem hev) (D0_le_A6 (hX hx))

theorem mul_mem_of_mem_extZ_of_not_mem {x : P6} (hx : x ∈ extZ X hX) (hod : x ∉ A6s) :
    x * zB ∈ X :=
  hx.resolve_left fun h => hod (D0_le_A6 (hX h))

@[expose] def S06 : Subgroup P6 := extZ D0 le_rfl

@[expose] def A1 : Subgroup P6 := extZ VA VA_le_D0

@[expose] def A2 : Subgroup P6 := extZ VB VB_le_D0

@[expose] def Z6 : Subgroup P6 := extZ (VA ⊓ VB) (inf_le_left.trans VA_le_D0)

theorem A1_inf_A2 : A1 ⊓ A2 = Z6 := by
  refine le_antisymm ?_ (le_inf (extZ_mono inf_le_left) (extZ_mono inf_le_right))
  rintro x ⟨h1, h2⟩
  by_cases hx : x ∈ A6s
  · exact Or.inl ⟨mem_of_mem_extZ_of_mem h1 hx, mem_of_mem_extZ_of_mem h2 hx⟩
  · exact Or.inr ⟨mul_mem_of_mem_extZ_of_not_mem h1 hx, mul_mem_of_mem_extZ_of_not_mem h2 hx⟩

theorem mem_inf_VA_VB {x : P6} (hx : x ∈ VA ⊓ VB) : x = 1 ∨ x = zA := by
  have h := enc_va_vb _ ((mem_VA x).1 hx.1) ((mem_VB x).1 hx.2)
  rw [← R6.enc_one] at h
  exact h.imp (fun h => R6.enc_inj h) (fun h => R6.enc_inj h)

theorem card_Z6_le : Nat.card Z6 ≤ 4 := by
  let f : Fin 4 → P6 := ![1, zA, zB, zA * zB]
  have hf : ∀ x ∈ Z6, ∃ i, f i = x := by
    rintro x (hx | hx)
    · rcases mem_inf_VA_VB hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rcases mem_inf_VA_VB hx with h | h
      · exact ⟨2, by
          show zB = x
          calc zB = x * zB * zB := by rw [h, one_mul]
            _ = x := by rw [mul_assoc, zB_mul_self, mul_one]⟩
      · exact ⟨3, by
          show zA * zB = x
          rw [← h, mul_assoc, zB_mul_self, mul_one]⟩
  have hsurj : Function.Surjective (fun i : {i : Fin 4 // f i ∈ Z6} => (⟨f i, i.2⟩ : Z6)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := hf x hx
    exact ⟨⟨i, hi ▸ hx⟩, Subtype.ext hi⟩
  calc Nat.card Z6 ≤ Nat.card {i : Fin 4 // f i ∈ Z6} := Nat.card_le_card_of_surjective _ hsurj
    _ ≤ Nat.card (Fin 4) := Finite.card_subtype_le _
    _ = 4 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)

theorem comm_of_mem_VA {x y : P6} (hx : x ∈ VA) (hy : y ∈ VA) : x * y = y * x := by
  rw [enc_eq_iff, R6.enc_mul, R6.enc_mul]
  exact enc_va_comm _ ((mem_VA x).1 hx) _ ((mem_VA y).1 hy)

theorem comm_of_mem_VB {x y : P6} (hx : x ∈ VB) (hy : y ∈ VB) : x * y = y * x := by
  rw [enc_eq_iff, R6.enc_mul, R6.enc_mul]
  exact enc_vb_comm _ ((mem_VB x).1 hx) _ ((mem_VB y).1 hy)

theorem centralizer_extZ {X : Subgroup P6} (hX : X ≤ D0)
    (hcent : ∀ x ∈ A6s, (∀ v ∈ X, x * v = v * x) → x ∈ X)
    (hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Subgroup.centralizer (X : Set P6) = extZ X hX := by
  ext x
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h' : ∀ v ∈ X, x * v = v * x := fun v hv => (h v hv).symm
    by_cases hx : x ∈ A6s
    · exact Or.inl (hcent x hx h')
    · refine Or.inr (hcent _ ?_ fun v hv => ?_)
      · rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_zB]
        rw [Equiv.Perm.mem_alternatingGroup] at hx
        rcases Int.units_eq_one_or (Perm.sign x) with h1 | h1
        · exact absurd h1 hx
        · rw [h1]; decide
      · calc x * zB * v = x * (zB * v) := mul_assoc _ _ _
          _ = x * (v * zB) := by rw [zB_comm_D0 (hX hv)]
          _ = x * v * zB := (mul_assoc _ _ _).symm
          _ = v * x * zB := by rw [h' v hv]
          _ = v * (x * zB) := mul_assoc _ _ _
  · rintro (hx | hx) v hv
    · exact hab v hv x hx
    · have h1 := hab v hv _ hx
      have h2 : v * zB = zB * v := (zB_comm_D0 (hX hv)).symm
      calc v * x = v * (x * zB * zB) := by rw [mul_assoc x, zB_mul_self, mul_one]
        _ = v * (x * zB) * zB := (mul_assoc _ _ _).symm
        _ = x * zB * v * zB := by rw [h1]
        _ = x * zB * (v * zB) := mul_assoc _ _ _
        _ = x * zB * (zB * v) := by rw [h2]
        _ = x * v := by rw [← mul_assoc, mul_assoc x zB zB, zB_mul_self, mul_one]

theorem centralizer_VA : Subgroup.centralizer (VA : Set P6) = A1 :=
  centralizer_extZ VA_le_D0 (fun _ hx h => cent_VA hx h) (fun _ hx _ hy => comm_of_mem_VA hx hy)

theorem centralizer_VB : Subgroup.centralizer (VB : Set P6) = A2 :=
  centralizer_extZ VB_le_D0 (fun _ hx h => cent_VB hx h) (fun _ hx _ hy => comm_of_mem_VB hx hy)

theorem zB_mem_normalizer_D0 : zB ∈ Subgroup.normalizer (D0 : Set P6) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  rw [zB_inv]
  constructor
  · intro hd
    rw [zB_comm_D0 hd, mul_assoc, zB_mul_self, mul_one]
    exact hd
  · intro hd
    have h := zB_comm_D0 hd
    have e : d = zB * d * zB := by
      have e1 : zB * (zB * d * zB) * zB = d := by
        rw [← mul_assoc, ← mul_assoc, zB_mul_self, one_mul, mul_assoc, zB_mul_self, mul_one]
      calc d = zB * (zB * d * zB) * zB := e1.symm
        _ = zB * d * zB * zB * zB := by rw [h]
        _ = zB * d * zB := by rw [mul_assoc (zB * d * zB) zB zB, zB_mul_self, mul_one]
    rw [e]
    exact hd

theorem normalizer_D0_le : Subgroup.normalizer (D0 : Set P6) ≤ S06 := by
  intro x hx
  by_cases hev : x ∈ A6s
  · exact Or.inl ((norm_D0 x hev).1 hx)
  · refine Or.inr ((norm_D0 _ ?_).1 (Subgroup.mul_mem _ hx zB_mem_normalizer_D0))
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_zB]
    rw [Equiv.Perm.mem_alternatingGroup] at hev
    rcases Int.units_eq_one_or (Perm.sign x) with h1 | h1
    · exact absurd h1 hev
    · rw [h1]; decide

theorem le_or_le_D0 {W : Subgroup P6} (hW : W ≤ D0) (h2 : ∀ w ∈ W, w * w = 1) :
    W ≤ VA ∨ W ≤ VB := by
  by_contra h
  push Not at h
  obtain ⟨⟨w₁, hw₁, hw₁'⟩, ⟨w₂, hw₂, hw₂'⟩⟩ :=
    And.intro (Set.not_subset.mp h.1) (Set.not_subset.mp h.2)
  refine enc_d0_prod _ ((mem_D0 w₁).1 (hW hw₁)) _ ((mem_D0 w₂).1 (hW hw₂))
    (fun h => hw₁' ((mem_VA w₁).2 h)) (fun h => hw₂' ((mem_VB w₂).2 h))
    (mul_self_iff.1 (h2 _ hw₁)) (mul_self_iff.1 (h2 _ hw₂)) ?_
  rw [← R6.enc_mul, ← mul_self_iff]
  exact h2 _ (W.mul_mem hw₁ hw₂)

theorem enc_mem_s06L {x : P6} (hx : x ∈ S06) : R6.enc x ∈ d0L ++ d0L.map (· * R6.enc zB) := by
  rcases hx with hx | hx
  · exact List.mem_append_left _ ((mem_D0 x).1 hx)
  · refine List.mem_append_right _ (List.mem_map.2 ⟨_, (mem_D0 _).1 hx, ?_⟩)
    rw [← R6.enc_mul, mul_assoc, zB_mul_self, mul_one]

theorem extL_eq_false {X : Subgroup P6} {hX : X ≤ D0} {L : List R6}
    (hL : ∀ y, y ∈ X ↔ R6.enc y ∈ L) {x : P6} (hx : x ∉ extZ X hX) : extL L (R6.enc x) = false := by
  simp only [extL, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨fun h => hx (Or.inl ((hL x).2 h)), fun h => hx (Or.inr ((hL _).2 ?_))⟩
  rwa [R6.enc_mul]

theorem le_or_le_S06 {W : Subgroup P6} (hW : W ≤ S06) (h2 : ∀ w ∈ W, w * w = 1) :
    W ≤ A1 ∨ W ≤ A2 := by
  by_contra h
  push Not at h
  obtain ⟨⟨w₁, hw₁, hw₁'⟩, ⟨w₂, hw₂, hw₂'⟩⟩ :=
    And.intro (Set.not_subset.mp h.1) (Set.not_subset.mp h.2)
  refine enc_s06_prod _ (enc_mem_s06L (hW hw₁)) _ (enc_mem_s06L (hW hw₂))
    (extL_eq_false mem_VA hw₁') (extL_eq_false mem_VB hw₂')
    (mul_self_iff.1 (h2 _ hw₁)) (mul_self_iff.1 (h2 _ hw₂)) ?_
  rw [← R6.enc_mul, ← mul_self_iff]
  exact h2 _ (W.mul_mem hw₁ hw₂)

@[expose] def c6 : P6 := List.formPerm [0, 1, 2, 3, 4, 5]

@[expose] def zA' : P6 := x0⁻¹ * zA * x0

@[expose] def zB' : P6 := x0⁻¹ * zB * x0

theorem c6_word : c6 = zB * zB' * zB * zA' * zA * zB * zB' := by decide +kernel

theorem swap_word : swap (0 : Fin 6) 1 = zA' * zB' * zA * zB' * zA * zA' * zB' := by
  decide +kernel

theorem isCycle_c6 : c6.IsCycle := List.isCycle_formPerm (by decide) (by decide)

theorem support_c6 : c6.support = Finset.univ := by decide +kernel

theorem c6_zero : c6 0 = 1 := by decide

theorem mem_conjugate_x0 {z : P6} (hz : z ∈ Z6) : x0⁻¹ * z * x0 ∈ CFSG.conjugate Z6 x0 :=
  ⟨z, hz, by simp⟩

theorem sup_Z6_conj_eq_top : Z6 ⊔ CFSG.conjugate Z6 x0 = ⊤ := by
  set W := Z6 ⊔ CFSG.conjugate Z6 x0 with hW
  have hzA : zA ∈ W := le_sup_left (a := Z6) (Or.inl ⟨zA_mem_VA, zA_mem_VB⟩)
  have hzB : zB ∈ W := le_sup_left (a := Z6) zB_mem_extZ
  have hzA' : zA' ∈ W :=
    le_sup_right (a := Z6) (mem_conjugate_x0 (Or.inl ⟨zA_mem_VA, zA_mem_VB⟩))
  have hzB' : zB' ∈ W := le_sup_right (a := Z6) (mem_conjugate_x0 zB_mem_extZ)
  have h6 : c6 ∈ W := by
    rw [c6_word]
    exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem hzB hzB') hzB) hzA')
      hzA) hzB) hzB'
  have hs : swap (0 : Fin 6) (c6 0) ∈ W := by
    rw [c6_zero, swap_word]
    exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem hzA' hzB') hzA) hzB')
      hzA) hzA') hzB'
  rw [eq_top_iff, ← Equiv.Perm.closure_cycle_adjacent_swap isCycle_c6 support_c6 0,
    Subgroup.closure_le]
  rintro y (rfl | rfl)
  · exact h6
  · exact hs

end CFSG.Quasithin.Ch3E213M.P6E
