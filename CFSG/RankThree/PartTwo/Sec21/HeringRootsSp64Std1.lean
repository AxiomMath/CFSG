module

public import CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64Blocks

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

open Matrix hiding ext
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesSp64
open CFSG.RankThree.PartTwo.Sec21.TablesL44 (eω eω_injective eω_ne_zero eω_add eω_zero)
open CFSG.RankThree.PartTwo CFSG.RankThree CFSG.RankThree.LocalRank CFSG
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank

section Ring

variable {R : Type*} [Ring R]

theorem blk_inv_aux (E X X' : R) (hEE : E * E = E) (hXE : X * E = E * X)
    (hX'E : X' * E = E * X') (hXX' : X * X' = 1) :
    (X * E + (1 - E)) * (X' * E + (1 - E)) = 1 := by
  have hEF : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hEE, sub_self]
  have hFE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hEE, sub_self]
  have hFF : (1 - E) * (1 - E) = 1 - E := by
    calc (1 - E) * (1 - E) = 1 - E - E + E * E := by noncomm_ring
      _ = 1 - E := by rw [hEE]; abel
  have e1 : (X * E + (1 - E)) * (X' * E + (1 - E)) =
      X * E * X' * E + X * E * (1 - E) + (1 - E) * X' * E + (1 - E) * (1 - E) := by
    noncomm_ring
  have p1 : X * E * X' * E = E := by
    calc X * E * X' * E = X * (E * X') * E := by noncomm_ring
      _ = X * (X' * E) * E := by rw [hX'E]
      _ = (X * X') * (E * E) := by noncomm_ring
      _ = E := by rw [hXX', hEE, one_mul]
  have p2 : X * E * (1 - E) = 0 := by
    calc X * E * (1 - E) = X * (E * (1 - E)) := by noncomm_ring
      _ = 0 := by rw [hEF, mul_zero]
  have p3 : (1 - E) * X' * E = 0 := by
    calc (1 - E) * X' * E = (1 - E) * (X' * E) := by noncomm_ring
      _ = (1 - E) * (E * X') := by rw [hX'E]
      _ = ((1 - E) * E) * X' := by noncomm_ring
      _ = 0 := by rw [hFE, zero_mul]
  rw [e1, p1, p2, p3, hFF]
  noncomm_ring

theorem blk_prod_aux (E X : R) (hEE : E * E = E) (hXE : X * E = E * X) :
    (X * E + (1 - E)) * (X * (1 - E) + (1 - (1 - E))) = X := by
  have hEF : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hEE, sub_self]
  have hFE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hEE, sub_self]
  have hFF : (1 - E) * (1 - E) = 1 - E := by
    calc (1 - E) * (1 - E) = 1 - E - E + E * E := by noncomm_ring
      _ = 1 - E := by rw [hEE]; abel
  have hFX : (1 - E) * X = X * (1 - E) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hXE]
  have e1 : (X * E + (1 - E)) * (X * (1 - E) + (1 - (1 - E))) =
      X * E * (X * (1 - E)) + X * E * E + (1 - E) * (X * (1 - E)) + (1 - E) * E := by
    noncomm_ring
  have p1 : X * E * (X * (1 - E)) = 0 := by
    calc X * E * (X * (1 - E)) = X * (E * X) * (1 - E) := by noncomm_ring
      _ = X * (X * E) * (1 - E) := by rw [hXE]
      _ = X * X * (E * (1 - E)) := by noncomm_ring
      _ = 0 := by rw [hEF, mul_zero]
  have p2 : X * E * E = X * E := by rw [mul_assoc, hEE]
  have p3 : (1 - E) * (X * (1 - E)) = X * (1 - E) := by
    calc (1 - E) * (X * (1 - E)) = ((1 - E) * X) * (1 - E) := by noncomm_ring
      _ = (X * (1 - E)) * (1 - E) := by rw [hFX]
      _ = X * ((1 - E) * (1 - E)) := by noncomm_ring
      _ = X * (1 - E) := by rw [hFF]
  rw [e1, p1, p2, p3, hFE]
  noncomm_ring

theorem blk_symp_aux (E X Xt J : R) (hEE : E * E = E) (hEJ : E * J = J * E)
    (hXE : X * E = E * X) (hXtE : E * Xt = Xt * E) (hXJ : Xt * J * X = J) :
    (E * Xt + (1 - E)) * J * (X * E + (1 - E)) = J := by
  have hFE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hEE, sub_self]
  have hEF : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hEE, sub_self]
  have hFF : (1 - E) * (1 - E) = 1 - E := by
    calc (1 - E) * (1 - E) = 1 - E - E + E * E := by noncomm_ring
      _ = 1 - E := by rw [hEE]; abel
  have hFJ : (1 - E) * J = J * (1 - E) := by rw [sub_mul, mul_sub, one_mul, mul_one, hEJ]
  have hFX : X * (1 - E) = (1 - E) * X := by rw [mul_sub, sub_mul, mul_one, one_mul, hXE]
  have hFXt : (1 - E) * Xt = Xt * (1 - E) := by rw [sub_mul, mul_sub, one_mul, mul_one, hXtE]
  have e1 : (E * Xt + (1 - E)) * J * (X * E + (1 - E)) =
      E * Xt * J * (X * E) + E * Xt * J * (1 - E) + (1 - E) * J * (X * E) +
        (1 - E) * J * (1 - E) := by
    noncomm_ring
  have T1 : E * Xt * J * (X * E) = J * E := by
    calc E * Xt * J * (X * E) = E * (Xt * J * X) * E := by noncomm_ring
      _ = E * J * E := by rw [hXJ]
      _ = J * E := by rw [hEJ, mul_assoc, hEE]
  have T2 : E * Xt * J * (1 - E) = 0 := by
    calc E * Xt * J * (1 - E) = E * (Xt * (J * (1 - E))) := by noncomm_ring
      _ = E * (Xt * ((1 - E) * J)) := by rw [hFJ]
      _ = E * ((Xt * (1 - E)) * J) := by noncomm_ring
      _ = E * (((1 - E) * Xt) * J) := by rw [hFXt]
      _ = (E * (1 - E)) * (Xt * J) := by noncomm_ring
      _ = 0 := by rw [hEF, zero_mul]
  have T3 : (1 - E) * J * (X * E) = 0 := by
    calc (1 - E) * J * (X * E) = (J * (1 - E)) * (X * E) := by rw [hFJ]
      _ = J * ((1 - E) * X) * E := by noncomm_ring
      _ = J * (X * (1 - E)) * E := by rw [hFX]
      _ = J * X * ((1 - E) * E) := by noncomm_ring
      _ = 0 := by rw [hFE, mul_zero]
  have T4 : (1 - E) * J * (1 - E) = J * (1 - E) := by
    calc (1 - E) * J * (1 - E) = J * (1 - E) * (1 - E) := by rw [hFJ]
      _ = J * ((1 - E) * (1 - E)) := by noncomm_ring
      _ = J * (1 - E) := by rw [hFF]
  rw [e1, T1, T2, T3, T4]
  noncomm_ring

end Ring

theorem blk_apply (X : Mat6) (e : Fin 3 ⊕ Fin 3 → F4) (x y : Fin 3 ⊕ Fin 3) :
    (X * diagonal e + (1 - diagonal e)) x y = X x y * e y + (if x = y then 1 - e x else 0) := by
  by_cases h : x = y
  · subst h
    simp [Matrix.mul_diagonal, Matrix.sub_apply]
  · simp [Matrix.mul_diagonal, Matrix.sub_apply, Matrix.one_apply_ne h, h]

theorem blk_isBlockDiag {α : Type*} {t : Fin 3 ⊕ Fin 3 → α} {X : Mat6} (hX : IsBlockDiag t X)
    (e : Fin 3 ⊕ Fin 3 → F4) : IsBlockDiag t (X * diagonal e + (1 - diagonal e)) := by
  intro x y hxy
  have hne : x ≠ y := fun h => hxy (h ▸ rfl)
  rw [blk_apply, hX x y hxy, if_neg hne]
  simp

theorem blk_isIdOutside {α : Type*} {t : Fin 3 ⊕ Fin 3 → α} {X : Mat6} (hX : IsBlockDiag t X)
    {e : Fin 3 ⊕ Fin 3 → F4} (he : ∀ x, e x = 0 ∨ e x = 1) (hfib : ∀ i j, t i = t j → e i = e j) :
    IsIdOutside {x | e x = 1} (X * diagonal e + (1 - diagonal e)) := by
  intro x y hxy
  rw [blk_apply]
  have hxy' : e x = 0 ∨ e y = 0 := by
    rcases hxy with hx | hy
    · left
      exact (he x).resolve_right hx
    · right
      exact (he y).resolve_right hy
  by_cases hxyeq : x = y
  · subst hxyeq
    have h0 : e x = 0 := by rcases hxy' with h | h <;> exact h
    rw [h0, Matrix.one_apply_eq]
    simp
  · rw [Matrix.one_apply_ne hxyeq, if_neg hxyeq]
    rcases hxy' with hx0 | hy0
    ·
      rcases he y with hy0 | hy1
      · rw [hy0, mul_zero, add_zero]
      · have hne : t x ≠ t y := fun h => by
          have := hfib x y h
          rw [hx0, hy1] at this
          exact zero_ne_one this
        rw [hX x y hne, zero_mul, add_zero]
    · rw [hy0, mul_zero, add_zero]

theorem exists_blk (e : Fin 3 ⊕ Fin 3 → F4) (he : ∀ x, e x * e x = e x)
    (hs : ∀ x, e x.swap = e x) (g : Sp) (hg : mat g * diagonal e = diagonal e * mat g) :
    ∃ h : Sp, mat h = mat g * diagonal e + (1 - diagonal e) := by
  set E : Mat6 := diagonal e with hE
  set X : Mat6 := mat g with hX
  set X' : Mat6 := mat g⁻¹ with hX'
  have hEE : E * E = E := by
    rw [hE, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    exact he x
  have hEt : Eᵀ = E := Matrix.diagonal_transpose e
  have hEJ : E * Jm = Jm * E := by
    ext x y
    rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal, Jm_apply]
    by_cases h : y = x.swap
    · rw [if_pos h, h, hs x, mul_one, one_mul]
    · rw [if_neg h]
      simp
  have hXX' : X * X' = 1 := mat_mul_inv g
  have hX'X : X' * X = 1 := mat_inv_mul g
  have hX'E : X' * E = E * X' := by
    calc X' * E = X' * E * (X * X') := by rw [hXX', Matrix.mul_one]
      _ = X' * (E * X) * X' := by noncomm_ring
      _ = X' * (X * E) * X' := by rw [← hg]
      _ = (X' * X) * E * X' := by noncomm_ring
      _ = E * X' := by rw [hX'X, Matrix.one_mul]
  have hXtE : E * Xᵀ = Xᵀ * E := by
    have h := congrArg Matrix.transpose hg
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hEt] at h
    exact h
  have hXJ : Xᵀ * Jm * X = Jm := mem_statedSp_iff.mp g.2
  have hBB' := blk_inv_aux E X X' hEE hg hX'E hXX'
  have hB'B := blk_inv_aux E X' X hEE hX'E hg hX'X
  have hBt : (X * E + (1 - E))ᵀ = E * Xᵀ + (1 - E) := by
    simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub, hEt]
  have hBJ : (X * E + (1 - E))ᵀ * Jm * (X * E + (1 - E)) = Jm := by
    rw [hBt]
    exact blk_symp_aux E X Xᵀ Jm hEE hEJ hg hXtE hXJ
  refine ⟨⟨⟨X * E + (1 - E), X' * E + (1 - E), hBB', hB'B⟩, ?_⟩, rfl⟩
  rw [mem_statedSp_iff]
  exact hBJ

@[expose] noncomputable def e1 (x : Fin 3 ⊕ Fin 3) : F4 := if ext (std 1) x = 0 then 1 else 0

theorem e1_01 (x : Fin 3 ⊕ Fin 3) : e1 x = 0 ∨ e1 x = 1 := by
  unfold e1
  by_cases h : ext (std 1) x = 0 <;> simp [h]

theorem e1_idem (x : Fin 3 ⊕ Fin 3) : e1 x * e1 x = e1 x := by
  rcases e1_01 x with h | h <;> rw [h] <;> simp

theorem e1_swap (x : Fin 3 ⊕ Fin 3) : e1 x.swap = e1 x := by
  unfold e1
  rw [ext_swap]
  by_cases h : ext (std 1) x = 0
  · have h0 : -ext (std 1) x = 0 := by rw [h]; decide
    rw [if_pos h0, if_pos h]
  · have h' : ¬ -ext (std 1) x = 0 := fun h0 => h (neg_eq_zero.mp h0)
    rw [if_neg h', if_neg h]

theorem e1_fibre (i j : Fin 3 ⊕ Fin 3) (h : ext (std 1) i = ext (std 1) j) : e1 i = e1 j := by
  unfold e1
  rw [h]

theorem e1_set : {x | e1 x = 1} = {i | ext (std 1) i = 0} := by
  ext x
  unfold e1
  by_cases h : ext (std 1) x = 0 <;> simp [h]

theorem e1'_set : {x | (fun y => 1 - e1 y) x = 1} = c01 := by
  ext x
  show 1 - e1 x = 1 ↔ ext (std 1) x ≠ 0
  unfold e1
  by_cases h : ext (std 1) x = 0 <;> simp [h]

theorem e1_inl (a : Fin 3) (h : a = 0 ∨ a = 1) : e1 (Sum.inl a) = 0 := by
  unfold e1
  rw [if_neg]
  rcases h with rfl | rfl <;> decide

theorem decomp_C1 (g : Sp) (hg : g ∈ C1) (hd : d2 ⟨g, hg⟩ = 1) :
    ∃ g₀ ∈ S2, ∃ g₁ ∈ Levi2, g = g₀ * g₁ := by
  have hX : IsBlockDiag (ext (std 1)) (mat g) := isBlockDiag_of_mem_centralizer hg
  have hXE : mat g * diagonal e1 = diagonal e1 * mat g :=
    commute_diagonal_of_isBlockDiag e1_fibre hX
  have hXE' : mat g * diagonal (fun x => 1 - e1 x) = diagonal (fun x => 1 - e1 x) * mat g :=
    commute_diagonal_of_isBlockDiag (fun i j h => by rw [e1_fibre i j h]) hX
  obtain ⟨g₀, hg₀⟩ := exists_blk e1 e1_idem e1_swap g hXE
  obtain ⟨g₁, hg₁⟩ := exists_blk (fun x => 1 - e1 x)
    (fun x => by have := e1_idem x; linear_combination this)
    (fun x => by rw [e1_swap]) g hXE'
  have hdiag : diagonal (fun x => 1 - e1 x) = 1 - diagonal e1 := by
    ext x y
    by_cases h : x = y
    · subst h
      simp [Matrix.sub_apply]
    · simp [Matrix.sub_apply, Matrix.one_apply_ne h, h]
  have hEE : diagonal e1 * diagonal e1 = diagonal e1 := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    exact e1_idem x
  have hg₀S2 : g₀ ∈ S2 := by
    rw [mem_S2_iff, hg₀, ← e1_set]
    exact blk_isIdOutside hX e1_01 e1_fibre
  have hbd₁ : IsBlockDiag (ext (std 1)) (mat g₁) := by
    rw [hg₁]
    exact blk_isBlockDiag hX _
  have hg₁C : g₁ ∈ C1 := mem_centralizer_of_isBlockDiag hbd₁
  have hent : ∀ a b : Fin 3, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      mat g₁ (Sum.inl a) (Sum.inl b) = mat g (Sum.inl a) (Sum.inl b) := by
    intro a b ha hb
    rw [hg₁, blk_apply, e1_inl a ha, e1_inl b hb]
    simp
  have hd₁ : d2 ⟨g₁, hg₁C⟩ = 1 := by
    rw [← hd]
    change mat g₁ (Sum.inl 0) (Sum.inl 0) * mat g₁ (Sum.inl 1) (Sum.inl 1) -
        mat g₁ (Sum.inl 0) (Sum.inl 1) * mat g₁ (Sum.inl 1) (Sum.inl 0) =
      mat g (Sum.inl 0) (Sum.inl 0) * mat g (Sum.inl 1) (Sum.inl 1) -
        mat g (Sum.inl 0) (Sum.inl 1) * mat g (Sum.inl 1) (Sum.inl 0)
    rw [hent 0 0 (Or.inl rfl) (Or.inl rfl), hent 1 1 (Or.inr rfl) (Or.inr rfl),
      hent 0 1 (Or.inl rfl) (Or.inr rfl), hent 1 0 (Or.inr rfl) (Or.inl rfl)]
  have hg₁L : g₁ ∈ Levi2 := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨⟨g₁, hg₁C⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩,
      ?_⟩
    · apply Units.ext
      exact hd₁
    · show IsIdOutside c01 (mat g₁)
      rw [hg₁, ← e1'_set]
      exact blk_isIdOutside hX (fun x => by rcases e1_01 x with h | h <;> simp [h])
        (fun i j h => by rw [e1_fibre i j h])
  have hprod : g = g₀ * g₁ := by
    apply mat_injective
    rw [mat_mul, hg₀, hg₁, hdiag]
    exact (blk_prod_aux (diagonal e1) (mat g) hEE hXE).symm
  exact ⟨g₀, hg₀S2, g₁, hg₁L, hprod⟩

theorem S2_le_C1 : S2 ≤ C1 := le_centralizer_of_iff (κ := 0) mem_S2_iff

theorem Levi2_le_C1 : Levi2 ≤ C1 := inf_le_left.trans (Subgroup.map_subtype_le _)

theorem components_std1 {Y : Subgroup C1} (hY : CFSG.IsComponent Y) :
    Y.map C1.subtype = S2 ∨ Y.map C1.subtype = Levi2 := by
  have key := components_eq_range_of_finite ![S2.subgroupOf C1, Levi2.subgroupOf C1]
    (Fin.forall_fin_two.mpr
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe S2_le_C1).symm
        isQuasisimple_S2,
       CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe Levi2_le_C1).symm
        isQuasisimple_Levi2⟩)
    (Fin.forall_fin_two.mpr
      ⟨normal_subgroupOf_of_iff (κ := 0) mem_S2_iff,
       (Subgroup.normal_subgroupOf_iff_le_normalizer Levi2_le_C1).mpr C1_le_normalizer_Levi2⟩)
    (fun P hP => by
      intro g hg
      have hd : d2 g = 1 := perfect_hom_trivial hP (d2.comp P.subtype) ⟨g, hg⟩
      obtain ⟨g₀, hg₀, g₁, hg₁, hgg⟩ := decomp_C1 (g : Sp) g.2 hd
      have hgeq : g = ⟨g₀, S2_le_C1 hg₀⟩ * ⟨g₁, Levi2_le_C1 hg₁⟩ := Subtype.ext hgg
      rw [hgeq]
      exact Subgroup.mul_mem _
        (Subgroup.mem_iSup_of_mem (0 : Fin 2) (Subgroup.mem_subgroupOf.mpr hg₀))
        (Subgroup.mem_iSup_of_mem (1 : Fin 2) (Subgroup.mem_subgroupOf.mpr hg₁)))
  have hmem : Y ∈ {K : Subgroup C1 | CFSG.IsComponent K} := hY
  rw [key] at hmem
  obtain ⟨i, rfl⟩ := hmem
  fin_cases i
  · exact Or.inl (Subgroup.map_subgroupOf_eq_of_le S2_le_C1)
  · exact Or.inr (Subgroup.map_subgroupOf_eq_of_le Levi2_le_C1)

theorem fibre1_zero : ∀ x : Fin 3 ⊕ Fin 3, ext (std 1) x = 0 ↔ (x = Sum.inl 2 ∨ x = Sum.inr 2) := by
  decide

theorem good_S2 {D : Set (MulAut A0)} (hs2 : sAut 1 (scFlip 2) ∈ D) : Good D S2 :=
  good_s2 hs2 fun g hg => (mem_S2_iff g).mpr (by
    have hset : {i : Fin 3 ⊕ Fin 3 | ext (std 1) i = 0} =
        {x : Fin 3 ⊕ Fin 3 | x = Sum.inl 2 ∨ x = Sum.inr 2} := Set.ext fibre1_zero
    rw [hset]
    exact hg)

theorem hsing_c01 : ∀ x y : Fin 3 ⊕ Fin 3, ext (std 1) x = 0 →
    (∀ v : Fin 3 → ZMod 3, v 0 = v 1 → ext v x = ext v y) → y = x := by
  decide +kernel

theorem good_Levi2 {D : Set (MulAut A0)}
    (hρ : sAut (Equiv.swap 0 1) (fun _ => false) ∈ D) : Good D Levi2 := by
  refine good_rho01 hρ fun P hP hPC => ?_
  have hPC1 : P ≤ C1 := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hPC g hg (std 1) (by decide))
  have hid := idOutside_of_perfect hP {v | v 0 = v 1} c01
    (fun x hx y hy => hsing_c01 x y (not_not.mp hx) hy) (fun g hg v hv => hPC g hg v hv)
  intro g hg
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨⟨g, hPC1 hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩,
    hid g hg⟩
  apply Units.ext
  exact perfect_hom_trivial hP (d2.comp (Subgroup.inclusion hPC1)) ⟨g, hg⟩

end CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

end
