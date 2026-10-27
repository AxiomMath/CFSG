module

public import CFSG.RankThree.PartOne.KFCL.SpClasses
public import CFSG.RankThree.PartOne.KFCL.SpOrbit

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFCL.BlockSL CFSG.LieType.Steinberg.Sp
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups commutatorElement Classical

variable {K : Type} [Field K] {p : ℕ}

section Tau

theorem sumCongr_mem_Hp {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.sumCongr π π ∈ Hp n := by
  intro a
  rcases a with i | i <;> rfl

theorem swap_mem_Hp {n : ℕ} (k : Fin n) : Equiv.swap (Sum.inl k) (Sum.inr k) ∈ Hp n := by
  intro a
  by_cases h1 : a = Sum.inl k
  · subst h1
    simp [par]
  · by_cases h2 : a = Sum.inr k
    · subst h2
      simp [par]
    · have h3 : par a ≠ Sum.inl k := by
        intro h
        apply h2
        rw [← par_par a, h]
        rfl
      have h4 : par a ≠ Sum.inr k := by
        intro h
        apply h1
        rw [← par_par a, h]
        rfl
      rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem exists_perm_pair' {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm α, σ a = c ∧ σ b = d := by
  have hbc : Equiv.swap a c b ≠ c := by
    intro h
    have : Equiv.swap a c b = Equiv.swap a c a := by rw [h, Equiv.swap_apply_left]
    exact hab (Equiv.injective _ this).symm
  refine ⟨Equiv.swap (Equiv.swap a c b) d * Equiv.swap a c, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hbc.symm hcd
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem exists_tau (a b : Fin 3 ⊕ Fin 3) (hab : a ≠ b) (hb : b ≠ par a) :
    ∃ τ ∈ Hp 3, τ (Sum.inl 0) = a ∧ τ (Sum.inl 1) = b := by
  rcases a with i | i <;> rcases b with j | j
  · have hij : i ≠ j := fun h => hab (by rw [h])
    obtain ⟨π, h0, h1⟩ := exists_perm_pair' (show (0 : Fin 3) ≠ 1 by decide) hij
    exact ⟨Equiv.sumCongr π π, sumCongr_mem_Hp π, by simp [h0], by simp [h1]⟩
  · have hij : i ≠ j := fun h => hb (by rw [h]; rfl)
    obtain ⟨π, h0, h1⟩ := exists_perm_pair' (show (0 : Fin 3) ≠ 1 by decide) hij
    refine ⟨Equiv.swap (Sum.inl j) (Sum.inr j) * Equiv.sumCongr π π,
      (Hp 3).mul_mem (swap_mem_Hp j) (sumCongr_mem_Hp π), ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl, h0]
      exact Equiv.swap_apply_of_ne_of_ne (by simpa using hij) (by simp)
    · simp [h1]
  · have hij : i ≠ j := fun h => hb (by rw [h]; rfl)
    obtain ⟨π, h0, h1⟩ := exists_perm_pair' (show (0 : Fin 3) ≠ 1 by decide) hij
    refine ⟨Equiv.swap (Sum.inl i) (Sum.inr i) * Equiv.sumCongr π π,
      (Hp 3).mul_mem (swap_mem_Hp i) (sumCongr_mem_Hp π), ?_, ?_⟩
    · simp [h0]
    · simp only [Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl, h1]
      exact Equiv.swap_apply_of_ne_of_ne (by simpa using hij.symm) (by simp)
  · have hij : i ≠ j := fun h => hab (by rw [h])
    obtain ⟨π, h0, h1⟩ := exists_perm_pair' (show (0 : Fin 3) ≠ 1 by decide) hij
    refine ⟨Equiv.swap (Sum.inl j) (Sum.inr j) * (Equiv.swap (Sum.inl i) (Sum.inr i) *
      Equiv.sumCongr π π),
      (Hp 3).mul_mem (swap_mem_Hp j) ((Hp 3).mul_mem (swap_mem_Hp i) (sumCongr_mem_Hp π)), ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl, h0, Equiv.swap_apply_left]
      exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hij)
    · have e : Equiv.swap (Sum.inl i : Fin 3 ⊕ Fin 3) (Sum.inr i) (Sum.inl j) = Sum.inl j :=
        Equiv.swap_apply_of_ne_of_ne (by simpa using hij.symm) (by simp)
      simp only [Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl, h1, e]
      exact Equiv.swap_apply_left _ _

end Tau

section Peel

variable [CharP K 2]

@[expose] noncomputable def Jjoin (p : ℕ) (S : Subgroup (StatedSp 3 K)) : Subgroup (StatedSp 3 K) :=
  ⨆ B : {B : ↥(blockOrbit (spWeyl 3 K) (SpStd K)) //
      S ≤ spTorus p 3 K ⊓ Subgroup.centralizer (B.1 : Set (StatedSp 3 K))}, B.1.1

theorem le_Jjoin {S B : Subgroup (StatedSp 3 K)} (hB : B ∈ blockOrbit (spWeyl 3 K) (SpStd K))
    (hS : S ≤ spTorus p 3 K ⊓ Subgroup.centralizer (B : Set (StatedSp 3 K))) : B ≤ Jjoin p S :=
  le_iSup (fun B : {B : ↥(blockOrbit (spWeyl 3 K) (SpStd K)) //
      S ≤ spTorus p 3 K ⊓ Subgroup.centralizer (B.1 : Set (StatedSp 3 K))} => B.1.1) ⟨⟨B, hB⟩, hS⟩

theorem conj_Ss_mem_orbit {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) :
    (Ss K).map (MulAut.conj (permSp τ hτ)).toMonoidHom ∈ blockOrbit (spWeyl 3 K) (SpStd K) :=
  ⟨permSp τ hτ, mem_spWeyl_iff.2 ⟨τ, hτ, rfl⟩, Ss K, Or.inr rfl, rfl⟩

theorem conj_Sl_mem_orbit {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) :
    (Sl K).map (MulAut.conj (permSp τ hτ)).toMonoidHom ∈ blockOrbit (spWeyl 3 K) (SpStd K) :=
  ⟨permSp τ hτ, mem_spWeyl_iff.2 ⟨τ, hτ, rfl⟩, Sl K, Or.inl rfl, rfl⟩

theorem le_hyp_conj_Ss {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K)
    {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3)
    (h : cls S (τ (Sum.inl 0)) = cls S (τ (Sum.inl 1))) :
    S ≤ spTorus p 3 K ⊓ Subgroup.centralizer
      (((Ss K).map (MulAut.conj (permSp τ hτ)).toMonoidHom : Subgroup (StatedSp 3 K)) : Set (StatedSp 3 K)) := by
  intro s hs
  refine ⟨hST hs, (mem_centralizer_map_conj_iff hτ).2 ?_⟩
  refine (mem_centralizer_Ss_iff (cj_mem_spTorus hτ (hST hs))).2 ?_
  rw [mat_cj_apply, mat_cj_apply]
  exact congrFun h ⟨s, hs⟩

theorem Wel_mem_conj {τ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hτ : τ ∈ Hp 3) (c : K) :
    permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹ ∈
      (Ss K).map (MulAut.conj (permSp τ hτ)).toMonoidHom :=
  Subgroup.mem_map.2 ⟨_, ⟨sl2Upper c, shortBlock_sl2Upper h01 c⟩, rfl⟩

theorem Wel_spec (hodd : Odd p) {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K)
    {i j : Fin 3 ⊕ Fin 3} (hij : i ≠ j) (hcls : cls S i = cls S j) (hκ : cls S i ≠ 1) (c : K) :
    ∃ h : StatedSp 3 K, h ∈ Jjoin p S ∧ h ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) ∧
      mat 3 K h = 1 + c • (Matrix.single i j 1 - Matrix.single (par j) (par i) 1) := by
  have hjpar : j ≠ par i := by
    intro h
    apply cls_par_ne hodd hST hκ
    rw [← h]
    exact hcls.symm
  obtain ⟨τ, hτ, h0, h1⟩ := exists_tau i j hij hjpar
  have hS := le_hyp_conj_Ss hST hτ (by rw [h0, h1]; exact hcls)
  refine ⟨permSp τ hτ * elt (.difference 0 1 h01) c * (permSp τ hτ)⁻¹,
    le_Jjoin (conj_Ss_mem_orbit hτ) hS (Wel_mem_conj hτ c), ?_, ?_⟩
  · intro s hs
    exact (Subgroup.mem_centralizer_iff.1 (hS hs).2 _ (Wel_mem_conj hτ c)).symm
  · rw [mat_conj_elt_diff, h0, h1]

omit [CharP K 2] in
theorem blkS_Wel_other {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K) {κ : ↥S → K}
    {i j : Fin 3 ⊕ Fin 3} (hi : cls S i = κ) (hj : cls S j = κ) {h : StatedSp 3 K} {c : K}
    (hmat : mat 3 K h = 1 + c • (Matrix.single i j 1 - Matrix.single (par j) (par i) 1))
    {l : ↥S → K} (hl : l ≠ κ) (hl' : l ≠ κ⁻¹) : blkS S l h = 1 := by
  ext a b
  rw [blkS_apply, hmat]
  have h1 : i ≠ a.1 := fun h => hl (by rw [← a.2, ← h, hi])
  have h2 : par j ≠ a.1 := by
    intro h
    have h3 := cls_par hST j
    rw [hj, h, a.2] at h3
    exact hl' h3
  simp [Matrix.single_apply_of_row_ne h1, Matrix.single_apply_of_row_ne h2, Matrix.one_apply,
    Subtype.ext_iff]

omit [CharP K 2] in
theorem blkS_Wel_main {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K) {κ : ↥S → K}
    (hκinv : κ⁻¹ ≠ κ) {i j : Fin 3 ⊕ Fin 3} (hi : cls S i = κ) (hj : cls S j = κ)
    {h : StatedSp 3 K} {c : K}
    (hmat : mat 3 K h = 1 + c • (Matrix.single i j 1 - Matrix.single (par j) (par i) 1)) :
    blkS S κ h = Matrix.transvection (⟨i, hi⟩ : {a // cls S a = κ}) ⟨j, hj⟩ c := by
  ext a b
  rw [blkS_apply, hmat]
  have h2 : par j ≠ a.1 := by
    intro h
    have h3 := cls_par hST j
    rw [hj, h, a.2] at h3
    exact hκinv h3.symm
  simp [Matrix.transvection, Matrix.single_apply_of_row_ne h2, Matrix.single_apply, Matrix.one_apply,
    Subtype.ext_iff]

theorem peel_step (hodd : Odd p) {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K) {κ : ↥S → K}
    (hκ : κ ≠ 1) (A : Matrix.SpecialLinearGroup {a // cls S a = κ} K) :
    ∃ h ∈ Jjoin p S, h ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) ∧ blkS S κ h = A.1 ∧
      ∀ l : ↥S → K, l ≠ κ → l ≠ κ⁻¹ → blkS S l h = 1 := by
  have hmain : ∀ A ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct {a // cls S a = κ} K → Matrix.SpecialLinearGroup {a // cls S a = κ} K)),
      ∃ h ∈ Jjoin p S, h ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) ∧ blkS S κ h = A.1 ∧
        ∀ l : ↥S → K, l ≠ κ → l ≠ κ⁻¹ → blkS S l h = 1 := by
    intro A hA
    refine Subgroup.closure_induction
      (p := fun A _ => ∃ h ∈ Jjoin p S, h ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) ∧
        blkS S κ h = A.1 ∧ ∀ l : ↥S → K, l ≠ κ → l ≠ κ⁻¹ → blkS S l h = 1) ?_ ?_ ?_ ?_ hA
    · rintro x ⟨t, rfl⟩
      have hcls : cls S t.i.1 = cls S t.j.1 := t.i.2.trans t.j.2.symm
      have hne : t.i.1 ≠ t.j.1 := fun h => t.hij (Subtype.ext h)
      have hκ' : cls S t.i.1 ≠ 1 := by rw [t.i.2]; exact hκ
      have hκinv : κ⁻¹ ≠ κ := by
        have := cls_par_ne hodd hST hκ'
        rwa [cls_par hST, t.i.2] at this
      obtain ⟨h, hJ, hC, hmat⟩ := Wel_spec hodd hST hne hcls hκ' t.c
      refine ⟨h, hJ, hC, ?_, fun l hl hl' => blkS_Wel_other hST t.i.2 t.j.2 hmat hl hl'⟩
      rw [blkS_Wel_main hST hκinv t.i.2 t.j.2 hmat]
      rfl
    · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [blkS_one]; rfl, fun l _ _ => blkS_one l⟩
    · rintro x y - - ⟨h₁, hJ₁, hC₁, hb₁, hl₁⟩ ⟨h₂, hJ₂, hC₂, hb₂, hl₂⟩
      refine ⟨h₁ * h₂, Subgroup.mul_mem _ hJ₁ hJ₂, Subgroup.mul_mem _ hC₁ hC₂, ?_, fun l hl hl' => ?_⟩
      · rw [blkS_mul hST κ hC₁, hb₁, hb₂]
        rfl
      · rw [blkS_mul hST l hC₁, hl₁ l hl hl', hl₂ l hl hl', one_mul]
    · rintro x - ⟨h, hJ, hC, hb, hl⟩
      refine ⟨h⁻¹, Subgroup.inv_mem _ hJ, Subgroup.inv_mem _ hC, ?_, fun l hl' hl'' => ?_⟩
      · rw [blkS_inv hST κ hC, hb]
        refine Matrix.inv_eq_right_inv ?_
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
        rfl
      · rw [blkS_inv hST l hC, hl l hl' hl'', inv_one]
  rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hmain
  exact hmain A (Subgroup.mem_top A)

end Peel

end CFSG.RankThree.PartOne.KFCL.Sp
