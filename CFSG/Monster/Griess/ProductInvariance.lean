module

public import CFSG.Monster.Griess.Invariance.TwoCoord
public import CFSG.Monster.Griess.Invariance.OddTwoCoord
public import CFSG.Monster.Griess.Invariance.OctadTwoCoord
public import CFSG.Monster.Griess.Invariance.ThreeOctad
public import CFSG.Monster.Griess.Invariance.OddOctad
public import CFSG.Monster.Griess.Grading
public import CFSG.Monster.Griess.FourGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix Module

namespace ProdInv

@[expose] def Inv3 (u v w : SpaceB) : Prop := T (tauB u) (tauB v) (tauB w) = T u v w

theorem Inv3.swap12 {u v w : SpaceB} (h : Inv3 u v w) : Inv3 v u w := by
  unfold Inv3 at *
  rw [T_swap12, h, T_swap12]

theorem Inv3.swap23 {u v w : SpaceB} (h : Inv3 u v w) : Inv3 u w v := by
  unfold Inv3 at *
  rw [T_swap23, h, T_swap23]

theorem inv3_of_grade {x y z : TIdx} (h : tgrade x + tgrade y + tgrade z ≠ 0) :
    Inv3 (tbasis x) (tbasis y) (tbasis z) := by
  unfold Inv3
  rw [T_Bg h (tbasis_mem_Bg x) (tbasis_mem_Bg y) (tbasis_mem_Bg z)]
  refine T_Bg ?_ (tauB_tbasis_mem_Bg x) (tauB_tbasis_mem_Bg y) (tauB_tbasis_mem_Bg z)
  rw [← map_add, ← map_add]
  intro h0
  exact h ((AddEquivClass.map_eq_zero_iff (f := alphaG)).1 h0)

theorem basisA_diag_eq (i : Fin 24) :
    (basisA s(i, i) : Matrix (Fin 24) (Fin 24) ℚ) = diagonal (Pi.single i 1) := by
  rw [coe_basisA, ite_eq_left rfl, diagonal_single]

theorem inv3_diag₁ (i : Fin 24) (v w : SpaceB) : Inv3 (tbasis (.inl i)) v w := by
  unfold Inv3
  rw [tbasis_diag]
  exact (T_tauB_of_diagonal (basisA_diag_eq i) v w).1

theorem inv3_diag₂ (i : Fin 24) (u w : SpaceB) : Inv3 u (tbasis (.inl i)) w := by
  unfold Inv3
  rw [tbasis_diag]
  exact (T_tauB_of_diagonal (basisA_diag_eq i) u w).2.1

theorem inv3_diag₃ (i : Fin 24) (u v : SpaceB) : Inv3 u v (tbasis (.inl i)) := by
  unfold Inv3
  rw [tbasis_diag]
  exact (T_tauB_of_diagonal (basisA_diag_eq i) u v).2.2

abbrev NIdx : Type := (LtPair × Fin 3) ⊕ (C₀ × Fin 24 × Fin 3) ⊕ OctIdx

@[expose] def nd (x : NIdx) : TIdx := .inr x

theorem pair_mem_VABCD (q : LtPair × Fin 3) : tbasis (.inr (.inl q)) ∈ VABCD :=
  Submodule.subset_span ⟨.inr q, rfl⟩

theorem inv3_PPP (q₁ q₂ q₃ : LtPair × Fin 3) :
    Inv3 (tbasis (.inr (.inl q₁))) (tbasis (.inr (.inl q₂))) (tbasis (.inr (.inl q₃))) :=
  T_tauB_of_mem_VABCD (pair_mem_VABCD q₁) (pair_mem_VABCD q₂) (pair_mem_VABCD q₃)

theorem inv3_OOP (r : Fin 3) (c c' : C₀) (i j : Fin 24) (q : LtPair × Fin 3) :
    Inv3 (tbasis (.inr (.inr (.inl (c, i, r))))) (tbasis (.inr (.inr (.inl (c', j, r)))))
      (tbasis (.inr (.inl q))) :=
  ((triality_Griess_odd_two_coordinate_invariance).1 r (XYZInv.oddVec_mem_oddSpan c i r)
    (XYZInv.oddVec_mem_oddSpan c' j r) (Submodule.subset_span ⟨q, rfl⟩)).1

theorem inv3_XYZ (a b c : C₀) (i j k : Fin 24) :
    Inv3 (tbasis (.inr (.inr (.inl (a, i, 0))))) (tbasis (.inr (.inr (.inl (b, j, 1)))))
      (tbasis (.inr (.inr (.inl (c, k, 2))))) :=
  ((triality_Griess_XYZ_invariance).1 (XYZInv.oddVec_mem_oddSpan a i 0)
    (XYZInv.oddVec_mem_oddSpan b j 1) (XYZInv.oddVec_mem_oddSpan c k 2)).1

theorem inv3_TTP (o o' : OctIdx) (q : LtPair × Fin 3) :
    Inv3 (tbasis (.inr (.inr (.inr o)))) (tbasis (.inr (.inr (.inr o'))))
      (tbasis (.inr (.inl q))) :=
  ((triality_Griess_octad_two_coordinate_invariance).1 _ (Submodule.subset_span ⟨o, rfl⟩) _
    (Submodule.subset_span ⟨o', rfl⟩) _ (Submodule.subset_span ⟨q, rfl⟩)).1

theorem inv3_TTT (o o' o'' : OctIdx) :
    Inv3 (tbasis (.inr (.inr (.inr o)))) (tbasis (.inr (.inr (.inr o'))))
      (tbasis (.inr (.inr (.inr o'')))) :=
  ((triality_Griess_three_octad_invariance).2.2.2 _ (Submodule.subset_span ⟨o, rfl⟩) _
    (Submodule.subset_span ⟨o', rfl⟩) _ (Submodule.subset_span ⟨o'', rfl⟩)).1

theorem inv3_OOT (r : Fin 3) (c c' : C₀) (i j : Fin 24) (o : OctIdx) :
    Inv3 (tbasis (.inr (.inr (.inl (c, i, r))))) (tbasis (.inr (.inr (.inl (c', j, r)))))
      (tbasis (.inr (.inr (.inr o)))) :=
  ((triality_Griess_odd_octad_invariance).1 r _ (Submodule.subset_span ⟨(c, i), rfl⟩) _
    (Submodule.subset_span ⟨(c', j), rfl⟩) _ (Submodule.subset_span ⟨o, rfl⟩)).1.1

theorem oddSlot_ne_zero (k : Fin 3) : oddSlot k ≠ 0 := by
  revert k
  decide

theorem oddSlot_add_ne_zero {k l : Fin 3} (h : k ≠ l) : oddSlot k + oddSlot l ≠ 0 := by
  revert k l
  decide

theorem oddSlot_add3_ne_zero {k l m : Fin 3} (h : ¬ (k ≠ l ∧ l ≠ m ∧ k ≠ m)) :
    oddSlot k + oddSlot l + oddSlot m ≠ 0 := by
  revert k l m
  decide

theorem fst_ne_zero {g : Gam} (h : g.1 ≠ 0) : g ≠ 0 := fun h0 => h (by rw [h0]; rfl)

theorem clsΩ_octad_ne_zero (d : OctadWord) : clsΩ (d : C) ≠ 0 := by
  intro h
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  have hw := d.2
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h01 t with rfl | rfl
  · rw [zero_smul] at ht
    rw [← ht] at hw
    simp at hw
  · rw [one_smul] at ht
    rw [← ht] at hw
    have : hammingNorm ((ΩC : C) : Fin 24 → ZMod 2) = 24 := by
      rw [coe_ΩC]
      decide
    omega

theorem inv3_of_fst {x y z : TIdx}
    (h : (tgrade x).1 + (tgrade y).1 + (tgrade z).1 ≠ 0) :
    Inv3 (tbasis x) (tbasis y) (tbasis z) :=
  inv3_of_grade (fun h0 => h (by
    have := congrArg Prod.fst h0
    simp only [Prod.fst_add] at this
    exact this))

theorem inv3_of_snd {x y z : TIdx}
    (h : (tgrade x).2 + (tgrade y).2 + (tgrade z).2 ≠ 0) :
    Inv3 (tbasis x) (tbasis y) (tbasis z) :=
  inv3_of_grade (fun h0 => h (by
    have := congrArg Prod.snd h0
    simp only [Prod.snd_add] at this
    exact this))

theorem tgrade_pair (q : LtPair × Fin 3) : tgrade (.inr (.inl q)) = 0 := rfl

theorem tgrade_odd (c : C₀) (i : Fin 24) (k : Fin 3) :
    tgrade (.inr (.inr (.inl (c, i, k)))) = (oddSlot k, clsΩ (c : C)) := rfl

theorem tgrade_oct (o : OctIdx) : tgrade (.inr (.inr (.inr o))) = (0, clsΩ (o.1 : C)) := rfl

theorem inv3_OOO (a b c : C₀) (i j k : Fin 24) (k₁ k₂ k₃ : Fin 3) :
    Inv3 (tbasis (.inr (.inr (.inl (a, i, k₁))))) (tbasis (.inr (.inr (.inl (b, j, k₂)))))
      (tbasis (.inr (.inr (.inl (c, k, k₃))))) := by
  by_cases hd : k₁ ≠ k₂ ∧ k₂ ≠ k₃ ∧ k₁ ≠ k₃
  · obtain ⟨h12, h23, h13⟩ := hd
    fin_cases k₁ <;> fin_cases k₂ <;> fin_cases k₃ <;> simp at h12 h23 h13
    · exact inv3_XYZ a b c i j k
    · exact (inv3_XYZ a c b i k j).swap23
    · exact (inv3_XYZ b a c j i k).swap12
    · exact ((inv3_XYZ c a b k i j).swap12).swap23
    · exact ((inv3_XYZ b c a j k i).swap23).swap12
    · exact (((inv3_XYZ c b a k j i).swap12).swap23).swap12
  · refine inv3_of_fst ?_
    rw [tgrade_odd, tgrade_odd, tgrade_odd]
    exact oddSlot_add3_ne_zero hd

theorem inv3_nd (x y z : NIdx) : Inv3 (tbasis (nd x)) (tbasis (nd y)) (tbasis (nd z)) := by
  rcases x with q₁ | ⟨c₁, i₁, k₁⟩ | o₁ <;> rcases y with q₂ | ⟨c₂, i₂, k₂⟩ | o₂ <;>
    rcases z with q₃ | ⟨c₃, i₃, k₃⟩ | o₃ <;> simp only [nd]
  · exact inv3_PPP q₁ q₂ q₃
  · exact inv3_of_fst (by rw [tgrade_pair, tgrade_pair, tgrade_odd]; simpa using oddSlot_ne_zero k₃)
  · exact inv3_of_snd (by
      rw [tgrade_pair, tgrade_pair, tgrade_oct]; simpa using ProdInv.clsΩ_octad_ne_zero o₃.1)
  · exact inv3_of_fst (by rw [tgrade_pair, tgrade_odd, tgrade_pair]; simpa using oddSlot_ne_zero k₂)
  · by_cases h : k₂ = k₃
    · subst h
      exact ((inv3_OOP k₂ c₂ c₃ i₂ i₃ q₁).swap23).swap12
    · exact inv3_of_fst (by
        rw [tgrade_pair, tgrade_odd, tgrade_odd]; simpa using oddSlot_add_ne_zero h)
  · exact inv3_of_fst (by rw [tgrade_pair, tgrade_odd, tgrade_oct]; simpa using oddSlot_ne_zero k₂)
  · exact inv3_of_snd (by
      rw [tgrade_pair, tgrade_oct, tgrade_pair]; simpa using ProdInv.clsΩ_octad_ne_zero o₂.1)
  · exact inv3_of_fst (by rw [tgrade_pair, tgrade_oct, tgrade_odd]; simpa using oddSlot_ne_zero k₃)
  · exact ((inv3_TTP o₂ o₃ q₁).swap23).swap12
  · exact inv3_of_fst (by rw [tgrade_odd, tgrade_pair, tgrade_pair]; simpa using oddSlot_ne_zero k₁)
  · by_cases h : k₁ = k₃
    · subst h
      exact (inv3_OOP k₁ c₁ c₃ i₁ i₃ q₂).swap23
    · exact inv3_of_fst (by
        rw [tgrade_odd, tgrade_pair, tgrade_odd]; simpa using oddSlot_add_ne_zero h)
  · exact inv3_of_fst (by rw [tgrade_odd, tgrade_pair, tgrade_oct]; simpa using oddSlot_ne_zero k₁)
  · by_cases h : k₁ = k₂
    · subst h
      exact inv3_OOP k₁ c₁ c₂ i₁ i₂ q₃
    · exact inv3_of_fst (by
        rw [tgrade_odd, tgrade_odd, tgrade_pair]; simpa using oddSlot_add_ne_zero h)
  · exact inv3_OOO c₁ c₂ c₃ i₁ i₂ i₃ k₁ k₂ k₃
  · by_cases h : k₁ = k₂
    · subst h
      exact inv3_OOT k₁ c₁ c₂ i₁ i₂ o₃
    · exact inv3_of_fst (by
        rw [tgrade_odd, tgrade_odd, tgrade_oct]; simpa using oddSlot_add_ne_zero h)
  · exact inv3_of_fst (by rw [tgrade_odd, tgrade_oct, tgrade_pair]; simpa using oddSlot_ne_zero k₁)
  · by_cases h : k₁ = k₃
    · subst h
      exact (inv3_OOT k₁ c₁ c₃ i₁ i₃ o₂).swap23
    · exact inv3_of_fst (by
        rw [tgrade_odd, tgrade_oct, tgrade_odd]; simpa using oddSlot_add_ne_zero h)
  · exact inv3_of_fst (by rw [tgrade_odd, tgrade_oct, tgrade_oct]; simpa using oddSlot_ne_zero k₁)
  · exact inv3_of_snd (by
      rw [tgrade_oct, tgrade_pair, tgrade_pair]; simpa using ProdInv.clsΩ_octad_ne_zero o₁.1)
  · exact inv3_of_fst (by rw [tgrade_oct, tgrade_pair, tgrade_odd]; simpa using oddSlot_ne_zero k₃)
  · exact (inv3_TTP o₁ o₃ q₂).swap23
  · exact inv3_of_fst (by rw [tgrade_oct, tgrade_odd, tgrade_pair]; simpa using oddSlot_ne_zero k₂)
  · by_cases h : k₂ = k₃
    · subst h
      exact ((inv3_OOT k₂ c₂ c₃ i₂ i₃ o₁).swap23).swap12
    · exact inv3_of_fst (by
        rw [tgrade_oct, tgrade_odd, tgrade_odd]; simpa using oddSlot_add_ne_zero h)
  · exact inv3_of_fst (by rw [tgrade_oct, tgrade_odd, tgrade_oct]; simpa using oddSlot_ne_zero k₂)
  · exact inv3_TTP o₁ o₂ q₃
  · exact inv3_of_fst (by rw [tgrade_oct, tgrade_oct, tgrade_odd]; simpa using oddSlot_ne_zero k₃)
  · exact inv3_TTT o₁ o₂ o₃

theorem inv3_basis (x y z : TIdx) : Inv3 (tbasis x) (tbasis y) (tbasis z) := by
  rcases x with i | x
  · exact inv3_diag₁ i _ _
  rcases y with j | y
  · exact inv3_diag₂ j _ _
  rcases z with k | z
  · exact inv3_diag₃ k _ _
  exact inv3_nd x y z

end ProdInv

open ProdInv in
@[expose] noncomputable def tauT : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ :=
  (T.compl₁₂ (tauB : SpaceB →ₗ[ℚ] SpaceB) (tauB : SpaceB →ₗ[ℚ] SpaceB)).compr₂
    (LinearMap.lcomp ℚ ℚ (tauB : SpaceB →ₗ[ℚ] SpaceB))

theorem tauT_apply (u v w : SpaceB) : tauT u v w = T (tauB u) (tauB v) (tauB w) := rfl

theorem T_tauB (u v w : SpaceB) : T (tauB u) (tauB v) (tauB w) = T u v w := by
  have h : tauT = T := tbasis.ext fun i => tbasis.ext fun j => tbasis.ext fun k =>
    ProdInv.inv3_basis i j k
  exact congrArg (fun f => f u v w) h

theorem T_tauB_symm (u v w : SpaceB) :
    T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  rw [← T_tauB (tauB.symm u), tauB.apply_symm_apply, tauB.apply_symm_apply,
    tauB.apply_symm_apply]

theorem tauB_gmul (u v : SpaceB) : tauB (gmul u v) = gmul (tauB u) (tauB v) := by
  refine eq_of_bform_eq fun w => ?_
  calc bform (tauB (gmul u v)) w = bform (tauB (gmul u v)) (tauB (tauB.symm w)) := by
        rw [tauB.apply_symm_apply]
    _ = bform (gmul u v) (tauB.symm w) := bform_tauB _ _
    _ = T u v (tauB.symm w) := bform_gmul _ _ _
    _ = T (tauB u) (tauB v) (tauB (tauB.symm w)) := (T_tauB u v _).symm
    _ = T (tauB u) (tauB v) w := by rw [tauB.apply_symm_apply]
    _ = bform (gmul (tauB u) (tauB v)) w := (bform_gmul _ _ _).symm

@[expose] def IsAlgAut (f : SpaceB ≃ₗ[ℚ] SpaceB) : Prop := ∀ u v, f (gmul u v) = gmul (f u) (f v)

theorem isAlgAut_one : IsAlgAut 1 := fun _ _ => rfl

theorem IsAlgAut.mul {f g : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsAlgAut f) (hg : IsAlgAut g) :
    IsAlgAut (f * g) := fun u v => by
  change f (g (gmul u v)) = gmul (f (g u)) (f (g v))
  rw [hg, hf]

theorem IsAlgAut.inv {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsAlgAut f) : IsAlgAut f⁻¹ := fun u v => by
  change f.symm (gmul u v) = gmul (f.symm u) (f.symm v)
  apply f.injective
  rw [f.apply_symm_apply, hf, f.apply_symm_apply, f.apply_symm_apply]

theorem isAlgAut_tauB : IsAlgAut tauB := tauB_gmul

theorem isAlgAut_xB : IsAlgAut xB := xB_gmul

theorem tauB_oneB : tauB oneB = oneB := by
  have h : ((quarterI : symMat) : Matrix (Fin 24) (Fin 24) ℚ) = diagonal fun _ => (4 : ℚ)⁻¹ := by
    change (4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) = _
    ext i j
    simp [Matrix.one_apply, diagonal_apply]
  exact tauB_inA_of_diagonal h

theorem rational_triality_product_invariance :
    (∀ u v w : SpaceB, T (tauB u) (tauB v) (tauB w) = T u v w) ∧
    (∀ u v w : SpaceB, T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) ∧
    (∀ u v : SpaceB, tauB (gmul u v) = gmul (tauB u) (tauB v)) ∧
    (∀ u v : SpaceB, bform (tauB u) (tauB v) = bform u v) ∧
    orderOf tauB = 3 ∧
    BR.map ((tauB : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR ∧
    tauB oneB = oneB ∧
    (∀ g ∈ fourGroupB, ∀ u v : SpaceB, g (gmul u v) = gmul (g u) (g v)) := by
  refine ⟨T_tauB, T_tauB_symm, tauB_gmul, bform_tauB, orderOf_tauB, map_tauB_BR, tauB_oneB, ?_⟩
  intro g hg
  rcases (rational_triality_four_group.2.2.2.2.2.1 g).1 hg with rfl | rfl | rfl | rfl
  · exact isAlgAut_one
  · exact isAlgAut_xB
  · exact (isAlgAut_tauB.mul isAlgAut_xB).mul isAlgAut_tauB.inv
  · have h2 : IsAlgAut (tauB ^ 2) := by rw [pow_two]; exact isAlgAut_tauB.mul isAlgAut_tauB
    exact (h2.mul isAlgAut_xB).mul h2.inv

end CFSG.Monster.Griess
