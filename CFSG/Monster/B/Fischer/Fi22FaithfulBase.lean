
module

public import CFSG.Monster.B.Fischer.Fi22FormsSpec
public import CFSG.Sporadic.Fi22.Setup
public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckInputs

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.F3.Native CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  Matrix CFSG.Certificates CFSG.Sporadic.Fi22

attribute [local irreducible] fi22Quad

theorem fi22FormCoeff_lt (r k : ℕ) : fi22FormCoeff r k < 3 := Nat.mod_lt _ (by norm_num)

theorem nat_any_iff {n : ℕ} {p : ℕ → Bool} :
    (Nat.any n fun i _ => p i) = true ↔ ∃ i < n, p i = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  constructor
  · rintro ⟨⟨i, hi⟩, -, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

theorem fi22Form_eq (r : ℕ) : fi22Form r = fi22Quad (trit fi22FormsBytes (752 * r)) := rfl

theorem fi22InvForm_eq : fi22InvForm = fi22Quad (trit fi22InvFormBytes 0) := rfl

noncomputable def fi22SeedGL
    (k : ℕ) : GL (Fin 77) (ZMod 3) := if k = 0 then gA else gB

theorem fi22SeedGL_val (k : ℕ) :
    ((fi22SeedGL k : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) =
      if k = 0 then mA else mB := by
  unfold fi22SeedGL
  split_ifs <;> rfl

theorem seedGL_mulVec_inv (k : ℕ) (v : Fi22V) :
    ((fi22SeedGL k : Matrix (Fin 77) (Fin 77) (ZMod 3))) *ᵥ
      (((fi22SeedGL k)⁻¹ : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) *ᵥ v = v := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem fi22B_eq : fi22B = toMat 77 (polarRows fi22InvFormBytes 0) := by
  rw [fi22B, fi22InvForm, polarMatrix_fi22Quad, toMat_polarRows]
  rfl

noncomputable def fi22T (r : ℕ) : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  fi22B⁻¹ * polarMatrix (fi22Form r)

theorem fi22CentralizerIdx_length : fi22CentralizerIdx.length = 6 := rfl

theorem fi22SepMats_size : fi22SepMats.size = 6 := by
  rw [fi22SepMats, Array.size_map, List.size_toArray, fi22CentralizerIdx_length]

theorem getElem!_map_toArray {l : List ℕ} {f : ℕ → Array V} {i : ℕ} (hi : i < l.length) :
    (l.toArray.map f)[i]! = f l[i]! := by
  rw [getElem!_pos _ i (by rw [Array.size_map, List.size_toArray]; exact hi), Array.getElem_map,
    List.getElem_toArray, getElem!_pos l i hi]

noncomputable def fi22CommMap :
    Matrix (Fin 77) (Fin 77) (ZMod 3) →ₗ[ZMod 3] (Fin 6 → Matrix (Fin 77) (Fin 77) (ZMod 3)) where
  toFun M t := M * fi22T (fi22CentralizerIdx.getD t 0) - fi22T (fi22CentralizerIdx.getD t 0) * M
  map_add' M N := by
    funext t
    simp only [Pi.add_apply, add_mul, mul_add]
    abel
  map_smul' c M := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, Matrix.smul_mul, Matrix.mul_smul]

abbrev Fi22GL : Type := LinearMap.GeneralLinearGroup (ZMod 3) Fi22V

noncomputable def fi22SeedLin (k : Fin 2) : Fi22GL :=
  Matrix.GeneralLinearGroup.toLin (fi22SeedGL k)

noncomputable def fi22G :
    Subgroup Fi22GL := Subgroup.closure (Set.range fi22SeedLin)

noncomputable def fi22Bil : LinearMap.BilinForm (ZMod 3) Fi22V := Matrix.toBilin' fi22B

noncomputable def fi22Beta (q : Fi22V → ZMod 3) : LinearMap.BilinForm (ZMod 3) Fi22V :=
  Matrix.toBilin' (polarMatrix q)

def fi22S : Set (Fi22V → ZMod 3) := {q | ∃ r ∈ fi22CentralizerIdx, fi22Form r = q}

noncomputable def fi22TLin (q : Fi22V → ZMod 3) : Module.End (ZMod 3) Fi22V :=
  Matrix.toLin' (fi22B⁻¹ * polarMatrix q)

theorem fi22X_finite : fi22X.Finite := by
  have : fi22X = fi22Form '' {r | r < 3510} := by
    ext q
    simp only [fi22X, Set.mem_ofPred_eq, Set.mem_image]
  rw [this]
  exact (Set.finite_lt_nat 3510).image _

theorem fi22Beta_apply {q : Fi22V → ZMod 3} (hq : q ∈ fi22X) (u w : Fi22V) :
    fi22Beta q u w = q (u + w) - q u - q w := by
  obtain ⟨r, -, rfl⟩ := hq
  rw [fi22Beta, Matrix.toBilin'_apply', fi22Form, fi22Quad_polar]

theorem fi22SeedLin_apply (k : Fin 2) (v : Fi22V) :
    (fi22SeedLin k : Fi22V →ₗ[ZMod 3] Fi22V) v = (fi22SeedGL k : Matrix _ _ (ZMod 3)) *ᵥ v :=
  Matrix.GeneralLinearGroup.toLin_apply _ v

theorem fi22SeedLin_inv_apply (k : Fin 2) (v : Fi22V) :
    (((fi22SeedLin k)⁻¹ : Fi22GL) : Fi22V →ₗ[ZMod 3] Fi22V) v =
      (((fi22SeedGL k)⁻¹ : GL (Fin 77) (ZMod 3)) : Matrix _ _ (ZMod 3)) *ᵥ v := by
  rw [fi22SeedLin, ← map_inv]
  exact Matrix.GeneralLinearGroup.toLin_apply _ v

theorem det_fi22SeedLin (k : Fin 2) :
    LinearMap.det (fi22SeedLin k : Fi22V →ₗ[ZMod 3] Fi22V) = 1 := by
  rw [fi22SeedLin, Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply',
    LinearMap.det_toLin', fi22SeedGL_val]
  split_ifs
  · exact det_mA matrixFacts
  · exact det_mB matrixFacts

theorem fi22Bil_apply (u w : Fi22V) :
    fi22Bil u w = fi22InvForm (u + w) - fi22InvForm u - fi22InvForm w := by
  rw [fi22Bil, Matrix.toBilin'_apply', fi22B, fi22InvForm, fi22Quad_polar]

theorem fi22S_subset : fi22S ⊆ fi22X := by
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨r, ?_, rfl⟩
  simp only [fi22CentralizerIdx, List.mem_cons, List.mem_nil_iff, or_false] at hr
  omega

theorem fi22_hroot : ∀ c : ZMod 3, c ^ Module.finrank (ZMod 3) Fi22V = 1 → c = 1 := by
  rw [Module.finrank_fin_fun]
  decide

theorem fi22P_eq : fi22P = Subgroup.closure (Set.range fun k : Fin 2 => fi22GenPerm k) := by
  rw [fi22P, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  change g ∈ (Vector.ofFn fun k : Fin 2 => fi22GenPerm k).toList ↔ _
  rw [Vector.toList_ofFn, List.mem_ofFn, Set.mem_range]

noncomputable def fi22ToLin : GL (Fin 77) (ZMod 3) →* Fi22GL :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem fi22ToLin_apply (g : GL (Fin 77) (ZMod 3)) :
    fi22ToLin g = Matrix.GeneralLinearGroup.toLin g := rfl

theorem fi22ToLin_injective : Function.Injective fi22ToLin :=
  Matrix.GeneralLinearGroup.toLin.injective

theorem fi22SeedLin_eq
    (k : Fin 2) : fi22SeedLin k = fi22ToLin (fi22SeedGL k) := rfl

theorem fi22SeedGL_mem
    (k : ℕ) : fi22SeedGL k ∈ CFSG.Sporadic.Fi22.J := by
  unfold fi22SeedGL
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem fi22ToLin_mem
    (g : CFSG.Sporadic.Fi22.J) : fi22ToLin g ∈ fi22G := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure ⟨0, by rw [fi22SeedLin_eq]; rfl⟩
    · exact Subgroup.subset_closure ⟨1, by rw [fi22SeedLin_eq]; rfl⟩
  | one => rw [map_one]; exact fi22G.one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact fi22G.mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact fi22G.inv_mem hx

noncomputable def fi22JHom :
    CFSG.Sporadic.Fi22.J →* fi22G :=
  (fi22ToLin.comp CFSG.Sporadic.Fi22.J.subtype).codRestrict fi22G fi22ToLin_mem

theorem fi22JHom_val (g : CFSG.Sporadic.Fi22.J) :
    ((fi22JHom g : fi22G) : Fi22GL) = fi22ToLin (g : GL (Fin 77) (ZMod 3)) := rfl

theorem fi22JHom_bijective : Function.Bijective fi22JHom := by
  refine ⟨fun g h e => ?_, ?_⟩
  · have e' := congrArg Subtype.val e
    rw [fi22JHom_val, fi22JHom_val] at e'
    exact Subtype.ext (fi22ToLin_injective e')
  rintro ⟨h, hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨⟨fi22SeedGL k, fi22SeedGL_mem k⟩, Subtype.ext (fi22SeedLin_eq k).symm⟩
  | one => exact ⟨1, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a⁻¹, by rw [map_inv, ha]; rfl⟩

noncomputable def fi22JEquivG :
    CFSG.Sporadic.Fi22.J ≃* fi22G :=
  MulEquiv.ofBijective fi22JHom fi22JHom_bijective

theorem fi22JEquivG_val (g : CFSG.Sporadic.Fi22.J) :
    ((fi22JEquivG g : fi22G) : Fi22GL) = fi22ToLin (g : GL (Fin 77) (ZMod 3)) := rfl

noncomputable def fi22MatEquiv :
    Blueprint.NativeSporadic.Fi22 ≃* CFSG.Sporadic.Fi22.J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 77 (by norm_num) mA mB (det_mA_ne_zero matrixFacts)
    (det_mB_ne_zero matrixFacts)

theorem fi22MatEquiv_val (u : Blueprint.NativeSporadic.Fi22) :
    (((fi22MatEquiv u : CFSG.Sporadic.Fi22.J) : GL (Fin 77) (ZMod 3)) :
      Matrix (Fin 77) (Fin 77) (ZMod 3)) = u.val.val :=
  Blueprint.NativeSporadic.matrixSeedEquiv_val 3 77 _ mA mB _ _ u

noncomputable def fi22EquivG :
    Blueprint.NativeSporadic.Fi22 ≃* fi22G :=
  fi22MatEquiv.trans fi22JEquivG

theorem fi22EquivG_apply (u : Blueprint.NativeSporadic.Fi22) :
    fi22EquivG u = fi22JEquivG (fi22MatEquiv u) := rfl

noncomputable def fi22SeedA :
    Blueprint.NativeSporadic.Fi22 := fi22MatEquiv.symm a

noncomputable def fi22SeedB :
    Blueprint.NativeSporadic.Fi22 := fi22MatEquiv.symm b

theorem fi22SeedA_val : fi22SeedA.val.val = mA := by
  rw [← fi22MatEquiv_val, fi22SeedA, MulEquiv.apply_symm_apply]
  rfl

theorem fi22SeedB_val : fi22SeedB.val.val = mB := by
  rw [← fi22MatEquiv_val, fi22SeedB, MulEquiv.apply_symm_apply]
  rfl

theorem fi22SeedGL_zero :
    fi22SeedGL ((0 : Fin 2) : ℕ) = gA := ite_eq_left rfl

theorem fi22SeedGL_one :
    fi22SeedGL ((1 : Fin 2) : ℕ) = gB := ite_eq_right one_ne_zero

theorem fi22JEquivG_a :
    ((fi22JEquivG a : fi22G) : Fi22GL) = fi22ToLin gA := by
  rw [fi22JEquivG_val]
  rfl

theorem fi22JEquivG_b :
    ((fi22JEquivG b : fi22G) : Fi22GL) = fi22ToLin gB := by
  rw [fi22JEquivG_val]
  rfl

theorem fi22EquivG_seedA :
    fi22EquivG fi22SeedA = ⟨fi22SeedLin 0, Subgroup.subset_closure ⟨0, rfl⟩⟩ := by
  apply Subtype.ext
  show ((fi22EquivG fi22SeedA : fi22G) : Fi22GL) = fi22SeedLin 0
  rw [fi22EquivG_apply, fi22SeedA, MulEquiv.apply_symm_apply, fi22JEquivG_a, fi22SeedLin_eq,
    fi22SeedGL_zero]

theorem fi22EquivG_seedB :
    fi22EquivG fi22SeedB = ⟨fi22SeedLin 1, Subgroup.subset_closure ⟨1, rfl⟩⟩ := by
  apply Subtype.ext
  show ((fi22EquivG fi22SeedB : fi22G) : Fi22GL) = fi22SeedLin 1
  rw [fi22EquivG_apply, fi22SeedB, MulEquiv.apply_symm_apply, fi22JEquivG_b, fi22SeedLin_eq,
    fi22SeedGL_one]

end CFSG.Monster.B.Fischer
