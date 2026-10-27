module

public import CFSG.RankThree.PartOne.KF4.B2Native

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

section PosRoots

@[expose] def f4B2PosRoot : Fin 4 → Fin Tag.F4.rank → ℤ :=
  (![![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 2, 0]] : Fin 4 → Fin 4 → ℤ)

theorem f4B2PosRoot_injective : Function.Injective f4B2PosRoot := by
  intro k k' h
  revert k k'
  decide +kernel

theorem f4B2PosRoot_dec : ∀ m : Fin 4, f4IsRootB (f4B2PosRoot m) = true ∧
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 1 ∨ i = f4Index 2) → f4B2PosRoot m i = 0) ∧
    0 < height (f4B2PosRoot m) := by
  decide +kernel

theorem f4B2PosRoot_neg_dec : ∀ m : Fin 4, f4IsRootB (-f4B2PosRoot m) = true := by
  decide +kernel

theorem exists_f4B2PosRoot_of_support : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, ¬(i = f4Index 1 ∨ i = f4Index 2) → f4RootVec m i = 0) →
      0 < height (f4RootVec m) → ∃ k, f4B2PosRoot k = f4RootVec m := by
  decide +kernel

theorem f4B2_reflect :
    reflect Tag.F4 (f4Index 1) (Pi.single (f4Index 2) 1) = f4B2PosRoot 2 ∧
    reflect Tag.F4 (f4Index 1) (-Pi.single (f4Index 2) 1) = -f4B2PosRoot 2 ∧
    reflect Tag.F4 (f4Index 2) (Pi.single (f4Index 1) 1) = f4B2PosRoot 3 ∧
    reflect Tag.F4 (f4Index 2) (-Pi.single (f4Index 1) 1) = -f4B2PosRoot 3 := by
  decide +kernel

theorem f4B2PosRoot_zero : f4B2PosRoot 0 = Pi.single (f4Index 2) 1 := by decide +kernel

theorem f4B2PosRoot_one : f4B2PosRoot 1 = Pi.single (f4Index 1) 1 := by decide +kernel

theorem f4B2PosRoot_mem_parabolicRoots (m : Fin 4) :
    f4B2PosRoot m ∈ parabolicRoots Tag.F4 f4B2Support := by
  obtain ⟨h1, h2, -⟩ := f4B2PosRoot_dec m
  exact ⟨isRoot_iff_f4IsRootB.2 h1, fun i hi => h2 i (by rwa [← mem_f4B2Support])⟩

theorem neg_f4B2PosRoot_mem_parabolicRoots (m : Fin 4) :
    -f4B2PosRoot m ∈ parabolicRoots Tag.F4 f4B2Support := by
  obtain ⟨h1, h2, -⟩ := f4B2PosRoot_dec m
  exact ⟨isRoot_iff_f4IsRootB.2 (f4B2PosRoot_neg_dec m), fun i hi => by
    rw [Pi.neg_apply, h2 i (by rwa [← mem_f4B2Support]), neg_zero]⟩

theorem range_f4B2PosRoot : Set.range f4B2PosRoot = parabolicPosRoots Tag.F4 f4B2Support := by
  ext β
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨h1, h2, h3⟩ := f4B2PosRoot_dec m
    have hr : IsRoot Tag.F4 (f4B2PosRoot m) := isRoot_iff_f4IsRootB.2 h1
    exact ⟨⟨hr, fun i hi => h2 i (by rwa [← mem_f4B2Support])⟩, hr, h3⟩
  · rintro ⟨⟨hβ, hout⟩, -, hpos⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hβ
    exact exists_f4B2PosRoot_of_support m
      (fun i hi => hout i (fun h => hi ((mem_f4B2Support i).1 h))) hpos

end PosRoots

section Mats

variable {K : Type} [Field K]

theorem f4B2_smul_single (t : K) (i j : Fin 4) :
    t • (single i j (1 : K) : Matrix (Fin 4) (Fin 4) K) = single i j t := by
  ext a b
  simp [Matrix.single_apply]

@[expose] def f4B2Na : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1]

@[expose] def f4B2NaInv : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def f4B2Nb : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

@[expose] def f4B2NbInv : Matrix (Fin 4) (Fin 4) K :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

theorem f4B2Na_mul_inv : (f4B2Na : Matrix (Fin 4) (Fin 4) K) * f4B2NaInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f4B2Na, f4B2NaInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem f4B2Nb_mul_inv : (f4B2Nb : Matrix (Fin 4) (Fin 4) K) * f4B2NbInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f4B2Nb, f4B2NbInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem f4B2Na_conj_x3 :
    (f4B2Na : Matrix (Fin 4) (Fin 4) K) * (single 0 1 1 + single 2 3 1) * f4B2NaInv =
      single 1 3 1 - single 0 2 1 := by
  rw [Matrix.mul_assoc]
  ext a b
  simp only [f4B2Na, f4B2NaInv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem f4B2Nb_conj_x2 :
    (f4B2Nb : Matrix (Fin 4) (Fin 4) K) * single 1 2 1 * f4B2NbInv = -single 0 3 1 := by
  rw [Matrix.mul_assoc]
  ext a b
  simp only [f4B2Nb, f4B2NbInv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
    Matrix.neg_apply, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem f4B2Nb_conj_y2 :
    (f4B2Nb : Matrix (Fin 4) (Fin 4) K) * single 2 1 1 * f4B2NbInv = -single 3 0 1 := by
  rw [Matrix.mul_assoc]
  ext a b
  simp only [f4B2Nb, f4B2NbInv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
    Matrix.neg_apply, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp

end Mats

section Families

variable
  {K : Type} [Field K]

theorem pinnedX_mem_f4B2 {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.F4 f4B2Support) (t : K) :
    pinnedX Tag.F4 K α t ∈ subsystemGroup Tag.F4 K f4B2Support :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def F4B2RootFamily (α : Fin Tag.F4.rank → ℤ) (X : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∃ ε : Kˣ, ∀ t : K, f4B2_data.Mat (pinnedX Tag.F4 K α t) = 1 + ((ε : K) * t) • X

theorem f4B2_weylElt_eq (i : Fin Tag.F4.rank) :
    weylElt Tag.F4 K i 1 =
      xUnit Tag.F4 K i 1 * yUnit Tag.F4 K i (-1) * xUnit Tag.F4 K i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem f4B2_Mat_na :
    f4B2_data.Mat (weylElt Tag.F4 K (f4Index 1) 1) = f4B2Na := by
  have hx := xUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inl rfl)) 1
  have hy := yUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inl rfl)) (-1)
  rw [f4B2_weylElt_eq, f4B2_data.Mat_mul (mul_mem hx hy) hx, f4B2_data.Mat_mul hx hy,
    f4B2_Mat_x2, f4B2_Mat_y2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [f4B2Na, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply]

theorem f4B2_Mat_nb :
    f4B2_data.Mat (weylElt Tag.F4 K (f4Index 2) 1) = f4B2Nb := by
  have hx := xUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inr rfl)) 1
  have hy := yUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4B2Support _).2
    (Or.inr rfl)) (-1)
  rw [f4B2_weylElt_eq, f4B2_data.Mat_mul (mul_mem hx hy) hx, f4B2_data.Mat_mul hx hy,
    f4B2_Mat_x3, f4B2_Mat_y3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [f4B2Nb, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply]

theorem f4B2_Mat_na_inv :
    f4B2_data.Mat (weylElt Tag.F4 K (f4Index 1) 1)⁻¹ = f4B2NaInv := by
  have hn : weylElt Tag.F4 K (f4Index 1) 1 ∈ subsystemGroup Tag.F4 K f4B2Support :=
    weylElt_mem_subsystemGroup ((mem_f4B2Support _).2 (Or.inl rfl)) 1
  rw [f4B2_data.Mat_inv hn, f4B2_Mat_na]
  exact Matrix.inv_eq_right_inv f4B2Na_mul_inv

theorem f4B2_Mat_nb_inv :
    f4B2_data.Mat (weylElt Tag.F4 K (f4Index 2) 1)⁻¹ = f4B2NbInv := by
  have hn : weylElt Tag.F4 K (f4Index 2) 1 ∈ subsystemGroup Tag.F4 K f4B2Support :=
    weylElt_mem_subsystemGroup ((mem_f4B2Support _).2 (Or.inr rfl)) 1
  rw [f4B2_data.Mat_inv hn, f4B2_Mat_nb]
  exact Matrix.inv_eq_right_inv f4B2Nb_mul_inv

theorem f4B2RootFamily_of_eq {α : Fin Tag.F4.rank → ℤ} {X : Matrix (Fin 4) (Fin 4) K}
    {g : K → ModGL Tag.F4 K} (hg : ∀ t, pinnedX Tag.F4 K α t = g t)
    (h : ∀ t, f4B2_data.Mat (g t) = 1 + t • X) : F4B2RootFamily K α X :=
  ⟨1, fun t => by rw [hg, h, Units.val_one, one_mul]⟩

theorem f4B2RootFamily_transport {i : Fin Tag.F4.rank} (hi : i ∈ f4B2Support)
    {α β : Fin Tag.F4.rank → ℤ} (hα : α ∈ parabolicRoots Tag.F4 f4B2Support)
    (hβ : reflect Tag.F4 i α = β) {X Y N Ninv : Matrix (Fin 4) (Fin 4) K}
    (hN : f4B2_data.Mat (weylElt Tag.F4 K i 1) = N)
    (hNinv : f4B2_data.Mat (weylElt Tag.F4 K i 1)⁻¹ = Ninv) (hNN : N * Ninv = 1)
    (hY : N * X * Ninv = Y) (hfam : F4B2RootFamily K α X) : F4B2RootFamily K β Y := by
  obtain ⟨ε, hε⟩ := hfam
  obtain ⟨ε₀, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hα.1
  rw [hβ] at h
  have hn : weylElt Tag.F4 K i 1 ∈ subsystemGroup Tag.F4 K f4B2Support :=
    weylElt_mem_subsystemGroup hi 1
  refine ⟨Units.mkOfMulEqOne ε₀ ε₀ hεε * ε, fun t => ?_⟩
  have e : pinnedX Tag.F4 K β t =
      weylElt Tag.F4 K i 1 * pinnedX Tag.F4 K α (ε₀ * t) * (weylElt Tag.F4 K i 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := pinnedX_mem_f4B2 hα (ε₀ * t)
  rw [e, f4B2_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4B2_data.Mat_mul hn hX, hN, hNinv, hε,
    ← hY]
  have e1 : (N * (1 + ((ε : K) * (ε₀ * t)) • X) * Ninv : Matrix (Fin 4) (Fin 4) K) =
      1 + ((ε : K) * (ε₀ * t)) • (N * X * Ninv) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hNN, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  rw [e1]
  congr 2
  simp only [Units.val_mul, Units.val_mkOfMulEqOne]
  ring

theorem f4B2Family_0 : F4B2RootFamily K (f4B2PosRoot 0) (single 0 1 1 + single 2 3 1) :=
  f4B2RootFamily_of_eq (fun t => by rw [f4B2PosRoot_zero, pinnedX_single])
    (fun t => by
      rw [f4B2_Mat_x3, smul_add, f4B2_smul_single, f4B2_smul_single])

theorem f4B2Family_1 : F4B2RootFamily K (f4B2PosRoot 1) (single 1 2 1) :=
  f4B2RootFamily_of_eq (fun t => by rw [f4B2PosRoot_one, pinnedX_single])
    (fun t => by rw [f4B2_Mat_x2, f4B2_smul_single])

theorem f4B2Family_2 :
    F4B2RootFamily K (f4B2PosRoot 2) (single 1 3 1 - single 0 2 1) :=
  f4B2RootFamily_transport ((mem_f4B2Support _).2 (Or.inl rfl)) (f4B2PosRoot_mem_parabolicRoots 0)
    (by rw [f4B2PosRoot_zero]; exact f4B2_reflect.1) f4B2_Mat_na f4B2_Mat_na_inv f4B2Na_mul_inv
    f4B2Na_conj_x3 f4B2Family_0

theorem f4B2Family_3 : F4B2RootFamily K (f4B2PosRoot 3) (-single 0 3 1) :=
  f4B2RootFamily_transport ((mem_f4B2Support _).2 (Or.inr rfl)) (f4B2PosRoot_mem_parabolicRoots 1)
    (by rw [f4B2PosRoot_one]; exact f4B2_reflect.2.2.1) f4B2_Mat_nb f4B2_Mat_nb_inv
    f4B2Nb_mul_inv f4B2Nb_conj_x2 f4B2Family_1

theorem f4B2Family_neg_1 : F4B2RootFamily K (-f4B2PosRoot 1) (single 2 1 1) :=
  f4B2RootFamily_of_eq (fun t => by rw [f4B2PosRoot_one, pinnedX_neg_single])
    (fun t => by rw [f4B2_Mat_y2, f4B2_smul_single])

theorem f4B2Family_neg_3 : F4B2RootFamily K (-f4B2PosRoot 3) (-single 3 0 1) :=
  f4B2RootFamily_transport ((mem_f4B2Support _).2 (Or.inr rfl))
    (neg_f4B2PosRoot_mem_parabolicRoots 1)
    (by rw [f4B2PosRoot_one]; exact f4B2_reflect.2.2.2) f4B2_Mat_nb f4B2_Mat_nb_inv
    f4B2Nb_mul_inv f4B2Nb_conj_y2 f4B2Family_neg_1

theorem mem_subsystemTorus_f4B2 {g : ModGL Tag.F4 K} :
    g ∈ subsystemTorus Tag.F4 K f4B2Support ↔
      ∃ a b : Kˣ, g = torus2Elt (f4Index 1) (f4Index 2) a b :=
  mem_subsystemTorus_pair (f4Index 1) (f4Index 2)

theorem prod_ofFn_four {M : Type*} [Monoid M] (f : Fin 4 → M) :
    (List.ofFn f).prod = f 0 * (f 1 * (f 2 * f 3)) := by
  simp [List.ofFn_succ]

theorem f4B2_prod_pos (y : Fin 4 → K) :
    (1 + y 0 • (single 0 1 1 + single 2 3 1) : Matrix (Fin 4) (Fin 4) K) *
        (1 + y 1 • single 1 2 1) * (1 + y 2 • (single 1 3 1 - single 0 2 1)) *
          (1 + y 3 • -single 0 3 1) =
      !![1, y 0, y 0 * y 1 - y 2, y 0 * y 2 - y 3; 0, 1, y 1, y 2; 0, 0, 1, y 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply] <;> ring

theorem f4B2_eq_one_of_Mat_mul_eq_one {t u : ModGL Tag.F4 K}
    (ht : t ∈ subsystemTorus Tag.F4 K f4B2Support)
    (hu : u ∈ parabolicLeviUnipotent Tag.F4 K f4B2Support) (h : f4B2_data.Mat (t * u) = 1) :
    t = 1 ∧ u = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_f4B2.1 ht
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) f4B2PosRoot
    f4B2PosRoot_injective range_f4B2PosRoot).surjOn hu
  obtain ⟨ε0, h0⟩ := f4B2Family_0 (K := K)
  obtain ⟨ε1, h1⟩ := f4B2Family_1 (K := K)
  obtain ⟨ε2, h2⟩ := f4B2Family_2 (K := K)
  obtain ⟨ε3, h3⟩ := f4B2Family_3 (K := K)
  set y : Fin 4 → K := ![(ε0 : K) * x 0, (ε1 : K) * x 1, (ε2 : K) * x 2, (ε3 : K) * x 3] with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.F4 K (f4B2PosRoot m) (x m),
      g ∈ subsystemGroup Tag.F4 K f4B2Support := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_f4B2 (f4B2PosRoot_mem_parabolicRoots m) _
  have hu' : f4B2_data.Mat (List.ofFn fun m => pinnedX Tag.F4 K (f4B2PosRoot m) (x m)).prod =
      !![1, y 0, y 0 * y 1 - y 2, y 0 * y 2 - y 3; 0, 1, y 1, y 2; 0, 0, 1, y 0; 0, 0, 0, 1] := by
    rw [f4B2_data.Mat_list_prod _ hlist, List.map_ofFn, prod_ofFn_four]
    simp only [Function.comp_apply]
    rw [h0, h1, h2, h3, ← f4B2_prod_pos y]
    simp [hy, Matrix.mul_assoc]
  rw [f4B2_data.Mat_mul (torus2Elt_mem_f4B2 a b) (Subgroup.list_prod_mem _ hlist),
    f4B2_Mat_torus, hu'] at h
  have e : ∀ p q, (Matrix.diagonal ![(b : K), ((a * b⁻¹ : Kˣ) : K), ((a⁻¹ * b : Kˣ) : K),
        ((b⁻¹ : Kˣ) : K)] *
      !![1, y 0, y 0 * y 1 - y 2, y 0 * y 2 - y 3; 0, 1, y 1, y 2; 0, 0, 1, y 0; 0, 0, 0, 1] :
        Matrix (Fin 4) (Fin 4) K) p q = (1 : Matrix (Fin 4) (Fin 4) K) p q := fun p q => by
    rw [h]
  have d0 := e 0 0
  have d1 := e 1 1
  simp [Matrix.diagonal_mul] at d0 d1
  have hb : b = 1 := d0
  subst hb
  have ha : a = 1 := by simpa using d1
  subst ha
  have o0 := e 0 1
  have o1 := e 1 2
  have o2 := e 1 3
  have o3 := e 0 3
  simp [Matrix.diagonal_mul] at o0 o1 o2 o3
  have hy0 : y 0 = 0 := o0
  have hy1 : y 1 = 0 := o1
  have hy2 : y 2 = 0 := o2
  have hy3 : y 3 = 0 := by
    rw [hy0, hy2] at o3
    simpa using o3
  have hx0 : x = 0 := by
    funext m
    fin_cases m
    · exact (mul_eq_zero.1 (show (ε0 : K) * x 0 = 0 from hy0)).resolve_left (Units.ne_zero _)
    · exact (mul_eq_zero.1 (show (ε1 : K) * x 1 = 0 from hy1)).resolve_left (Units.ne_zero _)
    · exact (mul_eq_zero.1 (show (ε2 : K) * x 2 = 0 from hy2)).resolve_left (Units.ne_zero _)
    · exact (mul_eq_zero.1 (show (ε3 : K) * x 3 = 0 from hy3)).resolve_left (Units.ne_zero _)
  subst hx0
  refine ⟨torus2Elt_one _ _, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem f4B2Rep_injective : Function.Injective (f4B2Rep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : f4B2_data.Mat (g : ModGL Tag.F4 K) = 1 := by
    have := congrArg (fun x : f4SpGroup K => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hg
    simpa [coe_f4B2Rep] using this
  exact Subtype.ext (f4B2_bruhat.Mat_eq_one
    (fun t ht u hu => f4B2_eq_one_of_Mat_mul_eq_one ht hu) g.2 hmat)

end Families

end CFSG.RankThree.PartOne.KF4
