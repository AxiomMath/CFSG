module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix

variable {G : Type*} [Group G] {r : ℕ}

@[expose] def u81Coord (b : Fin 3 → G) (a : Fin 3 → ZMod r) : G :=
  b 0 ^ (a 0).val * b 1 ^ (a 1).val * b 2 ^ (a 2).val

@[simp] theorem u81Coord_zero (b : Fin 3 → G) : u81Coord b (0 : Fin 3 → ZMod r) = 1 := by
  simp [u81Coord]

theorem u81Coord_single (b : Fin 3 → G) (j : Fin 3) (c : ZMod r) :
    u81Coord b (Pi.single j c) = b j ^ c.val := by
  fin_cases j <;> simp [u81Coord]

theorem u81_matrix_ext {N N' : Matrix (Fin 3) (Fin 3) (ZMod r)}
    (h : ∀ j, N *ᵥ Pi.single j 1 = N' *ᵥ Pi.single j 1) : N = N' :=
  Matrix.ext fun i j => by simpa [Matrix.mulVec_single_one] using congrFun (h j) i

structure U81Frame (r : ℕ) (B : Subgroup G) (b : Fin 3 → G) : Prop where
  elem : IsElemAbelian r B
  mem : ∀ i, b i ∈ B
  indep : ∀ a : Fin 3 → ZMod r, u81Coord b a = 1 → a = 0
  span : ∀ x ∈ B, ∃ a : Fin 3 → ZMod r, u81Coord b a = x

namespace U81Frame

variable {B : Subgroup G} {b : Fin 3 → G}

theorem comm (hF : U81Frame r B b) {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x := by
  haveI := hF.elem.1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)

theorem pow_eq_one (hF : U81Frame r B b) (i : Fin 3) : b i ^ r = 1 :=
  hF.elem.2 _ (hF.mem i)

theorem coord_mem (hF : U81Frame r B b) (a : Fin 3 → ZMod r) : u81Coord b a ∈ B :=
  B.mul_mem (B.mul_mem (B.pow_mem (hF.mem 0) _) (B.pow_mem (hF.mem 1) _))
    (B.pow_mem (hF.mem 2) _)

variable [NeZero r]

theorem pow_val_add (hF : U81Frame r B b) (i : Fin 3) (x y : ZMod r) :
    b i ^ (x + y).val = b i ^ x.val * b i ^ y.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ (hF.pow_eq_one i), pow_add]

theorem zpow_val_intCast (hF : U81Frame r B b) (i : Fin 3) (k : ℤ) :
    b i ^ (k : ZMod r).val = b i ^ k := by
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' k (hF.pow_eq_one i)]

theorem coord_add (hF : U81Frame r B b) (a c : Fin 3 → ZMod r) :
    u81Coord b (a + c) = u81Coord b a * u81Coord b c := by
  have h : ∀ i j (m k : ℕ), Commute (b i ^ m) (b j ^ k) := fun i j m k =>
    hF.comm (B.pow_mem (hF.mem i) m) (B.pow_mem (hF.mem j) k)
  simp only [u81Coord, Pi.add_apply, hF.pow_val_add]
  rw [((h 2 0 _ _).mul_right (h 2 1 _ _)).mul_mul_mul_comm, (h 1 0 _ _).mul_mul_mul_comm]

theorem coord_neg (hF : U81Frame r B b) (a : Fin 3 → ZMod r) :
    u81Coord b (-a) = (u81Coord b a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hF.coord_add, neg_add_cancel, u81Coord_zero])

theorem coord_injective (hF : U81Frame r B b) : Function.Injective (u81Coord (r := r) b) :=
  fun a c h => sub_eq_zero.1 (hF.indep _ (by
    rw [sub_eq_add_neg, hF.coord_add, hF.coord_neg, h, mul_inv_cancel]))

theorem coord_zpow_single (hF : U81Frame r B b) (j : Fin 3) (k : ℤ) :
    u81Coord b (Pi.single j (k : ZMod r)) = b j ^ k := by
  rw [u81Coord_single, hF.zpow_val_intCast]

theorem coord_single_one (hF : U81Frame r B b) (j : Fin 3) :
    u81Coord b (Pi.single j (1 : ZMod r)) = b j := by
  have h := hF.coord_zpow_single j 1
  rwa [Int.cast_one, zpow_one] at h

@[expose] noncomputable def coordEquiv (hF : U81Frame r B b) : (Fin 3 → ZMod r) ≃ B :=
  Equiv.ofBijective (fun a => ⟨u81Coord b a, hF.coord_mem a⟩)
    ⟨fun _ _ h => hF.coord_injective (congrArg Subtype.val h),
      fun x => (hF.span x x.2).imp fun _ h => Subtype.ext h⟩

theorem coord_coordEquiv_symm (hF : U81Frame r B b) (x : B) :
    u81Coord b (hF.coordEquiv.symm x) = x :=
  congrArg Subtype.val (hF.coordEquiv.apply_symm_apply x)

theorem conj_mem {m : G} (hm : m ∈ normalizer (B : Set G)) {x : G} (hx : x ∈ B) :
    m * x * m⁻¹ ∈ B :=
  (mem_normalizer_iff.1 hm x).1 hx

@[expose] noncomputable def conjFun (hF : U81Frame r B b) (m : normalizer (B : Set G))
    (a : Fin 3 → ZMod r) : Fin 3 → ZMod r :=
  hF.coordEquiv.symm ⟨(m : G) * u81Coord b a * (m : G)⁻¹, conj_mem m.2 (hF.coord_mem a)⟩

theorem coord_conjFun (hF : U81Frame r B b) (m : normalizer (B : Set G)) (a : Fin 3 → ZMod r) :
    u81Coord b (hF.conjFun m a) = (m : G) * u81Coord b a * (m : G)⁻¹ :=
  hF.coord_coordEquiv_symm _

theorem conjFun_add (hF : U81Frame r B b) (m : normalizer (B : Set G)) (a c : Fin 3 → ZMod r) :
    hF.conjFun m (a + c) = hF.conjFun m a + hF.conjFun m c := by
  apply hF.coord_injective
  rw [hF.coord_conjFun, hF.coord_add, hF.coord_add, hF.coord_conjFun, hF.coord_conjFun]
  group

theorem conjFun_zero (hF : U81Frame r B b) (m : normalizer (B : Set G)) :
    hF.conjFun m 0 = 0 := by
  apply hF.coord_injective
  rw [hF.coord_conjFun, u81Coord_zero]
  group

theorem conjFun_mul (hF : U81Frame r B b) (m m' : normalizer (B : Set G)) (a : Fin 3 → ZMod r) :
    hF.conjFun (m * m') a = hF.conjFun m (hF.conjFun m' a) := by
  apply hF.coord_injective
  rw [hF.coord_conjFun, hF.coord_conjFun, hF.coord_conjFun, Subgroup.coe_mul]
  group

theorem conjFun_one (hF : U81Frame r B b) (a : Fin 3 → ZMod r) : hF.conjFun 1 a = a := by
  apply hF.coord_injective
  rw [hF.coord_conjFun]
  simp

@[expose] noncomputable def conjV (hF : U81Frame r B b) (m : normalizer (B : Set G)) :
    (Fin 3 → ZMod r) →+ (Fin 3 → ZMod r) where
  toFun := hF.conjFun m
  map_zero' := hF.conjFun_zero m
  map_add' := hF.conjFun_add m

@[expose] noncomputable def rhoM (hF : U81Frame r B b) :
    normalizer (B : Set G) →* Matrix (Fin 3) (Fin 3) (ZMod r) where
  toFun m := LinearMap.toMatrix' ((hF.conjV m).toZModLinearMap r)
  map_one' := by
    have : (hF.conjV 1).toZModLinearMap r = LinearMap.id :=
      LinearMap.ext fun a => hF.conjFun_one a
    rw [this, LinearMap.toMatrix'_id]
  map_mul' m m' := by
    have : (hF.conjV (m * m')).toZModLinearMap r =
        ((hF.conjV m).toZModLinearMap r).comp ((hF.conjV m').toZModLinearMap r) :=
      LinearMap.ext fun a => hF.conjFun_mul m m' a
    rw [this, LinearMap.toMatrix'_comp]

theorem rhoM_mulVec (hF : U81Frame r B b) (m : normalizer (B : Set G)) (v : Fin 3 → ZMod r) :
    hF.rhoM m *ᵥ v = hF.conjFun m v :=
  LinearMap.toMatrix'_mulVec _ v

@[expose] noncomputable def rho (hF : U81Frame r B b) :
    normalizer (B : Set G) →* GL (Fin 3) (ZMod r) :=
  hF.rhoM.toHomUnits

theorem coord_rho_mulVec (hF : U81Frame r B b) (m : normalizer (B : Set G))
    (v : Fin 3 → ZMod r) :
    u81Coord b ((hF.rho m : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v) =
      (m : G) * u81Coord b v * (m : G)⁻¹ := by
  rw [show ((hF.rho m : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) = hF.rhoM m
    from rfl, hF.rhoM_mulVec, hF.coord_conjFun]

theorem rho_eq_one_iff (hF : U81Frame r B b) (m : normalizer (B : Set G)) :
    hF.rho m = 1 ↔ (m : G) ∈ centralizer (B : Set G) := by
  constructor
  · intro h
    refine mem_centralizer_iff.2 fun x hx => ?_
    obtain ⟨a, rfl⟩ := hF.span x hx
    have h2 := hF.coord_rho_mulVec m a
    rw [h, Units.val_one, one_mulVec] at h2
    calc u81Coord b a * (m : G) = (m * u81Coord b a * (m : G)⁻¹) * m := by rw [← h2]
      _ = m * u81Coord b a := by group
  · intro hm
    refine Units.ext (u81_matrix_ext fun j => hF.coord_injective ?_)
    rw [hF.coord_rho_mulVec, Units.val_one, one_mulVec,
      ← mem_centralizer_iff.1 hm _ (hF.coord_mem _)]
    group

theorem ker_rho (hF : U81Frame r B b) :
    hF.rho.ker = (centralizer (B : Set G)).subgroupOf (normalizer (B : Set G)) := by
  ext m
  rw [MonoidHom.mem_ker, hF.rho_eq_one_iff, Subgroup.mem_subgroupOf]

theorem rho_eq_diagonal (hF : U81Frame r B b) (m : normalizer (B : Set G)) {k : Fin 3 → ℤ}
    (h : ∀ i, (m : G) * b i * (m : G)⁻¹ = b i ^ k i) :
    (hF.rho m : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal fun i => (k i : ZMod r) := by
  refine u81_matrix_ext fun j => hF.coord_injective ?_
  rw [hF.coord_rho_mulVec, hF.coord_single_one, h, diagonal_mulVec_single]
  simp only [mul_one]
  rw [hF.coord_zpow_single]

theorem exists_rho_eq_diagonal (hF : U81Frame r B b) (m : normalizer (B : Set G))
    (h : ∀ i, (m : G) * b i * (m : G)⁻¹ ∈ zpowers (b i)) :
    ∃ α : Fin 3 → ZMod r, (hF.rho m : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α := by
  choose k hk using fun i => mem_zpowers_iff.1 (h i)
  exact ⟨_, hF.rho_eq_diagonal m fun i => (hk i).symm⟩

theorem conj_mem_zpowers_of_mulVec (hF : U81Frame r B b) (m : normalizer (B : Set G))
    (i : Fin 3)
    (h : (hF.rho m : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ Pi.single i 1 ∈
      Submodule.span (ZMod r) {(Pi.single i 1 : Fin 3 → ZMod r)}) :
    (m : G) * b i * (m : G)⁻¹ ∈ zpowers (b i) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  have he : c • (Pi.single i 1 : Fin 3 → ZMod r) = Pi.single i c := by
    ext j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  have h1 : (m : G) * b i * (m : G)⁻¹ = u81Coord b (Pi.single i c) := by
    rw [← he, hc, hF.coord_rho_mulVec, hF.coord_single_one]
  rw [h1, u81Coord_single]
  exact pow_mem (mem_zpowers _) _

end U81Frame

end CFSG.LocalAnalysis.UniquenessCase.UC22
