module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix

variable {G : Type*} [Group G] {r : ℕ}

@[expose] def u2dCoord (b : Fin 2 → G) (a : Fin 2 → ZMod r) : G :=
  b 0 ^ (a 0).val * b 1 ^ (a 1).val

@[simp] theorem u2dCoord_zero (b : Fin 2 → G) : u2dCoord b (0 : Fin 2 → ZMod r) = 1 := by
  simp [u2dCoord]

theorem u2dCoord_single (b : Fin 2 → G) (j : Fin 2) (c : ZMod r) :
    u2dCoord b (Pi.single j c) = b j ^ c.val := by
  fin_cases j <;> simp [u2dCoord]

theorem u2d_matrix_ext {N N' : Matrix (Fin 2) (Fin 2) (ZMod r)}
    (h : ∀ j, N *ᵥ Pi.single j 1 = N' *ᵥ Pi.single j 1) : N = N' :=
  Matrix.ext fun i j => by simpa [Matrix.mulVec_single_one] using congrFun (h j) i

structure U2DFrame (r : ℕ) (E : Subgroup G) (b : Fin 2 → G) : Prop where
  elem : IsElemAbelian r E
  mem : ∀ i, b i ∈ E
  indep : ∀ a : Fin 2 → ZMod r, u2dCoord b a = 1 → a = 0
  span : ∀ x ∈ E, ∃ a : Fin 2 → ZMod r, u2dCoord b a = x

namespace U2DFrame

variable {E : Subgroup G} {b : Fin 2 → G}

theorem comm (hF : U2DFrame r E b) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have := hF.elem.1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)

theorem pow_eq_one (hF : U2DFrame r E b) (i : Fin 2) : b i ^ r = 1 :=
  hF.elem.2 _ (hF.mem i)

theorem coord_mem (hF : U2DFrame r E b) (a : Fin 2 → ZMod r) : u2dCoord b a ∈ E :=
  E.mul_mem (E.pow_mem (hF.mem 0) _) (E.pow_mem (hF.mem 1) _)

variable [NeZero r]

theorem pow_val_add (hF : U2DFrame r E b) (i : Fin 2) (x y : ZMod r) :
    b i ^ (x + y).val = b i ^ x.val * b i ^ y.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ (hF.pow_eq_one i), pow_add]

theorem zpow_val_intCast (hF : U2DFrame r E b) (i : Fin 2) (k : ℤ) :
    b i ^ (k : ZMod r).val = b i ^ k := by
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' k (hF.pow_eq_one i)]

theorem coord_add (hF : U2DFrame r E b) (a c : Fin 2 → ZMod r) :
    u2dCoord b (a + c) = u2dCoord b a * u2dCoord b c := by
  have h : ∀ i j (m k : ℕ), Commute (b i ^ m) (b j ^ k) := fun i j m k =>
    hF.comm (E.pow_mem (hF.mem i) m) (E.pow_mem (hF.mem j) k)
  simp only [u2dCoord, Pi.add_apply, hF.pow_val_add]
  rw [(h 1 0 _ _).mul_mul_mul_comm]

theorem coord_neg (hF : U2DFrame r E b) (a : Fin 2 → ZMod r) :
    u2dCoord b (-a) = (u2dCoord b a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hF.coord_add, neg_add_cancel, u2dCoord_zero])

theorem coord_injective (hF : U2DFrame r E b) : Function.Injective (u2dCoord (r := r) b) :=
  fun a c h => sub_eq_zero.1 (hF.indep _ (by
    rw [sub_eq_add_neg, hF.coord_add, hF.coord_neg, h, mul_inv_cancel]))

theorem coord_zpow_single (hF : U2DFrame r E b) (j : Fin 2) (k : ℤ) :
    u2dCoord b (Pi.single j (k : ZMod r)) = b j ^ k := by
  rw [u2dCoord_single, hF.zpow_val_intCast]

theorem coord_single_one (hF : U2DFrame r E b) (j : Fin 2) :
    u2dCoord b (Pi.single j (1 : ZMod r)) = b j := by
  have h := hF.coord_zpow_single j 1
  rwa [Int.cast_one, zpow_one] at h

@[expose] noncomputable def coordEquiv (hF : U2DFrame r E b) : (Fin 2 → ZMod r) ≃ E :=
  Equiv.ofBijective (fun a => ⟨u2dCoord b a, hF.coord_mem a⟩)
    ⟨fun _ _ h => hF.coord_injective (congrArg Subtype.val h),
      fun x => (hF.span x x.2).imp fun _ h => Subtype.ext h⟩

theorem coord_coordEquiv_symm (hF : U2DFrame r E b) (x : E) :
    u2dCoord b (hF.coordEquiv.symm x) = x :=
  congrArg Subtype.val (hF.coordEquiv.apply_symm_apply x)

theorem conj_mem {m : G} (hm : m ∈ normalizer (E : Set G)) {x : G} (hx : x ∈ E) :
    m * x * m⁻¹ ∈ E :=
  (mem_normalizer_iff.1 hm x).1 hx

@[expose] noncomputable def conjFun (hF : U2DFrame r E b) (m : normalizer (E : Set G))
    (a : Fin 2 → ZMod r) : Fin 2 → ZMod r :=
  hF.coordEquiv.symm ⟨(m : G) * u2dCoord b a * (m : G)⁻¹, conj_mem m.2 (hF.coord_mem a)⟩

theorem coord_conjFun (hF : U2DFrame r E b) (m : normalizer (E : Set G)) (a : Fin 2 → ZMod r) :
    u2dCoord b (hF.conjFun m a) = (m : G) * u2dCoord b a * (m : G)⁻¹ :=
  hF.coord_coordEquiv_symm _

theorem conjFun_add (hF : U2DFrame r E b) (m : normalizer (E : Set G)) (a c : Fin 2 → ZMod r) :
    hF.conjFun m (a + c) = hF.conjFun m a + hF.conjFun m c := by
  apply hF.coord_injective
  rw [hF.coord_conjFun, hF.coord_add, hF.coord_add, hF.coord_conjFun, hF.coord_conjFun]
  group

theorem conjFun_zero (hF : U2DFrame r E b) (m : normalizer (E : Set G)) :
    hF.conjFun m 0 = 0 := by
  apply hF.coord_injective
  rw [hF.coord_conjFun, u2dCoord_zero]
  group

theorem conjFun_mul (hF : U2DFrame r E b) (m m' : normalizer (E : Set G)) (a : Fin 2 → ZMod r) :
    hF.conjFun (m * m') a = hF.conjFun m (hF.conjFun m' a) := by
  apply hF.coord_injective
  rw [hF.coord_conjFun, hF.coord_conjFun, hF.coord_conjFun, Subgroup.coe_mul]
  group

theorem conjFun_one (hF : U2DFrame r E b) (a : Fin 2 → ZMod r) : hF.conjFun 1 a = a := by
  apply hF.coord_injective
  rw [hF.coord_conjFun]
  simp

@[expose] noncomputable def conjV (hF : U2DFrame r E b) (m : normalizer (E : Set G)) :
    (Fin 2 → ZMod r) →+ (Fin 2 → ZMod r) where
  toFun := hF.conjFun m
  map_zero' := hF.conjFun_zero m
  map_add' := hF.conjFun_add m

@[expose] noncomputable def rhoM (hF : U2DFrame r E b) :
    normalizer (E : Set G) →* Matrix (Fin 2) (Fin 2) (ZMod r) where
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

theorem rhoM_mulVec (hF : U2DFrame r E b) (m : normalizer (E : Set G)) (v : Fin 2 → ZMod r) :
    hF.rhoM m *ᵥ v = hF.conjFun m v :=
  LinearMap.toMatrix'_mulVec _ v

@[expose] noncomputable def rho (hF : U2DFrame r E b) :
    normalizer (E : Set G) →* GL (Fin 2) (ZMod r) :=
  hF.rhoM.toHomUnits

theorem coord_rho_mulVec (hF : U2DFrame r E b) (m : normalizer (E : Set G))
    (v : Fin 2 → ZMod r) :
    u2dCoord b ((hF.rho m : Matrix (Fin 2) (Fin 2) (ZMod r)) *ᵥ v) =
      (m : G) * u2dCoord b v * (m : G)⁻¹ := by
  rw [show ((hF.rho m : GL (Fin 2) (ZMod r)) : Matrix (Fin 2) (Fin 2) (ZMod r)) = hF.rhoM m
    from rfl, hF.rhoM_mulVec, hF.coord_conjFun]

theorem rho_eq_one_iff (hF : U2DFrame r E b) (m : normalizer (E : Set G)) :
    hF.rho m = 1 ↔ (m : G) ∈ centralizer (E : Set G) := by
  constructor
  · intro h
    refine mem_centralizer_iff.2 fun x hx => ?_
    obtain ⟨a, rfl⟩ := hF.span x hx
    have h2 := hF.coord_rho_mulVec m a
    rw [h, Units.val_one, one_mulVec] at h2
    calc u2dCoord b a * (m : G) = (m * u2dCoord b a * (m : G)⁻¹) * m := by rw [← h2]
      _ = m * u2dCoord b a := by group
  · intro hm
    refine Units.ext (u2d_matrix_ext fun j => hF.coord_injective ?_)
    rw [hF.coord_rho_mulVec, Units.val_one, one_mulVec,
      ← mem_centralizer_iff.1 hm _ (hF.coord_mem _)]
    group

theorem ker_rho (hF : U2DFrame r E b) :
    hF.rho.ker = (centralizer (E : Set G)).subgroupOf (normalizer (E : Set G)) := by
  ext m
  rw [MonoidHom.mem_ker, hF.rho_eq_one_iff, Subgroup.mem_subgroupOf]

theorem rho_eq_diagonal (hF : U2DFrame r E b) (m : normalizer (E : Set G)) {k : Fin 2 → ℤ}
    (h : ∀ i, (m : G) * b i * (m : G)⁻¹ = b i ^ k i) :
    (hF.rho m : Matrix (Fin 2) (Fin 2) (ZMod r)) = diagonal fun i => (k i : ZMod r) := by
  refine u2d_matrix_ext fun j => hF.coord_injective ?_
  rw [hF.coord_rho_mulVec, hF.coord_single_one, h, diagonal_mulVec_single]
  simp only [mul_one]
  rw [hF.coord_zpow_single]

theorem exists_rho_eq_diagonal (hF : U2DFrame r E b) (m : normalizer (E : Set G))
    (h : ∀ i, (m : G) * b i * (m : G)⁻¹ ∈ zpowers (b i)) :
    ∃ α : Fin 2 → ZMod r, (hF.rho m : Matrix (Fin 2) (Fin 2) (ZMod r)) = diagonal α := by
  choose k hk using fun i => mem_zpowers_iff.1 (h i)
  exact ⟨_, hF.rho_eq_diagonal m fun i => (hk i).symm⟩

theorem rho_mulVec_single (hF : U2DFrame r E b) (m : normalizer (E : Set G)) {i j : Fin 2}
    {k : ℤ} (h : (m : G) * b j * (m : G)⁻¹ = b i ^ k) :
    (hF.rho m : Matrix (Fin 2) (Fin 2) (ZMod r)) *ᵥ Pi.single j 1 = Pi.single i (k : ZMod r) :=
  hF.coord_injective (by rw [hF.coord_rho_mulVec, hF.coord_single_one, h, hF.coord_zpow_single])

theorem rho_antidiag (hF : U2DFrame r E b) (m : normalizer (E : Set G))
    (h₀ : (m : G) * b 0 * (m : G)⁻¹ ∈ zpowers (b 1))
    (h₁ : (m : G) * b 1 * (m : G)⁻¹ ∈ zpowers (b 0)) :
    (hF.rho m : Matrix (Fin 2) (Fin 2) (ZMod r)) 0 0 = 0 ∧
      (hF.rho m : Matrix (Fin 2) (Fin 2) (ZMod r)) 1 1 = 0 := by
  obtain ⟨k₀, hk₀⟩ := mem_zpowers_iff.1 h₀
  obtain ⟨k₁, hk₁⟩ := mem_zpowers_iff.1 h₁
  have e₀ := congrFun (hF.rho_mulVec_single m hk₀.symm) 0
  have e₁ := congrFun (hF.rho_mulVec_single m hk₁.symm) 1
  simp only [Matrix.mulVec_single_one] at e₀ e₁
  exact ⟨by simpa using e₀, by simpa using e₁⟩

theorem conj_mem_zpowers_of_mulVec (hF : U2DFrame r E b) (m : normalizer (E : Set G))
    (i : Fin 2)
    (h : (hF.rho m : Matrix (Fin 2) (Fin 2) (ZMod r)) *ᵥ Pi.single i 1 ∈
      Submodule.span (ZMod r) {(Pi.single i 1 : Fin 2 → ZMod r)}) :
    (m : G) * b i * (m : G)⁻¹ ∈ zpowers (b i) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  have he : c • (Pi.single i 1 : Fin 2 → ZMod r) = Pi.single i c := by
    ext j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  have h1 : (m : G) * b i * (m : G)⁻¹ = u2dCoord b (Pi.single i c) := by
    rw [← he, hc, hF.coord_rho_mulVec, hF.coord_single_one]
  rw [h1, u2dCoord_single]
  exact pow_mem (mem_zpowers _) _

end U2DFrame

end CFSG.LocalAnalysis.UniquenessCase.UC22
