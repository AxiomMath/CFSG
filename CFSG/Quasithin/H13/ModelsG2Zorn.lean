module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped Matrix

section General

variable {K : Type*} [CommRing K]

@[expose] def zornIdentity : quasithinZorn K := (1, 0, 0, 1)

theorem zornMul_identity_left (y : quasithinZorn K) : quasithinZornMul zornIdentity y = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp only [quasithinZornMul, zornIdentity, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, one_mul, mul_zero, zero_add]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;>
    fin_cases i <;> simp [quasithinCross]

theorem zornMul_identity_right (y : quasithinZorn K) : quasithinZornMul y zornIdentity = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp only [quasithinZornMul, zornIdentity, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, mul_one, one_mul, zero_add]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;>
    fin_cases i <;> simp [quasithinCross]

theorem zornMul_add_left (x x' y : quasithinZorn K) :
    quasithinZornMul (x + x') y = quasithinZornMul x y + quasithinZornMul x' y := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨r', u', v', s'⟩ := x'
  obtain ⟨t, a, b, z⟩ := y
  simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [add_mul, Finset.sum_add_distrib]
    ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [add_mul, Finset.sum_add_distrib]
    ring

theorem zornMul_add_right (x y y' : quasithinZorn K) :
    quasithinZornMul x (y + y') = quasithinZornMul x y + quasithinZornMul x y' := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, a, b, z⟩ := y
  obtain ⟨t', a', b', z'⟩ := y'
  simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [mul_add, Finset.sum_add_distrib]
    ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [mul_add, Finset.sum_add_distrib]
    ring

theorem zornMul_smul_left (c : K) (x y : quasithinZorn K) :
    quasithinZornMul (c • x) y = c • quasithinZornMul x y := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, a, b, z⟩ := y
  simp only [quasithinZornMul, Prod.smul_mk, Pi.smul_apply, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)

theorem zornMul_smul_right (c : K) (x y : quasithinZorn K) :
    quasithinZornMul x (c • y) = c • quasithinZornMul x y := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, a, b, z⟩ := y
  simp only [quasithinZornMul, Prod.smul_mk, Pi.smul_apply, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinCross] <;> ring
  · simp only [Finset.mul_sum, mul_add]
    exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun _ _ => by ring)

variable (K) in
@[expose] def zornBilin : quasithinZorn K →ₗ[K] quasithinZorn K →ₗ[K] quasithinZorn K :=
  LinearMap.mk₂ K quasithinZornMul zornMul_add_left zornMul_smul_left zornMul_add_right
    zornMul_smul_right

theorem zornBilin_apply (x y : quasithinZorn K) : zornBilin K x y = quasithinZornMul x y :=
  rfl

variable (K) in
@[expose] def zornAut : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K) where
  carrier := {g | ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)}
  mul_mem' {g h} hg hh x y := by
    change g (h (quasithinZornMul x y)) = quasithinZornMul (g (h x)) (g (h y))
    rw [hh, hg]
  one_mem' _ _ := rfl
  inv_mem' {g} hg x y := by
    have h1 := hg (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    change g.symm (quasithinZornMul x y) = quasithinZornMul (g.symm x) (g.symm y)
    rw [← h1, LinearEquiv.symm_apply_apply]

theorem mem_zornAut {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} :
    g ∈ zornAut K ↔ ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y) :=
  Iff.rfl

theorem quasithinG2_eq_zornAut : quasithinG2 K = zornAut K :=
  Subgroup.closure_eq (zornAut K)

theorem zornAut_map_identity {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ zornAut K) :
    g zornIdentity = zornIdentity := by
  have h := hg zornIdentity (g.symm zornIdentity)
  rw [zornMul_identity_left, LinearEquiv.apply_symm_apply, zornMul_identity_right] at h
  exact h.symm

variable (K) in
@[expose] def zornCoord : quasithinZorn K ≃ₗ[K] (Fin 8 → K) where
  toFun x := ![x.1, x.2.1 0, x.2.1 1, x.2.1 2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2, x.2.2.2]
  invFun w := (w 0, ![w 1, w 2, w 3], ![w 4, w 5, w 6], w 7)
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl
  left_inv x := by
    obtain ⟨a, u, v, b⟩ := x
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;> fin_cases i <;> rfl
  right_inv w := by
    funext i
    fin_cases i <;> rfl

@[expose] def zornMatLin (G : Matrix (Fin 8) (Fin 8) K) : quasithinZorn K →ₗ[K] quasithinZorn K :=
  (zornCoord K).symm.toLinearMap ∘ₗ Matrix.toLin' G ∘ₗ (zornCoord K).toLinearMap

theorem zornMatLin_apply (G : Matrix (Fin 8) (Fin 8) K) (x : quasithinZorn K) :
    zornMatLin G x = (zornCoord K).symm (G *ᵥ zornCoord K x) :=
  rfl

theorem zornMatLin_mul (G H : Matrix (Fin 8) (Fin 8) K) (x : quasithinZorn K) :
    zornMatLin (G * H) x = zornMatLin G (zornMatLin H x) := by
  simp [zornMatLin_apply, Matrix.mulVec_mulVec]

theorem zornMatLin_one (x : quasithinZorn K) : zornMatLin (1 : Matrix (Fin 8) (Fin 8) K) x = x := by
  simp [zornMatLin_apply]

@[expose] def zornBasisVec (i : Fin 8) : quasithinZorn K :=
  (zornCoord K).symm (Pi.single i 1)

variable (K) in
@[expose] noncomputable def zornBasis : Module.Basis (Fin 8) K (quasithinZorn K) :=
  (Pi.basisFun K (Fin 8)).map (zornCoord K).symm

theorem zornBasis_apply (i : Fin 8) : zornBasis K i = zornBasisVec i := by
  simp [zornBasis, zornBasisVec]

theorem zornMatLin_mul_of_basis (G : Matrix (Fin 8) (Fin 8) K)
    (h : ∀ i j : Fin 8, zornMatLin G (quasithinZornMul (zornBasisVec i) (zornBasisVec j)) =
      quasithinZornMul (zornMatLin G (zornBasisVec i)) (zornMatLin G (zornBasisVec j)))
    (x y : quasithinZorn K) :
    zornMatLin G (quasithinZornMul x y) = quasithinZornMul (zornMatLin G x) (zornMatLin G y) := by
  have hB : (zornBilin K).compr₂ (zornMatLin G) =
      (zornBilin K).compl₁₂ (zornMatLin G) (zornMatLin G) := by
    refine LinearMap.ext_basis (zornBasis K) (zornBasis K) fun i j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, zornBilin_apply, zornBasis_apply]
    exact h i j
  have := LinearMap.congr_fun₂ hB x y
  simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, zornBilin_apply] using this

end General

theorem card_le_card_mul_card_inf_stabilizer {G X : Type*} [Group G] [MulAction G X] [Finite G]
    (H : Subgroup G) (x : X) (T : Set X) [Finite T] (hT : ∀ h ∈ H, h • x ∈ T) :
    Nat.card H ≤ Nat.card T * Nat.card ↥(H ⊓ MulAction.stabilizer G x) := by
  have h1 : Nat.card (MulAction.orbit H x) * Nat.card (MulAction.stabilizer H x) = Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  have h2 : Nat.card (MulAction.orbit H x) ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective
      (fun y : MulAction.orbit H x => (⟨y.1, ?_⟩ : T)) fun y z hyz => ?_
    · obtain ⟨h, hh⟩ := y.2
      rw [← hh]
      exact hT h h.2
    · have h := congrArg (fun t : T => (t : X)) hyz
      exact Subtype.ext h
  have h3 : Nat.card (MulAction.stabilizer H x) = Nat.card ↥(H ⊓ MulAction.stabilizer G x) :=
    Nat.card_congr
      { toFun := fun h => ⟨h.1.1, h.1.2, h.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← h1, h3]
  exact Nat.mul_le_mul_right _ h2

@[expose] def zornX0 : quasithinZorn (ZMod 3) := (0, ![0, 0, 1], ![0, 0, 2], 0)

@[expose] def zornY0 : quasithinZorn (ZMod 3) := (0, ![0, 1, 0], ![0, 2, 0], 0)

@[expose] def zornZ0 : quasithinZorn (ZMod 3) := (0, ![1, 0, 1], ![1, 0, 1], 0)

@[expose] def zornSet1 : Set (quasithinZorn (ZMod 3)) :=
  {x | quasithinZornMul x x = -zornIdentity}

@[expose] def zornSet2 : Set (quasithinZorn (ZMod 3)) :=
  {y | quasithinZornMul y y = -zornIdentity ∧
    quasithinZornMul zornX0 y + quasithinZornMul y zornX0 = 0}

@[expose] def zornSet3 : Set (quasithinZorn (ZMod 3)) :=
  {z | quasithinZornMul z z = -zornIdentity ∧
    quasithinZornMul zornX0 z + quasithinZornMul z zornX0 = 0 ∧
    quasithinZornMul zornY0 z + quasithinZornMul z zornY0 = 0 ∧
    quasithinZornMul (quasithinZornMul zornX0 zornY0) z +
      quasithinZornMul z (quasithinZornMul zornX0 zornY0) = 0}

instance : DecidablePred (· ∈ zornSet1) := fun x => by
  unfold zornSet1
  infer_instance

instance : DecidablePred (· ∈ zornSet2) := fun x => by
  unfold zornSet2
  infer_instance

instance : DecidablePred (· ∈ zornSet3) := fun x => by
  unfold zornSet3
  infer_instance

theorem card_zornSet1 : Fintype.card zornSet1 = 702 := by
  decide +kernel

theorem card_zornSet2 : Fintype.card zornSet2 = 252 := by
  decide +kernel

theorem card_zornSet3 : Fintype.card zornSet3 = 24 := by
  decide +kernel

theorem zornX0_mem : zornX0 ∈ zornSet1 := by
  decide +kernel

@[expose] def zornWords : Fin 8 → quasithinZorn (ZMod 3) :=
  ![zornIdentity, zornX0, zornY0, quasithinZornMul zornX0 zornY0, zornZ0,
    quasithinZornMul zornX0 zornZ0, quasithinZornMul zornY0 zornZ0,
    quasithinZornMul (quasithinZornMul zornX0 zornY0) zornZ0]

@[expose] def zornWordsInv : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  !![2, 0, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 2, 0, 0, 1, 0;
    0, 0, 2, 0, 0, 1, 0, 0;
    0, 2, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 1, 0, 1, 0;
    1, 0, 1, 0, 0, 1, 0, 2;
    0, 1, 0, 2, 1, 0, 2, 0;
    1, 0, 2, 0, 0, 2, 0, 2]

theorem zornBasisVec_eq_sum :
    ∀ k : Fin 8, zornBasisVec k = ∑ j, zornWordsInv j k • zornWords j := by
  decide +kernel

theorem eq_one_of_fix {g : quasithinZorn (ZMod 3) ≃ₗ[ZMod 3] quasithinZorn (ZMod 3)}
    (hg : g ∈ zornAut (ZMod 3)) (hx : g zornX0 = zornX0) (hy : g zornY0 = zornY0)
    (hz : g zornZ0 = zornZ0) : g = 1 := by
  have hw : ∀ j, g (zornWords j) = zornWords j := by
    intro j
    fin_cases j <;> simp [zornWords, hg _ _, zornAut_map_identity hg, hx, hy, hz]
  have hb : ∀ k, g (zornBasisVec k) = zornBasisVec k := by
    intro k
    rw [zornBasisVec_eq_sum k, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hw j]
  have hlin : (g : quasithinZorn (ZMod 3) →ₗ[ZMod 3] quasithinZorn (ZMod 3)) = LinearMap.id :=
    (zornBasis (ZMod 3)).ext fun k => by
      rw [zornBasis_apply, LinearEquiv.coe_coe, hb k, LinearMap.id_apply]
  exact LinearEquiv.ext fun v => by
    have := LinearMap.congr_fun hlin v
    simpa using this

instance : Finite (quasithinZorn (ZMod 3) ≃ₗ[ZMod 3] quasithinZorn (ZMod 3)) :=
  Finite.of_injective (fun g => (g : quasithinZorn (ZMod 3) → quasithinZorn (ZMod 3)))
    DFunLike.coe_injective

theorem card_zornAut_three_le : Nat.card (zornAut (ZMod 3)) ≤ 4245696 := by
  set A := zornAut (ZMod 3)
  set G := quasithinZorn (ZMod 3) ≃ₗ[ZMod 3] quasithinZorn (ZMod 3)
  set H1 : Subgroup G := A ⊓ MulAction.stabilizer G zornX0
  set H2 : Subgroup G := H1 ⊓ MulAction.stabilizer G zornY0
  set H3 : Subgroup G := H2 ⊓ MulAction.stabilizer G zornZ0
  have hm : ∀ g ∈ A, ∀ x, quasithinZornMul x x = -zornIdentity →
      quasithinZornMul (g x) (g x) = -zornIdentity := by
    intro g hg x hx
    have hneg : g (-zornIdentity) = -g zornIdentity := map_neg g zornIdentity
    rw [← hg, hx, hneg, zornAut_map_identity hg]
  have hanti : ∀ g ∈ A, ∀ a x, g a = a → quasithinZornMul a x + quasithinZornMul x a = 0 →
      quasithinZornMul a (g x) + quasithinZornMul (g x) a = 0 := by
    intro g hg a x ha h
    rw [← ha, ← hg, ← hg, ← map_add, h, map_zero]
  have hA : Nat.card A ≤ 702 * Nat.card H1 := by
    have := card_le_card_mul_card_inf_stabilizer A zornX0 zornSet1 fun g hg =>
      hm g hg _ zornX0_mem
    rwa [Nat.card_eq_fintype_card (α := zornSet1), card_zornSet1] at this
  have hH1 : Nat.card H1 ≤ 252 * Nat.card H2 := by
    have := card_le_card_mul_card_inf_stabilizer H1 zornY0 zornSet2 fun g hg => by
      have hgA : g ∈ A := hg.1
      have hgx : g zornX0 = zornX0 := hg.2
      exact ⟨hm g hgA _ (by decide +kernel), hanti g hgA _ _ hgx (by decide +kernel)⟩
    rwa [Nat.card_eq_fintype_card (α := zornSet2), card_zornSet2] at this
  have hH2 : Nat.card H2 ≤ 24 * Nat.card H3 := by
    have := card_le_card_mul_card_inf_stabilizer H2 zornZ0 zornSet3 fun g hg => by
      have hgA : g ∈ A := hg.1.1
      have hgx : g zornX0 = zornX0 := hg.1.2
      have hgy : g zornY0 = zornY0 := hg.2
      have hgxy : g (quasithinZornMul zornX0 zornY0) = quasithinZornMul zornX0 zornY0 := by
        rw [hgA, hgx, hgy]
      exact ⟨hm g hgA _ (by decide +kernel), hanti g hgA _ _ hgx (by decide +kernel),
        hanti g hgA _ _ hgy (by decide +kernel), hanti g hgA _ _ hgxy (by decide +kernel)⟩
    rwa [Nat.card_eq_fintype_card (α := zornSet3), card_zornSet3] at this
  have hH3 : Nat.card H3 = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun g h => Subtype.ext ?_⟩, ⟨1⟩⟩
    have hg := fun (g : H3) => eq_one_of_fix g.2.1.1.1 g.2.1.1.2 g.2.1.2 g.2.2
    rw [hg g, hg h]
  calc Nat.card A ≤ 702 * Nat.card H1 := hA
    _ ≤ 702 * (252 * Nat.card H2) := Nat.mul_le_mul_left _ hH1
    _ ≤ 702 * (252 * (24 * Nat.card H3)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hH2)
    _ = 4245696 := by rw [hH3]

end CFSG.Quasithin.H13
