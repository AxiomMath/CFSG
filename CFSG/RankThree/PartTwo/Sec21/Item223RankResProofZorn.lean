module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofEigen
public import CFSG.Quasithin.H13.ModelsG2Zorn
public import CFSG.Quasithin.Background.P3G2Zorn

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

open CFSG.Open CFSG.Quasithin.H13 CFSG.Quasithin.Explicit Matrix

section Coordinates

variable {R : Type*} [CommRing R]

@[expose] def mul8 (a b : Fin 8 → R) : Fin 8 → R :=
  ![a 0 * b 0 + a 1 * b 4 + a 2 * b 5 + a 3 * b 6,
    a 0 * b 1 + b 7 * a 1 - (a 5 * b 6 - a 6 * b 5),
    a 0 * b 2 + b 7 * a 2 - (a 6 * b 4 - a 4 * b 6),
    a 0 * b 3 + b 7 * a 3 - (a 4 * b 5 - a 5 * b 4),
    b 0 * a 4 + a 7 * b 4 + (a 2 * b 3 - a 3 * b 2),
    b 0 * a 5 + a 7 * b 5 + (a 3 * b 1 - a 1 * b 3),
    b 0 * a 6 + a 7 * b 6 + (a 1 * b 2 - a 2 * b 1),
    a 7 * b 7 + a 4 * b 1 + a 5 * b 2 + a 6 * b 3]

theorem zornCoord_mul (x y : quasithinZorn R) :
    zornCoord R (quasithinZornMul x y) = mul8 (zornCoord R x) (zornCoord R y) := by
  funext i
  fin_cases i <;>
    simp [zornCoord, quasithinZornMul, quasithinCross, mul8, Fin.sum_univ_three] <;> ring

@[expose] def gram8 : Matrix (Fin 8) (Fin 8) R :=
  !![0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, -1, 0, 0, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0]

theorem polar8_eq (a b : Fin 8 → R) :
    a ⬝ᵥ (gram8 *ᵥ b) = a 0 * b 7 + a 7 * b 0 -
      (a 1 * b 4 + a 4 * b 1 + a 2 * b 5 + a 5 * b 2 + a 3 * b 6 + a 6 * b 3) := by
  simp [gram8, dotProduct, Matrix.mulVec, Fin.sum_univ_eight]
  ring

@[expose] def one8 : Fin 8 → R := ![1, 0, 0, 0, 0, 0, 0, 1]

theorem mul8_mul8 (a c y : Fin 8 → R) (ha : a 0 + a 7 = 0) (hc : c 0 + c 7 = 0) :
    mul8 a (mul8 c y) + mul8 c (mul8 a y) = (-(a ⬝ᵥ (gram8 *ᵥ c))) • y := by
  have ha7 : a 7 = -a 0 := by linear_combination ha
  have hc7 : c 7 = -c 0 := by linear_combination hc
  rw [polar8_eq]
  funext i
  fin_cases i <;> simp [mul8, ha7, hc7] <;> ring

theorem mul8_add_left (a a' b : Fin 8 → R) : mul8 (a + a') b = mul8 a b + mul8 a' b := by
  funext i
  fin_cases i <;> simp [mul8] <;> ring

theorem mul8_add_right (a b b' : Fin 8 → R) : mul8 a (b + b') = mul8 a b + mul8 a b' := by
  funext i
  fin_cases i <;> simp [mul8] <;> ring

theorem mul8_smul_left (c : R) (a b : Fin 8 → R) : mul8 (c • a) b = c • mul8 a b := by
  funext i
  fin_cases i <;> simp [mul8] <;> ring

theorem mul8_smul_right (c : R) (a b : Fin 8 → R) : mul8 a (c • b) = c • mul8 a b := by
  funext i
  fin_cases i <;> simp [mul8] <;> ring

variable (R) in
@[expose] def mul8Bil : (Fin 8 → R) →ₗ[R] (Fin 8 → R) →ₗ[R] (Fin 8 → R) :=
  LinearMap.mk₂ R mul8 mul8_add_left mul8_smul_left mul8_add_right mul8_smul_right

theorem mul8Bil_apply (a b : Fin 8 → R) : mul8Bil R a b = mul8 a b := rfl

theorem mul8_map {S : Type*} [CommRing S] (f : R →+* S) (a b : Fin 8 → R) :
    mul8 (fun i => f (a i)) (fun i => f (b i)) = fun i => f (mul8 a b i) := by
  funext i
  fin_cases i <;> simp [mul8]

theorem gram8_map {S : Type*} [CommRing S] (f : R →+* S) :
    (gram8 : Matrix (Fin 8) (Fin 8) R).map f = gram8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram8]

theorem one8_map {S : Type*} [CommRing S] (f : R →+* S) :
    (fun i => f ((one8 : Fin 8 → R) i)) = one8 := by
  funext i
  fin_cases i <;> simp [one8]

theorem gram8_mul_self : (gram8 : Matrix (Fin 8) (Fin 8) R) * gram8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram8, Matrix.mul_apply, Fin.sum_univ_eight]

theorem gram8_det_ne_zero [Nontrivial R] : (gram8 : Matrix (Fin 8) (Fin 8) R).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse gram8_mul_self

theorem one8_ne_zero [Nontrivial R] : (one8 : Fin 8 → R) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [one8] at this

end Coordinates

section Mat

variable {R : Type*} [CommRing R]

variable (R) in
@[expose] def zornMat (g : quasithinZorn R →ₗ[R] quasithinZorn R) : Matrix (Fin 8) (Fin 8) R :=
  LinearMap.toMatrix' ((zornCoord R).toLinearMap ∘ₗ g ∘ₗ (zornCoord R).symm.toLinearMap)

theorem zornMat_mulVec (g : quasithinZorn R →ₗ[R] quasithinZorn R) (a : Fin 8 → R) :
    zornMat R g *ᵥ a = zornCoord R (g ((zornCoord R).symm a)) := by
  rw [zornMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem zornMat_comp (g h : quasithinZorn R →ₗ[R] quasithinZorn R) :
    zornMat R (g ∘ₗ h) = zornMat R g * zornMat R h := by
  rw [zornMat, zornMat, zornMat, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun a => ?_
  simp

theorem zornMat_id : zornMat R LinearMap.id = 1 := by
  rw [zornMat, ← LinearMap.toMatrix'_id]
  congr 1
  refine LinearMap.ext fun a => ?_
  simp

variable (R) in
@[expose] def zornGL : (quasithinZorn R ≃ₗ[R] quasithinZorn R) →* GL (Fin 8) R where
  toFun g := ⟨zornMat R g.toLinearMap, zornMat R g.symm.toLinearMap,
    by
      rw [← zornMat_comp, ← zornMat_id]
      congr 1
      exact LinearMap.ext fun x => by simp,
    by
      rw [← zornMat_comp, ← zornMat_id]
      congr 1
      exact LinearMap.ext fun x => by simp⟩
  map_one' := Units.ext zornMat_id
  map_mul' g h := Units.ext (by
    change zornMat R (g * h).toLinearMap = zornMat R g.toLinearMap * zornMat R h.toLinearMap
    rw [← zornMat_comp]
    rfl)

theorem zornGL_mulVec (g : quasithinZorn R ≃ₗ[R] quasithinZorn R) (a : Fin 8 → R) :
    ((zornGL R g : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ a =
      zornCoord R (g ((zornCoord R).symm a)) :=
  zornMat_mulVec _ a

theorem zornGL_injective : Function.Injective (zornGL R) := by
  intro g h hgh
  refine LinearEquiv.ext fun x => ?_
  have := congrArg (fun M : GL (Fin 8) R => (M : Matrix (Fin 8) (Fin 8) R) *ᵥ zornCoord R x) hgh
  simp only [zornGL_mulVec, LinearEquiv.symm_apply_apply] at this
  exact (zornCoord R).injective this

theorem transpose_mul_mul_of_form {n : Type*} [Fintype n] [DecidableEq n]
    {M G : Matrix n n R} (h : ∀ v w, (M *ᵥ v) ⬝ᵥ (G *ᵥ (M *ᵥ w)) = v ⬝ᵥ (G *ᵥ w)) :
    Mᵀ * G * M = G := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec] at h1
  simpa [Matrix.mulVec_single_one, single_dotProduct] using h1

end Mat

section Cayley

variable {K : Type} [Field K] [CharP K 2]

theorem cayley_mul8 {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ cayleyGroup K)
    (a b : Fin 8 → K) :
    ((zornGL K g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *ᵥ mul8 a b =
      mul8 (((zornGL K g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *ᵥ a)
        (((zornGL K g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *ᵥ b) := by
  obtain ⟨-, hm, -, -⟩ := hg
  rw [zornGL_mulVec, zornGL_mulVec, zornGL_mulVec]
  have h1 : mul8 a b = zornCoord K (quasithinZornMul ((zornCoord K).symm a)
      ((zornCoord K).symm b)) := by
    rw [zornCoord_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [h1, LinearEquiv.symm_apply_apply, ← CFSG.Quasithin.G11.P3G2.cayleyMul_eq, hm,
    CFSG.Quasithin.G11.P3G2.cayleyMul_eq, zornCoord_mul]

theorem polar8_zornCoord (x y : quasithinZorn K) :
    zornCoord K x ⬝ᵥ (gram8 *ᵥ zornCoord K y) = cayleyPolar x y := by
  rw [polar8_eq, cayleyPolar_eq]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [zornCoord, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_three]
  simp
  linear_combination (-(x.2.1 0 * y.2.2.1 0 + y.2.1 0 * x.2.2.1 0 + x.2.1 1 * y.2.2.1 1 +
    y.2.1 1 * x.2.2.1 1 + x.2.1 2 * y.2.2.1 2 + y.2.1 2 * x.2.2.1 2)) * h2

theorem cayley_gram8 {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ cayleyGroup K) :
    ((zornGL K g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * gram8 *
      ((zornGL K g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) = gram8 := by
  obtain ⟨-, -, -, hn⟩ := hg
  refine transpose_mul_mul_of_form fun v w => ?_
  rw [zornGL_mulVec, zornGL_mulVec, polar8_zornCoord]
  have hv : v = zornCoord K ((zornCoord K).symm v) := (LinearEquiv.apply_symm_apply _ v).symm
  have hw : w = zornCoord K ((zornCoord K).symm w) := (LinearEquiv.apply_symm_apply _ w).symm
  conv_rhs => rw [hv, hw, polar8_zornCoord]
  simp only [cayleyPolar, ← map_add, hn]

omit [CharP K 2] in
theorem cayley_one8 {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ cayleyGroup K) :
    ((zornGL K g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *ᵥ one8 = one8 := by
  obtain ⟨h1, -, -, -⟩ := hg
  rw [zornGL_mulVec]
  have hone : (zornCoord K).symm one8 = cayleyOne K := by
    apply (zornCoord K).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    fin_cases i <;> rfl
  rw [hone, h1]
  funext i
  fin_cases i <;> rfl

end Cayley

theorem mul8_inv_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    {A : Matrix (Fin 8) (Fin 8) K} (hA : ∀ a b, A *ᵥ mul8 a b = mul8 (A *ᵥ a) (A *ᵥ b))
    (a b : Fin 8 → L) : A.map f *ᵥ mul8 a b = mul8 (A.map f *ᵥ a) (A.map f *ᵥ b) := by
  have hs : ∀ k : Fin 8, (Pi.single k (1 : L) : Fin 8 → L) =
      fun l => f ((Pi.single k (1 : K) : Fin 8 → K) l) := by
    intro k
    funext l
    by_cases h : l = k
    · subst h
      simp
    · simp [h]
  have hmv : ∀ w : Fin 8 → K, A.map f *ᵥ (fun l => f (w l)) = fun l => f ((A *ᵥ w) l) := by
    intro w
    funext l
    rw [RingHom.map_mulVec]
    rfl
  have hB : (mul8Bil L).compr₂ (Matrix.toLin' (A.map f)) =
      (mul8Bil L).compl₁₂ (Matrix.toLin' (A.map f)) (Matrix.toLin' (A.map f)) := by
    refine LinearMap.ext_basis (Pi.basisFun L (Fin 8)) (Pi.basisFun L (Fin 8)) fun i j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, mul8Bil_apply,
      Pi.basisFun_apply, Matrix.toLin'_apply]
    rw [hs i, hs j, mul8_map, hmv, hmv, hmv, hA, mul8_map]
  have := LinearMap.congr_fun₂ hB a b
  simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, mul8Bil_apply,
    Matrix.toLin'_apply] using this

theorem card_le_nine_zorn_of_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (h3 : (3 : L) ≠ 0) (E : Subgroup (GL (Fin 8) L)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hform : ∀ x ∈ E, (x : Matrix (Fin 8) (Fin 8) L)ᵀ * gram8 * (x : Matrix (Fin 8) (Fin 8) L) =
      gram8)
    (hmul : ∀ x ∈ E, ∀ a b, (x : Matrix (Fin 8) (Fin 8) L) *ᵥ mul8 a b =
      mul8 ((x : Matrix (Fin 8) (Fin 8) L) *ᵥ a) ((x : Matrix (Fin 8) (Fin 8) L) *ᵥ b))
    (hone : ∀ x ∈ E, (x : Matrix (Fin 8) (Fin 8) L) *ᵥ one8 = one8) : Nat.card E ≤ 9 := by
  obtain ⟨b, d, hb⟩ := Sec4.exists_common_eigenbasis_pow_three h3 E hcomm hexp
  have htr : ∀ a, (∃ x ∈ E, d x a ≠ 1) → b a 0 + b a 7 = 0 := by
    rintro a ⟨x, hx, hne⟩
    have h1 := form_mulVec_mulVec' (hform x hx) (b a) one8
    rw [hb x hx a, hone x hx, smul_dotProduct, smul_eq_mul] at h1
    have h2 : (d x a - 1) * (b a ⬝ᵥ (gram8 *ᵥ one8)) = 0 := by linear_combination h1
    have h4 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
    rw [polar8_eq] at h4
    simpa [one8] using h4
  obtain ⟨a₀, ha₀⟩ := exists_index_of_eigen hb one8_ne_zero (c := fun _ => 1)
    (fun x hx => by rw [hone x hx, one_smul])
  refine card_le_nine_of_eigen hexp hb gram8 gram8_det_ne_zero hform mul8 mul8_smul_left
    mul8_smul_right hmul (-1) (by norm_num) (fun a c e ha hc _ _ => ?_) ?_
  · have hca : ∃ x ∈ E, d x c ≠ 1 := by
      obtain ⟨x, hx, hne⟩ := ha
      refine ⟨x, hx, fun h => hne ?_⟩
      rw [hc x hx] at h
      exact inv_eq_one.mp h
    rw [mul8_mul8 (b a) (b c) (b e) (htr a ha) (htr c hca), neg_one_mul]
  · have hinj : Function.Injective fun (a : {a // ∃ x ∈ E, d x a ≠ 1}) =>
        (⟨a.1, fun h => by
          obtain ⟨x, hx, hne⟩ := a.2
          exact hne (h ▸ ha₀ x hx)⟩ : {a : Fin 8 // a ≠ a₀}) :=
      fun a a' h => Subtype.ext (congrArg (fun z : {a : Fin 8 // a ≠ a₀} => z.1) h)
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

theorem cayleyGroup_card_le_nine {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : Subgroup ↥(cayleyGroup K)) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    Nat.card F ≤ 9 := by
  set L := AlgebraicClosure K
  set ρ : ↥(cayleyGroup K) →* GL (Fin 8) L :=
    (Matrix.GeneralLinearGroup.map (algebraMap K L)).comp
      ((zornGL K).comp (cayleyGroup K).subtype) with hρ
  have hinj₀ : Function.Injective ((zornGL K).comp (cayleyGroup K).subtype) :=
    zornGL_injective.comp Subtype.val_injective
  have hρinj : Function.Injective ρ := (Sec4.map_injective_GL _).comp hinj₀
  have : Finite ↥(cayleyGroup K) := Finite.of_injective _ hinj₀
  have : Finite (F.map ρ) := Finite.of_surjective _ (ρ.subgroupMap_surjective F)
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have h3 : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  have hcommF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hval : ∀ x : ↥(cayleyGroup K), ((ρ x : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) =
      ((zornGL K x.1 : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K).map (algebraMap K L) :=
    fun _ => rfl
  have h := card_le_nine_zorn_of_isAlgClosed h3 (F.map ρ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcommF x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hF.2 x hx, map_one])
    (by
      rintro _ ⟨x, -, rfl⟩
      rw [hval, ← Matrix.transpose_map, ← gram8_map (algebraMap K L), ← Matrix.map_mul,
        ← Matrix.map_mul, cayley_gram8 x.2])
    (by
      rintro _ ⟨x, -, rfl⟩ a b
      rw [hval]
      exact mul8_inv_map (algebraMap K L) (cayley_mul8 x.2) a b)
    (by
      rintro _ ⟨x, -, rfl⟩
      rw [hval, ← one8_map (algebraMap K L)]
      funext l
      have h1 := RingHom.map_mulVec (algebraMap K L)
        ((zornGL K x.1 : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) one8 l
      rw [cayley_one8 x.2] at h1
      exact h1.symm)
  rwa [Subgroup.card_map_of_injective hρinj] at h

end CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
