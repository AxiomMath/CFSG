module

public import CFSG.Quasithin.Background.SmithB49Act
public import CFSG.Quasithin.Background.SmithB51LnReal
public import CFSG.Quasithin.Background.B3ThreeBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.B49

open Matrix CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln

theorem exists_section {X W : Type*} [CommGroup X] [CommGroup W] (hX : ∀ x : X, x ^ 2 = 1)
    (f : X →* W) (hf : Function.Surjective f) : ∃ s : W →* X, ∀ w, f (s w) = w := by
  obtain ⟨S, hS1, hS2⟩ := CFSG.Quasithin.B3.exists_complement hX f.ker
  have hinj : Function.Injective (f.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : (s : X) ∈ f.ker ⊓ S := ⟨hs, s.2⟩
    rw [hS1, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective (f.comp S.subtype) := by
    intro w
    obtain ⟨m, rfl⟩ := hf w
    have hm : m ∈ f.ker ⊔ S := by rw [hS2]; exact Subgroup.mem_top m
    obtain ⟨k, hk, s, hs, rfl⟩ := Subgroup.mem_sup.1 hm
    refine ⟨⟨s, hs⟩, ?_⟩
    show f s = f (k * s)
    rw [map_mul, MonoidHom.mem_ker.1 hk, one_mul]
  let e : ↥S ≃* W := MulEquiv.ofBijective (f.comp S.subtype) ⟨hinj, hsurj⟩
  refine ⟨S.subtype.comp e.symm.toMonoidHom, fun w => ?_⟩
  show f ((e.symm w : ↥S) : X) = w
  exact e.apply_symm_apply w

variable {V : Type} [CommGroup V] {n : ℕ}

structure ExtData (L : Subgroup (MulAut V)) (U : Subgroup V)
    (π : ↥(StatedSL n (ZMod 2)) →* ↥L)
    (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2)) where
  b : ↥U ≃* Multiplicative (Fin n → ZMod 2)
  q : V →* Multiplicative (Fin n → ZMod 2)
  s : Multiplicative (Fin n → ZMod 2) →* V
  surj : Function.Surjective π
  hLU : ∀ (l : ↥L), ∀ u ∈ U, (l : MulAut V) u ∈ U
  b_eq : ∀ (γ : ↥(StatedSL n (ZMod 2))) (u : ↥U),
    Multiplicative.toAdd (b ⟨((π γ : ↥L) : MulAut V) u, hLU _ u u.2⟩) =
      mat γ *ᵥ Multiplicative.toAdd (b u)
  q_ker : ∀ v, q v = 1 ↔ v ∈ U
  q_eq : ∀ (γ : ↥(StatedSL n (ZMod 2))) (v : V),
    Multiplicative.toAdd (q (((π γ : ↥L) : MulAut V) v)) = M γ *ᵥ Multiplicative.toAdd (q v)
  qs : ∀ m, q (s m) = m

variable {L : Subgroup (MulAut V)} {U : Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
  {M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2)}

theorem ExtData.exists (hV : ∀ v : V, v ^ 2 = 1) (hU : RealM L U ⊥ π mat)
    (hQ : RealM L ⊤ U π M) : Nonempty (ExtData L U π M) := by
  obtain ⟨hπ, -, hLU, -, β, hβs, hβk, hβe⟩ := hU
  obtain ⟨-, -, -, -, β', hβ's, hβ'k, hβ'e⟩ := hQ
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  let q : V →* Multiplicative (Fin n → ZMod 2) :=
    β'.comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom
  have hq : ∀ v, q v = β' ⟨v, Subgroup.mem_top v⟩ := fun v => rfl
  have hqs : Function.Surjective q := by
    intro m
    obtain ⟨⟨v, hv⟩, hvm⟩ := hβ's m
    exact ⟨v, hvm⟩
  obtain ⟨s, hs⟩ := exists_section hV q hqs
  exact ⟨{ b := MulEquiv.ofBijective β ⟨hβi, hβs⟩
           q := q
           s := s
           surj := hπ
           hLU := hLU
           b_eq := fun γ u => hβe γ u _
           q_ker := fun v => by rw [hq]; exact hβ'k _
           q_eq := fun γ v => by rw [hq, hq]; exact hβ'e γ ⟨v, Subgroup.mem_top v⟩ _
           qs := hs }⟩

namespace ExtData

variable (D : ExtData L U π M)

theorem M_inv_mul (γ : ↥(StatedSL n (ZMod 2))) : M γ⁻¹ * M γ = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem M_mul_inv (γ : ↥(StatedSL n (ZMod 2))) : M γ * M γ⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem b_eq' (γ : ↥(StatedSL n (ZMod 2))) {x : V} (hx : x ∈ U) :
    Multiplicative.toAdd (D.b ⟨((π γ : ↥L) : MulAut V) x, D.hLU _ x hx⟩) =
      mat γ *ᵥ Multiplicative.toAdd (D.b ⟨x, hx⟩) :=
  D.b_eq γ ⟨x, hx⟩

@[expose] def wv (γ : ↥(StatedSL n (ZMod 2))) (m : Fin n → ZMod 2) : V :=
  ((π γ : ↥L) : MulAut V) (D.s (Multiplicative.ofAdd (M γ⁻¹ *ᵥ m))) *
    (D.s (Multiplicative.ofAdd m))⁻¹

theorem wv_mem (γ : ↥(StatedSL n (ZMod 2))) (m : Fin n → ZMod 2) : D.wv γ m ∈ U := by
  rw [← D.q_ker]
  apply Multiplicative.toAdd.injective
  rw [wv, map_mul, map_inv D.q, toAdd_mul, toAdd_inv, D.q_eq, D.qs, D.qs, toAdd_ofAdd,
    toAdd_ofAdd, mulVec_mulVec, M_mul_inv, one_mulVec, add_neg_cancel, toAdd_one]

@[expose] def cv (γ : ↥(StatedSL n (ZMod 2))) (m : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  Multiplicative.toAdd (D.b ⟨D.wv γ m, D.wv_mem γ m⟩)

theorem wv_add (γ : ↥(StatedSL n (ZMod 2))) (m m' : Fin n → ZMod 2) :
    D.wv γ (m + m') = D.wv γ m * D.wv γ m' := by
  simp only [wv, mulVec_add, ofAdd_add, map_mul, mul_inv]
  rw [mul_mul_mul_comm]

theorem cv_add (γ : ↥(StatedSL n (ZMod 2))) (m m' : Fin n → ZMod 2) :
    D.cv γ (m + m') = D.cv γ m + D.cv γ m' := by
  unfold cv
  rw [← toAdd_mul, ← map_mul]
  congr 2
  exact Subtype.ext (D.wv_add γ m m')

@[expose] def cvHom (γ : ↥(StatedSL n (ZMod 2))) : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
  AddMonoidHom.mk' (D.cv γ) (D.cv_add γ)

@[expose] noncomputable def cmat (γ : ↥(StatedSL n (ZMod 2))) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  LinearMap.toMatrix' (AddMonoidHom.toZModLinearMap 2 (D.cvHom γ))

theorem cmat_mulVec (γ : ↥(StatedSL n (ZMod 2))) (m : Fin n → ZMod 2) :
    D.cmat γ *ᵥ m = D.cv γ m := by
  rw [cmat, LinearMap.toMatrix'_mulVec]
  rfl

theorem wv_mul (γ δ : ↥(StatedSL n (ZMod 2))) (m : Fin n → ZMod 2) :
    D.wv (γ * δ) m = ((π γ : ↥L) : MulAut V) (D.wv δ (M γ⁻¹ *ᵥ m)) * D.wv γ m := by
  simp only [wv, _root_.mul_inv_rev, map_mul, Subgroup.coe_mul, MulAut.mul_apply, ← mulVec_mulVec,
    map_inv]
  group

theorem cv_mul (γ δ : ↥(StatedSL n (ZMod 2))) (m : Fin n → ZMod 2) :
    D.cv (γ * δ) m = D.cv γ m + mat γ *ᵥ D.cv δ (M γ⁻¹ *ᵥ m) := by
  unfold cv
  have h1 : (⟨D.wv (γ * δ) m, D.wv_mem _ m⟩ : ↥U) =
      ⟨((π γ : ↥L) : MulAut V) (D.wv δ (M γ⁻¹ *ᵥ m)), D.hLU _ _ (D.wv_mem δ _)⟩ *
        ⟨D.wv γ m, D.wv_mem γ m⟩ := Subtype.ext (D.wv_mul γ δ m)
  rw [h1, map_mul, toAdd_mul, add_comm]
  congr 1
  exact D.b_eq γ ⟨D.wv δ (M γ⁻¹ *ᵥ m), D.wv_mem δ _⟩

theorem cmat_mul (γ δ : ↥(StatedSL n (ZMod 2))) :
    D.cmat (γ * δ) = D.cmat γ + mat γ * D.cmat δ * M γ⁻¹ := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro m
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    cmat_mulVec, cmat_mulVec, cmat_mulVec, cv_mul]

@[expose] noncomputable def coc (γ : ↥(StatedSL n (ZMod 2))) : Fin n × Fin n → ZMod 2 :=
  (D.cmat γ).vec

theorem coc_mem : D.coc ∈ Z1A (muK M) := by
  intro γ δ
  show (D.cmat (γ * δ)).vec = (D.cmat γ).vec + muK M γ (D.cmat δ).vec
  rw [muK_vec, cmat_mul, vec_add]

@[expose] def unvec (x : Fin n × Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => x (j, i)

theorem vec_unvec (x : Fin n × Fin n → ZMod 2) : (unvec x).vec = x := by
  funext p
  rfl

@[expose] noncomputable def tX (X : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Multiplicative (Fin n → ZMod 2) →* V :=
  U.subtype.comp (D.b.symm.toMonoidHom.comp
    (AddMonoidHom.toMultiplicative (Matrix.mulVecLin X).toAddMonoidHom))

theorem tX_mem (X : Matrix (Fin n) (Fin n) (ZMod 2)) (m : Multiplicative (Fin n → ZMod 2)) :
    D.tX X m ∈ U := (D.b.symm _).2

theorem b_tX (X : Matrix (Fin n) (Fin n) (ZMod 2)) (m : Multiplicative (Fin n → ZMod 2)) :
    D.b ⟨D.tX X m, D.tX_mem X m⟩ = Multiplicative.ofAdd (X *ᵥ Multiplicative.toAdd m) := by
  have : (⟨D.tX X m, D.tX_mem X m⟩ : ↥U) =
      D.b.symm (Multiplicative.ofAdd (X *ᵥ Multiplicative.toAdd m)) := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem equiv_of_cob {X : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hX : ∀ γ, D.cmat γ = mat γ * X * M γ⁻¹ - X) (γ : ↥(StatedSL n (ZMod 2)))
    (m : Fin n → ZMod 2) :
    ((π γ : ↥L) : MulAut V) ((D.s * (D.tX X)⁻¹) (Multiplicative.ofAdd (M γ⁻¹ *ᵥ m))) =
      (D.s * (D.tX X)⁻¹) (Multiplicative.ofAdd m) := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  have hw : ((π γ : ↥L) : MulAut V) (D.s (Multiplicative.ofAdd (M γ⁻¹ *ᵥ m))) =
      D.wv γ m * D.s (Multiplicative.ofAdd m) := by
    rw [wv, inv_mul_cancel_right]
  have ht : D.wv γ m = ((π γ : ↥L) : MulAut V) (D.tX X (Multiplicative.ofAdd (M γ⁻¹ *ᵥ m))) *
      (D.tX X (Multiplicative.ofAdd m))⁻¹ := by
    have hmem : ((π γ : ↥L) : MulAut V) (D.tX X (Multiplicative.ofAdd (M γ⁻¹ *ᵥ m))) *
        (D.tX X (Multiplicative.ofAdd m))⁻¹ ∈ U :=
      U.mul_mem (D.hLU _ _ (D.tX_mem X _)) (U.inv_mem (D.tX_mem X _))
    have key : D.b ⟨D.wv γ m, D.wv_mem γ m⟩ = D.b ⟨_, hmem⟩ := by
      apply Multiplicative.toAdd.injective
      have e1 : (⟨_, hmem⟩ : ↥U) = ⟨((π γ : ↥L) : MulAut V) (D.tX X (Multiplicative.ofAdd
          (M γ⁻¹ *ᵥ m))), D.hLU _ _ (D.tX_mem X _)⟩ * (⟨D.tX X (Multiplicative.ofAdd m),
            D.tX_mem X _⟩)⁻¹ := rfl
      rw [e1, map_mul, map_inv D.b, toAdd_mul, toAdd_inv, D.b_eq' γ (D.tX_mem X _), b_tX,
        b_tX]
      change D.cv γ m = _
      rw [← cmat_mulVec, hX, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, sub_mulVec, ← mulVec_mulVec,
        ← mulVec_mulVec, sub_eq_add_neg]
      rfl
    exact congrArg Subtype.val (D.b.injective key)
  rw [hw, ht]
  set a := ((π γ : ↥L) : MulAut V) (D.tX X (Multiplicative.ofAdd (M γ⁻¹ *ᵥ m)))
  set b := D.tX X (Multiplicative.ofAdd m)
  set c := D.s (Multiplicative.ofAdd m)
  calc a * b⁻¹ * c * a⁻¹ = (a * a⁻¹) * (c * b⁻¹) := by ac_rfl
    _ = c * b⁻¹ := by rw [mul_inv_cancel, one_mul]

theorem split (h : D.coc ∈ B1A (muK M)) :
    ∃ X : Subgroup V, (∀ l ∈ L, ∀ x ∈ X, l x ∈ X) ∧ IsIntDirect U X ⊤ := by
  obtain ⟨x, hx⟩ := h
  set X := unvec x
  have hX : ∀ γ, D.cmat γ = mat γ * X * M γ⁻¹ - X := by
    intro γ
    have h1 := congrFun hx γ
    rw [coboundaryA_apply, ← vec_unvec x, muK_vec] at h1
    rw [← vec_inj, vec_sub]
    exact h1.symm
  set s' : Multiplicative (Fin n → ZMod 2) →* V := D.s * (D.tX X)⁻¹
  have hs'q : ∀ m, D.q (s' m) = m := by
    intro m
    have h1 : D.q (D.tX X m) = 1 := (D.q_ker _).2 (D.tX_mem X m)
    simp only [s', MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, D.qs, h1,
      inv_one, mul_one]
  have hequiv : ∀ γ m, ((π γ : ↥L) : MulAut V) (s' m) =
      s' (Multiplicative.ofAdd (M γ *ᵥ Multiplicative.toAdd m)) := by
    intro γ m
    have h1 := D.equiv_of_cob hX γ (M γ *ᵥ Multiplicative.toAdd m)
    rw [mulVec_mulVec, M_inv_mul, one_mulVec, ofAdd_toAdd] at h1
    exact h1
  refine ⟨s'.range, ?_, ?_, ?_⟩
  · rintro l hl _ ⟨m, rfl⟩
    obtain ⟨γ, hγ⟩ := D.surj ⟨l, hl⟩
    have : l = ((π γ : ↥L) : MulAut V) := by rw [hγ]
    rw [this, hequiv]
    exact ⟨_, rfl⟩
  · rw [eq_top_iff]
    intro v _
    have hu : v * (s' (D.q v))⁻¹ ∈ U := by
      rw [← D.q_ker, map_mul, map_inv, hs'q, mul_inv_cancel]
    have : v = v * (s' (D.q v))⁻¹ * s' (D.q v) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hu ⟨_, rfl⟩
  · rw [eq_bot_iff]
    rintro v ⟨hvU, m, rfl⟩
    rw [Subgroup.mem_bot]
    have h1 := (D.q_ker _).2 hvU
    rw [hs'q] at h1
    rw [h1, map_one]

theorem sub_mem_U (v : V) : v * (D.s (D.q v))⁻¹ ∈ U := by
  rw [← D.q_ker, map_mul, map_inv, D.qs, mul_inv_cancel]

theorem fixed {γ : ↥(StatedSL n (ZMod 2))} {v : V}
    (hq : M γ *ᵥ Multiplicative.toAdd (D.q v) = Multiplicative.toAdd (D.q v))
    (hv : ((π γ : ↥L) : MulAut V) v = v) :
    D.cmat γ *ᵥ Multiplicative.toAdd (D.q v) =
      Multiplicative.toAdd (D.b ⟨_, D.sub_mem_U v⟩) -
        mat γ *ᵥ Multiplicative.toAdd (D.b ⟨_, D.sub_mem_U v⟩) := by
  set m := Multiplicative.toAdd (D.q v) with hm
  have hq' : M γ⁻¹ *ᵥ m = m := by
    conv_lhs => rw [← hq]
    rw [mulVec_mulVec, M_inv_mul, one_mulVec]
  have hw : D.wv γ m = (((π γ : ↥L) : MulAut V) (v * (D.s (D.q v))⁻¹))⁻¹ *
      (v * (D.s (D.q v))⁻¹) := by
    rw [wv, hq', hm, ofAdd_toAdd]
    simp only [map_mul, map_inv, hv]
    group
  have key : (⟨D.wv γ m, D.wv_mem γ m⟩ : ↥U) =
      (⟨((π γ : ↥L) : MulAut V) (v * (D.s (D.q v))⁻¹), D.hLU _ _ (D.sub_mem_U v)⟩)⁻¹ *
        ⟨_, D.sub_mem_U v⟩ := Subtype.ext (by
          show D.wv γ m = _
          rw [hw]
          rfl)
  rw [cmat_mulVec, cv, key, map_mul, map_inv D.b, toAdd_mul, toAdd_inv, D.b_eq' γ (D.sub_mem_U v)]
  abel

end ExtData

end CFSG.Quasithin.B5.B49
