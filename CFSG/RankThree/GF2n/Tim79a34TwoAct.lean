module

public import CFSG.RankThree.GF2n.Tim79a34TwoSpace

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoSpace

open CFSG.RankThree.GF2n.Tim79a.TwoModel

theorem zmod2_eq_of_iff_zero : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by
  decide

section Aux

variable {G : Type} [Group G] {P V M : Subgroup G} {θ : P → Vec4}

@[expose] def conjP (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P) (m : M) (p : P) : P :=
  ⟨(m : G) * p * (m : G)⁻¹, hMP m m.2 p p.2⟩

theorem conjP_mul (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P) (m : M) (p q : P) :
    conjP hMP m (p * q) = conjP hMP m p * conjP hMP m q := by
  apply Subtype.ext
  simp only [conjP, Subgroup.coe_mul]
  group

theorem conjP_one (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P) (p : P) :
    conjP hMP 1 p = p := by
  apply Subtype.ext
  simp [conjP]

theorem conjP_comp (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P) (m m' : M) (p : P) :
    conjP hMP (m * m') p = conjP hMP m (conjP hMP m' p) := by
  apply Subtype.ext
  simp only [conjP, Subgroup.coe_mul]
  group

theorem conjP_congr (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (m : M) (p p' : P) (hpp : θ p = θ p') :
    θ (conjP hMP m p) = θ (conjP hMP m p') := by
  have h1 : θ (p' * (p'⁻¹ * p)) = θ p' + θ (p'⁻¹ * p) := h.add p' (p'⁻¹ * p)
  rw [mul_inv_cancel_left, hpp] at h1
  have hq : θ (p'⁻¹ * p) = 0 := left_eq_add.mp h1
  have hV : ((p'⁻¹ * p : P) : G) ∈ V := (h.ker _).mp hq
  have hcq : θ (conjP hMP m (p'⁻¹ * p)) = 0 := (h.ker _).mpr (hMV m m.2 _ hV)
  have e : conjP hMP m p = conjP hMP m p' * conjP hMP m (p'⁻¹ * p) := by
    rw [← conjP_mul hMP, mul_inv_cancel_left]
  rw [e, h.add, hcq, add_zero]

@[expose] noncomputable def actFun (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (m : M) (x : Vec4) : Vec4 :=
  θ (conjP hMP m (Function.surjInv h.surj x))

theorem actFun_apply (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (m : M) (p : P) :
    actFun h hMP m (θ p) = θ (conjP hMP m p) :=
  conjP_congr h hMP hMV m (Function.surjInv h.surj (θ p)) p
    (Function.surjInv_eq h.surj (θ p))

theorem actFun_mul (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (m m' : M) (x : Vec4) :
    actFun h hMP (m * m') x = actFun h hMP m (actFun h hMP m' x) := by
  obtain ⟨p, rfl⟩ := h.surj x
  rw [actFun_apply h hMP hMV m' p, actFun_apply h hMP hMV m (conjP hMP m' p),
    actFun_apply h hMP hMV (m * m') p, conjP_comp hMP m m' p]

theorem actFun_one (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (x : Vec4) :
    actFun h hMP 1 x = x := by
  obtain ⟨p, rfl⟩ := h.surj x
  rw [actFun_apply h hMP hMV 1 p, conjP_one hMP p]

theorem actFun_add (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (m : M) (x y : Vec4) :
    actFun h hMP m (x + y) = actFun h hMP m x + actFun h hMP m y := by
  obtain ⟨p, rfl⟩ := h.surj x
  obtain ⟨q, rfl⟩ := h.surj y
  rw [← h.add p q, actFun_apply h hMP hMV m (p * q), actFun_apply h hMP hMV m p,
    actFun_apply h hMP hMV m q, conjP_mul hMP m p q, h.add]

theorem actFun_qf (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (m : M) (x : Vec4) :
    qf (actFun h hMP m x) = qf x := by
  obtain ⟨p, rfl⟩ := h.surj x
  rw [actFun_apply h hMP hMV m p]
  apply zmod2_eq_of_iff_zero
  rw [← h.sq (conjP hMP m p), ← h.sq p]
  have e : ((conjP hMP m p : P) : G) * ((conjP hMP m p : P) : G)
      = (m : G) * ((p : G) * (p : G)) * (m : G)⁻¹ := by
    simp only [conjP]
    group
  rw [e]
  exact conj_eq_one_iff

@[expose] noncomputable def actEquiv (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (m : M) : Equiv.Perm Vec4 where
  toFun := actFun h hMP m
  invFun := actFun h hMP m⁻¹
  left_inv x := by
    show actFun h hMP m⁻¹ (actFun h hMP m x) = x
    rw [← actFun_mul h hMP hMV, inv_mul_cancel, actFun_one h hMP hMV]
  right_inv x := by
    show actFun h hMP m (actFun h hMP m⁻¹ x) = x
    rw [← actFun_mul h hMP hMV, mul_inv_cancel, actFun_one h hMP hMV]

theorem actEquiv_isIsom4 (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) (m : M) :
    IsIsom4 (actEquiv h hMP hMV m) :=
  ⟨fun x y => actFun_add h hMP hMV m x y, fun x => actFun_qf h hMP hMV m x⟩

@[expose] noncomputable def actHom (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) : M →* Equiv.Perm Vec4 :=
  MonoidHom.mk' (actEquiv h hMP hMV) fun m m' => by
    refine Equiv.ext fun x => ?_
    rw [Equiv.Perm.mul_apply]
    exact actFun_mul h hMP hMV m m' x

end Aux

theorem exists_act {G : Type} [Group G] {P V M : Subgroup G} {θ : P → Vec4}
    (h : PCoords P V θ) (hMP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hMV : ∀ m ∈ M, ∀ z ∈ V, m * z * m⁻¹ ∈ V) :
    ∃ act : M →* Equiv.Perm Vec4, (∀ m : M, IsIsom4 (act m)) ∧
      ∀ (m : M) (p : P) (hp : (m : G) * p * (m : G)⁻¹ ∈ P),
        θ ⟨(m : G) * p * (m : G)⁻¹, hp⟩ = act m (θ p) := by
  refine ⟨actHom h hMP hMV, fun m => actEquiv_isIsom4 h hMP hMV m, fun m p hp => ?_⟩
  exact (actFun_apply h hMP hMV m p).symm

end CFSG.RankThree.GF2n.Tim79a.TwoSpace
