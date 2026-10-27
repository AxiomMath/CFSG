module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Quasithin

variable {n : ℕ}

section Mat

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))

@[expose] noncomputable def matOfN : (V ≃ₗ[ZMod 2] V) →* GL (Fin n) (ZMod 2) where
  toFun ψ :=
    { val := LinearMap.toMatrix' (e.symm.trans (ψ.trans e)).toLinearMap
      inv := LinearMap.toMatrix' (e.symm.trans (ψ.symm.trans e)).toLinearMap
      val_inv := by
        rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
        congr 1
        ext v i
        simp
      inv_val := by
        rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
        congr 1
        ext v i
        simp }
  map_one' := Units.ext (by
    show LinearMap.toMatrix' _ = 1
    rw [← LinearMap.toMatrix'_id]
    congr 1
    ext v i
    simp)
  map_mul' ψ χ := Units.ext (by
    show LinearMap.toMatrix' _ = LinearMap.toMatrix' _ * LinearMap.toMatrix' _
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    ext v i
    simp)

theorem matOfN_mulVec (ψ : V ≃ₗ[ZMod 2] V) (v : V) :
    ((matOfN e ψ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) =
      e (ψ v) := by
  show (LinearMap.toMatrix' (e.symm.trans (ψ.trans e)).toLinearMap).mulVec (e v) = e (ψ v)
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem matOfN_mulVec' (ψ : V ≃ₗ[ZMod 2] V) (x : Fin n → ZMod 2) :
    ((matOfN e ψ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec x =
      e (ψ (e.symm x)) := by
  rw [← matOfN_mulVec, LinearEquiv.apply_symm_apply]

theorem matOfN_eq_iff (ψ : V ≃ₗ[ZMod 2] V) (γ : GL (Fin n) (ZMod 2)) :
    matOfN e ψ = γ ↔ ∀ v, e (ψ v) = (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) := by
  constructor
  · rintro rfl v
    rw [matOfN_mulVec]
  · intro h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, matOfN_mulVec', h, LinearEquiv.apply_symm_apply]

theorem matOfN_injective : Function.Injective (matOfN e) := by
  intro ψ χ h
  ext v
  apply e.injective
  rw [← matOfN_mulVec, ← matOfN_mulVec, h]

end Mat

section Img

variable {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)
  (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2))

@[expose] noncomputable def imgN (Y : Subgroup G) : Subgroup (GL (Fin n) (ZMod 2)) :=
  (D.img Y).map (matOfN e)

@[expose] noncomputable def homN {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G)) :
    ↥Y →* GL (Fin n) (ZMod 2) :=
  (matOfN e).comp (D.ρ.comp (Subgroup.inclusion hY))

theorem mem_imgN {Y : Subgroup G} {γ : GL (Fin n) (ZMod 2)} :
    γ ∈ imgN D e Y ↔ ∃ y ∈ Y, ∃ hy : y ∈ Subgroup.normalizer (U : Set G),
      matOfN e (D.ρ ⟨y, hy⟩) = γ := by
  unfold imgN
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨y, hyY, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp hψ
    exact ⟨y, hyY, hyN, rfl⟩
  · rintro ⟨y, hyY, hyN, rfl⟩
    exact ⟨_, L128A.HatU.rho_mem_img D hyY hyN, rfl⟩

theorem range_homN {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G)) :
    (homN D e hY).range = imgN D e Y := by
  ext γ
  rw [MonoidHom.mem_range, mem_imgN]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, hY y.2, rfl⟩
  · rintro ⟨y, hyY, hyN, rfl⟩
    exact ⟨⟨y, hyY⟩, rfl⟩

theorem imgN_mono {Y Y' : Subgroup G} (h : Y ≤ Y') : imgN D e Y ≤ imgN D e Y' := by
  intro γ hγ
  obtain ⟨y, hy, hyN, rfl⟩ := (mem_imgN D e).mp hγ
  exact (mem_imgN D e).mpr ⟨y, h hy, hyN, rfl⟩

theorem card_imgN (Y : Subgroup G) : Nat.card (imgN D e Y) = Nat.card (D.img Y) :=
  Nat.card_congr ((D.img Y).equivMapOfInjective _ (matOfN_injective e)).toEquiv.symm

theorem imgN_eq_map (Y : Subgroup G) :
    imgN D e Y = (Y.subgroupOf (Subgroup.normalizer (U : Set G))).map ((matOfN e).comp D.ρ) := by
  unfold imgN HatModelU.img
  rw [Subgroup.map_map]

theorem imgN_sup {Y Y' : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G))
    (hY' : Y' ≤ Subgroup.normalizer (U : Set G)) :
    imgN D e (Y ⊔ Y') = imgN D e Y ⊔ imgN D e Y' := by
  rw [imgN_eq_map D e (Y ⊔ Y'), imgN_eq_map D e Y, imgN_eq_map D e Y',
    Subgroup.subgroupOf_sup hY hY', Subgroup.map_sup]

theorem imgN_oTwoUpper [Finite G] {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G)) :
    imgN D e (oTwoUpper Y) = oTwoUpper (imgN D e Y) := by
  rw [imgN_eq_map D e (oTwoUpper Y), imgN_eq_map D e Y,
    ← A4.oTwoUpper_subgroupOf hY, oTwoUpper_map]

end Img

@[expose] noncomputable def linOfN (c : GL (Fin n) (ZMod 2)) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (c : Matrix (Fin n) (Fin n) (ZMod 2)))
    (Matrix.toLin' ((c⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

theorem linOfN_apply (c : GL (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    linOfN c x = (c : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec x := rfl

section Coords

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))

theorem matOfN_trans (c : GL (Fin n) (ZMod 2)) (ψ : V ≃ₗ[ZMod 2] V) :
    matOfN (e.trans (linOfN c)) ψ = c * matOfN e ψ * c⁻¹ := by
  rw [matOfN_eq_iff]
  intro v
  simp only [LinearEquiv.trans_apply, linOfN_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec (e v) ((c⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
    (c : Matrix (Fin n) (Fin n) (ZMod 2)), ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec, matOfN_mulVec]

end Coords

theorem imgN_trans {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)
    (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (c : GL (Fin n) (ZMod 2)) (Y : Subgroup G) :
    imgN D (e.trans (linOfN c)) Y = (imgN D e Y).map (MulAut.conj c).toMonoidHom := by
  unfold imgN
  rw [Subgroup.map_map]
  congr 1
  ext ψ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [matOfN_trans]

end CFSG.Quasithin.H13.L14411
