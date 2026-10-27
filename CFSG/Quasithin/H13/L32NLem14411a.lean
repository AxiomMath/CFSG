module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Quasithin

section PCore

variable {A Γ : Type*} [Group A] [Group Γ]

theorem pCore_eq_ker_of_surj [Finite A] (f : A →* Γ) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hΓ : ∀ N : Subgroup Γ, N.Normal → IsPGroup 2 N → N = ⊥) :
    CFSG.Open.pCore 2 A = f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker f) hk)
  have hN : ((CFSG.Open.pCore 2 A).map f).Normal :=
    (CFSG.LieType.BorelTits.pCore_normal (G := A) (r := 2)).map f hf
  have hP : IsPGroup 2 ↥((CFSG.Open.pCore 2 A).map f) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := A) (r := 2)).map f
  have h := hΓ _ hN hP
  intro x hx
  rw [MonoidHom.mem_ker]
  have : f x ∈ (CFSG.Open.pCore 2 A).map f := ⟨x, hx, rfl⟩
  rw [h] at this
  exact this

theorem nonempty_quot_equiv_of_surj [Finite A] (f : A →* Γ) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hΓ : ∀ N : Subgroup Γ, N.Normal → IsPGroup 2 N → N = ⊥) :
    Nonempty (A ⧸ CFSG.Open.pCore 2 A ≃* Γ) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (pCore_eq_ker_of_surj f hf hk hΓ)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem pCore_eq_comap_of_surj {B : Type*} [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    CFSG.Open.pCore 2 A = (CFSG.Open.pCore 2 B).comap f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective f hf
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mp (CFSG.LieType.BorelTits.map_pCore_le 2 f hf)
  · exact CFSG.LieType.BorelTits.le_pCore 2
      ((CFSG.LieType.BorelTits.pCore_normal (G := B) (r := 2)).comap f)
      ((CFSG.LieType.BorelTits.pCore_isPGroup (G := B) (r := 2)).comap_of_ker_isPGroup f hk)

end PCore

theorem s3_key : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 →
    ∃ c : Equiv.Perm (Fin 3), (σ * c * σ⁻¹ * c⁻¹) ^ 3 = 1 ∧ σ * c * σ⁻¹ * c⁻¹ ≠ 1 := by
  decide +kernel

theorem s33_key (n : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (hn : n ≠ 1) :
    ∃ c : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
      (n * c * n⁻¹ * c⁻¹) ^ 3 = 1 ∧ n * c * n⁻¹ * c⁻¹ ≠ 1 := by
  obtain ⟨σ, τ⟩ := n
  by_cases hσ : σ = 1
  · have hτ : τ ≠ 1 := fun h => hn (by rw [hσ, h]; rfl)
    obtain ⟨c, h3, h1⟩ := s3_key τ hτ
    refine ⟨(1, c), ?_, fun h => h1 (congrArg Prod.snd h)⟩
    ext1
    · simp [hσ]
    · simpa using h3
  · obtain ⟨c, h3, h1⟩ := s3_key σ hσ
    refine ⟨(c, 1), ?_, fun h => h1 (congrArg Prod.fst h)⟩
    ext1
    · simpa using h3
    · simp

theorem s33_normal_two (N : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) (hN : N.Normal)
    (hP : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨c, h3, h1⟩ := s33_key n hne
  have hm : n * c * n⁻¹ * c⁻¹ ∈ N := by
    rw [show n * c * n⁻¹ * c⁻¹ = n * (c * n⁻¹ * c⁻¹) by group]
    exact N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) c)
  obtain ⟨k, hk⟩ := hP ⟨_, hm⟩
  have hk' : (n * c * n⁻¹ * c⁻¹) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
  rw [hcop.gcd_eq_one] at hd
  exact h1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))

theorem oTwoUpper_idem {G : Type*} [Group G] (X : Subgroup G) :
    oTwoUpper (oTwoUpper X) = oTwoUpper X :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
    Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩)

section Mat

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))

@[expose] noncomputable def matOf : (V ≃ₗ[ZMod 2] V) →* GL (Fin 8) (ZMod 2) where
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

theorem matOf_mulVec (ψ : V ≃ₗ[ZMod 2] V) (v : V) :
    ((matOf e ψ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v) =
      e (ψ v) := by
  show (LinearMap.toMatrix' (e.symm.trans (ψ.trans e)).toLinearMap).mulVec (e v) = e (ψ v)
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem matOf_mulVec' (ψ : V ≃ₗ[ZMod 2] V) (x : Fin 8 → ZMod 2) :
    ((matOf e ψ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec x =
      e (ψ (e.symm x)) := by
  rw [← matOf_mulVec, LinearEquiv.apply_symm_apply]

theorem matOf_eq_iff (ψ : V ≃ₗ[ZMod 2] V) (γ : GL (Fin 8) (ZMod 2)) :
    matOf e ψ = γ ↔ ∀ v, e (ψ v) = (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v) := by
  constructor
  · rintro rfl v
    rw [matOf_mulVec]
  · intro h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, matOf_mulVec', h, LinearEquiv.apply_symm_apply]

theorem matOf_injective : Function.Injective (matOf e) := by
  intro ψ χ h
  ext v
  apply e.injective
  rw [← matOf_mulVec, ← matOf_mulVec, h]

end Mat

section Img

variable {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)
  (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))

@[expose] noncomputable def img8 (Y : Subgroup G) : Subgroup (GL (Fin 8) (ZMod 2)) :=
  (D.img Y).map (matOf e)

@[expose] noncomputable def hom8 {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G)) :
    ↥Y →* GL (Fin 8) (ZMod 2) :=
  (matOf e).comp (D.ρ.comp (Subgroup.inclusion hY))

theorem mem_img8 {Y : Subgroup G} {γ : GL (Fin 8) (ZMod 2)} :
    γ ∈ img8 D e Y ↔ ∃ y ∈ Y, ∃ hy : y ∈ Subgroup.normalizer (U : Set G),
      matOf e (D.ρ ⟨y, hy⟩) = γ := by
  unfold img8
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨y, hyY, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp hψ
    exact ⟨y, hyY, hyN, rfl⟩
  · rintro ⟨y, hyY, hyN, rfl⟩
    exact ⟨_, L128A.HatU.rho_mem_img D hyY hyN, rfl⟩

theorem range_hom8 {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G)) :
    (hom8 D e hY).range = img8 D e Y := by
  ext γ
  rw [MonoidHom.mem_range, mem_img8]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, hY y.2, rfl⟩
  · rintro ⟨y, hyY, hyN, rfl⟩
    exact ⟨⟨y, hyY⟩, rfl⟩

theorem img8_mono {Y Y' : Subgroup G} (h : Y ≤ Y') : img8 D e Y ≤ img8 D e Y' := by
  intro γ hγ
  obtain ⟨y, hy, hyN, rfl⟩ := (mem_img8 D e).mp hγ
  exact (mem_img8 D e).mpr ⟨y, h hy, hyN, rfl⟩

theorem card_img8 (Y : Subgroup G) : Nat.card (img8 D e Y) = Nat.card (D.img Y) :=
  Nat.card_congr ((D.img Y).equivMapOfInjective _ (matOf_injective e)).toEquiv.symm

theorem img8_eq_map (Y : Subgroup G) :
    img8 D e Y = (Y.subgroupOf (Subgroup.normalizer (U : Set G))).map ((matOf e).comp D.ρ) := by
  unfold img8 HatModelU.img
  rw [Subgroup.map_map]

theorem img8_sup {Y Y' : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G))
    (hY' : Y' ≤ Subgroup.normalizer (U : Set G)) :
    img8 D e (Y ⊔ Y') = img8 D e Y ⊔ img8 D e Y' := by
  rw [img8_eq_map D e (Y ⊔ Y'), img8_eq_map D e Y, img8_eq_map D e Y',
    Subgroup.subgroupOf_sup hY hY', Subgroup.map_sup]

theorem img8_oTwoUpper [Finite G] {Y : Subgroup G} (hY : Y ≤ Subgroup.normalizer (U : Set G)) :
    img8 D e (oTwoUpper Y) = oTwoUpper (img8 D e Y) := by
  rw [img8_eq_map D e (oTwoUpper Y), img8_eq_map D e Y,
    ← A4.oTwoUpper_subgroupOf hY, oTwoUpper_map]

end Img

end CFSG.Quasithin.H13.L14411
