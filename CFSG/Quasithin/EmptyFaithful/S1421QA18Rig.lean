module

public import CFSG.Quasithin.EmptyFaithful.S1421QA18Ext

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421QA18

variable {G D : Type} [Group G] [Group D]

@[expose] def AmalgamRigid (P₁ P₂ : Subgroup D) : Prop :=
  P₁ ⊔ P₂ = ⊤ ∧
  ∀ (a₁ : MulAut ↥P₁) (a₂ : MulAut ↥P₂),
    (∀ (x : D) (h₁ : x ∈ P₁) (h₂ : x ∈ P₂),
      ((a₁ ⟨x, h₁⟩ : ↥P₁) : D) = ((a₂ ⟨x, h₂⟩ : ↥P₂) : D)) →
    ∃ ρ : MulAut D, (∀ (x : D) (h : x ∈ P₁), ρ x = ((a₁ ⟨x, h⟩ : ↥P₁) : D)) ∧
      ∀ (x : D) (h : x ∈ P₂), ρ x = ((a₂ ⟨x, h⟩ : ↥P₂) : D)

end S1421QA18

@[expose] def D4AmalgamRigid : Prop :=
  ∀ (D : Type) [Group D], IsLieOverTwo .trialityD4 0 1 D →
    ∀ TD P₁ P₂ : Subgroup D, IsYAmalgamPair TD P₁ P₂ → S1421QA18.AmalgamRigid P₁ P₂

@[expose] def D4Order : Prop :=
  ∀ (D : Type) [Group D], IsLieOverTwo .trialityD4 0 1 D → Nat.card D = 211341312

namespace S1421QA18

variable {G D : Type} [Group G] [Group D]

@[expose] def conjEquiv {A M : Subgroup G} (hn : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (x : G)
    (hx : x ∈ M) : ↥A ≃* ↥A where
  toFun a := ⟨x * a * x⁻¹, hn x hx a a.2⟩
  invFun a := ⟨x⁻¹ * a * x, by simpa using hn x⁻¹ (M.inv_mem hx) a a.2⟩
  left_inv a := by ext; simp [mul_assoc]
  right_inv a := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

section Rigid

variable {A₁ A₂ M₁ M₂ : Subgroup G} {P₁ P₂ : Subgroup D}
  (φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂))

@[expose] noncomputable def transport1 (hn₁ : ∀ m ∈ M₁, ∀ a ∈ A₁, m * a * m⁻¹ ∈ A₁) (x : G)
    (hx : x ∈ M₁) : MulAut ↥P₁ :=
  ((iso1 φ).symm.trans (conjEquiv hn₁ x hx)).trans (iso1 φ)

@[expose] noncomputable def transport2 (hn₂ : ∀ m ∈ M₂, ∀ a ∈ A₂, m * a * m⁻¹ ∈ A₂) (x : G)
    (hx : x ∈ M₂) : MulAut ↥P₂ :=
  ((iso2 φ).symm.trans (conjEquiv hn₂ x hx)).trans (iso2 φ)

theorem transport1_apply (hn₁ : ∀ m ∈ M₁, ∀ a ∈ A₁, m * a * m⁻¹ ∈ A₁) (x : G) (hx : x ∈ M₁)
    {a : G} (ha : a ∈ A₁) :
    ((transport1 φ hn₁ x hx ⟨f1 φ a, f1_mem φ ha⟩ : ↥P₁) : D) = f1 φ (x * a * x⁻¹) := by
  have e : (iso1 φ).symm ⟨f1 φ a, f1_mem φ ha⟩ = ⟨a, ha⟩ := by
    rw [MulEquiv.symm_apply_eq]; exact Subtype.ext (f1_apply φ ha)
  show (((iso1 φ) (conjEquiv hn₁ x hx ((iso1 φ).symm ⟨f1 φ a, f1_mem φ ha⟩)) : ↥P₁) : D) = _
  rw [e, f1_apply φ (hn₁ x hx a ha)]
  rfl

theorem transport2_apply (hn₂ : ∀ m ∈ M₂, ∀ a ∈ A₂, m * a * m⁻¹ ∈ A₂) (x : G) (hx : x ∈ M₂)
    {a : G} (ha : a ∈ A₂) :
    ((transport2 φ hn₂ x hx ⟨f2 φ a, f2_mem φ ha⟩ : ↥P₂) : D) = f2 φ (x * a * x⁻¹) := by
  have e : (iso2 φ).symm ⟨f2 φ a, f2_mem φ ha⟩ = ⟨a, ha⟩ := by
    rw [MulEquiv.symm_apply_eq]; exact Subtype.ext (f2_apply φ ha)
  show (((iso2 φ) (conjEquiv hn₂ x hx ((iso2 φ).symm ⟨f2 φ a, f2_mem φ ha⟩)) : ↥P₂) : D) = _
  rw [e, f2_apply φ (hn₂ x hx a ha)]
  rfl

theorem eq_of_agree {P₁ P₂ : Subgroup D} (hgen : P₁ ⊔ P₂ = ⊤) {σ τ : MulAut D}
    (h₁ : ∀ y ∈ P₁, σ y = τ y) (h₂ : ∀ y ∈ P₂, σ y = τ y) : σ = τ := by
  have hle : P₁ ⊔ P₂ ≤ MonoidHom.eqLocus σ.toMonoidHom τ.toMonoidHom :=
    sup_le (fun y hy => h₁ y hy) (fun y hy => h₂ y hy)
  rw [hgen] at hle
  ext d
  exact hle (Subgroup.mem_top d)

theorem exists_psi_of_rigid (hrig : AmalgamRigid P₁ P₂)
    (hn₁ : ∀ m ∈ M₁, ∀ a ∈ A₁, m * a * m⁻¹ ∈ A₁) (hn₂ : ∀ m ∈ M₂, ∀ a ∈ A₂, m * a * m⁻¹ ∈ A₂)
    (hker : ∀ x ∈ M₁ ⊓ M₂, (∀ a ∈ A₁, x * a * x⁻¹ = a) → (∀ a ∈ A₂, x * a * x⁻¹ = a) → x = 1) :
    ∃ ψ : ↥(M₁ ⊓ M₂) →* MulAut D,
      (∀ (x : G) (hx : x ∈ M₁ ⊓ M₂) (a : G), a ∈ A₁ → ψ ⟨x, hx⟩ (f1 φ a) = f1 φ (x * a * x⁻¹)) ∧
      (∀ (x : G) (hx : x ∈ M₁ ⊓ M₂) (a : G), a ∈ A₂ → ψ ⟨x, hx⟩ (f2 φ a) = f2 φ (x * a * x⁻¹)) ∧
      Function.Injective ψ ∧
      (∀ (b : G) (hb : b ∈ M₁ ⊓ M₂), b ∈ A₁ → b ∈ A₂ → ψ ⟨b, hb⟩ = MulAut.conj (f1 φ b)) := by
  classical
  have hcompat : ∀ x : ↥(M₁ ⊓ M₂), ∀ (y : D) (h₁ : y ∈ P₁) (h₂ : y ∈ P₂),
      ((transport1 φ hn₁ x.1 x.2.1 ⟨y, h₁⟩ : ↥P₁) : D) =
        ((transport2 φ hn₂ x.1 x.2.2 ⟨y, h₂⟩ : ↥P₂) : D) := by
    intro x y h₁ h₂
    obtain ⟨b, hb, rfl⟩ := exists_f1 φ h₁
    have hb2 : b ∈ A₂ := mem_A₂_of_f1_mem φ hb h₂
    have h2' : f1 φ b = f2 φ b := f1_eq_f2 φ hb hb2
    have hxb₁ : x.1 * b * x.1⁻¹ ∈ A₁ := hn₁ x.1 x.2.1 b hb
    have hxb₂ : x.1 * b * x.1⁻¹ ∈ A₂ := hn₂ x.1 x.2.2 b hb2
    have e1 := transport1_apply φ hn₁ x.1 x.2.1 hb
    have e2 := transport2_apply φ hn₂ x.1 x.2.2 hb2
    have hy2 : (⟨f1 φ b, h₂⟩ : ↥P₂) = ⟨f2 φ b, f2_mem φ hb2⟩ := Subtype.ext h2'
    rw [hy2, e2]
    exact e1.trans (f1_eq_f2 φ hxb₁ hxb₂)
  choose ρ hρ₁ hρ₂ using fun x : ↥(M₁ ⊓ M₂) =>
    hrig.2 (transport1 φ hn₁ x.1 x.2.1) (transport2 φ hn₂ x.1 x.2.2) (hcompat x)
  have hr1 : ∀ (x : ↥(M₁ ⊓ M₂)) (a : G), a ∈ A₁ → ρ x (f1 φ a) = f1 φ (x.1 * a * x.1⁻¹) := by
    intro x a ha
    rw [hρ₁ x (f1 φ a) (f1_mem φ ha)]
    exact transport1_apply φ hn₁ x.1 x.2.1 ha
  have hr2 : ∀ (x : ↥(M₁ ⊓ M₂)) (a : G), a ∈ A₂ → ρ x (f2 φ a) = f2 φ (x.1 * a * x.1⁻¹) := by
    intro x a ha
    rw [hρ₂ x (f2 φ a) (f2_mem φ ha)]
    exact transport2_apply φ hn₂ x.1 x.2.2 ha
  have hone : ρ 1 = 1 := by
    apply eq_of_agree hrig.1
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := exists_f1 φ hy
      rw [hr1 1 a ha]; simp
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := exists_f2 φ hy
      rw [hr2 1 a ha]; simp
  have hmulρ : ∀ x y : ↥(M₁ ⊓ M₂), ρ (x * y) = ρ x * ρ y := by
    intro x y
    apply eq_of_agree hrig.1
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := exists_f1 φ hz
      have hya : y.1 * a * y.1⁻¹ ∈ A₁ := hn₁ y.1 y.2.1 a ha
      rw [hr1 (x * y) a ha, MulAut.mul_apply, hr1 y a ha, hr1 x _ hya]
      congr 1
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := exists_f2 φ hz
      have hya : y.1 * a * y.1⁻¹ ∈ A₂ := hn₂ y.1 y.2.2 a ha
      rw [hr2 (x * y) a ha, MulAut.mul_apply, hr2 y a ha, hr2 x _ hya]
      congr 1
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
  refine ⟨{ toFun := ρ, map_one' := hone, map_mul' := hmulρ },
    fun x hx a ha => hr1 ⟨x, hx⟩ a ha, fun x hx a ha => hr2 ⟨x, hx⟩ a ha, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : ρ x = 1 := hx
    refine Subtype.ext (hker x.1 x.2 (fun a ha => ?_) (fun a ha => ?_))
    · have h1 := hr1 x a ha
      rw [hx'] at h1
      exact (f1_inj φ (hn₁ x.1 x.2.1 a ha) ha h1.symm)
    · have h1 := hr2 x a ha
      rw [hx'] at h1
      exact (f2_inj φ (hn₂ x.1 x.2.2 a ha) ha h1.symm)
  · intro b hb hbA₁ hbA₂
    show ρ ⟨b, hb⟩ = _
    apply eq_of_agree hrig.1
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := exists_f1 φ hz
      rw [hr1 ⟨b, hb⟩ a ha, MulAut.conj_apply, f1_mul φ (A₁.mul_mem hbA₁ ha) (A₁.inv_mem hbA₁),
        f1_mul φ hbA₁ ha, f1_inv φ hbA₁]
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := exists_f2 φ hz
      rw [hr2 ⟨b, hb⟩ a ha, MulAut.conj_apply, f1_eq_f2 φ hbA₁ hbA₂,
        f2_mul φ (A₂.mul_mem hbA₂ ha) (A₂.inv_mem hbA₂), f2_mul φ hbA₂ ha, f2_inv φ hbA₂]

end Rigid

theorem isExtension_of_rigid [Finite G] {A₁ A₂ M₁ M₂ : Subgroup G} {TD P₁ P₂ : Subgroup D}
    (φ : (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂))
    (yam : IsYAmalgamPair TD P₁ P₂) (hrig : AmalgamRigid P₁ P₂)
    (hA₁ : A₁ ≤ M₁) (hA₂ : A₂ ≤ M₂)
    (hn₁ : ∀ m ∈ M₁, ∀ a ∈ A₁, m * a * m⁻¹ ∈ A₁) (hn₂ : ∀ m ∈ M₂, ∀ a ∈ A₂, m * a * m⁻¹ ∈ A₂)
    (hM₁ : M₁ ≤ A₁ ⊔ (M₁ ⊓ M₂)) (hM₂ : M₂ ≤ A₂ ⊔ (M₁ ⊓ M₂))
    (hi₁ : A₁ ⊓ M₂ ≤ A₂) (hi₂ : A₂ ⊓ M₁ ≤ A₁)
    (hker : ∀ x ∈ M₁ ⊓ M₂, (∀ a ∈ A₁, x * a * x⁻¹ = a) → (∀ a ∈ A₂, x * a * x⁻¹ = a) → x = 1) :
    IsExtensionOfLieAmalgam D M₁ M₂ := by
  obtain ⟨ψ, h₁, h₂, hinj, hinn⟩ := exists_psi_of_rigid φ hrig hn₁ hn₂ hker
  exact (ExtData.mk A₁ A₂ M₁ M₂ TD P₁ P₂ φ ψ yam hA₁ hA₂ hn₁ hn₂ hM₁ hM₂ hi₁ hi₂ h₁ h₂ hinj
    hinn).isExtension

end S1421QA18

end CFSG.Quasithin
