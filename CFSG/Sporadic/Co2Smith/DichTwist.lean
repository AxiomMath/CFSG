module

public import CFSG.Sporadic.Co2Smith.DichExt

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u v w w'

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace SmithConfig

variable (c₂ : SmithConfig.{v})

@[expose] noncomputable def rho : c₂.H →* S0 :=
  (MulEquiv.ofBijective c₂.ψ c₂.ψ_bijective).symm.toMonoidHom.comp (QuotientGroup.mk' c₂.E)

theorem rho_eq_iff
    (x : c₂.H) (s : S0) : c₂.rho x = s ↔ (c₂.ι s)⁻¹ * x ∈ c₂.E := by
  rw [← QuotientGroup.eq, c₂.mk_ι]
  show (MulEquiv.ofBijective c₂.ψ c₂.ψ_bijective).symm (QuotientGroup.mk x) = s ↔ _
  rw [MulEquiv.symm_apply_eq, eq_comm]
  rfl

theorem rho_ι (s : S0) : c₂.rho (c₂.ι s) = s := by
  rw [rho_eq_iff, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem rho_E (e : c₂.E) : c₂.rho (e : c₂.H) = 1 := by
  rw [rho_eq_iff, map_one, inv_one, one_mul]
  exact e.2

variable {T : Type w} [Group T] {T' : Type w'} [Group T']

@[expose] def fibSub (π : T →* S0) : Subgroup (c₂.H × T) where
  carrier := {p | c₂.rho p.1 = π p.2}
  mul_mem' {p q} hp hq := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at hp hq ⊢
    rw [hp, hq]
  one_mem' := by simp
  inv_mem' {p} hp := by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at hp ⊢
    rw [hp]

theorem mem_fibSub (π : T →* S0) (p : c₂.H × T) : p ∈ c₂.fibSub π ↔ c₂.rho p.1 = π p.2 :=
  Iff.rfl

theorem zE_mem_fibSub (π : T →* S0) {t : T} (ht : π t = 1) :
    ((c₂.zE : c₂.H), t) ∈ c₂.fibSub π := by
  rw [mem_fibSub, ht]
  exact c₂.rho_E c₂.zE

@[expose] noncomputable def zPair (π : T →* S0) (t : T) (ht : π t = 1) : c₂.fibSub π :=
  ⟨((c₂.zE : c₂.H), t), c₂.zE_mem_fibSub π ht⟩

abbrev Twist (π : T →* S0) (t : T) (ht : π t = 1) : Type _ :=
  c₂.fibSub π ⧸ Subgroup.normalClosure {c₂.zPair π t ht}

@[expose] noncomputable def fibCongr {π : T →* S0} {π' : T' →* S0} (β : T ≃* T')
    (hβ : ∀ x, π' (β x) = π x) : c₂.fibSub π ≃* c₂.fibSub π' where
  toFun p := ⟨(p.1.1, β p.1.2), by
    rw [mem_fibSub, hβ]
    exact p.2⟩
  invFun p := ⟨(p.1.1, β.symm p.1.2), by
    rw [mem_fibSub, ← hβ, MulEquiv.apply_symm_apply]
    exact p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  map_mul' p q := by
    apply Subtype.ext
    simp

@[expose] noncomputable def twistCongr {π : T →* S0} {π' : T' →* S0} (β : T ≃* T')
    (hβ : ∀ x, π' (β x) = π x) {t : T} {t' : T'} (ht : π t = 1) (ht' : π' t' = 1)
    (hβt : β t = t') : c₂.Twist π t ht ≃* c₂.Twist π' t' ht' :=
  QuotientGroup.congr _ _ (c₂.fibCongr β hβ) (by
    rw [Subgroup.map_normalClosure _ _ (c₂.fibCongr β hβ).surjective, Set.image_singleton]
    congr 2
    apply Subtype.ext
    show ((c₂.zE : c₂.H), β t) = ((c₂.zE : c₂.H), t')
    rw [hβt])

end SmithConfig

namespace LocalConfig

variable (c₁ : LocalConfig.{u}) (c₂ : SmithConfig.{v})

@[expose] noncomputable def eOf (p : c₂.fibSub (c₁.piHat c₂)) : c₂.E :=
  ⟨(c₂.ι (c₁.piHat c₂ p.1.2))⁻¹ * p.1.1, (c₂.rho_eq_iff _ _).mp p.2⟩

theorem eOf_val (p : c₂.fibSub (c₁.piHat c₂)) :
    (c₁.eOf c₂ p : c₂.H) = (c₂.ι (c₁.piHat c₂ p.1.2))⁻¹ * p.1.1 := rfl

theorem compat_inv_piHat (t : c₁.Shat c₂) (e : c₂.E) :
    c₂.θL c₁ (c₂.cE (c₂.ι (c₁.piHat c₂ t))⁻¹ e) = c₁.cE (t : c₁.H)⁻¹ (c₂.θL c₁ e) :=
  (c₁.piHat_spec c₂ t).symm.inv e

@[expose] noncomputable def twistHom : c₂.fibSub (c₁.piHat c₂) →* c₁.H where
  toFun p := (p.1.2 : c₁.H) * (c₂.θL c₁ (c₁.eOf c₂ p) : c₁.H)
  map_one' := by
    have h : c₁.eOf c₂ 1 = 1 := by
      apply Subtype.ext
      rw [eOf_val]
      simp
    simp only [h, map_one]
    simp
  map_mul' p q := by
    have h : c₁.eOf c₂ (p * q) =
        c₂.cE (c₂.ι (c₁.piHat c₂ q.1.2))⁻¹ (c₁.eOf c₂ p) * c₁.eOf c₂ q := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, c₂.cE_val, eOf_val, eOf_val, eOf_val]
      simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
      group
    rw [h, map_mul, compat_inv_piHat]
    simp only [Subgroup.coe_mul, Prod.snd_mul, c₁.cE_val]
    group

theorem twistHom_apply (p : c₂.fibSub (c₁.piHat c₂)) :
    c₁.twistHom c₂ p = (p.1.2 : c₁.H) * (c₂.θL c₁ (c₁.eOf c₂ p) : c₁.H) := rfl

theorem twistHom_surjective : Function.Surjective (c₁.twistHom c₂) := by
  intro h₁
  obtain ⟨t, ht, e, rfl⟩ := c₁.exists_Shat_mul_E c₂ h₁
  set s := c₁.piHat c₂ ⟨t, ht⟩
  have hmem : (c₂.ι s * (c₁.θL c₂.toLocalConfig e : c₂.H), (⟨t, ht⟩ : c₁.Shat c₂)) ∈
      c₂.fibSub (c₁.piHat c₂) := by
    rw [SmithConfig.mem_fibSub, map_mul, c₂.rho_ι, SmithConfig.rho_E, mul_one]
  refine ⟨⟨_, hmem⟩, ?_⟩
  have he : c₁.eOf c₂ ⟨_, hmem⟩ = c₁.θL c₂.toLocalConfig e := by
    apply Subtype.ext
    rw [eOf_val]
    show (c₂.ι s)⁻¹ * (c₂.ι s * _) = _
    group
  rw [twistHom_apply, he, ← c₁.θL_symm_apply, MulEquiv.symm_apply_apply]

theorem twistHom_ker :
    (c₁.twistHom c₂).ker =
      Subgroup.normalClosure {c₂.zPair (c₁.piHat c₂) (c₁.zHat c₂) (c₁.piHat_zHat c₂)} := by
  apply le_antisymm
  · intro p hp
    rw [MonoidHom.mem_ker, twistHom_apply] at hp
    have ht : (p.1.2 : c₁.H) = ((c₂.θL c₁ (c₁.eOf c₂ p))⁻¹ : c₁.E) := by
      rw [Subgroup.coe_inv]
      exact eq_inv_of_mul_eq_one_left hp
    obtain ⟨k, hk, hke⟩ := c₁.center_of_mem_Shat c₂ p.1.2.2 (by rw [ht]; exact SetLike.coe_mem _)
    have hπ : c₁.piHat c₂ p.1.2 = 1 := (c₁.piHat_eq_one_iff c₂ _).mpr ⟨k, hk, hke⟩
    have hx : (c₁.eOf c₂ p : c₂.H) = p.1.1 := by rw [eOf_val, hπ, map_one, inv_one, one_mul]
    have hθ : c₂.θL c₁ (c₁.eOf c₂ p) = (k⁻¹ : c₁.E) := by
      have h1 : ((c₂.θL c₁ (c₁.eOf c₂ p))⁻¹ : c₁.E) = k := Subtype.ext (ht.symm.trans hke)
      rw [← h1, inv_inv]
    rcases (c₁.mem_center_iff k).mp hk with rfl | rfl
    · have h1 : c₁.eOf c₂ p = 1 := by
        rw [inv_one] at hθ
        rw [← map_eq_one_iff _ (c₂.θL c₁).injective, hθ]
      have hp1 : p = 1 := by
        apply Subtype.ext
        apply Prod.ext
        · rw [← hx, h1]; rfl
        · exact Subtype.ext (by rw [hke]; rfl)
      rw [hp1]
      exact Subgroup.one_mem _
    · have h1 : c₁.eOf c₂ p = c₂.zE := by
        apply (c₂.θL c₁).injective
        rw [hθ, inv_eq_of_mul_eq_one_right c₁.zE_sq, θL_zE]
      have hp1 : p = c₂.zPair (c₁.piHat c₂) (c₁.zHat c₂) (c₁.piHat_zHat c₂) := by
        apply Subtype.ext
        apply Prod.ext
        · rw [← hx, h1]; rfl
        · exact Subtype.ext hke
      rw [hp1]
      exact Subgroup.subset_normalClosure rfl
  · apply Subgroup.normalClosure_le_normal
    rintro _ rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, twistHom_apply]
    have h1 : c₁.eOf c₂ (c₂.zPair (c₁.piHat c₂) (c₁.zHat c₂) (c₁.piHat_zHat c₂)) = c₂.zE := by
      apply Subtype.ext
      rw [eOf_val]
      show (c₂.ι (c₁.piHat c₂ (c₁.zHat c₂)))⁻¹ * (c₂.zE : c₂.H) = c₂.zE
      rw [c₁.piHat_zHat, map_one, inv_one, one_mul]
    rw [h1, θL_zE]
    exact congrArg Subtype.val c₁.zE_sq

@[expose] noncomputable def twistEquiv :
    c₂.Twist (c₁.piHat c₂) (c₁.zHat c₂) (c₁.piHat_zHat c₂) ≃* c₁.H :=
  (QuotientGroup.quotientMulEquivOfEq (c₁.twistHom_ker c₂).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (c₁.twistHom_surjective c₂))

end LocalConfig

theorem commutator_S0 :
    commutator S0 = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S0) with h | h
  · exfalso
    have hab : ∀ g h' : S0, g * h' = h' * g := fun g h' => by
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h')
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    have h1 := frS_s1_y1
    rw [hab (frS 1) (frS 0), mul_assoc, frS_s1_sq, mul_one] at h1
    exact frS_zero_ne_one (by
      have h2 : frS 0 * 1 = frS 0 * frS 0 := by rw [mul_one]; exact h1
      exact (mul_left_cancel h2).symm)
  · exact h

theorem split_or_perfect
    {T : Type*} [Group T] (π : T →* S0) (hπ : Function.Surjective π)
    (c : T) (hker : ∀ t, π t = 1 ↔ t = 1 ∨ t = c) :
    (∃ S' : Subgroup T, c ∉ S' ∧ S'.map π = ⊤) ∨ commutator T = ⊤ := by
  have hmap : (commutator T).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hπ,
      ← commutator_def, commutator_S0]
  by_cases hc : c ∈ commutator T
  · right
    rw [eq_top_iff]
    intro t _
    have ht : π t ∈ (commutator T).map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨d, hd, hdt⟩ := ht
    have h1 : π (d⁻¹ * t) = 1 := by rw [map_mul, map_inv, hdt, inv_mul_cancel]
    have e : t = d * (d⁻¹ * t) := by group
    rw [e]
    rcases (hker _).mp h1 with h | h
    · rw [h, mul_one]; exact hd
    · rw [h]; exact Subgroup.mul_mem _ hd hc
  · exact Or.inl ⟨_, hc, hmap⟩

end CFSG.Sporadic.Co2Smith
