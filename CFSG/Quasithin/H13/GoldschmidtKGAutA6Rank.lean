module

public import CFSG.Quasithin.H13.A6S13721b
public import CFSG.Quasithin.H13.GoldschmidtKGAutA6Finite
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3

section Induced

variable {K Q : Type*} [Group K] [Group Q]

theorem exists_induced_aut (α : K →* Q) (hα : Function.Surjective α) (σ : MulAut K)
    (hσ : ∀ k, α (σ k) = 1 ↔ α k = 1) : ∃ ρ : MulAut Q, ∀ k, ρ (α k) = α (σ k) := by
  have hker : α.ker ≤ (α.comp σ.toMonoidHom).ker := fun k hk => by
    rw [MonoidHom.mem_ker] at hk ⊢
    exact (hσ k).mpr hk
  let f : Q →* Q := MonoidHom.liftOfRightInverse α (Function.surjInv hα)
    (Function.rightInverse_surjInv hα) ⟨α.comp σ.toMonoidHom, hker⟩
  have hf : ∀ k, f (α k) = α (σ k) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
      (Function.rightInverse_surjInv hα) ⟨α.comp σ.toMonoidHom, hker⟩ k
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨k, rfl⟩ := hα q
    rw [hf] at hq
    exact (hσ k).mp hq
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨k', rfl⟩ := hα q
    obtain ⟨k, rfl⟩ := σ.surjective k'
    exact ⟨α k, hf k⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun k => hf k⟩

theorem exists_hom_induced {Γ : Type*} [Group Γ] (α : K →* Q) (hα : Function.Surjective α)
    (ι : Γ →* MulAut K) (hι : ∀ γ k, α (ι γ k) = 1 ↔ α k = 1) :
    ∃ ρ : Γ →* MulAut Q, ∀ γ k, ρ γ (α k) = α (ι γ k) := by
  choose ρ₀ hρ₀ using fun γ => exists_induced_aut α hα (ι γ) (hι γ)
  refine ⟨MonoidHom.mk' ρ₀ fun γ γ' => ?_, hρ₀⟩
  ext q
  obtain ⟨k, rfl⟩ := hα q
  rw [MulAut.mul_apply, hρ₀, hρ₀, hρ₀, map_mul, MulAut.mul_apply]

end Induced

theorem conjAut_one' : DoubleA3.conjAut (1 : ↥A6Models.autA6) = 1 :=
  MulEquiv.ext fun x => Subtype.ext (by simp [DoubleA3.conjAut_apply])

theorem conjAut_mul' (a b : ↥A6Models.autA6) :
    DoubleA3.conjAut (a * b) = DoubleA3.conjAut a * DoubleA3.conjAut b :=
  MulEquiv.ext fun x => Subtype.ext (by
    simp only [DoubleA3.conjAut_apply, MulAut.mul_apply, Subgroup.coe_mul, mul_inv_rev]
    group)

@[expose] def conjHom : ↥A6Models.autA6 →* MulAut ↥A6Models.psl29 where
  toFun := DoubleA3.conjAut
  map_one' := conjAut_one'
  map_mul' := conjAut_mul'

noncomputable def autEquiv : ↥A6Models.autA6 ≃* MulAut ↥A6Models.psl29 :=
  MulEquiv.ofBijective conjHom
    ⟨fun _ _ h => DoubleA3.conjAut_injective h, fun f => DoubleA3.conjAut_surjective f⟩

theorem factAutA6Rank : FactAutA6Rank := by
  intro G _ _ K P E hKP hEP hEK ⟨α, hα, hαker⟩ hfaith hexp
  let ι : ↥E →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hEK)
  have hιapply : ∀ (e : ↥E) (k : ↥K), ((ι e k : ↥K) : G) = (e : G) * (k : G) * (e : G)⁻¹ :=
    fun e k => rfl
  have hι : ∀ e k, α (ι e k) = 1 ↔ α k = 1 := by
    intro e k
    rw [hαker, hαker, hιapply]
    exact ((Subgroup.mem_normalizer_iff.mp (hEP e.2)) (k : G)).symm
  obtain ⟨ρ, hρ⟩ := exists_hom_induced α hα ι hι
  have hρker : ∀ e : ↥E, ρ e = 1 ↔ (e : G) ∈ P := by
    intro e
    constructor
    · intro h
      refine hfaith e e.2 fun k hk => ?_
      have h1 := hρ e ⟨k, hk⟩
      rw [h, MulAut.one_apply] at h1
      have h2 : α (ι e ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
        rw [map_mul, map_inv, ← h1, mul_inv_cancel]
      rw [hαker] at h2
      simpa [hιapply] using h2
    · intro h
      refine MulEquiv.ext fun q => ?_
      obtain ⟨k, rfl⟩ := hα q
      rw [hρ, MulAut.one_apply]
      have h2 : α (ι e k * k⁻¹) = 1 := by
        rw [hαker]
        have hk' : (k : G) * (e : G)⁻¹ * (k : G)⁻¹ ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (hKP k.2)) ((e : G)⁻¹)
          exact this.mp (P.inv_mem h)
        have : ((ι e k * k⁻¹ : ↥K) : G) = (e : G) * ((k : G) * (e : G)⁻¹ * (k : G)⁻¹) := by
          simp [hιapply, mul_assoc]
        rw [this]
        exact P.mul_mem h hk'
      rw [map_mul, map_inv] at h2
      exact mul_inv_eq_one.mp h2
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let θ : ↥E →* ↥A6Models.autA6 :=
    autEquiv.symm.toMonoidHom.comp ((MulAut.congr ψ.symm).toMonoidHom.comp ρ)
  have hθker : ∀ e : ↥E, θ e = 1 ↔ (e : G) ∈ P := by
    intro e
    rw [← hρker]
    show autEquiv.symm (MulAut.congr ψ.symm (ρ e)) = 1 ↔ ρ e = 1
    rw [map_eq_one_iff _ autEquiv.symm.injective, map_eq_one_iff _ (MulAut.congr ψ.symm).injective]
  have hker : θ.ker = (P ⊓ E).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, hθker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, e.2⟩, fun h => h.1⟩
  have hrel : (P ⊓ E).relIndex E = Nat.card θ.range := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
  rw [hrel]
  refine card_le_eight_of_exp_two θ.range ?_
  rintro _ ⟨e, rfl⟩
  have h2 : θ (e * e) = 1 := (hθker (e * e)).mpr (hexp e e.2)
  rw [map_mul] at h2
  exact h2

end CFSG.Quasithin.H13.A6
