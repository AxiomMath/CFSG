module

public import CFSG.Quasithin.Background.RonanG1016McL
public import CFSG.Quasithin.Background.RonanG1016Defs
public import CFSG.Quasithin.Background.RonanG1016PermInj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

open CFSG.ComponentClassification.OutcomeLocal

theorem mem_or_mul_mem_of_normalizes {G : Type*} [Group G] {A : Subgroup G} {x : G}
    (hx2 : x * x = 1) (hN : ∀ a ∈ A, x * a * x ∈ A) {g : G}
    (hg : g ∈ A ⊔ Subgroup.zpowers x) : g ∈ A ∨ g * x ∈ A := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, g = a ∨ g = a * x}
      mul_mem' := by
        rintro g g' ⟨a, ha, hg⟩ ⟨a', ha', hg'⟩
        rcases hg with hg | hg <;> rcases hg' with hg' | hg'
        · exact ⟨a * a', A.mul_mem ha ha', Or.inl (by rw [hg, hg'])⟩
        · exact ⟨a * a', A.mul_mem ha ha', Or.inr (by rw [hg, hg']; group)⟩
        · refine ⟨a * (x * a' * x), A.mul_mem ha (hN a' ha'), Or.inr ?_⟩
          rw [hg, hg']
          calc a * x * a' = a * x * a' * (x * x) := by rw [hx2, mul_one]
            _ = a * (x * a' * x) * x := by group
        · refine ⟨a * (x * a' * x), A.mul_mem ha (hN a' ha'), Or.inl ?_⟩
          rw [hg, hg']
          group
      one_mem' := ⟨1, A.one_mem, Or.inl rfl⟩
      inv_mem' := by
        rintro g ⟨a, ha, hg⟩
        rcases hg with hg | hg
        · exact ⟨a⁻¹, A.inv_mem ha, Or.inl (by rw [hg])⟩
        · refine ⟨x * a⁻¹ * x, hN _ (A.inv_mem ha), Or.inr ?_⟩
          rw [hg]
          calc (a * x)⁻¹ = x⁻¹ * a⁻¹ := by group
            _ = x * a⁻¹ * (x * x) := by rw [hxinv, hx2, mul_one]
            _ = x * a⁻¹ * x * x := by group }
  have hle : A ⊔ Subgroup.zpowers x ≤ S :=
    sup_le (fun a ha => ⟨a, ha, Or.inl rfl⟩)
      ((Subgroup.zpowers_le).2 ⟨1, A.one_mem, Or.inr (by group)⟩)
  obtain ⟨a, ha, h | h⟩ := hle hg
  · exact Or.inl (h ▸ ha)
  · right
    rw [h, mul_assoc, hx2, mul_one]
    exact ha

theorem hom_eq_one_of_perfect {G : Type*} [Group G] {P K : Subgroup G} (hPK : P ≤ K)
    (hP : commutator ↥P = ⊤) {A : Type*} [CommGroup A] (ε : ↥K →* A) {p : G} (hp : p ∈ P) :
    ε ⟨p, hPK hp⟩ = 1 := by
  have h1 : commutator ↥P ≤ (ε.comp (Subgroup.inclusion hPK)).ker :=
    Abelianization.commutator_subset_ker _
  rw [hP] at h1
  exact h1 (Subgroup.mem_top (⟨p, hp⟩ : ↥P))

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section PermHom

variable {K : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

theorem exists_permHom {M : Type} [AddCommGroup M] [Module (ZMod 2) M] {n : ℕ}
    (R : Equiv.Perm (Fin n) →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (hR : Function.Injective R) (hJ : Invariant K J) (β : ↥J ≃ₗ[ZMod 2] M)
    (h : (restrictG K J hJ).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      R.range) :
    ∃ θ : ↥K →* Equiv.Perm (Fin n), Function.Surjective θ ∧
      ∀ (γ : ↥K) (x : ↥J),
        ((R (θ γ) : LinearMap.GeneralLinearGroup (ZMod 2) M) : M →ₗ[ZMod 2] M) (β x) =
          β (restrictHom K J hJ γ x) := by
  set c := LinearMap.GeneralLinearGroup.congrLinearEquiv β with hc
  set e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥J with he
  let ρ : ↥K →* LinearMap.GeneralLinearGroup (ZMod 2) M :=
    c.toMonoidHom.comp (e.symm.toMonoidHom.comp (restrictHom K J hJ))
  have hρR : ρ.range = R.range := by
    rw [← h, MonoidHom.range_comp, MonoidHom.range_comp]
    rfl
  have hmem : ∀ γ : ↥K, ρ γ ∈ R.range := fun γ => hρR ▸ ⟨γ, rfl⟩
  let θ : ↥K →* Equiv.Perm (Fin n) :=
    (MonoidHom.ofInjective hR).symm.toMonoidHom.comp (ρ.codRestrict R.range hmem)
  have hθ : ∀ γ : ↥K, R (θ γ) = ρ γ := by
    intro γ
    have h1 : (MonoidHom.ofInjective hR) (θ γ) = ρ.codRestrict R.range hmem γ :=
      (MonoidHom.ofInjective hR).apply_symm_apply _
    exact congrArg Subtype.val h1
  refine ⟨θ, ?_, ?_⟩
  · intro σ
    have : R σ ∈ ρ.range := hρR.symm ▸ ⟨σ, rfl⟩
    obtain ⟨γ, hγ⟩ := this
    refine ⟨γ, hR ?_⟩
    rw [hθ, hγ]
  · intro γ x
    rw [hθ]
    have h1 : ρ γ = c (e.symm (restrictHom K J hJ γ)) := rfl
    rw [h1, hc, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
    have hg : (e.symm (restrictHom K J hJ γ)).toLinearEquiv = restrictHom K J hJ γ :=
      e.apply_symm_apply _
    rw [LinearMap.GeneralLinearGroup.coe_ofLinearEquiv] 
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hg]

theorem permHom_eq_one_iff {M : Type} [AddCommGroup M] [Module (ZMod 2) M] {n : ℕ}
    (R : Equiv.Perm (Fin n) →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (hR : Function.Injective R) (hJ : Invariant K J) (β : ↥J ≃ₗ[ZMod 2] M)
    (θ : ↥K →* Equiv.Perm (Fin n))
    (hθ : ∀ (γ : ↥K) (x : ↥J),
        ((R (θ γ) : LinearMap.GeneralLinearGroup (ZMod 2) M) : M →ₗ[ZMod 2] M) (β x) =
          β (restrictHom K J hJ γ x)) (γ : ↥K) :
    θ γ = 1 ↔ restrictHom K J hJ γ = 1 := by
  constructor
  · intro h1
    ext x
    have := hθ γ x
    rw [h1, map_one] at this
    have h2 : β x = β (restrictHom K J hJ γ x) := by simpa using this
    have h3 : restrictHom K J hJ γ x = x := (β.injective h2).symm
    rw [h3]
    rfl
  · intro h1
    apply hR
    rw [map_one]
    apply Units.ext
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := β.surjective y
    rw [hθ γ x, h1]
    rfl

theorem faithfulOn_of_perm {M : Type} [AddCommGroup M] [Module (ZMod 2) M] {n : ℕ} (hn : 2 ≤ n)
    (R : Equiv.Perm (Fin n) →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (hR : Function.Injective R) (hJ : Invariant K J) (β : ↥J ≃ₗ[ZMod 2] M)
    (h : (restrictG K J hJ).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      R.range)
    {H : Subgroup (GLV V)} {a : GLV V} (hHK : H ≤ K) (haK : a ∈ K)
    (hKH : K ≤ H ⊔ Subgroup.zpowers a) (ha2 : a * a = 1) (hN : ∀ h ∈ H, a * h * a ∈ H)
    (hHf : FaithfulOn H J)
    (hε : ∀ ε : ↥K →* ℤˣ, ∀ (h : GLV V) (hh : h ∈ H), ε ⟨h, hHK hh⟩ = 1) :
    FaithfulOn K J := by
  obtain ⟨θ, hθs, hθ⟩ := exists_permHom R hR hJ β h
  rw [faithfulOn_iff]
  intro c hc hcJ
  by_contra hc1
  set ε : ↥K →* ℤˣ := Equiv.Perm.sign.comp θ with hεdef
  have hεc : ε ⟨c, hc⟩ = 1 := by
    have h1 : θ ⟨c, hc⟩ = 1 :=
      (permHom_eq_one_iff R hR hJ β θ hθ ⟨c, hc⟩).2 (restrictHom_eq_one_iff.2 hcJ)
    simp [hεdef, h1]
  rcases mem_or_mul_mem_of_normalizes ha2 hN (hKH hc) with hcH | hcaH
  · exact hc1 (faithfulOn_iff.1 hHf c hcH hcJ)
  · have hεa : ε ⟨a, haK⟩ = 1 := by
      have e1 : ε ⟨c * a, hHK hcaH⟩ = 1 := hε ε (c * a) hcaH
      have e2 : (⟨c * a, hHK hcaH⟩ : ↥K) = ⟨c, hc⟩ * ⟨a, haK⟩ := rfl
      rw [e2, map_mul, hεc, one_mul] at e1
      exact e1
    have hall : ∀ (k : GLV V) (hk : k ∈ K), ε ⟨k, hk⟩ = 1 := by
      intro k hk
      rcases mem_or_mul_mem_of_normalizes ha2 hN (hKH hk) with hkH | hkaH
      · exact hε ε k hkH
      · have e1 : ε ⟨k * a, hHK hkaH⟩ = 1 := hε ε (k * a) hkaH
        have e2 : (⟨k * a, hHK hkaH⟩ : ↥K) = ⟨k, hk⟩ * ⟨a, haK⟩ := rfl
        rw [e2, map_mul, hεa, mul_one] at e1
        exact e1
    have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h01
      have := congrArg Fin.val h01
      simp at this
    obtain ⟨γ, hγ⟩ := hθs (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)
    have h1 : ε γ = -1 := by
      simp [hεdef, hγ, Equiv.Perm.sign_swap hne]
    have h2 : ε γ = 1 := hall γ.1 γ.2
    rw [h1] at h2
    exact absurd h2 (by decide)

theorem exists_permEquiv {M : Type} [AddCommGroup M] [Module (ZMod 2) M] {n : ℕ}
    (R : Equiv.Perm (Fin n) →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (hR : Function.Injective R) (hJ : Invariant K J) (β : ↥J ≃ₗ[ZMod 2] M)
    (h : (restrictG K J hJ).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      R.range) (hf : FaithfulOn K J) :
    ∃ φ : ↥K ≃* Equiv.Perm (Fin n), ∀ (γ : ↥K) (x : ↥J),
      ((R (φ γ) : LinearMap.GeneralLinearGroup (ZMod 2) M) : M →ₗ[ZMod 2] M) (β x) =
        β (restrictHom K J hJ γ x) := by
  obtain ⟨θ, hθs, hθ⟩ := exists_permHom R hR hJ β h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h1 := (permHom_eq_one_iff R hR hJ β θ hθ γ).1 hγ
    exact restrictHom_injective_of_faithfulOn hJ hf (by rw [h1, map_one])
  exact ⟨MulEquiv.ofBijective θ ⟨hinj, hθs⟩, hθ⟩

end PermHom

section Natural

variable {K : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

@[expose] def permCoreEquiv (n : ℕ) : ↥(permCore n) ≃ₗ[ZMod 2] ↥(sumZero n) :=
  LinearEquiv.ofEq _ _ (Submodule.ext fun _ => Iff.rfl)

theorem coe_permCoreEquiv {n : ℕ} (u : ↥(permCore n)) :
    ((permCoreEquiv n u : ↥(sumZero n)) : Fin n → ZMod 2) = (u : Fin n → ZMod 2) := rfl

theorem isSymNatural_of_sumZero {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hJ : Invariant K J)
    (hf : FaithfulOn K J) (β : ↥J ≃ₗ[ZMod 2] ↥(sumZero n))
    (h : (restrictG K J hJ).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (sumZeroRep n).range) :
    CFSG.Quasithin.RonanG1016.IsSymNaturalSub K J n := by
  obtain ⟨φ, hφ⟩ := exists_permEquiv (sumZeroRep n) (sumZeroRep_injective' hn) hJ β h hf
  refine ⟨φ, ((permCoreEquiv n).trans β.symm).toLinearMap, ?_, ?_, ?_⟩
  · exact ((permCoreEquiv n).trans β.symm).surjective
  · intro u
    have hev : ¬ Even n := Nat.not_even_iff_odd.2 hodd
    simp only [LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, hev, false_and, or_false]
  · intro γ u u' hu
    set x : ↥J := ((permCoreEquiv n).trans β.symm) u with hx
    have h1 := hφ γ x
    have e1 : β x = permCoreEquiv n u := by
      rw [hx, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    have e2 : ((sumZeroRep n (φ γ) : LinearMap.GeneralLinearGroup (ZMod 2) ↥(sumZero n)) :
        ↥(sumZero n) →ₗ[ZMod 2] ↥(sumZero n)) (permCoreEquiv n u) = permCoreEquiv n u' := by
      apply Subtype.ext
      rw [sumZeroRep_apply, coe_sumZeroEquiv, coe_permCoreEquiv, coe_permCoreEquiv, hu]
      rfl
    rw [e1, e2] at h1
    have h2 : ((permCoreEquiv n).trans β.symm) u' = restrictHom K J hJ γ x := by
      rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
    show ((((permCoreEquiv n).trans β.symm) u' : ↥J) : V) = (γ : GLV V) ((x : ↥J) : V)
    rw [h2]
    rfl

theorem isSymNatural_of_heart {n : ℕ} (hn : 5 ≤ n) (hev : Even n) (hJ : Invariant K J)
    (hf : FaithfulOn K J) (β : ↥J ≃ₗ[ZMod 2] (↥(sumZero n) ⧸ onesLine n))
    (h : (restrictG K J hJ).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (heartRep n).range) :
    CFSG.Quasithin.RonanG1016.IsSymNaturalSub K J n := by
  obtain ⟨φ, hφ⟩ := exists_permEquiv (heartRep n) (heartRep_injective' hn) hJ β h hf
  let q : ↥(permCore n) →ₗ[ZMod 2] ↥J :=
    (β.symm : (↥(sumZero n) ⧸ onesLine n) →ₗ[ZMod 2] ↥J) ∘ₗ (onesLine n).mkQ ∘ₗ
      (permCoreEquiv n).toLinearMap
  have hq : ∀ u, q u = β.symm (Submodule.Quotient.mk (permCoreEquiv n u)) := fun u => rfl
  refine ⟨φ, q, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective (onesLine n) (β y)
    obtain ⟨u, rfl⟩ := (permCoreEquiv n).surjective z
    exact ⟨u, by rw [hq, hz, LinearEquiv.symm_apply_apply]⟩
  · intro u
    rw [hq, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, mem_onesLine]
    constructor
    · rintro ⟨c, hc⟩
      have hc' : (u : Fin n → ZMod 2) = fun _ => c := hc
      have hcc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hcc c with rfl | rfl
      · left
        exact Subtype.ext hc'
      · right
        exact ⟨hev, fun i => by rw [hc']⟩
    · rintro (rfl | ⟨-, hu⟩)
      · exact ⟨0, rfl⟩
      · exact ⟨1, funext hu⟩
  · intro γ u u' hu
    set x : ↥J := q u with hx
    have h1 := hφ γ x
    have e1 : β x = Submodule.Quotient.mk (permCoreEquiv n u) := by
      rw [hx, hq, LinearEquiv.apply_symm_apply]
    have e2 : ((heartRep n (φ γ) : LinearMap.GeneralLinearGroup (ZMod 2)
        (↥(sumZero n) ⧸ onesLine n)) : (↥(sumZero n) ⧸ onesLine n) →ₗ[ZMod 2]
          (↥(sumZero n) ⧸ onesLine n)) (Submodule.Quotient.mk (permCoreEquiv n u)) =
        Submodule.Quotient.mk (permCoreEquiv n u') := by
      rw [heartRep_apply_mk]
      congr 1
      apply Subtype.ext
      rw [coe_sumZeroEquiv, coe_permCoreEquiv, coe_permCoreEquiv, hu]
      rfl
    rw [e1, e2] at h1
    have h2 : q u' = restrictHom K J hJ γ x := by
      rw [hq, h1, LinearEquiv.symm_apply_apply]
    show ((q u' : ↥J) : V) = (γ : GLV V) ((x : ↥J) : V)
    rw [h2]
    rfl

end Natural

end G11

end CFSG.Quasithin
