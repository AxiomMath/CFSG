module

public import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianLift
public import CFSG.SignalizerFunctorTheorem.NonLocal.Nondegenerate

public section

open Module Module.End CFSG.SignalizerFunctorTheorem.NonLocal
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

section Extension

variable (K F : Type*) [Field K] [Field F] [Algebra K F] (ι : Type*) [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def extendScalars : Matrix ι ι K →+* Module.End F (ι → F) :=
  (Matrix.toLinAlgEquiv' (R := F) (n := ι)).toAlgHom.toRingHom.comp
    (algebraMap K F).mapMatrix

theorem extendScalars_injective : Function.Injective (extendScalars K F ι) := by
  intro a b h
  have h1 := (Matrix.toLinAlgEquiv' (R := F) (n := ι)).injective h
  exact Matrix.map_injective (algebraMap K F).injective h1

theorem extendScalars_scalar (c : K) :
    extendScalars K F ι (Matrix.scalar ι c) = (algebraMap K F c) • (1 : Module.End F (ι → F)) := by
  ext v i
  simp [extendScalars, Matrix.scalar_apply, Matrix.mulVec_diagonal, Algebra.smul_def]

theorem exists_scalar_of_extendScalars [Nonempty ι] (M : Matrix ι ι K) (c : F)
    (h : extendScalars K F ι M = c • 1) : ∃ c₀ : K, M = Matrix.scalar ι c₀ := by
  have hent : ∀ i j, algebraMap K F (M i j) = if i = j then c else 0 := by
    intro i j
    have := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
    simpa [extendScalars, Matrix.mulVec_single_one, Pi.single_apply] using this
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hc : c = algebraMap K F (M i₀ i₀) := by simpa using (hent i₀ i₀).symm
  refine ⟨M i₀ i₀, ?_⟩
  ext i j
  apply (algebraMap K F).injective
  rw [hent i j]
  by_cases hij : i = j
  · subst hij; simp [Matrix.scalar_apply, hc]
  · simp [Matrix.scalar_apply, hij]

end Extension


structure ProjData (K : Type*) [Field K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (H X : Type*) [Group H] [Group X] where
  ρ : H →* Matrix.GeneralLinearGroup ι K
  hρ : Function.Injective ρ
  π : H →* X
  hπ : Function.Surjective π
  hker : ∀ h, π h = 1 ↔ ∃ c : Kˣ, (ρ h : Matrix ι ι K) = Matrix.scalar ι (c : K)

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {H X : Type*} [Group H]
  [Group X]

namespace ProjData

variable (P : ProjData K ι H X) (F : Type*) [Field F] [Algebra K F]

@[expose] noncomputable def rhoBar : H →* Module.End F (ι → F) :=
  (extendScalars K F ι : Matrix ι ι K →+* Module.End F (ι → F)).toMonoidHom.comp
    ((Units.coeHom (Matrix ι ι K)).comp P.ρ)

theorem rhoBar_apply (h : H) : P.rhoBar F h = extendScalars K F ι (P.ρ h : Matrix ι ι K) := rfl

theorem rhoBar_injective : Function.Injective (P.rhoBar F) := by
  intro a b h
  apply P.hρ
  apply Units.ext
  exact extendScalars_injective K F ι h

theorem ker_iff [Nonempty ι] (h : H) : P.π h = 1 ↔ ∃ c : F, P.rhoBar F h = c • 1 := by
  rw [P.hker]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨algebraMap K F c, ?_⟩
    rw [rhoBar_apply, hc, extendScalars_scalar]
  · rintro ⟨c, hc⟩
    obtain ⟨c₀, hc₀⟩ := exists_scalar_of_extendScalars K F ι _ c hc
    have hc₀' : (P.ρ h : Matrix ι ι K) = Matrix.scalar ι c₀ := hc₀
    have hc0 : c₀ ≠ 0 := by
      rintro rfl
      have h1 : (P.ρ h : Matrix ι ι K) = 0 := by rw [hc₀']; simp
      have h2 := Units.inv_mul (P.ρ h)
      rw [h1, mul_zero] at h2
      obtain ⟨i⟩ := ‹Nonempty ι›
      have := congrFun (congrFun h2 i) i
      simp at this
    exact ⟨Units.mk0 c₀ hc0, by simpa using hc₀'⟩

end ProjData



theorem ProjData.card_le_of_minimal [Finite H] [Nonempty ι] [Finite K] {r s : ℕ} [Fact r.Prime]
    [CharP K r] (P : ProjData K ι H X) (hs : s.Prime) (hrs : s ≠ r)
    {Γ : Type*} [Group Γ] (φH : Γ →* H) (V : Subgroup X) [IsMulCommutative V]
    (hVexp : ∀ v ∈ V, v ^ s = 1)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V)
    (hmin : ∀ V' : Subgroup X, V' ≤ V → V' ≠ ⊥ →
      (∀ g : Γ, ∀ v ∈ V', P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V') → V' = V) :
    Nat.card V ≤ s ^ (Fintype.card ι - 1) ∨
      ∃ e : ℕ, e ≤ Fintype.card ι ∧ e ∣ Nat.card V ∧ Nat.card V ≤ e ^ 2 := by
  classical
  let F := AlgebraicClosure K
  have hFchar : CharP F r := charP_of_injective_algebraMap (algebraMap K F).injective r
  let Vt : Subgroup H := V.comap P.π
  let π' : Vt →* V := (P.π.comp Vt.subtype).codRestrict V (fun h => h.2)
  have hπ'surj : Function.Surjective π' := by
    intro v
    obtain ⟨h, hh⟩ := P.hπ v
    exact ⟨⟨h, by simp [Vt, hh]⟩, Subtype.ext hh⟩
  let Zs : Subgroup Vt := π'.ker
  have hZs : ∀ g : Vt, g ∈ Zs ↔ ∃ c : F, (P.rhoBar F).comp Vt.subtype g = c • 1 := by
    intro g
    have h1 : π' g = 1 ↔ P.π (g : H) = 1 := by
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [MonoidHom.mem_ker, h1, P.ker_iff F]
    rfl
  have hcard : Nat.card Vt = Nat.card V * Nat.card Zs := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zs,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π' hπ'surj).toEquiv]
  have : Finite X := Finite.of_surjective P.π P.hπ
  have := Fintype.ofFinite K
  have hq : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hrq : r ∣ Nat.card K := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K r
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self r n.ne_zero
  have hKdvd : ∀ g : Vt, g ∈ Zs → (g : H) ^ (Nat.card K - 1) = 1 := by
    intro g hg
    have hg1 : P.π (g : H) = 1 := by
      have := (MonoidHom.mem_ker.mp hg)
      exact congrArg Subtype.val this
    obtain ⟨c, hc⟩ := (P.hker _).mp hg1
    apply P.hρ
    apply Units.ext
    have hc1 : ((c : K)) ^ (Nat.card K - 1) = 1 := by
      rw [hq]
      exact FiniteField.pow_card_sub_one_eq_one _ c.ne_zero
    rw [map_pow, Units.val_pow_eq_pow_val, hc, ← map_pow, hc1]
    simp
  have hZsr : ¬ r ∣ Nat.card Zs := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Zs) r h
    have h1 : (z : Vt) ^ (Nat.card K - 1) = 1 := by
      apply Subtype.ext
      exact hKdvd z z.2
    have h2 : r ∣ Nat.card K - 1 := by
      rw [← hz]
      exact orderOf_dvd_of_pow_eq_one (by
        have : (z : Zs) ^ (Nat.card K - 1) = 1 := Subtype.ext h1
        exact this)
    have h3 : r ∣ 1 := by
      have h4 : 1 ≤ Nat.card K := Nat.card_pos
      have := Nat.dvd_sub hrq h2
      rwa [Nat.sub_sub_self h4] at this
    exact (Fact.out : r.Prime).one_lt.ne' (Nat.dvd_one.mp h3)
  have hVr : ¬ r ∣ Nat.card V := by
    intro h
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) r h
    have h1 : (v : V) ^ s = 1 := Subtype.ext (hVexp v v.2)
    have h2 : r ∣ s := by
      rw [← hv]
      exact orderOf_dvd_of_pow_eq_one h1
    exact hrs ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) hs).mp h2).symm
  have hinv : (Nat.card Vt : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F r, hcard]
    exact fun h => ((Nat.Prime.dvd_mul Fact.out).mp h).elim hVr hZsr
  let ρ' : Vt →* Module.End F (ι → F) := (P.rhoBar F).comp Vt.subtype
  have hρ' : Function.Injective ρ' := (P.rhoBar_injective F).comp Subtype.val_injective
  have hd : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
  have hZpos : 0 < Nat.card Zs := Nat.card_pos
  let V₀ : Subgroup X := (Subgroup.center Vt).map (P.π.comp Vt.subtype)
  have hV₀V : V₀ ≤ V := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hVtnorm : ∀ g : Γ, ∀ y ∈ Vt, φH g * y * (φH g)⁻¹ ∈ Vt := by
    intro g y hy
    show P.π (φH g * y * (φH g)⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact hnorm g _ hy
  have hV₀norm : ∀ g : Γ, ∀ v ∈ V₀, P.π (φH g) * v * (P.π (φH g))⁻¹ ∈ V₀ := by
    rintro g _ ⟨z, hz, rfl⟩
    have hzV : φH g * (z : H) * (φH g)⁻¹ ∈ Vt := hVtnorm g z z.2
    refine ⟨⟨_, hzV⟩, ?_, ?_⟩
    · show _ ∈ Subgroup.center Vt
      rw [Subgroup.mem_center_iff]
      intro y
      have hy' : (φH g)⁻¹ * (y : H) * φH g ∈ Vt := by
        have := hVtnorm g⁻¹ y y.2
        simpa [map_inv] using this
      have hzc := Subgroup.mem_center_iff.mp (show z ∈ Subgroup.center Vt from hz) ⟨_, hy'⟩
      apply Subtype.ext
      have h5 := congrArg Subtype.val hzc
      simp only [Subgroup.coe_mul] at h5 ⊢
      calc (y : H) * (φH g * z * (φH g)⁻¹)
          = φH g * (((φH g)⁻¹ * y * φH g) * z) * (φH g)⁻¹ := by group
        _ = φH g * (z * ((φH g)⁻¹ * y * φH g)) * (φH g)⁻¹ := by rw [h5]
        _ = (φH g * z * (φH g)⁻¹) * y := by group
    · simp [map_mul, map_inv]
  have hZcentral : ∀ g : Vt, g ∈ Zs → g ∈ Subgroup.center Vt := by
    intro g hg
    obtain ⟨c, hc⟩ := (hZs g).mp hg
    rw [Subgroup.mem_center_iff]
    intro y
    apply hρ'
    rw [map_mul, map_mul]
    have : ρ' g = c • 1 := hc
    rw [this]
    ext x
    simp
  have hKdvd' := hKdvd
  rcases eq_or_ne V₀ ⊥ with h0 | h0
  ·
    right
    have hcomm : ∀ a b : Vt, ⁅a, b⁆ ∈ Zs := by
      intro a b
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact (commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' (π' a) (π' b)))
    have hcenter : ∀ a : Vt, (∀ b, a * b = b * a) → a ∈ Zs := by
      intro a ha
      have hmem : a ∈ Subgroup.center Vt := Subgroup.mem_center_iff.mpr (fun b => (ha b).symm)
      have h1 : P.π (a : H) ∈ V₀ := ⟨a, hmem, rfl⟩
      rw [h0, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    obtain ⟨e, he, hdvd, hle⟩ := card_le_sq_of_nondegenerate ρ' hρ' Zs hZs hcomm hcenter hinv
    rw [hcard, hd] at *
    refine ⟨e, he, ?_, ?_⟩
    · rw [mul_comm (Nat.card V)] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left hZpos hdvd
    · rw [mul_comm (Nat.card V)] at hle
      exact Nat.le_of_mul_le_mul_left hle hZpos
  ·
    left
    have hV₀V' : V₀ = V := hmin V₀ hV₀V h0 hV₀norm
    have hab : ∀ a : Vt, a ∈ Subgroup.center Vt := by
      intro a
      have h1 : P.π (a : H) ∈ V₀ := by rw [hV₀V']; exact a.2
      obtain ⟨z, hz, hza⟩ := h1
      have hza' : P.π (z : H) = P.π (a : H) := hza
      have h2 : a * z⁻¹ ∈ Zs := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        show P.π (((a * z⁻¹ : Vt)) : H) = 1
        simp [map_mul, map_inv, hza']
      have h3 := hZcentral _ h2
      have : a = (a * z⁻¹) * z := by group
      rw [this]
      exact Subgroup.mul_mem _ h3 hz
    have hcommT : IsMulCommutative (⊤ : Subgroup Vt) :=
      ⟨⟨fun x y => Subtype.ext (by
        have := Subgroup.mem_center_iff.mp (hab x.1) y.1
        exact this.symm)⟩⟩
    have hexp : ∀ a ∈ (⊤ : Subgroup Vt), a ^ s ∈ Zs := by
      intro a _
      rw [MonoidHom.mem_ker, map_pow]
      exact Subtype.ext (hVexp _ (π' a).2)
    have hinvT : (Nat.card (⊤ : Subgroup Vt) : F) ≠ 0 := by
      rw [Subgroup.card_top]
      exact hinv
    have hb := card_le_of_abelian_mod_scalars hs.pos ρ' Zs ⊤ hcommT hinvT le_top hZs hexp
    rw [Subgroup.card_top, hcard, hd, mul_comm (Nat.card V)] at hb
    exact Nat.le_of_mul_le_mul_left hb hZpos


end CFSG.SignalizerFunctorTheorem.NonLocal
