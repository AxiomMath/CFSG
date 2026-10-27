module

public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut szFieldAut_S
  szFieldAut_injective)
open CFSG.LieType.Suzuki (suzukiGroup_outer_isCyclic_card_dvd)
open CFSG.LocalAnalysis.ComponentInitial (Suzuki_model_opposite_root_interface
  card_ringAut_and_isCyclic)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification (OuterAutomorphisms.inner)

variable {a : ℕ} {K : Type} [Field K]

theorem exists_conj_suzukiSElt [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u₀ v₀ : K)
    (l : Kˣ) (c d : K) :
    ∃ w : K, suzukiSElt a K u₀ v₀ * suzukiDElt a K l * suzukiSElt a K c d *
      (suzukiSElt a K u₀ v₀ * suzukiDElt a K l)⁻¹ = suzukiSElt a K ((l⁻¹ : Kˣ) * c) w := by
  have : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  rw [show suzukiSElt a K u₀ v₀ * suzukiDElt a K l * suzukiSElt a K c d *
      (suzukiSElt a K u₀ v₀ * suzukiDElt a K l)⁻¹ = suzukiSElt a K u₀ v₀ *
        (suzukiDElt a K l * suzukiSElt a K c d * (suzukiDElt a K l)⁻¹) *
          (suzukiSElt a K u₀ v₀)⁻¹ by group, suzukiDElt_conj' hK, suzukiSElt_inv hK,
    suzukiSElt_mul hK, suzukiSElt_mul hK]
  refine ⟨_, congrArg₂ (suzukiSElt a K) ?_ rfl⟩
  rw [add_comm u₀, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem eq_one_of_szFieldAut_mem_inner (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : RingAut K}
    (hσ : szFieldAut a K σ ∈ OuterAutomorphisms.inner (suzukiGroup a K)) : σ = 1 := by
  obtain ⟨g, hg⟩ := hσ
  have hconj : ∀ x, g * x * g⁻¹ = szFieldAut a K σ x := fun x => by
    rw [← hg]
    rfl
  have hU : ∀ τ : RingAut K, ∀ x ∈ suzukiU a K, szFieldAut a K τ x ∈ suzukiU a K := by
    intro τ x hx
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
    rw [szFieldAut_S]
    exact suzukiSElt_mem_suzukiU a K _ _
  have hgN : g ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [hconj]
      exact hU σ x hx
    · rw [hconj] at hx
      have h := hU σ⁻¹ _ hx
      rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h
  obtain ⟨-, -, hNB, -⟩ := Suzuki_model_opposite_root_interface ha hK
  rw [hNB] at hgN
  obtain ⟨⟨⟨u₀, v₀⟩, l⟩, hgB, -⟩ := (suzuki_borel_structure hK).2.2.2.2.2.2.1 g hgN
  simp only at hgB
  have hfst : ∀ c : K, σ c = ((l⁻¹ : Kˣ) : K) * c := by
    intro c
    obtain ⟨w, hw⟩ := exists_conj_suzukiSElt hK u₀ v₀ l c 0
    rw [← hgB, hconj, szFieldAut_S] at hw
    exact (suzukiSElt_inj.1 hw).1
  have hl : ((l⁻¹ : Kˣ) : K) = 1 := by
    have h := hfst 1
    rwa [map_one, mul_one, eq_comm] at h
  exact RingEquiv.ext fun c => by rw [hfst, hl, one_mul, RingAut.one_apply]

theorem Suzuki_full_field_automorphism_splitting (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ (σ : RingAut K) (g : suzukiGroup a K),
      (((szFieldAut a K σ g : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ) ∧
    (∃ e : suzukiGroup a K ⋊[szFieldAut a K] RingAut K ≃* MulAut (suzukiGroup a K),
      ∀ (g : suzukiGroup a K) (σ : RingAut K), e ⟨g, σ⟩ = MulAut.conj g * szFieldAut a K σ) ∧
    Nat.card (szFieldAut a K).range = 2 * a + 1 ∧
    (szFieldAut a K).range ⊓ OuterAutomorphisms.inner (suzukiGroup a K) = ⊥ ∧
    IsCyclic (Outer (suzukiGroup a K)) ∧ Nat.card (Outer (suzukiGroup a K)) = 2 * a + 1 ∧
    Odd (Nat.card (Outer (suzukiGroup a K))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨hcardAut, -⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hinf : (szFieldAut a K).range ⊓ OuterAutomorphisms.inner (suzukiGroup a K) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨σ, rfl⟩, hσ⟩
    rw [eq_one_of_szFieldAut_mem_inner ha hK hσ, map_one]
    exact Subgroup.one_mem _
  set π : RingAut K →* Outer (suzukiGroup a K) :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner (suzukiGroup a K))).comp (szFieldAut a K)
    with hπ
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    exact eq_one_of_szFieldAut_mem_inner ha hK ((QuotientGroup.eq_one_iff _).1 hσ)
  obtain ⟨hOcyc, hOdvd⟩ := suzukiGroup_outer_isCyclic_card_dvd ha hK
  have : Finite (Outer (suzukiGroup a K)) :=
    Nat.finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero (by omega) hOdvd)
  have hOcard : Nat.card (Outer (suzukiGroup a K)) = 2 * a + 1 := by
    refine Nat.dvd_antisymm hOdvd ?_
    rw [← hcardAut]
    exact Subgroup.card_dvd_of_injective π hπinj
  have hπsurj : Function.Surjective π :=
    (Function.Injective.bijective_of_nat_card_le hπinj (by rw [hcardAut, hOcard])).2
  have hdecomp : ∀ α : MulAut (suzukiGroup a K), ∃ (g : suzukiGroup a K) (σ : RingAut K),
      α = MulAut.conj g * szFieldAut a K σ := by
    intro α
    obtain ⟨σ, hσ⟩ := hπsurj (QuotientGroup.mk α)
    have hmem : α * (szFieldAut a K σ)⁻¹ ∈ OuterAutomorphisms.inner (suzukiGroup a K) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (QuotientGroup.mk α : Outer (suzukiGroup a K)) * (π σ)⁻¹ = 1
      rw [hσ, mul_inv_cancel]
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, σ, by rw [hg, inv_mul_cancel_right]⟩
  obtain ⟨-, -, hsimple⟩ := suzuki_simple ha hK
  have hcenter : Subgroup.center (suzukiGroup a K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup a K)) with
      h | h
    · exact h
    · have h1 := (suzuki_perfect ha hK).1
      rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
      exact absurd h1 bot_ne_top
  have hcomm : ∀ σ : RingAut K,
      (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).comp
          (szFieldAut a K σ).toMonoidHom =
        (MulAut.conj (szFieldAut a K σ)).toMonoidHom.comp MulAut.conj := by
    intro σ
    refine MonoidHom.ext fun g => MulEquiv.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  set Φ := SemidirectProduct.lift MulAut.conj (szFieldAut a K) hcomm with hΦdef
  have hΦ : ∀ g σ, Φ ⟨g, σ⟩ = MulAut.conj g * szFieldAut a K σ := fun g σ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, σ⟩ h
    rw [hΦ] at h
    have hσ : szFieldAut a K σ ∈ OuterAutomorphisms.inner (suzukiGroup a K) :=
      ⟨g⁻¹, by rw [map_inv]; exact (eq_inv_of_mul_eq_one_right h).symm⟩
    have hσ1 := eq_one_of_szFieldAut_mem_inner ha hK hσ
    rw [hσ1, map_one, mul_one] at h
    have hg : g ∈ Subgroup.center (suzukiGroup a K) := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun e : MulAut (suzukiGroup a K) => e x) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * g = g * x * g⁻¹ * g := by rw [hx]
        _ = g * x := by group
    rw [hcenter, Subgroup.mem_bot] at hg
    rw [hg, hσ1]
    rfl
  have hΦsurj : Function.Surjective Φ := fun α => by
    obtain ⟨g, σ, rfl⟩ := hdecomp α
    exact ⟨⟨g, σ⟩, rfl⟩
  refine ⟨fun σ g => coe_szFieldAut σ g,
    ⟨MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩, fun g σ => rfl⟩, ?_, hinf, hOcyc, hOcard, ?_⟩
  · rw [← hcardAut]
    exact Nat.card_range_of_injective szFieldAut_injective
  · rw [hOcard]
    exact odd_two_mul_add_one a

end CFSG.RankThree.Automorphisms
