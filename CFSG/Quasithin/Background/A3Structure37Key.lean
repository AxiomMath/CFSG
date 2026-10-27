
module

public import CFSG.Quasithin.Background.A3Structure37KeyBase

public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure37Frattini

public section

namespace CFSG.Quasithin

namespace A37

open scoped commutatorElement

theorem centralizes_pCore {G : Type} [Group G] [Finite G] {L₁ L₂ : Subgroup G}
    (hn : L₂ ≤ Subgroup.normalizer (L₁ : Set G))
    [Group.IsPerfect ↥L₁] [Group.IsPerfect ↥L₂]
    (hc : ⁅L₁, L₂⁆ ≤ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype)
    (hF : CFSG.fittingSubgroup ↥L₁ ≠ ⊤)
    (hX : A36Extra ↥L₁) {q : ℕ} (hq : q.Prime)
    (hqF : q ∣ Nat.card (CFSG.fittingSubgroup ↥L₁)) :
    ∀ g ∈ L₂, ∀ r ∈ (CFSG.pCore q ↥L₁).map L₁.subtype, g * r = r * g := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hsc, hfaith, hcase, hker⟩ := hX q hq hqF
  have hPchar : P.Characteristic := hsc.characteristic
  have hPp : IsPGroup q ↥P := (CFSG.pCore_isPGroup (G := ↥L₁) (p := q)).to_subgroup P
  have hVcard : Nat.card (↥P ⧸ frattini ↥P) = q ^ 2 := card_frattini_quotient_two hq hPp hcase
  let _ : CommGroup (↥P ⧸ frattini ↥P) :=
    { (inferInstance : Group (↥P ⧸ frattini ↥P)) with
      mul_comm := frattiniQuotient_mul_comm hq hPp }
  let R : Subgroup ↥L₁ := CFSG.pCore q ↥L₁
  let Θ : MulAut ↥L₁ →* MulAut (↥P ⧸ frattini ↥P) := frattiniActionX R P
  let ρ₂ : ↥L₂ →* MulAut ↥L₁ := (Subgroup.normalizerMonoidHom L₁).comp (Subgroup.inclusion hn)
  have hρ₂ : ∀ (g : ↥L₂) (y : ↥L₁), ((ρ₂ g y : ↥L₁) : G) = (g : G) * y * (g : G)⁻¹ := by
    intro g y
    simp [ρ₂]
  let S : Subgroup (MulAut (↥P ⧸ frattini ↥P)) := (Θ.comp MulAut.conj).range
  let T : Subgroup (MulAut (↥P ⧸ frattini ↥P)) := (Θ.comp ρ₂).range
  have hSperf : ⁅S, S⁆ = S := by
    have : Group.IsPerfect ↥S := Group.IsPerfect.range _
    exact Subgroup.commutator_eq_self
  have hTperf : ⁅T, T⁆ = T := by
    have : Group.IsPerfect ↥T := Group.IsPerfect.range _
    exact Subgroup.commutator_eq_self
  have hSne : S ≠ ⊥ := by
    obtain ⟨x, hx⟩ : ∃ x : ↥L₁, x ∉ CFSG.fittingSubgroup ↥L₁ := by
      by_contra hcon
      push Not at hcon
      exact hF (eq_top_iff.2 fun x _ => hcon x)
    intro hbot
    have h1 : Θ (MulAut.conj x) ∈ S := ⟨x, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : MulAut.conj x ∈ Θ.ker := h1
    rw [conj_mem_ker_frattiniActionX_iff R P] at h2
    exact hx ((hker x).1 h2)
  have hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s := by
    rintro _ ⟨x, rfl⟩ _ ⟨g, rfl⟩
    have hgx : ⁅(g : G), (x : G)⁆ ∈ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype := by
      apply hc
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator g.2 x.2
    obtain ⟨f, hfF, hf⟩ := hgx
    have hfx : ρ₂ g x = f * x := by
      apply Subtype.ext
      rw [hρ₂]
      have hf' : (f : G) = ⁅(g : G), (x : G)⁆ := hf
      show (g : G) * x * (g : G)⁻¹ = (f : G) * x
      rw [hf', commutatorElement_def]
      group
    have hfker : MulAut.conj f ∈ Θ.ker := by
      rw [conj_mem_ker_frattiniActionX_iff R P]
      exact (hker f).2 hfF
    have key : Θ (ρ₂ g) * Θ (MulAut.conj x) * (Θ (ρ₂ g))⁻¹ = Θ (MulAut.conj x) := by
      rw [← map_inv, ← map_mul, ← map_mul, mulAut_conj_conj, hfx, map_mul, map_mul,
        MonoidHom.mem_ker.1 hfker, one_mul]
    show Θ (MulAut.conj x) * Θ (ρ₂ g) = Θ (ρ₂ g) * Θ (MulAut.conj x)
    exact ((mul_inv_eq_iff_eq_mul.1 key)).symm
  have hTbot : T = ⊥ := eq_bot_of_commute hq hVcard S T hSperf hSne hTperf hcomm
  have hΘ : ∀ g : ↥L₂, Θ (ρ₂ g) = 1 := fun g => by
    have : Θ (ρ₂ g) ∈ T := ⟨g, rfl⟩
    rw [hTbot, Subgroup.mem_bot] at this
    exact this
  let φ : ↥L₂ →* MulAut ↥R := (MulAut.characteristic R).comp ρ₂
  let A : Subgroup (MulAut ↥R) := φ.range
  have hact : ∀ g : ↥L₂, ∀ x ∈ P, x⁻¹ * (φ g) x ∈ frattiniIn P := fun g =>
    (mem_ker_frattiniActionX R P).1 (MonoidHom.mem_ker.2 (hΘ g))
  have : Finite (MulAut ↥R) :=
    Finite.of_injective (fun f : MulAut ↥R => (f : ↥R → ↥R)) DFunLike.coe_injective
  have hApgrp : IsPGroup q ↥A := by
    refine CFSG.SectionRank.Ccomm.isPGroup_of_forall_prime_orderOf (p := q) fun a ℓ hℓ hord => ?_
    by_contra hne
    obtain ⟨g, hg⟩ := a.2
    have hcop : (orderOf (a : MulAut ↥R)).Coprime q := by
      rw [Subgroup.orderOf_coe, hord]
      exact (Nat.coprime_primes hℓ hq).2 hne
    have h1 : (a : MulAut ↥R) = 1 :=
      hfaith _ hcop (fun x hx => by rw [← hg]; exact hact g x hx)
    have h2 : a = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hord
    exact hℓ.ne_one hord.symm
  have hAbot : A = ⊥ := by
    by_contra hne
    have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).2 hne
    have : Group.IsPerfect ↥A := Group.IsPerfect.range _
    have : Group.IsNilpotent ↥A := hApgrp.isNilpotent
    exact Group.IsPerfect.not_isNilpotent ↥A inferInstance
  intro g hg r hr
  obtain ⟨y, hy, rfl⟩ := hr
  have h1 : φ ⟨g, hg⟩ = 1 := by
    have : φ ⟨g, hg⟩ ∈ A := ⟨_, rfl⟩
    rw [hAbot, Subgroup.mem_bot] at this
    exact this
  have h2 : ρ₂ ⟨g, hg⟩ y = y := by
    have := congrArg (fun z : MulAut ↥R => ((z ⟨y, hy⟩ : ↥R) : ↥L₁)) h1
    exact this
  have h3 := congrArg (fun z : ↥L₁ => (z : G)) h2
  simp only [hρ₂] at h3
  show g * (y : G) = (y : G) * g
  exact (mul_inv_eq_iff_eq_mul.1 h3)

theorem centralizes_fitting {G : Type} [Group G] [Finite G] {L₁ L₂ : Subgroup G}
    (hn : L₂ ≤ Subgroup.normalizer (L₁ : Set G))
    [Group.IsPerfect ↥L₁] [Group.IsPerfect ↥L₂]
    (hc : ⁅L₁, L₂⁆ ≤ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype)
    (hF : CFSG.fittingSubgroup ↥L₁ ≠ ⊤) (hX : A36Extra ↥L₁) :
    ⁅(CFSG.fittingSubgroup ↥L₁).map L₁.subtype, L₂⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.map_le_iff_le_comap,
    CFSG.fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  have hq : (p.1.1).Prime := Nat.prime_of_mem_primeFactors p.1.2
  have : Fact (p.1.1).Prime := ⟨hq⟩
  intro y hy
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hqF : p.1.1 ∣ Nat.card (CFSG.fittingSubgroup ↥L₁)
  · exact centralizes_pCore hn hc hF hX hq hqF g hg _ ⟨y, hy, rfl⟩
  · have hle : CFSG.pCore p.1.1 ↥L₁ ≤ CFSG.fittingSubgroup ↥L₁ := CFSG.pCore_le_fitting _ _
    have hbot : CFSG.pCore p.1.1 ↥L₁ = ⊥ := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥L₁) (p := p.1.1)).exists_card_eq
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, pow_zero] at hk
        exact Subgroup.card_eq_one.1 hk
      · exact absurd ((dvd_pow_self _ hpos.ne').trans (hk ▸ Subgroup.card_dvd_of_le hle)) hqF
    have hy1 : y = 1 := by
      have := hy
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [hy1]
    simp

end A37

end CFSG.Quasithin
