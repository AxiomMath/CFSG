module

public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpC
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.G9Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

section General

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall_conj_mem {Γ H : Subgroup G}
    (h : ∀ γ ∈ Γ, ∀ x ∈ H, γ * x * γ⁻¹ ∈ H) : Γ ≤ Subgroup.normalizer (H : Set G) := by
  intro γ hγ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h γ hγ x hx, fun hx => ?_⟩
  have := h γ⁻¹ (Γ.inv_mem hγ) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_fitting (Γ : Subgroup G) :
    Γ ≤ Subgroup.normalizer (((genFittingFitting ↥Γ).map Γ.subtype : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun γ hγ x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hN : (genFittingFitting ↥Γ).Normal := CFSG.fittingSubgroup_normal
  exact Subgroup.mem_map.2 ⟨⟨γ, hγ⟩ * y * ⟨γ, hγ⟩⁻¹, hN.conj_mem y hy ⟨γ, hγ⟩, by simp⟩

variable [Finite G]

theorem isNilpotent_fitting_map (Γ : Subgroup G) :
    Group.IsNilpotent ↥((genFittingFitting ↥Γ).map Γ.subtype) := by
  have : Group.IsNilpotent ↥(genFittingFitting ↥Γ) := CFSG.fittingSubgroup_nilpotent
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective (genFittingFitting ↥Γ) Γ.subtype Γ.subtype_injective)

theorem pCoreOf_le_fitting {p : ℕ} (hp : p.Prime) (Γ : Subgroup G) :
    pCoreOf p Γ ≤ (genFittingFitting ↥Γ).map Γ.subtype := by
  have : Fact p.Prime := ⟨hp⟩
  refine Subgroup.map_mono ?_
  have h : Open.pCore p ↥Γ = CFSG.pCore p ↥Γ := (CFSG.pCore_eq_open _ _).symm
  exact CFSG.pCore_le_fitting ↥Γ p

theorem card_pCoreOf_eq_fitting {p : ℕ} (hp : p.Prime) (Γ : Subgroup G) :
    Nat.card ↥(pCoreOf p Γ) =
      p ^ (Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype)).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hN : genFittingFitting ↥Γ = CFSG.fittingSubgroup ↥Γ := rfl
  set N : Subgroup ↥Γ := CFSG.fittingSubgroup ↥Γ with hNdef
  have hmapN : Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype) = Nat.card ↥N := by
    rw [hN]
    exact Subgroup.card_map_of_injective Γ.subtype_injective
  have hQ : Nat.card ↥(pCoreOf p Γ) = Nat.card ↥(CFSG.pCore p ↥Γ) := by
    rw [pCoreOf, Subgroup.card_map_of_injective Γ.subtype_injective]
  rw [hmapN, hQ]
  let P : Sylow p ↥N := default
  have hP : Nat.card ↥(P : Subgroup ↥N) = p ^ (Nat.card ↥N).factorization p :=
    P.card_eq_multiplicity
  have hle1 : P.map N.subtype ≤ CFSG.pCore p ↥Γ :=
    Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent p P
  have h1 : p ^ (Nat.card ↥N).factorization p ≤ Nat.card ↥(CFSG.pCore p ↥Γ) := by
    rw [← hP, ← Subgroup.card_map_of_injective (f := N.subtype) N.subtype_injective]
    exact Subgroup.card_le_of_le hle1
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥Γ)).exists_card_eq
  have hdvd : Nat.card ↥(CFSG.pCore p ↥Γ) ∣ Nat.card ↥N :=
    Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting ↥Γ p)
  have h2 : k ≤ (Nat.card ↥N).factorization p := by
    rw [hk] at hdvd
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  have h3 : Nat.card ↥(CFSG.pCore p ↥Γ) ≤ p ^ (Nat.card ↥N).factorization p := by
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos h2
  exact le_antisymm h3 h1

theorem not_two_dvd_card_fitting_of_pCoreOf_two_eq_bot {Γ : Subgroup G} (h2 : pCoreOf 2 Γ = ⊥) :
    ¬ 2 ∣ Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype) := by
  intro hdvd
  have h := card_pCoreOf_eq_fitting Nat.prime_two Γ
  rw [h2, Subgroup.card_bot] at h
  have hf := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hdvd
  have := Nat.one_lt_two_pow hf.ne'
  omega

theorem mem_centralizer_fitting_of_forall_pCoreOf {Γ : Subgroup G} {a : G}
    (ha : ∀ p : ℕ, p.Prime → a ∈ Subgroup.centralizer (pCoreOf p Γ : Set G)) :
    a ∈ Subgroup.centralizer (((genFittingFitting ↥Γ).map Γ.subtype : Subgroup G) : Set G) := by
  set F : Subgroup G := (genFittingFitting ↥Γ).map Γ.subtype with hF
  set C : Subgroup G := F ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hCF : C ≤ F := inf_le_left
  have hdvd : Nat.card F ∣ Nat.card C := by
    rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
    intro p hp
    have hle : pCoreOf p Γ ≤ C := by
      refine le_inf (pCoreOf_le_fitting hp Γ) fun x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact ((Subgroup.mem_centralizer_iff.1 (ha p hp)) x hx).symm
    have h1 : p ^ (Nat.card F).factorization p ∣ Nat.card C := by
      rw [← card_pCoreOf_eq_fitting hp Γ]
      exact Subgroup.card_dvd_of_le hle
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1
  have hCeq : C = F := Subgroup.eq_of_le_of_card_ge hCF (Nat.le_of_dvd Nat.card_pos hdvd)
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfC : f ∈ C := hCeq ▸ hf
  have := Subgroup.mem_centralizer_iff.1 hfC.2 a rfl
  exact this.symm

end General

section G94

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {Γ A : Subgroup (GLV V)} {m : ℕ}

instance finite_linearEquiv_zmod2 (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective

theorem le_normalizer_pCoreOf (p : ℕ) (Γ : Subgroup (GLV V)) :
    Γ ≤ Subgroup.normalizer (pCoreOf p Γ : Set (GLV V)) :=
  le_normalizer_of_forall_conj_mem (pCoreOf_normal_conj p Γ)

theorem odd_card_pCoreOf [Finite V] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Γ : Subgroup (GLV V)) :
    Odd (Nat.card ↥(pCoreOf p Γ)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (isPGroup_pCoreOf p Γ).exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem g94_pCoreOf_two_eq_bot [Finite V] (hyp : G94Hyp Γ A m) : pCoreOf 2 Γ = ⊥ :=
  pCoreOf_two_eq_bot_of_isIrr hyp.irreducible

theorem g94_fixedSpace_pCoreOf_eq_bot (hyp : G94Hyp Γ A m) {p : ℕ} (hne : pCoreOf p Γ ≠ ⊥) :
    fixedSpace (pCoreOf p Γ) = ⊥ :=
  fixedSpace_pCoreOf_eq_bot_of_isIrr hyp.irreducible hne

theorem g94_not_two_dvd_card_fitting [Finite V] (hyp : G94Hyp Γ A m) :
    ¬ 2 ∣ Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype) :=
  not_two_dvd_card_fitting_of_pCoreOf_two_eq_bot (g94_pCoreOf_two_eq_bot hyp)

theorem g94_odd_card_fitting [Finite V] (hyp : G94Hyp Γ A m) :
    Odd (Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype)) :=
  Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (g94_not_two_dvd_card_fitting hyp))

theorem g94_fitting_ne_bot (hyp : G94Hyp Γ A m) : (genFittingFitting ↥Γ).map Γ.subtype ≠ ⊥ := by
  intro hF
  have hA : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine hyp.faithful a ha fun f hf => ?_
    rw [hF, Subgroup.mem_bot] at hf
    rw [hf]
    simp
  have h1 := hyp.A_card
  rw [hA, Subgroup.card_bot] at h1
  have h2 := Nat.one_lt_two_pow (n := m) (by have := hyp.A_ne; omega)
  omega

theorem g94_inf_centralizer_fitting_eq_bot (hyp : G94Hyp Γ A m) :
    A ⊓ Subgroup.centralizer
      (((genFittingFitting ↥Γ).map Γ.subtype : Subgroup (GLV V)) : Set (GLV V)) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  exact hyp.faithful a ha.1 fun f hf => (Subgroup.mem_centralizer_iff.1 ha.2 f hf).symm

theorem g94_eq_bot_of_le_centralizer_pCoreOf [Finite V] (hyp : G94Hyp Γ A m)
    {B : Subgroup (GLV V)} (hBA : B ≤ A)
    (hB : ∀ p : ℕ, p.Prime → p ≠ 2 → B ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V))) :
    B = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine hyp.faithful a (hBA ha) fun f hf => ?_
  have hcent : a ∈ Subgroup.centralizer
      (((genFittingFitting ↥Γ).map Γ.subtype : Subgroup (GLV V)) : Set (GLV V)) := by
    refine mem_centralizer_fitting_of_forall_pCoreOf fun p hp => ?_
    by_cases h2 : p = 2
    · subst h2
      rw [g94_pCoreOf_two_eq_bot hyp, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh]
      simp
    · exact hB p hp h2 ha
  exact (Subgroup.mem_centralizer_iff.1 hcent f hf).symm

theorem g94_inf_centralizer_pCoreOf_three_eq_bot [Finite V] (hyp : G94Hyp Γ A m)
    (h5 : ∀ p : ℕ, p.Prime → 5 ≤ p →
      A ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V))) :
    A ⊓ Subgroup.centralizer (pCoreOf 3 Γ : Set (GLV V)) = ⊥ := by
  refine g94_eq_bot_of_le_centralizer_pCoreOf hyp inf_le_left fun p hp hp2 => ?_
  by_cases h3 : p = 3
  · subst h3
    exact inf_le_right
  · refine inf_le_left.trans (h5 p hp ?_)
    have := hp.two_le
    by_contra h
    interval_cases p
    · exact hp2 rfl
    · exact h3 rfl
    · exact absurd hp (by decide)

end G94

end CFSG.Quasithin.SzN31
