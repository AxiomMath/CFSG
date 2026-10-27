module

public import CFSG.Quasithin.Vol2.Ch3E215MSp4A
public import CFSG.Quasithin.Vol2.Ch3E215MSp4D

public section

namespace CFSG.Quasithin.Ch3E215M.Sp4

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M CFSG.Timmesfeld
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mul_of {P Z X : Subgroup G} [(Z.subgroupOf P).Normal] (hZP : Z ≤ P)
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Z) (hsq : ∀ p ∈ P, p * p ∈ Z)
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2] {e : ℕ} (hq : Nat.card F₀ = 2 ^ e)
    (he : 1 ≤ e) (ψ : ↥X →* antiSp F₀) (hψs : Function.Surjective ψ)
    (hker : ψ.ker ≤ (actQ hXP hXZ).ker)
    (hirr : ∀ N : Subgroup G, Z ≤ N → N ≤ P → X ≤ Subgroup.normalizer (N : Set G) →
      N = Z ∨ N = P)
    (hnt : ∃ y ∈ X, ∃ p ∈ P, y * p * y⁻¹ * p⁻¹ ∉ Z) (hcard : Z.relIndex P ≤ 2 ^ (4 * e))
    {p₁ p₂ : G} (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P) (h₁ : p₁ ∉ Z) (h₂ : p₂ ∉ Z) :
    ∃ y ∈ X, (y * p₁ * y⁻¹)⁻¹ * p₂ ∈ Z := by
  classical
  let ρ : antiSp F₀ →* MulAut (↥P ⧸ Z.subgroupOf P) :=
    (QuotientGroup.lift ψ.ker (actQ hXP hXZ) hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.toMonoidHom
  have hρ : ∀ y : ↥X, ρ (ψ y) = actQ hXP hXZ y := by
    intro y
    have e1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm (ψ y) =
        (y : ↥X ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift ψ.ker (actQ hXP hXZ) hker
      ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm (ψ y)) = actQ hXP hXZ y
    rw [e1, QuotientGroup.lift_mk]
  have hsqQ : ∀ q : ↥P ⧸ Z.subgroupOf P, q * q = 1 := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq _ p.2
  have hirrQ : ∀ Y : Subgroup (↥P ⧸ Z.subgroupOf P), (∀ γ, ∀ q ∈ Y, ρ γ q ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    have hYX : ∀ y : ↥X, ∀ q ∈ Y, actQ hXP hXZ y q ∈ Y := fun y q hq => by
      rw [← hρ]
      exact hY _ q hq
    rcases hirr _ (le_comapQ hZP Y) (comapQ_le Y) (le_normalizer_comapQ hXP hXZ hYX) with
      hN | hN
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : (p : G) ∈ comapQ Y := mem_comapQ.2 ⟨p.2, hq⟩
      rw [hN] at h1
      exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h1))
    · right
      rw [eq_top_iff]
      intro q _
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : (p : G) ∈ comapQ Y := by rw [hN]; exact p.2
      obtain ⟨hp', hq⟩ := mem_comapQ.1 h1
      exact hq
  have hntρ : ρ ≠ 1 := by
    intro h1
    obtain ⟨y, hy, p, hp, hyp⟩ := hnt
    apply hyp
    have h3 : actQ hXP hXZ ⟨y, hy⟩ = 1 := by rw [← hρ, h1]; rfl
    have h4 := congrArg (fun φ : MulAut (↥P ⧸ Z.subgroupOf P) => φ ((⟨p, hp⟩ : ↥P) :
      ↥P ⧸ Z.subgroupOf P)) h3
    simp only [MulAut.one_apply] at h4
    rw [actQ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h4
    have hw : ((y * p * y⁻¹)⁻¹ * p : G) ∈ Z := h4
    have hw' := Z.inv_mem hw
    have hpX : y * p * y⁻¹ * p⁻¹ = p * ((y * p * y⁻¹)⁻¹ * p)⁻¹ * p⁻¹ := by group
    rw [hpX]
    exact (Subgroup.Normal.conj_mem inferInstance ⟨_, hZP hw'⟩
      (Subgroup.mem_subgroupOf.2 hw') ⟨p, hp⟩ : _)
  have hne : ∀ (p : G) (hp : p ∈ P), p ∉ Z →
      ((⟨p, hp⟩ : ↥P) : ↥P ⧸ Z.subgroupOf P) ≠ 1 := by
    intro p hp hpZ h0
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h0
    exact hpZ h0
  obtain ⟨γ, hγ⟩ := @exists_apply_eq_of_irr F₀ _ _ _ e hq he (↥P ⧸ Z.subgroupOf P)
    (quotCommGroup hcomm) _ hsqQ ρ hirrQ hntρ hcard _ _ (hne p₁ hp₁ h₁) (hne p₂ hp₂ h₂)
  obtain ⟨y, rfl⟩ := hψs γ
  rw [hρ, actQ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hγ
  exact ⟨y, y.2, hγ⟩

variable {X T M V : Subgroup G} {g : G}

theorem exists_mem_conj_mul (h : E2.Pair X T M V g) (hchar : CharTwo X)
    (hJ : IsPGroup 2 ↥(kerIn M X)) {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2] {e : ℕ}
    (hq : Nat.card F₀ = 2 ^ e) (he : 1 ≤ e) (ψ : ↥X →* antiSp F₀)
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = (kerIn M X).subgroupOf X)
    (hPZ : (V ⊓ B6.conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) ≤
      2 ^ (4 * e))
    {p₁ p₂ : G} (hp₁ : p₁ ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V))
    (hp₂ : p₂ ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) (h₁ : p₁ ∉ V ⊓ B6.conjSub g V)
    (h₂ : p₂ ∉ V ⊓ B6.conjSub g V) :
    ∃ y ∈ X, (y * p₁ * y⁻¹)⁻¹ * p₂ ∈ V ⊓ B6.conjSub g V := by
  obtain ⟨r, x, hr, hx, hxo⟩ := exists_mem_orderOf_ppd hq he ψ hψs
  have hk : 0 < 4 * e := by omega
  have := normal_Z h
  refine exists_conj_mul_of h.inf_conj_le_P (fun a ha b hb => (h.commutator_sq_mem_Z ha hb).1)
    (fun a ha => by rw [← pow_two]; exact (h.commutator_sq_mem_Z ha ha).2)
    h.le_normalizer_P h.le_normalizer_Z hq he ψ hψs ?_
    (fun N hZN hNP hXN => eq_or_eq_of_le_normalizer h hchar hk hr hx hxo hPZ hZN hNP hXN)
    ?_ hPZ hp₁ hp₂ h₁ h₂
  · intro y hy
    rw [hψk, Subgroup.mem_subgroupOf] at hy
    rw [MonoidHom.mem_ker]
    ext q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    rw [actQ_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc := commutator_mem_Z_of_kerIn h hchar hJ hk hr hx hxo hPZ hy p.2
    have hc' := (V ⊓ B6.conjSub g V).inv_mem hc
    have e1 : ((y : G) * p * (y : G)⁻¹)⁻¹ * p =
        (p : G)⁻¹ * ((y : G) * p * (y : G)⁻¹ * (p : G)⁻¹)⁻¹ * ((p : G)⁻¹)⁻¹ := by group
    show ((y : G) * p * (y : G)⁻¹)⁻¹ * p ∈ V ⊓ B6.conjSub g V
    rw [e1, conj_eq_of_mem_Z h (P_le_X h ((kerIn M X ⊓ V ⊔ B6.conjSub g (kerIn M X ⊓ V)).inv_mem
      p.2)) hc']
    exact hc'
  · by_contra hall
    push Not at hall
    exact not_forall_mem_Z h hchar hr.prime (hr.ne_two hk) hx hxo fun p hp => hall x hx p hp

end CFSG.Quasithin.Ch3E215M.Sp4
