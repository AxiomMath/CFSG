module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartTwo.Sec13.CritProof

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

@[expose] def omegaOneIn {P : Type*} [Group P] (p : ℕ) (C : Subgroup P) : Subgroup P :=
  (omega₁ (G := C) (p := p)).map C.subtype

theorem eq_one_of_isPGroup_zpowers {M : Type*} [Group M] {p : ℕ} [Fact p.Prime]
    {S : Subgroup M} (hS : IsPGroup p S) {σ : M} (hσ : σ ∈ S) {n : ℕ} (hn : σ ^ n = 1)
    (hcop : Nat.Coprime n p) : σ = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨σ, hσ⟩
  have h1 : σ ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf σ ∣ Nat.gcd n (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one h1)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hcop), Nat.dvd_one,
    orderOf_eq_one_iff] at h2
  exact h2

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

theorem exists_isThompsonCritical (hP : IsPGroup p P) :
    ∃ C : Subgroup P, IsThompsonCritical C ∧ (Nontrivial P → C ≠ ⊥) ∧
      ∀ α : MulAut P, Nat.Coprime (orderOf α) p → (∀ x ∈ C, α x = x) → α = 1 := by
  obtain ⟨⟨C, hC⟩, hne⟩ := thompson_critical_subgroup hP
  refine ⟨C, hC, fun hnt => hne C hC hnt, fun α hα hfix => ?_⟩
  have hself : centralizer (C : Set P) ≤ C := by
    rw [hC.2.2.2]
    exact inf_le_left
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcop : (orderOf α).Coprime (Nat.card P) := by
    rw [hn]
    exact Nat.Coprime.pow_right n hα
  exact CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_self_centralizing p hP C
    hself α (orderOf α) (pow_orderOf_eq_one α) hcop hfix

theorem exists_isThompsonCritical_omega (hp2 : p ≠ 2) (hP : IsPGroup p P) :
    ∃ C : Subgroup P, IsThompsonCritical C ∧ (Nontrivial P → C ≠ ⊥) ∧
      (∀ α : MulAut P, Nat.Coprime (orderOf α) p → (∀ x ∈ C, α x = x) → α = 1) ∧
      ((omegaOneIn p C : Subgroup P) : Set P) = {x | x ∈ C ∧ x ^ p = 1} ∧
      (omegaOneIn p C).Characteristic ∧ (Nontrivial P → omegaOneIn p C ≠ ⊥) ∧
      ⁅omegaOneIn p C, (⊤ : Subgroup P)⁆ ≤
        omegaOneIn p C ⊓ centralizer ((omegaOneIn p C : Subgroup P) : Set P) ∧
      (∀ x ∈ omegaOneIn p C, x ^ p = 1) ∧
      IsPGroup p (fixingSubgroup (MulAut P) ((omegaOneIn p C : Subgroup P) : Set P)) ∧
      ∀ α : MulAut P, Nat.Coprime (orderOf α) p → (∀ x ∈ omegaOneIn p C, α x = x) → α = 1 := by
  obtain ⟨C, hC, hne, hfaith⟩ := exists_isThompsonCritical hP
  obtain ⟨hCchar, hCΦ, hCcomm, hCcen⟩ := hC
  have hCp : IsPGroup p C := hP.to_subgroup C
  have hΦ : frattini C ≤ center C := by
    intro x hx
    rw [mem_center_iff]
    intro g
    have hxZ := hCΦ (mem_map_of_mem C.subtype hx)
    exact Subtype.ext (mem_centralizer_iff.1 hxZ.2 g g.2)
  obtain ⟨-, -, -, hset, hΩchar, hΩne⟩ := central_frattini_odd_power_map hp2 hCp hΦ
  set Ω := omega₁ (G := C) (p := p) with hΩdef
  have hΩpow : ∀ y : C, y ∈ Ω → y ^ p = 1 := fun y hy => by
    rw [← SetLike.mem_coe, hset] at hy
    exact hy
  have hDdef : omegaOneIn p C = Ω.map C.subtype := rfl
  have hDchar : (omegaOneIn p C).Characteristic := by
    rw [hDdef]
    infer_instance
  have hDC : omegaOneIn p C ≤ C := by
    rw [hDdef]
    exact map_subtype_le Ω
  have hdet : ∀ α : MulAut P, Nat.Coprime (orderOf α) p →
      (∀ x ∈ omegaOneIn p C, α x = x) → α = 1 := by
    intro α hcop hfixD
    set αC := MulAut.characteristic C α with hαC
    have hαCcop : (orderOf αC).Coprime p :=
      Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ α) hcop
    have hαCfix : ∀ y ∈ Ω, αC y = y := fun y hy =>
      Subtype.ext (hfixD (y : P) (by rw [hDdef]; exact mem_map_of_mem C.subtype hy))
    have hαC1 : αC = 1 := central_frattini_odd_aut_detection hp2 hCp hΦ αC hαCcop hαCfix
    refine hfaith α hcop fun c hc => ?_
    have := congrArg (fun β : MulAut C => ((β ⟨c, hc⟩ : C) : P)) hαC1
    exact this
  refine ⟨C, ⟨hCchar, hCΦ, hCcomm, hCcen⟩, hne, hfaith, ?_, hDchar, ?_, ?_, ?_, ?_, hdet⟩
  · ext x
    constructor
    · intro hx
      rw [SetLike.mem_coe, hDdef] at hx
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      exact ⟨y.2, by rw [subtype_apply, ← coe_pow, hΩpow y hy, coe_one]⟩
    · rintro ⟨hxC, hxp⟩
      rw [SetLike.mem_coe, hDdef]
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      have hmem : (⟨x, hxC⟩ : C) ∈ (Ω : Set C) := by
        rw [hset]
        exact Subtype.ext (by rw [coe_pow]; exact hxp)
      exact hmem
  · intro hnt
    rw [hDdef, Ne, map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact hΩne ((nontrivial_iff_ne_bot C).2 (hne hnt))
  · rw [commutator_le]
    intro d hd g _
    have hdC := hDC hd
    have hz : ⁅d, g⁆ ∈ C ⊓ centralizer (C : Set P) :=
      commutatorElement_mem_swap (hCcomm (commutator_mem_commutator (mem_top g) hdC))
    refine ⟨?_, centralizer_le (SetLike.coe_subset_coe.2 hDC) hz.2⟩
    have e : ⁅d, g⁆ = d * (g * d⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    have : (omegaOneIn p C).Normal := by
      have := hDchar
      infer_instance
    exact mul_mem hd (Normal.conj_mem inferInstance _ (inv_mem hd) g)
  · intro x hx
    rw [hDdef] at hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    rw [subtype_apply, ← coe_pow, hΩpow y hy, coe_one]
  · apply isPGroup_of_coprime_eq_one
    rintro ⟨α, hα⟩ hcop
    rw [orderOf_mk] at hcop
    exact Subtype.ext (hdet α hcop fun x hx => ((mem_fixingSubgroup_iff (MulAut P)).1 hα) x hx)

end CFSG.RankThree.PartTwo.Sec13.CritProof

namespace CFSG.RankThree.PartTwo.Sec13.CritProof

open Subgroup

variable {X : Type*} [Group X] {p : ℕ} [hp : Fact p.Prime]

theorem centralizes_of_coprime_of_fixing {Q : Subgroup X} {D₀ : Set Q}
    (hfix : IsPGroup p (fixingSubgroup (MulAut Q) D₀)) {g : X}
    (hg : g ∈ normalizer (Q : Set X)) (hcop : Nat.Coprime (orderOf g) p)
    (hgD : ∀ d ∈ D₀, g * (d : X) * g⁻¹ = d) : ∀ x ∈ Q, g * x * g⁻¹ = x := by
  set σ : MulAut Q := Q.normalizerMonoidHom ⟨g, hg⟩ with hσ
  have hσfix : σ ∈ fixingSubgroup (MulAut Q) D₀ := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    change g * (d : X) * g⁻¹ = d
    exact hgD d hd
  have hpow : σ ^ orderOf g = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨g, hg⟩ : normalizer (Q : Set X)) ^ orderOf g = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact pow_orderOf_eq_one g)
    rw [this, map_one]
  have hσ1 : σ = 1 := eq_one_of_isPGroup_zpowers hfix hσfix hpow hcop
  intro x hx
  have h := congrArg (fun τ : MulAut Q => ((τ ⟨x, hx⟩ : Q) : X)) hσ1
  exact h

end CFSG.RankThree.PartTwo.Sec13.CritProof
