module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF1
import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Open
open CFSG.RankThree.PartTwo.Sec19

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Theta


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem exists_theta (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) :
    ∃ Θ : MulAut (C0 σ) →* (X ≃+* X),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : C0 σ →* MulAut (C0 σ)).range ∧
      (∀ α : MulAut (C0 σ), ∃ g δ, α = MulAut.conj g * fieldActor σ δ) := by
  obtain ⟨-, hdec, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, -⟩ :=
    even_triality_exact_automorphism_normal_form hn X hX σ hσ
  refine ⟨Θ, hΘ, hker, fun α => ?_⟩
  obtain ⟨⟨g, δ⟩, hgδ⟩ := (hdec α).exists
  exact ⟨g, δ, hgδ⟩

theorem gal_cube_cases (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) (ψ : X ≃+* X) (hψ : ψ ^ 3 = 1) :
    ψ = 1 ∨ ψ = σ ∨ ψ = σ ^ 2 := by
  obtain ⟨-, -, -, hcyc, hcard3, -, -, -⟩ :=
    even_triality_exact_automorphism_normal_form hn X hX σ hσ
  haveI : Finite (X ≃+* X) := Nat.finite_of_card_ne_zero (by rw [hcard3]; omega)
  haveI := hcyc
  have hσ3 : σ ^ 3 = 1 := nf1_sigma_pow_three σ n hX hσ
  have hσ1 : σ ≠ 1 := nf1_sigma_ne_one σ n hn hX hσ
  exact mem_of_cube_eq_one_cyclic σ hσ3 hσ1 (nf1_sq_ne_one σ hσ3 hσ1) ψ hψ

theorem theta_tauAut {Θ : MulAut (C0 σ) →* (X ≃+* X)}
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) : Θ (tauAut σ) = σ :=
  hΘ _ 1 σ (by rw [map_one, one_mul])

theorem tauAut_not_inner (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) (g : C0 σ) : tauAut σ ≠ MulAut.conj g := by
  obtain ⟨Θ, hΘ, -, -⟩ := exists_theta σ n hn hX hσ
  intro h
  have h1 : Θ (tauAut σ) = 1 := by
    have := hΘ (MulAut.conj g) g 1 (by rw [fieldActor_one, mul_one])
    rw [h]
    exact this
  rw [theta_tauAut σ hΘ] at h1
  exact nf1_sigma_ne_one σ n hn hX hσ h1

end Theta

section E27


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

@[expose] noncomputable def innerPart (E : Subgroup (MulAut (C0 σ))) : Subgroup (C0 σ) :=
  E.comap (MulAut.conj : C0 σ →* MulAut (C0 σ))

theorem mem_innerPart {E : Subgroup (MulAut (C0 σ))} {x : C0 σ} :
    x ∈ innerPart σ E ↔ MulAut.conj x ∈ E := Iff.rfl

theorem innerPart_isElemAbelian (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 (innerPart σ E) := by
  have hinj := conj_injective_C0 σ n hn hX hσ
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := elemAb_comm
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE)
  refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hEc _ a.2 _ b.2
  · rw [map_pow, map_one]
    exact hE.2 _ hx

theorem card_le_nine_C0 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {F : Subgroup (C0 σ)} (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 9 :=
  CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hn
    (by rw [hX]; rfl) (σ := σ.toRingHom) (fun c => hσ c) F hF

theorem card_innerPart_le_nine (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E) :
    Nat.card (innerPart σ E) ≤ 9 :=
  card_le_nine_C0 σ n hn hX hσ (innerPart_isElemAbelian σ n hn hX hσ hE)

theorem nine_le_card_innerPart (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) : 9 ≤ Nat.card (innerPart σ E) := by
  obtain ⟨Θ, hΘ, hker, -⟩ := exists_theta σ n hn hX hσ
  set Θ' : E →* (X ≃+* X) := Θ.comp E.subtype with hΘ'
  have hσ3 : σ ^ 3 = 1 := nf1_sigma_pow_three σ n hX hσ
  have hσ1 : σ ≠ 1 := nf1_sigma_ne_one σ n hn hX hσ
  have hle : Θ'.range ≤ Subgroup.zpowers σ := by
    rintro _ ⟨⟨α, hα⟩, rfl⟩
    have hα3 : α ^ 3 = 1 := hE.2 α hα
    have hψ : Θ α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    show Θ α ∈ Subgroup.zpowers σ
    rcases gal_cube_cases σ n hn hX hσ (Θ α) hψ with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers σ
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) 2
  have hrange : Nat.card Θ'.range ≤ 3 := by
    calc Nat.card Θ'.range ≤ Nat.card (Subgroup.zpowers σ) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hσ3 hσ1]
  have hkr := Subgroup.card_ker_mul_card_range Θ'
  rw [hcard] at hkr
  have hker9 : 9 ≤ Nat.card Θ'.ker := by
    by_contra hlt
    push_neg at hlt
    have : Nat.card Θ'.ker * Nat.card Θ'.range ≤ 8 * 3 := Nat.mul_le_mul (by omega) hrange
    omega
  let f : innerPart σ E → Θ'.ker := fun x => ⟨⟨MulAut.conj (x : C0 σ), x.2⟩, by
    show Θ (MulAut.conj (x : C0 σ)) = 1
    have : MulAut.conj (x : C0 σ) ∈ Θ.ker := by rw [hker]; exact ⟨x, rfl⟩
    exact this⟩
  have hfs : Function.Surjective f := by
    rintro ⟨⟨α, hα⟩, hk⟩
    have hk' : Θ α = 1 := hk
    have : α ∈ Θ.ker := hk'
    rw [hker] at this
    obtain ⟨x, rfl⟩ := this
    exact ⟨⟨x, hα⟩, rfl⟩
  exact hker9.trans (Nat.card_le_card_of_surjective f hfs)

theorem card_innerPart_eq (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) : Nat.card (innerPart σ E) = 9 :=
  le_antisymm (card_innerPart_le_nine σ n hn hX hσ hE)
    (nine_le_card_innerPart σ n hn hX hσ hE hcard)

theorem exists_outer_of_E27 (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) : ∃ β ∈ E, ∀ g : C0 σ, β ≠ MulAut.conj g := by
  by_contra hcon
  push_neg at hcon
  have h9 := card_innerPart_eq σ n hn hX hσ hE hcard
  let f : innerPart σ E → E := fun x => ⟨MulAut.conj (x : C0 σ), x.2⟩
  have hfs : Function.Surjective f := by
    rintro ⟨β, hβ⟩
    obtain ⟨g, hg⟩ := hcon β hβ
    exact ⟨⟨g, by rw [mem_innerPart, ← hg]; exact hβ⟩, Subtype.ext hg.symm⟩
  have := Nat.card_le_card_of_surjective f hfs
  omega

theorem exists_outer_shape (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) :
    ∃ β ∈ E, ∃ (g : C0 σ) (e : ℕ), (e = 1 ∨ e = 2) ∧ β = MulAut.conj g * tauAut σ ^ e := by
  obtain ⟨Θ, hΘ, hker, hdec⟩ := exists_theta σ n hn hX hσ
  obtain ⟨β, hβE, hβout⟩ := exists_outer_of_E27 σ n hn hX hσ hE hcard
  have hβ3 : β ^ 3 = 1 := hE.2 β hβE
  have hβΘ3 : Θ β ^ 3 = 1 := by rw [← map_pow Θ, hβ3, map_one]
  have hβ1 : Θ β ≠ 1 := by
    intro h
    have hmem : β ∈ Θ.ker := MonoidHom.mem_ker.2 h
    rw [hker] at hmem
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hmem
    exact hβout g hg.symm
  obtain ⟨e, he12, hΘe⟩ : ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Θ β = σ ^ e := by
    rcases gal_cube_cases σ n hn hX hσ _ hβΘ3 with h | h | h
    · exact absurd h hβ1
    · exact ⟨1, Or.inl rfl, by rw [h, pow_one]⟩
    · exact ⟨2, Or.inr rfl, h⟩
  obtain ⟨g, δ, hgδ⟩ := hdec β
  have hδ : δ = σ ^ e := (hΘ β g δ hgδ).symm.trans hΘe
  have hpow : fieldActor (t := TwistTag.D4) σ (σ ^ e) = tauAut σ ^ e :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ e
  refine ⟨β, hβE, g, e, he12, ?_⟩
  rw [← hpow, ← hδ]
  exact hgδ

end E27

end CFSG.RankThree.PartTwo.Sec4.E27
