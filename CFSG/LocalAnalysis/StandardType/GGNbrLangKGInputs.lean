module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangRegLinearLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .A ∨ lab.tag = .twA) ∧ ¬ p ∣ lab.rank + 1) ∨
    ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank = 3)

@[expose] def GGNbrLangRegClassicalLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C ∨ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank)

@[expose] def GGNbrLangRegExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ (lab.tag = .triD4 ∧ p ≠ 3) ∨
    ((lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) ∧
      p ≠ 3) ∨
    (lab.tag = .E8 ∧ p ≠ 3 ∧ p ≠ 5)

@[expose] def GGNbrLangRegLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangRegLinearLabel p lab ∨ GGNbrLangRegClassicalLabel lab ∨ GGNbrLangRegExcLabel p lab

@[expose] def GGNbrLangTorTypeALabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .twA) ∧ p ∣ lab.rank + 1

@[expose] def GGNbrLangTorExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) ∧
      p = 3) ∨
    (lab.tag = .E8 ∧ (p = 3 ∨ p = 5))

@[expose] def GGNbrLangTorLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangTorTypeALabel p lab ∨ GGNbrLangTorExcLabel p lab

@[expose] def GGNbrLangT3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .triD4 ∧ p = 3

@[expose] def GGNbrLangTypeASixLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .twA) ∧
    ((p = 3 ∧ (lab.rank = 2 ∨ lab.rank = 5)) ∨ (p = 5 ∧ lab.rank = 4))

@[expose] def GGNbrLangTypeARankLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangTorTypeALabel p lab ∧ ¬ GGNbrLangTypeASixLabel p lab

theorem ggNbrLangRest12Label_split {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGNbrLangRest12Label p lab) :
    GGNbrLangRegLabel p lab ∨ GGNbrLangTorLabel p lab ∨ GGNbrLangT3Label p lab := by
  obtain ⟨⟨-, hlin2, -, hf2, -, -, -⟩, -, hB2⟩ := h
  obtain ⟨tag, rank, n⟩ := lab
  simp only [GGNbrLangRegLabel, GGNbrLangRegLinearLabel, GGNbrLangRegClassicalLabel,
    GGNbrLangRegExcLabel, GGNbrLangTorLabel, GGNbrLangTorTypeALabel, GGNbrLangTorExcLabel,
    GGNbrLangT3Label, GGLinearTwoLabel, GGNbrLangFieldTwoLabel, LargeEvenInLambda2] at *
  cases tag <;> simp at * <;> omega

theorem ggNbrLangTypeARankLabel_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : GGNbrLangTypeARankLabel p lab) :
    (lab.rank + 1) / p + 1 < max (lab.rank + 1 - 4) 2 ∧
      (lab.tag = .A → (lab.rank + 1) / p + 1 < max (lab.rank + 1 - 3) 2) := by
  obtain ⟨⟨htag, k, hk⟩, h6⟩ := h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hk1 : 1 ≤ k := by rcases k with _ | k <;> simp_all
  have hdiv : (lab.rank + 1) / p = k := by rw [hk]; exact Nat.mul_div_cancel_left k hp.pos
  rw [hdiv]
  simp only [GGNbrLangTypeASixLabel, not_and, not_or] at h6
  have h6' := h6 htag
  have key : k + 6 ≤ p * k := by
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · interval_cases k
      · have : p ≠ 3 := fun h => (h6'.1 h).1 (by omega)
        have : p ≠ 5 := fun h => h6'.2 h (by omega)
        have : p ≠ 4 := fun h => by subst h; norm_num at hp
        have : p ≠ 6 := fun h => by subst h; norm_num at hp
        omega
      · have : p ≠ 3 := fun h => (h6'.1 h).2 (by omega)
        have : p ≠ 4 := fun h => by subst h; norm_num at hp
        omega
    · nlinarith
  constructor
  · omega
  · intro _; omega

@[expose] noncomputable def kgInducedAut {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) : MulAut K →* MulAut R :=
  (MulAut.congr θ).toMonoidHom.comp (centerQuotAut K)

@[expose] def KGLangTorusCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ A : Subgroup (MulAut K), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I →
        ∃ T : Subgroup K, (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧ (∀ t : K, α₀ t ∈ T ↔ t ∈ T) ∧
          (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ T, α t = t) ∧
          (∀ t ∈ T, α₀ t = t → ∃ s ∈ T, t = ((List.range p).map fun i => (α₀ ^ i) s).prod) ∧
          ∃ e ∈ T, e ≠ 1 ∧ e ^ p = 1 ∧ ∀ α ∈ A, α e = e

@[expose] def KGLangTorusOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (KGLangTorusCont p)

@[expose] def KGFieldNotInnerCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ α : MulAut R, (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, α = u * f) → α ∉ I → α ^ p = 1 →
    ∀ h ∈ I, h ^ p = 1 → h * α = α * h →
      ∀ J₀ : Subgroup R, IsComponentOf J₀ (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)) →
        ∀ α' : MulAut J₀, (∀ j : J₀, (α' j : R) = α j) →
          GGMarkingAll (K := J₀) fun _ R' _ I' _ θ' => kgInducedAut θ' α' ∉ I'

@[expose] def KGFieldNotInnerInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    ¬ GGNbrLangT3Label p lab → LargeEvenLabelAll lab (KGFieldNotInnerCont p)

end CFSG.StandardType
