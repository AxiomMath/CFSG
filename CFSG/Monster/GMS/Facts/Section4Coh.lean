module

public import CFSG.Monster.GMS.S35

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def ThreeAInvolutionClasses (a z₀ : G) : Prop :=
  ∀ b x : G, IsConj a b → x ∈ typeSet a z₀ b .threeA →
    (∀ t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}, orderOf t = 2 →
      (t ∈ twoANbr a b ∧ t ∈ twoANbr a x) ∨ (t ∈ twoBNbr a z₀ b ∧ t ∈ twoBNbr a z₀ x) ∨
        (t ∈ twoBBNbr z₀ b ∧ t ∈ twoBBNbr z₀ x)) ∧
    ∀ t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x},
      ∀ s ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x},
        orderOf t = 2 → orderOf s = 2 →
          ((t ∈ twoANbr a b ∧ s ∈ twoANbr a b) ∨ (t ∈ twoBNbr a z₀ b ∧ s ∈ twoBNbr a z₀ b) ∨
            (t ∈ twoBBNbr z₀ b ∧ s ∈ twoBBNbr z₀ b)) →
          ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}, g * t * g⁻¹ = s

@[expose] def FourAPerfect (a z₀ : G) : Prop :=
  ∀ b x : G, IsConj a b → x ∈ typeSet a z₀ b .fourA →
    ⁅Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x},
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}⁆ =
        Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}

@[expose] def FiveAInvolutions (a z₀ : G) : Prop :=
  ∀ b x : G, IsConj a b → x ∈ typeSet a z₀ b .fiveA →
    (∀ t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x},
      ∀ s ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x},
        orderOf t = 2 → orderOf s = 2 → ((IsConj a t ∧ IsConj a s) ∨ (IsConj z₀ t ∧ IsConj z₀ s)) →
          ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}, g * t * g⁻¹ = s) ∧
    ∃ t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x},
      ∃ t' ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x},
        t * t' = t' * t ∧ IsConj a t ∧ IsConj z₀ t' ∧ IsConj a (t * t')

@[expose] def FiveATwoA (a z₀ : G) : Prop :=
  ∀ b x : G, IsConj a b → x ∈ typeSet a z₀ b .fiveA →
    ∃ t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}, IsConj a t

theorem FiveAInvolutions.fiveATwoA {a z₀ : G} (h : FiveAInvolutions a z₀) : FiveATwoA a z₀ := by
  intro b x hb hx
  obtain ⟨t, ht, -, -, -, hta, -, -⟩ := (h b x hb hx).2
  exact ⟨t, ht, hta⟩

@[expose] def CoTwoIrreducible (a z₀ : G) : Prop :=
  ∀ t t' : G, IsConj a t → IsConj z₀ t' → t * t' = t' * t → IsConj a (t * t') →
    ∀ N : Subgroup G, t ∈ N → t' ∈ N → N ≤ leechQ t' ⊓ Subgroup.centralizer {t} →
      (∀ g ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'}, ∀ n ∈ N,
        g * n * g⁻¹ ∈ N) →
        (∀ n ∈ N, n = 1 ∨ n = t ∨ n = t' ∨ n = t * t') ∨ N = leechQ t' ⊓ Subgroup.centralizer {t}

@[expose] def CoTwoStructure (a z₀ : G) : Prop :=
  ∀ t t' : G, IsConj a t → IsConj z₀ t' → t * t' = t' * t → IsConj a (t * t') →
    ⁅Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'},
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'}⁆ =
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'} ∧
    (∀ g ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'},
      (∀ n ∈ leechQ t' ⊓ Subgroup.centralizer {t}, g * n = n * g) →
        g = 1 ∨ g = t ∨ g = t' ∨ g = t * t') ∧
    ∃ y ∈ leechQ t' ⊓ Subgroup.centralizer {t}, IsConj a y ∧ y ≠ t ∧ y ≠ t * t'

@[expose] def ThreeCSingleClass (a z₀ : G) : Prop :=
  ∀ b x t s : G, IsConj a b → x ∈ typeSet a z₀ b .threeC →
    t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} →
    s ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} →
    orderOf t = 2 → orderOf s = 2 →
      ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}, g * t * g⁻¹ = s

@[expose] def ThreeCGenerated (a z₀ : G) : Prop :=
  ∀ b x t₁ t₂ : G, IsConj a b → x ∈ typeSet a z₀ b .threeC →
    t₁ ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} →
    t₂ ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} →
    orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ →
      (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {t₁}) ⊔
          (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} ⊓
            Subgroup.centralizer {t₂}) =
        Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}

@[expose] def threeCLineBound : ℕ := 8 * 181440

@[expose] def ThreeCTripleCore (a z₀ : G) : Prop :=
  ∀ b x w : G, IsConj a b → x ∈ typeSet a z₀ b .threeC → IsConj z₀ w →
    w ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} →
      ∀ M : Subgroup G, M ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} ⊓
          Subgroup.centralizer {w} →
        (∀ s ∈ M, ∀ s' ∈ M, orderOf s = 2 → orderOf s' = 2 → s = s') →
          Nat.card M ≤ threeCLineBound

end CFSG.Monster.GMS
