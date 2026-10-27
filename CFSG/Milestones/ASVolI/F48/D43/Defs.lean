module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs
public import CFSG.Milestones.ASVolI.F48.Small.Pres

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Open CFSG.ASVolI.ChF

@[expose] noncomputable def burnsideF48d_perm (T : Table) : Equiv.Perm (Fin 26572) :=
  Classical.epsilon fun g => Rep 26572 T g

@[expose] noncomputable def burnsideF48d_γ (k : ℕ) : Equiv.Perm (Fin 26572) :=
  burnsideF48d_perm (burnsideF48d_toT (burnsideF48d_gen k))

@[expose] noncomputable def burnsideF48d_frob : Equiv.Perm (Fin 26572) :=
  burnsideF48d_perm (burnsideF48d_toT (burnsideF48d_phi ()))

@[expose] noncomputable def burnsideF48d_X : Subgroup (Equiv.Perm (Fin 26572)) :=
  Subgroup.closure (Set.range fun k : Fin 8 => burnsideF48d_γ k)

theorem burnsideF48d_γ_mem (k : Fin 8) : burnsideF48d_γ k ∈ burnsideF48d_X :=
  Subgroup.subset_closure ⟨k, rfl⟩

@[expose] noncomputable def burnsideF48d_σ (j : ℕ) : Equiv.Perm (Fin 26572) :=
  burnsideF48s_ev (fun k : Fin 8 => burnsideF48d_γ k) (burnsideF48d_LW.getD j [])

theorem burnsideF48d_σ_mem (j : ℕ) : burnsideF48d_σ j ∈ burnsideF48d_X :=
  burnsideF48s_ev_mem _ _ fun l _ => burnsideF48d_γ_mem l.1

@[expose] noncomputable def burnsideF48d_L (j : Fin 17) : ↥burnsideF48d_X :=
  ⟨burnsideF48d_σ j, burnsideF48d_σ_mem j⟩

abbrev burnsideF48d_S1 : Set (Fin 17) := {j | j ≠ 1}

abbrev burnsideF48d_S2 : Set (Fin 17) := {j | j ≠ 0}

@[expose] noncomputable def burnsideF48d_P1 : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' burnsideF48d_S1)

@[expose] noncomputable def burnsideF48d_P2 : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' burnsideF48d_S2)

@[expose] noncomputable def burnsideF48d_T : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' {j | 2 ≤ j.val ∧ j.val ≤ 4})

@[expose] noncomputable def burnsideF48d_U : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' {j | 5 ≤ j.val})

abbrev burnsideF48d_line : Finset (Fin 26572) := {0, 1, 2, 6}

abbrev burnsideF48d_aptF : Finset (Fin 26572) := {0, 6, 479, 26571, 15916, 186}

abbrev burnsideF48d_baseF : Finset (Fin 26572) := {0, 26571, 6, 479, 15916, 186, 1, 3}

structure burnsideF48d_ModelFacts : Prop where
  card_X : Nat.card ↥burnsideF48d_X = 20560831566912
  equiv_X : ∀ (H : Type) [Group H], ChF.IsGenLie H .D4tw 3 1 → Nonempty (↥burnsideF48d_X ≃* H)
  gen_rep : ∀ k < 8, Rep 26572 (burnsideF48d_toT (burnsideF48d_gen k)) (burnsideF48d_γ k)
  frob_rep : Rep 26572 (burnsideF48d_toT (burnsideF48d_phi ())) burnsideF48d_frob
  letter_rep : ∀ j < 17, Rep 26572 (burnsideF48d_letters ())[2 * j]! (burnsideF48d_σ j) ∧
    Rep 26572 (burnsideF48d_letters ())[2 * j + 1]! (burnsideF48d_σ j)⁻¹
  base : ∀ z : ↥burnsideF48d_X,
    (∀ p ∈ burnsideF48d_baseF, (z : Equiv.Perm (Fin 26572)) p = p) → z = 1
  trans : ∀ p : Fin 26572, ∃ z : ↥burnsideF48d_X, (z : Equiv.Perm (Fin 26572)) 0 = p
  mem_P1 : ∀ z : ↥burnsideF48d_X, z ∈ burnsideF48d_P1 ↔ (z : Equiv.Perm (Fin 26572)) 0 = 0
  mem_P2 : ∀ z : ↥burnsideF48d_X, z ∈ burnsideF48d_P2 ↔
    ∀ p ∈ burnsideF48d_line, (z : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line
  mem_T : ∀ z : ↥burnsideF48d_X, z ∈ burnsideF48d_T ↔
    ∀ p ∈ burnsideF48d_aptF, (z : Equiv.Perm (Fin 26572)) p = p
  B_eq_closure : burnsideF48d_P1 ⊓ burnsideF48d_P2 =
    Subgroup.closure (burnsideF48d_L '' {j | 2 ≤ j.val})
  card_P1 : Nat.card ↥burnsideF48d_P1 = 773778096
  card_P2 : Nat.card ↥burnsideF48d_P2 = 110539728
  card_B : Nat.card ↥(burnsideF48d_P1 ⊓ burnsideF48d_P2) = 27634932
  card_U : Nat.card ↥burnsideF48d_U = 531441
  card_T : Nat.card ↥burnsideF48d_T = 52
  U_le : burnsideF48d_U ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2
  T_le : burnsideF48d_T ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2
  U_normal : ∀ b ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2, ∀ u ∈ burnsideF48d_U,
    b * u * b⁻¹ ∈ burnsideF48d_U
  sylow : ChF.IsSylowOf 3 burnsideF48d_U ⊤
  B_eq : burnsideF48d_P1 ⊓ burnsideF48d_P2 =
    ⊤ ⊓ Subgroup.normalizer (burnsideF48d_U : Set ↥burnsideF48d_X)
  P1_ne_P2 : burnsideF48d_P1 ≠ burnsideF48d_P2
  P1_max : burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ burnsideF48d_P1 ∧ burnsideF48d_P1 ≤ ⊤ ∧
    burnsideF48d_P1 ≠ ⊤ ∧ ∀ R : Subgroup ↥burnsideF48d_X, burnsideF48d_P1 < R → R ≤ ⊤ → R = ⊤
  P2_max : burnsideF48d_P1 ⊓ burnsideF48d_P2 ≤ burnsideF48d_P2 ∧ burnsideF48d_P2 ≤ ⊤ ∧
    burnsideF48d_P2 ≠ ⊤ ∧ ∀ R : Subgroup ↥burnsideF48d_X, burnsideF48d_P2 < R → R ≤ ⊤ → R = ⊤
  hconj : ∀ K'' : Subgroup ↥burnsideF48d_X, K'' ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 →
    Nat.card ↥K'' = 52 →
      ∃ t ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ burnsideF48d_T
  normalizer_T : ∀ b ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2,
    (∀ t ∈ burnsideF48d_T, b * t * b⁻¹ ∈ burnsideF48d_T) → b ∈ burnsideF48d_T
  xred : ∀ x ∈ burnsideF48d_P1, x ∉ burnsideF48d_P2 →
    (∀ k ∈ burnsideF48d_T, x * k * x⁻¹ ∈ burnsideF48d_T) → (burnsideF48d_L 0)⁻¹ * x ∈ burnsideF48d_T
  yred : ∀ y ∈ burnsideF48d_P2, y ∉ burnsideF48d_P1 →
    (∀ k ∈ burnsideF48d_T, y * k * y⁻¹ ∈ burnsideF48d_T) → (burnsideF48d_L 1)⁻¹ * y ∈ burnsideF48d_T
  fix_P1 : ∀ p : Fin 26572,
    (∀ z ∈ burnsideF48d_P1, ((z : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = p) → p = 0
  inv_P2 : ∀ S : Finset (Fin 26572), S.Nonempty → S.card ≤ 4 →
    (∀ z ∈ burnsideF48d_P2, ∀ q ∈ S, ((z : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q ∈ S) →
      S = burnsideF48d_line
  comm_T : ∀ t ∈ burnsideF48d_T, burnsideF48d_L 0 * burnsideF48d_L 1 * t =
    t * (burnsideF48d_L 0 * burnsideF48d_L 1) → t = 1
  KW_cov : ∀ c ∈ burnsideF48d_T, ∃ w ∈ burnsideF48d_KW, burnsideF48s_ev burnsideF48d_L w = c

@[expose] def burnsideF48d_ExtCase : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 .D4tw 3 1 Gp M₁ M₂ → Gp ≠ ⊤ →
    F48Concl .D4tw 3 1 Gp M₁ M₂

end CFSG.ASVolI
