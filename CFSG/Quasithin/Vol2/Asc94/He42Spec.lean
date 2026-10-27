module

public import CFSG.Quasithin.Vol2.Asc94.He42Base
public import CFSG.Quasithin.Vol2.Asc94.He42PDef
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaGen1
public import CFSG.Sporadic.Schreier.J4SBinary
public import CFSG.Sporadic.Schreier.J4SOrder

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

structure YSpec (S : HeSetup G) (y₁ y₂ : G) : Prop where
  mem₁ : y₁ ∈ S.N
  mem₂ : y₂ ∈ S.N
  ord₁ : orderOf y₁ = 3
  ord₂ : orderOf y₂ = 3
  comm : y₁ * y₂ = y₂ * y₁
  rho₁ : S.rhoG y₁ = (S.g, 1)
  rho₂ : S.rhoG y₂ = (1, S.g)

namespace HeSetup

variable (S : HeSetup G)

structure BaseFacts : Prop where
  card_A : Nat.card S.A = 64
  card_A' : Nat.card S.A' = 64
  card_Z : Nat.card S.Z = 16
  card_J : Nat.card S.J = 256
  card_N : Nat.card S.N = 9216
  card_B : Nat.card S.B = 4
  card_L1 : Nat.card S.L1 = 3840
  card_L2 : Nat.card S.L2 = 3840
  card_K : Nat.card S.K = 768
  A_le_J : S.A ≤ S.J
  A'_le_J : S.A' ≤ S.J
  Z_le_A : S.Z ≤ S.A
  Z_le_A' : S.Z ≤ S.A'
  B_le_Z : S.B ≤ S.Z
  J_le_K : S.J ≤ S.K
  K_le_N : S.K ≤ S.N
  K_le_L1 : S.K ≤ S.L1
  K_le_L2 : S.K ≤ S.L2
  L1_inf_L2 : S.L1 ⊓ S.L2 = S.K
  relIndex_K_L1 : S.K.relIndex S.L1 = 5
  relIndex_K_L2 : S.K.relIndex S.L2 = 5
  L1_le_normalizer : S.L1 ≤ normalizer (S.A : Set G)
  L2_le_normalizer : S.L2 ≤ normalizer (S.A' : Set G)
  L1_le_centralizer : S.L1 ≤ centralizer (S.B : Set G)
  L2_le_centralizer : S.L2 ≤ centralizer (S.B : Set G)
  A_comm : ∀ x ∈ S.A, ∀ y ∈ S.A, x * y = y * x
  A'_comm : ∀ x ∈ S.A', ∀ y ∈ S.A', x * y = y * x
  A_sq : ∀ x ∈ S.A, x * x = 1
  A'_sq : ∀ x ∈ S.A', x * x = 1

@[expose] def StepPsi : Prop :=
  (∃ ψ : ↥S.L1 →* Equiv.Perm (Fin 5), PData S.L1 S.K S.A S.J ψ) ∧
    ∃ ψ : ↥S.L2 →* Equiv.Perm (Fin 5), PData S.L2 S.K S.A' S.J ψ

@[expose] def StepYnorm (y₁ y₂ : G) : Prop :=
  (y₁ ∈ normalizer (S.L1 : Set G) ∧ y₁ ∈ normalizer (S.K : Set G) ∧
      ∀ j ∈ S.J, y₁ * j * y₁⁻¹ * j⁻¹ ∈ S.A) ∧
    (y₂ ∈ normalizer (S.L2 : Set G) ∧ y₂ ∈ normalizer (S.K : Set G) ∧
      ∀ j ∈ S.J, y₂ * j * y₂⁻¹ * j⁻¹ ∈ S.A')

@[expose] def StepYfpf (y₁ y₂ : G) : Prop :=
  (∀ a ∈ S.A, a * y₁ = y₁ * a → a = 1) ∧ (∀ a ∈ S.A', a * y₂ = y₂ * a → a = 1)

@[expose] def StepY0 (y₁ y₂ : G) : Prop :=
  y₁ * y₂⁻¹ ∈ S.K ∧ y₁ * y₂⁻¹ ∉ S.J ∧ orderOf (y₁ * y₂⁻¹) = 3

@[expose] def StepR (y₁ y₂ : G) : Prop :=
  (Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4 ∧
      S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) = ⊥) ∧
    (Nat.card ↥(S.A ⊓ centralizer ({y₂} : Set G)) = 4 ∧
      S.A' ⊓ (S.A ⊓ centralizer ({y₂} : Set G)) = ⊥) ∧
    (∀ w ∈ S.A', w * (y₁ * y₂) = (y₁ * y₂) * w → w ∈ S.Z) ∧
    (∀ w ∈ S.A, w * (y₁ * y₂) = (y₁ * y₂) * w → w ∈ S.Z)

@[expose] def StepAZ (y₁ y₂ : G) : Prop :=
  (∀ a ∈ S.A, ∃ z ∈ S.Z, ∃ r ∈ S.A ⊓ centralizer ({y₂} : Set G), a = z * r) ∧
    ∀ a ∈ S.A', ∃ z ∈ S.Z, ∃ r ∈ S.A' ⊓ centralizer ({y₁} : Set G), a = z * r

@[expose] def StepV (y₁ y₂ : G) : Prop :=
  ∃ v : G, v * v = 1 ∧ v * y₁ * v⁻¹ = y₁⁻¹ ∧ v * y₂ * v⁻¹ = y₂⁻¹ ∧
    ∀ b ∈ S.B, v * b * v⁻¹ ∈ S.B

@[expose] def StepZcomm : Prop :=
  ∀ z ∈ S.Z, z ∈ (commutator ↥S.L).map S.L.subtype

@[expose] def StepSpread : Prop :=
  (∀ g ∈ S.L1, g ∉ S.K → ∀ z ∈ S.Z, g * z * g⁻¹ ∈ S.Z → z ∈ S.B) ∧
    ∀ g ∈ S.L2, g ∉ S.K → ∀ z ∈ S.Z, g * z * g⁻¹ ∈ S.Z → z ∈ S.B

@[expose] def StepN : Prop :=
  (∀ h ∈ S.L1, (∀ l ∈ S.L2, h * l * h⁻¹ ∈ S.L2) → h ∈ S.K) ∧
    ∀ h ∈ S.L2, (∀ l ∈ S.L1, h * l * h⁻¹ ∈ S.L1) → h ∈ S.K

@[expose] def StepW : Prop :=
  (∀ g ∈ S.L2, g ∉ S.K → S.A ⊔ S.A.map (MulAut.conj g).toMonoidHom = S.L2) ∧
    ∀ g ∈ S.L1, g ∉ S.K → S.A' ⊔ S.A'.map (MulAut.conj g).toMonoidHom = S.L1

@[expose] def StepUniq : Prop :=
  ∀ h ∈ S.L1, ∀ g ∈ S.L2, g ∉ S.L1 → ∀ l ∈ S.L1, ∀ m ∈ S.L2, g * l = h * m → h ∈ S.L2

end HeSetup

@[expose] def Open422 (S : HeSetup G) (y₁ y₂ : G) : Prop :=
  ∀ c : G, c * y₁ = y₁ * c → c * y₂ = y₂ * c → (∀ b ∈ S.B, c * b = b * c) → c ∈ S.L1

end CFSG.Quasithin.A94.He42
