module

public import CFSG.RankThree.GF2n.Tim79a34Pairing

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open scoped commutatorElement

variable {G : Type} [Group G]

structure TwData (V H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H) (a : Fin n ⊕ Fin n → GaloisField 2 1)
    (T : Subgroup ↥(StatedSp n (GaloisField 2 1))) (z₀ : Xbar V H) : Prop where
  three_le : 3 ≤ n
  bij : Function.Bijective Φ
  ne_zero : a ≠ 0
  trans : CaseM.IsTransGroup a T
  map_eq : T.map Φ = VZ V H
  z_mem : z₀ ∈ Subgroup.center (Xbar V H)
  z_ne : z₀ ≠ 1
  z_sq : z₀ * z₀ = 1
  center_eq : Subgroup.center (Xbar V H) = Subgroup.zpowers z₀
  inf_eq : Subgroup.center (Xbar V H) ⊓ commutator (Xbar V H) = ⊥
  sup_eq : Subgroup.center (Xbar V H) ⊔ commutator (Xbar V H) = ⊤
  D_not_comm : ∀ d ∈ Dy V H, d ∉ commutator (Xbar V H)
  D_mul : ∀ d ∈ Dy V H, z₀ * d ∈ commutator (Xbar V H)

@[expose] def TwistedStructStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    qBar V H = 2 → Sec23Three V H → ¬ CentreClause V H →
    ∃ (n : ℕ) (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H)
      (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
      (z₀ : Xbar V H), TwData V H Φ a T z₀

@[expose] def TwistedWLowerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    ∀ {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H)
      (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
      (z₀ : Xbar V H), TwData V H Φ a T z₀ →
    Nat.card ↥(V ⊓ wOf V H) ^ (2 * n) ≤ Nat.card ↥(wOf V H)

@[expose] def TwistedWSplitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    Sec25Concl V H P →
    Nat.card ↥(wOf V H) = Nat.card ↥(P ⊓ wOf V H) * Nat.card ↥(V ⊓ wOf V H)

@[expose] def TwistedZRStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    Sec24bTilde V H P → Sec25Concl V H P →
    ∀ {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H)
      (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
      (z₀ : Xbar V H), TwData V H Φ a T z₀ → z₀ ∈ Rbar V H P

@[expose] def TwistedBoundStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    qBar V H = 2 → Sec24bTilde V H P → Sec25Concl V H P →
    ∀ {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H)
      (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1)))
      (z₀ : Xbar V H), TwData V H Φ a T z₀ → z₀ ∈ Rbar V H P →
    2 * Nat.card ↥(P ⊓ wOf V H) ≤ Nat.card ↥(V ⊓ wOf V H) ^ (2 * n - 1)

@[expose] def NoInvCompStatement : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (F : Type) [Field F] [CharP F 2] [Finite F], Nat.card F = 2 →
    ∀ (a : Fin n ⊕ Fin n → F), a ≠ 0 → ∀ (T S : Subgroup ↥(StatedSp n F)),
      CaseM.IsTransGroup a T → S ≤ spRad a → S ⊔ T = spRad a → S ⊓ T = ⊥ →
      (∀ (w : Fin n ⊕ Fin n → F) (g : ↥(StatedSp n F)), CaseM.spForm a w = 0 →
        SpExtras.mat n F g = CaseM.spTrans w 1 → ∀ x ∈ S, g * x * g⁻¹ ∈ S) → False

@[expose] def SpRadFactsStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (F : Type) [Field F] [CharP F 2] [Finite F], Nat.card F = 2 →
    ∀ (a : Fin n ⊕ Fin n → F), a ≠ 0 →
      (∀ g ∈ spRad a, ∀ h ∈ spRad a, g * h = h * g) ∧ (∀ g ∈ spRad a, g * g = 1) ∧
        Nat.card ↥(spRad a) = 2 ^ (2 * n - 1)

@[expose] def CommPairingStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B Px K₀ : Subgroup G) (m : ℕ), A ≤ B → K₀ ≤ Px →
    (∀ b ∈ B, ∀ r ∈ Px, ⁅b, r⁆ ∈ A) → (∀ a ∈ A, ∀ x ∈ B ⊔ Px, a * x = x * a) →
    (∀ b ∈ B, ∀ k ∈ K₀, b * k = k * b) →
    (∀ b ∈ B, (∀ r ∈ Px, b * r = r * b) → b ∈ A) →
    (∀ r ∈ Px, ∀ k ∈ K₀, r * k * r⁻¹ ∈ K₀) → (∀ r ∈ Px, ∀ r' ∈ Px, ⁅r, r'⁆ ∈ K₀) →
    (∀ r ∈ Px, r * r ∈ K₀) → K₀.relIndex Px = 2 ^ m →
    Nat.card ↥B ≤ Nat.card ↥A * Nat.card ↥A ^ m

theorem tim79a34TwoTwistedStatement_of_steps (hA : TwistedStructStatement)
    (hα : TwistedWLowerStatement) (hβ : TwistedWSplitStatement) (hγ : TwistedZRStatement)
    (hδ : TwistedBoundStatement) : Tim79a34TwoTwistedStatement := by
  intro G _ _ M V Q P H hs hq h3 hnc hT hC
  obtain ⟨n, Φ, a, T, z₀, hd⟩ := hA G M V Q P H hs hq h3 hnc
  have h1 := hα G M V Q P H hs Φ a T z₀ hd
  have h2 := hβ G M V Q P H hs hC
  have h3' := hγ G M V Q P H hs hT hC Φ a T z₀ hd
  have h4 := hδ G M V Q P H hs hq hT hC Φ a T z₀ hd h3'
  have hn := hd.three_le
  have hApos : 0 < Nat.card ↥(V ⊓ wOf V H) := Nat.card_pos
  have hpow : Nat.card ↥(V ⊓ wOf V H) ^ (2 * n) =
      Nat.card ↥(V ⊓ wOf V H) * Nat.card ↥(V ⊓ wOf V H) ^ (2 * n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2, hpow, mul_comm (Nat.card ↥(P ⊓ wOf V H))] at h1
  have h5 := Nat.le_of_mul_le_mul_left h1 hApos
  have h6 : 0 < Nat.card ↥(V ⊓ wOf V H) ^ (2 * n - 1) := pow_pos hApos _
  omega

end CFSG.RankThree.GF2n.Tim79a
