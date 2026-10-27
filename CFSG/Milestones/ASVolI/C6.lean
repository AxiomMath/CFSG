module

public import CFSG.Milestones.ASVolI.C5

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

structure HypC_6_2 (L R TH Λ : Subgroup G) : Prop where
  L_finite : Finite L
  R_finite : Finite R
  TH_finite : Finite TH
  Λ_finite : Finite Λ
  R_acts : R ≤ Subgroup.normalizer (L : Set G)
  perf : L = oTwoUpper L
  O2_le : pCoreOf 2 (L ⊔ R) ≤ R
  U_ne : ⁅pCoreOf 2 L, L⁆ ≠ ⊥
  U_elem : IsElemAbelian 2 ⁅pCoreOf 2 L, L⁆
  TH_two : IsPGroup 2 TH
  R_le : R ≤ TH
  R_norm : TH ≤ Subgroup.normalizer (R : Set G)
  TH_norm : TH ≤ Subgroup.normalizer (Λ : Set G)
  L_sub : IsSubnormal L (L ⊔ TH)
  no_common : ∀ R₀ : Subgroup G, R₀ ≤ R → R₀ ≠ ⊥ → L ⊔ TH ≤ Subgroup.normalizer (R₀ : Set G) →
    ¬ (Λ ⊓ Subgroup.normalizer (R : Set G) ≤ Λ ⊓ Subgroup.normalizer (R₀ : Set G))

@[expose] noncomputable def mRU (R U : Subgroup G) : ℕ :=
  sInf {k : ℕ | ∃ A : Subgroup G, A ≤ U ∧ R ⊓ Subgroup.centralizer (U : Set G) <
    R ⊓ Subgroup.centralizer (A : Set G) ∧ A.relIndex U = 2 ^ k}

abbrev S3wrZ2 : Type := Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)

@[expose] def IsA3Product (H L : Subgroup G) (s : ℕ) : Prop :=
  ∃ K₁ : Subgroup G, IsBlock2 H K₁ ∧ IsAltType K₁ 3 ∧
    (s = 1 ∧ L = K₁ ∨ s = 2 ∧ ∃ K₂ : Subgroup G, K₂ ≠ K₁ ∧ IsBlock2 H K₂ ∧ IsAltType K₂ 3 ∧
      K₁ ≤ Subgroup.centralizer (K₂ : Set G) ∧ L = K₁ ⊔ K₂)

@[expose] def e12 : ↥(evenWeight 7) :=
  ⟨fun i => if i = 0 ∨ i = 1 then 1 else 0, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    decide +kernel⟩

structure A7QuotientIdent (H R : Subgroup G) (α : ↥H →* Equiv.Perm (Fin 7)) : Prop where
  onto : Function.Surjective α
  ker : α.ker = (pCoreOf 2 H).subgroupOf H
  R_img : (R.subgroupOf H).map α = Subgroup.zpowers (Equiv.swap (0 : Fin 7) 1)

structure A7Ident (H L R : Subgroup G) (α : ↥H →* Equiv.Perm (Fin 7))
    (β : ↥(blockU L) →* Multiplicative (evenWeight 7)) : Prop where
  onto : Function.Surjective α
  ker : α.ker = (pCoreOf 2 H).subgroupOf H
  R_img : (R.subgroupOf H).map α = Subgroup.zpowers (Equiv.swap (0 : Fin 7) 1)
  β_bij : Function.Bijective β
  equiv : ∀ (h : ↥H) (u v : ↥(blockU L)), (v : G) = h * u * h⁻¹ → ∀ i : Fin 7,
    ((Multiplicative.toAdd (β v) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) ((α h)⁻¹ i)

@[expose] def E12In (L : Subgroup G) (β : ↥(blockU L) →* Multiplicative (evenWeight 7)) : Subgroup G :=
  (Subgroup.comap β (Subgroup.zpowers (Multiplicative.ofAdd e12))).map (blockU L).subtype

end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_6_1 : Prop :=
  ∀ (G : Type) [Group G] (H Λ : Subgroup G) [Finite H] [Finite Λ],
    CharTwo H →
    ((∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
      QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
      QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2))) →
    IsPGroup 2 Λ → IsSylowTwoOf (Λ ⊓ H) H →
    Λ ⊓ H < Λ →
    (∀ T₀ : Subgroup G, T₀ ≠ ⊥ → T₀ ≤ Λ ⊓ H → H ≤ Subgroup.normalizer (T₀ : Set G) →
      Λ ⊓ Subgroup.normalizer (T₀ : Set G) = Λ ⊓ H) →
    ((Λ ⊓ H).relIndex (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) = 2 ∧
      thompsonJ (Λ ⊓ H) = baum (Λ ⊓ H) ∧
      ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        (baum (Λ ⊓ H) : Set G) = (pCoreOf 2 H : Set G) * (rconj x (pCoreOf 2 H) : Set G)) ∧
    ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
        IsAltType (oTwoUpper H) 5)) ∨
      IsA3Product H (oTwoUpper H) 1 ∨ IsA3Product H (oTwoUpper H) 2) ∧
    (∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
      ((IsBlock2 H (oTwoUpper H) ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type (oTwoUpper H) n) ∨
          IsAltType (oTwoUpper H) 3)) →
        AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H)}) ∧
      (∀ n : ℕ, 1 < n → IsBlock2 H (oTwoUpper H) → IsLin2Type (oTwoUpper H) n →
        ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
          IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n) ∧
      (IsBlock2 H (oTwoUpper H) → IsAltType (oTwoUpper H) 3 →
        ∀ B : Subgroup G, B ≤ (Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) →
          IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ 1)) ∧
    (∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
      ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) →
      ∃ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H ∧ r ∉ thompsonJ (Λ ⊓ H) ∧
        (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
        AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H), A₁, rconj r A₁}) ∧
    ((pCoreOf 2 H : Set G) =
      (((Λ ⊓ H) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) *
        (pCoreOf 2 (oTwoUpper H) : Set G)) ∧
    (((Λ ⊓ H).relIndex Λ = 2 ∧ thompsonJ (Λ ⊓ H) = thompsonJ Λ ∧
      ((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3) →
        Nonempty (↥H ≃* (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∨
    (IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 3 ∧
      Nonempty (↥H ≃* Equiv.Perm (Fin 4)) ∧ IsDihedralOrSemidihedral Λ) ∨
    (((IsBlock2 H (oTwoUpper H) ∧ IsAltType (oTwoUpper H) 5) ∨ IsA3Product H (oTwoUpper H) 2) ∧
      thompsonJ (Λ ⊓ H) = thompsonJ (Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G)) ∧
      QuotHas (Λ ⊓ Subgroup.normalizer ((Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G) :
          Subgroup G) : Set G)) (thompsonJ (Λ ⊓ H))
        (fun Y _ => Nonempty (Y ≃* DihedralGroup 4)) ∧
      ∀ x ∈ Λ ⊓ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G), x ∉ Λ ⊓ H →
        ∀ (A₁ : Subgroup G) (r : G), r ∈ Λ ⊓ H → r ∉ thompsonJ (Λ ⊓ H) →
          (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 →
          AFam (Λ ⊓ H) = {pCoreOf 2 H, rconj x (pCoreOf 2 H), A₁, rconj r A₁} →
          Nat.card ↥(Λ ⊓ Subgroup.normalizer ((A₁ ⊔ pCoreOf 2 H : Subgroup G) : Set G)) ≥
            Nat.card ↥(Λ ⊓ H)))

@[expose] def C_6_2 : Prop :=
  ∀ (G : Type) [Group G] (L R TH Λ : Subgroup G), HypC_6_2 L R TH Λ →
    ¬ (L ⊔ TH ≤ Subgroup.normalizer (R : Set G)) ∧ pCoreOf 2 (L ⊔ R) < R

theorem as_C_6_2 : C_6_2 := by
  intro G _ L R TH Λ h
  have hR : R ≠ ⊥ := by
    intro hR0
    have h1 : pCoreOf 2 L ≤ ⊥ := by
      have h0 := h.O2_le
      rw [hR0, sup_bot_eq] at h0
      exact h0
    apply h.U_ne
    rw [le_bot_iff.mp h1]
    simp
  have hnot : ¬ (L ⊔ TH ≤ Subgroup.normalizer (R : Set G)) := fun hLT =>
    h.no_common R le_rfl hR hLT le_rfl
  refine ⟨hnot, lt_of_le_of_ne h.O2_le fun heq => hnot ?_⟩
  have hN : L ⊔ R ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ R) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ R)
  rw [heq] at hN
  exact sup_le (le_sup_left.trans hN) h.R_norm

@[expose] def C_6_3 : Prop :=
  ∀ (G : Type) [Group G] (L R TH Λ : Subgroup G), HypC_6_2 L R TH Λ →
    let X := Λ ⊓ Subgroup.normalizer (R : Set G)
    let Q := pCoreOf 2 (L ⊔ R)
    let D := R ⊓ Subgroup.centralizer (L : Set G)
    let U := ⁅pCoreOf 2 L, L⁆
    (∃ x ∈ (X : Set G) * (TH : Set G), ¬ rconj x U ≤ Q) ∧
    (R ⊓ Subgroup.centralizer (U : Set G) ≤ Q →
      ∀ x ∈ (X : Set G) * (TH : Set G), ¬ rconj x U ≤ Q →
        mRU R U ≤ Nat.log 2 ((rconj x U ⊓ Subgroup.centralizer (U : Set G)).relIndex (rconj x U))) ∧
    (Q = R ⊓ Subgroup.centralizer (U : Set G) →
      (frattini ↥Q).map Q.subtype ≤ D →
      QuotHas R Q (fun Y _ => IsE2 (mRU R U) Y) →
      ∀ x ∈ (X : Set G) * (TH : Set G), ¬ rconj x U ≤ Q →
        (((R : Set G) = (U : Set G) * (rconj x U : Set G) *
              ((R ⊓ Subgroup.centralizer ((U ⊔ rconj x U : Subgroup G) : Set G) : Subgroup G) :
                Set G) ∧
            (R : Set G) = (rconj x U : Set G) * (Q : Set G)) ∧
          (Q : Set G) = (U : Set G) *
            ((Q ⊓ Subgroup.centralizer (rconj x U : Set G) : Subgroup G) : Set G)) ∧
        ((∀ q ∈ Q, (∀ r ∈ R, q * r * q⁻¹ * r⁻¹ ∈ D) → q ∈ U ⊔ D) → Q = U ⊔ D) ∧
        ((TH ⊓ Λ).relIndex X = 2 → TH ≤ Subgroup.normalizer (L : Set G) →
          AFam R = {Q, rconj x Q} ∧ (R : Set G) = (Q : Set G) * (rconj x Q : Set G) ∧
          D ⊓ rconj x D = ⊥ ∧ (frattini ↥D).map D.subtype = ⊥))

@[expose] def C_6_4 : Prop :=
  ∀ (G : Type) [Group G] (L R TH Λ : Subgroup G), HypC_6_2 L R TH Λ →
    let H := L ⊔ TH
    let X := Λ ⊓ Subgroup.normalizer (R : Set G)
    let Q := pCoreOf 2 H
    let D := R ⊓ Subgroup.centralizer (L : Set G)
    let U := ⁅pCoreOf 2 L, L⁆
    let LV := oTwoUpper (L ⊓ Subgroup.normalizer (R : Set G))
    L = oTwoUpper H → IsBlock2 H L → IsAltType L 7 → Q ≤ R →
    ∀ α : ↥H →* Equiv.Perm (Fin 7), A7QuotientIdent H R α →
    (∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → H ≤ Subgroup.normalizer (R₀ : Set G) →
      Λ ⊓ Subgroup.normalizer (R₀ : Set G) = R) →
    IsPGroup 2 Λ → LV ≤ Subgroup.normalizer (Λ : Set G) →
    ∃ β : ↥(blockU L) →* Multiplicative (evenWeight 7), A7Ident H L R α β ∧
    ⁅U, R⁆ = E12In L β ∧
    ((Q = D ⊔ U ∧ D ⊓ U = ⊥ ∧ U ≤ Subgroup.centralizer (D : Set G)) ∧ ⁅Q, R⁆ = E12In L β) ∧
    (R.relIndex X = 2 ∧ ∀ x ∈ X, x ∉ R → ¬ rconj x U ≤ Q) ∧
    (∀ x ∈ X, x ∉ R → (R : Set G) = (Q : Set G) * (rconj x U : Set G) ∧
      AFam R = {Q, rconj x Q}) ∧
    (∀ x ∈ X, x ∉ R → D ⊓ rconj x D = ⊥) ∧
    D ≤ centerOf R ∧
    (R ≤ thompsonJ Λ ∧ ∃ Q₀ D₀ : Subgroup G, thompsonJ Λ = Q₀ ⊔ D₀ ∧ Q₀ ⊓ D₀ = ⊥ ∧
      D₀ ≤ Subgroup.centralizer (Q₀ : Set G) ∧ Q₀ ≤ centerOf R ∧
      Q₀.relIndex (centerOf R) = 2 ∧ ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥D₀ ≃* DihedralGroup n)) ∧
    (thompsonJ Λ).relIndex Λ ≤ 2 ∧
    (LV = oTwoUpper (LV ⊔ Λ) ∧ (LV.subgroupOf (LV ⊔ Λ)).Normal ∧
      Λ ≤ Subgroup.centralizer (pCoreOf 2 LV : Set G)) ∧
    E12In L β ≤ centerOf (TH ⊔ Λ)

end CFSG.ASVolI
