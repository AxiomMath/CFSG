module

public import CFSG.Walter.W67.Interface
public import CFSG.Walter.JRAssembly
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

@[expose] def S_Frame_nonempty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (h : Hyp G), Nonempty (Frame h)

@[expose] def S_lemma_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (h : Hyp G) (fr : Frame h),
    (h.q % 8 = 3 ∨ h.q % 8 = 5) ∧
    JT.IsInternalDirectProduct (Subgroup.zpowers h.J) h.F h.CK ∧ Odd (Nat.card h.F) ∧
    h.K ⊓ h.CK = ⊥ ∧
    IsElementaryAbelian 2 (fr.S : Subgroup G) ∧ Nat.card (fr.S : Subgroup G) = 8 ∧
    JT.IsInternalDirectProduct (Subgroup.zpowers h.J) fr.T fr.S ∧
    h.H ⊓ Subgroup.centralizer (fr.T : Set G) = fr.CS ∧
    JT.IsInternalDirectProduct (fr.S : Subgroup G) fr.E fr.CS ∧
    h.F ≤ fr.E ∧ (h.F.subgroupOf fr.E).Normal ∧ (∃ g ∈ fr.E, Subgroup.zpowers g ⊔ h.F = fr.E) ∧
    fr.E ⊓ Subgroup.centralizer (h.K : Set G) = h.F ∧ h.K ⊓ fr.E = ⊥ ∧
    JT.IsInternalDirectProduct (Subgroup.zpowers h.J) (h.K ⊔ fr.E) h.H

@[expose] def S_lemma_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (h : Hyp G) (fr : Frame h),
    (∀ N : Subgroup G, N.Normal → N.index ≠ 2) →
    (fr.CS.subgroupOf (Subgroup.normalizer ((fr.S : Subgroup G) : Set G))).index = 21 ∧
    (∀ s ∈ (fr.S : Subgroup G), ∀ t ∈ (fr.S : Subgroup G), orderOf s = 2 → orderOf t = 2 →
      ∃ n ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G), n * s * n⁻¹ = t) ∧
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y

@[expose] def S_IsJRSubgroup_nonempty_jrGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {L K' : Subgroup G} {J : G} {p g : ℕ} [Fact p.Prime],
    p ≠ 2 → 0 < g → IsJRSubgroup L J K' p g →
    ∃ hL' : JRGroup L, hL'.p = p ∧ hL'.f = g ∧ (hL'.J : G) = J ∧
      hL'.K.map L.subtype = K'

@[expose] def S_lemma_2_6_i : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (h : Hyp G) (fr : Frame h) {X : Subgroup G}, X ≤ fr.E → X ≠ ⊥ →
    h.eX X ∣ h.f ∧ Nonempty (h.KX X ≃* PSL(2, GaloisField h.p (h.f / h.eX X))) ∧
    Subgroup.normalizer (X : Set G) ⊓ h.H =
      Subgroup.zpowers h.J ⊔ (h.KX X ⊔ fr.EX X)

@[expose] def S_lemma_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : MinCE G) (fr : Frame m.toHyp), 3 < m.q → fr.E ≠ ⊥ →
    commutator G = ⊤ → JFacts → RFacts → RMult →
    (m.p = 3 ∨ m.p = 5) ∧ m.eX fr.E ∣ m.f ∧
    ((m.p = 3 ∧ Odd m.f) ∨
      (m.p = 5 ∧ m.eX fr.E = m.f ∧ (m.f = 1 ∨ (m.f.Prime ∧ m.F = ⊥))))

@[expose] def S_Std_nonempty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : MinCE G), JFacts → RFacts → RMult →
    ∃ s : Std G, s.toMinCE = m

@[expose] def S_prop_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), JFacts → RFacts → ∀ {r : ℕ}, r ∈ s.fr.σ →
    (s.p = 3 → r = 3 ∨ r ∣ s.q ^ 2 - s.q + 1) ∧
    (s.p = 5 → r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 19)

@[expose] def S_lemma_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → ∀ {T₂ : G}, T₂ ∈ s.fr.T →
    orderOf T₂ = 2 → ∀ (N : Subgroup G), s.A T₂ ⊔ s.V T₂ ≤ N → (Nat.card N).factorization 2 = 2 →
    ((s.V T₂).subgroupOf N).Normal

@[expose] def S_prop_4_3_ab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (h : Hyp G) (fr : Frame h), h.p = 3 →
    (∀ N : Subgroup G, N.Normal → N.index ≠ 2) → ∀ {T₂ : G}, T₂ ∈ fr.T → orderOf T₂ = 2 →
    ∃ U : Subgroup G, Nat.card U = 3 ∧
      Subgroup.normalizer (fr.V T₂ : Set G) = U ⊔ Subgroup.centralizer (fr.V T₂ : Set G) ∧
      U ≤ Subgroup.centralizer (fr.E : Set G) ∧ ⁅U, fr.V T₂⁆ = fr.V T₂ ∧
      Nat.card ↥((fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) = 2 ∧
      let T₁g : Subgroup G := (fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)
      JT.IsInternalDirectProduct (fr.V T₂) (T₁g ⊔ fr.A T₂ ⊔ fr.E)
        (Subgroup.centralizer (fr.V T₂ : Set G)) ∧
      ⁅T₁g, fr.A T₂ ⊔ fr.E⁆ = fr.A T₂ ∧
      JT.IsInternalDirectProduct (fr.V T₂) T₁g fr.S

@[expose] def S_prop_4_3_c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → ∀ {T₂ : G}, T₂ ∈ s.fr.T →
    orderOf T₂ = 2 → RFacts →
    (∀ Aα : Subgroup G, Aα ≤ s.A T₂ → Aα ≠ ⊥ →
        Subgroup.normalizer (Aα : Set G) = Subgroup.normalizer (s.V T₂ : Set G)) ∧
      (∀ Aα : Subgroup G, Aα ≤ s.A₀ T₂ → Aα ≠ ⊥ →
        Subgroup.centralizer (Aα : Set G) = s.V T₂ ⊔ s.A T₂ ⊔ s.fr.E ∧
        ((Subgroup.centralizer (Aα : Set G)).subgroupOf
          (Subgroup.normalizer (Aα : Set G))).index = 6)

@[expose] def S_cor_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → ∀ {T₂ : G}, T₂ ∈ s.fr.T →
    orderOf T₂ = 2 → RFacts →
    Nat.Coprime (Nat.card (s.A T₂)) (s.A T₂).index ∧
    (s.A₀ T₂ ≠ ⊥ → CFSG.IsTISubset (s.D₂ T₂) (Subgroup.normalizer (s.V T₂ : Set G)))

@[expose] def S_lemma_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → ∀ (f5 : Frame5 s) (P : Subgroup G),
    IsElementaryAbelian 3 P → P ≠ ⊥ →
    Subgroup.zpowers s.J ⊔ f5.B ⊔ s.fr.E ≤ Subgroup.normalizer (P : Set G) →
    (∀ Q : Subgroup G, Q ≤ P →
      Subgroup.zpowers s.J ⊔ f5.B ⊔ s.fr.E ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥ ∨ Q = P) →
    Subgroup.normalizer (P : Set G) =
      (Subgroup.zpowers s.J ⊔ f5.B ⊔ s.fr.E) ⊔ Subgroup.centralizer (P : Set G)

@[expose] def S_prop_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → RFacts →
    ¬ 3 ∣ Nat.card s.fr.E

@[expose] def S_lemma_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), RFacts → ∀ {X : Subgroup G}, X ≤ s.fr.E → X ≠ ⊥ →
    Group.IsSolvable (s.L X) → X = s.fr.E ∧ (Nat.card s.fr.E).Prime

@[expose] def S_lemma_6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), JFacts → RFacts → ∀ {r : ℕ} [Fact r.Prime],
    r ∈ s.fr.σ → ∀ (P₀ : Subgroup G), P₀ ≤ s.fr.E → IsPGroup r P₀ →
    (Nat.card P₀).factorization r = (Nat.card s.fr.E).factorization r →
    ¬ Group.IsSolvable (Subgroup.normalizer ((omega1 r P₀ : Subgroup G) : Set G)) →
    ∀ (P : Subgroup G), P ≤ Subgroup.normalizer ((omega1 r P₀ : Subgroup G) : Set G) →
    IsPGroup r P →
    (Nat.card P).factorization r =
      (Nat.card (Subgroup.normalizer ((omega1 r P₀ : Subgroup G) : Set G))).factorization r →
    P ⊓ s.fr.E = P₀ → P ⊓ Subgroup.centralizer ({s.J} : Set G) = P₀ →
    ¬ IsCyclic ↥(P ⊓ s.L (omega1 r P₀))

@[expose] def S_cor_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 5 → JFacts → RFacts →
    False

@[expose] def S_lemma_6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), RFacts → ∀ {X : Subgroup G}, X ≤ s.fr.E → X ≠ ⊥ →
    Group.IsSolvable (Subgroup.normalizer (X : Set G)) →
    X = s.fr.E ∧ Nat.card X = 7 ∧
    (∀ x y : G, orderOf x = 7 → y * x * y⁻¹ ≠ x⁻¹) ∧
    ∀ P : Sylow 3 G, IsElementaryAbelian 3 (P : Subgroup G) ∧ Nat.card (P : Subgroup G) = 3 ^ 7 ∧
      ∀ x ∈ (P : Subgroup G), x ≠ 1 →
        (Nat.card (Subgroup.centralizer ({x} : Set G))).factorization 7 = 1

@[expose] def S_lemma_6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), JFacts → RFacts → ∀ {r : ℕ} [Fact r.Prime],
    r ∈ s.fr.σ → ∀ (P₀ : Subgroup G), P₀ ≤ s.fr.E → IsPGroup r P₀ →
    (Nat.card P₀).factorization r = (Nat.card s.fr.E).factorization r →
    ¬ Group.IsSolvable (Subgroup.normalizer ((omega1 r P₀ : Subgroup G) : Set G))

@[expose] def S_prop_6_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → JFacts → RFacts →
    (∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q ≠ 5 →
      ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → ∀ P : Sylow p L, IsCyclic (P : Subgroup L)) →
    False

@[expose] def S_prop_6_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → RFacts →
    Nat.card s.fr.E < s.f

section CT

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
open scoped Classical

@[expose] def S_lemma_7_1 : Prop :=
  ∀ {Γ : Type} [Group Γ] [Fintype Γ] (Hh Kk Ee Xx : Subgroup Γ) (hK : Kk ≤ Hh),
    (Kk.subgroupOf Hh).Normal → Ee ≤ Xx → Xx ≤ Hh → Kk ⊓ Ee = ⊥ ∧ Kk ⊔ Ee = Hh → ∀ (D : Set Γ),
    D ⊆ Xx →
    (∀ g ∈ Hh, (D ∩ (fun x => g * x * g⁻¹) '' D).Nonempty →
      g ∈ Xx ∧ (fun x => g * x * g⁻¹) '' D = D) →
    ∀ (r : ℕ) (a b : Fin r → ℤ), (∀ i, a i = 1 ∨ a i = -1) → (∀ i, b i = 1 ∨ b i = -1) →
    ∀ (φ : Fin r → ↥(Xx ⊓ Kk) → ℂ) (χ' : Fin r → Kk → ℂ), (∀ i, φ i ∈ CFSG.BlocksIrr ↥(Xx ⊓ Kk)) →
    (∀ i, χ' i ∈ CFSG.BlocksIrr Kk) → Function.Injective φ → Function.Injective χ' →
    (∀ i, ∀ x ∈ Hh, ∀ k : Kk, ∀ hk : x * (k : Γ) * x⁻¹ ∈ Kk, χ' i ⟨_, hk⟩ = χ' i k) →
    ∀ (θY : ↥(Xx ⊓ Kk) → ℂ), (θY = ∑ i, (a i : ℂ) • φ i) →
    (∀ y : ↥(Xx ⊓ Kk), (y : Γ) ∉ D → θY y = 0) →
    ((fun k : Kk => inducedFunction ((Xx ⊓ Kk).subgroupOf Kk)
        (fun y => θY ⟨y, Subgroup.mem_subgroupOf.mp y.2⟩) k) = ∑ i, (b i : ℂ) • χ' i) →
    ∀ (φX : Fin r → Xx → ℂ), (∀ i, φX i ∈ CFSG.BlocksIrr Xx) →
    (∀ i, ∀ y : ↥(Xx ⊓ Kk), φX i (Subgroup.inclusion inf_le_left y) = φ i y) →
    (∀ x : Xx, (x : Γ) ∉ D → (∑ i, (a i : ℂ) • φX i) x = 0) →
    ∃ χ : Fin r → Hh → ℂ, (∀ i, χ i ∈ CFSG.BlocksIrr Hh) ∧
      (∀ i, ∀ k : Kk, χ i (Subgroup.inclusion hK k) = χ' i k) ∧
      (fun x : Hh => inducedFunction (Xx.subgroupOf Hh)
        (fun y => (∑ i, (a i : ℂ) • φX i) ⟨y, Subgroup.mem_subgroupOf.mp y.2⟩) x) =
        ∑ i, (b i : ℂ) • χ i

end CT

section CT7

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
open scoped Classical

attribute [local instance] Fintype.ofFinite

end CT7

@[expose] def S_ctData_of_hypII : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hII : HypII G), ¬ 3 ∣ Nat.card hII.fr.E →
    Nonempty (CTData hII.q (Nat.card hII.fr.E) (Nat.card G))

@[expose] def S_prop_8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hII : HypII G), ¬ 3 ∣ Nat.card hII.fr.E → hII.fr.E = ⊥

@[expose] def S_lemma_8_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 3 → RFacts →
    ∃ hII : HypII G, hII.toHyp = s.toHyp ∧ hII.fr.S = s.fr.S

@[expose] def S_psl2_three_oddMultiplier : Prop :=
  ∀ n : ℕ, Odd n → OddMultiplierTrivial (PSL(2, GaloisField 3 n))

@[expose] def S_lemma_8_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {L : Type} [Group L] [Finite L] (hL : JRGroup L), 3 < hL.q →
    hL.R1 ∧ hL.R2 ∧ hL.R4 → ∀ (Z : Subgroup G) [Z.Normal], Z ≤ Subgroup.center G →
    Odd (Nat.card Z) → Z ≠ ⊥ → commutator G = ⊤ → (G ⧸ Z) ≃* L →
    ∃ hII : HypII G, hII.fr.E = Z

@[expose] def S_rMult_of : Prop :=
  RFacts → RMult

@[expose] def S_outCyclic_of_R : Prop :=
  ∀ {L : Type} [Group L] [Finite L] (hL : JRGroup L), 5 < hL.q → JTThreeHyp → OutCyclic L

@[expose] def S_rFacts_of : Prop :=
  JTThreeHyp → RFacts

end CFSG.Walter.W67
