module

public import CFSG.Quasithin.H13.A6S138Ia
public import CFSG.Quasithin.H13.A6S1384a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] def NatL4 (S : Setting4 G T L V) (H : Subgroup G) : Prop :=
  ∃ ρ : ↥H →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
    Function.Surjective ρ ∧ (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
    ∃ β : ↥(conjClosure S.V3 H) →* Multiplicative (Fin 4 → ZMod 2),
      Function.Surjective β ∧
      (∀ u : ↥(conjClosure S.V3 H), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
      ∀ (h : ↥H) (u v : ↥(conjClosure S.V3 H)), (v : G) = h * u * h⁻¹ →
        Multiplicative.toAdd (β v) =
          ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u))

end Setting4

@[expose] def Lem13825One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ∀ n, 3 ≤ n → n ≤ 5 → IsPSL n 2 1 ↥(S.KSt H K) →
      (∃ h ∈ H, InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) →
      n = 4 ∧ IsHatA6 L ∧ S.NatL4 H

@[expose] def Lem13825NoL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
      (∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) →
      ¬ IsPSL 3 2 1 ↥(S.KSt H K)

@[expose] def Lem13825Par : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    (∀ H' ∈ S.Hz, ∀ K' ∈ cComp H', ¬ IsPSL 3 2 1 ↥(S.KSt H' K')) →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
      (∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) →
      ∀ n, 4 ≤ n → n ≤ 5 → IsPSL n 2 1 ↥(S.KSt H K) →
        n = 4 ∧ (IsHatA6 L ↔ T ≤ K ⊔ pCoreOf 2 H)

@[expose] def Lem13825G1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    (∀ H' ∈ S.Hz, ∀ K' ∈ cComp H', ¬ IsPSL 5 2 1 ↥(S.KSt H' K')) →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, IsPSL 4 2 1 ↥(S.KSt H K) → H = S.G1

@[expose] def Lem13825NoA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
      (∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) →
      IsPSL 4 2 1 ↥(S.KSt H K) → ¬ IsHatA6 L → ¬ T ≤ K ⊔ pCoreOf 2 H → False

@[expose] def Lem13825Nat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
      (∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) →
      IsPSL 4 2 1 ↥(S.KSt H K) → IsHatA6 L → T ≤ K ⊔ pCoreOf 2 H → H = S.G1 → S.NatL4 H

theorem lem13825_of (h1 : Lem13825One) (h2a : Lem13825NoL3) (h2 : Lem13825Par)
    (h3 : Lem13825G1) (h4 : Lem13825NoA6) (h5 : Lem13825Nat) : Lem13825 := by
  intro G _ _ T L V S hS H hH K hK n hn3 hn5 hn
  have hno3 : ∀ H' ∈ S.Hz, ∀ K' ∈ cComp H', ¬ IsPSL 3 2 1 ↥(S.KSt H' K') := by
    intro H' hH' K' hK' h3'
    by_cases htr : ∃ h ∈ H', InducesTransvMod h (conjClosure S.V3 H') (fsuV1 T V)
    · have := (h1 G T L V S hS H' hH' K' hK' 3 le_rfl (by norm_num) h3' htr).1
      omega
    · push Not at htr
      exact h2a G T L V S hS H' hH' K' hK' htr h3'
  have hn4 : ∀ H' ∈ S.Hz, ∀ K' ∈ cComp H', ∀ m, 3 ≤ m → m ≤ 5 →
      IsPSL m 2 1 ↥(S.KSt H' K') → m = 4 := by
    intro H' hH' K' hK' m hm3 hm5 hm
    by_cases htr : ∃ h ∈ H', InducesTransvMod h (conjClosure S.V3 H') (fsuV1 T V)
    · exact (h1 G T L V S hS H' hH' K' hK' m hm3 hm5 hm htr).1
    · push Not at htr
      rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | hm4
      · exact absurd hm (hno3 H' hH' K' hK')
      · exact (h2 G T L V S hS hno3 H' hH' K' hK' htr m hm4 hm5 hm).1
  have hno5 : ∀ H' ∈ S.Hz, ∀ K' ∈ cComp H', ¬ IsPSL 5 2 1 ↥(S.KSt H' K') := by
    intro H' hH' K' hK' h5'
    have := hn4 H' hH' K' hK' 5 (by norm_num) le_rfl h5'
    omega
  obtain rfl : n = 4 := hn4 H hH K hK n hn3 hn5 hn
  have hG1 : H = S.G1 := h3 G T L V S hS hno5 H hH K hK hn
  have key : IsHatA6 L ∧ S.NatL4 H := by
    by_cases htr : ∃ h ∈ H, InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)
    · obtain ⟨-, hhat, hnat⟩ := h1 G T L V S hS H hH K hK 4 (by norm_num) (by norm_num) hn htr
      exact ⟨hhat, hnat⟩
    · push Not at htr
      obtain ⟨-, hiff⟩ := h2 G T L V S hS hno3 H hH K hK htr 4 le_rfl (by norm_num) hn
      by_cases hhat : IsHatA6 L
      · exact ⟨hhat, h5 G T L V S hS H hH K hK htr hn hhat (hiff.mp hhat) hG1⟩
      · exact (h4 G T L V S hS H hH K hK htr hn hhat fun hT => hhat (hiff.mpr hT)).elim
  obtain ⟨hhat, ρ, hρ, hk, β, hβ, hβk, heq⟩ := key
  exact ⟨rfl, ⟨hhat, ρ, hρ, hk, β, hβ, hβk, heq⟩, hG1⟩

end CFSG.Quasithin.H13.A6
