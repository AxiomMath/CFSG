module

public import CFSG.RankThree.GF2n.Stroth80.Sec44
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth312aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q →
    ∀ (𝓛 : Finset (Subgroup G)),
      (∀ L' ∈ 𝓛, (∃ m ∈ M, L' = conjSubgroup m (LB M Q B)) ∧ t ∈ L') → 1 < 𝓛.card →
      ∀ m : ℕ, 2 ≤ m → (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
          NaturalRep (ι := Fin m) K (StatedSL m K) (Rt M (LB M Q B) t)
            (Vt M (LB M Q B) B Z t) Z (hc.CN t)) →
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ m ∧ QuotSat (⨆ L' ∈ 𝓛, L') (inSubgroup (pCore 2) (⨆ L' ∈ 𝓛, L'))
          (IsSLModel k (Nat.card Z))

@[expose] def Stroth312bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q →
    ∀ (L₁ L₂ : Subgroup G), (∃ m ∈ M, L₁ = conjSubgroup m (LB M Q B)) →
      (∃ m ∈ M, L₂ = conjSubgroup m (LB M Q B)) → t ∈ L₁ → t ∈ L₂ → L₁ ≠ L₂ → ¬ SLNat hc t →
      QuotSat (L₁ ⊔ L₂) (inSubgroup (pCore 2) (L₁ ⊔ L₂)) (IsSLModel 2 (Nat.card Z)) ∨
        L₁ ⊔ L₂ = Rt M (LB M Q B) t

theorem iSup_pair_eq_sup (L₁ L₂ : Subgroup G) [DecidableEq (Subgroup G)] :
    (⨆ L' ∈ ({L₁, L₂} : Finset (Subgroup G)), L') = L₁ ⊔ L₂ := by
  rw [Finset.iSup_insert, Finset.iSup_singleton]

theorem stroth44_of_312ab (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (ha : Stroth312aStatement) (hb : Stroth312bStatement) (hCL : ClassicalNonsolvableStatement) :
    Stroth44Statement := by
  classical
  intro G _ _ M Q Z B hN hc n hw hn hno hgen A hAH hAN hodd
  by_contra hA
  obtain ⟨t, htLB, htQ, 𝓛, hL, hcard, hsolv, hne⟩ :=
    hc.exists_solvable_family h34 hw hn hno hgen A hAH hAN hodd hA
  obtain ⟨L₁, h₁, L₂, h₂, h12⟩ := Finset.one_lt_card.mp hcard
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hq2 : ∃ j : ℕ, Nat.card Z = 2 ^ j := ⟨jj, hZ2⟩
  obtain ⟨⟨m₁, hm₁, hL₁⟩, ht₁⟩ := hL L₁ h₁
  obtain ⟨⟨m₂, hm₂, hL₂⟩, ht₂⟩ := hL L₂ h₂
  have hle : L₁ ⊔ L₂ ≤ ⨆ L' ∈ 𝓛, L' :=
    sup_le (le_iSup₂_of_le L₁ h₁ le_rfl) (le_iSup₂_of_le L₂ h₂ le_rfl)
  have hsolv' : Group.IsSolvable ↥(L₁ ⊔ L₂) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  have hne' : L₁ ⊔ L₂ ≠ LB M Q B := by
    intro hX
    have hc₁ : Nat.card L₁ = Nat.card (LB M Q B) := hL₁ ▸ card_conjSubgroup m₁ _
    have hc₂ : Nat.card L₂ = Nat.card (LB M Q B) := hL₂ ▸ card_conjSubgroup m₂ _
    have e₁ : L₁ = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge (hX ▸ le_sup_left) hc₁.ge
    have e₂ : L₂ = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge (hX ▸ le_sup_right) hc₂.ge
    exact h12 (e₁.trans e₂.symm)
  by_cases hSL : SLNat hc t
  · obtain ⟨K, hF, hFin, hK, m, hm, hnat⟩ := hSL
    obtain ⟨k, hk2, -, hQSX⟩ := ha G M Q Z B hc n hw hn hno hgen t htLB htQ {L₁, L₂}
      (by
        intro L' hL'
        rcases Finset.mem_insert.mp hL' with rfl | hL'
        · exact ⟨⟨m₁, hm₁, hL₁⟩, ht₁⟩
        · rw [Finset.mem_singleton.mp hL']
          exact ⟨⟨m₂, hm₂, hL₂⟩, ht₂⟩)
      (by rw [Finset.card_pair h12]; norm_num) m hm ⟨K, hF, hFin, hK, hnat⟩
    rw [iSup_pair_eq_sup] at hQSX
    exact not_quotSat_isSLModel_of_solvable hCL hq4 hq2 hk2 hsolv' hQSX
  · rcases hb G M Q Z B hc n hw hn hno hgen t htLB htQ L₁ L₂ ⟨m₁, hm₁, hL₁⟩ ⟨m₂, hm₂, hL₂⟩
      ht₁ ht₂ h12 hSL with hSL2 | hXR
    · exact not_quotSat_isSLModel_of_solvable hCL hq4 hq2 le_rfl hsolv' hSL2
    · exact hc.false_of_eq_Rt h310 hCL hw hn hno hgen htLB htQ hXR hsolv' hne'

end CFSG.RankThree.GF2n.Stroth80
