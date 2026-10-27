module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSL
public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerNormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGOppositeRadicalCountNormalAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
        ∀ V ∈ ggOppositeRadicals G₀ Q,
          G₀ ≤ Subgroup.normalizer ((Q ⊔ V : Subgroup G) : Set G)

theorem ggOppositeRadicalCountNormalInput_iff :
    GGOppositeRadicalCountNormalInput ↔ ∀ t, GGOppositeRadicalCountNormalAt t :=
  ⟨fun h t G _ _ n f ψ G₀ hp => h G t n f ψ G₀ hp,
    fun h G _ _ t n f ψ G₀ hp => h t G n f ψ G₀ hp⟩

theorem ggOppositeRadicalCountNormalAt_of_rank_lt_two {t : StatedLieTag}
    (h : ∀ n f, (ggU t n f).D.rank < 2) : GGOppositeRadicalCountNormalAt t := by
  intro G _ _ n f ψ G₀ hp
  exact absurd hp.1.2 (not_le.mpr (h n f))

theorem ggOppositeRadicalCountNormalAt_POmegaOdd :
    GGOppositeRadicalCountNormalAt .POmegaOdd := by
  intro G _ _ n f ψ G₀ hp
  exact absurd rfl hp.1.1.2.2.2

theorem ggOppositeRadicalCountNormalAt_PSL : GGOppositeRadicalCountNormalAt .PSL := by
  intro G _ _ n f ψ G₀ hp Q hQne hQ
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hp
  subst hrange
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact (GGOppRad.ggOppRadGood_of_sl (ι := Fin (m + 1)) (K := GaloisField 2 f) ψ hker
    hQne hQ).countNormal hQ

theorem ggOppositeRadicalCountNormalInput_of_families
    (hPSU : GGOppositeRadicalCountNormalAt .PSU) (hPSp : GGOppositeRadicalCountNormalAt .PSp)
    (hPlus : GGOppositeRadicalCountNormalAt .POmegaPlus)
    (hMinus : GGOppositeRadicalCountNormalAt .POmegaMinus)
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) :
    GGOppositeRadicalCountNormalInput := by
  rw [ggOppositeRadicalCountNormalInput_iff]
  intro t
  cases t with
  | PSL => exact ggOppositeRadicalCountNormalAt_PSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggOppositeRadicalCountNormalAt_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | G2 => exact ggOppositeRadicalCountNormalAt_of_rank_lt_two fun _ _ => (Nat.zero_lt_two : 0 < 2)
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact h2E6
  | trialityD4 => exact ggOppositeRadicalCountNormalAt_of_rank_lt_two fun _ _ => (Nat.zero_lt_two : 0 < 2)
  | twistedB2 => exact ggOppositeRadicalCountNormalAt_of_rank_lt_two fun _ _ => (Nat.zero_lt_two : 0 < 2)
  | twistedG2 => exact ggOppositeRadicalCountNormalAt_of_rank_lt_two fun _ _ => (Nat.zero_lt_two : 0 < 2)
  | twistedF4 => exact ggOppositeRadicalCountNormalAt_of_rank_lt_two fun _ _ => (Nat.zero_lt_two : 0 < 2)
  | Tits => exact ggOppositeRadicalCountNormalAt_of_rank_lt_two fun _ _ => (Nat.zero_lt_two : 0 < 2)

@[expose] def GGOppositeRadicalUniversalAt (t : StatedLieTag) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    Finite (ggU t n f).K ∧
      (∀ z ∈ Subgroup.center (ggU t n f).K, z ^ 2 = 1 → z = 1) ∧
      ∀ Q : Subgroup (ggU t n f).K, Q ≠ ⊥ → GGRadicalTwo ⊤ Q → GGOppRadGood ⊤ Q

theorem ggOppositeRadicalCountNormalAt_of_universal {t : StatedLieTag}
    (h : GGOppositeRadicalUniversalAt t) : GGOppositeRadicalCountNormalAt t := by
  intro G _ _ n f ψ G₀ hp Q hQne hQ
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hp
  subst hrange
  obtain ⟨hfin, hinv, hgood⟩ := h n f hadm hrk
  exact (GGOppRad.GGOppRadGood.of_lift ψ hker (fun z hz h2 => hinv z (hker hz) h2)
    (fun Q' hQ'ne hQ' => hgood Q' hQ'ne hQ') hQne hQ).countNormal hQ

theorem ggOppositeRadicalUniversalAt_PSL : GGOppositeRadicalUniversalAt .PSL := by
  intro n f hadm _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hf : Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := inferInstance
  exact ⟨hf, fun z hz h2 => GGOppRad.eq_one_of_mem_center_of_sq_eq_one
      (ι := Fin (m + 1)) (K := GaloisField 2 f) hz h2,
    fun Q hQne hQ => GGOppRad.ggOppRadGood_sl (ι := Fin (m + 1)) (K := GaloisField 2 f) hQne hQ⟩

end Inputs

section Assembly

theorem ggTwoSignalizerGenInput_of_families
    (hPSU : GGOppositeRadicalCountNormalAt .PSU) (hPSp : GGOppositeRadicalCountNormalAt .PSp)
    (hPlus : GGOppositeRadicalCountNormalAt .POmegaPlus)
    (hMinus : GGOppositeRadicalCountNormalAt .POmegaMinus)
    (hF4 : GGOppositeRadicalCountNormalAt .F4) (hE6 : GGOppositeRadicalCountNormalAt .E6)
    (hE7 : GGOppositeRadicalCountNormalAt .E7) (hE8 : GGOppositeRadicalCountNormalAt .E8)
    (h2E6 : GGOppositeRadicalCountNormalAt .twistedE6) : GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_oppositeRadicalCountNormal
    (ggOppositeRadicalCountNormalInput_of_families hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 h2E6)

end Assembly

end CFSG.StandardType
