module

public import CFSG.Quasithin.Vol2.Ch5Statements
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

abbrev sec53M1 (L : Subgroup G) : Subgroup G := Subgroup.normalizer (L : Set G)

abbrev sec53M2 (H : Subgroup G) : Subgroup G := Subgroup.normalizer (oTwoUpper H : Set G)

abbrev sec53M12 (L H : Subgroup G) : Subgroup G := sec53M1 L ⊓ sec53M2 H

abbrev sec53S (T L : Subgroup G) : Subgroup G := T ⊓ L

abbrev sec53ZS (T L : Subgroup G) : Subgroup G := centerOf (sec53S T L)

@[expose] def IsSec53Param (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  2 ≤ f ∧ (t = .PSL ∧ m = 3 ∨ t = .PSp ∧ m = 2 ∨ t = .G2 ∧ m = 0 ∨ t = .trialityD4 ∧ m = 0 ∨
    t = .twistedF4 ∧ m = 0 ∨ t = .PSU ∧ m = 4 ∨ t = .PSU ∧ m = 5 ∧ f = 2)

@[expose] def Stmt5_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f → IsSec53Param t m f →
      LieModel G t m 2 f ∨
      (t = .PSL ∧ m = 3 ∧ ∀ z ∈ sec53ZS T L, orderOf z = 2 →
        ¬ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H)

@[expose] def Stmt5_3_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T .PSL 3 f → 2 ≤ f →
    (∀ z ∈ sec53ZS T L, orderOf z = 2 →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H) →
    ∀ z ∈ sec53ZS T L, orderOf z = 2 → Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H

@[expose] def Stmt5_3_Lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f → IsSec53Param t m f → LieModel G t m 2 f

theorem exists_involution_sec53ZS [Finite G] {T M L : Subgroup G} {n : ℕ}
    (h : Hyp5_0_1 G T M L n) : ∃ z ∈ sec53ZS T L, orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCoreOf 2 L ≠ ⊥ := by
    intro h0
    apply h.faithful.2.2.2
    have hc : Subgroup.closure {z | z ∈ pCoreOf 2 L ⊓ Subgroup.centralizer
        (pCoreOf 2 L : Set G) ∧ z ^ 2 = 1} = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro z ⟨hz, -⟩
      rw [h0] at hz
      exact (Subgroup.mem_bot.mp (Subgroup.mem_inf.mp hz).1)
    rw [quasithinV2, hc, Subgroup.commutator_bot_left]
  have hle : pCoreOf 2 L ≤ T := by
    have hS : CFSG.QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
      isSylowTwoOf_of_isSylowTwo h.sylow le_sup_right
    refine hS.le_of_normalizes ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact (sup_le Subgroup.le_normalizer (h.T_le.trans h.normal)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hne : sec53S T L ≠ ⊥ := by
    intro h1
    apply hO2
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ sec53S T L := Subgroup.mem_inf.mpr ⟨hle hx,
      CFSG.LieType.BorelTits.pCoreOf_le 2 L hx⟩
    rw [h1] at this
    exact this
  have hSp : IsPGroup 2 (sec53S T L) := h.sylow.1.to_le inf_le_left
  have hnt : Nontrivial (sec53S T L) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hc := hSp.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center (sec53S T L)) := hSp.to_subgroup _
  have h2 : 2 ∣ Nat.card (Subgroup.center (sec53S T L)) := by
    rcases hcp.card_eq_or_dvd with h | h
    · exact absurd (Nat.card_eq_one_iff_unique.mp h).1 (not_subsingleton_iff_nontrivial.mpr hc)
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((z : sec53S T L) : G), Subgroup.mem_inf.mpr ⟨(z : sec53S T L).2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz

theorem stmt5_3_Lie_of (h534 : Stmt5_3_4) (h537 : Stmt5_3_7) : Stmt5_3_Lie := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  rcases h534 G T M L V H B D L₂ n t m f hyp hty hpar with h | ⟨rfl, rfl, h2⟩
  · exact h
  · exfalso
    obtain ⟨z, hz, hz2⟩ := exists_involution_sec53ZS hyp.toHyp5_0_1
    exact h2 z hz hz2 (h537 G T M L V H B D L₂ n f hyp hty hpar.1 h2 z hz hz2)

end CFSG.Quasithin.H13
