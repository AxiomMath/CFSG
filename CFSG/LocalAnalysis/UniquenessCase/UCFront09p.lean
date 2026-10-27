module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09f
import CFSG.LocalAnalysis.UniquenessCase.UCFront09i
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
import CFSG.LocalAnalysis.UniquenessCase.UCFront09o
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UC22P22p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_eq_bot_of_mem_calNOf (D : Data G) {X H : Subgroup G} (hUX : UniqueMax D.M X)
    (hH : H ∈ calNOf X) (hHM : H ≠ D.M) : pCoreOf 2 H = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := D.standing.simple
  by_contra hO
  have hHN : H = normalizer (pCoreOf 2 H : Set G) := by
    rcases eq_or_lt_of_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) with h | h
    · exact h
    · rcases (normalizer_eq_top_iff.1 (hH.1.2 _ h)).eq_bot_or_eq_top with h1 | h1
      · exact absurd h1 hO
      · exact absurd (top_le_iff.1 (h1.symm.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)))
          hH.1.1
  rcases eq_or_lt_of_le (uc22p22p_le_of_uniqueMax hUX
      ⟨pCoreOf 2 H, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, hHN⟩ hH.2) with h | h
  · exact hHM h
  · exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
      (hH.1.2 _ h)

theorem exists_mem_invStar9 (K X : Subgroup G) (p : ℕ) : ∃ R : Subgroup G, R ∈ InvStar9 K X p := by
  obtain ⟨R, -, hR⟩ := Finite.exists_le_maximal (p := (· ∈ Inv9 K X p))
    (show (⊥ : Subgroup G) ∈ Inv9 K X p from ⟨bot_le, IsPGroup.of_bot, le_normalizer_of_normal⟩)
  exact ⟨R, hR⟩

theorem isSylowOf_of_mem_invStar9 (D : Data G) {L X H R : Subgroup G} (hLM : L ≤ D.M)
    (hLN : D.M ≤ normalizer (L : Set G)) (hA5 : IsAlt (Bar2 L) 5) (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L)
    (hZ : ⁅pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ⊓ X, X⁆ ≠ ⊥)
    (hUX : UniqueMax D.M X) (hXH : X ≤ H) (hR : R ∈ InvStar9 (I9 H ⊔ X) X 2) :
    R ≠ ⊥ ∧ normalizer (R : Set G) ≤ D.M ∧ IsSylowOf 2 R (I9 H ⊔ R) ∧
      IsSylowOf 2 (R ⊓ I9 H) (I9 H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := I9 H with hIdef
  obtain ⟨hRIX, hR2, hXR⟩ := hR.1
  have hXM : X ≤ D.M := hXL.trans hLM
  have hHI : H ≤ normalizer (I : Set G) := le_normalizer_I9 H
  have hRH : R ≤ H := hRIX.trans (sup_le (map_subtype_le _) hXH)
  have hRI : R ≤ normalizer (I : Set G) := hRH.trans hHI
  have hR1 : R ≠ ⊥ := by
    rintro rfl
    exact zO2_ne_bot hZ (le_bot_iff.1 (hR.2 ⟨inf_le_right.trans le_sup_right,
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le (inf_le_left.trans inf_le_left),
      le_normalizer_zO2 hXM⟩ bot_le))
  have hNR : normalizer (R : Set G) ≤ D.M := uc22p22p_le_of_uniqueMax hUX ⟨R, hR1, hR2, rfl⟩ hXR
  set A := I ⊓ normalizer (R : Set G) with hAdef
  have hXA : X ≤ normalizer (A : Set G) :=
    (le_inf (hXH.trans hHI) (hXR.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hRA : R ≤ normalizer (A : Set G) :=
    (le_inf hRI (le_normalizer.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hAX : ⁅A, X⁆ ≤ R := (commutator_le_pCoreOf_of_mem_inv9' hLN hXL hcov hA5
    ⟨inf_le_right.trans hNR, fun h => not_dvd_card_I9 H (h.trans (card_dvd_of_le inf_le_left)),
      hXA⟩).trans (le_of_mem_invStar9 hR
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans (inf_le_left.trans le_sup_left))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
      (hXA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A))
      (hRA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)))
  have hRK : IsSylowOf 2 R ((I ⊔ R) ⊓ normalizer (R : Set G)) := by
    obtain ⟨U, hU, hRU⟩ : ∃ U : Subgroup G,
        IsSylowOf 2 U ((I ⊔ R) ⊓ normalizer (R : Set G)) ∧ R ≤ U := by
      obtain ⟨Q, hQ⟩ :=
        (hR2.comap_subtype (K := (I ⊔ R) ⊓ normalizer (R : Set G))).exists_le_sylow
      exact ⟨_, ⟨Q, rfl⟩, fun r hr => ⟨⟨r, le_inf le_sup_right le_normalizer hr⟩, hQ hr, rfl⟩⟩
    have hXU : X ≤ normalizer (U : Set G) := le_normalizer_iff.2 fun x hx u hu => by
      obtain ⟨huIR, huN⟩ := mem_inf.1 (hU.le hu)
      rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left I R hRI] at huIR
      obtain ⟨a, ha, r, hr, rfl⟩ := Set.mem_mul.1 huIR
      have haN : a ∈ normalizer (R : Set G) := by
        simpa using (normalizer _).mul_mem huN ((normalizer _).inv_mem (le_normalizer hr))
      have haU : a ∈ U := by simpa using U.mul_mem hu (U.inv_mem (hRU hr))
      have hc : x * a * x⁻¹ * a⁻¹ ∈ R := by
        simpa [commutatorElement_def, mul_assoc] using
          R.inv_mem (hAX (commutator_mem_commutator (mem_inf.2 ⟨ha, haN⟩) hx))
      have hxr : x * r * x⁻¹ ∈ R := (mem_normalizer_iff.1 (hXR hx) r).1 hr
      rw [show x * (a * r) * x⁻¹ = x * a * x⁻¹ * a⁻¹ * a * (x * r * x⁻¹) by group]
      exact U.mul_mem (U.mul_mem (hRU hc) haU) (hRU hxr)
    have hUR := hR.2 ⟨hU.le.trans (inf_le_left.trans (sup_le le_sup_left hRIX)), hU.isPGroup,
      hXU⟩ hRU
    rwa [le_antisymm hUR hRU] at hU
  have hRIR : IsSylowOf 2 R (I ⊔ R) := isSylowOf_of_inf_normalizer_le le_sup_right le_rfl hRK
  exact ⟨hR1, hNR, hRIR, hRIR.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hRI)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
