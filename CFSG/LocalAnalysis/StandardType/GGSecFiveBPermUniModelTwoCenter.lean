module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootModel
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag


theorem exists_unitary_model_of_uniLabel_of_twoCenter {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n f : ℕ} (hn : 4 ≤ n)
    (hz : f = 1 → Line63.H5.twoCenter L = ⊥)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = f) p Bs L) :
    p ∣ 2 ^ f + 1 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (φ : ↥(unitarySU 2 f F n) →* L),
      Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin n → F, LineU.ActsDiagU φ a t := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hmark : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => GGSecFiveBPermUniLabel (r + 1) p lab ∧ lab.n = f) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨lab, hlab, hhas, R, hGR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨hUni, hm⟩ := hP
  obtain ⟨tag, rank, m⟩ := lab
  have hUni' : tag = .twA ∧ rank = (r + 1) - 1 ∧ p ∣ 2 ^ m + 1 := hUni
  obtain ⟨htag, hrank, hpq⟩ := hUni'
  have hm' : m = f := hm
  subst tag
  have hrankr : rank = r := by omega
  subst rank
  subst m
  exact ⟨hpq, exists_unitary_model_of_twA_label hR (by omega) hpq hhas hz⟩

end CFSG.StandardType

end
