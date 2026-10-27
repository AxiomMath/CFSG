module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.SmithB42HatA6Model
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitHatA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem isHat_of_tripleA6Six {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} (h : TripleA6Six H U Z) :
    IsHat ↥H (alternatingGroup (Fin 6)) := by
  obtain ⟨_, _, _, Γ₀, _, _, hHat, _, hReal⟩ := h
  obtain ⟨π, hπ⟩ := hReal
  exact IsHat.of_mulEquiv (FFC.equivOfRealizes (FFModel.nat_faithful Γ₀) hπ) hHat

theorem bijective_of_surjective_isHat_a6_of_quasisimple_odd_center
    {C H : Type} [Group C] [Finite C] [Group H] [Finite H]
    (hC : CFSG.Open.IsQuasisimple C) (hodd : Odd (Nat.card (Subgroup.center C)))
    (hH : IsHat H (alternatingGroup (Fin 6)))
    (f : C →* H) (hf : Function.Surjective f) :
    Function.Bijective f := by
  haveI hperfC : Group.IsPerfect C := ⟨hC.1⟩
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hH.1.2.1
  haveI hHnt : Nontrivial H := (QuotientGroup.mk'_surjective (Subgroup.center H)).nontrivial
  have hker_ne_top : f.ker ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton H := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      have hx : f x = 1 := by
        have hmem : x ∈ f.ker := by rw [htop]; exact Subgroup.mem_top x
        simpa using hmem
      have hy : f y = 1 := by
        have hmem : y ∈ f.ker := by rw [htop]; exact Subgroup.mem_top y
        simpa using hmem
      rw [hx, hy]⟩
    exact not_subsingleton H hsub
  have hker : f.ker ≤ Subgroup.center C :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hC f.ker hker_ne_top
  let eC : C ⧸ Subgroup.center C ≃* H ⧸ Subgroup.center H :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hf hker
  obtain ⟨eA⟩ := hH.2.2
  have hCalt : UC22.IsAlt (C ⧸ Subgroup.center C) 6 := ⟨eC.trans eA⟩
  have hH1080 : Nat.card H = 1080 :=
    (CFSG.Quasithin.HatA6.quasisimple_card hH.1.1 hH.2.1 eA).2
  rcases s15k_schur_alt_six hC hodd hCalt with hA6 | hA6Z3
  ·
    obtain ⟨e⟩ := hA6
    have hc360 : Nat.card C = 360 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.Orbit.card_alt6_eq]
    have hle := Nat.card_le_card_of_surjective f hf
    omega
  ·
    obtain ⟨-, hZ3, hAlt⟩ := hA6Z3
    obtain ⟨e6⟩ := hAlt
    have hc1080 : Nat.card C = 1080 :=
      (CFSG.Quasithin.HatA6.quasisimple_card ⟨hC.1⟩ hZ3 e6).2
    exact Function.Surjective.bijective_of_nat_card_le hf (by rw [hc1080, hH1080])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
