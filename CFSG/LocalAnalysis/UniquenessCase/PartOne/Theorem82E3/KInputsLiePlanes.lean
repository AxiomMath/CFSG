module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalCoords
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalK7Dvd
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalWeightTwo
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open CFSG.LinearAlgebra CFSG.ClassicalGroups.Symplectic Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

private theorem planes_pRank_eq_of_zero_coord {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    {c : Multiplicative (Fin 3 → ZMod 3) →* Y} (hc : IsSignedCoords A c) {p : ℕ} (hp : 1 < p)
    {v : Fin 3 → ZMod 3} (hv : v ≠ 0) (hv0 : ∃ i, v i = 0) :
    CFSG.Open.pRank p (centralizer ({c (.ofAdd v)} : Set Y)) =
        CFSG.Open.pRank p (centralizer ({c (.ofAdd ![1, 0, 0])} : Set Y)) ∨
      CFSG.Open.pRank p (centralizer ({c (.ofAdd v)} : Set Y)) =
        CFSG.Open.pRank p (centralizer ({c (.ofAdd ![1, 1, 0])} : Set Y)) := by
  obtain ⟨σ, ε, hε, hshape⟩ := exists_signedPerm_eq_point v hv
  obtain ⟨n, hn⟩ := hc.2.2.2 σ ε hε
  have key : ∀ w : Fin 3 → ZMod 3, (∀ i, v i = ε i * w (σ i)) →
      CFSG.Open.pRank p (centralizer ({c (.ofAdd v)} : Set Y)) =
        CFSG.Open.pRank p (centralizer ({c (.ofAdd w)} : Set Y)) := by
    intro w hw
    have h1 := hn (Multiplicative.ofAdd w)
    have h2 : (Multiplicative.ofAdd fun i => ε i *
        Multiplicative.toAdd (Multiplicative.ofAdd w) (σ i)) = Multiplicative.ofAdd v := by
      apply Multiplicative.toAdd.injective
      funext i
      simp [hw i]
    rw [h2] at h1
    rw [Coords.centralizer_singleton_eq_map_conj h1.symm, Coords.pRank_map_conj hp]
  rcases hshape with h | h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (key _ h)
  · exfalso
    obtain ⟨i, hi⟩ := hv0
    have h3 := h i
    have h1 : (![1, 1, 1] : Fin 3 → ZMod 3) (σ i) = 1 := by
      generalize σ i = j
      fin_cases j <;> rfl
    rw [hi, h1, mul_one] at h3
    exact hε i h3.symm

theorem k7Sp6Planes_holds :
    K7Sp6Planes := by
  intro Y _ _ f h p hp hp5 hpq A _ _ c hc
  have hq2 : 2 ^ f ≠ 2 := by
    intro h2
    rw [qPlusPi, h2] at hpq
    norm_num at hpq
    exact hp.ne_one hpq
  have hZ : center Y = ⊥ := center_eq_bot_of_isLie811_of_ne h (by decide) (fun _ => hq2)
  obtain ⟨-, -, -, -, hm⟩ := h
  obtain ⟨K, _, _, _, hK, hK3, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psp (by decide) hm
  have hs := isCubeRootBlock_cubeRootBlockStd
    (ModelUnpack.three_ne_zero_of_charP (K := K) Nat.prime_two (by decide))
  have := Fact.mk hp
  have hN3 := ModelUnpack.not_dvd_card_scalars_statedSp (n := 3) (K := K) (by norm_num)
    Nat.prime_three (by norm_num)
  have hNp := ModelUnpack.not_dvd_card_scalars_statedSp (n := 3) (K := K) (by norm_num) hp
    (by omega)
  have hZ3 : ¬ 3 ∣ Nat.card (center Y) := by rw [hZ, Subgroup.card_bot]; norm_num
  have hZp : ¬ p ∣ Nat.card (center Y) := by rw [hZ, Subgroup.card_bot]; exact hp.not_dvd_one
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by
    rw [hK]
    exact Sp6ThreeLocal.dvd_sq_sub_one_of_dvd_qPlusPi hpq
  have hrank := ModelTransport.pRank_centralizer_image_eq_of_model
    (Sp6ThreeLocal.c₀_signedCoords hs) hN3
    (GroupTheory.WeirSylow.uniqueElemSylow_statedProj_statedSp_three K hK3) hZ3 hNp hZp e hc
  have hpt : ∀ w, 2 ≤ CFSG.Open.pRank p
      (centralizer ({Sp6ThreeLocal.c₀ hs w} : Set (StatedSp 3 K))) →
      2 ≤ CFSG.Open.pRank p (centralizer ({c w} : Set Y)) := by
    intro w hw
    have h1 := hrank {w}
    rw [Set.image_singleton, Set.image_singleton] at h1
    rw [h1]
    exact hw
  refine ⟨?_, fun v hv hv0 => ?_⟩
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    have h1 := hrank {Multiplicative.ofAdd ![1, 0, 0], Multiplicative.ofAdd ![0, 1, 0]}
    rw [Set.image_pair, Set.image_pair] at h1
    rw [h1]
    exact Sp6ThreeLocal.one_le_pRank_centralizer_c₀_planeA_of_dvd hs hp hpK
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    rcases planes_pRank_eq_of_zero_coord hc hp.one_lt hv hv0 with h1 | h1 <;> rw [h1]
    · exact hpt _ (Sp6ThreeLocal.two_le_pRank_centralizer_c₀_weight_one_of_dvd hs hp hpK)
    · exact hpt _ (Sp6ThreeLocal.two_le_pRank_centralizer_c₀_weight_two_of_charTwo hs hp hpK)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
