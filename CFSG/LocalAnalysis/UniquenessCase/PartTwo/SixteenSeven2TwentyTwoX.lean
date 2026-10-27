module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyIrrThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoXConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoXFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two_x (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)}
    (hΔ : Concl1617 D ⊥ V hV L A g Δ) (hS : Case168_2Small D ⊥ V hV L) :
    ∀ J ∈ deltaConj Δ g, ∃ x : G, conjSubgroup J x ∈ deltaConj Δ g ∧ conjSubgroup J x ≠ J ∧
      ∀ u ∈ V ⊓ conjSubgroup D.M g, (∀ J' ∈ deltaConj Δ g, conjSubgroup J' u = J') →
        conjSubgroup (J ⊓ centralizer ({u} : Set G)) x =
          conjSubgroup J x ⊓ centralizer ({u} : Set G) := by
  obtain ⟨F, π, hFinj, hrange, hact, hcomm, htrans⟩ := s16c167_irr_three D hC hS
  have hM : D.M ≤ normalizer (V : Set G) := hC.setting.hyp16.hyp125.normalizer_eq.ge
  have hmem : ∀ i, F i ∈ irrSet (barSub ⊥ V hV L) := fun i => by
    have h : F i ∈ irrBar L ⊥ V hV := by rw [hrange]; exact Set.mem_range_self i
    exact h
  have hFne : ∀ i, F i ≠ ⊥ := by
    intro i hi
    have hlt := (hmem i).2.1
    simp [hi] at hlt
  have hΔF : ∀ J ∈ Δ, ∃ i, imgTil ⊥ V hV J = F i := by
    intro J hJ
    have h : imgTil ⊥ V hV J ∈ irrBar L ⊥ V hV := hΔ.2.2.2.2.1 hS.case168_2 J hJ
    rw [hrange] at h
    exact h.imp fun i hi => hi.symm
  obtain ⟨⟨j₁, j₂, hj, hinf, hsup⟩, hΔI⟩ :=
    s16c167_twenty_two_delta hV hΔ.1 hΔ.2.1 hΔ.2.2.1 hΔ.2.2.2.1 hΔF
  have hpair := s16c167_twenty_two_pairs hact
    (fun i j => (htrans i j).imp fun y hy => hy.2) hj hinf hsup
  obtain ⟨-, -, hIconj⟩ := s16c167_twenty_two_family hV hM hact hFne hpair
  have hinj : Function.Injective (fun i => preTil ⊥ V hV (F i)) := fun i j h =>
    hFinj (by simpa only [imgTil_preTil] using congrArg (imgTil ⊥ V hV) h)
  intro J hJ
  obtain ⟨I, hI, rfl⟩ := hJ
  obtain ⟨I', hI', hne⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hΔ.1]; norm_num) I
  obtain ⟨i, rfl⟩ := hΔI I hI
  obtain ⟨i', rfl⟩ := hΔI I' hI'
  have hii' : i ≠ i' := fun h => hne (by rw [h])
  obtain ⟨r, hri, hr⟩ := s16c167_twenty_two_transitive hV hM hcomm htrans i i'
  have hIr : conjSubgroup (preTil ⊥ V hV (F i)) (r : G)⁻¹ = preTil ⊥ V hV (F i') := by
    rw [hIconj r i, hri]
  have hshift := s16c167_twenty_two_x_shift (preTil ⊥ V hV (F i)) g r
  refine ⟨g⁻¹ * (r : G)⁻¹ * g, ?_, ?_, ?_⟩
  · rw [hshift, hIr]
    exact ⟨_, hI', rfl⟩
  · rw [hshift, hIr]
    intro h
    have h' := congrArg (fun C => conjSubgroup C g⁻¹) h
    simp only [E3.conjSubgroup_conj_inv] at h'
    exact hne h'
  · intro u hu hfix
    obtain ⟨huV, huM⟩ := Subgroup.mem_inf.1 hu
    have huM' : g * u * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 huM
    obtain ⟨m, hmu, hm2, hρm⟩ := s16c167_twenty_two_x_triv
      (ρ := π.comp (s16c167_barHom hV hM)) hinj hIconj hii' (hV.2 u huV) huM'
      (hfix _ ⟨_, hI, rfl⟩) (hfix _ ⟨_, hI', rfl⟩)
    refine s16c167_twenty_two_x_transport (preTil_le ⊥ V hV (F i)) fun v hv => ?_
    have h := hr m hm2 hρm v hv
    rwa [hmu] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
