module

public import CFSG.Timmesfeld.ARS.Sec13Connected

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀) (hcl : LeviClosed R A A₀)
include hS

theorem centGen_le_stabSet {B : Subgroup G} : centGen R A A₀ B ≤ stabSet (deltaSet R A A₀ B) :=
  gen_le fun _ hX => le_stabSet_deltaSet_of_commuting hS.hyp.root hX.1 hX.2

theorem centGen_ne_levi {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    centGen R A A₀ B ≠ levi R A A₀ := by
  intro he
  obtain ⟨X, hX, hXB⟩ := exists_mem_leviSet_not_commuting hS.hyp hS.mem hS.sec8.2 hS.opp hB
  refine hXB (hS.commuting_of_forall_conjSet_eq hB hX fun x hx => ?_).symm
  exact mem_stabSet.1 (hS.centGen_le_stabSet (he ▸ le_gen hX hx))

include hcl in
theorem isSigmaMaximal_centGen {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    IsSigmaSubgroup (leviSet R A A₀) (centGen R A A₀ B) ∧ centGen R A A₀ B ≠ levi R A A₀ ∧
      ∀ K, IsSigmaSubgroup (leviSet R A A₀) K → centGen R A A₀ B ≤ K →
        K = centGen R A A₀ B ∨ K = levi R A A₀ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  refine ⟨⟨_, fun _ hX => hX.1, rfl⟩, hS.centGen_ne_levi hB, fun K ⟨S, hSΔ, hKS⟩ hHK => ?_⟩
  by_cases hKV : K = levi R A A₀
  · exact Or.inr hKV
  left
  set Ψ := {X | X ∈ leviSet R A A₀ ∧ X ≤ K} with hΨdef
  have hKΨ : K = gen Ψ := le_antisymm (hKS ▸ gen_mono fun X hX => ⟨hSΔ hX, hKS ▸ le_gen hX⟩)
    (gen_le fun _ hX => hX.2)
  have hKV' : K ≤ levi R A A₀ := hKΨ ▸ gen_mono fun _ hX => hX.1
  have hΨR : Ψ ⊆ R := fun _ hX => hX.1.1.1
  have hnorm : ∀ g ∈ (⨆ B ∈ Ψ, B), ∀ X ∈ Ψ, conjSub X g ∈ Ψ := by
    intro g hg X hX
    have hgK : g ∈ K := hKΨ ▸ hg
    exact ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 (hKV' hgK), conjSub_le hX.2 hgK⟩
  have hgenK : (⨆ B ∈ Ψ, B) = K := hKΨ.symm
  have hΔΨ : ∀ E ∈ deltaSet R A A₀ B, E ∈ Ψ := fun E hE =>
    ⟨hE.1, (le_gen (show E ∈ {X | X ∈ leviSet R A A₀ ∧ Commuting X B} from
      ⟨hE.1, (hE.2.1.2.2).symm⟩)).trans hHK⟩
  have hΔΩ : ∀ E ∈ deltaSet R A A₀ B, E ∈ isolatedIn Ψ := by
    refine fun E hE => ⟨hΔΨ E hE, fun F hF hEF => hKV ?_⟩
    refine le_antisymm hKV' ?_
    rw [← hS.gen_inter_lambdaSet_sup_eq_levi hE.1 hF.1 hEF]
    refine sup_le (gen_le fun X hX => ?_) hF.2
    exact (le_gen (show X ∈ {X | X ∈ leviSet R A A₀ ∧ Commuting X B} from
      ⟨hX.1, commuting_of_mem_deltaSet_of_mem_lambdaSet hS.hyp hS.mem hS.opp hB hE hX.1
        hX.2⟩)).trans hHK
  set N := ⨆ X ∈ isolatedIn Ψ, X with hNdef
  have hN2 : IsPGroup 2 N := Sec3.isPGroup_iSup_isolatedIn hR hΨR hnorm
  have hΩN : ∀ X ∈ isolatedIn Ψ, X ≤ N := fun X hX =>
    le_iSup₂ (f := fun X (_ : X ∈ isolatedIn Ψ) => X) X hX
  have hNK : ∀ g ∈ K, conjSub N g = N := by
    intro g hg
    have hg' : g ∈ ⨆ B ∈ Ψ, B := hgenK ▸ hg
    have hle : ∀ h ∈ ⨆ B ∈ Ψ, B, conjSub N h ≤ N := by
      intro h hh
      rw [hNdef, conjSub, Subgroup.map_iSup]
      refine iSup_le fun X => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hX => hΩN _ (Sec3.conjSub_mem_isolatedIn hnorm hX hh)
    exact Singular.conjSub_eq_of_le hS.hyp (hle g hg')
  have hΨN : ∀ W ∈ Ψ, W ≤ N → W ∈ isolatedIn Ψ := by
    refine fun W hW hWN => ⟨hW, fun W' hW' hWW' => ?_⟩
    obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hW'.1.1.1
    have hop : Opposite W (conjSub W w) := Sec5.opposite_conjSub_self hWW' hw hw1
    have hWw : conjSub W w ≤ N := by
      rw [← hNK w (hW'.2 hw)]
      exact Subgroup.map_mono hWN
    exact Sec3.not_opposite_of_isPGroup_sup hR hW.1.1.1 (hR.conjSub_mem hW.1.1.1 w)
      (hN2.to_le (sup_le hWN hWw)) hop
  obtain ⟨Y₀, hY₀⟩ := deltaSet_nonempty hS.hyp hS.mem hS.sec8.2 hS.opp hB
  obtain ⟨Z, hZ, hZN⟩ := QD.exists_forall_not_le_commutator hN2 hΩN
    (fun X hX => hR.ne_bot X hX.1.1.1.1) (hΔΩ Y₀ hY₀)
  have hZc : ∀ Y ∈ isolatedIn Ψ, Commuting Z Y := by
    intro Y hY
    by_contra hZY
    have hZY' : Z ≠ Y := fun e => hZY (e ▸ hR.commuting_self hZ.1.1.1.1)
    rcases hR.rel _ hZ.1.1.1.1 _ hY.1.1.1.1 hZY' with h1 | h1 | h1
    · exact hZY h1
    · exact hZ.2 Y hY.1 h1
    · have hCΨ : ⁅Z, Y⁆ ∈ Ψ :=
        ⟨Levi.commutator_mem_leviSet hR hS.mem hS.opp hZ.1.1 hY.1.1 h1,
          QD.commutator_le_of_le hZ.1.2 hY.1.2⟩
      have hCN : ⁅Z, Y⁆ ≤ N := QD.commutator_le_of_le (hΩN Z hZ) (hΩN Y hY)
      exact hZN _ (hΨN _ hCΨ hCN) (Subgroup.commutator_mono le_rfl (hΩN Y hY))
  set Zs := {X | X ∈ isolatedIn Ψ ∧ ∀ Y ∈ isolatedIn Ψ, Commuting X Y} with hZsdef
  have hZsΔ : Zs ⊆ deltaSet R A A₀ B := by
    intro X hX
    rw [← hS.setOf_forall_commuting_eq hB]
    exact ⟨hX.1.1.1, fun Y hY => hX.2 Y (hΔΩ Y hY)⟩
  have hZsK : ∀ X ∈ Zs, ∀ g ∈ K, conjSub X g ∈ Zs := by
    intro X hX g hg
    have hg' : g ∈ ⨆ B ∈ Ψ, B := hgenK ▸ hg
    refine ⟨Sec3.conjSub_mem_isolatedIn hnorm hX.1 hg', fun Y hY => ?_⟩
    have hY' := Sec3.conjSub_mem_isolatedIn hnorm hY (Subgroup.inv_mem _ hg')
    have h1 := (hX.2 _ hY').conjSub g
    rwa [Plane.conjSub_inv_conjSub] at h1
  have hΔZs : deltaSet R A A₀ B ⊆ Zs := by
    intro Y hY
    obtain ⟨g, hg, rfl⟩ := hS.exists_mem_gen_conjSub_eq hcl hB (hZsΔ ⟨hZ, hZc⟩) hY
    exact hZsK Z ⟨hZ, hZc⟩ g (hHK hg)
  refine le_antisymm ?_ hHK
  rw [hKΨ]
  refine gen_le fun X hX => le_gen ⟨hX.1, hS.commuting_of_forall_conjSet_eq hB hX.1
    fun x hx => ?_⟩
  have hxK : x ∈ K := hX.2 hx
  have heq : Zs = deltaSet R A A₀ B := Set.Subset.antisymm hZsΔ hΔZs
  ext Y
  rw [mem_conjSet, ← heq]
  constructor
  · intro hY
    have := hZsK _ hY x hxK
    rwa [Plane.conjSub_inv_conjSub] at this
  · intro hY
    exact hZsK Y hY x⁻¹ (Subgroup.inv_mem _ hxK)

end Sec13

end CFSG.Timmesfeld.ARS
