module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticFourWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticTorusActions
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticSupport
public import CFSG.LocalAnalysis.StandardType.GGQTwoCyclicAutomizer
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix Polynomial CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot (permSp planeCoords planeOf)
open CFSG.StandardType.WitSpNs
open CFSG.LieType.Chevalley (WSL)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped commutatorElement

theorem four_dvd_zeroBlock_of_full_planeFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2)
    {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (t : ↥E) {i j : Fin n} (hij : i ≠ j) (hi : k i t = 1) (hj : k j t = 1) :
    4 ∣ Nat.card (ggAutomizer
      ⁅spSupported (t : StatedSp n K) {X - 1}, spSupported (t : StatedSp n K) {X - 1}⁆ E) := by
  classical
  let t₀ : StatedSp n K := A₀⁻¹ * t * A₀
  let I : Finset (Fin n) := {i, j}
  have hI : ∀ a ∈ I, M ^ (Multiplicative.toAdd (k a t)).val = 1 := by
    intro a ha
    rcases Finset.mem_insert.mp ha with h | h
    · subst a
      rw [hi]
      rfl
    · have h := Finset.mem_singleton.mp h
      subst a
      rw [hj]
      rfl
  have ht₀ : t₀ ∈ suppGroup (planeCoords I)ᶜ :=
    mem_suppGroup_compl_of_planeMat (hframe t) hI
  have hplanes : planeCoords I = coords i ∪ coords j := by
    ext a
    rcases a with a | a <;> simp [I, planeCoords, planeOf, coords, or_comm]
  let f : StatedSp 2 K →* StatedSp n K :=
    (MulAut.conj A₀).toMonoidHom.comp (pairEmbed K hij)
  have hrange : f.range ≤ spSupported (t : StatedSp n K) {X - 1} := by
    rintro a ⟨g, rfl⟩
    have hg : pairEmbed K hij g ∈ suppGroup (planeCoords I) := by
      rw [hplanes, ← range_pairEmbed hij]
      exact ⟨g, rfl⟩
    have h := conj_mem_fixedFactor_of_disjoint_support A₀ ht₀ hg
    have ht : A₀ * t₀ * A₀⁻¹ = (t : StatedSp n K) := by dsimp [t₀]; group
    change A₀ * pairEmbed K hij g * A₀⁻¹ ∈ spSupported (t : StatedSp n K) {X - 1}
    simpa only [ht, spFixedFactor] using h
  let R : StatedSp n K := f (twoPlaneRotation K)
  have hRJ : R ∈ ⁅spSupported (t : StatedSp n K) {X - 1},
      spSupported (t : StatedSp n K) {X - 1}⁆ := by
    have hm : (commutator (StatedSp 2 K)).map f ≤
        ⁅spSupported (t : StatedSp n K) {X - 1}, spSupported (t : StatedSp n K) {X - 1}⁆ := by
      rw [commutator, Subgroup.map_commutator, Subgroup.map_top]
      exact Subgroup.commutator_mono hrange hrange
    exact hm (Subgroup.mem_map.mpr ⟨twoPlaneRotation K, twoPlaneRotation_mem_commutator, rfl⟩)
  let π : Equiv.Perm (Fin n) := Equiv.swap i j
  let L₀ : StatedSp n K := A₀ * longBlock K n j WSL * A₀⁻¹
  let P₀ : StatedSp n K := A₀ * permSp K π * A₀⁻¹
  have hR : R = L₀ * P₀ := by
    change A₀ * pairEmbed K hij (twoPlaneRotation K) * A₀⁻¹ = L₀ * P₀
    rw [pairEmbed_twoPlaneRotation_eq_weyl]
    dsimp [L₀, P₀, π]
    group
  have hRN : R ∈ Subgroup.normalizer (E : Set (StatedSp n K)) := by
    rw [hR]
    exact Subgroup.mul_mem _
      (longBlock_mem_normalizer_of_full_frame hK hdet hM hframe hsurj j)
      (permSp_mem_normalizer_of_full_frame hframe hsurj π)
  have hR4 : R ^ 4 = 1 := by
    change f (twoPlaneRotation K) ^ 4 = 1
    rw [← map_pow, twoPlaneRotation_pow_four, map_one]
  have hact : ∀ g : ↥E, ∃ g' : ↥E,
      (∀ a, k a g' = if a = j then (k (π.symm a) g)⁻¹ else k (π.symm a) g) ∧
        R * g * R⁻¹ = g' := by
    intro g
    obtain ⟨gP, hgP, hPeq⟩ := exists_conj_permSp_of_full_frame hframe hsurj π g
    obtain ⟨gR, hgR, hLeq⟩ := exists_conj_longBlock_of_full_frame hK hdet hM hframe hsurj j gP
    refine ⟨gR, ?_, ?_⟩
    · intro a
      simpa only [hgP] using hgR a
    · have hP : P₀ * g * P₀⁻¹ = gP := hPeq
      have hL : L₀ * gP * L₀⁻¹ = gR := hLeq
      calc R * g * R⁻¹ = L₀ * (P₀ * g * P₀⁻¹) * L₀⁻¹ := by rw [hR]; group
        _ = L₀ * gP * L₀⁻¹ := by rw [hP]
        _ = gR := hL
  let α : Multiplicative (ZMod 3) := Multiplicative.ofAdd (1 : ZMod 3)
  obtain ⟨d, hd⟩ := hsurj (fun a => if a = i then α else 1)
  have hdi : k i d = α := by simpa using hd i
  obtain ⟨d₁, hd₁, hRd⟩ := hact d
  obtain ⟨d₂, hd₂, hRd₁⟩ := hact d₁
  have hπi : π.symm i = j := by simp [π]
  have hπj : π.symm j = i := by simp [π]
  have hd₂i : k i d₂ = α⁻¹ := by
    rw [hd₂ i, if_neg hij, hπi, hd₁ j, if_pos rfl, hπj, hdi]
  have hR2d : R ^ 2 * (d : StatedSp n K) * (R ^ 2)⁻¹ = d₂ := by
    calc R ^ 2 * (d : StatedSp n K) * (R ^ 2)⁻¹ = R * (R * d * R⁻¹) * R⁻¹ := by rw [pow_two]; group
      _ = R * d₁ * R⁻¹ := by rw [hRd]
      _ = d₂ := hRd₁
  have hmove : R ^ 2 * (d : StatedSp n K) * (R ^ 2)⁻¹ ≠ d := by
    intro h
    have hdd : d₂ = d := Subtype.ext (hR2d.symm.trans h)
    have hα : α⁻¹ = α := by rw [← hd₂i, hdd, hdi]
    exact (show α⁻¹ ≠ α by decide +kernel) hα
  exact QTwoCav.four_dvd_ggAutomizer_of_four_action hRJ hRN hR4 d.property hmove

end CFSG.StandardType.QTwoSymplecticCav

end
