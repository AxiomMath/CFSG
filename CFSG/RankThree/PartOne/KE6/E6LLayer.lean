module

public import CFSG.RankThree.PartOne.KE6.E6LStdComm
public import CFSG.RankThree.PartOne.KE6.E8T3E6
public import CFSG.RankThree.PartOne.KD4L.Layer
public import CFSG.RankThree.PartOne.KE6.E6LNormal

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

open scoped Matrix MatrixGroups

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem exists_torus_split6 [E6Sub τ] [IsAlgClosed L] {t : ModGL τ L} (ht : t ∈ torusGroup τ L) :
    ∃ t' T : ModGL τ L, t' ∈ torusGroup τ L ∧ T ∈ subsystemGroup τ L (e6Set τ) ∧ t = t' * T ∧
      ∀ g ∈ subsystemGroup τ L (e6Set τ), t' * g = g * t' := by
  exact KD4L.exists_torus_split_of_word e6Idx (fun _ hi => exists_e6Id_eq hi) (fun s => by
    obtain ⟨T, hTs, hT⟩ := exists_e6TorusWord_scalars (τ := τ) (L := L) s
    exact ⟨T, supportedTorus_le_subsystemGroup _ hTs, supportedTorus_le_torusGroup _ hTs, hT⟩) ht

end Torus

section Assembly

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem layer_of_standard6 (hf : 1 ≤ f) {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hstd : StdTwist6 n₁ π) {h n : ModGL τ L} (hh : h ∈ subsystemGroup τ L (e6Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (e6Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ subsystemGroup τ L (e6Set τ), (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (subsystemGroup τ L (e6Set τ) : Set (ModGL τ L))) ∧
      ∀ m : Fin τ.rank, m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈
            P := by
  exact KD4L.layer_of_split (J := e6Set τ) (m₀ := e6Idx 3) rfl (U := stdLayer τ ℓ f n₁)
    (fun _ => mem_stdLayer) (fun _ ht => exists_torus_split6 ht) (hstd.finite_quasisimple hf)
    (fun _ hq' hc' => hstd.commute_of_commute hf hq' hc')
    (fun _ _ _ hk Y => hstd.middle_SL2 (ℓ := ℓ) (f := f) hk Y) hh hlang hP

theorem e6Nodes_eq_e6Set (τ : Tag) : e6Nodes τ = e6Set τ := by
  ext i
  change i.val ≤ 5 ↔ i.val < Tag.E6.rank
  have : Tag.E6.rank = 6 := rfl
  omega

end Assembly

theorem e6Layer (τ : Tag) [M27Ok τ] [E6Sub τ] : E6Layer τ := by
  intro L _ _ ℓ f _ _ hf ε hε n hn hnC hmaps hrel P hP
  have hw : MapsJ τ (e6Set τ) (weylQuotientHom τ L ⟨n, hn⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ, hact⟩ := exists_action hw
  have hπJ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπJ hπJ' hu hact
  have hstd : StdTwist6 n₁ π := ⟨hπ, hgen⟩
  have hP' : P = subsystemGroup τ L (e6Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hP, subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  obtain ⟨h1, h2, h3, h4⟩ := layer_of_standard6 hf hstd hh hlang hP'
  refine ⟨h1, h2, ?_, fun m hm k _ _ _ hk => h4 m hm k hk⟩
  intro y hy hc
  rw [e6Nodes_eq_e6Set, ← subsystemGroup_eq_rootSpan] at hy ⊢
  exact h3 y hy hc

theorem e6Layer_E8 : E6Layer Tag.E8 := e6Layer Tag.E8

end CFSG.RankThree.PartOne.KE6
