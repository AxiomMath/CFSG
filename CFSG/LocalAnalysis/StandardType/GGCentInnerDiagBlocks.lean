module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsOrthAux.Comp

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggE0Concl_sup {G : Type} [Group G] {A B C₀ : Subgroup G} (hA : GGE0Concl A C₀)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hB : B ≤ Subgroup.centralizer (C₀ : Set G)) :
    GGE0Concl (A ⊔ B) C₀ := by
  have hAB := Subgroup.coe_mul_of_right_le_normalizer_left A B hBA
  refine ⟨sup_le hA.1 (hB.trans (Subgroup.centralizer_le_normalizer (C₀ : Set G))), ?_⟩
  intro hm
  refine largeEvenMarking_mono (P' := fun lab R _ I _ θ => GGChevStTag lab ∧
    ∀ ε ∈ (A ⊔ B : Subgroup G), ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥C₀ => (l' : G) = ε⁻¹ * l * ε) φ) ?_ (hA.2 hm)
  rintro lab R _ I F θ ⟨htag, hAind⟩
  refine ⟨htag, fun ε hε => ?_⟩
  change ε ∈ (↑(A ⊔ B) : Set G) at hε
  rw [hAB] at hε
  obtain ⟨a, ha, h, hh, rfl⟩ := hε
  obtain ⟨φ, hφI, hφ⟩ := hAind a ha
  refine ⟨φ, hφI, fun l l' hl => hφ l l' ?_⟩
  have hx : a⁻¹ * (l : G) * a ∈ C₀ :=
    (Subgroup.mem_set_normalizer_iff''.mp (hA.1 ha) (l : G)).mp l.2
  have hcomm : (a⁻¹ * (l : G) * a) * h = h * (a⁻¹ * (l : G) * a) :=
    (Subgroup.mem_centralizer_iff.mp (hB hh)) _ hx
  calc (l' : G) = (a * h)⁻¹ * (l : G) * (a * h) := hl
    _ = h⁻¹ * (a⁻¹ * (l : G) * a) * h := by rw [mul_inv_rev]; group
    _ = a⁻¹ * (l : G) * a := by
        rw [mul_assoc, hcomm]
        exact inv_mul_cancel_left h _

theorem exists_isComponentOf_block {G ι : Type} [Group G] [Finite G] (P : Finset ι)
    (Gb : ι → Subgroup G)
    (hc : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ x ∈ Gb i, ∀ y ∈ Gb j, Commute x y)
    {C₀ : Subgroup G} (hC₀ : IsComponentOf C₀ (⨆ i ∈ P, Gb i)) :
    ∃ i ∈ P, IsComponentOf C₀ (Gb i) := by
  classical
  let M : Subgroup G := ⨆ i ∈ P, Gb i
  let B : ↥P → Subgroup G := fun i => Gb i.1
  have hBM : ∀ i : ↥P, B i ≤ M := fun i =>
    le_iSup₂ (f := fun (i : ι) (_ : i ∈ P) => Gb i) i.1 i.2
  have hn : ∀ i : ↥P, ((B i).subgroupOf M).Normal := by
    intro i
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hBM i)]
    refine iSup₂_le fun j hj => ?_
    by_cases hji : j = i.1
    · subst hji
      exact Subgroup.le_normalizer
    · have hcent : Gb j ≤ Subgroup.centralizer (Gb i.1 : Set G) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (hc i.1 i.2 j hj (Ne.symm hji) x hx y hy).eq
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hsup : (⨆ i : ↥P, B i) = M :=
    (iSup_subtype' (f := fun (i : ι) (_ : i ∈ P) => Gb i)).symm
  have hL : CFSG.IsComponent (C₀.subgroupOf M) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hC₀.1).1 hC₀
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.SsOrth.exists_le_of_isComponent_of_normal_iSup
      B hBM hn hsup hC₀.1 hL
  exact ⟨i.1, i.2, hC₀.of_le_of_le hi (hBM i)⟩

theorem biSup_erase_le_centralizer {G ι : Type} [Group G] [DecidableEq ι] (P : Finset ι)
    (Gb : ι → Subgroup G)
    (hc : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ x ∈ Gb i, ∀ y ∈ Gb j, Commute x y) {i : ι} (hi : i ∈ P) :
    (⨆ j ∈ P.erase i, Gb j) ≤ Subgroup.centralizer (Gb i : Set G) := by
  refine iSup₂_le fun j hj => ?_
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (hc i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm x hx y hy).eq

theorem ggE0Concl_biSup {G ι : Type} [Group G] [Finite G] (P : Finset ι) (Gb : ι → Subgroup G)
    (hc : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ x ∈ Gb i, ∀ y ∈ Gb j, Commute x y)
    (hblock : ∀ i ∈ P, ∀ C : Subgroup G, IsComponentOf C (Gb i) → GGE0Concl (Gb i) C)
    {C₀ : Subgroup G} (hC₀ : IsComponentOf C₀ (⨆ i ∈ P, Gb i)) :
    GGE0Concl (⨆ i ∈ P, Gb i) C₀ := by
  classical
  obtain ⟨i, hi, hCi⟩ := exists_isComponentOf_block P Gb hc hC₀
  have hcent := biSup_erase_le_centralizer P Gb hc hi
  rw [← Finset.insert_erase hi, Finset.iSup_insert]
  refine ggE0Concl_sup (hblock i hi C₀ hCi) (fun y hy => ?_) ?_
  · exact Subgroup.centralizer_le_normalizer _ (hcent hy)
  · exact hcent.trans (Subgroup.centralizer_le hCi.1)

end CFSG.StandardType
