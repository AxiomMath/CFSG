module

public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.LocalCores
open scoped commutatorElement

theorem odd_card_iSup_of_commute {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Subgroup G) (hc : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hodd : ∀ i, Odd (Nat.card ↥(H i))) : Odd (Nat.card ↥(⨆ i, H i)) := by
  have hrange : (Subgroup.noncommPiCoprod hc).range = ⨆ i, H i := Subgroup.noncommPiCoprod_range
  have hdvd : Nat.card ↥(Subgroup.noncommPiCoprod hc).range ∣ Nat.card (∀ i, ↥(H i)) :=
    Subgroup.card_range_dvd _
  rw [hrange] at hdvd
  have hpi : Odd (Nat.card (∀ i, ↥(H i))) := by
    rw [Nat.card_pi]
    exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i _ => hodd i
  exact Odd.of_dvd_nat hpi hdvd

theorem odd_card_radical_of_layer_eq_top {D : Type*} [Group D] [Finite D] (hE : layer D = ⊤)
    (hodd : ∀ K : Subgroup D, IsComponent K → Odd (Nat.card ↥(Subgroup.center ↥K))) :
    Odd (Nat.card ↥(solvableRadical D)) := by
  classical
  have hRn : (solvableRadical D).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hRs : Group.IsSolvable ↥(solvableRadical D) := CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hcomm : ⁅layer D, solvableRadical D⁆ = ⊥ :=
    (component_solvable_centralizer hRs hRn.isSubnormal).2
  rw [hE] at hcomm
  have hRZ : solvableRadical D ≤ Subgroup.center D := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro g
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm (Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_iff.mp hle r hr).symm
  have hcenter := (layer_center (G := D)).1
  have hZle : Subgroup.center D ≤
      ⨆ K : ComponentIndex D, (Subgroup.center ↥K.1).map K.1.subtype := by
    intro z hz
    rw [← hcenter]
    refine (mem_map_center_iff (layer D)).mpr ⟨by rw [hE]; exact Subgroup.mem_top z, ?_⟩
    rw [hE]
    exact Subgroup.mem_centralizer_iff.mpr fun h _ => Subgroup.mem_center_iff.mp hz h
  have hjoin : Odd (Nat.card ↥(⨆ K : ComponentIndex D,
      (Subgroup.center ↥K.1).map K.1.subtype)) := by
    refine odd_card_iSup_of_commute _ ?_ fun K => ?_
    · intro K L hKL x y hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      rcases distinct_components_commute K.2 L.2 with h | h
      · exact absurd (Subtype.ext h) hKL
      · have : ⁅(x' : D), (y' : D)⁆ = 1 := by
          have hmem : ⁅(x' : D), (y' : D)⁆ ∈ ⁅K.1, L.1⁆ :=
            Subgroup.commutator_mem_commutator x'.2 y'.2
          rw [h] at hmem
          exact Subgroup.mem_bot.mp hmem
        exact (commutatorElement_eq_one_iff_mul_comm.mp this)
    · rw [Subgroup.card_map_of_injective K.1.subtype_injective]
      exact hodd K.1 K.2
  exact Odd.of_dvd_nat hjoin ((Subgroup.card_dvd_of_le hRZ).trans (Subgroup.card_dvd_of_le hZle))

theorem odd_card_radical_of_blocks {D : Type*} [Group D] [Finite D] {ι : Type*}
    (B : ι → Subgroup D) (hB : ∀ i, IsComponent (B i)) (hgen : ⨆ i, B i = ⊤)
    (hodd : ∀ i, Odd (Nat.card ↥(Subgroup.center ↥(B i)))) :
    Odd (Nat.card ↥(solvableRadical D)) := by
  refine odd_card_radical_of_layer_eq_top ?_ fun K hK => ?_
  · refine eq_top_iff.mpr ?_
    rw [← hgen]
    exact iSup_le fun i => component_le_layer (hB i)
  · by_cases h : ∃ i, K = B i
    · obtain ⟨i, rfl⟩ := h
      exact hodd i
    · exfalso
      push Not at h
      have hKB : ∀ i, K ≤ Subgroup.centralizer (B i : Set D) := fun i => by
        rcases distinct_components_commute hK (hB i) with e | e
        · exact absurd e (h i)
        · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp e
      have hKcenter : ∀ x ∈ K, x ∈ Subgroup.center D := by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ ⨆ i, B i := by rw [hgen]; exact Subgroup.mem_top g
        have hle : (⨆ i, B i : Subgroup D) ≤ Subgroup.centralizer {x} :=
          iSup_le fun i y hy => by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_iff.mp (hKB i hx) y hy)
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
      obtain ⟨-, -, hnc⟩ := hK.1
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_center_iff.mp (hKcenter x x.2) y).symm

end CFSG.RankThree.PartOne.F106
