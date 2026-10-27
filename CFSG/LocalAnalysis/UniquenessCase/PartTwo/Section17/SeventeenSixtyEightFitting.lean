module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySeven
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem layer_le_barImage_conjClosure {D : Data G} {L : Subgroup G}
    (hA : ∀ J ∈ calC D.M, J ∈ conjSetOf D.M L) :
    CFSG.layer (Bar2 D.M) ≤ barImage D.M (conjClosure D.M L) := by
  rw [s13_Layer13_layer_eq_iSup]
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨L', hL', rfl⟩ :=
    s13_exists_calC_of_component D.M (s13_Layer13_mem_comps.mp hJ)
  obtain ⟨x, hx, rfl⟩ := hA L' hL'
  exact barImage_mono
    (le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf D.M L) => K) _ ⟨x, hx, rfl⟩ le_rfl)

theorem isPGroup_pElementSubgroup_centralizer_of_layer_le (D : Data G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    (h638 : UC6.R6_38 D) (h5 : 5 ∈ D.sig) {A : Subgroup (Bar2 D.M)}
    (hlayer : CFSG.layer (Bar2 D.M) ≤ A) :
    IsPGroup 5 ↥(CFSG.RankThree.PartOne.pElementSubgroup 5
      (Subgroup.centralizer (A : Set (Bar2 D.M)))) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have htop : CFSG.GH74.GLS.oResidual 5 (Bar2 D.M) = ⊤ :=
    uc22p21c_oResidual_bar_eq_top Nat.prime_five
      (h638 5 Nat.prime_five (by norm_num) (Or.inl h5))
  let S : Set (Bar2 D.M) := {x | x ∈ Subgroup.centralizer (A : Set (Bar2 D.M)) ∧
    ∃ k : ℕ, orderOf x = 5 ^ k}
  have hScomm : ∀ s ∈ S, s ∈ commutator (Bar2 D.M) := fun s hs => by
    obtain ⟨-, k, hk⟩ := hs
    exact uc22p21c_mem_commutator_of_oResidual_eq_top htop (k := k) (hk ▸ dvd_rfl)
  have hSpow : ∀ s ∈ S, ∃ k : ℕ, s ^ 5 ^ k = 1 := fun s hs => by
    obtain ⟨-, k, hk⟩ := hs
    exact ⟨k, hk ▸ pow_orderOf_eq_one s⟩
  have hYcomm : Subgroup.closure S ≤ commutator (Bar2 D.M) :=
    (Subgroup.closure_le _).mpr hScomm
  have h1 : Subgroup.closure S ≤
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
    rw [Subgroup.closure_le]
    intro s hs
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hlayer) hs.1
  have h2 : ∀ q : ℕ, q.Prime → q ≠ 5 → Subgroup.closure S ≤
      Subgroup.centralizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M)) := by
    intro q hq hqp
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk⟩ := hSpow s hs
    exact mem_centralizer_pCore_of_pElement D hV h22 h23 Nat.prime_five hq hqp
      (hScomm s hs) hk
  have h3 : ∀ x ∈ Subgroup.closure S, ∃ n : ℕ,
      x ^ 5 ^ n ∈ Subgroup.centralizer (CFSG.pCore 5 (Bar2 D.M) : Set (Bar2 D.M)) :=
    fun x hx => commutator_bar_pow_mem_centralizer_pCore D hV h22 h23 Nat.prime_five
      (hYcomm hx)
  haveI := CFSG.GroupTheory.isNilpotent_of_le_centralizer_layer_pCores Nat.prime_five h1 h2 h3
  have hYp : IsPGroup 5 (Subgroup.closure S) := by
    have hcl := CFSG.GroupTheory.isPGroup_closure_of_isNilpotent (Y := ↥(Subgroup.closure S))
      (p := 5) (S := (Subgroup.closure S).subtype ⁻¹' S) fun s hs => by
        obtain ⟨k, hk⟩ := hSpow _ hs
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
    rw [Subgroup.closure_preimage_eq_top] at hcl
    exact hcl.of_equiv Subgroup.topEquiv
  exact hYp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
