module

public import CFSG.Quasithin.Vol2.Ch10SecB6Pair
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecB6Odd

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_K1 (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hyp : Hyp10 G T L I)
    {K : Subgroup G} (hKli : Ch10.IsLi T L K) {H : Subgroup G} (hH2 : pCoreOf 2 H ≠ ⊥)
    (hS : IsSylowTwoOf (Ch10.T1 T L) H) (hKH : K ≤ H) :
    ∃ K1 ∈ cComp H, K ≤ K1 ∧ H ≤ Subgroup.normalizer (K1 : Set G) := by
  have hX : ∃ t ∈ T, K = L ∨ K = CFSG.conjugate L t := by
    rcases hKli with rfl | ⟨t, ht, -, rfl⟩
    · exact ⟨1, T.one_mem, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr rfl⟩
  obtain ⟨t, ht, hX⟩ := hX
  obtain ⟨hXc, hn, -, -⟩ := SecB.li_data h37 h38 hyp ht hX
  have hfam : K ∈ lFamily (Ch10.T1 T L) :=
    cComp_subset_lFamily (inf_le_left.trans (SecA.le_fsuM T L)) hXc
  obtain ⟨K1, hK1, hKK1⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hH2 hS hKH hfam
  have hn1 := Vol2Native.lemma_1_2_4_normal hK h37 h38 hH2 hS hfam hKK1 hK1 hn
  exact ⟨K1, hK1, hKK1,
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK1)).mp hn1⟩

omit [Finite G] in
theorem le_of_commutator_eq {H K1 D : Subgroup G} {z : G} (hDH : D ≤ H)
    (hK1 : H ≤ Subgroup.normalizer (K1 : Set G)) (hzK1 : z ∈ K1)
    (hDD : ⁅D, Subgroup.zpowers z⁆ = D) : D ≤ K1 := by
  rw [← hDD, Subgroup.commutator_le]
  intro d hd y hy
  have hyK : y ∈ K1 := (Subgroup.zpowers_le.mpr hzK1) hy
  rw [commutatorElement_def]
  exact K1.mul_mem ((Subgroup.mem_normalizer_iff.mp (hK1 (hDH hd)) y).mp hyK) (K1.inv_mem hyK)

theorem not_mem_pCoreOf_of_commutator_eq {H D : Subgroup G} {z : G} (hDH : D ≤ H)
    (hD : Odd (Nat.card D)) (hD1 : D ≠ ⊥) (hDD : ⁅D, Subgroup.zpowers z⁆ = D) :
    z ∉ pCoreOf 2 H := by
  intro hz
  apply hD1
  have h1 : D ≤ pCoreOf 2 H := by
    rw [← hDD, Subgroup.commutator_le]
    intro d hd y hy
    have hyQ : y ∈ pCoreOf 2 H := (Subgroup.zpowers_le.mpr hz) hy
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hDH hd)) y).mp hyQ)
      (Subgroup.inv_mem _ hyQ)
  have h2 := SecB.inf_eq_bot_of_two_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hD
  exact le_bot_iff.mp (h2 ▸ le_inf h1 le_rfl)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
