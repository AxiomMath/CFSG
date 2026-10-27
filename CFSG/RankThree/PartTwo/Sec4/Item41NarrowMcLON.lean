module

public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowThreeCover
public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Sporadic.ONOddCore.Involutions
public import CFSG.Sporadic.Schreier.ONInvolution
public import CFSG.RankThree.PartOne.SecRank.CentralizerRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item41Narrow

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native in
theorem card_centralizer_mclP
    {t : mclP} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set mclP)) = 40320 := by
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ := mcl_involution_centralizers
  have htR : (t : Equiv.Perm (Fin 275)) ∈ mclR := (le_sup_left : mclP ≤ mclP ⊔ _) t.2
  have ht2 : orderOf (t : Equiv.Perm (Fin 275)) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨r, hr, g, hg, hrep⟩ := hcover _ htR ht2
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows r hr
  have hrepP : tp 275 r.rep ∈ mclP := by
    have h1 := mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) t.2) hg
    rwa [hrep, show g⁻¹ * (g * tp 275 r.rep * g⁻¹) * g = tp 275 r.rep by group] at h1
  have hrout : r.outer = false := by
    cases h : r.outer
    · rfl
    · exact absurd hrepP (hout.1 h)
  have hr40320 : r.centOrder = 40320 := by
    have hm := List.mem_map_of_mem (f := fun r => (r.outer, r.classSize, r.centOrder)) hr
    rw [hmap] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · rw [hrout] at h
      exact absurd h (by decide)
  rw [CFSG.RankThree.PartTwo.Census.card_centralizer_subgroup, hrep,
    inf_centralizer_conj mclP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcent,
    hr40320]

open CFSG.ONSchreier in
theorem card_centralizer_Pv
    {t : Pv} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set Pv)) = 161280 := by
  obtain ⟨g, hg, hgt⟩ := CFSG.Sporadic.ONOddCore.cti_on_all_involutions_conjugate
    (t : Equiv.Perm (Fin N)) t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  obtain ⟨-, -, -, hM, -, hcard⟩ := at_on_full_involution_centralizer
  rw [CFSG.RankThree.PartTwo.Census.card_centralizer_subgroup, hgt,
    CFSG.Sporadic.SmallOddCore.inf_centralizer_conj Pv hg,
    Subgroup.card_map_of_injective (MulAut.conj g).injective, ← hM, hcard]

theorem localRank_three_mclP_le :
    localRank 3 CFSG.Sporadic.Schreier.mclP ≤ 3 :=
  CFSG.RankThree.PartOne.SecRank.localRank_three_le_of_centralizer 2 fun t ht h27 => by
    rw [card_centralizer_mclP ht] at h27
    exact absurd h27 (by norm_num)

theorem localRank_three_Pv_le :
    localRank 3 CFSG.ONSchreier.Pv ≤ 3 :=
  CFSG.RankThree.PartOne.SecRank.localRank_three_le_of_centralizer 2 fun t ht h27 => by
    rw [card_centralizer_Pv ht] at h27
    exact absurd h27 (by norm_num)

theorem item4_1ThreeCoverMcLON_holds :
    Item4_1ThreeCoverMcLON := by
  intro X _ _ _ _ _ _ h
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
      (e.trans CFSG.Sporadic.Schreier.mclPermEquiv) Nat.prime_three]
    exact localRank_three_mclP_le
  · obtain ⟨e⟩ := h
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
      (e.trans CFSG.ONSchreier.onEquivPv) Nat.prime_three]
    exact localRank_three_Pv_le

theorem item4_1ThreeCover_of_griess
    (hGA : GriessMultipliersAllModels) : Item4_1ThreeCover :=
  item4_1ThreeCover_of_mcLON hGA item4_1ThreeCoverMcLON_holds

end CFSG.RankThree.PartTwo.Sec4.Item41Narrow
