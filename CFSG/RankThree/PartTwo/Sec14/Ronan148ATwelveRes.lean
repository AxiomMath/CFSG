module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwelveImg
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VHJ5
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Six
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J


section Certificates


theorem step148HJHJCent5_holds (h134 : Item134) (h48 : Sec4.Item4_8) :
    Ronan148V.Step148HJHJCent5 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl hJX hZ5 h12
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hdYd : d ∈ Yd := hYBYd hdYB
  obtain ⟨φ⟩ := hJ2
  set dα := alpha148 A Y d hdA with hdαdef
  have hdα3 : dα ^ 3 = 1 := alpha148_pow_three hA3 hdA
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hdA fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff, ← hdαdef, h, one_mul, mul_one]
  obtain ⟨-, hYd6, hYdp, -, -⟩ :=
    img148_yd_facts_of_j2 hY.2 hdA (hA3 d hdA) hYd hJ hYdJ hAJ hA6 hθ φ hdYd hdα1 hdα3
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdYdα : dα ∈ img148 A Y Yd :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdYd, rfl⟩
  have hYdY : Yd ≤ Y := (le_of_mem_thetaComponentsIn hYd).trans inf_le_left
  obtain ⟨ψ5⟩ := hZ5
  have hZC := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hD1 : deltaZero A (lB A) (centPre148 A Y J) ≤ Y :=
    (sSup_le fun _ hQ => hQ.2 : deltaZero A (lB A) (centPre148 A Y J) ≤ centPre148 A Y J).trans
      centPre148_le
  refine false_of_ncard_twelve_img148' h134 h48 hS hY hB hc h12 hdA _ _ (img148_mono hD1)
    (img148_mono hYdY) ?_ ?_ ?_ (isTwelveType_of_mulEquiv_A5 ψ5)
    (isTwelveType_of_tripleCover_A6 hYd6 hYdp)
  ·
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hZC hx).2 dα hdJα).symm
  ·
    intro x hx
    obtain ⟨g, hgM, hgYd, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hgd := Subgroup.mem_centralizer_singleton_iff.mp
      ((le_of_mem_thetaComponentsIn hYd) hgYd).2
    simpa using hgd
  ·
    intro x hx
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (img148_mono hYdJ)) (hZC hx).2

theorem step148HJA5J2Twelve_holds (h134 : Item134) (h48 : Sec4.Item4_8) :
    Ronan148W.Step148HJA5J2Twelve := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne hZ2 hAZ hZ27 hJd hZJ h12
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := hB.1 hdB
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  set dα := alpha148 A Y d hdA with hdαdef
  have hdα3 : dα ^ 3 = 1 := alpha148_pow_three hA3 hdA
  have hdα1 : dα ≠ 1 := fun h =>
    hd1 (alpha148_injective hA3 hdA A.one_mem (h.trans Ronan148V.alpha148_one'.symm))
  have hzc : img148 A Y (Subgroup.zpowers d) = Subgroup.zpowers dα :=
    le_antisymm (img148_zpowers_le hdA) (Subgroup.zpowers_le.mpr
      (mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, Subgroup.mem_zpowers d, rfl⟩))
  have hCd : Subgroup.centralizer
      (img148 A Y (Subgroup.zpowers d) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      Subgroup.centralizer {dα} := by
    rw [hzc, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hdZ : dα ∈ Zα := by
    have hdB' : dα ∈ img148 A Y B :=
      mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩
    rw [← hAZ] at hdB'
    exact hdB'.2
  obtain ⟨ψ⟩ := hZ2
  obtain ⟨hF6, hFp, -, -⟩ := inf_centralizer_facts_of_j2 ψ hdZ hdα1 hdα3 (by rw [← hCd]; exact hZ27)
  obtain ⟨η5⟩ := hJ5
  have hYdY : Yd ≤ Y := (le_of_mem_thetaComponentsIn hYd).trans inf_le_left
  have hD1 : deltaZero A (lB A) (centPre148 A Y J) ≤ Y :=
    (sSup_le fun _ hQ => hQ.2 : deltaZero A (lB A) (centPre148 A Y J) ≤ centPre148 A Y J).trans
      centPre148_le
  have hT₂ : IsTwelveType ↥(img148 A Y Yd) := by
    rw [heq]
    exact isTwelveType_of_mulEquiv_A5 η5
  refine false_of_ncard_twelve_img148' h134 h48 hS hY hB hc h12 hdA
    (Zα ⊓ Subgroup.centralizer {dα}) (img148 A Y Yd) (inf_le_left.trans (img148_mono hD1))
    (img148_mono hYdY) inf_le_right ?_ ?_ (isTwelveType_of_tripleCover_A6 hF6 hFp) hT₂
  ·
    rw [heq, ← hCd]
    exact hJd
  ·
    intro x hx
    rw [heq]
    exact hZJ hx.1

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
