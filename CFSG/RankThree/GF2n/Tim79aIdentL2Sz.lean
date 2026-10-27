module

public import CFSG.RankThree.GF2n.Tim79aIdentCore
public import CFSG.StronglyEmbedded.BenderCentre

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open CFSG.StronglyEmbedded.BenderCentre
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

variable {G : Type} [Group G]

theorem tim79aIdentL2SzStatement_of_certs :
    Tim79aIdentL2SzStatement := by
  intro G _ _ M V Q P H hs _ _ hK
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hd : Sec23Data V H := hs.data
  have hB : IsBenderL2Sz (XbarZ V H) := hK
  have hBG : IsBenderGroup (XbarZ V H) := hB.isBenderGroup
  have hEel : Assembly.IsElemAbelian 2 (VZ V H) := hc.isElemAbelian_Vtilde
  have hE1 : VZ V H ≠ ⊥ := hc.Vtilde_ne_bot hd
  obtain ⟨S, hES⟩ := exists_le_sylowCenter hBG hEel
  have hEZ : VZ V H = sylowCenter (S : Subgroup (XbarZ V H)) := by
    by_contra hne
    have hlt : VZ V H < sylowCenter (S : Subgroup (XbarZ V H)) := lt_of_le_of_ne hES hne
    obtain ⟨z, hzZ, hzE⟩ := SetLike.exists_of_lt hlt
    have hz1 : z ≠ 1 := fun h => hzE (h ▸ (VZ V H).one_mem)
    obtain ⟨⟨v, hvE⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    obtain ⟨nh, hnhN, hnhz⟩ := exists_normalizer_conj_mem hBG S hE1 hES hzZ hz1
    have hne' : conjSubgroup nh (VZ V H) ≠ VZ V H := fun h => hzE (h ▸ hnhz)
    obtain ⟨w, hw⟩ := exists_not_mem_normalizer hBG S
    have ha₀E : w * v * w⁻¹ ∈ conjSubgroup w (VZ V H) := by
      rw [mem_conjSubgroup, show w⁻¹ * (w * v * w⁻¹) * w = v by group]
      exact hvE
    have ha₀1 : w * v * w⁻¹ ≠ 1 := by
      intro h
      apply hv1'
      have h2 : w⁻¹ * (w * v * w⁻¹) * w = 1 := by rw [h]; group
      rwa [show w⁻¹ * (w * v * w⁻¹) * w = v by group] at h2
    have ha₀N := not_mem_normalizer_of_mem_conj hBG hES hw ha₀E ha₀1
    have hgen0 : sylowCenter (S : Subgroup (XbarZ V H)) ⊔ Subgroup.zpowers (w * v * w⁻¹) = ⊤ :=
      sylowCenter_sup_zpowers_eq_top hB S ha₀N
    refine hc.false_of_cover hd {n | n ∈ Subgroup.normalizer ((S : Subgroup (XbarZ V H)) : Set _)}
      hne' ?_ ?_ ha₀E ha₀1 ?_
    · intro n hn a ha b hb
      have haZ := conjSubgroup_le_sylowCenter hn hES ha
      exact ((mem_sylowCenter.mp (hES hb)).2 a (mem_sylowCenter.mp haZ).1)
    · intro n hn a ha b hb
      have haZ := conjSubgroup_le_sylowCenter hn hES ha
      have hbZ := conjSubgroup_le_sylowCenter hnhN hES hb
      exact ((mem_sylowCenter.mp hbZ).2 a (mem_sylowCenter.mp haZ).1)
    · refine eq_top_iff.mpr ?_
      rw [← hgen0]
      refine sup_le_sup_right ?_ _
      intro z' hz'
      by_cases hz'1 : z' = 1
      · rw [hz'1]
        exact Subgroup.one_mem _
      obtain ⟨n, hn, hzn⟩ := exists_normalizer_conj_mem hBG S hE1 hES hz' hz'1
      exact Subgroup.mem_iSup_of_mem n (Subgroup.mem_iSup_of_mem hn hzn)
  have hcard : Nat.card (VZ V H) = Nat.card (barOf V H V) := hc.card_Vtilde hd
  rcases hK with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · left
    refine ⟨n, hn, ?_, ⟨e⟩, S, ?_⟩
    · rw [qBar, ← hcard, hEZ, card_sylowCenter_psl2 hn e S]
    · exact (sylowCenter_eq_of_psl2 hn e S).symm.trans hEZ.symm
  · right
    left
    refine ⟨n, hn, ?_, ⟨e⟩, S, ?_⟩
    · rw [qBar, ← hcard, hEZ, card_sylowCenter_sz hn e S]
    · exact hEZ.trans (map_center_eq S).symm

end CFSG.RankThree.GF2n.Tim79a
