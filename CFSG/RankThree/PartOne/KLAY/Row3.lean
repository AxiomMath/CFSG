module

public import CFSG.RankThree.PartOne.KLAY.D4
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame
public import CFSG.RankThree.PartOne.KLAY.Frames

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

theorem kf1212LayerRow3
    : KF1212LayerRow 3 := by
  intro G _ _ p A c L E ctx hmodel hEA _
  have hEA' : E = A := hEA (by norm_num)
  have h := ctx.hyp
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hKfin, σ, hP, ⟨ζ, hζ⟩, ε, hε, hFT₁, hFT₂⟩ := exists_r3frame hcore hmodel
  have hf1 : 1 ≤ f := hP.one_le
  have hpq : p ∣ 2 ^ f - 1 := hP.dvd
  have hq : IsCentralPQuot p (d4Q hP) := isCentralPQuot_d4Q hP
  obtain ⟨bM, hbMT, hbMp, hbM1, hKq, hKz, hTK, ⟨U, hU, hU2, hTU, hnc⟩, k, hkf, hkfin, hk,
    ⟨eqv₂⟩⟩ := d4_side_two hP hζ
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega) hpq
  have hK6 : 6 ≤ 2 ^ f := by omega
  obtain ⟨x, hx⟩ := hFT₁ bM hbMT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA' ▸ x.2.1
  have hbb : ε ⟨(x : G), hxL⟩ = d4Q hP bM := hx
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : d4Q hP bM = d4Q hP 1 := by
      rw [← hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbM1 (hq.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA']
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (Tp3 hP).map (d4Q hP) := by
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA'.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := ctx.generic.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem ctx.L_le_centralizer hA ε (d4Q hP) hε hq hxA hxL hbMp hbb
    (T₀ := Tp3 hP) (U := U) (fun t ht => Tp3_exp hP t ht) hAT hKq hKz hTK hU hU2 hTU hnc
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  refine ⟨by norm_num, by norm_num, f, hf1, hpq, ⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩, k,
    hkf, hkfin, hk, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · exact ⟨eqv.trans (eqv₂.trans (projectiveSpecialLinearGroupEquivStatedProj 2 k))⟩

end CFSG.RankThree.PartOne.KLAY
