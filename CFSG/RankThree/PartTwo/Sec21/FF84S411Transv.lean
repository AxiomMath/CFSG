module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Wrap
public import CFSG.RankThree.PartTwo.Sec21.FF84S411TransvStmt
public import CFSG.RankThree.PartTwo.Sec21.FF84S411R

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem EA2_cen_le_L (hpost : FF84Post b L B K b₁ b₂) (hb3 : orderOf b = 3) {A : Subgroup G}
    (hA : A ≤ Cen b) (hAE : IsElementaryAbelian 2 A) : A ≤ L := by
  intro a ha
  obtain ⟨i, l, hl, rfl⟩ := cen_decomp hpost (hA ha)
  have hlc : Commute b l := (Subgroup.mem_centralizer_singleton_iff.1 (hpost.sec.hyp.hLC hl)).symm
  have hcm : Commute (b ^ i) l := hlc.zpow_left i
  have hsq : (b ^ i * l) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) _ ha
  rw [hcm.mul_pow] at hsq
  have hb2 : (b ^ i) ^ 2 = (l ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
  have hmem : (b ^ i) ^ 2 ∈ Subgroup.zpowers b ⊓ L := by
    refine ⟨?_, ?_⟩
    · rw [← zpow_natCast, ← zpow_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _
    · rw [hb2]; exact L.inv_mem (L.pow_mem hl 2)
  rw [hpost.cbL, Subgroup.mem_bot, ← zpow_natCast, ← zpow_mul] at hmem
  have h3 : (3 : ℤ) ∣ i * (2 : ℕ) := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hmem
    rw [hb3] at this
    exact_mod_cast this
  have hi : (3 : ℤ) ∣ i := by omega
  have hbi : b ^ i = 1 := by
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rw [hb3]
    exact_mod_cast hi
  rw [hbi, one_mul]
  exact hl

section


theorem hypTransvRank_of (h41 : FF84_4_1) (h47 : S47TransportItem) (hP : A_PiStar_stmt)
    (hR : A_transvRank_stmt) : HypTransvRank := by
  intro G _ _ b L B K b₁ b₂ hpost U hU t htS ht1 hne A hA hAE
  have c := S48Ctx_of h41 h47 hpost
  have hA8 : A8Model L := a8Model_of_hyp hpost.sec.hyp
  have h180 := card_L_cen_b₁ hA8 hpost
  obtain ⟨e, he₁, he₂⟩ := M0_model hA8 hpost
  have hBP := trX_inf_B_L hpost e he₁ he₂
  have hUL : U ≤ L := ((S47_PiStar_eq hpost U).1 hU).1
  obtain ⟨htSS, htb⟩ := Subgroup.mem_inf.1 htS
  have htU : t ∈ U := by rw [← c.S48_CSb hU]; exact Subgroup.mem_inf.2 ⟨htSS, htb⟩
  have htL : t ∈ L := hUL htU
  have hb₁ : b₁ ∈ L := (Subgroup.mem_inf.1 hpost.sec.hb₁).2
  have h1 : t ∉ ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆ := fun hm =>
    hne (c.S49_one_comp₁ hU h180 hm ht1)
  have h2 : t ∉ ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆ := fun hm =>
    hne (c.S49_one_comp₂ hU h180 hm ht1)
  have hY : trX e U ∈ PiStar A8s Pm 2 := by
    have := (trX_piStar_iff e (inf_le_right : B ⊓ L ≤ L) hUL).1 ((S47_PiStar_eq hpost U).1 hU)
    rwa [hBP] at this
  rw [hP] at hY
  have hY' : trX e U = Ua ∨ trX e U = Ub := hY
  have eb₁ : ((e ⟨b₁, hb₁⟩ : A8s) : P8) = cc := he₁ ⟨b₁, hb₁⟩ rfl
  have hyY : ((e ⟨t, htL⟩ : A8s) : P8) ∈ trX e U := (mem_trX e).2 ⟨⟨t, htL⟩, htU, rfl⟩
  have hy1 : ((e ⟨t, htL⟩ : A8s) : P8) ≠ 1 := by
    intro h
    apply ht1
    have h' : e ⟨t, htL⟩ = 1 := Subtype.ext h
    have := e.injective (h'.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hz : Subgroup.zpowers b₁ ≤ L := (Subgroup.zpowers_le).2 hb₁
  have hyc : ((e ⟨t, htL⟩ : A8s) : P8) ∉ ⁅trX e U, Subgroup.zpowers cc⁆ := by
    intro hm
    have hcomm : ⁅trX e U, Subgroup.zpowers cc⁆ = trX e ⁅U, Subgroup.zpowers b₁⁆ := by
      rw [trX_comm e hUL hz, trX_zpowers e hb₁, eb₁]
    rw [hcomm, mem_trX] at hm
    obtain ⟨x', hx', hxx'⟩ := hm
    have hx'x : x' = ⟨t, htL⟩ := e.injective (Subtype.ext hxx')
    apply h1
    have : t ∈ ⁅U, Subgroup.zpowers b₁⁆ := by
      have := hx'
      rw [hx'x] at this
      exact this
    exact Subgroup.commutator_mono (c.U_le_S hU) le_rfl this
  have hyc2 : ((e ⟨t, htL⟩ : A8s) : P8) ∉ trX e U ⊓ Cen cc := by
    intro hm
    have hinf := trX_inf_cen e U hb₁
    rw [eb₁] at hinf
    rw [← hinf, mem_trX] at hm
    obtain ⟨x', hx', hxx'⟩ := hm
    have hx'x : x' = ⟨t, htL⟩ := e.injective (Subtype.ext hxx')
    apply h2
    rw [c.comm_b₂_eq hU]
    have := hx'
    rw [hx'x] at this
    exact this
  have hbound := hR _ hY' _ hyY hy1 hyc hyc2
  have hAbt : A ≤ Cen b ⊓ Cen t := (S3.Op_le 2 _).trans' hA
  have hAL : A ≤ L := EA2_cen_le_L hpost c.ord_b (fun a ha => (Subgroup.mem_inf.1 (hAbt ha)).1) hAE
  set N : Subgroup G := Op 2 (Cen b ⊓ Cen t) ⊓ L with hN
  have hAN : A ≤ N := le_inf hA hAL
  have hNle : trX e N ≤ Op 2 (Cen ((e ⟨t, htL⟩ : A8s) : P8) ⊓ A8s) := by
    refine S3.le_Op_of_normal 2 (Cen ((e ⟨t, htL⟩ : A8s) : P8) ⊓ A8s) (trX e N) ?_ ?_ ?_
    · intro z hz'
      refine Subgroup.mem_inf.2 ⟨?_, trX_le e N hz'⟩
      have hNt : N ⊓ Cen t = N := inf_eq_left.2 fun n hn =>
        (Subgroup.mem_inf.1 (S3.Op_le 2 _ (Subgroup.mem_inf.1 hn).1)).2
      have := trX_inf_cen e N htL
      rw [hNt] at this
      have hz2 : z ∈ trX e N ⊓ Cen ((e ⟨t, htL⟩ : A8s) : P8) := by
        rw [← this]; exact hz'
      exact (Subgroup.mem_inf.1 hz2).2
    · exact isPGroup_trX e ((S3.Op_isPGroup 2 _).to_le inf_le_left)
    · intro h hh m hm
      obtain ⟨hhc, hhA⟩ := Subgroup.mem_inf.1 hh
      obtain ⟨n, hn, rfl⟩ := (mem_trX e).1 hm
      set ℓ : ↥L := e.symm ⟨h, hhA⟩ with hℓ
      have hℓe : e ℓ = ⟨h, hhA⟩ := by simp [hℓ]
      have hℓt : (ℓ : G) ∈ Cen t := by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have hzc' : h * ((e ⟨t, htL⟩ : A8s) : P8) = ((e ⟨t, htL⟩ : A8s) : P8) * h :=
          Subgroup.mem_centralizer_singleton_iff.1 hhc
        have h5 : e (ℓ * ⟨t, htL⟩) = e (⟨t, htL⟩ * ℓ) := by
          rw [map_mul, map_mul, hℓe]
          exact Subtype.ext hzc'
        have := e.injective h5
        exact congrArg Subtype.val this
      have hℓb : (ℓ : G) ∈ Cen b := hpost.sec.hyp.hLC ℓ.2
      have hn' := Subgroup.mem_inf.1 hn
      refine (mem_trX e).2 ⟨ℓ * n * ℓ⁻¹, ?_, ?_⟩
      · have hmem : (ℓ : G) * (n : G) * (ℓ : G)⁻¹ ∈ Op 2 (Cen b ⊓ Cen t) :=
          S3.Op_conj_mem 2 (Subgroup.le_normalizer (Subgroup.mem_inf.2 ⟨hℓb, hℓt⟩))
            (Subgroup.mem_inf.1 hn).1
        have hL' : (ℓ : G) * (n : G) * (ℓ : G)⁻¹ ∈ L :=
          L.mul_mem (L.mul_mem ℓ.2 n.2) (L.inv_mem ℓ.2)
        exact Subgroup.mem_inf.2 ⟨hmem, hL'⟩
      · rw [map_mul, map_mul, map_inv, hℓe]
        rfl
  have hAA' : trX e A ≤ Op 2 (Cen ((e ⟨t, htL⟩ : A8s) : P8) ⊓ A8s) :=
    (trX_mono e hAN).trans hNle
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1
    ((S3.Op_isPGroup 2 _).to_le (hA : A ≤ Op 2 (Cen b ⊓ Cen t)))
  have hAk : IsElemAb 2 k A := ⟨hAE, hk⟩
  have hAk' := isElemAb_trX_fwd e (by norm_num) hAL hAk
  have := hbound _ hAA' hAk'.1
  rw [natCard_trX e hAL] at this
  exact this

end

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
