module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.EvenSporadicStandard.HNRecog Subgroup

private theorem natCard_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem natCard_a5WrTwo : Nat.card A5WrTwo = 7200 := by
  rw [RegularWreathProduct.card, natCard_alternatingGroup_five,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  norm_num

private theorem card_le_two_mul_card_inf_range (L : Subgroup A5WrTwo) :
    Nat.card L ≤ 2 * Nat.card ↥(L ⊓ A5WrTwo.baseEmb.range) := by
  have hK : A5WrTwo.baseEmb.range.index = 2 := by
    rw [A5WrTwo.range_baseEmb]
    exact A5WrTwo.index_commutator
  have h3 := Subgroup.index_inf_le (H := L) (K := A5WrTwo.baseEmb.range)
  rw [hK] at h3
  have hpos : 0 < L.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card L * L.index = Nat.card A5WrTwo := Subgroup.card_mul_index L
    _ = Nat.card ↥(L ⊓ A5WrTwo.baseEmb.range) * (L ⊓ A5WrTwo.baseEmb.range).index :=
      (Subgroup.card_mul_index _).symm
    _ ≤ Nat.card ↥(L ⊓ A5WrTwo.baseEmb.range) * (L.index * 2) := Nat.mul_le_mul_left _ h3
    _ = 2 * Nat.card ↥(L ⊓ A5WrTwo.baseEmb.range) * L.index := by ring

private theorem card_le_card_map_fst_mul_card_map_snd
    (L : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    Nat.card L ≤ Nat.card ↥(L.map (MonoidHom.fst _ _)) * Nat.card ↥(L.map (MonoidHom.snd _ _)) := by
  have hle : L ≤ (L.map (MonoidHom.fst _ _)).prod (L.map (MonoidHom.snd _ _)) :=
    Subgroup.le_prod_iff.2 ⟨le_rfl, le_rfl⟩
  calc Nat.card L ≤ Nat.card ↥((L.map (MonoidHom.fst _ _)).prod (L.map (MonoidHom.snd _ _))) :=
        Subgroup.card_le_of_le hle
    _ = _ := by rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]

private theorem isSylowTwoOf_of_card_eq_four {P : Subgroup (alternatingGroup (Fin 5))}
    (hP : Nat.card P = 4) : CFSG.QuasithinUnique.IsSylowTwoOf P ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 2) (by rw [hP]; norm_num), ?_⟩
  have hidx : (P.subgroupOf ⊤).index = P.index := Subgroup.relIndex_top_right P
  rw [hidx]
  have h := Subgroup.card_mul_index P
  rw [hP, natCard_alternatingGroup_five] at h
  omega

private theorem card_map_le_four {L : Subgroup (alternatingGroup (Fin 5))}
    (hL : Nat.card L ∣ 16) : Nat.card L ≤ 4 := by
  have h1 : Nat.card L ∣ Nat.gcd 16 60 :=
    Nat.dvd_gcd hL (natCard_alternatingGroup_five ▸ Subgroup.card_subgroup_dvd_card L)
  have hg : Nat.gcd 16 60 = 4 := by norm_num
  rw [hg] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem le_of_isSylowTwoOf_of_not_three_dvd_a5WrTwo {S H : Subgroup A5WrTwo}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hSH : S ≤ H) (h3 : ¬ 3 ∣ Nat.card ↥H) :
    H ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := natCard_a5WrTwo
  obtain ⟨-, hS2, hSidx⟩ := hS
  have hidx : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [hidx] at hSidx
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hmul := Subgroup.card_mul_index S
  rw [hk, hG] at hmul
  have hk5 : 2 ^ k = 32 := by
    have hk13 : k < 13 := by
      by_contra hc
      have h : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      nlinarith
    interval_cases k <;> omega
  have hS32 : Nat.card S = 32 := hk.trans hk5
  have hKc : Nat.card A5WrTwo.baseEmb.range = 3600 := by
    have h := Subgroup.card_mul_index A5WrTwo.baseEmb.range
    rw [A5WrTwo.range_baseEmb, A5WrTwo.index_commutator, hG] at h
    rw [A5WrTwo.range_baseEmb]
    omega
  have hSK : Nat.card ↥(S ⊓ A5WrTwo.baseEmb.range) = 16 := by
    have h1 : Nat.card ↥(S ⊓ A5WrTwo.baseEmb.range) ∣ Nat.gcd 32 3600 :=
      Nat.dvd_gcd (hS32 ▸ Subgroup.card_dvd_of_le inf_le_left)
        (hKc ▸ Subgroup.card_dvd_of_le inf_le_right)
    have hg : Nat.gcd 32 3600 = 16 := by norm_num
    rw [hg] at h1
    have h2 := card_le_two_mul_card_inf_range S
    have h4 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hcomap : ∀ L : Subgroup A5WrTwo,
      Nat.card ↥(L.comap A5WrTwo.baseEmb) = Nat.card ↥(L ⊓ A5WrTwo.baseEmb.range) := by
    intro L
    rw [← Subgroup.card_map_of_injective A5WrTwo.baseEmb_injective, Subgroup.map_comap_eq,
      inf_comm]
  have hS' : Nat.card ↥(S.comap A5WrTwo.baseEmb) = 16 := (hcomap S).trans hSK
  have hSH' : S.comap A5WrTwo.baseEmb ≤ H.comap A5WrTwo.baseEmb := Subgroup.comap_mono hSH
  have h3' : ¬ 3 ∣ Nat.card ↥(H.comap A5WrTwo.baseEmb) := fun h =>
    h3 (h.trans ((hcomap H).symm ▸ Subgroup.card_dvd_of_le inf_le_left))
  have hp1 := card_map_le_four (L := (S.comap A5WrTwo.baseEmb).map (MonoidHom.fst _ _))
    (hS' ▸ Subgroup.card_map_dvd _ _)
  have hp2 := card_map_le_four (L := (S.comap A5WrTwo.baseEmb).map (MonoidHom.snd _ _))
    (hS' ▸ Subgroup.card_map_dvd _ _)
  have hprod := card_le_card_map_fst_mul_card_map_snd (S.comap A5WrTwo.baseEmb)
  rw [hS'] at hprod
  have hq1 : Nat.card ↥((S.comap A5WrTwo.baseEmb).map (MonoidHom.fst _ _)) = 4 := by
    nlinarith
  have hq2 : Nat.card ↥((S.comap A5WrTwo.baseEmb).map (MonoidHom.snd _ _)) = 4 := by
    nlinarith
  have hr1 : (H.comap A5WrTwo.baseEmb).map (MonoidHom.fst _ _) ≤
      (S.comap A5WrTwo.baseEmb).map (MonoidHom.fst _ _) :=
    le_of_isSylowTwoOf_of_not_three_dvd_alt le_rfl (MulEquiv.refl _)
      (isSylowTwoOf_of_card_eq_four hq1) (Subgroup.map_mono hSH')
      (fun h => h3' (h.trans (Subgroup.card_map_dvd _ _)))
  have hr2 : (H.comap A5WrTwo.baseEmb).map (MonoidHom.snd _ _) ≤
      (S.comap A5WrTwo.baseEmb).map (MonoidHom.snd _ _) :=
    le_of_isSylowTwoOf_of_not_three_dvd_alt le_rfl (MulEquiv.refl _)
      (isSylowTwoOf_of_card_eq_four hq2) (Subgroup.map_mono hSH')
      (fun h => h3' (h.trans (Subgroup.card_map_dvd _ _)))
  have hH' := card_le_card_map_fst_mul_card_map_snd (H.comap A5WrTwo.baseEmb)
  have hc1 := Subgroup.card_le_of_le hr1
  have hc2 := Subgroup.card_le_of_le hr2
  rw [hq1] at hc1
  rw [hq2] at hc2
  have hH16 : Nat.card ↥(H.comap A5WrTwo.baseEmb) ≤ 16 := by
    calc _ ≤ _ := hH'
      _ ≤ 4 * 4 := Nat.mul_le_mul hc1 hc2
  have hH := card_le_two_mul_card_inf_range H
  rw [← hcomap H] at hH
  exact (Subgroup.eq_of_le_of_card_ge hSH (by omega)).ge

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
