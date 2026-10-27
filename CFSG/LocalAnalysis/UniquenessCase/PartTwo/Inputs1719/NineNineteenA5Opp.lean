module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5Act

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OppThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_eq_one_of_index_two_pow {K Y : Subgroup G} (hK : (K.subgroupOf Y).Normal)
    (hidx : ∃ k : ℕ, (K.subgroupOf Y).index = 2 ^ k) {p : ℕ} (hp : Odd p) {y : G} (hy : y ∈ Y)
    {a : ℕ} (hya : y ^ p ^ a = 1) : y ∈ K := by
  obtain ⟨k, hk⟩ := hidx
  have : (K.subgroupOf Y).Normal := hK
  have hyq : (⟨y, hy⟩ : ↥Y) ^ p ^ a = 1 := Subtype.ext (by simpa using hya)
  have hqa : ((⟨y, hy⟩ : ↥Y) : ↥Y ⧸ K.subgroupOf Y) ^ p ^ a = 1 := by
    rw [← QuotientGroup.mk_pow, hyq]
    simp
  have hq2 : ((⟨y, hy⟩ : ↥Y) : ↥Y ⧸ K.subgroupOf Y) ^ 2 ^ k = 1 := by
    rw [← hk, Subgroup.index_eq_card]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime (p ^ a) (2 ^ k) := Nat.Coprime.pow a k hp.coprime_two_right
  have hq : ((⟨y, hy⟩ : ↥Y) : ↥Y ⧸ K.subgroupOf Y) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp ⟨hqa, hq2⟩
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := K.subgroupOf Y) ⟨y, hy⟩).1 hq)

theorem opp_three_eq_of_le {M L Y : Subgroup G} (hL : L ∈ calC M) (hA5 : IsAlt (Bar2 L) 5)
    (hLY : L ≤ Y) (hnorm : (L.subgroupOf Y).Normal)
    (hidx : ∃ k : ℕ, (L.subgroupOf Y).index = 2 ^ k) : Opp 3 Y = L := by
  have hle : Opp 3 Y ≤ L := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxY, k, hk⟩
    exact mem_of_pow_eq_one_of_index_two_pow hnorm hidx (p := 3) (a := k) (by norm_num) hxY
      (by rw [← hk]; exact pow_orderOf_eq_one x)
  have hgen : Opp 3 L ≤ Opp 3 Y := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact Subgroup.closure_mono fun x hx => ⟨hLY hx.1, hx.2⟩
  have hLL : Opp 3 L = L :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.opp_three_eq_self_of_bar2 hL
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five hA5)
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.three_dvd_bar2_of_isAlt hA5)
  rw [hLL] at hgen
  exact le_antisymm hle hgen

theorem exists_eq_map_conj_of_card_three {L D₃ A : Subgroup G} (hA5 : IsAlt (Bar2 L) 5)
    (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) (hAL : A ≤ L) (hA : Nat.card A = 3) :
    ∃ l ∈ L, A = D₃.map (MulAut.conj l).toMonoidHom := by
  have hDcard : Nat.card ↥(D₃.subgroupOf L) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₃L).toEquiv, hD₃]
  have hAcard : Nat.card ↥(A.subgroupOf L) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA]
  have hcyc : ∀ T : Sylow 3 ↥L, IsCyclic ↥T := by
    intro T
    have hT : IsPGroup 3 ↥((T : Subgroup ↥L).map L.subtype) := T.isPGroup'.map L.subtype
    have h := card_dvd_three_of_isPGroup hA5 hT (Subgroup.map_subtype_le (T : Subgroup ↥L))
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h
    exact isCyclic_of_card_dvd_prime h
  obtain ⟨l, hl⟩ := CFSG.AGLEmbeddingD2.exists_eq_map_conj_of_isCyclic hcyc hDcard hAcard
  refine ⟨l, l.2, ?_⟩
  have hcomp : (L.subtype.comp (MulAut.conj l).toMonoidHom : ↥L →* G) =
      (MulAut.conj (l : G)).toMonoidHom.comp L.subtype := by
    ext x
    simp [MulAut.conj_apply]
  have key : ((A.subgroupOf L).map L.subtype) =
      ((D₃.subgroupOf L).map (MulAut.conj l).toMonoidHom).map L.subtype := by
    rw [hl]
  rw [Subgroup.map_subgroupOf_eq_of_le hAL, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hD₃L] at key
  exact key

theorem le_iSup_map_conj {M L D₃ : Subgroup G} (hL : L ∈ calC M) (hA5 : IsAlt (Bar2 L) 5)
    (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) :
    L ≤ ⨆ l : ↥L, D₃.map (MulAut.conj (l : G)).toMonoidHom := by
  have hLL : Opp 3 L = L :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.opp_three_eq_self_of_bar2 hL
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five hA5)
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.three_dvd_bar2_of_isAlt hA5)
  have hgen : Opp 3 L ≤ ⨆ l : ↥L, D₃.map (MulAut.conj (l : G)).toMonoidHom := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxL, k, hk⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hx1 : x = 1 := by
        rw [← orderOf_eq_one_iff, hk, hk0, pow_zero]
      rw [hx1]
      exact Subgroup.one_mem _
    · have hzp : IsPGroup 3 ↥(Subgroup.zpowers x) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
      have hzL : Subgroup.zpowers x ≤ L := Subgroup.zpowers_le.mpr hxL
      have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ 3 :=
        card_dvd_three_of_isPGroup hA5 hzp hzL
      rw [Nat.card_zpowers, hk] at hdvd
      have hk1 : k = 1 := by
        have hle : k ≤ 1 := by
          rw [← Nat.pow_dvd_pow_iff_le_right (x := 3) (by norm_num : 1 < 3)]
          simpa using hdvd
        omega
      have hxord : orderOf x = 3 := by rw [hk, hk1, pow_one]
      have hzcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
      obtain ⟨l, hlL, hl⟩ :=
        exists_eq_map_conj_of_card_three (A := Subgroup.zpowers x) hA5 hD₃L hD₃ hzL hzcard
      have hmem : x ∈ D₃.map (MulAut.conj (l : G)).toMonoidHom := hl ▸ Subgroup.mem_zpowers x
      exact Subgroup.mem_iSup_of_mem
        (S := fun l : ↥L => D₃.map (MulAut.conj (l : G)).toMonoidHom) ⟨l, hlL⟩ hmem
  calc L = Opp 3 L := hLL.symm
    _ ≤ ⨆ l : ↥L, D₃.map (MulAut.conj (l : G)).toMonoidHom := hgen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
