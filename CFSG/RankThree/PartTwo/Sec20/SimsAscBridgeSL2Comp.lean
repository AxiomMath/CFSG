module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.KGroups.L3EpsInvLin
import CFSG.GH74.GLS.IVK.L2.Lemma12
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup

public section

namespace CFSG.RankThree.PartTwo.Sec20.SL2Comp

open CFSG.GH74.GLS.IVK

private theorem eq_five_or_seven_of_half {p : ℕ} (hp5 : 5 ≤ p)
    (h : p * (p ^ 2 - 1) / 2 = 60 ∨ p * (p ^ 2 - 1) / 2 = 168) : p = 5 ∨ p = 7 := by
  have hp7 : p ≤ 7 := by
    by_contra hp
    have h8 : 252 ≤ p * (p ^ 2 - 1) / 2 :=
      calc 252 = 8 * (8 ^ 2 - 1) / 2 := by norm_num
        _ ≤ p * (p ^ 2 - 1) / 2 := Nat.div_le_div_right (Nat.mul_le_mul (by omega)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1))
    omega
  interval_cases p <;> simp_all

private theorem l2Field_and_nonempty_mulEquiv {Y : Type} [Group Y] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {S : Subgroup Y}
    (eS : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) :
    L2Field (GaloisField p 1) ∧ Nonempty (↥S ⧸ Subgroup.center ↥S ≃* L2 (GaloisField p 1)) := by
  have hcard : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  refine ⟨⟨?_, ?_⟩, ⟨(QuotientGroup.congr (Subgroup.center ↥S)
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1))) eS
    (Subgroup.map_center_eq eS)).trans (L2.equivPSL (GaloisField p 1)).symm⟩⟩
  · rw [hcard]
    exact (Fact.out : p.Prime).odd_of_ne_two (by omega)
  · rw [hcard]
    omega

private theorem isSimpleGroup_range_and_card {Y : Type} [Group Y]
    [Finite Y] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {S : Subgroup Y}
    (eS : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1))
    {L : Subgroup Y} (hLS : L ≤ S) (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    {Qk : Type} [Group Qk] [IsSimpleGroup Qk] (φ : ↥L →* Qk) (hφ : Function.Surjective φ)
    (hQ : (∃ n : ℕ, Even n ∧ 0 < n ∧
        Nonempty (Qk ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))) ∨
      (∃ n : ℕ, Odd n ∧
        Nonempty (Qk ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)))) :
    IsSimpleGroup ((QuotientGroup.mk' (Subgroup.center ↥S)).comp (Subgroup.inclusion hLS)).range ∧
      (Nat.card ((QuotientGroup.mk' (Subgroup.center ↥S)).comp (Subgroup.inclusion hLS)).range =
          60 ∨
        Nat.card ((QuotientGroup.mk' (Subgroup.center ↥S)).comp (Subgroup.inclusion hLS)).range =
          168) := by
  set f := (QuotientGroup.mk' (Subgroup.center ↥S)).comp (Subgroup.inclusion hLS)
  have hker : ∀ l : ↥L, f l = 1 → l ∈ Subgroup.center ↥L := fun l hl => by
    have hz : Subgroup.inclusion hLS l ∈ Subgroup.center ↥S := (QuotientGroup.eq_one_iff _).1 hl
    refine Subgroup.mem_center_iff.2 fun m => Subgroup.inclusion_injective hLS ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hz _
  have : Group.IsPerfect Qk := Group.IsPerfect.ofSurjective hφ
  have hQc : Subgroup.center Qk = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative Qk)
  have hkerφ : f.rangeRestrict.ker ≤ φ.ker := fun l hl => by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hl
    exact MonoidHom.center_le_ker φ hφ hQc (hker l hl)
  let φbar : ↥f.range →* Qk :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨φ, hkerφ⟩
  have hφbar : Function.Surjective φbar := fun x => by
    obtain ⟨l, rfl⟩ := hφ x
    exact ⟨f.rangeRestrict l, f.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨φ, hkerφ⟩ l⟩
  have hM1 : f.range ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hL1
    refine Group.IsPerfect.not_isMulCommutative ↥L (Subgroup.center_eq_top_iff.1 ?_)
    refine eq_top_iff.2 fun l _ => hker l ?_
    have hl : f l ∈ f.range := MonoidHom.mem_range.2 ⟨l, rfl⟩
    rwa [h, Subgroup.mem_bot] at hl
  obtain ⟨hF, ⟨e⟩⟩ := l2Field_and_nonempty_mulEquiv hp5 eS
  obtain ⟨hs, -, hc⟩ := L2OddGroup.isSimpleGroup_and_card_of_surjective hF e
    (Group.IsPerfect.range f) hM1 φbar hφbar hQ
  exact ⟨hs, hc⟩

theorem sl2Comp_facts {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) {t : Y} {S : Subgroup Y}
    (hI : CFSG.GH74.KGroups.L3Eps.InvData p Y t S)
    (eS : ↥S ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1))
    {L : Subgroup Y} (hLS : L ≤ S) (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    {Qk : Type} [Group Qk] [IsSimpleGroup Qk] (φ : ↥L →* Qk) (hφ : Function.Surjective φ)
    (hQ : (∃ n : ℕ, Even n ∧ 0 < n ∧
        Nonempty (Qk ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))) ∨
      (∃ n : ℕ, Odd n ∧
        Nonempty (Qk ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)))) :
    t ∈ L ∧
    (∀ N : Subgroup Y, N ≤ L → IsPGroup 2 N → (∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) →
      ∀ n ∈ N, ∀ s ∈ S, n * s = s * n) ∧
    (L = S → p = 5 ∨ p = 7) := by
  obtain ⟨hs, hc⟩ := isSimpleGroup_range_and_card hp5 eS hLS hL hL1 φ hφ hQ
  set f := (QuotientGroup.mk' (Subgroup.center ↥S)).comp (Subgroup.inclusion hLS)
  refine ⟨?_, ?_, ?_⟩
  ·
    have h2 : 2 ∣ Nat.card ↥L := Nat.dvd_trans
      (by rcases hc with h | h <;> rw [h] <;> norm_num) (Subgroup.card_range_dvd f)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hx1 : (x : Y) ≠ 1 := fun h => by
      rw [show x = 1 from Subtype.ext h, orderOf_one] at hx
      omega
    have hxx : (x : Y) * x = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx, pow_two] at h
      exact congrArg Subtype.val h
    rcases hI.involution x (hLS x.2) hxx with h | h
    · exact absurd h hx1
    · exact h ▸ x.2
  ·
    intro N hNL hN hnorm n hn s hs'
    have hN' : (N.subgroupOf L).Normal := ⟨fun x hx g => hnorm g g.2 x hx⟩
    have hMn : ((N.subgroupOf L).map f.rangeRestrict).Normal :=
      hN'.map _ f.rangeRestrict_surjective
    have hM2 : IsPGroup 2 ((N.subgroupOf L).map f.rangeRestrict) :=
      (hN.comap_subtype (K := L)).map _
    have hM : (N.subgroupOf L).map f.rangeRestrict = ⊥ := by
      refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun h => ?_
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hM2
      rw [h, Subgroup.card_top] at hk
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hk]
        rcases hc with h' | h' <;> rw [h'] <;> norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    have h1 := Subgroup.mem_map_of_mem f.rangeRestrict
      (show (⟨n, hNL hn⟩ : ↥L) ∈ N.subgroupOf L from hn)
    rw [hM, Subgroup.mem_bot] at h1
    have hz : Subgroup.inclusion hLS ⟨n, hNL hn⟩ ∈ Subgroup.center ↥S :=
      (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h1)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨s, hs'⟩)).symm
  ·
    intro hEq
    obtain ⟨hF, ⟨e⟩⟩ := l2Field_and_nonempty_mulEquiv hp5 eS
    have hsurj : Function.Surjective f := fun k => by
      obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) k
      exact ⟨⟨(s : Y), hEq ▸ s.2⟩, rfl⟩
    have hK := ivk_1_2b (GaloisField p 1) hF _ e
    rw [GaloisField.card p 1 one_ne_zero, pow_one] at hK
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, hK] at hc
    exact eq_five_or_seven_of_half hp5 hc

end CFSG.RankThree.PartTwo.Sec20.SL2Comp
