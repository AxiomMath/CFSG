module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.LRed6Mod
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearG2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank EmptyFaithfulMultiple.FFL
open scoped commutatorElement

namespace LRed8

theorem card_of_surj_simple {G L : Type} [Group G] [Group L] [IsSimpleGroup G] (π : G →* L)
    (hπ : Function.Surjective π) : Nat.card L = 1 ∨ Nat.card L = Nat.card G := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · right
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hk
    exact (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)).symm
  · left
    have : Subsingleton L := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hπ x
      obtain ⟨b, rfl⟩ := hπ y
      have ha : a ∈ π.ker := hk ▸ Subgroup.mem_top a
      have hb : b ∈ π.ker := hk ▸ Subgroup.mem_top b
      rw [MonoidHom.mem_ker] at ha hb
      rw [ha, hb]⟩
    exact Nat.card_unique

theorem not_naturalList2_of_card_2520
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hL : Nat.card ↥L = 2520) : ¬ B51NaturalList2 L U Z := by
  have hS : LRed6.InS (Nat.card ↥L) := Or.inr (Or.inr (Or.inl hL))
  rintro (⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨F, _, _, hF, π, hπ⟩ | ⟨F, _, _, hF, π, hπ⟩)
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hF] at hc
    exact LRed6.sl2_num hS hc.symm
  · have hc := card_eq_of_nat_realizes1527d hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX : Nat.card ↥(StatedSp 2 F) =
        (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
      rw [hI, Finset.prod_pair (by norm_num)]
    rw [hX] at hc
    exact LRed6.sp4_num hS hc.symm
  · have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
      have := FFC.charP_two_of_card_pow hF
      exact (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hF, hF] at hcard
    exact LRed6.g2_num hS hcard.symm
  · have h1 : Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 6)) :=
      Nat.card_le_card_of_surjective π hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  · have hs : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 8))
    rcases card_of_surj_simple (G := ↥(alternatingGroup (Fin 8))) π hπ.1 with h1 | h1
    · omega
    · rw [card_alternatingGroup1527d 8 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
      omega
  · have hF2 : Nat.card F = 2 := by simpa using hF
    have h1 : Nat.card ↥L ∣ Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
      Subgroup.card_dvd_of_surjective hπ.1
    rw [card_commutator_quasithinG2 hF2, hL] at h1
    norm_num at h1
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hF] at hc
    exact LRed6.sl3_num hS hc.symm

end LRed8

end CFSG.Quasithin
