module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.UC2TenNine
public import CFSG.GH74.AS16.Notation1641

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_invertedIn_of_shape {L X : Subgroup G} {n r : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hXL : X ≤ L) (hXcard : Nat.card X = r) (hr : r.Prime) (hr2 : r ≠ 2) :
    UC22.F05.InvertedIn L X := by
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr1 : 1 < r := hr.one_lt
  have hXcard1 : 1 < Nat.card X := by rw [hXcard]; exact hr1
  have hnt : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hXcard1
  obtain ⟨x, hxX, hx1⟩ : ∃ x : G, x ∈ X ∧ x ≠ 1 := by
    obtain ⟨y, hy⟩ := exists_ne (1 : X)
    exact ⟨y, y.2, fun h => hy (Subtype.ext h)⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (pCore 2 ↥L)
  let xL : ↥L := ⟨x, hXL hxX⟩
  have hxL1 : xL ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hxLord : orderOf xL = r := by
    rw [Subgroup.orderOf_mk]
    have hdvd : orderOf x ∣ r := by
      rw [← hXcard]
      exact Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hxbar1 : π xL ≠ 1 := by
    intro h
    have hmem : xL ∈ pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
      exact h
    have hdvd : orderOf xL ∣ Nat.card ↥(pCore 2 ↥L) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(pCore 2 ↥L))).mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hm] at hdvd
    have hd1 : orderOf xL ≠ 1 := fun h => hxL1 (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    have hp2 : p = 2 := by
      have hpdvd : p ∣ 2 ^ m := hpd.trans hdvd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hp hpdvd)
    have h2 : 2 ∣ orderOf xL := by simpa [hp2] using hpd
    rw [hxLord] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2).symm
  have hxbarord : orderOf (π xL) = r := by
    have hdvd : orderOf (π xL) ∣ orderOf xL := orderOf_map_dvd π xL
    rw [hxLord] at hdvd
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxbar1
    · exact h
  obtain ⟨s, -, hsinv⟩ := exists_involution_inverts_of_shape hshape hr hr2 hxbarord
  obtain ⟨kL, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L) s
  have hkL : (kL : G) ∈ L := kL.2
  let Xbar : Subgroup (Bar2 L) := (X.subgroupOf L).map π
  have hdisj : X ⊓ pCoreOf 2 L = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hXcard]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(pCore 2 ↥L))).mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    have hpc : Nat.card ↥(CFSG.Open.pCoreOf 2 L) = 2 ^ m := by
      rw [CFSG.openPCoreOf_eq_map_pCore]
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hm
    rw [hpc]
    exact (Nat.coprime_two_left.mpr (hr.odd_of_ne_two hr2)).symm.pow_right m
  have hXbar_card : Nat.card Xbar = r := by
    have hker : (X.subgroupOf L) ⊓ π.ker = ⊥ := by
      rw [QuotientGroup.ker_mk']
      ext y
      constructor
      · intro hy
        have hy' : (y : G) ∈ X ⊓ CFSG.Open.pCoreOf 2 L := by
          refine ⟨Subgroup.mem_subgroupOf.mp hy.1, ?_⟩
          have hyk : y ∈ CFSG.pCore 2 ↥L := hy.2
          rw [CFSG.openPCoreOf_eq_map_pCore]
          exact Subgroup.mem_map_of_mem _ hyk
        rw [hdisj, Subgroup.mem_bot] at hy'
        exact Subtype.ext (by simpa using hy')
      · intro hy
        rw [Subgroup.mem_bot] at hy
        subst hy
        exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    have h := CFSG.Walter.Suzuki.card_map_of_inf_ker_eq_bot π (X.subgroupOf L) hker
    rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv, hXcard]
  have hpow : ∀ y (hy : y ∈ X), ∃ m : ℤ, (π ⟨y, hXL hy⟩) = (π xL) ^ m := by
    intro y hy
    have hybar_mem : π ⟨y, hXL hy⟩ ∈ Xbar :=
      Subgroup.mem_map_of_mem _ hy
    have hxbar_mem : π xL ∈ Xbar := Subgroup.mem_map_of_mem _ hxX
    have hmem := mem_zpowers_of_prime_card (G := ↥Xbar) hXbar_card
      (g := ⟨π xL, hxbar_mem⟩) (g' := ⟨π ⟨y, hXL hy⟩, hybar_mem⟩)
      (by intro h; exact hxbar1 (congrArg Subtype.val h))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨m, (congrArg Subtype.val hm).symm⟩
  have hconjz : ∀ (a b : Bar2 L) (n : ℤ), a * b ^ n * a⁻¹ = (a * b * a⁻¹) ^ n := by
    intro a b n
    change MulAut.conj a (b ^ n) = (MulAut.conj a b) ^ n
    exact map_zpow (MulAut.conj a) b n
  have hkinv : ∀ y ∈ X, (kL : G) * y * (kL : G)⁻¹ * y ∈ pCoreOf 2 L := by
    intro y hy
    let yL : ↥L := ⟨y, hXL hy⟩
    let z : G := (kL : G) * y * (kL : G)⁻¹ * y
    have hzL : z ∈ L := L.mul_mem (L.mul_mem (L.mul_mem hkL (hXL hy)) (L.inv_mem hkL)) (hXL hy)
    have hyinv : s * (π yL) * s⁻¹ = (π yL)⁻¹ := by
      obtain ⟨m, hm⟩ := hpow y hy
      rw [hm, ← hk]
      calc π kL * (π xL) ^ m * (π kL)⁻¹
          = (π kL * π xL * (π kL)⁻¹) ^ m := hconjz _ _ _
        _ = (s * π xL * s⁻¹) ^ m := by rw [hk]
        _ = ((π xL)⁻¹) ^ m := by rw [hsinv]
        _ = ((π xL) ^ m)⁻¹ := by rw [inv_zpow]
    have hq : π ⟨z, hzL⟩ = 1 := by
      have hprod : (⟨z, hzL⟩ : ↥L) = kL * yL * kL⁻¹ * yL := Subtype.ext rfl
      rw [hprod]
      calc π (kL * yL * kL⁻¹ * yL) = π kL * π yL * (π kL)⁻¹ * π yL := by
            simp only [map_mul, map_inv]
        _ = s * (π yL) * s⁻¹ * (π yL) := by rw [hk]
        _ = (π yL)⁻¹ * (π yL) := by rw [hyinv]
        _ = 1 := inv_mul_cancel (π yL)
    have hmem : (⟨z, hzL⟩ : ↥L) ∈ pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
      exact hq
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.mem_map_of_mem _ hmem
  exact exists_inverted_of_inverts_mod_pCore hXL hXcard hr hr2 hkL hkinv

theorem seventeen_fiftyfive_stepA_core (D : Data G) (h109 : Inputs1719.UC2_10_9 D)
    {V₀ V : Subgroup G} (h3 : R17_3At D V₀ V) (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hLM : L ≤ D.M) (hLN : (L.subgroupOf D.M).Normal)
    {n : ℕ} (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {s : ℕ} (hso : Odd s) (hsn : s ∣ n)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    {X : Subgroup G} (hXL : X ≤ L) (hXcard : Nat.card X = r)
    (heq : conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ D.M} = conjSetOf D.M X) :
    V₀ = ⊥ ∧ ∃ X' : Subgroup G, X' ≤ CFSG.Quasithin.perfectCore L ∧
      X' ≤ Subgroup.normalizer (D.T : Set G) ∧ Nat.card X' = r ∧ UC6.InU D.M X' ∧
      UniqueMax D.M (CFSG.Quasithin.perfectCore L ⊔ D.T) := by
  have hInU : UC6.InU D.M X := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.inU_iff_mem_uniqueSet]
    exact mem_uniqueSet_of_conjSetOf_eq D h3 hLM hLN hshape hso hr hrdvd hXL hXcard heq
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLN
  have hTL : D.T ≤ Subgroup.normalizer (L : Set G) := D.sylowM.le.trans hML
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ D.T) L := by
    have hM' : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
      CFSG.GH74.AS16.isSylowTwoOf_iff.2 D.sylowM
    have := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hM' hLM hML
    rwa [inf_comm] at this
  obtain ⟨a, haL, hX'T⟩ : ∃ a ∈ L, X.map (MulAut.conj a).toMonoidHom ≤
      Subgroup.normalizer (D.T : Set G) := by
    rcases hshape with h2 | hsz
    · exact exists_conj_le_normalizer_T_of_isL2_bar2 h2 hTL hT2 hSyl hso hsn hr hrdvd hXL hXcard
    · exact exists_conj_le_normalizer_T_of_isSz_bar2 hsz hTL hT2 hSyl hso hsn hr hrdvd hXL hXcard
  let X' : Subgroup G := X.map (MulAut.conj a).toMonoidHom
  have hX'L : X' ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem haL (hXL hx)) (L.inv_mem haL)
  have hX'card : Nat.card X' = r := by
    rw [show Nat.card X' = Nat.card X from
      Subgroup.card_map_of_injective (MulAut.conj a).injective, hXcard]
  have hInU' : UC6.InU D.M X' :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.inU_iff_mem_uniqueSet.2
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conj_mem_uniqueSet
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.inU_iff_mem_uniqueSet.1 hInU) (hLM haL))
  have hr2 : r ≠ 2 := by
    intro h2
    subst h2
    have hodd : Odd (2 ^ s - 1) := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by
      obtain ⟨k, hk⟩ := hso
      omega)
    exact hodd.not_two_dvd_nat hrdvd
  obtain ⟨hPcalC, hPN, hPshape, hPmap⟩ := perfectCore_of_isL2_or_isSz_1755 hLM hLN hshape
  have hPK : X' ≤ CFSG.Quasithin.perfectCore L :=
    le_perfectCore_of_map_eq_top hPmap rfl (hr.odd_of_ne_two hr2) hX'L hX'card
  have hinvP : UC22.F05.InvertedIn (CFSG.Quasithin.perfectCore L) X' :=
    exists_invertedIn_of_shape hPshape hPK hX'card hr hr2
  have hUTP : UniqueMax D.M (CFSG.Quasithin.perfectCore L ⊔ D.T) :=
    uniqueMax_of_inverted_uc2_10_9 h109 hso hr hrdvd
      (le_inf (hPK.trans hPcalC.1.le) hX'T) hX'card hInU' hPK hPcalC.1.le hinvP
  exact ⟨v0_eq_bot_of_uc2_10_9_of_normal h109 hV hPcalC hPN hUTP hso hr hrdvd
      hPK hX'T hX'card hInU', X', hPK, hX'T, hX'card, hInU', hUTP⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
