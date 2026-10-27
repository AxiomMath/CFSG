module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveKGpU
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveKGpAutS
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveKGpAutD
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312K
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LargeExtraspecial.S8DimB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {n : ℕ}

private theorem isSimpleGroup_of_isSz {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : CFSG.Quasithin.IsSz n X) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n h).2

private theorem false_of_isSimpleGroup_of_isMulCommutative {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hcomm : IsMulCommutative X) {n : ℕ} (hn : 1 < n)
    (hcard : Nat.card X = 2 ^ n) : False := by
  haveI : IsMulCommutative X := hcomm
  have hprime : (Nat.card X).Prime := (Group.is_simple_iff_prime_card (α := X)).mp hsimple
  have hpow : (2 ^ n).Prime := by rwa [← hcard]
  exact absurd (Nat.Prime.eq_one_of_pow hpow) (by omega)

private theorem fusionOddCore_eq_bot_of_sq_eq_one {X : Type} [Group X] [Finite X]
    (hsq : ∀ x : X, x ^ 2 = 1) : fusionOddCore X = ⊥ := by
  rw [CFSG.Open.fusionOddCore, sSup_eq_bot]
  intro N hN
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq x)
  have hdvdN : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have h12 : orderOf x = 1 ∨ orderOf x = 2 := by omega
  rcases h12 with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hN.2) (even_iff_two_dvd.mpr (h2 ▸ hdvdN))

private theorem false_of_isSimpleGroup_of_isMulCommutative_of_dvd {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hcomm : IsMulCommutative X) {n : ℕ} (hn : 1 < n)
    (hdvd : 2 ^ n ∣ Nat.card X) : False := by
  haveI : IsMulCommutative X := hcomm
  have hprime : (Nat.card X).Prime := (Group.is_simple_iff_prime_card (α := X)).mp hsimple
  have h2n : 1 < 2 ^ n := by
    calc 1 < 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hne : 2 ^ n ≠ 1 := by omega
  have heq : 2 ^ n = Nat.card X :=
    (hprime.eq_one_or_self_of_dvd (2 ^ n) hdvd).resolve_left hne
  have hpow : (2 ^ n).Prime := heq ▸ hprime
  exact absurd (Nat.Prime.eq_one_of_pow hpow) (by omega)

private theorem coprime_two_card_fusionOddCore (X : Type) [Group X] [Finite X] :
    Nat.Coprime 2 (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold CFSG.Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext N
    exact and_congr Iff.rfl Nat.coprime_two_left.symm
  rw [h]
  exact CFSG.pPrimeCore_coprime_card

private theorem normal_isPGroup_eq_bot_of_index_two {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} (hgen : normalClosure (Y : Set X) = ⊤)
    (hsup : Y ⊔ fusionOddCore X = ⊤) (hcardY : Nat.card Y = 2)
    (hOddO : Odd (Nat.card (fusionOddCore X))) (hOne : Nat.card (fusionOddCore X) ≠ 1) :
    ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := by
  have hnotnormal : ¬ Y.Normal := by
    intro hYN
    have hYtop : Y = ⊤ := by rw [← hgen, Subgroup.normalClosure_eq_self Y]
    have hOle : fusionOddCore X ≤ Y := by rw [hYtop]; exact le_top
    have hdvdO : Nat.card (fusionOddCore X) ∣ Nat.card Y := Subgroup.card_dvd_of_le hOle
    rw [hcardY] at hdvdO
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvdO with h | h
    · exact hOne h
    · rw [h] at hOddO
      norm_num at hOddO
  intro N hN hN2
  have hcop : Nat.Coprime 2 (Nat.card (fusionOddCore X)) := Nat.coprime_two_left.mpr hOddO
  have hprod : (fusionOddCore X : Set X) * (Y : Set X) = Set.univ := by
    rw [← Subgroup.normal_mul, sup_comm, hsup]
    exact Subgroup.coe_top
  have hleY : N ≤ Y :=
    (CFSG.pCore_le_of_coprime_normal_mul_eq_univ 2 Nat.prime_two (fusionOddCore X) Y
      hcop hprod).1 N hN hN2
  by_contra hNne
  have h1lt : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
  have hdvd : Nat.card N ∣ 2 := by
    have := Subgroup.card_dvd_of_le hleY
    rwa [hcardY] at this
  have hcardN : Nat.card N = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · omega
    · exact h
  exact hnotnormal (Subgroup.eq_of_le_of_card_ge hleY (by rw [hcardN, hcardY]) ▸ hN)

theorem Shape166.odd_card_center (hY : IsElemAbelian 2 Y)
    (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y n) :
    Odd (Nat.card (center X)) := by
  obtain ⟨hcardY, hcase⟩ := hX
  have hdvd : 2 ^ n ∣ Nat.card X := by
    rw [← hcardY, ← Subgroup.card_top (G := X)]
    exact Subgroup.card_dvd_of_le le_top
  rcases hcase with ⟨hn1, hPSL | hSz | hPSU⟩ | ⟨hn1, hsup, p, hp, hO⟩
  · have hsimple := CFSG.QuasithinUnique.Unc25G2.A312Sub.isSimpleGroup_of_stated hPSL
    have hcenter : Subgroup.center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
      · exact h
      · exfalso
        exact false_of_isSimpleGroup_of_isMulCommutative_of_dvd hsimple
          (Subgroup.center_eq_top_iff.mp h) hn1 hdvd
    rw [hcenter]
    norm_num
  · have hsimple := isSimpleGroup_of_isSz hSz
    have hcenter : Subgroup.center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
      · exact h
      · exfalso
        exact false_of_isSimpleGroup_of_isMulCommutative_of_dvd hsimple
          (Subgroup.center_eq_top_iff.mp h) hn1 hdvd
    rw [hcenter]
    norm_num
  · rcases (Nat.dvd_prime Nat.prime_three).mp hPSU.2.2 with h | h <;> rw [h] <;> norm_num
  · have hcardY2 : Nat.card Y = 2 := by
      rw [hcardY, hn1]
      norm_num
    have hOddO : Odd (Nat.card (fusionOddCore X)) :=
      Nat.coprime_two_left.mp (coprime_two_card_fusionOddCore X)
    have hOne : Nat.card (fusionOddCore X) ≠ 1 := by
      rcases hO with h | ⟨hE, h⟩
      · rw [h]; exact hp.ne_one
      · rw [h]
        intro hp3
        have hp2 : 2 ≤ p := hp.two_le
        have h8 : 8 ≤ p ^ 3 := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
        omega
    exact CFSG.CGT.Timmesfeld75.odd_card_center fun N hN hN2 =>
      normal_isPGroup_eq_bot_of_index_two hgen hsup hcardY2 hOddO hOne N hN hN2

private theorem card_eq_two_mul_oddCore {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (hsup : Y ⊔ fusionOddCore X = ⊤) (hcardY : Nat.card Y = 2)
    (hYO : Y ⊓ fusionOddCore X = ⊥) :
    Nat.card X = 2 * Nat.card (fusionOddCore X) := by
  have h := CFSG.LargeExtraspecial.S8.card_sup_mul_card_inf_of_normal' (fusionOddCore X) Y
  rw [show fusionOddCore X ⊔ Y = Y ⊔ fusionOddCore X from sup_comm _ _, hsup,
    Subgroup.card_top, inf_comm, hYO, Subgroup.card_bot, mul_one, hcardY] at h
  omega

private theorem conj_inf_normalizer_eq_bot_of_index_two {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} (hsup : Y ⊔ fusionOddCore X = ⊤) (hcardY : Nat.card Y = 2)
    (hOddO : Odd (Nat.card (fusionOddCore X))) {W : Subgroup X} (hWY : W ≤ Y) (hW : W ≠ ⊥)
    {x : X} (hx : conjSubgroup Y x ≠ Y) :
    conjSubgroup Y x ⊓ normalizer (W : Set X) = ⊥ := by
  have hYO : Y ⊓ fusionOddCore X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hdvdY : orderOf z ∣ 2 := by
      have h := Subgroup.orderOf_dvd_natCard Y hz.1
      rwa [hcardY] at h
    have hdvdO : orderOf z ∣ Nat.card (fusionOddCore X) :=
      Subgroup.orderOf_dvd_natCard (fusionOddCore X) hz.2
    have hOddZ : Odd (orderOf z) := Odd.of_dvd_nat hOddO hdvdO
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvdY with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hOddZ; norm_num at hOddZ
  have hcardX := card_eq_two_mul_oddCore hsup hcardY hYO
  have hWYeq : W = Y := by
    have hdvd : Nat.card W ∣ 2 := by
      have := Subgroup.card_dvd_of_le hWY
      rwa [hcardY] at this
    have h1 : 1 < Nat.card W := (Subgroup.one_lt_card_iff_ne_bot W).mpr hW
    have hcardW : Nat.card W = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · omega
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hWY (by rw [hcardW, hcardY])
  rw [hWYeq]
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hcardK : Nat.card (conjSubgroup Y x) = 2 := by
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hcardY]
  have hzK : z ∈ conjSubgroup Y x := hz.1
  have hzN : z ∈ normalizer (Y : Set X) := hz.2
  have hordz : orderOf z = 2 := by
    have hdvd : orderOf z ∣ 2 := by
      have h := Subgroup.orderOf_dvd_natCard (conjSubgroup Y x) hzK
      rwa [hcardK] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hzpK : Subgroup.zpowers z = conjSubgroup Y x := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hzK
    · rw [Nat.card_zpowers, hordz, hcardK]
  have hKle : conjSubgroup Y x ≤ normalizer (Y : Set X) := by
    rw [← hzpK]
    exact Subgroup.zpowers_le.mpr hzN
  have hinf : Y ⊓ conjSubgroup Y x = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    by_contra hu1
    have hordY : orderOf u = 2 := by
      have hdvd : orderOf u ∣ 2 := by
        have h := Subgroup.orderOf_dvd_natCard Y hu.1
        rwa [hcardY] at h
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hu1
      · exact h
    have hzpY : Subgroup.zpowers u = Y := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact hu.1
      · rw [Nat.card_zpowers, hordY, hcardY]
    have hzpK' : Subgroup.zpowers u = conjSubgroup Y x := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact hu.2
      · rw [Nat.card_zpowers, hordY, hcardK]
    exact hx (by rw [← hzpK', hzpY])
  have hprod := CFSG.LargeExtraspecial.S8.card_sup_mul_card_inf_of_le_normalizer' hKle
  rw [hinf, Subgroup.card_bot, mul_one, hcardY, hcardK] at hprod
  norm_num at hprod
  have hdvd4 : 4 ∣ Nat.card X := by
    rw [← hprod, ← Subgroup.card_top (G := X)]
    exact Subgroup.card_dvd_of_le le_top
  refine absurd hdvd4 ?_
  intro h4
  rw [hcardX] at h4
  obtain ⟨k, hk⟩ := h4
  have h2dvd : 2 ∣ Nat.card (fusionOddCore X) := ⟨k, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hOddO) (even_iff_two_dvd.mpr h2dvd)

theorem Shape166.conj_inf_normalizer_eq_bot_of_isPSL
    {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} {n : ℕ} (hPSL : CFSG.Quasithin.IsPSL 2 2 n X) (hY : IsElemAbelian 2 Y)
    (hcardY : Nat.card Y = 2 ^ n) {W : Subgroup X} (hWY : W ≤ Y) (hW : W ≠ ⊥) {x : X}
    (hx : conjSubgroup Y x ≠ Y) :
    conjSubgroup Y x ⊓ normalizer (W : Set X) = ⊥ := by
  have hB : BenderType X n 1 1 := rankOne_benderType_psl hPSL
  haveI : IsSimpleGroup X := hB.isSimple
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := n) hcardY
  obtain ⟨S, hYS⟩ := hY2.exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hScard : Nat.card (S : Subgroup X) = 2 ^ n := by
    have := hc.card_eq
    rw [pow_one] at this
    exact this
  have hSY : (S : Subgroup X) = Y :=
    (Subgroup.eq_of_le_of_card_ge hYS (by rw [hcardY, hScard])).symm
  have hSW : (S : Subgroup X) ≤ normalizer (W : Set X) :=
    le_normalizer_of_commute fun a ha b hb => by
      have haY : a ∈ Y := hSY ▸ hWY ha
      have hbY : b ∈ Y := hSY ▸ hb
      exact congrArg Subtype.val (hY.1.is_comm.comm ⟨a, haY⟩ ⟨b, hbY⟩)
  have hNne : normalizer (W : Set X) ≠ ⊤ := by
    intro htop
    have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW h
    · have hSt : (S : Subgroup X) = ⊤ := by
        rw [hSY]
        exact top_le_iff.mp (h ▸ hWY)
      have hb : t ∈ CFSG.GH74.Uniqueness.Bender.borel (⊤ : Subgroup X) := by
        rw [CFSG.GH74.Uniqueness.Bender.borel, Subgroup.normalizer_eq_top]
        trivial
      exact hc.not_mem (hSt ▸ hb)
  have hYx2 : IsPGroup 2 (conjSubgroup Y x) := by
    apply IsPGroup.of_card (n := n)
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hcardY]
  have h1 : conjSubgroup Y x ⊓ normalizer (W : Set X) ≤
      conjSubgroup Y x ⊓ normalizer (S : Set X) :=
    inf_le_inf_left _ (hc.le_borel_of_le hSW hNne)
  have h2 : conjSubgroup Y x ⊓ normalizer (S : Set X) =
      conjSubgroup Y x ⊓ (S : Subgroup X) :=
    IsPGroup.inf_normalizer_sylow hYx2 S
  have hYxS : ((x⁻¹ • S : Sylow 2 X) : Subgroup X) = conjSubgroup Y x := by
    rw [Sylow.coe_subgroup_smul, conjSubgroup, hSY]
    rfl
  have hSne : S ≠ x⁻¹ • S := by
    intro heq
    apply hx
    have hsub : ((x⁻¹ • S : Sylow 2 X) : Subgroup X) = Y := by rw [← heq, hSY]
    rw [← hYxS, hsub]
  have h3 : conjSubgroup Y x ⊓ (S : Subgroup X) = ⊥ := by
    rw [hSY, inf_comm, ← hYxS]
    have hti := CFSG.Quasithin.Stroth.BenderType.sylowTwoTI hB S (x⁻¹ • S) hSne
    rwa [hSY] at hti
  rw [eq_bot_iff] at h3 ⊢
  exact h1.trans (h2.trans_le h3)

theorem Shape166.conj_inf_normalizer_eq_bot_of_isSz
    {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} {n : ℕ} (hSz : CFSG.Quasithin.IsSz n X) (hY : IsElemAbelian 2 Y)
    (hcardY : Nat.card Y = 2 ^ n) {W : Subgroup X} (hWY : W ≤ Y) (hW : W ≠ ⊥) {x : X}
    (hx : conjSubgroup Y x ≠ Y) :
    conjSubgroup Y x ⊓ normalizer (W : Set X) = ⊥ := by
  have hB : BenderType X n 2 1 := rankOne_benderType_sz hSz
  haveI : IsSimpleGroup X := hB.isSimple
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := n) hcardY
  obtain ⟨S, hYS⟩ := hY2.exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hYroot : Y ≤ rootCenter (S : Subgroup X) :=
    hc.elemAbelian_le_rootCenter hYS fun z hz => by
      have := hY.2 z hz
      simpa [sq] using this
  have hYrootEq : Y = rootCenter (S : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hYroot (by rw [hcardY, hc.card_center])
  have hSW : (S : Subgroup X) ≤ normalizer (W : Set X) := by
    refine le_normalizer_of_commute fun a ha b hb => ?_
    have haZ : a ∈ rootCenter (S : Subgroup X) := by
      rw [← hYrootEq]
      exact hWY ha
    exact (Subgroup.mem_centralizer_iff.mp haZ.2 b hb).symm
  have hNne : normalizer (W : Set X) ≠ ⊤ := by
    intro htop
    have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW h
    · have hYtop : Y = ⊤ := top_le_iff.mp (h ▸ hWY)
      have hroot_top : rootCenter (S : Subgroup X) = ⊤ := by rw [← hYrootEq]; exact hYtop
      have hSt : (S : Subgroup X) = ⊤ :=
        top_le_iff.mp (hroot_top ▸ rootCenter_le (S : Subgroup X))
      have hb : t ∈ CFSG.GH74.Uniqueness.Bender.borel (⊤ : Subgroup X) := by
        rw [CFSG.GH74.Uniqueness.Bender.borel, Subgroup.normalizer_eq_top]
        trivial
      exact hc.not_mem (hSt ▸ hb)
  have hYx2 : IsPGroup 2 (conjSubgroup Y x) := by
    apply IsPGroup.of_card (n := n)
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hcardY]
  have h1 : conjSubgroup Y x ⊓ normalizer (W : Set X) ≤
      conjSubgroup Y x ⊓ normalizer (S : Set X) :=
    inf_le_inf_left _ (hc.le_borel_of_le hSW hNne)
  have h2 : conjSubgroup Y x ⊓ normalizer (S : Set X) =
      conjSubgroup Y x ⊓ (S : Subgroup X) :=
    IsPGroup.inf_normalizer_sylow hYx2 S
  let S' : Sylow 2 X := S.mapSurjective (f := (MulAut.conj x⁻¹).toMonoidHom)
    (MulAut.conj x⁻¹).surjective
  have hS'coe : (S' : Subgroup X) = conjSubgroup (S : Subgroup X) x := by
    simp [S', conjSubgroup]
  have hYxroot : conjSubgroup Y x = rootCenter (S' : Subgroup X) := by
    rw [hS'coe, conjSubgroup, conjSubgroup, hYrootEq, ← rootCenter_map]
  have hSne : S ≠ S' := by
    intro heq
    apply hx
    rw [hYxroot, ← heq, hYrootEq]
  have h3 : conjSubgroup Y x ⊓ (S : Subgroup X) = ⊥ := by
    rw [hYxroot]
    have hle : rootCenter (S' : Subgroup X) ⊓ (S : Subgroup X) ≤
        (S' : Subgroup X) ⊓ (S : Subgroup X) :=
      le_inf (inf_le_left.trans (rootCenter_le _)) inf_le_right
    have hle2 : rootCenter (S' : Subgroup X) ⊓ (S : Subgroup X) ≤ ⊥ := by
      calc rootCenter (S' : Subgroup X) ⊓ (S : Subgroup X)
          ≤ (S' : Subgroup X) ⊓ (S : Subgroup X) := hle
        _ = (S : Subgroup X) ⊓ (S' : Subgroup X) := inf_comm _ _
        _ = ⊥ := CFSG.Quasithin.Stroth.BenderType.sylowTwoTI hB S S' hSne
    exact le_bot_iff.mp hle2
  rw [eq_bot_iff] at h3 ⊢
  exact h1.trans (h2.trans_le h3)

theorem Shape166.conj_inf_normalizer_eq_bot
    (hY : IsElemAbelian 2 Y)
    (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y n) {W : Subgroup X}
    (hWY : W ≤ Y) (hW : W ≠ ⊥) {x : X} (hx : conjSubgroup Y x ≠ Y) :
    conjSubgroup Y x ⊓ normalizer (W : Set X) = ⊥ := by
  obtain ⟨hcardY, hcase⟩ := hX
  rcases hcase with ⟨hn1, hPSL | hSz | hPSU⟩ | ⟨hn1, hsup, p, hp, hO⟩
  · exact Shape166.conj_inf_normalizer_eq_bot_of_isPSL hPSL hY hcardY hWY hW hx
  · exact Shape166.conj_inf_normalizer_eq_bot_of_isSz hSz hY hcardY hWY hW hx
  · exact Shape166.conj_inf_normalizer_eq_bot_of_isPSUGp hPSU hY hcardY hWY hW hx
  · have hcardY2 : Nat.card Y = 2 := by
      rw [hcardY, hn1]
      norm_num
    have hOddO : Odd (Nat.card (fusionOddCore X)) :=
      Nat.coprime_two_left.mp (coprime_two_card_fusionOddCore X)
    exact conj_inf_normalizer_eq_bot_of_index_two hsup hcardY2 hOddO hWY hW hx

theorem Shape166.exists_conj_ne (hY : IsElemAbelian 2 Y)
    (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y n) :
    ∃ x : X, conjSubgroup Y x ≠ Y := by
  by_contra h
  push Not at h
  have hYnorm : Y.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    have h1 := h g⁻¹
    simpa [conjSubgroup, inv_inv] using h1
  have hYtop : Y = ⊤ := by
    rw [← hgen, Subgroup.normalClosure_eq_self Y]
  have hcomm : IsMulCommutative X := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have h' := hY.1.is_comm.comm ⟨a, by rw [hYtop]; trivial⟩ ⟨b, by rw [hYtop]; trivial⟩
    exact congrArg Subtype.val h'
  have hsq : ∀ a : X, a ^ 2 = 1 := by
    intro a
    have h' := hY.2 a (by rw [hYtop]; trivial)
    simpa [pow_two] using h'
  obtain ⟨hcardY, hcase⟩ := hX
  have hcardX : Nat.card X = 2 ^ n := by
    rw [← Subgroup.card_top (G := X), ← hYtop, hcardY]
  rcases hcase with ⟨hn1, hPSL | hSz | hPSU⟩ | ⟨hn1, hsup, p, hp, hO⟩
  · exact false_of_isSimpleGroup_of_isMulCommutative
      (CFSG.QuasithinUnique.Unc25G2.A312Sub.isSimpleGroup_of_stated hPSL) hcomm hn1 hcardX
  · exact false_of_isSimpleGroup_of_isMulCommutative
      (isSimpleGroup_of_isSz hSz) hcomm hn1 hcardX
  · haveI : IsMulCommutative X := hcomm
    have hbot : commutator X = ⊥ := commutator_eq_bot X
    have htopbot : (⊤ : Subgroup X) = ⊥ := by rw [← hPSU.1]; exact hbot
    have hcard1 : Nat.card X = 1 := by
      rw [← Subgroup.card_top (G := X), htopbot, Subgroup.card_bot]
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hbotO : fusionOddCore X = ⊥ := fusionOddCore_eq_bot_of_sq_eq_one hsq
    have hcardO : Nat.card (fusionOddCore X) = 1 := by
      rw [hbotO, Subgroup.card_bot]
    rcases hO with h | ⟨hE, hcard3⟩
    · rw [hcardO] at h
      exact hp.ne_one h.symm
    · rw [hcardO] at hcard3
      have hp2 : 2 ≤ p := hp.two_le
      have h8 : 8 ≤ p ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
      omega

theorem Shape166.exists_eq_conj_of_isPSL
    {X : Type} [Group X] [Finite X] {Y : Subgroup X} {n : ℕ}
    (hPSL : CFSG.Quasithin.IsPSL 2 2 n X) (hY : IsElemAbelian 2 Y)
    (hcardY : Nat.card Y = 2 ^ n) (α : MulAut X) (hα : α * α = 1)
    (hαY : ∀ y ∈ Y, α y = y) : ∃ y ∈ Y, α = MulAut.conj y := by
  have hB : BenderType X n 1 1 := rankOne_benderType_psl hPSL
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := n) hcardY
  obtain ⟨S, hYS⟩ := hY2.exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hScard : Nat.card (S : Subgroup X) = 2 ^ n := by
    have := hc.card_eq
    rw [pow_one] at this
    exact this
  have hSY : (S : Subgroup X) = Y :=
    (Subgroup.eq_of_le_of_card_ge hYS (by rw [hcardY, hScard])).symm
  obtain ⟨r, hr, hσ⟩ := hB.lemma_3_6_a S α fun x hx => hαY x (hSY ▸ hx)
  exact ⟨r, hSY ▸ rootCenter_le (S : Subgroup X) hr, MulEquiv.ext fun k => hσ k⟩

theorem Shape166.exists_eq_conj (hY : IsElemAbelian 2 Y)
    (hgen : normalClosure (Y : Set X) = ⊤) (hX : Shape166 X Y n)
    (hcase : CFSG.Quasithin.IsPSL 2 2 n X ∨ CFSG.Quasithin.IsSz n X ∨
      (n = 1 ∧ (Nat.card (fusionOddCore X)).Prime))
    (α : MulAut X) (hα : α * α = 1) (hαY : ∀ y ∈ Y, α y = y) :
    ∃ y ∈ Y, α = MulAut.conj y := by
  have hcardY := hX.1
  rcases hcase with hPSL | hSz | ⟨hn1, hPrime⟩
  · exact Shape166.exists_eq_conj_of_isPSL hPSL hY hcardY α hα hαY
  · exact Shape166.exists_eq_conj_of_isSz hSz hY hcardY α hα hαY
  · exact Shape166.exists_eq_conj_of_index_two hY hgen hX hn1 hPrime α hα hαY

end CFSG.LocalAnalysis.WeakClosure81

end
