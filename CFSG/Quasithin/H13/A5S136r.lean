module

public import CFSG.Quasithin.H13.A5S136q
public import CFSG.Quasithin.EmptyFaithful.LRed3Four
public import CFSG.Quasithin.Background.B69SL2
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem card_statedSL_two {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem card_statedSL_three {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 3 K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three K

theorem card_statedSL_five_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 5 K) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK

theorem card_statedSp_two {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSp 2 K) =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 2,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem sl3_ne_20160 (q : ℕ) : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≠ 20160 := by
  intro h
  rcases Nat.lt_or_ge q 4 with hlt | hge
  · interval_cases q <;> norm_num at h
  · have h1 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hge 3
    have h2 : 4 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
    have h3 : 4 ^ 3 * ((4 ^ 2 - 1) * (4 ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h1 1))
    norm_num at h3
    omega

theorem sp4_ne_20160 {q : ℕ} (hq : 2 ≤ q) : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ≠ 20160 := by
  intro h
  rcases Nat.lt_or_ge q 3 with hlt | hge
  · interval_cases q
    norm_num at h
  · have h1 : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hge 4
    have h2 : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
    have h3 : 3 ^ 4 * ((3 ^ 2 - 1) * (3 ^ 4 - 1)) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h1 1))
    norm_num at h3
    omega

theorem two_pow_sq (n : ℕ) : (2 ^ n) ^ 2 = 4 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

section Types

variable {Y : Type} [Group Y]

theorem isSimpleGroup_of_isPSL34 (h : IsPSL 3 2 2 Y) : IsSimpleGroup Y :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h).2

theorem card_of_isPSL34 (h : IsPSL 3 2 2 Y) : Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem center_eq_bot_of_isPSL34 (h : IsPSL 3 2 2 Y) : Subgroup.center Y = ⊥ := by
  have := isSimpleGroup_of_isPSL34 h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hc | hc
  · exact hc
  · exfalso
    have hcomm : ∀ a b : Y, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b) a)
    let _ : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := Y)
    rw [card_of_isPSL34 h] at hp
    norm_num at hp

theorem card_quot_center_of_isPSL34 (h : IsPSL 3 2 2 Y) :
    Nat.card (Y ⧸ Subgroup.center Y) = 20160 := by
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isPSL34 h)).toEquiv,
    Nat.card_congr (QuotientGroup.quotientBot (G := Y)).toEquiv, card_of_isPSL34 h]

theorem isQuasisimple_of_isPSL34 (h : IsPSL 3 2 2 Y) : CFSG.IsQuasisimple Y := by
  have := isSimpleGroup_of_isPSL34 h
  refine CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup ?_
  by_contra hcon
  push Not at hcon
  have hZ := center_eq_bot_of_isPSL34 h
  have htop : Subgroup.center Y = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.mpr fun y => hcon y x
  rw [htop] at hZ
  have := card_of_isPSL34 h
  have h1 : Nat.card Y = 1 := by
    rw [← Subgroup.card_top (G := Y), hZ, Subgroup.card_bot]
  omega

theorem card_eq_of_surjective_of_isSimpleGroup {Γ : Type} [Group Γ] [IsSimpleGroup Γ]
    [Nontrivial Y] (π : Γ →* Y) (hπ : Function.Surjective π) : Nat.card Y = Nat.card Γ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp h
    exact (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)).symm
  · exfalso
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨g, rfl⟩ := hπ y
    exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top g))

theorem injective_of_surjective_of_isSimpleGroup {Γ : Type} [Group Γ] [IsSimpleGroup Γ]
    [Nontrivial Y] (π : Γ →* Y) (hπ : Function.Surjective π) : Function.Injective π := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff π).mp h
  · exfalso
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨g, rfl⟩ := hπ y
    exact hy ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top g))

theorem card_le_of_surjective {Γ : Type} [Group Γ] [Finite Γ] (π : Γ →* Y)
    (hπ : Function.Surjective π) : Nat.card Y ≤ Nat.card Γ :=
  Nat.card_le_card_of_surjective π hπ

theorem false_of_b42Types_L34
    (hG2 : FactG2Cayley) (hY : IsPSL 3 2 2 Y) (h : CFSG.QuasithinUnique.Bridge.B42Types Y) :
    False := by
  have hc := card_of_isPSL34 hY
  have hs := isSimpleGroup_of_isPSL34 hY
  have hZ := center_eq_bot_of_isPSL34 hY
  rcases h with ⟨K, _, _, n, hn, hK, ⟨e⟩⟩ | ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ |
      ⟨K, _, _, n, hn, hK, ⟨e⟩⟩ | ⟨K, _, _, n, hn, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, N, hN, ⟨e⟩⟩ |
      ⟨m, hm, ⟨e⟩⟩ | hhat | ⟨K, _, _, n, hK, hn, ⟨e⟩⟩
  ·
    rw [Nat.card_congr e.toEquiv, card_statedSL_two, hK, two_pow_sq] at hc
    exact psl22_ne_20160 n hc
  ·
    rw [Nat.card_congr e.toEquiv, card_statedSL_three] at hc
    exact sl3_ne_20160 _ hc
  ·
    rw [Nat.card_congr e.toEquiv, card_statedSp_two] at hc
    have h2 : 2 ≤ Nat.card K := by
      rw [hK]
      exact (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ n)).trans_eq' (by norm_num)
    exact sp4_ne_20160 h2 hc
  ·
    have hZG : Subgroup.center ↥(CFSG.Open.quasithinG2 K) = ⊥ := by
      rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]
    have eZ : ↥(CFSG.Open.quasithinG2 K) ≃*
        ↥(CFSG.Open.quasithinG2 K) ⧸ Subgroup.center ↥(CFSG.Open.quasithinG2 K) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZG.symm)
    have hG : IsG2 2 n Y := IsG2.of_mulEquiv (e.trans eZ).symm (hG2 K n hn hK)
    have hcG := (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG).1 rfl
    obtain ⟨r, hr, hord⟩ := L1295B.two_part_ordG2 (n := n) (by omega)
    rw [hc, hord] at hcG
    have := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (a := 6) (b := n * 6) (r := 315) (s := r)
      (by decide) hr (by norm_num at hcG ⊢; omega)
    omega
  ·
    have hs' : IsSimpleGroup ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK
    have hD : (commutator ↥(CFSG.Open.quasithinG2 K)).map (CFSG.Open.quasithinG2 K).subtype =
        ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    let eD : ↥(commutator ↥(CFSG.Open.quasithinG2 K)) ≃*
        ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      ((commutator ↥(CFSG.Open.quasithinG2 K)).equivMapOfInjective
        (CFSG.Open.quasithinG2 K).subtype (CFSG.Open.quasithinG2 K).subtype_injective).trans
        (MulEquiv.subgroupCongr hD)
    have hDs : IsSimpleGroup ↥(commutator ↥(CFSG.Open.quasithinG2 K)) := eD.isSimpleGroup
    have hYp : Group.IsPerfect Y := (isQuasisimple_of_isPSL34 hY).1
    have : Group.IsPerfect ↥N := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hN0 : N ≠ ⊥ := by
      rintro rfl
      have h1 : Nat.card Y = 1 := by
        rw [Nat.card_congr e.toEquiv, Subgroup.card_bot]
      omega
    have heq : N = commutator ↥(CFSG.Open.quasithinG2 K) :=
      Vol2.Ch10.SecA.C10P01.eq_commutator_of_isPerfect N hN0 hDs
    obtain ⟨eP⟩ := lred3_equiv_g2derived_psu33 hK
    have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
      rw [GaloisField.card 3 (2 * 1) (by norm_num)]
      norm_num
    have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
    have hP : IsPSU 3 3 1 Y := ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1),
      inferInstance, inferInstance, hK9,
      ⟨((e.trans (MulEquiv.subgroupCongr heq)).trans eD).trans eP.symm⟩⟩
    rw [L1295B.card_of_isPSU_three_three hP] at hc
    norm_num at hc
  ·
    rw [Nat.card_congr e.toEquiv] at hc
    rcases hm with rfl | rfl | rfl
    · rw [Ch1Four.card_alt5 ⟨MulEquiv.refl _⟩] at hc
      norm_num at hc
    · rw [Ch1Four.card_alt6 ⟨MulEquiv.refl _⟩] at hc
      norm_num at hc
    · rw [Ch1Four.card_alt7 ⟨MulEquiv.refl _⟩] at hc
      norm_num at hc
  ·
    rw [Ch1Four.card_hat6 hhat] at hc
    norm_num at hc
  ·
    rcases hn with rfl | rfl
    · obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := hY
      exact B69.not_equiv_sl_four_psl_three (K := K) (F := K3) hK (by rw [hK3]; norm_num)
        (e.trans (B69.statedSLEquivStatedProj hK 4)) e3
    · rw [Nat.card_congr e.toEquiv, card_statedSL_five_two hK] at hc
      norm_num at hc

end Types

section Modules

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_table_L34
    {G L : Subgroup (MulAut V)} (h34 : IsPSL 3 2 2 ↥L)
    (ht : AsB45Table G L) (hqq : qOf G ≤ ((2 : ℚ) : WithTop ℚ)) : False := by
  have hq := isQuasisimple_of_isPSL34 h34
  have hc := card_of_isPSL34 h34
  have hcZ := card_quot_center_of_isPSL34 h34
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  rcases ht with ⟨⟨π, hR⟩, -⟩ | ⟨m, hm, horth, -⟩ | ⟨m, ⟨K, _, _, hK, π, hR⟩, -⟩ |
      ⟨f, hsz, -⟩ | ⟨m, hm, -, hq2, -⟩ | ⟨⟨K, _, _, hK, π, hR⟩, -⟩ | ⟨-, hq2⟩ |
      ⟨⟨K, _, _, Γ₀, -, hhat, -, π, hR⟩, -⟩ | ⟨-, hq2⟩ | ⟨⟨x, y, hxy, π, hR⟩, -⟩ | ⟨-, hq2⟩
  ·
    have h1 := card_le_of_surjective (Γ := ↥(alternatingGroup (Fin 7))) π hR.1
    rw [hc, Ch1Four.card_alt7 ⟨MulEquiv.refl _⟩] at h1
    omega
  ·
    obtain ⟨K, _, _, _, hK, π, hR⟩ := horth
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨e⟩ := lred3_cq_stated hq (StatedSL 2 K)
      (lred3_simple_statedProj_sl le_rfl (Or.inr h4)) π hR.1
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
      (by norm_num), hK] at hcZ
    have hg : Nat.gcd 2 (2 ^ (2 * m) - 1) = 1 :=
      Nat.coprime_two_left.mpr (Nat.Even.sub_odd Nat.one_le_two_pow
        ((Nat.even_pow' (by omega)).mpr even_two) odd_one)
    rw [hg, Nat.div_one, show 2 * (2 - 1) / 2 = 1 by rfl, pow_one,
      show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton, two_pow_sq] at hcZ
    exact psl22_ne_20160 (2 * m) hcZ
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hm1 : m = 1 := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          have := Finite.one_lt_card (α := K)
          rw [hK] at this
          norm_num at this
        · omega
      subst hm1
      exact lred3_false_of_su3_one hq hK π hR.1
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h4 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      have hne : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := fun h => by
        have h2 : 2 ^ m = 2 := congrArg Prod.snd h
        omega
      obtain ⟨e⟩ := lred3_cq_stated hq (StatedSU 3 (2 ^ m) K)
        (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 m hK 3 le_rfl hne)
        π hR.1
      have hU : IsPSU 3 2 m (↥L ⧸ Subgroup.center ↥L) :=
        ⟨⟨Nat.prime_two, by omega, le_rfl, hne⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
      have hcU := (CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl
      obtain ⟨r, hr, hord⟩ := L1295B.two_part_ordTwistedA_two (n := m) (by omega)
      rw [hcZ, show (3 : ℕ) - 1 = 2 by rfl, hord] at hcU
      have h3 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (a := 6) (b := m * 3) (r := 315)
        (s := r) (by decide) hr (by norm_num at hcU ⊢; omega)
      have hm2 : m = 2 := by omega
      subst hm2
      have h62400 : CFSG.Open.ordTwistedA 2 (2 ^ 2) = 62400 := by
        rw [L1295B.ordTwistedA_two_eq _ (by norm_num)]
        norm_num
      have := (CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl
      rw [hcZ, show (3 : ℕ) - 1 = 2 by rfl, h62400] at this
      norm_num at this
  ·
    obtain ⟨a, K, _, _, ha, hf, hK, ⟨e⟩⟩ := hsz.exists_equiv
    rw [hf] at hK
    rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK] at hc
    have h2 : (2 ^ (2 * a + 1)) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    generalize 2 ^ (2 * a + 1) = q at h2 hc
    have hq1 : 1 ≤ q := by omega
    have h1 : (((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ZMod 3)) = 0 := by
      rw [hc]
      decide
    have h2' : (q : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, h2]
      rfl
    push_cast [Nat.cast_sub hq1] at h1
    rw [h2'] at h1
    exact absurd h1 (by decide)
  ·
    exact absurd hq2 (not_lt.2 hqq)
  ·
    obtain ⟨eP⟩ := lred3_equiv_g2derived_psu33 (K := K) (by rw [hK]; norm_num)
    have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
      rw [GaloisField.card 3 (2 * 1) (by norm_num)]
      norm_num
    have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
    have hP : IsPSU 3 3 1 ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1), inferInstance,
        inferInstance, hK9, ⟨eP.symm⟩⟩
    have h1 := card_le_of_surjective
      (Γ := ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆) π hR.1
    rw [hc, L1295B.card_of_isPSU_three_three hP] at h1
    omega
  · exact absurd hq2 (not_lt.2 hqq)
  ·
    obtain ⟨e⟩ := lred3_cq_of_quasisimple hhat.1 hq π hR.1
    obtain ⟨f⟩ := hhat.2.2
    have h1 : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card ↥CFSG.Open.quasithinM22 :=
      Nat.card_congr (e.symm.trans f).toEquiv
    have h2 : Nat.card ↥CFSG.Open.quasithinM22 = 443520 := by
      rw [show CFSG.Open.quasithinM22 = CFSG.Blueprint.NativeSporadic.M22 from rfl]
      exact CFSG.Sporadic.Mathieu.card_M22
    rw [hcZ, h2] at h1
    norm_num at h1
  · exact absurd hq2 (not_lt.2 hqq)
  ·
    obtain ⟨hs, hcard⟩ := Vol2.Ch10.SecA.C10P01.stab_props_m22 hxy
    have h1 := card_eq_of_surjective_of_isSimpleGroup
      (Γ := ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 24)) y)) π hR.1
    rw [hc, hcard] at h1
    norm_num at h1
  · exact absurd hq2 (not_lt.2 hqq)

end Modules

theorem false_of_d310Two_L34 {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {U C : Subgroup W} (h34 : IsPSL 3 2 2 ↥L)
    (h : (∃ n, BinaryNaturalSL L U C 3 n) ∨ (∃ n, BinaryNaturalSp4 L U C n) ∨
      AlternatingNatural L U C 6 ∨ BinaryNaturalSL L U C 4 1 ∨ BinaryNaturalSL L U C 5 1 ∨
      A7Four L U C) : False := by
  have hc := card_of_isPSL34 h34
  rcases h with ⟨n, K, _, _, hKc, π, hπ⟩ | ⟨n, K, _, _, hKc, π, hπ⟩ | ⟨π, hπ⟩ |
      ⟨K, _, _, hKc, π, hπ⟩ | ⟨K, _, _, hKc, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    have h2 : Nat.card ↥L = Nat.card ↥(StatedSL 3 K) :=
      (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
    rw [h2, card_statedSL_three] at hc
    exact sl3_ne_20160 _ hc
  ·
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    have h2 : Nat.card ↥L = Nat.card ↥(StatedSp 2 K) :=
      (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
    rw [h2, card_statedSp_two] at hc
    exact sp4_ne_20160 Finite.one_lt_card hc
  ·
    have h1 := card_le_of_surjective (Γ := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [hc, Ch1Four.card_alt6 ⟨MulEquiv.refl _⟩] at h1
    omega
  ·
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    have hK2 : Nat.card K = 2 := by rw [hKc]; norm_num
    let e : ↥(StatedSL 4 K) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := h34
    exact B69.not_equiv_sl_four_psl_three (K := K) (F := K3) hK2 (by rw [hK3]; norm_num)
      (e.symm.trans (B69.statedSLEquivStatedProj hK2 4)) e3
  ·
    have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
    have h2 : Nat.card ↥L = Nat.card ↥(StatedSL 5 K) :=
      (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)).symm
    rw [h2, card_statedSL_five_two (by rw [hKc]; norm_num)] at hc
    norm_num at hc
  ·
    have h1 := card_le_of_surjective (Γ := ↥(alternatingGroup (Fin 7))) π hπ.1
    rw [hc, Ch1Four.card_alt7 ⟨MulEquiv.refl _⟩] at h1
    omega

theorem false_of_insp4_L34
    (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45) (hD310 : D310)
    {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) (hMp : Mp = L) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (hq : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ)) (h34 : IsPSL 3 2 2 ↥L) :
    False := by
  rcases hD310 W M Mp T L V hD hMp hqM with hT | ⟨hfirst, -, -⟩
  ·
    have hT' : T ≤ stabSub V := fun t ht => hT t ht
    subst hMp
    have hLs : Mp ≤ stabSub V := insp5a_le_stabSub hD.hyp
    have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
    have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT'
    have hQ := lred3_qsec hD.hyp rfl hO2
    have hb4 := lred3_b4Hyp hA21 hD.hyp rfl hO2
    have hqhat := lred3_qhatOf_autSec hD rfl hT'
    have hqs := lred3_qOf_autSec hD rfl hT' hq
    have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
      CFSG.QuasithinUnique.Bridge.sec_sq_eq_one hexp ⊤ _
    have hLt : CFSG.IsQuasisimple ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
      hb4.2.2.1
    let eK : ↥(resHomOn V hLs).range ≃* ↥(autSub Mp V) :=
      MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs).symm
    let e2 : ↥(autSub Mp V) ≃* ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
      B5.secEquiv (autSub Mp V) (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful
    let f : ↥Mp →* ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
      (e2.toMonoidHom.comp eK.toMonoidHom).comp (resHomOn V hLs).rangeRestrict
    have hf : Function.Surjective f :=
      e2.surjective.comp (eK.surjective.comp (MonoidHom.rangeRestrict_surjective _))
    have : IsSimpleGroup ↥Mp := isSimpleGroup_of_isPSL34 h34
    have : Nontrivial ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hLt
    have hfi := injective_of_surjective_of_isSimpleGroup f hf
    have hLt34 : IsPSL 3 2 2 ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
      isPSL_of_mulEquiv (MulEquiv.ofBijective f ⟨hfi, hf⟩).symm h34
    rcases h45 _ hsv _ _ hb4 hqhat with ⟨-, ⟨A, hA'⟩, -⟩ | ⟨-, ht⟩ | h3
    · exact false_of_b42Types_L34 hG2 hLt34
        (CFSG.QuasithinUnique.Bridge.asB42Types_of_asB42With (KP := CFSG.SectionRank.IsKGroupCat)
          h42 _ hsv _ _ hb4 ⟨A, hA'⟩)
    · exact false_of_table_L34 hLt34 ht hqs
    · exact absurd h3.2.1 (not_lt.2 hqs)
  · exact false_of_d310Two_L34 h34 hfirst

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

attribute [local instance] commGroupOfFact

theorem false_of_L34
    (h1323 : Input1323Two) (h1336 : Input1336)
    (h24 : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      ⁅V, conjSub g⁻¹ V⁆ = ⊥)
    (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45) (hD310 : D310)
    {K : Subgroup G} (hK : K ∈ cComp S.G1) (hKn : S.G1 ≤ Subgroup.normalizer (K : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) (hL : IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    False := by
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := isSimpleGroup_of_isPSL34 hL
  have hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := (isQuasisimple_of_isPSL34 hL).1
  have hF := S.hypF918_sup h1323 h1336 h24 hK hKn hKM (L1295B.isQuasisimple_of_simple hperf hS)
  have hHz := S.sup_mem_Hz h1336 hK hKM
  have hTK := S.T_le_normalizer_of_G1 h1336 hKn
  have hSQ : SQTKGroup ↥(K ⊔ (S.L1 ⊔ T)) := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian
      (T := T) ⟨le_sup_right.trans le_sup_right, hHz.1.2⟩
    exact ⟨hq, hk⟩
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirr := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFe := factElem hF hIU
  have hirr' : subM S.V1 (conjClosure I (K ⊔ (S.L1 ⊔ T))) I ∈
      IrrPlusOn (autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) (conjClosure K T))
        (orbSup (autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) T)
          (subM S.V1 (conjClosure I (K ⊔ (S.L1 ⊔ T))) I))
        (autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) T) := hirr
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hMp : autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) (conjClosure K T) =
      autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) K := by
    rw [L1295B.conjClosure_eq hTK]
  have hqM := hA.qhat_M hD.sylow.1
  have hne : autIH S.V1 I (K ⊔ (S.L1 ⊔ T)) K ≠ ⊥ := by
    rw [autIH_eq_map hF (le_of_mem_cComp hF.K_cComp)]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨eI⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS hne
  exact false_of_insp4_L34 hA21 hG2 h42 h45 hD310 ⟨hD, hA.qhat_VT hD.exp, hirr'⟩ hMp hqM
    (hA.qOf_VT hD.exp) (isPSL_of_mulEquiv eI.symm hL)

end Setting

theorem endL34K_of
    (h1323 : Input1323Two) (h1336 : Input1336) (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley)
    (h42 : AsB42) (h45 : AsB45) (hD310 : D310) : EndL34K := by
  intro G _ _ T L V S hC K hK hKn hKM hL
  exact S.false_of_L34 h1323 h1336 (fun g hg hne => (hC.h24 g hg hne).2) hA21 hG2 h42 h45 hD310
    hK hKn hKM hL

end CFSG.Quasithin.H13.A5
