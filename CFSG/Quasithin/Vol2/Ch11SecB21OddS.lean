module

public import CFSG.Quasithin.Vol2.Ch11SecB21Odd
public import CFSG.Quasithin.Vol2.KGFact4413Lie

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem inf_centralizer_hall_eq_botS (h4413 : H13.Stmt4_4_13Lie) (h442 : TmpL4_4_2)
    (hNS : FactNotSmall443) (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hyp : Hyp11 G T L I n) {H B K : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hlie : E2.E22LieCases H T (H ⊓ Subgroup.normalizer (L : Set G)) K)
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ Subgroup.normalizer (L : Set G)))
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hTB : T ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (L : Set G)) ⊔
      (T ⊓ Subgroup.normalizer (B : Set G))) :
    B ⊓ Subgroup.centralizer (fsuV T I : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set V := fsuV T I
  set C := B ⊓ Subgroup.centralizer (V : Set G) with hCdef
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => hBab a ha.1 b hb.1
  by_contra hne
  obtain ⟨⟨x, hxC⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxo : orderOf x ≠ 1 := fun h => hx1' (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hxo
  have hBodd : Odd (Nat.card B) := hB.2.1
  have hxodd : Odd (orderOf x) := hBodd.of_dvd_nat (B.orderOf_dvd_natCard hxC.1)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hxodd) (even_iff_two_dvd.mpr hpd)
  have hxo0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  set y := x ^ (orderOf x / p) with hydef
  have hyo : orderOf y = p := orderOf_pow_orderOf_div hxo0 hpd
  set A := torsionSub C hCab p with hAdef
  have hyA : y ∈ A := mem_torsionSub.mpr ⟨C.pow_mem hxC _, hyo ▸ pow_orderOf_eq_one y⟩
  have hy1 : y ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hyo, h, orderOf_one])
  have hA1 : A ≠ ⊥ := fun h => hy1 (by rw [h] at hyA; exact hyA)
  have hAC : A ≤ C := fun z hz => (mem_torsionSub.mp hz).1
  have hAB : A ≤ B := hAC.trans inf_le_left
  have hAel : IsElemAbelian p A := isElemAbelian_torsionSub C hCab p
  have hTM : T ≤ M := hyp.normal
  have hTX : T ≤ H ⊓ M := le_inf hH.1.1 hTM
  have hTS : QuasithinUnique.IsSylowTwoOf T (H ⊓ M) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTX
  have hNA : T ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht z hz
    obtain ⟨hzB, hzC⟩ := (mem_torsionSub.mp hz).1
    have htV : t ∈ Subgroup.normalizer (V : Set G) := T_le_normalizer_fsuV T I ht.1
    refine mem_torsionSub.mpr ⟨⟨(Subgroup.mem_normalizer_iff.mp ht.2 z).mp hzB, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (B2F.le_normalizer_centralizer le_rfl htV) z).mp hzC
    · rw [conj_pow, (mem_torsionSub.mp hz).2, mul_one, mul_inv_cancel]
  have hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) :=
    mul_comm_sylow_of_normalizes (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M))
      (B6.pCoreOf_two_le_of_isSylowTwoOf hTS) hTX (hAB.trans hB.1) hTB hNA
  have h1 := (((h4413 G H T (H ⊓ M) hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hH.1.2
    ⟨K, hKc, hHK, hlie⟩ (isSylowTwoOf_of_isHStar hyp hH)
    (isUniqueMaxOver_of_isHStar h331 hyp hH)).2 B hB.1 hB.2.1 hB.2.2).1 p A hp hAB hAel hAT).2
  obtain ⟨hVLT, hVred, -⟩ := h3228 G T L I hyp.fsu
  rw [fsuL0_eq hyp] at hVLT hVred
  have hVL : V = ⁅V, L⁆ := (commutator_fsuV_eq_self hyp).symm
  have hV1 : V ≠ ⊥ := fsuV_ne_bot hyp
  have hAM : A ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (hAB.trans (hB.1.trans inf_le_right)) (hAC.trans inf_le_right)
  have hAodd : Odd (Nat.card A) := hBodd.of_dvd_nat (Subgroup.card_dvd_of_le hAB)
  rcases h442 G T M L A V hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
      (isMaxTwoLocal_M h331 hyp) hTM hyp.fsu.maximal hyp.fsu.faithful Subgroup.le_normalizer
      hyp.fsu.quasisimple le_rfl hVLT hVred hVL hV1 hAM hA1 hAel.1 hAodd with hN | hsmall
  · exact h1 fun z hz => ⟨hz.1, hN hz.2⟩
  · exact hNS (↥L ⧸ CFSG.pCore 2 ↥L) n hyp.one_lt hyp.shape hsmall.2.1

end CFSG.Quasithin.Vol2.Ch11.SecB
