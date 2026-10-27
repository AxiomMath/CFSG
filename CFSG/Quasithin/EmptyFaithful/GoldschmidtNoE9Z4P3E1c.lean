module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3E1b
public import CFSG.Quasithin.EmptyFaithful.S146zRHat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3Lines3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9z4_normalizer_eq_of_C1 (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (hdat : IsE9Dat T M H PQ R₁ R₂ s) (hC : Stage14614C1 T H p) :
    Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) ⊓
      mcOf T = T := by
  classical
  obtain ⟨V, _, _, β, hb⟩ := E9P2.Sec.exists_betaData h35 S hred hshape
  obtain ⟨σ, hσT, hσpow, hσinv⟩ := E9P2.E1.exists_sigma hb
  obtain ⟨P, hPK, hPel, hP9, -⟩ := e9_exists_P h35 S hred hshape
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTH : T ≤ H := hred.isHTM.1.1
  have hTG : T ≤ mcOf T := hTH.trans hHG
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKG : oTwoUpper H ≤ mcOf T := hKH.trans hHG
  have hKPQ : oTwoUpper H ≤ PQ := hred.oTwoUpper_le_pq S.hyp.sylow.1
  have hKn : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    have h := le_normalizer_conjClosure (oTwoUpper H) (mcOf T)
    rwa [hC.1] at h
  have hKQ : oTwoUpper H ⊓ pCoreOf 2 H ≤ pCoreOf 2 (mcOf T) :=
    E9P2.E1.inf_pCoreOf_le hKH hHG hKn
  have hPG : P ≤ mcOf T := hPK.trans hKG
  have hσH : σ ∈ H := hTH hσT
  have hσG : σ ∈ mcOf T := hHG hσH
  have hKhat : imageOTwoQuot (mcOf T) (oTwoUpper H) = imageOTwoQuot (mcOf T) P := by
    refine E9P2.E1.hat_K_eq hKG hPK fun k hk => ?_
    obtain ⟨x, hxP, hxk⟩ := E9P2.E1.exists_mem_mul hb (hPK.trans hKPQ) hP9
      (E9P2.E1.inf_pCoreOf_eq_bot H hP9) (hKPQ hk)
    exact ⟨x, hxP, hKQ ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem (hPK hxP)) hk, hxk⟩⟩
  obtain ⟨hEel, hE9⟩ := E9P2.E1.isElemAbelian_hat hPG hPel hP9
  have hnorm : ((T ⊓ Subgroup.normalizer (R₁ : Set G)).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two hdat.indexT
  have hTn : T ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) :
      Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnorm
  have hσ2 : σ ^ 2 ∈ T ⊓ Subgroup.normalizer (R₁ : Set G) := by
    have h := Subgroup.pow_index_mem ((T ⊓ Subgroup.normalizer (R₁ : Set G)).subgroupOf T)
      (⟨σ, hσT⟩ : ↥T)
    rw [show ((T ⊓ Subgroup.normalizer (R₁ : Set G)).subgroupOf T).index = 2 from
      hdat.indexT] at h
    simpa using Subgroup.mem_subgroupOf.mp h
  set T₀ : Subgroup G := T ⊓ Subgroup.normalizer (R₁ : Set G) with hT₀
  set N : Subgroup G := Subgroup.normalizer (T₀ : Set G) ⊓ mcOf T with hN
  have hTN : T ≤ N := le_inf hTn hTG
  have hodd : ∀ x ∈ imageOTwoQuot (mcOf T) N, ¬ 2 ∣ orderOf x → x = 1 := by
    refine E9P2.Lines.odd_order_eq_one (K := imageOTwoQuot (mcOf T) P)
      (T0 := imageOTwoQuot (mcOf T) T₀) (T := imageOTwoQuot (mcOf T) T)
      (N := imageOTwoQuot (mcOf T) N) (σ := qPi (mcOf T) ⟨σ, hσG⟩)
      (t0 := qPi (mcOf T) ⟨σ, hσG⟩ ^ 2) hE9 hEel.2 (fun a ha b hb => zmComm hEel ha hb)
      ?_ ?_ (mem_imageOTwoQuot_iff.mpr ⟨σ, hσG, hσT, rfl⟩) ?_ ?_ ?_ (q_image_mono inf_le_left)
      ?_ ?_ ?_ ?_
    · rw [← hKhat]
      exact fun x hx => q_image_mem_normalizer (K := oTwoUpper H) (L := N)
        (fun n hn => hKn hn.2) hx
    · exact A4.isSylowTwoOf_mono (q_hatT_sylow S) (q_image_mono hTN) le_top
    · intro k hk
      obtain ⟨x, hxG, hxP, rfl⟩ := mem_imageOTwoQuot_iff.mp hk
      exact E9P2.E1.hat_sq_inverts hHG hKn hσH (fun y hy => hσinv y (hKPQ hy)) (hPK hxP) hσG hxG
    · intro t ht
      obtain ⟨t', htG, htT, rfl⟩ := mem_imageOTwoQuot_iff.mp ht
      obtain ⟨i, hi⟩ := hσpow t' htT
      refine ⟨i, fun k hk => ?_⟩
      obtain ⟨x, hxG, hxP, rfl⟩ := mem_imageOTwoQuot_iff.mp hk
      exact E9P2.E1.hat_conj_pow hHG hKn hσH hi (hPK hxP) hσG htG hxG
    · exact fun x hx => q_image_mem_normalizer (K := T₀) (L := N) (fun n hn => hn.1) hx
    · refine mem_imageOTwoQuot_iff.mpr ⟨σ ^ 2, (mcOf T).pow_mem hσG 2, hσ2, ?_⟩
      rfl
    · intro k hk
      obtain ⟨x, hxG, hxP, rfl⟩ := mem_imageOTwoQuot_iff.mp hk
      have h := E9P2.E1.hat_sq_inverts hHG hKn hσH (fun y hy => hσinv y (hKPQ hy)) (hPK hxP)
        hσG hxG
      rwa [inv_pow] at h
    · exact fun r hr hd => hC.2 hshape.1 r hr (hd.trans (Subgroup.card_quotient_dvd_card _))
    · exact fun E hE => E9P2.E1.card_le_nine_of_pRank (S.pRank_quotient_le_two Nat.prime_three
        (by norm_num)) hE
  have hodd1 : ∀ x ∈ N, Odd (orderOf x) → x = 1 := by
    intro x hxN hxo
    have hxG : x ∈ mcOf T := hxN.2
    have hmem : qPi (mcOf T) ⟨x, hxG⟩ ∈ imageOTwoQuot (mcOf T) N :=
      mem_imageOTwoQuot_iff.mpr ⟨x, hxG, hxN, rfl⟩
    have hord : ¬ 2 ∣ orderOf (qPi (mcOf T) ⟨x, hxG⟩) := by
      intro h2
      have h3 : 2 ∣ orderOf (⟨x, hxG⟩ : ↥(mcOf T)) := h2.trans (orderOf_map_dvd _ _)
      rw [Subgroup.orderOf_mk] at h3
      exact (Nat.not_even_iff_odd.mpr hxo) (even_iff_two_dvd.mpr h3)
    have hxQ : x ∈ pCoreOf 2 (mcOf T) := (mk_eq_one_iff_mem_pCoreOf _).mp (hodd _ hmem hord)
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨x, hxQ⟩
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj] at hxo
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exact absurd (Nat.even_pow.mpr ⟨even_two, hj0⟩) (Nat.not_even_iff_odd.mpr hxo)
  have hN2 : IsPGroup 2 N := by
    have hbot : oTwoUpper N = ⊥ :=
      eq_bot_iff.mpr ((Subgroup.closure_le ⊥).mpr fun x hx =>
        Subgroup.mem_bot.mpr (hodd1 x hx.1 hx.2))
    intro g
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper N g.2
    rw [hbot, Subgroup.mem_bot] at hk
    exact ⟨k, Subtype.ext hk⟩
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTG
  exact le_antisymm ((A4.isSylowTwoOf_iff_maximal.mp hTsyl).2.2 N inf_le_right hN2 hTN) hTN

end Main

end CFSG.Quasithin
