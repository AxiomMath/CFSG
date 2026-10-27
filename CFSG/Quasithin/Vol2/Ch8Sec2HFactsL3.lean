module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsDPf
public import CFSG.Quasithin.Background.HFL3Alpha
public import CFSG.Quasithin.Background.HFL3Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

theorem exists_model_l3nine {V : Type} [CommGroup V] {L M : Subgroup (MulAut V)}
    (hLM : Mathieu.IsOver L M) {n : ℕ} (hL : BinaryNineTensor L ⊤ ⊥ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (hK : Nat.card K = (2 ^ n) ^ 2)
      (e : V ≃* L3Nine.HMod n K), L.map (congrHom e) = L3Nine.img hK ∧
        M.map (congrHom e) ≤ L3Nine.norm hK := by
  obtain ⟨K, _, _, _, hK, hreal⟩ := hL
  have hK' : Nat.card K = (2 ^ n) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, he⟩ := L3Nine.exists_model hK' hreal
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK', e, he, ?_⟩
  have h1 : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) =
      Subgroup.normalizer ((L.map (congrHom e) : Subgroup (MulAut (L3Nine.HMod n K))) :
        Set (MulAut (L3Nine.HMod n K))) :=
    Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
  rw [L3Nine.norm, ← he, ← h1]
  exact Subgroup.map_mono hLM.2

theorem hTab82Nine_holds : HTab82Nine := by
  intro V _ _ L M hLM n hn hL
  obtain ⟨K, _, _, _, hK, e, -, hMN⟩ := exists_model_l3nine hLM hL
  have : Finite (L3Nine.HMod n K) := Finite.of_equiv V e.toEquiv
  have : Finite (MulAut V) := finite_mulAut V
  refine ⟨?_, ?_, fun hn1 => ?_, fun hn1 => ?_⟩
  · rw [← pRank_two_map_congrHom e M]
    refine pRank_le_of_card_le fun A hAM hAe k hk => ?_
    have h := L3Nine.card_le_of_elemAb_norm hn hK (hAM.trans hMN) hAe
    rw [hk] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  · rw [← betaH_map_congrHom e M]
    have : Finite (MulAut (L3Nine.HMod n K)) := MulEquiv.finite_left
    refine le_betaH_iff_isPGroup.mpr fun U _ hnp => ?_
    obtain ⟨p, hp, hp2, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        p ∣ Nat.card ↥(M.map (congrHom e) ⊓ centSub U) := by
      by_contra hno
      push Not at hno
      apply hnp
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
      intro d hd hdd
      by_contra hd2
      exact hno d hd hd2 hdd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M.map (congrHom e) ⊓ centSub U)) p
      hpdvd
    have hyo : orderOf (y : MulAut (L3Nine.HMod n K)) = p := by rw [Subgroup.orderOf_coe, hy]
    have hy1 : (y : MulAut (L3Nine.HMod n K)) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hyo
      exact hp.one_lt.ne hyo
    have hodd : Odd (orderOf (y : MulAut (L3Nine.HMod n K))) := by
      rw [hyo]
      exact hp.odd_of_ne_two hp2
    have hUy : U ≤ fixV (Subgroup.zpowers (y : MulAut (L3Nine.HMod n K))) := fun u hu =>
      H.mem_fixV_zpowers_iff.mpr (mem_centSub.mp y.2.2 u hu)
    have h4 := L3Nine.le_rkIdx_of_odd hn hK (hMN y.2.1) hy1 hodd
    exact_mod_cast h4.trans (L3Nine.rkIdx_anti hUy)
  · refine le_iInf₂ fun k hk => ?_
    rw [← alphaSet_map_congrHom e M] at hk
    exact_mod_cast (L3Nine.alphaSet_spec hn hK hMN hk).2
  · refine iInf₂_eq_top.mpr fun k hk => ?_
    rw [← alphaSet_map_congrHom e M] at hk
    exact absurd (L3Nine.alphaSet_spec hn hK hMN hk).1 (by omega)

theorem card_eq_two_pow_rk_V {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (U : Subgroup V) : Nat.card U = 2 ^ rk ↥U :=
  card_eq_two_pow hV U

theorem hOffNormal82L3_holds : HOffNormal82L3 := by
  intro V _ _ L M hLM S A hSM hS _ hAS hAe hL hA4 hfix4
  obtain ⟨K, _, _, _, hK, e, -, hMN⟩ := exists_model_l3nine hLM hL
  have : Finite (L3Nine.HMod 1 K) := Finite.of_equiv V e.toEquiv
  have : Finite (MulAut V) := finite_mulAut V
  have hV : ∀ v : V, v ^ 2 = 1 := fun v => by
    have h := L3Nine.sq_eq_one_HMod (e v)
    rw [← map_pow] at h
    exact e.injective (h.trans (map_one e).symm)
  have hcA : Nat.card ↥(A.map (congrHom e)) = Nat.card K ^ 2 := by
    rw [card_map_congrHom, card_eq_two_pow_rk_of hAe, hA4, hK]
    norm_num
  have hcf : 2 ^ 1 < Nat.card ↥(fixV (A.map (congrHom e))) := by
    rw [fixV_map_congrHom, Subgroup.card_map_of_injective e.injective,
      card_eq_two_pow_rk_V hV, hfix4]
    norm_num
  have h := L3Nine.le_normalizer_of_le (le_refl 1) hK ((Subgroup.map_mono hSM).trans hMN)
    ((isPGroup_map_congrHom e).2 hS) (Subgroup.map_mono hAS)
    ((isElemAbelian2_map_congrHom e).2 hAe) hcA.ge hcf
  have h1 : (Subgroup.normalizer (A : Set (MulAut V))).map (congrHom e) =
      Subgroup.normalizer ((A.map (congrHom e) : Subgroup (MulAut (L3Nine.HMod 1 K))) :
        Set (MulAut (L3Nine.HMod 1 K))) :=
    Subgroup.map_equiv_normalizer_eq A (MulAut.congr e)
  rw [← h1] at h
  exact (Subgroup.map_le_map_iff_of_injective (congrHom_injective e)).mp h

theorem hTab82_holds :
    HTab82 :=
  hTab82_of hTab82Nine_holds

theorem hOffNormal82_holds :
    HOffNormal82 :=
  hOffNormal82_of hOffNormal82L3_holds

end CFSG.Quasithin.H13
