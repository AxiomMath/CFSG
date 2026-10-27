module

public import CFSG.Quasithin.H13.U4ParPointQuot
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem two_dvd_card_modO2_perfectCore_parP (hm : 2 ≤ m) :
    2 ∣ Nat.card (CFSG.Quasithin.ModO2 (perfectCore (parP h))) := by
  haveI := h.finite
  haveI : Finite h.fixedField := Subtype.finite
  rw [Nat.card_congr (modO2PerfectCoreParPEquivSL2 h hm).toEquiv,
    Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
      h.fixedField).toEquiv,
    CFSG.Open.StatedAPI.card_statedSL_two]
  refine dvd_mul_of_dvd_left ?_ _
  rw [h.card_fixedField]
  exact dvd_pow_self 2 (by omega)

theorem lieModel_modO2_perfectCore_parP (hm : 2 ≤ m) :
    CFSG.Blueprint.LieModel (CFSG.Quasithin.ModO2 (perfectCore (parP h))) .PSL 2 2 m := by
  haveI := h.finite
  haveI : Finite h.fixedField := Subtype.finite
  have hcard : Nat.card h.fixedField = 2 ^ m := h.card_fixedField
  have e : CFSG.Quasithin.ModO2 (perfectCore (parP h)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 h.fixedField) :=
    (modO2PerfectCoreParPEquivSL2 h hm).trans
      ((QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot h).symm)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 h.fixedField))
  refine Or.inl ⟨by decide, ⟨?_, h.fixedField, inferInstance, inferInstance, hcard, ⟨e⟩⟩⟩
  refine ⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩
  · intro hpair
    have h2 : 2 ^ m = 2 := congrArg Prod.snd hpair
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  · intro hpair
    have h2 : 2 ^ m = 3 := congrArg Prod.snd hpair
    have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    rw [h2] at hdvd
    omega

theorem map_parP_of_map_hypUnitriangular (hm : 2 ≤ m) {θ : MulAut (hypSU h 2 0)}
    (hθ : (hypUnitriangular h 2 0).map θ.toMonoidHom = hypUnitriangular h 2 0) :
    (parP h).map θ.toMonoidHom = parP h := by
  have := h.finite
  have hB : (hypBorel h 2 0).map θ.toMonoidHom = hypBorel h 2 0 := by
    rw [← UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num),
      Subgroup.map_equiv_normalizer_eq, hθ,
      UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
  have hco : IsCoatom ((parP h).map θ.toMonoidHom) :=
    (OrderIso.isCoatom_iff (f := MulEquiv.mapSubgroup θ) (parP h)).mpr (isCoatom_parP h)
  have hBle : hypBorel h 2 0 ≤ (parP h).map θ.toMonoidHom := by
    rw [← hB]
    exact Subgroup.map_mono (UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num))
  rcases eq_parP_or_eq_parP2 h hco hBle with e | e
  · exact e
  · exfalso
    have hc : ∀ a ∈ CFSG.Open.pCoreOf 2 (perfectCore (parP2 h)),
        ∀ b ∈ CFSG.Open.pCoreOf 2 (perfectCore (parP2 h)), a * b = b * a :=
      fun a ha b hb => pCoreOf_perfectCore_parP2_comm h ha hb
    rw [← e, ← CFSG.Quasithin.map_perfectCore θ.toMonoidHom, pCoreOf_map_of_inj θ.injective,
      pCoreOf_perfectCore_parP h hm, comm_map_iff θ.injective] at hc
    obtain ⟨a, ha, b, hb, hab⟩ := exists_radQ_ne_comm h
    exact hab (hc a ha b hb)

end CFSG.Quasithin.H13.U4Par
