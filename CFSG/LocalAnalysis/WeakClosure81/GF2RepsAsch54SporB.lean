module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporNineSub
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Sporadic.Schreier.BSchreierCase
public import CFSG.RankThree.PartOne.SPOR.OuterB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code

theorem pow_three_eq_one_of_pow_nine_Ppair
    (p : Ppair) (hp : p ^ 9 = 1) : p ^ 3 = 1 := by
  let φ : Ppair →* Equiv.Perm (Fin 24) := AutPerm.subtype.comp Ppair.subtype
  have hφ : Function.Injective φ := AutPerm.subtype_injective.comp Ppair.subtype_injective
  let ψ : NativeSporadic.M24 →* Equiv.Perm (Fin 24) :=
    (MulAut.conj bridgeQ⁻¹).toMonoidHom.comp NativeSporadic.M24.subtype
  have hψ : Function.Injective ψ :=
    (MulAut.conj bridgeQ⁻¹).injective.comp NativeSporadic.M24.subtype_injective
  obtain ⟨g, hg, hpg⟩ := (mem_AutPerm_iff_conj (φ p)).1 (p : AutPerm).2
  have he : φ p = ψ ⟨g, hg⟩ := Equiv.ext fun i => by
    rw [hpg i]
    simp only [ψ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, Equiv.Perm.mul_apply]
  have h9 : (⟨g, hg⟩ : NativeSporadic.M24) ^ 9 = 1 :=
    (map_eq_one_iff ψ hψ).1 (by rw [map_pow, ← he, ← map_pow, hp, map_one])
  exact (map_eq_one_iff φ hφ).1 (by
    rw [map_pow, he, ← map_pow, pow_three_eq_one_of_pow_nine_M24 _ h9, map_one])

theorem pow_three_eq_one_of_pow_nine_Ntwo
    (g : Ntwo) (hg : g ^ 9 = 1) : g ^ 3 = 1 :=
  pow_three_eq_one_of_pow_nine_of_ker (twoCoreEquiv.toMonoidHom.comp mkK)
    (by rw [ker_twoCore, natCard_R2N]; norm_num)
    (pow_three_eq_one_of_pow_nine_prod pow_three_eq_one_of_pow_nine_Ppair fun b hb => by
      have h6 : b ^ 6 = 1 := by
        have h := pow_card_eq_one' (x := b)
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
        exact h
      have h := pow_gcd_eq_one.2 ⟨hb, h6⟩
      rwa [show Nat.gcd 9 6 = 3 by norm_num] at h) g hg

theorem pow_three_eq_one_of_pow_nine_comap_Ntwo
    {g : Cbar} (hg : g ∈ Ntwo.comap iotaD) (h9 : g ^ 9 = 1) : g ^ 3 = 1 := by
  have h := pow_three_eq_one_of_pow_nine_Ntwo ⟨iotaD g, hg⟩ (Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact (map_pow iotaD g 9).symm.trans (by rw [h9, map_one])))
  refine (map_eq_one_iff iotaD iotaD_injective).1 ?_
  rw [map_pow]
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
  exact h'

theorem natCard_comap_Ntwo :
    Nat.card (Ntwo.comap iotaD) = 22858846741463040 := by
  rw [← Subgroup.card_map_of_injective iotaD_injective, Subgroup.map_comap_eq_self Ntwo_le_Shat,
    natCard_Ntwo]

private theorem calL0NineCheck_Ntwo : calL0NineCheck 41 22858846741463040 = true := by
  decide +kernel

theorem not_hasCompFactor_isCalL0_comap_Ntwo :
    ¬ HasCompFactor (Ntwo.comap iotaD) IsCalL0 :=
  not_hasCompFactor_isCalL0_of_dvd_of_forall_mem_pow_nine
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput calL0NineCheck_Ntwo
    (fun _ hg h9 => pow_three_eq_one_of_pow_nine_comap_Ntwo hg h9) (dvd_of_eq natCard_comap_Ntwo)

theorem not_hasCompFactor_isCalL0_Jbar :
    ¬ HasCompFactor Jbar IsCalL0 := by
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨hKs, hKc⟩ := CFSG.ComponentClassification.BMCase.Kstab_rStar_simple
  have e := (QuotientGroup.quotientMulEquivOfEq ker_jbarToKv.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective jbarToKv jbarToKv_surjective)
  have : IsSimpleGroup (Jbar ⧸ Ebar.subgroupOf Jbar) := @MulEquiv.isSimpleGroup _ _ _ _ hKs e
  rintro ⟨L, _, hL, hcal⟩
  rcases isCompositionFactor_of_normal (Ebar.subgroupOf Jbar) hL with h1 | h2
  · exact not_isCalL0_of_isCompositionFactor_of_dvd hO (k := 23) (N := 2 ^ 23) (by decide +kernel)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).toEquiv,
        Ebar_extraspecial.2]) h1 hcal
  · exact not_isCalL0_of_isCompositionFactor_of_isSimpleGroup hO (k := 18)
      (by rw [(Nat.card_congr e.toEquiv).trans hKc]; decide +kernel) h2 hcal

theorem exists_isSylowIn_le_comap_Ptwo :
    ∃ T : Subgroup Cbar, IsSylowIn 2 T ⊤ ∧ T ≤ Ptwo.comap iotaD := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Nat.card (Ptwo.comap iotaD) = 2 ^ 41 * 3465 := by
    rw [← Subgroup.card_map_of_injective iotaD_injective,
      Subgroup.map_comap_eq_self (Ptwo_le_Ntwo.trans Ntwo_le_Shat), natCard_Ptwo]
    norm_num
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Ptwo.comap iotaD) 2 (n := 41)
    (by rw [hP]; exact dvd_mul_right _ _)
  obtain ⟨m, hm, hCm⟩ := short_centralizer_quotient_sylow_two.2.1
  have hTc : Nat.card (K.map (Ptwo.comap iotaD).subtype) = 2 ^ 41 := by
    rw [Subgroup.card_map_of_injective (Ptwo.comap iotaD).subtype_injective, hK]
  have hidx : (K.map (Ptwo.comap iotaD).subtype).index = m := by
    have h := (K.map (Ptwo.comap iotaD).subtype).card_mul_index
    rw [hTc, hCm] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  refine ⟨K.map (Ptwo.comap iotaD).subtype, ⟨le_top, IsPGroup.of_card hTc, ?_⟩,
    Subgroup.map_subtype_le K⟩
  rw [Subgroup.relIndex_top_right, hidx]
  exact hm.not_two_dvd_nat

theorem comap_Ptwo_le_Jbar : Ptwo.comap iotaD ≤ Jbar := fun g hg => by
  have h : iotaD g ∈ Jhat := Ptwo_le_Jhat hg
  rw [Jhat_eq_map] at h
  exact (Subgroup.mem_map_iff_mem iotaD_injective).1 h

theorem Jbar_sup_comap_Ntwo : Jbar ⊔ Ntwo.comap iotaD = ⊤ := by
  have hτ : taubar ∈ Ntwo.comap iotaD := tauhat_mem_Ntwo
  rw [eq_top_iff, ← closure_insert_taubar_eq_top (le_sup_left : Jbar ≤ Jbar ⊔ Ntwo.comap iotaD),
    Subgroup.closure_le]
  exact Set.insert_subset_iff.2 ⟨(le_sup_right : Ntwo.comap iotaD ≤ _) hτ, subset_rfl⟩

theorem Jbar_ne_top :
    Jbar ≠ ⊤ := fun h => by
  have h1 := congrArg (fun H : Subgroup Cbar => Nat.card H) h
  simp only [Subgroup.card_top, CFSG.Monster.AxisCount.Baby.natCard_Cbar, natCard_Jbar] at h1
  omega

theorem comap_Ntwo_ne_top :
    Ntwo.comap iotaD ≠ ⊤ :=
  fun h => by
  have h1 := congrArg (fun H : Subgroup Cbar => Nat.card H) h
  simp only [Subgroup.card_top, CFSG.Monster.AxisCount.Baby.natCard_Cbar, natCard_comap_Ntwo]
    at h1
  omega

theorem exists_isLPair_Jbar_comap_Ntwo :
    ∃ T : Subgroup Cbar, IsSylowIn 2 T ⊤ ∧ IsLPair IsCalL0 T Jbar (Ntwo.comap iotaD) := by
  obtain ⟨T, hT, hTP⟩ := exists_isSylowIn_le_comap_Ptwo
  exact ⟨T, hT,
    { le_left := hTP.trans comap_Ptwo_le_Jbar
      le_right := hTP.trans (Subgroup.comap_mono Ptwo_le_Ntwo)
      ne_top_left := Jbar_ne_top
      ne_top_right := comap_Ntwo_ne_top
      not_left := not_hasCompFactor_isCalL0_Jbar
      not_right := not_hasCompFactor_isCalL0_comap_Ntwo
      sup_eq_top := Jbar_sup_comap_Ntwo }⟩

theorem asch54SporGenAt_b :
    Asch54SporGenAt .B := by
  obtain ⟨T, hT, h⟩ := exists_isLPair_Jbar_comap_Ntwo
  let e : Cbar ≃* NativeSporadic.Carrier .B := CFSG.Sporadic.BSchreier.nativeBEquivCbar.symm
  have : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv Cbar e.toEquiv
  exact asch54SporGenAt_of_isLPair_of_card_outer_eq_one (C := NativeSporadic.Carrier .B)
    (CFSG.Sporadic.Bridge.B.nonempty_mulEquiv.map MulEquiv.symm)
    CFSG.RankThree.PartOne.SPOR.card_outer_B (isSylowIn_top_map_mulEquiv hT e) (h.map e)

end CFSG.LocalAnalysis.WeakClosure81

end
