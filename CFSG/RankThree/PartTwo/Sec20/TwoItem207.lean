module

public import CFSG.RankThree.PartTwo.Sec20.TwoFinal
public import CFSG.RankThree.PartTwo.Sec20.TwoAlt20
public import CFSG.RankThree.PartTwo.Sec20.TwoThetaApply
public import CFSG.RankThree.PartTwo.Sec20.TwoO2Y
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSevenG
public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSevenStruct
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofSevenY
public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Image
public import CFSG.RankThree.PartTwo.Sec20.TwoThetaFStar
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofThetaCert
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Final
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofGTwoThree
import CFSG.RankThree.PartTwo.Sec3.Sims321Count

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_inf_le_of_hyp201 {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M := by
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hBE : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) := Late.isElemAbelian_of_le hA.1 inf_le_left
  exact (normalizer_le_gamma inf_le_left (two_le_pRank_of_elemAbelian hBE h9.ge)).trans
    h.mem_scriptM.2

theorem card_map_inf_of_card_nine {L B : Subgroup G} (hBL : B ≤ L) (hB9 : Nat.card B = 9) :
    Nat.card ((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (hB9.trans (by norm_num))
  have hB3L : IsPGroup 3 (B.subgroupOf L) := hB3.comap_subtype
  have h1 := card_eq_card_map_mul_inf_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (B.subgroupOf L)
  rw [QuotientGroup.ker_mk', card_inf_eq_one_of_isPGroup hB3L CFSG.pCore_isPGroup, mul_one,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB9] at h1
  exact h1.symm

theorem injective_mk_inf_of_isPGroup {A L : Subgroup G} (hB3 : IsPGroup 3 (A ⊓ L : Subgroup G)) :
    Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      ((A ⊓ L).subgroupOf L).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB3L : IsPGroup 3 ((A ⊓ L).subgroupOf L) := hB3.comap_subtype
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  have h1 : (x : ↥L) ∈ (A ⊓ L).subgroupOf L ⊓ CFSG.pCore 2 ↥L := ⟨x.2, hx⟩
  have hbot : (A ⊓ L).subgroupOf L ⊓ CFSG.pCore 2 ↥L = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_inf_eq_one_of_isPGroup hB3L CFSG.pCore_isPGroup)
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem map_autIn_le_of_normalizer_le {A M L : Subgroup G} (hAM : A ≤ M)
    (hB3 : IsPGroup 3 (A ⊓ L : Subgroup G))
    (hNB : Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M) :
    (Sec4.autIn ⊤ (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))).map
        (MulAut.congr (quotientRestrictEquiv inf_le_right
          (injective_mk_inf_of_isPGroup hB3)).symm).toMonoidHom ≤
      Sec4.autIn M (A ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBL : A ⊓ L ≤ L := inf_le_right
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set β := quotientRestrictEquiv hBL (injective_mk_inf_of_isPGroup hB3) with hβ
  rintro _ ⟨τ, hτ, rfl⟩
  obtain ⟨z, hzN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) z
  obtain ⟨y, hy, m, hm, rfl⟩ := exists_mul_of_mk_mem_normalizer hBL hB3 hzN
  obtain ⟨b, hb, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hbB : ((b : ↥L) : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb
  have hnN : ((b : G) * (m : G)) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    mul_mem (Subgroup.le_normalizer hbB) hm
  refine Sec4.mem_autIn_iff.mpr ⟨(b : G) * m, hnN, M.mul_mem (hAM hbB.1) (hNB hm), ?_⟩
  have ho1 : π o = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ho
  apply MulEquiv.ext
  intro w
  apply β.injective
  rw [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [Sec4.normalizerMonoidHom_apply_coe, quotientRestrictEquiv_apply,
    quotientRestrictEquiv_apply]
  have hval : (⟨((A ⊓ L).normalizerMonoidHom ⟨(b : G) * m, hnN⟩ w : G),
      hBL ((A ⊓ L).normalizerMonoidHom ⟨(b : G) * m, hnN⟩ w).2⟩ : ↥L) =
      b * m * ⟨w, hBL w.2⟩ * (b * m)⁻¹ := by
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hval, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_mul, ho1, mul_one]

theorem exists_quaternion_le_autIn_of_facts {A M L : Subgroup G} (hAM : A ≤ M)
    (hB3 : IsPGroup 3 (A ⊓ L : Subgroup G)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hNB : Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M)
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2))) :
    ∃ Q : Subgroup (MulAut ↥(A ⊓ L)), Q ≤ Sec4.autIn M (A ⊓ L) ∧
      Nonempty (↥Q ≃* QuaternionGroup 2) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set Bb := ((A ⊓ L).subgroupOf L).map π with hBb
  obtain ⟨e⟩ := hLq
  set e' := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  have hBb' : Nat.card (Bb.map e'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective,
      card_map_inf_of_card_nine inf_le_right h9]
  obtain ⟨q⟩ := KFacts.L34.nonempty_automizer_of_card_eq_nine
    KFacts.L34.card_galoisField_two_two hBb'
  let qB : Sec4.autIn ⊤ Bb ≃* QuaternionGroup 2 :=
    (KFacts.L34.automizerEquivAutIn Bb).symm.trans
      ((CFSG.RankThree.Asc83Table.automizerCongr e' Bb).trans q)
  set κ := MulAut.congr (quotientRestrictEquiv inf_le_right
    (injective_mk_inf_of_isPGroup hB3)).symm with hκ
  refine ⟨(Sec4.autIn ⊤ Bb).map κ.toMonoidHom, map_autIn_le_of_normalizer_le hAM hB3 hNB, ⟨?_⟩⟩
  exact ((Sec4.autIn ⊤ Bb).equivMapOfInjective κ.toMonoidHom κ.injective).symm.trans qB

@[expose] def Item207Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → Hyp1921 G A M N L → T ≤ N →
      kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N

theorem item207Two_of_kfacts
    (h432 : Sec4.Item4_32Comp) (h41 : Sec4.Item4_1LargePrime) (hG2 : Sec17.KS176GTwo)
    (hK : KF207Theta) (hKΘ : KF207ThetaTwo) (h1912 : Item1912)
    (h194 : Sec19.Item194UsedWide3) (h23 : Item1923) (h204 : Item204Two) (h205 : Item205Two) :
    Item207Two := by
  intro G _ _ A M L N c T hT hyp hTN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hCK
  have hA : Alt20 G A M L N c := alt20_of_hyp1921 h1912 h194 h23 hyp hT.centralizer_eq
  obtain ⟨h1, -, h3, -, -⟩ := h205 G A M L N c T hT hyp
  have h204' := h204 G A M L N c T hT hyp
  have hN := hA.eq_normalizer
  have hAL := hA.le_normalizer
  have hLq := hA.quotient_iso
  have hLp : ⁅L, L⁆ = L := Sec18.commutator_eq_of_mem_oTwoComponentsIn hyp.mem_oTwoComponentsIn
  have h9 := hA.card_inf
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hA.sylow_inf.isPGroup
  have hNBM := normalizer_inf_le_of_hyp201 hT.toHyp201 h9
  have hAM : A ≤ M := le_of_hyp201 hT.toHyp201
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hcN : c ∈ N := hN ▸ hAL hcA
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have h206 := item206One_core Sec3.Sims321.item321Count_holds hT h9
    (exists_quaternion_le_autIn_of_facts hAM hB3 h9 hNBM hLq) hA.normal_inf_sup hA.K_mem
    h204' h1 h3
  have hE := step207E_core Sec3.Sims321.item321Split_holds hT hN hAL hA.K_mem hA.K_type h204'
    h1 h3 hTN hCK
  have hgen := step207Gen_core hT hN hLq hA.not_le hA.pCoreOf_le hA.relIndex_inf
    (card_map_inf_of_card_nine inf_le_right h9)
    (Late.Hyp1921.map_inf_eq_normalizer_of hyp inf_le_right h9 hNBM hA.not_le hA.pCoreOf_le).ge
    hTN
  have hLE := step207LE_core hT hN hAL hLq hA.pCoreOf_le hA.sylow_inf hLp h3 h206 hgen hTN
  obtain ⟨x, hxK, hxB, hcx, hKK0⟩ := step207Struct_core Sec3.Sims321.item321Split_holds hT hN
    hAL hA.K_mem hA.K_type hA.normal_inf_sup h204' h1 h3 hTN hCK
  have hcyc := step207YCyclic_core h432 h41 hG2 hT hN hAL hA.sylow_top h3 hTN hCK hE hcx
  have hθ := step207YTheta_core hK hT hLq hLp hLE hcyc
  set F := fTwenty M N c T with hFdef
  set Y := normalClosureIn (Subgroup.centralizer (F : Set G)) (x * c * x⁻¹) with hYdef
  have hF1 : F ≠ ⊥ := Res5.fTwenty_ne_bot_core hT hN hAL h3 hTN hA.K_not_le hE
  have hFZ : F ≤ zTwenty T := inf_le_left
  have hF2 : IsPGroup 2 F := hT.sylow.isPGroup.to_le
    (hFZ.trans fun z hz => (mem_and_commute_of_mem_zTwenty hz).1)
  have hTC : T ≤ Subgroup.centralizer (F : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact ((mem_and_commute_of_mem_zTwenty (hFZ hf)).2 t ht).symm
  have hFC : F ≤ Subgroup.centralizer (F : Set G) := fun f hf =>
    hTC ((mem_and_commute_of_mem_zTwenty (hFZ hf)).1)
  have hLC : L ≤ Subgroup.centralizer (F : Set G) :=
    hLE.trans (Subgroup.centralizer_le fun z hz => (inf_le_right : F ≤ eTwenty M N c T) hz)
  have hYC : Y ≤ Subgroup.centralizer (F : Set G) := normalClosureIn_le hcx
  have hCY : Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_normalClosureIn _ _
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) := eq_zpowers_sup_inf_core hT hLq h9 (by
    intro hc1
    have := hA.orderOf_c
    rw [hc1, orderOf_one] at this
    norm_num at this)
  have hxM : x ∈ M := hKM hxK
  have hAx : A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.centralizer (F : Set G) := by
    have hB : (A ⊓ L).map (MulAut.conj x).toMonoidHom = A ⊓ L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxB
    rw [hAeq, Subgroup.map_sup, hB, MonoidHom.map_zpowers]
    refine sup_le ?_ (inf_le_right.trans hLC)
    rw [Subgroup.zpowers_le]
    exact hcx
  have hO2C : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (F : Set G)) ≠ ⊥ := by
    intro hbot
    apply hF1
    rw [eq_bot_iff, ← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hFC
      (Subgroup.centralizer_le_normalizer _) hF2
  have hO2Y := TwoTheta.pCoreOf_le_of_hyp191 hyp.hyp191
    ((isE27_of_mem_partTwoE hT.mem_partTwoE).map (MulAut.conj x))
    (TwoTheta.mem_scriptM_gamma_map_conj hT.mem_scriptM hxM) hAx hO2C hYC hCY hTC hT.sylow
  have h3G : 3 ∣ Nat.card G := by
    have h27 := (isE27_of_mem_partTwoE hT.mem_partTwoE).2
    have h := Subgroup.card_subgroup_dvd_card A
    rw [h27] at h
    exact (show 3 ∣ 27 by norm_num).trans h
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) :=
    TwoTheta.y_le_normalizer hKΘ hT.toTheoremFourHyp h3G hF2 hF1
      (hYC.trans (Subgroup.centralizer_le_normalizer _)) (hLC.trans hCY) hLp hLq hθ
      ((hO2Y.trans hTN).trans hN.le)
  have hI : iTwenty M N c ≤ N := (normalClosureIn_le
    (Subgroup.mem_inf.mpr ⟨self_mem_normalClosureIn M c, hcN⟩)).trans
    inf_le_right
  exact hA.K_not_le (TwoTheta.le_of_struct hKK0 (hYN.trans hN.ge) hI hA.pCoreOf_K_le)

section Holds


theorem item207Two_of (h1912 : Item1912) (h194 : Sec19.Item194UsedWide3) (h23 : Item1923)
    (h204 : Item204Two) (h205 : Item205Two) : Item207Two :=
  item207Two_of_kfacts (Sec4.item4_32Comp_of_three Sec4.RonanK432.k432InnerThree_holds
    Sec4.RonanK432.k432List_holds) Sec4.diag_item41LargePrime_holds Sec17.ks176GTwo_holds
    kF207Theta_proof kF207ThetaTwo h1912 h194 h23 h204 h205

end Holds

end CFSG.RankThree.PartTwo.Sec20
