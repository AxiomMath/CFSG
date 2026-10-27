module

public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1L112Step3
public import CFSG.Quasithin.H13.KGFactM22Index
public import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop
public import CFSG.Quasithin.EmptyFaithful.S152VM22

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG

variable {S T : Type} [Group S] [Group T]

theorem card_eq_card_mul_card_pCore (H : Subgroup S)
    (φ : ↥H ⧸ CFSG.pCore 2 ↥H ≃* T) :
    Nat.card ↥H = Nat.card T * Nat.card (CFSG.pCore 2 ↥H) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H),
    Nat.card_congr φ.toEquiv]

theorem two_mul_card_le_card_of_pCore_ne_bot [Finite S] (H : Subgroup S)
    (hcore : CFSG.pCore 2 ↥H ≠ ⊥) (φ : ↥H ⧸ CFSG.pCore 2 ↥H ≃* T) :
    Nat.card T * 2 ≤ Nat.card ↥H := by
  have h1 : 1 < Nat.card (CFSG.pCore 2 ↥H) :=
    (Subgroup.one_lt_card_iff_ne_bot (CFSG.pCore 2 ↥H)).2 hcore
  rw [card_eq_card_mul_card_pCore H φ]
  exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h1)

theorem noPerfectTwoCoreSection_of_card_lt [Finite S]
    (hS : Nat.card S < 2 * Nat.card T) : NoPerfectTwoCoreSection S T := by
  intro H _hperf hcore
  refine ⟨fun φ => ?_⟩
  have hle : Nat.card ↥H ≤ Nat.card S := Subgroup.card_le_card_group (H := H)
  have hge : Nat.card T * 2 ≤ Nat.card ↥H :=
    two_mul_card_le_card_of_pCore_ne_bot H hcore φ
  omega

theorem noPerfectTwoCoreSection_alt7_alt7 :
    NoPerfectTwoCoreSection ↥(alternatingGroup (Fin 7)) ↥(alternatingGroup (Fin 7)) := by
  apply noPerfectTwoCoreSection_of_card_lt
  have h7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  rw [h7]
  norm_num

theorem noPerfectTwoCoreSection_alt7_m22 :
    NoPerfectTwoCoreSection ↥(alternatingGroup (Fin 7))
      CFSG.ComponentClassification.WittDesign.M22 := by
  apply noPerfectTwoCoreSection_of_card_lt
  have h7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hM : Nat.card CFSG.ComponentClassification.WittDesign.M22 = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  rw [h7, hM]
  norm_num

theorem noPerfectTwoCoreSection_m22_m22 :
    NoPerfectTwoCoreSection CFSG.ComponentClassification.WittDesign.M22
      CFSG.ComponentClassification.WittDesign.M22 := by
  apply noPerfectTwoCoreSection_of_card_lt
  have hpos : 0 < Nat.card CFSG.ComponentClassification.WittDesign.M22 := Nat.card_pos
  omega

theorem noPerfectTwoCoreSection_m22_alt7 :
    NoPerfectTwoCoreSection CFSG.ComponentClassification.WittDesign.M22
      ↥(alternatingGroup (Fin 7)) := by
  intro H _hperf hcore
  refine ⟨fun φ => ?_⟩
  have h7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hM : Nat.card CFSG.ComponentClassification.WittDesign.M22 = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hge : 5040 ≤ Nat.card ↥H := by
    have h := two_mul_card_le_card_of_pCore_ne_bot H hcore φ
    rw [h7] at h
    omega
  have hidx : H.index < 176 := by
    have hmul := Subgroup.card_mul_index H
    rw [hM] at hmul
    by_contra h
    have h176 : 176 ≤ H.index := Nat.le_of_not_lt h
    have h' : 5040 * 176 ≤ Nat.card ↥H * H.index := Nat.mul_le_mul hge h176
    rw [hmul] at h'
    norm_num at h'
  rcases CFSG.Quasithin.H13.KGM22.factM22SubgroupIndex_holds H hidx with
    htop | ⟨g, hg⟩ | ⟨g, hg⟩
  ·
    have hbot : CFSG.pCore 2 ↥H = ⊥ := by
      rw [htop]
      haveI : IsSimpleGroup CFSG.ComponentClassification.WittDesign.M22 :=
        CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
      have hnot2 : ¬ IsPGroup 2 CFSG.ComponentClassification.WittDesign.M22 := by
        simpa only [CFSG.Blueprint.NativeSporadic.Carrier] using
          CFSG.Quasithin.S152V.not_isPGroup_M22
      exact CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_equiv
        (Subgroup.topEquiv (G := CFSG.ComponentClassification.WittDesign.M22))
        (CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_simple hnot2)
    exact hcore hbot
  ·
    have hbot : CFSG.pCore 2 ↥H = ⊥ := by
      rw [hg]
      haveI : IsSimpleGroup
          (MulAction.stabilizer CFSG.ComponentClassification.WittDesign.M22
            (0 : Fin 22)) :=
        CFSG.ComponentClassification.WittDesign.isSimpleGroup_stabilizer (a := 0)
      have hcard : Nat.card
          (MulAction.stabilizer CFSG.ComponentClassification.WittDesign.M22
            (0 : Fin 22)) = 20160 :=
        CFSG.ComponentClassification.WittDesign.card_stabilizer_point 0
      have hnot2 : ¬ IsPGroup 2
          (MulAction.stabilizer CFSG.ComponentClassification.WittDesign.M22
            (0 : Fin 22)) := by
        intro h2
        have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨n, hn⟩ := h2.exists_card_eq
        rw [hcard] at hn
        have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
      exact CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_equiv
        (MulEquiv.subgroupMap (MulAut.conj g)
          (MulAction.stabilizer CFSG.ComponentClassification.WittDesign.M22
            (0 : Fin 22))).symm
        (CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_simple hnot2)
    exact hcore hbot
  ·
    have hhex : Nat.card (CFSG.Quasithin.Asc94.m22HexStab) = 5760 := by
      rw [← CFSG.Quasithin.M22Witt.stabilizer_m22HexadF]
      exact CFSG.ComponentClassification.WittDesign.card_stabilizer_hexad
        CFSG.Quasithin.M22Witt.m22HexadF_mem_hexads
    have hHcard : Nat.card ↥H = 5760 := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hhex
    have hQ := card_eq_card_mul_card_pCore H φ
    rw [hHcard, h7] at hQ
    have hQge : 2 ≤ Nat.card (CFSG.pCore 2 ↥H) :=
      Nat.succ_le_of_lt ((Subgroup.one_lt_card_iff_ne_bot (CFSG.pCore 2 ↥H)).2 hcore)
    omega

theorem noPerfectTwoCoreSection_congr {S S' T T' : Type} [Group S] [Group S'] [Group T]
    [Group T'] (e : S ≃* S') (f : T ≃* T')
    (h : NoPerfectTwoCoreSection S T) : NoPerfectTwoCoreSection S' T' := by
  intro H' hperf' hcore'
  refine ⟨fun φ => ?_⟩
  let H : Subgroup S := H'.comap e.toMonoidHom
  have hHmap : H.map e.toMonoidHom = H' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective H'
  let eH : ↥H ≃* ↥H' :=
    (MulEquiv.subgroupMap e H).trans (MulEquiv.subgroupCongr hHmap)
  have hperf : Group.IsPerfect ↥H := by
    haveI := hperf'
    exact Group.IsPerfect.ofSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  have hcore : CFSG.pCore 2 ↥H ≠ ⊥ := by
    intro hbot
    apply hcore'
    rw [← CFSG.pCore_map_iso 2 eH, hbot, Subgroup.map_bot]
  have hq : (↥H ⧸ CFSG.pCore 2 ↥H) ≃* (↥H' ⧸ CFSG.pCore 2 ↥H') :=
    QuotientGroup.congr (CFSG.pCore 2 ↥H) (CFSG.pCore 2 ↥H') eH
      (CFSG.pCore_map_iso 2 eH)
  exact (h H hperf hcore).false (hq.trans (φ.trans f.symm))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
