module

public import CFSG.Quasithin.Recognition.St84.J2ModelY2
public import CFSG.Quasithin.Recognition.St84.J2ModelY3
public import CFSG.Quasithin.Recognition.St84.J2VertexA

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.A312J2 CFSG.Quasithin.F112R.J2L CFSG.Quasithin.J2Cz
open CFSG.Quasithin.F112R.St84.Heis CFSG.Quasithin.F112R.St84.J2Model
open CFSG.Sporadic.SmallOddCore

variable {G : Type} [Group G]

theorem orderOf_bm : orderOf bm = 3 := by
  have hne : bm ≠ 1 := by
    intro h
    have h1 : κHom e1 = κHom (βM e1) := by
      simpa [h] using bm_conj e1
    have h2 : e1 = βM e1 := κHom_injective h1
    have h3 : βM e1 ≠ e1 := by
      rw [beta_e1]
      decide +kernel
    exact h3 h2.symm
  exact orderOf_eq_prime (p := 3) bm_pow_three hne

noncomputable def conjY3
    (g : ↥(j2CtxA.Y 3)) :
    ↥(j2CtxA.Y 3) ≃* ↥(j2CtxA.Y 3) :=
  @MulAut.conj ↥(j2CtxA.Y 3) (Subgroup.toGroup (j2CtxA.Y 3)) g

theorem exists_mulEquiv_map_sylowTwoOf_Y3 [Finite G]
    {L T : Subgroup G}
    (e : ↥L ≃* ↥(j2CtxA.Y 3)) (hT : IsSylowTwoOf T L) :
    ∃ e' : ↥L ≃* ↥(j2CtxA.Y 3),
      (T.subgroupOf L).map (e' : ↥L →* ↥(j2CtxA.Y 3)) =
        j2CtxA.S.subgroupOf (j2CtxA.Y 3) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₂, hS₂⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow hT
  have hSY3 : IsSylowTwoOf j2CtxA.S (j2CtxA.Y 3) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right j2A_sylow (j2CtxA.S_le_Y 3) le_top
  obtain ⟨S₃, hS₃⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow hSY3
  have hsurj : Function.Surjective (e : ↥L →* ↥(j2CtxA.Y 3)) := e.surjective
  let S₂' : Sylow 2 ↥(j2CtxA.Y 3) := S₂.mapSurjective hsurj
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(j2CtxA.Y 3) S₂' S₃
  refine ⟨e.trans (conjY3 g), ?_⟩
  have hcoe : (S₂' : Subgroup ↥(j2CtxA.Y 3)) =
      (S₂ : Subgroup ↥L).map (e : ↥L →* ↥(j2CtxA.Y 3)) := rfl
  have hsmul : ((g • S₂' : Sylow 2 ↥(j2CtxA.Y 3)) : Subgroup ↥(j2CtxA.Y 3)) =
      (S₂' : Subgroup ↥(j2CtxA.Y 3)).map
        (conjY3 g : ↥(j2CtxA.Y 3) →* ↥(j2CtxA.Y 3)) :=
    Sylow.coe_subgroup_smul
  calc (T.subgroupOf L).map (e.trans (conjY3 g) : ↥L →* ↥(j2CtxA.Y 3))
      = ((T.subgroupOf L).map (e : ↥L →* ↥(j2CtxA.Y 3))).map
          (conjY3 g : ↥(j2CtxA.Y 3) →* ↥(j2CtxA.Y 3)) := by
        rw [MulEquiv.toMonoidHom_trans, Subgroup.map_map]
    _ = (S₂' : Subgroup ↥(j2CtxA.Y 3)).map
          (conjY3 g : ↥(j2CtxA.Y 3) →* ↥(j2CtxA.Y 3)) := by
        rw [← hS₂]
        exact congrArg
          (fun K => K.map (conjY3 g : ↥(j2CtxA.Y 3) →* ↥(j2CtxA.Y 3))) hcoe.symm
    _ = ((g • S₂' : Sylow 2 ↥(j2CtxA.Y 3)) : Subgroup ↥(j2CtxA.Y 3)) := hsmul.symm
    _ = j2CtxA.S.subgroupOf (j2CtxA.Y 3) := by rw [hg, hS₃]

theorem exists_orderOf_three_mem_normalizer :
    ∃ x ∈ Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J), orderOf x = 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C2 : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 j2C2Gens with hC2
  have hC2card : Nat.card C2 = 1920 := by
    rw [hC2]
    exact j2_C2_concrete.2
  have hT0le : T0m ≤ C2 := by
    rw [hC2]
    exact T0m_le_C2
  have hT0card : Nat.card T0m = 2 ^ 7 := by
    rw [card_T0m]
    norm_num
  have hT0p : IsPGroup 2 T0m := IsPGroup.of_card (n := 7) hT0card
  have hT0sylow : IsSylowTwoOf T0m C2 := by
    refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex hT0le hT0p ?_
    have hrel := Subgroup.relIndex_mul_card (H := T0m) (K := C2)
    rw [inf_eq_left.mpr hT0le, card_T0m, hC2card] at hrel
    have h15 : T0m.relIndex C2 = 15 := by omega
    rw [h15]
    norm_num
  obtain ⟨e⟩ := J2Model.nonempty_C2_equiv_Y3
  obtain ⟨e', he'⟩ := exists_mulEquiv_map_sylowTwoOf_Y3 e hT0sylow
  have hbmC : bm ∈ C2 := by
    rw [hC2]
    exact bm_mem_C2
  let bmC : ↥C2 := ⟨bm, hbmC⟩
  have hbmCord : orderOf bmC = 3 := by
    rw [← Subgroup.orderOf_coe bmC]
    exact orderOf_bm
  have hbmCN : bmC ∈ Subgroup.normalizer ((T0m.subgroupOf C2) : Set ↥C2) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hT0le, Subgroup.mem_subgroupOf]
    simpa [bmC] using bm_mem_normalizer_T0m
  have hbij : Function.Bijective (e' : ↥C2 →* ↥(j2CtxA.Y 3)) :=
    ⟨e'.injective, e'.surjective⟩
  have hmapN : (Subgroup.normalizer ((T0m.subgroupOf C2) : Set ↥C2)).map
        (e' : ↥C2 →* ↥(j2CtxA.Y 3)) =
      Subgroup.normalizer ((j2CtxA.S.subgroupOf (j2CtxA.Y 3)) : Set ↥(j2CtxA.Y 3)) := by
    rw [Subgroup.map_normalizer_eq_of_bijective _ hbij, he']
  have hxN' : e' bmC ∈ Subgroup.normalizer
      ((j2CtxA.S.subgroupOf (j2CtxA.Y 3)) : Set ↥(j2CtxA.Y 3)) := by
    rw [← hmapN]
    exact Subgroup.mem_map_of_mem _ hbmCN
  have hxJ : ((e' bmC : ↥(j2CtxA.Y 3)) : ↥CFSG.Sporadic.J2.J) ∈
      Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J) := by
    have h := hxN'
    rw [← Subgroup.subgroupOf_normalizer_eq (H := j2CtxA.S) (N := j2CtxA.Y 3)
      (j2CtxA.S_le_Y 3), Subgroup.mem_subgroupOf] at h
    exact h
  refine ⟨((e' bmC : ↥(j2CtxA.Y 3)) : ↥CFSG.Sporadic.J2.J), hxJ, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact hbmCord

theorem J2Y.card_normalizer :
    Nat.card (Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J)) = 384 := by
  classical
  set N := Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J) with hN
  have hle : N ≤ j2CtxA.Y 3 ⊓ j2CtxA.Y 2 :=
    le_inf (J2Y.normalizer_le (Or.inr rfl)) (J2Y.normalizer_le (Or.inl rfl))
  have hdvd : Nat.card N ∣ 384 :=
    (Subgroup.card_dvd_of_le hle).trans J2Y.card_inf_dvd
  have h128 : 128 ∣ Nat.card N := by
    have hS : j2CtxA.S ≤ N := fun x hx => Subgroup.le_normalizer hx
    have h := Subgroup.card_dvd_of_le hS
    have hScard : Nat.card ↥j2CtxA.S = 128 := by
      have h2 : twoPart (⊤ : Subgroup ↥CFSG.Sporadic.J2.J) = 2 ^ 7 :=
        CFSG.Quasithin.S1421QA17.twoPart_eq_of_card (n := 7) (m := 4725) (by norm_num) (by
          rw [Subgroup.card_top, CFSG.Sporadic.J2.card_J]
          norm_num)
      rw [IsSylowTwoOf.card_eq j2A_sylow, h2]
      norm_num
    rwa [hScard] at h
  obtain ⟨x, hxN, hxord⟩ := exists_orderOf_three_mem_normalizer
  have h3 : 3 ∣ Nat.card N := by
    have h := Subgroup.orderOf_dvd_natCard (s := N) hxN
    rwa [hxord] at h
  have h384 : 384 ∣ Nat.card N := by
    have hcop : Nat.Coprime 128 3 := by decide
    have h := hcop.mul_dvd_of_dvd_of_dvd h128 h3
    simpa using h
  exact (Nat.dvd_antisymm_iff.mpr ⟨h384, hdvd⟩).symm

theorem J2Y.normalizer_eq_inf :
    Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J) = j2CtxA.Y 3 ⊓ j2CtxA.Y 2 := by
  classical
  set N := Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J) with hN
  have hle : N ≤ j2CtxA.Y 3 ⊓ j2CtxA.Y 2 :=
    le_inf (J2Y.normalizer_le (Or.inr rfl)) (J2Y.normalizer_le (Or.inl rfl))
  have hNcard : Nat.card N = 384 := J2Y.card_normalizer
  have hlecard : Nat.card N ≤ Nat.card ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hinfcard : Nat.card ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) = 384 := by
    have h1 : Nat.card ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) ≤ 384 :=
      Nat.le_of_dvd (by norm_num) J2Y.card_inf_dvd
    have h2 : 384 ≤ Nat.card ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) := by
      rw [← hNcard]
      exact hlecard
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hinfcard, hNcard])

theorem card_inf_normalizer_of_mulEquiv [Finite G]
    {L T : Subgroup G} (e : ↥L ≃* ↥(j2CtxA.Y 3))
    (hT : IsSylowTwoOf T L) :
    Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set G)) = 384 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he⟩ := exists_mulEquiv_map_sylowTwoOf_Y3 e hT
  set NJ := Subgroup.normalizer (j2CtxA.S : Set ↥CFSG.Sporadic.J2.J) with hNJ
  have hsub : Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set G)) =
      Nat.card ↥((Subgroup.normalizer (T : Set G)).subgroupOf L) := by
    rw [inf_comm L (Subgroup.normalizer (T : Set G)),
      ← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (T : Set G)) L]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        Subgroup.normalizer (T : Set G) ⊓ L ≤ L)).symm.toEquiv
  rw [hsub, Subgroup.subgroupOf_normalizer_eq hT.1]
  have hbij : Function.Bijective (e' : ↥L →* ↥(j2CtxA.Y 3)) :=
    ⟨e'.injective, e'.surjective⟩
  let H : Subgroup ↥(j2CtxA.Y 3) :=
    (T.subgroupOf L).map (e' : ↥L →* ↥(j2CtxA.Y 3))
  have hH : H = (j2CtxA.S.subgroupOf (j2CtxA.Y 3) : Subgroup ↥(j2CtxA.Y 3)) := he
  have hmap : Nat.card ↥(Subgroup.normalizer (T.subgroupOf L : Set ↥L)) =
      Nat.card ↥(Subgroup.normalizer (H : Set ↥(j2CtxA.Y 3))) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective (H := T.subgroupOf L) hbij]
    exact (Subgroup.card_map_of_injective e'.injective).symm
  rw [hmap, hH]
  have hY3 : Nat.card ↥(Subgroup.normalizer
      (j2CtxA.S.subgroupOf (j2CtxA.Y 3) : Set ↥(j2CtxA.Y 3))) =
      Nat.card ↥(NJ.subgroupOf (j2CtxA.Y 3)) := by
    rw [Subgroup.subgroupOf_normalizer_eq (j2CtxA.S_le_Y 3)]
  rw [hY3]
  have hinf : Nat.card ↥(NJ.subgroupOf (j2CtxA.Y 3)) = Nat.card ↥NJ := by
    rw [← Subgroup.inf_subgroupOf_right NJ (j2CtxA.Y 3),
      inf_eq_left.mpr (J2Y.normalizer_le (Or.inr rfl))]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (J2Y.normalizer_le (Or.inr rfl))).toEquiv
  rw [hinf]
  exact J2Y.card_normalizer

theorem J2LocalData.nonempty_mulEquiv_borel [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    Nonempty (↥(bigB L2 L1 S) ≃* ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : S ≤ L2 := J2LocalData.S_le_right hF h1 h2 hD
  have hBL : bigB L2 L1 S = L2 ⊓ Subgroup.normalizer (S : Set G) := by
    rw [CFSG.Quasithin.F1.bigB_eq_parabolic_inf (hyp111R_of_vs3_va5 hF h1 h2).symm,
      hD.sup_eq, inf_eq_left.mpr hSL]
  have hBsub : (bigB L2 L1 S).subgroupOf L2 = Subgroup.normalizer (S.subgroupOf L2) := by
    rw [hBL, inf_comm L2 (Subgroup.normalizer (S : Set G)),
      Subgroup.inf_subgroupOf_right (Subgroup.normalizer (S : Set G)) L2]
    exact Subgroup.subgroupOf_normalizer_eq hSL
  obtain ⟨eL⟩ := J2LocalData.nonempty_mulEquiv_model hF h1 h2 hD
  obtain ⟨eY⟩ := J2Model.nonempty_mulEquiv_Y3
  let e₀ : ↥L2 ≃* ↥(j2CtxA.Y 3) :=
    (MulEquiv.subgroupCongr hD.sup_eq).symm.trans (eL.trans eY.symm)
  have hSLsylow : IsSylowTwoOf S L2 := by
    have hcardS : Nat.card S = 2 ^ 7 := J2LocalData.card_S hF h1 h2 hD
    have hcardS128 : Nat.card S = 128 := by
      rw [hcardS]
      norm_num
    have hcardL2 : Nat.card L2 = 1920 := J2LocalData.card_right h2 hD
    refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex hSL
      (IsPGroup.of_card (n := 7) hcardS) ?_
    have hrel := Subgroup.relIndex_mul_card (H := S) (K := L2)
    rw [inf_eq_left.mpr hSL, hcardS128, hcardL2] at hrel
    have h15 : S.relIndex L2 = 15 := by omega
    rw [h15]
    norm_num
  obtain ⟨e, he⟩ := exists_mulEquiv_map_sylowTwoOf_Y3 e₀ hSLsylow
  have htail : ↥(Subgroup.normalizer
        (j2CtxA.S.subgroupOf (j2CtxA.Y 3) : Set ↥(j2CtxA.Y 3))) ≃*
      ↥(j2CtxA.Y 3 ⊓ j2CtxA.Y 2) :=
    (MulEquiv.subgroupCongr
      (Subgroup.subgroupOf_normalizer_eq (j2CtxA.S_le_Y 3)).symm).trans
      ((Subgroup.subgroupOfEquivOfLe (J2Y.normalizer_le (Or.inr rfl))).trans
        (MulEquiv.subgroupCongr J2Y.normalizer_eq_inf))
  have hbij : Function.Bijective (e : ↥L2 →* ↥(j2CtxA.Y 3)) :=
    ⟨e.injective, e.surjective⟩
  let H : Subgroup ↥(j2CtxA.Y 3) :=
    (S.subgroupOf L2).map (e : ↥L2 →* ↥(j2CtxA.Y 3))
  have hH : H = (j2CtxA.S.subgroupOf (j2CtxA.Y 3) : Subgroup ↥(j2CtxA.Y 3)) := he
  have hmap : (Subgroup.normalizer (S.subgroupOf L2 : Set ↥L2)).map
        (e : ↥L2 →* ↥(j2CtxA.Y 3)) =
      Subgroup.normalizer (H : Set ↥(j2CtxA.Y 3)) :=
    Subgroup.map_normalizer_eq_of_bijective (S.subgroupOf L2) hbij
  have hnorm : Subgroup.normalizer (H : Set ↥(j2CtxA.Y 3)) =
      Subgroup.normalizer
        (j2CtxA.S.subgroupOf (j2CtxA.Y 3) : Set ↥(j2CtxA.Y 3)) := by
    rw [hH]
  refine ⟨(Subgroup.subgroupOfEquivOfLe hD.bigB_le_right).symm.trans ?_⟩
  refine (MulEquiv.subgroupCongr hBsub).trans ?_
  refine (Subgroup.equivMapOfInjective
    (Subgroup.normalizer (S.subgroupOf L2 : Set ↥L2))
    (e : ↥L2 →* ↥(j2CtxA.Y 3)) e.injective).trans ?_
  refine (MulEquiv.subgroupCongr hmap).trans ?_
  refine (MulEquiv.subgroupCongr hnorm).trans ?_
  exact htail

end CFSG.Quasithin.F112R.St84
