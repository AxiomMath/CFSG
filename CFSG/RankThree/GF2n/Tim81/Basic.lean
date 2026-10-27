module

public import CFSG.RankThree.GF2n.Tim81.Defs
public import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.RankThree.GF2n.Tim77Prop24Core

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

namespace Hyp

theorem le_M (h : Hyp M V) : V ≤ M := h.maxAb.prop.1

theorem le_normalizer (h : Hyp M V) : M ≤ Subgroup.normalizer (V : Set G) := h.maxAb.prop.2.1

theorem isPGroup_V (h : Hyp M V) : IsPGroup 2 V :=
  fun x => ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩

private theorem Q_ne_bot (h : Hyp M V) : inSubgroup (pCore 2) M ≠ ⊥ := by
  obtain ⟨R, hRne, hR2, hMR⟩ := h.maxLocal.1
  have hRM : R ≤ M := by rw [hMR]; exact Subgroup.le_normalizer
  have hRQ : R ≤ inSubgroup (pCore 2) M :=
    le_inSubgroup_pCore hRM (by rw [hMR]) hR2
  intro hQ
  exact hRne (le_bot_iff.mp (hRQ.trans_eq hQ))

theorem ne_bot (h : Hyp M V) : V ≠ ⊥ := by
  intro hbot
  set Q : Subgroup G := inSubgroup (pCore 2) M with hQdef
  have hQne : Q ≠ ⊥ := Q_ne_bot h
  have hQ2 : IsPGroup 2 Q := (inSubgroup_pCore_two M).1
  set Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G) with hZdef
  have hZne : Z ≠ ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
    haveI : Nontrivial ↥(Subgroup.center ↥Q) := hQ2.center_nontrivial
    obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥Q)
    have hwQ : ((w : ↥Q) : G) ∈ Q := (w : ↥Q).2
    have hwC : ((w : ↥Q) : G) ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨q, hq⟩)
    have hwne : ((w : ↥Q) : G) ≠ 1 := by
      intro hw
      exact hw1 (Subtype.ext (Subtype.ext hw))
    intro hZ
    have hmem : ((w : ↥Q) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hZ]
      exact Subgroup.mem_inf.mpr ⟨hwQ, hwC⟩
    exact hwne (Subgroup.mem_bot.mp hmem)
  have hZM : Z ≤ M := inf_le_left.trans (inSubgroup_pCore_two M).2.1
  have hMZ : M ≤ Subgroup.normalizer (Z : Set G) := fun m hm =>
    mem_normalizer_inf ((inSubgroup_pCore_two M).2.2 hm)
      (mem_normalizer_centralizer ((inSubgroup_pCore_two M).2.2 hm))
  have hZc : IsMulCommutative Z := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    exact Subgroup.mem_centralizer_iff.mp y.2.2 x.1 x.2.1
  have hZV : Z ≤ V := h.maxAb.le_of_ge ⟨hZM, hMZ, hZc⟩ (by rw [hbot]; exact bot_le)
  exact hZne (le_bot_iff.mp (hZV.trans_eq hbot))

theorem normalizer_eq (h : Hyp M V) : Subgroup.normalizer (V : Set G) = M := by
  by_contra hne
  exact h.maxLocal.2 _ (lt_of_le_of_ne h.le_normalizer (Ne.symm hne))
    ⟨V, h.ne_bot, h.isPGroup_V, rfl⟩

theorem le_Q (h : Hyp M V) : V ≤ inSubgroup (pCore 2) M :=
  le_of_isMulCommutative_normal h.fitting h.le_M h.le_normalizer h.maxAb.prop.2.2

theorem Pc_le_M (h : Hyp M V) : Pc M V ≤ M :=
  inf_le_left.trans (inSubgroup_pCore_two M).2.1

theorem le_Pc (h : Hyp M V) : V ≤ Pc M V :=
  le_inf h.le_Q (Subgroup.le_centralizer_iff_isMulCommutative.mpr h.maxAb.prop.2.2)

theorem le_normalizer_Pc (h : Hyp M V) : M ≤ Subgroup.normalizer (Pc M V : Set G) :=
  fun m hm => mem_normalizer_inf ((inSubgroup_pCore_two M).2.2 hm)
    (mem_normalizer_centralizer (h.le_normalizer hm))

private theorem centralizer_P_and_frattini_le (h : Hyp M V) :
    Subgroup.centralizer
        (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) = V ∧
      inSubgroup frattini
        (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤ V := by
  have hα := tim78_2_9_alpha h.fitting h.le_M h.le_normalizer h.maxAb.prop.2.2 (rfl : _ = _)
  have hβ := tim78_2_9_beta_of_elementary h.fitting h.maxAb (fun x hx => h.elem.2 x hx)
    (rfl : _ = _)
  have hCM : Subgroup.centralizer
      (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤ M := by
    intro c hc
    obtain ⟨⟨x, hxV⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne_bot
    have hxP : x ∈ inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) :=
      (hβ.2 ▸ hxV).1
    have hcx : c * x = x * c :=
      (Subgroup.mem_centralizer_iff.mp hc x hxP).symm
    exact h.normalizer_eq ▸ Tim77.mem_normalizer_of_commute_of_isTI h.ti hxV
      (fun h1 => hx1 (Subtype.ext h1)) hcx
  have hVC : V ≤ Subgroup.centralizer
      (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp hp.2 v hv).symm
  refine ⟨le_antisymm (fun c hc => ?_) hVC, hβ.1⟩
  have hc' : c ∈ M ⊓ Subgroup.centralizer
      (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
    ⟨hCM hc, hc⟩
  rw [hα, ← hβ.2] at hc'
  exact hc'

theorem centralizer_Pc (h : Hyp M V) : Subgroup.centralizer (Pc M V : Set G) = V :=
  (centralizer_P_and_frattini_le h).1

theorem frattini_Pc_le (h : Hyp M V) : inSubgroup frattini (Pc M V) ≤ V :=
  (centralizer_P_and_frattini_le h).2

theorem centralizer_le_M (h : Hyp M V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ M := by
  intro c hc
  have hcv : c * v = v * c :=
    (Subgroup.mem_centralizer_iff.mp hc v (Set.mem_singleton v)).symm
  exact h.normalizer_eq ▸ Tim77.mem_normalizer_of_commute_of_isTI h.ti hv hv1 hcv

theorem normalizer_le_M (h : Hyp M V) {U : Subgroup G} (hU : U ≤ V) (hU1 : U ≠ ⊥) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  intro g hg
  have hgU : conjSubgroup g U = U := conjSubgroup_eq_self_iff.mpr hg
  have hle : U ≤ V ⊓ conjSubgroup g V := by
    refine le_inf hU ?_
    calc U = conjSubgroup g U := hgU.symm
      _ ≤ conjSubgroup g V := Subgroup.map_mono hU
  have hne : V ⊓ conjSubgroup g V ≠ ⊥ := by
    intro hbot
    exact hU1 (le_bot_iff.mp (hle.trans_eq hbot))
  have hVg : conjSubgroup g V = V := conjSubgroup_eq_of_isTI h.ti hne
  exact h.normalizer_eq ▸ conjSubgroup_eq_self_iff.mp hVg

theorem center_sylow_le (h : Hyp M V) {S : Subgroup G} (hSM : S ≤ M)
    (hS : IsPGroup 2 S) (hQS : inSubgroup (pCore 2) M ≤ S) :
    S ⊓ Subgroup.centralizer (S : Set G) ≤ V := by
  intro z hz
  have hzC : z ∈ Subgroup.centralizer
      (inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp hz.2 p (hQS hp.1)
  rw [← h.centralizer_Pc]
  exact hzC

private theorem exists_mem_normalizer_not_mem {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hne : U ≠ T) :
    ∃ y ∈ T, y ∈ Subgroup.normalizer (U : Set G) ∧ y ∉ U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hlt : U.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    exact le_antisymm hUT (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥T) (U.subgroupOf T) hlt
  obtain ⟨y, hyN, hyU⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hUT, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyU (Subgroup.mem_subgroupOf.mpr h)⟩

theorem isSylow_of_sylow_M (h : Hyp M V) :
    ∀ S : Sylow 2 M, ∃ T : Sylow 2 G, (T : Subgroup G) = (S : Subgroup M).map M.subtype := by
  intro S
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup G := (S : Subgroup M).map M.subtype with hS'def
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map M.subtype
  have hQS : inSubgroup (pCore 2) M ≤ S' := by
    have hp : pCore 2 M ≤ (S : Subgroup M) :=
      (CFSG.pCore_isPGroup (p := 2) (G := M)).le_sylow_of_normal S
    simpa [hS'def, inSubgroup] using Subgroup.map_mono (f := M.subtype) hp
  obtain ⟨T, hTS⟩ := hS'2.exists_le_sylow
  refine ⟨T, ?_⟩
  by_contra hne
  have hne' : S' ≠ (T : Subgroup G) := fun h => hne h.symm
  obtain ⟨y, hyT, hyN, hyS'⟩ :=
    exists_mem_normalizer_not_mem T.isPGroup' hTS hne'
  set ZS : Subgroup G := (Subgroup.center ↥S').map S'.subtype with hZSdef
  have hZS_le : ZS ≤ S' ⊓ Subgroup.centralizer (S' : Set G) := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨s, hs⟩)⟩
  have hZSV : ZS ≤ V :=
    hZS_le.trans (h.center_sylow_le (Subgroup.map_subtype_le (S : Subgroup M)) hS'2 hQS)
  have hS'ne : S' ≠ ⊥ := by
    intro hbot
    exact Q_ne_bot h (le_bot_iff.mp (hQS.trans_eq hbot))
  have hZSne : ZS ≠ ⊥ := by
    haveI : Nontrivial ↥S' := (Subgroup.nontrivial_iff_ne_bot S').mpr hS'ne
    haveI : Nontrivial ↥(Subgroup.center ↥S') := hS'2.center_nontrivial
    obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥S')
    have hwmem : ((w : ↥S') : G) ∈ ZS := ⟨w.1, w.2, rfl⟩
    have hwne : ((w : ↥S') : G) ≠ 1 := by
      intro hw
      exact hw1 (Subtype.ext (Subtype.ext hw))
    intro hbot
    exact hwne (Subgroup.mem_bot.mp (hbot ▸ hwmem))
  have hyNZS : y ∈ Subgroup.normalizer (ZS : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := S') (Subgroup.center ↥S') hyN
  have hyM : y ∈ M := h.normalizer_le_M hZSV hZSne hyNZS
  have hTM : (T : Subgroup G) ⊓ M = S' := by
    have hW2 : IsPGroup 2 ((T : Subgroup G).subgroupOf M) := T.isPGroup'.comap_subtype
    have hSleW : (S : Subgroup M) ≤ (T : Subgroup G).subgroupOf M := fun s hs =>
      Subgroup.mem_subgroupOf.mpr (hTS (Subgroup.mem_map_of_mem M.subtype hs))
    have hWeq : (T : Subgroup G).subgroupOf M = (S : Subgroup M) :=
      S.is_maximal' hW2 hSleW
    rw [← Subgroup.subgroupOf_map_subtype (T : Subgroup G) M, hWeq, ← hS'def]
  exact hyS' (hTM ▸ ⟨hyT, hyM⟩)

end Hyp

end CFSG.RankThree.GF2n.Tim81
