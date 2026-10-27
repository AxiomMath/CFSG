module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThree
public import CFSG.LocalAnalysis.WeakClosure81.EightTwo
public import CFSG.Quasithin.Background.I62Main

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem conjSubgroup_inf' (g : G) (U W : Subgroup G) :
    conjSubgroup (U ⊓ W) g = conjSubgroup U g ⊓ conjSubgroup W g :=
  Subgroup.map_inf_eq U W (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem isTISetIn_top_of_isTI {V : Subgroup G} (hTI : IsTI V) : IsTISetIn V ⊤ := by
  refine ⟨le_top, fun g _ hg => ?_⟩
  have h := hTI g⁻¹
  have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V = conjSubgroup V g := by
    rw [t75_conjSubgroup_eq, inv_inv]
  rw [hconj] at h
  rcases h with hbot | heq
  · exact hbot
  · exfalso
    have hle : V ≤ conjSubgroup V g := by
      have h2 : V ⊓ conjSubgroup V g ≤ conjSubgroup V g := inf_le_right
      rwa [heq] at h2
    have heq' : V = conjSubgroup V g :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup'])
    exact hg (conjSubgroup_eq_iff_mem_normalizer.mp heq'.symm)

theorem pCoreOf_top_subgroupOf (X : Subgroup G) :
    pCoreOf 2 (⊤ : Subgroup X) = (pCoreOf 2 X).subgroupOf X := by
  have h1 : pCoreOf 2 (⊤ : Subgroup X) = CFSG.pCore 2 ↥X := by
    rw [pCoreOf]
    change (CFSG.pCore 2 (⊤ : Subgroup X)).map
        (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom = CFSG.pCore 2 ↥X
    exact CFSG.pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
  rw [h1]
  exact (openPCoreOf_subgroupOf 2 X).symm

theorem conjSubgroup_mem_omegaSet {V H E W : Subgroup G} (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal) (hW : W ∈ omegaSet V H E) {h : G} (hh : h ∈ H) :
    conjSubgroup W h ∈ omegaSet V H E := by
  rw [mem_omegaSet] at hW ⊢
  obtain ⟨g, rfl, hWE, hWO⟩ := hW
  have hEfix : conjSubgroup E h = E :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (le_normalizer_of_subgroupOf_normal hEH hEnorm hh)
  have hOfix : conjSubgroup (pCoreOf 2 H) h = pCoreOf 2 H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh)
  have hOinv : conjSubgroup (pCoreOf 2 H) h⁻¹ = pCoreOf 2 H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hh))
  refine ⟨g * h, by rw [CFSG.Quasithin.conjSubgroup_conjSubgroup], ?_, ?_⟩
  · intro hbot
    obtain ⟨x, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWE
    have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp x.2).1
    have hxW : (x : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.mp x.2).2
    have hx1 : (x : G) ≠ 1 := fun h1 => hx1' (Subtype.ext h1)
    have hxE' : h⁻¹ * (x : G) * h ∈ E := by
      have hm : h⁻¹ * (x : G) * h ∈ conjSubgroup E h := by
        rw [mem_conjSubgroup_iff]
        rw [show h * (h⁻¹ * (x : G) * h) * h⁻¹ = (x : G) by group]
        exact hxE
      rwa [hEfix] at hm
    have hxW' : h⁻¹ * (x : G) * h ∈ conjSubgroup (conjSubgroup V g) h := by
      rw [mem_conjSubgroup_iff]
      rw [show h * (h⁻¹ * (x : G) * h) * h⁻¹ = (x : G) by group]
      exact hxW
    have hmem : h⁻¹ * (x : G) * h ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hxE', hxW'⟩
    have hne1 : h⁻¹ * (x : G) * h ≠ 1 := by
      intro h1
      apply hx1
      have h2 := congrArg (fun t => h * t * h⁻¹) h1
      simpa [mul_assoc] using h2
    exact hne1 (Subgroup.mem_bot.mp hmem)
  · intro hle
    apply hWO
    have h1 : conjSubgroup (conjSubgroup (conjSubgroup V g) h) h⁻¹ ≤
        conjSubgroup (pCoreOf 2 H) h⁻¹ := Subgroup.map_mono hle
    have hW' : conjSubgroup (conjSubgroup (conjSubgroup V g) h) h⁻¹ = conjSubgroup V g := by
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel, CFSG.Quasithin.conjSubgroup_one]
    rwa [hW', hOinv] at h1

theorem iSub_subgroupOf_normal {V H E : Subgroup G} (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal) :
    ((iSub V H E).subgroupOf H).Normal := by
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun U => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hIleH).2 ?_
  intro h hh
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hOfix : conjSubgroup (pCoreOf 2 H) h = pCoreOf 2 H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh)
  have hmap : conjSubgroup (iSub V H E) h =
      ⨆ U ∈ omegaSet V H E, conjSubgroup (U ⊓ pCoreOf 2 H) h := by
    rw [iSub]
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
  rw [hmap]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun U => iSup_le fun hU => ?_
    have hsub : conjSubgroup (U ⊓ pCoreOf 2 H) h ≤ conjSubgroup U h ⊓ pCoreOf 2 H := by
      rw [conjSubgroup_inf']
      exact inf_le_inf le_rfl (le_of_eq hOfix)
    exact hsub.trans (inf_pCoreOf_le_iSub (conjSubgroup_mem_omegaSet hEH hEnorm hU hh))
  · refine iSup_le fun U => iSup_le fun hU => ?_
    have hUinv : conjSubgroup U h⁻¹ ∈ omegaSet V H E :=
      conjSubgroup_mem_omegaSet hEH hEnorm hU (H.inv_mem hh)
    refine le_iSup₂_of_le (conjSubgroup U h⁻¹) hUinv ?_
    have hconj : conjSubgroup (conjSubgroup U h⁻¹) h = U := by
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel, CFSG.Quasithin.conjSubgroup_one]
    rw [conjSubgroup_inf', hconj, hOfix]

theorem pCoreOf_tiX_eq_tiY {V A : Subgroup G} (h : CFSG.Quasithin.I62.Hyp V A) :
    pCoreOf 2 (V ⊔ A) = CFSG.Quasithin.ASInputs.tiY V A := by
  have hb := h.toBase
  set X := V ⊔ A with hXdef
  have hVX : V ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hUX : CFSG.Quasithin.ASInputs.tiU V A ≤ X := inf_le_left.trans hVX
  have hBX : CFSG.Quasithin.ASInputs.tiB V A ≤ X := inf_le_left.trans hAX
  have hYX : CFSG.Quasithin.ASInputs.tiY V A ≤ X := sup_le hUX hBX
  obtain ⟨x, hxX, hxA⟩ := h.exists_conjSubgroup_eq
  have hAV : conjSubgroup V x = A := by
    rw [← hxA, CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      CFSG.Quasithin.conjSubgroup_one]
  set T : Subgroup ↥X := V.subgroupOf X with hT
  set g : ↥X := ⟨x⁻¹, X.inv_mem hxX⟩ with hg
  have hTg : CFSG.CGT.Timmesfeld75.conjSubgroup g T = A.subgroupOf X := by
    rw [hT, CFSG.Quasithin.I62.tconj_subgroupOf (X := X), hg]
    simp only [inv_inv]
    rw [hAV]
  have hWC : CFSG.CGT.Timmesfeld75.IsWC T := by
    refine ⟨⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hb.comm_V a.2 b.2))⟩⟩, fun y hy =>
      Subtype.ext (by simpa using hb.hV.2 _ hy)⟩, fun t ht ht1 => ⟨fun y hy => ?_,
        fun g' hg' => ?_⟩⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hb.comm_V hy ht)
    · rw [hT, CFSG.Quasithin.I62.tconj_subgroupOf (X := X)] at hg' ⊢
      have ht1' : (t : G) ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
      have hle : conjSubgroup V (g' : G)⁻¹ ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
        intro y hy
        have hyX : y ∈ X := by
          have h1 : (g' : G)⁻¹ * y * ((g' : G)⁻¹)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hy
          rw [inv_inv] at h1
          rw [show y = (g' : G) * ((g' : G)⁻¹ * y * (g' : G)) * (g' : G)⁻¹ by group]
          exact X.mul_mem (X.mul_mem g'.2 (hVX h1)) (X.inv_mem g'.2)
        have h2 := hg' (show (⟨y, hyX⟩ : ↥X) ∈ (conjSubgroup V (g' : G)⁻¹).subgroupOf X from hy)
        rw [Subgroup.mem_centralizer_singleton_iff] at h2 ⊢
        exact congrArg Subtype.val h2
      rw [h.conjSubgroup_eq_of_le_centralizer (X.inv_mem g'.2) ht ht1' hle]
  have hne : CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ T := by
    rw [hTg, hT]
    intro heq
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hAX, inf_eq_left.mpr hVX] at heq
    apply h.ne
    rw [eq_bot_iff]
    intro u hu
    have hu' : u ∈ V ⊓ A := ⟨hu.1, heq ▸ hu.1⟩
    rw [hb.inf] at hu'
    exact hu'
  have hnorm : CFSG.CGT.Timmesfeld75.normIn T (CFSG.CGT.Timmesfeld75.conjSubgroup g T) ≠ ⊥ := by
    rw [hTg, hT, CFSG.Quasithin.I62.normIn_subgroupOf (X := X) V hAX]
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact h.ne (le_bot_iff.mp (hbot le_rfl hUX))
  have hsup : T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T = ⊤ := by
    rw [hTg, hT, ← Subgroup.subgroupOf_sup hVX hAX]
    exact Subgroup.subgroupOf_self X
  have hcfg : CFSG.CGT.Timmesfeld75.cfgM T (CFSG.CGT.Timmesfeld75.conjSubgroup g T) =
      (CFSG.Quasithin.ASInputs.tiY V A).subgroupOf X := by
    rw [hTg, CFSG.CGT.Timmesfeld75.cfgM, hT,
      CFSG.Quasithin.I62.normIn_subgroupOf (X := X) V hAX,
      CFSG.Quasithin.I62.normIn_subgroupOf (X := X) A hVX,
      ← Subgroup.subgroupOf_sup hUX hBX]
  obtain ⟨h214, -⟩ :=
    CFSG.CGT.Timmesfeld75.lemma214_proved ↥X T hWC g hne hnorm
  rw [hsup, hcfg] at h214
  have hmap := congrArg (fun K : Subgroup ↥X => K.map X.subtype) h214
  rw [Subgroup.map_subgroupOf_eq_of_le hYX, pCoreOf_top_subgroupOf,
    Subgroup.map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 X)] at hmap
  exact hmap.symm

theorem pCoreOf_sup_conj_eq {V : Subgroup G} (hV : IsElemAbelian 2 V) (hTI : IsTI V)
    {a b : G} (hne : conjSubgroup V a ≠ conjSubgroup V b)
    (hN : conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) ≠ ⊥)
    (hnot : ¬ conjSubgroup V a ≤ normalizer (conjSubgroup V b : Set G)) :
    pCoreOf 2 (conjSubgroup V a ⊔ conjSubgroup V b) =
      (conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G)) ⊔
        (conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G)) := by
  set U := conjSubgroup V a with hU
  set U' := conjSubgroup V b with hU'
  have hUe : IsElemAbelian 2 U := isElemAbelian_conjSubgroup' hV a
  have hU'e : IsElemAbelian 2 U' := isElemAbelian_conjSubgroup' hV b
  have hcard : Nat.card U = Nat.card U' := by rw [card_conjSubgroup', card_conjSubgroup']
  have hTIU : IsTISetIn U ⊤ := isTISetIn_top_of_isTI (isTI_conj hTI a)
  have hTIU' : IsTISetIn U' ⊤ := isTISetIn_top_of_isTI (isTI_conj hTI b)
  have hcross : ∀ g : G, U ≠ conjSubgroup U' g → conjSubgroup U' g ⊓ U = ⊥ := by
    intro g hg
    have hconj : conjSubgroup U' g = conjSubgroup V (b * g) := by
      rw [hU', CFSG.Quasithin.conjSubgroup_conjSubgroup]
    rw [hconj] at hg
    rcases inf_conjSubgroup_eq_bot_or_eq hTI a (b * g) with hbot | heq
    · rw [hconj, hU]
      rw [inf_comm]
      exact hbot
    · exact absurd (hU.trans heq) hg
  have hUnot : U ⊓ normalizer (U' : Set G) ≠ U :=
    fun hEq => hnot (by rw [← hEq]; exact inf_le_right)
  have hUlt : U ⊓ normalizer (U' : Set G) < U := lt_of_le_of_ne inf_le_left hUnot
  have hU'ne : U ⊓ normalizer (U' : Set G) ≠ ⊥ := by
    rw [hU, hU']
    exact hN
  have hHyp : CFSG.Quasithin.I62.Hyp U U' :=
    CFSG.Quasithin.I62.Hyp.mk' hUe hU'e hcard hTIU hTIU' hcross hU'ne hUlt
  have hp := pCoreOf_tiX_eq_tiY hHyp
  rw [hU, hU'] at hp
  exact hp

theorem sevenOneCore_holds {V H E : Subgroup G} (hV : IsElemAbelian 2 V) (hTI : IsTI V)
    (hE : IsMulCommutative E) : SevenOneCore V H E := by
  intro U hU U' hU' x hx
  by_cases hle : U ≤ normalizer (U' : Set G)
  · exact ⟨hx.1, hle hx.1⟩
  · obtain ⟨a, b, hUa, hUb, hN⟩ := nVSub_conj_ne_bot_of_mem_omegaSet hTI hE hU hU'
    have hne : conjSubgroup V a ≠ conjSubgroup V b := by
      intro heq
      apply hle
      rw [hUa, heq, ← hUb]
      exact Subgroup.le_normalizer
    have hnot : ¬ conjSubgroup V a ≤ normalizer (conjSubgroup V b : Set G) := by
      rw [← hUa, ← hUb]
      exact hle
    have hp := pCoreOf_sup_conj_eq hV hTI hne hN hnot
    have hxO : x ∈ (U ⊓ normalizer (U' : Set G)) ⊔ (U' ⊓ normalizer (U : Set G)) := by
      have hxO' : x ∈ pCoreOf 2 (U ⊔ U') := hx.2
      simpa [hUa, hUb, hp] using hxO'
    have hts : (U' ⊓ normalizer (U : Set G) : Subgroup G) ≤
        Subgroup.normalizer ((U ⊓ normalizer (U' : Set G) : Subgroup G) : Set G) := by
      intro z hz
      have key : ∀ aa ∈ (U ⊓ normalizer (U' : Set G) : Subgroup G), aa * z = z * aa := by
        intro aa ha
        have hz' : z ∈ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) := by
          rw [← hUb, ← hUa]
          exact hz
        have ha' : aa ∈ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) := by
          rw [← hUa, ← hUb]
          exact ha
        exact nVSub_comm_bSub_conj hTI hne ha' hz'
      exact CFSG.Quasithin.I62.mem_normalizer_of_conj
        (fun aa ha => by rw [show z * aa * z⁻¹ = aa by rw [← key aa ha]; group]; exact ha)
        (fun aa ha => by
          rw [show z⁻¹ * aa * z = z⁻¹ * (aa * z) by group, key aa ha,
            show z⁻¹ * (z * aa) = aa by group]
          exact ha)
    have hxmul : x ∈ (((U ⊓ normalizer (U' : Set G) : Subgroup G) : Set G) *
        ((U' ⊓ normalizer (U : Set G) : Subgroup G) : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left
        (U ⊓ normalizer (U' : Set G) : Subgroup G)
        (U' ⊓ normalizer (U : Set G) : Subgroup G) hts]
      exact hxO
    obtain ⟨y, hy, z, hz, hxz⟩ := hxmul
    have hyU : y ∈ U := hy.1
    have hzU : z ∈ U := by
      have hzy : z = y⁻¹ * x := by rw [← hxz]; group
      rw [hzy]
      exact U.mul_mem (U.inv_mem hyU) hx.1
    have hzU' : z ∈ U' := hz.1
    have hbot : U ⊓ U' = ⊥ := by
      rcases inf_conjSubgroup_eq_bot_or_eq hTI a b with h | h
      · rwa [hUa, hUb]
      · exact absurd h hne
    have hz1 : z = 1 := by
      have hzbot : z ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact ⟨hzU, hzU'⟩
      exact Subgroup.mem_bot.mp hzbot
    refine ⟨hx.1, ?_⟩
    rw [← hxz, hz1]
    simpa using hy.2

theorem seven_two_iSub_isElemAbelian_uncond {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    IsElemAbelian 2 (iSub V H E) :=
  seven_two_iSub_isElemAbelian hV hTI hE hOmH (sevenOneCore_holds hV hTI hE)

theorem seven_three_one {V H E J : Subgroup G} (hV : IsElemAbelian 2 V) (hTI : IsTI V)
    (hE : IsMulCommutative E) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hVOm : V ∈ omegaSet V H E) (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal)
    {h : G} (hh : h ∈ H) (hP : IsPGroup 2 ↥(V ⊔ conjSubgroup V h ⊔ J)) :
    ∀ u ∈ V, ∀ v ∈ conjSubgroup V h, u * v = v * u := by
  have hVhOm : conjSubgroup V h ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet hEH hEnorm hVOm hh
  obtain ⟨a, b, hVa, hVb, hNab⟩ := nVSub_conj_ne_bot_of_mem_omegaSet hTI hE hVOm hVhOm
  have hN : V ⊓ normalizer (conjSubgroup V h : Set G) ≠ ⊥ := by
    rw [hVb]
    have hVa' : conjSubgroup V a = V := hVa.symm
    rwa [hVa'] at hNab
  have hP' : IsPGroup 2 ↥(V ⊔ conjSubgroup V h) :=
    hP.to_le (le_sup_left : V ⊔ conjSubgroup V h ≤ V ⊔ conjSubgroup V h ⊔ J)
  exact commute_of_isPGroup_sup hV hTI ⟨a, hVa⟩ ⟨b, hVb⟩ hN hP'

end CFSG.LocalAnalysis.WeakClosure81
