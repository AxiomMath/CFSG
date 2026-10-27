module

public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem nVSub_conj_ne_bot_of_mem_omegaSet {V H E U U' : Subgroup G}
    (hTI : IsTI V) (hE : IsMulCommutative E) (hU : U ∈ omegaSet V H E)
    (hU' : U' ∈ omegaSet V H E) :
    ∃ a b : G, U = conjSubgroup V a ∧ U' = conjSubgroup V b ∧
      conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) ≠ ⊥ := by
  rw [mem_omegaSet] at hU hU'
  obtain ⟨a, rfl, hEU, -⟩ := hU
  obtain ⟨b, rfl, hEU', -⟩ := hU'
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEU
  obtain ⟨w', hw'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEU'
  have hwE : (w : G) ∈ E := (Subgroup.mem_inf.mp w.2).1
  have hwU : (w : G) ∈ conjSubgroup V a := (Subgroup.mem_inf.mp w.2).2
  have hw'E : (w' : G) ∈ E := (Subgroup.mem_inf.mp w'.2).1
  have hw'U : (w' : G) ∈ conjSubgroup V b := (Subgroup.mem_inf.mp w'.2).2
  have hwne : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hw'ne : (w' : G) ≠ 1 := fun h => hw'1 (Subtype.ext h)
  have hcomm : (w : G) * (w' : G) = (w' : G) * (w : G) :=
    congrArg Subtype.val (hE.is_comm.comm ⟨(w : G), hwE⟩ ⟨(w' : G), hw'E⟩)
  obtain ⟨hwn, -⟩ := commute_mem_normalizer hTI ⟨a, rfl⟩ ⟨b, rfl⟩ hwU hwne hw'U hw'ne hcomm
  exact ⟨a, b, rfl, rfl,
    Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨(w : G), Subgroup.mem_inf.mpr ⟨hwU, hwn⟩⟩, fun h => hwne (Subtype.ext_iff.mp h)⟩⟩

theorem isPGroup_closure_pair_of_mem_normalizer {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {a b : G} {d e : G} (hd : d ∈ conjSubgroup V a) (he : e ∈ conjSubgroup V b)
    (hdN : d ∈ normalizer (conjSubgroup V b : Set G)) :
    IsPGroup 2 (Subgroup.closure ({d, e} : Set G)) := by
  have hAp : IsPGroup 2 (conjSubgroup V a) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup' hV a)
  have hBp : IsPGroup 2 (conjSubgroup V b) :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup' hV b)
  have hdp : IsPGroup 2 (Subgroup.zpowers d) := hAp.to_le (Subgroup.zpowers_le.mpr hd)
  have hnorm : Subgroup.zpowers d ≤ normalizer (conjSubgroup V b : Set G) :=
    Subgroup.zpowers_le.mpr hdN
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers d ⊔ conjSubgroup V b : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hdp hBp hnorm
  refine hsup.to_le ((Subgroup.closure_le (K := Subgroup.zpowers d ⊔ conjSubgroup V b)).mpr ?_)
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with h | h
  · rw [h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  · rw [h]
    exact Subgroup.mem_sup_right he

theorem commutator_conj_mem_nVSub {V : Subgroup G} (hV : IsElemAbelian 2 V) (hTI : IsTI V)
    {a b : G} {v y : G} (hv : v ∈ conjSubgroup V a)
    (hy : y ∈ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G)) :
    ⁅v, y⁆ ∈ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) := by
  have hconj : conjSubgroup (conjSubgroup V a) (a⁻¹ * b) = conjSubgroup V b := by
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  have hy' : y ∈ bSub (conjSubgroup V a) (a⁻¹ * b) := by
    rw [bSub, hconj]
    exact hy
  have h := commutator_mem_nVSub (isElemAbelian_conjSubgroup' hV a) (isTI_conj hTI a) hv hy'
  rwa [nVSub, hconj] at h

theorem commutator_conj_mem_bSub {V : Subgroup G} (hV : IsElemAbelian 2 V) (hTI : IsTI V)
    {a b : G} {w u : G} (hw : w ∈ conjSubgroup V b)
    (hu : u ∈ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G)) :
    ⁅w, u⁆ ∈ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) := by
  have hconj : conjSubgroup (conjSubgroup V a) (a⁻¹ * b) = conjSubgroup V b := by
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  have hw' : w ∈ conjSubgroup (conjSubgroup V a) (a⁻¹ * b) := by rw [hconj]; exact hw
  have hu' : u ∈ nVSub (conjSubgroup V a) (a⁻¹ * b) := by
    rw [nVSub, hconj]
    exact hu
  have h := commutator_mem_bSub (isElemAbelian_conjSubgroup' hV a) (isTI_conj hTI a) hw' hu'
  rwa [bSub, hconj] at h

theorem odd_orderOf_mul_of_conj {V : Subgroup G} (hV : IsElemAbelian 2 V) (hTI : IsTI V)
    {a b : G} (hN : conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) ≠ ⊥)
    {v y : G} (hv : v ∈ conjSubgroup V a)
    (hvN : v ∉ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G))
    (hy : y ∈ conjSubgroup V b)
    (hyN : y ∉ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G)) :
    Odd (orderOf (v * y)) := by
  have hconj : conjSubgroup (conjSubgroup V a) (a⁻¹ * b) = conjSubgroup V b := by
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  have hN' : nVSub (conjSubgroup V a) (a⁻¹ * b) ≠ ⊥ := by
    rw [nVSub, hconj]
    exact hN
  have hvN' : v ∉ nVSub (conjSubgroup V a) (a⁻¹ * b) := by
    rw [nVSub, hconj]
    exact hvN
  have hyN' : y ∉ bSub (conjSubgroup V a) (a⁻¹ * b) := by
    rw [bSub, hconj]
    exact hyN
  exact odd_orderOf_mul (isElemAbelian_conjSubgroup' hV a) (isTI_conj hTI a) hN' hv hvN'
    (by rwa [hconj]) hyN'

theorem seven_three_A {V H E U U' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    {d e : G} (hd : d ∈ U) (he : e ∈ U')
    (hnot : ¬ IsPGroup 2 (Subgroup.closure ({d, e} : Set G))) :
    Odd (orderOf (d * e)) := by
  obtain ⟨a, b, hUa, hUb, hN⟩ := nVSub_conj_ne_bot_of_mem_omegaSet hTI hE hU hU'
  rw [hUa] at hd
  rw [hUb] at he
  have hdN : d ∉ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) := by
    intro hd'
    exact hnot (isPGroup_closure_pair_of_mem_normalizer hV hd'.1 he hd'.2)
  have heN : e ∉ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) := by
    intro he'
    refine hnot ?_
    rw [show ({d, e} : Set G) = {e, d} by rw [Set.pair_comm]]
    exact isPGroup_closure_pair_of_mem_normalizer hV he'.1 hd he'.2
  exact odd_orderOf_mul_of_conj hV hTI hN hd hdN he heN

theorem nVSub_comm_bSub_conj {V : Subgroup G} (hTI : IsTI V) {a b : G}
    (hne : conjSubgroup V a ≠ conjSubgroup V b)
    {u v : G} (hu : u ∈ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G))
    (hv : v ∈ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G)) :
    u * v = v * u := by
  have hconj : conjSubgroup (conjSubgroup V a) (a⁻¹ * b) = conjSubgroup V b := by
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  have hne' : conjSubgroup (conjSubgroup V a) (a⁻¹ * b) ≠ conjSubgroup V a := by
    rw [hconj]
    exact fun h => hne h.symm
  have hu' : u ∈ nVSub (conjSubgroup V a) (a⁻¹ * b) := by
    rw [nVSub, hconj]
    exact hu
  have hv' : v ∈ bSub (conjSubgroup V a) (a⁻¹ * b) := by
    rw [bSub, hconj]
    exact hv
  exact nVSub_comm_bSub (isTI_conj hTI a) hne' hu' hv'

theorem le_normalizer_of_subgroupOf_normal {E H : Subgroup G} (hEH : E ≤ H)
    (h : (E.subgroupOf H).Normal) : H ≤ normalizer (E : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hxE
    have hxH : x ∈ H := hEH hxE
    have hmem := h.conj_mem (⟨x, hxH⟩ : H) (by rw [Subgroup.mem_subgroupOf]; exact hxE)
      (⟨g, hg⟩ : H)
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  · intro hy
    have hyH : g * x * g⁻¹ ∈ H := hEH hy
    have hmem := h.conj_mem (⟨g * x * g⁻¹, hyH⟩ : H)
      (by rw [Subgroup.mem_subgroupOf]; exact hy) ((⟨g, hg⟩ : H)⁻¹)
    rw [Subgroup.mem_subgroupOf] at hmem
    have hkey : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    simpa [hkey] using hmem

@[expose] def SevenOneCore (V H E : Subgroup G) : Prop :=
  ∀ U ∈ omegaSet V H E, ∀ U' ∈ omegaSet V H E,
    U ⊓ pCoreOf 2 (U ⊔ U') ≤ U ⊓ normalizer (U' : Set G)

theorem inf_pCoreOf_le_inf_pCoreOf_sup {V H E U U' : Subgroup G}
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hU : U ∈ omegaSet V H E)
    (hU' : U' ∈ omegaSet V H E) :
    U ⊓ pCoreOf 2 H ≤ U ⊓ pCoreOf 2 (U ⊔ U') := by
  have hXH : U ⊔ U' ≤ H := sup_le (hOmH U hU) (hOmH U' hU')
  have hYp : IsPGroup 2 ↥((U ⊔ U') ⊓ pCoreOf 2 H : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le inf_le_right
  have hYle : (U ⊔ U') ⊓ pCoreOf 2 H ≤ pCoreOf 2 (U ⊔ U') := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hYp
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨(U ⊔ U').mul_mem ((U ⊔ U').mul_mem hz hy.1) ((U ⊔ U').inv_mem hz),
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H (hXH hz)) y).mp hy.2⟩
    · intro hy
      have hz' : z⁻¹ ∈ U ⊔ U' := (U ⊔ U').inv_mem hz
      have hkey : z⁻¹ * (z * y * z⁻¹) * z = y := by group
      rw [← hkey]
      refine ⟨(U ⊔ U').mul_mem ((U ⊔ U').mul_mem hz' hy.1) hz, ?_⟩
      simpa using (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H (hXH hz')) (z * y * z⁻¹)).mp hy.2
  intro x hx
  exact ⟨hx.1, hYle ⟨Subgroup.mem_sup_left hx.1, hx.2⟩⟩

theorem seven_two_iSub_isElemAbelian {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hCore : SevenOneCore V H E) :
    IsElemAbelian 2 (iSub V H E) := by
  have hgen : ∀ U ∈ omegaSet V H E, ∀ U' ∈ omegaSet V H E,
      ∀ x ∈ U ⊓ pCoreOf 2 H, ∀ y ∈ U' ⊓ pCoreOf 2 H, x * y = y * x := by
    intro U hU U' hU' x hx y hy
    obtain ⟨a, hUa, hEUa, hUOa⟩ := mem_omegaSet.mp hU
    obtain ⟨b, hUb, hEUb, hUOb⟩ := mem_omegaSet.mp hU'
    subst hUa
    subst hUb
    have hxU : x ∈ conjSubgroup V a := (Subgroup.mem_inf.mp hx).1
    have hxO : x ∈ pCoreOf 2 H := (Subgroup.mem_inf.mp hx).2
    have hyU : y ∈ conjSubgroup V b := (Subgroup.mem_inf.mp hy).1
    have hyO : y ∈ pCoreOf 2 H := (Subgroup.mem_inf.mp hy).2
    by_cases heq : conjSubgroup V a = conjSubgroup V b
    · rw [← heq] at hyU
      exact CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm (isElemAbelian_conjSubgroup' hV a) hxU hyU
    · by_cases hcomm : ∀ u ∈ conjSubgroup V a, ∀ v ∈ conjSubgroup V b, u * v = v * u
      · exact hcomm x hxU y hyU
      · have hxO2 : x ∈ pCoreOf 2 (conjSubgroup V a ⊔ conjSubgroup V b) :=
          (inf_pCoreOf_le_inf_pCoreOf_sup hOmH hU hU' ⟨hxU, hxO⟩).2
        have hyO2 : y ∈ pCoreOf 2 (conjSubgroup V b ⊔ conjSubgroup V a) :=
          (inf_pCoreOf_le_inf_pCoreOf_sup hOmH hU' hU ⟨hyU, hyO⟩).2
        have hxN : x ∈ conjSubgroup V a ⊓ normalizer (conjSubgroup V b : Set G) :=
          hCore _ hU _ hU' ⟨hxU, hxO2⟩
        have hyN : y ∈ conjSubgroup V b ⊓ normalizer (conjSubgroup V a : Set G) :=
          hCore _ hU' _ hU ⟨hyU, hyO2⟩
        exact nVSub_comm_bSub_conj hTI heq hxN hyN
  have hle : iSub V H E ≤ Subgroup.centralizer (iSub V H E : Set G) := by
    refine iSup_le fun U => iSup_le fun hU => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup_le fun U' => iSup_le fun hU' => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hgen U' hU' U hU x hx y hy).symm
  have hmc : IsMulCommutative (iSub V H E) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp hle
  have hiSub_eq : (⨆ U : {U // U ∈ omegaSet V H E}, (U.1 ⊓ pCoreOf 2 H)) = iSub V H E := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun U => le_iSup₂_of_le U.1 U.2 le_rfl
    · refine iSup_le fun U => iSup_le fun hU =>
        le_iSup_of_le (⟨U, hU⟩ : {U // U ∈ omegaSet V H E}) le_rfl
  have hsq : ∀ x ∈ iSub V H E, x * x = 1 := by
    intro x hx
    have hx' : x ∈ ⨆ U : {U // U ∈ omegaSet V H E}, (U.1 ⊓ pCoreOf 2 H) := by
      rw [hiSub_eq]
      exact hx
    exact Subgroup.iSup_induction' (S := fun U : {U // U ∈ omegaSet V H E} =>
        U.1 ⊓ pCoreOf 2 H) (C := fun x _ => x * x = 1)
      (fun U x hxU => by
        have hUmem := U.2
        rw [mem_omegaSet] at hUmem
        obtain ⟨a, hUa, -, -⟩ := hUmem
        rw [hUa] at hxU
        exact CFSG.CGT.Timmesfeld75.elemAbelian_mul_self (isElemAbelian_conjSubgroup' hV a)
          (Subgroup.mem_inf.mp hxU).1)
      (by rw [mul_one])
      (fun x y hx hy ihx ihy => by
        have hxy : x * y = y * x :=
          congrArg Subtype.val (hmc.is_comm.comm ⟨x, hiSub_eq ▸ hx⟩ ⟨y, hiSub_eq ▸ hy⟩)
        have hyx : y * x = x * y := hxy.symm
        calc (x * y) * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hyx]
          _ = x * x * y * y := by group
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [ihx, ihy, mul_one])
      hx'
  refine ⟨hmc, fun x hx => ?_⟩
  simpa [pow_two] using hsq x hx

theorem mem_pCoreOf_of_forall_closure_isPGroup {H : Subgroup G} {u : G} (huH : u ∈ H)
    (h : ∀ g ∈ H, IsPGroup 2 (Subgroup.closure ({u, g * u * g⁻¹} : Set G))) :
    u ∈ pCoreOf 2 H := by
  have hcore : (⟨u, huH⟩ : H) ∈ CFSG.pCore 2 H := by
    refine CFSG.BaerSuzuki.Helpers.mem_pCore_of_pairwise_conjugates (G := H) (p := 2)
      ⟨u, huH⟩ ?_
    intro g
    have hS := h (g : G) g.2
    have hmap : (Subgroup.closure ({⟨u, huH⟩, g * ⟨u, huH⟩ * g⁻¹} : Set H)).map H.subtype =
        Subgroup.closure ({u, (g : G) * u * (g : G)⁻¹} : Set G) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by simp)
      · intro hx
        rcases hx with hx | hx
        · exact ⟨⟨u, huH⟩, Or.inl rfl, by simpa using hx.symm⟩
        · exact ⟨g * ⟨u, huH⟩ * g⁻¹, Or.inr rfl, by simpa using hx.symm⟩
    have hEq : (Subgroup.closure ({⟨u, huH⟩, g * ⟨u, huH⟩ * g⁻¹} : Set H) : Subgroup H) =
        (Subgroup.closure ({u, (g : G) * u * (g : G)⁻¹} : Set G)).comap H.subtype := by
      rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective
        (Subgroup.closure ({⟨u, huH⟩, g * ⟨u, huH⟩ * g⁻¹} : Set H)), hmap]
    rw [hEq]
    exact IsPGroup.comap_subtype (K := H) hS
  exact Subgroup.mem_map.mpr ⟨⟨u, huH⟩, hcore, rfl⟩

@[expose] def kerMOf (M H : Subgroup G) : Subgroup G :=
  ((M.subgroupOf H).normalCore).map H.subtype

end CFSG.LocalAnalysis.WeakClosure81
