module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem isElemAbelian_subgroupOf {U H : Subgroup G} (h : IsElemAbelian 2 U) :
    IsElemAbelian 2 (U.subgroupOf H) :=
  h.comap H.subtype_injective

private theorem isTI_subgroupOf {U H : Subgroup G} (hTI : IsTI U) :
    IsTI (U.subgroupOf H) := by
  intro γ
  rcases hTI (γ : G) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hx1' : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx1
    have hx2' : (x : G) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup (γ : G) U := by
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      have hx2'' := hx2
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx2''
      simpa using Subgroup.mem_subgroupOf.mp hx2''
    have hx' : (x : G) ∈ U ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (γ : G) U :=
      Subgroup.mem_inf.mpr ⟨hx1', hx2'⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  · right
    have hUC : U ≤ CFSG.CGT.Timmesfeld75.conjSubgroup (γ : G) U := by
      have hle : U ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (γ : G) U ≤
          CFSG.CGT.Timmesfeld75.conjSubgroup (γ : G) U := inf_le_right
      rwa [h] at hle
    refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx
    have hxC : (x : G) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup (γ : G) U := hUC hxU
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hxC
    exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr (Subgroup.mem_subgroupOf.mpr hxC)

private theorem mem_normalizer_of_mem_normalizer_subgroupOf {U H : Subgroup G} (hUH : U ≤ H)
    {m : ↥H} (hm : m ∈ Subgroup.normalizer ((U.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    (m : G) ∈ Subgroup.normalizer (U : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUH] at hm
  exact Subgroup.mem_subgroupOf.mp hm

private theorem mem_normalizer_subgroupOf_of_mem_normalizer {X H : Subgroup G} (hXH : X ≤ H)
    {a : ↥H}
    (ha : (a : G) ∈ Subgroup.normalizer (X : Set G)) :
    a ∈ Subgroup.normalizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hXH]
  exact Subgroup.mem_subgroupOf.mpr ha

private theorem subgroupOf_mem_omegaSet_top {U H E W : Subgroup G} {k : G}
    (hUH : U ≤ H) (hWH : W ≤ H) (hW : W = conjSubgroup U k) (hk : k ∈ H)
    (hEH : E ≤ H) (hEW : E ⊓ W ≠ ⊥) (hWO : ¬ W ≤ pCoreOf 2 H) :
    W.subgroupOf H ∈ omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) := by
  refine mem_omegaSet.mpr ⟨⟨k, hk⟩, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective H.subtype_injective
    rw [map_conjSubgroup_subgroupOf' hUH hk, Subgroup.map_subgroupOf_eq_of_le hWH, hW]
  · have hE'W' : E.subgroupOf H ⊓ W.subgroupOf H = (E ⊓ W).subgroupOf H :=
      (Subgroup.comap_inf E W H.subtype).symm
    rw [hE'W']
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    apply hEW
    have hEWh : E ⊓ W ≤ H := inf_le_left.trans hEH
    have hinf : (E ⊓ W) ⊓ H = E ⊓ W := inf_eq_left.mpr hEWh
    rw [disjoint_iff] at hbot
    rwa [hinf] at hbot
  · rw [pCoreOf_top_subgroupOf]
    intro hle
    apply hWO
    intro x hx
    have hxH : x ∈ H := hWH hx
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ W.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    have h2 := hle hmem
    rwa [Subgroup.mem_subgroupOf] at h2

private theorem map_subtype_mem_omegaIn_of_mem_omegaSet_top {V H E U : Subgroup G}
    {W' : Subgroup ↥H}
    (hU : U ∈ omegaIn V H E)
    (hW' : W' ∈ omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H)) :
    W'.map H.subtype ∈ omegaIn V H E := by
  obtain ⟨a, hUa, -, -⟩ := mem_omegaSet.mp hU.1
  obtain ⟨γ, hW'γ, hEW', hW'O'⟩ := mem_omegaSet.mp hW'
  have hmapW : W'.map H.subtype = conjSubgroup U (γ : G) := by
    rw [hW'γ, ← map_conjSubgroup_hom H.subtype (U.subgroupOf H) γ,
      Subgroup.map_subgroupOf_eq_of_le hU.2]
    rfl
  refine ⟨?_, Subgroup.map_subtype_le W'⟩
  refine mem_omegaSet.mpr ⟨a * (γ : G), ?_, ?_, ?_⟩
  · rw [hmapW, hUa, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  · obtain ⟨x, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEW'
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(x : G), ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · have h := (Subgroup.mem_inf.mp x.2).1
        rwa [Subgroup.mem_subgroupOf] at h
      · exact Subgroup.mem_map.mpr ⟨x.1, (Subgroup.mem_inf.mp x.2).2, rfl⟩
    · intro hh
      apply hx1'
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : ↥(E ⊓ W'.map H.subtype) => (t : G)) hh
  · intro hle
    apply hW'O'
    rw [pCoreOf_top_subgroupOf]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))

private theorem iSub_top_subgroupOf_le {V H E J U : Subgroup G}
    (hU : U ∈ omegaIn V H E)
    (hIJ : ∀ W ∈ omegaIn V H E, W ⊓ pCoreOf 2 H ≤ J) :
    iSub (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) ≤ J.subgroupOf H := by
  refine iSup_le fun W' => iSup_le fun hW' => ?_
  have hW : W'.map H.subtype ∈ omegaIn V H E :=
    map_subtype_mem_omegaIn_of_mem_omegaSet_top hU hW'
  intro x hx
  obtain ⟨hxW', hxO⟩ := Subgroup.mem_inf.mp hx
  rw [pCoreOf_top_subgroupOf] at hxO
  rw [Subgroup.mem_subgroupOf] at hxO ⊢
  exact hIJ (W'.map H.subtype) hW
    ⟨Subgroup.mem_map.mpr ⟨x, hxW', rfl⟩, hxO⟩

theorem seven_three_three_in {V H E J U U' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hT : ∀ W ∈ omegaIn V H E, ∀ W' ∈ omegaIn V H E, ∃ k ∈ H, W' = conjSubgroup W k)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal)
    (hU : U ∈ omegaIn V H E) (hU' : U' ∈ omegaIn V H E) {u v : G}
    (hu : u ∈ U) (huO : u ∉ pCoreOf 2 H) (hv : v ∈ U') (hvO : v ∉ pCoreOf 2 H)
    (huv : u⁻¹ * v ∈ J) :
    ∃ j ∈ J, u = j⁻¹ * v * j := by
  have hV'e : IsElemAbelian 2 (U.subgroupOf H) :=
    isElemAbelian_subgroupOf (isElemAbelian_of_mem_omegaSet hV hU.1)
  have hV'TI : IsTI (U.subgroupOf H) :=
    isTI_subgroupOf (isTI_of_mem_omegaSet hU.1 hTI)
  haveI : IsMulCommutative E := hE
  have hE' : IsMulCommutative (E.subgroupOf H) := inferInstance
  obtain ⟨-, -, hEU, hUO⟩ := mem_omegaSet.mp hU.1
  obtain ⟨-, -, hEU', hU'O⟩ := mem_omegaSet.mp hU'.1
  obtain ⟨k, hk, hU'k⟩ := hT U hU U' hU'
  have hV'mem : U.subgroupOf H ∈
      omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) :=
    subgroupOf_mem_omegaSet_top hU.2 hU.2 (CFSG.Quasithin.conjSubgroup_one U).symm
      H.one_mem hEH hEU hUO
  have hU'mem : U'.subgroupOf H ∈
      omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) :=
    subgroupOf_mem_omegaSet_top hU.2 hU'.2 hU'k hk hEH hEU' hU'O
  have hJ' : J.subgroupOf H ≤ pCoreOf 2 (⊤ : Subgroup ↥H) := by
    rw [pCoreOf_top_subgroupOf]
    exact Subgroup.subgroupOf_mono H hJ
  have hJnorm' : ((J.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).Normal :=
    hJnorm.subgroupOf ⊤
  have hEnorm' : ((E.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).Normal :=
    hEnorm.subgroupOf ⊤
  let u' : ↥H := ⟨u, hU.2 hu⟩
  let v' : ↥H := ⟨v, hU'.2 hv⟩
  have hu'd : u' ∈ dSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) := by
    refine mem_dSet.mpr ⟨U.subgroupOf H, hV'mem, Subgroup.mem_subgroupOf.mpr hu, ?_⟩
    rw [pCoreOf_top_subgroupOf]
    intro hmem
    exact huO (Subgroup.mem_subgroupOf.mp hmem)
  have hv'd : v' ∈ dSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) := by
    refine mem_dSet.mpr ⟨U'.subgroupOf H, hU'mem, Subgroup.mem_subgroupOf.mpr hv, ?_⟩
    rw [pCoreOf_top_subgroupOf]
    intro hmem
    exact hvO (Subgroup.mem_subgroupOf.mp hmem)
  have huv' : u'⁻¹ * v' ∈ J.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    simpa using huv
  obtain ⟨j', hj', heq⟩ := seven_three_three hV'e hV'TI hE' le_top hEnorm'
    (fun _ _ => le_top) hJ' hJnorm' hu'd hv'd huv'
  refine ⟨(j' : G), Subgroup.mem_subgroupOf.mp hj', ?_⟩
  have := congrArg (fun t : ↥H => (t : G)) heq
  simpa using this

theorem seven_three_four_normalizer_in {V H E J U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal)
    (hIJ : ∀ W ∈ omegaIn V H E, W ⊓ pCoreOf 2 H ≤ J)
    (hU : U ∈ omegaIn V H E) {h : G} (hh : h ∈ H)
    (hNh : h ∈ normalizer ((U ⊔ J : Subgroup G) : Set G)) :
    ∃ m ∈ H ⊓ normalizer (U : Set G), ∃ j ∈ J, h = m * j := by
  have hJleH : J ≤ H := hJ.trans (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) H)
  have hV'e : IsElemAbelian 2 (U.subgroupOf H) :=
    isElemAbelian_subgroupOf (isElemAbelian_of_mem_omegaSet hV hU.1)
  have hV'TI : IsTI (U.subgroupOf H) :=
    isTI_subgroupOf (isTI_of_mem_omegaSet hU.1 hTI)
  haveI : IsMulCommutative E := hE
  have hE' : IsMulCommutative (E.subgroupOf H) := inferInstance
  obtain ⟨-, -, hEU, hUO⟩ := mem_omegaSet.mp hU.1
  have hV'mem : U.subgroupOf H ∈
      omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) :=
    subgroupOf_mem_omegaSet_top hU.2 hU.2 (CFSG.Quasithin.conjSubgroup_one U).symm
      H.one_mem hEH hEU hUO
  have hJ' : J.subgroupOf H ≤ pCoreOf 2 (⊤ : Subgroup ↥H) := by
    rw [pCoreOf_top_subgroupOf]
    exact Subgroup.subgroupOf_mono H hJ
  have hJnorm' : ((J.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).Normal :=
    hJnorm.subgroupOf ⊤
  have hEnorm' : ((E.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).Normal :=
    hEnorm.subgroupOf ⊤
  have hIJ' : iSub (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) ≤ J.subgroupOf H :=
    iSub_top_subgroupOf_le hU hIJ
  have hNh' : (⟨h, hh⟩ : ↥H) ∈
      Subgroup.normalizer ((U.subgroupOf H ⊔ J.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    have hsup : (U.subgroupOf H ⊔ J.subgroupOf H : Subgroup ↥H) = (U ⊔ J).subgroupOf H :=
      (Subgroup.subgroupOf_sup hU.2 hJleH).symm
    rw [Subgroup.mem_normalizer_iff] at hNh ⊢
    intro y
    rw [hsup]
    constructor
    · intro hy
      have hy' : (y : G) ∈ U ⊔ J := Subgroup.mem_subgroupOf.mp hy
      have h2 := (hNh (y : G)).mp hy'
      rw [Subgroup.mem_subgroupOf]
      simpa using h2
    · intro hy
      have hy' : (h * (y : G) * h⁻¹) ∈ U ⊔ J := by
        have h := hy
        rw [Subgroup.mem_subgroupOf] at h
        simpa using h
      exact Subgroup.mem_subgroupOf.mpr ((hNh (y : G)).mpr hy')
  obtain ⟨m', hm', j', hj', heq⟩ := seven_three_four_normalizer hV'e hV'TI hE' le_top hEnorm'
    hV'mem (fun _ _ => le_top) hJ' hJnorm' hIJ'
    (show (⟨h, hh⟩ : ↥H) ∈ (⊤ : Subgroup ↥H) from trivial) hNh'
  refine ⟨(m' : G), ⟨m'.2, ?_⟩, (j' : G), Subgroup.mem_subgroupOf.mp hj', ?_⟩
  · exact mem_normalizer_of_mem_normalizer_subgroupOf hU.2 (Subgroup.mem_inf.mp hm').2
  · have := congrArg (fun t : ↥H => (t : G)) heq
    simpa using this

theorem seven_six_one_relIndex_eq_two_in {V H E J A X U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal)
    (hIJ : ∀ W ∈ omegaIn V H E, W ⊓ pCoreOf 2 H ≤ J)
    (hJX : J ≤ X) (hXH : X ≤ H) (hAH : A ≤ H) (hAX : A ≤ normalizer (X : Set G))
    (hXodd : Odd (J.relIndex X))
    (hfaith : ∀ a ∈ A, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J)
    (hU : U ∈ omegaIn V H E) (hUA : U ≤ A) :
    J.relIndex U = 2 := by
  have hV'e : IsElemAbelian 2 (U.subgroupOf H) :=
    isElemAbelian_subgroupOf (isElemAbelian_of_mem_omegaSet hV hU.1)
  have hV'TI : IsTI (U.subgroupOf H) :=
    isTI_subgroupOf (isTI_of_mem_omegaSet hU.1 hTI)
  haveI : IsMulCommutative E := hE
  have hE' : IsMulCommutative (E.subgroupOf H) := inferInstance
  obtain ⟨-, -, hEU, hUO⟩ := mem_omegaSet.mp hU.1
  have hV'mem : U.subgroupOf H ∈
      omegaSet (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) :=
    subgroupOf_mem_omegaSet_top hU.2 hU.2 (CFSG.Quasithin.conjSubgroup_one U).symm
      H.one_mem hEH hEU hUO
  have hJ' : J.subgroupOf H ≤ pCoreOf 2 (⊤ : Subgroup ↥H) := by
    rw [pCoreOf_top_subgroupOf]
    exact Subgroup.subgroupOf_mono H hJ
  have hJnorm' : ((J.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).Normal :=
    hJnorm.subgroupOf ⊤
  have hEnorm' : ((E.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).Normal :=
    hEnorm.subgroupOf ⊤
  have hIJ' : iSub (U.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) ≤ J.subgroupOf H :=
    iSub_top_subgroupOf_le hU hIJ
  have hJX' : J.subgroupOf H ≤ X.subgroupOf H := Subgroup.subgroupOf_mono H hJX
  have hXodd' : Odd ((J.subgroupOf H).relIndex (X.subgroupOf H)) := by
    rw [Subgroup.relIndex_subgroupOf hXH]
    exact hXodd
  have hAX' : A.subgroupOf H ≤
      Subgroup.normalizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro a ha
    exact mem_normalizer_subgroupOf_of_mem_normalizer hXH
      (hAX (Subgroup.mem_subgroupOf.mp ha))
  have hfaith' : ∀ a ∈ A.subgroupOf H,
      (∀ x ∈ X.subgroupOf H, ⁅a, x⁆ ∈ J.subgroupOf H) → a ∈ J.subgroupOf H := by
    intro a ha hcomm
    refine Subgroup.mem_subgroupOf.mpr (hfaith (a : G) (Subgroup.mem_subgroupOf.mp ha) ?_)
    intro x hx
    have hx' : (⟨x, hXH hx⟩ : ↥H) ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    have h := hcomm ⟨x, hXH hx⟩ hx'
    rw [Subgroup.mem_subgroupOf] at h
    have hcoe : ((⁅a, (⟨x, hXH hx⟩ : ↥H)⁆ : ↥H) : G) = ⁅(a : G), x⁆ :=
      map_commutatorElement H.subtype a (⟨x, hXH hx⟩ : ↥H)
    rwa [hcoe] at h
  obtain ⟨hres, -⟩ := seven_six_one_relIndex_eq_two hV'e hV'TI hE' le_top hEnorm'
    (fun _ _ => le_top) hJ' hJnorm' hIJ' hJX' le_top hAX' hXodd' hfaith'
    (U.subgroupOf H) hV'mem (Subgroup.subgroupOf_mono H hUA)
  rwa [Subgroup.relIndex_subgroupOf hU.2] at hres

end CFSG.LocalAnalysis.WeakClosure81
