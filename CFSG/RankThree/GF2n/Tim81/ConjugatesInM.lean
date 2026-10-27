module

public import CFSG.RankThree.GF2n.Tim81.Basic
public import CFSG.RankThree.GF2n.Tim78RootType
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private theorem mem_conjSubgroup_subgroupOf {M U : Subgroup G} {g x : ↥M} :
    x ∈ conjSubgroup g (U.subgroupOf M) ↔ (x : G) ∈ conjSubgroup (g : G) U := by
  rw [mem_conjSubgroup, mem_conjSubgroup, Subgroup.mem_subgroupOf]
  rfl

private theorem isTI_subgroupOf {M U : Subgroup G} (hTI : IsTI U) :
    IsTI (U.subgroupOf M) := by
  intro g
  rcases hTI (g : G) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hmem : (x : G) ∈ U ⊓ conjSubgroup (g : G) U :=
      Subgroup.mem_inf.mpr ⟨hx1, mem_conjSubgroup_subgroupOf.mp hx2⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  · right
    refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup_subgroupOf]
    have hx' : (x : G) ∈ U := hx
    rw [← h] at hx'
    exact (Subgroup.mem_inf.mp hx').2

private theorem isRootTypeTI_subgroupOf {M U : Subgroup G} (hUM : U ≤ M)
    (hroot : Tim78.IsRootTypeTI U) : Tim78.IsRootTypeTI (U.subgroupOf M) := by
  refine ⟨isTI_subgroupOf hroot.1, fun g hg a ha b hb => ?_⟩
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  obtain ⟨htU, htN⟩ := Subgroup.mem_inf.mp ht
  have hUconjM : conjSubgroup (g : G) U ≤ M := by
    intro x hx
    have hx' : (g : G)⁻¹ * x * (g : G) ∈ U := mem_conjSubgroup.mp hx
    have := M.mul_mem (M.mul_mem g.2 (hUM hx')) (M.inv_mem g.2)
    rwa [show (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x by group] at this
  have hnorm : (t : G) ∈ Subgroup.normalizer (conjSubgroup (g : G) U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h1 := (Subgroup.mem_normalizer_iff.mp htN ⟨w, hUconjM hw⟩).mp
        (mem_conjSubgroup_subgroupOf.mpr hw)
      exact mem_conjSubgroup_subgroupOf.mp h1
    · intro hw
      have hwM : (t : G) * w * (t : G)⁻¹ ∈ M := hUconjM hw
      have hwM' : w ∈ M := by
        have := M.mul_mem (M.mul_mem (M.inv_mem t.2) hwM) t.2
        rwa [show (t : G)⁻¹ * ((t : G) * w * (t : G)⁻¹) * (t : G) = w by group] at this
      have h1 := (Subgroup.mem_normalizer_iff.mp htN ⟨w, hwM'⟩).mpr
        (mem_conjSubgroup_subgroupOf.mpr hw)
      exact mem_conjSubgroup_subgroupOf.mp h1
  have hne : U ⊓ Subgroup.normalizer (conjSubgroup (g : G) U : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : (t : G) ∈ U ⊓ Subgroup.normalizer (conjSubgroup (g : G) U : Set G) :=
      ⟨htU, hnorm⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ht1 (Subtype.ext (Subtype.ext hmem))
  exact Subtype.ext (hroot.2 (g : G) hne (a : G) ha (b : G) (mem_conjSubgroup_subgroupOf.mp hb))

private noncomputable def quotientAction {A H : Type*} [Group A] [Group H]
    (ρ : A →* MulAut H) (N : Subgroup H) [N.Normal]
    (hN : ∀ a : A, Subgroup.map (ρ a) N = N) : A →* MulAut (H ⧸ N) where
  toFun a := QuotientGroup.congr N N (ρ a) (hN a)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => rw [QuotientGroup.congr_mk, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

namespace Hyp

theorem center_Pc (h : Hyp M V) :
    Pc M V ⊓ Subgroup.centralizer (Pc M V : Set G) = V := by
  rw [h.centralizer_Pc, inf_eq_right.mpr h.le_Pc]

theorem commute_of_conj_inf_ne_bot (h : Hyp M V) (hroot : Tim78.IsRootTypeTI V) {g : G}
    (hg : conjSubgroup g V ⊓ M ≠ ⊥) :
    ∀ a ∈ V, ∀ b ∈ conjSubgroup g V, a * b = b * a := by
  have hne : conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup 1 V : Set G) ≠ ⊥ := by
    simpa [conjSubgroup_one, h.normalizer_eq] using hg
  have hcomm := Tim78.commute_of_isRootTypeTI hroot (g := g) (h := 1) hne
  intro a ha b hb
  exact (hcomm b hb a (by simpa [conjSubgroup_one] using ha)).symm

theorem conj_le_Pc_or_inf_eq_bot (h : Hyp M V) (hroot : Tim78.IsRootTypeTI V) {g : G}
    (hg : conjSubgroup g V ≤ M) :
    conjSubgroup g V ≤ Pc M V ∨ conjSubgroup g V ⊓ inSubgroup (pCore 2) M = ⊥ := by
  classical
  set U : Subgroup G := conjSubgroup g V with hU
  have hUel : Assembly.IsElemAbelian 2 U := by
    change Assembly.IsElemAbelian 2 (V.map (MulAut.conj g).toMonoidHom)
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', hae⟩ := a.2
      obtain ⟨b', hb', hbe⟩ := b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hae, ← hbe, ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, h.elem.2 x hx, map_one]
  have hUroot : Tim78.IsRootTypeTI U := by
    refine ⟨isTI_conjSubgroup hroot.1 g, fun k hk a ha b hb => ?_⟩
    rw [← conjSubgroup_mul] at hk hb
    exact Tim78.commute_of_isRootTypeTI hroot (g := g) (h := k * g) hk a ha b hb
  have hUrootM : Tim78.IsRootTypeTI (U.subgroupOf M) :=
    isRootTypeTI_subgroupOf hg hUroot
  have hUelM : Assembly.IsElemAbelian 2 (U.subgroupOf M) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val (hUel.1.is_comm.comm ⟨(a : G), a.2⟩ ⟨(b : G), b.2⟩)
    · intro x hx
      apply Subtype.ext
      simpa using hUel.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
  rcases tim78_2_13 hUelM hUrootM with hbot | hle
  · right
    have hmap : Subgroup.map M.subtype (U.subgroupOf M ⊓ pCore 2 ↥M) =
        U ⊓ inSubgroup (pCore 2) M := by
      rw [Subgroup.map_inf_eq _ _ _ M.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hg]
      rfl
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  · left
    have hUQ : U ≤ inSubgroup (pCore 2) M := by
      calc U = (U.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hg).symm
        _ ≤ (pCore 2 ↥M).map M.subtype := Subgroup.map_mono hle
        _ = inSubgroup (pCore 2) M := rfl
    have hUM : U ≤ M := hUQ.trans (inSubgroup_pCore_two M).2.1
    have hUne : U ≠ ⊥ := by
      rw [hU]
      intro hbot
      apply h.ne_bot
      have h := congrArg (conjSubgroup g⁻¹) hbot
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h
      simpa [conjSubgroup] using h
    have hgne : U ⊓ M ≠ ⊥ := by
      rwa [inf_eq_left.mpr hUM]
    have hcomm := commute_of_conj_inf_ne_bot h hroot hgne
    have hUcent : U ≤ Subgroup.centralizer (V : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    exact le_inf hUQ hUcent

private theorem map_conjNormal_subgroupOf_eq (h : Hyp M V)
    [((Pc M V).subgroupOf M).Normal] (a : ↥M) :
    Subgroup.map (MulAut.conjNormal (H := (Pc M V).subgroupOf M) a)
      ((V.subgroupOf M).subgroupOf ((Pc M V).subgroupOf M)) =
      (V.subgroupOf M).subgroupOf ((Pc M V).subgroupOf M) := by
  let P0 : Subgroup ↥M := (Pc M V).subgroupOf M
  let V0 : Subgroup ↥M := V.subgroupOf M
  let N : Subgroup ↥P0 := V0.subgroupOf P0
  haveI hV0_normal : V0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_M).mpr h.le_normalizer
  let ρ : ↥M →* MulAut ↥P0 := MulAut.conjNormal
  change Subgroup.map (ρ a) N = N
  apply le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hconj : (((ρ a) y : ↥P0) : ↥M) = a * (y : ↥M) * a⁻¹ := by
      simpa [ρ] using MulAut.conjNormal_apply (H := P0) (a : G) y
    change (((ρ a) y : ↥P0) : ↥M) ∈ V0
    rw [hconj]
    exact hV0_normal.conj_mem (y : ↥M) hy a
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨(ρ a⁻¹) x, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hxV : (x : ↥M) ∈ V0 := Subgroup.mem_subgroupOf.mp hx
      have hconj : (((ρ a⁻¹) x : ↥P0) : ↥M) = a⁻¹ * (x : ↥M) * a := by
        simpa [ρ] using MulAut.conjNormal_apply (H := P0) ((a⁻¹ : ↥M) : G) x
      rw [hconj]
      simpa [mul_assoc] using hV0_normal.conj_mem (x : ↥M) hxV a⁻¹
    · have hprod : (ρ a) * (ρ a⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      change (ρ a) ((ρ a⁻¹) x) = x
      rw [← MulAut.mul_apply, hprod, MulAut.one_apply]

private theorem subgroupOf_le_ker_quotientAction (h : Hyp M V)
    [((Pc M V).subgroupOf M).Normal]
    [((V.subgroupOf M).subgroupOf ((Pc M V).subgroupOf M)).Normal]
    {X : Subgroup G} (hXP : ⁅Pc M V, X⁆ ≤ V) :
    X.subgroupOf M ≤
      (quotientAction (MulAut.conjNormal (H := (Pc M V).subgroupOf M))
        ((V.subgroupOf M).subgroupOf ((Pc M V).subgroupOf M))
        (map_conjNormal_subgroupOf_eq h)).ker := by
  let P0 : Subgroup ↥M := (Pc M V).subgroupOf M
  let V0 : Subgroup ↥M := V.subgroupOf M
  let N : Subgroup ↥P0 := V0.subgroupOf P0
  haveI hV0_normal : V0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_M).mpr h.le_normalizer
  haveI hN_normal : N.Normal := hV0_normal.subgroupOf P0
  let ρ : ↥M →* MulAut ↥P0 := MulAut.conjNormal
  change X.subgroupOf M ≤ (quotientAction ρ N (map_conjNormal_subgroupOf_eq h)).ker
  intro x hx
  rw [MonoidHom.mem_ker]
  ext q
  induction q using QuotientGroup.induction_on with
  | H p =>
    have hpP : (p : G) ∈ Pc M V := Subgroup.mem_subgroupOf.mp p.2
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hcomm : ⁅(x : ↥M), (p : ↥M)⁆ ∈ V0 := by
      rw [Subgroup.mem_subgroupOf]
      have hmem : ⁅(x : G), (p : G)⁆ ∈ ⁅X, Pc M V⁆ :=
        Subgroup.commutator_mem_commutator hxX hpP
      have hv : ⁅(x : G), (p : G)⁆ ∈ V := hXP (by
        rwa [Subgroup.commutator_comm X (Pc M V)] at hmem)
      change ⁅(x : G), ((p : ↥M) : G)⁆ ∈ V
      exact hv
    change (QuotientGroup.congr N N (ρ x) (map_conjNormal_subgroupOf_eq h x))
        (QuotientGroup.mk p) = QuotientGroup.mk p
    rw [QuotientGroup.congr_mk]
    refine (QuotientGroup.eq_iff_div_mem).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have hcoecalc : ((((ρ x) p) / p : ↥P0) : ↥M) =
        (x : ↥M) * (p : ↥M) * (x : ↥M)⁻¹ * (p : ↥M)⁻¹ := by
      simp [div_eq_mul_inv, ρ, MulAut.conjNormal_apply, mul_assoc]
    rw [hcoecalc]
    simpa [commutatorElement_def] using hcomm

private theorem commutator_mem_V_of_mem_ker (h : Hyp M V)
    [((Pc M V).subgroupOf M).Normal]
    [((V.subgroupOf M).subgroupOf ((Pc M V).subgroupOf M)).Normal]
    {m0 : ↥M}
    (hm0 : m0 ∈ (quotientAction (MulAut.conjNormal (H := (Pc M V).subgroupOf M))
      ((V.subgroupOf M).subgroupOf ((Pc M V).subgroupOf M))
      (map_conjNormal_subgroupOf_eq h)).ker)
    {p : G} (hp : p ∈ Pc M V) : ⁅(m0 : G), p⁆ ∈ V := by
  let P0 : Subgroup ↥M := (Pc M V).subgroupOf M
  let V0 : Subgroup ↥M := V.subgroupOf M
  let N : Subgroup ↥P0 := V0.subgroupOf P0
  haveI hV0_normal : V0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_M).mpr h.le_normalizer
  haveI hN_normal : N.Normal := hV0_normal.subgroupOf P0
  let ρ : ↥M →* MulAut ↥P0 := MulAut.conjNormal
  have hpM : p ∈ M := h.Pc_le_M hp
  let p0 : ↥P0 := ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.mpr hp⟩
  have hfix : (QuotientGroup.congr N N (ρ m0) (map_conjNormal_subgroupOf_eq h m0))
      (QuotientGroup.mk p0) = QuotientGroup.mk p0 := by
    have h1 : (quotientAction ρ N (map_conjNormal_subgroupOf_eq h)) m0 = 1 :=
      MonoidHom.mem_ker.mp hm0
    have h2 := congrArg (fun f : MulAut (↥P0 ⧸ N) => f (QuotientGroup.mk p0)) h1
    simpa [quotientAction] using h2
  rw [QuotientGroup.congr_mk] at hfix
  have hdiv : (((ρ m0) p0) / p0 : ↥P0) ∈ N :=
    (QuotientGroup.eq_iff_div_mem).mp hfix
  rw [Subgroup.mem_subgroupOf] at hdiv
  have hcoecalc : ((((ρ m0) p0) / p0 : ↥P0) : ↥M) =
      (m0 : ↥M) * (p0 : ↥M) * (m0 : ↥M)⁻¹ * (p0 : ↥M)⁻¹ := by
    simp [div_eq_mul_inv, ρ, MulAut.conjNormal_apply, mul_assoc]
  rw [hcoecalc] at hdiv
  rw [Subgroup.mem_subgroupOf] at hdiv
  simpa [commutatorElement_def] using hdiv

private theorem commutator_normalClosure_le_V (h : Hyp M V) {X : Subgroup G}
    (hXP : ⁅Pc M V, X⁆ ≤ V) :
    ∀ m0 : ↥M, m0 ∈ Subgroup.normalClosure (X.subgroupOf M) →
      ∀ p ∈ Pc M V, ⁅(m0 : G), p⁆ ∈ V := by
  let P : Subgroup G := Pc M V
  let P0 : Subgroup ↥M := P.subgroupOf M
  let V0 : Subgroup ↥M := V.subgroupOf M
  let N : Subgroup ↥P0 := V0.subgroupOf P0
  haveI hP0_normal : P0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.Pc_le_M).mpr h.le_normalizer_Pc
  haveI hV0_normal : V0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_M).mpr h.le_normalizer
  haveI hN_normal : N.Normal := hV0_normal.subgroupOf P0
  let ρ : ↥M →* MulAut ↥P0 := MulAut.conjNormal
  let φ : ↥M →* MulAut (↥P0 ⧸ N) :=
    quotientAction ρ N (fun a => map_conjNormal_subgroupOf_eq h a)
  have hX0_ker : X.subgroupOf M ≤ φ.ker :=
    subgroupOf_le_ker_quotientAction h hXP
  have hY0_ker : Subgroup.normalClosure (X.subgroupOf M) ≤ φ.ker := by
    haveI : φ.ker.Normal := MonoidHom.normal_ker φ
    exact Subgroup.normalClosure_le_normal hX0_ker
  intro m0 hm0 p hp
  exact commutator_mem_V_of_mem_ker h (hY0_ker hm0) hp

private theorem eq_one_of_odd_of_commutator_le (h : Hyp M V) {X : Subgroup G} {y0 : ↥M} {y : G}
    (hy0eq : (y0 : G) = y) (hycent : y ∈ Subgroup.centralizer (V : Set G))
    (hcom : ∀ m0 : ↥M, m0 ∈ Subgroup.normalClosure (X.subgroupOf M) →
      ∀ p ∈ Pc M V, ⁅(m0 : G), p⁆ ∈ V)
    (hy0Y : y0 ∈ Subgroup.normalClosure (X.subgroupOf M))
    (hyM : y ∈ M) (hyodd : Odd (orderOf y)) : y = 1 := by
  let P : Subgroup G := Pc M V
  let R : Subgroup G := Subgroup.zpowers y
  have hPR : ⁅P, R⁆ ≤ V := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_le]
    intro k hk p hp
    have hR_eq : Subgroup.map M.subtype (Subgroup.zpowers y0) = R := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hy0eq
    rw [← hR_eq] at hk
    obtain ⟨k0, hk0, hk0eq⟩ := Subgroup.mem_map.mp hk
    rw [← hk0eq]
    exact hcom k0 (Subgroup.zpowers_le.mpr hy0Y hk0) p hp
  have hRnormP : R ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (h.le_normalizer_Pc hyM)
  have hRcentV : R ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hycent
  have hVR : ⁅V, R⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRcentV
  have hdouble : ⁅⁅P, R⁆, R⁆ = ⊥ := by
    simpa [hVR] using Subgroup.commutator_mono hPR (le_refl R)
  have hP2 : IsPGroup 2 P := (inSubgroup_pCore_two M).1.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have hcoprime : Nat.Coprime (Nat.card R) (Nat.card P) := by
    rw [show Nat.card R = orderOf y by
      simpa [R] using Nat.card_zpowers y, hk]
    exact (Nat.coprime_two_left.mpr hyodd).symm.pow_right k
  have hPRbot :=
    CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot
      P R hRnormP hcoprime hdouble
  have hRcentP : R ≤ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.commutator_comm] at hPRbot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPRbot
  have hyP : y ∈ Subgroup.centralizer (P : Set G) :=
    hRcentP (Subgroup.mem_zpowers y)
  have hyV : y ∈ V := by
    rw [← h.centralizer_Pc]
    exact hyP
  exact Tim78.eq_one_of_odd_of_isPGroup h.isPGroup_V hyV hyodd

private theorem eq_one_of_odd_of_mem_normalClosure (h : Hyp M V) {X : Subgroup G}
    (hXV : X ≤ Subgroup.centralizer (V : Set G))
    (hcom : ∀ m0 : ↥M, m0 ∈ Subgroup.normalClosure (X.subgroupOf M) →
      ∀ p ∈ Pc M V, ⁅(m0 : G), p⁆ ∈ V)
    {y0 : ↥M} (hy0Y : y0 ∈ Subgroup.normalClosure (X.subgroupOf M))
    {y : G} (hy0eq : (y0 : G) = y) (hyM : y ∈ M) (hyodd : Odd (orderOf y)) : y = 1 := by
  have hX0_cent : X.subgroupOf M ≤ Subgroup.centralizer (V.subgroupOf M : Set ↥M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    apply Subtype.ext
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    exact Subgroup.mem_centralizer_iff.mp (hXV hxX) (v : G) hvV
  have hY0_cent : Subgroup.normalClosure (X.subgroupOf M) ≤
      Subgroup.centralizer (V.subgroupOf M : Set ↥M) := by
    haveI hV0_normal : (V.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_M).mpr h.le_normalizer
    haveI : (Subgroup.centralizer (V.subgroupOf M : Set ↥M)).Normal :=
      Subgroup.normal_centralizer
    exact Subgroup.normalClosure_le_normal hX0_cent
  have hy_cent : y ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvM : v ∈ M := h.le_M hv
    have hmem : (⟨v, hvM⟩ : ↥M) ∈ V.subgroupOf M := Subgroup.mem_subgroupOf.mpr hv
    have h := (hY0_cent hy0Y) ⟨v, hvM⟩ hmem
    have hG : v * (y0 : G) = (y0 : G) * v := by
      simpa using congrArg (fun z : ↥M => (z : G)) h
    rw [← hy0eq]
    exact hG
  exact eq_one_of_odd_of_commutator_le h hy0eq hy_cent hcom hy0Y hyM hyodd

theorem le_pCore_of_commutator_le (h : Hyp M V) {X : Subgroup G} (hXM : X ≤ M)
    (hXV : X ≤ Subgroup.centralizer (V : Set G)) (hXP : ⁅Pc M V, X⁆ ≤ V) :
    X ≤ inSubgroup (pCore 2) M := by
  classical
  let Y0 : Subgroup ↥M := Subgroup.normalClosure (X.subgroupOf M)
  let Y : Subgroup G := Y0.map M.subtype
  have hY_le_M : Y ≤ M := Subgroup.map_subtype_le Y0
  have hYnorm : M ≤ Subgroup.normalizer (Y : Set G) := by
    have hsub : Y.subgroupOf M = Y0 := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyx' : y = x := Subtype.ext hyx
        simpa [hyx'] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le Y0)).mp
    rw [hsub]
    exact Subgroup.normalClosure_normal
  have hXY : X ≤ Y := by
    intro x hx
    rw [show Y = Y0.map M.subtype from rfl, Subgroup.mem_map]
    exact ⟨⟨x, hXM hx⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hYodd_triv : ∀ y ∈ Y, Odd (orderOf y) → y = 1 := by
    intro y hyY hyodd
    obtain ⟨y0, hy0Y, hy0eq⟩ := Subgroup.mem_map.mp hyY
    exact eq_one_of_odd_of_mem_normalClosure h hXV
      (commutator_normalClosure_le_V h hXP) hy0Y hy0eq (hY_le_M hyY) hyodd
  have hY2 : IsPGroup 2 Y := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card Y) with ⟨k, hk⟩ |
      ⟨q, hqprime, hqdvd, hqodd⟩
    · exact IsPGroup.of_card (p := 2) hk
    · haveI : Fact (Nat.Prime q) := ⟨hqprime⟩
      obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      have hyY : (y : G) ∈ Y := y.2
      have hodd : Odd (orderOf (y : G)) := by
        rw [← Subgroup.orderOf_mk (y : G) y.2, hyord]
        exact hqodd
      have hy1 : (y : G) = 1 := hYodd_triv (y : G) hyY hodd
      have hq1 : q = 1 := by
        rw [← hyord]
        have h2 : orderOf y = orderOf (y : G) := by
          simpa using Subgroup.orderOf_mk (y : G) y.2
        rw [h2, hy1, orderOf_one]
      exact absurd hq1 hqprime.ne_one
  have hYQ : Y ≤ inSubgroup (pCore 2) M :=
    Tim78.le_inSubgroup_pCore hY_le_M hYnorm hY2
  exact hXY.trans hYQ

end Hyp

end CFSG.RankThree.GF2n.Tim81
