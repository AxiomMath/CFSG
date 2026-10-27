module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCfg
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPDescent
import CFSG.GH74.GLS.Balance.SolvCompBasic
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

theorem components_conj_of_sup_eq_top {Y : Type} [Group Y] [Finite Y] {L T : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hT : IsPGroup 2 T) (hsup : L ⊔ T = ⊤) :
    ∀ J : Subgroup Y, IsComponentOf J ⊤ → ∃ t ∈ T, J = conjSubgroup L t := by
  classical
  intro J hJ
  set N₀ : Subgroup Y := ⨆ t : T, conjSubgroup L (t : Y) with hN₀
  have hLN : L ≤ N₀ := by
    have h : conjSubgroup L ((1 : T) : Y) ≤ N₀ :=
      le_iSup (fun t : T => conjSubgroup L (t : Y)) (1 : T)
    simpa [conjSubgroup_one] using h
  have hle : ∀ u : Y, u ∈ T → conjSubgroup N₀ u ≤ N₀ := by
    intro u hu
    rw [hN₀]
    rw [show conjSubgroup (⨆ t : T, conjSubgroup L (t : Y)) u
        = (⨆ t : T, conjSubgroup L (t : Y)).map (MulAut.conj u⁻¹).toMonoidHom from rfl,
      Subgroup.map_iSup]
    apply iSup_le
    intro s
    rw [show (conjSubgroup L (s : Y)).map (MulAut.conj u⁻¹).toMonoidHom
        = conjSubgroup (conjSubgroup L (s : Y)) u from rfl, conjSubgroup_conjSubgroup]
    exact le_iSup (fun v : T => conjSubgroup L (v : Y))
      (⟨(s : Y) * u, T.mul_mem s.2 hu⟩ : T)
  have hconj_eq : ∀ u : Y, u ∈ T → conjSubgroup N₀ u = N₀ := by
    intro u hu
    refine le_antisymm (hle u hu) ?_
    have h1 : conjSubgroup N₀ u⁻¹ = N₀ := by
      refine le_antisymm (hle u⁻¹ (T.inv_mem hu)) ?_
      calc N₀ = conjSubgroup (conjSubgroup N₀ u) u⁻¹ := by
            simp [conjSubgroup_conjSubgroup, conjSubgroup_one]
        _ ≤ conjSubgroup N₀ u⁻¹ := Subgroup.map_mono (hle u hu)
    have h2 : conjSubgroup N₀ u = N₀ := by
      calc conjSubgroup N₀ u = conjSubgroup (conjSubgroup N₀ u⁻¹) u := by rw [h1]
        _ = N₀ := by simp [conjSubgroup_conjSubgroup, conjSubgroup_one]
    exact le_of_eq h2.symm
  have hnorm : N₀.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    apply sup_le
    · intro x hx
      exact Subgroup.le_normalizer (hLN hx)
    · intro t ht
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h := hconj_eq t⁻¹ (T.inv_mem ht)
      simpa [conjSubgroup] using h
  let π : Y →* Y ⧸ N₀ := QuotientGroup.mk' N₀
  have hTmap : T.map π = ⊤ := by
    have h1 : (⊤ : Subgroup Y).map π = L.map π ⊔ T.map π := by
      rw [← hsup, Subgroup.map_sup]
    rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N₀)] at h1
    have hLbot : L.map π = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hLN hy
    rw [hLbot, bot_sup_eq] at h1
    exact h1.symm
  have htop : IsPGroup 2 (⊤ : Subgroup (Y ⧸ N₀)) := by
    have h := hT.map π
    rwa [hTmap] at h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  have hJN : J ≤ N₀ := by
    have hPimg : IsPGroup 2 (J.map π) := htop.to_le le_top
    haveI : Group.IsPerfect ↥(J.map π) := Group.IsPerfect.map (f := π)
    haveI : Group.IsNilpotent ↥(J.map π) := hPimg.isNilpotent
    have hsolv : Group.IsSolvable ↥(J.map π) := inferInstance
    have hsub : Subsingleton ↥(J.map π) := by
      by_contra hns
      haveI : Nontrivial ↥(J.map π) := not_subsingleton_iff_nontrivial.mp hns
      exact Group.IsPerfect.not_isSolvable ↥(J.map π) hsolv
    intro x hx
    have hx' : π x ∈ J.map π := Subgroup.mem_map_of_mem π hx
    have hzero : (⟨π x, hx'⟩ : ↥(J.map π)) = 1 := Subsingleton.elim _ _
    have hπx : π x = 1 := congrArg Subtype.val hzero
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπx
    exact hπx
  by_contra hcon
  have hcomp : ∀ t : T, IsComponentOf (conjSubgroup L (t : Y)) ⊤ := by
    intro t
    have h := (CFSG.ComponentClassification.LocalComponents.equiv_iff
      (MulAut.conj (t : Y)⁻¹) L).mpr hL
    simpa [conjSubgroup] using h
  have hcomm : ∀ t : T, ⁅J, conjSubgroup L (t : Y)⁆ = ⊥ := by
    intro t
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne J _
      hJ (hcomp t) (fun heq => hcon ⟨(t : Y), t.2, heq⟩)
  have hJcent : J ≤ Subgroup.centralizer (N₀ : Set Y) := by
    rw [hN₀, Subgroup.iSup_eq_closure, Subgroup.centralizer_closure]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨t, hyt⟩
    have hxc : x ∈ Subgroup.centralizer ((conjSubgroup L (t : Y)) : Set Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm t) hx
    exact Subgroup.mem_centralizer_iff.mp hxc y hyt
  haveI : IsMulCommutative ↥J := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp (hJcent a.2) (b : Y) (hJN b.2)).symm
  have hsub : Subsingleton ↥J := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact (not_subsingleton_iff_nontrivial.mpr
    (CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2)) hsub

variable {Q : Type} [Group Q] [Finite Q] {T A B R L₀ : Subgroup Q}

private theorem wc813pcomp_not_le_of_component (h : Cfg813 T A B R L₀) {X : Subgroup Q}
    (hX : IsComponentOf X ⊤) : ¬ X ≤ R := by
  intro hXR
  haveI : Group.IsPerfect ↥X := ⟨hX.2.2.1⟩
  haveI : Nontrivial ↥X := CFSG.ComponentClassification.Quasisimple.nontrivial hX.2.2
  haveI : Group.IsSolvable ↥R := h.R_solvable
  have hsolv : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXR)
      (Subgroup.inclusion_injective hXR)
  exact Group.IsPerfect.not_isSolvable ↥X hsolv

private theorem wc813pcomp_map_conjSubgroup {G H : Type} [Group G] [Group H]
    (f : G →* H) (A : Subgroup G) (g : G) :
    (conjSubgroup A g).map f = conjSubgroup (A.map f) (f g) := by
  rw [show conjSubgroup A g = A.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      show conjSubgroup (A.map f) (f g)
        = (A.map f).map (MulAut.conj (f g)⁻¹).toMonoidHom from rfl]
  rw [Subgroup.map_map (K := A) (f := (MulAut.conj g⁻¹).toMonoidHom) (g := f),
      Subgroup.map_map (K := A) (f := f) (g := (MulAut.conj (f g)⁻¹).toMonoidHom)]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul]

theorem Cfg813.component_cover (h : Cfg813 T A B R L₀) :
    ∀ J : Subgroup Q, IsComponentOf J ⊤ → ∃ t ∈ T, J ⊔ R = conjSubgroup L₀ t := by
  intro J hJ
  haveI : R.Normal := h.R_normal
  let π : Q →* Q ⧸ R := QuotientGroup.mk' R
  have hJR : ¬ J ≤ R := wc813pcomp_not_le_of_component h hJ
  have hJcomp : IsComponentOf (J.map π) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.image hJ π
      (QuotientGroup.mk'_surjective R)
      (by rw [QuotientGroup.ker_mk']; exact hJR)
  have hL0sub : IsSubnormal L₀ ⊤ := h.L₀_comp.2.2.2.1
  have hL0subImage : CFSG.Open.IsSubnormal (L₀.map π) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective R)
        (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hL0sub
          Subgroup.IsSubnormal.top))
  have hL0q : CFSG.Open.IsQuasisimple ↥(L₀.map π) := by
    obtain ⟨X, hXgrp, φ, hφsurj, hφker, hXq⟩ := h.L₀_comp.2.2.2.2
    letI : Group X := hXgrp
    let r0 : ↥L₀ →* Q ⧸ R := π.domRestrict L₀
    let resπ : ↥L₀ →* r0.range := r0.rangeRestrict
    have hresπsurj : Function.Surjective resπ := MonoidHom.rangeRestrict_surjective r0
    have hkerπ : resπ.ker = R.subgroupOf L₀ := by
      rw [show resπ = r0.rangeRestrict from rfl, MonoidHom.ker_rangeRestrict,
        show r0 = π.domRestrict L₀ from rfl, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    have hkerφ : φ.ker = R.subgroupOf L₀ := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hφker k
    have hrange : r0.range = L₀.map π := by
      rw [show r0 = π.domRestrict L₀ from rfl,
        show π.domRestrict L₀ = π.comp L₀.subtype from rfl,
        ← MonoidHom.map_range π L₀.subtype, Subgroup.range_subtype]
    have hequiv : r0.range ≃* X :=
      (QuotientGroup.quotientKerEquivOfSurjective resπ hresπsurj).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq (M := φ.ker) (N := resπ.ker)
          (by rw [hkerπ, hkerφ])).symm.trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj))
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      ((MulEquiv.subgroupCongr hrange).symm.trans hequiv)
      ⟨hXq.1.commutator_eq_top, hXq.2.1⟩
  have hL0comp : IsComponentOf (L₀.map π) ⊤ := ⟨le_top, hL0subImage, hL0q⟩
  have hTcomp : IsPGroup 2 (T.map π) := h.sylow.isPGroup.map π
  have hsup : L₀.map π ⊔ T.map π = ⊤ := by
    rw [← Subgroup.map_sup, h.L₀_sup,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective R)]
  obtain ⟨u, hu, hJu⟩ :=
    components_conj_of_sup_eq_top hL0comp hTcomp hsup (J.map π) hJcomp
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
  refine ⟨t, ht, ?_⟩
  have hmapconj : (conjSubgroup L₀ t).map π = conjSubgroup (L₀.map π) (π t) :=
    wc813pcomp_map_conjSubgroup π L₀ t
  have heq := congrArg (Subgroup.comap π) hJu
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', ← hmapconj, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk'] at heq
  have hRle : R ≤ conjSubgroup L₀ t := by
    intro r hr
    rw [mem_conjSubgroup_iff]
    exact h.L₀_comp.2.1 (h.R_normal.conj_mem r hr t)
  rw [sup_eq_left.mpr hRle] at heq
  exact heq

private theorem wc813pcomp_hasQuotShape_of_component (h : Cfg813 T A B R L₀)
    {J : Subgroup Q} (hJ : IsComponentOf J ⊤)
    (P : ∀ (X : Type) [Group X], Prop) (hP : HasQuotShape L₀ (R : Set Q) P) :
    HasQuotShape J (R : Set Q) P := by
  haveI : R.Normal := h.R_normal
  obtain ⟨t₀, _ht₀, hJt₀⟩ := Cfg813.component_cover h J hJ
  obtain ⟨X, hXgrp, φ₀, hφ₀surj, hφ₀ker, hPX⟩ := hP
  letI : Group X := hXgrp
  have hmem : ∀ j : ↥J, t₀ * (j : Q) * t₀⁻¹ ∈ L₀ := fun j =>
    mem_conjSubgroup_iff.mp
      (hJt₀ ▸ (Subgroup.mem_sup_left j.2 : (j : Q) ∈ J ⊔ R))
  let φ : ↥J →* X :=
    { toFun := fun j => φ₀ ⟨t₀ * (j : Q) * t₀⁻¹, hmem j⟩
      map_one' := by
        have h1 : (⟨t₀ * (1 : ↥J) * t₀⁻¹, hmem 1⟩ : ↥L₀) = 1 := Subtype.ext (by simp)
        rw [h1, map_one]
      map_mul' := by
        intro a b
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        group }
  have hkerφ : ∀ j : ↥J, φ j = 1 ↔ (j : Q) ∈ R := by
    intro j
    change φ₀ ⟨t₀ * (j : Q) * t₀⁻¹, hmem j⟩ = 1 ↔ (j : Q) ∈ R
    rw [hφ₀ker]
    constructor
    · intro hj
      have := h.R_normal.conj_mem (t₀ * (j : Q) * t₀⁻¹) hj t₀⁻¹
      simpa [mul_assoc] using this
    · intro hj
      exact h.R_normal.conj_mem (j : Q) hj t₀
  have hsurjφ : Function.Surjective φ := by
    intro y
    obtain ⟨ℓ, rfl⟩ := hφ₀surj y
    have hw : t₀⁻¹ * (ℓ : Q) * t₀ ∈ conjSubgroup L₀ t₀ := by
      rw [mem_conjSubgroup_iff]
      have h : t₀ * (t₀⁻¹ * (ℓ : Q) * t₀) * t₀⁻¹ = (ℓ : Q) := by group
      rw [h]
      exact ℓ.2
    rw [← hJt₀] at hw
    obtain ⟨j, hj, r, hr, hjr⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    refine ⟨⟨j, hj⟩, ?_⟩
    change φ₀ ⟨t₀ * j * t₀⁻¹, hmem ⟨j, hj⟩⟩ = φ₀ ℓ
    have hr' : t₀ * r⁻¹ * t₀⁻¹ ∈ R := h.R_normal.conj_mem r⁻¹ (R.inv_mem hr) t₀
    have hjeq : (⟨t₀ * j * t₀⁻¹, hmem ⟨j, hj⟩⟩ : ↥L₀)
        = ℓ * ⟨t₀ * r⁻¹ * t₀⁻¹, h.L₀_comp.2.1 hr'⟩ := by
      apply Subtype.ext
      simp only [Subtype.coe_mk, Subgroup.coe_mul]
      have h2 : t₀ * j * t₀⁻¹ = (ℓ : Q) * (t₀ * r⁻¹ * t₀⁻¹) := by
        have h4 : (ℓ : Q) = t₀ * (j * r) * t₀⁻¹ := by
          rw [hjr]
          group
        rw [h4]
        group
      exact h2
    have hz : φ₀ ⟨t₀ * r⁻¹ * t₀⁻¹, h.L₀_comp.2.1 hr'⟩ = 1 :=
      (hφ₀ker ⟨t₀ * r⁻¹ * t₀⁻¹, h.L₀_comp.2.1 hr'⟩).mpr hr'
    rw [hjeq, map_mul, hz, mul_one]
  exact ⟨X, hXgrp, φ, hsurjφ, hkerφ, hPX⟩

theorem Cfg813.inf_R_eq_center (h : Cfg813 T A B R L₀) {J : Subgroup Q} (hJ : IsComponentOf J ⊤) :
    ∀ x : Q, x ∈ J ⊓ R ↔ ∃ hx : x ∈ J, (⟨x, hx⟩ : ↥J) ∈ Subgroup.center ↥J := by
  intro x
  constructor
  · intro hx
    obtain ⟨hxJ, hxR⟩ := Subgroup.mem_inf.mp hx
    refine ⟨hxJ, ?_⟩
    haveI : Group.IsSolvable ↥R := h.R_solvable
    have hRsub : IsSubnormal R ⊤ :=
      CFSG.Open.IsSubnormal.of_mathlib h.R_normal.isSubnormal
    have hcomm : ⁅J, R⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
        J R hJ hRsub
    have hRcent : R ≤ Subgroup.centralizer (J : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact hcomm)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    exact Subgroup.mem_centralizer_iff.mp (hRcent hxR) (y : Q) y.2
  · rintro ⟨hxJ, hxcent⟩
    refine Subgroup.mem_inf.mpr ⟨hxJ, ?_⟩
    obtain ⟨X, hXgrp, φ, hφsurj, hφker, hXsimple⟩ :=
      wc813pcomp_hasQuotShape_of_component h hJ (fun X _ => IsSimpleGroup X) h.L₀_simple
    letI : Group X := hXgrp
    haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
    haveI : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
    haveI : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := φ) hφsurj
    haveI : IsSimpleGroup X := hXsimple
    have hcommX : ¬ IsMulCommutative X := Group.IsPerfect.not_isMulCommutative X
    have hcenterX : Subgroup.center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hbot | htop
      · exact hbot
      · exact absurd (Subgroup.center_eq_top_iff.mp htop) hcommX
    have hzmem : φ ⟨x, hxJ⟩ ∈ (Subgroup.center ↥J).map φ :=
      Subgroup.mem_map_of_mem φ hxcent
    have hzX : φ ⟨x, hxJ⟩ ∈ Subgroup.center X :=
      Subgroup.map_center_le_center (f := φ) hφsurj hzmem
    rw [hcenterX, Subgroup.mem_bot] at hzX
    exact (hφker ⟨x, hxJ⟩).mp hzX

theorem Cfg813.center_odd (h : Cfg813 T A B R L₀) {J : Subgroup Q} (hJ : IsComponentOf J ⊤) :
    Odd (Nat.card (Subgroup.center ↥J)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥J) := even_iff_two_dvd.mp heven
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  let w : ↥J := (z : ↥J)
  have hwmem : w ∈ Subgroup.center ↥J := z.2
  have hworder : orderOf w = 2 := by
    rw [show w = (z : ↥J) from rfl, Subgroup.orderOf_coe, hzorder]
  haveI : R.Normal := h.R_normal
  let U : Subgroup ↥J := Subgroup.zpowers w
  have hUcard : Nat.card U = 2 := by
    rw [show U = Subgroup.zpowers w from rfl, Nat.card_zpowers, hworder]
  have hUp : IsPGroup 2 U := IsPGroup.of_card (n := 1) (by rw [hUcard]; norm_num)
  have hUnormal : U.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    change (Subgroup.zpowers w).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers w
    rw [MonoidHom.map_zpowers]
    congr 1
    change g * w * g⁻¹ = w
    have hg := Subgroup.mem_center_iff.mp hwmem g
    rw [hg]
    group
  haveI : U.Normal := hUnormal
  have hJsub : J.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hJ.2.1
      Subgroup.IsSubnormal.top
  have hle : U.map J.subtype ≤ CFSG.pCore 2 Q :=
    CFSG.GH74.GLS.Balance.SolvComp.map_le_pCore_of_isSubnormal hJsub hUp
  have hcore : CFSG.pCore 2 Q = ⊥ :=
    h.no_normal_two (CFSG.pCore 2 Q) (CFSG.pCore_normal (p := 2) (G := Q))
      (CFSG.pCore_isPGroup (p := 2) (G := Q))
  have hzle : (w : Q) ∈ CFSG.pCore 2 Q :=
    hle (Subgroup.mem_map_of_mem J.subtype (Subgroup.mem_zpowers w))
  rw [hcore, Subgroup.mem_bot] at hzle
  have hz1 : w = 1 := Subtype.ext hzle
  rw [hz1, orderOf_one] at hworder
  exact absurd hworder (by norm_num)

private theorem wc813pcomp_eq_of_sup_R_eq (h : Cfg813 T A B R L₀) {X X' : Subgroup Q}
    (hX : IsComponentOf X ⊤) (hX' : IsComponentOf X' ⊤) (heq : X ⊔ R = X' ⊔ R) : X = X' := by
  by_contra hne
  haveI : R.Normal := h.R_normal
  let π : Q →* Q ⧸ R := QuotientGroup.mk' R
  have hRmap : R.map π = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨r, hr, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hr
  have hXRmap : X.map π = (X ⊔ R).map π := by
    rw [Subgroup.map_sup, hRmap, sup_bot_eq]
  have hX'Rmap : X'.map π = (X' ⊔ R).map π := by
    rw [Subgroup.map_sup, hRmap, sup_bot_eq]
  have himg : X.map π = X'.map π := by
    rw [hXRmap, heq, ← hX'Rmap]
  have hcompX : IsComponentOf (X.map π) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.image hX π
      (QuotientGroup.mk'_surjective R)
      (by rw [QuotientGroup.ker_mk']; exact wc813pcomp_not_le_of_component h hX)
  have hcomm : ⁅X, X'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne X X' hX hX' hne
  have hcommmap : ⁅X.map π, X'.map π⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
  rw [← himg] at hcommmap
  haveI : IsMulCommutative ↥(X.map π) := Subgroup.commutator_self_eq_bot_iff.mp hcommmap
  haveI : Group.IsPerfect ↥(X.map π) := ⟨hcompX.2.2.1⟩
  haveI : Nontrivial ↥(X.map π) :=
    CFSG.ComponentClassification.Quasisimple.nontrivial hcompX.2.2
  exact Group.IsPerfect.not_isMulCommutative ↥(X.map π) inferInstance

theorem Cfg813.component_conj (h : Cfg813 T A B R L₀) {J J' : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hJ' : IsComponentOf J' ⊤) : ∃ t ∈ T, J' = conjSubgroup J t := by
  obtain ⟨t₁, ht₁, h₁⟩ := Cfg813.component_cover h J hJ
  obtain ⟨t₂, ht₂, h₂⟩ := Cfg813.component_cover h J' hJ'
  haveI : R.Normal := h.R_normal
  refine ⟨t₁⁻¹ * t₂, T.mul_mem (T.inv_mem ht₁) ht₂, ?_⟩
  have hconjcomp : IsComponentOf (conjSubgroup J (t₁⁻¹ * t₂)) ⊤ := by
    have hh := (CFSG.ComponentClassification.LocalComponents.equiv_iff
      (MulAut.conj ((t₁⁻¹ * t₂) : Q)⁻¹) J).mpr hJ
    simpa [conjSubgroup] using hh
  have hprod : conjSubgroup J (t₁⁻¹ * t₂) ⊔ R = conjSubgroup L₀ t₂ := by
    have hRfix : R.map (MulAut.conj ((t₁⁻¹ * t₂) : Q)⁻¹).toMonoidHom = R :=
      Subgroup.Normal.map_conj_eq R _
    have hsup : conjSubgroup (J ⊔ R) (t₁⁻¹ * t₂) =
        conjSubgroup J (t₁⁻¹ * t₂) ⊔ R := by
      rw [show conjSubgroup (J ⊔ R) (t₁⁻¹ * t₂)
          = (J ⊔ R).map (MulAut.conj ((t₁⁻¹ * t₂) : Q)⁻¹).toMonoidHom from rfl,
        Subgroup.map_sup]
      rw [show conjSubgroup J (t₁⁻¹ * t₂)
          = J.map (MulAut.conj ((t₁⁻¹ * t₂) : Q)⁻¹).toMonoidHom from rfl]
      rw [show R.map (MulAut.conj ((t₁⁻¹ * t₂) : Q)⁻¹).toMonoidHom = R from hRfix]
    rw [← hsup, h₁, conjSubgroup_conjSubgroup]
    congr 1
    group
  have heq : conjSubgroup J (t₁⁻¹ * t₂) ⊔ R = J' ⊔ R := by
    rw [hprod, ← h₂]
  exact (wc813pcomp_eq_of_sup_R_eq h hconjcomp hJ' heq).symm

private theorem wc813pcomp_centerQuotient_equiv (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (P : ∀ (X : Type) [Group X], Prop)
    (hP : HasQuotShape L₀ (R : Set Q) P) :
    ∃ (X : Type) (_ : Group X), P X ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* X) := by
  obtain ⟨X, hXgrp, φ, hφsurj, hφker, hPX⟩ :=
    wc813pcomp_hasQuotShape_of_component h hJ P hP
  refine ⟨X, hXgrp, hPX, ?_⟩
  letI : Group X := hXgrp
  have hker : φ.ker = Subgroup.center ↥J := by
    ext k
    rw [MonoidHom.mem_ker, hφker k]
    constructor
    · intro hkR
      obtain ⟨hx, hxk⟩ := (Cfg813.inf_R_eq_center h hJ (k : Q)).mp
        (Subgroup.mem_inf.mpr ⟨k.2, hkR⟩)
      convert hxk using 1
    · intro hkc
      exact (Subgroup.mem_inf.mp
        ((Cfg813.inf_R_eq_center h hJ (k : Q)).mpr ⟨k.2, hkc⟩)).2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (M := φ.ker) (N := Subgroup.center ↥J)
    hker).symm.trans (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)⟩

private noncomputable def wc813pcomp_centerBot_equiv {X : Type} [Group X] {J : Subgroup Q}
    (hZbot : Subgroup.center ↥J = ⊥)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* X) : ↥J ≃* X :=
  ((QuotientGroup.quotientMulEquivOfEq (M := Subgroup.center ↥J) (N := ⊥) hZbot).trans
    (QuotientGroup.quotientBot (G := ↥J))).symm.trans e

theorem Cfg813.oddShape5 (hF0 : OddSchurMultiplierFact) (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) : OddShape5 J := by
  refine ⟨hJ.2.2, Cfg813.center_odd h hJ, ?_⟩
  rcases h.L₀_shape with (hL2 | hU3) | ⟨hL34, _hdyn⟩
  · obtain ⟨X, hXgrp, hPX, ⟨e⟩⟩ :=
      wc813pcomp_centerQuotient_equiv h hJ (fun X _ => IsL2 X 2) hL2
    letI : Group X := hXgrp
    have hquot : IsL2 (↥J ⧸ Subgroup.center ↥J) 2 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hPX
    have hZ : Nat.card (Subgroup.center ↥J) = 1 :=
      hF0 ↥J hJ.2.2 (Cfg813.center_odd h hJ) (Or.inl hquot)
    exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv
      (wc813pcomp_centerBot_equiv (Subgroup.eq_bot_of_card_eq (Subgroup.center ↥J) hZ) e).symm hPX)
  · obtain ⟨X, hXgrp, hPX, ⟨e⟩⟩ :=
      wc813pcomp_centerQuotient_equiv h hJ (fun X _ => IsU3 X 2) hU3
    letI : Group X := hXgrp
    have hquot : IsU3 (↥J ⧸ Subgroup.center ↥J) 2 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hPX
    have hZ : Nat.card (Subgroup.center ↥J) = 1 :=
      hF0 ↥J hJ.2.2 (Cfg813.center_odd h hJ) (Or.inr (Or.inl hquot))
    exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv
      (wc813pcomp_centerBot_equiv (Subgroup.eq_bot_of_card_eq (Subgroup.center ↥J) hZ) e).symm hPX))
  · rcases hL34 with hL3 | hSp4
    · obtain ⟨X, hXgrp, hPX, ⟨e⟩⟩ :=
        wc813pcomp_centerQuotient_equiv h hJ (fun X _ => IsL3 X 2) hL3
      letI : Group X := hXgrp
      have hquot : IsL3 (↥J ⧸ Subgroup.center ↥J) 2 :=
        CFSG.Blueprint.LieModel.of_mulEquiv e.symm hPX
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hJ.2.2, hquot⟩)))
    · obtain ⟨X, hXgrp, hPX, ⟨e⟩⟩ :=
        wc813pcomp_centerQuotient_equiv h hJ (fun X _ => IsSp4 X 2) hSp4
      letI : Group X := hXgrp
      have hquot : IsSp4 (↥J ⧸ Subgroup.center ↥J) 2 :=
        CFSG.Blueprint.LieModel.of_mulEquiv e.symm hPX
      have hZ : Nat.card (Subgroup.center ↥J) = 1 :=
        hF0 ↥J hJ.2.2 (Cfg813.center_odd h hJ) (Or.inr (Or.inr hquot))
      have eJ : ↥J ≃* X :=
        wc813pcomp_centerBot_equiv (Subgroup.eq_bot_of_card_eq (Subgroup.center ↥J) hZ) e
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (CFSG.Blueprint.LieModel.of_mulEquiv eJ.symm hPX))))

private theorem wc813pcomp_card_isL2 {X : Type} [Group X] (h : IsL2 X 2) : Nat.card X = 60 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h]; decide

private theorem wc813pcomp_card_isU3 {X : Type} [Group X] (h : IsU3 X 2) : Nat.card X = 62400 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h]; decide

private theorem wc813pcomp_card_isL3 {X : Type} [Group X] (h : IsL3 X 2) : Nat.card X = 20160 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h]; decide

private theorem wc813pcomp_card_isSp4 {X : Type} [Group X] (h : IsSp4 X 2) :
    Nat.card X = 979200 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h]; decide

private theorem wc813pcomp_isMaxParabolicMod_conj {N L P : Subgroup Q} {g : Q}
    (h : IsMaxParabolicMod N L P) :
    IsMaxParabolicMod (conjSubgroup N g) (conjSubgroup L g) (conjSubgroup P g) := by
  obtain ⟨hNP, hPL, hmax, S, hNS, hSL, hSpow, hSodd, hSnorm⟩ := h
  refine ⟨Subgroup.map_mono hNP, ?_, ?_, conjSubgroup S g, Subgroup.map_mono hNS,
    Subgroup.map_mono hSL, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_mono hPL.le) ?_
    intro heq
    apply hPL.ne
    simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using
      congrArg (fun A => conjSubgroup A g⁻¹) heq
  · intro Y' hY'lt hY'le
    have hle' : P ≤ conjSubgroup Y' g⁻¹ := by
      intro p hp
      rw [mem_conjSubgroup_iff]
      apply hY'lt.le
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hp
    have hlt : P < conjSubgroup Y' g⁻¹ := by
      refine lt_of_le_of_ne hle' ?_
      intro heq
      exact hY'lt.ne (by
        simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using
          congrArg (fun A => conjSubgroup A g) heq)
    have hle : conjSubgroup Y' g⁻¹ ≤ L := by
      intro x hx
      have := mem_conjSubgroup_iff.mp (hY'le (mem_conjSubgroup_iff.mp hx))
      simpa [mul_assoc] using this
    have hres := hmax (conjSubgroup Y' g⁻¹) hlt hle
    simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using
      congrArg (fun A => conjSubgroup A g) hres
  · intro s' hs'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
    obtain ⟨k, hk⟩ := hSpow s hs
    refine ⟨k, ?_⟩
    change ((MulAut.conj g⁻¹) s) ^ (2 ^ k) ∈ N.map (MulAut.conj g⁻¹).toMonoidHom
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem _ hk
  · have hri : (conjSubgroup S g).relIndex (conjSubgroup L g) = S.relIndex L := by
      change (S.map (MulAut.conj g⁻¹).toMonoidHom).relIndex
        (L.map (MulAut.conj g⁻¹).toMonoidHom) = S.relIndex L
      rw [Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        S L (MulAut.conj g⁻¹).injective]
    rw [hri]
    exact hSodd
  · have hinf : conjSubgroup L g ⊓ normalizer (conjSubgroup S g)
        = conjSubgroup (L ⊓ normalizer S) g := by
      change (L.map (MulAut.conj g⁻¹).toMonoidHom) ⊓
          normalizer (S.map (MulAut.conj g⁻¹).toMonoidHom)
        = (L ⊓ normalizer S).map (MulAut.conj g⁻¹).toMonoidHom
      rw [Subgroup.map_inf L (normalizer S) (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective]
      congr 1
      exact (Subgroup.map_normalizer_eq_of_bijective S (MulAut.conj g⁻¹).bijective).symm
    rw [hinf]
    exact Subgroup.map_mono hSnorm

private theorem wc813pcomp_actsOnDynkinMod_conj {N L : Subgroup Q} {t : Q} (g : Q)
    (h : ActsOnDynkinMod N L t) :
    ActsOnDynkinMod (conjSubgroup N g) (conjSubgroup L g) (g⁻¹ * t * g) := by
  obtain ⟨htN, P, hP, hne⟩ := h
  refine ⟨?_, conjSubgroup P g, wc813pcomp_isMaxParabolicMod_conj hP, ?_⟩
  · rw [← conjSubgroup_eq_iff_mem_normalizer]
    rw [← conjSubgroup_eq_iff_mem_normalizer] at htN
    rw [show conjSubgroup (conjSubgroup L g) (g⁻¹ * t * g) = conjSubgroup (conjSubgroup L t) g by
          rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
          congr 1
          group,
      htN]
  · intro l' hl'
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
    intro heq
    apply hne l hl
    have h2 : conjSubgroup (conjSubgroup P g)
        ((g⁻¹ * t * g)⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) l)
        = conjSubgroup P (t⁻¹ * l * g) := by
      rw [conjSubgroup_conjSubgroup]
      congr 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h2] at heq
    calc conjSubgroup P (t⁻¹ * l)
        = conjSubgroup (conjSubgroup P (t⁻¹ * l * g)) g⁻¹ := by
          rw [conjSubgroup_conjSubgroup]
          congr 1
          group
      _ = conjSubgroup (conjSubgroup P g) g⁻¹ := by rw [heq]
      _ = P := by simp [conjSubgroup_conjSubgroup, conjSubgroup_one]

private theorem wc813pcomp_eq_inf_sup_of_le_sup {R J P : Subgroup Q} [R.Normal] (hRP : R ≤ P)
    (hPL : P ≤ J ⊔ R) : P = (P ⊓ J) ⊔ R := by
  apply le_antisymm
  · intro p hp
    obtain ⟨j, hj, r, hr, hjr⟩ := Subgroup.mem_sup_of_normal_right.mp (hPL hp)
    have hjP : j ∈ P := by
      have : p * r⁻¹ = j := by rw [← hjr]; group
      rw [← this]
      exact P.mul_mem hp (P.inv_mem (hRP hr))
    rw [← hjr]
    exact Subgroup.mul_mem_sup ⟨hjP, hj⟩ hr
  · exact sup_le inf_le_left hRP

private theorem wc813pcomp_conj_inf_ne {R J P : Subgroup Q} [R.Normal] (hRP : R ≤ P)
    (hPL : P ≤ J ⊔ R) {g : Q} (hg : conjSubgroup J g = J) (hne : conjSubgroup P g ≠ P) :
    conjSubgroup (P ⊓ J) g ≠ P ⊓ J := by
  intro heq
  apply hne
  have hP := wc813pcomp_eq_inf_sup_of_le_sup hRP hPL
  calc conjSubgroup P g
      = conjSubgroup ((P ⊓ J) ⊔ R) g := congrArg (fun A => conjSubgroup A g) hP
    _ = conjSubgroup (P ⊓ J) g ⊔ conjSubgroup R g := by
        simp only [conjSubgroup, Subgroup.map_sup]
    _ = conjSubgroup (P ⊓ J) g ⊔ R := by
        congr 1
        change R.map (MulAut.conj g⁻¹).toMonoidHom = R
        exact Subgroup.Normal.map_conj_eq R g⁻¹
    _ = (P ⊓ J) ⊔ R := by rw [heq]
    _ = P := hP.symm

private theorem wc813pcomp_false_of_isL2 (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hr : RankTwoShape J)
    (hshape : HasQuotShape L₀ (R : Set Q) (fun X _ => IsL2 X 2)) : False := by
  have hodd := Cfg813.center_odd h hJ
  obtain ⟨X, hXgrp, hPX, ⟨e⟩⟩ :=
    wc813pcomp_centerQuotient_equiv h hJ (fun X _ => IsL2 X 2) hshape
  letI : Group X := hXgrp
  have hXcard : Nat.card X = 60 := wc813pcomp_card_isL2 hPX
  have hquot : Nat.card (↥J ⧸ Subgroup.center ↥J) = 60 := by
    rw [← hXcard]; exact Nat.card_congr e.toEquiv
  have hcardJ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
  rcases hr with h3 | hSp4 | hsl3
  · have hJc : Nat.card ↥J = 20160 := wc813pcomp_card_isL3 h3
    have h1 : 20160 = 60 * Nat.card (Subgroup.center ↥J) := by
      rw [← hJc, hcardJ, hquot]
    have hZ : Nat.card (Subgroup.center ↥J) = 336 := by omega
    rw [hZ] at hodd; norm_num at hodd
  · have hJc : Nat.card ↥J = 979200 := wc813pcomp_card_isSp4 hSp4
    have h1 : 979200 = 60 * Nat.card (Subgroup.center ↥J) := by
      rw [← hJc, hcardJ, hquot]
    have hZ : Nat.card (Subgroup.center ↥J) = 16320 := by omega
    rw [hZ] at hodd; norm_num at hodd
  · have hZq : Nat.card (↥J ⧸ Subgroup.center ↥J) = 20160 :=
      wc813pcomp_card_isL3 hsl3.2
    rw [hquot] at hZq; norm_num at hZq

private theorem wc813pcomp_false_of_isU3 (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hr : RankTwoShape J)
    (hshape : HasQuotShape L₀ (R : Set Q) (fun X _ => IsU3 X 2)) : False := by
  obtain ⟨X, hXgrp, hPX, ⟨e⟩⟩ :=
    wc813pcomp_centerQuotient_equiv h hJ (fun X _ => IsU3 X 2) hshape
  letI : Group X := hXgrp
  have hXcard : Nat.card X = 62400 := wc813pcomp_card_isU3 hPX
  have hquot : Nat.card (↥J ⧸ Subgroup.center ↥J) = 62400 := by
    rw [← hXcard]; exact Nat.card_congr e.toEquiv
  have hcardJ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
  rcases hr with h3 | hSp4 | hsl3
  · have hJc : Nat.card ↥J = 20160 := wc813pcomp_card_isL3 h3
    have h1 : 20160 = 62400 * Nat.card (Subgroup.center ↥J) := by
      rw [← hJc, hcardJ, hquot]
    omega
  · have hJc : Nat.card ↥J = 979200 := wc813pcomp_card_isSp4 hSp4
    have h1 : 979200 = 62400 * Nat.card (Subgroup.center ↥J) := by
      rw [← hJc, hcardJ, hquot]
    omega
  · have hZq : Nat.card (↥J ⧸ Subgroup.center ↥J) = 20160 :=
      wc813pcomp_card_isL3 hsl3.2
    rw [hquot] at hZq; norm_num at hZq

theorem Cfg813.dynkin_component (hF0 : OddSchurMultiplierFact) (h : Cfg813 T A B R L₀)
    {J : Subgroup Q} (hJ : IsComponentOf J ⊤) (hr : RankTwoShape J) :
    ∃ t ∈ T ⊓ normalizer (J : Set Q), ActsOnDynkinMod (⊥ : Subgroup Q) J t := by
  rcases h.L₀_shape with (hL2 | hU3) | ⟨_hL34, t₁, ht₁, hacts₁⟩
  · exact (wc813pcomp_false_of_isL2 h hJ hr hL2).elim
  · exact (wc813pcomp_false_of_isU3 h hJ hr hU3).elim
  · obtain ⟨t₀, ht₀, hJt₀⟩ := Cfg813.component_cover h J hJ
    haveI : R.Normal := h.R_normal
    set t₂ : Q := t₀⁻¹ * t₁ * t₀ with ht₂def
    have ht₂T : t₂ ∈ T := by
      rw [ht₂def]
      exact T.mul_mem (T.mul_mem (T.inv_mem ht₀) ht₁.1) ht₀
    have hconjR : conjSubgroup R t₀ = R := by
      rw [conjSubgroup_eq_iff_mem_normalizer]
      rw [Subgroup.normalizer_eq_top_iff.mpr h.R_normal]
      exact Subgroup.mem_top t₀
    have hacts₂ : ActsOnDynkinMod R (J ⊔ R) t₂ := by
      simpa [ht₂def, hconjR, ← hJt₀] using wc813pcomp_actsOnDynkinMod_conj t₀ hacts₁
    have ht₂N : t₂ ∈ normalizer (J ⊔ R : Subgroup Q) := hacts₂.1
    have hcompJ : IsComponentOf (conjSubgroup J t₂) ⊤ := by
      have hh := (CFSG.ComponentClassification.LocalComponents.equiv_iff
        (MulAut.conj t₂⁻¹) J).mpr hJ
      simpa [conjSubgroup] using hh
    have hconjJ : conjSubgroup J t₂ = J := by
      have hNR : conjSubgroup (J ⊔ R) t₂ = J ⊔ R :=
        conjSubgroup_eq_iff_mem_normalizer.mpr ht₂N
      have hsup : conjSubgroup J t₂ ⊔ R = J ⊔ R := by
        rw [show conjSubgroup (J ⊔ R) t₂ = conjSubgroup J t₂ ⊔ R by
              simp only [conjSubgroup, Subgroup.map_sup]
              congr 1
              change R.map (MulAut.conj t₂⁻¹).toMonoidHom = R
              exact Subgroup.Normal.map_conj_eq R t₂⁻¹] at hNR
        exact hNR
      exact wc813pcomp_eq_of_sup_R_eq h hcompJ hJ hsup
    have ht₂NJ : t₂ ∈ normalizer (J : Set Q) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hconjJ
    have hodd : Odd (Nat.card ↥(J ⊓ R)) := by
      have hcard : Nat.card ↥(J ⊓ R) = Nat.card ↥(Subgroup.center ↥J) := by
        apply Nat.card_congr
        exact
          { toFun := fun x => ⟨⟨(x : Q), ((Cfg813.inf_R_eq_center h hJ (x : Q)).mp x.2).choose⟩,
              ((Cfg813.inf_R_eq_center h hJ (x : Q)).mp x.2).choose_spec⟩
            invFun := fun z => ⟨(z : ↥J), (Cfg813.inf_R_eq_center h hJ (z : ↥J)).mpr
              ⟨z.1.2, z.2⟩⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext rfl }
      rw [hcard]
      exact Cfg813.center_odd h hJ
    obtain ⟨P, hPmax, hPne⟩ := hacts₂.2
    have hP'max : IsMaxParabolicMod (⊥ : Subgroup Q) J (P ⊓ J) :=
      wc813pcomp_isMaxParabolicMod_inf hodd hPmax
    refine ⟨t₂, ⟨ht₂T, ht₂NJ⟩, ht₂NJ, P ⊓ J, hP'max, ?_⟩
    intro l hl
    intro heq
    have h1 : conjSubgroup J t₂⁻¹ = J := by
      have := congrArg (fun A => conjSubgroup A t₂⁻¹) hconjJ
      simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using this.symm
    have hgJ : conjSubgroup J (t₂⁻¹ * l) = J := by
      rw [← conjSubgroup_conjSubgroup, h1]
      exact conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hl)
    exact wc813pcomp_conj_inf_ne hPmax.1 hPmax.2.1.le hgJ
      (hPne l (Subgroup.mem_sup_left hl)) heq

end CFSG.LocalAnalysis.WeakClosure81

end
