module

import CFSG.StronglyEmbedded.BenderRootModel
import CFSG.Timmesfeld.Bridge.RootSetsConn16
import CFSG.Timmesfeld.Bridge.OddRootOrbit
public import CFSG.Timmesfeld.Bridge.OddRootSzMainLineQ
public import CFSG.Timmesfeld.Bridge.OddRootSzMainTwoTransSylow

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

private def szSLineMap (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) :
    ↥(szS E P) →* Equiv.Perm ↥(szLine D d e) :=
  (szLineHom D d e).comp
    (Subgroup.inclusion ((szS_le_szN E P).trans (c.szN_le_szLineStab P hP)))

private def szSMap (E : Set G) (P : Sylow 2 (SzBar E)) : ↥(szS E P) →* SzBar E :=
  (szMk E).comp (Subgroup.inclusion ((szS_le_szN E P).trans (szN_le_closure E P)))

private def szLineK (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) : Subgroup ↥(szS E P) :=
  (Subgroup.centralizer
    (szLineT D d e E : Set (Equiv.Perm ↥(szLine D d e)))).comap (szSLineMap c P hP)

private def szLineN (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) : Subgroup (SzBar E) :=
  (szLineK c P hP).map (szSMap E P)

private theorem szSMap_mem (P : Sylow 2 (SzBar E)) (s : ↥(szS E P)) :
    szSMap E P s ∈ (P : Subgroup (SzBar E)) := by
  obtain ⟨hH, hP⟩ := mem_szS_iff.mp s.2
  change szMk E ⟨s.1, (szS_le_szN E P).trans (szN_le_closure E P) s.2⟩ ∈
    (P : Subgroup (SzBar E))
  convert hP using 2

private theorem szSMap_surj (P : Sylow 2 (SzBar E)) {p : SzBar E}
    (hp : p ∈ (P : Subgroup (SzBar E))) :
    ∃ s : ↥(szS E P), szSMap E P s = p := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 (Subgroup.closure E)) p
  have hyP : szMk E y ∈ (P : Subgroup (SzBar E)) := by
    change QuotientGroup.mk' (CFSG.pCore 2 (Subgroup.closure E)) y ∈
      (P : Subgroup (SzBar E))
    rw [hy]
    exact hp
  have hyS : (y : G) ∈ szS E P := mem_szS_iff.mpr ⟨y.2, hyP⟩
  refine ⟨⟨y.1, hyS⟩, ?_⟩
  change szMk E ⟨y.1, (szS_le_szN E P).trans (szN_le_closure E P) hyS⟩ = p
  rw [show (⟨y.1, (szS_le_szN E P).trans (szN_le_closure E P) hyS⟩ :
    ↥(Subgroup.closure E)) = y from Subtype.ext rfl]
  exact hy

private theorem mem_szQ_of_szSMap_eq_one (P : Sylow 2 (SzBar E)) {s : ↥(szS E P)}
    (h : szSMap E P s = 1) : (s : G) ∈ szQ E :=
  (szMk_eq_one_iff_mem_szQ ((szS_le_szN E P).trans (szN_le_closure E P) s.2)).mp h

private theorem szLineHom_eq_one_of_mem_szComp (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P) {b : G} (hb : b ∈ szComp E e)
    (hbl : b ∈ szLineStab D d e) :
    szLineHom D d e ⟨b, hbl⟩ = 1 := by
  apply Equiv.ext
  intro X
  rw [Equiv.Perm.one_apply]
  obtain ⟨x, hx, rfl⟩ := exists_szLinePt X
  rw [szLineHom_szLinePt]
  have hbE : b ∈ E := hb.1
  have hbS : b ∈ szS E P := (c.mem_szS_iff_commute P c.e_mem hbE hP).mpr hb.2
  have hcomm : Commute b x := by
    rw [c.szLineSet_eq] at hx
    rcases hx with hxroot | hxcomp
    · exact (c.commute_of_mem_rootSet_d hxroot (Subgroup.subset_closure hbE)).symm
    · have hxS : x ∈ szS E P :=
        (c.mem_szS_iff_commute P c.e_mem hxcomp.1 hP).mpr hxcomp.2
      exact c.hyp.setup.oddT.commute_of_isPGroup (isPGroup_szS E P)
        (c.subset_commSet hbE).1 (c.subset_commSet hxcomp.1).1 hbS hxS
  have hconj : b * x * b⁻¹ = x := by
    rw [hcomm.eq]
    group
  apply Subtype.ext
  change rootSet D (b * x * b⁻¹) = rootSet D x
  rw [hconj]

private theorem szLineT_conj_eq_self_of_card_le_two (c : SzCfg G D d E e n)
    {x t : Equiv.Perm ↥(szLine D d e)} (hx : x ∈ (szLineHom D d e).range)
    (hxα : x (szLinePt D d e d c.d_mem_szLineSet) =
      szLinePt D d e d c.d_mem_szLineSet)
    (ht : t ∈ szLineT D d e E) (hcard : Nat.card (szLineT D d e E) ≤ 2) :
    x * t * x⁻¹ = t := by
  by_cases ht1 : t = 1
  · rw [ht1, mul_one, mul_inv_cancel]
  · have ht2 : t * t = 1 := by
      have := c.szLineT_isElemAbelian.2 t ht
      simpa [pow_two] using this
    have hzle : Subgroup.zpowers t ≤ szLineT D d e E := Subgroup.zpowers_le.mpr ht
    have hzcard : Nat.card (Subgroup.zpowers t) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by simpa [pow_two] using ht2) ht1
    have hcard' : Nat.card (szLineT D d e E) ≤ Nat.card (Subgroup.zpowers t) := by
      rw [hzcard]
      exact hcard
    have hT0eq : Subgroup.zpowers t = szLineT D d e E :=
      Subgroup.eq_of_le_of_card_ge hzle hcard'
    have hu : x * t * x⁻¹ ∈ Subgroup.zpowers t := by
      rw [hT0eq]
      exact c.szLineT_normal x hx hxα t ht
    rcases CFSG.Timmesfeld.Bridge.eq_one_or_eq_of_mem_zpowers ht2 hu with h1 | h1
    · exfalso
      have ht1' : t = 1 := by
        have := congrArg (fun z => x⁻¹ * z * x) h1
        simpa [mul_assoc] using this
      exact ht1 ht1'
    · exact h1

private theorem mem_szLineK_of_mem_szQ (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) {s : ↥(szS E P)} (hs : (s : G) ∈ szQ E) :
    s ∈ szLineK c P hP := by
  refine Subgroup.mem_comap.mpr ?_
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hψ : szSLineMap c P hP s ∈ szLineT D d e E :=
    Subgroup.mem_map.mpr
      ⟨⟨(s : G), (szS_le_szN E P).trans (c.szN_le_szLineStab P hP) s.2⟩, hs, rfl⟩
  have hcomm := c.szLineT_isElemAbelian.1.is_comm.comm
    ⟨szSLineMap c P hP s, hψ⟩ ⟨t, ht⟩
  exact (congrArg Subtype.val hcomm).symm

private theorem sylowCenter_le_szLineN (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) :
    sylowCenter (P : Subgroup (SzBar E)) ≤ szLineN c P hP := by
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]
    exact (szLineN c P hP).one_mem
  · obtain ⟨b, hbcomp, hbH, hbimg⟩ :=
      c.exists_comp_of_mem_sylowCenter P c.e_mem hP hz hz1
    have hbE : b ∈ E := hbcomp.1
    have hbS : b ∈ szS E P :=
      (c.mem_szS_iff_commute P c.e_mem hbE hP).mpr hbcomp.2
    refine Subgroup.mem_map.mpr ⟨⟨b, hbS⟩, ?_, ?_⟩
    · refine Subgroup.mem_comap.mpr ?_
      change szLineHom D d e
        ⟨b, (szS_le_szN E P).trans (c.szN_le_szLineStab P hP) hbS⟩ ∈
        Subgroup.centralizer _
      rw [szLineHom_eq_one_of_mem_szComp c P hP hbcomp
        ((szS_le_szN E P).trans (c.szN_le_szLineStab P hP) hbS)]
      exact (Subgroup.centralizer _).one_mem
    · change szMk E ⟨b, (szS_le_szN E P).trans (szN_le_closure E P) hbS⟩ = z
      rw [show (⟨b, (szS_le_szN E P).trans (szN_le_closure E P) hbS⟩ :
        ↥(Subgroup.closure E)) = ⟨b, hbH⟩ from Subtype.ext rfl]
      exact hbimg

private theorem conj_szSLineMap_mem_centralizer (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P) {k : ↥(szS E P)}
    (hk : k ∈ szLineK c P hP) {h : G} (hhN : h ∈ szN E P) :
    szSLineMap c P hP ⟨h * (k : G) * h⁻¹, conj_mem_szS hhN k.2⟩ ∈
      Subgroup.centralizer (szLineT D d e E : Set (Equiv.Perm ↥(szLine D d e))) := by
  have hslN : szN E P ≤ szLineStab D d e := c.szN_le_szLineStab P hP
  have hSH : szS E P ≤ szN E P := szS_le_szN E P
  have hconjS : h * (k : G) * h⁻¹ ∈ szS E P := conj_mem_szS hhN k.2
  have hdecomp : szSLineMap c P hP ⟨h * (k : G) * h⁻¹, hconjS⟩ =
      szLineHom D d e ⟨h, hslN hhN⟩ * szSLineMap c P hP k *
        (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ := by
    have h1 : (⟨h, hslN hhN⟩ : ↥(szLineStab D d e)) *
        ⟨(k : G), (hSH.trans hslN) k.2⟩ * (⟨h, hslN hhN⟩ : ↥(szLineStab D d e))⁻¹ =
        ⟨h * (k : G) * h⁻¹, (hSH.trans hslN) hconjS⟩ := by
      apply Subtype.ext
      rfl
    change szLineHom D d e ⟨h * (k : G) * h⁻¹, (hSH.trans hslN) hconjS⟩ =
      szLineHom D d e ⟨h, hslN hhN⟩ *
        szLineHom D d e ⟨(k : G), (hSH.trans hslN) k.2⟩ *
        (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹
    rw [← h1, map_mul, map_mul, map_inv]
  have hfix : szLineHom D d e ⟨h, hslN hhN⟩
      (szLinePt D d e d c.d_mem_szLineSet) = szLinePt D d e d c.d_mem_szLineSet :=
    c.szLineHom_fix_of_mem_closure (szN_le_closure E P hhN)
  have hx : szLineHom D d e ⟨h, hslN hhN⟩ ∈ (szLineHom D d e).range := ⟨_, rfl⟩
  have hxinv : (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ ∈ (szLineHom D d e).range :=
    (szLineHom D d e).range.inv_mem hx
  have hfixinv : (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹
      (szLinePt D d e d c.d_mem_szLineSet) = szLinePt D d e d c.d_mem_szLineSet := by
    have := congrArg (⇑(szLineHom D d e ⟨h, hslN hhN⟩)⁻¹) hfix
    simpa using this.symm
  have hT : ∀ s ∈ szLineT D d e E,
      szLineHom D d e ⟨h, hslN hhN⟩ * s * (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ ∈
        szLineT D d e E := c.szLineT_normal _ hx hfix
  have hTinv : ∀ s ∈ szLineT D d e E,
      (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ * s * szLineHom D d e ⟨h, hslN hhN⟩ ∈
        szLineT D d e E := c.szLineT_normal _ hxinv hfixinv
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [hdecomp]
  have hu : (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ * t *
      szLineHom D d e ⟨h, hslN hhN⟩ ∈ szLineT D d e E := hTinv t ht
  have hkc : szSLineMap c P hP k *
      ((szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ * t * szLineHom D d e ⟨h, hslN hhN⟩) =
      ((szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ * t * szLineHom D d e ⟨h, hslN hhN⟩) *
        szSLineMap c P hP k :=
    (Subgroup.mem_centralizer_iff.mp hk _ hu).symm
  calc t * (szLineHom D d e ⟨h, hslN hhN⟩ * szSLineMap c P hP k *
        (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹)
      = szLineHom D d e ⟨h, hslN hhN⟩ *
          (((szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ * t *
            szLineHom D d e ⟨h, hslN hhN⟩) * szSLineMap c P hP k) *
          (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ := by group
    _ = szLineHom D d e ⟨h, hslN hhN⟩ *
          (szSLineMap c P hP k *
            ((szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ * t *
              szLineHom D d e ⟨h, hslN hhN⟩)) *
          (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹ := by rw [hkc]
    _ = (szLineHom D d e ⟨h, hslN hhN⟩ * szSLineMap c P hP k *
          (szLineHom D d e ⟨h, hslN hhN⟩)⁻¹) * t := by group

private theorem conj_mem_szLineN (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) {b w : SzBar E}
    (hb : b ∈ Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E)))
    (hw : w ∈ szLineN c P hP) : b * w * b⁻¹ ∈ szLineN c P hP := by
  obtain ⟨k, hk, hkw⟩ := Subgroup.mem_map.mp hw
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 (Subgroup.closure E)) b
  have hSH : szS E P ≤ Subgroup.closure E :=
    (szS_le_szN E P).trans (szN_le_closure E P)
  have hyN : (y : G) ∈ szN E P := by
    rw [mem_szN_iff]
    refine ⟨y.2, ?_⟩
    change QuotientGroup.mk' (CFSG.pCore 2 (Subgroup.closure E)) y ∈
      Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))
    rw [hy]
    exact hb
  have hconjS : (y : G) * (k : G) * (y : G)⁻¹ ∈ szS E P := conj_mem_szS hyN k.2
  refine Subgroup.mem_map.mpr
    ⟨⟨(y : G) * (k : G) * (y : G)⁻¹, hconjS⟩, ?_, ?_⟩
  · exact Subgroup.mem_comap.mpr
      (conj_szSLineMap_mem_centralizer c P hP hk hyN)
  · have hyb : szMk E y = b := hy
    have hkw' : szMk E ⟨(k : G), hSH k.2⟩ = w := hkw
    change szMk E ⟨(y : G) * (k : G) * (y : G)⁻¹, hSH hconjS⟩ = b * w * b⁻¹
    calc szMk E ⟨(y : G) * (k : G) * (y : G)⁻¹, hSH hconjS⟩
        = szMk E y * szMk E ⟨(k : G), hSH k.2⟩ * (szMk E y)⁻¹ := by
          rw [show (⟨(y : G) * (k : G) * (y : G)⁻¹, hSH hconjS⟩ :
            ↥(Subgroup.closure E)) =
            y * ⟨(k : G), hSH k.2⟩ * y⁻¹ from Subtype.ext rfl]
          rw [map_mul, map_mul, map_inv]
      _ = b * w * b⁻¹ := by rw [hyb, hkw']

theorem SzCfg.twoTransHyp (c : SzCfg G D d E e n) (h4 : 4 ≤ Nat.card (szLineT D d e E)) :
    TwoTransHyp (szLineHom D d e).range (szLineT D d e E)
      (szLinePt D d e d c.d_mem_szLineSet) where
  two_trans β γ β' γ' h h' := by
    obtain ⟨r, hr, hr'⟩ := c.szLineHom_two_trans h h'
    exact ⟨szLineHom D d e r, ⟨r, rfl⟩, hr, hr'⟩
  le := Subgroup.map_le_range (szLineHom D d e)
    ((szQ E).subgroupOf (szLineStab D d e))
  fix := c.szLineT_fix
  normal := c.szLineT_normal
  elemAb := c.szLineT_isElemAbelian
  four_le := h4
  semireg := c.szLineT_semireg

private theorem card_szLineT_add_one (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) (h4 : 4 ≤ Nat.card (szLineT D d e E)) :
    Nat.card (szLineT D d e E) + 1 = Nat.card ↥(szLine D d e) := by
  let h := c.twoTransHyp h4
  obtain ⟨j, hj⟩ := h.exists_card_eq
  letI : Fintype ↥(szN E P) := Fintype.ofFinite _
  refine card_add_one_of_semireg (N := ↥(szN E P))
    ((szLineHom D d e).comp (Subgroup.inclusion (c.szN_le_szLineStab P hP)))
    c.szLineT_semireg c.szLineT_fix hj ?_ ?_
    (P := (szS E P).subgroupOf (szN E P)) ?_ (not_two_dvd_index_szS E P) ?_
  · intro x
    exact c.szLineHom_fix_of_mem_closure (szN_le_closure E P x.2)
  · intro β γ hβ hγ
    exact c.szN_trans P hP hβ hγ
  · exact (isPGroup_szS E P).of_equiv
      (Subgroup.subgroupOfEquivOfLe (szS_le_szN E P)).symm
  · intro p hpP β hβ
    have hsS : ((p : ↥(szN E P)) : G) ∈ szS E P := Subgroup.mem_subgroupOf.mp hpP
    obtain ⟨y, hyQ, hyeq⟩ := c.szLineS_orbit P hP hsS β
    refine ⟨szLineHom D d e ⟨y, c.szQ_le_szLineStab hyQ⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨y, c.szQ_le_szLineStab hyQ⟩, hyQ, rfl⟩
    · have hfirst : szLineHom D d e
          ⟨((p : ↥(szN E P)) : G), c.szN_le_szLineStab P hP
            (p : ↥(szN E P)).2⟩ =
          szLineHom D d e ⟨((p : ↥(szN E P)) : G),
            c.szN_le_szLineStab P hP (szS_le_szN E P hsS)⟩ := by
        congr 1
      change szLineHom D d e
        ⟨((p : ↥(szN E P)) : G), c.szN_le_szLineStab P hP
          (p : ↥(szN E P)).2⟩ β = _
      rw [hfirst]
      exact hyeq

private theorem exists_szSMap_generator (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) (h4 : 4 ≤ Nat.card (szLineT D d e E))
    (hreg : Nat.card (szLineT D d e E) + 1 = Nat.card ↥(szLine D d e)) :
    ∃ x : ↥(szS E P), ∀ p : (P : Subgroup (SzBar E)),
      ∃ k : ℕ, (p : SzBar E)⁻¹ * (szSMap E P x) ^ k ∈ szLineN c P hP := by
  let h := c.twoTransHyp h4
  let ρS : Subgroup (Equiv.Perm ↥(szLine D d e)) := szLineS D d e E P
  have hsl : szS E P ≤ szLineStab D d e :=
    (szS_le_szN E P).trans (c.szN_le_szLineStab P hP)
  have hP2 : IsPGroup 2 ρS := by
    change IsPGroup 2
      (((szS E P).subgroupOf (szLineStab D d e)).map (szLineHom D d e))
    exact ((isPGroup_szS E P).of_equiv
      (Subgroup.subgroupOfEquivOfLe hsl).symm).map (szLineHom D d e)
  have hPX : ρS ≤ (szLineHom D d e).range := Subgroup.map_le_range _ _
  have hPα : ∀ p ∈ ρS, p (szLinePt D d e d c.d_mem_szLineSet) =
      szLinePt D d e d c.d_mem_szLineSet := c.szLineS_fix P
  obtain ⟨x, hxρS, hxgen⟩ := h.exists_mod_centralizer hreg hPX hPα hP2
  obtain ⟨r, hrS, hrx⟩ := Subgroup.mem_map.mp hxρS
  let sx : ↥(szS E P) := ⟨((r : ↥(szLineStab D d e)) : G), hrS⟩
  have hsx : szSLineMap c P hP sx = x := by
    change szLineHom D d e
      ⟨((r : ↥(szLineStab D d e)) : G), hsl hrS⟩ = x
    convert hrx using 1
  refine ⟨sx, ?_⟩
  intro p
  obtain ⟨sp, hsp⟩ := szSMap_surj P p.2
  have hspρ : szSLineMap c P hP sp ∈ ρS := by
    refine Subgroup.mem_map.mpr ⟨⟨(sp : G), hsl sp.2⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr sp.2
  obtain ⟨k, hk⟩ := hxgen (szSLineMap c P hP sp) hspρ
  refine ⟨k, ?_⟩
  have hmemK : sp⁻¹ * sx ^ k ∈ szLineK c P hP := by
    refine Subgroup.mem_comap.mpr ?_
    change szSLineMap c P hP (sp⁻¹ * sx ^ k) ∈
      Subgroup.centralizer (szLineT D d e E : Set (Equiv.Perm ↥(szLine D d e)))
    rw [map_mul, map_inv, map_pow, hsx]
    exact hk
  have himg : szSMap E P (sp⁻¹ * sx ^ k) =
      (p : SzBar E)⁻¹ * (szSMap E P sx) ^ k := by
    rw [map_mul, map_inv, map_pow, hsp]
  have hmem : szSMap E P (sp⁻¹ * sx ^ k) ∈ szLineN c P hP :=
    Subgroup.mem_map.mpr ⟨sp⁻¹ * sx ^ k, hmemK, rfl⟩
  rwa [himg] at hmem

private theorem commute_of_szLineN_eq_sylowCenter (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P)
    (h4 : 4 ≤ Nat.card (szLineT D d e E))
    (hreg : Nat.card (szLineT D d e E) + 1 = Nat.card ↥(szLine D d e))
    (hW : szLineN c P hP = sylowCenter (P : Subgroup (SzBar E))) :
    ∀ p q : (P : Subgroup (SzBar E)), p * q = q * p := by
  obtain ⟨x, hxgen⟩ := exists_szSMap_generator c P hP h4 hreg
  let xP : (P : Subgroup (SzBar E)) := ⟨szSMap E P x, szSMap_mem P x⟩
  have hgen : ∀ p : (P : Subgroup (SzBar E)), ∃ k : ℕ,
      (p : SzBar E)⁻¹ * (xP : SzBar E) ^ k ∈
        sylowCenter (P : Subgroup (SzBar E)) := by
    intro p
    obtain ⟨k, hk⟩ := hxgen p
    exact ⟨k, hW ▸ hk⟩
  intro p q
  obtain ⟨k, hpk⟩ := hgen p
  obtain ⟨l, hql⟩ := hgen q
  let wp : SzBar E := (p : SzBar E)⁻¹ * (xP : SzBar E) ^ k
  let wq : SzBar E := (q : SzBar E)⁻¹ * (xP : SzBar E) ^ l
  have hwpZ : wp ∈ sylowCenter (P : Subgroup (SzBar E)) := hpk
  have hwqZ : wq ∈ sylowCenter (P : Subgroup (SzBar E)) := hql
  have hwp_cent : ∀ y ∈ (P : Subgroup (SzBar E)), Commute y wp :=
    fun y hy => (mem_sylowCenter.mp hwpZ).2 y hy
  have hwq_cent : ∀ y ∈ (P : Subgroup (SzBar E)), Commute y wq :=
    fun y hy => (mem_sylowCenter.mp hwqZ).2 y hy
  have hp_eq : (p : SzBar E) = (xP : SzBar E) ^ k * wp⁻¹ := by
    dsimp [wp]
    group
  have hq_eq : (q : SzBar E) = (xP : SzBar E) ^ l * wq⁻¹ := by
    dsimp [wq]
    group
  apply Subtype.ext
  change (p : SzBar E) * (q : SzBar E) = (q : SzBar E) * (p : SzBar E)
  rw [hp_eq, hq_eq]
  have hxP_mem : (xP : SzBar E) ∈ (P : Subgroup (SzBar E)) := xP.2
  have h1 : Commute ((xP : SzBar E) ^ k) ((xP : SzBar E) ^ l) :=
    Commute.pow_pow_self (xP : SzBar E) k l
  have h2 : Commute (wp⁻¹) ((xP : SzBar E) ^ l) :=
    ((hwp_cent ((xP : SzBar E) ^ l) (Subgroup.pow_mem _ hxP_mem l)).symm).inv_left
  have h3 : Commute ((xP : SzBar E) ^ k) (wq⁻¹) :=
    (hwq_cent ((xP : SzBar E) ^ k) (Subgroup.pow_mem _ hxP_mem k)).inv_right
  have h4 : Commute (wp⁻¹) (wq⁻¹) := by
    have h : Commute wp wq :=
      (hwp_cent wq (mem_sylowCenter.mp hwqZ).1).symm
    exact h.inv_left.inv_right
  exact ((h1.mul_right h3).mul_left (h2.mul_right h4)).eq

private theorem false_of_szLineN_eq_sylowCenter (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P)
    (h4 : 4 ≤ Nat.card (szLineT D d e E))
    (hreg : Nat.card (szLineT D d e E) + 1 = Nat.card ↥(szLine D d e))
    (hW : szLineN c P hP = sylowCenter (P : Subgroup (SzBar E))) : False := by
  have hcomm := commute_of_szLineN_eq_sylowCenter c P hP h4 hreg hW
  obtain ⟨s1, hs1, s2, hs2, hnc⟩ := c.exists_not_commute_szS P
  let p1 : (P : Subgroup (SzBar E)) := ⟨szSMap E P ⟨s1, hs1⟩, szSMap_mem P ⟨s1, hs1⟩⟩
  let p2 : (P : Subgroup (SzBar E)) := ⟨szSMap E P ⟨s2, hs2⟩, szSMap_mem P ⟨s2, hs2⟩⟩
  have hval : szSMap E P ⟨s1, hs1⟩ * szSMap E P ⟨s2, hs2⟩ =
      szSMap E P ⟨s2, hs2⟩ * szSMap E P ⟨s1, hs1⟩ :=
    congrArg Subtype.val (hcomm p1 p2)
  have hmem : s1 * s2 * s1⁻¹ * s2⁻¹ ∈ szS E P :=
    (szS E P).mul_mem
      ((szS E P).mul_mem ((szS E P).mul_mem hs1 hs2) ((szS E P).inv_mem hs1))
      ((szS E P).inv_mem hs2)
  have hmap1 : szSMap E P ⟨s1 * s2 * s1⁻¹ * s2⁻¹, hmem⟩ =
      szSMap E P ⟨s1, hs1⟩ * szSMap E P ⟨s2, hs2⟩ *
        (szSMap E P ⟨s1, hs1⟩)⁻¹ * (szSMap E P ⟨s2, hs2⟩)⁻¹ := by
    rw [show (⟨s1 * s2 * s1⁻¹ * s2⁻¹, hmem⟩ : ↥(szS E P)) =
      ⟨s1, hs1⟩ * ⟨s2, hs2⟩ * ⟨s1, hs1⟩⁻¹ * ⟨s2, hs2⟩⁻¹ from Subtype.ext rfl]
    simp only [map_mul, map_inv]
  have hmap : szSMap E P ⟨s1 * s2 * s1⁻¹ * s2⁻¹, hmem⟩ = 1 := by
    rw [hmap1, hval]
    group
  exact hnc (mem_szQ_of_szSMap_eq_one P hmap)

private theorem mem_szLineK_of_szLineN_eq (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) (hW : szLineN c P hP = (P : Subgroup (SzBar E))) :
    ∀ s : ↥(szS E P), s ∈ szLineK c P hP := by
  intro s
  have hφ : szSMap E P s ∈ szLineN c P hP := by
    rw [hW]
    exact szSMap_mem P s
  obtain ⟨k, hk, hφk⟩ := Subgroup.mem_map.mp hφ
  have hφ1 : szSMap E P (k⁻¹ * s) = szSMap E P k⁻¹ * szSMap E P s :=
    map_mul (szSMap E P) k⁻¹ s
  have hzero : szSMap E P (k⁻¹ * s) = 1 := by
    rw [hφ1, map_inv (szSMap E P) k, hφk]
    group
  have hqK : k⁻¹ * s ∈ szLineK c P hP :=
    mem_szLineK_of_mem_szQ c P hP (mem_szQ_of_szSMap_eq_one P hzero)
  have hs : s = k * (k⁻¹ * s) := by group
  rw [hs]
  exact (szLineK c P hP).mul_mem hk hqK

private theorem szSLineMap_mem_centralizer (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) (hP : e ∈ szS E P) :
    ∀ s : ↥(szS E P), szSLineMap c P hP s ∈
      Subgroup.centralizer
        (szLineT D d e E : Set (Equiv.Perm ↥(szLine D d e))) := by
  have hsl : szS E P ≤ szLineStab D d e :=
    (szS_le_szN E P).trans (c.szN_le_szLineStab P hP)
  intro s
  by_cases hsmall : Nat.card (szLineT D d e E) ≤ 2
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hxrange : szSLineMap c P hP s ∈ (szLineHom D d e).range := ⟨_, rfl⟩
    have hxS : szSLineMap c P hP s ∈ szLineS D d e E P :=
      Subgroup.mem_map.mpr
        ⟨⟨(s : G), hsl s.2⟩, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
    have hxα := c.szLineS_fix P _ hxS
    have hconj := szLineT_conj_eq_self_of_card_le_two c hxrange hxα ht hsmall
    calc t * szSLineMap c P hP s
        = (szSLineMap c P hP s * t * (szSLineMap c P hP s)⁻¹) *
            szSLineMap c P hP s := by rw [hconj]
      _ = szSLineMap c P hP s * t := by group
  · have h4 : 4 ≤ Nat.card (szLineT D d e E) := by
      have hpg : IsPGroup 2 (szLineT D d e E) :=
        CFSG.Open.IsElemAbelian.isPGroup c.szLineT_isElemAbelian
      rcases hpg.card_eq_or_dvd with h1 | hdvd
      · rw [h1] at hsmall
        norm_num at hsmall
      · obtain ⟨m, hm⟩ := hdvd
        have hm2 : 2 ≤ m := by
          rcases m with _ | _ | m
          · rw [hm] at hsmall
            norm_num at hsmall
          · rw [hm] at hsmall
            norm_num at hsmall
          · omega
        rw [hm]
        nlinarith
    have hreg := card_szLineT_add_one c P hP h4
    have hNP : szLineN c P hP ≤ (P : Subgroup (SzBar E)) := by
      intro w hw
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hw
      exact szSMap_mem P k
    rcases CFSG.StronglyEmbedded.BenderCentre.eq_sylowCenter_or_eq_of_normalized
      c.isBenderGroup P (sylowCenter_le_szLineN c P hP) hNP
      (fun b hb w hw => conj_mem_szLineN c P hP hb hw) with hW | hW
    · exact (false_of_szLineN_eq_sylowCenter c P hP h4 hreg hW).elim
    · exact Subgroup.mem_comap.mp (mem_szLineK_of_szLineN_eq c P hP hW s)

theorem SzCfg.commute_commutator_szS (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    (hP : e ∈ szS E P) {s y : G} (hs : s ∈ szS E P) (hy : y ∈ szQ E) :
    Commute (s * y * s⁻¹ * y⁻¹) e := by
  have hsH : s ∈ Subgroup.closure E := szN_le_closure E P (szS_le_szN E P hs)
  have himage : (fun x => s * x * s⁻¹) '' E = E :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp
      (closure_le_normalizer_of_isMaxOrbit c.hyp.setup c.maxOrbit hsH)
  have hyS : y ∈ szS E P := szQ_le_szS E P hy
  have hq : s * y * s⁻¹ * y⁻¹ ∈ szQ E :=
    (szQ E).mul_mem (conj_mem_szQ himage hy) ((szQ E).inv_mem hy)
  have hmemS : s * y * s⁻¹ * y⁻¹ ∈ szS E P :=
    (szS E P).mul_mem
      ((szS E P).mul_mem ((szS E P).mul_mem hs hyS) ((szS E P).inv_mem hs))
      ((szS E P).inv_mem hyS)
  have hsl : szS E P ≤ szLineStab D d e :=
    (szS_le_szN E P).trans (c.szN_le_szLineStab P hP)
  have hψy : szSLineMap c P hP ⟨y, hyS⟩ ∈ szLineT D d e E := by
    change szLineHom D d e ⟨y, hsl hyS⟩ ∈ szLineT D d e E
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hsl hyS⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hψs := szSLineMap_mem_centralizer c P hP ⟨s, hs⟩
  have hcomm : szSLineMap c P hP ⟨s, hs⟩ * szSLineMap c P hP ⟨y, hyS⟩ =
      szSLineMap c P hP ⟨y, hyS⟩ * szSLineMap c P hP ⟨s, hs⟩ :=
    (Subgroup.mem_centralizer_iff.mp hψs _ hψy).symm
  have hψ : szSLineMap c P hP ⟨s * y * s⁻¹ * y⁻¹, hmemS⟩ = 1 := by
    rw [show (⟨s * y * s⁻¹ * y⁻¹, hmemS⟩ : ↥(szS E P)) =
      ⟨s, hs⟩ * ⟨y, hyS⟩ * ⟨s, hs⟩⁻¹ * ⟨y, hyS⟩⁻¹ from Subtype.ext rfl]
    simp only [map_mul, map_inv, hcomm]
    group
  have hρ : szLineHom D d e ⟨s * y * s⁻¹ * y⁻¹, c.szQ_le_szLineStab hq⟩ = 1 := by
    have hsame : szSLineMap c P hP ⟨s * y * s⁻¹ * y⁻¹, hmemS⟩ =
        szLineHom D d e ⟨s * y * s⁻¹ * y⁻¹, c.szQ_le_szLineStab hq⟩ := by
      change szLineHom D d e ⟨s * y * s⁻¹ * y⁻¹, hsl hmemS⟩ =
        szLineHom D d e ⟨s * y * s⁻¹ * y⁻¹, c.szQ_le_szLineStab hq⟩
      congr 1
    rw [← hsame]
    exact hψ
  exact (c.szLineHom_eq_one_iff hq).mp hρ

end CFSG.Timmesfeld.Bridge.OddRoot
