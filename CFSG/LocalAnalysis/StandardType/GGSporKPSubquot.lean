module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportCore
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Assembly.OpenBridges

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4

private theorem gkq_pPrimeCore_subgroupOf_top {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {Y : Subgroup H} (hY : Y.IsSubnormal) :
    (CFSG.pPrimeCore p H).subgroupOf Y = CFSG.pPrimeCore p ↥Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkey := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ p} hY
  rw [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore] at hkey
  have hmap := congrArg (fun S : Subgroup H => S.subgroupOf Y) hkey
  have h1 : (Subgroup.map Y.subtype (CFSG.pPrimeCore p ↥Y)).subgroupOf Y =
      CFSG.pPrimeCore p ↥Y :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have h2 : (Y ⊓ CFSG.pPrimeCore p H).subgroupOf Y = (CFSG.pPrimeCore p H).subgroupOf Y :=
    Subgroup.inf_subgroupOf_left (CFSG.pPrimeCore p H) Y
  rw [h1, h2] at hmap
  exact hmap.symm

private noncomputable def gkq_mapMkEquivQuotientSubgroupOf {G : Type} [Group G] (p : ℕ)
    (Y : Subgroup G) :
    ↥(Y.map (QuotientGroup.mk' (CFSG.pPrimeCore p G))) ≃*
      ↥Y ⧸ (CFSG.pPrimeCore p G).subgroupOf Y := by
  let f : G →* G ⧸ CFSG.pPrimeCore p G := QuotientGroup.mk' (CFSG.pPrimeCore p G)
  let g : ↥Y →* G ⧸ CFSG.pPrimeCore p G := f.domRestrict Y
  have hker : g.ker = (CFSG.pPrimeCore p G).subgroupOf Y := by
    show (f.comp Y.subtype).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : g.range = Y.map f := MonoidHom.domRestrict_range Y f
  exact (MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange g).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))

private noncomputable def gkq_quotientPPrimeCoreCongr {A B : Type} [Group A] [Group B]
    (p : ℕ) (e : A ≃* B) :
    A ⧸ CFSG.pPrimeCore p A ≃* B ⧸ CFSG.pPrimeCore p B :=
  QuotientGroup.congr (CFSG.pPrimeCore p A) (CFSG.pPrimeCore p B) e
    (CFSG.pPrimeCore_map_iso p e)

private noncomputable def gkq_quotientCenterCongr {A B : Type} [Group A] [Group B]
    (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)

theorem bmPSubquot_equiv_pQuot {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) {x : Q}
    {C : Subgroup Q} (h : LargeEvenPComponent p (Subgroup.centralizer {x}) C) :
    Nonempty (BMPSubquot p x C ≃* PQuot p C) := by
  unfold LargeEvenPComponent at h
  obtain ⟨hCX, hsub, -, -⟩ := h
  let X : Subgroup Q := Subgroup.centralizer ({x} : Set Q)
  let Y : Subgroup X := C.subgroupOf X
  have hcoreY : (CFSG.pPrimeCore p ↥X).subgroupOf Y = CFSG.pPrimeCore p ↥Y :=
    gkq_pPrimeCore_subgroupOf_top hp hsub.subgroupOf
  let e : Y ≃* C := Subgroup.subgroupOfEquivOfLe hCX
  refine ⟨(gkq_mapMkEquivQuotientSubgroupOf p Y).trans ?_⟩
  exact (QuotientGroup.quotientMulEquivOfEq hcoreY).trans (gkq_quotientPPrimeCoreCongr p e)

theorem bmPSubquot_centerQuot_equiv_pSimple {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {x : Q} {C : Subgroup Q}
    (h : LargeEvenPComponent p (Subgroup.centralizer {x}) C) :
    Nonempty (BMPSubquot p x C ⧸ Subgroup.center (BMPSubquot p x C) ≃* PSimple p C) := by
  obtain ⟨φ⟩ := bmPSubquot_equiv_pQuot hp h
  exact ⟨gkq_quotientCenterCongr φ⟩

end CFSG.StandardType.SporadicShape
