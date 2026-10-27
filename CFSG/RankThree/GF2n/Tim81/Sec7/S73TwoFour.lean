module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Base
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Swap
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Setup
import CFSG.Timmesfeld.Bridge.RootStructR2ManySection
import CFSG.Timmesfeld.Bridge.SchurNarrowTransport
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim81.Sec7 (rOf oOf yOf)
open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.RootMany
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

private theorem conj_commutator_mem_V (hS : Sec7Hyp M V n f)
    (hS3 : ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ = V)
    {g x y : G} (hg : g ∈ M) (hx : x ∈ p0Of M V (A ⊔ B))
    (hy : y ∈ p0Of M V (A ⊔ B)) :
    ⁅g * x * g⁻¹, g * y * g⁻¹⁆ ∈ V := by
  have hmem : ⁅x, y⁆ ∈ V := by
    rw [← hS3]
    exact Subgroup.commutator_mem_commutator hx hy
  have hcomm : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [hcomm]
  exact (Subgroup.mem_normalizer_iff.mp
    (hS.sec5.toRootHyp.toHyp.le_normalizer hg) _).mp hmem

private theorem conj_sq_mem_V (hS : Sec7Hyp M V n f)
    (hS5 : ∀ x ∈ p0Of M V (A ⊔ B), x * x ∈ V)
    {g x : G} (hg : g ∈ M) (hx : x ∈ p0Of M V (A ⊔ B)) :
    (g * x * g⁻¹) * (g * x * g⁻¹) ∈ V := by
  have hsq : (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  rw [hsq]
  exact (Subgroup.mem_normalizer_iff.mp (hS.sec5.toRootHyp.toHyp.le_normalizer hg) _).mp
    (hS5 x hx)

private theorem commutator_Pc_conj_mem_V (hS : Sec7Hyp M V n f)
    {g p x : G} (hg : g ∈ M) (hp : p ∈ Pc M V) (hx : x ∈ p0Of M V (A ⊔ B)) :
    ⁅p, g * x * g⁻¹⁆ ∈ V := by
  have hk : g⁻¹ * p * g ∈ Pc M V := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc (M.inv_mem hg)) p).mp hp
  have hkx : ⁅g⁻¹ * p * g, x⁆ ∈ V := by
    rw [← hS.sec5.commutator_Pc_eq_V hS.ne]
    exact Subgroup.commutator_mem_commutator hk (Subgroup.mem_inf.mp hx).1
  have heq : ⁅p, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * p * g, x⁆ * g⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp (hS.sec5.toRootHyp.toHyp.le_normalizer hg) _).mp hkx

private theorem conj_commutator_mem_V_of_trivial (hS : Sec7Hyp M V n f)
    {g y x : G} (hg : g ∈ M)
    (hy : ∀ p ∈ p0Of M V (A ⊔ B), ⁅y, p⁆ ∈ V)
    (hx : x ∈ p0Of M V (A ⊔ B)) :
    ⁅g * y * g⁻¹, g * x * g⁻¹⁆ ∈ V := by
  have heq : ⁅g * y * g⁻¹, g * x * g⁻¹⁆ = g * ⁅y, x⁆ * g⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp (hS.sec5.toRootHyp.toHyp.le_normalizer hg) _).mp
    (hy x hx)

private theorem mk_mem_centralizer_of_two_four (hS : Sec7Hyp M V n f) (h71 : Sec7.Stmt71 M V)
    (h72 : Sec7.Stmt72 M V n f) (hAut4 : UnitaryFourAutCentralizer)
    (hD : L2Datum M V A B h) (h4 : n = 4) {y : G} (hyR : y ∈ rOf M h)
    (hhM : h ∈ M) (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hyP : ∀ p ∈ p0Of M V (A ⊔ B), ⁅y, p⁆ ∈ V) :
    let ybar : MBar M := QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyR.1⟩
    ybar ∈ Subgroup.centralizer ((imgQ M (A ⊔ B) : Subgroup (MBar M)) : Set (MBar M)) ∧
      ybar ∈ Subgroup.centralizer (imgQ M (r0Of M V (A ⊔ B)) : Set (MBar M)) ∧
      ybar ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩} : Set (MBar M)) ∧
      IsPGroup 2 (Subgroup.zpowers ybar) ∧
      (pPrimeCore 2 ↥(Subgroup.centralizer
        ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) :
          Set (MBar M)))).index ≤ 2 := by
  subst h4
  classical
  obtain ⟨hS1, -, -, -, -, hS6, -, -, -, -⟩ := h72 A B h hD
  have hf2 : 2 ≤ f := by
    have h4 : 4 ≤ 2 ^ f := by
      rw [← hS.card_V]
      exact hS.sec5.toRootHyp.four_le_card
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  let ybar : MBar M := QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyR.1⟩
  have hy2M : IsPGroup 2 (Subgroup.zpowers (⟨y, hyR.1⟩ : ↥M)) := by
    have hcomap : (Subgroup.zpowers y).subgroupOf M = Subgroup.zpowers (⟨y, hyR.1⟩ : ↥M) := by
      ext z
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [← hcomap]
    exact hy2.comap_of_injective M.subtype M.subtype_injective
  have hybar2 : IsPGroup 2 (Subgroup.zpowers ybar) := by
    have h := IsPGroup.map hy2M (QuotientGroup.mk' (pCore 2 ↥M))
    rwa [MonoidHom.map_zpowers] at h
  have hR0M : r0Of M V (A ⊔ B) ≤ M :=
    (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans inf_le_left
  have hybarR0 : ybar ∈ Subgroup.centralizer (imgQ M (r0Of M V (A ⊔ B)) : Set (MBar M)) := by
    refine (Sec6Hyp.mk_mem_centralizer_imgQ_iff hS.toSec6Hyp hR0M ⟨y, hyR.1⟩).mpr ?_
    intro r hr
    exact (Subgroup.mem_inf.mp (L2Datum.commutator_r0_mem_p0 hS hD hS1 hS6 hyR hyP hr)).1
  have hybarh : ybar ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩} : Set (MBar M)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyh : h * y = y * h :=
      Subgroup.mem_centralizer_iff.mp hyR.2 h (Subgroup.mem_zpowers h)
    have hcomm : (⟨y, hyR.1⟩ : ↥M) * ⟨h, hhM⟩ = ⟨h, hhM⟩ * ⟨y, hyR.1⟩ := Subtype.ext hyh.symm
    rw [← map_mul, ← map_mul, hcomm]
  have hodd := Sec6Hyp.odd_card_centralizer_imgQ_m0Of hS.toSec6Hyp h71
  have hAut4res := hAut4 (MBar M) (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f
    hS.one_le hf2 (hS.sec5.imgQ_m0Of_normal) hS.m0 hodd
    (imgQ M A) ⟨A, hD.memA, rfl⟩ (imgQ M B) ⟨B, hD.memB, rfl⟩
    (Sec6Hyp.isL2Gen_imgQ hS.toSec6Hyp hD.memA hD.memB hD.l2)
    (QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩)
    (by
      rw [← imgQ_sup hAM hBM]
      exact mk_mem_imgQ hD.mem)
    (by rw [L2Datum.orderOf_mk hS.toSec6Hyp hD hhM, hS.card_V])
  have hybarperp : ybar ∈ Subgroup.centralizer
      (perpRoots (imgQ M '' sigmaSet M V) (imgQ M A ⊔ imgQ M B) : Set (MBar M)) := by
    rw [L2Datum.perpRoots_eq hS.toSec6Hyp hD]
    exact hybarR0
  have hybarX : ybar ∈ Subgroup.centralizer
      ((imgQ M (A ⊔ B) : Subgroup (MBar M)) : Set (MBar M)) := by
    rw [imgQ_sup hAM hBM]
    exact hAut4res.1 ybar (Subgroup.mem_inf.mpr ⟨hybarperp, hybarh⟩) hybar2
  refine ⟨hybarX, hybarR0, hybarh, hybar2, ?_⟩
  have h := hAut4res.2
  rw [L2Datum.perpRoots_eq hS.toSec6Hyp hD, ← imgQ_sup hAM hBM] at h
  exact h

private structure MemP0Hyp (M V A B : Subgroup G) (h : G) (n f : ℕ) (y : G) : Prop where
  hS : Sec7Hyp M V n f
  h71 : Sec7.Stmt71 M V
  h72 : Sec7.Stmt72 M V n f
  hLP : UnitaryLinePair
  hAut4 : UnitaryFourAutCentralizer
  hD : L2Datum M V A B h
  h4 : n = 4
  hyR : y ∈ rOf M h
  hy2 : IsPGroup 2 (Subgroup.zpowers y)
  hyP : ∀ p ∈ p0Of M V (A ⊔ B), ⁅y, p⁆ ∈ V

private def OddCoreSwap (M V A B : Subgroup G) (h : G) (n f : ℕ) (y : G) : Prop :=
  ∃ (hyM : y ∈ M) (g : ↥M) (Cbar Obar : Subgroup (MBar M)) (ybar : MBar M),
    ybar = QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyM⟩ ∧
    Obar = (pPrimeCore 2 ↥Cbar).map Cbar.subtype ∧
    imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)) ∧
    imgQ M (conjSubgroup (g : G) (r0Of M V (A ⊔ B))) = imgQ M (A ⊔ B) ∧
    ybar ∈ Cbar ∧
    MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g) ybar ∈ Cbar ∧
    (pPrimeCore 2 ↥Cbar).index ≤ 2 ∧
    conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g) (imgQ M (A ⊔ B)) =
      imgQ M (r0Of M V (A ⊔ B)) ∧
    conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g) (imgQ M (r0Of M V (A ⊔ B))) =
      imgQ M (A ⊔ B) ∧
    conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g) Cbar = Cbar ∧
    Odd (Nat.card Obar) ∧
    conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g) Obar = Obar ∧
    (∀ x : MBar M, MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g) x ∈ Obar ↔ x ∈ Obar) ∧
    IsPGroup 2 (Subgroup.zpowers ybar)

private theorem conj_secHyp {y : G} (C : MemP0Hyp M V A B h n f y) {g : ↥M} :
    let W2 : Subgroup G := conjSubgroup (g : G) (p0Of M V (A ⊔ B))
    let R' : Subgroup G := M ⊓ Subgroup.normalizer (W2 : Set G)
    RootMany.SecHyp R' (Pc M V) W2 V ∧ Pc M V ≤ R' := by
  classical
  obtain ⟨-, -, hS3, -, hS5, -, -, -, -, -⟩ := C.h72 A B h C.hD
  have hP0M : p0Of M V (A ⊔ B) ≤ M :=
    inf_le_left.trans C.hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hgM : (g : G) ∈ M := g.2
  let P0 : Subgroup G := p0Of M V (A ⊔ B)
  let W2 : Subgroup G := conjSubgroup (g : G) P0
  let R' : Subgroup G := M ⊓ Subgroup.normalizer (W2 : Set G)
  have hVW2 : V ≤ W2 := by
    calc V = conjSubgroup (g : G) V :=
          (mem_normalizer_iff_conjSubgroup_eq.mp
            (C.hS.sec5.toRootHyp.toHyp.le_normalizer hgM)).symm
      _ ≤ conjSubgroup (g : G) P0 := conjSubgroup_mono (L2Datum.V_le_p0 C.hS.toSec6Hyp C.hD)
      _ = W2 := rfl
  have hW2M : W2 ≤ M := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    exact M.mul_mem (M.mul_mem hgM (hP0M hp)) (M.inv_mem hgM)
  have hW2R' : W2 ≤ R' := le_inf hW2M Subgroup.le_normalizer
  have hPR' : Pc M V ≤ R' := by
    refine le_inf C.hS.sec5.toRootHyp.toHyp.Pc_le_M ?_
    rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro p hp e he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
    exact hVW2 (commutator_Pc_conj_mem_V C.hS hgM hp hx)
  have hSec : RootMany.SecHyp R' (Pc M V) W2 V :=
    { le := hVW2
      le_R := hW2R'
      conj_E := fun r hr e he =>
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hr).2 e).mp he
      conj_A := fun r hr x hx =>
        (Subgroup.mem_normalizer_iff.mp
          (C.hS.sec5.toRootHyp.toHyp.le_normalizer (Subgroup.mem_inf.mp hr).1) x).mp hx
      comm := fun x hx y hy => by
        obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
        change ⁅(g : G) * x0 * (g : G)⁻¹, (g : G) * y0 * (g : G)⁻¹⁆ ∈ V
        exact conj_commutator_mem_V C.hS hS3 hgM hx0 hy0
      sq := fun x hx => by
        obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
        change ((g : G) * x0 * (g : G)⁻¹) * ((g : G) * x0 * (g : G)⁻¹) ∈ V
        exact conj_sq_mem_V C.hS hS5 hgM hx0
      ker := fun k hk e he => by
        obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp he
        change ⁅k, (g : G) * x0 * (g : G)⁻¹⁆ ∈ V
        exact commutator_Pc_conj_mem_V C.hS hgM hk hx0 }
  exact ⟨hSec, hPR'⟩

private theorem conj_normalizes {y : G} (C : MemP0Hyp M V A B h n f y) {g : ↥M} :
    let P0 : Subgroup G := p0Of M V (A ⊔ B)
    let W2 : Subgroup G := conjSubgroup (g : G) P0
    ((g : G) * y * (g : G)⁻¹) ∈ Subgroup.normalizer (W2 : Set G) := by
  obtain ⟨hS1, -, -, -, -, -⟩ := C.h72 A B h C.hD
  let P0 : Subgroup G := p0Of M V (A ⊔ B)
  let W2 : Subgroup G := conjSubgroup (g : G) P0
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hyN : conjSubgroup y P0 = P0 :=
    mem_normalizer_iff_conjSubgroup_eq.mp
      (L2Datum.rOf_le_normalizer_p0 C.hS.toSec6Hyp C.hD hS1 C.hyR)
  calc conjSubgroup ((g : G) * y * (g : G)⁻¹) W2
      = conjSubgroup (((g : G) * y * (g : G)⁻¹) * (g : G)) P0 := by
        rw [show W2 = conjSubgroup (g : G) P0 from rfl, conjSubgroup_conjSubgroup]
    _ = conjSubgroup ((g : G) * y) P0 := by
        congr 1
        group
    _ = conjSubgroup (g : G) (conjSubgroup y P0) := by rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup (g : G) P0 := by rw [hyN]
    _ = W2 := rfl

private theorem secRep_conj_eq_one {y : G} (C : MemP0Hyp M V A B h n f y)
    {g : ↥M} (hg1 : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)))
    {m : ℕ} (hm_odd : Odd m)
    (hpowP : (y * ((g : G) * y * (g : G)⁻¹)) ^ m ∈ Pc M V) :
    ∀ e ∈ conjSubgroup (g : G) (p0Of M V (A ⊔ B)), ⁅y, e⁆ ∈ V := by
  classical
  have hgM : (g : G) ∈ M := g.2
  have hyM : y ∈ M := C.hyR.1
  let P0 : Subgroup G := p0Of M V (A ⊔ B)
  let W2 : Subgroup G := conjSubgroup (g : G) P0
  let R' : Subgroup G := M ⊓ Subgroup.normalizer (W2 : Set G)
  let yg : G := (g : G) * y * (g : G)⁻¹
  obtain ⟨hS1, -, -, -, -, -⟩ := C.h72 A B h C.hD
  obtain ⟨hSec, hPR'⟩ := conj_secHyp C
  let E : Subgroup ↥R' := W2.subgroupOf R'
  let Asub : Subgroup ↥R' := V.subgroupOf R'
  letI : E.Normal := hSec.normal_E
  letI : Asub.Normal := hSec.normal_A
  letI : Fact (RootMany.IsElemSection E Asub) := ⟨hSec.isElemSection⟩
  let T := RootMany.secRep E Asub
  have hyR' : y ∈ R' :=
    Subgroup.mem_inf.mpr ⟨hyM, L2Datum.rOf_le_normalizer_conj_p0 C.hS C.h72 C.hD g hg1 C.hyR⟩
  have hygM : yg ∈ M := M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM)
  have hygN : yg ∈ Subgroup.normalizer (W2 : Set G) := conj_normalizes C
  have hygR' : yg ∈ R' := Subgroup.mem_inf.mpr ⟨hygM, hygN⟩
  have hTyg : T ⟨yg, hygR'⟩ = 1 := by
    rw [RootMany.secRep_eq_one_iff]
    intro e he
    have heW2 : (e : G) ∈ W2 := Subgroup.mem_subgroupOf.mp he
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp heW2
    rw [Subgroup.mem_subgroupOf]
    change yg * (e : G) * yg⁻¹ * (e : G)⁻¹ ∈ V
    have hxe' : (e : G) = (g : G) * x * (g : G)⁻¹ := by
      simpa [MulAut.conj_apply] using hxe.symm
    rw [hxe']
    have h := conj_commutator_mem_V_of_trivial C.hS hgM C.hyP hx
    simpa [commutatorElement_def, yg] using h
  have hTP : ∀ (p : G) (hp : p ∈ Pc M V), T ⟨p, hPR' hp⟩ = 1 := by
    intro p hp
    rw [RootMany.secRep_eq_one_iff]
    intro e he
    have heW2 : (e : G) ∈ W2 := Subgroup.mem_subgroupOf.mp he
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp heW2
    rw [Subgroup.mem_subgroupOf]
    change p * (e : G) * p⁻¹ * (e : G)⁻¹ ∈ V
    have hxe' : (e : G) = (g : G) * x * (g : G)⁻¹ := by
      simpa [MulAut.conj_apply] using hxe.symm
    rw [hxe']
    have h := commutator_Pc_conj_mem_V C.hS hgM hp hx
    simpa [commutatorElement_def] using h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)
    (G := Subgroup.zpowers y)).mp C.hy2 ⟨y, Subgroup.mem_zpowers y⟩
  have hyk : y ^ 2 ^ k = 1 := by
    rw [← hk, Subgroup.orderOf_mk y (Subgroup.mem_zpowers y)]
    exact pow_orderOf_eq_one y
  have hT2 : T ⟨y, hyR'⟩ ^ 2 ^ k = 1 := by
    calc T ⟨y, hyR'⟩ ^ 2 ^ k = T (⟨y, hyR'⟩ ^ 2 ^ k) := (map_pow T _ _).symm
      _ = T 1 := by rw [show (⟨y, hyR'⟩ : ↥R') ^ 2 ^ k = 1 from Subtype.ext hyk]
      _ = 1 := map_one T
  have hR'yyg : y * yg ∈ R' := R'.mul_mem hyR' hygR'
  have hTm : T ⟨y, hyR'⟩ ^ m = 1 := by
    have hTyyg : T ⟨y * yg, hR'yyg⟩ = T ⟨y, hyR'⟩ := by
      rw [show (⟨y * yg, hR'yyg⟩ : ↥R') = ⟨y, hyR'⟩ * ⟨yg, hygR'⟩ from rfl, map_mul,
        hTyg, mul_one]
    calc T ⟨y, hyR'⟩ ^ m = T ⟨y * yg, hR'yyg⟩ ^ m := by rw [hTyyg]
      _ = T (⟨y * yg, hR'yyg⟩ ^ m) := (map_pow T _ _).symm
      _ = T ⟨(y * yg) ^ m, hPR' hpowP⟩ := by congr 1
      _ = 1 := hTP _ hpowP
  have hcop : Nat.Coprime (2 ^ k) m :=
    (Nat.coprime_two_left.mpr hm_odd).pow_left k
  have hTy : T ⟨y, hyR'⟩ = 1 :=
    (pow_eq_one_iff_of_coprime (a := T ⟨y, hyR'⟩) hcop).mp ⟨hT2, hTm⟩
  intro e he
  have hmemE : (⟨e, hSec.le_R he⟩ : ↥R') ∈ E := Subgroup.mem_subgroupOf.mpr he
  have h := (RootMany.secRep_eq_one_iff E Asub ⟨y, hyR'⟩).mp hTy ⟨e, hSec.le_R he⟩ hmemE
  simpa [commutatorElement_def] using Subgroup.mem_subgroupOf.mp h

namespace L2Datum

private theorem oddCoreSwap_of_memP0Hyp {y : G} (C : MemP0Hyp M V A B h n f y) :
    OddCoreSwap M V A B h n f y := by
  have h4 := C.h4
  subst h4
  classical
  obtain ⟨hS1, -, hS3, -, hS5, -, -, -, -, -⟩ := C.h72 A B h C.hD
  have hf2 : 2 ≤ f := by
    have h4 : 4 ≤ 2 ^ f := by
      rw [← C.hS.card_V]
      exact C.hS.sec5.toRootHyp.four_le_card
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)
  have hAM : A ≤ M := (C.hS.sec5.le_M_of_mem_sigmaSet C.hD.memA).1
  have hBM : B ≤ M := (C.hS.sec5.le_M_of_mem_sigmaSet C.hD.memB).1
  have hXM : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  have hyM : y ∈ M := C.hyR.1
  have hhM : h ∈ M := hXM C.hD.mem
  let P0 : Subgroup G := p0Of M V (A ⊔ B)
  let R0 : Subgroup G := r0Of M V (A ⊔ B)
  let ybar : MBar M := QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyM⟩
  let Cbar : Subgroup (MBar M) :=
    Subgroup.centralizer ((imgQ M (A ⊔ B) ⊔ imgQ M R0 : Subgroup (MBar M)) : Set (MBar M))
  obtain ⟨hybarX, hybarR0, hybarh, hybar2, hindex0⟩ :=
    mk_mem_centralizer_of_two_four C.hS C.h71 C.h72 C.hAut4 C.hD rfl C.hyR hhM C.hy2 C.hyP
  have hindex : (pPrimeCore 2 ↥Cbar).index ≤ 2 := by simpa [Cbar, R0] using hindex0
  obtain ⟨g, hg1, hg2, -⟩ := L2Datum.exists_swap C.hS C.hLP C.hD rfl
  let gbar : MBar M := QuotientGroup.mk' (pCore 2 ↥M) g
  have hgM : (g : G) ∈ M := g.2
  have hgX : conjSubgroup gbar (imgQ M (A ⊔ B)) = imgQ M R0 := by
    rw [← imgQ_conjSubgroup g (A ⊔ B), hg1]
  have hgR0 : conjSubgroup gbar (imgQ M R0) = imgQ M (A ⊔ B) := by
    rw [← imgQ_conjSubgroup g R0, hg2]
  have hybarC : ybar ∈ Cbar := by
    change ybar ∈ Subgroup.centralizer
      ((imgQ M (A ⊔ B) ⊔ imgQ M R0 : Subgroup (MBar M)) : Set (MBar M))
    rw [CFSG.centralizer_sup_eq]
    exact Subgroup.mem_inf.mpr ⟨hybarX, hybarR0⟩
  have hybarCg : MulAut.conj gbar ybar ∈ Cbar := by
    change MulAut.conj gbar ybar ∈ Subgroup.centralizer
      ((imgQ M (A ⊔ B) ⊔ imgQ M R0 : Subgroup (MBar M)) : Set (MBar M))
    rw [CFSG.centralizer_sup_eq]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h : MulAut.conj gbar ybar ∈ conjSubgroup gbar
          (Subgroup.centralizer (imgQ M R0 : Set (MBar M))) :=
        Subgroup.mem_map_of_mem (MulAut.conj gbar).toMonoidHom hybarR0
      rw [← CFSG.CGT.Timmesfeld75.centralizer_conjSubgroup_eq, hgR0] at h
      exact h
    · have h : MulAut.conj gbar ybar ∈ conjSubgroup gbar
          (Subgroup.centralizer (imgQ M (A ⊔ B) : Set (MBar M))) :=
        Subgroup.mem_map_of_mem (MulAut.conj gbar).toMonoidHom hybarX
      rw [← CFSG.CGT.Timmesfeld75.centralizer_conjSubgroup_eq, hgX] at h
      exact h
  have hgCbar : conjSubgroup gbar Cbar = Cbar := by
    change conjSubgroup gbar (Subgroup.centralizer
      ((imgQ M (A ⊔ B) ⊔ imgQ M R0 : Subgroup (MBar M)) : Set (MBar M))) =
      Subgroup.centralizer
        ((imgQ M (A ⊔ B) ⊔ imgQ M R0 : Subgroup (MBar M)) : Set (MBar M))
    rw [← CFSG.CGT.Timmesfeld75.centralizer_conjSubgroup_eq, conjSubgroup_sup,
      hgX, hgR0, sup_comm]
  let Obar : Subgroup (MBar M) := (pPrimeCore 2 ↥Cbar).map Cbar.subtype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddCore : Odd (Nat.card ↥(pPrimeCore 2 ↥Cbar)) :=
    (pPrimeCore_coprime_card (p := 2) (G := ↥Cbar)).odd_of_left
  have hoddObar : Odd (Nat.card Obar) := by
    change Odd (Nat.card ((pPrimeCore 2 ↥Cbar).map Cbar.subtype))
    rw [Subgroup.card_map_of_injective Cbar.subtype_injective]
    exact hoddCore
  have hgN : gbar ∈ Subgroup.normalizer (Obar : Set (MBar M)) :=
    CFSG.normalizer_le_normalizer_image_of_characteristic Cbar (pPrimeCore 2 ↥Cbar)
      (mem_normalizer_iff_conjSubgroup_eq.mpr hgCbar)
  have hgObar : conjSubgroup gbar Obar = Obar := mem_normalizer_iff_conjSubgroup_eq.mp hgN
  have hmemObar_iff : ∀ x : MBar M, MulAut.conj gbar x ∈ Obar ↔ x ∈ Obar := fun x =>
    (Subgroup.mem_normalizer_iff.mp hgN x).symm
  exact ⟨hyM, g, Cbar, Obar, ybar, rfl, rfl, hg1, hg2, hybarC, hybarCg, hindex, hgX, hgR0, hgCbar,
    hoddObar, hgObar, hmemObar_iff, hybar2⟩

private theorem mem_p0Of_of_oddCoreSwap {y : G} (C : MemP0Hyp M V A B h n f y)
    (D : OddCoreSwap M V A B h n f y) : y ∈ p0Of M V (A ⊔ B) := by
  have h4 := C.h4
  subst h4
  classical
  obtain ⟨hS1, -, -, -, -, -, -, -, -, -⟩ := C.h72 A B h C.hD
  obtain ⟨hyM, g, Cbar, Obar, ybar, hybar_eq, hObar_eq, hg1, hg2, hybarC,
    hybarCg, hindex, hgX, hgR0, hgCbar, hoddObar, hgObar, hmemObar_iff, hybar2⟩ := D
  subst hybar_eq
  subst hObar_eq
  let ybar : MBar M := QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyM⟩
  let Obar : Subgroup (MBar M) := (pPrimeCore 2 ↥Cbar).map Cbar.subtype
  let P0 : Subgroup G := p0Of M V (A ⊔ B)
  let gbar : MBar M := QuotientGroup.mk' (pCore 2 ↥M) g
  let yg : G := (g : G) * y * (g : G)⁻¹
  have hgM : (g : G) ∈ M := g.2
  have hygM : yg ∈ M := M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM)
  let z : ↥Cbar := ⟨ybar, hybarC⟩
  let zg : ↥Cbar := ⟨MulAut.conj gbar ybar, hybarCg⟩
  by_cases hyO : ybar ∈ Obar
  · have hybar1 : ybar = 1 :=
      CFSG.Timmesfeld.Bridge.eq_one_of_mem_odd_of_mem_two hoddObar hybar2 hyO
        (Subgroup.mem_zpowers ybar)
    have hyPc : y ∈ Pc M V := (Sec6Hyp.mk_eq_one_iff C.hS.toSec6Hyp ⟨y, hyM⟩).mp hybar1
    rw [← hS1]
    exact Subgroup.mem_inf.mpr ⟨hyPc, C.hyR.2⟩
  · have hzO : z ∉ pPrimeCore 2 ↥Cbar := fun hz =>
      hyO (Subgroup.mem_map_of_mem Cbar.subtype hz)
    have hzgO : zg ∉ pPrimeCore 2 ↥Cbar := by
      intro hzg
      exact hyO ((hmemObar_iff ybar).mp (Subgroup.mem_map_of_mem Cbar.subtype hzg))
    have hindex2 : (pPrimeCore 2 ↥Cbar).index = 2 := by
      have hne0 : (pPrimeCore 2 ↥Cbar).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hne1 : (pPrimeCore 2 ↥Cbar).index ≠ 1 := fun h1 =>
        hzO (Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top z)
      omega
    have hmulO : z * zg ∈ pPrimeCore 2 ↥Cbar := by
      rw [Subgroup.mul_mem_iff_of_index_two hindex2]
      exact iff_of_false hzO hzgO
    have hwObar : ybar * MulAut.conj gbar ybar ∈ Obar :=
      Subgroup.mem_map_of_mem Cbar.subtype hmulO
    let w : MBar M := ybar * MulAut.conj gbar ybar
    let m : ℕ := orderOf w
    have hm_odd : Odd m := by
      exact Odd.of_dvd_nat hoddObar (Subgroup.orderOf_dvd_natCard Obar hwObar)
    have hw_eq : w = QuotientGroup.mk' (pCore 2 ↥M)
        ⟨y * yg, M.mul_mem hyM hygM⟩ := by
      simp only [w, ybar, gbar, yg]
      change QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyM⟩ *
          (QuotientGroup.mk' (pCore 2 ↥M) g * QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyM⟩ *
            (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹) =
        QuotientGroup.mk' (pCore 2 ↥M) ⟨y * ((g : G) * y * (g : G)⁻¹), _⟩
      simp only [← map_mul, ← map_inv]
      rfl
    have hpowP : (y * yg) ^ m ∈ Pc M V := by
      have h1 : QuotientGroup.mk' (pCore 2 ↥M)
          ((⟨y * yg, M.mul_mem hyM hygM⟩ : ↥M) ^ m) = 1 := by
        rw [map_pow, ← hw_eq]
        exact pow_orderOf_eq_one w
      simpa using (Sec6Hyp.mk_eq_one_iff C.hS.toSec6Hyp _).mp h1
    have hP0M : p0Of M V (A ⊔ B) ≤ M :=
      inf_le_left.trans C.hS.sec5.toRootHyp.toHyp.Pc_le_M
    have hW2M : conjSubgroup (g : G) P0 ≤ M := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      exact M.mul_mem (M.mul_mem hgM (hP0M hp)) (M.inv_mem hgM)
    have hyW2 : ∀ e ∈ conjSubgroup (g : G) P0, ⁅y, e⁆ ∈ V :=
      secRep_conj_eq_one ⟨C.hS, C.h71, C.h72, C.hLP, C.hAut4, C.hD, rfl, C.hyR, C.hy2,
        C.hyP⟩ hg1 hm_odd hpowP
    have hcommP : ∀ p ∈ Pc M V, ⁅y, p⁆ ∈ V := by
      intro p hp
      rw [L2Datum.Pc_eq_p0_sup_conj C.hS C.h72 C.hD g hg1] at hp
      exact Sec6Hyp.commutator_mem_of_mem_sup C.hS.toSec6Hyp hP0M hW2M C.hyP hyW2 p hp
    have hyPc : y ∈ Pc M V := Sec6Hyp.mem_Pc_of_commutator_mem C.hS.toSec6Hyp hyM hcommP
    rw [← hS1]
    exact Subgroup.mem_inf.mpr ⟨hyPc, C.hyR.2⟩

theorem mem_p0_of_two_four (hS : Sec7Hyp M V n f) (h71 : Sec7.Stmt71 M V)
    (h72 : Sec7.Stmt72 M V n f) (hLP : UnitaryLinePair)
    (hAut4 : UnitaryFourAutCentralizer) (hD : L2Datum M V A B h) (h4 : n = 4)
    {y : G} (hyR : y ∈ rOf M h) (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hyP : ∀ p ∈ p0Of M V (A ⊔ B), ⁅y, p⁆ ∈ V) : y ∈ p0Of M V (A ⊔ B) := by
  subst h4
  exact mem_p0Of_of_oddCoreSwap ⟨hS, h71, h72, hLP, hAut4, hD, rfl, hyR, hy2, hyP⟩
    (oddCoreSwap_of_memP0Hyp ⟨hS, h71, h72, hLP, hAut4, hD, rfl, hyR, hy2, hyP⟩)

end L2Datum

end CFSG.RankThree.GF2n.Tim81

end
