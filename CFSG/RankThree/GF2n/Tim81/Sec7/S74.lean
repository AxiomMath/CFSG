module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
import CFSG.GroupTheory.PerfectImageRange
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

theorem Sec5Hyp.y0Of_le_iSup_sigmaAt (hS : Sec5Hyp M V) {A B : Subgroup G}
    (hA : A ∈ sigmaSet M V) (hB : B ∈ sigmaSet M V) :
    y0Of V (A ⊔ B) ≤ ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C := by
  refine iSup₂_le fun x hx => ?_
  have hxA : conjSubgroup x V ∈ sigmaAt A :=
    hS.conj_mem_sigmaAt (sigmaSet_subset_omegaSet M V hA)
      (Subgroup.centralizer_le_normalizer (A : Set G)
        (Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_left hy) hx))
      (hS.self_mem_sigmaAt hA)
  have hxB : conjSubgroup x V ∈ sigmaAt B :=
    hS.conj_mem_sigmaAt (sigmaSet_subset_omegaSet M V hB)
      (Subgroup.centralizer_le_normalizer (B : Set G)
        (Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_right hy) hx))
      (hS.self_mem_sigmaAt hB)
  exact le_iSup₂_of_le (conjSubgroup x V) ⟨hxA, hxB⟩ le_rfl

theorem Sec5Hyp.iSup_sigmaAt_le (hS : Sec5Hyp M V) {A B : Subgroup G} {g : G}
    (hAg : A = conjSubgroup g V) (hA : A ∈ sigmaSet M V) (hB : B ∈ sigmaSet M V) :
    (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ≤ cenOf (A ⊔ B) ⊓ conjSubgroup g (m0Of M V) := by
  have hAω : A ∈ omegaSet V := sigmaSet_subset_omegaSet M V hA
  have hBω : B ∈ omegaSet V := sigmaSet_subset_omegaSet M V hB
  have hconj := Hyp.sigmaAt_conj hS.toRootHyp.toHyp g
  refine iSup₂_le fun C hC => le_inf ?_ ?_
  · intro x hx
    exact le_of_eq (centralizer_sup_eq A B).symm
      ⟨(hS.le_of_mem_sigmaAt hAω hC.1).2 hx, (hS.le_of_mem_sigmaAt hBω hC.2).2 hx⟩
  · have hC' : C ∈ sigmaSet (conjSubgroup g M) (conjSubgroup g V) := by
      have h := hC.1
      rw [hAg, hconj] at h
      exact h
    have h := le_m0Of_of_mem_sigmaSet hC'
    rwa [m0Of_conjSubgroup g] at h

theorem Sec7.Stmt73.y0Of_eq (h73 : Sec7.Stmt73 M V n f) {A B : Subgroup G} {h : G}
    (hX : L2Datum M V A B h) : y0Of V (A ⊔ B) = y0Of V (Subgroup.zpowers h) := by
  obtain ⟨hYc, hYconj, -⟩ := h73 A B h hX
  refine le_antisymm (y0Of_anti V (Subgroup.zpowers_le.mpr hX.mem)) ?_
  refine iSup₂_le fun y hy => ?_
  obtain ⟨x, hx, hxy⟩ := hYconj y hy
  rw [hxy]
  exact le_iSup₂_of_le x (hYc hx) le_rfl

theorem Sec5Hyp.y0Of_inf_conj_Pc_eq_bot (hS : Sec5Hyp M V) (h73 : Sec7.Stmt73 M V n f)
    {A B : Subgroup G} {g h : G} (hAg : A = conjSubgroup g V) (hX : L2Datum M V A B h) :
    y0Of V (Subgroup.zpowers h) ⊓ conjSubgroup g (Pc M V) = ⊥ := by
  have hYc : y0Of V (Subgroup.zpowers h) ≤ cenOf A := by
    intro y hy
    have h1 : y ∈ cenOf (A ⊔ B) := (h73 A B h hX).1 hy
    rw [Subgroup.mem_centralizer_iff] at h1 ⊢
    intro a ha
    exact h1 a (Subgroup.mem_sup_left ha)
  have hYN : y0Of V (Subgroup.zpowers h) ≤
      Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) := by
    intro y hy
    exact hS.mem_normalizer_conj_Pc g (hAg ▸ hYc hy)
  have hnormal : ((conjSubgroup g (Pc M V)).subgroupOf
      (y0Of V (Subgroup.zpowers h))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYN
  have h2 : IsPGroup 2 ((conjSubgroup g (Pc M V)).subgroupOf
      (y0Of V (Subgroup.zpowers h))) :=
    (isPGroup_conj_Pc M V g).comap_subtype
  have hbot : ((conjSubgroup g (Pc M V)).subgroupOf
      (y0Of V (Subgroup.zpowers h))) = ⊥ := by
    have hle : ((conjSubgroup g (Pc M V)).subgroupOf (y0Of V (Subgroup.zpowers h))) ≤
        pCore 2 ↥(y0Of V (Subgroup.zpowers h)) := le_sSup ⟨hnormal, h2⟩
    rw [(h73 A B h hX).2.2.1] at hle
    exact le_bot_iff.mp hle
  rw [eq_bot_iff]
  intro y hy
  have h1 : (⟨y, hy.1⟩ : ↥(y0Of V (Subgroup.zpowers h))) ∈
      (conjSubgroup g (Pc M V)).subgroupOf (y0Of V (Subgroup.zpowers h)) := hy.2
  rw [hbot] at h1
  exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp h1))

theorem Sec6Hyp.Pc_le_m0Of (hS : Sec6Hyp M V) (h71 : Sec7.Stmt71 M V) : Pc M V ≤ m0Of M V := by
  obtain ⟨U, hU⟩ := hS.ne
  have h1 : ⁅Pc M V, U⁆ ≤ ⁅Pc M V, m0Of M V⁆ :=
    Subgroup.commutator_mono (le_refl (Pc M V)) (le_m0Of_of_mem_sigmaSet hU)
  have h2 : ⁅Pc M V, m0Of M V⁆ ≤ m0Of M V :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := Pc M V) (K := m0Of M V)).mp
      (hS.sec5.toRootHyp.toHyp.Pc_le_M.trans hS.sec5.toRootHyp.toHyp.le_normalizer_m0Of)
  have hV : V ≤ Pc M V ⊓ m0Of M V :=
    le_inf hS.sec5.toRootHyp.toHyp.le_Pc
      ((hS.sec5.V_le_commutator hU).trans (h1.trans h2))
  have hN : m0Of M V ≤ Subgroup.normalizer (Pc M V ⊓ m0Of M V : Subgroup G) := by
    intro x hx
    have hxM : x ∈ M := hS.sec5.m0Of_le_M hx
    exact mem_normalizer_inf (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc hxM)
      (hS.sec5.toRootHyp.toHyp.le_normalizer_m0Of hxM)
  rcases h71 (Pc M V ⊓ m0Of M V) hV inf_le_left hN with hEq | hEq
  · exfalso
    have hle : ⁅Pc M V, U⁆ ≤ V := by
      have h := le_inf (hS.sec5.commutator_le_Pc hU) (h1.trans h2)
      rw [hEq] at h
      exact h
    have hce : ⁅Pc M V, U⁆ = V := le_antisymm hle (hS.sec5.V_le_commutator hU)
    have hcard : Nat.card V ^ 3 = Nat.card V := by
      rw [← hS.sec5.card_commutator_Pc hU, hce]
    have hq2 : Nat.card V ^ 2 = 1 := by
      have hmul : Nat.card V * Nat.card V ^ 2 = Nat.card V * 1 := by
        rw [mul_one, ← pow_succ']
        exact hcard
      exact Nat.mul_left_cancel Nat.card_pos hmul
    have h16 : 16 ≤ Nat.card V ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ Nat.card V ^ 2 := Nat.pow_le_pow_left hS.sec5.toRootHyp.four_le_card 2
    omega
  · exact inf_eq_left.mp hEq

theorem Sec7Hyp.conj_m0Of_le_sup (hS : Sec7Hyp M V n f) (h73 : Sec7.Stmt73 M V n f)
    {A B : Subgroup G} {g h : G} (hAg : A = conjSubgroup g V) (hX : L2Datum M V A B h)
    (hYm : y0Of V (Subgroup.zpowers h) ≤ conjSubgroup g (m0Of M V)) :
    conjSubgroup g (m0Of M V) ≤ y0Of V (Subgroup.zpowers h) ⊔ conjSubgroup g (Pc M V) := by
  obtain ⟨Φ, hΦker, hΦrange, -⟩ := hS.m0
  obtain ⟨-, -, -, -, Ψ, hΨsurj, hΨker⟩ := h73 A B h hX
  have hYM : y0Of V (Subgroup.zpowers h) ≤ conjSubgroup g M :=
    hYm.trans (conjSubgroup_mono hS.toSec6Hyp.sec5.m0Of_le_M)
  have hf : ∀ y : ↥(y0Of V (Subgroup.zpowers h)), (MulAut.conj g⁻¹) (y : G) ∈ M := by
    intro y
    have hy : (y : G) ∈ conjSubgroup g M := hYM y.2
    simpa using (mem_conjSubgroup.mp hy)
  let e : ↥(y0Of V (Subgroup.zpowers h)) →* ↥M :=
    ((MulAut.conj g⁻¹).toMonoidHom.comp (y0Of V (Subgroup.zpowers h)).subtype).codRestrict M hf
  let ι : ↥(y0Of V (Subgroup.zpowers h)) →* MBar M :=
    (QuotientGroup.mk' (pCore 2 ↥M)).comp e
  have he : ∀ y : ↥(y0Of V (Subgroup.zpowers h)), ((e y : ↥M) : G) = g⁻¹ * (y : G) * g := by
    intro y
    show (MulAut.conj g⁻¹) (y : G) = _
    rw [MulAut.conj_apply, inv_inv]
  have hinj : Function.Injective ι := by
    have hker : ∀ y : ↥(y0Of V (Subgroup.zpowers h)), ι y = 1 → y = 1 := by
      intro y hy
      have hp : g⁻¹ * (y : G) * g ∈ Pc M V := by
        have h := (Sec6Hyp.mk_eq_one_iff hS.toSec6Hyp (e y)).mp hy
        rwa [he y] at h
      have hmemP : (y : G) ∈ conjSubgroup g (Pc M V) := mem_conjSubgroup.mpr hp
      have hmem : (y : G) ∈ y0Of V (Subgroup.zpowers h) ⊓ conjSubgroup g (Pc M V) :=
        ⟨y.2, hmemP⟩
      rw [Sec5Hyp.y0Of_inf_conj_Pc_eq_bot hS.toSec6Hyp.sec5 h73 hAg hX] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    intro x y hxy
    have h1 : ι (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : x * y⁻¹ = 1 := hker _ h1
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h2]
      _ = y := one_mul y
  have hrange : ι.range ≤ imgQ M (conjSubgroup g⁻¹ (y0Of V (Subgroup.zpowers h))) := by
    rintro z ⟨y, rfl⟩
    refine mk_mem_imgQ (x := e y) ?_
    have hval : g * ((e y : ↥M) : G) * g⁻¹ = (y : G) := by
      rw [he y]
      group
    rw [mem_conjSubgroup, inv_inv, hval]
    exact y.2
  have hmono : conjSubgroup g⁻¹ (y0Of V (Subgroup.zpowers h)) ≤ m0Of M V :=
    calc conjSubgroup g⁻¹ (y0Of V (Subgroup.zpowers h))
        ≤ conjSubgroup g⁻¹ (conjSubgroup g (m0Of M V)) := conjSubgroup_mono hYm
      _ = m0Of M V := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hιΦ : ι.range ≤ Φ.range := by
    rw [hΦrange]
    exact hrange.trans (imgQ_mono hmono)
  have h4 : 4 ≤ n := hS.four_le
  have hnq : (n, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h1 : n = 3 := congrArg Prod.fst h
    omega
  have hperf : commutator
      ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) = ⊤ :=
    (Unitary.isQuasisimple_SU (p := 2) (f := f) (n := n) (F := GaloisField 2 (2 * f))
      (card_galoisField_two_mul hS.one_le) (by omega) hnq).1.commutator_eq_top
  have hmain : Φ.range ≤ ι.range :=
    CFSG.GroupTheory.range_le_of_perfect_of_quotient hperf Φ hΦker
      (pPrimeCore 2 ↥(y0Of V (Subgroup.zpowers h))) Ψ hΨsurj hΨker ι hinj hιΦ
  have himg : imgQ M (m0Of M V) ≤ imgQ M (conjSubgroup g⁻¹ (y0Of V (Subgroup.zpowers h))) := by
    rw [← hΦrange]
    exact hmain.trans hrange
  have hsup : m0Of M V ≤ conjSubgroup g⁻¹ (y0Of V (Subgroup.zpowers h)) ⊔ Pc M V :=
    hS.toSec6Hyp.le_sup_Pc_of_imgQ_le hS.toSec6Hyp.sec5.m0Of_le_M himg
  calc conjSubgroup g (m0Of M V)
      ≤ conjSubgroup g (conjSubgroup g⁻¹ (y0Of V (Subgroup.zpowers h)) ⊔ Pc M V) :=
        conjSubgroup_mono hsup
    _ = conjSubgroup g (conjSubgroup g⁻¹ (y0Of V (Subgroup.zpowers h))) ⊔
          conjSubgroup g (Pc M V) := by rw [conjSubgroup_sup]
    _ = y0Of V (Subgroup.zpowers h) ⊔ conjSubgroup g (Pc M V) := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

private theorem Sec6Hyp.commutator_inf_y0Of_eq_bot (hS : Sec6Hyp M V)
    {A B : Subgroup G} {g : G} (hAg : A = conjSubgroup g V)
    (hYc : y0Of V (A ⊔ B) ≤ cenOf (A ⊔ B))
    (hYP : y0Of V (A ⊔ B) ⊓ conjSubgroup g (Pc M V) = ⊥)
    (hTc : (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ≤ cenOf (A ⊔ B)) :
    ⁅(⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ⊓ conjSubgroup g (Pc M V), y0Of V (A ⊔ B)⁆ = ⊥ := by
  set T : Subgroup G := ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C with hT
  set D : Subgroup G := T ⊓ conjSubgroup g (Pc M V) with hD
  have hYN : y0Of V (A ⊔ B) ≤ Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) := by
    intro y hy
    have h2 : y ∈ cenOf (A ⊔ B) := hYc hy
    rw [Subgroup.mem_centralizer_iff] at h2
    refine hS.sec5.mem_normalizer_conj_Pc g ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hAg] at ha
    exact h2 a (Subgroup.mem_sup_left ha)
  have hTY : T ≤ Subgroup.normalizer (y0Of V (A ⊔ B) : Set G) :=
    hTc.trans (cenOf_le_normalizer_y0Of V (A ⊔ B))
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro d hd y hy
  have hdT : d ∈ T := hd.1
  have hdP : d ∈ conjSubgroup g (Pc M V) := hd.2
  have h1 : ⁅d, y⁆ ∈ y0Of V (A ⊔ B) :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := T) (K := y0Of V (A ⊔ B))).mp
      hTY (Subgroup.commutator_mem_commutator hdT hy)
  have h2 : ⁅d, y⁆ ∈ conjSubgroup g (Pc M V) :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := y0Of V (A ⊔ B))
      (K := conjSubgroup g (Pc M V))).mp hYN
      (Subgroup.commutator_mem_commutator (H₁ := conjSubgroup g (Pc M V))
        (H₂ := y0Of V (A ⊔ B)) hdP hy)
  have h3 : ⁅d, y⁆ ∈ y0Of V (A ⊔ B) ⊓ conjSubgroup g (Pc M V) := ⟨h1, h2⟩
  rw [hYP] at h3
  exact Subgroup.mem_bot.mpr h3

private theorem Sec6Hyp.conj_Pc_le_normalizer_inf_sup (hS : Sec6Hyp M V)
    {A B : Subgroup G} {g : G} (hAg : A = conjSubgroup g V) (hA : A ∈ sigmaSet M V)
    (hTcA : (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ≤ cenOf A) :
    conjSubgroup g (Pc M V) ≤ Subgroup.normalizer
      ((⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ⊓ conjSubgroup g (Pc M V) ⊔ A : Subgroup G) := by
  set T : Subgroup G := ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C with hT
  set D : Subgroup G := T ⊓ conjSubgroup g (Pc M V) with hD
  have hDA : D ≤ Subgroup.normalizer (A : Set G) :=
    (inf_le_left.trans hTcA).trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hAC : A ≤ cenOf (conjSubgroup g (Pc M V)) :=
    (Subgroup.le_centralizer_iff).mp (hAg.symm ▸ conjSubgroup_Pc_le_centralizer M V g)
  have hNPg : ⁅D ⊔ A, conjSubgroup g (Pc M V)⁆ ≤ D ⊔ A := by
    rw [Subgroup.commutator_le]
    intro x hx p hp
    have hx' : x ∈ (D : Set G) * (A : Set G) := by
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right D A hDA]
    obtain ⟨d, hd, a, ha, rfl⟩ := Set.mem_mul.mp hx'
    have hap : a * p * a⁻¹ = p := by
      have h1 : p * a = a * p := Subgroup.mem_centralizer_iff.mp (hAC ha) p hp
      rw [← h1]
      group
    have hcomm : ⁅d * a, p⁆ = ⁅d, p⁆ := by
      rw [commutatorElement_def, commutatorElement_def,
        show d * a * p * (d * a)⁻¹ * p⁻¹ = d * (a * p * a⁻¹) * (d⁻¹ * p⁻¹) by group, hap]
      group
    rw [hcomm]
    have hmem : ⁅d, p⁆ ∈ A := by
      have hle : ⁅d, p⁆ ∈ ⁅conjSubgroup g (Pc M V), conjSubgroup g (Pc M V)⁆ :=
        Subgroup.commutator_mem_commutator (show d ∈ conjSubgroup g (Pc M V) from hd.2) hp
      rw [hS.sec5.commutator_conj_Pc (hAg ▸ hA)] at hle
      exact hAg.symm ▸ hle
    exact Subgroup.mem_sup_right hmem
  exact (Subgroup.le_normalizer_iff_commutator_le_left
    (H := conjSubgroup g (Pc M V)) (K := D ⊔ A)).mpr hNPg

theorem Sec6Hyp.iSup_sigmaAt_inf_conj_Pc_eq_bot (hS : Sec6Hyp M V) (h71 : Sec7.Stmt71 M V)
    {A B : Subgroup G} {g : G} (hAg : A = conjSubgroup g V) (hA : A ∈ sigmaSet M V)
    (hB : B ∈ sigmaSet M V) (hAB : IsL2Gen A B)
    (hYc : y0Of V (A ⊔ B) ≤ cenOf (A ⊔ B))
    (hYP : y0Of V (A ⊔ B) ⊓ conjSubgroup g (Pc M V) = ⊥)
    (hsup : y0Of V (A ⊔ B) ⊔ conjSubgroup g (Pc M V) = conjSubgroup g (m0Of M V)) :
    (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ⊓ conjSubgroup g (Pc M V) = ⊥ := by
  set T : Subgroup G := ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C with hT
  set D : Subgroup G := T ⊓ conjSubgroup g (Pc M V) with hD
  have hTle : T ≤ cenOf (A ⊔ B) ⊓ conjSubgroup g (m0Of M V) :=
    hS.sec5.iSup_sigmaAt_le hAg hA hB
  have hTc : T ≤ cenOf (A ⊔ B) := hTle.trans inf_le_left
  have hTcA : T ≤ cenOf A := by
    intro c hc
    have h1 : c ∈ cenOf (A ⊔ B) := hTc hc
    rw [Subgroup.mem_centralizer_iff] at h1 ⊢
    intro a ha
    exact h1 a (Subgroup.mem_sup_left ha)
  have hTcB : T ≤ cenOf B := by
    intro c hc
    have h1 : c ∈ cenOf (A ⊔ B) := hTc hc
    rw [Subgroup.mem_centralizer_iff] at h1 ⊢
    intro b hb
    exact h1 b (Subgroup.mem_sup_right hb)
  have hDY : ⁅D, y0Of V (A ⊔ B)⁆ = ⊥ :=
    hS.commutator_inf_y0Of_eq_bot hAg hYc hYP hTc
  have hYCD : y0Of V (A ⊔ B) ≤ cenOf D := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : ⁅d, y⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hDY]
      exact Subgroup.commutator_mem_commutator hd hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
  have hYA : y0Of V (A ⊔ B) ≤ cenOf A := by
    intro y hy
    have h2 : y ∈ cenOf (A ⊔ B) := hYc hy
    rw [Subgroup.mem_centralizer_iff] at h2 ⊢
    intro a ha
    exact h2 a (Subgroup.mem_sup_left ha)
  have hYcen : y0Of V (A ⊔ B) ≤ cenOf (D ⊔ A) :=
    (le_inf hYCD hYA).trans (le_of_eq (centralizer_sup_eq D A).symm)
  have hPgN : conjSubgroup g (Pc M V) ≤ Subgroup.normalizer ((D ⊔ A : Subgroup G) : Set G) :=
    hS.conj_Pc_le_normalizer_inf_sup hAg hA hTcA
  have hm0N : m0Of (conjSubgroup g M) (conjSubgroup g V) ≤
      Subgroup.normalizer ((D ⊔ A : Subgroup G) : Set G) := by
    rw [m0Of_conjSubgroup g, ← hsup]
    exact sup_le (hYcen.trans (Subgroup.centralizer_le_normalizer ((D ⊔ A : Subgroup G) : Set G)))
      hPgN
  have hVle : conjSubgroup g V ≤ D ⊔ A := hAg.symm.trans_le le_sup_right
  have hAP : A ≤ conjSubgroup g (Pc M V) :=
    hAg.symm ▸ conjSubgroup_mono (g := g) hS.sec5.toRootHyp.toHyp.le_Pc
  have hNP : D ⊔ A ≤ Pc (conjSubgroup g M) (conjSubgroup g V) := by
    rw [Pc_conjSubgroup]
    exact sup_le inf_le_right hAP
  rcases Sec7.Stmt71.conj h71 g (D ⊔ A) hVle hNP hm0N with hEq | hEq
  · have hDA : D ≤ A := le_sup_left.trans (le_of_eq (hEq.trans hAg.symm))
    have hDle : D ≤ A ⊓ cenOf B := le_inf hDA (inf_le_left.trans hTcB)
    rw [IsL2Gen.inf_cenOf_eq_bot hAB] at hDle
    exact le_bot_iff.mp hDle
  · exfalso
    have hYle : y0Of V (A ⊔ B) ≤ A := by
      have hc : cenOf (conjSubgroup g (Pc M V)) = A :=
        (centralizer_conjSubgroup_eq g (Pc M V)).trans
          ((congrArg (conjSubgroup g) hS.sec5.toRootHyp.toHyp.centralizer_Pc).trans hAg.symm)
      have h := hYcen
      rw [hEq, Pc_conjSubgroup] at h
      exact h.trans (le_of_eq hc)
    have hVA : V ≤ A := (le_y0Of V (A ⊔ B)).trans hYle
    have hcardA : Nat.card A = Nat.card V := hAg.symm ▸ card_conjSubgroup g V
    have hAV : A = V := (Subgroup.eq_of_le_of_card_ge hVA (le_of_eq hcardA)).symm
    exact absurd hAV (ne_of_mem_sigmaSet hS.sec5.toRootHyp hA)

theorem Sec7Hyp.stmt74 (hS : Sec7Hyp M V n f) (h71 : Sec7.Stmt71 M V)
    (h73 : Sec7.Stmt73 M V n f) : Sec7.Stmt74 M V := by
  intro A B g hAg hA hB hAB
  obtain ⟨h, hX⟩ := exists_l2Datum hA hB hAB
  obtain ⟨hYc0, -, -, -, -⟩ := h73 A B h hX
  have hYeq : y0Of V (A ⊔ B) = y0Of V (Subgroup.zpowers h) := Sec7.Stmt73.y0Of_eq h73 hX
  have hYc : y0Of V (A ⊔ B) ≤ cenOf (A ⊔ B) := hYeq.symm ▸ hYc0
  have hYleT : y0Of V (A ⊔ B) ≤ ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C :=
    hS.toSec6Hyp.sec5.y0Of_le_iSup_sigmaAt hA hB
  have hTm : (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ≤ conjSubgroup g (m0Of M V) :=
    (hS.toSec6Hyp.sec5.iSup_sigmaAt_le hAg hA hB).trans inf_le_right
  have hYm : y0Of V (Subgroup.zpowers h) ≤ conjSubgroup g (m0Of M V) := by
    rw [← hYeq]
    exact hYleT.trans hTm
  have hYP : y0Of V (A ⊔ B) ⊓ conjSubgroup g (Pc M V) = ⊥ :=
    hYeq.symm ▸ Sec5Hyp.y0Of_inf_conj_Pc_eq_bot hS.toSec6Hyp.sec5 h73 hAg hX
  have hPc : Pc M V ≤ m0Of M V := hS.toSec6Hyp.Pc_le_m0Of h71
  have hsup0 : y0Of V (Subgroup.zpowers h) ⊔ conjSubgroup g (Pc M V) =
      conjSubgroup g (m0Of M V) :=
    le_antisymm (sup_le hYm (conjSubgroup_mono hPc)) (hS.conj_m0Of_le_sup h73 hAg hX hYm)
  have hsup : y0Of V (A ⊔ B) ⊔ conjSubgroup g (Pc M V) = conjSubgroup g (m0Of M V) := by
    rw [hYeq]
    exact hsup0
  have hTD : (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ⊓ conjSubgroup g (Pc M V) = ⊥ :=
    hS.toSec6Hyp.iSup_sigmaAt_inf_conj_Pc_eq_bot h71 hAg hA hB hAB hYc hYP hsup
  refine ⟨le_antisymm hYleT ?_, hYP, hsup⟩
  intro t ht
  have hYN : y0Of V (A ⊔ B) ≤ Subgroup.normalizer (conjSubgroup g (Pc M V) : Set G) := by
    intro y hy
    have h1 : y ∈ cenOf (A ⊔ B) := hYc hy
    rw [Subgroup.mem_centralizer_iff] at h1
    refine hS.toSec6Hyp.sec5.mem_normalizer_conj_Pc g ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hAg] at ha
    exact h1 a (Subgroup.mem_sup_left ha)
  have ht' : t ∈ y0Of V (A ⊔ B) ⊔ conjSubgroup g (Pc M V) := by
    rw [hsup]
    exact hTm ht
  have htprod : t ∈ (y0Of V (A ⊔ B) : Set G) * (conjSubgroup g (Pc M V) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (y0Of V (A ⊔ B))
      (conjSubgroup g (Pc M V)) hYN]
    exact ht'
  obtain ⟨y, hy, p, hp, rfl⟩ := Set.mem_mul.mp htprod
  have hyt : y ∈ ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C := hYleT hy
  have hpT : p ∈ ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C := by
    have h1 : y⁻¹ * (y * p) ∈ ⨆ C ∈ sigmaAt A ∩ sigmaAt B, C :=
      (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C).mul_mem
        ((⨆ C ∈ sigmaAt A ∩ sigmaAt B, C).inv_mem hyt) ht
    simpa using h1
  have hpBot : p ∈ (⊥ : Subgroup G) := by
    rw [← hTD]
    exact ⟨hpT, hp⟩
  rw [Subgroup.mem_bot.mp hpBot, mul_one]
  exact hy

end CFSG.RankThree.GF2n.Tim81
