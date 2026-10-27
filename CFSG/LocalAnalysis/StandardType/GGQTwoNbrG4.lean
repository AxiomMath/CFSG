module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType
open CFSG.Assembly
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem qTwoNbrH_conj_comp {Q : Type} [Group Q] (a b : Q) :
    (MulEquiv.toMonoidHom (MulAut.conj a)).comp (MulEquiv.toMonoidHom (MulAut.conj b⁻¹)) =
      MulEquiv.toMonoidHom (MulAut.conj (a * b⁻¹)) := by
  ext z
  change a * (b⁻¹ * z * b⁻¹⁻¹) * a⁻¹ = (a * b⁻¹) * z * (a * b⁻¹)⁻¹
  group

private theorem qTwoNbrH_le_map_conj_inv {Q : Type} [Group Q] (a : Q) {S J A : Subgroup Q}
    (hA : A = S.map (MulEquiv.toMonoidHom (MulAut.conj a))) (hAJ : A ≤ J) :
    S ≤ J.map (MulEquiv.toMonoidHom (MulAut.conj a⁻¹)) := by
  intro z hz
  have h1 : (MulAut.conj a) z ∈ J := hAJ (by rw [hA]; exact Subgroup.mem_map_of_mem _ hz)
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj a) z, h1, ?_⟩
  change a⁻¹ * (a * z * a⁻¹) * a⁻¹⁻¹ = z
  group

private theorem qTwoNbrH_comm_mul_right {Q : Type} [Group Q] (a b d : Q) (h : d * b = b * d) :
    ⁅a * d, b⁆ = ⁅a, b⁆ := by
  have h' : d * b * d⁻¹ = b := by rw [h, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * d * b * (a * d)⁻¹ * b⁻¹ = a * (d * b * d⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h']

private theorem qTwoNbrH_comm_mul_left {Q : Type} [Group Q] (a b d : Q) (h : d * a = a * d) :
    ⁅a, b * d⁆ = ⁅a, b⁆ := by
  have h0 : d * a * d⁻¹ = a := by rw [h, mul_inv_cancel_right]
  have h' : d * a⁻¹ * d⁻¹ = a⁻¹ := by
    calc d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [h0]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * d) * a⁻¹ * (b * d)⁻¹ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h']

private theorem qTwoNbrH_K_le_joinSup {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel p B Bs x L D J y K)
    (hcomp : ggQTwoNbrCompProp hM) (hblock : ggQTwoNbrBlockProp hM)
    (htransport : ggQTwoNbrTransportProp hM) :
    K ≤ ggQTwoNbrJoinSup Bs J K := by
  classical
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  rcases htransport with ⟨I0, hI0card, htrans⟩
  let P : Subgroup G := ggQTwoNbrJoinSup Bs J K
  let qK : ↥K →* hM.Q := hM.q.comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Bs))
  have hconjK : ∀ n ∈ K, ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
    intro n hn k hk
    exact K.mul_mem (K.mul_mem hn hk) (K.inv_mem hn)
  have hPK : P ≤ K := by
    change ggQTwoNbrJoinSup Bs J K ≤ K
    unfold ggQTwoNbrJoinSup
    rw [iSup_le_iff]
    intro n
    rw [iSup_le_iff]
    intro hn
    rw [iSup_le_iff]
    intro φ
    rintro x ⟨j, hjJ, rfl⟩
    simpa [MulAut.conj_apply] using hconjK n hn j (hM.hJK hjJ)
  let Psub : Subgroup ↥(K ⊔ Bs) := P.subgroupOf (K ⊔ Bs)
  let Pbar : Subgroup hM.Q := Psub.map hM.q
  have hPbar_le : Pbar ≤ hM.Kbar := by
    rintro x ⟨k, hk, rfl⟩
    rw [hM.hKbar]
    exact ⟨⟨(k : G), hPK (Subgroup.mem_subgroupOf.mp hk)⟩, rfl⟩
  have hJ_le_P : ∀ (n : G) (hn : n ∈ K) (hnN : n ∈ Subgroup.normalizer (Bs : Set G)),
      J.map (MulAut.conj n).toMonoidHom ≤ P := by
    intro n hn hnN
    change J.map (MulAut.conj n).toMonoidHom ≤ ggQTwoNbrJoinSup Bs J K
    unfold ggQTwoNbrJoinSup
    refine le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le
      ⟨(Subgroup.normalizerMonoidHom Bs) ⟨n, hnN⟩, hnN, ?_⟩ le_rfl))
    intro b
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨n, hnN⟩ b
  have hJbar_le_Pbar : ∀ (n : G) (hn : n ∈ K) (hnN : n ∈ Subgroup.normalizer (Bs : Set G)),
      hM.Jbar.map (MulAut.conj (hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩)).toMonoidHom ≤ Pbar := by
    intro n hn hnN x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hM.hJbar] at hy
    obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp hy
    have hxq : (MulAut.conj (hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩))
        (hM.q ((Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Bs)) ((Subgroup.inclusion hM.hJK) j))) =
        hM.q ⟨n * (j : G) * n⁻¹, (le_sup_left : K ≤ K ⊔ Bs) (hconjK n hn j (hM.hJK j.2))⟩ := by
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      exact congrArg hM.q (Subtype.ext rfl)
    change (MulAut.conj (hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hn⟩))
      (hM.q ((Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Bs)) ((Subgroup.inclusion hM.hJK) j))) ∈ Pbar
    rw [hxq]
    refine Subgroup.mem_map.mpr ⟨⟨n * (j : G) * n⁻¹,
      (le_sup_left : K ≤ K ⊔ Bs) (hconjK n hn j (hM.hJK j.2))⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hmem : (MulAut.conj n) (j : G) ∈ J.map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem _ j.2
    have hP := hJ_le_P n hn hnN hmem
    simpa [MulAut.conj_apply] using hP

  rcases hblock with ⟨IB, hIBcard, hIBJ⟩
  have hIB := htrans IB hIBcard
  obtain ⟨nB, hnBK, hnBN, hnBeq⟩ := hIB
  have hseedJ : (coordBlockSU hM.F0 2 1 I0).map hM.ψ ≤
      hM.Jbar.map (MulAut.conj (hM.q ⟨nB, (le_sup_left : K ≤ K ⊔ Bs) hnBK⟩)⁻¹).toMonoidHom :=
    qTwoNbrH_le_map_conj_inv _ hnBeq hIBJ
  have hblock_le : ∀ I : Finset (Fin hM.d), I.card = 4 →
      (coordBlockSU hM.F0 2 1 I).map hM.ψ ≤ Pbar := by
    intro I hI
    have hI' := htrans I hI
    obtain ⟨n, hnK, hnN, hnEq⟩ := hI' 
    have hstep : (coordBlockSU hM.F0 2 1 I).map hM.ψ =
        ((coordBlockSU hM.F0 2 1 I0).map hM.ψ).map
          (MulAut.conj (hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hnK⟩)).toMonoidHom := hnEq
    rw [hstep]
    refine (Subgroup.map_mono hseedJ).trans ?_
    rw [Subgroup.map_map]
    have hmK : n * nB⁻¹ ∈ K := K.mul_mem hnK (K.inv_mem hnBK)
    have hmN : n * nB⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ hnBN)
    have hle := hJbar_le_Pbar (n * nB⁻¹) hmK hmN
    have hmap_eq : ((MulEquiv.toMonoidHom (MulAut.conj (hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hnK⟩))).comp
        (MulEquiv.toMonoidHom (MulAut.conj (hM.q ⟨nB, (le_sup_left : K ≤ K ⊔ Bs) hnBK⟩)⁻¹))) =
        MulEquiv.toMonoidHom (MulAut.conj (hM.q ⟨n * nB⁻¹, (le_sup_left : K ≤ K ⊔ Bs) hmK⟩)) := by
      have hq_mul : hM.q ⟨n * nB⁻¹, (le_sup_left : K ≤ K ⊔ Bs) hmK⟩ =
          hM.q ⟨n, (le_sup_left : K ≤ K ⊔ Bs) hnK⟩ *
            (hM.q ⟨nB, (le_sup_left : K ≤ K ⊔ Bs) hnBK⟩)⁻¹ := by
        rw [show (⟨n * nB⁻¹, (le_sup_left : K ≤ K ⊔ Bs) hmK⟩ : ↥(K ⊔ Bs)) =
          (⟨n, (le_sup_left : K ≤ K ⊔ Bs) hnK⟩ : ↥(K ⊔ Bs)) *
            (⟨nB, (le_sup_left : K ≤ K ⊔ Bs) hnBK⟩ : ↥(K ⊔ Bs))⁻¹ from Subtype.ext (by simp)]
        rw [map_mul, map_inv]
      rw [hq_mul]
      exact qTwoNbrH_conj_comp _ _
    rw [hmap_eq]
    exact hle
  have hd5 : 5 ≤ hM.d := hM.hd
  have hgen := fourBlockSup_eq_top hM.hcardF0 (by omega : 4 ≤ hM.d)
  have hKbar_le : hM.Kbar ≤ Pbar := by
    rw [← hM.hψ_range, MonoidHom.range_eq_map, ← hgen]
    change Subgroup.map hM.ψ (⨆ I, ⨆ (_ : I.card = 4),
      coordBlockSU hM.F0 2 1 I) ≤ Pbar
    rw [Subgroup.map_iSup]
    refine iSup_le (fun I => ?_)
    rw [Subgroup.map_iSup]
    exact iSup_le (fun hI => hblock_le I hI)
  have hdecomp : ∀ k ∈ K, ∃ p ∈ P, ∃ d ∈ hM.Delta, k = p * d := by
    intro k hk
    have hkbar : qK ⟨k, hk⟩ ∈ Pbar := by
      have : qK ⟨k, hk⟩ ∈ hM.Kbar := by
        rw [hM.hKbar]
        exact ⟨⟨k, hk⟩, rfl⟩
      exact hKbar_le this
    obtain ⟨pk, hpk, hpkq⟩ := Subgroup.mem_map.mp hkbar
    have hpkP : (pk : G) ∈ P := Subgroup.mem_subgroupOf.mp hpk
    have hpkK : (pk : G) ∈ K := hPK hpkP
    have hker : (pk : G)⁻¹ * k ∈ hM.Delta := by
      have hpkq' : hM.q ⟨(pk : G), (le_sup_left : K ≤ K ⊔ Bs) hpkK⟩ =
          hM.q ⟨k, (le_sup_left : K ≤ K ⊔ Bs) hk⟩ := hpkq
      have hinv : hM.q ⟨(pk : G)⁻¹, (le_sup_left : K ≤ K ⊔ Bs) (K.inv_mem hpkK)⟩ =
          (hM.q ⟨(pk : G), (le_sup_left : K ≤ K ⊔ Bs) hpkK⟩)⁻¹ := by
        exact map_inv hM.q (⟨(pk : G), (le_sup_left : K ≤ K ⊔ Bs) hpkK⟩ : ↥(K ⊔ Bs))
      have harg : (⟨((pk : G)⁻¹ * k), (le_sup_left : K ≤ K ⊔ Bs) (K.mul_mem (K.inv_mem hpkK) hk)⟩ :
          ↥(K ⊔ Bs)) = (⟨((pk : G)⁻¹), (le_sup_left : K ≤ K ⊔ Bs) (K.inv_mem hpkK)⟩ : ↥(K ⊔ Bs)) *
            (⟨k, (le_sup_left : K ≤ K ⊔ Bs) hk⟩ : ↥(K ⊔ Bs)) := Subtype.ext rfl
      have hq : hM.q ⟨((pk : G)⁻¹ * k), (le_sup_left : K ≤ K ⊔ Bs) (K.mul_mem (K.inv_mem hpkK) hk)⟩ = 1 := by
        rw [harg, map_mul, hinv, ← hpkq']
        exact inv_mul_cancel _
      have hmem : (⟨((pk : G)⁻¹ * k), (le_sup_left : K ≤ K ⊔ Bs) (K.mul_mem (K.inv_mem hpkK) hk)⟩ :
          ↥(K ⊔ Bs)) ∈ hM.q.ker := MonoidHom.mem_ker.mpr hq
      rw [hM.hq_ker] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    exact ⟨(pk : G), hpkP, (pk : G)⁻¹ * k, hker, by group⟩
  have hmapc : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperf : K = ⁅K, K⁆ := by
    rw [← hmapc, hM.hKperf, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm_le : ⁅K, K⁆ ≤ P := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨p1, hp1, d1, hd1, rfl⟩ := hdecomp x hx
    obtain ⟨p2, hp2, d2, hd2, rfl⟩ := hdecomp y hy
    have hd1c : d1 * (p2 * d2) = (p2 * d2) * d1 :=
      hM.hDelta_central d1 hd1 (p2 * d2) (K.mul_mem (hPK hp2) (hM.hDelta_le_K hd2))
    have hd2c : d2 * p1 = p1 * d2 := hM.hDelta_central d2 hd2 p1 (hPK hp1)
    rw [qTwoNbrH_comm_mul_right p1 (p2 * d2) d1 hd1c, qTwoNbrH_comm_mul_left p1 p2 d2 hd2c,
      commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hp1 hp2) (P.inv_mem hp1)) (P.inv_mem hp2)
  calc K = ⁅K, K⁆ := hperf
    _ ≤ P := hcomm_le

theorem qTwoNbr_gen {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hM : QTwoNbrModel p B Bs x L D J y K)
    (hcomp : ggQTwoNbrCompProp hM) (hblock : ggQTwoNbrBlockProp hM)
    (htransport : ggQTwoNbrTransportProp hM) :
    K ≤ ggQTwoNbrJoinSup Bs J K :=
  qTwoNbrH_K_le_joinSup hM hcomp hblock htransport

end CFSG.StandardType.QTwo

end
