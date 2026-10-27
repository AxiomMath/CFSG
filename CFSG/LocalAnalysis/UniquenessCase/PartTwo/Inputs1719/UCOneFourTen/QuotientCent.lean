module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims122
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaTransfer
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.GH74.GLS.LU.Local.Core2
import CFSG.GroupTheory.Commutator.SubgroupOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

variable {G : Type} [Group G] [Finite G]

private lemma mem_centOverO2_iff_uc410 {X L : Subgroup G} {x : G} :
    x ∈ F08.CentOverO2 X L ↔ x ∈ X ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  let Q := CFSG.Open.pCoreOf 2 L
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have norm_of_pred : ∀ y : G, (y ∈ X ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Q) →
      y ∈ Subgroup.normalizer (L : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]
      intro l hl
      rw [Subgroup.mem_comap]
      change y * l * y⁻¹ ∈ L
      have hmem : y * l * y⁻¹ = (y * l * y⁻¹ * l⁻¹) * l := by group
      rw [hmem]
      exact L.mul_mem (hQL (hy.2 l hl)) hl
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  unfold F08.CentOverO2
  constructor
  · intro hx
    change x ∈ Subgroup.closure {y : G | y ∈ X ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Q} at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨X.one_mem, fun l _ => by simp⟩
    | mul a b _ _ ha hb =>
      refine ⟨X.mul_mem ha.1 hb.1, fun l hl => ?_⟩
      have haQ : a ∈ Subgroup.normalizer (Q : Set G) :=
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L) (norm_of_pred a ha)
      have h1 : a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 haQ (b * l * b⁻¹ * l⁻¹)).1 (hb.2 l hl)
      have h2 : a * l * a⁻¹ * l⁻¹ ∈ Q := ha.2 l hl
      have hmem := Q.mul_mem h1 h2
      convert hmem using 1
      group
    | inv a _ ha =>
      refine ⟨X.inv_mem ha.1, fun l hl => ?_⟩
      have haQ : a ∈ Subgroup.normalizer (Q : Set G) :=
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L) (norm_of_pred a ha)
      have hq : l * a * l⁻¹ * a⁻¹ ∈ Q := by
        rw [show l * a * l⁻¹ * a⁻¹ = (a * l * a⁻¹ * l⁻¹)⁻¹ by group]
        exact Q.inv_mem (ha.2 l hl)
      have hmem := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haQ)
        (l * a * l⁻¹ * a⁻¹)).1 hq
      convert hmem using 1
      group
  · rintro ⟨hxX, hxL⟩
    exact Subgroup.subset_closure ⟨hxX, hxL⟩

omit [Finite G] in
private lemma pCoreOf_map_uc410 {H L : Subgroup G} (hLH : L ≤ H) :
    CFSG.Open.pCoreOf 2 ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) =
      ((CFSG.Open.pCoreOf 2 L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥H)
  have h := pCoreOf_map_of_surjective_of_isPGroup_ker
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _) hker (L.subgroupOf H)
  rw [CFSG.GroupTheory.pCoreOf_subgroupOf 2 hLH] at h
  exact h

private lemma mem_normalizer_of_mem_normalizer_sup_uc410 {L Q : Subgroup G}
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hQ : IsPGroup 2 Q)
    (hLperf : ⁅L, L⁆ = L) {w : G}
    (hw : w ∈ Subgroup.normalizer ((L ⊔ Q : Subgroup G) : Set G)) :
    w ∈ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLQmap : (L ⊔ Q).map (MulAut.conj w).toMonoidHom = L ⊔ Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  have hLwLQ : L.map (MulAut.conj w).toMonoidHom ≤ L ⊔ Q :=
    (Subgroup.map_mono le_sup_left).trans_eq hLQmap
  have hsup : L.subgroupOf (L ⊔ Q) ⊔ Q.subgroupOf (L ⊔ Q) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hLnorm : (L.subgroupOf (L ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQL)
  have hKperf : ⁅(L.map (MulAut.conj w).toMonoidHom).subgroupOf (L ⊔ Q),
      (L.map (MulAut.conj w).toMonoidHom).subgroupOf (L ⊔ Q)⁆ =
      (L.map (MulAut.conj w).toMonoidHom).subgroupOf (L ⊔ Q) := by
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hLwLQ hLwLQ, ← Subgroup.map_commutator,
      hLperf]
  have hle := CFSG.GH74.GLS.LU.Local.perfect_le_of_sup_eq_top_of_isPGroup
    (p := 2) hsup (hQ.comap_subtype) hKperf
  have hLwle : L.map (MulAut.conj w).toMonoidHom ≤ L := by
    intro x hx
    exact hle (show (⟨x, hLwLQ hx⟩ : ↥(L ⊔ Q)) ∈
      (L.map (MulAut.conj w).toMonoidHom).subgroupOf (L ⊔ Q) from hx)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge hLwle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]

private lemma mem_normalizer_sup_of_map_mem_normalizer_uc410 {H L : Subgroup G} {w : G}
    (hLH : L ≤ H) (hwH : w ∈ H)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨w, hwH⟩ ∈
      Subgroup.normalizer ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    w ∈ Subgroup.normalizer ((L ⊔ CFSG.Open.pCoreOf 2 H : Subgroup G) : Set G) := by
  let φ := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let N : Subgroup ↥H := CFSG.pCore 2 ↥H
  let P : Subgroup ↥H := L.subgroupOf H ⊔ N
  have hLQH : L ⊔ CFSG.Open.pCoreOf 2 H ≤ H :=
    sup_le hLH (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hPmap : P.map H.subtype = L ⊔ CFSG.Open.pCoreOf 2 H := by
    show (L.subgroupOf H ⊔ N).map H.subtype = L ⊔ CFSG.Open.pCoreOf 2 H
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH]
    rfl
  have hPcomap : P = ((L.subgroupOf H).map φ).comap φ := by
    show L.subgroupOf H ⊔ N = ((L.subgroupOf H).map (QuotientGroup.mk' N)).comap
      (QuotientGroup.mk' N)
    rw [sup_comm]
    exact (QuotientGroup.comap_map_mk' N (L.subgroupOf H)).symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    have hzH : z ∈ H := hLQH hz
    rw [← hPmap] at hz
    obtain ⟨y, hyP, hyz⟩ := Subgroup.mem_map.mp hz
    have hyL : φ y ∈ (L.subgroupOf H).map φ :=
      Subgroup.mem_comap.mp (hPcomap ▸ hyP)
    have hwy : φ (⟨w, hwH⟩ * y * ⟨w, hwH⟩⁻¹) ∈ (L.subgroupOf H).map φ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp h (φ y)).mp hyL
    have hwyP : ⟨w, hwH⟩ * y * ⟨w, hwH⟩⁻¹ ∈ P :=
      hPcomap.symm ▸ (Subgroup.mem_comap.mpr hwy)
    have hval : (H.subtype (⟨w, hwH⟩ * y * ⟨w, hwH⟩⁻¹) : G) = w * z * w⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_subtype]
      rw [show (y : G) = z from hyz]
    change w * z * w⁻¹ ∈ L ⊔ CFSG.Open.pCoreOf 2 H
    rw [← hval]
    exact hPmap ▸ Subgroup.mem_map_of_mem H.subtype hwyP
  · rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]

private lemma commutator_mem_pCoreOf_of_cent_uc410 {H L : Subgroup G} {w l : G}
    (hLH : L ≤ H) (hwH : w ∈ H) (hlL : l ∈ L)
    (hwN : w ∈ Subgroup.normalizer (L : Set G))
    (hcent : ∀ x ∈ (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨w, hwH⟩ * x *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨w, hwH⟩)⁻¹ * x⁻¹ ∈
        CFSG.Open.pCoreOf 2 ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) :
    w * l * w⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let z := w * l * w⁻¹ * l⁻¹
  have hzL : z ∈ L := by
    have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwN l).mp hlL
    exact L.mul_mem h1 (L.inv_mem hlL)
  have hzH : z ∈ H := hLH hzL
  let wH : ↥H := ⟨w, hwH⟩
  let lH : ↥H := ⟨l, hLH hlL⟩
  let zH : ↥H := ⟨z, hzH⟩
  have hlstar : φ lH ∈ (L.subgroupOf H).map φ :=
    Subgroup.mem_map_of_mem φ hlL
  have hz_img : φ zH ∈ CFSG.Open.pCoreOf 2 ((L.subgroupOf H).map φ) := by
    have hcomm := hcent (φ lH) hlstar
    have heq' : wH * lH * wH⁻¹ * lH⁻¹ = zH := by
      ext
      rfl
    rw [← heq', map_mul, map_mul, map_mul, map_inv]
    exact hcomm
  rw [pCoreOf_map_uc410 hLH] at hz_img
  obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz_img
  have haG : (a : G) ∈ CFSG.Open.pCoreOf 2 L := ha
  have hbQ : ((a⁻¹ * zH : ↥H) : G) ∈ CFSG.Open.pCoreOf 2 H := by
    have h1 : φ (a⁻¹ * zH) = 1 := by
      rw [map_mul, map_inv, haz, inv_mul_cancel]
    refine ⟨a⁻¹ * zH, ?_, rfl⟩
    exact (QuotientGroup.eq_one_iff (a⁻¹ * zH)).mp h1
  have hzdecomp : z = (a : G) * ((a⁻¹ * zH : ↥H) : G) := by
    change z = (a : G) * ((a : G)⁻¹ * z)
    group
  have hbL : ((a⁻¹ * zH : ↥H) : G) ∈ L := by
    have haL : (a : G) ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L haG
    have := L.mul_mem (L.inv_mem haL) (hzdecomp ▸ hzL)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hbO : ((a⁻¹ * zH : ↥H) : G) ∈ CFSG.Open.pCoreOf 2 L := by
    have hInf : ((a⁻¹ * zH : ↥H) : G) ∈ L ⊓ CFSG.Open.pCoreOf 2 H := ⟨hbL, hbQ⟩
    have hnorm : ((L ⊓ CFSG.Open.pCoreOf 2 H).subgroupOf L).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
      intro x hx
      have hxQ : x ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G) :=
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) (hLH hx)
      rw [Subgroup.mem_normalizer_iff] at hxQ ⊢
      intro y
      constructor
      · intro hy
        exact ⟨L.mul_mem (L.mul_mem hx hy.1) (L.inv_mem hx), (hxQ y).mp hy.2⟩
      · intro hy
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hxQ y).mpr hy.2⟩
        have hmem := L.mul_mem (L.mul_mem (L.inv_mem hx) hy.1) hx
        have heq : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rwa [heq] at hmem
    have hQ2 : IsPGroup 2 ↥(L ⊓ CFSG.Open.pCoreOf 2 H) := by
      intro x
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
        (⟨(x : G), x.2.2⟩ : ↥(CFSG.Open.pCoreOf 2 H))
      exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hnorm hQ2 hInf
  change z ∈ CFSG.Open.pCoreOf 2 L
  rw [hzdecomp]
  exact (CFSG.Open.pCoreOf 2 L).mul_mem haG hbO

private lemma centOverO2_le_left_uc410 {X L : Subgroup G} : F08.CentOverO2 X L ≤ X := by
  intro x hx
  rw [mem_centOverO2_iff_uc410] at hx
  exact hx.1

theorem centOverO2_map {H M L W : Subgroup G} (hMH : M ≤ H)
    (hQM : CFSG.Open.pCoreOf 2 H ≤ M) (hL : L ∈ calC M) (hWH : W ≤ H) :
    F08.CentOverO2 ((W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
        ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) =
      ((F08.CentOverO2 W L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let Q := CFSG.Open.pCoreOf 2 H
  let QM := CFSG.Open.pCoreOf 2 M
  have hLM : L ≤ M := hL.1.le
  have hLH : L ≤ H := hLM.trans hMH
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQ_le_QM : Q ≤ QM := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 hQM ?_ hQp
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr
      (hMH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hQMn : QM ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims122.le_normalizer_of_isSubnormal_perfect
      (Nat.card M) M rfl L QM hL.1 hL.2.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hQL : Q ≤ Subgroup.normalizer (L : Set G) := hQ_le_QM.trans hQMn
  apply le_antisymm
  · intro x hx
    rw [mem_centOverO2_iff_uc410] at hx
    obtain ⟨wH, hwW, rfl⟩ := Subgroup.mem_map.mp hx.1
    have hwWH : (wH : G) ∈ W := hwW
    have hwH : (wH : G) ∈ H := hWH hwWH
    let Lstar := (L.subgroupOf H).map φ
    have hwNormStar : φ wH ∈ Subgroup.normalizer (Lstar : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        intro l hl
        rw [Subgroup.mem_comap]
        change φ wH * l * (φ wH)⁻¹ ∈ Lstar
        have h := hx.2 l hl
        have heq : φ wH * l * (φ wH)⁻¹ = (φ wH * l * (φ wH)⁻¹ * l⁻¹) * l := by group
        rw [heq]
        exact Lstar.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 Lstar h) hl
      · have hcard : Nat.card (Lstar.map (MulAut.conj (φ wH)).toMonoidHom) = Nat.card Lstar :=
          Subgroup.card_map_of_injective (MulAut.conj (φ wH)).injective
        exact le_of_eq hcard.symm
    have hwNLQ : (wH : G) ∈ Subgroup.normalizer ((L ⊔ Q : Subgroup G) : Set G) :=
      mem_normalizer_sup_of_map_mem_normalizer_uc410 hLH hwH hwNormStar
    have hwN : (wH : G) ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_of_mem_normalizer_sup_uc410 hQL hQp hL.2.1 hwNLQ
    have hwCent : (wH : G) ∈ F08.CentOverO2 W L := by
      rw [mem_centOverO2_iff_uc410]
      exact ⟨hwWH, fun l hl => commutator_mem_pCoreOf_of_cent_uc410 hLH hwH hl hwN hx.2⟩
    exact Subgroup.mem_map.mpr ⟨wH, Subgroup.mem_subgroupOf.mpr hwCent, rfl⟩
  · intro x hx
    obtain ⟨wH, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hw' : (wH : G) ∈ F08.CentOverO2 W L := hw
    rw [mem_centOverO2_iff_uc410] at hw'
    rw [mem_centOverO2_iff_uc410]
    refine ⟨Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hw'.1), ?_⟩
    intro lstar hlstar
    obtain ⟨lH, hlH, rfl⟩ := Subgroup.mem_map.mp hlstar
    have hlL : (lH : G) ∈ L := hlH
    have hcomm : (wH : G) * (lH : G) * (wH : G)⁻¹ * (lH : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 L := hw'.2 (lH : G) hlL
    rw [pCoreOf_map_uc410 hLH]
    refine Subgroup.mem_map.mpr ⟨wH * lH * wH⁻¹ * lH⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hcomm
    · simp [map_mul, map_inv]

theorem isSylowOf_map {H M L R W : Subgroup G} (hMH : M ≤ H)
    (hQM : CFSG.Open.pCoreOf 2 H ≤ M) (hL : L ∈ calC M) (hWH : W ≤ H)
    (hR : IsSylowOf 2 R (F08.CentOverO2 W L)) :
    IsSylowOf 2 ((R.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
      (F08.CentOverO2 ((W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
        ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  let C := F08.CentOverO2 W L
  let CH := C.subgroupOf H
  let Cstar := CH.map φ
  have hCH : C ≤ H := (centOverO2_le_left_uc410.trans hWH)
  have hRH : R ≤ H := hR.le.trans hCH
  have hR' : IsSylowOf 2 (R.subgroupOf H) CH := by
    have hm : IsSylowOf 2 ((R.subgroupOf H).map H.subtype) (CH.map H.subtype) := by
      rw [show CH.map H.subtype = C from Subgroup.map_subgroupOf_eq_of_le hCH,
        show (R.subgroupOf H).map H.subtype = R from Subgroup.map_subgroupOf_eq_of_le hRH]
      exact hR
    exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) H).mp hm
  let f : ↥CH →* ↥Cstar :=
    (φ.comp CH.subtype).codRestrict Cstar fun x => Subgroup.mem_map_of_mem φ x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, by ext; rfl⟩
  have hker : IsPGroup 2 f.ker := by
    rintro ⟨x, hx⟩
    have hx1 : φ (CH.subtype x) = 1 := by
      have h := congrArg (fun z : ↥Cstar => (z : ↥H ⧸ CFSG.pCore 2 ↥H)) hx
      simpa [f] using h
    have hxker : CH.subtype x ∈ CFSG.pCore 2 ↥H := by
      have hmem := MonoidHom.mem_ker.mpr hx1
      rwa [QuotientGroup.ker_mk'] at hmem
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥H) ⟨CH.subtype x, hxker⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact congrArg Subtype.val hn
  obtain ⟨Q, hQ⟩ := hR'
  have hCstar_eq : Cstar = F08.CentOverO2
      ((W.subgroupOf H).map φ) ((L.subgroupOf H).map φ) := by
    rw [centOverO2_map hMH hQM hL hWH]
  rw [← hCstar_eq]
  refine ⟨Sylow.mapSurjective hf Q, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : Cstar.subtype.comp f = φ.comp CH.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hQ]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
