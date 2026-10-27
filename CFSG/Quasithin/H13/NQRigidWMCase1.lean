module

public import CFSG.Quasithin.H13.NQRigidWMSetup
public import CFSG.Quasithin.H13.NQRigidWMCore
public import CFSG.Quasithin.H13.NQRigidWMTransport
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.H13.NQBlockOriginalSupplements

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank
open CFSG.Open (pCoreOf)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped IsMulCommutative commutatorElement

section Internal

variable {G : Type} [Group G]

theorem commV_autOn_map {L W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G)) : (commV (autOn L W)).map W.subtype = ⁅W, L⁆ :=
  CFSG.Quasithin.AutOn.map_commV_autOn_eq hLW

@[expose] noncomputable def internalDatum {L M W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G))
    (hC : L ⊓ centralizer (W : Set G) = (CFSG.solvableRadical L).map L.subtype)
    (hU : ⁅W, L⁆ = qtnqU L M) : WMDatum L M ↥W where
  ι := W.subtype
  inj := W.subtype_injective
  φ := (autOn L W).subtype.comp (autOnHom hLW)
  comp l x := Setup.rho_apply_coe hLW l x
  ker := by
    rw [← ker_autOnHom_eq hLW hC]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  img := by
    have hr : ((autOn L W).subtype.comp (autOnHom hLW)).range = autOn L W := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (autOnHom_surjective hLW),
        ← MonoidHom.range_eq_map, range_subtype]
    rw [hr, commV_autOn_map hLW, hU]

theorem internalDatum_range {L M W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G))
    (hC : L ⊓ centralizer (W : Set G) = (CFSG.solvableRadical L).map L.subtype)
    (hU : ⁅W, L⁆ = qtnqU L M) : (internalDatum hLW hC hU).φ.range = autOn L W := by
  show ((autOn L W).subtype.comp (autOnHom hLW)).range = autOn L W
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (autOnHom_surjective hLW),
    ← MonoidHom.range_eq_map, range_subtype]

theorem explicitModule_of_alternatives {L M W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ normalizer (W : Set G))
    (hC : L ⊓ centralizer (W : Set G) = (CFSG.solvableRadical L).map L.subtype)
    (hU : ⁅W, L⁆ = qtnqU L M)
    (halt : BinaryNaturalSL (autOn L W) (commV (autOn L W))
        (fixV (autOn L W) ⊓ commV (autOn L W)) 2 2 ∨
      (fixV (autOn L W) ⊓ commV (autOn L W) = ⊥ ∧
        AlternatingNatural (autOn L W) (commV (autOn L W)) ⊥ 5) ∨
      BinaryNaturalSL (autOn L W) (commV (autOn L W))
        (fixV (autOn L W) ⊓ commV (autOn L W)) 3 1 ∨
      (∃ (I : Fin 2 → Subgroup ↥W) (π : ↥(StatedSL 3 (ZMod 2)) →* ↥(autOn L W)), iSupIndep I ∧
        (⨆ i, I i) = commV (autOn L W) ∧
          ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia (autOn L W) (I i) ⊥ π)) :
    QTNQExplicitModule L M := by
  have hr := internalDatum_range hLW hC hU
  rw [← hr] at halt
  rcases halt with h | ⟨-, h⟩ | h | ⟨I, π, hind, hsup, hreal⟩
  · exact Or.inl ((internalDatum hLW hC hU).naturalFour h)
  · exact Or.inr (Or.inl ((internalDatum hLW hC hU).deletedFive h))
  · exact Or.inr (Or.inr (Or.inr ((internalDatum hLW hC hU).naturalThreeExtension h)))
  · exact Or.inr (Or.inr (Or.inl ((internalDatum hLW hC hU).naturalThreeDouble hind hsup hreal)))

end Internal

section QTNQ

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem isSylowTwoOf_qtnq (h : QTNQ T L M) : IsSylowTwoOf T M :=
  ⟨h.t_le, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le h.t_le))⟩

theorem autOn_qtnqVc_data (h : QTNQ T L M) :
    ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ IsSimpleGroup ↥(autOn L (qtnqVc M)) ∧
      s * (s ^ 2 - 1) = 2 * Nat.card ↥(autOn L (qtnqVc M)) ∧
      CFSG.IsQuasisimple ↥(autOn L (qtnqVc M)) := by
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  obtain ⟨R, hR⟩ := NQBlock.exists_originalCentralizer hTL
  obtain ⟨-, -, ⟨s, hsP, hs5, ⟨e0⟩⟩, -⟩ := NQBlock.original_common_residual h hR
  have hLW : L ≤ normalizer (qtnqVc M : Set G) := h.l_le.trans (qtnqVc_isTwoReducedIn M).2.1
  set eS : ↥(autOn L (qtnqVc M)) ≃* projectiveSL 2 (ZMod s) :=
    (radQuotEquivAutOn hLW h.centralizer_eq_radical).symm.trans e0 with heS
  have hsim : IsSimpleGroup (projectiveSL 2 (ZMod s)) := isSimpleGroup_projectiveSL_two_zmod hs5
  have hsimp : IsSimpleGroup ↥(autOn L (qtnqVc M)) := eS.isSimpleGroup
  have hcard : s * (s ^ 2 - 1) = 2 * Nat.card ↥(autOn L (qtnqVc M)) := by
    rw [Nat.card_congr eS.toEquiv]
    exact card_projectiveSL_two_zmod (by omega)
  have hdvd : s ∣ Nat.card ↥(autOn L (qtnqVc M)) := by
    have h1 : s ∣ 2 * Nat.card ↥(autOn L (qtnqVc M)) := hcard ▸ dvd_mul_right s _
    rcases (Nat.Prime.dvd_mul hsP.out).mp h1 with h2 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact h2
  have hne : Nat.card ↥(autOn L (qtnqVc M)) ≠ s := by
    intro h2
    rw [h2] at hcard
    have h3 : s ^ 2 - 1 = 2 := by
      have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < s) (hcard.trans (mul_comm 2 s))
      exact this
    have h4 : 25 ≤ s ^ 2 := by nlinarith
    omega
  have hnab := exists_noncomm_of_isSimpleGroup hsP.out hdvd hne
  exact ⟨s, hsP.out, hs5, hsimp, hcard, isQuasisimple_of_simple_nonab hnab⟩

theorem b56_qtnq (h56 : AsB56) (h : QTNQ T L M)
    (hJ : ⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ = L) :
    ∃ A : Subgroup (MulAut ↥(qtnqVc M)),
      IsFFStarOffender (autOn M (qtnqVc M)) A ∧ ⁅autOn L (qtnqVc M), A⁆ = autOn L (qtnqVc M) ∧
      autOn L (qtnqVc M) ≤ ffJ (autOn M (qtnqVc M)) ∧
      (∀ x ∈ ffJ (autOn M (qtnqVc M)), ∀ k ∈ autOn L (qtnqVc M),
        x * k * x⁻¹ ∈ autOn L (qtnqVc M)) ∧
      pCoreOf 2 (ffJ (autOn M (qtnqVc M))) = ⊥ ∧ A ≤ ffJ (autOn M (qtnqVc M)) ∧
      (B56Case1 (ffJ (autOn M (qtnqVc M))) ∨ B56Case2 (ffJ (autOn M (qtnqVc M))) ∨
        B56Case3 (ffJ (autOn M (qtnqVc M))) ∨ B56Case4 (ffJ (autOn M (qtnqVc M))) ∨
        B56Case5 (ffJ (autOn M (qtnqVc M)))) := by
  have hred := qtnqVc_isTwoReducedIn M
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  have hML : M ≤ normalizer (L : Set G) := h.eq_normalizer.le
  have hLW : L ≤ normalizer (qtnqVc M : Set G) := h.l_le.trans hred.2.1
  obtain ⟨s, -, -, hsimp, -, -⟩ := autOn_qtnqVc_data h
  have hJ' : L = ⁅L, thompsonJ T⁆ := by
    rw [← elemThompson_map_subtype_eq_thompsonJ, hJ]
  obtain ⟨A, -, hA, hLA⟩ :=
    exists_offender_of_thompson (isSylowTwoOf_qtnq h) hTL hred hLW hsimp hJ'
  obtain ⟨hKJ, hn, hQ, hAJ, hcases⟩ := b56Cases_ffJ_autOn h56 hred.2.2.1.2 hred.2.1 h.l_le hML
    (sqtkGroup_of_qtnq h) (Setup.pCoreOf_autOn_eq_bot hred) hA hLA
  exact ⟨autOn A (qtnqVc M), hA, hLA, hKJ, hn, hQ, hAJ, hcases⟩

theorem explicitModule_of_b56Case1
    (h : QTNQ T L M)
    (hKJ : autOn L (qtnqVc M) ≤ ffJ (autOn M (qtnqVc M)))
    (hn : ∀ x ∈ ffJ (autOn M (qtnqVc M)), ∀ k ∈ autOn L (qtnqVc M),
      x * k * x⁻¹ ∈ autOn L (qtnqVc M))
    (h1 : B56Case1 (ffJ (autOn M (qtnqVc M)))) : QTNQExplicitModule L M := by
  obtain ⟨s, hs, hs5, -, hcard, hKq⟩ := autOn_qtnqVc_data h
  have hF := eq_of_le_quasisimple hKJ hn hKq h1.1
  have hB : B51Conclusion (ffJ (autOn M (qtnqVc M))) (autOn L (qtnqVc M)) := hF ▸ h1.2.1
  have hLW : L ≤ normalizer (qtnqVc M : Set G) := h.l_le.trans (qtnqVc_isTwoReducedIn M).2.1
  exact explicitModule_of_alternatives hLW h.centralizer_eq_radical rfl
    (psl2_module_of_b51Conclusion hB hs hs5 hcard)

end QTNQ

end CFSG.Quasithin.H13.NQRigid
