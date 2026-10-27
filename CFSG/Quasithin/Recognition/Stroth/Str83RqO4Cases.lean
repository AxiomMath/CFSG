module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot

import CFSG.Walter.Cited.HuppertAlperin
import CFSG.Quasithin.Vol2.GoldschmidtF431L3Base
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4LocalStructure
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexBase
import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4L2Cover
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dichotomy
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4CaseIFacts
import CFSG.GH74.Uniqueness.Section15Aux3
public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5
open CFSG.Quasithin.RonanF13 (HallTwoPrime)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem conjSub_MX_x₁ (i : ℤ) :
    conjSub t.x₁ (t.MX t.QT i) = t.MX t.QT (-i) := by
  have hQ : conjSub t.x₁ t.QT = t.QT := by
    simpa [conjSub] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp t.x₁_mem_normalizer_pCoreOf_GT)
  unfold Track.MX normIn
  rw [conjSub_inf, ← conjSub_normalizer, hQ,
    show conjSub t.x₁ (t.Gv i) = t.Gv (-i) from t.map_Gv_x₁ i]

private theorem conjSub_EX_x₁ (i : ℤ) :
    conjSub t.x₁ (t.EX t.QT i) = t.EX t.QT (-i) := by
  have hQ : conjSub t.x₁ t.QT = t.QT := by
    simpa [conjSub] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp t.x₁_mem_normalizer_pCoreOf_GT)
  unfold Track.EX
  rw [conjSub_inf, ← conjSub_normalizer, hQ,
    show conjSub t.x₁ (t.Qv i) = t.Qv (-i) from t.map_Qv_x₁ i]

private theorem conjSub_LX_x₁ (i : ℤ) :
    conjSub t.x₁ (t.LX t.QT i) = t.LX t.QT (-i) := by
  unfold Track.LX
  rw [conjSub_oTwoPrime, conjSub_MX_x₁]

theorem QT_le_EX {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.QT ≤ t.EX t.QT 1 :=
  le_inf (t.pCoreOf_GT_le_Qv hfr 1) Subgroup.le_normalizer

theorem Zv_one_le_EX {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Zv 1 ≤ t.EX t.QT 1 := by
  refine le_inf (t.Zv_le_Qv 1) ?_
  refine (t.Zv_le_centralizer 1).trans ((Subgroup.centralizer_le ?_).trans
    (Subgroup.centralizer_le_normalizer (t.QT : Set G)))
  intro x hx
  exact t.pCoreOf_GT_le_Qv hfr 1 hx

theorem EX_QT_lt_Qv_one {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hEQ : t.EX t.QT 1 ≤ t.Qv 0) : t.EX t.QT 1 < t.Qv 1 := by
  refine lt_of_le_not_ge inf_le_left ?_
  intro h
  exact t.Qv_one_not_le_Qv_zero hfr (h.trans hEQ)

theorem map_centerOf_LX_x₁ :
    (centerOf (t.LX t.QT 1)).map (MulAut.conj t.x₁).toMonoidHom = centerOf (t.LX t.QT (-1)) ∧
      (centerOf (t.LX t.QT (-1))).map (MulAut.conj t.x₁).toMonoidHom =
        centerOf (t.LX t.QT 1) := by
  constructor
  · change conjSub t.x₁ (centerOf (t.LX t.QT 1)) = centerOf (t.LX t.QT (-1))
    rw [← CFSG.Quasithin.H13.F431.L3.centerOf_conjSub, conjSub_LX_x₁]
  · change conjSub t.x₁ (centerOf (t.LX t.QT (-1))) = centerOf (t.LX t.QT 1)
    rw [← CFSG.Quasithin.H13.F431.L3.centerOf_conjSub, conjSub_LX_x₁]
    norm_num

theorem K_le_normalizer_centerOf_LX : t.K ≤ normalizer (centerOf (t.LX t.QT 1) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k (centerOf (t.LX t.QT 1)) = centerOf (t.LX t.QT 1)
  rw [← CFSG.Quasithin.H13.F431.L3.centerOf_conjSub]
  congr 1
  unfold Track.LX Track.MX normIn
  have hQ : conjSub k t.QT = t.QT := by
    simpa [conjSub] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.K_le_normalizer_pCoreOf_GT hk))
  have hGv : conjSub k (t.Gv 1) = t.Gv 1 := by
    simpa [conjSub] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (t.K_le_Gv 1 hk)))
  rw [conjSub_oTwoPrime, conjSub_inf, ← conjSub_normalizer, hQ, hGv]

private theorem EX_le_QT_of_EX_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hE : pCoreOf 2 (t.MX t.QT 1) = t.EX t.QT 1)
    (hEE : t.EX t.QT 1 = t.EX t.QT (-1)) : t.EX t.QT 1 ≤ t.QT := by
  have hEQv1 : t.EX t.QT 1 ≤ t.Qv 1 := inf_le_left
  have hE2 : IsPGroup 2 (t.EX t.QT 1) := (t.isPGroup_Qv 1).to_le hEQv1
  have hEMX : t.EX t.QT 1 ≤ t.MX t.QT 1 :=
    le_inf inf_le_right (hEQv1.trans (t.Qv_le_Gv_self 1))
  have hENorm : t.MX t.QT 1 ≤ normalizer (t.EX t.QT 1 : Set G) := by
    rw [← hE]
    exact le_normalizer_pCoreOf 2 _
  have hx₂E : t.x₂ ∈ normalizer (t.EX t.QT 1 : Set G) :=
    hENorm (Subgroup.mem_inf.mpr ⟨t.x₂_mem_normalizer_pCoreOf_GT, t.x₂_mem_Gv_one⟩)
  have hx₁E : t.x₁ ∈ normalizer (t.EX t.QT 1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub t.x₁ (t.EX t.QT 1) = t.EX t.QT 1
    rw [conjSub_EX_x₁, hEE]
  have hτE : t.x₂ * t.x₁ ∈ normalizer (t.EX t.QT 1 : Set G) :=
    Subgroup.mul_mem _ hx₂E hx₁E
  have hEGv0 : t.EX t.QT 1 ≤ t.Gv 0 := hEQv1.trans (t.Qv_le_Gv hfr 1).1
  have hEGv1 : t.EX t.QT 1 ≤ t.Gv 1 := hEQv1.trans (t.Qv_le_Gv_self 1)
  have hshift : ∀ i k : ℤ, t.EX t.QT 1 ≤ t.Gv i →
      t.EX t.QT 1 ≤ t.Gv (i + 2 * k) := by
    intro i k hD
    have hmap : (t.EX t.QT 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        t.EX t.QT 1 := by
      simpa [conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem hτE k))
    calc t.EX t.QT 1 = (t.EX t.QT 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom :=
          hmap.symm
      _ ≤ (t.Gv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := Subgroup.map_mono hD
      _ = t.Gv (i + 2 * k) := map_qv_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) i k
  have hEall : ∀ i : ℤ, t.EX t.QT 1 ≤ t.Gv i := by
    intro i
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
    · simpa using hshift 0 k hEGv0
    · simpa [show 1 + 2 * k = 2 * k + 1 by ring] using hshift 1 k hEGv1
  have hEGT : t.EX t.QT 1 ≤ t.GT := le_iInf hEall
  have hGTMX : t.GT ≤ t.MX t.QT 1 :=
    le_inf (le_normalizer_pCoreOf 2 t.GT) (iInf_le _ 1)
  exact le_pCoreOf_of_le_normalizer 2 hEGT (hGTMX.trans hENorm) hE2

theorem EX_QT_ne {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ : t.ArcL t.QT) (hE : pCoreOf 2 (t.MX t.QT 1) = t.EX t.QT 1) :
    t.EX t.QT 1 ≠ t.EX t.QT (-1) := by
  intro hEE
  have hQT_Gv0 : t.QT ≤ t.Gv 0 := fun x hx => (Subgroup.mem_inf.mp (hQ.le hx)).1.2
  have hQT_Gvneg1 : t.QT ≤ t.Gv (-1) := fun x hx => (Subgroup.mem_inf.mp (hQ.le hx)).2
  have hEQT : t.EX t.QT 1 ≤ t.QT := EX_le_QT_of_EX_eq t hfr hE hEE
  have hQTE : t.QT ≤ t.EX t.QT 1 := t.QT_le_EX hfr
  have hQTQv1 : t.QT = t.Qv 1 := by
    have hEeq : t.Qv 1 ⊓ normalizer (t.QT : Set G) = t.QT :=
      le_antisymm (by simpa only [Track.EX] using hEQT) hQTE
    refine le_antisymm (t.pCoreOf_GT_le_Qv hfr 1) ?_
    by_contra hle
    have hne : t.QT ≠ t.Qv 1 := fun h => hle (le_of_eq h.symm)
    obtain ⟨y, hyQv1, hyN, hyNot⟩ :=
      CFSG.Walter.Huppert.exists_mem_normalizer_not_mem (t.isPGroup_Qv 1)
        (t.pCoreOf_GT_le_Qv hfr 1) hne
    have hyinf : y ∈ t.Qv 1 ⊓ normalizer (t.QT : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyQv1, hyN⟩
    rw [hEeq] at hyinf
    exact hyNot hyinf
  have hGw : t.Gw (-1) 0 = t.Gv (-1) ⊓ t.Gv 0 := by
    have h := t.Gw_add_one (-1)
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hleGw : t.Qv 1 ≤ t.Gw (-1) 0 := by
    rw [hGw, ← hQTQv1]
    exact fun x hx => ⟨hQT_Gvneg1 hx, hQT_Gv0 hx⟩
  have hinf := (t.inf_Gv_eq_inf_Qv hfr 0 (X := t.Qv 1) (t.isPGroup_Qv 1)).1 hleGw
  have hinf' : t.Qv 1 ⊓ t.Gv 1 = t.Qv 1 ⊓ t.Qv 0 := by simpa using hinf
  rw [show t.Qv 1 ⊓ t.Gv 1 = t.Qv 1 from inf_eq_left.mpr (t.Qv_le_Gv_self 1)] at hinf'
  exact t.Qv_one_not_le_Qv_zero hfr (by rw [hinf']; exact inf_le_right)

theorem eq_QT_of_normal {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {D : Subgroup G} (hQD : t.QT ≤ D)
    (hDE : D ≤ t.EX t.QT 1 ⊓ t.EX t.QT (-1)) (hM : t.MX t.QT 1 ≤ normalizer (D : Set G))
    {s : G} (hs0 : s ∈ t.MX t.QT 0) (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1))
    (hsD : s ∈ normalizer (D : Set G)) : D = t.QT := by
  have hDQv1 : D ≤ t.Qv 1 := fun x hx => (Subgroup.mem_inf.mp (hDE hx)).1.1
  have hDQvneg : D ≤ t.Qv (-1) := fun x hx => (Subgroup.mem_inf.mp (hDE hx)).2.1
  have hD2 : IsPGroup 2 D := (t.isPGroup_Qv 1).to_le hDQv1
  have hDEXneg : D ≤ t.EX t.QT (-1) := fun x hx => (Subgroup.mem_inf.mp (hDE hx)).2
  have huMX : t.x₁⁻¹ * s ∈ t.MX t.QT 1 :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _
      ((Subgroup.normalizer _).inv_mem t.x₁_mem_normalizer_pCoreOf_GT) hs0.1, hs.1⟩
  have huD : t.x₁⁻¹ * s ∈ normalizer (D : Set G) := hM huMX
  have hx₁D : t.x₁ ∈ normalizer (D : Set G) := by
    have h : s * (t.x₁⁻¹ * s)⁻¹ ∈ normalizer (D : Set G) :=
      Subgroup.mul_mem _ hsD ((Subgroup.normalizer _).inv_mem huD)
    convert h using 1
    group
  have hx₂D : t.x₂ ∈ normalizer (D : Set G) :=
    hM (Subgroup.mem_inf.mpr ⟨t.x₂_mem_normalizer_pCoreOf_GT, t.x₂_mem_Gv_one⟩)
  have hτD : t.x₂ * t.x₁ ∈ normalizer (D : Set G) := Subgroup.mul_mem _ hx₂D hx₁D
  have hDGv0 : D ≤ t.Gv 0 := hDQv1.trans (t.Qv_le_Gv hfr 1).1
  have hDGv1 : D ≤ t.Gv 1 := hDQv1.trans (t.Qv_le_Gv_self 1)
  have hshift : ∀ i k : ℤ, D ≤ t.Gv i → D ≤ t.Gv (i + 2 * k) := by
    intro i k hD
    have hmap : D.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = D := by
      simpa [conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem hτD k))
    calc D = D.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := hmap.symm
      _ ≤ (t.Gv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := Subgroup.map_mono hD
      _ = t.Gv (i + 2 * k) := map_qv_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) i k
  have hDall : ∀ i : ℤ, D ≤ t.Gv i := by
    intro i
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
    · have := hshift 0 k hDGv0
      simpa using this
    · have := hshift 1 k hDGv1
      simpa [show 1 + 2 * k = 2 * k + 1 by ring] using this
  have hDGT : D ≤ t.GT := le_iInf hDall
  have hGTleMX : t.GT ≤ t.MX t.QT 1 :=
    le_inf (le_normalizer_pCoreOf 2 t.GT) (iInf_le _ 1)
  have hGTnormD : t.GT ≤ normalizer (D : Set G) := hGTleMX.trans hM
  exact le_antisymm (le_pCoreOf_of_le_normalizer 2 hDGT hGTnormD hD2) hQD

private theorem exists_sylow_imageOTwoQuot {L T : Subgroup G} (hT : IsSylowTwoOf T L) :
    ∃ S : Sylow 2 (oTwoQuot ↥L), (S : Subgroup (oTwoQuot ↥L)) = imageOTwoQuot L T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : pCoreOf 2 L ≤ T := hT.pCoreOf_le
  have hTq : IsSylowTwoOf (imageOTwoQuot L T) ⊤ := QA12.isSylowTwoOf_image_top hT hQ
  have hidx : ¬ 2 ∣ (imageOTwoQuot L T).index := by
    have heq : ((imageOTwoQuot L T).subgroupOf ⊤).index = (imageOTwoQuot L T).index := by
      have h1 := (Subgroup.relIndex_subgroupOf (H := imageOTwoQuot L T)
        (K := (⊤ : Subgroup (oTwoQuot ↥L))) (L := ⊤) le_rfl)
      simpa [Subgroup.subgroupOf_self] using h1
    intro h
    exact hTq.2.2 (heq.symm ▸ h)
  exact ⟨hTq.2.1.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

private theorem card_normalizer_imageOTwoQuot_l2 {L T : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    Nat.card (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))) =
      2 ^ f * (2 ^ f - 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  obtain ⟨e⟩ := hL2
  let U : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUcoe : (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))) =
      (imageOTwoQuot L T).map e.toMonoidHom := by
    have h := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
    simpa [U, hScoe] using h
  have hmap : (Subgroup.normalizer (imageOTwoQuot L T : Set (oTwoQuot ↥L))).map e.toMonoidHom =
      Subgroup.normalizer
        ((U : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))) : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, ← hUcoe]
  refine (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm.trans ?_
  rw [hmap]
  have hf1 : 1 ≤ f := le_trans (by norm_num) hf
  have hf0 : f ≠ 0 := Nat.one_le_iff_ne_zero.mp hf1
  exact CFSG.Walter.psl2_even_card_normalizer_sylow_two (f := f) hf0 U

private theorem inf_sup_le_sup_inf {L Q M : Subgroup G} (hLM : L ≤ M)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) :
    (L ⊔ Q) ⊓ M ≤ L ⊔ Q ⊓ M := by
  intro x hx
  obtain ⟨hxLQ, hxM⟩ := Subgroup.mem_inf.mp hx
  have hxQL : x ∈ Q ⊔ L := by rwa [sup_comm]
  obtain ⟨q, hq, l, hl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hLQ).mp hxQL
  have hqM : q ∈ M := by
    have : (q * l) * l⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem (hLM hl))
    simpa using this
  exact (L ⊔ Q ⊓ M).mul_mem
    (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hq, hqM⟩)) (Subgroup.mem_sup_left hl)

private theorem D2_le_LX {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ : t.ArcL t.QT) :
    t.D2 ≤ t.LX t.QT 1 := by
  have hD2K : t.D2 ≤ t.K := le_sup_right
  have hD2L2 : t.D2 ≤ L2 := t.hD2hall.1.trans (F1.borelOf_le L2 S)
  have hD2MX : t.D2 ≤ t.MX t.QT 1 :=
    hD2K.trans (le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv 1))
  have hcovL : L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1 := ArcL.L2_le_LX_sup_Qv_one t hfr hQ
  have hLMX : t.LX t.QT 1 ≤ t.MX t.QT 1 := oTwoPrime_le _
  have hMXQv : t.MX t.QT 1 ⊓ t.Qv 1 = t.EX t.QT 1 := by
    unfold Track.MX normIn Track.EX
    rw [inf_assoc, inf_eq_right.mpr (t.Qv_le_Gv_self 1), inf_comm]
  have hLN : t.LX t.QT 1 ≤ Subgroup.normalizer (t.Qv 1 : Set G) :=
    hLMX.trans (inf_le_right.trans (t.Gv_le_normalizer_Qv 1))
  have hmod : t.MX t.QT 1 ⊓ L2 ≤ t.LX t.QT 1 ⊔ t.MX t.QT 1 ⊓ t.Qv 1 := by
    calc t.MX t.QT 1 ⊓ L2 ≤ t.MX t.QT 1 ⊓ (t.LX t.QT 1 ⊔ t.Qv 1) :=
          inf_le_inf_left _ hcovL
      _ = (t.LX t.QT 1 ⊔ t.Qv 1) ⊓ t.MX t.QT 1 := inf_comm _ _
      _ ≤ t.LX t.QT 1 ⊔ t.Qv 1 ⊓ t.MX t.QT 1 :=
          inf_sup_le_sup_inf hLMX hLN
      _ = t.LX t.QT 1 ⊔ t.MX t.QT 1 ⊓ t.Qv 1 := by rw [inf_comm]
  have hEL : t.EX t.QT 1 ≤ t.LX t.QT 1 := by
    rw [← ArcL.pCoreOf_LX_one t hfr hQ]
    exact pCoreOf_le 2 _
  exact (le_inf hD2MX hD2L2).trans (hmod.trans (by rw [hMXQv]; exact sup_le le_rfl hEL))

private theorem K_le_normalizer_PX : t.K ≤ normalizer (t.PX t.QT : Set G) := by
  have hKQ : t.K ≤ normalizer (t.Qv 0 : Set G) := t.K_le_normalizer_Qv 0
  have hKMX : t.K ≤ normalizer (t.MX t.QT 1 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (t.MX t.QT 1) = t.MX t.QT 1
    have hQT : conjSub k t.QT = t.QT := by
      simpa [conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.K_le_normalizer_pCoreOf_GT hk))
    have hGv : conjSub k (t.Gv 1) = t.Gv 1 := by
      simpa [conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (t.K_le_Gv 1 hk)))
    unfold Track.MX normIn
    rw [conjSub_inf, ← conjSub_normalizer, hQT, hGv]
  intro k hk
  rw [Track.PX]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hKQ hk, hKMX hk⟩

private theorem K_le_normalizer_centerOf_PX :
    t.K ≤ Subgroup.normalizer (centerOf (t.PX t.QT) : Set G) := by
  have hKP : t.K ≤ Subgroup.normalizer (t.PX t.QT : Set G) := K_le_normalizer_PX t
  intro k hk
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hKP hk, (CFSG.Walter.Huppert.normalizer_le_normalizer_centralizer (t.PX t.QT)) (hKP hk)⟩

private theorem conjSub_PX_x₁ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : conjSub t.x₁ (t.PX t.QT) = t.PX t.QT := by
  have hQT : conjSub t.x₁ t.QT = t.QT := by
    simpa [conjSub] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp t.x₁_mem_normalizer_pCoreOf_GT)
  have hle : conjSub t.x₁ (t.PX t.QT) ≤ t.PX t.QT := by
    intro q hq
    set p : G := (MulAut.conj t.x₁).symm q with hpdef
    have hp : p ∈ t.PX t.QT := by
      simpa [hpdef] using (Subgroup.mem_map_equiv.mp hq)
    have hpq : (MulAut.conj t.x₁) p = q := by
      rw [hpdef, MulAut.conj_apply, MulAut.conj_symm_apply]
      group
    rw [← hpq]
    obtain ⟨hpQ, hpMX⟩ := Subgroup.mem_inf.mp hp
    obtain ⟨hpN, hpGv⟩ := Subgroup.mem_inf.mp hpMX
    have hpneg : p ∈ t.Gv (-1) := (t.Qv_le_Gv hfr 0).1 hpQ
    have hQ : (MulAut.conj t.x₁) p ∈ t.Qv 0 := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj t.x₁).toMonoidHom hpQ
      rwa [t.map_Qv_x₁ 0] at h
    have hN : (MulAut.conj t.x₁) p ∈ normalizer (t.QT : Set G) := by
      have h : (MulAut.conj t.x₁) p ∈ conjSub t.x₁ (normalizer (t.QT : Set G)) := by
        rw [mem_conjSub]
        change t.x₁⁻¹ * (t.x₁ * p * t.x₁⁻¹) * t.x₁ ∈ normalizer (t.QT : Set G)
        convert hpN using 1
        group
      rw [← conjSub_normalizer, hQT] at h
      exact h
    have hGv1 : (MulAut.conj t.x₁) p ∈ t.Gv 1 := by
      have h : (MulAut.conj t.x₁) p ∈ conjSub t.x₁ (t.Gv (-1)) := by
        rw [mem_conjSub]
        change t.x₁⁻¹ * (t.x₁ * p * t.x₁⁻¹) * t.x₁ ∈ t.Gv (-1)
        convert hpneg using 1
        group
      have hmap : conjSub t.x₁ (t.Gv (-1)) = t.Gv 1 := t.map_Gv_x₁ (-1)
      rwa [hmap] at h
    exact Subgroup.mem_inf.mpr ⟨hQ, Subgroup.mem_inf.mpr ⟨hN, hGv1⟩⟩
  have hcard : Nat.card ↥(conjSub t.x₁ (t.PX t.QT)) = Nat.card ↥(t.PX t.QT) := by
    simpa [conjSub] using Subgroup.card_map_of_injective
      (K := t.PX t.QT) (f := (MulAut.conj t.x₁).toMonoidHom) (MulAut.conj t.x₁).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

private theorem isSylowTwoOf_pX_LX_neg {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1)) :
    IsSylowTwoOf (t.PX t.QT) (t.LX t.QT (-1)) := by
  have hPle : t.PX t.QT ≤ t.LX t.QT 1 := hP.le
  have hLneg : t.LX t.QT (-1) = conjSub t.x₁ (t.LX t.QT 1) := (conjSub_LX_x₁ t 1).symm
  refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex ?_ hP.2.1 ?_
  · rw [hLneg]
    have hsub : conjSub t.x₁ (t.PX t.QT) ≤ conjSub t.x₁ (t.LX t.QT 1) :=
      Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hPle
    rwa [conjSub_PX_x₁ t hfr] at hsub
  · rw [hLneg, ← conjSub_PX_x₁ t hfr]
    change ¬ 2 ∣ (Subgroup.map (MulAut.conj t.x₁).toMonoidHom (t.PX t.QT)).relIndex
      (Subgroup.map (MulAut.conj t.x₁).toMonoidHom (t.LX t.QT 1))
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t.x₁).injective]
    exact hP.2.2

private theorem pCoreOf_LX_neg {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT) :
    pCoreOf 2 (t.LX t.QT (-1)) = t.EX t.QT (-1) := by
  have h := congrArg (conjSub t.x₁) (ArcL.pCoreOf_LX_one t hfr hQ)
  rw [conjSub_EX_x₁] at h
  rwa [← pCoreOf_conjSub, conjSub_LX_x₁] at h

private theorem D2_hall_pX {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ : t.ArcL t.QT)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1)) :
    HallTwoPrime t.D2 (t.LX t.QT 1 ⊓ normalizer (t.PX t.QT : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup G := t.LX t.QT 1 with hLdef
  set M : Subgroup G := L ⊓ normalizer (t.PX t.QT : Set G) with hMdef
  set Q : Subgroup G := pCoreOf 2 L with hQdef
  have hQeq : Q = t.EX t.QT 1 := by
    rw [hQdef, hLdef]
    exact ArcL.pCoreOf_LX_one t hfr hQ
  have hD2L : t.D2 ≤ L := D2_le_LX t hfr hQ
  have hD2M : t.D2 ≤ M := le_inf hD2L ((le_sup_right : t.D2 ≤ t.K).trans t.K_le_normalizer_PX)
  have hTL : t.PX t.QT ≤ L := hP.le
  have hQL : Q ≤ t.PX t.QT := hP.pCoreOf_le
  have hQM : Q ≤ M := le_inf (hQL.trans hTL) (hQL.trans Subgroup.le_normalizer)
  have hL2 : IsL2Quot f (oTwoQuot ↥L) := by
    rw [hLdef]
    exact ArcL.isL2Quot_LX_one t hfr hQ
  have hNcard := card_normalizer_imageOTwoQuot_l2 hfr.hf hL2 hP
  have hMcard := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul L M inf_le_left
  have hNimg : imageOTwoQuot L M =
      Subgroup.normalizer (imageOTwoQuot L (t.PX t.QT) : Set (oTwoQuot ↥L)) := by
    rw [hMdef]
    exact (CFSG.Quasithin.QA12.normalizer_image_eq hTL hQL).symm
  have hMQ : M ⊓ Q = Q := inf_eq_right.mpr hQM
  have hcardM : Nat.card ↥M = 2 ^ f * (2 ^ f - 1) * Nat.card ↥Q := by
    rw [hMcard, hNimg, hNcard, hMQ]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
    (show IsPGroup 2 (t.EX t.QT 1) from by
      rw [← ArcL.pCoreOf_LX_one t hfr hQ]; exact pCoreOf_isPGroup 2 _)
  have hrel := Subgroup.relIndex_mul_card (H := t.D2) (K := M)
  rw [inf_eq_left.mpr hD2M, t.card_D2 hfr, hcardM, hQeq, hm] at hrel
  have hrel' : t.D2.relIndex M * (2 ^ f - 1) = 2 ^ (f + m) * (2 ^ f - 1) := by
    rw [hrel, pow_add]
    ring
  change t.D2 ≤ M ∧ Odd (Nat.card t.D2) ∧ ∃ k, t.D2.relIndex M = 2 ^ k
  have hf2 : 2 ≤ f := hfr.hf
  have hf1 : 1 ≤ f := by omega
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hpos : 0 < 2 ^ f - 1 := by omega
  refine ⟨hD2M, t.hD2hall.2.1, ?_⟩
  exact ⟨f + m, Nat.eq_of_mul_eq_mul_right (n := t.D2.relIndex M) (m := 2 ^ f - 1)
    (k := 2 ^ (f + m)) hpos hrel'⟩

private theorem K_le_normalizer_sup_EX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hE : pCoreOf 2 (t.MX t.QT 1) = t.EX t.QT 1) :
    t.K ≤ normalizer ((t.EX t.QT 1 ⊔ t.EX t.QT (-1) : Subgroup G) : Set G) := by
  have hK1 : t.K ≤ normalizer (t.EX t.QT 1 : Set G) := by
    rw [← hE]
    exact (le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv 1)).trans
      (le_normalizer_pCoreOf 2 (t.MX t.QT 1))
  have hK2 : t.K ≤ normalizer (t.EX t.QT (-1) : Set G) := by
    rw [← pCoreOf_LX_neg t hfr hQ]
    have hKMX : t.K ≤ t.MX t.QT (-1) :=
      le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv (-1))
    exact hKMX.trans ((le_normalizer_oTwoPrime _).trans
      (normalizer_le_normalizer_pCoreOf 2 _))
  intro k hk
  exact CFSG.Walter.Huppert.mem_normalizer_sup (hK1 hk) (hK2 hk)

private theorem PX_eq_sup_EX {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ : t.ArcL t.QT)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT)
    (hE : pCoreOf 2 (t.MX t.QT 1) = t.EX t.QT 1) :
    t.PX t.QT = t.EX t.QT 1 ⊔ t.EX t.QT (-1) := by
  have hE2P : t.EX t.QT (-1) ≤ t.PX t.QT := by
    rw [← pCoreOf_LX_neg t hfr hQ]
    exact (isSylowTwoOf_pX_LX_neg t hfr hP).pCoreOf_le
  have hXT : t.EX t.QT 1 ⊔ t.EX t.QT (-1) ≤ t.PX t.QT := sup_le hEP hE2P
  have hL2 : IsL2Quot f (oTwoQuot ↥(t.LX t.QT 1)) :=
    ArcL.isL2Quot_LX_one t hfr hQ
  have hD : HallTwoPrime t.D2
      (t.LX t.QT 1 ⊓ normalizer (t.PX t.QT : Set G)) := D2_hall_pX t hfr hQ hP
  have hXD : t.D2 ≤ normalizer ((t.EX t.QT 1 ⊔ t.EX t.QT (-1) : Subgroup G) : Set G) :=
    (le_sup_right : t.D2 ≤ t.K).trans (K_le_normalizer_sup_EX t hfr hQ hE)
  have hX : ¬ t.EX t.QT 1 ⊔ t.EX t.QT (-1) ≤ pCoreOf 2 (t.LX t.QT 1) := by
    intro hle
    have hcore : pCoreOf 2 (t.LX t.QT 1) = t.EX t.QT 1 := ArcL.pCoreOf_LX_one t hfr hQ
    have hE2leE : t.EX t.QT (-1) ≤ t.EX t.QT 1 :=
      le_sup_right.trans (hle.trans (le_of_eq hcore))
    have hcard : Nat.card ↥(t.EX t.QT (-1)) = Nat.card ↥(t.EX t.QT 1) := by
      rw [show t.EX t.QT (-1) = conjSub t.x₁ (t.EX t.QT 1) from (conjSub_EX_x₁ t 1).symm]
      simpa [conjSub] using Subgroup.card_map_of_injective
        (K := t.EX t.QT 1) (f := (MulAut.conj t.x₁).toMonoidHom)
        (MulAut.conj t.x₁).injective
    have hEeq : t.EX t.QT (-1) = t.EX t.QT 1 :=
      Subgroup.eq_of_le_of_card_ge hE2leE (le_of_eq hcard.symm)
    exact t.EX_QT_ne hfr hQ hE hEeq.symm
  refine le_antisymm ?_ hXT
  have h := le_sup_pCoreOf_of_torus_of_l2 hfr.hf hL2 hP hD hXT hXD hX
  have hsup : (t.EX t.QT 1 ⊔ t.EX t.QT (-1)) ⊔ t.EX t.QT 1 =
      t.EX t.QT 1 ⊔ t.EX t.QT (-1) := sup_eq_left.mpr le_sup_left
  rwa [ArcL.pCoreOf_LX_one t hfr hQ, hsup] at h

private theorem MX_one_le_normalizer_centerOf :
    t.MX t.QT 1 ≤ normalizer (centerOf (t.LX t.QT 1) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub m (centerOf (t.LX t.QT 1)) = centerOf (t.LX t.QT 1)
  have hmL : m ∈ normalizer (t.LX t.QT 1 : Set G) := le_normalizer_oTwoPrime _ hm
  have hmap : conjSub m (t.LX t.QT 1) = t.LX t.QT 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmL
  rw [← CFSG.Quasithin.H13.F431.L3.centerOf_conjSub, hmap]

private theorem MX_neg_one_le_normalizer_centerOf :
    t.MX t.QT (-1) ≤ normalizer (centerOf (t.LX t.QT (-1)) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub m (centerOf (t.LX t.QT (-1))) = centerOf (t.LX t.QT (-1))
  have hmL : m ∈ normalizer (t.LX t.QT (-1) : Set G) := le_normalizer_oTwoPrime _ hm
  have hmap : conjSub m (t.LX t.QT (-1)) = t.LX t.QT (-1) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmL
  rw [← CFSG.Quasithin.H13.F431.L3.centerOf_conjSub, hmap]

private theorem conjSub_centerOf_of_swap {s : G} (hs0 : s ∈ t.MX t.QT 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    conjSub s (centerOf (t.LX t.QT 1)) = centerOf (t.LX t.QT (-1)) ∧
      conjSub s (centerOf (t.LX t.QT (-1))) = centerOf (t.LX t.QT 1) := by
  set u : G := t.x₁⁻¹ * s with hudef
  have hsN : s ∈ normalizer (t.QT : Set G) := hs0.1
  have huN : u ∈ normalizer (t.QT : Set G) :=
    Subgroup.mul_mem _ ((Subgroup.normalizer _).inv_mem t.x₁_mem_normalizer_pCoreOf_GT) hsN
  have huMX1 : u ∈ t.MX t.QT 1 := Subgroup.mem_inf.mpr ⟨huN, hs.1⟩
  have huMXneg : u ∈ t.MX t.QT (-1) := Subgroup.mem_inf.mpr ⟨huN, hs.2⟩
  have hsu : s = t.x₁ * u := by rw [hudef]; group
  have huA : conjSub u (centerOf (t.LX t.QT 1)) = centerOf (t.LX t.QT 1) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (MX_one_le_normalizer_centerOf t huMX1)
  have huA2 : conjSub u (centerOf (t.LX t.QT (-1))) = centerOf (t.LX t.QT (-1)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (MX_neg_one_le_normalizer_centerOf t huMXneg)
  constructor
  · rw [hsu, conjSub_mul, huA]
    exact (map_centerOf_LX_x₁ t).1
  · rw [hsu, conjSub_mul, huA2]
    exact (map_centerOf_LX_x₁ t).2

private theorem centerOf_LX_neg_le_EX_neg {f : ℕ}
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f) :
    centerOf (t.LX t.QT (-1)) ≤ t.EX t.QT (-1) := by
  have hA2 : centerOf (t.LX t.QT (-1)) =
      conjSub t.x₁ (centerOf (t.LX t.QT 1)) := (map_centerOf_LX_x₁ t).1.symm
  have hE2 : t.EX t.QT (-1) = conjSub t.x₁ (t.EX t.QT 1) := (conjSub_EX_x₁ t 1).symm
  rw [hA2, hE2]
  exact conjSub_mono t.x₁ hnat.Z_le

private theorem card_image_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1)) :
    Nat.card ↥(imageOTwoQuot (t.LX t.QT 1) (t.PX t.QT)) = 2 ^ f := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup G := t.LX t.QT 1
  have hf2 : 2 ≤ f := hfr.hf
  have hP' : IsSylowTwoOf (t.PX t.QT) L := hP
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hP'
  obtain ⟨e⟩ := ArcL.isL2Quot_LX_one t hfr hQ
  let U : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUcard : Nat.card ↥(U : Subgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))) = 2 ^ f :=
    CFSG.Quasithin.St84.psl2_sylow_two_card (by omega : 1 ≤ f) U
  have hUS : Nat.card ↥(U : Subgroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))) =
      Nat.card ↥(S : Subgroup (oTwoQuot ↥L)) := by
    rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S]
    exact Subgroup.card_map_of_injective (K := (S : Subgroup (oTwoQuot ↥L)))
      (f := e.toMonoidHom) e.injective
  rw [← hScoe]
  exact hUS.symm.trans hUcard

private theorem card_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT) :
    Nat.card ↥(t.PX t.QT) = 2 ^ f * Nat.card ↥(t.EX t.QT 1) := by
  have hcardimg := card_image_PX t hfr hQ hP
  have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul
    (t.LX t.QT 1) (t.PX t.QT) hP.le
  rwa [hcardimg, show pCoreOf 2 (t.LX t.QT 1) = t.EX t.QT 1 from
    ArcL.pCoreOf_LX_one t hfr hQ, inf_eq_right.mpr hEP] at h

private theorem inf_EX_EX_neg_le_centralizer_PX
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hPX : t.PX t.QT = t.EX t.QT 1 ⊔ t.EX t.QT (-1)) :
    t.EX t.QT 1 ⊓ t.EX t.QT (-1) ≤ centralizer (t.PX t.QT : Set G) := by
  have hEcent : t.EX t.QT 1 ≤ Subgroup.centralizer (t.EX t.QT 1 : Set G) := by
    letI := hab.1
    exact Subgroup.le_centralizer (H := t.EX t.QT 1)
  have hE2cent : t.EX t.QT (-1) ≤ Subgroup.centralizer (t.EX t.QT (-1) : Set G) := by
    rw [show t.EX t.QT (-1) = conjSub t.x₁ (t.EX t.QT 1) from (conjSub_EX_x₁ t 1).symm]
    have h := conjSub_mono t.x₁ hEcent
    rwa [← conjSub_centralizer] at h
  have hE : t.EX t.QT 1 ≤ Subgroup.centralizer
      (t.EX t.QT 1 ⊓ t.EX t.QT (-1) : Subgroup G) :=
    hEcent.trans (Subgroup.centralizer_le fun _ hd => (Subgroup.mem_inf.mp hd).1)
  have hE2 : t.EX t.QT (-1) ≤ Subgroup.centralizer
      (t.EX t.QT 1 ⊓ t.EX t.QT (-1) : Subgroup G) :=
    hE2cent.trans (Subgroup.centralizer_le fun _ hd => (Subgroup.mem_inf.mp hd).2)
  have hPle : t.PX t.QT ≤ Subgroup.centralizer
      (t.EX t.QT 1 ⊓ t.EX t.QT (-1) : Subgroup G) := by
    rw [hPX]
    exact sup_le hE hE2
  exact (Subgroup.le_centralizer_iff (H := t.EX t.QT 1 ⊓ t.EX t.QT (-1))
    (K := t.PX t.QT)).mpr hPle

private theorem inf_EX_EX_neg_le_relCent {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT) :
    t.EX t.QT 1 ⊓ t.EX t.QT (-1) ≤
      St84.relCent (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) (t.PX t.QT) := by
  have hEcoreMX : pCoreOf 2 (t.MX t.QT 1) = t.EX t.QT 1 := ArcL.pCoreOf_MX_one t hfr hQ
  have hPX := PX_eq_sup_EX t hfr hQ hP hEP hEcoreMX
  have hDcentP := inf_EX_EX_neg_le_centralizer_PX t hab hPX
  have hEA : t.EX t.QT 1 ≤ Subgroup.normalizer (centerOf (t.LX t.QT 1) : Set G) := fun e he =>
    (hnat.normal (hnat.E_le he)).2
  intro d hd
  refine (St84.mem_relCent hEA).mpr ⟨(Subgroup.mem_inf.mp hd).1, fun p hp => ?_⟩
  have hcomm : p * d = d * p := (Subgroup.mem_centralizer_iff.mp (hDcentP hd)) p hp
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
  exact (centerOf (t.LX t.QT 1)).one_mem

private theorem card_inf_EX_EX_neg {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT) :
    Nat.card ↥(t.EX t.QT 1 ⊓ t.EX t.QT (-1)) =
      2 ^ f * Nat.card ↥(centerOf (t.LX t.QT 1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup G := t.EX t.QT 1
  let E2 : Subgroup G := t.EX t.QT (-1)
  let A : Subgroup G := centerOf (t.LX t.QT 1)
  let D : Subgroup G := E ⊓ E2
  have hEcoreMX : pCoreOf 2 (t.MX t.QT 1) = E := by
    rw [show E = t.EX t.QT 1 from rfl]
    exact ArcL.pCoreOf_MX_one t hfr hQ
  have hPeq : t.PX t.QT = E ⊔ E2 := PX_eq_sup_EX t hfr hQ hP hEP hEcoreMX
  have hPleQv0 : t.PX t.QT ≤ t.Qv 0 := by
    change t.Qv 0 ⊓ t.MX t.QT 1 ≤ t.Qv 0
    exact inf_le_left
  have hPMXneg : t.PX t.QT ≤ t.MX t.QT (-1) := by
    refine le_inf ?_ ?_
    · exact (show t.Qv 0 ⊓ t.MX t.QT 1 ≤ t.MX t.QT 1 from inf_le_right).trans inf_le_left
    · exact hPleQv0.trans (t.Qv_le_Gv hfr 0).1
  have hE2coreMX : E2 = pCoreOf 2 (t.MX t.QT (-1)) := by
    have h := congrArg (conjSub t.x₁) hEcoreMX
    rw [← pCoreOf_conjSub, conjSub_MX_x₁, conjSub_EX_x₁] at h
    exact h.symm
  have hEN : E ≤ Subgroup.normalizer (E2 : Set G) :=
    hEP.trans (hPMXneg.trans (by rw [hE2coreMX]; exact le_normalizer_pCoreOf 2 _))
  have hprod := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := E) (K := E2) hEN
  have hE2card : Nat.card ↥E2 = Nat.card ↥E := by
    rw [show E2 = conjSub t.x₁ E from (conjSub_EX_x₁ t 1).symm]
    exact CFSG.Quasithin.H13.F431.L3.card_conjSub t.x₁ E
  rw [← hPeq, hE2card, card_PX t hfr hQ hP hEP] at hprod
  have hDrel : 2 ^ f * Nat.card ↥D = Nat.card ↥E := by
    have h1 : (2 ^ f * Nat.card ↥D) * Nat.card ↥E = Nat.card ↥E * Nat.card ↥E := by
      calc (2 ^ f * Nat.card ↥D) * Nat.card ↥E = (2 ^ f * Nat.card ↥E) * Nat.card ↥D := by ring
        _ = Nat.card ↥E * Nat.card ↥E := hprod
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hEidx : Nat.card ↥E = 2 ^ (2 * f) * Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := E)
    rw [inf_eq_left.mpr hnat.Z_le, hnat.index] at h
    exact h.symm
  have h2f : 2 ^ (2 * f) = 2 ^ f * 2 ^ f := by
    rw [show 2 * f = f + f by omega, pow_add]
  rw [hEidx, h2f, mul_assoc] at hDrel
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ f) hDrel

private theorem inf_EX_EX_neg_eq_relCent {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT) :
    t.EX t.QT 1 ⊓ t.EX t.QT (-1) =
      St84.relCent (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) (t.PX t.QT) := by
  let E : Subgroup G := t.EX t.QT 1
  let A : Subgroup G := centerOf (t.LX t.QT 1)
  have hDcard := card_inf_EX_EX_neg t hfr hQ hnat hP hEP
  have hA_le_rel : A ≤ St84.relCent E A (t.PX t.QT) := by
    intro a ha
    refine (St84.mem_relCent ?_).mpr ⟨hnat.Z_le ha, fun p hp => ?_⟩
    · exact fun e he => (hnat.normal (hnat.E_le he)).2
    · have hcent : a ∈ Subgroup.centralizer (t.LX t.QT 1 : Set G) := (Subgroup.mem_inf.mp ha).2
      rw [show ⁅a, p⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hcent p (hP.le hp)).symm)]
      exact A.one_mem
  have hline : Nat.card ↥(St84.relCent E A (t.PX t.QT)) = 2 ^ f * Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := St84.relCent E A (t.PX t.QT))
    rw [inf_eq_left.mpr hA_le_rel, hnat.line (t.PX t.QT) hP] at h
    exact h.symm
  have hDle := inf_EX_EX_neg_le_relCent t hfr hQ hab hnat hP hEP
  refine Subgroup.eq_of_le_of_card_ge hDle ?_
  rw [hline, hDcard]

private theorem centralizer_EX_le_EX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f) :
    t.LX t.QT 1 ⊓ centralizer (t.EX t.QT 1 : Set G) ≤ t.EX t.QT 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup G := t.LX t.QT 1
  let E : Subgroup G := t.EX t.QT 1
  let C : Subgroup G := L ⊓ centralizer (E : Set G)
  have hLE : E ≤ L := by
    rw [show E = pCoreOf 2 L from (ArcL.pCoreOf_LX_one t hfr hQ).symm]
    exact pCoreOf_le 2 L
  have hEC : E ≤ C := le_inf hLE (by letI := hab.1; exact Subgroup.le_centralizer (H := E))
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := by
    have hLE' : L ≤ Subgroup.normalizer (E : Set G) := by
      have h := le_normalizer_pCoreOf 2 L
      rwa [show pCoreOf 2 L = E from ArcL.pCoreOf_LX_one t hfr hQ] at h
    have hLcen : L ≤ Subgroup.normalizer (centralizer (E : Set G) : Set G) :=
      hLE'.trans (CFSG.Walter.Huppert.normalizer_le_normalizer_centralizer E)
    exact fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hLcen hl⟩
  haveI hCnormal : (C.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLC
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  haveI : IsSimpleGroup (oTwoQuot ↥L) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hfr.hf
      (by rw [show L = t.LX t.QT 1 from rfl]; exact ArcL.isL2Quot_LX_one t hfr hQ)
  haveI hN : ((C.subgroupOf L).map π).Normal :=
    hCnormal.map π (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((C.subgroupOf L).map π) with hbot | htop
  · intro c hc
    have hcsub : (⟨c, (Subgroup.mem_inf.mp hc).1⟩ : ↥L) ∈ C.subgroupOf L := hc
    have hker := (Subgroup.map_eq_bot_iff (C.subgroupOf L)).mp hbot hcsub
    rw [show π.ker = pCore 2 ↥L from QuotientGroup.ker_mk' _,
      ← CFSG.openPCoreOf_subgroupOf 2 L] at hker
    simpa [E, ← ArcL.pCoreOf_LX_one t hfr hQ] using Subgroup.mem_subgroupOf.mp hker
  · exfalso
    have hCL : C = L :=
      (CFSG.Quasithin.Stroth.map_oTwoQuot_subgroupOf_eq_top_iff inf_le_left
        (by rwa [ArcL.pCoreOf_LX_one t hfr hQ])).mp htop
    have hAE : E ≤ centerOf L :=
      le_inf hLE ((Subgroup.le_centralizer_iff).mp (by rw [← hCL]; exact inf_le_right))
    have hAeqE : centerOf L = E := le_antisymm hnat.Z_le hAE
    have hidx := hnat.index
    rw [hAeqE, Subgroup.relIndex_self] at hidx
    exact (Nat.one_lt_two_pow (Nat.mul_ne_zero (by norm_num)
      (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num) hfr.hf)))).ne' hidx.symm

private theorem centerOf_inf_centerOf_eq_QT {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hZ : t.QT ≤ centerOf (t.LX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f) :
    centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) = t.QT := by
  have hA2_le : centerOf (t.LX t.QT (-1)) ≤ t.EX t.QT (-1) :=
    centerOf_LX_neg_le_EX_neg t hnat
  have hQD : t.QT ≤ centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) := by
    refine le_inf hZ ?_
    have hQx : conjSub t.x₁ t.QT = t.QT := by
      simpa [conjSub] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp t.x₁_mem_normalizer_pCoreOf_GT)
    have hconj : conjSub t.x₁ (centerOf (t.LX t.QT 1)) = centerOf (t.LX t.QT (-1)) :=
      (map_centerOf_LX_x₁ t).1
    have h := conjSub_mono t.x₁ hZ
    rwa [hQx, hconj] at h
  have hDE : centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) ≤
      t.EX t.QT 1 ⊓ t.EX t.QT (-1) :=
    inf_le_inf hnat.Z_le hA2_le
  have hM : t.MX t.QT 1 ≤
      normalizer ((centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) : Subgroup G) : Set G) := by
    have hAL : centerOf (t.LX t.QT 1) ≤ Subgroup.centralizer (t.LX t.QT 1 : Set G) := inf_le_right
    have hLC : t.LX t.QT 1 ≤ Subgroup.centralizer (centerOf (t.LX t.QT 1) : Set G) :=
      (Subgroup.le_centralizer_iff).mpr hAL
    have hLD : t.LX t.QT 1 ≤ normalizer
        ((centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) : Subgroup G) : Set G) :=
      hLC.trans ((Subgroup.centralizer_le (by
        intro d hd; exact (Subgroup.mem_inf.mp hd).1)).trans
          (Subgroup.centralizer_le_normalizer _))
    have hKA : t.K ≤ normalizer (centerOf (t.LX t.QT 1) : Set G) :=
      (le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv 1)).trans
        (MX_one_le_normalizer_centerOf t)
    have hKA2 : t.K ≤ normalizer (centerOf (t.LX t.QT (-1)) : Set G) :=
      (le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv (-1))).trans
        (MX_neg_one_le_normalizer_centerOf t)
    have hKD : t.K ≤ normalizer
        ((centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) : Subgroup G) : Set G) := fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKA hk, hKA2 hk⟩
    rw [ArcL.MX_one_eq_sup t hfr hQ]
    exact sup_le hLD hKD
  obtain ⟨s, hs0, hs⟩ := hQ.swap
  have hsD : s ∈ normalizer
      ((centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub s (centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1))) =
      centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1))
    have hswap := conjSub_centerOf_of_swap t hs0 hs
    rw [conjSub_inf, hswap.1, hswap.2, inf_comm]
  exact t.eq_QT_of_normal hfr hQD hDE hM hs0 hs hsD

private theorem inf_EX_EX_neg_eq_centerOf_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT)
    (hPX : t.PX t.QT = t.EX t.QT 1 ⊔ t.EX t.QT (-1)) :
    t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT) := by
  have hE2P : t.EX t.QT (-1) ≤ t.PX t.QT := by
    rw [← pCoreOf_LX_neg t hfr hQ]
    exact (isSylowTwoOf_pX_LX_neg t hfr hP).pCoreOf_le
  have hDleP : t.EX t.QT 1 ⊓ t.EX t.QT (-1) ≤ t.PX t.QT :=
    inf_le_left.trans hEP
  have hDcent : t.EX t.QT 1 ⊓ t.EX t.QT (-1) ≤
      centralizer (t.PX t.QT : Set G) :=
    inf_EX_EX_neg_le_centralizer_PX t hab hPX
  have hZP_E : centerOf (t.PX t.QT) ≤ t.EX t.QT 1 := by
    refine (le_inf ?_ ?_).trans (centralizer_EX_le_EX t hfr hQ hab hnat)
    · exact (inf_le_left : centerOf (t.PX t.QT) ≤ t.PX t.QT).trans hP.le
    · exact (inf_le_right : centerOf (t.PX t.QT) ≤
        Subgroup.centralizer (t.PX t.QT : Set G)).trans
        (Subgroup.centralizer_le (show (t.EX t.QT 1 : Set G) ⊆ t.PX t.QT from hEP))
  have hZmap : conjSub t.x₁ (centerOf (t.PX t.QT)) = centerOf (t.PX t.QT) := by
    rw [← CFSG.Quasithin.H13.F431.L3.centerOf_conjSub, conjSub_PX_x₁ t hfr]
  have hZP_E2 : centerOf (t.PX t.QT) ≤ t.EX t.QT (-1) := by
    calc centerOf (t.PX t.QT) = conjSub t.x₁ (centerOf (t.PX t.QT)) := hZmap.symm
      _ ≤ conjSub t.x₁ (t.EX t.QT 1) := conjSub_mono t.x₁ hZP_E
      _ = t.EX t.QT (-1) := conjSub_EX_x₁ t 1
  refine le_antisymm ?_ ?_
  · intro d hd
    exact Subgroup.mem_inf.mpr ⟨hDleP hd, hDcent hd⟩
  · intro z hz
    exact Subgroup.mem_inf.mpr ⟨hZP_E hz, hZP_E2 hz⟩

private theorem relIndex_inf_EX_EX_neg {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT) :
    (t.EX t.QT 1 ⊓ t.EX t.QT (-1)).relIndex (t.EX t.QT 1) = 2 ^ f := by
  let E : Subgroup G := t.EX t.QT 1
  let E2 : Subgroup G := t.EX t.QT (-1)
  let A : Subgroup G := centerOf (t.LX t.QT 1)
  let D : Subgroup G := E ⊓ E2
  have hDrel : D = St84.relCent E A (t.PX t.QT) :=
    inf_EX_EX_neg_eq_relCent t hfr hQ hab hnat hP hEP
  have hAD : A.relIndex D = 2 ^ f := by
    have h := hnat.line (t.PX t.QT) hP
    rwa [← hDrel] at h
  have hAleD : A ≤ D := by
    intro a ha
    rw [hDrel]
    refine (St84.mem_relCent (E := E) (Z := A) (A := t.PX t.QT) ?_).mpr
      ⟨hnat.Z_le ha, ?_⟩
    · exact fun e he => (hnat.normal (hnat.E_le he)).2
    · intro p hp
      have hcent : a ∈ Subgroup.centralizer (t.LX t.QT 1 : Set G) := (Subgroup.mem_inf.mp ha).2
      rw [show ⁅a, p⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hcent p (hP.le hp)).symm)]
      exact A.one_mem
  have hmul := Subgroup.relIndex_mul_relIndex (H := A) (K := D)
    (L := t.EX t.QT 1) hAleD (show D ≤ t.EX t.QT 1 from inf_le_left)
  rw [hAD, hnat.index] at hmul
  have h2 : 2 ^ (2 * f) = 2 ^ f * 2 ^ f := by
    rw [show 2 * f = f + f by omega, pow_add]
  rw [h2] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ f) hmul

private theorem sup_centerOf_le_centerOf_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT) :
    centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ≤ centerOf (t.PX t.QT) := by
  have hA2_le : centerOf (t.LX t.QT (-1)) ≤ t.EX t.QT (-1) :=
    centerOf_LX_neg_le_EX_neg t hnat
  have hE2P : t.EX t.QT (-1) ≤ t.PX t.QT := by
    rw [← pCoreOf_LX_neg t hfr hQ]
    exact (isSylowTwoOf_pX_LX_neg t hfr hP).pCoreOf_le
  have hPneg : t.PX t.QT ≤ t.LX t.QT (-1) := (isSylowTwoOf_pX_LX_neg t hfr hP).le
  refine sup_le ?_ ?_
  · intro a ha
    refine Subgroup.mem_inf.mpr ⟨hEP (hnat.Z_le ha), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hcent : a ∈ Subgroup.centralizer (t.LX t.QT 1 : Set G) := (Subgroup.mem_inf.mp ha).2
    exact (Subgroup.mem_centralizer_iff.mp hcent) p (hP.le hp)
  · intro a ha
    refine Subgroup.mem_inf.mpr ⟨hE2P (hA2_le ha), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hcent : a ∈ Subgroup.centralizer (t.LX t.QT (-1) : Set G) := (Subgroup.mem_inf.mp ha).2
    exact (Subgroup.mem_centralizer_iff.mp hcent) p (hPneg hp)

private theorem Zv_zero_le_centerOf_PX (hZ0 : t.Zv 0 ≤ normIn t.QT (t.Gw (-1) 1)) :
    t.Zv 0 ≤ centerOf (t.PX t.QT) := by
  have hN : t.Zv 0 ≤ Subgroup.normalizer (t.QT : Set G) := hZ0.trans inf_le_left
  have hGw : t.Zv 0 ≤ t.Gw (-1) 1 := hZ0.trans inf_le_right
  have hGv1 : t.Zv 0 ≤ t.Gv 1 :=
    fun z hz => mem_win_iff.mp (hGw hz) 1 (by norm_num) le_rfl
  have hP : t.Zv 0 ≤ t.PX t.QT := le_inf (t.Zv_le_Qv 0) (le_inf hN hGv1)
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨hP hz, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  exact (Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hz)) p
    (Subgroup.mem_inf.mp hp).1

theorem residue_facts {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ : t.ArcL t.QT) (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hZ : t.QT ≤ centerOf (t.LX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1)) (hEP : t.EX t.QT 1 ≤ t.PX t.QT)
    (hE : pCoreOf 2 (t.MX t.QT 1) = t.EX t.QT 1)

    (hZ0 : t.Zv 0 ≤ normIn t.QT (t.Gw (-1) 1)) :
    t.QT = centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) ∧
      t.PX t.QT = t.EX t.QT 1 ⊔ t.EX t.QT (-1) ∧
      t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT) ∧
      (t.EX t.QT 1 ⊓ t.EX t.QT (-1)).relIndex (t.EX t.QT 1) = 2 ^ f ∧
      centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ≤ centerOf (t.PX t.QT) ∧
      t.Zv 0 ≤ centerOf (t.PX t.QT) := by
  have hAint := centerOf_inf_centerOf_eq_QT t hfr hQ hZ hnat
  have hPX := PX_eq_sup_EX t hfr hQ hP hEP hE
  exact ⟨hAint.symm, hPX,
    inf_EX_EX_neg_eq_centerOf_PX t hfr hQ hab hnat hP hEP hPX,
    relIndex_inf_EX_EX_neg t hfr hQ hab hnat hP hEP,
    sup_centerOf_le_centerOf_PX t hfr hQ hnat hP hEP,
    Zv_zero_le_centerOf_PX t hZ0⟩

private theorem exists_ne_one_D2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : ∃ k ∈ t.D2, k ≠ 1 := by
  have hcard : Nat.card t.D2 = 2 ^ f - 1 := t.card_D2 hfr
  have hgt : 1 < Nat.card t.D2 := by
    rw [hcard]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
    omega
  have hne : t.D2 ≠ ⊥ := by
    intro hbot
    rw [hbot] at hgt
    have h1 : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
    rw [h1] at hgt
    omega
  obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨(k : G), k.2, fun h => hk (Subtype.ext h)⟩

private theorem D2_fixed_points {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hD2 : t.D2 ≤ t.YX t.QT 1) :
    ∀ k ∈ t.D2, k ≠ 1 → ∀ e ∈ t.EX t.QT 1,
      ⁅e, k⁆ ∈ centerOf (t.LX t.QT 1) → e ∈ centerOf (t.LX t.QT 1) := by
  intro k hk hk1 e he hcomm
  have hkL : k ∈ t.LX t.QT 1 := (oTwoRes_le (t.LX t.QT 1)) (hD2 hk)
  have hdvd : orderOf k ∣ 2 ^ f - 1 := by
    rw [← t.card_D2 hfr]
    exact Subgroup.orderOf_dvd_natCard t.D2 hk
  have hodd : Odd (orderOf k) := by
    refine Odd.of_dvd_nat ?_ hdvd
    have hf2 : 2 ≤ f := hfr.hf
    have heven : Even (2 ^ f) := by
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd (one_le_pow₀ one_le_two) heven odd_one
  have hkE : k ∉ t.EX t.QT 1 := by
    intro hkE
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (show IsPGroup 2 (t.EX t.QT 1) from
      (t.isPGroup_Qv 1).to_le inf_le_left).exists_orderOf_eq_pow ⟨k, hkE⟩
    have hkord : orderOf k = 2 ^ n := (Subgroup.orderOf_mk k hkE).symm.trans hn
    have hn0 : n = 0 := by
      by_contra hn0
      have heven : Even (2 ^ n) := by
        simpa [Nat.even_pow, hn0] using even_two
      rw [← hkord] at heven
      exact Nat.not_even_iff_odd.mpr hodd heven
    exact hk1 (orderOf_eq_one_iff.mp (by rw [hkord, hn0, pow_zero]))
  exact hnat.fpf k hkL hodd hkE e he hcomm

private theorem centerOf_LX_relIndex_centerOf_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEE : t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT)) :
    (centerOf (t.LX t.QT 1)).relIndex (centerOf (t.PX t.QT)) = 2 ^ f := by
  have hEP : t.EX t.QT 1 ≤ t.PX t.QT := ArcL.EX_one_le_pX t hfr hQ
  have h := hnat.line (t.PX t.QT) hP
  rw [← inf_EX_EX_neg_eq_relCent t hfr hQ hab hnat hP hEP, hEE] at h
  exact h

private theorem card_centerOf_LX_neg_eq_centerOf_LX :
    Nat.card (centerOf (t.LX t.QT (-1))) = Nat.card (centerOf (t.LX t.QT 1)) := by
  rw [show centerOf (t.LX t.QT (-1)) = conjSub t.x₁ (centerOf (t.LX t.QT 1)) from
    (map_centerOf_LX_x₁ t).1.symm]
  exact CFSG.Quasithin.H13.F431.L3.card_conjSub t.x₁ (centerOf (t.LX t.QT 1))

private theorem D2_le_normalizer_centerOf_LX_neg :
    t.D2 ≤ Subgroup.normalizer (centerOf (t.LX t.QT (-1)) : Set G) := by
  have hK : t.K ≤ Subgroup.normalizer (centerOf (t.LX t.QT (-1)) : Set G) :=
    (le_inf t.K_le_normalizer_pCoreOf_GT (t.K_le_Gv (-1))).trans
      (MX_neg_one_le_normalizer_centerOf t)
  exact (le_sup_right : t.D2 ≤ t.K).trans hK

private theorem commutator_EX_PX_le_centerOf_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEE : t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT)) :
    ⁅t.EX t.QT 1, t.PX t.QT⁆ ≤ centerOf (t.PX t.QT) := by
  have hEP : t.EX t.QT 1 ≤ t.PX t.QT := ArcL.EX_one_le_pX t hfr hQ
  have hrel : St84.relCent (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) (t.PX t.QT) =
      centerOf (t.PX t.QT) := by
    rw [← inf_EX_EX_neg_eq_relCent t hfr hQ hab hnat hP hEP, hEE]
  have h := hnat.comm_eq (t.PX t.QT) hP
  rw [hrel] at h
  exact le_sup_left.trans h.le

private theorem relIndex_EX_PX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hEP : t.EX t.QT 1 ≤ t.PX t.QT) :
    (t.EX t.QT 1).relIndex (t.PX t.QT) = 2 ^ f := by
  have hcard := card_PX t hfr hQ hP hEP
  have hrel := Subgroup.relIndex_mul_card (H := t.EX t.QT 1) (K := t.PX t.QT)
  rw [inf_eq_left.mpr hEP, hcard] at hrel
  haveI : Nonempty ↥(t.EX t.QT 1) := ⟨1, (t.EX t.QT 1).one_mem⟩
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel

private theorem D2_transitive_on_centerOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hEE : t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT))
    (hAZ : centerOf (t.LX t.QT 1) ≤ centerOf (t.PX t.QT))
    (hDZ : t.D2 ≤ Subgroup.normalizer (centerOf (t.PX t.QT) : Set G))
    (hDA : t.D2 ≤ Subgroup.normalizer (centerOf (t.LX t.QT 1) : Set G))
    (hfpf : ∀ k ∈ t.D2, k ≠ 1 → ∀ e ∈ t.EX t.QT 1,
      ⁅e, k⁆ ∈ centerOf (t.LX t.QT 1) → e ∈ centerOf (t.LX t.QT 1))
    (hrelA : (centerOf (t.LX t.QT 1)).relIndex (centerOf (t.PX t.QT)) = 2 ^ f) :
    ∀ x ∈ centerOf (t.PX t.QT), x ∉ centerOf (t.LX t.QT 1) →
      ∀ y ∈ centerOf (t.PX t.QT), y ∉ centerOf (t.LX t.QT 1) →
        ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ centerOf (t.LX t.QT 1) := by
  have hAP : ∀ a ∈ t.D2, ∀ x ∈ centerOf (t.PX t.QT),
      a * x * a⁻¹ ∈ centerOf (t.PX t.QT) :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hDZ ha) x).mp hx
  have hAN : ∀ a ∈ t.D2, ∀ x ∈ centerOf (t.LX t.QT 1),
      a * x * a⁻¹ ∈ centerOf (t.LX t.QT 1) :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hDA ha) x).mp hx
  have hfree : ∀ a ∈ t.D2, a ≠ 1 → ∀ x ∈ centerOf (t.PX t.QT),
      x⁻¹ * (a * x * a⁻¹) ∈ centerOf (t.LX t.QT 1) → x ∈ centerOf (t.LX t.QT 1) := by
    intro a ha ha1 x hxP hx
    have hxE : x ∈ t.EX t.QT 1 := (Subgroup.mem_inf.mp (hEE ▸ hxP)).1
    have haxP : a * x * a⁻¹ ∈ centerOf (t.PX t.QT) := hAP a ha x hxP
    have hcomm : x⁻¹ * (a * x * a⁻¹) = a * x * a⁻¹ * x⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haxP).2) x⁻¹
        ((t.PX t.QT).inv_mem (Subgroup.mem_inf.mp hxP).1)
    rw [hcomm] at hx
    refine hfpf a ha ha1 x hxE ?_
    rw [show ⁅x, a⁆ = (a * x * a⁻¹ * x⁻¹)⁻¹ from by
      rw [commutatorElement_def]
      group]
    exact (centerOf (t.LX t.QT 1)).inv_mem hx
  have hidx : ((centerOf (t.LX t.QT 1)).subgroupOf (centerOf (t.PX t.QT))).index = 2 ^ f :=
    hrelA
  have hcard : Nat.card t.D2 =
      ((centerOf (t.LX t.QT 1)).subgroupOf (centerOf (t.PX t.QT))).index - 1 := by
    rw [hidx, t.card_D2 hfr]
  intro x hx hxA y hy hyA
  obtain ⟨a, ha, hconj⟩ :=
    CFSG.GH74.Uniqueness.trans_of_free_of_card (A := t.D2)
      (P := centerOf (t.PX t.QT)) (N := centerOf (t.LX t.QT 1))
      hAZ hAP hAN hfree hcard x hx hxA y hy hyA
  refine ⟨a, ha, ?_⟩
  have hayP : a * x * a⁻¹ ∈ centerOf (t.PX t.QT) := hAP a ha x hx
  have hcomm : y⁻¹ * (a * x * a⁻¹) = a * x * a⁻¹ * y⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hayP).2) y⁻¹
      ((t.PX t.QT).inv_mem (Subgroup.mem_inf.mp hy).1)
  rwa [← hcomm]

private theorem caseI_or_caseII_core {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hD2 : t.D2 ≤ t.YX t.QT 1) (h0 : t.Zv 0 ⊓ t.QT = ⊥) (h1 : t.Zv 1 ⊓ t.QT = ⊥)
    (hEE : t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT))
    (hQZ : t.QT ≤ centerOf (t.PX t.QT)) (hZ0 : t.Zv 0 ≤ centerOf (t.PX t.QT))
    (hidxP : (t.EX t.QT 1).relIndex (t.PX t.QT) = 2 ^ f)
    (hcomm : ⁅t.EX t.QT 1, t.PX t.QT⁆ ≤ centerOf (t.PX t.QT))
    (hfpf : ∀ k ∈ t.D2, k ≠ 1 → ∀ e ∈ t.EX t.QT 1,
      ⁅e, k⁆ ∈ centerOf (t.LX t.QT 1) → e ∈ centerOf (t.LX t.QT 1))
    (htr : ∀ x ∈ centerOf (t.PX t.QT), x ∉ centerOf (t.LX t.QT 1) →
      ∀ y ∈ centerOf (t.PX t.QT), y ∉ centerOf (t.LX t.QT 1) →
        ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ centerOf (t.LX t.QT 1))
    (hQA : t.QT = centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)))
    (hAZ : centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ≤ centerOf (t.PX t.QT))
    (hrelA : (centerOf (t.LX t.QT 1)).relIndex (centerOf (t.PX t.QT)) = 2 ^ f)
    (hcard : Nat.card (centerOf (t.LX t.QT (-1))) = Nat.card (centerOf (t.LX t.QT 1)))
    (hDA2 : t.D2 ≤ Subgroup.normalizer (centerOf (t.LX t.QT (-1)) : Set G)) :
    (centerOf (t.LX t.QT 1) = t.QT ∧ t.EX t.QT 1 ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ t.QT ∧
      t.Zv 0 ≤ t.Zv 1 ∧ (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) ∧
      (∀ e ∈ t.EX t.QT 1, (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → l * e * l⁻¹ = e) →
        e ∈ t.QT)) ∨
    (t.Zv 0 ≤ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ∧
      t.QT.relIndex (centerOf (t.LX t.QT 1)) = 2 ^ f ∧
      (∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ centerOf (t.LX t.QT (-1)),
        k * x * k⁻¹ * x⁻¹ ∈ t.QT → x ∈ t.QT) ∧
      (∀ x ∈ centerOf (t.LX t.QT (-1)), x ∉ t.QT →
        ∀ y ∈ centerOf (t.LX t.QT (-1)), y ∉ t.QT → ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ t.QT)) := by
  rcases t.centerOf_LX_eq_QT_or_caseII hQA hEE hAZ hZ0 hrelA hcard hDA2 hfpf htr with hA | h
  · exact Or.inl ⟨hA, t.caseI_of_centerOf_LX_eq_QT hfr hnat hD2 h0 h1
      (Zv_one_le_EX t hfr) hEE hQZ hZ0 hidxP hcomm hA hfpf htr⟩
  · exact Or.inr h

theorem caseI_or_caseII {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ : t.ArcL t.QT) (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hP : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1))
    (hD2 : t.D2 ≤ t.YX t.QT 1) (h0 : t.Zv 0 ⊓ t.QT = ⊥) (h1 : t.Zv 1 ⊓ t.QT = ⊥)
    (hres : t.QT = centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) ∧
      t.PX t.QT = t.EX t.QT 1 ⊔ t.EX t.QT (-1) ∧
      t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT) ∧
      (t.EX t.QT 1 ⊓ t.EX t.QT (-1)).relIndex (t.EX t.QT 1) = 2 ^ f ∧
      centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ≤ centerOf (t.PX t.QT) ∧
      t.Zv 0 ≤ centerOf (t.PX t.QT)) :
    (centerOf (t.LX t.QT 1) = t.QT ∧ t.EX t.QT 1 ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ t.QT ∧
      t.Zv 0 ≤ t.Zv 1 ∧ (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) ∧
      (∀ e ∈ t.EX t.QT 1, (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → l * e * l⁻¹ = e) →
        e ∈ t.QT)) ∨
    (t.Zv 0 ≤ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ∧
      t.QT.relIndex (centerOf (t.LX t.QT 1)) = 2 ^ f ∧
      (∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ centerOf (t.LX t.QT (-1)),
        k * x * k⁻¹ * x⁻¹ ∈ t.QT → x ∈ t.QT) ∧
      (∀ x ∈ centerOf (t.LX t.QT (-1)), x ∉ t.QT →
        ∀ y ∈ centerOf (t.LX t.QT (-1)), y ∉ t.QT → ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ t.QT)) := by
  obtain ⟨hQA, -, hEE, -, hAZ, hZ0⟩ := hres
  have hrelA : (centerOf (t.LX t.QT 1)).relIndex (centerOf (t.PX t.QT)) = 2 ^ f :=
    centerOf_LX_relIndex_centerOf_PX t hfr hQ hab hnat hP hEE
  have hcard : Nat.card (centerOf (t.LX t.QT (-1))) = Nat.card (centerOf (t.LX t.QT 1)) :=
    card_centerOf_LX_neg_eq_centerOf_LX t
  have hDA2 : t.D2 ≤ Subgroup.normalizer (centerOf (t.LX t.QT (-1)) : Set G) :=
    D2_le_normalizer_centerOf_LX_neg t
  have hDZ : t.D2 ≤ Subgroup.normalizer (centerOf (t.PX t.QT) : Set G) :=
    (le_sup_right : t.D2 ≤ t.K).trans (K_le_normalizer_centerOf_PX t)
  have hDA : t.D2 ≤ Subgroup.normalizer (centerOf (t.LX t.QT 1) : Set G) :=
    (le_sup_right : t.D2 ≤ t.K).trans (K_le_normalizer_centerOf_LX t)
  have hfpf : ∀ k ∈ t.D2, k ≠ 1 → ∀ e ∈ t.EX t.QT 1,
      ⁅e, k⁆ ∈ centerOf (t.LX t.QT 1) → e ∈ centerOf (t.LX t.QT 1) :=
    D2_fixed_points t hfr hnat hD2
  have htr := D2_transitive_on_centerOf t hfr hEE (le_sup_left.trans hAZ)
    hDZ hDA hfpf hrelA
  have hQZ : t.QT ≤ centerOf (t.PX t.QT) :=
    (hQA.le.trans inf_le_left).trans (le_sup_left.trans hAZ)
  have hidxP : (t.EX t.QT 1).relIndex (t.PX t.QT) = 2 ^ f :=
    relIndex_EX_PX t hfr hQ hP (ArcL.EX_one_le_pX t hfr hQ)
  have hcomm : ⁅t.EX t.QT 1, t.PX t.QT⁆ ≤ centerOf (t.PX t.QT) :=
    commutator_EX_PX_le_centerOf_PX t hfr hQ hab hnat hP hEE
  exact caseI_or_caseII_core t hfr hnat hD2 h0 h1 hEE hQZ hZ0 hidxP hcomm hfpf htr
    hQA hAZ hrelA hcard hDA2

end Track

end CFSG.Quasithin.Stroth.Rq

end
