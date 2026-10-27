module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Smear

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot

open AChief

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G X : Subgroup Γ}

theorem sol_qimg_sol (G : Subgroup Γ) : sol (qimg (sol G) G) = ⊥ := by
  rw [sol_qimg (isSolvable_sol G) (le_nrm_sol G)]
  exact qimg_self

@[expose] noncomputable def quotSolEquiv (G : Subgroup Γ) :
    ↥G ⧸ CFSG.solvableRadical ↥G ≃* ↥(qimg (sol G) G) :=
  have hker : (qres (sol G) G (le_nrm_sol G)).ker = CFSG.solvableRadical ↥G := by
    rw [ker_qres, subgroupOf_sol]
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (qres (sol G) G (le_nrm_sol G))
      (qres_surjective (le_nrm_sol G)))

omit [Finite Γ] in
theorem quotSolEquiv_mk (G : Subgroup Γ) (g : ↥G) :
    ((quotSolEquiv G (QuotientGroup.mk g) : ↥(qimg (sol G) G)) : QG (sol G)) =
      qmap (sol G) ⟨g, le_nrm_sol G g.2⟩ := rfl

theorem sol_qimg_sol_of_le (hX : X ≤ G) : sol (qimg (sol G) X) = qimg (sol G) (sol X) :=
  sol_qimg (isSolvable_sol G) (hX.trans (le_nrm_sol G))

theorem mem_mcal_iff_qimg_mem_lcal (hXG : X ≤ G) (hX : sol G ≤ X) :
    X ∈ mcal G ↔ qimg (sol G) X ∈ lcal (qimg (sol G) G) := by
  rw [← mcal_eq_lcal_of_sol_eq_bot (sol_qimg_sol G),
    qimg_mem_mcal_iff (isSolvable_sol G) (le_nrm_sol G) hXG hX]

theorem bijOn_mcal_sol (G : Subgroup Γ) :
    Set.BijOn (qimg (sol G)) (mcal G) (lcal (qimg (sol G) G)) := by
  have h := bijOn_mcal (isSolvable_sol G) (le_nrm_sol G)
  rwa [mcal_eq_lcal_of_sol_eq_bot (sol_qimg_sol G)] at h

theorem bijOn_ltilde_sol (G : Subgroup Γ) :
    Set.BijOn (qimg (sol G)) (ltilde G) (ltilde (qimg (sol G) G)) :=
  bijOn_ltilde (isSolvable_sol G) (le_nrm_sol G)

theorem qpre_mem_mcal {J : Subgroup (QG (sol G))} (hJ : J ∈ lcal (qimg (sol G) G)) :
    qpre (sol G) J ∈ mcal G ∧ qimg (sol G) (qpre (sol G) J) = J := by
  obtain ⟨M, hM, rfl⟩ := (bijOn_mcal_sol G).surjOn hJ
  rw [qpre_qimg (hM.1.trans (le_nrm_sol G)), sup_eq_left.mpr hM.2.1]
  exact ⟨hM, rfl⟩

theorem kOf_qimg_sol (hX : X ≤ G) : kOf (qimg (sol G) X) = qimg (sol G) (kOf X) :=
  kOf_qimg (isSolvable_sol G) (hX.trans (le_nrm_sol G))

theorem kOf_eq_qpre_sol (G : Subgroup Γ) :
    kOf G = qpre (sol G) (kOf (qimg (sol G) G)) := by
  rw [kOf_qimg_sol le_rfl, qpre_qimg ((kOf_le G).trans (le_nrm_sol G)),
    sup_eq_left.mpr (sol_le_kOf G)]

omit [Finite Γ] in
private theorem sol_le_khat (X : Subgroup Γ) : sol X ≤ khat X := by
  rw [khat_eq_mcal]
  exact le_sup_right

theorem khat_qimg_sol (hX : X ≤ G) : khat (qimg (sol G) X) = qimg (sol G) (khat X) :=
  khat_qimg (isSolvable_sol G) (hX.trans (le_nrm_sol G))

theorem khat_eq_qpre_sol (G : Subgroup Γ) :
    khat G = qpre (sol G) (khat (qimg (sol G) G)) := by
  rw [khat_qimg_sol le_rfl, qpre_qimg ((khat_le G).trans (le_nrm_sol G)),
    sup_eq_left.mpr (sol_le_khat G)]

theorem qSetting_of_kSetting {R : Subgroup Γ} (h : KSetting p A G) (hR : Group.IsSolvable R)
    (hG : G ≤ nrm R) (hA : A ≤ nrm R) : QSetting p R A G where
  prime := h.prime
  solvable := hR
  elemAbelian := h.elemAbelian
  normalizes := h.normalizes
  coprime := (signalizerMcBrideHypothesisB_iff.mp h.hypB).2.1
  le_nrm_G := hG
  le_nrm_A := hA

theorem qSetting_sol (h : KSetting p A G) : QSetting p (sol G) A G :=
  qSetting_of_kSetting h (isSolvable_sol G) (le_nrm_sol G)
    (h.normalizes.trans (normalizer_le_nrm_sol G))

theorem kSetting_qimg {R : Subgroup Γ} (h : KSetting p A G) (hG : G ≤ nrm R) :
    KSetting p (qimg R A) (qimg R G) where
  prime := h.prime
  elemAbelian := isElemAbelian_qimg h.elemAbelian
  normalizes := qimg_le_normalizer h.normalizes
  hypB := hypB_qimg hG h.hypB

theorem kSetting_qimg_sol (h : KSetting p A G) :
    KSetting p (qimg (sol G) A) (qimg (sol G) G) :=
  kSetting_qimg h (le_nrm_sol G)

omit [Finite Γ] in
theorem QSetting.qimg_inf_centralizer {R : Subgroup Γ} (h : QSetting p R A G) {Y : Subgroup Γ}
    (hYG : Y ≤ G) (hAY : A ≤ Subgroup.normalizer (Y : Set Γ)) :
    qimg R (Y ⊓ Subgroup.centralizer (A : Set Γ)) =
      qimg R Y ⊓ Subgroup.centralizer ((qimg R A : Subgroup (QG R)) : Set (QG R)) :=
  AChief.qimg_inf_centralizer h.prime h.elemAbelian hAY h.le_nrm_A (hYG.trans h.le_nrm_G)
    (h.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYG))

omit [Finite Γ] in
theorem QSetting.isSolvable_qimg_inf_centralizer_iff {R : Subgroup Γ} (h : QSetting p R A G)
    {X : Subgroup Γ} (hXG : X ≤ G) (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) :
    Group.IsSolvable (qimg R X ⊓ Subgroup.centralizer ((qimg R A : Subgroup (QG R)) : Set (QG R)) :
        Subgroup (QG R)) ↔
      Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set Γ) : Subgroup Γ) := by
  rw [← h.qimg_inf_centralizer hXG hAX]
  exact isSolvable_qimg_iff h.solvable ((inf_le_left.trans hXG).trans h.le_nrm_G)

theorem isDAInvariant_qimg {R : Subgroup Γ} (h : KSetting p A G) (hG : G ≤ nrm R)
    (hA : A ≤ nrm R) (hX : IsDAInvariant A G X) :
    IsDAInvariant (qimg R A) (qimg R G) (qimg R X) := by
  refine ⟨qimg_mono hX.1, ?_, qimg_le_normalizer hX.2.2⟩
  have hcop : Nat.Coprime p (Nat.card G) := (signalizerMcBrideHypothesisB_iff.mp h.hypB).2.1
  rw [← AChief.qimg_inf_centralizer h.prime h.elemAbelian h.normalizes hA hG hcop]
  exact qimg_le_normalizer hX.2.1

theorem isDAInvariant_qimg_sol (h : KSetting p A G) (hX : IsDAInvariant A G X) :
    IsDAInvariant (qimg (sol G) A) (qimg (sol G) G) (qimg (sol G) X) :=
  isDAInvariant_qimg h (le_nrm_sol G) (h.normalizes.trans (normalizer_le_nrm_sol G)) hX

omit [Finite Γ] in
theorem qimg_le_normalizer_iff_sol {J : Subgroup Γ} (hJ : J ∈ mcal G) (hX : X ≤ G) :
    qimg (sol G) X ≤ Subgroup.normalizer (qimg (sol G) J : Set (QG (sol G))) ↔
      X ≤ Subgroup.normalizer (J : Set Γ) :=
  qimg_le_normalizer_iff hJ.1 ((inf_le_right (a := G)).trans hJ.2.1) (le_nrm_sol G) hX

theorem mem_mcalA_iff_qimg_mem_lcalA (h : KSetting p A G) {J : Subgroup Γ} (hJ : J ∈ mcal G) :
    J ∈ mcalA G A ↔ qimg (sol G) J ∈ lcalA (qimg (sol G) G) (qimg (sol G) A) := by
  have : mcalA (qimg (sol G) G) (qimg (sol G) A) = lcalA (qimg (sol G) G) (qimg (sol G) A) := by
    unfold mcalA lcalA
    rw [mcal_eq_lcal_of_sol_eq_bot (sol_qimg_sol G)]
  rw [← this, mem_mcalA_qimg_iff (qSetting_sol h) hJ]

theorem le_kDown_of_qimg_le_sol (h : KSetting p A G) (hX : X ≤ G)
    (hle : qimg (sol G) X ≤ kDown (qimg (sol G) G) (qimg (sol G) A)) : X ≤ kDown G A :=
  le_kDown_of_qimg_le (qSetting_sol h) le_rfl hX hle

theorem kDown_qimg_sol (h : KSetting p A G) :
    kDown (qimg (sol G) G) (qimg (sol G) A) = qimg (sol G) (kDown G A) :=
  kDown_qimg (qSetting_sol h) le_rfl

theorem kUp_qimg_sol (h : KSetting p A G) :
    kUp (qimg (sol G) G) (qimg (sol G) A) = qimg (sol G) (kUp G A) :=
  kUp_qimg (qSetting_sol h)

theorem le_normalizer_kUp_iff_sol (h : KSetting p A G) (hX : X ≤ G) :
    qimg (sol G) X ≤
        Subgroup.normalizer (kUp (qimg (sol G) G) (qimg (sol G) A) : Set (QG (sol G))) ↔
      X ≤ Subgroup.normalizer (kUp G A : Set Γ) :=
  le_normalizer_kUp_iff (qSetting_sol h) hX

theorem exists_mem_kUp_of_qimg_sol (h : KSetting p A G) (hX : X ≤ G)
    (hbar : ∀ z ∈ qimg (sol G) X, ∃ w ∈ kUp (qimg (sol G) G) (qimg (sol G) A),
      w⁻¹ * z ∈ kDown (qimg (sol G) G) (qimg (sol G) A)) :
    ∀ x ∈ X, ∃ y ∈ kUp G A, y⁻¹ * x ∈ kDown G A :=
  exists_mem_kUp_of_qimg (qSetting_sol h) le_rfl hX hbar

theorem qimg_inf_centralizer_sol (h : KSetting p A G) :
    qimg (sol G) (G ⊓ Subgroup.centralizer (A : Set Γ)) =
      qimg (sol G) G ⊓ Subgroup.centralizer ((qimg (sol G) A : Subgroup (QG (sol G))) :
        Set (QG (sol G))) :=
  (qSetting_sol h).qimg_inf_centralizer le_rfl h.normalizes

omit [Finite Γ] in
theorem QSetting.qimg_inf_centralizer_singleton {R : Subgroup Γ} (h : QSetting p R A G) {a : Γ}
    (ha : a ∈ A) :
    qimg R (G ⊓ Subgroup.centralizer {a}) =
      qimg R G ⊓ Subgroup.centralizer {qmap R ⟨a, h.le_nrm_A ha⟩} := by
  have h' := h.mono_left (Subgroup.zpowers_le.mpr ha)
  have hn : Subgroup.zpowers a ≤ Subgroup.normalizer (G : Set Γ) :=
    (Subgroup.zpowers_le.mpr ha).trans h.normalizes
  have := h'.qimg_inf_centralizer (Y := G) le_rfl hn
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure,
    qimg_zpowers (h.le_nrm_A ha), Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    at this

theorem QSetting.kOf_qimg_inf_centralizer {R : Subgroup Γ} (h : QSetting p R A G) {a : Γ}
    (ha : a ∈ A) :
    kOf (qimg R G ⊓ Subgroup.centralizer {qmap R ⟨a, h.le_nrm_A ha⟩}) =
      qimg R (kOf (G ⊓ Subgroup.centralizer {a})) := by
  rw [← h.qimg_inf_centralizer_singleton ha]
  exact kOf_qimg h.solvable (inf_le_left.trans h.le_nrm_G)

theorem QSetting.qimg_iSup_kOf_inf_centralizer {R : Subgroup Γ} (h : QSetting p R A G)
    (hRG : R ≤ G) :
    qimg R (⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a})) =
      ⨆ (b : QG R) (_ : b ∈ qimg R A) (_ : b ≠ 1),
        kOf (qimg R G ⊓ Subgroup.centralizer {b}) := by
  have hle : ∀ a : Γ, kOf (G ⊓ Subgroup.centralizer {a}) ≤ nrm R := fun a =>
    (kOf_le _).trans (inf_le_left.trans h.le_nrm_G)
  apply le_antisymm
  · rw [qimg_le_iff (iSup_le fun a => iSup_le fun _ => iSup_le fun _ => hle a)]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    rw [← qimg_le_iff (hle a), ← h.kOf_qimg_inf_centralizer ha]
    exact le_iSup_of_le (qmap R ⟨a, h.le_nrm_A ha⟩) (le_iSup_of_le
      ((mem_qimg_iff R A _).mpr ⟨⟨a, h.le_nrm_A ha⟩, ha, rfl⟩)
      (le_iSup_of_le (h.qmap_ne_one hRG ha ha1) le_rfl))
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    obtain ⟨y, hy, rfl⟩ := (mem_qimg_iff R A b).mp hb
    have hy1 : (y : Γ) ≠ 1 := fun h1 => hb1 (by rw [show y = 1 from Subtype.ext h1, map_one])
    rw [h.kOf_qimg_inf_centralizer hy]
    exact qimg_mono (le_iSup_of_le (y : Γ) (le_iSup_of_le hy (le_iSup_of_le hy1 le_rfl)))

theorem kOf_le_sup_sol (h : KSetting p A G)
    (hbar : kOf (qimg (sol G) G) ≤ ⨆ (b : QG (sol G)) (_ : b ∈ qimg (sol G) A) (_ : b ≠ 1),
      kOf (qimg (sol G) G ⊓ Subgroup.centralizer {b})) :
    kOf G ≤ (⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a})) ⊔
      sol G := by
  have hL : (⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a})) ≤ G :=
    iSup_le fun a => iSup_le fun _ => iSup_le fun _ => (kOf_le _).trans inf_le_left
  calc kOf G = qpre (sol G) (kOf (qimg (sol G) G)) := kOf_eq_qpre_sol G
    _ ≤ qpre (sol G) (qimg (sol G)
        (⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a}))) :=
      qpre_mono (hbar.trans (le_of_eq ((qSetting_sol h).qimg_iSup_kOf_inf_centralizer
        (sol_le G)).symm))
    _ = _ := qpre_qimg (hL.trans (le_nrm_sol G))

theorem sol_inf_centralizer_le_kOf (G : Subgroup Γ) (a : Γ) :
    sol G ⊓ Subgroup.centralizer {a} ≤ kOf (G ⊓ Subgroup.centralizer {a}) := by
  have hY : G ⊓ Subgroup.centralizer {a} ≤ nrm (sol G) := inf_le_left.trans (le_nrm_sol G)
  refine le_trans (fun x hx => ?_) (sol_le_kOf _)
  exact inf_le_sol (isSolvable_sol G) hY
    (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨sol_le G hx.1, hx.2⟩, hx.1⟩)

theorem sol_le_iSup_kOf (h : KSetting p A G) (hrank : p ^ 2 ≤ Nat.card A) :
    sol G ≤ ⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a}) := by
  have hq := qSetting_sol h
  have hgen := iSup_centralizer_nonidentity h.prime h.elemAbelian hrank hq.le_nrm_A
    (hq.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (sol_le G)))
  calc sol G = ⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), sol G ⊓ Subgroup.centralizer {a} := hgen.symm
    _ ≤ _ := iSup_mono fun a => iSup_mono fun _ => iSup_mono fun _ =>
      sol_inf_centralizer_le_kOf G a

theorem kOf_le_iSup_kOf (h : KSetting p A G) (hrank : p ^ 2 ≤ Nat.card A)
    (hbar : kOf (qimg (sol G) G) ≤ ⨆ (b : QG (sol G)) (_ : b ∈ qimg (sol G) A) (_ : b ≠ 1),
      kOf (qimg (sol G) G ⊓ Subgroup.centralizer {b})) :
    kOf G ≤ ⨆ (a : Γ) (_ : a ∈ A) (_ : a ≠ 1), kOf (G ⊓ Subgroup.centralizer {a}) :=
  (kOf_le_sup_sol h hbar).trans (sup_le le_rfl (sol_le_iSup_kOf h hrank))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
