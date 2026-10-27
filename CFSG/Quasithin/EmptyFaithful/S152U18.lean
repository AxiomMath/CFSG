module

public import CFSG.Quasithin.EmptyFaithful.S152UStruct
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_of_forall_le_normalizer {S I : Subgroup G} (hSI : S ≤ I) (hS : IsPGroup 2 S)
    (h : ∀ Q : Subgroup G, S ≤ Q → Q ≤ I → IsPGroup 2 Q →
      Q ≤ Subgroup.normalizer (S : Set G) → Q ≤ S) : IsSylowTwoOf S I := by
  obtain ⟨P, hP, hSP⟩ := EscapingLocal.exists_isSylowTwoOf_ge hSI hS
  have hSP' : S = P := by
    by_contra hne
    obtain ⟨x, hxP, hxS, hxN⟩ :=
      exists_mem_normalizer_not_mem_of_lt hP.2.1 (lt_of_le_of_ne hSP hne)
    have hQP : S ⊔ Subgroup.zpowers x ≤ P := sup_le hSP (Subgroup.zpowers_le.mpr hxP)
    have hQ := h (S ⊔ Subgroup.zpowers x) le_sup_left (hQP.trans hP.1) (hP.2.1.to_le hQP)
      (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN))
    exact hxS (hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  rwa [hSP']

omit [Finite G] in
theorem cgsIn_le_CGS (H S : Subgroup G) : cgsIn H S ≤ CGS S :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => inf_le_right

omit [Finite G] in
theorem oTwoUpper_eq_bot_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) : oTwoUpper P = ⊥ :=
  le_bot_iff.mp (oTwoUpper_le_of_pow_mem fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    exact ⟨k, Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hk)⟩)

omit [Finite G] in
theorem mem_of_mem_preOn_autOn {M V X N : Subgroup G} (hXM : X ≤ M) (hXN : X ≤ N)
    (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ N) {x : G}
    (hx : x ∈ preOn M V (autOn X V)) : x ∈ N := by
  obtain ⟨hxM, hxV, hxa⟩ := mem_preOn.mp hx
  obtain ⟨y, hyV, hyX, hy⟩ := mem_autOn_iff_exists.mp hxa
  have hc : y⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := (conjAct_eq_iff hyV hxV).mp hy
  have hcM : y⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (hXM hyX)) hxM
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact N.mul_mem (hXN hyX) (hC ⟨hcM, hc⟩)

theorem mem_normalizer_of_commutes {A : Type*} [Group A] {B : Subgroup A} {t : A}
    (ht : ∀ b ∈ B, t * b = b * t) : t ∈ Subgroup.normalizer (B : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : t * h * t⁻¹ = h := by rw [ht h hh]; group
    rw [this]
    exact hh
  · intro hx
    have h1 := ht _ hx
    have h2 : t * h * t⁻¹ = h := by
      have : t * (t * h * t⁻¹) = (t * h * t⁻¹) * t := h1
      have h3 : t * t * h * t⁻¹ = t * h := by
        calc t * t * h * t⁻¹ = (t * (t * h * t⁻¹)) * t⁻¹ * t := by group
          _ = ((t * h * t⁻¹) * t) * t⁻¹ * t := by rw [this]
          _ = t * h := by group
      calc t * h * t⁻¹ = t⁻¹ * (t * t * h * t⁻¹) := by group
        _ = t⁻¹ * (t * h) := by rw [h3]
        _ = h := by group
    rw [← h2]
    exact hx

section Main

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem T_le_normalizer_S152 (hD : Inputs152 T Mc M H B₀ I) :
    T ≤ Subgroup.normalizer (sOf152 T Mc M B₀ : Set G) := by
  have : ((sOf152 T Mc M B₀).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hD.h17.2.2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer S_le_T152).mp this

theorem isSylowTwoOf_S152 (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hB₀ : IsB0 T Mc M B₀) (hI : Hyp15215 T Mc M B₀ I) (hD : Inputs152 T Mc M H B₀ I)
    (hOm : Om4FactsStatement) : IsSylowTwoOf (sOf152 T Mc M B₀) I := by
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  refine isSylowTwoOf_of_forall_le_normalizer (S_le_I152 hD) (hs.qtfe.sylow.1.to_le S_le_T152) ?_
  intro Q hSQ hQI hQ2 hQN
  have hQM : Q ≤ M := hQN.trans (normalizer_S_le_M152 hs hD)
  have hQV : Q ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hQM.trans hMV
  have hSV : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    (S_le_T152.trans hTM).trans hMV
  have hCvN : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer' Subgroup.le_normalizer hMV
  have hsylCv : IsSylowTwoOf (T ⊓ (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))
      (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
    isSylowTwoOf_inf_of_le_normalizer (isSylowTwoOf_of_le151 hs.qtfe.sylow hTM) inf_le_left hCvN
  intro q hq
  have hqM : q ∈ M := hQM hq
  have hqV : q ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hMV hqM
  have hq1 : conjAct (V154 T Mc M) ⟨q, hqV⟩ ∈ Subgroup.normalizer
      (autOn (sOf152 T Mc M B₀) (V154 T Mc M) : Set (MulAut (V154 T Mc M))) :=
    autOn_le_normalizer_autOn hQV hSV hQN (mem_autOn_of_mem hqV hq)
  have hq2 : conjAct (V154 T Mc M) ⟨q, hqV⟩ ∈ autOn M (V154 T Mc M) := mem_autOn_of_mem hqV hqM
  have hq3 := normalizer_autS_le_autT hs hB₀ hD hOm _ hq2 hq1
  obtain ⟨t, htV, htT, hteq⟩ := mem_autOn_iff_exists.mp hq3
  have hc : t⁻¹ * q ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
    (conjAct_eq_iff htV hqV).mp hteq
  have hcM : t⁻¹ * q ∈ M := M.mul_mem (M.inv_mem (hTM htT)) hqM
  have hcI : t⁻¹ * q ∈ I := (cv_le_inf152 hs hD ⟨hcM, hc⟩).2
  have htI : t ∈ I := by
    have : t = q * (t⁻¹ * q)⁻¹ := by group
    rw [this]
    exact I.mul_mem (hQI hq) (I.inv_mem hcI)
  have htS : t ∈ sOf152 T Mc M B₀ := by
    rw [← inf_T_I152 hs hH hI hD]
    exact ⟨htT, htI⟩
  have hcQ : t⁻¹ * q ∈ Q := Q.mul_mem (Q.inv_mem (hSQ htS)) hq
  have hcT : t⁻¹ * q ∈ T ⊓ (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    have hTCQ : T ⊓ (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ≤ Q := fun x hx =>
      hSQ (inf_centralizer_le_S152 hs B₀ ⟨hx.1, hx.2.2⟩)
    have := inf_eq_of_isSylowTwoOf_of_le hsylCv hQ2 hTCQ
    rw [← this]
    exact ⟨hcQ, hcM, hc⟩
  have hcS : t⁻¹ * q ∈ sOf152 T Mc M B₀ := inf_centralizer_le_S152 hs B₀ ⟨hcT.1, hcT.2.2⟩
  have : q = t * (t⁻¹ * q) := by group
  rw [this]
  exact (sOf152 T Mc M B₀).mul_mem htS hcS

theorem baum_eq152 (hD : Inputs152 T Mc M H B₀ I) : baum T = baum (sOf152 T Mc M B₀) :=
  baum_eq_of_le hD.h14.baum_le S_le_T152

theorem cgs_le152 (hD : Inputs152 T Mc M H B₀ I) : cgsIn I (baum T) ≤ M ⊓ I :=
  le_inf ((cgsIn_le_CGS _ _).trans hD.h159.one_cgs) (cgsIn_le _ _)

theorem oTwoUpper_le_cv_of_le_Mc (hs : Setting152 T Mc M) (hD : Inputs152 T Mc M H B₀ I)
    {Y : Subgroup G} (hYM : Y ≤ M) (hYMc : Y ≤ Mc) :
    oTwoUpper Y ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hinf : M ⊓ Mc = (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T :=
    hD.h14.inf_eq.1.trans hD.h14.inf_eq.2
  have hY : Y ≤ (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T := hinf ▸ le_inf hYM hYMc
  have hCvV : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤
      Subgroup.normalizer (V154 T Mc M : Set G) := inf_le_left.trans hMV
  have hCv0 : autOn (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) (V154 T Mc M) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨x, hxV, hxC, rfl⟩ := mem_autOn_iff_exists.mp hφ
    rw [Subgroup.mem_bot]
    exact A4.conjAct_eq_one_iff.mpr hxC.2
  have h1 : autOn Y (V154 T Mc M) ≤ autOn T (V154 T Mc M) := by
    calc autOn Y (V154 T Mc M)
        ≤ autOn ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T) (V154 T Mc M) :=
          A4.autOn_mono hY
      _ = autOn (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) (V154 T Mc M) ⊔
            autOn T (V154 T Mc M) := autOn_sup hCvV (hTM.trans hMV)
      _ = autOn T (V154 T Mc M) := by rw [hCv0, bot_sup_eq]
  have hYV : Y ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hYM.trans hMV
  have h2 : autOn (oTwoUpper Y) (V154 T Mc M) = ⊥ := by
    rw [← A4.oTwoUpper_autOn hYV]
    exact le_bot_iff.mp ((oTwoUpper_mono h1).trans
      (oTwoUpper_eq_bot_of_isPGroup (isPGroup_autOn hs.qtfe.sylow.1 (hTM.trans hMV))).le)
  refine le_inf ((oTwoUpper_le Y).trans hYM) ?_
  by_contra hcon
  exact autOn_ne_bot_of_not_le_centralizer ((oTwoUpper_le Y).trans hYV) hcon h2

theorem not_normal_oTwoUpper152 (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hI : Hyp15215 T Mc M B₀ I) (hD : Inputs152 T Mc M H B₀ I)
    (hSyl : IsSylowTwoOf (sOf152 T Mc M B₀) I)
    (hX : ¬ oTwoUpper (M ⊓ I) ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :
    ¬ ∀ g ∈ autOn M (V154 T Mc M), ∀ y ∈ autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M),
      g * y * g⁻¹ ∈ autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) := by
  intro hnorm
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hXM : oTwoUpper (M ⊓ I) ≤ M := (oTwoUpper_le _).trans inf_le_left
  have hXI : oTwoUpper (M ⊓ I) ≤ I := (oTwoUpper_le _).trans inf_le_right
  have hCvI : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ I :=
    (cv_le_inf152 hs hD).trans inf_le_right
  have hXW : oTwoUpper (M ⊓ I) ≤ preOn M (V154 T Mc M) (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M)) :=
    fun x hx => mem_preOn.mpr ⟨hXM hx, hMV (hXM hx), mem_autOn_of_mem _ hx⟩
  have hWn : M ≤ Subgroup.normalizer
      (preOn M (V154 T Mc M) (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M)) : Set G) :=
    le_normalizer_preOn hMV hnorm
  have hWI : preOn M (V154 T Mc M) (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M)) ≤ I :=
    fun x hx => mem_of_mem_preOn_autOn hXM hXI hCvI hx
  have hSn := T_le_normalizer_S152 hD
  have hKn : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hH.1.1.trans (le_normalizer_oTwoUpper H)
  have hG₀n : T ≤ Subgroup.normalizer
      (((sOf152 T Mc M B₀ ⊔ preOn M (V154 T Mc M) (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M))) ⊔
        oTwoUpper H : Subgroup G) : Set G) :=
    le_normalizer_sup' (le_normalizer_sup' hSn (hTM.trans hWn)) hKn
  have hG₀I : (sOf152 T Mc M B₀ ⊔ preOn M (V154 T Mc M) (autOn (oTwoUpper (M ⊓ I))
      (V154 T Mc M))) ⊔ oTwoUpper H ≤ I :=
    sup_le (sup_le (S_le_I152 hD) hWI) ((K_le_inf152 hD).trans inf_le_right)
  have hO2S : pCoreOf 2 I ≤ sOf152 T Mc M B₀ := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
  have hO2 : pCoreOf 2 I ≤ pCoreOf 2 ((sOf152 T Mc M B₀ ⊔ preOn M (V154 T Mc M)
      (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M))) ⊔ oTwoUpper H) :=
    le_pCoreOf_of_le_normalizer 2 (hO2S.trans (le_sup_left.trans le_sup_left))
      (hG₀I.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  set G₀ : Subgroup G := (sOf152 T Mc M B₀ ⊔ preOn M (V154 T Mc M)
      (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M))) ⊔ oTwoUpper H with hG₀
  have hG₁ : InH T (G₀ ⊔ T) := by
    refine ⟨le_sup_right, ?_⟩
    have h1 : pCoreOf 2 G₀ ≤ pCoreOf 2 (G₀ ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 G₀).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 G₀) (hG₀n.trans (normalizer_le_normalizer_pCoreOf 2 G₀)))
        (pCoreOf_isPGroup 2 G₀)
    intro h
    apply hI.inH.2
    rw [eq_bot_iff]
    exact (hO2.trans h1).trans (le_of_eq h)
  have hXG : oTwoUpper (M ⊓ I) ≤ G₀ ⊔ T :=
    hXW.trans (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hnotMc : ¬ G₀ ⊔ T ≤ Mc := by
    intro hle
    have h1 := oTwoUpper_le_cv_of_le_Mc hs hD hXM (hXG.trans hle)
    rw [oTwoUpper_idem] at h1
    exact hX h1
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hG₁.2
  have hTM' : InM T M' := ⟨hM'.1, hG₁.1.trans hM'.2⟩
  rcases (hD.m_eq M').mp hTM' with hMM | hMM
  · have hKG : oTwoUpper H ≤ G₀ ⊔ T := le_sup_right.trans le_sup_left
    have hKM : oTwoUpper H ≤ M := (hKG.trans hM'.2).trans hMM.le
    apply hH.2.1
    rw [H_eq152 hs hH]
    exact sup_le hKM hTM
  · exact hnotMc (hM'.2.trans hMM.le)


theorem card_autOn_T152 (hs : Setting152 T Mc M)
    (h36 : Nat.card (autOn M (V154 T Mc M)) = 36)
    (h9 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 9) :
    Nat.card (autOn T (V154 T Mc M)) = 4 := by
  have hMb := autOn_M_eq_sup152 hs
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    (T_le_M152 hs).trans (le_normalizer_V154 T Mc M)
  have hT2 := isPGroup_autOn hs.qtfe.sylow.1 hTV
  have hTbN : autOn T (V154 T Mc M) ≤
      Subgroup.normalizer (oTwoUpper (autOn M (V154 T Mc M)) : Set (MulAut (V154 T Mc M))) :=
    (A4.autOn_mono (T_le_M152 hs)).trans (le_normalizer_oTwoUpper _)
  have hinf : oTwoUpper (autOn M (V154 T Mc M)) ⊓ autOn T (V154 T Mc M) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_of_odd_of_isPGroup (by rw [h9]; decide) hT2 hx.1 hx.2
  have hcard := card_sup_eq_mul_of_le_normalizer hTbN hinf
  rw [sup_comm, ← hMb, h36, h9] at hcard
  omega

theorem relIndex_autOn_S_T152 (hs : Setting152 T Mc M) (hD : Inputs152 T Mc M H B₀ I) :
    (autOn (sOf152 T Mc M B₀) (V154 T Mc M)).relIndex (autOn T (V154 T Mc M)) = 2 := by
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    (T_le_M152 hs).trans (le_normalizer_V154 T Mc M)
  rw [relIndex_autOn S_le_T152 hTV (inf_centralizer_le_S152 hs B₀), hD.h17.2.2]

theorem autOn_S_eq_B₀152 (hs : Setting152 T Mc M) (hB₀ : IsB0 T Mc M B₀)
    (hD : Inputs152 T Mc M H B₀ I) (hT4 : Nat.card (autOn T (V154 T Mc M)) = 4) :
    autOn (sOf152 T Mc M B₀) (V154 T Mc M) = B₀ := by
  have hSTb : autOn (sOf152 T Mc M B₀) (V154 T Mc M) ≤ autOn T (V154 T Mc M) :=
    A4.autOn_mono S_le_T152
  have hmul := Subgroup.relIndex_mul_card (autOn (sOf152 T Mc M B₀) (V154 T Mc M))
    (autOn T (V154 T Mc M))
  rw [inf_of_le_left hSTb, relIndex_autOn_S_T152 hs hD, hT4] at hmul
  have hS2 : Nat.card (autOn (sOf152 T Mc M B₀) (V154 T Mc M)) = 2 := by omega
  exact (Subgroup.eq_of_le_of_card_ge (B₀_le_autOn_S152 hs hB₀) (by rw [hS2, hB₀.2.1])).symm

omit [Finite G] in
theorem comm_of_isElemAbelian152 {E : Subgroup G} (h : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm h hx hy

theorem mem_normalizer_of_inverts {A : Type*} [Group A] {E Y : Subgroup A} {b : A}
    (hb2 : b ^ 2 = 1) (hinv : ∀ e ∈ E, b * e * b⁻¹ = e⁻¹) (hYE : Y ≤ E) :
    b ∈ Subgroup.normalizer (Y : Set A) := by
  have hbb : b * b = 1 := by rw [← sq]; exact hb2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hinv h (hYE hh)]
    exact Y.inv_mem hh
  · intro hx
    have h1 := hinv _ (hYE hx)
    have h2 : b * (b * h * b⁻¹) * b⁻¹ = h := by
      calc b * (b * h * b⁻¹) * b⁻¹ = (b * b) * h * (b⁻¹ * b⁻¹) := by group
        _ = h := by
          have : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hbb, inv_one]
          rw [hbb, this]; group
    rw [h2] at h1
    have := Y.inv_mem hx
    rw [← h1] at this
    simpa using Y.inv_mem this

theorem concl15218ii_of_not_le152 (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hB₀ : IsB0 T Mc M B₀) (hI : Hyp15215 T Mc M B₀ I) (hD : Inputs152 T Mc M H B₀ I)
    (hOm : Om4FactsStatement) (hSyl : IsSylowTwoOf (sOf152 T Mc M B₀) I)
    (hX : ¬ oTwoUpper (M ⊓ I) ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :
    Concl15218ii T Mc M H B₀ I := by
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMV
  have hnn := not_normal_oTwoUpper152 hs hH hI hD hSyl hX
  have hNiM : M ⊓ I ≤ M := inf_le_left
  have hNiV : M ⊓ I ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hNiM.trans hMV
  have hXNi : oTwoUpper (M ⊓ I) ≤ M ⊓ I := oTwoUpper_le _
  have hXV : oTwoUpper (M ⊓ I) ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hXNi.trans hNiV
  have hAE : autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) ≤ oTwoUpper (autOn M (V154 T Mc M)) := by
    rw [← A4.oTwoUpper_autOn hNiV]
    exact oTwoUpper_mono (A4.autOn_mono hNiM)
  have hEn : ∀ g ∈ autOn M (V154 T Mc M), ∀ e ∈ oTwoUpper (autOn M (V154 T Mc M)),
      g * e * g⁻¹ ∈ oTwoUpper (autOn M (V154 T Mc M)) := fun g hg e he =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hg) e).mp he
  have hΩ : IsOmegaFourPlusOn M (V154 T Mc M) := by
    rcases hD.h17.1 with ⟨⟨e⟩⟩ | h
    · exfalso
      have h20 : Nat.card (autOn M (V154 T Mc M)) = 20 := by
        rw [Nat.card_congr e.toEquiv]
        exact card_sz_zero
      exact hnn (normalizes_of_le_of_card_dvd_prime (by norm_num) (card_oTwoUpper_dvd_five h20)
        hAE hEn)
    · exact h
  have hV := isElemAbelian_V152 hs
  have h36 := (om4_card152 hOm hΩ).1
  have h9 := (om4_card152 hOm hΩ).2
  have h13ii : Case15213ii T Mc M H := by
    rcases hD.h13.cases with hi | hii
    · exfalso
      rcases hi.2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · rw [Nat.card_congr e.toEquiv] at h36
        simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at h36
      · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card] at h36
        omega
      · rw [Nat.card_congr e.toEquiv, card_sz_zero] at h36
        omega
    · exact hii
  have hB₀le := B₀_le_autOn_M152 hs hB₀
  have hfpf := B₀_fpf hs hB₀ hD hOm
  have hAne : autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) ≠ ⊥ :=
    autOn_ne_bot_of_not_le_centralizer hXV
      (fun h => hX (le_inf ((oTwoUpper_le _).trans inf_le_left) h))
  obtain ⟨z, hz1, hzZs, hzstab, t, htΩ, htB, htz⟩ :=
    om4_stab152 hOm hΩ hB₀.1 hB₀le hB₀.2.1 hfpf hAE hAne hnn
  have hT4 := card_autOn_T152 hs h36 h9
  have hSbB := autOn_S_eq_B₀152 hs hB₀ hD hT4
  have htT : t ∈ autOn T (V154 T Mc M) := by
    have hn : t ∈ Subgroup.normalizer (autOn (sOf152 T Mc M B₀) (V154 T Mc M) :
        Set (MulAut (V154 T Mc M))) := by
      rw [hSbB]
      exact mem_normalizer_of_commutes htB
    exact normalizer_autS_le_autT hs hB₀ hD hOm t htΩ hn
  have hz2 : (z : G) ^ 2 = 1 := hV.2 z z.2
  have hzG1 : (z : G) ≠ 1 := hz1
  have hZ₁card : Nat.card (Subgroup.zpowers (z : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hzG1
  have hZ₁Zs : Subgroup.zpowers (z : G) ≤ zSOf T Mc M B₀ := Subgroup.zpowers_le.mpr hzZs
  obtain ⟨hZscard, hZsab⟩ := card_zS152 hB₀ hD
  have hZZs : quasithinOmegaOneCenter T ≤ zSOf T Mc M B₀ := hD.h14.le_zS
  have hZcard := hD.h17.2.1
  have hzZ : (z : G) ∉ quasithinOmegaOneCenter T := by
    intro hzZ
    obtain ⟨p, hpV, hpT, hpt⟩ := mem_autOn_iff_exists.mp htT
    apply htz
    rw [← hpt]
    apply Subtype.ext
    rw [conj_coe_apply]
    show p * (z : G) * p⁻¹ = z
    have hc : p * (z : G) = (z : G) * p := (quasithinOmegaOneCenter_le_center T hzZ).2 p hpT
    rw [hc]
    group
  have hZ₁Z : Subgroup.zpowers (z : G) ⊓ quasithinOmegaOneCenter T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases eq_one_or_eq_of_mem_zpowers hz2 hx.1 with h | h
    · exact h
    · exact absurd (h ▸ hx.2) hzZ
  have hZ₁sup : Subgroup.zpowers (z : G) ⊔ quasithinOmegaOneCenter T = zSOf T Mc M B₀ := by
    have hnorm : quasithinOmegaOneCenter T ≤ Subgroup.normalizer
        ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := fun y hy =>
      mem_normalizer_of_commutes fun w hw =>
        comm_of_isElemAbelian152 hZsab (hZZs hy) (hZ₁Zs hw)
    have hcard := card_sup_eq_mul_of_le_normalizer hnorm hZ₁Z
    have hle : quasithinOmegaOneCenter T ⊔ Subgroup.zpowers (z : G) ≤ zSOf T Mc M B₀ :=
      sup_le hZZs hZ₁Zs
    have heq : quasithinOmegaOneCenter T ⊔ Subgroup.zpowers (z : G) = zSOf T Mc M B₀ := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [hZscard, hcard, hZcard, hZ₁card]
    rw [sup_comm]
    exact heq
  have hSNi : sOf152 T Mc M B₀ ≤ M ⊓ I := le_inf (S_le_T152.trans hTM) (S_le_I152 hD)
  have hNiX : M ⊓ I = oTwoUpper (M ⊓ I) ⊔ sOf152 T Mc M B₀ :=
    eq_oTwoUpper_sup_of_isSylowTwoOf (isSylowTwoOf_restrict hSyl hSNi inf_le_right)
  have hCvNi : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ I :=
    le_inf inf_le_left ((cv_le_inf152 hs hD).trans inf_le_right)
  have hNb : autOn (M ⊓ I) (V154 T Mc M) =
      autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) ⊔ B₀ := by
    have h1 : autOn (M ⊓ I) (V154 T Mc M) =
        autOn (oTwoUpper (M ⊓ I) ⊔ sOf152 T Mc M B₀) (V154 T Mc M) :=
      congrArg (fun Y => autOn Y (V154 T Mc M)) hNiX
    rw [h1, autOn_sup hXV (S_le_T152.trans hTV), hSbB]
  have hA3 : Nat.card (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M)) = 3 := by
    have hdvd : Nat.card (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M)) ∣ 3 ^ 2 := by
      have := Subgroup.card_dvd_of_le hAE
      rw [h9] at this
      simpa using this
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases i
    · exfalso
      apply hAne
      exact Subgroup.card_eq_one.mp (by simpa using hi')
    · simpa using hi'
    · exfalso
      have hEq : autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) = oTwoUpper (autOn M (V154 T Mc M)) :=
        Subgroup.eq_of_le_of_card_ge hAE (by rw [h9, hi']; norm_num)
      apply hnn
      rw [hEq]
      exact hEn
  have hBnorm : B₀ ≤ Subgroup.normalizer (autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) :
      Set (MulAut (V154 T Mc M))) := by
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact Subgroup.one_mem _
    · obtain ⟨b₀, -, hb02, hB₀eq⟩ := exists_zpowers_eq_of_card_two hB₀.2.1
      have hbb₀ : b = b₀ := (eq_one_or_eq_of_mem_zpowers hb02 (hB₀eq ▸ hb)).resolve_left hb1
      have hb2 : b ^ 2 = 1 := by rw [hbb₀]; exact hb02
      exact mem_normalizer_of_inverts hb2 (B₀_inverts hs hB₀ hD hOm b hb hb1) hAE
  have hAB : autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) ⊓ B₀ = ⊥ := by
    have hB2 : IsPGroup 2 B₀ := IsPGroup.of_card (n := 1) (by rw [hB₀.2.1]; norm_num)
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_of_odd_of_isPGroup (by rw [h9]; decide) hB2 (hAE hx.1) hx.2
  have hNb6 : Nat.card (autOn (M ⊓ I) (V154 T Mc M)) = 6 := by
    have := card_sup_eq_mul_of_le_normalizer hBnorm hAB
    rw [hNb, sup_comm, this, hB₀.2.1, hA3]
  refine ⟨?_, h13ii, hΩ, Subgroup.zpowers (z : G), hZ₁sup, hZ₁Z, ?_, ?_⟩
  · intro hle
    exact hX (oTwoUpper_le_cv_of_le_Mc hs hD hNiM (hle.trans inf_le_left))
  · ext x
    constructor
    · intro hx
      have hxV := hMV hx.1
      have hmem : conjAct (V154 T Mc M) ⟨x, hxV⟩ ∈ autOn (oTwoUpper (M ⊓ I)) (V154 T Mc M) ⊔ B₀ :=
        hNb ▸ mem_autOn_of_mem hxV hx
      have hfix : conjAct (V154 T Mc M) ⟨x, hxV⟩ z = z :=
        (hzstab _ (mem_autOn_of_mem hxV hx.1)).mpr hmem
      have hxz : x * (z : G) = (z : G) * x := by
        have h1 := congrArg Subtype.val hfix
        rw [conj_coe_apply] at h1
        calc x * (z : G) = (x * (z : G) * x⁻¹) * x := by group
          _ = (z : G) * x := by rw [show x * (z : G) * x⁻¹ = z from h1]
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ((Commute.zpow_right (show Commute x (z : G) from hxz) k).eq).symm
    · intro hx
      have hxV := hMV hx.1
      have hxz : (z : G) * x = x * (z : G) :=
        Subgroup.mem_centralizer_iff.mp hx.2 (z : G) (Subgroup.mem_zpowers (z : G))
      have hfix : conjAct (V154 T Mc M) ⟨x, hxV⟩ z = z := by
        apply Subtype.ext
        rw [conj_coe_apply]
        show x * (z : G) * x⁻¹ = z
        rw [← hxz]
        group
      have hmem := (hzstab _ (mem_autOn_of_mem hxV hx.1)).mp hfix
      exact mem_of_conjAct_mem_autOn hMV hNiM hCvNi hx.1 (hNb ▸ hmem)
  · have h1 := relIndex_autOn hNiM hMV hCvNi
    have hmul := Subgroup.relIndex_mul_card (autOn (M ⊓ I) (V154 T Mc M))
      (autOn M (V154 T Mc M))
    rw [inf_of_le_left (A4.autOn_mono hNiM), h1, hNb6, h36] at hmul
    omega

theorem lemma_15_2_18 (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hB₀ : IsB0 T Mc M B₀)
    (hI : Hyp15215 T Mc M B₀ I) (hD : Inputs152 T Mc M H B₀ I) (hOm : Om4FactsStatement) :
    Lemma15218Concl T Mc M H B₀ I := by
  have hSyl := isSylowTwoOf_S152 hs hH hB₀ hI hD hOm
  refine ⟨hSyl, baum_eq152 hD, cgs_le152 hD, ?_⟩
  by_cases hX : oTwoUpper (M ⊓ I) ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)
  · left
    have hSNi : sOf152 T Mc M B₀ ≤ M ⊓ I :=
      le_inf (S_le_T152.trans (T_le_M152 hs)) (S_le_I152 hD)
    have hNiX : M ⊓ I = oTwoUpper (M ⊓ I) ⊔ sOf152 T Mc M B₀ :=
      eq_oTwoUpper_sup_of_isSylowTwoOf (isSylowTwoOf_restrict hSyl hSNi inf_le_right)
    show M ⊓ I ≤ Mc ⊓ I
    rw [hNiX]
    exact sup_le (hX.trans (cv_le_inf152 hs hD)) (S_le_inf152 hD)
  · right
    exact concl15218ii_of_not_le152 hs hH hB₀ hI hD hOm hSyl hX

end Main

theorem stageLemma15218_of (h5 : StageLemma15205) (h159 : StageLemma1519)
    (h11 : StageLemma15211) (h13 : StageLemma15213) (h14 : StageLemma15214)
    (hN : StageNotation15209) (h16 : StageLemma15216) (h17 : StageLemma15217)
    (hOm : Om4FactsStatement) : StageLemma15218 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI
  exact lemma_15_2_18 hs hH hB₀ hI
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩ hOm

end CFSG.Quasithin
