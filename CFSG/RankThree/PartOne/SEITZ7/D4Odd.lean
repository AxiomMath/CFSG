module

public import CFSG.RankThree.PartOne.SEITZ7.D4Core
public import CFSG.RankThree.PartOne.SEITZ6.G2Odd

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.RankThree.PartOne.CTP CFSG.DihedralBlueprint
open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

theorem mkT_mem_Uhat [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {b0 a1 a4 a8 b3 b7 : K}
    (h0 : σ b0 = b0) (h3 : σ b3 = b3) (h7 : σ b7 = b7) :
    ordT σ (mkT b0 a1 a4 a8 b3 b7) ∈ Uhat σ := by
  rw [ordT_mkT]
  have hm : ∀ p ∈ posT, ∀ x ∈ twistedRootSubgroupD4 σ (rt p), x ∈ Uhat σ := fun p hp x hx =>
    (le_iSup₂_of_le (f := fun p (_ : p ∈ posT) => twistedRootSubgroupD4 σ (rt p)) p hp le_rfl) hx
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (hm 0 (by simp [posT]) _ ((mem_XB hσ _).2 ⟨b0, h0, rfl⟩))
    (hm 1 (by simp [posT]) _ ((mem_XA hσ _).2 ⟨a1, rfl⟩)))
    (hm 4 (by simp [posT]) _ ((mem_XAB hσ _).2 ⟨a4, rfl⟩)))
    (hm 8 (by simp [posT]) _ ((mem_XAAB hσ _).2 ⟨a8, rfl⟩)))
    (hm 3 (by simp [posT]) _ ((mem_XN hσ _).2 ⟨b3, h3, rfl⟩)))
    (hm 7 (by simp [posT]) _ ((mem_XH hσ _).2 ⟨b7, h7, rfl⟩))

theorem card_Uhat [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) :
    Nat.card (Uhat σ) = Nat.card (fixedField σ) ^ 3 * Nat.card K ^ 3 := by
  let f : (fixedField σ) × K × K × K × (fixedField σ) × (fixedField σ) → Uhat σ :=
    fun v => ⟨ordT σ (mkT v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2),
      mkT_mem_Uhat hσ v.1.2 v.2.2.2.2.1.2 v.2.2.2.2.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b0, a1, a4, a8, b3, b7⟩ ⟨b0', a1', a4', a8', b3', b7'⟩ h
      have h' := congrArg Subtype.val h
      obtain ⟨e0, e1, e4, e8, e3, e7⟩ := ordT_inj σ h'
      simp only [mkT] at e0 e1 e4 e8 e3 e7
      simp at e0 e1 e4 e8 e3 e7
      simp [e0, e1, e4, e8, e3, e7]
    · intro u
      obtain ⟨c, hc0, hc3, hc7, hcu⟩ := exists_ordT hσ u.2
      refine ⟨(⟨c 0, hc0⟩, c 1, c 4, c 8, ⟨c 3, hc3⟩, ⟨c 7, hc7⟩), Subtype.ext ?_⟩
      show ordT σ (mkT (c 0) (c 1) (c 4) (c 8) (c 3) (c 7)) = _
      rw [hcu, ordT_mkT]
      rfl
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp only [Nat.card_prod]
  ring

@[expose] def qT : List ℕ := [0, 4, 8, 3, 7]

theorem mem_qT {p : ℕ} (hp : p ∈ qT) : p = 0 ∨ p = 4 ∨ p = 8 ∨ p = 3 ∨ p = 7 := by
  simpa [qT] using hp

theorem qT_sub_posT {p : ℕ} (hp : p ∈ qT) : p ∈ posT := by
  rcases mem_qT hp with rfl | rfl | rfl | rfl | rfl <;> simp [posT]

theorem qT_check : (∀ p ∈ qT, 1 ≤ rt p 0) ∧ rt 1 0 = 0 ∧ ∀ k ∈ posT, 1 ≤ rt k 0 → k ∈ qT := by
  decide +kernel

theorem cone_Q {p k : ℕ} (hp : p ∈ qT) (hk : k < 12) {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (h : rt k = i • rt 1 + j • rt p) : k ∈ qT := by
  obtain ⟨hkp, -⟩ := cone_pos (a := 1) (b := p) (by simp [posT]) (qT_sub_posT hp) hk hi hj h
  obtain ⟨h1, h2, h3⟩ := qT_check
  refine h3 k hkp ?_
  have h0 := congrFun h 0
  simp only [Pi.add_apply, Pi.smul_apply] at h0
  simp only [nsmul_eq_mul, h2] at h0
  have hp1 := h1 p hp
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have : (1 : ℤ) ≤ j * rt p 0 := by nlinarith
  linarith

@[expose] noncomputable def Qt (σ : K →+* K) : Subgroup (twistedGroup σ) :=
  ⨆ p ∈ qT, twistedRootGroup σ (rt p)

theorem rootGroup_le_Qt {p : ℕ} (hp : p ∈ qT) : twistedRootGroup σ (rt p) ≤ Qt σ :=
  le_iSup₂_of_le (f := fun p (_ : p ∈ qT) => twistedRootGroup σ (rt p)) p hp le_rfl

theorem Qt_conj_Xalpha {x : twistedGroup σ} (hx : x ∈ twistedRootGroup σ (rt 1))
    {y : twistedGroup σ} (hy : y ∈ Qt σ) : x * y * x⁻¹ ∈ Qt σ := by
  refine conj_mem_of_forall_mem (X := fun p => twistedRootGroup σ (rt p)) (P := {p | p ∈ qT})
    (M := Qt σ) (fun p hp y hy => ?_) hy
  have hr1 : IsRoot .G2 (rt 1) := isRoot_rt (by norm_num)
  have hp12 : p < 12 := lt_twelve_of_mem_posT (qT_sub_posT hp)
  have hrp : IsRoot .G2 (rt p) := isRoot_rt hp12
  have hlin : LinIndepPair (rt 1) (rt p) := by
    apply linIndep_of_det
    have : ∀ p ∈ qT, rt 1 0 * rt p 1 - rt 1 1 * rt p 0 ≠ 0 := by decide +kernel
    exact this p hp
  have hc := commutator_mem_iSup_twistedRootGroup (σ := σ) hlin hx hy
  have hcQ : ⁅x, y⁆ ∈ Qt σ := by
    refine (iSup₂_le fun ε hε => ?_ :
      (⨆ ε ∈ openCone {β | IsRoot .G2 β} (rt 1) (rt p), twistedRootGroup σ ε) ≤ Qt σ) hc
    obtain ⟨hεR, i, j, hi, hj, hεij⟩ := hε
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hεR
    have hk12 : k < 12 := by simpa [len_roots] using hk
    exact rootGroup_le_Qt (cone_Q hp hk12 hi hj hεij)
  have hyQ : y ∈ Qt σ := rootGroup_le_Qt hp hy
  have := mul_mem hcQ hyQ
  rwa [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ * y = x * y * x⁻¹ by group] at this

theorem reflect_Q_check : ∀ p ∈ qT, ∃ p' ∈ qT, reflect .G2 (ng 1) (rt p) = rt p' := by
  decide +kernel

theorem normalizer_of_conj {G : Type*} [Group G] {N : Subgroup G} {g : G}
    (h1 : ∀ y ∈ N, g * y * g⁻¹ ∈ N) (h2 : ∀ y ∈ N, g⁻¹ * y * g ∈ N) :
    g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem Tt_conj_Qt {t : twistedGroup σ} (ht : t ∈ Tt σ) {y : twistedGroup σ} (hy : y ∈ Qt σ) :
    t * y * t⁻¹ ∈ Qt σ := by
  refine conj_mem_of_forall_mem (X := fun p => twistedRootGroup σ (rt p)) (P := {p | p ∈ qT})
    (M := Qt σ) (fun p hp y hy => ?_) hy
  have hr : IsRoot .G2 (rt p) := isRoot_rt (lt_twelve_of_mem_posT (qT_sub_posT hp))
  exact rootGroup_le_Qt hp
    ((Subgroup.mem_normalizer_iff.1 (Tt_normalizes σ hr ht) y).1 hy)

theorem Qt_conj_nHat {y : twistedGroup σ} (hy : y ∈ Qt σ) :
    nHat σ (ng 1) * y * (nHat σ (ng 1))⁻¹ ∈ Qt σ := by
  refine conj_mem_of_forall_mem (X := fun p => twistedRootGroup σ (rt p)) (P := {p | p ∈ qT})
    (M := Qt σ) (fun p hp y hy => ?_) hy
  obtain ⟨p', hp', hr⟩ := reflect_Q_check p hp
  have := nHat_conj_mem σ (ng 1) (isRoot_rt (lt_twelve_of_mem_posT (qT_sub_posT hp))) hy
  rw [hr] at this
  exact rootGroup_le_Qt hp' this

theorem nHat_mem_normalizer_Qt :
    nHat σ (ng 1) ∈ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) := by
  refine normalizer_of_conj (fun y hy => Qt_conj_nHat hy) (fun y hy => ?_)
  have hsq : nHat σ (ng 1) ^ 2 ∈ Tt σ :=
    Subgroup.mem_iSup_of_mem (ng 1) (nHat_sq_mem σ (ng 1))
  have e : (nHat σ (ng 1))⁻¹ * y * nHat σ (ng 1) =
      nHat σ (ng 1) * ((nHat σ (ng 1) ^ 2)⁻¹ * y * ((nHat σ (ng 1) ^ 2)⁻¹)⁻¹) *
        (nHat σ (ng 1))⁻¹ := by
    group
  rw [e]
  exact Qt_conj_nHat (Tt_conj_Qt (inv_mem hsq) hy)

theorem Xalpha_mem_normalizer_Qt {x : twistedGroup σ} (hx : x ∈ twistedRootGroup σ (rt 1)) :
    x ∈ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) :=
  normalizer_of_conj (fun y hy => Qt_conj_Xalpha hx hy) (fun y hy => by
    simpa using Qt_conj_Xalpha (inv_mem hx) hy)

theorem Tt_le_normalizer_Qt : Tt σ ≤ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) := by
  intro t ht
  exact normalizer_of_conj (fun y hy => Tt_conj_Qt ht hy) (fun y hy => by
    simpa using Tt_conj_Qt (inv_mem ht) hy)

theorem posUnipotent_le_normalizer_Qt :
    posUnipotent (twistedDatum σ) ≤ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγR, hγp⟩ := hγ
  have hγR' : IsRoot .G2 γ := by
    rw [twistedDatum_roots] at hγR
    exact hγR
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγR'
  have hk' : k < 12 := by simpa [len_roots] using hk
  have hkp := ht_pos_aux k hk' hγp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkp
  show twistedRootGroup σ (rt k) ≤ _
  rcases hkp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact fun x hx => Xalpha_mem_normalizer_Qt hx
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer
  · exact (rootGroup_le_Qt (by simp [qT])).trans Subgroup.le_normalizer

theorem borel_le_normalizer_Qt :
    borel (twistedDatum σ) (hHat σ) ≤ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) :=
  sup_le Tt_le_normalizer_Qt posUnipotent_le_normalizer_Qt

theorem Xalpha_le_Asub [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    twistedRootGroup σ (rt 1) ≤ Asub σ hσ := by
  intro y hy
  have hy' : (y : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 1) :=
    Subgroup.mem_subgroupOf.1 hy
  obtain ⟨a, hya⟩ := (mem_XA hσ _).1 hy'
  have : y = slShort σ hσ (sl2Upper a) :=
    Subtype.ext (hya.trans (slShort_upper_xA σ hσ a).symm)
  rw [this]
  exact ⟨_, rfl⟩

theorem posUnipotent_eq_Qt_mul {u : twistedGroup σ} (hu : u ∈ posUnipotent (twistedDatum σ)) :
    ∃ q ∈ Qt σ, ∃ x ∈ twistedRootGroup σ (rt 1), u = q * x := by
  have hle : twistedRootGroup σ (rt 1) ≤ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) :=
    fun x hx => Xalpha_mem_normalizer_Qt hx
  have hP : posUnipotent (twistedDatum σ) ≤ twistedRootGroup σ (rt 1) ⊔ Qt σ := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγR, hγp⟩ := hγ
    have hγR' : IsRoot .G2 γ := by
      rw [twistedDatum_roots] at hγR
      exact hγR
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγR'
    have hk' : k < 12 := by simpa [len_roots] using hk
    have hkp := ht_pos_aux k hk' hγp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkp
    show twistedRootGroup σ (rt k) ≤ _
    rcases hkp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (rootGroup_le_Qt (by simp [qT])).trans le_sup_right
    · exact le_sup_left
    · exact (rootGroup_le_Qt (by simp [qT])).trans le_sup_right
    · exact (rootGroup_le_Qt (by simp [qT])).trans le_sup_right
    · exact (rootGroup_le_Qt (by simp [qT])).trans le_sup_right
    · exact (rootGroup_le_Qt (by simp [qT])).trans le_sup_right
  have hmem : u⁻¹ ∈ twistedRootGroup σ (rt 1) ⊔ Qt σ := hP (inv_mem hu)
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (twistedRootGroup σ (rt 1)) (Qt σ) hle
  rw [← SetLike.mem_coe, h, Set.mem_mul] at hmem
  obtain ⟨x, hx, q, hq, hxq⟩ := hmem
  refine ⟨q⁻¹, inv_mem hq, x⁻¹, inv_mem hx, ?_⟩
  rw [← mul_inv_rev, hxq, inv_inv]

theorem xHg_eq_psiB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {d : K} (hdσ : σ d = d) :
    xHg hσ d hdσ = psiB σ hσ (sl2Upper (⟨d, hdσ⟩ : fixedField σ)) :=
  Subtype.ext (psiB_upper σ hσ ⟨d, hdσ⟩).symm

theorem Asub_comm_xHg [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {d : K} (hdσ : σ d = d)
    {a : twistedGroup σ} (ha : a ∈ Asub σ hσ) : a * xHg hσ d hdσ = xHg hσ d hdσ * a := by
  rw [xHg_eq_psiB hσ hdσ]
  exact Asub_Bsub_commute σ hσ a ha _ ⟨_, rfl⟩

theorem borel_cent_decomp [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {b : twistedGroup σ}
    (hb : b ∈ borel (twistedDatum σ) (hHat σ)) {d : K} (hd : d ≠ 0) (hdσ : σ d = d)
    (hbx : b * xHg hσ d hdσ = xHg hσ d hdσ * b) :
    ∃ q ∈ Qt σ, ∃ a ∈ Asub σ hσ, b = q * a := by
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hb' : b ∈ (borel (twistedDatum σ) (hHat σ) : Set (twistedGroup σ)) := hb
  rw [coe_borel hct, Set.mem_mul] at hb'
  obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hb'
  have hu0U : ((u0 : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
    rw [posUnipotent_twisted] at hu0
    exact Subgroup.mem_subgroupOf.1 hu0
  have hcomm : u0 * xHg hσ d hdσ = xHg hσ d hdσ * u0 :=
    Subtype.ext (commute_Uhat_xH hσ hu0U d)
  have h1 : t0 * xHg hσ d hdσ = xHg hσ d hdσ * t0 := by
    have h2 : t0 * xHg hσ d hdσ * u0 = xHg hσ d hdσ * t0 * u0 := by
      calc t0 * xHg hσ d hdσ * u0 = t0 * (xHg hσ d hdσ * u0) := by group
        _ = t0 * (u0 * xHg hσ d hdσ) := by rw [hcomm]
        _ = t0 * u0 * xHg hσ d hdσ := by group
        _ = xHg hσ d hdσ * (t0 * u0) := hbx
        _ = xHg hσ d hdσ * t0 * u0 := by group
    exact mul_right_cancel h2
  obtain ⟨s, u, hs, hsu⟩ := mem_Tt_form ht0
  have h1' : (t0 : adjointGroup d4 K) * xH d * (t0 : adjointGroup d4 K)⁻¹ = xH d := by
    have h3 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h3
    have hcoe : ((xHg hσ d hdσ : twistedGroup σ) : adjointGroup d4 K) = xH d := rfl
    rw [hcoe] at h3
    calc (t0 : adjointGroup d4 K) * xH d * (t0 : adjointGroup d4 K)⁻¹ =
        (xH d * (t0 : adjointGroup d4 K)) * (t0 : adjointGroup d4 K)⁻¹ := by rw [h3]
      _ = xH d := by group
  rw [hsu] at h1'
  have h2 : xH (s * d) = xH d := by
    have e : (torusElement d4 K (nd 2) s * hShortHom σ u) * xH d *
        (torusElement d4 K (nd 2) s * hShortHom σ u)⁻¹ =
        torusElement d4 K (nd 2) s * (hShortHom σ u * xH d * (hShortHom σ u)⁻¹) *
          (torusElement d4 K (nd 2) s)⁻¹ := by group
    rw [e, hShort_xH, hB_xH] at h1'
    exact h1'
  have hs1 : (s : K) = 1 := by
    have := xPar_injective (F := rootOperatorFamily d4) (K := K) (isRoot_d4 (by norm_num : 22 < 24))
      h2
    exact mul_right_cancel₀ hd (by rw [this, one_mul])
  have hs1' : s = 1 := Units.ext hs1
  subst hs1'
  have ht0A : t0 = slShort σ hσ (dSL u) := by
    apply Subtype.ext
    rw [slShort_dSL, hsu, torusElement_one_d4, one_mul]
  obtain ⟨q', hq', x, hx, hu0'⟩ := posUnipotent_eq_Qt_mul hu0
  refine ⟨t0 * q' * t0⁻¹, Tt_conj_Qt ht0 hq', t0 * x, ?_, ?_⟩
  · rw [ht0A]
    exact mul_mem ⟨_, rfl⟩ (Xalpha_le_Asub hσ hx)
  · rw [hu0']
    group

theorem cent_bruhat [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {g : twistedGroup σ} {d : K}
    (hd : d ≠ 0) (hdσ : σ d = d) (hg : g * xHg hσ d hdσ = xHg hσ d hdσ * g) :
    g ∈ borel (twistedDatum σ) (hHat σ) ∨
      ∃ b ∈ borel (twistedDatum σ) (hHat σ), ∃ u ∈ twistedRootGroup σ (rt 1),
        g = b * nHat σ (ng 1) * u := by
  have hgU : (g : adjointGroup d4 K) * xH d * (g : adjointGroup d4 K)⁻¹ ∈ Upt σ := by
    have h3 := congrArg Subtype.val hg
    simp only [Subgroup.coe_mul] at h3
    have hcoe : ((xHg hσ d hdσ : twistedGroup σ) : adjointGroup d4 K) = xH d := rfl
    rw [hcoe] at h3
    have : (g : adjointGroup d4 K) * xH d * (g : adjointGroup d4 K)⁻¹ = xH d := by
      rw [h3]; group
    rw [this]
    exact (mem_Upt_iff hσ).2 ⟨d, 0, hdσ, by simp [xA_zero]⟩
  exact bruhat_stab_h_tw hσ hd hdσ hgU

theorem cent_decomp [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {g : twistedGroup σ}
    {d : K} (hd : d ≠ 0) (hdσ : σ d = d) (hg : g * xHg hσ d hdσ = xHg hσ d hdσ * g) :
    ∃ q ∈ Qt σ, ∃ a ∈ Asub σ hσ, g = q * a := by
  rcases cent_bruhat hσ hd hdσ hg with hB | ⟨b, hb, u, hu, rfl⟩
  · exact borel_cent_decomp hσ hB hd hdσ hg
  · have hn1A : nHat σ (ng 1) ∈ Asub σ hσ := nHat_one_mem_Asub hσ
    have huA : u ∈ Asub σ hσ := Xalpha_le_Asub hσ hu
    have c1 := Asub_comm_xHg hσ hdσ hn1A
    have c2 := Asub_comm_xHg hσ hdσ huA
    have hb' : b * xHg hσ d hdσ = xHg hσ d hdσ * b := by
      have h2 : b * xHg hσ d hdσ * (nHat σ (ng 1) * u) =
          xHg hσ d hdσ * b * (nHat σ (ng 1) * u) := by
        calc b * xHg hσ d hdσ * (nHat σ (ng 1) * u) =
            b * (xHg hσ d hdσ * nHat σ (ng 1)) * u := by group
          _ = b * (nHat σ (ng 1) * xHg hσ d hdσ) * u := by rw [c1]
          _ = b * nHat σ (ng 1) * (xHg hσ d hdσ * u) := by group
          _ = b * nHat σ (ng 1) * (u * xHg hσ d hdσ) := by rw [c2]
          _ = b * nHat σ (ng 1) * u * xHg hσ d hdσ := by group
          _ = xHg hσ d hdσ * (b * nHat σ (ng 1) * u) := hg
          _ = xHg hσ d hdσ * b * (nHat σ (ng 1) * u) := by group
      exact mul_right_cancel h2
    obtain ⟨q, hq, a, ha, rfl⟩ := borel_cent_decomp hσ hb hd hdσ hb'
    exact ⟨q, hq, a * nHat σ (ng 1) * u, mul_mem (mul_mem ha hn1A) huA, by group⟩

theorem cent_mem_normalizer_Qt [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {g : twistedGroup σ}
    {d : K} (hd : d ≠ 0) (hdσ : σ d = d) (hg : g * xHg hσ d hdσ = xHg hσ d hdσ * g) :
    g ∈ Subgroup.normalizer (Qt σ : Set (twistedGroup σ)) := by
  rcases cent_bruhat hσ hd hdσ hg with hB | ⟨b, hb, u, hu, rfl⟩
  · exact borel_le_normalizer_Qt hB
  · exact mul_mem (mul_mem (borel_le_normalizer_Qt hb) nHat_mem_normalizer_Qt)
      (Xalpha_mem_normalizer_Qt hu)

theorem Uhat_isPGroup [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hF : Nat.card (fixedField σ) = 2 ^ n) :
    IsPGroup 2 (Uhat σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  exact ⟨12 * n, by rw [card_Uhat hσ, hF, hK]; ring⟩

theorem Qt_le_posUnipotent : Qt σ ≤ posUnipotent (twistedDatum σ) := by
  refine iSup₂_le fun p hp => ?_
  have hp' := lt_twelve_of_mem_posT (qT_sub_posT hp)
  have hpos : 0 < ht (rt p) := by
    rcases mem_qT hp with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  exact le_iSup₂_of_le (rt p) ⟨by rw [twistedDatum_roots]; exact isRoot_rt hp', hpos⟩ le_rfl

theorem Qt_isPGroup [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hF : Nat.card (fixedField σ) = 2 ^ n) :
    IsPGroup 2 (Qt σ) := by
  intro y
  have hy : ((y : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
    have h := Qt_le_posUnipotent y.2
    rw [posUnipotent_twisted] at h
    exact Subgroup.mem_subgroupOf.1 h
  obtain ⟨k, hk⟩ := Uhat_isPGroup hσ hK hF ⟨_, hy⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : Uhat σ => (z : adjointGroup d4 K)) hk
  simpa using this

theorem Asub_facts [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) :
    IsSimpleGroup (Asub σ hσ) ∧ ¬ IsPGroup 2 (Asub σ hσ) ∧ Even (Nat.card (Asub σ hσ)) := by
  have hK' : Nat.card K = 2 ^ (3 * n) := by rw [hK, pow_mul']
  have h4 : 4 ≤ Nat.card K := by
    rw [hK']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : Nat.card (Asub σ hσ) = 2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1) := by
    rw [Asub, ← Nat.card_congr (MonoidHom.ofInjective (slShort_injective hσ)).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK']
  refine ⟨?_, ?_, ?_⟩
  · have := SEITZ6.isSimpleGroup_SL2 (F := K) h4
    exact MulEquiv.isSimpleGroup (MonoidHom.ofInjective (slShort_injective hσ)).symm
  · intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h
    rw [hcard] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (SEITZ6.three_dvd_two_pow_sq_sub_one (3 * n)).mul_left _
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · rw [hcard]
    exact (Nat.even_pow' (by omega)).2 even_two |>.mul_right _

theorem cent_R_trivial [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hF : Nat.card (fixedField σ) = 2 ^ n)
    {H : Subgroup (twistedGroup σ)} (hL : Lsub σ hσ ≤ H) {R : Subgroup (twistedGroup σ)}
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hodd : Odd (Nat.card R)) {d : K} (hd : d ≠ 0)
    (hdσ : σ d = d) :
    R ⊓ Subgroup.centralizer ({xHg hσ d hdσ} : Set (twistedGroup σ)) = ⊥ := by
  obtain ⟨hAs, hA2, hAe⟩ := Asub_facts hσ hn hK
  set D := Subgroup.centralizer ({xHg hσ d hdσ} : Set (twistedGroup σ)) with hDdef
  have hmemD : ∀ g : twistedGroup σ, g ∈ D ↔ g * xHg hσ d hdσ = xHg hσ d hdσ * g := by
    intro g
    rw [hDdef, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact (h _ (Set.mem_singleton _)).symm
    · intro h x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h.symm
  have hAD : Asub σ hσ ≤ D := fun a ha => (hmemD a).2 (Asub_comm_xHg hσ hdσ ha)
  have hQD : Qt σ ≤ D := by
    intro q hq
    refine (hmemD q).2 ?_
    have hqU : ((q : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
      have h := Qt_le_posUnipotent hq
      rw [posUnipotent_twisted] at h
      exact Subgroup.mem_subgroupOf.1 h
    exact Subtype.ext (commute_Uhat_xH hσ hqU d)
  refine SEITZ6.odd_normalized_trivial D (Qt σ) (Asub σ hσ) (R ⊓ D) hQD hAD inf_le_right
    (fun g hg q hq => ?_) (Qt_isPGroup hσ hK hF) hAs hA2 hAe
    (fun g hg => cent_decomp hσ hd hdσ ((hmemD g).1 hg))
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)) ?_
  · have := cent_mem_normalizer_Qt hσ hd hdσ ((hmemD g).1 hg)
    exact (Subgroup.mem_normalizer_iff.1 this q).1 hq
  · intro a ha c hc
    exact ⟨hRn a (hL (Asub_le_Lsub σ hσ ha)) c hc.1,
      D.mul_mem (D.mul_mem (hAD ha) hc.2) (D.inv_mem (hAD ha))⟩

theorem xHg_isInvolution [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {c : K} (hcσ : σ c = c)
    (hc : c ≠ 0) : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (xHg hσ c hcσ) :=
  ⟨fun h => xH_ne_one hc (congrArg Subtype.val h), by
    rw [pow_two]
    exact Subtype.ext (xd_mul_self 22 c)⟩

theorem odd_core_trivial_tw [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hF : Nat.card (fixedField σ) = 2 ^ n)
    {H : Subgroup (twistedGroup σ)} (hL : Lsub σ hσ ≤ H) {R : Subgroup (twistedGroup σ)}
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hodd : Odd (Nat.card R)) : R = ⊥ := by
  have : CharP (fixedField σ) 2 :=
    (RingHom.charP_iff (fixedField σ).subtype (fixedField σ).subtype.injective 2).2 inferInstance
  have h4 : 4 ≤ Nat.card (fixedField σ) := by rw [hF]; exact SEITZ6.four_le_two_pow hn
  obtain ⟨t, ht0, ht1⟩ := SEITZ6.exists_ne_zero_one (K := fixedField σ) h4
  have h1σ : σ (1 : K) = 1 := map_one σ
  have htσ : σ (t : K) = (t : K) := t.2
  have ht0' : (t : K) ≠ 0 := fun h => ht0 (Subtype.ext h)
  have h1t : ((1 : K) + t) ≠ 0 := fun h => ht1 (Subtype.ext (CharTwo.add_eq_zero.1 h).symm)
  have h1tσ : σ ((1 : K) + t) = 1 + t := by rw [map_add, h1σ, htσ]
  have hab : xHg hσ 1 h1σ ≠ xHg hσ t htσ := fun h => by
    have := xPar_injective (F := rootOperatorFamily d4) (K := K)
      (isRoot_d4 (by norm_num : 22 < 24)) (congrArg Subtype.val h)
    exact ht1 (Subtype.ext this.symm)
  have hcomm : Commute (xHg hσ 1 h1σ) (xHg hσ t htσ) := by
    refine Subtype.ext ?_
    show xd 22 (1 : K) * xd 22 (t : K) = xd 22 (t : K) * xd 22 1
    rw [← xd_add, ← xd_add, add_comm]
  have hxH : ∀ c (hc : σ c = c), xHg hσ c hc ∈ H := fun c hc => by
    rw [xHg_eq_psiB hσ hc]
    exact hL (Bsub_le_Lsub σ hσ ⟨_, rfl⟩)
  obtain ⟨V, hVH, hV, haV, hbV⟩ :=
    CFSG.GorensteinWalter.exists_kleinFour_of_commuting_involutions_le H _ _
      (xHg_isInvolution hσ h1σ one_ne_zero) (xHg_isInvolution hσ htσ ht0') hab hcomm
      (hxH _ h1σ) (hxH _ htσ)
  have hnorm : NormalizedBy R V := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hRn v (hVH hv) r hr, fun hr => ?_⟩
    have := hRn v⁻¹ (H.inv_mem (hVH hv)) _ hr
    rwa [show v⁻¹ * (v * r * v⁻¹) * v⁻¹⁻¹ = r by group] at this
  have hsolv : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hab1 : xHg hσ 1 h1σ * xHg hσ t htσ = xHg hσ (1 + t) h1tσ :=
    Subtype.ext (xd_add 22 (1 : K) (t : K)).symm
  have hw := ambient_fourgroup_fixed_order_identity V R hV hodd hsolv hnorm (xHg hσ 1 h1σ)
    (xHg hσ t htσ) haV hbV (fun h => xH_ne_one one_ne_zero (congrArg Subtype.val h))
    (fun h => xH_ne_one ht0' (congrArg Subtype.val h)) hab
  rw [hab1, cent_R_trivial hσ hn hK hF hL hRn hodd one_ne_zero h1σ,
    cent_R_trivial hσ hn hK hF hL hRn hodd ht0' htσ,
    cent_R_trivial hσ hn hK hF hL hRn hodd h1t h1tσ] at hw
  simp only [Subgroup.card_bot, mul_one] at hw
  exact Subgroup.card_eq_one.1 (Nat.eq_one_of_mul_eq_one_right hw)

end CFSG.RankThree.PartOne.SEITZ7
