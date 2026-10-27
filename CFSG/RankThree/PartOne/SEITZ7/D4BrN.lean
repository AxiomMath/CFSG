module

public import CFSG.RankThree.PartOne.SEITZ7.D4AB
public import CFSG.RankThree.PartOne.SEITZ6.G2BrN

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

theorem posUnipotent_twisted (σ : K →+* K) :
    posUnipotent (twistedDatum σ) = (Uhat σ).subgroupOf (twistedGroup σ) := by
  have h : posUnipotent (twistedDatum σ) =
      ⨆ γ ∈ {γ : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 γ ∧ 0 < ht γ}, twistedRootGroup σ γ := by
    rw [CFSG.LieType.Steinberg.posUnipotent, twisted_setOf_pos_eq]
    rfl
  rw [h, iSup_twistedRootGroup_eq_subgroupOf σ (S := {γ | IsRoot .G2 γ ∧ 0 < ht γ})
    fun β hβ => hβ.1]
  congr 1
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγR, hγp⟩ := hγ
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγR
    have hk' : k < 12 := by simpa [len_roots] using hk
    have hkp := ht_pos_aux k hk' hγp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkp
    refine le_iSup₂_of_le k ?_ le_rfl
    rcases hkp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [posT]
  · refine iSup₂_le fun p hp => ?_
    have hp' := lt_twelve_of_mem_posT hp
    have hpos : 0 < ht (rt p) := by
      rcases mem_posT hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    exact le_iSup₂_of_le (rt p) ⟨isRoot_rt hp', hpos⟩ le_rfl

theorem Tt_normalizes (σ : K →+* K) {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    (⨆ i, hHat σ i) ≤ Subgroup.normalizer (twistedRootGroup σ β : Set (twistedGroup σ)) := by
  refine iSup_le fun l => ?_
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hHat_conj_mem σ l hβ hh hx
  · intro hx
    have := hHat_conj_mem σ l hβ (inv_mem hh) hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this

theorem Tt_conj_X {t : twistedGroup σ} (ht : t ∈ ⨆ i, hHat σ i)
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) {y : adjointGroup d4 K}
    (hy : y ∈ twistedRootSubgroupD4 σ β) :
    (t : adjointGroup d4 K) * y * (t : adjointGroup d4 K)⁻¹ ∈ twistedRootSubgroupD4 σ β := by
  have hy' : (⟨y, twistedRootSubgroupD4_le_twistedGroup σ hβ hy⟩ : twistedGroup σ) ∈
      twistedRootGroup σ β := Subgroup.mem_subgroupOf.2 hy
  exact Subgroup.mem_subgroupOf.1 ((Subgroup.mem_normalizer_iff.1 (Tt_normalizes σ hβ ht) _).1 hy')

theorem Tt_conj_Upt {t : twistedGroup σ} (ht : t ∈ ⨆ i, hHat σ i) {y : adjointGroup d4 K}
    (hy : y ∈ Upt σ) : (t : adjointGroup d4 K) * y * (t : adjointGroup d4 K)⁻¹ ∈ Upt σ := by
  have hy7 : ∀ y ∈ twistedRootSubgroupD4 σ (rt 7), (t : adjointGroup d4 K) * y *
      (t : adjointGroup d4 K)⁻¹ ∈ twistedRootSubgroupD4 σ (rt 7) := fun y hy =>
    Tt_conj_X ht (isRoot_rt (by norm_num)) hy
  have hy1 : ∀ y ∈ twistedRootSubgroupD4 σ (rt 1), (t : adjointGroup d4 K) * y *
      (t : adjointGroup d4 K)⁻¹ ∈ twistedRootSubgroupD4 σ (rt 1) := fun y hy =>
    Tt_conj_X ht (isRoot_rt (by norm_num)) hy
  have hle : Upt σ ≤ (Upt σ).comap (MulAut.conj (t : adjointGroup d4 K)).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_sup_left (hy7 x hx)
    · exact Subgroup.mem_sup_right (hy1 x hx)
  exact hle hy

theorem Tt_conj_Upt_iff {t : twistedGroup σ} (ht : t ∈ ⨆ i, hHat σ i) {y : adjointGroup d4 K} :
    (t : adjointGroup d4 K) * y * (t : adjointGroup d4 K)⁻¹ ∈ Upt σ ↔ y ∈ Upt σ := by
  refine ⟨fun h => ?_, Tt_conj_Upt ht⟩
  have := Tt_conj_Upt (inv_mem ht) h
  rwa [show ((t⁻¹ : twistedGroup σ) : adjointGroup d4 K) * ((t : adjointGroup d4 K) * y *
      (t : adjointGroup d4 K)⁻¹) * ((t⁻¹ : twistedGroup σ) : adjointGroup d4 K)⁻¹ = y by
    simp only [Subgroup.coe_inv]; group] at this

theorem commute_Uhat_xH [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {u : adjointGroup d4 K}
    (hu : u ∈ Uhat σ) (c : K) : u * xH c = xH c * u := by
  have hle : Uhat σ ≤ Subgroup.centralizer ({xH c} : Set (adjointGroup d4 K)) := by
    refine iSup₂_le fun p hp x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show xH c * x = x * xH c
    rcases mem_posT hp with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨c', -, rfl⟩ := (mem_XB hσ x).1 hx
      exact (commute_22_2 c c')
    · obtain ⟨c', rfl⟩ := (mem_XA hσ x).1 hx
      exact commute_xH_xA σ c c'
    · obtain ⟨c', rfl⟩ := (mem_XAB hσ x).1 hx
      exact ((commute_22_5 c c').mul_right (commute_22_7 c (σ c'))).mul_right
        (commute_22_9 c (σ (σ c'))) |>.eq
    · obtain ⟨c', rfl⟩ := (mem_XAAB hσ x).1 hx
      exact ((commute_22_12 c c').mul_right (commute_22_15 c (σ c'))).mul_right
        (commute_22_13 c (σ (σ c'))) |>.eq
    · obtain ⟨c', -, rfl⟩ := (mem_XN hσ x).1 hx
      exact (commute_22_19 c c').eq
    · obtain ⟨c', -, rfl⟩ := (mem_XH hσ x).1 hx
      show xd 22 c * xd 22 c' = xd 22 c' * xd 22 c
      rw [← xd_add, ← xd_add, add_comm]
  exact (Subgroup.mem_centralizer_iff.1 (hle hu) (xH c) (Set.mem_singleton _)).symm

theorem twisted_bruhatExtras' (σ : K →+* K) : BruhatExtras (twistedDatum σ) (hHat σ) where
  borel_inf_negUnipotent := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have hB : borel (adjDatum (rootOperatorFamily d4) K) (torus (τ := d4) K) ⊓
        negUnipotent (adjDatum (rootOperatorFamily d4) K) = ⊥ :=
      eq_bot_iff.2 ((inf_le_inf
        (sup_le (iSup_le fun i => (torus_le_diag i).trans (diag_le_tri htHom))
          ((iSup₂_le fun γ hγ => rootGroup_le_unip htHom hγ.2).trans (unip_le_tri htHom)))
        (iSup₂_le fun γ hγ => rootGroup_le_unip (-htHom) (by
          rw [AddMonoidHom.neg_apply, htHom_apply]
          exact neg_pos.2 hγ.2))).trans (tri_inf_unip_neg htHom).le)
    have h : (g : adjointGroup d4 K) ∈
        borel (adjDatum (rootOperatorFamily d4) K) (torus (τ := d4) K) ⊓
          negUnipotent (adjDatum (rootOperatorFamily d4) K) :=
      Subgroup.mem_inf.2 ⟨borel_twisted_le σ hg.1, negUnipotent_twisted_le σ hg.2⟩
    rw [hB, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem inversionUnipotent_simple_le_tw (σ : K →+* K) :
    inversionUnipotent (twistedDatum σ)
      ((coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem.simple (ng 1)) ≤
        twistedRootGroup σ (rt 1) := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγR, hpos, hneg⟩ := hγ
  have hγR' : IsRoot .G2 γ := by
    rw [twistedDatum_roots] at hγR
    exact hγR
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγR'
  have hk' : k < 12 := by simpa [len_roots] using hk
  have e : weylAction (twistedDatum σ).isFiniteType
      ((coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem.simple (ng 1)) (rt k) =
        reflect .G2 (ng 1) (rt k) :=
    weylAction_simple_eq_reflect (isFiniteType_cartan .G2) (ng 1) (rt k)
  rw [e] at hneg
  have := CFSG.RankThree.PartOne.SEITZ6.simple_inversion_check k hk' hpos hneg
  subst this
  exact le_rfl

theorem Upt_le_Uhat (σ : K →+* K) : Upt σ ≤ Uhat σ := by
  refine sup_le ?_ ?_
  · exact le_iSup₂_of_le 7 (by simp [posT]) le_rfl
  · exact le_iSup₂_of_le 1 (by simp [posT]) le_rfl

theorem Upt_le_twistedGroup (σ : K →+* K) : Upt σ ≤ twistedGroup σ :=
  sup_le (twistedRootSubgroupD4_le_twistedGroup σ (isRoot_rt (by norm_num)))
    (twistedRootSubgroupD4_le_twistedGroup σ (isRoot_rt (by norm_num)))

@[expose] noncomputable def xHg (hσ : ∀ c, σ (σ (σ c)) = c) [CharP K 2] (d : K) (hd : σ d = d) :
    twistedGroup σ :=
  ⟨xH d, twistedRootSubgroupD4_le_twistedGroup σ (isRoot_rt (by norm_num))
    ((mem_XH hσ _).2 ⟨d, hd, rfl⟩)⟩

theorem xHg_mem [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (d : K) (hd : σ d = d) :
    xHg hσ d hd ∈ twistedRootGroup σ (rt 7) :=
  Subgroup.mem_subgroupOf.2 ((mem_XH hσ _).2 ⟨d, hd, rfl⟩)

theorem xH_ne_one [CharP K 2] {d : K} (hd : d ≠ 0) : (xH d : adjointGroup d4 K) ≠ 1 := fun h =>
  hd (xPar_injective (F := rootOperatorFamily d4) (K := K) (isRoot_d4 (by norm_num : 22 < 24))
    (h.trans (xd_zero 22).symm))

theorem weyl_stab_h_tw (σ : K →+* K) (w : (coxeterMatrix (twistedDatum σ).isFiniteType).Group)
    (hw : weylAction (twistedDatum σ).isFiniteType w (rt 7) = rt 7) :
    w = 1 ∨ w = (coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem.simple (ng 1) :=
  CFSG.RankThree.PartOne.SEITZ6.weyl_stab_h (K := ZMod 2) w hw

theorem bruhat_stab_h_tw [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {g : twistedGroup σ} {d : K}
    (hd : d ≠ 0) (hdσ : σ d = d)
    (hg : (g : adjointGroup d4 K) * xH d * (g : adjointGroup d4 K)⁻¹ ∈ Upt σ) :
    g ∈ borel (twistedDatum σ) (hHat σ) ∨
      ∃ b ∈ borel (twistedDatum σ) (hHat σ), ∃ u ∈ twistedRootGroup σ (rt 1),
        g = b * nHat σ (ng 1) * u := by
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  have hBU := twisted_bruhatExtras' σ
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hw
  have hpos : ∀ z ∈ Upt σ, ∀ z' : twistedGroup σ, (z' : adjointGroup d4 K) = z →
      z' ∈ borel (twistedDatum σ) (hHat σ) := fun z hz z' hz' =>
    posUnipotent_le_borel (by
      rw [posUnipotent_twisted]
      exact Subgroup.mem_subgroupOf.2 (hz' ▸ Upt_le_Uhat σ hz))
  have huP : u ∈ posUnipotent (twistedDatum σ) := inversionUnipotent_le_posUnipotent w hu
  have huU : ((u : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
    have h1 := huP
    rw [posUnipotent_twisted] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨t, htl, hrt0⟩ := weylAction_long (ZMod 2) w 7 (by simp [longPos])
  have hrt : weylAction (twistedDatum σ).isFiniteType w (rt 7) = rt t := hrt0
  have ht12 : t < 12 := by
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at htl
    omega
  have hr7 : rt 7 ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_rt (by norm_num)
  have hxt : nrep hct w * xHg hσ d hdσ * (nrep hct w)⁻¹ ∈ twistedRootGroup σ (rt t) := by
    have h := (actsAs_nrep hct w).conj_mem hr7 (xHg_mem hσ d hdσ)
    rw [hrt] at h
    exact h
  set z : twistedGroup σ := nrep hct w * xHg hσ d hdσ * (nrep hct w)⁻¹ with hz
  have hzne : z ≠ 1 := by
    intro h1
    have h2 : xHg hσ d hdσ = 1 := by
      have : xHg hσ d hdσ = (nrep hct w)⁻¹ * z * nrep hct w := by rw [hz]; group
      rw [this, h1]; group
    exact xH_ne_one hd (congrArg Subtype.val h2)
  have hcomm : u * xHg hσ d hdσ = xHg hσ d hdσ * u :=
    Subtype.ext (commute_Uhat_xH hσ huU d)
  have hconj : (b * nrep hct w * u) * xHg hσ d hdσ * (b * nrep hct w * u)⁻¹ = b * z * b⁻¹ := by
    rw [hz, show (b * nrep hct w * u) * xHg hσ d hdσ * (b * nrep hct w * u)⁻¹ =
      b * (nrep hct w * (u * xHg hσ d hdσ * u⁻¹) * (nrep hct w)⁻¹) * b⁻¹ by group, hcomm]
    group
  have hcoe : ((xHg hσ d hdσ : twistedGroup σ) : adjointGroup d4 K) = xH d := rfl
  have hbz : ((b * z * b⁻¹ : twistedGroup σ) : adjointGroup d4 K) ∈ Upt σ := by
    have := hg
    rw [← hconj]
    simpa [hcoe] using this
  have hB : z ∈ borel (twistedDatum σ) (hHat σ) := by
    have h1 : b * z * b⁻¹ ∈ borel (twistedDatum σ) (hHat σ) := hpos _ hbz _ rfl
    have := mul_mem (mul_mem (inv_mem hb) h1) hb
    rwa [show b⁻¹ * (b * z * b⁻¹) * b = z by group] at this
  have hneg : ∀ {t' : ℕ}, t' < 12 → ht (rt t') < 0 → z ∈ twistedRootGroup σ (rt t') → False := by
    intro t' ht' hneg' hz'
    have hmem : z ∈ negUnipotent (twistedDatum σ) :=
      rootGroup_le_negUnipotent (by rw [twistedDatum_roots]; exact isRoot_rt ht') hneg' hz'
    have := hBU.borel_inf_negUnipotent
    have h3 : z ∈ borel (twistedDatum σ) (hHat σ) ⊓ negUnipotent (twistedDatum σ) := ⟨hB, hmem⟩
    rw [this, Subgroup.mem_bot] at h3
    exact hzne h3
  have hbTU : ∃ t0 ∈ ⨆ i, hHat σ i, ∃ u0 ∈ posUnipotent (twistedDatum σ), b = t0 * u0 := by
    have hb' : b ∈ (borel (twistedDatum σ) (hHat σ) : Set (twistedGroup σ)) := hb
    rw [coe_borel hct, Set.mem_mul] at hb'
    obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hb'
    exact ⟨t0, ht0, u0, hu0, rfl⟩
  have ht7 : t = 7 := by
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at htl
    rcases htl with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hbTU
      have hu0U : ((u0 : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
        rw [posUnipotent_twisted] at hu0
        exact Subgroup.mem_subgroupOf.1 hu0
      obtain ⟨c, hc0, hc3, hc7, hcu⟩ := exists_ordT hσ hu0U
      obtain ⟨c', hc'σ, hc'⟩ := (mem_XB hσ _).1 (Subgroup.mem_subgroupOf.1 hxt)
      have h1 : (u0 : adjointGroup d4 K) * (z : adjointGroup d4 K) * (u0 : adjointGroup d4 K)⁻¹ ∈
          Upt σ := by
        have := (Tt_conj_Upt_iff ht0 (y := (u0 : adjointGroup d4 K) * z *
          (u0 : adjointGroup d4 K)⁻¹)).1 (by simpa [mul_assoc] using hbz)
        simpa using this
      rw [hc', hcu] at h1
      have := eq_zero_of_conj_xB hσ c c' hc'σ h1
      apply hzne
      apply Subtype.ext
      rw [hc', this]
      exact (xd_zero 2)
    · exfalso
      exact hneg (t' := 2) (by norm_num) (by decide +kernel) hxt
    · exfalso
      obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hbTU
      have hu0U : ((u0 : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
        rw [posUnipotent_twisted] at hu0
        exact Subgroup.mem_subgroupOf.1 hu0
      obtain ⟨c, hc0, hc3, hc7, hcu⟩ := exists_ordT hσ hu0U
      obtain ⟨c', hc'σ, hc'⟩ := (mem_XN hσ _).1 (Subgroup.mem_subgroupOf.1 hxt)
      have h1 : (u0 : adjointGroup d4 K) * (z : adjointGroup d4 K) * (u0 : adjointGroup d4 K)⁻¹ ∈
          Upt σ := by
        have := (Tt_conj_Upt_iff ht0 (y := (u0 : adjointGroup d4 K) * z *
          (u0 : adjointGroup d4 K)⁻¹)).1 (by simpa [mul_assoc] using hbz)
        simpa using this
      rw [hc', hcu] at h1
      have := eq_zero_of_conj_xN hσ c c' h1
      apply hzne
      apply Subtype.ext
      rw [hc', this]
      exact (xd_zero 19)
    · exfalso
      exact hneg (t' := 6) (by norm_num) (by decide +kernel) hxt
    · rfl
    · exfalso
      exact hneg (t' := 10) (by norm_num) (by decide +kernel) hxt
  subst ht7
  rcases weyl_stab_h_tw σ w hrt with rfl | rfl
  · left
    rw [nrep_one hct, mul_one]
    exact mul_mem hb (posUnipotent_le_borel huP)
  · right
    exact ⟨b, hb, u, inversionUnipotent_simple_le_tw σ hu,
      congrArg (fun x => b * x * u) (nrep_simple hct (ng 1))⟩

theorem mem_borel_of_mem_Upt {z : twistedGroup σ} (hz : (z : adjointGroup d4 K) ∈ Upt σ) :
    z ∈ borel (twistedDatum σ) (hHat σ) :=
  posUnipotent_le_borel (by
    rw [posUnipotent_twisted]
    exact Subgroup.mem_subgroupOf.2 (Upt_le_Uhat σ hz))

theorem xA_ne_one [CharP K 2] {a : K} (ha : a ≠ 0) : xA σ a ≠ 1 := by
  intro h
  have e0 : (1 : adjointGroup d4 K) = ordT σ (mkT 0 0 0 0 0 0) := by
    rw [ordT_mkT]
    simp [xB, xA, xAB, xAAB, xN, xH, xd_zero]
  have e1 : xA σ a = ordT σ (mkT 0 a 0 0 0 0) := by
    rw [ordT_mkT]
    simp [xB, xAB, xAAB, xN, xH, xd_zero]
  rw [e1, e0] at h
  have := (ordT_inj σ h).2.1
  simp [mkT] at this
  exact ha this

theorem reflect_1_5' : reflect .G2 (ng 1) (rt 1) = rt 5 := by decide +kernel

theorem normalizer_Upt_borel [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {g : twistedGroup σ}
    (hg : ∀ x ∈ Upt σ, (g : adjointGroup d4 K) * x * (g : adjointGroup d4 K)⁻¹ ∈ Upt σ) :
    g ∈ borel (twistedDatum σ) (hHat σ) := by
  have h7 : (g : adjointGroup d4 K) * xH 1 * (g : adjointGroup d4 K)⁻¹ ∈ Upt σ :=
    hg _ ((mem_Upt_iff hσ).2 ⟨1, 0, map_one σ, by simp [xA, xd_zero]⟩)
  rcases bruhat_stab_h_tw hσ one_ne_zero (map_one σ) h7 with h | ⟨b, hb, u, hu, rfl⟩
  · exact h
  · exfalso
    have hBU := twisted_bruhatExtras' σ
    have hr1 : IsRoot .G2 (rt 1) := isRoot_rt (by norm_num)
    have hyA : xA σ 1 ∈ twistedRootSubgroupD4 σ (rt 1) := (mem_XA hσ _).2 ⟨1, rfl⟩
    set y : twistedGroup σ := ⟨xA σ 1, twistedRootSubgroupD4_le_twistedGroup σ hr1 hyA⟩ with hy
    have hy' : y ∈ twistedRootGroup σ (rt 1) := Subgroup.mem_subgroupOf.2 hyA
    have hycomm : u * y = y * u := Subtype.ext
      (commute_of_mem_twistedRootSubgroupD4 σ hr1 (Subgroup.mem_subgroupOf.1 hu) hyA).eq
    have hz : nHat σ (ng 1) * y * (nHat σ (ng 1))⁻¹ ∈ twistedRootGroup σ (rt 5) := by
      have := nHat_conj_mem σ (ng 1) hr1 hy'
      rwa [reflect_1_5'] at this
    set z : twistedGroup σ := nHat σ (ng 1) * y * (nHat σ (ng 1))⁻¹ with hzdef
    have hyU : (y : adjointGroup d4 K) ∈ Upt σ :=
      (mem_Upt_iff hσ).2 ⟨0, 1, map_zero σ, by simp [hy, xd_zero, xH]⟩
    have hbz : ((b * z * b⁻¹ : twistedGroup σ) : adjointGroup d4 K) ∈ Upt σ := by
      have h1 := hg _ hyU
      have e : b * nHat σ (ng 1) * u * y * (b * nHat σ (ng 1) * u)⁻¹ = b * z * b⁻¹ := by
        rw [hzdef, show b * nHat σ (ng 1) * u * y * (b * nHat σ (ng 1) * u)⁻¹ =
          b * (nHat σ (ng 1) * (u * y * u⁻¹) * (nHat σ (ng 1))⁻¹) * b⁻¹ by group, hycomm]
        group
      rw [← e]
      simpa using h1
    have hB : z ∈ borel (twistedDatum σ) (hHat σ) := by
      have h1 : b * z * b⁻¹ ∈ borel (twistedDatum σ) (hHat σ) := mem_borel_of_mem_Upt hbz
      have := mul_mem (mul_mem (inv_mem hb) h1) hb
      rwa [show b⁻¹ * (b * z * b⁻¹) * b = z by group] at this
    have hmem : z ∈ negUnipotent (twistedDatum σ) :=
      rootGroup_le_negUnipotent (by rw [twistedDatum_roots]; exact isRoot_rt (by norm_num))
        (by exact (by decide +kernel : ht (rt 5) < 0)) hz
    have h3 : z ∈ borel (twistedDatum σ) (hHat σ) ⊓ negUnipotent (twistedDatum σ) := ⟨hB, hmem⟩
    rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at h3
    have h4 : y = 1 := by
      have : y = (nHat σ (ng 1))⁻¹ * z * nHat σ (ng 1) := by rw [hzdef]; group
      rw [this, h3]; group
    exact xA_ne_one (σ := σ) one_ne_zero (congrArg Subtype.val h4)

theorem normalizer_Upt_form [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (hne : ∃ a, σ a ≠ a)
    {g : twistedGroup σ}
    (hg : ∀ x ∈ Upt σ, (g : adjointGroup d4 K) * x * (g : adjointGroup d4 K)⁻¹ ∈ Upt σ) :
    ∃ t0 ∈ ⨆ i, hHat σ i, ∃ a b c : K, σ b = b ∧ σ c = c ∧
      (g : adjointGroup d4 K) = (t0 : adjointGroup d4 K) * (xA σ a * xN b * xH c) := by
  have hB := normalizer_Upt_borel hσ hg
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hb' : g ∈ (borel (twistedDatum σ) (hHat σ) : Set (twistedGroup σ)) := hB
  rw [coe_borel hct, Set.mem_mul] at hb'
  obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hb'
  have hu0U : ((u0 : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
    rw [posUnipotent_twisted] at hu0
    exact Subgroup.mem_subgroupOf.1 hu0
  obtain ⟨c, hc0, hc3, hc7, hcu⟩ := exists_ordT hσ hu0U
  have hn : ∀ a : K, ordT σ c * xA σ a * (ordT σ c)⁻¹ ∈ Upt σ := by
    intro a
    have h1 := hg (xA σ a) ((mem_Upt_iff hσ).2 ⟨0, a, map_zero σ, by simp [xH, xd_zero]⟩)
    have h2 := (Tt_conj_Upt_iff ht0 (y := (u0 : adjointGroup d4 K) * xA σ a *
      (u0 : adjointGroup d4 K)⁻¹)).1 (by simpa [mul_assoc] using h1)
    rwa [hcu] at h2
  obtain ⟨h0, h4, h8⟩ := coords_of_conj_xA hσ hne c hc0 hn
  refine ⟨t0, ht0, c 1, c 3, c 7, hc3, hc7, ?_⟩
  rw [Subgroup.coe_mul, hcu]
  congr 1
  unfold ordT
  rw [h0, h4, h8]
  simp [xB, xAB, xAAB, xd_zero, mul_assoc]

end CFSG.RankThree.PartOne.SEITZ7
