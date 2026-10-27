module

public import CFSG.Timmesfeld.ARS.CaseBOmega

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

theorem sq_mem_of_mem_M (h : Hyp G R) {X : Subgroup G} (hX : X ∈ R) {m : G}
    (hm : m ∈ M R X) : m * m ∈ X := by
  have := h.finite
  have hR := h.root
  have hcomm := (Q_eq_M h hX).2.2.1
  let S : Subgroup G :=
    { carrier := {y | y ∈ M R X ∧ y * y ∈ X}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have hc : ⁅a⁻¹, b⁆ ∈ X := by
          rw [← hcomm]
          exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ha) hb
        have e : a * b * (a * b) = a * a * ⁅a⁻¹, b⁆ * (b * b) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact X.mul_mem (X.mul_mem ha2 hc) hb2
      one_mem' := ⟨Subgroup.one_mem _, by rw [one_mul]; exact X.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        rw [← _root_.mul_inv_rev]
        exact X.inv_mem ha2 }
  have hle : M R X ≤ S := by
    refine sup_le (fun x hx => ⟨QD.le_M_self hx, by rw [hR.mul_self X hX x hx]; exact
      X.one_mem⟩) (iSup₂_le fun B hB x hx => ⟨QD.le_M hB hx, ?_⟩)
    rw [hR.mul_self B hB.1.1 x hx]
    exact X.one_mem
  exact (hle hm).2

theorem conjSub_hidAt_of (hR : IsRootClass R) {g : G}
    (hg : ∀ a b : Fin 4, a ≠ b → conjSub (xg Ψ a b) g = xg Ψ a b) {s₁ s₂ t₁ t₂ : Fin 4}
    (h12 : s₁ ≠ s₂) (h34 : t₁ ≠ t₂) (h14 : s₁ ≠ t₂) (h23 : s₂ ≠ t₁) :
    conjSub (hidAt R Ψ s₁ s₂ t₁ t₂) g = hidAt R Ψ s₁ s₂ t₁ t₂ := by
  rw [hidAt, conjSub_inf, conjSub_W hR, conjSub_inf, conjSub_centralizer', conjSub_centralizer',
    hg _ _ h14, hg _ _ h23, hg _ _ h12, hg _ _ h34]

section Torus

variable (h : Hyp G R) (hS : Skel R Ψ) {K : Type*} [Field K] [Finite K] [CharP K 2]
  {φ : ↥(xg Ψ 0 3 ⊔ xg Ψ 3 0) ≃* SpecialLinearGroup (Fin 2) K}
  (hφA : ((xg Ψ 0 3).subgroupOf (xg Ψ 0 3 ⊔ xg Ψ 3 0)).map φ.toMonoidHom = upperUnipotent K)
  (hφB : ((xg Ψ 3 0).subgroupOf (xg Ψ 0 3 ⊔ xg Ψ 3 0)).map φ.toMonoidHom = lowerUnipotent K)
include h hS hφA hφB

theorem conjSub_xg_torPar (c : Kˣ) {a b : Fin 4} (hab : a ≠ b) :
    conjSub (xg Ψ a b) (FrameSL3.torPar φ c) = xg Ψ a b := by
  have := h.finite
  have hR := h.root
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  have h01 : conjSub (xg Ψ 0 1) (FrameSL3.torPar φ c) = xg Ψ 0 1 := by
    refine Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA
      ⟨hS.mem_lambdaSet_row hR (by decide) (by decide) (by decide), hS.mem 0 1 (by decide),
        hS.special (by decide) (by decide) (by decide)⟩ c
  have h02 : conjSub (xg Ψ 0 2) (FrameSL3.torPar φ c) = xg Ψ 0 2 := by
    refine Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA
      ⟨hS.mem_lambdaSet_row hR (by decide) (by decide) (by decide), hS.mem 0 2 (by decide),
        hS.special (by decide) (by decide) (by decide)⟩ c
  have h13 : conjSub (xg Ψ 1 3) (FrameSL3.torPar φ c) = xg Ψ 1 3 := by
    refine Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA
      ⟨hS.mem_lambdaSet_col hR (by decide) (by decide) (by decide), hS.mem 1 3 (by decide),
        (hS.special (by decide : (1 : Fin 4) ≠ 3) (by decide) (by decide)).symm⟩ c
  have h23 : conjSub (xg Ψ 2 3) (FrameSL3.torPar φ c) = xg Ψ 2 3 := by
    refine Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA
      ⟨hS.mem_lambdaSet_col hR (by decide) (by decide) (by decide), hS.mem 2 3 (by decide),
        (hS.special (by decide : (2 : Fin 4) ≠ 3) (by decide) (by decide)).symm⟩ c
  have h03 : conjSub (xg Ψ 0 3) (FrameSL3.torPar φ c) = xg Ψ 0 3 :=
    Sec8Field.conjSub_torPar hφA c
  have h30 : conjSub (xg Ψ 3 0) (FrameSL3.torPar φ c) = xg Ψ 3 0 :=
    conjSub_eq_self_iff.2 (NaturalModule.coe_mem_normalizer hφB le_sup_right (by
      rw [MulEquiv.apply_symm_apply]
      exact NaturalModule.diagElt_mem_normalizer_lowerUnipotent c))
  have hmemV : FrameSL3.torPar φ c ∈ xg Ψ 0 3 ⊔ xg Ψ 3 0 := Sec8Field.torPar_mem_sup φ c
  have hcV : ∀ {x y : Fin 4}, x ≠ y → Commuting (xg Ψ 0 3) (xg Ψ x y) →
      Commuting (xg Ψ 3 0) (xg Ψ x y) → conjSub (xg Ψ x y) (FrameSL3.torPar φ c) = xg Ψ x y := by
    intro x y _ h1 h2
    refine conjSub_of_forall_commute fun z hz => ?_
    have hle : xg Ψ 0 3 ⊔ xg Ψ 3 0 ≤ Subgroup.centralizer {z} :=
      sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.2 (h1 w hw z hz))
        (fun w hw => Subgroup.mem_centralizer_singleton_iff.2 (h2 w hw z hz))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hmemV)
  have h12 : conjSub (xg Ψ 1 2) (FrameSL3.torPar φ c) = xg Ψ 1 2 :=
    hcV (by decide) (commuting_xg (by decide) (by decide) (by decide) (by decide))
      (commuting_xg (by decide) (by decide) (by decide) (by decide))
  have h21 : conjSub (xg Ψ 2 1) (FrameSL3.torPar φ c) = xg Ψ 2 1 :=
    hcV (by decide) (commuting_xg (by decide) (by decide) (by decide) (by decide))
      (commuting_xg (by decide) (by decide) (by decide) (by decide))
  have hcomm : ∀ {x y z : Fin 4}, x ≠ y → y ≠ z → x ≠ z →
      conjSub (xg Ψ x y) (FrameSL3.torPar φ c) = xg Ψ x y →
      conjSub (xg Ψ y z) (FrameSL3.torPar φ c) = xg Ψ y z →
      conjSub (xg Ψ x z) (FrameSL3.torPar φ c) = xg Ψ x z := by
    intro x y z hxy hyz hxz e1 e2
    rw [← commutator_xg hxy hyz hxz, conjSub, Subgroup.map_commutator, ← conjSub, ← conjSub, e1,
      e2]
  have h10 := hcomm (by decide : (1 : Fin 4) ≠ 3) (by decide) (by decide) h13 h30
  have h20 := hcomm (by decide : (2 : Fin 4) ≠ 3) (by decide) (by decide) h23 h30
  have h31 := hcomm (by decide : (3 : Fin 4) ≠ 0) (by decide) (by decide) h30 h01
  have h32 := hcomm (by decide : (3 : Fin 4) ≠ 0) (by decide) (by decide) h30 h02
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption

end Torus

section Perm

variable [CharP F 2]

variable (Ψ) in
noncomputable abbrev perm (σ : Equiv.Perm (Fin 4)) : SpecialLinearGroup (Fin 4) F →* G :=
  Ψ.comp (MulAut.conj (pm σ)).toMonoidHom

theorem xg_perm (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) :
    xg (perm Ψ σ) a b = xg Ψ (σ a) (σ b) := by
  by_cases hab : a = b
  · subst hab
    simp [xg, X]
  · rw [xg, ← Subgroup.map_map]
    change (conjSub (X a b) (pm σ)).map Ψ = _
    rw [conjSub_X_pm σ hab]

theorem Skel.perm (hS : Skel R Ψ) (σ : Equiv.Perm (Fin 4)) : Skel R (perm Ψ σ) where
  inj := hS.inj.comp (MulAut.conj (pm σ)).injective
  mem a b hab := by
    rw [xg_perm]
    exact hS.mem _ _ (σ.injective.ne hab)
  opp a b hab := by
    rw [xg_perm, xg_perm]
    exact hS.opp _ _ (σ.injective.ne hab)

theorem hidAt_perm (σ : Equiv.Perm (Fin 4)) (s₁ s₂ t₁ t₂ : Fin 4) :
    hidAt R (perm Ψ σ) s₁ s₂ t₁ t₂ = hidAt R Ψ (σ s₁) (σ s₂) (σ t₁) (σ t₂) := by
  simp only [hidAt, xg_perm]

theorem Om_perm (σ : Equiv.Perm (Fin 4)) :
    Om R (perm Ψ σ) = lambdaSet R (xg Ψ (σ 0) (σ 3)) ∩ lambdaSet R (xg Ψ (σ 1) (σ 2)) := by
  simp only [Om, xg_perm]

end Perm

variable (R Ψ) in
@[expose] def PtHyp : Prop :=
  Sec8 R (xg Ψ 0 3) ∧ ∃ Δ : Set (Subgroup G), IsWeakTI R Δ ∧ xg Ψ 0 3 ∈ Δ

theorem ptHyp_of_hypB (hB : HypB G R (xg Ψ 0 3)) : PtHyp R Ψ :=
  ⟨hB.sec8, hB.exists_isWeakTI⟩

theorem PtHyp.perm [CharP F 2] (hR : IsRootClass R) (hP : PtHyp R Ψ) (σ : Equiv.Perm (Fin 4)) :
    PtHyp R (perm Ψ σ) := by
  obtain ⟨h8, Δ, hΔ, hAΔ⟩ := hP
  have e : xg (CaseB.perm Ψ σ) 0 3 = conjSub (xg Ψ 0 3) (Ψ (pm σ)) := by
    rw [xg_perm, conjSub_xg σ (by decide)]
  rw [PtHyp, e]
  exact ⟨h8.conjSub hR _, conjSet Δ (Ψ (pm σ)), Sec5.isWeakTI_conjSet hR hΔ _,
    conjSub_mem_conjSet hAΔ _⟩

abbrev σU : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 1 3

abbrev σT : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

abbrev σT₀ : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

variable (R Ψ) in
noncomputable abbrev hU : Subgroup G := hidAt R Ψ 0 3 1 2

variable (Ψ) in
noncomputable abbrev cent4 : Subgroup G :=
  Subgroup.centralizer (((xg Ψ 0 3 ⊔ xg Ψ 3 0) ⊔ (xg Ψ 1 2 ⊔ xg Ψ 2 1) : Subgroup G) : Set G)

section HiddenU

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ)
include h hS

theorem hid_eq_1032 : hid R Ψ = hidAt R Ψ 1 0 3 2 := by
  have e := conjSub_hidAt (Ψ := Ψ) h.root σT (s₁ := 0) (s₂ := 1) (t₁ := 2) (t₂ := 3)
    (by decide) (by decide) (by decide) (by decide)
  have hT : (pm σT : SpecialLinearGroup (Fin 4) F) = pm (Equiv.swap 0 1) * pm (Equiv.swap 2 3) :=
    (pm_mul _ _).symm
  rw [hT, map_mul, conjSub_mul, conjSub_hid_swap23 h hS, conjSub_hid_swap01 h hS] at e
  rw [e, show σT 0 = 1 from by decide, show σT 1 = 0 from by decide, show σT 2 = 3 from by decide,
    show σT 3 = 2 from by decide]

omit h hS in
theorem hU_eq_hid_perm : hU R Ψ = hid R (perm Ψ σU) := by
  rw [hid, hidAt_perm, show σU 0 = 0 from by decide, show σU 1 = 3 from by decide,
    show σU 2 = 1 from by decide, show σU 3 = 2 from by decide]

theorem hU_eq_3021 : hU R Ψ = hidAt R Ψ 3 0 2 1 := by
  rw [hU_eq_hid_perm, hid_eq_1032 h (hS.perm σU), hidAt_perm, show σU 1 = 3 from by decide,
    show σU 0 = 0 from by decide, show σU 3 = 2 from by decide, show σU 2 = 1 from by decide]

omit h hS in
theorem hU_perm_T₀ (h : Hyp G R) (hS : Skel R Ψ) : hU R (perm Ψ σT₀) = hU R Ψ := by
  rw [hU_eq_3021 h hS, hU, hidAt_perm, show σT₀ 0 = 3 from by decide, show σT₀ 3 = 0 from by decide,
    show σT₀ 1 = 2 from by decide, show σT₀ 2 = 1 from by decide]

omit hS in
theorem hU_eq_conjSub : hU R Ψ = conjSub (hid R Ψ) (Ψ (pm σU)) := by
  rw [conjSub_hidAt h.root σU (s₁ := 0) (s₂ := 1) (t₁ := 2) (t₂ := 3) (by decide) (by decide)
    (by decide) (by decide), show σU 0 = 0 from by decide, show σU 1 = 3 from by decide,
    show σU 2 = 1 from by decide, show σU 3 = 2 from by decide]

omit hS in
theorem card_hU : Nat.card (hU R Ψ) = Nat.card (hid R Ψ) := by
  rw [hU_eq_conjSub h]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem commuting_hU {a b : Fin 4} (hab : a ≠ b) (hc : a = 0 ∨ a = 3 ∨ b = 1 ∨ b = 2) :
    Commuting (hU R Ψ) (xg Ψ a b) := by
  have e : xg Ψ a b = xg (perm Ψ σU) (σU⁻¹ a) (σU⁻¹ b) := by
    rw [xg_perm]
    simp
  rw [hU_eq_hid_perm, e]
  refine commuting_hid h (hS.perm σU) (σU⁻¹.injective.ne hab) ?_
  revert hab hc
  fin_cases a <;> fin_cases b <;> decide

omit [CharP F 2] h hS in
theorem hU_le_M_02 : hU R Ψ ≤ M R (xg Ψ 0 2) := inf_le_left.trans inf_le_left

omit [CharP F 2] h hS in
theorem hU_le_M_31 : hU R Ψ ≤ M R (xg Ψ 3 1) := inf_le_left.trans inf_le_right

theorem hU_le_cent4 : hU R Ψ ≤ cent4 Ψ := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : (xg Ψ 0 3 ⊔ xg Ψ 3 0) ⊔ (xg Ψ 1 2 ⊔ xg Ψ 2 1) ≤ Subgroup.centralizer {u} := by
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;> intro y hy <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    exacts [(commuting_hU h hS (by decide) (by decide) u hu y hy).symm,
      (commuting_hU h hS (by decide) (by decide) u hu y hy).symm,
      (commuting_hU h hS (by decide) (by decide) u hu y hy).symm,
      (commuting_hU h hS (by decide) (by decide) u hu y hy).symm]
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem hU_inf_02 : hU R Ψ ⊓ xg Ψ 0 2 = ⊥ := by
  have := h.finite
  refine eq_bot_iff.2 fun u hu => ?_
  rw [Subgroup.mem_bot]
  exact eq_one_of_forall_commute h.root h.noIsolated (hS.mem 0 2 (by decide))
    (hS.mem 3 0 (by decide)) (hS.special (by decide : (3 : Fin 4) ≠ 0) (by decide)
      (by decide)).symm hu.2
    fun z hz => commuting_hU h hS (by decide : (3 : Fin 4) ≠ 0) (by decide) u hu.1 z hz

omit [CharP F 2] in
theorem hid_inf_02 : hid R Ψ ⊓ xg Ψ 0 2 = ⊥ := by
  have := h.finite
  refine eq_bot_iff.2 fun n hn => ?_
  rw [Subgroup.mem_bot]
  exact eq_one_of_forall_commute h.root h.noIsolated (hS.mem 0 2 (by decide))
    (hS.mem 1 0 (by decide)) (hS.special (by decide : (1 : Fin 4) ≠ 0) (by decide)
      (by decide)).symm hn.2
    fun z hz => commuting_hid_10 h hS n hn.1 z hz

theorem mul_self_of_mem_hU {u : G} (hu : u ∈ hU R Ψ) : u * u = 1 := by
  have hm := sq_mem_of_mem_M h (hS.mem 0 2 (by decide)) (hU_le_M_02 hu)
  have : u * u ∈ hU R Ψ ⊓ xg Ψ 0 2 := ⟨Subgroup.mul_mem _ hu hu, hm⟩
  rwa [hU_inf_02 h hS, Subgroup.mem_bot] at this

theorem hU_ne_bot (hB : HypB G R (xg Ψ 0 3)) : hU R Ψ ≠ ⊥ := by
  rw [hU_eq_conjSub h]
  intro he
  exact hid_ne_bot h hS hB ((Subgroup.map_eq_bot_iff_of_injective _
    (MulAut.conj _).injective).1 he)

omit [CharP F 2] in
theorem commute_of_mem_hU_of_mem_02 {u c : G} (hu : u ∈ hU R Ψ) (hc : c ∈ xg Ψ 0 2) :
    Commute u c :=
  have := h.finite
  (QD.commuting_M h.root (hS.mem 0 2 (by decide)) c hc u (hU_le_M_02 hu)).symm

omit [CharP F 2] in
theorem conjSub_02_hU {u : G} (hu : u ∈ hU R Ψ) : conjSub (xg Ψ 0 2) u = xg Ψ 0 2 :=
  conjSub_of_forall_commute fun _ hc => commute_of_mem_hU_of_mem_02 h hS hu hc

theorem conjSub_M_hU {u : G} (hu : u ∈ hU R Ψ) :
    conjSub (M R (xg Ψ 0 3)) u = M R (xg Ψ 0 3) ∧
      conjSub (M R (xg Ψ 1 2)) u = M R (xg Ψ 1 2) := by
  rw [Sec5.conjSub_M h.root, Sec5.conjSub_M h.root,
    conjSub_of_forall_commute fun x hx => commuting_hU h hS (by decide) (by decide) u hu x hx,
    conjSub_of_forall_commute fun x hx => commuting_hU h hS (by decide) (by decide) u hu x hx]
  exact ⟨rfl, rfl⟩

theorem conjSub_mem_Om {u : G} (hu : u ∈ hU R Ψ) {D : Subgroup G} (hD : D ∈ Om R Ψ) :
    conjSub D u ∈ Om R Ψ := by
  have e1 : conjSub (xg Ψ 0 3) u = xg Ψ 0 3 :=
    conjSub_of_forall_commute fun x hx => commuting_hU h hS (by decide) (by decide) u hu x hx
  have e2 : conjSub (xg Ψ 1 2) u = xg Ψ 1 2 :=
    conjSub_of_forall_commute fun x hx => commuting_hU h hS (by decide) (by decide) u hu x hx
  have h1 := conjSub_mem_lambdaSet h.root hD.1 u
  have h2 := conjSub_mem_lambdaSet h.root hD.2 u
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

theorem conj_mem_W {u : G} (hu : u ∈ hU R Ψ) {w : G} (hw : w ∈ W R (xg Ψ 0 3) (xg Ψ 1 2)) :
    u * w * u⁻¹ ∈ W R (xg Ψ 0 3) (xg Ψ 1 2) := by
  obtain ⟨e1, e2⟩ := conjSub_M_hU h hS hu
  refine ⟨?_, ?_⟩
  · rw [← e1]
    exact conj_mem_conjSub u hw.1
  · rw [← e2]
    exact conj_mem_conjSub u hw.2

omit [CharP F 2] in
theorem xg13_inf_M_02 : xg Ψ 1 3 ⊓ M R (xg Ψ 0 2) = ⊥ :=
  inf_M_eq_bot_of_special h (hS.mem 1 3 (by decide)) (hS.mem 0 2 (by decide))
    (hS.mem_lambdaSet_col h.root (by decide : (3 : Fin 4) ≠ 2) (by decide) (by decide))
    (hS.special (by decide : (1 : Fin 4) ≠ 3) (by decide) (by decide))
    (by
      rw [commutator_xg (by decide) (by decide) (by decide)]
      exact hS.xg_ne (by decide) (by decide) (by decide))

theorem exists_mul_mem_hid_of_mem_M {w : G} (hw : w ∈ W R (xg Ψ 0 3) (xg Ψ 1 2))
    (hwC : w ∈ M R (xg Ψ 0 2)) : ∃ c ∈ xg Ψ 0 2, c⁻¹ * w ∈ hid R Ψ := by
  obtain ⟨c', hc', c, hc, hn⟩ := exists_mul_mem_hid h hS hw
  have hc'1 : c' = 1 := by
    have hmem : c' ∈ xg Ψ 1 3 ⊓ M R (xg Ψ 0 2) := by
      refine ⟨hc', ?_⟩
      have e : c' = w * ((c' * c)⁻¹ * w)⁻¹ * c⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwC
        (Subgroup.inv_mem _ (hid_le_M_02 h hS hn))) (Subgroup.inv_mem _ (QD.le_M_self hc))
    rwa [xg13_inf_M_02 h hS, Subgroup.mem_bot] at hmem
  subst hc'1
  exact ⟨c, hc, by simpa using hn⟩

theorem exists_commutator_eq {c' u : G} (hc' : c' ∈ xg Ψ 1 3) (hu : u ∈ hU R Ψ) :
    ∃ c ∈ xg Ψ 0 2, c⁻¹ * ⁅c', u⁆ ∈ hid R Ψ := by
  have hR := h.root
  have hc'W := xg_13_le_W h hS hc'
  refine exists_mul_mem_hid_of_mem_M h hS ?_ ?_
  · rw [commutatorElement_def, show c' * u * c'⁻¹ * u⁻¹ = c' * (u * c'⁻¹ * u⁻¹) by group]
    exact Subgroup.mul_mem _ hc'W (conj_mem_W h hS hu (Subgroup.inv_mem _ hc'W))
  · have e : conjSub (M R (xg Ψ 0 2)) c' = M R (xg Ψ 0 2) := by
      rw [Sec5.conjSub_M hR, conjSub_of_forall_commute fun x hx =>
        commuting_xg (Ψ := Ψ) (by decide : (1 : Fin 4) ≠ 3) (by decide : (0 : Fin 4) ≠ 2)
          (by decide) (by decide) c' hc' x hx]
    have hm : c' * u * c'⁻¹ ∈ M R (xg Ψ 0 2) := by
      rw [← e]
      exact conj_mem_conjSub c' (hU_le_M_02 hu)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hm (Subgroup.inv_mem _ (hU_le_M_02 hu))

theorem commute_torPar {u : G} (hu : u ∈ hU R Ψ) {K : Type*} [Field K]
    (φ : ↥(xg Ψ 0 3 ⊔ xg Ψ 3 0) ≃* SpecialLinearGroup (Fin 2) K) (c : Kˣ) :
    Commute u (FrameSL3.torPar φ c) := by
  have hle : xg Ψ 0 3 ⊔ xg Ψ 3 0 ≤ Subgroup.centralizer {u} := sup_le
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (commuting_hU h hS (by decide) (by decide) u hu x hx).symm)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (commuting_hU h hS (by decide) (by decide) u hu x hx).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (Sec8Field.torPar_mem_sup φ c))).symm

theorem commute_of_conjSub_eq {u : G} (hu : u ∈ hU R Ψ) {D : Subgroup G} (hD : D ∈ Om R Ψ)
    (hDu : conjSub D u = D) {d : G} (hd : d ∈ D) : Commute u d := by
  have := h.finite
  have hR := h.root
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  by_cases hd1 : d = 1
  · rw [hd1]
    exact Commute.one_right u
  obtain ⟨k, -, -, φ, hφA, -⟩ := (hS.opp 0 3 (by decide)).exists_mulEquiv_SL2' hR hA
  obtain ⟨dd, hadd, hinj, hdd1, -, hDd, hconj⟩ :=
    Sec8Field.exists_param h hA hA₀ hφA (mem_lambdaStar_of_mem_Om hS hR hD) hd hd1
  have hud : u * d * u⁻¹ ∈ D := by
    have := conj_mem_conjSub u hd
    rwa [hDu] at this
  obtain ⟨s, hs⟩ := hDd _ hud
  have h0 : dd 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact left_eq_mul.1 h00
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [h0] at hs
    apply hd1
    calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
      _ = 1 := by rw [← hs]; group
  set t := FrameSL3.torPar φ (Units.mk0 s hs0) with ht
  have hc : Commute u t := commute_torPar h hS hu φ _
  have key : u * dd s * u⁻¹ = dd (s * s) := by
    have e : dd s = t * d * t⁻¹ := by
      rw [← hdd1, ht, hconj, mul_one]
      rfl
    rw [e]
    calc u * (t * d * t⁻¹) * u⁻¹ = (u * t) * d * (u * t)⁻¹ := by group
      _ = (t * u) * d * (t * u)⁻¹ := by rw [hc.eq]
      _ = t * dd s * t⁻¹ := by rw [hs]; group
      _ = dd (s * s) := by rw [ht, hconj]; rfl
  have hss : s * s = 1 := by
    apply hinj
    rw [← key, hs, hdd1]
    calc u * (u * d * u⁻¹) * u⁻¹ = (u * u) * d * (u * u)⁻¹ := by group
      _ = d := by rw [mul_self_of_mem_hU h hS hu]; group
  have hs1 : s = 1 := by
    have hsq : (s + 1) * (s + 1) = 0 := by
      rw [CharTwo.add_mul_self, hss, mul_one, CharTwo.add_self_eq_zero]
    have h1 := mul_self_eq_zero.1 hsq
    have := eq_neg_of_add_eq_zero_left h1
    rwa [CharTwo.neg_eq] at this
  rw [hs1, hdd1] at hs
  calc u * d = u * d * u⁻¹ * u := by group
    _ = d * u := by rw [← hs]

end HiddenU

section Regular

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
include h hS hP

omit [CharP F 2] in
theorem inf_M_02_eq_bot_of_mem_Om {D : Subgroup G} (hD : D ∈ Om R Ψ) (hDC : D ≠ xg Ψ 0 2) :
    D ⊓ M R (xg Ψ 0 2) = ⊥ := by
  obtain ⟨h8, Δ, hΔ, hAΔ⟩ := hP
  have := h.finite
  have hR := h.root
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  refine eq_bot_iff.2 fun d hd => ?_
  rw [Subgroup.mem_bot]
  by_contra hd1
  obtain ⟨k, -, -, φ, hφA, hφB⟩ := (hS.opp 0 3 (by decide)).exists_mulEquiv_SL2' hR hA
  obtain ⟨dd, hadd, -, hdd1, -, hDd, hconj⟩ :=
    Sec8Field.exists_param h hA hA₀ hφA (mem_lambdaStar_of_mem_Om hS hR hD) hd.1 hd1
  have hDM : D ≤ M R (xg Ψ 0 2) := by
    intro x hx
    obtain ⟨s, rfl⟩ := hDd x hx
    by_cases hs : s = 0
    · subst hs
      have h00 := hadd 0 0
      rw [add_zero] at h00
      rw [left_eq_mul.1 h00]
      exact Subgroup.one_mem _
    · have e : dd s = FrameSL3.torPar φ (Units.mk0 s hs) * d *
          (FrameSL3.torPar φ (Units.mk0 s hs))⁻¹ := by
        rw [← hdd1, hconj, mul_one]
        rfl
      have hM : conjSub (M R (xg Ψ 0 2)) (FrameSL3.torPar φ (Units.mk0 s hs)) =
          M R (xg Ψ 0 2) := by
        rw [Sec5.conjSub_M hR, conjSub_xg_torPar h hS hφA hφB _ (by decide)]
      rw [e, ← hM]
      exact conj_mem_conjSub _ hd.2
  have hmem : D ∈ insert (xg Ψ 0 2) (lambdaSet R (xg Ψ 0 2)) := by
    rw [← (Q_eq_M h (hS.mem 0 2 (by decide))).2.1]
    exact ⟨hD.1.1.1, hDM⟩
  rcases hmem with e | hl
  · exact hDC e
  · exact not_mem_lambdaSet_of_mem_Om h hS h8 hΔ hAΔ (mem_Om_02 h hS) hD (Ne.symm hDC) hl

theorem ne_one_of_mem_point {D : Subgroup G} (hD : D ∈ Om R Ψ) (hDC : D ≠ xg Ψ 0 2)
    {d c' c : G} (hd : d ∈ D) (hd1 : d ≠ 1) (hc : c ∈ xg Ψ 0 2)
    (hn : (c' * c)⁻¹ * d ∈ hid R Ψ) : c' ≠ 1 := by
  rintro rfl
  have hmem : d ∈ D ⊓ M R (xg Ψ 0 2) := by
    refine ⟨hd, ?_⟩
    have e : d = c * ((1 * c)⁻¹ * d) := by group
    rw [e]
    exact Subgroup.mul_mem _ (QD.le_M_self hc) (hid_le_M_02 h hS hn)
  rw [inf_M_02_eq_bot_of_mem_Om h hS hP hD hDC, Subgroup.mem_bot] at hmem
  exact hd1 hmem

theorem eq_one_of_commutator_mem {c' u : G} (hc' : c' ∈ xg Ψ 1 3) (hc'1 : c' ≠ 1)
    (hu : u ∈ hU R Ψ) (hcu : ⁅c', u⁆ ∈ xg Ψ 0 2) : u = 1 := by
  obtain ⟨h8, Δ, hΔ, hAΔ⟩ := hP
  have := h.finite
  have hR := h.root
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  obtain ⟨k, -, -, φ, hφA, hφB⟩ := (hS.opp 0 3 (by decide)).exists_mulEquiv_SL2' hR hA
  obtain ⟨dd, hadd, -, hdd1, -, hDd, hconj⟩ := Sec8Field.exists_param h hA hA₀ hφA
    (mem_lambdaStar_of_mem_Om hS hR (mem_Om_13 h hS)) hc' hc'1
  have h0 : dd 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact left_eq_mul.1 h00
  have hall : ∀ x ∈ xg Ψ 1 3, ⁅x, u⁆ ∈ xg Ψ 0 2 := by
    intro x hx
    obtain ⟨s, rfl⟩ := hDd x hx
    by_cases hs : s = 0
    · subst hs
      rw [h0, commutatorElement_one_left]
      exact Subgroup.one_mem _
    · set t := FrameSL3.torPar φ (Units.mk0 s hs) with ht
      have e : dd s = t * c' * t⁻¹ := by
        rw [← hdd1, ht, hconj, mul_one]
        rfl
      have hc : Commute u t := commute_torPar h hS hu φ _
      have hu' : t * u * t⁻¹ = u := by rw [← hc.eq]; group
      have e2 : ⁅t * c' * t⁻¹, u⁆ = t * ⁅c', u⁆ * t⁻¹ := by
        conv_lhs => rw [← hu']
        simp only [commutatorElement_def]
        group
      rw [e, e2, ← conjSub_xg_torPar h hS hφA hφB (Units.mk0 s hs) (by decide : (0 : Fin 4) ≠ 2)]
      exact conj_mem_conjSub t hcu
  have hle : conjSub (xg Ψ 1 3) u ≤ xg Ψ 1 3 ⊔ xg Ψ 0 2 := by
    rintro _ ⟨x, hx, rfl⟩
    change u * x * u⁻¹ ∈ _
    have e : u * x * u⁻¹ = ⁅x, u⁆⁻¹ * x := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ (hall x hx)))
      (Subgroup.mem_sup_left hx)
  have hne : xg Ψ 1 3 ≠ xg Ψ 0 2 := hS.xg_ne (by decide) (by decide) (by decide)
  have hC : conjSub (xg Ψ 1 3) u ≠ xg Ψ 0 2 := by
    intro e
    apply hne
    have e' := congrArg (fun H => conjSub H u⁻¹) e
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at e'
    rw [e', conjSub_02_hU h hS (Subgroup.inv_mem _ hu)]
  have hfix : conjSub (xg Ψ 1 3) u = xg Ψ 1 3 := by
    by_contra hne'
    exact false_of_le_sup h hS h8 hΔ hAΔ (mem_Om_13 h hS) (mem_Om_02 h hS) hne
      (hR.conjSub_mem (hS.mem 1 3 (by decide)) u) hle hne' hC
  exact eq_one_of_mem_M_of_conjSub_eq h (hS.mem 3 1 (by decide))
    ⟨hS.mem 1 3 (by decide), hS.opp 3 1 (by decide)⟩ (hU_le_M_31 hu) hfix

theorem eq_one_of_conjSub_eq {u : G} (hu : u ∈ hU R Ψ) {D : Subgroup G} (hD : D ∈ Om R Ψ)
    (hDC : D ≠ xg Ψ 0 2) (hDu : conjSub D u = D) : u = 1 := by
  have := h.finite
  have hR := h.root
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD.1.1.1
  obtain ⟨c', hc', c, hc, hn⟩ := exists_mul_mem_hid h hS (le_W_of_mem_Om hD hd)
  have hc'1 := ne_one_of_mem_point h hS hP hD hDC hd hd1 hc hn
  refine eq_one_of_commutator_mem h hS hP hc' hc'1 hu ?_
  set n := (c' * c)⁻¹ * d with hn_def
  have hud := commute_of_conjSub_eq h hS hu hD hDu hd
  have huc := commute_of_mem_hU_of_mem_02 h hS hu hc
  set m := c' * n with hm_def
  have hmd : m = c⁻¹ * d := by
    have hcc' : Commute c c' := commuting_xg (Ψ := Ψ) (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 3) (by decide) (by decide) c hc c' hc'
    rw [hm_def, hn_def]
    calc c' * ((c' * c)⁻¹ * d) = c' * c⁻¹ * c'⁻¹ * d := by group
      _ = c⁻¹ * c' * c'⁻¹ * d := by rw [(hcc'.inv_left).eq]
      _ = c⁻¹ * d := by group
  have hum : Commute u m := by
    rw [hmd]
    exact huc.inv_right.mul_right hud
  have hc'm : c' = m * n⁻¹ := by rw [hm_def]; group
  have e : ⁅c', u⁆ = m * ⁅n⁻¹, u⁆ * m⁻¹ := by
    rw [hc'm, commutatorElement_def, commutatorElement_def]
    calc m * n⁻¹ * u * (m * n⁻¹)⁻¹ * u⁻¹ = m * n⁻¹ * u * n * (m⁻¹ * u⁻¹) := by group
      _ = m * n⁻¹ * u * n * (u⁻¹ * m⁻¹) := by rw [← hum.inv_inv.eq]
      _ = m * (n⁻¹ * u * n⁻¹⁻¹ * u⁻¹) * m⁻¹ := by group
  have hcomm : ⁅n⁻¹, u⁆ ∈ xg Ψ 0 2 := by
    rw [← (Q_eq_M h (hS.mem 0 2 (by decide))).2.2.1]
    exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (hid_le_M_02 h hS hn))
      (hU_le_M_02 hu)
  have hmC : conjSub (xg Ψ 0 2) m = xg Ψ 0 2 := by
    refine conjSub_of_forall_commute fun k hk => ?_
    rw [hm_def]
    exact (commuting_xg (Ψ := Ψ) (by decide : (1 : Fin 4) ≠ 3) (by decide : (0 : Fin 4) ≠ 2)
      (by decide) (by decide) c' hc' k hk).mul_left
      (QD.commuting_M hR (hS.mem 0 2 (by decide)) k hk n (hid_le_M_02 h hS hn)).symm
  rw [e, ← hmC]
  exact conj_mem_conjSub m hcomm

theorem exists_mem_point {D : Subgroup G} (hD : D ∈ Om R Ψ) (hDC : D ≠ xg Ψ 0 2) {c'₀ : G}
    (hc'₀ : c'₀ ∈ xg Ψ 1 3) (hc'₀1 : c'₀ ≠ 1) :
    ∃ c ∈ xg Ψ 0 2, ∃ n ∈ hid R Ψ, c'₀ * c * n ∈ D := by
  have := h.finite
  have hR := h.root
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  obtain ⟨k, -, -, φ, hφA, hφB⟩ := (hS.opp 0 3 (by decide)).exists_mulEquiv_SL2' hR hA
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD.1.1.1
  obtain ⟨c', hc', c, hc, hn⟩ := exists_mul_mem_hid h hS (le_W_of_mem_Om hD hd)
  have hc'1 := ne_one_of_mem_point h hS hP hD hDC hd hd1 hc hn
  obtain ⟨dd, hadd, -, hdd1, -, hDd, hconj⟩ := Sec8Field.exists_param h hA hA₀ hφA
    (mem_lambdaStar_of_mem_Om hS hR (mem_Om_13 h hS)) hc' hc'1
  obtain ⟨s, hs⟩ := hDd c'₀ hc'₀
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hc'₀1
    rw [← hs]
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact left_eq_mul.1 h00
  set t := FrameSL3.torPar φ (Units.mk0 s hs0) with ht
  have e : c'₀ = t * c' * t⁻¹ := by
    rw [← hs, ← hdd1, ht, hconj, mul_one]
    rfl
  have hN := conj_mem_conjSub t hn
  rw [conjSub_hidAt_of h.root (fun a b hab => conjSub_xg_torPar h hS hφA hφB (Units.mk0 s hs0) hab)
    (s₁ := 0) (s₂ := 1) (t₁ := 2) (t₂ := 3) (by decide) (by decide) (by decide) (by decide)] at hN
  have hC := conj_mem_conjSub t hc
  rw [conjSub_xg_torPar h hS hφA hφB (Units.mk0 s hs0) (by decide : (0 : Fin 4) ≠ 2)] at hC
  have hD' := conj_mem_conjSub t hd
  rw [Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA
    (mem_lambdaStar_of_mem_Om hS hR hD)] at hD'
  refine ⟨t * c * t⁻¹, hC, t * ((c' * c)⁻¹ * d) * t⁻¹, hN, ?_⟩
  rw [e, show t * c' * t⁻¹ * (t * c * t⁻¹) * (t * ((c' * c)⁻¹ * d) * t⁻¹) = t * d * t⁻¹ by
    group]
  exact hD'

theorem eq_of_mem_point {D D' : Subgroup G} (hD : D ∈ Om R Ψ) (hD' : D' ∈ Om R Ψ)
    (hDC : D ≠ xg Ψ 0 2) (hD'C : D' ≠ xg Ψ 0 2) {c'₀ c₁ c₂ n : G} (hc'₀ : c'₀ ∈ xg Ψ 1 3)
    (hc'₀1 : c'₀ ≠ 1) (hc₁ : c₁ ∈ xg Ψ 0 2) (hc₂ : c₂ ∈ xg Ψ 0 2) (hn : n ∈ hid R Ψ)
    (h1 : c'₀ * c₁ * n ∈ D) (h2 : c'₀ * c₂ * n ∈ D') : D = D' := by
  obtain ⟨h8, Δ, hΔ, hAΔ⟩ := hP
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  by_contra hne
  have hxC : c₁⁻¹ * c₂ ∈ xg Ψ 0 2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₁) hc₂
  have hx : c₁⁻¹ * c₂ ∈ D ⊔ D' := by
    have hcomm : Commute n (c₁⁻¹ * c₂) :=
      (QD.commuting_M hR (hS.mem 0 2 (by decide)) _ hxC n (hid_le_M_02 h hS hn)).symm
    have e : c₁⁻¹ * c₂ = (c'₀ * c₁ * n)⁻¹ * (c'₀ * c₂ * n) := by
      calc c₁⁻¹ * c₂ = n⁻¹ * (n * (c₁⁻¹ * c₂)) := by group
        _ = n⁻¹ * ((c₁⁻¹ * c₂) * n) := by rw [hcomm.eq]
        _ = (c'₀ * c₁ * n)⁻¹ * (c'₀ * c₂ * n) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left h1))
      (Subgroup.mem_sup_right h2)
  by_cases hx1 : c₁⁻¹ * c₂ = 1
  · have e12 : c₁ = c₂ := inv_mul_eq_one.1 hx1
    subst e12
    have hmem : c'₀ * c₁ * n ∈ D ⊓ D' := ⟨h1, h2⟩
    rw [inf_eq_bot hR hiso hD.1.1.1 hD'.1.1.1 hne, Subgroup.mem_bot] at hmem
    have hc'M : c'₀ ∈ xg Ψ 1 3 ⊓ M R (xg Ψ 0 2) := by
      refine ⟨hc'₀, ?_⟩
      have e : c'₀ = (c₁ * n)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
        exact hmem
      rw [e]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (QD.le_M_self hc₁) (hid_le_M_02 h hS hn))
    rw [xg13_inf_M_02 h hS, Subgroup.mem_bot] at hc'M
    exact hc'₀1 hc'M
  · obtain ⟨k, -, -, φ, hφA, hφB⟩ := (hS.opp 0 3 (by decide)).exists_mulEquiv_SL2' hR hA
    obtain ⟨dd, hadd, -, hdd1, -, hDd, hconj⟩ := Sec8Field.exists_param h hA hA₀ hφA
      (mem_lambdaStar_of_mem_Om hS hR (mem_Om_02 h hS)) hxC hx1
    have hCle : xg Ψ 0 2 ≤ D ⊔ D' := by
      intro y hy
      obtain ⟨s, rfl⟩ := hDd y hy
      by_cases hs : s = 0
      · subst hs
        have h00 := hadd 0 0
        rw [add_zero] at h00
        rw [left_eq_mul.1 h00]
        exact Subgroup.one_mem _
      · have e : dd s = FrameSL3.torPar φ (Units.mk0 s hs) * (c₁⁻¹ * c₂) *
            (FrameSL3.torPar φ (Units.mk0 s hs))⁻¹ := by
          rw [← hdd1, hconj, mul_one]
          rfl
        have hDD : conjSub (D ⊔ D') (FrameSL3.torPar φ (Units.mk0 s hs)) = D ⊔ D' := by
          rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
            Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA
              (mem_lambdaStar_of_mem_Om hS hR hD),
            Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA
              (mem_lambdaStar_of_mem_Om hS hR hD')]
        rw [e, ← hDD]
        exact conj_mem_conjSub _ hx
    exact false_of_le_sup h hS h8 hΔ hAΔ hD hD' hne (hS.mem 0 2 (by decide)) hCle
      (Ne.symm hDC) (Ne.symm hD'C)

theorem exists_conjSub_hU_eq {D : Subgroup G} (hD : D ∈ Om R Ψ) (hDC : D ≠ xg Ψ 0 2) :
    ∃ u ∈ hU R Ψ, conjSub (xg Ψ 1 3) u = D := by
  have := h.finite
  have hR := h.root
  have : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨c'₀, hc'₀, hc'₀1⟩ := hR.exists_ne_one (hS.mem 1 3 (by decide))
  have hne : xg Ψ 1 3 ≠ xg Ψ 0 2 := hS.xg_ne (by decide) (by decide) (by decide)
  have hC'S : ∀ u ∈ hU R Ψ, conjSub (xg Ψ 1 3) u ∈ Om R Ψ ∧ conjSub (xg Ψ 1 3) u ≠ xg Ψ 0 2 := by
    intro u hu
    refine ⟨conjSub_mem_Om h hS hu (mem_Om_13 h hS), fun e => hne ?_⟩
    have e' := congrArg (fun H => conjSub H u⁻¹) e
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at e'
    rw [e', conjSub_02_hU h hS (Subgroup.inv_mem _ hu)]
  let f : hU R Ψ → {D : Subgroup G // D ∈ Om R Ψ ∧ D ≠ xg Ψ 0 2} :=
    fun u => ⟨conjSub (xg Ψ 1 3) u, hC'S u u.2⟩
  have hf : Function.Injective f := by
    intro u₁ u₂ e
    have e' : conjSub (xg Ψ 1 3) u₁ = conjSub (xg Ψ 1 3) u₂ := congrArg Subtype.val e
    have h1 : conjSub (xg Ψ 1 3) ((u₂ : G)⁻¹ * u₁) = xg Ψ 1 3 := by
      rw [conjSub_mul, e', ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have h2 := eq_one_of_mem_M_of_conjSub_eq h (hS.mem 3 1 (by decide))
      ⟨hS.mem 1 3 (by decide), hS.opp 3 1 (by decide)⟩
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU_le_M_31 u₂.2)) (hU_le_M_31 u₁.2)) h1
    exact Subtype.ext (inv_mul_eq_one.1 h2).symm
  have hpt : ∀ D : {D : Subgroup G // D ∈ Om R Ψ ∧ D ≠ xg Ψ 0 2},
      ∃ n : G, n ∈ hid R Ψ ∧ ∃ c ∈ xg Ψ 0 2, c'₀ * c * n ∈ D.1 := fun D => by
    obtain ⟨c, hc, n, hn, hm⟩ := exists_mem_point h hS hP D.2.1 D.2.2 hc'₀ hc'₀1
    exact ⟨n, hn, c, hc, hm⟩
  choose g hg using hpt
  let g' : {D : Subgroup G // D ∈ Om R Ψ ∧ D ≠ xg Ψ 0 2} → hid R Ψ := fun D => ⟨g D, (hg D).1⟩
  have hg' : Function.Injective g' := by
    intro D₁ D₂ e
    have e' : g D₁ = g D₂ := congrArg Subtype.val e
    obtain ⟨-, c₁, hc₁, h1⟩ := hg D₁
    obtain ⟨-, c₂, hc₂, h2⟩ := hg D₂
    rw [e'] at h1
    exact Subtype.ext (eq_of_mem_point h hS hP D₁.2.1 D₂.2.1 D₁.2.2 D₂.2.2 hc'₀ hc'₀1 hc₁ hc₂
      (hg D₂).1 h1 h2)
  have hcard : Nat.card {D : Subgroup G // D ∈ Om R Ψ ∧ D ≠ xg Ψ 0 2} ≤ Nat.card (hU R Ψ) := by
    rw [card_hU h]
    exact Nat.card_le_card_of_injective g' hg'
  obtain ⟨u, hu⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨D, hD, hDC⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

end Regular

section Moufang

variable [CharP F 2]

theorem hU_perm_T : hU R (perm Ψ σT) = hidAt R Ψ 1 2 0 3 := by
  rw [hU, hidAt_perm, show σT 0 = 1 from by decide, show σT 3 = 2 from by decide,
    show σT 1 = 0 from by decide, show σT 2 = 3 from by decide]

theorem cent4_perm_T : cent4 (perm Ψ σT) = cent4 Ψ := by
  simp only [cent4, xg_perm, show σT 0 = 1 from by decide, show σT 3 = 2 from by decide,
    show σT 1 = 0 from by decide, show σT 2 = 3 from by decide]
  rw [sup_comm (xg Ψ 1 2 ⊔ xg Ψ 2 1)]

omit [CharP F 2] in
theorem conjSub_of_mem_cent4 {g : G} (hg : g ∈ cent4 Ψ) :
    conjSub (xg Ψ 0 3) g = xg Ψ 0 3 ∧ conjSub (xg Ψ 3 0) g = xg Ψ 3 0 ∧
      conjSub (xg Ψ 1 2) g = xg Ψ 1 2 ∧ conjSub (xg Ψ 2 1) g = xg Ψ 2 1 := by
  rw [Subgroup.mem_centralizer_iff] at hg
  refine ⟨conjSub_of_forall_commute fun x hx => (hg x ?_).symm,
    conjSub_of_forall_commute fun x hx => (hg x ?_).symm,
    conjSub_of_forall_commute fun x hx => (hg x ?_).symm,
    conjSub_of_forall_commute fun x hx => (hg x ?_).symm⟩
  · exact SetLike.mem_coe.2 (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
  · exact SetLike.mem_coe.2 (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
  · exact SetLike.mem_coe.2 (Subgroup.mem_sup_right (Subgroup.mem_sup_left hx))
  · exact SetLike.mem_coe.2 (Subgroup.mem_sup_right (Subgroup.mem_sup_right hx))

variable (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
include h hS hP

theorem hU_eq_cent4_inf : hU R Ψ = cent4 Ψ ⊓ M R (xg Ψ 0 2) := by
  refine le_antisymm (le_inf (hU_le_cent4 h hS) hU_le_M_02) fun g hg => ?_
  have := h.finite
  have hR := h.root
  obtain ⟨-, e30, -, e21⟩ := conjSub_of_mem_cent4 hg.1
  have hC₀ : xg Ψ 2 0 ∈ omegaSet R (xg Ψ 0 2) := ⟨hS.mem 2 0 (by decide), hS.opp 0 2 (by decide)⟩
  have hgC : conjSub (xg Ψ 0 2) g = xg Ψ 0 2 := conjSub_of_forall_commute fun x hx =>
    (QD.commuting_M hR (hS.mem 0 2 (by decide)) x hx g hg.2).symm
  have hS₀ := hS.perm σT₀
  have hP₀ := hP.perm hR σT₀
  have v0 : σT₀ 0 = 3 := by decide
  have v1 : σT₀ 1 = 2 := by decide
  have v2 : σT₀ 2 = 1 := by decide
  have v3 : σT₀ 3 = 0 := by decide
  have e13 : xg (perm Ψ σT₀) 1 3 = xg Ψ 2 0 := by rw [xg_perm, v1, v3]
  have e02 : xg (perm Ψ σT₀) 0 2 = xg Ψ 3 1 := by rw [xg_perm, v0, v2]
  have hOm : conjSub (xg Ψ 2 0) g ∈ Om R (perm Ψ σT₀) := by
    have hm := mem_Om_13 h hS₀
    rw [e13, Om_perm, v0, v1, v2, v3] at hm
    rw [Om_perm, v0, v1, v2, v3]
    have h1 := conjSub_mem_lambdaSet hR hm.1 g
    have h2 := conjSub_mem_lambdaSet hR hm.2 g
    rw [e30] at h1
    rw [e21] at h2
    exact ⟨h1, h2⟩
  have hne : conjSub (xg Ψ 2 0) g ≠ xg (perm Ψ σT₀) 0 2 := by
    rw [e02]
    intro e
    have hop := (hS.opp 0 2 (by decide)).conj g
    rw [hgC, e] at hop
    exact hop.not_commuting (hR.ne_bot _ (hS.mem 0 2 (by decide)))
      (commuting_xg (by decide) (by decide) (by decide) (by decide))
  obtain ⟨u, hu, hug⟩ := exists_conjSub_hU_eq h hS₀ hP₀ hOm hne
  rw [hU_perm_T₀ h hS] at hu
  rw [e13] at hug
  have hfix : conjSub (xg Ψ 2 0) (u⁻¹ * g) = xg Ψ 2 0 := by
    rw [conjSub_mul, ← hug, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have h1 := eq_one_of_mem_M_of_conjSub_eq h (hS.mem 0 2 (by decide)) hC₀
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU_le_M_02 hu)) hg.2) hfix
  exact (inv_mul_eq_one.1 h1) ▸ hu

end Moufang

end CaseB

end CFSG.Timmesfeld.ARS
