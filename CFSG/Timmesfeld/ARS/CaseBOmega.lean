module

public import CFSG.Timmesfeld.ARS.CaseBHidden
public import CFSG.Timmesfeld.ARS.Sec8Field
public import CFSG.Timmesfeld.ARS.Sec8Projection

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

variable (R Ψ) in
abbrev Om : Set (Subgroup G) := lambdaSet R (xg Ψ 0 3) ∩ lambdaSet R (xg Ψ 1 2)

section Inter

variable (h : Hyp G R) (hS : Skel R Ψ)
include h hS

omit [Field F] hS in
theorem inf_M_eq_bot_of_special {X Y Z : Subgroup G} (hX : X ∈ R) (hY : Y ∈ R)
    (hZ : Z ∈ lambdaSet R Y) (hs : Special R X Z) (hne : ⁅X, Z⁆ ≠ Y) : X ⊓ M R Y = ⊥ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  refine eq_bot_iff.2 fun a ha => ?_
  rw [Subgroup.mem_bot]
  refine eq_one_of_forall_commute hR hiso hX hZ.1.1 hs ha.1 fun z hz => ?_
  have hc : ⁅a, z⁆ ∈ Y ⊓ ⁅X, Z⁆ := by
    refine ⟨?_, Subgroup.commutator_mem_commutator ha.1 hz⟩
    rw [← (Q_eq_M h hY).2.2.1]
    exact Subgroup.commutator_mem_commutator ha.2 (QD.le_M hZ hz)
  rw [inf_eq_bot hR hiso hY hs.1 hne.symm, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem inf_M_12_eq_bot : xg Ψ 0 3 ⊓ M R (xg Ψ 1 2) = ⊥ :=
  inf_M_eq_bot_of_special h (hS.mem 0 3 (by decide)) (hS.mem 1 2 (by decide))
    (hS.mem_lambdaSet_row h.root (by decide) (by decide) (by decide))
    (hS.special (by decide : (1 : Fin 4) ≠ 0) (by decide) (by decide)).symm
    (by
      rw [Subgroup.commutator_comm, commutator_xg (by decide) (by decide) (by decide)]
      exact hS.xg_ne (by decide) (by decide) (by decide))

theorem inf_M_03_eq_bot : xg Ψ 1 2 ⊓ M R (xg Ψ 0 3) = ⊥ :=
  inf_M_eq_bot_of_special h (hS.mem 1 2 (by decide)) (hS.mem 0 3 (by decide))
    (hS.mem_lambdaSet_row h.root (by decide) (by decide) (by decide))
    (hS.special (by decide : (0 : Fin 4) ≠ 1) (by decide) (by decide)).symm
    (by
      rw [Subgroup.commutator_comm, commutator_xg (by decide) (by decide) (by decide)]
      exact hS.xg_ne (by decide) (by decide) (by decide))

theorem inf_M_21_eq_bot : xg Ψ 0 3 ⊓ M R (xg Ψ 2 1) = ⊥ :=
  inf_M_eq_bot_of_special h (hS.mem 0 3 (by decide)) (hS.mem 2 1 (by decide))
    (hS.mem_lambdaSet_row h.root (by decide) (by decide) (by decide))
    (hS.special (by decide : (2 : Fin 4) ≠ 0) (by decide) (by decide)).symm
    (by
      rw [Subgroup.commutator_comm, commutator_xg (by decide) (by decide) (by decide)]
      exact hS.xg_ne (by decide) (by decide) (by decide))

theorem mem_Om_of_le {X : Subgroup G} (hX : X ∈ R) (hXW : X ≤ W R (xg Ψ 0 3) (xg Ψ 1 2)) :
    X ∈ Om R Ψ := by
  have hR := h.root
  have h1 : X ∈ insert (xg Ψ 0 3) (lambdaSet R (xg Ψ 0 3)) := by
    rw [← (Q_eq_M h (hS.mem 0 3 (by decide))).2.1]
    exact ⟨hX, hXW.trans inf_le_left⟩
  have h2 : X ∈ insert (xg Ψ 1 2) (lambdaSet R (xg Ψ 1 2)) := by
    rw [← (Q_eq_M h (hS.mem 1 2 (by decide))).2.1]
    exact ⟨hX, hXW.trans inf_le_right⟩
  refine ⟨h1.resolve_left fun e => ?_, h2.resolve_left fun e => ?_⟩
  · have hle : xg Ψ 0 3 ≤ xg Ψ 0 3 ⊓ M R (xg Ψ 1 2) :=
      le_inf le_rfl (e ▸ hXW.trans inf_le_right)
    rw [inf_M_12_eq_bot h hS, le_bot_iff] at hle
    exact hR.ne_bot _ (hS.mem 0 3 (by decide)) hle
  · have hle : xg Ψ 1 2 ≤ xg Ψ 1 2 ⊓ M R (xg Ψ 0 3) :=
      le_inf le_rfl (e ▸ hXW.trans inf_le_left)
    rw [inf_M_03_eq_bot h hS, le_bot_iff] at hle
    exact hR.ne_bot _ (hS.mem 1 2 (by decide)) hle

omit h hS in
theorem le_W_of_mem_Om {D : Subgroup G} (hD : D ∈ Om R Ψ) :
    D ≤ W R (xg Ψ 0 3) (xg Ψ 1 2) :=
  le_inf (QD.le_M hD.1) (QD.le_M hD.2)

omit h in
theorem mem_lambdaStar_of_mem_Om [Finite G] (hR : IsRootClass R) {D : Subgroup G}
    (hD : D ∈ Om R Ψ) : D ∈ lambdaStar R (xg Ψ 0 3) (xg Ψ 3 0) :=
  mem_lambdaStar_of_mem_lambdaSet hR (mem_omegaSet_30 hS) (mem_leviSet_12 hS) hD.1 hD.2

end Inter

section Planes

variable (h : Hyp G R) {A : Subgroup G} (hA : A ∈ R)
include h hA

theorem mem_of_mem_lambdaSet_of_mem {Δ' : Set (Subgroup G)} (hΔ' : IsWeakTI R Δ')
    (hAΔ' : A ∈ Δ') {D D' : Subgroup G} (hD : D ∈ Δ') (hDA : D ≠ A)
    (hD'A : D' ∈ lambdaSet R A) (hD'D : D' ∈ lambdaSet R D) : D' ∈ Δ' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have hDR := hΔ'.1 hD
  by_contra hD'Δ
  have hnc : ¬ Commuting D' (gen Δ') := fun hc =>
    hD'Δ (Sec5.mem_of_commuting_gen hR hiso hnd hΩ hΔ' hD'A.1.1 hc)
  have hZ : ∃ Z ∈ Δ', ¬ Commuting Z D' := by
    by_contra! hall
    exact hnc (commuting_iff_le_centralizer.2 (gen_le fun Z hZ =>
      commuting_iff_le_centralizer.1 (hall Z hZ).symm))
  obtain ⟨Z, hZΔ, hZD'⟩ := hZ
  have hZA : Z ≠ A := fun e => hZD' (e ▸ hD'A.1.2.2)
  have hZD : Z ≠ D := fun e => hZD' (e ▸ hD'D.1.2.2)
  have hZl : Z ∈ lambdaSet R A := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ' hAΔ' hZΔ hZA.symm
  have hZlD : Z ∈ lambdaSet R D := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ' hD hZΔ hZD.symm
  apply hZD'
  refine commuting_iff_commutator_eq_bot.2 (eq_bot_iff.2 ?_)
  rw [← inf_eq_bot hR hiso hA hDR hDA.symm]
  exact le_inf (commutator_le_of_le_M h hA (QD.le_M hZl) (QD.le_M hD'A))
    (commutator_le_of_le_M h hDR (QD.le_M hZlD) (QD.le_M hD'D))

end Planes

section Points

variable (h : Hyp G R) (hS : Skel R Ψ) (h8 : Sec8 R (xg Ψ 0 3)) {Δ : Set (Subgroup G)}
  (hΔ : IsWeakTI R Δ) (hAΔ : xg Ψ 0 3 ∈ Δ)
include h hS h8 hΔ hAΔ

omit hΔ hAΔ in
theorem eq_of_mem_plane {Δ' : Set (Subgroup G)} (hΔ' : IsWeakTI R Δ')
    (hAΔ' : xg Ψ 0 3 ∈ Δ') {D D' : Subgroup G} (hD : D ∈ Om R Ψ) (hD' : D' ∈ Om R Ψ)
    (hDΔ : D ∈ Δ') (hD'Δ : D' ∈ Δ') : D = D' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  obtain ⟨C₁, hC₁, F₁, hF₁Δ, hF₁, hF₁C₁⟩ := exists_special_lambdaStar h hA h8 hA₀ hΔ' hAΔ'
  have hDs := mem_lambdaStar_of_mem_Om hS hR hD
  have hD's := mem_lambdaStar_of_mem_Om hS hR hD'
  have hDle := le_sup_commutator_of_mem h hA h8 hA₀ hΔ' hAΔ' hC₁ hF₁Δ hF₁ hF₁C₁ hDΔ hDs
  have hD'le := le_sup_commutator_of_mem h hA h8 hA₀ hΔ' hAΔ' hC₁ hF₁Δ hF₁ hF₁C₁ hD'Δ hD's
  by_contra hne
  have hsup := sup_eq_of_le_of_commuting hR hiso (hΔ'.1 hF₁Δ) hF₁C₁.1 hD.1.1.1 hD'.1.1.1
    hF₁C₁.2.1.symm hDle hD'le hne
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hS.mem 1 2 (by decide))
  apply ha1
  refine eq_one_of_mem_levi_of_commute h hA h8 hA₀ hΔ' hAΔ' hC₁ hF₁Δ hF₁ hF₁C₁
    (le_iSup₂ (f := fun X (_ : X ∈ leviSet R (xg Ψ 0 3) (xg Ψ 3 0)) => X) _
      (mem_leviSet_12 hS) ha) fun m hm => ?_
  rw [← hsup] at hm
  have hc : Commuting (xg Ψ 1 2) (D ⊔ D') := Commuting.sup_right hD.2.1.2.2 hD'.2.1.2.2
  exact hc a ha m hm

theorem exists_plane {D : Subgroup G} (hD : D ∈ Om R Ψ) :
    ∃ Δ' : Set (Subgroup G), IsWeakTI R Δ' ∧ xg Ψ 0 3 ∈ Δ' ∧ D ∈ Δ' := by
  have := h.finite
  have hR := h.root
  obtain ⟨c, hcA, -, hDc⟩ := exists_conjSet_of_mem_lambdaStar h (hS.mem 0 3 (by decide)) h8
    (mem_omegaSet_30 hS) hΔ hAΔ (mem_lambdaStar_of_mem_Om hS hR hD)
  exact ⟨conjSet Δ c, Sec5.isWeakTI_conjSet hR hΔ c, hcA ▸ conjSub_mem_conjSet hAΔ c, hDc⟩

theorem not_mem_lambdaSet_of_mem_Om {D D' : Subgroup G} (hD : D ∈ Om R Ψ) (hD' : D' ∈ Om R Ψ)
    (hne : D ≠ D') : D' ∉ lambdaSet R D := by
  intro hD'D
  obtain ⟨Δ', hΔ', hAΔ', hDΔ'⟩ := exists_plane h hS h8 hΔ hAΔ hD
  exact hne (eq_of_mem_plane h hS h8 hΔ' hAΔ' hD hD' hDΔ'
    (mem_of_mem_lambdaSet_of_mem h (hS.mem 0 3 (by decide)) hΔ' hAΔ' hDΔ' hD.1.1.2.1 hD'.1
      hD'D))

theorem special_21 {D : Subgroup G} (hD : D ∈ Om R Ψ) :
    Special R D (xg Ψ 2 1) ∧ ⁅D, xg Ψ 2 1⁆ ∈ lambdaStar R (xg Ψ 0 3) (xg Ψ 3 0) ∧
      ⁅D, xg Ψ 2 1⁆ ∈ lambdaSet R (xg Ψ 2 1) := by
  have := h.finite
  have hR := h.root
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  have hDs := mem_lambdaStar_of_mem_Om hS hR hD
  have hs : Special R (xg Ψ 2 1) D := special_of_commuting h hA h8 hA₀ hΔ hAΔ hDs
    (mem_leviSet_12 hS) (mem_leviSet_21 hS) (hS.xg_ne (by decide) (by decide) (by decide))
    hD.2.1.2.2
  have hstar : ⁅D, xg Ψ 2 1⁆ ∈ lambdaStar R (xg Ψ 0 3) (xg Ψ 3 0) :=
    (exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ (mem_leviSet_21 hS) hDs hs.symm).1 _
      hs.symm.1 le_sup_right
  refine ⟨hs.symm, hstar, mem_lambdaSet_of_commuting h hA h8 hA₀ hΔ hAΔ hstar
    (mem_leviSet_21 hS) hs.symm.2.2.symm⟩

theorem not_commuting_comm {D D' : Subgroup G} (hD : D ∈ Om R Ψ) (hD' : D' ∈ Om R Ψ)
    (hne : D ≠ D') : ¬ Commuting D' ⁅D, xg Ψ 2 1⁆ := by
  intro hc
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  obtain ⟨Δ', hΔ', hAΔ', hDΔ'⟩ := exists_plane h hS h8 hΔ hAΔ hD
  obtain ⟨hs, hstar, -⟩ := special_21 h hS h8 hΔ hAΔ hD
  have hDs := mem_lambdaStar_of_mem_Om hS hR hD
  have hDD' : Commuting D' D :=
    (commuting_W₁ h hS).mono (le_W_of_mem_Om hD') (le_W_of_mem_Om hD)
  have hcomm : Commuting D' (gen Δ') := by
    refine commuting_gen_of_forall h hA hA₀ hΔ' hAΔ' hD'.1.1.2.2.symm fun Q hQ hQs => ?_
    have hle := le_sup_commutator_of_mem h hA h8 hA₀ hΔ' hAΔ' (mem_leviSet_21 hS) hDΔ' hDs hs
      hQ hQs
    exact (hDD'.sup_right hc).mono le_rfl hle
  have hD'Δ' := Sec5.mem_of_commuting_gen hR hiso hnd hΩ hΔ' hD'.1.1.1 hcomm
  exact hne (eq_of_mem_plane h hS h8 hΔ' hAΔ' hD hD' hDΔ' hD'Δ')

theorem false_of_le_sup {D D' X : Subgroup G} (hD : D ∈ Om R Ψ) (hD' : D' ∈ Om R Ψ)
    (hne : D ≠ D') (hX : X ∈ R) (hXle : X ≤ D ⊔ D') (hXD : X ≠ D) (hXD' : X ≠ D') : False := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hA := hS.mem 0 3 (by decide)
  have hB₁ := hS.mem 2 1 (by decide)
  have hXO : X ∈ Om R Ψ := mem_Om_of_le h hS hX (hXle.trans (sup_le (le_W_of_mem_Om hD)
    (le_W_of_mem_Om hD')))
  have hW₂ : ∀ {Y : Subgroup G}, Y ∈ Om R Ψ → ∀ y ∈ Y, ∀ b ∈ xg Ψ 2 1,
      ⁅y, b⁆ ∈ M R (xg Ψ 0 3) ⊓ M R (xg Ψ 2 1) := by
    intro Y hY y hy b hb
    obtain ⟨-, hstar, hl⟩ := special_21 h hS h8 hΔ hAΔ hY
    exact ⟨QD.le_M hstar.1 (Subgroup.commutator_mem_commutator hy hb),
      QD.le_M hl (Subgroup.commutator_mem_commutator hy hb)⟩
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB₁
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
  have hDD' : Commuting D D' := (commuting_W₁ h hS).mono (le_W_of_mem_Om hD)
    (le_W_of_mem_Om hD')
  have hle : D ≤ Subgroup.normalizer ((D' : Subgroup G) : Set G) :=
    le_normalizer_of_conjSub_le fun g hg =>
      (conjSub_of_forall_commute fun k hk => hDD' g hg k hk).le
  have hx' : x ∈ ((D : Subgroup G) : Set G) * ((D' : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hXle hx
  obtain ⟨d, hd, d', hd', rfl⟩ := hx'
  beta_reduce at hx hx1
  have hd'1 : d' ≠ 1 := by
    rintro rfl
    rw [mul_one] at hx hx1
    have hmem : d ∈ X ⊓ D := ⟨hx, hd⟩
    rw [inf_eq_bot hR hiso hX hD.1.1.1 hXD, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [one_mul] at hx hx1
    have hmem : d' ∈ X ⊓ D' := ⟨hx, hd'⟩
    rw [inf_eq_bot hR hiso hX hD'.1.1.1 hXD', Subgroup.mem_bot] at hmem
    exact hx1 hmem
  set y := ⁅d', b⁆ with hy
  have hid : ⁅d * d', b⁆ = y * ⁅y⁻¹, d⁆ * ⁅d, b⁆ := by
    simp only [hy, commutatorElement_def]
    group
  have ht : ⁅y⁻¹, d⁆ ∈ xg Ψ 0 3 ⊓ (M R (xg Ψ 0 3) ⊓ M R (xg Ψ 2 1)) := by
    refine ⟨?_, ?_⟩
    · rw [← (Q_eq_M h hA).2.2.1]
      exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (hW₂ hD' d' hd' b hb).1)
        (QD.le_M hD.1 hd)
    · have e : ⁅y⁻¹, d⁆ = y⁻¹ * ⁅d * d', b⁆ * ⁅d, b⁆⁻¹ := by
        rw [hid]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hW₂ hD' d' hd' b hb))
        (hW₂ hXO _ hx b hb)) (Subgroup.inv_mem _ (hW₂ hD d hd b hb))
  have hbot : xg Ψ 0 3 ⊓ (M R (xg Ψ 0 3) ⊓ M R (xg Ψ 2 1)) = ⊥ :=
    eq_bot_iff.2 fun z hz => (inf_M_21_eq_bot h hS).le ⟨hz.1, hz.2.2⟩
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at ht
  have hyd : Commute d y := by
    have := (Commute.inv_left (show Commute y⁻¹ d from ht)).symm
    rwa [inv_inv] at this
  obtain ⟨hs', hstar', -⟩ := special_21 h hS h8 hΔ hAΔ hD'
  have hsp := (special_of_not_commuting h hA hD.1 hstar'.1
    (not_commuting_comm h hS h8 hΔ hAΔ hD' hD hne.symm)).1
  have hy1 : y = 1 := eq_one_of_commute_of_special hR hiso hD.1.1.1 hstar'.1.1.1 hsp hd hd1
    (Subgroup.commutator_mem_commutator hd' hb) hyd
  apply hd'1
  refine eq_one_of_commute_of_special hR hiso hB₁ hD'.1.1.1 hs'.symm hb hb1 hd' ?_
  rw [hy, commutatorElement_eq_one_iff_mul_comm] at hy1
  exact hy1.symm

omit h8 hΔ hAΔ in
theorem mem_Om_02 : xg Ψ 0 2 ∈ Om R Ψ :=
  ⟨hS.mem_lambdaSet_row h.root (by decide) (by decide) (by decide),
    hS.mem_lambdaSet_col h.root (by decide) (by decide) (by decide)⟩

omit h8 hΔ hAΔ in
theorem mem_Om_13 : xg Ψ 1 3 ∈ Om R Ψ :=
  ⟨hS.mem_lambdaSet_col h.root (by decide) (by decide) (by decide),
    hS.mem_lambdaSet_row h.root (by decide) (by decide) (by decide)⟩

omit h8 hΔ hAΔ in
theorem hid_eq_0132 [CharP F 2] : hid R Ψ = hidAt R Ψ 0 1 3 2 := by
  have e := conjSub_hidAt (Ψ := Ψ) h.root (Equiv.swap 2 3) (s₁ := 0) (s₂ := 1) (t₁ := 2)
    (t₂ := 3) (by decide) (by decide) (by decide) (by decide)
  rw [conjSub_hid_swap23 h hS] at e
  rw [e]
  have h0 : (Equiv.swap (2 : Fin 4) 3) 0 = 0 := by decide
  have h1 : (Equiv.swap (2 : Fin 4) 3) 1 = 1 := by decide
  have h2 : (Equiv.swap (2 : Fin 4) 3) 2 = 3 := by decide
  have h3 : (Equiv.swap (2 : Fin 4) 3) 3 = 2 := by decide
  rw [h0, h1, h2, h3]

omit h8 hΔ hAΔ in
theorem hid_le_M_02 [CharP F 2] : hid R Ψ ≤ M R (xg Ψ 0 2) := by
  rw [hid_eq_0132 h hS]
  exact inf_le_left.trans inf_le_left

theorem eq_of_commuting_01 [CharP F 2] {D : Subgroup G} (hD : D ∈ Om R Ψ)
    (hDP : Commuting D (xg Ψ 0 1)) : D = xg Ψ 0 2 := by
  have := h.finite
  have hR := h.root
  have hDM : D ≤ M R (xg Ψ 0 2) := by
    intro d hd
    obtain ⟨c', hc', c, hc, hn⟩ := exists_mul_mem_hid h hS (le_W_of_mem_Om hD hd)
    have hc'1 : c' = 1 := by
      refine eq_one_of_forall_commute hR h.noIsolated (hS.mem 1 3 (by decide))
        (hS.mem 0 1 (by decide)) (hS.special (by decide) (by decide) (by decide)).symm hc'
        fun p hp => ?_
      have e : c' = d * ((c' * c)⁻¹ * d)⁻¹ * c⁻¹ := by group
      rw [e]
      exact ((hDP d hd p hp).mul_left (commuting_hid_01 _ hn p hp).inv_left).mul_left
        ((commuting_xg (Ψ := Ψ) (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 1)
          (by decide) (by decide) c hc p hp).inv_left)
    subst hc'1
    have e : d = c * ((1 * c)⁻¹ * d) := by group
    rw [e]
    exact Subgroup.mul_mem _ (QD.le_M_self hc) (hid_le_M_02 h hS hn)
  have hmem : D ∈ insert (xg Ψ 0 2) (lambdaSet R (xg Ψ 0 2)) := by
    rw [← (Q_eq_M h (hS.mem 0 2 (by decide))).2.1]
    exact ⟨hD.1.1.1, hDM⟩
  rcases hmem with h1 | h1
  · exact h1
  · by_contra hne
    exact not_mem_lambdaSet_of_mem_Om h hS h8 hΔ hAΔ (mem_Om_02 h hS) hD (Ne.symm hne) h1

theorem eq_one_of_commute_01 [CharP F 2] {D : Subgroup G} (hD : D ∈ Om R Ψ)
    (hDC : D ≠ xg Ψ 0 2) {d : G} (hd : d ∈ D) (hdP : ∀ p ∈ xg Ψ 0 1, Commute d p) :
    d = 1 := by
  have := h.finite
  have hR := h.root
  have hA := hS.mem 0 3 (by decide)
  have hA₀ := mem_omegaSet_30 hS
  by_contra hd1
  obtain ⟨n, -, -, φ, hφA, -⟩ := (hS.opp 0 3 (by decide)).exists_mulEquiv_SL2' hR hA
  have hDs := mem_lambdaStar_of_mem_Om hS hR hD
  have hPs : xg Ψ 0 1 ∈ lambdaStar R (xg Ψ 0 3) (xg Ψ 3 0) :=
    ⟨hS.mem_lambdaSet_row hR (by decide) (by decide) (by decide),
      hS.mem 0 1 (by decide), hS.special (by decide) (by decide) (by decide)⟩
  obtain ⟨dd, hadd, -, hd1', -, hDd, hconj⟩ := Sec8Field.exists_param h hA hA₀ hφA hDs hd hd1
  apply hDC
  refine eq_of_commuting_01 h hS h8 hΔ hAΔ hD fun x hx p hp => ?_
  obtain ⟨s, rfl⟩ := hDd x hx
  by_cases hs : s = 0
  · subst hs
    have h00 := hadd 0 0
    rw [add_zero] at h00
    rw [left_eq_mul.1 h00]
    exact Commute.one_left p
  set c : (GaloisField 2 n)ˣ := Units.mk0 s hs
  have e : dd s = FrameSL3.torPar φ c * d * (FrameSL3.torPar φ c)⁻¹ := by
    rw [← hd1', hconj c 1, mul_one]
    rfl
  rw [e]
  have hPc := Sec8Field.conjSub_torPar_of_mem_lambdaStar h hA hA₀ hφA hPs c⁻¹
  have hp' : (FrameSL3.torPar φ c)⁻¹ * p * (FrameSL3.torPar φ c) ∈ xg Ψ 0 1 := by
    rw [← hPc]
    refine ⟨p, hp, ?_⟩
    rw [← Sec8Field.torPar_inv]
    simp
  have := hdP _ hp'
  calc FrameSL3.torPar φ c * d * (FrameSL3.torPar φ c)⁻¹ * p =
      FrameSL3.torPar φ c * (d * ((FrameSL3.torPar φ c)⁻¹ * p * FrameSL3.torPar φ c)) *
        (FrameSL3.torPar φ c)⁻¹ := by group
    _ = FrameSL3.torPar φ c * (((FrameSL3.torPar φ c)⁻¹ * p * FrameSL3.torPar φ c) * d) *
        (FrameSL3.torPar φ c)⁻¹ := by rw [this.eq]
    _ = p * (FrameSL3.torPar φ c * d * (FrameSL3.torPar φ c)⁻¹) := by group

end Points

end CaseB

end CFSG.Timmesfeld.ARS
