module

public import CFSG.Timmesfeld.ARS.CaseBB2

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

variable (R Ψ) in
noncomputable abbrev fundSub [CharP F 2] : Subgroup G :=
  xg Ψ 2 1 ⊔ xg Ψ 1 2 ⊔ (xg Ψ 1 3 ⊔ xg Ψ 3 1) ⊔ (hU R Ψ ⊔ hU R (perm Ψ σT))

abbrev σC : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

abbrev σL : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

section Pm

variable [CharP F 2]

theorem pm_conj_xs (σ : Equiv.Perm (Fin 4)) {i j : Fin 4} (hij : i ≠ j) (s : F) :
    Ψ (pm σ) * xs Ψ hij s * (Ψ (pm σ))⁻¹ = xs Ψ (σ.injective.ne hij) s := by
  rw [xs, xs, ← map_inv, ← map_mul, ← map_mul, pm_mul_transvection_mul_inv]

theorem pmC_conj_xs13 (s : F) : Ψ (pm σC) * xs Ψ ne13 s * (Ψ (pm σC))⁻¹ = xs Ψ ne31 s := by
  rw [pm_conj_xs]
  rfl

theorem pmC_conj_xs02 (s : F) : Ψ (pm σC) * xs Ψ ne02 s * (Ψ (pm σC))⁻¹ = xs Ψ ne20 s := by
  rw [pm_conj_xs]
  rfl

theorem pmC_mul_pm13 :
    Ψ (pm σC) * Ψ (pm (Equiv.swap 1 3)) = Ψ (pm (Equiv.swap 1 3)) * Ψ (pm σC) := by
  rw [← map_mul, ← map_mul, pm_mul, pm_mul]
  congr 2
  decide

theorem conjSub_hU_pmC (h : Hyp G R) (hS : Skel R Ψ) :
    conjSub (hU R Ψ) (Ψ (pm σC)) = hU R (perm Ψ σT) := by
  have e : hidAt R (perm Ψ σL) 0 1 2 3 = hidAt R (perm Ψ σL) 1 0 3 2 :=
    hid_eq_1032 h (hS.perm σL)
  rw [hidAt_perm, hidAt_perm] at e
  rw [hU, conjSub_hidAt h.root σC ne03 ne12 ne02 ne31, hU_perm_T]
  rw [show σL 0 = 1 from by decide, show σL 1 = 2 from by decide,
    show σL 2 = 0 from by decide, show σL 3 = 3 from by decide] at e
  rw [e, show σC 0 = 2 from by decide, show σC 3 = 1 from by decide,
    show σC 1 = 3 from by decide, show σC 2 = 0 from by decide]

end Pm

section Gen

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ)
include h hS

omit h hS in
theorem xg21_le_fundSub : xg Ψ 2 1 ≤ fundSub R Ψ :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

omit h hS in
theorem xg12_le_fundSub : xg Ψ 1 2 ≤ fundSub R Ψ :=
  le_sup_right.trans (le_sup_left.trans le_sup_left)

omit h hS in
theorem xg13_le_fundSub : xg Ψ 1 3 ≤ fundSub R Ψ :=
  le_sup_left.trans (le_sup_right.trans le_sup_left)

omit h hS in
theorem xg31_le_fundSub : xg Ψ 3 1 ≤ fundSub R Ψ :=
  le_sup_right.trans (le_sup_right.trans le_sup_left)

omit h hS in
theorem hU_le_fundSub : hU R Ψ ≤ fundSub R Ψ :=
  le_sup_left.trans le_sup_right

omit h hS in
theorem hU'_le_fundSub : hU R (perm Ψ σT) ≤ fundSub R Ψ :=
  le_sup_right.trans le_sup_right

omit h hS in
theorem pm13_mem_fundSub : Ψ (pm (Equiv.swap 1 3)) ∈ fundSub R Ψ :=
  sup_le xg13_le_fundSub xg31_le_fundSub (pm_swap_mem_sup ne13)

omit h hS in
theorem commutatorElement_mem {L : Subgroup G} {a b : G} (ha : a ∈ L) (hb : b ∈ L) :
    ⁅a, b⁆ ∈ L := by
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)

omit h hS in
theorem commutator_le_of_le {L H₁ H₂ : Subgroup G} (h₁ : H₁ ≤ L) (h₂ : H₂ ≤ L) :
    ⁅H₁, H₂⁆ ≤ L :=
  (Subgroup.commutator_le).2 fun _ ha _ hb => commutatorElement_mem (h₁ ha) (h₂ hb)

theorem xs02_mem_and_xs20_mem [Finite F] (hP : PtHyp R Ψ) (hU1 : hU R Ψ ≠ ⊥) (t : F) :
    xs Ψ ne02 t ∈ fundSub R Ψ ∧ xs Ψ ne20 t ∈ fundSub R Ψ := by
  obtain ⟨e, ι, hι⟩ := exists_linParamU h hS
  have he := hι.one_le hU1
  set v : Fin e → F := Pi.single ⟨0, he⟩ 1 with hv
  have hv0 : v ≠ 0 := fun h0 => one_ne_zero (by
    have := congrFun h0 ⟨0, he⟩
    rwa [hv, Pi.single_eq_same] at this)
  have hq : Qc R Ψ (ι v) ≠ 0 := fun h0 => hv0 (hι.eq_zero_of_Qc h hS hP h0)
  set s := t / Qc R Ψ (ι v) with hs
  have hsq : s * Qc R Ψ (ι v) = t := div_mul_cancel₀ t hq
  have e1 := hι.commutator_xs13 h hS s v
  rw [hsq] at e1
  set π := Ψ (pm (Equiv.swap 1 3)) with hπ
  set g := Ψ (pm σC) with hg
  have hL : Lc R Ψ (ι (s • v)) = π * ι (s • v) * π⁻¹ := Lc_eq_conj_pm13 h hS (hι.mem _)
  have e2 : xs Ψ ne02 t = ⁅xs Ψ ne13 s, ι v⁆ * (π * ι (s • v) * π⁻¹)⁻¹ := by
    rw [e1, ← hL]
    group
  have hπL := pm13_mem_fundSub (R := R) (Ψ := Ψ)
  refine ⟨?_, ?_⟩
  · rw [e2]
    refine Subgroup.mul_mem _ (commutatorElement_mem (xg13_le_fundSub (xs_mem _ _))
      (hU_le_fundSub (hι.mem v))) (Subgroup.inv_mem _ ?_)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hπL (hU_le_fundSub (hι.mem _)))
      (Subgroup.inv_mem _ hπL)
  · have hgU : ∀ w, g * ι w * g⁻¹ ∈ fundSub R Ψ := fun w => by
      apply hU'_le_fundSub
      rw [← conjSub_hU_pmC h hS]
      exact conj_mem_conjSub _ (hι.mem w)
    have e3 : xs Ψ ne20 t = g * xs Ψ ne02 t * g⁻¹ := (pmC_conj_xs02 t).symm
    have e4 : g * (π * ι (s • v) * π⁻¹) * g⁻¹ = π * (g * ι (s • v) * g⁻¹) * π⁻¹ := by
      have hgπ : g * π = π * g := pmC_mul_pm13
      have hgπ' : π⁻¹ * g⁻¹ = g⁻¹ * π⁻¹ := by
        rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hgπ]
      calc g * (π * ι (s • v) * π⁻¹) * g⁻¹ = (g * π) * ι (s • v) * (π⁻¹ * g⁻¹) := by group
        _ = (π * g) * ι (s • v) * (g⁻¹ * π⁻¹) := by rw [hgπ, hgπ']
        _ = π * (g * ι (s • v) * g⁻¹) * π⁻¹ := by group
    have e5 : g * ⁅xs Ψ ne13 s, ι v⁆ * g⁻¹ = ⁅xs Ψ ne31 s, g * ι v * g⁻¹⁆ := by
      rw [← pmC_conj_xs13 (Ψ := Ψ) s, ← hg, commutatorElement_def, commutatorElement_def]
      group
    rw [e3, e2, show g * (⁅xs Ψ ne13 s, ι v⁆ * (π * ι (s • v) * π⁻¹)⁻¹) * g⁻¹ =
      (g * ⁅xs Ψ ne13 s, ι v⁆ * g⁻¹) * (g * (π * ι (s • v) * π⁻¹) * g⁻¹)⁻¹ by group, e4, e5]
    refine Subgroup.mul_mem _ (commutatorElement_mem (xg31_le_fundSub (xs_mem _ _)) (hgU v))
      (Subgroup.inv_mem _ ?_)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hπL (hgU _)) (Subgroup.inv_mem _ hπL)

theorem xg02_le_and_xg20_le [Finite F] (hP : PtHyp R Ψ) (hU1 : hU R Ψ ≠ ⊥) :
    xg Ψ 0 2 ≤ fundSub R Ψ ∧ xg Ψ 2 0 ≤ fundSub R Ψ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨t, rfl⟩ := (mem_xg_iff ne02).1 hx
    exact (xs02_mem_and_xs20_mem h hS hP hU1 t).1
  · obtain ⟨t, rfl⟩ := (mem_xg_iff ne20).1 hx
    exact (xs02_mem_and_xs20_mem h hS hP hU1 t).2

theorem xg03_le_and_xg30_le [Finite F] (hP : PtHyp R Ψ) (hU1 : hU R Ψ ≠ ⊥) :
    xg Ψ 0 3 ≤ fundSub R Ψ ∧ xg Ψ 3 0 ≤ fundSub R Ψ := by
  obtain ⟨hC, hC₀⟩ := xg02_le_and_xg20_le h hS hP hU1
  have h01 : xg Ψ 0 1 ≤ fundSub R Ψ := by
    rw [← commutator_xg ne02 ne21 ne01]
    exact commutator_le_of_le hC xg21_le_fundSub
  have h10 : xg Ψ 1 0 ≤ fundSub R Ψ := by
    rw [← commutator_xg ne12 ne20 ne10]
    exact commutator_le_of_le xg12_le_fundSub hC₀
  refine ⟨?_, ?_⟩
  · rw [← commutator_xg ne01 ne13 ne03]
    exact commutator_le_of_le h01 xg13_le_fundSub
  · rw [← commutator_xg ne31 ne10 ne30]
    exact commutator_le_of_le xg31_le_fundSub h10

theorem fundSub_eq_top [Finite F] (hB : HypB G R (xg Ψ 0 3)) : fundSub R Ψ = ⊤ := by
  have := h.finite
  have hR := h.root
  have hA : xg Ψ 0 3 ∈ R := hS.mem 0 3 ne03
  have h8 := hB.sec8
  obtain ⟨Δ, hΔ, hAΔ⟩ := hB.exists_isWeakTI
  have hA₀ := mem_omegaSet_30 hS
  have hP := ptHyp_of_hypB hB
  have hU1 := hU_ne_bot h hS hB
  obtain ⟨hC, -⟩ := xg02_le_and_xg20_le h hS hP hU1
  obtain ⟨-, hA₀L⟩ := xg03_le_and_xg30_le h hS hP hU1
  have hOm : ∀ D ∈ Om R Ψ, D ≤ fundSub R Ψ := by
    intro D hD
    by_cases hDC : D = xg Ψ 0 2
    · rw [hDC]
      exact hC
    obtain ⟨u, hu, rfl⟩ := exists_conjSub_hU_eq h hS hP hD hDC
    exact conjSub_le xg13_le_fundSub (hU_le_fundSub hu)
  have hV : levi R (xg Ψ 0 3) (xg Ψ 3 0) ≤ fundSub R Ψ := by
    rw [levi_eq_sup_of_ne h hA h8 hA₀ hΔ hAΔ (mem_leviSet_12 hS) (mem_leviSet_21 hS)
      (hS.xg_ne (by decide) (by decide) (by decide))]
    exact sup_le xg12_le_fundSub xg21_le_fundSub
  have hM : M R (xg Ψ 0 3) ≤ fundSub R Ψ := by
    rw [M_eq_gen_lambdaStar h hA hA₀]
    refine gen_le fun D' hD' => ?_
    obtain ⟨B, hB', hD'B⟩ := exists_mem_leviSet_mem_lambdaSet h hA h8 hA₀ hΔ hAΔ hD'
    obtain ⟨v, hv, hvB⟩ := exists_mem_levi_conjSub_eq h hA h8 hA₀ hΔ hAΔ hB' (mem_leviSet_12 hS)
    have hvA : conjSub (xg Ψ 0 3) v = xg Ψ 0 3 := conjSub_of_forall_commute fun a ha =>
      ((Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left _ _ hv)) a ha).symm
    have hD : conjSub D' v ∈ Om R Ψ := by
      refine ⟨?_, ?_⟩
      · have := conjSub_mem_lambdaSet hR hD'.1 v
        rwa [hvA] at this
      · have := conjSub_mem_lambdaSet hR hD'B v
        rwa [hvB] at this
    have e : conjSub (conjSub D' v) v⁻¹ = D' := by
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [← e]
    exact conjSub_le (hOm _ hD) (Subgroup.inv_mem _ (hV hv))
  have htop := gen_lambdaSet_sup_eq_top h hA hA₀
  rw [eq_top_iff, ← htop]
  exact sup_le ((gen_le fun C hC => QD.le_M hC).trans hM) hA₀L

end Gen

end CaseB

end CFSG.Timmesfeld.ARS
