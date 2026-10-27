module

public import CFSG.Timmesfeld.ARS.CaseBField

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

section Pm13

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ)
include h hS

omit h hS in
theorem pm13_eq : Ψ (pm (Equiv.swap 1 3)) = xs Ψ ne13 1 * xs Ψ ne31 1 * xs Ψ ne13 1 := by
  rw [pm_swap_eq ne13, map_mul, map_mul]

omit h hS in
theorem pm13_conj_xs {i j : Fin 4} (hij : i ≠ j) (s : F) :
    Ψ (pm (Equiv.swap 1 3)) * xs Ψ hij s * (Ψ (pm (Equiv.swap 1 3)))⁻¹ =
      xs Ψ ((Equiv.swap 1 3).injective.ne hij) s := by
  rw [xs, xs, ← map_inv, ← map_mul, ← map_mul, pm_mul_transvection_mul_inv]

omit h hS in
theorem pm13_mul_self : Ψ (pm (Equiv.swap 1 3)) * Ψ (pm (Equiv.swap 1 3)) = (1 : G) := by
  rw [← map_mul, pm_mul, Equiv.swap_mul_self, show (pm 1 : SpecialLinearGroup (Fin 4) F) = 1 from
    Subtype.ext (by
      rw [coe_pm, SpecialLinear.signedPerm_one]
      exact Matrix.diagonal_one), map_one]

theorem conjSub_hU_pm13 : conjSub (hU R Ψ) (Ψ (pm (Equiv.swap 1 3))) = hid R Ψ := by
  rw [conjSub_hidAt h.root _ ne03 ne12 ne02 ne31, hid_eq_0132 h hS]
  congr 1

theorem conjSub_hid_pm13 : conjSub (hid R Ψ) (Ψ (pm (Equiv.swap 1 3))) = hU R Ψ := by
  rw [← conjSub_hU_pm13 h hS, ← conjSub_mul, pm13_mul_self, conjSub_one]

theorem hU_inf_M_03 : hU R Ψ ⊓ M R (xg Ψ 0 3) = ⊥ := by
  refine eq_bot_iff.2 fun u hu => ?_
  rw [Subgroup.mem_bot]
  refine eq_one_of_mem_M_of_conjSub_eq h (hS.mem 0 3 ne03) (mem_omegaSet_30 hS) hu.2 ?_
  exact conjSub_of_forall_commute fun x hx => commuting_hU h hS ne30 (by decide) u hu.1 x hx

omit [CharP F 2] in
theorem mul_self_of_mem_hid {n : G} (hn : n ∈ hid R Ψ) : n * n = 1 := by
  have h1 := sq_mem_of_mem_M h (hS.mem 0 3 ne03) hn.1.1
  have h2 : n * n ∈ M R (xg Ψ 1 2) := Subgroup.mul_mem _ hn.1.2 hn.1.2
  have : n * n ∈ xg Ψ 0 3 ⊓ M R (xg Ψ 1 2) := ⟨h1, h2⟩
  rwa [inf_M_12_eq_bot h hS, Subgroup.mem_bot] at this

theorem Lc_eq_conj_pm13 {u : G} (hu : u ∈ hU R Ψ) :
    Lc R Ψ u = Ψ (pm (Equiv.swap 1 3)) * u * (Ψ (pm (Equiv.swap 1 3)))⁻¹ := by
  have := h.finite
  have hR := h.root
  set π := Ψ (pm (Equiv.swap 1 3)) with hπ
  have hπinv : π⁻¹ = π := inv_eq_of_mul_eq_one_left (pm13_mul_self (Ψ := Ψ))
  have hπU : ∀ {v : G}, v ∈ hU R Ψ → π * v * π⁻¹ ∈ hid R Ψ := fun hv => by
    rw [← conjSub_hU_pm13 h hS]
    exact conj_mem_conjSub _ hv
  have hπN : ∀ {n : G}, n ∈ hid R Ψ → π * n * π⁻¹ ∈ hU R Ψ := fun hn => by
    rw [← conjSub_hid_pm13 h hS]
    exact conj_mem_conjSub _ hn
  have hππ : ∀ g : G, π * (π * g * π⁻¹) * π⁻¹ = g := fun g => by
    rw [hπinv]
    calc π * (π * g * π) * π = (π * π) * g * (π * π) := by group
      _ = g := by rw [pm13_mul_self]; group
  have hcen : ∀ k ∈ xg Ψ 0 2, ∀ m ∈ M R (xg Ψ 0 2), Commute k m :=
    fun k hk m hm => QD.commuting_M hR (hS.mem 0 2 ne02) k hk m hm
  have hC' : ∀ {v : G}, v ∈ hU R Ψ →
      xs Ψ ne13 1 * v * (xs Ψ ne13 1)⁻¹ = xs Ψ ne02 (Qc R Ψ v) * Lc R Ψ v * v := by
    intro v _
    rw [← commutator_eq_xs_mul_Lc (R := R) v, commutatorElement_def]
    group
  have hC₁ : ∀ {n : G}, n ∈ hid R Ψ →
      xs Ψ ne31 1 * n * (xs Ψ ne31 1)⁻¹ =
        xs Ψ ne02 (Qc R Ψ (π * n * π⁻¹)) * (π * Lc R Ψ (π * n * π⁻¹) * π⁻¹) * n := by
    intro n hn
    have e := commutator_eq_xs_mul_Lc (R := R) (Ψ := Ψ) (π * n * π⁻¹)
    have e2 := congrArg (fun g => π * g * π⁻¹) e
    rw [show π * ⁅xs Ψ ne13 1, π * n * π⁻¹⁆ * π⁻¹ =
        ⁅π * xs Ψ ne13 1 * π⁻¹, π * (π * n * π⁻¹) * π⁻¹⁆ by
          simp only [commutatorElement_def]; group,
      hππ, hπ, pm13_conj_xs, ← hπ] at e2
    rw [show π * (xs Ψ ne02 (Qc R Ψ (π * n * π⁻¹)) * Lc R Ψ (π * n * π⁻¹)) * π⁻¹ =
        (π * xs Ψ ne02 (Qc R Ψ (π * n * π⁻¹)) * π⁻¹) * (π * Lc R Ψ (π * n * π⁻¹) * π⁻¹) by
          group, hπ, pm13_conj_xs, ← hπ] at e2
    have e3 : xs Ψ ((Equiv.swap (1 : Fin 4) 3).injective.ne ne13) (1 : F) = xs Ψ ne31 1 := rfl
    have e4 : xs Ψ ((Equiv.swap (1 : Fin 4) 3).injective.ne ne02) (Qc R Ψ (π * n * π⁻¹)) =
        xs Ψ ne02 (Qc R Ψ (π * n * π⁻¹)) := rfl
    rw [e3, e4, commutatorElement_def] at e2
    calc xs Ψ ne31 1 * n * (xs Ψ ne31 1)⁻¹ =
        (xs Ψ ne31 1 * n * (xs Ψ ne31 1)⁻¹ * n⁻¹) * n := by group
      _ = _ := by rw [e2]
  have hL₁ := Lc_mem h hS hu
  set L₁ := Lc R Ψ u with hL₁_def
  set u₁ := π * L₁ * π⁻¹ with hu₁_def
  have hu₁ : u₁ ∈ hU R Ψ := hπN hL₁
  set v := π * Lc R Ψ u₁ * π⁻¹ with hv_def
  have hv : v ∈ hU R Ψ := hπN (Lc_mem h hS hu₁)
  have hyC : ∀ t : F, xs Ψ ne31 1 * xs Ψ ne02 t * (xs Ψ ne31 1)⁻¹ = xs Ψ ne02 t := fun t => by
    rw [(commuting_xg (Ψ := Ψ) ne31 ne02 (by decide) (by decide) _ (xs_mem _ _) _
      (xs_mem _ _)).eq]
    group
  have hyu : xs Ψ ne31 1 * u * (xs Ψ ne31 1)⁻¹ = u := by
    rw [(commuting_hU h hS ne31 (by decide) u hu _ (xs_mem _ _)).symm.eq]
    group
  have hx'C : ∀ t : F, xs Ψ ne13 1 * xs Ψ ne02 t * (xs Ψ ne13 1)⁻¹ = xs Ψ ne02 t := fun t => by
    rw [(commuting_xg (Ψ := Ψ) ne13 ne02 (by decide) (by decide) _ (xs_mem _ _) _
      (xs_mem _ _)).eq]
    group
  have hx'L : xs Ψ ne13 1 * L₁ * (xs Ψ ne13 1)⁻¹ = L₁ := by
    rw [(commuting_hid_13 h hS L₁ hL₁ _ (xs_mem _ _)).symm.eq]
    group
  have hm : Commute (xs Ψ ne02 (Qc R Ψ u)) (Lc R Ψ v * v * L₁) :=
    hcen _ (xs_mem _ _) _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hid_le_M_02 h hS (Lc_mem h hS hv)) (hU_le_M_02 hv)) (hid_le_M_02 h hS hL₁))
  have hLL : L₁ * L₁ = 1 := mul_self_of_mem_hid h hS hL₁
  have hsum : Qc R Ψ u + Qc R Ψ u₁ + Qc R Ψ v + Qc R Ψ u = Qc R Ψ u₁ + Qc R Ψ v := by
    linear_combination CharTwo.add_self_eq_zero (Qc R Ψ u)
  have e_pi : π * u * π⁻¹ = xs Ψ ne02 (Qc R Ψ u₁ + Qc R Ψ v) * Lc R Ψ v * (v * u) := by
    calc π * u * π⁻¹ = xs Ψ ne13 1 * (xs Ψ ne31 1 * (xs Ψ ne13 1 * u * (xs Ψ ne13 1)⁻¹) *
          (xs Ψ ne31 1)⁻¹) * (xs Ψ ne13 1)⁻¹ := by rw [hπ, pm13_eq]; group
      _ = xs Ψ ne13 1 * ((xs Ψ ne31 1 * xs Ψ ne02 (Qc R Ψ u) * (xs Ψ ne31 1)⁻¹) *
          (xs Ψ ne31 1 * L₁ * (xs Ψ ne31 1)⁻¹) * (xs Ψ ne31 1 * u * (xs Ψ ne31 1)⁻¹)) *
          (xs Ψ ne13 1)⁻¹ := by rw [hC' hu, ← hL₁_def]; group
      _ = xs Ψ ne13 1 * (xs Ψ ne02 (Qc R Ψ u) * (xs Ψ ne02 (Qc R Ψ u₁) * v * L₁) * u) *
          (xs Ψ ne13 1)⁻¹ := by rw [hyC, hC₁ hL₁, hyu]
      _ = (xs Ψ ne13 1 * xs Ψ ne02 (Qc R Ψ u) * (xs Ψ ne13 1)⁻¹) *
          (xs Ψ ne13 1 * xs Ψ ne02 (Qc R Ψ u₁) * (xs Ψ ne13 1)⁻¹) *
          (xs Ψ ne13 1 * v * (xs Ψ ne13 1)⁻¹) * (xs Ψ ne13 1 * L₁ * (xs Ψ ne13 1)⁻¹) *
          (xs Ψ ne13 1 * u * (xs Ψ ne13 1)⁻¹) := by group
      _ = xs Ψ ne02 (Qc R Ψ u) * xs Ψ ne02 (Qc R Ψ u₁) *
          (xs Ψ ne02 (Qc R Ψ v) * Lc R Ψ v * v) * L₁ * (xs Ψ ne02 (Qc R Ψ u) * L₁ * u) := by
        rw [hx'C, hx'C, hC' hv, hx'L, hC' hu, ← hL₁_def]
      _ = xs Ψ ne02 (Qc R Ψ u) * xs Ψ ne02 (Qc R Ψ u₁) * xs Ψ ne02 (Qc R Ψ v) *
          ((Lc R Ψ v * v * L₁) * xs Ψ ne02 (Qc R Ψ u)) * L₁ * u := by group
      _ = xs Ψ ne02 (Qc R Ψ u) * xs Ψ ne02 (Qc R Ψ u₁) * xs Ψ ne02 (Qc R Ψ v) *
          (xs Ψ ne02 (Qc R Ψ u) * (Lc R Ψ v * v * L₁)) * L₁ * u := by rw [← hm.eq]
      _ = (xs Ψ ne02 (Qc R Ψ u) * xs Ψ ne02 (Qc R Ψ u₁) * xs Ψ ne02 (Qc R Ψ v) *
          xs Ψ ne02 (Qc R Ψ u)) * Lc R Ψ v * v * (L₁ * L₁) * u := by group
      _ = xs Ψ ne02 (Qc R Ψ u₁ + Qc R Ψ v) * Lc R Ψ v * (v * u) := by
        rw [← xs_add, ← xs_add, ← xs_add, hsum, hLL]
        group
  have hCA : xg Ψ 0 2 ≤ M R (xg Ψ 0 3) :=
    QD.le_M (hS.mem_lambdaSet_row hR ne02 ne23 ne03)
  have hvu : v * u = 1 := by
    have hmem : v * u ∈ hU R Ψ ⊓ M R (xg Ψ 0 3) := by
      refine ⟨Subgroup.mul_mem _ hv hu, ?_⟩
      have e : v * u = (xs Ψ ne02 (Qc R Ψ u₁ + Qc R Ψ v) * Lc R Ψ v)⁻¹ * (π * u * π⁻¹) := by
        rw [e_pi]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hCA (xs_mem _ _))
        (Lc_mem h hS hv).1.1)) (hπU hu).1.1
    rwa [hU_inf_M_03 h hS, Subgroup.mem_bot] at hmem
  rw [hvu, mul_one] at e_pi
  have ht : xs Ψ ne02 (Qc R Ψ u₁ + Qc R Ψ v) = 1 := by
    have hmem : xs Ψ ne02 (Qc R Ψ u₁ + Qc R Ψ v) ∈ hid R Ψ ⊓ xg Ψ 0 2 := by
      refine ⟨?_, xs_mem _ _⟩
      have e : xs Ψ ne02 (Qc R Ψ u₁ + Qc R Ψ v) = (π * u * π⁻¹) * (Lc R Ψ v)⁻¹ := by
        rw [e_pi]
        group
      rw [e]
      exact Subgroup.mul_mem _ (hπU hu) (Subgroup.inv_mem _ (Lc_mem h hS hv))
    rwa [hid_inf_02 h hS, Subgroup.mem_bot] at hmem
  rw [ht, one_mul] at e_pi
  have hvu' : v = u := by
    have := eq_inv_of_mul_eq_one_left hvu
    rw [this, inv_eq_of_mul_eq_one_left (mul_self_of_mem_hU h hS hu)]
  rw [e_pi, hvu']

end Pm13

section Sqrt

variable [CharP F 2] [Finite F]

variable (F) in
noncomputable abbrev sqrtF (t : F) : F := (frobeniusEquiv F 2).symm t

theorem sqrtF_sq (t : F) : sqrtF F t ^ 2 = t := by
  have := frobenius_apply_frobeniusEquiv_symm F 2 t
  rwa [frobenius_def] at this

theorem sqrtF_add (s t : F) : sqrtF F (s + t) = sqrtF F s + sqrtF F t := map_add _ s t

theorem sqrtF_mul (s t : F) : sqrtF F (s * t) = sqrtF F s * sqrtF F t := map_mul _ s t

theorem sqrtF_sq' (t : F) : sqrtF F (t ^ 2) = t := by
  have := frobeniusEquiv_symm_apply_frobenius F 2 t
  rwa [frobenius_def] at this

end Sqrt

variable (R Ψ) in
@[expose] noncomputable def xU [Finite F] [CharP F 2] (ι : (Fin 1 → F) → G) (t : F) : G :=
  ι fun _ => sqrtF F (t / Qc R Ψ (ι fun _ => 1))

section One

variable [CharP F 2] [Finite F] (h : Hyp G R) (hS : Skel R Ψ) {ι : (Fin 1 → F) → G}
  (hι : LinParamU R Ψ 1 ι)
include h hS hι

omit h hS in
theorem xU_add (s t : F) : xU R Ψ ι (s + t) = xU R Ψ ι s * xU R Ψ ι t := by
  rw [xU, xU, xU, ← hι.add, add_div, sqrtF_add]
  rfl

omit h hS in
theorem xU_mem (t : F) : xU R Ψ ι t ∈ hU R Ψ := hι.mem _

omit h hS in
theorem xU_zero : xU R Ψ ι 0 = 1 := by
  have := xU_add hι 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

omit [Finite F] in
theorem Qc_ι_one (s : F) : Qc R Ψ (ι fun _ => s) = s ^ 2 * Qc R Ψ (ι fun _ => 1) := by
  have := hι.Qc_smul h hS s (fun _ => 1)
  rwa [show (s • fun _ : Fin 1 => (1 : F)) = fun _ => s from funext fun _ => by simp] at this

theorem Qc_xU (hP : PtHyp R Ψ) (t : F) : Qc R Ψ (xU R Ψ ι t) = t := by
  have hq : Qc R Ψ (ι fun _ => 1) ≠ 0 := fun h0 => by
    have := hι.eq_zero_of_Qc h hS hP h0
    exact one_ne_zero (congrFun this 0)
  rw [xU, Qc_ι_one h hS hι, sqrtF_sq, div_mul_cancel₀ _ hq]

omit h hS in
theorem exists_xU_eq (hP : PtHyp R Ψ) (h : Hyp G R) (hS : Skel R Ψ) {u : G}
    (hu : u ∈ hU R Ψ) : ∃ t, xU R Ψ ι t = u := by
  obtain ⟨v, rfl⟩ := hι.surj u hu
  refine ⟨Qc R Ψ (ι v), ?_⟩
  have hv : v = fun _ => v 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [xU, hv, Qc_ι_one h hS hι]
  have hq : Qc R Ψ (ι fun _ => 1) ≠ 0 := fun h0 => by
    have := hι.eq_zero_of_Qc h hS hP h0
    exact one_ne_zero (congrFun this 0)
  rw [mul_div_cancel_right₀ _ hq, sqrtF_sq']

omit h hS in
theorem xU_injective (hP : PtHyp R Ψ) (h : Hyp G R) (hS : Skel R Ψ) :
    Function.Injective (xU R Ψ ι) := by
  intro s t e
  have := congrArg (Qc R Ψ) e
  rwa [Qc_xU h hS hι hP, Qc_xU h hS hι hP] at this

omit h hS in
theorem blk02_conj_xU (c : Fˣ) (t : F) :
    blk Ψ ne02 (NaturalModule.diagElt c) * xU R Ψ ι t *
      (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹ = xU R Ψ ι ((c : F) ^ 2 * t) := by
  rw [xU, hι.smul, xU]
  congr 1
  funext _
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc, sqrtF_mul, sqrtF_sq']

theorem commutator_xs13_xU (hP : PtHyp R Ψ) (s t : F) :
    ⁅xs Ψ ne13 s, xU R Ψ ι t⁆ = xs Ψ ne02 (s * t) * Lc R Ψ (xU R Ψ ι (s ^ 2 * t)) := by
  have e := hι.commutator_xs13 h hS s (fun _ => sqrtF F (t / Qc R Ψ (ι fun _ => 1)))
  have hq : Qc R Ψ (ι fun _ => sqrtF F (t / Qc R Ψ (ι fun _ => 1))) = t := Qc_xU h hS hι hP t
  rw [hq] at e
  rw [xU, e, xU]
  congr 3
  funext _
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc, sqrtF_mul, sqrtF_sq']

theorem commute_xU_Lc (s t : F) : Commute (xU R Ψ ι s) (Lc R Ψ (xU R Ψ ι t)) := by
  have hβ : ∀ v w : Fin 1 → F, βU R Ψ ι v w = 0 := by
    have h11 : βU R Ψ ι (fun _ => 1) (fun _ => 1) = 0 := by
      rw [βU, show ((fun _ => (1 : F)) + fun _ => 1 : Fin 1 → F) = 0 from
        funext fun _ => CharTwo.add_self_eq_zero 1, hι.map_zero, Qc_one h hS,
        sub_sub, CharTwo.add_self_eq_zero, sub_zero]
    intro v w
    have hv : v = v 0 • fun _ => 1 := funext fun i => by simp [Subsingleton.elim i 0]
    have hw : w = w 0 • fun _ => 1 := funext fun i => by simp [Subsingleton.elim i 0]
    rw [hv, hw, hι.βU_smul_left h hS, hι.βU_smul_right h hS, h11, mul_zero, mul_zero]
  have e := (hι.xs_βU h hS (fun _ => sqrtF F (s / Qc R Ψ (ι fun _ => 1)))
    (fun _ => sqrtF F (t / Qc R Ψ (ι fun _ => 1)))).1
  rw [hβ, xs_zero, eq_comm, commutatorElement_eq_one_iff_mul_comm] at e
  exact e

end One

end CaseB

end CFSG.Timmesfeld.ARS
