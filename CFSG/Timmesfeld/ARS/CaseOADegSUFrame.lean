module

public import CFSG.Timmesfeld.ARS.CaseOADegMinus
public import CFSG.Timmesfeld.ARS.CaseOADegSUDict
public import CFSG.Timmesfeld.ARS.CaseOADegSUCent

public section

namespace CFSG.Timmesfeld.ARS.CaseOADeg

open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin.Twisted CFSG.Timmesfeld.RankTwo
open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

section Idx

@[expose] def shortIdx (γ : Fin (5 - 1) → ℤ) :
    (Fin (4 / 2) ⊕ Fin (4 / 2)) × (Fin (4 / 2) ⊕ Fin (4 / 2)) :=
  if γ = sr nd3 then (.inl j0, .inr j1) else if γ = -sr nd3 then (.inr j0, .inl j1)
  else if γ = sr nd2 + sr nd3 then (.inl j0, .inl j1) else (.inr j0, .inr j1)

@[expose] def longIdx (γ : Fin (5 - 1) → ℤ) : Fin (4 / 2) ⊕ Fin (4 / 2) :=
  if γ = sr nd2 then .inl j1 else if γ = -sr nd2 then .inr j1
  else if γ = sr nd2 + 2 • sr nd3 then .inl j0 else .inr j0

theorem shortIdx_d3 : shortIdx (sr nd3) = (.inl j0, .inr j1) := by
  rw [shortIdx, ite_eq_left rfl]

theorem shortIdx_nd3 : shortIdx (-sr nd3) = (.inr j0, .inl j1) := by
  rw [shortIdx, ite_eq_right (ne_of_apply_ne' nd3 (by simp)), ite_eq_left rfl]

theorem shortIdx_d23 : shortIdx (sr nd2 + sr nd3) = (.inl j0, .inl j1) := by
  rw [shortIdx, ite_eq_right (ne_of_apply_ne' nd2 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd2 (by simp)), ite_eq_left rfl]

theorem shortIdx_nd23 : shortIdx (-(sr nd2 + sr nd3)) = (.inr j0, .inr j1) := by
  rw [shortIdx, ite_eq_right (ne_of_apply_ne' nd2 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd2 (by simp)), ite_eq_right (ne_of_apply_ne' nd2 (by simp))]

theorem longIdx_d2 : longIdx (sr nd2) = .inl j1 := by
  rw [longIdx, ite_eq_left rfl]

theorem longIdx_nd2 : longIdx (-sr nd2) = .inr j1 := by
  rw [longIdx, ite_eq_right (ne_of_apply_ne' nd2 (by simp)), ite_eq_left rfl]

theorem longIdx_d223 : longIdx (sr nd2 + 2 • sr nd3) = .inl j0 := by
  rw [longIdx, ite_eq_right (ne_of_apply_ne' nd3 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd2 (by simp)), ite_eq_left rfl]

theorem longIdx_nd223 : longIdx (-(sr nd2 + 2 • sr nd3)) = .inr j0 := by
  rw [longIdx, ite_eq_right (ne_of_apply_ne' nd2 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd3 (by simp)), ite_eq_right (ne_of_apply_ne' nd2 (by simp))]

theorem refl23 :
    reflection (Spin.cartanB (5 - 1)) nd2 (sr nd3) = sr nd2 + sr nd3 ∧
    reflection (Spin.cartanB (5 - 1)) nd2 (sr nd2 + sr nd3) = sr nd3 ∧
    reflection (Spin.cartanB (5 - 1)) nd2 (sr nd2 + 2 • sr nd3) = sr nd2 + 2 • sr nd3 ∧
    reflection (Spin.cartanB (5 - 1)) nd3 (sr nd2) = sr nd2 + 2 • sr nd3 ∧
    reflection (Spin.cartanB (5 - 1)) nd3 (sr nd2 + sr nd3) = sr nd2 + sr nd3 ∧
    reflection (Spin.cartanB (5 - 1)) nd3 (sr nd2 + 2 • sr nd3) = sr nd2 := by
  have h23 : Spin.cartanB (5 - 1) nd2 nd3 = -1 := by decide
  have h32 : Spin.cartanB (5 - 1) nd3 nd2 = -2 := by decide
  have r22 := refl_self nd2
  have r33 := refl_self nd3
  have r23 : reflection (Spin.cartanB (5 - 1)) nd2 (sr nd3) = sr nd2 + sr nd3 := by
    rw [CaseOANSL.reflection_single', h23]
    module
  have r32 : reflection (Spin.cartanB (5 - 1)) nd3 (sr nd2) = sr nd2 + 2 • sr nd3 := by
    rw [CaseOANSL.reflection_single', h32]
    module
  refine ⟨r23, ?_, ?_, r32, ?_, ?_⟩
  · rw [map_add, r22, r23]
    abel
  · rw [map_add, map_nsmul, r22, r23]
    module
  · rw [map_add, r32, r33]
    module
  · rw [map_add, map_nsmul, r32, r33]
    module

end Idx

section Elements

variable {F K : Type} [Field F] [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
  (ι : F →+* K) (ζ : K)

@[expose] noncomputable def suS (γ : Fin (5 - 1) → ℤ) (p : Fin 2 → F) : SU σ 4 :=
  suElt σ hσ (shortIdx γ).1 (shortIdx γ).2 (kap ι ζ p)

@[expose] noncomputable def suL (γ : Fin (5 - 1) → ℤ) (x : F) : SU σ 4 :=
  suLong σ (longIdx γ) (ι x)

variable {σ ι ζ} (hι : ∀ x, σ (ι x) = ι x)

include hι in
theorem trace_ι (x : F) : ι x + σ (ι x) = 0 := by
  rw [hι]
  exact CharTwo.add_self_eq_zero _

omit [CharP K 2] in
theorem suS_add (γ : Fin (5 - 1) → ℤ) (p q : Fin 2 → F) :
    suS σ hσ ι ζ γ (p + q) = suS σ hσ ι ζ γ p * suS σ hσ ι ζ γ q := by
  rw [suS, suS, suS, kap_add, suElt_add]

include hι in
theorem suL_add (γ : Fin (5 - 1) → ℤ) (x y : F) :
    suL σ ι γ (x + y) = suL σ ι γ x * suL σ ι γ y := by
  rw [suL, suL, suL, map_add, suLong_add _ (trace_ι hι x) (trace_ι hι y)]

theorem idx_d3 : idx (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2)) ≠ idx (Sum.inr j1) := by decide
theorem idx_nd3 : idx (Sum.inr j0 : Fin (4 / 2) ⊕ Fin (4 / 2)) ≠ idx (Sum.inl j1) := by decide
theorem idx_d23 : idx (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2)) ≠ idx (Sum.inl j1) := by decide
theorem idx_nd23 : idx (Sum.inr j0 : Fin (4 / 2) ⊕ Fin (4 / 2)) ≠ idx (Sum.inr j1) := by decide
theorem idx_1 : idx (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2)) ≠ idx (Sum.inr j0) := by decide

variable {b c : F} (hb : ι b = ζ + σ ζ) (hc : ι c = ζ * σ ζ)

include hι hb hc in
theorem suS_comm_suL (p : Fin 2 → F) (s : F) :
    ⁅suS σ hσ ι ζ (sr nd3) p, suL σ ι (sr nd2) s⁆ =
      suS σ hσ ι ζ (sr nd2 + sr nd3) (s • p) *
        suL σ ι (sr nd2 + 2 • sr nd3) (s * planeNorm b c p) := by
  have h := (suRelationsModel hσ 4).shortLong (Sum.inl j0) (Sum.inr j1) idx_d3 (kap ι ζ p) (ι s)
    (hι s)
  simp only [suRelationsModel_ξ, suRelationsModel_ξL, Sum.swap_inr] at h
  simp only [suS, suL, shortIdx_d3, shortIdx_d23, longIdx_d2, longIdx_d223, kap_smul, map_mul,
    ← norm_kap hb hc hι p]
  rw [h, mul_comm (ι s) (σ (kap ι ζ p) * kap ι ζ p)]

include hι hb hc in
theorem suS_comm_suS (p q : Fin 2 → F) :
    ⁅suS σ hσ ι ζ (sr nd3) p, suS σ hσ ι ζ (sr nd2 + sr nd3) q⁆ =
      suL σ ι (sr nd2 + 2 • sr nd3) (polarPlane b c p q) := by
  have h := (suRelationsModel hσ 4).trace (Sum.inl j0) (Sum.inr j1) idx_d3 (kap ι ζ p)
    (kap ι ζ q)
  simp only [suRelationsModel_ξ, suRelationsModel_ξL, Sum.swap_inr] at h
  simp only [suS, suL, shortIdx_d3, shortIdx_d23, longIdx_d223, ← polar_kap hb hc hι p q]
  exact h

omit [CharP K 2] in
theorem commute_of_comm_eq_one {G : Type*} [Group G] {x y : G} (h : ⁅x, y⁆ = 1) : Commute x y :=
  commutatorElement_eq_one_iff_commute.1 h

include hι in
theorem suS_commute_suL₁ (p : Fin 2 → F) (s : F) :
    Commute (suS σ hσ ι ζ (sr nd3) p) (suL σ ι (sr nd2 + 2 • sr nd3) s) := by
  simp only [suS, suL, shortIdx_d3, longIdx_d223]
  exact (commute_of_comm_eq_one ((suRelationsModel hσ 4).commLS (Sum.inl j0) (Sum.inl j0)
    (Sum.inr j1) idx_d3 (by decide) (by decide) (ι s) (kap ι ζ p) (hι s))).symm

include hι in
theorem suS_commute_suL₂ (p : Fin 2 → F) (s : F) :
    Commute (suS σ hσ ι ζ (sr nd2 + sr nd3) p) (suL σ ι (sr nd2 + 2 • sr nd3) s) := by
  simp only [suS, suL, shortIdx_d23, longIdx_d223]
  exact (commute_of_comm_eq_one ((suRelationsModel hσ 4).commLS (Sum.inl j0) (Sum.inl j0)
    (Sum.inl j1) idx_d23 (by decide) (by decide) (ι s) (kap ι ζ p) (hι s))).symm

include hι in
theorem suS_commute_suL₃ (p : Fin 2 → F) (s : F) :
    Commute (suS σ hσ ι ζ (sr nd2 + sr nd3) p) (suL σ ι (sr nd2) s) := by
  simp only [suS, suL, shortIdx_d23, longIdx_d2]
  exact (commute_of_comm_eq_one ((suRelationsModel hσ 4).commLS (Sum.inl j1) (Sum.inl j0)
    (Sum.inl j1) idx_d23 (by decide) (by decide) (ι s) (kap ι ζ p) (hι s))).symm

include hσ hι in
theorem suL_commute_suL (s t : F) :
    Commute (suL σ ι (sr nd2 + 2 • sr nd3) s) (suL σ ι (sr nd2) t) := by
  simp only [suL, longIdx_d223, longIdx_d2]
  exact commute_of_comm_eq_one ((suRelationsModel hσ 4).commLL (Sum.inl j0) (Sum.inl j1)
    (by decide) (ι s) (ι t) (hι s) (hι t))

end Elements

section Weyl

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)

omit [CharP K 2] in
theorem mat_suElt' {a b : Fin (4 / 2) ⊕ Fin (4 / 2)} (h : idx a ≠ idx b) (c : K) :
    SUExtras.mat σ 4 (suElt σ hσ a b c) = rootMatrix σ (crd a) (crd (Sum.swap b)) c := by
  rw [suElt, dite_eq_left h, SUExtras.mat_apply, coe_rootHom, toAdd_ofAdd]

omit [CharP K 2] in
theorem mat_suLong' (a : Fin (4 / 2) ⊕ Fin (4 / 2)) {c : K} (h : c + σ c = 0) :
    SUExtras.mat σ 4 (suLong σ a c) = longRootMatrix (crd a) c := by
  rw [suLong, dite_eq_left h, SUExtras.mat_apply, coe_longRootHom, toAdd_ofAdd]

omit [CharP K 2] in
theorem conj_suElt_of_mat {W : SU σ 4} {π : Equiv.Perm (Fin 4)}
    (hπ : ∀ s, π (Fin.rev s) = Fin.rev (π s))
    (hW : SUExtras.mat σ 4 W = SpecialLinear.signedPerm π 1)
    {a b a' b' : Fin (4 / 2) ⊕ Fin (4 / 2)} (hab : idx a ≠ idx b) (hab' : idx a' ≠ idx b')
    (ha : π (crd a) = crd a') (hb : π (crd (Sum.swap b)) = crd (Sum.swap b')) (c : K) :
    W * suElt σ hσ a b c * W⁻¹ = suElt σ hσ a' b' c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply SUExtras.mat_injective
  rw [map_mul, map_mul, hW, mat_suElt' hσ hab, mat_suElt' hσ hab',
    signedPerm_mul_rootMatrix (σ := σ) hπ (fun s => by simp) _ _ c, ha, hb]
  simp

omit [CharP K 2] in
theorem conj_suLong_of_mat {W : SU σ 4} {π : Equiv.Perm (Fin 4)}
    (hπ : ∀ s, π (Fin.rev s) = Fin.rev (π s))
    (hW : SUExtras.mat σ 4 W = SpecialLinear.signedPerm π 1)
    {a a' : Fin (4 / 2) ⊕ Fin (4 / 2)} (ha : π (crd a) = crd a') {c : K} (hc : c + σ c = 0) :
    W * suLong σ a c * W⁻¹ = suLong σ a' c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply SUExtras.mat_injective
  rw [map_mul, map_mul, hW, mat_suLong' a hc, mat_suLong' a' hc,
    signedPerm_mul_longRootMatrix (σ := σ) hπ (fun s => by simp) _ c, ha]
  simp

theorem one_trace : (1 : K) + σ 1 = 0 := by
  rw [map_one]
  exact CharTwo.add_self_eq_zero 1

variable (σ) in
@[expose] noncomputable def weyl₂ : SU σ 4 :=
  suLong σ (Sum.inl j1) 1 * suLong σ (Sum.inr j1) 1 * suLong σ (Sum.inl j1) 1

variable (σ) in
@[expose] noncomputable def weyl₃ : SU σ 4 :=
  suElt σ hσ (Sum.inl j0) (Sum.inr j1) 1 * suElt σ hσ (Sum.inr j0) (Sum.inl j1) 1 *
    suElt σ hσ (Sum.inl j0) (Sum.inr j1) 1

theorem mat_weyl₂ : SUExtras.mat σ 4 (weyl₂ σ) = SpecialLinear.signedPerm (Equiv.swap 1 2) 1 := by
  rw [weyl₂, map_mul, map_mul, mat_suLong' _ one_trace, mat_suLong' _ one_trace]
  have e : longRootMatrix (crd (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2))) (1 : K) =
      longRootMatrix (Fin.rev (crd (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2)))) (-(1 : K)⁻¹) := by
    rw [inv_one, CharTwo.neg_eq]
    rfl
  have hsw : Equiv.swap (crd (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2)))
      (Fin.rev (crd (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2)))) = Equiv.swap (1 : Fin 4) 2 := rfl
  have hsg : longSign (crd (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2))) (1 : K) = 1 := by
    funext s
    simp [longSign, CharTwo.neg_eq]
  rw [e, longRootMatrix_weyl (by decide) one_ne_zero, hsw, hsg]

theorem mat_weyl₃ : SUExtras.mat σ 4 (weyl₃ σ hσ) =
    SpecialLinear.signedPerm (Equiv.swap 0 1 * Equiv.swap 3 2) 1 := by
  rw [weyl₃, suElt_swap hσ idx_1, map_one, map_mul, map_mul, mat_suElt' hσ idx_d3,
    mat_suElt' hσ idx_1]
  have e : rootMatrix σ (crd (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2)))
      (crd (Sum.swap (Sum.inr j0 : Fin (4 / 2) ⊕ Fin (4 / 2)))) (-1 : K) =
      rootMatrix σ (crd (Sum.swap (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2))))
        (crd (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2))) (-(1 : K)⁻¹) := by
    rw [inv_one]
    rfl
  have hsw : Equiv.swap (crd (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2)))
      (crd (Sum.swap (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2)))) *
      Equiv.swap (Fin.rev (crd (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2))))
        (Fin.rev (crd (Sum.swap (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2))))) =
      Equiv.swap (0 : Fin 4) 1 * Equiv.swap 3 2 := rfl
  have hsg : shortSign σ (crd (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2)))
      (crd (Sum.swap (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2)))) (1 : K) = 1 := by
    funext s
    simp [shortSign, CharTwo.neg_eq]
  rw [e, rootMatrix_weyl (σ := σ) (by decide) (by decide) (by decide) (by decide) one_ne_zero, hsw,
    hsg]

theorem hπ₂ : ∀ s : Fin 4, Equiv.swap (1 : Fin 4) 2 (Fin.rev s) = Fin.rev (Equiv.swap 1 2 s) := by
  decide

theorem hπ₃ : ∀ s : Fin 4, (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 3 2 : Equiv.Perm (Fin 4))
    (Fin.rev s) = Fin.rev ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 3 2 : Equiv.Perm (Fin 4)) s) := by
  decide

end Weyl

section WeylConj

variable {F K : Type} [Field F] [Field K] [CharP K 2] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)
  {ι : F →+* K} {ζ : K}

@[expose] noncomputable def weylSU (k : Fin (5 - 1)) : SU σ 4 :=
  if k = nd2 then weyl₂ σ else weyl₃ σ hσ

omit [CharP K 2] in
theorem weylSU_two : weylSU hσ nd2 = weyl₂ σ := ite_eq_left rfl

omit [CharP K 2] in
theorem weylSU_three : weylSU hσ nd3 = weyl₃ σ hσ := ite_eq_right (by decide)

theorem weyl₂_suS_d3 (p : Fin 2 → F) :
    weyl₂ σ * suS σ hσ ι ζ (sr nd3) p * (weyl₂ σ)⁻¹ = suS σ hσ ι ζ (sr nd2 + sr nd3) p := by
  simp only [suS, shortIdx_d3, shortIdx_d23]
  exact conj_suElt_of_mat hσ hπ₂ mat_weyl₂ idx_d3 idx_d23 (by decide) (by decide) _

theorem weyl₂_suS_nd3 (p : Fin 2 → F) :
    weyl₂ σ * suS σ hσ ι ζ (-sr nd3) p * (weyl₂ σ)⁻¹ = suS σ hσ ι ζ (-(sr nd2 + sr nd3)) p := by
  simp only [suS, shortIdx_nd3, shortIdx_nd23]
  exact conj_suElt_of_mat hσ hπ₂ mat_weyl₂ idx_nd3 idx_nd23 (by decide) (by decide) _

theorem weyl₂_suS_d23 (p : Fin 2 → F) :
    weyl₂ σ * suS σ hσ ι ζ (sr nd2 + sr nd3) p * (weyl₂ σ)⁻¹ = suS σ hσ ι ζ (sr nd3) p := by
  simp only [suS, shortIdx_d3, shortIdx_d23]
  exact conj_suElt_of_mat hσ hπ₂ mat_weyl₂ idx_d23 idx_d3 (by decide) (by decide) _

theorem weyl₂_suS_nd23 (p : Fin 2 → F) :
    weyl₂ σ * suS σ hσ ι ζ (-(sr nd2 + sr nd3)) p * (weyl₂ σ)⁻¹ = suS σ hσ ι ζ (-sr nd3) p := by
  simp only [suS, shortIdx_nd3, shortIdx_nd23]
  exact conj_suElt_of_mat hσ hπ₂ mat_weyl₂ idx_nd23 idx_nd3 (by decide) (by decide) _

variable {hσ} (hι : ∀ x, σ (ι x) = ι x)
include hι

theorem weyl₂_suL_d2 (x : F) :
    weyl₂ σ * suL σ ι (sr nd2) x * (weyl₂ σ)⁻¹ = suL σ ι (-sr nd2) x := by
  simp only [suL, longIdx_d2, longIdx_nd2]
  exact conj_suLong_of_mat hπ₂ mat_weyl₂ (by decide) (trace_ι hι x)

theorem weyl₂_suL_nd2 (x : F) :
    weyl₂ σ * suL σ ι (-sr nd2) x * (weyl₂ σ)⁻¹ = suL σ ι (sr nd2) x := by
  simp only [suL, longIdx_d2, longIdx_nd2]
  exact conj_suLong_of_mat hπ₂ mat_weyl₂ (by decide) (trace_ι hι x)

theorem weyl₂_suL_d223 (x : F) :
    weyl₂ σ * suL σ ι (sr nd2 + 2 • sr nd3) x * (weyl₂ σ)⁻¹ = suL σ ι (sr nd2 + 2 • sr nd3) x := by
  simp only [suL, longIdx_d223]
  exact conj_suLong_of_mat hπ₂ mat_weyl₂ (by decide) (trace_ι hι x)

theorem weyl₂_suL_nd223 (x : F) :
    weyl₂ σ * suL σ ι (-(sr nd2 + 2 • sr nd3)) x * (weyl₂ σ)⁻¹ =
      suL σ ι (-(sr nd2 + 2 • sr nd3)) x := by
  simp only [suL, longIdx_nd223]
  exact conj_suLong_of_mat hπ₂ mat_weyl₂ (by decide) (trace_ι hι x)

theorem weyl₃_suL_d2 (x : F) :
    weyl₃ σ hσ * suL σ ι (sr nd2) x * (weyl₃ σ hσ)⁻¹ = suL σ ι (sr nd2 + 2 • sr nd3) x := by
  simp only [suL, longIdx_d2, longIdx_d223]
  exact conj_suLong_of_mat hπ₃ (mat_weyl₃ hσ) (by decide) (trace_ι hι x)

theorem weyl₃_suL_nd2 (x : F) :
    weyl₃ σ hσ * suL σ ι (-sr nd2) x * (weyl₃ σ hσ)⁻¹ = suL σ ι (-(sr nd2 + 2 • sr nd3)) x := by
  simp only [suL, longIdx_nd2, longIdx_nd223]
  exact conj_suLong_of_mat hπ₃ (mat_weyl₃ hσ) (by decide) (trace_ι hι x)

theorem weyl₃_suL_d223 (x : F) :
    weyl₃ σ hσ * suL σ ι (sr nd2 + 2 • sr nd3) x * (weyl₃ σ hσ)⁻¹ = suL σ ι (sr nd2) x := by
  simp only [suL, longIdx_d2, longIdx_d223]
  exact conj_suLong_of_mat hπ₃ (mat_weyl₃ hσ) (by decide) (trace_ι hι x)

theorem weyl₃_suL_nd223 (x : F) :
    weyl₃ σ hσ * suL σ ι (-(sr nd2 + 2 • sr nd3)) x * (weyl₃ σ hσ)⁻¹ = suL σ ι (-sr nd2) x := by
  simp only [suL, longIdx_nd2, longIdx_nd223]
  exact conj_suLong_of_mat hπ₃ (mat_weyl₃ hσ) (by decide) (trace_ι hι x)

variable {b c : F} (hb : ι b = ζ + σ ζ)
include hb

theorem weyl₃_suS_d3 (p : Fin 2 → F) :
    weyl₃ σ hσ * suS σ hσ ι ζ (sr nd3) p * (weyl₃ σ hσ)⁻¹ =
      suS σ hσ ι ζ (-sr nd3) (planeRefl b c planeOne p) := by
  simp only [suS, shortIdx_d3, shortIdx_nd3, kap_planeRefl hb hι]
  rw [suElt_swap hσ idx_1, hσ, CharTwo.neg_eq]
  exact conj_suElt_of_mat hσ hπ₃ (mat_weyl₃ hσ) idx_d3 idx_1 (by decide) (by decide) _

theorem weyl₃_suS_nd3 (p : Fin 2 → F) :
    weyl₃ σ hσ * suS σ hσ ι ζ (-sr nd3) p * (weyl₃ σ hσ)⁻¹ =
      suS σ hσ ι ζ (sr nd3) (planeRefl b c planeOne p) := by
  simp only [suS, shortIdx_d3, shortIdx_nd3, kap_planeRefl hb hι]
  rw [← CharTwo.neg_eq (σ (kap ι ζ p)), ← suElt_swap hσ idx_d3]
  exact conj_suElt_of_mat hσ hπ₃ (mat_weyl₃ hσ) idx_nd3 (by decide) (by decide) (by decide) _

theorem weyl₃_suS_d23 (p : Fin 2 → F) :
    weyl₃ σ hσ * suS σ hσ ι ζ (sr nd2 + sr nd3) p * (weyl₃ σ hσ)⁻¹ =
      suS σ hσ ι ζ (sr nd2 + sr nd3) (planeRefl b c planeOne p) := by
  simp only [suS, shortIdx_d23, kap_planeRefl hb hι]
  rw [← CharTwo.neg_eq (σ (kap ι ζ p)), ← suElt_swap hσ idx_d23]
  exact conj_suElt_of_mat hσ hπ₃ (mat_weyl₃ hσ) idx_d23 (by decide) (by decide) (by decide) _

theorem weyl₃_suS_nd23 (p : Fin 2 → F) :
    weyl₃ σ hσ * suS σ hσ ι ζ (-(sr nd2 + sr nd3)) p * (weyl₃ σ hσ)⁻¹ =
      suS σ hσ ι ζ (-(sr nd2 + sr nd3)) (planeRefl b c planeOne p) := by
  simp only [suS, shortIdx_nd23, kap_planeRefl hb hι]
  rw [← CharTwo.neg_eq (σ (kap ι ζ p)), ← suElt_swap hσ idx_nd23]
  exact conj_suElt_of_mat hσ hπ₃ (mat_weyl₃ hσ) idx_nd23 (by decide) (by decide) (by decide) _

theorem weylSU_conj (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k : Fin (5 - 1)}
    (hk : k = nd2 ∨ k = nd3) {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ pairRoots (minusDatum 5 hirr) nd2 nd3) :
    (MinusLong 5 γ → ∀ a, weylSU hσ k * suL σ ι γ a * (weylSU hσ k)⁻¹ =
      suL σ ι (reflection (Spin.cartanB (5 - 1)) k γ) a) ∧
    (MinusShort 5 γ → ∀ p, weylSU hσ k * suS σ hσ ι ζ γ p * (weylSU hσ k)⁻¹ =
      suS σ hσ ι ζ (reflection (Spin.cartanB (5 - 1)) k γ)
        (if k.val + 2 = 5 then planeRefl b c planeOne p else p)) := by
  obtain ⟨hγR, hγs⟩ := hγ
  obtain ⟨r23, r2s, r2l, r32, r3s, r3l⟩ := refl23
  have r22 := refl_self nd2
  have r33 := refl_self nd3
  have hL2 : MinusLong 5 (sr nd2) := minusLong_single (n := 5) (k := nd2) (by decide)
  have hL2' : MinusLong 5 (-sr nd2) := minusLong_neg_single (n := 5) (k := nd2) (by decide)
  have hL4 : MinusLong 5 (sr nd2 + 2 • sr nd3) := minusLong_B2long (n := 5) (i := nd2) (by decide)
  have hL4' : MinusLong 5 (-(sr nd2 + 2 • sr nd3)) := CaseOANSL.minusLong_neg' hL4
  have hS3 : MinusShort 5 (sr nd3) := minusShort_single (n := 5) (k := nd3) (by decide)
  have hS3' : MinusShort 5 (-sr nd3) := minusShort_neg_single (n := 5) (k := nd3) (by decide)
  have hS5 : MinusShort 5 (sr nd2 + sr nd3) := minusShort_B2sum (n := 5) (i := nd2) (by decide)
  have hS5' : ¬ MinusLong 5 (-(sr nd2 + sr nd3)) := fun h =>
    hS5.not_long (by simpa using CaseOANSL.minusLong_neg' h)
  have i2 : ¬ (nd2.val + 2 = 5) := by decide
  have i3 : nd3.val + 2 = 5 := by decide
  rcases pairB2₅ hγR hγs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl
  · exact ⟨fun _ a => by rw [weylSU_two, r22]; exact weyl₂_suL_d2 hι a,
      fun h => absurd hL2 h.not_long⟩
  · exact ⟨fun _ a => by rw [weylSU_three, r32]; exact weyl₃_suL_d2 hι a,
      fun h => absurd hL2 h.not_long⟩
  · exact ⟨fun _ a => by rw [weylSU_two, map_neg, r22, neg_neg]; exact weyl₂_suL_nd2 hι a,
      fun h => absurd hL2' h.not_long⟩
  · exact ⟨fun _ a => by rw [weylSU_three, map_neg, r32]; exact weyl₃_suL_nd2 hι a,
      fun h => absurd hL2' h.not_long⟩
  · exact ⟨fun h => absurd h hS3.not_long, fun _ p => by
      rw [weylSU_two, r23, ite_eq_right i2]; exact weyl₂_suS_d3 hσ p⟩
  · exact ⟨fun h => absurd h hS3.not_long, fun _ p => by
      rw [weylSU_three, r33, ite_eq_left i3]; exact weyl₃_suS_d3 hι hb p⟩
  · exact ⟨fun h => absurd h hS3'.not_long, fun _ p => by
      rw [weylSU_two, map_neg, r23, ite_eq_right i2]; exact weyl₂_suS_nd3 hσ p⟩
  · exact ⟨fun h => absurd h hS3'.not_long, fun _ p => by
      rw [weylSU_three, map_neg, r33, neg_neg, ite_eq_left i3]; exact weyl₃_suS_nd3 hι hb p⟩
  · exact ⟨fun h => absurd h hS5.not_long, fun _ p => by
      rw [weylSU_two, r2s, ite_eq_right i2]; exact weyl₂_suS_d23 hσ p⟩
  · exact ⟨fun h => absurd h hS5.not_long, fun _ p => by
      rw [weylSU_three, r3s, ite_eq_left i3]; exact weyl₃_suS_d23 hι hb p⟩
  · exact ⟨fun h => absurd h hS5', fun _ p => by
      rw [weylSU_two, map_neg, r2s, ite_eq_right i2]; exact weyl₂_suS_nd23 hσ p⟩
  · exact ⟨fun h => absurd h hS5', fun _ p => by
      rw [weylSU_three, map_neg, r3s, ite_eq_left i3]; exact weyl₃_suS_nd23 hι hb p⟩
  · exact ⟨fun _ a => by rw [weylSU_two, r2l]; exact weyl₂_suL_d223 hι a,
      fun h => absurd hL4 h.not_long⟩
  · exact ⟨fun _ a => by rw [weylSU_three, r3l]; exact weyl₃_suL_d223 hι a,
      fun h => absurd hL4 h.not_long⟩
  · exact ⟨fun _ a => by rw [weylSU_two, map_neg, r2l]; exact weyl₂_suL_nd223 hι a,
      fun h => absurd hL4' h.not_long⟩
  · exact ⟨fun _ a => by rw [weylSU_three, map_neg, r3l]; exact weyl₃_suL_nd223 hι a,
      fun h => absurd hL4' h.not_long⟩

end WeylConj

section RankOne

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary.SUExtras

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)

theorem exists_sl2_short :
    ∃ β : SpecialLinearGroup (Fin 2) K →* SU σ 4,
      (∀ a, β (sl2Upper a) = suElt σ hσ (Sum.inl j0) (Sum.inr j1) a) ∧
      ∀ a, β (sl2Lower a) = suElt σ hσ (Sum.inl j1) (Sum.inr j0) a :=
  CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels
    ((suRelationsModel hσ 4).shortRels hσ (show Even 4 by decide) (i := j0) (by decide))

include hσ in
theorem exists_sl2_long :
    ∃ β : SpecialLinearGroup (Fin 2) (sigmaFixedField σ) →* SU σ 4, Function.Injective β ∧
      (∀ c, β (sl2Upper c) = suLong σ (Sum.inl j1) c) ∧
      ∀ c, β (sl2Lower c) = suLong σ (Sum.inr j1) c := by
  have he : Even 4 := by decide
  have hk : ¬ j1.val + 1 < 4 / 2 := by decide
  obtain ⟨Θ₀, hΘ₀x, hΘ₀y⟩ :=
    CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (longModelRels hσ he hk)
  have hblock : ((SU σ 2).subtype.comp (rankOneLastEvenHom σ hσ he hk)).comp Θ₀ =
      SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (sigmaFixedField σ).subtype) := by
    refine CFSG.SectionRank.EvenCover.sl2_hom_ext (fun c => Units.ext ?_) (fun c => Units.ext ?_)
    · change SUExtras.mat σ 2 (rankOneLastEvenHom σ hσ he hk (Θ₀ (sl2Upper c))) =
        ((SpecialLinearGroup.map (sigmaFixedField σ).subtype (sl2Upper c) :
          SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      rw [mat_rankOneLastEvenHom, hΘ₀x, SpecialLinearGroup.map_apply_coe, coe_sl2Upper]
      change SUExtras.toBlock _ _ (SUExtras.mat σ 4 (suLong σ (Sum.inl j1) c)) = _
      rw [mat_suLong _ (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 c.2))]
      have e1 : crd (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2)) = (1 : Fin 4) := rfl
      have e2 : crd (Sum.swap (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2))) = (2 : Fin 4) := rfl
      have e3 : lowIdx (n := 4) j1 = (1 : Fin 4) := rfl
      have e4 : Fin.rev (1 : Fin 4) = 2 := rfl
      rw [e1, e2, e3, e4]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [SUExtras.toBlock]
    · change SUExtras.mat σ 2 (rankOneLastEvenHom σ hσ he hk (Θ₀ (sl2Lower c))) =
        ((SpecialLinearGroup.map (sigmaFixedField σ).subtype (sl2Lower c) :
          SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      rw [mat_rankOneLastEvenHom, hΘ₀y, SpecialLinearGroup.map_apply_coe, coe_sl2Lower]
      change SUExtras.toBlock _ _ (SUExtras.mat σ 4 (suLong σ (Sum.inr j1) c)) = _
      rw [mat_suLong _ (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 c.2))]
      have e1 : crd (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2)) = (2 : Fin 4) := rfl
      have e2 : crd (Sum.swap (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2))) = (1 : Fin 4) := rfl
      have e3 : lowIdx (n := 4) j1 = (1 : Fin 4) := rfl
      have e4 : Fin.rev (1 : Fin 4) = 2 := rfl
      rw [e1, e2, e3, e4]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [SUExtras.toBlock]
  have hinj : Function.Injective Θ₀ := by
    intro g g' h
    have h' := congrArg ((SU σ 2).subtype.comp (rankOneLastEvenHom σ hσ he hk)) h
    have h'' : SpecialLinearGroup.toGL (SpecialLinearGroup.map (sigmaFixedField σ).subtype g) =
        SpecialLinearGroup.toGL (SpecialLinearGroup.map (sigmaFixedField σ).subtype g') := by
      change (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (sigmaFixedField σ).subtype)) g =
        (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (sigmaFixedField σ).subtype)) g'
      rw [← hblock]
      exact h'
    have h3 := SpecialLinearGroup.toGL_injective h''
    ext a b
    have h4 := congrArg
      (fun M : SpecialLinearGroup (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) a b) h3
    simpa using h4
  refine ⟨(CFSG.LieType.CurtisTits.rankOne (Unitary.rootGroup σ hσ 4) j1).subtype.comp Θ₀,
    Subtype.val_injective.comp hinj, fun c => ?_, fun c => ?_⟩
  · rw [MonoidHom.comp_apply, hΘ₀x]
    rfl
  · rw [MonoidHom.comp_apply, hΘ₀y]
    rfl

theorem iSup_rankOne_SU4 {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) :
    ⨆ k, (Unitary.rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 4
        (Pi.single k 1) ⊔ Unitary.rootGroup (unitaryInvolution K 2 f)
          (unitaryInvolution_involutive hK) 4 (-Pi.single k 1)) =
      ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hK
  exact CaseM.iSup_rankOne_eq_top (D := Unitary.rootDatum hK 4)
    (Unitary.isCTGroupDatum hK 4 (by norm_num) ζ hζ)
    (show divisible 4 = ∅ by rw [divisible, ite_eq_left (by decide)])

end RankOne

end CFSG.Timmesfeld.ARS.CaseOADeg
