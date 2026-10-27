module

public import CFSG.Sporadic.HN.Local.Stabilizer
public import CFSG.Sporadic.HN.Local.TypeCertificate

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK CFSG.Sporadic.Fi23 CFSG.Sporadic.Th

theorem t2_mem_stabHN : wG 12 ∈ stabHN := type_certificate.1

theorem t4_mem_stabHN : wG 13 ∈ stabHN := type_certificate.2.1

theorem thetaS_t2 :
    thetaS ⟨wG 12, t2_mem_stabHN⟩ = ⟨sig2, sig2_even⟩ :=
  thetaS_of_action t2_mem_stabHN type_certificate.2.2.1 labP_pit2

theorem thetaS_t4 :
    thetaS ⟨wG 13, t4_mem_stabHN⟩ = ⟨sig4, sig4_even⟩ :=
  thetaS_of_action t4_mem_stabHN type_certificate.2.2.2.1 labP_pit4

theorem x2_mem_stabHN : wG 2 ∈ stabHN := alt_certificate.1

theorem thetaS_x2 :
    (thetaS ⟨wG 2, x2_mem_stabHN⟩ : Equiv.Perm (Fin 12)) = pOne :=
  (ctuc_hn_point_stabilizer_alternating_twelve).2.2.1 x2_mem_stabHN

theorem theta_t2_type :
    (thetaS ⟨wG 12, t2_mem_stabHN⟩ : Equiv.Perm (Fin 12)).cycleType = Multiset.replicate 2 2 := by
  rw [thetaS_t2]; exact sig2_type

theorem theta_t4_type :
    (thetaS ⟨wG 13, t4_mem_stabHN⟩ : Equiv.Perm (Fin 12)).cycleType = Multiset.replicate 4 2 := by
  rw [thetaS_t4]; exact sig4_type

theorem theta_x2_type :
    (thetaS ⟨wG 2, x2_mem_stabHN⟩ : Equiv.Perm (Fin 12)).cycleType = Multiset.replicate 6 2 := by
  rw [thetaS_x2]; exact pOne_type

noncomputable def letterEl (j : ℕ) (z : ℤ) : J dHN :=
  if z.natAbs ≤ 2 then genG dHN z else if z.natAbs - 3 < j then
    (if 0 < z then wG (z.natAbs - 3) else (wG (z.natAbs - 3))⁻¹) else 1

theorem wG_eq (j : ℕ) : wG j = wordG (letterEl j) Native.invWords[j]! := slpG_eq _ _ j

theorem wordG_invWord_gen {G : Type*} [Group G] (f : ℤ → G) {w : List ℤ}
    (hw : ∀ z ∈ w, f (-z) = (f z)⁻¹) : wordG f (CFSG.Sporadic.F5.Native.invWord w) = (wordG f w)⁻¹ := by
  induction w with
  | nil => simp [wordG, CFSG.Sporadic.F5.Native.invWord]
  | cons z w ih =>
    have ih' := ih fun z' hz' => hw z' (List.mem_cons_of_mem _ hz')
    unfold CFSG.Sporadic.F5.Native.invWord at ih' ⊢
    simp only [wordG, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev] at ih' ⊢
    rw [ih', hw z List.mem_cons_self]

theorem genG_neg' {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    genG dHN (-z) = (genG dHN z)⁻¹ := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp [genG]

theorem w14_letters : ∀ z ∈ Native.invFusW,
    (z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∨ (3 ≤ z.natAbs ∧ z.natAbs - 3 < 14) := by
  decide +kernel

theorem w14_word : Native.invWords[14]! = Native.invFusW ++ [15] ++
    CFSG.Sporadic.F5.Native.invWord Native.invFusW := by
  decide +kernel

theorem letterEl_neg {z : ℤ} (hz : (z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∨
    (3 ≤ z.natAbs ∧ z.natAbs - 3 < 14)) : letterEl 14 (-z) = (letterEl 14 z)⁻¹ := by
  unfold letterEl
  rcases hz with h2 | ⟨h3, h4⟩
  · have h2' : z.natAbs ≤ 2 := by omega
    rw [ite_eq_left (by simpa using h2'), ite_eq_left h2']
    exact genG_neg' h2
  · have h2 : ¬ z.natAbs ≤ 2 := by omega
    rw [ite_eq_right (by simpa using h2), ite_eq_right h2, ite_eq_left (by simpa using h4),
      ite_eq_left h4]
    by_cases hp : 0 < z
    · rw [ite_eq_right (by omega), ite_eq_left hp]
      simp
    · rw [ite_eq_left (by omega), ite_eq_right hp, inv_inv]
      simp

theorem wG14_form : wG 14 = wordG (letterEl 14) Native.invFusW * wG 12 *
    (wordG (letterEl 14) Native.invFusW)⁻¹ := by
  have hneg : ∀ z ∈ Native.invFusW, letterEl 14 (-z) = (letterEl 14 z)⁻¹ :=
    fun z hz => letterEl_neg (w14_letters z hz)
  have hmid : letterEl 14 ((12 : ℤ) + 3) = wG 12 := by
    unfold letterEl
    norm_num
  rw [wG_eq, w14_word]
  have := wordG_invWord_gen (letterEl 14) hneg
  simp only [wordG, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one] at this ⊢
  rw [this]
  congr 2
  all_goals exact hmid

theorem isConj_t2_x2 : IsConj (wG 12) (wG 2) := by
  rw [← type_certificate.2.2.2.2.1]
  exact isConj_iff.2 ⟨_, wG14_form.symm⟩

end CFSG.Sporadic.HN.Local
