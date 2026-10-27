module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.ModelFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Setup

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S31

section Abstract

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

theorem not_mem_fixedFitting_of_fpf
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p)
    {c : X} (hcz : ∀ z ∈ fixedFitting f, z ≠ 1 → c * z * c⁻¹ ≠ z) : c ∉ fixedFitting f := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  intro hc0
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF.C0_ne_bot
  have hz1 : (z : X) ≠ 1 := fun h1 => hz (Subtype.ext h1)
  by_cases hc1 : c = 1
  · exact hcz z z.2 hz1 (by simp [hc1])
  · exact hcz c hc0 hc1 (by simp)

theorem fixedNormalizer_fpf
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) {c : X}
    (hc : c ∈ signalizerFixedSubgroup f)
    (hcz : ∀ z ∈ fixedFitting f, z ≠ 1 → c * z * c⁻¹ ≠ z) :
    ∀ y ∈ CFSG.fittingSubgroupOf (fixedNormalizer f), y ≠ 1 → c * y * c⁻¹ ≠ y := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  have hc0 := not_mem_fixedFitting_of_fpf h hf hcz
  intro y hy hy1 hcomm
  have hy' : y ∈ Subgroup.centralizer (fixedFitting f : Set X) := by
    rw [← (near_fitting_eq_centralizer h hf).1]
    exact hy
  refine hy1 (hF.fpf c hc hc0 y hy' ?_)
  rwa [mul_inv_eq_iff_eq_mul] at hcomm

theorem exists_fpf_fixedNormalizer
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    ∃ v ∈ signalizerFixedSubgroup f,
      ∀ y ∈ CFSG.fittingSubgroupOf (fixedNormalizer f), y ≠ 1 → v * y * v⁻¹ ≠ y := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  obtain ⟨v, hv, hv0⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne (fixedFitting_le f) hF.C0_ne)
  refine ⟨v, hv, fun y hy hy1 hcomm => hy1 ?_⟩
  have hy' : y ∈ Subgroup.centralizer (fixedFitting f : Set X) := by
    rw [← (near_fitting_eq_centralizer h hf).1]
    exact hy
  refine hF.fpf v hv hv0 y hy' ?_
  rwa [mul_inv_eq_iff_eq_mul] at hcomm

end Abstract

section Transfer

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem fpf_kJ
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) {c : Γ}
    (hc : c ∈ cenIn J (norIn A J))
    (hcz : ∀ z ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)), z ≠ 1 → c * z * c⁻¹ ≠ z) :
    ∀ y ∈ CFSG.fittingSubgroupOf (kJ A J), y ≠ 1 → c * y * c⁻¹ ≠ y := by
  obtain ⟨f, hf, hC, hC₀, hM, hFM⟩ := h.exists_frame_data hJ
  have hNS := h.nearSimple hJ
  rw [← hC] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  intro y hy hy1 hcomm
  rw [← hFM] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  refine fixedNormalizer_fpf hNS hf hc' (fun z hz hz1 hcomm' => ?_) y' hy'
    (fun h1 => hy1 (by rw [h1]; rfl)) (Subtype.ext hcomm)
  refine hcz (z : Γ) (by rw [← hC₀]; exact ⟨z, hz, rfl⟩) (fun h1 => hz1 (Subtype.ext h1)) ?_
  simpa using congrArg Subtype.val hcomm'

theorem exists_fpf_kJ
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ∃ v ∈ cenIn J (norIn A J),
      ∀ y ∈ CFSG.fittingSubgroupOf (kJ A J), y ≠ 1 → v * y * v⁻¹ ≠ y := by
  obtain ⟨f, hf, hC, hC₀, hM, hFM⟩ := h.exists_frame_data hJ
  obtain ⟨v, hv, hvy⟩ := exists_fpf_fixedNormalizer (h.nearSimple hJ) hf
  refine ⟨(v : Γ), by rw [← hC]; exact ⟨v, hv, rfl⟩, fun y hy hy1 hcomm => ?_⟩
  rw [← hFM] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  exact hvy y' hy' (fun h1 => hy1 (by rw [h1]; rfl)) (Subtype.ext hcomm)

theorem exists_good_involution
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    (hJ3 : ¬ Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) :
    ∃ c ∈ cenIn J (norIn A J), orderOf c = 2 ∧
      ∀ z ∈ CFSG.fittingSubgroupOf (cenIn J (norIn A J)), z ≠ 1 → c * z * c⁻¹ ≠ z := by
  obtain ⟨f, hf, hC, hC₀, hM, hFM⟩ := h.exists_frame_data hJ
  obtain ⟨t, ht, ht2, htz⟩ := NearSimple.exists_involution_fpf (h.nearSimple hJ) hf hJ3
  refine ⟨(t : Γ), by rw [← hC]; exact ⟨t, ht, rfl⟩, ?_, fun z hz hz1 hcomm => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact ht2
  · rw [← hC₀] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact htz z' hz' (fun h1 => hz1 (by rw [h1]; rfl)) (Subtype.ext hcomm)

theorem kJ_eq_cenIn_of_psl3
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    (hJ3 : Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) :
    kJ A J = cenIn J (norIn A J) := by
  obtain ⟨f, hf, hC, -, hM, -⟩ := h.exists_frame_data hJ
  rw [← hM, ← hC, (NearSimple.fixedNormalizer_eq_of_psl3 (h.nearSimple hJ) hf hJ3).1]

end Transfer

theorem padicValNat_235 (a b e : ℕ) :
    padicValNat 2 (2 ^ a * 3 ^ b * 5 ^ e) = a ∧ padicValNat 3 (2 ^ a * 3 ^ b * 5 ^ e) = b ∧
      padicValNat 5 (2 ^ a * 3 ^ b * 5 ^ e) = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : padicValNat 2 (3 ^ b) = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := (Nat.prime_two.dvd_of_dvd_pow hd); omega)
  have h2' : padicValNat 2 (5 ^ e) = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := (Nat.prime_two.dvd_of_dvd_pow hd); omega)
  have h3 : padicValNat 3 (2 ^ a) = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := (Nat.prime_three.dvd_of_dvd_pow hd); omega)
  have h3' : padicValNat 3 (5 ^ e) = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := (Nat.prime_three.dvd_of_dvd_pow hd); omega)
  have h5 : padicValNat 5 (2 ^ a) = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow hd); omega)
  have h5' : padicValNat 5 (3 ^ b) = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow hd); omega)
  have p2 : (2 : ℕ) ^ a ≠ 0 := by positivity
  have p3 : (3 : ℕ) ^ b ≠ 0 := by positivity
  have p5 : (5 : ℕ) ^ e ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [padicValNat.mul (by positivity) p5, padicValNat.mul p2 p3, padicValNat.prime_pow, h2, h2']
    simp
  · rw [padicValNat.mul (by positivity) p5, padicValNat.mul p2 p3, padicValNat.prime_pow, h3, h3']
    simp
  · rw [padicValNat.mul (by positivity) p5, padicValNat.mul p2 p3, padicValNat.prime_pow, h5, h5']
    simp

theorem card_pow_inj {c c' m m' : ℕ} (hc : c = 6 ∨ c = 12 ∨ c = 20 ∨ c = 72)
    (hc' : c' = 6 ∨ c' = 12 ∨ c' = 20 ∨ c' = 72) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : c ^ m = c' ^ m') : c = c' := by
  have key : ∀ a b e a' b' e' : ℕ, (2 ^ a * 3 ^ b * 5 ^ e) ^ m = (2 ^ a' * 3 ^ b' * 5 ^ e') ^ m' →
      a * m = a' * m' ∧ b * m = b' * m' ∧ e * m = e' * m' := by
    intro a b e a' b' e' hh
    simp only [mul_pow, ← pow_mul] at hh
    have h1 := padicValNat_235 (a * m) (b * m) (e * m)
    have h2 := padicValNat_235 (a' * m') (b' * m') (e' * m')
    rw [hh] at h1
    exact ⟨h1.1.symm.trans h2.1, h1.2.1.symm.trans h2.2.1, h1.2.2.symm.trans h2.2.2⟩
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso
       first
       | (have := key 1 1 0 2 1 0 (by simpa using h); omega)
       | (have := key 1 1 0 2 0 1 (by simpa using h); omega)
       | (have := key 1 1 0 3 2 0 (by simpa using h); omega)
       | (have := key 2 1 0 1 1 0 (by simpa using h); omega)
       | (have := key 2 1 0 2 0 1 (by simpa using h); omega)
       | (have := key 2 1 0 3 2 0 (by simpa using h); omega)
       | (have := key 2 0 1 1 1 0 (by simpa using h); omega)
       | (have := key 2 0 1 2 1 0 (by simpa using h); omega)
       | (have := key 2 0 1 3 2 0 (by simpa using h); omega)
       | (have := key 3 2 0 1 1 0 (by simpa using h); omega)
       | (have := key 3 2 0 2 1 0 (by simpa using h); omega)
       | (have := key 3 2 0 2 0 1 (by simpa using h); omega))

section Cards

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem card_fixed_cases
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    (Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)) ∧
        Nat.card (signalizerFixedSubgroup f) = 6) ∨
      (Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) ∧
        Nat.card (signalizerFixedSubgroup f) = 12) ∨
      (∃ n : ℕ, p = 2 * n + 1 ∧ Nonempty (X ≃* Sz n) ∧
        Nat.card (signalizerFixedSubgroup f) = 20) ∨
      (Nonempty (X ≃* PSU3 2 p) ∧ Nat.card (signalizerFixedSubgroup f) = 72) := by
  rcases h.model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    have hcop : Nat.Coprime p (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 p))) := by
      rw [← Nat.card_congr e.toEquiv]
      exact h.coprime
    refine ⟨⟨e⟩, ?_⟩
    rw [← ModelFacts.card_fixed_congr e f]
    exact PSL2Even.card_fixed h.prime hcop _ (by rw [orderOf_congr, hf])
  · right
    left
    exact ⟨⟨e⟩, (NearSimple.fixedNormalizer_eq_of_psl3 h hf ⟨e⟩).2.1⟩
  · right
    right
    left
    refine ⟨n, rfl, ⟨e⟩, ?_⟩
    have hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)) := by
      rw [← Nat.card_congr e.toEquiv]
      exact h.coprime
    rw [← ModelFacts.card_fixed_congr e f,
      SzModel.card_fixed h.prime hcop _ (by rw [orderOf_congr, hf])]
  · right
    right
    right
    have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
      rw [← Nat.card_congr e.toEquiv]
      exact h.coprime
    refine ⟨⟨e⟩, ?_⟩
    rw [← ModelFacts.card_fixed_congr e f,
      UnitaryFrame.card_fixedSubgroup h.prime hcop _ (by rw [orderOf_congr, hf])]

omit [Finite X] in
theorem nonempty_mulEquiv_of_card_pow_eq
    {X' : Type*} [Group X'] [Finite X'] (h : NearSimple p X)
    (h' : NearSimple p X') {f : MulAut X} {f' : MulAut X'} (hf : orderOf f = p)
    (hf' : orderOf f' = p) {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hcard : Nat.card (signalizerFixedSubgroup f) ^ m =
      Nat.card (signalizerFixedSubgroup f') ^ m') : Nonempty (X ≃* X') := by
  rcases card_fixed_cases h hf with ⟨⟨e⟩, hc⟩ | ⟨⟨e⟩, hc⟩ | ⟨n, hn, ⟨e⟩, hc⟩ | ⟨⟨e⟩, hc⟩ <;>
    rcases card_fixed_cases h' hf' with ⟨⟨e'⟩, hc'⟩ | ⟨⟨e'⟩, hc'⟩ | ⟨n', hn', ⟨e'⟩, hc'⟩ |
      ⟨⟨e'⟩, hc'⟩ <;>
    rw [hc, hc'] at hcard
  all_goals first
    | exact ⟨e.trans e'.symm⟩
    | (obtain rfl : n = n' := by omega
       exact ⟨e.trans e'.symm⟩)
    | (exfalso
       have := card_pow_inj (by simp) (by simp) hm hm' hcard
       omega)

end Cards

end Sec6S31

end CFSG.SignalizerFunctorTheorem.McBride.Near
