module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpLabel
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpFourier
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCube
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisOrbit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQTrivType

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.Quasithin.SmithCurtis

private theorem spST_finrank_range_conj {K : Type} [Field K] {n : ℕ} {k : Type} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k (StatedSp n K) V) (g y : StatedSp n K) :
    Module.finrank k (LinearMap.range (ρ (g * y * g⁻¹) - 1)) =
      Module.finrank k (LinearMap.range (ρ y - 1)) := by
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

private theorem spST_spLabelVec_zero {n : ℕ} {a : Fin n → ℕ}
    (hzero : ∀ i, 0 < i.val → a i = 0) (j : Fin n) (hj : j.val = 0) :
    spLabelVec a j = a j := by
  unfold spLabelVec
  rw [Finset.filter_true_of_mem (fun i _ => by simp only [Fin.le_def]; omega)]
  rw [Finset.sum_eq_single j]
  · intro b _ hb
    rw [hzero b (by by_contra h; exact hb (Fin.ext (by omega)))]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem spST_spLabelVec_of_pos {n : ℕ} {a : Fin n → ℕ}
    (hzero : ∀ i, 0 < i.val → a i = 0) (j : Fin n) (hj : 0 < j.val) :
    spLabelVec a j = 0 := by
  unfold spLabelVec
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [hzero i (by have := hi.2; simp only [Fin.le_def] at this; omega)]
  simp

private theorem spST_spLabelVec_eq_zero {n : ℕ} {a : Fin n → ℕ} (hall : ∀ i, a i = 0) :
    spLabelVec a = 0 := by
  funext j
  unfold spLabelVec
  apply Finset.sum_eq_zero
  intro i _
  rw [hall i]
  simp

private theorem spST_chi_diagHom_zero {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 0 < n) {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V]
    [Module k V] {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k}
    {μ : Fin n → k} (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (hzero : ∀ i, 0 < i.val → a i = 0) {c : ℕ} (hc : a ⟨0, hn⟩ = c) :
    ∀ t : Fin n → Kˣ, χ (diagHom n K t) = algebraMap K k (t ⟨0, hn⟩ : K) ^ c := by
  intro t
  rw [chi_diagHom_eq_spTorusChar ht ha t, spTorusChar_apply]
  have hb0 : spLabelVec a ⟨0, hn⟩ = (c : ℤ) := by
    rw [spST_spLabelVec_zero hzero ⟨0, hn⟩ rfl, hc]
  refine (Finset.prod_eq_single_of_mem (⟨0, hn⟩ : Fin n) (Finset.mem_univ _) ?_).trans ?_
  · intro b _ hb
    have hbpos : 0 < b.val := by
      by_contra h
      exact hb (Fin.ext (by simpa using h))
    rw [spST_spLabelVec_of_pos hzero b hbpos]
    simp
  · rw [hb0, zpow_natCast]

private theorem spST_chi_one_of_all_zero {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (hall : ∀ i, a i = 0) : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1 := by
  intro h hh
  obtain ⟨t, rfl⟩ := spCurtisDatum_H_le hh
  rw [chi_diagHom_eq_spTorusChar ht ha t, spTorusChar_apply, spST_spLabelVec_eq_zero hall]
  simp

private theorem spST_chi_one_cube {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp 3 K) V} {y₀ : V} {χ : StatedSp 3 K → k} {μ : Fin 3 → k}
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {a : Fin 3 → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) (ha2 : a 2 = Nat.card K - 1) :
    ∀ h ∈ (spCurtisDatum 3 K).H, χ h = 1 := by
  have : Fintype K := Fintype.ofFinite K
  intro h hh
  obtain ⟨t, rfl⟩ := spCurtisDatum_H_le hh
  rw [chi_diagHom_eq_spTorusChar ht ha t, spTorusChar_apply]
  have hb : ∀ j : Fin 3, spLabelVec a j = ((Nat.card K - 1 : ℕ) : ℤ) := by
    intro j
    fin_cases j
    all_goals
      rw [spLabelVec, Finset.sum_filter, Fin.sum_univ_three]
      simp [ha0, ha1, ha2, Fin.le_def]
  rw [Finset.prod_congr rfl (fun j _ => by rw [hb j])]
  apply Finset.prod_eq_one
  intro j _
  rw [zpow_natCast, ← map_pow]
  rw [show (t j : K) ^ (Nat.card K - 1) = 1 from by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (t j).ne_zero]
  rw [map_one]

open CFSG.LieType.RootSystem in
private theorem spST_orbit_rank {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha0 : ∀ i, 0 < a i ↔ μ i = (spCurtisDatum n K).dScalar χ i)
    {m : ℕ} {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {g y : StatedSp n K}
    (hxw : (spCurtisDatum n K).nW x = g * y * g⁻¹) (u : Fin m → Fin n → ℤ)
    (hu : ∀ i, ∃ w, u i = weylAction (isFiniteType_cartanC n) w (spFromStd2 n (spLabelVec a)))
    (hinj : Function.Injective u)
    (hmove : ∀ i j, u i ≠ weylAction (isFiniteType_cartanC n) x (u j)) :
    m ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  let D : CurtisDatum (StatedSp n K) (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem 2 :=
    spCurtisDatum n K
  let cs := (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem
  let : MulAction (coxeterMatrix (isFiniteType_cartanC n)).Group (Fin n → ℤ) :=
    MulAction.compHom (Fin n → ℤ) (weylAction (isFiniteType_cartanC n))
  have hv : ∀ t : Fin n, μ t ≠ (spCurtisDatum n K).dScalar χ t →
      cs.simple t • spFromStd2 n (spLabelVec a) = spFromStd2 n (spLabelVec a) := by
    intro t htne
    have hat : a t = 0 := by
      by_contra hne
      exact htne ((ha0 t).mp (Nat.pos_of_ne_zero hne))
    simpa [cs, MulAction.compHom_smul_def, Module.End.smul_def]
      using weylAction_simple_spLabelVec (n := n) a hat
  have hu' : ∀ i, u i ∈ MulAction.orbit (coxeterMatrix (isFiniteType_cartanC n)).Group
      (spFromStd2 n (spLabelVec a)) := by
    intro i
    obtain ⟨w, hw⟩ := hu i
    exact MulAction.mem_orbit_iff.mpr ⟨w, by
      simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hw.symm⟩
  have hmove' : ∀ i j, u i ≠ x • u j := by
    intro i j
    simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hmove i j
  have horbit := le_finrank_range_sub_one_of_mem_orbit (D := D) hρ ht hv
    x u hu' hinj hmove'
  rw [hxw, spST_finrank_range_conj ρ g y] at horbit
  exact horbit

private theorem spST_four_orbit {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {k : Type} [Field k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha0 : ∀ i, 0 < a i ↔ μ i = (spCurtisDatum n K).dScalar χ i)
    {y : StatedSp n K} (hy : y * y = 1) (hy1 : y ≠ 1)
    (hP : ∃ i : Fin n, 1 ≤ i.val ∧ 0 < a i)
    (hcube : n = 3 → a ⟨0, by omega⟩ ≠ 0 ∨ a ⟨1, by omega⟩ ≠ 0) :
    4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  obtain ⟨g, π, s, hσ, hx, hg⟩ := exists_conj_mat_eq_spMonoPerm (n := n) (by omega) hy hy1
  obtain ⟨x, hxr, hxw⟩ := exists_nW_eq_of_mat_eq hσ hg
  obtain ⟨u, hu, hinj, hmove⟩ := exists_four_orbit_spLabelVec hn hP hcube hxr hx
  exact spST_orbit_rank hρ ht ha0 hxw u hu hinj hmove

private theorem spST_two_orbit {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {k : Type} [Field k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha0 : ∀ i, 0 < a i ↔ μ i = (spCurtisDatum n K).dScalar χ i)
    {y : StatedSp n K} (hy : y * y = 1) (hy1 : y ≠ 1)
    (h2 : ∃ i : Fin n, 2 ≤ i.val ∧ 0 < a i) :
    2 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  obtain ⟨g, π, s, hσ, hx, hg⟩ := exists_conj_mat_eq_spMonoPerm (n := n) (by omega) hy hy1
  obtain ⟨x, hxr, hxw⟩ := exists_nW_eq_of_mat_eq hσ hg
  obtain ⟨u, hu, hinj, hmove⟩ := exists_two_orbit_spLabelVec hn h2 hxr hx
  exact spST_orbit_rank hρ ht ha0 hxw u hu hinj hmove

private theorem spST_pow_two_add_one_lt {c i f : ℕ} (hi : c = 2 ^ i) (hlt : c < 2 ^ f)
    (hf : f = 2 ∨ f = 3) : c + 1 < 2 ^ f := by
  subst hi
  have hif : i < f := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  rcases hf with rfl | rfl <;> interval_cases i <;> norm_num

private theorem spST_natural {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (hμ0 : ∀ i, a i + 1 < Nat.card K → μ i = 0)
    (hzero : ∀ i, 0 < i.val → a i = 0) {c i : ℕ}
    (hc : a ⟨0, hn⟩ = c) (hci : c = 2 ^ i) (hcq : c + 1 < Nat.card K) :
    μ = 0 ∧ ∃ φ : K →+* k, ∀ t : Fin n → Kˣ, χ (diagHom n K t) = φ (t ⟨0, hn⟩) := by
  have h1q : 1 < Nat.card K := by omega
  refine ⟨?_, ?_⟩
  · funext j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj
      exact hμ0 _ (by rw [hc]; exact hcq)
    · have hpos : 0 < j.val := by
        rcases Nat.eq_zero_or_pos j.val with h | h
        · exact absurd (Fin.ext (by simpa using h)) hj
        · exact h
      exact hμ0 j (by rw [hzero j hpos]; exact h1q)
  · refine ⟨(iterateFrobenius k 2 i).comp (algebraMap K k), fun t => ?_⟩
    rw [chi_diagHom_eq_spTorusChar ht ha t, spTorusChar_apply]
    have hb0 : spLabelVec a ⟨0, hn⟩ = (c : ℤ) := by
      rw [spST_spLabelVec_zero hzero ⟨0, hn⟩ rfl, hc]
    have hprod : (Finset.univ.prod fun j : Fin n =>
        algebraMap K k (t j : K) ^ spLabelVec a j) =
        algebraMap K k (t ⟨0, hn⟩ : K) ^ c := by
      refine (Finset.prod_eq_single_of_mem (⟨0, hn⟩ : Fin n) (Finset.mem_univ _) ?_).trans ?_
      · intro b _ hb
        have hbpos : 0 < b.val := by
          by_contra h
          exact hb (Fin.ext (by simpa using h))
        rw [spST_spLabelVec_of_pos hzero b hbpos]
        simp
      · rw [hb0, zpow_natCast]
    rw [hprod, RingHom.comp_apply, iterateFrobenius_def, hci]

private theorem spST_exists_odd_choose {q c : ℕ} (hq : q = 4 ∨ q = 8) (hpos : 0 < c)
    (hlt : c < q) (hpow : ¬ ∃ i, c = 2 ^ i) :
    ∃ j, 0 < j ∧ j < c ∧ Odd (c.choose j) := by
  rcases hq with rfl | rfl
  · interval_cases c
    · exact absurd ⟨0, rfl⟩ hpow
    · exact absurd ⟨1, by norm_num⟩ hpow
    · exact ⟨1, by norm_num, by norm_num, by decide +kernel⟩
  · interval_cases c
    · exact absurd ⟨0, rfl⟩ hpow
    · exact absurd ⟨1, by norm_num⟩ hpow
    · exact ⟨1, by norm_num, by norm_num, by decide +kernel⟩
    · exact absurd ⟨2, by norm_num⟩ hpow
    · exact ⟨1, by norm_num, by norm_num, by decide +kernel⟩
    · exact ⟨2, by norm_num, by norm_num, by decide +kernel⟩
    · exact ⟨1, by norm_num, by norm_num, by decide +kernel⟩

private theorem spST_coprime_of_lt {q c : ℕ} (hq : q = 4 ∨ q = 8) (hpos : 0 < c)
    (hlt : c < q - 1) : c.Coprime (q - 1) := by
  rcases hq with rfl | rfl
  · interval_cases c <;> decide +kernel
  · interval_cases c <;> decide +kernel

private theorem spST_trivial {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1)
    {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (hμ0 : ∀ i, a i + 1 < Nat.card K → μ i = 0)
    (hzero : ∀ i, 0 < i.val → a i = 0) (h0z : a ⟨0, hn⟩ = 0)
    (hK4 : 4 ≤ Nat.card K) : False := by
  have hall : ∀ i, a i = 0 := by
    intro i
    rcases Nat.eq_zero_or_pos i.val with h | h
    · have hi : i = ⟨0, hn⟩ := Fin.ext h
      rw [hi, h0z]
    · exact hzero i h
  have hμ : μ = 0 := by
    funext i
    exact hμ0 i (by have := hK4; have := hall i; omega)
  have hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1 := spST_chi_one_of_all_zero ht ha hall
  rw [hμ] at ht
  obtain ⟨g, hg⟩ := hρ1
  exact hg (omq_rep_eq_one_of_isCurtisType_zero (spCurtisDatum n K) hρ ht hχ g)

private theorem spST_cube {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {ρ : Representation k (StatedSp 3 K) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp 3 K → k} {μ : Fin 3 → k}
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {a : Fin 3 → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (ha_lt : ∀ i : Fin 3, a i < Nat.card K)
    (ha0 : ∀ i, 0 < a i ↔ μ i = (spCurtisDatum 3 K).dScalar χ i)
    (ha0z : a 0 = 0) (ha1z : a 1 = 0) (ha2pos : 0 < a 2)
    (hK4 : 4 ≤ Nat.card K) (hq : Nat.card K = 4 ∨ Nat.card K = 8)
    {y : StatedSp 3 K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    (((∃ (i : Fin 3) (c : ℕ), c.Coprime (Nat.card K - 1) ∧
        ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ c) ∧
        2 ≤ Module.finrank k (LinearMap.range (ρ y - 1))) ∨
      4 ≤ Module.finrank k (LinearMap.range (ρ y - 1))) := by
  by_cases hlt : a 2 + 1 < Nat.card K
  · left
    refine ⟨⟨2, a 2, spST_coprime_of_lt hq ha2pos (by omega), ha 2⟩, ?_⟩
    exact spST_two_orbit (n := 3) (by omega) hρ ht ha0 hy hy1 ⟨2, le_rfl, ha2pos⟩
  · right
    have ha2 : a 2 = Nat.card K - 1 := by have := ha_lt 2; omega
    exact four_le_finrank_of_chi_trivial (n := 3) (by omega) hK4 (algebraMap K k) hρ ht
      (spST_chi_one_cube ht ha ha0z ha1z ha2) ((ha0 2).mp ha2pos) hy hy1

private theorem spST_case_cube {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {ρ : Representation k (StatedSp 3 K) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp 3 K → k} {μ : Fin 3 → k}
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {a : Fin 3 → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (ha_lt : ∀ i : Fin 3, a i < Nat.card K)
    (ha0 : ∀ i, 0 < a i ↔ μ i = (spCurtisDatum 3 K).dScalar χ i)
    (ha0z : a 0 = 0) (ha1z : a 1 = 0) (hP : ∃ i : Fin 3, 1 ≤ i.val ∧ 0 < a i)
    (hK4 : 4 ≤ Nat.card K) (hq : Nat.card K = 4 ∨ Nat.card K = 8)
    {y : StatedSp 3 K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    ((∃ (i : Fin 3) (c : ℕ), c.Coprime (Nat.card K - 1) ∧
        ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ c) ∧
        2 ≤ Module.finrank k (LinearMap.range (ρ y - 1))) ∨
      4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  obtain ⟨i, hi1, hipos⟩ := hP
  have ha2pos : 0 < a 2 := by
    have hi : i = 2 := by
      have hilt := i.isLt
      rcases Nat.eq_or_lt_of_le hi1 with h | h
      · exfalso
        have hi1' : i = 1 := Fin.ext h.symm
        subst hi1'
        exact Nat.lt_irrefl 0 (ha1z ▸ hipos)
      · exact Fin.ext (by omega)
    rwa [hi] at hipos
  exact spST_cube hρ ht ha ha_lt ha0 ha0z ha1z ha2pos hK4 hq hy hy1

private theorem spST_case_natural {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}
    (hn : 3 ≤ n) (hf : f = 2 ∨ f = 3) (hK : Nat.card K = 2 ^ f) {k : Type} [Field k]
    [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i)
    (ha_lt : ∀ i, a i < Nat.card K)
    (ha0 : ∀ i, 0 < a i ↔ μ i = (spCurtisDatum n K).dScalar χ i)
    (hμ0 : ∀ i, a i + 1 < Nat.card K → μ i = 0)
    (hzero : ∀ i, 0 < i.val → a i = 0) (h0z : a ⟨0, by omega⟩ ≠ 0)
    (hq : Nat.card K = 4 ∨ Nat.card K = 8) {y : StatedSp n K} (hy : y * y = 1)
    (hy1 : y ≠ 1) :
    (μ = 0 ∧ ∃ φ : K →+* k, ∀ t : Fin n → Kˣ, χ (diagHom n K t) = φ (t ⟨0, by omega⟩)) ∨
      ((∃ (i : Fin n) (c : ℕ), c.Coprime (Nat.card K - 1) ∧
          ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ c) ∧
        2 ≤ Module.finrank k (LinearMap.range (ρ y - 1))) ∨
      4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  have hcpos : 0 < a ⟨0, by omega⟩ := Nat.pos_of_ne_zero h0z
  by_cases hpow : ∃ i, a ⟨0, by omega⟩ = 2 ^ i
  · obtain ⟨i, hi⟩ := hpow
    refine Or.inl (spST_natural (n := n) (by omega) ht ha hμ0 hzero rfl hi ?_)
    have hres := spST_pow_two_add_one_lt (c := a ⟨0, by omega⟩) hi (hK ▸ ha_lt _) hf
    rwa [← hK] at hres
  · obtain ⟨j, hj, hjc, hodd⟩ := spST_exists_odd_choose hq hcpos (ha_lt _) hpow
    exact Or.inr (Or.inr (four_le_finrank_of_odd_choose hn (algebraMap K k) hρ ht
      ((ha0 _).mp hcpos) (ha_lt _) hj hjc hodd
      (spST_chi_diagHom_zero (n := n) (by omega) ht ha hzero rfl) hy hy1))

private theorem spST_dichotomy {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}
    (hn : 3 ≤ n) (hf : f = 2 ∨ f = 3) (hK : Nat.card K = 2 ^ f) {k : Type} [Field k]
    [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1)
    {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {y : StatedSp n K} (hy : y * y = 1)
    (hy1 : y ≠ 1) {a : Fin n → ℕ} (ha_lt : ∀ i, a i < Nat.card K)
    (ha0 : ∀ i, 0 < a i ↔ μ i = (spCurtisDatum n K).dScalar χ i)
    (hμ0 : ∀ i, a i + 1 < Nat.card K → μ i = 0)
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i) :
    (μ = 0 ∧ ∃ φ : K →+* k, ∀ t : Fin n → Kˣ, χ (diagHom n K t) = φ (t ⟨0, by omega⟩)) ∨
      ((∃ (i : Fin n) (c : ℕ), c.Coprime (Nat.card K - 1) ∧
          ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ c) ∧
        2 ≤ Module.finrank k (LinearMap.range (ρ y - 1))) ∨
      4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  have hq : Nat.card K = 4 ∨ Nat.card K = 8 := by
    rcases hf with rfl | rfl <;> rw [hK] <;> norm_num
  have hK4 : 4 ≤ Nat.card K := by rcases hq with h | h <;> omega
  by_cases hP : ∃ i : Fin n, 1 ≤ i.val ∧ 0 < a i
  · by_cases hcube : n = 3 → a ⟨0, by omega⟩ ≠ 0 ∨ a ⟨1, by omega⟩ ≠ 0
    · exact Or.inr (Or.inr (spST_four_orbit hn hρ ht ha0 hy hy1 hP hcube))
    · push Not at hcube
      obtain ⟨hn3, ha0z, ha1z⟩ := hcube
      subst hn3
      exact Or.inr (spST_case_cube hρ ht ha ha_lt ha0 ha0z ha1z hP hK4 hq hy hy1)
  · have hzero : ∀ i, 0 < i.val → a i = 0 := by
      intro i hi
      by_contra hne
      exact hP ⟨i, by omega, Nat.pos_of_ne_zero hne⟩
    by_cases h0z : a ⟨0, by omega⟩ = 0
    · exact (spST_trivial (n := n) (by omega) hρ hρ1 ht ha hμ0 hzero h0z hK4).elim
    · exact spST_case_natural hn hf hK hρ ht ha ha_lt ha0 hμ0 hzero h0z hq hy hy1

theorem sp_small_type {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ} (hn : 3 ≤ n)
    (hf : f = 2 ∨ f = 3) (hK : Nat.card K = 2 ^ f) {k : Type} [Field k] [CharP k 2]
    [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1)
    {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {y : StatedSp n K} (hy : y * y = 1)
    (hy1 : y ≠ 1) :
    (μ = 0 ∧ ∃ φ : K →+* k, ∀ t : Fin n → Kˣ, χ (diagHom n K t) = φ (t ⟨0, by omega⟩ : K)) ∨
      ((∃ (i : Fin n) (c : ℕ), c.Coprime (Nat.card K - 1) ∧
          ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ c) ∧
        2 ≤ Module.finrank k (LinearMap.range (ρ y - 1))) ∨
      4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  obtain ⟨a, ha_lt, ha0, hμ0, ha⟩ := exists_spLabel ht
  exact spST_dichotomy hn hf hK hρ hρ1 ht hy hy1 ha_lt ha0 hμ0 ha

end CFSG.LocalAnalysis.WeakClosure81
