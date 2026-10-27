module

public import CFSG.Quasithin.Background.TorusComplementH1
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open scoped Matrix

section Generation

theorem exists_su4_torus {K : Type} [Field K] {σ : K ≃+* K} {l : K} (hl : σ l * l = 1) :
    ∃ t₀ t₁ : SUid σ 4, Commute t₀ t₁ ∧ orderOf t₀ ∣ orderOf l ∧ orderOf t₁ ∣ orderOf l ∧
      (∀ v : Fin 4 → K, t₀ • v = fun i => if i = 0 then (l ^ 3)⁻¹ * v i else l * v i) ∧
      (∀ v : Fin 4 → K, t₁ • v = fun i => if i = 1 then (l ^ 3)⁻¹ * v i else l * v i) := by
  classical
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have hm : σ (l ^ 3)⁻¹ * (l ^ 3)⁻¹ = 1 := by
    rw [map_inv₀, map_pow, ← mul_inv, ← mul_pow, hl, one_pow, inv_one]
  let d : Fin 4 → Fin 4 → K := fun j i => if i = j then (l ^ 3)⁻¹ else l
  have hd : ∀ j i, σ (d j i) * d j i = 1 := by
    intro j i
    simp only [d]
    split_ifs
    · exact hm
    · exact hl
  have hdet : ∀ j : Fin 4, (Matrix.diagonal (d j)).det = 1 := by
    intro j
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    fin_cases j <;> simp [d] <;> field_simp <;> ring
  have hiso : ∀ j : Fin 4, ∀ x y : Fin 4 → K,
      herm σ (Matrix.diagonal (d j) *ᵥ x) (Matrix.diagonal (d j) *ᵥ y) = herm σ x y := by
    intro j x y
    simp only [herm_def, Matrix.mulVec_diagonal, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc σ (d j i) * σ (x i) * (d j i * y i) = (σ (d j i) * d j i) * (σ (x i) * y i) := by ring
      _ = σ (x i) * y i := by rw [hd, one_mul]
  let t : Fin 4 → SUid σ 4 := fun j => mkSU σ (Matrix.diagonal (d j)) (hdet j) (hiso j)
  have ht : ∀ j v, t j • v = fun i => d j i * v i := by
    intro j v
    simp only [t, mkSU_smul]
    funext i
    rw [Matrix.mulVec_diagonal]
  have hpow : ∀ j (k : ℕ) (v : Fin 4 → K), (t j ^ k) • v = fun i => d j i ^ k * v i := by
    intro j k
    induction k with
    | zero => intro v; funext i; simp
    | succ k ih =>
      intro v
      funext i
      rw [pow_succ, mul_smul, ht, ih]
      ring
  have hord : ∀ j i, d j i ^ orderOf l = 1 := by
    intro j i
    simp only [d]
    split_ifs
    · rw [inv_pow, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, inv_one]
    · exact pow_orderOf_eq_one l
  have htord : ∀ j, orderOf (t j) ∣ orderOf l := by
    intro j
    apply orderOf_dvd_of_pow_eq_one
    apply ext_smul
    intro v
    rw [hpow, one_smul]
    funext i
    rw [hord, one_mul]
  refine ⟨t 0, t 1, ?_, htord 0, htord 1, fun v => ?_, fun v => ?_⟩
  · apply ext_smul
    intro v
    rw [mul_smul, mul_smul, ht, ht, ht, ht]
    funext i
    ring
  · rw [ht]
    funext i
    simp only [d]
    split_ifs <;> rfl
  · rw [ht]
    funext i
    simp only [d]
    split_ifs <;> rfl

theorem su4_commute_of_smul_single_eq_self {K : Type} [Field K] {σ : K ≃+* K} {j : Fin 4}
    {t : SUid σ 4} {l μ : K}
    (ht : ∀ v : Fin 4 → K, t • v = fun i => if i = j then μ * v i else l * v i)
    {g : SUid σ 4} (hg : g • (Pi.single j 1 : Fin 4 → K) = Pi.single j 1) : Commute g t := by
  have hherm : ∀ w : Fin 4 → K, herm σ (Pi.single j 1 : Fin 4 → K) w = w j := by
    intro w
    rw [herm_single_left, map_one, one_mul]
  have htv : ∀ w : Fin 4 → K,
      t • w = l • w + ((μ - l) * w j) • (Pi.single j 1 : Fin 4 → K) := by
    intro w
    rw [ht]
    funext i
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.single_eq_same]
      ring
    · rw [if_neg hij, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.single_eq_of_ne (i := j) (i' := i) hij, mul_zero, add_zero]
  have hgj : ∀ w : Fin 4 → K, (g • w) j = w j := by
    intro w
    rw [← hherm (g • w), ← hg, herm_smul_smul, hherm]
  have hsc : ∀ (c : K) (w : Fin 4 → K), g • (c • w) = c • (g • w) := fun c w => smul_comm g c w
  apply ext_smul
  intro v
  calc (g * t) • v
      = g • (t • v) := mul_smul _ _ _
    _ = g • (l • v + ((μ - l) * v j) • (Pi.single j 1 : Fin 4 → K)) := by rw [htv v]
    _ = l • (g • v) + ((μ - l) * v j) • (g • (Pi.single j 1 : Fin 4 → K)) := by
        simp only [smul_add, hsc]
    _ = l • (g • v) + ((μ - l) * (g • v) j) • (Pi.single j 1 : Fin 4 → K) := by
        rw [hg, ← hgj v]
    _ = t • (g • v) := (htv (g • v)).symm
    _ = (t * g) • v := (mul_smul _ _ _).symm

@[expose] def su4FixOneEmb {K : Type} [Field K] : (Fin 3 → K) →ₗ[K] (Fin 4 → K) where
  toFun u := ![u 0, 0, u 1, u 2]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c u := by
    funext i
    fin_cases i <;> simp

@[simp] theorem su4FixOneEmb_apply {K : Type} [Field K] (u : Fin 3 → K) :
    su4FixOneEmb u = ![u 0, 0, u 1, u 2] := rfl

theorem su4FixOneEmb_isometry {K : Type} [Field K] {σ : K ≃+* K} (u v : Fin 3 → K) :
    herm σ (su4FixOneEmb u) (su4FixOneEmb v) = herm σ u v := by
  simp [su4FixOneEmb_apply, herm, Fin.sum_univ_four, Fin.sum_univ_three]

theorem exists_su4_smul_fix_single_one {K : Type} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) (h3 : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) {a : Fin 4 → K}
    (ha0 : a 0 ≠ 0) (ha : herm σ a a = 0) :
    ∃ g : SUid σ 4, g • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) ∧ (g • a) 0 = 0 := by
  classical
  set u : Fin 3 → K := ![a 0, a 2, a 3] with hu
  have ha' : σ (a 0) * a 0 + σ (a 1) * a 1 + σ (a 2) * a 2 + σ (a 3) * a 3 = 0 := by
    simpa [herm, Fin.sum_univ_four] using ha
  have huu : herm σ u u = σ (a 0) * a 0 + σ (a 2) * a 2 + σ (a 3) * a 3 := by
    simp [herm, Fin.sum_univ_three, hu]
  have huval : herm σ u u = -(σ (a 1) * a 1) := by
    rw [huu]
    linear_combination ha'
  have hperp : ∀ x : Fin 3 → K,
      herm σ (su4FixOneEmb x) (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) = 0 := by
    intro x
    rw [herm_single_right]
    simp [su4FixOneEmb_apply]
  have key : ∃ g₃ ∈ T σ 3, (g₃ • u) 0 = 0 := by
    by_cases ha1 : a 1 = 0
    · have hu_iso : herm σ u u = 0 := by
        rw [huval, ha1, map_zero, zero_mul, neg_zero]
      have hu0 : u ≠ 0 := by
        intro h
        exact ha0 (by simpa [hu] using congrFun h 0)
      obtain ⟨s, hs⟩ := hσ.exists_norm_neg_one
      set w : Fin 3 → K := ![0, 1, s] with hw
      have hw_iso : herm σ w w = 0 := by
        simp only [hw, herm, Fin.sum_univ_three]
        simp [hs]
      have hw0 : w ≠ 0 := by
        intro h
        have h1 := congrFun h 1
        simp [hw] at h1
      obtain ⟨g₃, hg₃, hg₃s⟩ := exists_mem_T_smul_eq_of_iso hσ (le_refl 3) hu0 hu_iso hw0 hw_iso
      exact ⟨g₃, hg₃, by rw [hg₃s]; simp [hw]⟩
    · have hN : herm σ u u ≠ 0 := by
        rw [huval]
        exact neg_ne_zero.mpr (mul_ne_zero ((map_ne_zero σ).mpr ha1) ha1)
      have hNfix : σ (herm σ u u) = herm σ u u := herm_self_fixed σ hσ.invol u
      obtain ⟨c', hc'⟩ := hσ.exists_norm hNfix
      have hc'0 : c' ≠ 0 := by
        rintro rfl
        rw [map_zero, zero_mul] at hc'
        exact hN hc'.symm
      have hσc'0 : σ c' ≠ 0 := (map_ne_zero σ).mpr hc'0
      have hx1 : herm σ (c'⁻¹ • u) (c'⁻¹ • u) = 1 := by
        rw [herm_smul_left, herm_smul_right, map_inv₀, ← hc']
        field_simp
      have hx2 : herm σ (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K)
          (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) = 1 := by
        rw [herm_single_left, map_one, one_mul, Pi.single_eq_same]
      obtain ⟨g₃, hg₃, hg₃s⟩ :=
        exists_mem_T_smul_eq_of_norm_one hσ (Or.inr ⟨le_rfl, h3⟩) hx1 hx2
      refine ⟨g₃, hg₃, ?_⟩
      have hgu : g₃ • u = c' • (Pi.single (1 : Fin 3) (1 : K) : Fin 3 → K) := by
        have h := congrArg (fun z => c' • z) hg₃s
        rw [smul_comm g₃ c'⁻¹ u, smul_smul, mul_inv_cancel₀ hc'0, one_smul] at h
        exact h
      rw [hgu]
      simp
  obtain ⟨g₃, hg₃T, hg₃u⟩ := key
  obtain ⟨g, -, hgφ, hgfix⟩ := transport hσ.invol (su4FixOneEmb (K := K)) su4FixOneEmb_isometry hg₃T
  have hge1 : g • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := hgfix _ hperp
  refine ⟨g, hge1, ?_⟩
  have haeq : a = su4FixOneEmb u + a 1 • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := by
    funext i
    fin_cases i <;> simp [su4FixOneEmb_apply, hu]
  have hga : g • a = su4FixOneEmb (g₃ • u) + a 1 • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := by
    conv_lhs => rw [haeq]
    rw [smul_add, smul_comm g (a 1) (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K), hgφ, hge1]
  rw [hga, Pi.add_apply, Pi.smul_apply, su4FixOneEmb_apply, Matrix.cons_val_zero, hg₃u, zero_add,
    Pi.single_eq_of_ne (i := 1) (i' := 0) (by decide), smul_zero]

theorem le_closure_commute_su4 {K : Type} [Field K] {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (h3 : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) {t₀ t₁ : SUid σ 4} {l μ : K}
    (ht₀ : ∀ v : Fin 4 → K, t₀ • v = fun i => if i = 0 then μ * v i else l * v i)
    (ht₁ : ∀ v : Fin 4 → K, t₁ • v = fun i => if i = 1 then μ * v i else l * v i) :
    (⊤ : Subgroup (SUid σ 4)) ≤ Subgroup.closure {g | Commute g t₀ ∨ Commute g t₁} := by
  classical
  have hfix0 : ∀ g : SUid σ 4, g • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) → Commute g t₀ :=
    fun g hg => su4_commute_of_smul_single_eq_self (j := 0) ht₀ hg
  have hfix1 : ∀ g : SUid σ 4, g • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
      (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) → Commute g t₁ :=
    fun g hg => su4_commute_of_smul_single_eq_self (j := 1) ht₁ hg
  rw [← T_four_eq_top hσ]
  refine (Subgroup.closure_le (Subgroup.closure {g | Commute g t₀ ∨ Commute g t₁})).mpr ?_
  rintro x ⟨a, c, ha, hc, hx⟩
  by_cases ha0 : a 0 = 0
  · have hxe0 : x • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
        (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
      rw [hx, herm_single_right, ha0, map_zero, zero_mul, mul_zero, zero_smul, add_zero]
    exact Subgroup.subset_closure (Or.inl (hfix0 x hxe0))
  · obtain ⟨g, hge1, hga0⟩ := exists_su4_smul_fix_single_one hσ h3 ha0 ha
    have hgi1 : g⁻¹ • (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) =
        (Pi.single (1 : Fin 4) (1 : K) : Fin 4 → K) := by
      conv_lhs => rw [← hge1]
      rw [inv_smul_smul]
    have hg1 : Commute g t₁ := hfix1 g hge1
    have hgi : Commute g⁻¹ t₁ := hfix1 g⁻¹ hgi1
    have hy0 : (g * x * g⁻¹) • (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) =
        (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) := by
      rw [conj_smul_of_tv g x hx, herm_single_right, hga0, map_zero, zero_mul, mul_zero,
        zero_smul, add_zero]
    have hy : Commute (g * x * g⁻¹) t₀ := hfix0 (g * x * g⁻¹) hy0
    have h1 : g ∈ Subgroup.closure {g | Commute g t₀ ∨ Commute g t₁} :=
      Subgroup.subset_closure (Or.inr hg1)
    have h2 : g⁻¹ ∈ Subgroup.closure {g | Commute g t₀ ∨ Commute g t₁} :=
      Subgroup.subset_closure (Or.inr hgi)
    have h3 : g * x * g⁻¹ ∈ Subgroup.closure {g | Commute g t₀ ∨ Commute g t₁} :=
      Subgroup.subset_closure (Or.inl hy)
    have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h3) h1

end Generation

theorem hasFpfTorusGen_statedSU {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) : HasFpfTorusGen (StatedSU 4 (2 ^ n) K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 4]
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hq4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmul : (2 ^ n - 1) * (2 ^ n + 1) = (2 ^ n) ^ 2 - 1 := by
    zify [hq1, Nat.one_le_pow 2 (2 ^ n) (by omega)]
    ring
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      CFSG.ClassicalGroups.Unitary.card_units_of_card hK]
  have hlord : orderOf ((g ^ (2 ^ n - 1) : Kˣ) : K) = 2 ^ n + 1 := by
    rw [orderOf_units, orderOf_pow_of_dvd (by omega) ⟨2 ^ n + 1, by rw [hord, hmul]⟩, hord,
      ← hmul, Nat.mul_div_cancel_left _ (by omega)]
  generalize ((g ^ (2 ^ n - 1) : Kˣ) : K) = l at hlord
  have hlnorm : CFSG.LieType.BorelTits.unitaryInvolution K 2 n l * l = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ, ← hlord]
    exact pow_orderOf_eq_one l
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hlord
    omega
  have hl3 : (l ^ 3)⁻¹ ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one (inv_eq_one.mp h)
    rw [hlord] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    omega
  have h3 : ∃ s : K, s ≠ 0 ∧ CFSG.LieType.BorelTits.unitaryInvolution K 2 n s * s ≠ 1 := by
    refine ⟨g, g.ne_zero, fun h => ?_⟩
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ,
      ← Units.val_pow_eq_pow_val] at h
    have h1 : g ^ (2 ^ n + 1) = 1 := Units.ext (by rw [h, Units.val_one])
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord, ← hmul] at h2
    have h4 := Nat.le_of_dvd (by omega) h2
    have h5 : (2 ^ n - 1) * (2 ^ n + 1) ≤ 1 * (2 ^ n + 1) := by rwa [one_mul]
    have h6 := Nat.le_of_mul_le_mul_right h5 (by omega)
    omega
  have hoddl : Odd (orderOf l) := by
    rw [hlord]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  obtain ⟨t₀, t₁, hcomm, ho₀, ho₁, ht₀, ht₁⟩ := exists_su4_torus hlnorm
  have hfix : ∀ (j : Fin 4) (t : SUid (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4),
      (∀ v : Fin 4 → K, t • v = fun i => if i = j then (l ^ 3)⁻¹ * v i else l * v i) →
        ∀ v : Fin 4 → K, ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v → v = 0 := by
    intro j t ht v hv
    rw [← smul_def, ht] at hv
    funext i
    have hvi := congrFun hv i
    split_ifs at hvi
    · have h0 : ((l ^ 3)⁻¹ - 1) * v i = 0 := by linear_combination hvi
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hl3)
    · have h0 : (l - 1) * v i = 0 := by linear_combination hvi
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hl1)
  refine ⟨{t₀, t₁}, ⟨t₀, Set.mem_insert _ _⟩, ?_, ?_, ?_, ?_⟩
  · rintro γ (rfl | rfl)
    · exact hoddl.of_dvd_nat ho₀
    · exact hoddl.of_dvd_nat ho₁
  · rintro γ (rfl | rfl)
    · exact hfix 0 _ ht₀
    · exact hfix 1 _ ht₁
  · rintro γ (rfl | rfl) γ' (rfl | rfl)
    · exact Commute.refl _
    · exact hcomm
    · exact hcomm.symm
    · exact Commute.refl _
  · refine (le_closure_commute_su4 hσ h3 ht₀ ht₁).trans (Subgroup.closure_mono ?_)
    rintro x (hx | hx)
    · exact ⟨t₀, Set.mem_insert _ _, hx⟩
    · exact ⟨t₁, Set.mem_insert_of_mem _ rfl, hx⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
