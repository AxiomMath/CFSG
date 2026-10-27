module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSU
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpAniso
import CFSG.LieType.SeitzGeneration.OuterLinearWide

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration

namespace USeitz

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def UCentre (H : Subgroup (SUid σ n)) (a : Fin n → K) : Prop :=
  ∀ (g : SUid σ n) (c : K), c + σ c = 0 → (∀ v, g • v = v + (c * herm σ a v) • a) → g ∈ H

theorem uCentre_zero (H : Subgroup (SUid σ n)) : UCentre H (0 : Fin n → K) := by
  intro g c _ hg
  have : g = 1 := ext_smul σ fun v => by rw [hg, smul_zero, add_zero, one_smul]
  rw [this]
  exact H.one_mem

theorem uCentre_of_smul {H : Subgroup (SUid σ n)} {g : SUid σ n} (hg : g ∈ H) {a : Fin n → K}
    (ha : UCentre H (g • a)) : UCentre H a := by
  intro t c hc ht
  have h1 : g * t * g⁻¹ ∈ H := by
    refine ha _ c hc fun v => ?_
    have e : herm σ a (g⁻¹ • v) = herm σ (g • a) v := by
      rw [← herm_smul_smul σ g, smul_inv_smul]
    rw [mul_smul, mul_smul, ht, smul_add, smul_inv_smul, smul_comm, e]
  have h2 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
  rw [h2]
  exact H.mul_mem (H.mul_mem (H.inv_mem hg) h1) hg

theorem T_le_of_uCentre {H : Subgroup (SUid σ n)}
    (h : ∀ a : Fin n → K, herm σ a a = 0 → UCentre H a) : T σ n ≤ H := by
  rw [T, Subgroup.closure_le]
  rintro g ⟨a, c, ha, hc, hg⟩
  exact h a ha g c hc hg

theorem transport_le (hσ : ∀ c, σ (σ c) = c) {m : ℕ} {H : Subgroup (SUid σ n)}
    (φ : (Fin m → K) →ₗ[K] (Fin n → K)) (hφ : ∀ u v, herm σ (φ u) (φ v) = herm σ u v)
    (hH : ∀ u, herm σ u u = 0 → UCentre H (φ u)) {g : SUid σ m} (hg : g ∈ T σ m) :
    ∃ g' ∈ H, (∀ u, g' • φ u = φ (g • u)) ∧
      ∀ v, (∀ u, herm σ (φ u) v = 0) → g' • v = v := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, c, ha, hc, h⟩ := hg
    have ha' : herm σ (φ a) (φ a) = 0 := by rw [hφ, ha]
    refine ⟨tv hσ ha' hc, hH a ha _ c hc (tv_smul hσ ha' hc), fun u => ?_, fun v hv => ?_⟩
    · rw [tv_smul, h, map_add, map_smul, hφ]
    · rw [tv_smul, hv, mul_zero, zero_smul, add_zero]
  | one => exact ⟨1, H.one_mem, fun u => by simp, fun v _ => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨g', hg', h1, h2⟩ := ihg
    obtain ⟨h', hh', h3, h4⟩ := ihh
    refine ⟨g' * h', H.mul_mem hg' hh', fun u => ?_, fun v hv => ?_⟩
    · rw [mul_smul, h3, h1, mul_smul]
    · rw [mul_smul, h4 v hv, h2 v hv]
  | inv g _ ihg =>
    obtain ⟨g', hg', h1, h2⟩ := ihg
    refine ⟨g'⁻¹, H.inv_mem hg', fun u => ?_, fun v hv => ?_⟩
    · rw [inv_smul_eq_iff, h1, smul_inv_smul]
    · rw [inv_smul_eq_iff, h2 v hv]

theorem exists_mem_of_orthonormal (hσ : IsUnitaryInvolution σ) {H : Subgroup (SUid σ n)}
    {x z : Fin n → K} (hx : herm σ x x = 1) (hz : herm σ z z = 1) (hxz : herm σ x z = 0)
    (hH : ∀ α β : K, σ α * α + σ β * β = 0 → UCentre H (α • x + β • z)) (α β : K)
    (hN : σ α * α + σ β * β = 1) :
    ∃ t ∈ H, t • x = α • x + β • z ∧ ∀ v, herm σ x v = 0 → herm σ z v = 0 → t • v = v := by
  have hzx : herm σ z x = 0 := herm_eq_zero_comm σ hσ.invol hxz
  have hφ : ∀ c d : Fin 2 → K, herm σ (pairL x z c) (pairL x z d) = herm σ c d := by
    intro c d
    simp only [pairL, LinearMap.coe_mk, AddHom.coe_mk, herm_add_left, herm_add_right,
      herm_smul_left, herm_smul_right, hx, hz, hxz, hzx, herm_fin_two]
    ring
  have hA : su2 hσ.invol hN ∈ T σ 2 := by
    rw [T_two_eq_top hσ]
    exact Subgroup.mem_top _
  have hHφ : ∀ u : Fin 2 → K, herm σ u u = 0 → UCentre H (pairL x z u) := by
    intro u hu
    refine hH (u 0) (u 1) ?_
    rw [herm_fin_two] at hu
    exact hu
  obtain ⟨g, hg, hgφ, hfix⟩ := transport_le hσ.invol (pairL x z) hφ hHφ hA
  refine ⟨g, hg, ?_, fun v hxv hzv => hfix v fun u => ?_⟩
  · have hx' : pairL x z (Pi.single 0 1) = x := by simp [pairL]
    rw [← hx', hgφ, su2_smul_single]
    simp [pairL]
  · simp [pairL, hxv, hzv]

section Family

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def lc (e : ι → Fin n → K) (f : ι → K) : Fin n → K := ∑ i, f i • e i

omit [DecidableEq ι] in
theorem lc_add (e : ι → Fin n → K) (f g : ι → K) : lc e (f + g) = lc e f + lc e g := by
  simp only [lc, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem lc_single (e : ι → Fin n → K) (i : ι) (c : K) : lc e (Pi.single i c) = c • e i := by
  rw [lc, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (by simp), Pi.single_eq_same]

omit [Fintype ι] in
theorem herm_sum_left {s : Finset ι} (v : ι → Fin n → K) (y : Fin n → K) :
    herm σ (∑ i ∈ s, v i) y = ∑ i ∈ s, herm σ (v i) y := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_left, ih]

omit [Fintype ι] in
theorem herm_sum_right {s : Finset ι} (x : Fin n → K) (v : ι → Fin n → K) :
    herm σ x (∑ i ∈ s, v i) = ∑ i ∈ s, herm σ x (v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right, ih]

variable {e : ι → Fin n → K}

theorem herm_lc_right (he : ∀ i j, herm σ (e i) (e j) = if i = j then 1 else 0) (i : ι)
    (f : ι → K) : herm σ (e i) (lc e f) = f i := by
  rw [lc, herm_sum_right, Finset.sum_eq_single i (fun j _ hj => by
    rw [herm_smul_right, he, if_neg (Ne.symm hj), mul_zero]) (by simp), herm_smul_right, he,
    if_pos rfl, mul_one]

theorem herm_lc (he : ∀ i j, herm σ (e i) (e j) = if i = j then 1 else 0) (f g : ι → K) :
    herm σ (lc e f) (lc e g) = ∑ i, σ (f i) * g i := by
  conv_lhs => rw [lc]
  rw [herm_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [herm_smul_left, herm_lc_right he]

theorem uCentre_lc (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0)
    {H : Subgroup (SUid σ n)} (he : ∀ i j, herm σ (e i) (e j) = if i = j then 1 else 0)
    (hpair : ∀ i j, i ≠ j → ∀ x y : K, σ x * x + σ y * y = 0 → UCentre H (x • e i + y • e j))
    (f : ι → K) (hf : ∑ i, σ (f i) * f i = 0) : UCentre H (lc e f) := by
  classical
  induction hk : (Finset.univ.filter fun i => f i ≠ 0).card using Nat.strong_induction_on
    generalizing f with
  | _ k ih =>
  set S := Finset.univ.filter fun i => f i ≠ 0 with hS
  have hmem : ∀ i, i ∈ S ↔ f i ≠ 0 := fun i => by simp [hS]
  have hN : ∀ i ∈ S, σ (f i) * f i ≠ 0 := fun i hi =>
    mul_ne_zero ((map_ne_zero σ).2 ((hmem i).1 hi)) ((hmem i).1 hi)
  by_cases h3 : 3 ≤ k
  · have key : ∀ i j, i ∈ S → j ∈ S → i ≠ j → σ (f i) * f i + σ (f j) * f j ≠ 0 →
        UCentre H (lc e f) := by
      intro i j hi hj hij hm
      set y := f i • e i + f j • e j with hy
      have hyy : herm σ y y = σ (f i) * f i + σ (f j) * f j := by
        simp only [hy, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he,
          if_neg hij, if_neg (Ne.symm hij), if_true]
        ring
      obtain ⟨d, hd⟩ := exists_smul_norm_one hσ (hyy ▸ hm)
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_smul, herm_zero_left] at hd
        exact zero_ne_one hd
      have hN1 : σ (d * f i) * (d * f i) + σ (d * f j) * (d * f j) = 1 := by
        rw [← hd, herm_smul_left, herm_smul_right, hyy, map_mul, map_mul]
        ring
      have hpij : ∀ α β : K, σ α * α + σ β * β = 0 → UCentre H (α • e i + β • e j) :=
        hpair i j hij
      have hii := he i i
      have hjj := he j j
      have hij' := he i j
      rw [if_pos rfl] at hii hjj
      rw [if_neg hij] at hij'
      obtain ⟨t, ht, htx, hfix⟩ := exists_mem_of_orthonormal hσ hii hjj hij' hpij _ _ hN1
      set f₀ : ι → K := Function.update (Function.update f i 0) j 0 with hf₀
      set f' : ι → K := f₀ + Pi.single i d⁻¹ with hf'
      have hfd : f = f₀ + Pi.single i (f i) + Pi.single j (f j) := by
        funext m
        by_cases hmi : m = i
        · rw [hmi, Pi.add_apply, Pi.add_apply, hf₀, Function.update_of_ne hij,
            Function.update_self, Pi.single_eq_same, Pi.single_eq_of_ne hij]
          ring
        · by_cases hmj : m = j
          · rw [hmj, Pi.add_apply, Pi.add_apply, hf₀, Function.update_self,
              Pi.single_eq_of_ne hij.symm, Pi.single_eq_same]
            ring
          · rw [Pi.add_apply, Pi.add_apply, hf₀, Function.update_of_ne hmj,
              Function.update_of_ne hmi, Pi.single_eq_of_ne hmi, Pi.single_eq_of_ne hmj]
            ring
      have hr : t • lc e f₀ = lc e f₀ := by
        refine hfix _ ?_ ?_
        · rw [herm_lc_right he, hf₀, Function.update_of_ne hij, Function.update_self]
        · rw [herm_lc_right he, hf₀, Function.update_self]
      have hc : t⁻¹ • lc e f = lc e f' := by
        rw [inv_smul_eq_iff, hf', lc_add, lc_single, smul_add, hr, smul_comm, htx]
        conv_lhs => rw [hfd, lc_add, lc_add, lc_single, lc_single]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel_left₀ hd0, inv_mul_cancel_left₀ hd0,
          add_assoc]
      have hf'iso : ∑ m, σ (f' m) * f' m = 0 := by
        rw [← herm_lc he, ← hc, herm_smul_smul, herm_lc he, hf]
      have hsub : (Finset.univ.filter fun m => f' m ≠ 0) ⊆ S.erase j := by
        intro m hm
        rw [Finset.mem_filter] at hm
        rw [Finset.mem_erase]
        have hm' := hm.2
        by_cases hmi : m = i
        · subst hmi
          exact ⟨hij, hi⟩
        · have : f' m = f m := by
            rw [hf', Pi.add_apply, Pi.single_eq_of_ne hmi, add_zero, hf₀]
            by_cases hmj : m = j
            · subst hmj; simp at hm'
              rw [hf', Pi.add_apply, Pi.single_eq_of_ne hmi, add_zero, hf₀,
                Function.update_self] at hm'
              exact absurd rfl hm'
            · rw [Function.update_of_ne hmj, Function.update_of_ne hmi]
          refine ⟨fun hmj => ?_, (hmem m).2 (this ▸ hm')⟩
          subst hmj
          apply hm'
          rw [hf', Pi.add_apply, Pi.single_eq_of_ne hmi, add_zero, hf₀, Function.update_self]
      have hlt : (Finset.univ.filter fun m => f' m ≠ 0).card < k := by
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hj] at this
        omega
      exact uCentre_of_smul (H.inv_mem ht) (hc ▸ ih _ hlt f' hf'iso rfl)
    obtain ⟨i, hi, j, hj, l, hl, hij, hil, hjl⟩ := Finset.two_lt_card.1 (by omega : 2 < S.card)
    by_cases h1 : σ (f i) * f i + σ (f j) * f j = 0
    · by_cases h2 : σ (f i) * f i + σ (f l) * f l = 0
      · refine key j l hj hl hjl fun h => hN i hi ?_
        have : (2 : K) * (σ (f i) * f i) = 0 := by linear_combination h1 + h2 - h
        exact (mul_eq_zero.1 this).resolve_left h2K
      · exact key i l hi hl hil h2
    · exact key i j hi hj hij h1
  · have hsum : ∀ {β : Type} [AddCommMonoid β] (g : ι → β), (∀ m, m ∉ S → g m = 0) →
        ∀ T : Finset ι, S ⊆ T → ∑ m, g m = ∑ m ∈ T, g m := fun g hg T hT =>
      (Finset.sum_subset (Finset.subset_univ T) fun m _ hm => hg m fun h => hm (hT h)).symm
    have hf0 : ∀ m, m ∉ S → f m = 0 := fun m hm => by
      by_contra h
      exact hm ((hmem m).2 h)
    interval_cases k
    · have : f = 0 := funext fun m => hf0 m (by rw [Finset.card_eq_zero.1 hk]; simp)
      rw [this, show lc e 0 = 0 by simp [lc]]
      exact uCentre_zero H
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hk
      have := hsum (fun m => σ (f m) * f m) (fun m hm => by rw [hf0 m hm, mul_zero]) {i}
        hi.le
      rw [Finset.sum_singleton, hf] at this
      exact absurd this.symm (hN i (by rw [hi]; exact Finset.mem_singleton_self i))
    · obtain ⟨i, j, hij, hij'⟩ := Finset.card_eq_two.1 hk
      have hlc : lc e f = f i • e i + f j • e j := by
        rw [lc, hsum (fun m => f m • e m) (fun m hm => by rw [hf0 m hm, zero_smul]) {i, j}
          hij'.le, Finset.sum_pair hij]
      have hiso : σ (f i) * f i + σ (f j) * f j = 0 := by
        rw [← hf, hsum (fun m => σ (f m) * f m) (fun m hm => by rw [hf0 m hm, mul_zero]) {i, j}
          hij'.le, Finset.sum_pair hij]
      rw [hlc]
      exact hpair i j hij _ _ hiso

end Family

section Field

theorem isSquare_norm [Finite K] (c : K) : IsSquare (σ c * c) := by
  classical
  have := Fintype.ofFinite K
  by_cases hc : c = 0
  · rw [hc, mul_zero]
    exact IsSquare.zero
  have hsc : σ c ≠ 0 := (map_ne_zero σ).2 hc
  have hs : quadraticChar K (σ c) = quadraticChar K c := by
    by_cases h : IsSquare c
    · rw [(quadraticChar_one_iff_isSquare hc).2 h,
        (quadraticChar_one_iff_isSquare hsc).2 (h.map σ)]
    · rw [quadraticChar_neg_one_iff_not_isSquare.2 h,
        quadraticChar_neg_one_iff_not_isSquare.2 fun h' => h (by simpa using h'.map σ.symm)]
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hsc hc), map_mul, hs, ← sq,
    quadraticChar_sq_one hc]

theorem exists_hilbert90 (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0) {α : K}
    (hα : σ α * α = 1) : ∃ β : K, β ≠ 0 ∧ α * σ β = β := by
  have key : ∀ c : K, c + α * σ c ≠ 0 → ∃ β : K, β ≠ 0 ∧ α * σ β = β := fun c hc =>
    ⟨c + α * σ c, hc, by
      rw [map_add, map_mul, hσ.invol]
      linear_combination c * hα⟩
  by_cases h1 : (1 : K) + α * σ 1 = 0
  · obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
    refine key τ ?_
    have hα1 : α = -1 := by rw [map_one, mul_one] at h1; linear_combination h1
    rw [hα1, show σ τ = -τ by linear_combination hτ]
    intro h
    exact hτ0 ((mul_eq_zero.1 (by linear_combination h : (2 : K) * τ = 0)).resolve_left h2K)
  · exact key 1 h1

theorem exists_sq_of_norm_one [Finite K] (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0)
    {α : K} (hα : σ α * α = 1) : ∃ γ : K, γ * γ = α := by
  obtain ⟨β, hβ0, hβ⟩ := exists_hilbert90 hσ h2K hα
  obtain ⟨r, hr⟩ := isSquare_norm (σ := σ) β
  have hσβ : σ β ≠ 0 := (map_ne_zero σ).2 hβ0
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact mul_ne_zero hσβ hβ0 hr
  refine ⟨β / r, ?_⟩
  rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hr0 hr0)]
  linear_combination (-β) * hβ + α * hr

end Field

section Geometry

theorem exists_isotropic_of_two_le (hσ : IsUnitaryInvolution σ) {W : Submodule K (Fin n → K)}
    (hW : 2 ≤ Module.finrank K W) (T : (Fin n → K) →ₗ[K] (Fin n → K))
    (hT : ∀ u w, herm σ w (T u) = σ (herm σ u (T w))) :
    ∃ w ∈ W, w ≠ 0 ∧ herm σ w (T w) = 0 := by
  have hW0 : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  by_cases huu : herm σ u (T u) = 0
  · exact ⟨u, hu, hu0, huu⟩
  let ℓ : W →ₗ[K] K :=
    { toFun := fun w => herm σ u (T w)
      map_add' := fun w w' => by simp only [Submodule.coe_add, map_add, herm_add_right]
      map_smul' := fun c w => by
        simp only [Submodule.coe_smul, map_smul, herm_smul_right, RingHom.id_apply,
          smul_eq_mul] }
  have hker : 0 < Module.finrank K (LinearMap.ker ℓ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ℓ
    have h2 : Module.finrank K (LinearMap.range ℓ) ≤ 1 :=
      (Submodule.finrank_le _).trans (by rw [Module.finrank_self])
    omega
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := LinearMap.ker ℓ)
    fun h => by rw [h, finrank_bot] at hker; omega
  set w' : Fin n → K := (x : Fin n → K) with hw'
  have hw'W : w' ∈ W := x.2
  have hw'0 : w' ≠ 0 := by
    intro h
    apply hx0
    exact Subtype.ext h
  have huw : herm σ u (T w') = 0 := LinearMap.mem_ker.1 hxk
  have hwu : herm σ w' (T u) = 0 := by rw [hT, huw, map_zero]
  by_cases hww : herm σ w' (T w') = 0
  · exact ⟨w', hw'W, hw'0, hww⟩
  have hfix : ∀ y, σ (herm σ y (T y)) = herm σ y (T y) := fun y => (hT y y).symm
  obtain ⟨τ, hτ⟩ := hσ.norm_surj (-herm σ u (T u) / herm σ w' (T w'))
    (by rw [map_div₀, map_neg, hfix, hfix]) (div_ne_zero (neg_ne_zero.2 huu) hww)
  refine ⟨u + τ • w', W.add_mem hu (W.smul_mem τ hw'W), fun h => huu ?_, ?_⟩
  · have hu' : u = -(τ • w') := eq_neg_of_add_eq_zero_left h
    rw [hu', map_neg, map_smul, herm_neg_right, herm_smul_right, ← hu', huw, mul_zero, neg_zero]
  · simp only [map_add, map_smul, herm_add_left, herm_add_right, herm_smul_left,
      herm_smul_right, huw, hwu]
    ring_nf
    rw [hτ, div_mul_cancel₀ _ hww]
    ring

@[expose] def eigU (x : SUid σ n) (γ : K) : Submodule K (Fin n → K) where
  carrier := {v | x • v = γ • v}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_add, hv, hw, smul_add]
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_comm, hv, smul_comm]

theorem mem_eigU {x : SUid σ n} {γ : K} {v : Fin n → K} : v ∈ eigU x γ ↔ x • v = γ • v :=
  Iff.rfl

@[expose] noncomputable def actL (x : SUid σ n) : (Fin n → K) →ₗ[K] (Fin n → K) :=
  Matrix.mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

@[simp] theorem actL_apply (x : SUid σ n) (v : Fin n → K) : actL x v = x • v := rfl

theorem finrank_le_of_mapsTo (x : SUid σ n) {A B : Submodule K (Fin n → K)}
    (h : ∀ u ∈ A, x • u ∈ B) : Module.finrank K A ≤ Module.finrank K B :=
  LinearMap.finrank_le_finrank_of_injective (f := (actL x).restrict h) fun u w huw => by
    have : x • (u : Fin n → K) = x • (w : Fin n → K) := congrArg Subtype.val huw
    exact Subtype.ext (smul_left_cancel x this)

theorem exists_stable_pair (hσ : ∀ c, σ (σ c) = c) {a b : SUid σ n} {u : Fin n → K} (hu0 : u ≠ 0)
    {γ μ β : K} (hau : a • u = γ • u) (habu : a • b • u = μ • b • u) (hbbu : b • b • u = β • u)
    (huu : herm σ u u = 0) (hub : herm σ u (b • u) = 0) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, a • w ∈ W) ∧ ∀ w ∈ W, b • w ∈ W := by
  have hbu : herm σ (b • u) u = 0 := herm_eq_zero_comm σ hσ hub
  have hbb : herm σ (b • u) (b • u) = 0 := by rw [herm_smul_smul, huu]
  refine ⟨Submodule.span K {u, b • u}, fun h => hu0 ?_, ?_, ?_, ?_⟩
  · have : u ∈ Submodule.span K {u, b • u} := Submodule.subset_span (by simp)
    rw [h] at this
    exact (Submodule.mem_bot K).1 this
  · intro x hx y hy
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hx
    obtain ⟨c', d', rfl⟩ := Submodule.mem_span_pair.1 hy
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, huu, hub, hbu,
      hbb]
    ring
  · intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hw
    refine Submodule.mem_span_pair.2 ⟨c * γ, d * μ, ?_⟩
    rw [smul_add, smul_comm a c u, smul_comm a d (b • u), hau, habu, smul_smul, smul_smul]
  · intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hw
    refine Submodule.mem_span_pair.2 ⟨d * β, c, ?_⟩
    rw [smul_add, smul_comm b c u, smul_comm b d (b • u), hbbu, smul_smul, add_comm]

end Geometry

section Lifts

theorem eigU_sup_eigU (h2K : (2 : K) ≠ 0) {x : SUid σ n} {γ : K} (hγ : γ ≠ 0)
    (hx2 : ∀ v : Fin n → K, x • x • v = (γ * γ) • v) : eigU x γ ⊔ eigU x (-γ) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  refine Submodule.mem_sup.2 ⟨(2⁻¹ : K) • (v + γ⁻¹ • x • v), ?_, (2⁻¹ : K) • (v - γ⁻¹ • x • v),
    ?_, ?_⟩
  · rw [mem_eigU, smul_comm x (2⁻¹ : K), smul_add, smul_comm x γ⁻¹, hx2]
    generalize x • v = y
    match_scalars <;> field_simp
  · rw [mem_eigU, smul_comm x (2⁻¹ : K), smul_sub, smul_comm x γ⁻¹, hx2]
    generalize x • v = y
    match_scalars <;> field_simp
  · have h2 : (2⁻¹ : K) + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2K]
    generalize x • v = y
    linear_combination (norm := module) h2 • v

theorem eigU_inf_eigU (h2K : (2 : K) ≠ 0) {x : SUid σ n} {γ : K} (hγ : γ ≠ 0) :
    eigU x γ ⊓ eigU x (-γ) = ⊥ := by
  rw [eq_bot_iff]
  intro v hvv
  obtain ⟨hv, hv'⟩ := Submodule.mem_inf.1 hvv
  rw [mem_eigU] at hv hv'
  have : (2 * γ) • v = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 2 [← neg_neg γ]
    rw [neg_smul, ← hv', ← hv, add_neg_cancel]
  exact (Submodule.mem_bot K).2 ((smul_eq_zero.1 this).resolve_left (mul_ne_zero h2K hγ))

theorem herm_eigU_neg (h2K : (2 : K) ≠ 0) {x : SUid σ n} {γ : K} (hε : σ γ * γ = 1)
    {u w : Fin n → K} (hu : u ∈ eigU x γ) (hw : w ∈ eigU x (-γ)) : herm σ u w = 0 := by
  have h := herm_smul_smul σ x u w
  rw [mem_eigU.1 hu, mem_eigU.1 hw, herm_smul_left, herm_smul_right] at h
  have : (2 : K) * herm σ u w = 0 := by linear_combination -h - herm σ u w * hε
  exact (mul_eq_zero.1 this).resolve_left h2K

theorem herm_eigU_self (h2K : (2 : K) ≠ 0) {x : SUid σ n} {γ : K} (hε : σ γ * γ = -1)
    {u w : Fin n → K} (hu : u ∈ eigU x γ) (hw : w ∈ eigU x γ) : herm σ u w = 0 := by
  have h := herm_smul_smul σ x u w
  rw [mem_eigU.1 hu, mem_eigU.1 hw, herm_smul_left, herm_smul_right] at h
  have : (2 : K) * herm σ u w = 0 := by linear_combination -h + herm σ u w * hε
  exact (mul_eq_zero.1 this).resolve_left h2K

theorem exists_stable_of_anticomm (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0) (hn : 3 ≤ n)
    {a b : SUid σ n} {γ β : K} (hγ : γ ≠ 0) (hε : σ γ * γ = 1 ∨ σ γ * γ = -1)
    (hβ : σ β * β = 1) (ha2 : ∀ v : Fin n → K, a • a • v = (γ * γ) • v)
    (hb2 : ∀ v : Fin n → K, b • b • v = β • v) (hab : ∀ v : Fin n → K, a • b • v = -(b • a • v)) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, a • w ∈ W) ∧ ∀ w ∈ W, b • w ∈ W := by
  have hbp : ∀ u ∈ eigU a γ, b • u ∈ eigU a (-γ) := fun u hu => by
    rw [mem_eigU, hab, mem_eigU.1 hu, smul_comm b γ u, neg_smul]
  have hbm : ∀ u ∈ eigU a (-γ), b • u ∈ eigU a γ := fun u hu => by
    rw [mem_eigU, hab, mem_eigU.1 hu, smul_comm b (-γ) u, neg_smul, neg_neg]
  have hdim : 2 ≤ Module.finrank K (eigU a γ) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (eigU a γ) (eigU a (-γ))
    rw [eigU_sup_eigU h2K hγ ha2, eigU_inf_eigU h2K hγ, finrank_top, finrank_bot,
      Module.finrank_fin_fun] at h1
    have h2 := finrank_le_of_mapsTo b hbp
    have h3 := finrank_le_of_mapsTo b hbm
    omega
  have key : ∀ u ∈ eigU a γ, u ≠ 0 → herm σ u u = 0 → herm σ u (b • u) = 0 →
      ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
        (∀ w ∈ W, a • w ∈ W) ∧ ∀ w ∈ W, b • w ∈ W := fun u hu hu0 huu hub =>
    exists_stable_pair hσ.invol hu0 (mem_eigU.1 hu) (mem_eigU.1 (hbp u hu)) (hb2 u) huu hub
  rcases hε with hε | hε
  · obtain ⟨u, hu, hu0, huu⟩ := exists_isotropic_of_two_le hσ hdim LinearMap.id
      fun u w => herm_conj σ hσ.invol u w
    exact key u hu hu0 huu (herm_eigU_neg h2K hε hu (hbp u hu))
  · obtain ⟨ρ, hρ0, hρ⟩ := exists_hilbert90 hσ h2K (α := σ β)
      (by rw [hσ.invol, mul_comm, hβ])
    obtain ⟨u, hu, hu0, hub⟩ := exists_isotropic_of_two_le hσ hdim (ρ • actL b) fun u w => by
      simp only [LinearMap.smul_apply, actL_apply, herm_smul_right, map_mul]
      rw [← herm_conj σ hσ.invol, ← herm_smul_smul σ b (b • w) u, hb2, herm_smul_left]
      linear_combination -herm σ w (b • u) * hρ
    refine key u hu hu0 (herm_eigU_self h2K hε hu hu) ?_
    simpa [LinearMap.smul_apply, actL_apply, herm_smul_right, hρ0] using hub

theorem exists_stable_of_comm_anti (h2K : (2 : K) ≠ 0) (hn : 1 ≤ n) {a b : SUid σ n} {γ : K}
    (hγ : γ ≠ 0) (hε : σ γ * γ = -1) (ha2 : ∀ v : Fin n → K, a • a • v = (γ * γ) • v)
    (hab : ∀ v : Fin n → K, a • b • v = b • a • v) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      (∀ w ∈ W, a • w ∈ W) ∧ ∀ w ∈ W, b • w ∈ W := by
  have key : ∀ μ : K, σ μ * μ = -1 → eigU a μ ≠ ⊥ →
      ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
        (∀ w ∈ W, a • w ∈ W) ∧ ∀ w ∈ W, b • w ∈ W := fun μ hμ hne =>
    ⟨eigU a μ, hne, fun x hx y hy => herm_eigU_self h2K hμ hx hy,
      fun w hw => by rw [mem_eigU.1 hw]; exact (eigU a μ).smul_mem μ hw,
      fun w hw => by rw [mem_eigU, hab, mem_eigU.1 hw, smul_comm]⟩
  by_cases hp : eigU a γ = ⊥
  · refine key (-γ) (by rw [map_neg, neg_mul_neg, hε]) fun hm => ?_
    have h := eigU_sup_eigU h2K hγ ha2
    rw [hp, hm, bot_sup_eq] at h
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact bot_ne_top h
  · exact key γ hε hp

@[expose] def sgn (s : Bool) : K := if s then 1 else -1

theorem sgn_mul_self (s : Bool) : sgn s * sgn s = (1 : K) := by cases s <;> simp [sgn]

theorem map_sgn (s : Bool) : σ (sgn s) = (sgn s : K) := by cases s <;> simp [sgn]

theorem sgn_of_ne {s s' : Bool} (h : s ≠ s') : (sgn s' : K) = -sgn s := by
  cases s <;> cases s' <;> simp_all [sgn]

end Lifts

section Comm

variable {a b : SUid σ n} {γ δ : K}

@[expose] def commEig (a b : SUid σ n) (γ δ : K) (χ : Bool × Bool) : Submodule K (Fin n → K) :=
  eigU a (sgn χ.1 * γ) ⊓ eigU b (sgn χ.2 * δ)

@[expose] def commProj (a b : SUid σ n) (γ δ : K) (χ : Bool × Bool) (v : Fin n → K) :
    Fin n → K :=
  (4⁻¹ : K) • (v + (sgn χ.1 * γ⁻¹) • a • v + (sgn χ.2 * δ⁻¹) • b • v +
    (sgn χ.1 * sgn χ.2 * γ⁻¹ * δ⁻¹) • a • b • v)

theorem commProj_mem (hγ : γ ≠ 0) (hδ : δ ≠ 0) (ha2 : ∀ v : Fin n → K, a • a • v = (γ * γ) • v)
    (hb2 : ∀ v : Fin n → K, b • b • v = (δ * δ) • v) (hab : ∀ v : Fin n → K, a • b • v = b • a • v)
    (χ : Bool × Bool) (v : Fin n → K) : commProj a b γ δ χ v ∈ commEig a b γ δ χ := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_eigU, commProj]
    simp only [smul_add, smul_comm a (4⁻¹ : K), smul_comm a (sgn χ.1 * γ⁻¹),
      smul_comm a (sgn χ.2 * δ⁻¹), smul_comm a (sgn χ.1 * sgn χ.2 * γ⁻¹ * δ⁻¹), ha2]
    generalize a • v = y₁
    generalize b • v = y₂
    generalize a • y₂ = y₃
    rcases χ with ⟨_ | _, _ | _⟩ <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte] <;>
      match_scalars <;> field_simp
  · rw [mem_eigU, commProj]
    simp only [smul_add, smul_comm b (4⁻¹ : K), smul_comm b (sgn χ.1 * γ⁻¹),
      smul_comm b (sgn χ.2 * δ⁻¹), smul_comm b (sgn χ.1 * sgn χ.2 * γ⁻¹ * δ⁻¹), hb2, ← hab,
      smul_comm a (δ * δ)]
    generalize a • v = y₁
    generalize b • v = y₂
    generalize a • y₂ = y₃
    rcases χ with ⟨_ | _, _ | _⟩ <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte] <;>
      match_scalars <;> field_simp

theorem sum_commProj (h2K : (2 : K) ≠ 0) (v : Fin n → K) :
    ∑ χ, commProj a b γ δ χ v = v := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2K h2K
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, commProj, sgn]
  generalize a • v = y₁
  generalize b • v = y₂
  generalize a • y₂ = y₃
  simp only [if_true, Bool.false_eq_true, if_false]
  match_scalars <;> field_simp <;> ring

theorem norm_sgn_mul {γ : K} (hε : σ γ * γ = 1) (s : Bool) : σ (sgn s * γ) * (sgn s * γ) = 1 := by
  rw [map_mul, map_sgn]
  linear_combination (sgn s * sgn s) * hε + sgn_mul_self (K := K) s

theorem herm_commEig (h2K : (2 : K) ≠ 0) (hεa : σ γ * γ = 1) (hεb : σ δ * δ = 1)
    {χ ψ : Bool × Bool} (hne : χ ≠ ψ) {u w : Fin n → K} (hu : u ∈ commEig a b γ δ χ)
    (hw : w ∈ commEig a b γ δ ψ) : herm σ u w = 0 := by
  by_cases h1 : χ.1 = ψ.1
  · have h2 : χ.2 ≠ ψ.2 := fun h => hne (Prod.ext h1 h)
    have hw' : w ∈ eigU b (-(sgn χ.2 * δ)) := by
      rw [← neg_mul, ← sgn_of_ne h2]
      exact (Submodule.mem_inf.1 hw).2
    exact herm_eigU_neg h2K (norm_sgn_mul hεb _) (Submodule.mem_inf.1 hu).2 hw'
  · have hw' : w ∈ eigU a (-(sgn χ.1 * γ)) := by
      rw [← neg_mul, ← sgn_of_ne h1]
      exact (Submodule.mem_inf.1 hw).1
    exact herm_eigU_neg h2K (norm_sgn_mul hεa _) (Submodule.mem_inf.1 hu).1 hw'

theorem uCentre_of_comm (hσ : IsUnitaryInvolution σ) (h2K : (2 : K) ≠ 0)
    {H : Subgroup (SUid σ n)} (hγ : γ ≠ 0) (hδ : δ ≠ 0) (hεa : σ γ * γ = 1)
    (hεb : σ δ * δ = 1) (ha2 : ∀ v : Fin n → K, a • a • v = (γ * γ) • v)
    (hb2 : ∀ v : Fin n → K, b • b • v = (δ * δ) • v) (hab : ∀ v : Fin n → K, a • b • v = b • a • v)
    (hcent : ∀ x, (x = a ∨ x = b ∨ x = a * b) → ∀ (c : Fin n → K) (l : K), σ l * l = 1 →
      x • c = l • c → herm σ c c = 0 → UCentre H c)
    (haniso : ∀ χ, ∀ v ∈ commEig a b γ δ χ, v ≠ 0 → herm σ v v ≠ 0)
    (c : Fin n → K) (hc : herm σ c c = 0) : UCentre H c := by
  classical
  set V := commEig a b γ δ with hV
  set P := commProj a b γ δ with hP
  have hPV : ∀ χ v, P χ v ∈ V χ := commProj_mem hγ hδ ha2 hb2 hab
  have hsum : ∀ v, ∑ χ, P χ v = v := sum_commProj h2K
  have horth : ∀ {χ ψ}, χ ≠ ψ → ∀ {u w}, u ∈ V χ → w ∈ V ψ → herm σ u w = 0 :=
    fun hne _ _ hu hw => herm_commEig h2K hεa hεb hne hu hw
  let ι := {χ : Bool × Bool // V χ ≠ ⊥}
  have hex : ∀ χ : ι, ∃ e ∈ V χ.1, herm σ e e = 1 := by
    intro χ
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.2
    obtain ⟨d, hd⟩ := exists_smul_norm_one hσ (haniso χ.1 u hu hu0)
    exact ⟨d • u, (V χ.1).smul_mem d hu, hd⟩
  choose e heV he1 using hex
  have hline : ∀ (χ : ι), ∀ v ∈ V χ.1, v = herm σ (e χ) v • e χ := by
    intro χ v hv
    set w := v - herm σ (e χ) v • e χ with hw
    have hwV : w ∈ V χ.1 := (V χ.1).sub_mem hv ((V χ.1).smul_mem _ (heV χ))
    have hew : herm σ (e χ) w = 0 := by
      rw [hw, herm_sub_right, herm_smul_right, he1, mul_one, sub_self]
    by_contra hne
    have hw0 : w ≠ 0 := fun h => hne (by rw [← sub_eq_zero, ← hw, h])
    have hww := haniso χ.1 w hwV hw0
    obtain ⟨τ, hτ⟩ := hσ.norm_surj (-(herm σ w w)⁻¹)
      (by rw [map_neg, map_inv₀, herm_self_fixed σ hσ.invol]) (neg_ne_zero.2 (inv_ne_zero hww))
    have hwe : herm σ w (e χ) = 0 := herm_eq_zero_comm σ hσ.invol hew
    refine haniso χ.1 (e χ + τ • w) ((V χ.1).add_mem (heV χ) ((V χ.1).smul_mem τ hwV))
      (fun h => ?_) ?_
    · have := congrArg (herm σ (e χ)) h
      rw [herm_add_right, herm_smul_right, he1, hew, mul_zero, add_zero, herm_zero_right] at this
      exact one_ne_zero this
    · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he1, hew, hwe,
        mul_zero, add_zero, zero_add]
      linear_combination (herm σ w w) * hτ - mul_inv_cancel₀ hww
  have he : ∀ i j : ι, herm σ (e i) (e j) = if i = j then 1 else 0 := by
    intro i j
    split_ifs with hij
    · rw [hij, he1]
    · exact horth (fun h => hij (Subtype.ext h)) (heV i) (heV j)
  have hpair : ∀ i j : ι, i ≠ j → ∀ x y : K, σ x * x + σ y * y = 0 →
      UCentre H (x • e i + y • e j) := by
    intro i j hij x y hxy
    have hiso : herm σ (x • e i + y • e j) (x • e i + y • e j) = 0 := by
      have hij' := he i j
      have hji' := he j i
      rw [if_neg hij] at hij'
      rw [if_neg (Ne.symm hij)] at hji'
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he1, hij', hji',
        mul_zero, add_zero, zero_add, mul_one]
      linear_combination hxy
    have hai : ∀ k : ι, a • e k = (sgn k.1.1 * γ) • e k := fun k =>
      (Submodule.mem_inf.1 (heV k)).1
    have hbi : ∀ k : ι, b • e k = (sgn k.1.2 * δ) • e k := fun k =>
      (Submodule.mem_inf.1 (heV k)).2
    have key : ∀ X, (X = a ∨ X = b ∨ X = a * b) → ∀ l : K, σ l * l = 1 → X • e i = l • e i →
        X • e j = l • e j → UCentre H (x • e i + y • e j) := by
      intro X hX l hl hXi hXj
      refine hcent X hX _ l hl ?_ hiso
      rw [smul_add, smul_comm X x, smul_comm X y, hXi, hXj, smul_comm x l, smul_comm y l,
        smul_add]
    by_cases h1 : i.1.1 = j.1.1
    · exact key a (Or.inl rfl) _ (norm_sgn_mul hεa _) (hai i) (by rw [hai j, h1])
    by_cases h2 : i.1.2 = j.1.2
    · exact key b (Or.inr (Or.inl rfl)) _ (norm_sgn_mul hεb _) (hbi i) (by rw [hbi j, h2])
    have hab' : ∀ k : ι, (a * b) • e k = ((sgn k.1.1 * γ) * (sgn k.1.2 * δ)) • e k := by
      intro k
      rw [mul_smul, hbi, smul_comm, hai, smul_smul, mul_comm]
    refine key (a * b) (Or.inr (Or.inr rfl)) _ ?_ (hab' i) ?_
    · rw [map_mul]
      linear_combination (σ (sgn i.1.2 * δ) * (sgn i.1.2 * δ)) * norm_sgn_mul hεa i.1.1 +
        norm_sgn_mul hεb i.1.2
    · rw [hab' j, sgn_of_ne h1, sgn_of_ne h2]
      ring_nf
  have hc' : c = lc e fun χ => herm σ (e χ) c := by
    have hcomp : ∀ χ : ι, herm σ (e χ) c = herm σ (e χ) (P χ.1 c) := by
      intro χ
      conv_lhs => rw [← hsum c]
      rw [herm_sum_right, Finset.sum_eq_single χ.1 (fun ψ _ hψ => horth (Ne.symm hψ) (heV χ)
        (hPV ψ c)) (by simp)]
    have hzero : ∀ χ : Bool × Bool, ¬ V χ ≠ ⊥ → P χ c = 0 := by
      intro χ hχ
      push Not at hχ
      have := hPV χ c
      rw [hχ] at this
      exact (Submodule.mem_bot K).1 this
    conv_lhs => rw [← hsum c]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun χ => V χ ≠ ⊥),
      Finset.sum_eq_zero (f := fun χ : {χ // ¬ V χ ≠ ⊥} => P χ.1 c) (fun χ _ => hzero χ.1 χ.2),
      add_zero, lc]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hcomp χ]
    exact hline χ _ (hPV χ.1 c)
  rw [hc']
  refine uCentre_lc hσ h2K he hpair _ ?_
  rw [← herm_lc he, ← hc', hc]

end Comm

theorem uCentre_of_eig {P : Type} [Group P] (π : SUid σ n →* P) {E : Subgroup P}
    {x : SUid σ n} (hxE : π x ∈ E) (hx1 : π x ≠ 1) {c : Fin n → K} {l : K} (hl : σ l * l = 1)
    (hxc : x • c = l • c) :
    UCentre ((⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ centralizer ({a} : Set P)).comap π)
      c := by
  intro t s _ ht
  have e : ∀ v, herm σ c (x • v) = l * herm σ c v := by
    intro v
    have h := herm_smul_smul σ x c v
    rw [hxc, herm_smul_left] at h
    linear_combination (-(herm σ c (x • v))) * hl + l * h
  have hcomm : x * t = t * x := ext_smul σ fun v => by
    rw [mul_smul, mul_smul, ht, ht, smul_add, smul_comm x (s * herm σ c v) c, hxc, e, smul_smul]
    ring_nf
  rw [mem_comap]
  have hsub : (⊤ : Subgroup P) ⊓ centralizer ({π x} : Set P) ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ centralizer ({a} : Set P) :=
    le_iSup₂_of_le (π x) hxE (le_iSup_of_le hx1 le_rfl)
  exact hsub ⟨mem_top _, mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hcomm])⟩

end USeitz

open USeitz in
theorem seitzFourUAniso_holds : SeitzFourUAniso := by
  intro K _ _ σ n P _ _ π hc hn h2K hZ E hE h4 haniso
  classical
  have hσ := hc.involution
  set M : Subgroup P := ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓
    centralizer ({a} : Set P) with hM
  set H := M.comap π with hH
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hscal : ∀ g : SUid σ (m + 1), π g = 1 → ∃ c : K, ∀ v : Fin (m + 1) → K, g • v = c • v := by
    intro g hg
    obtain ⟨c, hc'⟩ := hc.ker_scalar g hg
    exact ⟨c, fun v => by
      rw [ClassicalGroups.Unitary.smul_def, hc', Matrix.smul_mulVec, Matrix.one_mulVec]⟩
  have hπscal : ∀ g : SUid σ (m + 1), ∀ c : K, (∀ v : Fin (m + 1) → K, g • v = c • v) →
      π g = 1 := by
    intro g c hg
    have hcen : π g ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, rfl⟩ := hc.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact ext_smul σ fun v => by rw [mul_smul, mul_smul, hg, hg, smul_comm]
    rw [hZ] at hcen
    exact (Subgroup.mem_bot).1 hcen
  have h4' : Nat.card E = 2 ^ 2 := h4
  obtain ⟨e₁, he₁E, he₁1⟩ : ∃ x ∈ E, x ≠ 1 := by
    have hne : E ≠ ⊥ := by rintro h; rw [h, Subgroup.card_bot] at h4; norm_num at h4
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨e₂, he₂E, he₂z⟩ := exists_notMem_zpowers_of_card_sq Nat.prime_two hE.2 h4' he₁E he₁1
  have he₂1 : e₂ ≠ 1 := fun h => he₂z (h ▸ Subgroup.one_mem _)
  have he₁₂ : e₁ ≠ e₂ := fun h => he₂z (h ▸ Subgroup.mem_zpowers e₁)
  obtain ⟨a, ha⟩ := hc.surjective e₁
  obtain ⟨b, hb⟩ := hc.surjective e₂
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE.2 x hx
  have hcomm : e₁ * e₂ = e₂ * e₁ := by
    have := hE.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩
    exact congrArg Subtype.val this
  obtain ⟨α, hα⟩ := hscal (a * a) (by rw [map_mul, ha, hEsq e₁ he₁E])
  obtain ⟨β, hβ⟩ := hscal (b * b) (by rw [map_mul, hb, hEsq e₂ he₂E])
  obtain ⟨ν, hν⟩ := hscal (a * b * a⁻¹ * b⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb, hcomm]
    group)
  have ha2 : ∀ v : Fin (m + 1) → K, a • a • v = α • v := fun v => by rw [← mul_smul, hα]
  have hb2 : ∀ v : Fin (m + 1) → K, b • b • v = β • v := fun v => by rw [← mul_smul, hβ]
  have hab : ∀ v : Fin (m + 1) → K, a • b • v = ν • b • a • v := fun v => by
    rw [← hν, mul_smul, mul_smul, mul_smul, inv_smul_smul, inv_smul_smul]
  have hnorm : ∀ x : SUid σ (m + 1), ∀ c : K, (∀ v : Fin (m + 1) → K, x • v = c • v) →
      σ c * c = 1 := by
    intro x c hx
    have h := herm_smul_smul σ x (e0 K m) (e0 K m)
    rw [hx, herm_smul_left, herm_smul_right, herm_e0_e0, mul_one] at h
    exact h
  have hαn : σ α * α = 1 := hnorm _ _ hα
  have hβn : σ β * β = 1 := hnorm _ _ hβ
  have hα0 : α ≠ 0 := by rintro rfl; rw [mul_zero] at hαn; exact zero_ne_one hαn
  have hν2 : ν * ν = 1 := by
    have h1 := ha2 (b • b⁻¹ • e0 K m)
    rw [hab, smul_comm a ν, hab, ha2, smul_comm b α, smul_smul, smul_smul, smul_inv_smul] at h1
    have h2 : (ν * ν * α - α) • e0 K m = 0 := by rw [sub_smul, h1, sub_self]
    have h3 := congrFun h2 0
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at h3
    have : (ν * ν - 1) * α = 0 := by linear_combination h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hα0)
  obtain ⟨γ, hγ⟩ := exists_sq_of_norm_one hσ h2K hαn
  obtain ⟨δ, hδ⟩ := exists_sq_of_norm_one hσ h2K hβn
  have hγ0 : γ ≠ 0 := by rintro rfl; rw [mul_zero] at hγ; exact hα0 hγ.symm
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hδ
    rw [← hδ, map_zero, zero_mul] at hβn
    exact zero_ne_one hβn
  have hε : ∀ {μ ξ : K}, μ * μ = ξ → σ ξ * ξ = 1 → σ μ * μ = 1 ∨ σ μ * μ = -1 := by
    intro μ ξ hμ hξ
    refine mul_self_eq_one_iff.1 ?_
    rw [← hξ, ← hμ, map_mul]
    ring
  have hεa := hε hγ hαn
  have hεb := hε hδ hβn
  rw [← hγ] at ha2
  rw [← hδ] at hb2
  have hstab1 : ∀ (W : Submodule K (Fin (m + 1) → K)) (x : SUid σ (m + 1)),
      (∀ w ∈ W, x • w ∈ W) → ∀ g, π g = π x → ∀ w ∈ W, g • w ∈ W := by
    intro W x hx g hg w hw
    obtain ⟨c, hcg⟩ := hscal (x⁻¹ * g) (by rw [map_mul, map_inv, hg, inv_mul_cancel])
    have : g • w = x • c • w := by rw [← hcg, ← mul_smul, mul_inv_cancel_left]
    rw [this]
    exact hx _ (W.smul_mem c hw)
  have hstab : ∀ W : Submodule K (Fin (m + 1) → K), (∀ w ∈ W, a • w ∈ W) →
      (∀ w ∈ W, b • w ∈ W) → ∀ g : SUid σ (m + 1), π g ∈ E → ∀ w ∈ W, g • w ∈ W := by
    intro W hWa hWb g hg
    rcases SpSeitz.mem_four hE h4 he₁E he₂E hg he₁1 he₂1 he₁₂ with h | h | h | h
    · exact hstab1 W 1 (fun w hw => by rw [one_smul]; exact hw) g (by rw [h, map_one])
    · exact hstab1 W a hWa g (by rw [h, ha])
    · exact hstab1 W b hWb g (by rw [h, hb])
    · exact hstab1 W (a * b) (fun w hw => by rw [mul_smul]; exact hWa _ (hWb w hw)) g
        (by rw [h, map_mul, ha, hb])
  have hcontra : ∀ W : Submodule K (Fin (m + 1) → K), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) → (∀ w ∈ W, a • w ∈ W) → (∀ w ∈ W, b • w ∈ W) →
      False := fun W hW0 hti hWa hWb => hW0 (haniso W hti (hstab W hWa hWb))
  have hcent : ∀ x, (x = a ∨ x = b ∨ x = a * b) → ∀ (c : Fin (m + 1) → K) (l : K),
      σ l * l = 1 → x • c = l • c → herm σ c c = 0 → UCentre H c := by
    intro x hx c l hl hxc _
    have hxE : π x ∈ E ∧ π x ≠ 1 := by
      rcases hx with rfl | rfl | rfl
      · exact ⟨ha ▸ he₁E, ha ▸ he₁1⟩
      · exact ⟨hb ▸ he₂E, hb ▸ he₂1⟩
      · rw [map_mul, ha, hb]
        refine ⟨E.mul_mem he₁E he₂E, fun h => he₁₂ ?_⟩
        calc e₁ = e₁ * (e₂ * e₂) := by rw [hEsq e₂ he₂E, mul_one]
          _ = e₂ := by rw [← mul_assoc, h, one_mul]
    exact uCentre_of_eig π hxE.1 hxE.2 hl hxc
  have hall : ∀ c : Fin (m + 1) → K, herm σ c c = 0 → UCentre H c := by
    rcases mul_self_eq_one_iff.1 hν2 with rfl | rfl
    · have hab1 : ∀ v : Fin (m + 1) → K, a • b • v = b • a • v := fun v => by
        rw [hab, one_smul]
      rcases hεa with hεa | hεa
      · rcases hεb with hεb | hεb
        · refine uCentre_of_comm hσ h2K hγ0 hδ0 hεa hεb ha2 hb2 hab1 hcent ?_
          intro χ v hv hv0 hvv
          have hva := (Submodule.mem_inf.1 hv).1
          have hvb := (Submodule.mem_inf.1 hv).2
          refine hcontra (K ∙ v) (fun h => hv0 ((Submodule.span_singleton_eq_bot).1 h)) ?_ ?_ ?_
          · intro x hx y hy
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
            obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
            rw [herm_smul_left, herm_smul_right, hvv, mul_zero, mul_zero]
          · intro w hw
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
            rw [smul_comm, mem_eigU.1 hva, smul_smul]
            exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
          · intro w hw
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
            rw [smul_comm, mem_eigU.1 hvb, smul_smul]
            exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
        · obtain ⟨W, hW0, hti, hWb, hWa⟩ := exists_stable_of_comm_anti h2K (by omega) hδ0 hεb hb2
            fun v => (hab1 v).symm
          exact (hcontra W hW0 hti hWa hWb).elim
      · obtain ⟨W, hW0, hti, hWa, hWb⟩ := exists_stable_of_comm_anti h2K (by omega) hγ0 hεa ha2
          hab1
        exact (hcontra W hW0 hti hWa hWb).elim
    · have hab1 : ∀ v : Fin (m + 1) → K, a • b • v = -(b • a • v) := fun v => by
        rw [hab, neg_one_smul]
      obtain ⟨W, hW0, hti, hWa, hWb⟩ :=
        exists_stable_of_anticomm hσ h2K hn hγ0 hεa hβn ha2 (fun v => by rw [hb2, hδ]) hab1
      exact (hcontra W hW0 hti hWa hWb).elim
  have hT : T σ (m + 1) ≤ H := T_le_of_uCentre hall
  rw [T_eq_top hσ (by omega) hc.exists_norm] at hT
  intro k _
  obtain ⟨g, rfl⟩ := hc.surjective k
  exact hT (Subgroup.mem_top g)

theorem seitzFourInner_psu :
    SeitzFourInner fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSU n p f :=
  seitzFourInner_psu_of_aniso seitzFourUAniso_holds

end CFSG.LocalAnalysis.WeakClosure81
