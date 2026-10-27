module

public import CFSG.Quasithin.Recognition.J2RecLines

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem fin5_two_fixed : ∀ f : Fin 5 → Fin 5, (∀ i, f (f (f i)) = i) →
    ∃ i j, i ≠ j ∧ f i = i ∧ f j = j := by
  decide +kernel

variable {G : Type} [Group G] {z : G}

theorem conj_cube {y : G} (hy3 : y ^ 3 = 1) (w : G) :
    y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = w := by
  have h : y * y * y = 1 := by simpa [pow_succ, mul_assoc] using hy3
  calc y * (y * (y * w * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * w * (y * y * y)⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
    _ = w := by rw [h]; simp

theorem conj_mem_pCoreOf {y g : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G))
    (hg : g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    y * g * y⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hy) g).mp hg

theorem _root_.CFSG.Quasithin.IsTypeH2.exists_line_conj (h : IsTypeH2 G z) {x : Fin 5 → G}
    (hxQ : ∀ i, x i ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hx : J2FiveLines z x)
    {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (i : Fin 5) :
    ∃ k, y * x i * y⁻¹ = x k ∨ y * x i * y⁻¹ = z * x k := by
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  refine h.eq_line_of_involution hxQ hx (conj_mem_pCoreOf hy (hxQ i)) ?_ ?_ ?_
  · calc y * x i * y⁻¹ * (y * x i * y⁻¹) = y * (x i * x i) * y⁻¹ := by group
      _ = 1 := by rw [hx.x_sq i]; group
  · intro h1
    apply hx.x_ne_one h.ne_one i
    have : x i = y⁻¹ * (y * x i * y⁻¹) * y := by group
    rw [this, h1]
    group
  · intro h1
    apply hx.x_ne_d h.ne_one i
    have : x i = y⁻¹ * (y * x i * y⁻¹) * y := by group
    rw [this, h1]
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [hyz]
      _ = z := by group

theorem _root_.CFSG.Quasithin.IsTypeH2.exists_two_fixed_lines (h : IsTypeH2 G z) {x : Fin 5 → G}
    (hxQ : ∀ i, x i ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hx : J2FiveLines z x)
    {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : y ^ 3 = 1) :
    ∃ i j, i ≠ j ∧ y * x i * y⁻¹ = x i ∧ y * x j * y⁻¹ = x j := by
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hz2 : z * z = 1 := hx.d_sq
  choose f hf using h.exists_line_conj hxQ hx hy
  let S : Fin 5 → Set G := fun k => {w | w = x k ∨ w = z * x k}
  have hstep : ∀ i, ∀ w ∈ S i, y * w * y⁻¹ ∈ S (f i) := by
    intro i w hw
    have hi := hf i
    rcases hw with rfl | rfl
    · exact hi
    · have hc : y * (z * x i) * y⁻¹ = z * (y * x i * y⁻¹) := by
        calc y * (z * x i) * y⁻¹ = (y * z) * x i * y⁻¹ := by group
          _ = (z * y) * x i * y⁻¹ := by rw [hyz]
          _ = z * (y * x i * y⁻¹) := by group
      rw [hc]
      rcases hi with hi | hi
      · rw [hi]; exact Or.inr rfl
      · rw [hi]; left
        calc z * (z * x (f i)) = (z * z) * x (f i) := by group
          _ = x (f i) := by rw [hz2, one_mul]
  have hid : ∀ i, f (f (f i)) = i := by
    intro i
    have h0 : x i ∈ S i := Or.inl rfl
    have h1 := hstep _ _ h0
    have h2 := hstep _ _ h1
    have h3 := hstep _ _ h2
    have hy3' : y * (y * (y * x i * y⁻¹) * y⁻¹) * y⁻¹ = x i := conj_cube hy3 _
    rw [hy3'] at h3
    by_contra hne
    rcases h3 with h3 | h3
    · exact hx.x_ne_x h.ne_one (Ne.symm hne) h3
    · exact hx.x_ne_dx h.ne_one (Ne.symm hne) h3
  obtain ⟨i, j, hij, hfi, hfj⟩ := fin5_two_fixed f hid
  have hfix : ∀ k, f k = k → y * x k * y⁻¹ = x k := by
    intro k hk
    have hk' := hf k
    rw [hk] at hk'
    rcases hk' with hk' | hk'
    · exact hk'
    · exfalso
      have hc : y * (z * x k) * y⁻¹ = z * (y * x k * y⁻¹) := by
        calc y * (z * x k) * y⁻¹ = (y * z) * x k * y⁻¹ := by group
          _ = (z * y) * x k * y⁻¹ := by rw [hyz]
          _ = z * (y * x k * y⁻¹) := by group
      have h2 : y * (y * x k * y⁻¹) * y⁻¹ = x k := by
        rw [hk']
        calc y * (z * x k) * y⁻¹ = z * (y * x k * y⁻¹) := hc
          _ = z * (z * x k) := by rw [hk']
          _ = (z * z) * x k := by group
          _ = x k := by rw [hz2, one_mul]
      have h3 : y * (y * (y * x k * y⁻¹) * y⁻¹) * y⁻¹ = x k := conj_cube hy3 _
      rw [h2] at h3
      have h4 : z * x k = x k := by rw [← hk', h3]
      have : z = 1 := by
        have h5 : z * x k * (x k)⁻¹ = x k * (x k)⁻¹ := by rw [h4]
        simpa using h5
      exact h.ne_one this
  exact ⟨i, j, hij, hfix i hfi, hfix j hfj⟩

end CFSG.Quasithin.Kleidman.ThreeLocal
