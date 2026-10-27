module

public import CFSG.Quasithin.H13.A5V1367a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

theorem eq_one_of_pow_four {Γ : Type*} [Group Γ] {P : Subgroup Γ} (hP : IsPGroup 2 P) {x r : Γ}
    (hx : x ∈ Subgroup.normalizer (P : Set Γ)) (hodd : Odd (orderOf x)) (hr : r ∈ P)
    (h4 : (r * x) ^ 4 = 1) : x = 1 := by
  have key : ∀ k : ℕ, (r * x) ^ k * (x ^ k)⁻¹ ∈ P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hxk : x ^ k ∈ Subgroup.normalizer (P : Set Γ) := Subgroup.pow_mem _ hx k
      have h1 : x ^ k * r * (x ^ k)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxk r).mp hr
      have e : (r * x) ^ (k + 1) * (x ^ (k + 1))⁻¹ =
          ((r * x) ^ k * (x ^ k)⁻¹) * (x ^ k * r * (x ^ k)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact P.mul_mem ih h1
  have h4P : (x ^ 4)⁻¹ ∈ P := by
    have := key 4
    rwa [h4, one_mul] at this
  obtain ⟨j, hj⟩ := hP ⟨(x ^ 4)⁻¹, h4P⟩
  have hj' : (x ^ 4)⁻¹ ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hx4 : x ^ (4 * 2 ^ j) = 1 := by
    rw [pow_mul, ← inv_inj, ← inv_pow, hj', inv_one]
  have hdvd : orderOf x ∣ 2 ^ (j + 2) := by
    have := orderOf_dvd_of_pow_eq_one hx4
    rwa [show 4 * 2 ^ j = 2 ^ (j + 2) by rw [pow_add]; ring] at this
  have hcop : (orderOf x).Coprime (2 ^ (j + 2)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

section Module

variable {U : Type*} [CommGroup U]

theorem mul_inv_mem_of_G2 {G₁ G₂ : Subgroup (MulAut U)} {W₁ W₂ C : Subgroup U}
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hinf : W₁ ⊓ W₂ = C)
    (hW₁ : W₁ = commV G₁ ⊔ C) (hW₂ : commV G₂ ≤ W₂)
    (hinv₁ : ∀ g ∈ G₂, ∀ w ∈ W₁, g w ∈ W₁) (hinv₂ : ∀ g ∈ G₁, ∀ w ∈ W₂, g w ∈ W₂)
    (hC : ∀ g ∈ G₂, ∀ c ∈ C, g c = c) {g : MulAut U} (hg : g ∈ G₂) {w : U} (hw : w ∈ W₁) :
    g w * w⁻¹ ∈ C := by
  have hCW₁ : C ≤ W₁ := hinf ▸ inf_le_left
  have hcomm : ∀ y ∈ commV G₁, g y * y⁻¹ ∈ C := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y _ => g y * y⁻¹ ∈ C) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, ha, v, rfl⟩
      have hav : a v * v⁻¹ ∈ W₁ := hW₁ ▸ Subgroup.mem_sup_left
        (Subgroup.subset_closure ⟨a, ha, v, rfl⟩)
      have hgv : g v * v⁻¹ ∈ W₂ := hW₂ (Subgroup.subset_closure ⟨g, hg, v, rfl⟩)
      have h1 : g (a v * v⁻¹) * (a v * v⁻¹)⁻¹ ∈ W₁ :=
        W₁.mul_mem (hinv₁ g hg _ hav) (W₁.inv_mem hav)
      have h2 : a (g v * v⁻¹) * (g v * v⁻¹)⁻¹ ∈ W₂ :=
        W₂.mul_mem (hinv₂ a ha _ hgv) (W₂.inv_mem hgv)
      have hga : g (a v) = a (g v) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, (hc a ha g hg).symm]
      have e : g (a v * v⁻¹) * (a v * v⁻¹)⁻¹ = a (g v * v⁻¹) * (g v * v⁻¹)⁻¹ := by
        simp only [map_mul, map_inv, hga, mul_inv_rev, inv_inv]
        ac_rfl
      rw [← hinf]
      exact ⟨h1, e ▸ h2⟩
    · simp [C.one_mem]
    · intro x y _ _ hx hy
      have e : g (x * y) * (x * y)⁻¹ = (g x * x⁻¹) * (g y * y⁻¹) := by
        simp only [map_mul, mul_inv_rev]
        ac_rfl
      rw [e]
      exact C.mul_mem hx hy
    · intro x _ hx
      have e : g x⁻¹ * x⁻¹⁻¹ = (g x * x⁻¹)⁻¹ := by
        simp only [map_inv, inv_inv, mul_inv_rev]
        ac_rfl
      rw [e]
      exact C.inv_mem hx
  rw [hW₁] at hw
  obtain ⟨y, hy, c, hc', rfl⟩ := Subgroup.mem_sup.mp hw
  have e : g (y * c) * (y * c)⁻¹ = g y * y⁻¹ := by
    rw [map_mul, hC g hg c hc', mul_inv_rev]
    calc g y * c * (c⁻¹ * y⁻¹) = g y * y⁻¹ * (c * c⁻¹) := by ac_rfl
      _ = g y * y⁻¹ := by rw [mul_inv_cancel, mul_one]
  rw [e]
  exact hcomm y hy

theorem mul_inv_mem_of_eq {W₁ W₂ C : Subgroup U} (hinf : W₁ ⊓ W₂ = C) {g g' : MulAut U}
    (hg₁ : ∀ w ∈ W₁, g w ∈ W₁) (hg₂ : ∀ w ∈ W₂, g w ∈ W₂)
    (hg₁' : ∀ w ∈ W₁, g' w ∈ W₁) (hg₂' : ∀ w ∈ W₂, g' w ∈ W₂)
    {u₁ u₂ : U} (hu₁ : u₁ ∈ W₁) (hu₂ : u₂ ∈ W₂) (h : g (u₁ * u₂) = g' (u₁ * u₂)) :
    g u₁ * (g' u₁)⁻¹ ∈ C := by
  rw [map_mul, map_mul] at h
  have e : g u₁ * (g' u₁)⁻¹ = g' u₂ * (g u₂)⁻¹ := by
    calc g u₁ * (g' u₁)⁻¹ = (g u₁ * g u₂) * ((g u₂)⁻¹ * (g' u₁)⁻¹) := by group
      _ = (g' u₁ * g' u₂) * ((g u₂)⁻¹ * (g' u₁)⁻¹) := by rw [h]
      _ = g' u₁ * (g' u₂ * (g u₂)⁻¹) * (g' u₁)⁻¹ := by group
      _ = g' u₂ * (g u₂)⁻¹ := by rw [mul_comm (g' u₁), mul_inv_cancel_right]
  rw [← hinf]
  refine ⟨W₁.mul_mem (hg₁ u₁ hu₁) (W₁.inv_mem (hg₁' u₁ hu₁)), ?_⟩
  rw [e]
  exact W₂.mul_mem (hg₂' u₂ hu₂) (W₂.inv_mem (hg₂ u₂ hu₂))

omit [CommGroup U] in
theorem mul_inv_mem_trans {Γ : Type*} [Group Γ] {C : Subgroup Γ} {a b c : Γ}
    (h₁ : a * b⁻¹ ∈ C) (h₂ : b * c⁻¹ ∈ C) : a * c⁻¹ ∈ C := by
  have := C.mul_mem h₁ h₂
  rwa [show a * b⁻¹ * (b * c⁻¹) = a * c⁻¹ by group] at this

omit [CommGroup U] in
theorem mul_inv_mem_symm {Γ : Type*} [Group Γ] {C : Subgroup Γ} {a b : Γ} (h : a * b⁻¹ ∈ C) :
    b * a⁻¹ ∈ C := by
  have := C.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem four_ne {G₁ G₂ P : Subgroup (MulAut U)} {W₁ W₂ C : Subgroup U}
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = C)
    (hinv₁ : ∀ g ∈ G₁ ⊔ G₂, ∀ w ∈ W₁, g w ∈ W₁) (hinv₂ : ∀ g ∈ G₁ ⊔ G₂, ∀ w ∈ W₂, g w ∈ W₂)
    (hC : ∀ g ∈ G₁ ⊔ G₂, ∀ c ∈ C, g c = c) (hW₁ : W₁ = commV G₁ ⊔ C) (hW₂ : commV G₂ ≤ W₂)
    (hN1 : ∀ g ∈ G₁, ∀ w ∈ W₁, w ∉ C → g w * w⁻¹ ∈ C → g * g = 1)
    (hP : IsPGroup 2 P) (hPG : P ≤ G₁) {x : MulAut U} (hxG : x ∈ G₁)
    (hxN : x ∈ Subgroup.normalizer (P : Set (MulAut U))) (hodd : Odd (orderOf x)) (hx1 : x ≠ 1)
    {u : U} (hu : u ∉ W₂) (hPu : ∀ p ∈ P, p u = u) {r₁ r₂ s₁ g₂ : MulAut U} (hr₁ : r₁ ∈ P)
    (hr₂ : r₂ ∈ G₂) (hs₁ : s₁ ∈ P) (hg₂ : g₂ ∈ G₂) :
    u ≠ (r₁ * r₂ * x) u ∧ u ≠ ((r₁ * r₂ * x) * (r₁ * r₂ * x)) u ∧
      (r₁ * r₂ * x) u ≠ ((r₁ * r₂ * x) * (r₁ * r₂ * x)) u ∧
      (r₁ * r₂ * x) u ≠ (s₁ * g₂) u ∧ ((r₁ * r₂ * x) * (r₁ * r₂ * x)) u ≠ (s₁ * g₂) u := by
  have hG₁J : G₁ ≤ G₁ ⊔ G₂ := le_sup_left
  have hG₂J : G₂ ≤ G₁ ⊔ G₂ := le_sup_right
  have hCW₂ : C ≤ W₂ := hinf ▸ inf_le_right
  have hT : ∀ g ∈ G₂, ∀ w ∈ W₁, g w * w⁻¹ ∈ C := fun g hg w hw =>
    mul_inv_mem_of_G2 hc hinf hW₁ hW₂ (fun g hg => hinv₁ g (hG₂J hg))
      (fun g hg => hinv₂ g (hG₁J hg)) (fun g hg => hC g (hG₂J hg)) hg hw
  have hmod : ∀ g ∈ G₁, ∀ h ∈ G₂, ∀ w ∈ W₁, (g * h) w * (g w)⁻¹ ∈ C := by
    intro g hg h hh w hw
    have hc' := hT h hh w hw
    have e : (g * h) w = (h w * w⁻¹) * g w := by
      rw [MulAut.mul_apply]
      calc g (h w) = g ((h w * w⁻¹) * w) := by rw [inv_mul_cancel_right]
        _ = g (h w * w⁻¹) * g w := map_mul _ _ _
        _ = (h w * w⁻¹) * g w := by rw [hC g (hG₁J hg) _ hc']
    rw [e, mul_inv_cancel_right]
    exact hc'
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top u)
  have hu₁C : u₁ ∉ C := fun h => hu (W₂.mul_mem (hCW₂ h) hu₂)
  obtain ⟨b, hb⟩ : ∃ b : MulAut U, r₁ * x = b := ⟨_, rfl⟩
  have hbG : b ∈ G₁ := hb ▸ G₁.mul_mem (hPG hr₁) hxG
  have hn : r₁ * r₂ * x = b * r₂ := by
    rw [← hb, mul_assoc, (hc x hxG r₂ hr₂).symm, ← mul_assoc]
  have hnn : (b * r₂) * (b * r₂) = (b * b) * (r₂ * r₂) := by
    have h1 := hc b hbG r₂ hr₂
    calc b * r₂ * (b * r₂) = b * (r₂ * b) * r₂ := by group
      _ = b * (b * r₂) * r₂ := by rw [h1]
      _ = b * b * (r₂ * r₂) := by group
  rw [hn, hnn]
  have hnJ : b * r₂ ∈ G₁ ⊔ G₂ := (G₁ ⊔ G₂).mul_mem (hG₁J hbG) (hG₂J hr₂)
  have hnnJ : b * b * (r₂ * r₂) ∈ G₁ ⊔ G₂ :=
    (G₁ ⊔ G₂).mul_mem (hG₁J (G₁.mul_mem hbG hbG)) (hG₂J (G₂.mul_mem hr₂ hr₂))
  have hmJ : s₁ * g₂ ∈ G₁ ⊔ G₂ := (G₁ ⊔ G₂).mul_mem (hG₁J (hPG hs₁)) (hG₂J hg₂)
  have h1J : (1 : MulAut U) ∈ G₁ ⊔ G₂ := (G₁ ⊔ G₂).one_mem
  have hb4 : (r₁ * x) ^ 4 = (b * b) * (b * b) := by
    rw [hb, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have hb1 : b u₁ * u₁⁻¹ ∉ C := by
    intro h
    have hbb := hN1 b hbG u₁ hu₁ hu₁C h
    exact hx1 (eq_one_of_pow_four hP hxN hodd hr₁ (by rw [hb4, hbb, one_mul]))
  have hb2 : (b * b) u₁ * u₁⁻¹ ∉ C := by
    intro h
    have hbb := hN1 (b * b) (G₁.mul_mem hbG hbG) u₁ hu₁ hu₁C h
    exact hx1 (eq_one_of_pow_four hP hxN hodd hr₁ (by rw [hb4, hbb]))
  have hcomp : ∀ {g g' : MulAut U}, g ∈ G₁ ⊔ G₂ → g' ∈ G₁ ⊔ G₂ →
      g (u₁ * u₂) = g' (u₁ * u₂) → g u₁ * (g' u₁)⁻¹ ∈ C := fun hg hg' h =>
    mul_inv_mem_of_eq hinf (hinv₁ _ hg) (hinv₂ _ hg) (hinv₁ _ hg') (hinv₂ _ hg') hu₁ hu₂ h
  have hn1 : (b * r₂) u₁ * (b u₁)⁻¹ ∈ C := hmod b hbG r₂ hr₂ u₁ hu₁
  have hnn1 : (b * b * (r₂ * r₂)) u₁ * ((b * b) u₁)⁻¹ ∈ C :=
    hmod (b * b) (G₁.mul_mem hbG hbG) (r₂ * r₂) (G₂.mul_mem hr₂ hr₂) u₁ hu₁
  have hm1 : (s₁ * g₂) u₁ * u₁⁻¹ ∈ C := by
    have h1 := hmod s₁ (hPG hs₁) g₂ hg₂ u₁ hu₁
    have h2 : s₁ u₁ * ((1 : MulAut U) u₁)⁻¹ ∈ C :=
      hcomp (hG₁J (hPG hs₁)) h1J (by rw [hPu s₁ hs₁, MulAut.one_apply])
    rw [MulAut.one_apply] at h2
    exact mul_inv_mem_trans h1 h2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h2 : (b * r₂) u₁ * ((1 : MulAut U) u₁)⁻¹ ∈ C :=
      hcomp hnJ h1J (by rw [MulAut.one_apply, ← h])
    rw [MulAut.one_apply] at h2
    exact hb1 (mul_inv_mem_trans (mul_inv_mem_symm hn1) h2)
  · have h2 : (b * b * (r₂ * r₂)) u₁ * ((1 : MulAut U) u₁)⁻¹ ∈ C :=
      hcomp hnnJ h1J (by rw [MulAut.one_apply, ← h])
    rw [MulAut.one_apply] at h2
    exact hb2 (mul_inv_mem_trans (mul_inv_mem_symm hnn1) h2)
  · have h2 : (b * r₂) u₁ * ((b * b * (r₂ * r₂)) u₁)⁻¹ ∈ C := hcomp hnJ hnnJ h
    have h3 : b u₁ * ((b * b) u₁)⁻¹ ∈ C :=
      mul_inv_mem_trans (mul_inv_mem_trans (mul_inv_mem_symm hn1) h2) hnn1
    have e1 : b⁻¹ (b u₁) = u₁ := MulAut.inv_apply_self U b u₁
    have e2 : b⁻¹ ((b * b) u₁) = b u₁ := MulAut.inv_apply_self U b (b u₁)
    have h4 := hC b⁻¹ ((G₁ ⊔ G₂).inv_mem (hG₁J hbG)) _ h3
    rw [map_mul, map_inv, e1, e2] at h4
    rw [← h4] at h3
    exact hb1 (mul_inv_mem_symm h3)
  · have h2 : (b * r₂) u₁ * ((s₁ * g₂) u₁)⁻¹ ∈ C := hcomp hnJ hmJ h
    exact hb1 (mul_inv_mem_trans (mul_inv_mem_trans (mul_inv_mem_symm hn1) h2) hm1)
  · have h2 : (b * b * (r₂ * r₂)) u₁ * ((s₁ * g₂) u₁)⁻¹ ∈ C := hcomp hnnJ hmJ h
    exact hb2 (mul_inv_mem_trans (mul_inv_mem_trans (mul_inv_mem_symm hnn1) h2) hm1)

end Module

end CFSG.Quasithin.H13.A5
