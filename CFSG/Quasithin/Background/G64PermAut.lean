module

public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin Equiv Equiv.Perm

section Swap

variable {α : Type*} [DecidableEq α]

theorem swap_mul_swap_comm_of_ne {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  have hdis : (swap a b).Disjoint (swap c d) := by
    intro x
    by_cases hx : x = a ∨ x = b
    · right
      rcases hx with rfl | rfl
      · exact swap_apply_of_ne_of_ne hac had
      · exact swap_apply_of_ne_of_ne hbc hbd
    · left
      push Not at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2
  exact hdis.commute.eq

theorem share_of_not_commute_swap {a b c d : α}
    (h : swap a b * swap c d ≠ swap c d * swap a b) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra hcon
  push Not at hcon
  exact h (swap_mul_swap_comm_of_ne hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2)

theorem exists_of_not_commute_swap {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
    (h : swap a b * swap c d ≠ swap c d * swap a b) :
    ∃ p q r : α, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ swap a b = swap p q ∧ swap c d = swap p r := by
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun e => h (by rw [e])
    exact ⟨a, b, d, hab, hcd, hbd, rfl, rfl⟩
  by_cases had : a = d
  · subst had
    have hbc : b ≠ c := fun e => h (by rw [e, swap_comm])
    exact ⟨a, b, c, hab, Ne.symm hcd, hbc, rfl, swap_comm _ _⟩
  by_cases hbc : b = c
  · subst hbc
    exact ⟨b, a, d, Ne.symm hab, hcd, had, swap_comm _ _, rfl⟩
  by_cases hbd : b = d
  · subst hbd
    exact ⟨b, a, c, Ne.symm hab, Ne.symm hcd, hac, swap_comm _ _, swap_comm _ _⟩
  exact absurd (swap_mul_swap_comm_of_ne hac had hbc hbd) h

theorem swap_mul_swap_mul_swap_of_ne {p q r : α} (hpr : p ≠ r) (hqr : q ≠ r) :
    swap p q * swap p r * swap p q = swap q r := by
  have h := (swap_apply_apply (swap p q) p r).symm
  rw [swap_apply_left, swap_apply_of_ne_of_ne hpr.symm hqr.symm, swap_inv] at h
  exact h

end Swap

theorem closure_swap_zero {n : ℕ} (i₀ : Fin n) :
    Subgroup.closure (Set.range fun j : Fin n => swap i₀ j) = ⊤ := by
  rw [eq_top_iff, ← closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  by_cases hx : x = i₀
  · subst hx
    exact Subgroup.subset_closure ⟨y, rfl⟩
  by_cases hy : y = i₀
  · subst hy
    exact Subgroup.subset_closure ⟨x, swap_comm _ _⟩
  have h := swap_mul_swap_mul_swap_of_ne (p := i₀) (Ne.symm hy) hxy
  rw [← h]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
    exact Subgroup.subset_closure ⟨_, rfl⟩

theorem exists_eq_conj_of_isSwap {n : ℕ} (hn : 3 ≤ n) (φ : Perm (Fin n) →* Perm (Fin n))
    (hinj : Function.Injective φ) (hsw : ∀ σ : Perm (Fin n), σ.IsSwap → (φ σ).IsSwap) :
    ∃ f : Perm (Fin n), ∀ σ, φ σ = f * σ * f⁻¹ := by
  classical
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin n := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [hi₀, hi₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂, Fin.ext_iff]
  set t : Fin n → Perm (Fin n) := fun j => φ (swap i₀ j) with ht
  have hnc : ∀ j k, j ≠ i₀ → k ≠ i₀ → j ≠ k → t j * t k ≠ t k * t j := by
    intro j k hj hk hjk e
    rw [ht, ← map_mul, ← map_mul] at e
    have := congrArg (fun σ : Perm (Fin n) => σ i₀) (hinj e)
    simp only [Perm.mul_apply, swap_apply_left] at this
    rw [swap_apply_of_ne_of_ne hk (Ne.symm hjk), swap_apply_of_ne_of_ne hj hjk] at this
    exact hjk this.symm
  have hts : ∀ j, j ≠ i₀ → (t j).IsSwap := fun j hj => hsw _ ⟨i₀, j, Ne.symm hj, rfl⟩
  obtain ⟨a₁, b₁, hab₁, he₁⟩ := hts i₁ (Ne.symm h01)
  obtain ⟨a₂, b₂, hab₂, he₂⟩ := hts i₂ (Ne.symm h02)
  have hnc12 := hnc i₁ i₂ (Ne.symm h01) (Ne.symm h02) h12
  rw [he₁, he₂] at hnc12
  obtain ⟨p, q, r, hpq, hpr, hqr, hq, hr⟩ := exists_of_not_commute_swap hab₁ hab₂ hnc12
  rw [hq] at he₁
  rw [hr] at he₂
  have hclaim : ∀ j, j ≠ i₀ → ∃ q', q' ≠ p ∧ t j = swap p q' := by
    intro j hj
    by_cases hj1 : j = i₁
    · subst hj1
      exact ⟨q, Ne.symm hpq, he₁⟩
    by_cases hj2 : j = i₂
    · subst hj2
      exact ⟨r, Ne.symm hpr, he₂⟩
    obtain ⟨x, y, hxy, hej⟩ := hts j hj
    have hn1 := hnc i₁ j (Ne.symm h01) hj (Ne.symm hj1)
    have hn2 := hnc i₂ j (Ne.symm h02) hj (Ne.symm hj2)
    rw [he₁, hej] at hn1
    rw [he₂, hej] at hn2
    by_cases hpx : p = x
    · subst hpx
      exact ⟨y, Ne.symm hxy, hej⟩
    by_cases hpy : p = y
    · subst hpy
      exact ⟨x, hxy, by rw [hej, swap_comm]⟩
    exfalso
    have hxyqr : swap x y = swap q r := by
      rcases share_of_not_commute_swap hn1 with h1 | h1 | h1 | h1
      · exact absurd h1 hpx
      · exact absurd h1 hpy
      · rcases share_of_not_commute_swap hn2 with h2 | h2 | h2 | h2
        · exact absurd h2 hpx
        · exact absurd h2 hpy
        · exact absurd (h1.trans h2.symm) hqr
        · rw [h1, h2]
      · rcases share_of_not_commute_swap hn2 with h2 | h2 | h2 | h2
        · exact absurd h2 hpx
        · exact absurd h2 hpy
        · rw [h1, h2, swap_comm]
        · exact absurd (h1.trans h2.symm) hqr
    have hconj : t i₁ * t i₂ * t i₁ = t j := by
      rw [he₁, he₂, swap_mul_swap_mul_swap_of_ne hpr hqr, hej, hxyqr]
    rw [ht, ← map_mul, ← map_mul, swap_mul_swap_mul_swap_of_ne h02 h12] at hconj
    have := congrArg (fun σ : Perm (Fin n) => σ i₀) (hinj hconj)
    simp only [swap_apply_left] at this
    rw [swap_apply_of_ne_of_ne h01 h02] at this
    exact hj this.symm
  choose! g hg using hclaim
  set f : Fin n → Fin n := fun j => if j = i₀ then p else g j with hf
  have hfinj : Function.Injective f := by
    intro j k hjk
    by_cases hj : j = i₀ <;> by_cases hk : k = i₀
    · rw [hj, hk]
    · simp [hf, hj, hk] at hjk
      exact absurd hjk.symm (hg k hk).1
    · simp [hf, hj, hk] at hjk
      exact absurd hjk (hg j hj).1
    · simp [hf, hj, hk] at hjk
      have e : φ (swap i₀ j) = φ (swap i₀ k) := by
        rw [show φ (swap i₀ j) = t j from rfl, show φ (swap i₀ k) = t k from rfl, (hg j hj).2,
          (hg k hk).2, hjk]
      have := congrArg (fun σ : Perm (Fin n) => σ i₀) (hinj e)
      simp only [swap_apply_left] at this
      exact this
  set F : Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj) with hF
  have hFi₀ : F i₀ = p := by simp [hF, hf]
  have hFj : ∀ j, j ≠ i₀ → F j = g j := fun j hj => by simp [hF, hf, hj]
  refine ⟨F, fun σ => ?_⟩
  have heq : φ = (MulAut.conj F).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense (closure_swap_zero i₀) ?_
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i₀
    · have h1 : swap i₀ j = 1 := by rw [hj, swap_self]; rfl
      show φ (swap i₀ j) = F * swap i₀ j * F⁻¹
      rw [h1, map_one, mul_one, mul_inv_cancel]
    · show φ (swap i₀ j) = F * swap i₀ j * F⁻¹
      rw [← swap_apply_apply, hFi₀, hFj j hj]
      exact (hg j hj).2
  rw [heq]
  rfl

variable {V : Type*} [CommGroup V]

theorem sq_eq_one_of_rankOne (hV2 : ∀ v : V, v ^ 2 = 1) {z : MulAut V} {w : V}
    (h : ∀ v, z v * v⁻¹ = 1 ∨ z v * v⁻¹ = w) : z ^ 2 = 1 := by
  have hzw : z w = w := by
    rcases h w with h1 | h1
    · exact mul_inv_eq_one.1 h1
    · have : z w = w * w := by
        calc z w = (z w * w⁻¹) * w := by group
          _ = w * w := by rw [h1]
      rw [← sq, hV2] at this
      have hw : w = 1 := z.injective (by rw [this, map_one])
      rw [this, hw]
  ext v
  rw [sq, MulAut.mul_apply, MulAut.one_apply]
  rcases h v with h1 | h1
  · have hv : z v = v := mul_inv_eq_one.1 h1
    rw [hv, hv]
  · have hv : z v = w * v := by rw [← h1]; group
    rw [hv, map_mul, hzw, hv, ← mul_assoc, ← sq, hV2, one_mul]

theorem apply_eq_of_commute {x c : MulAut V} (hx : Nat.card (commV (Subgroup.zpowers x)) = 2)
    (hcx : c * x = x * c) {y : V} (hy : y ∈ commV (Subgroup.zpowers x)) : c y = y := by
  have hmap : (commV (Subgroup.zpowers x)).map c.toMonoidHom = commV (Subgroup.zpowers x) := by
    rw [← G6.commV_zpowers_conj, show c * x * c⁻¹ = x by rw [hcx]; group]
  have hcy : c y ∈ commV (Subgroup.zpowers x) := by
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  by_cases hy1 : y = 1
  · rw [hy1, map_one]
  rcases eq_one_or_eq_of_card_two hx hy hy1 hcy with h1 | h1
  · exact absurd (c.injective (h1.trans (map_one c).symm)) hy1
  · exact h1

theorem exists_eq_on_of_normalizes {H : Subgroup (MulAut V)} {n : ℕ} (hn : 3 ≤ n)
    (θ : ↥H ≃* Perm (Fin n))
    (htr : ∀ σ : Perm (Fin n), σ.IsSwap →
      Nat.card (commV (Subgroup.zpowers ((θ.symm σ : ↥H) : MulAut V))) = 2)
    (hsw : ∀ (x : MulAut V) (hx : x ∈ H), Nat.card (commV (Subgroup.zpowers x)) = 2 →
      (θ ⟨x, hx⟩).IsSwap)
    {g : MulAut V} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ∃ k ∈ H, ∀ v ∈ commV H, g v = k v := by
  classical
  let cg : ↥H →* ↥H :=
    { toFun := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
      map_one' := by ext1; simp
      map_mul' := fun x y => by ext1; simp [mul_assoc] }
  let φ : Perm (Fin n) →* Perm (Fin n) :=
    θ.toMonoidHom.comp (cg.comp θ.symm.toMonoidHom)
  have hφ : ∀ σ, φ σ = θ ⟨g * (θ.symm σ : MulAut V) * g⁻¹, hg _ (θ.symm σ).2⟩ := fun _ => rfl
  have hinj : Function.Injective φ := by
    intro σ τ e
    rw [hφ, hφ] at e
    have h1 := congrArg Subtype.val (θ.injective e)
    simp only [mul_left_inj, mul_right_inj] at h1
    exact θ.symm.injective (Subtype.ext h1)
  have hsw' : ∀ σ : Perm (Fin n), σ.IsSwap → (φ σ).IsSwap := by
    intro σ hσ
    rw [hφ]
    apply hsw
    rw [G6.card_commV_zpowers_conj]
    exact htr σ hσ
  obtain ⟨f, hf⟩ := exists_eq_conj_of_isSwap hn φ hinj hsw'
  set k : ↥H := θ.symm f with hk
  refine ⟨k, k.2, ?_⟩
  have hconj : ∀ x : ↥H, g * (x : MulAut V) * g⁻¹ = (k : MulAut V) * x * (k : MulAut V)⁻¹ := by
    intro x
    have h1 := hf (θ x)
    rw [hφ, MulEquiv.symm_apply_apply] at h1
    have h2 : (⟨g * (x : MulAut V) * g⁻¹, hg _ x.2⟩ : ↥H) = k * x * k⁻¹ := by
      apply θ.injective
      rw [h1, map_mul, map_mul, map_inv, hk, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  set c : MulAut V := (k : MulAut V)⁻¹ * g with hc
  have hcomm : ∀ x ∈ H, c * x = x * c := by
    intro x hx
    have h1 := hconj ⟨x, hx⟩
    rw [hc]
    calc (k : MulAut V)⁻¹ * g * x = (k : MulAut V)⁻¹ * (g * x * g⁻¹) * g := by group
      _ = (k : MulAut V)⁻¹ * ((k : MulAut V) * x * (k : MulAut V)⁻¹) * g := by rw [h1]
      _ = x * ((k : MulAut V)⁻¹ * g) := by group
  have hH : H ≤ Subgroup.closure
      {x : MulAut V | ∃ σ : Perm (Fin n), σ.IsSwap ∧ x = ((θ.symm σ : ↥H) : MulAut V)} := by
    intro x hx
    have h1 : θ ⟨x, hx⟩ ∈ Subgroup.closure {σ : Perm (Fin n) | σ.IsSwap} := by
      rw [closure_isSwap]
      trivial
    have h2 := Subgroup.mem_map_of_mem (H.subtype.comp θ.symm.toMonoidHom) h1
    rw [MonoidHom.map_closure] at h2
    have h3 : (H.subtype.comp θ.symm.toMonoidHom) (θ ⟨x, hx⟩) = x := by simp
    rw [h3] at h2
    refine (Subgroup.closure_mono ?_) h2
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩
  intro v hv
  have hle : commV H ≤ fixV (Subgroup.zpowers c) := by
    refine (G6.commV_mono hH).trans (G6.commV_closure_le ?_)
    rintro _ ⟨σ, hσ, rfl⟩ w
    have hx := htr σ hσ
    have hcx := hcomm _ (θ.symm σ).2
    rw [fixV_zpowers_iff]
    exact apply_eq_of_commute hx hcx (G6.mem_commV_of_mem (Subgroup.mem_zpowers _) w)
  have := (fixV_zpowers_iff.1 (hle hv))
  rw [hc, MulAut.mul_apply] at this
  calc g v = (k : MulAut V) ((k : MulAut V)⁻¹ (g v)) := by simp
    _ = (k : MulAut V) v := by rw [this]

end CFSG.Quasithin.G64
