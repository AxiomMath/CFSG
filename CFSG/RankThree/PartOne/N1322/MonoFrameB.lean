module

public import CFSG.RankThree.PartOne.N1322.MonoFrameA

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv

variable {K : Type*} [Field K]

structure FrameB (d : CoreData K) : Prop where
  n4 : d.n = 4
  eps0 : eps 0 ∈ d.D ∧ eps 0 ∈ d.Lm
  eps1 : eps 1 ∈ d.D ∧ eps 1 ∈ d.Lm
  a01 : ∃ r : Kˣ, aref 0 1 r ∈ d.D ∧ aref 0 1 r ∈ d.Lm ∧
    ∀ s : Kˣ, aref 0 1 s ∈ d.Lm → s = r ∨ s = -r

theorem diag_refl_in_L (h2 : (2 : K) ≠ 0) {a : Fin 3 → Kˣ}
    (hr : IsRefl (mono 1 a : GL (Fin 3) K)) (ha2 : a 2 = 1) : a = epsU 0 ∨ a = epsU 1 := by
  rcases isRefl_diag h2 hr with h0 | h1 | h2'
  · exact Or.inl h0
  · exact Or.inr h1
  · exfalso
    have : a 2 = -1 := by rw [h2']; simp [epsU]
    rw [ha2] at this
    exact neg_one_ne_one h2 this.symm

theorem eps_mul_eps :
    (eps 0 * eps 1 : GL (Fin 3) K) = mono 1 (fun j => epsU 0 j * epsU 1 j) := by
  rw [eps, eps, mono_mul]
  exact congrArg₂ mono (one_mul _) (funext fun j => by simp)

theorem swap01_zpow_eq_one {k : ℤ} (h : (swap (0 : Fin 3) 1) ^ k = 1) : ∃ m, k = 2 * m := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · exact ⟨m, hm⟩
  · exfalso
    rw [hm, swap01_zpow_odd] at h
    revert h
    decide

theorem frame_b_core (h2 : (2 : K) ≠ 0) {d : CoreData K}
    (hL2 : ∀ l ∈ d.Lm, ∃ σ a, l = mono σ a ∧ σ 2 = 2 ∧ a 2 = 1)
    (hrefl : ∀ g ∈ d.D, IsRefl g)
    (hcover : ∀ x : d.Lm, IsNCInv x → (x : GL (Fin 3) K) ∈ d.D)
    {ρ t₀ : d.Lm} (hg : DihGens d.Lm d.n ρ t₀)
    (hρ : HasPerm (ρ : GL (Fin 3) K) (swap 0 1)) (e : ℤ)
    (h0 : HasPerm ((t₀ * ρ ^ e : d.Lm) : GL (Fin 3) K) 1) : FrameB d := by
  have hperm : ∀ k : ℤ, HasPerm ((t₀ * ρ ^ k : d.Lm) : GL (Fin 3) K)
      ((swap (0 : Fin 3) 1) ^ (k - e)) := by
    intro k
    have h1 : t₀ * ρ ^ k = (t₀ * ρ ^ e) * ρ ^ (k - e) := by
      rw [mul_assoc, ← zpow_add]
      exact congrArg (fun m : ℤ => t₀ * ρ ^ m) (by ring)
    rw [h1]
    have := h0.mul (hρ.zpow (k - e))
    simpa using this
  obtain ⟨t1, ht1⟩ : ∃ t1 : d.Lm, t1 = t₀ * ρ ^ e := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ t2 : d.Lm, t2 = t₀ * ρ ^ (e + 2) := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ t3 : d.Lm, t3 = t₀ * ρ ^ (e + 1) := ⟨_, rfl⟩
  have hp1 : HasPerm (t1 : GL (Fin 3) K) 1 := by rw [ht1]; exact h0
  have hp2 : HasPerm (t2 : GL (Fin 3) K) 1 := by
    have := hperm (e + 2)
    rw [show e + 2 - e = 2 by ring, zpow_two, swap_mul_self] at this
    rw [ht2]; exact this
  have hp3 : HasPerm (t3 : GL (Fin 3) K) (swap 0 1) := by
    have := hperm (e + 1)
    rw [show e + 1 - e = 1 by ring, zpow_one] at this
    rw [ht3]; exact this
  have hρ2 : HasPerm ((ρ ^ (2 : ℤ) : d.Lm) : GL (Fin 3) K) 1 := by
    have := hρ.zpow 2
    rw [zpow_two (swap (0 : Fin 3) 1), swap_mul_self] at this
    simpa using this
  have h4 : ρ ^ (4 : ℤ) = 1 := by
    have hcomm : ((t₀ * ρ ^ e : d.Lm) : GL (Fin 3) K) * ((ρ ^ (2 : ℤ) : d.Lm) : GL (Fin 3) K) =
        ((ρ ^ (2 : ℤ) : d.Lm) : GL (Fin 3) K) * ((t₀ * ρ ^ e : d.Lm) : GL (Fin 3) K) :=
      HasPerm.comm_of_one h0 hρ2
    have hc : (t₀ * ρ ^ e) * ρ ^ (2 : ℤ) = ρ ^ (2 : ℤ) * (t₀ * ρ ^ e) := Subtype.ext hcomm
    have l1 : (t₀ * ρ ^ e) * ρ ^ (2 : ℤ) = t₀ * ρ ^ (e + 2) := by rw [mul_assoc, ← zpow_add]
    have l2 : ρ ^ (2 : ℤ) * (t₀ * ρ ^ e) = t₀ * ρ ^ (e - 2) := by
      rw [← mul_assoc, hg.rt, mul_assoc, ← zpow_add]
      exact congrArg (fun m : ℤ => t₀ * ρ ^ m) (by ring)
    rw [l1, l2] at hc
    have h5 := mul_left_cancel hc
    calc ρ ^ (4 : ℤ) = ρ ^ (e + 2) * (ρ ^ (e - 2))⁻¹ := by
          rw [← zpow_neg, ← zpow_add]
          exact congrArg (fun m : ℤ => ρ ^ m) (by ring)
      _ = 1 := by rw [h5, mul_inv_cancel]
  have hn4 : d.n = 4 := by
    have hdvd := (hg.zpow_eq_one_iff 4).mp h4
    have h5 := Int.le_of_dvd (by norm_num) hdvd
    have h6 := hg.four
    omega
  have nc1 : IsNCInv t1 := (hg.nc_iff t1).mpr ⟨e, ht1⟩
  have nc2 : IsNCInv t2 := (hg.nc_iff t2).mpr ⟨e + 2, ht2⟩
  have nc3 : IsNCInv t3 := (hg.nc_iff t3).mpr ⟨e + 1, ht3⟩
  have hD1 := hcover t1 nc1
  have hD2 := hcover t2 nc2
  have hD3 := hcover t3 nc3
  have hdiag : ∀ x : d.Lm, HasPerm (x : GL (Fin 3) K) 1 → (x : GL (Fin 3) K) ∈ d.D →
      (x : GL (Fin 3) K) = eps 0 ∨ (x : GL (Fin 3) K) = eps 1 := by
    intro x hx hxD
    obtain ⟨-, a, hxa, ha2⟩ := Lmono hL2 x hx
    have hr : IsRefl (mono 1 a : GL (Fin 3) K) := hxa ▸ hrefl _ hxD
    rcases diag_refl_in_L h2 hr ha2 with h | h
    · left; rw [hxa, h]; rfl
    · right; rw [hxa, h]; rfl
  have e1 := hdiag t1 hp1 hD1
  have e2 := hdiag t2 hp2 hD2
  have hne12 : (t1 : GL (Fin 3) K) ≠ t2 := by
    intro h
    have h' : t1 = t2 := Subtype.ext h
    rw [ht1, ht2] at h'
    have h5 := mul_left_cancel h'
    apply hg.rho_sq_ne_one
    calc ρ ^ (2 : ℤ) = ρ ^ (e + 2) * (ρ ^ e)⁻¹ := by
          rw [← zpow_neg, ← zpow_add]
          exact congrArg (fun m : ℤ => ρ ^ m) (by ring)
      _ = 1 := by rw [← h5, mul_inv_cancel]
  have hprod : ((ρ ^ (2 : ℤ) : d.Lm) : GL (Fin 3) K) = (t1 : GL (Fin 3) K) * t2 := by
    have := hg.refl_mul e (e + 2)
    rw [← ht1, ← ht2, show e + 2 - e = 2 by ring] at this
    rw [← this]
    rfl
  have hcases : ((t1 : GL (Fin 3) K) = eps 0 ∧ (t2 : GL (Fin 3) K) = eps 1) ∨
      ((t1 : GL (Fin 3) K) = eps 1 ∧ (t2 : GL (Fin 3) K) = eps 0) := by
    rcases e1 with h1 | h1 <;> rcases e2 with h2' | h2'
    · exact absurd (h1.trans h2'.symm) hne12
    · exact Or.inl ⟨h1, h2'⟩
    · exact Or.inr ⟨h1, h2'⟩
    · exact absurd (h1.trans h2'.symm) hne12
  have hρ2eps : ((ρ ^ (2 : ℤ) : d.Lm) : GL (Fin 3) K) = eps 0 * eps 1 := by
    rw [hprod]
    rcases hcases with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · rw [h1, h2']
    · rw [h1, h2']
      exact mono_one_comm (epsU 1) (epsU 0)
  have hepsD : eps 0 ∈ d.D ∧ eps 0 ∈ d.Lm ∧ eps 1 ∈ d.D ∧ eps 1 ∈ d.Lm := by
    rcases hcases with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · exact ⟨h1 ▸ hD1, h1 ▸ t1.2, h2' ▸ hD2, h2' ▸ t2.2⟩
    · exact ⟨h2' ▸ hD2, h2' ▸ t2.2, h1 ▸ hD1, h1 ▸ t1.2⟩
  obtain ⟨-, b, hb, hb2⟩ := Lmono hL2 t3 hp3
  have hbsq : b 1 * b 0 = 1 := by
    have hsq : (t3 : GL (Fin 3) K) * t3 = 1 := by
      have := congrArg Subtype.val nc3.1
      simpa using this
    rw [hb] at hsq
    have := (mono_sq_eq_one hsq).2 0
    simpa using this
  have hbU : b = aU 0 1 (b 0) := aU_eq_of_swap01 hb2 hbsq
  have ht3eq : (t3 : GL (Fin 3) K) = aref 0 1 (b 0) := by
    rw [hb, aref]
    exact congrArg (mono (swap 0 1)) hbU
  have hrot : ∀ k : ℤ, ρ ^ k = ρ ^ (k % 4) := fun k => zpow_eq_zpow_emod k h4
  have hdiagL : ∀ x : d.Lm, HasPerm (x : GL (Fin 3) K) 1 →
      x = 1 ∨ x = ρ ^ (2 : ℤ) ∨ x = t1 ∨ x = t2 := by
    intro x hx
    obtain ⟨k, hk | hk⟩ := hg.all x
    · have hpk : HasPerm (x : GL (Fin 3) K) ((swap (0 : Fin 3) 1) ^ k) := by
        rw [hk]; simpa using hρ.zpow k
      obtain ⟨m, hm⟩ := swap01_zpow_eq_one (hpk.unique hx)
      rw [hk, hrot k]
      have hk4 : k % 4 = 0 ∨ k % 4 = 2 := by omega
      rcases hk4 with h | h
      · left; rw [h, zpow_zero]
      · right; left; rw [h]
    · have hpk : HasPerm (x : GL (Fin 3) K) ((swap (0 : Fin 3) 1) ^ (k - e)) := by
        rw [hk]; exact hperm k
      obtain ⟨m, hm⟩ := swap01_zpow_eq_one (hpk.unique hx)
      have hx' : x = t1 * ρ ^ (k - e) := by
        rw [hk, ht1, mul_assoc, ← zpow_add]
        exact congrArg (fun m : ℤ => t₀ * ρ ^ m) (by ring)
      rw [hrot (k - e)] at hx'
      have hk4 : (k - e) % 4 = 0 ∨ (k - e) % 4 = 2 := by omega
      rcases hk4 with h | h
      · right; right; left; rw [hx', h, zpow_zero, mul_one]
      · right; right; right
        rw [hx', h, ht1, ht2, mul_assoc, ← zpow_add]
  refine ⟨hn4, ⟨hepsD.1, hepsD.2.1⟩, ⟨hepsD.2.2.1, hepsD.2.2.2⟩, b 0, ?_, ?_, ?_⟩
  · rw [← ht3eq]; exact hD3
  · rw [← ht3eq]; exact t3.2
  · intro s hs
    have hδ := aref_mul_aref (K := K) (by decide : (0 : Fin 3) ≠ 1) (b 0) s
    obtain ⟨q, hq⟩ : ∃ q : Kˣ, q = (b 0)⁻¹ * s := ⟨_, rfl⟩
    rw [← hq] at hδ
    have hδL : (aref 0 1 (b 0) : GL (Fin 3) K) * aref 0 1 s ∈ d.Lm :=
      d.Lm.mul_mem (ht3eq ▸ t3.2) hs
    obtain ⟨δ, hδdef⟩ : ∃ δ : d.Lm, (δ : GL (Fin 3) K) = aref 0 1 (b 0) * aref 0 1 s :=
      ⟨⟨_, hδL⟩, rfl⟩
    have hδ' : (δ : GL (Fin 3) K) = mono 1 (aU 0 1 q) := by rw [hδdef, hδ]
    have key : ∀ c : Fin 3 → Kˣ, (δ : GL (Fin 3) K) = mono 1 c → q = c 0 ∧ q⁻¹ = c 1 := by
      intro c hc
      have hh := (mono_injective (hδ'.symm.trans hc)).2
      constructor
      · have := congrFun hh 0
        rw [aU_left] at this
        exact this
      · have := congrFun hh 1
        rw [aU_right (by decide : (0 : Fin 3) ≠ 1)] at this
        exact this
    have hs_of_q : s = b 0 * q := by rw [hq, mul_inv_cancel_left]
    rcases hdiagL δ ⟨aU 0 1 q, hδ'⟩ with h | h | h | h
    ·
      left
      have hc := key (fun _ => 1) (by rw [h]; exact mono_one.symm)
      rw [hs_of_q, hc.1]
      simp
    ·
      right
      have hc := key (fun j => epsU 0 j * epsU 1 j) (by
        rw [h, hρ2eps]; exact eps_mul_eps)
      have hq' : q = -1 := by
        rw [hc.1]; simp [epsU]
      rw [hs_of_q, hq']
      simp
    ·
      exfalso
      rcases e1 with h1 | h1
      · have hc := key (epsU 0) ((congrArg Subtype.val h).trans h1)
        have hq1 : q = 1 := inv_eq_one.mp (by rw [hc.2]; simp [epsU])
        rw [hc.1] at hq1
        exact neg_one_ne_one h2 (by simpa [epsU] using hq1)
      · have hc := key (epsU 1) ((congrArg Subtype.val h).trans h1)
        have hq1 : q = 1 := by rw [hc.1]; simp [epsU]
        have h3 := hc.2
        rw [hq1, inv_one] at h3
        exact neg_one_ne_one h2 (by simpa [epsU] using h3.symm)
    ·
      exfalso
      rcases e2 with h1 | h1
      · have hc := key (epsU 0) ((congrArg Subtype.val h).trans h1)
        have hq1 : q = 1 := inv_eq_one.mp (by rw [hc.2]; simp [epsU])
        rw [hc.1] at hq1
        exact neg_one_ne_one h2 (by simpa [epsU] using hq1)
      · have hc := key (epsU 1) ((congrArg Subtype.val h).trans h1)
        have hq1 : q = 1 := by rw [hc.1]; simp [epsU]
        have h3 := hc.2
        rw [hq1, inv_one] at h3
        exact neg_one_ne_one h2 (by simpa [epsU] using h3.symm)

theorem frame_dichotomy (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X)
    (hc2 : ∃ μ : K, μ ≠ 0 ∧ d.c = μ • Pi.single 2 1)
    (hL2 : ∀ l ∈ d.Lm, ∃ σ a, l = mono σ a ∧ σ 2 = 2 ∧ a 2 = 1) : FrameB d := by
  have hcover := hcover_of_hyp h2 h
  obtain ⟨e⟩ := h.Ldih
  obtain ⟨ρ, t₀, hg⟩ := exists_gens h.n_mem e
  obtain ⟨σρ, hσρ⟩ : ∃ σ, HasPerm (ρ : GL (Fin 3) K) σ := by
    obtain ⟨σ, a, hxa, -, -⟩ := hL2 ρ ρ.2
    exact ⟨σ, a, hxa⟩
  obtain ⟨σt, hσt⟩ : ∃ σ, HasPerm (t₀ : GL (Fin 3) K) σ := by
    obtain ⟨σ, a, hxa, -, -⟩ := hL2 t₀ t₀.2
    exact ⟨σ, a, hxa⟩
  have hσρ2 : σρ 2 = 2 := (Lmono hL2 ρ hσρ).1
  have hσt2 : σt 2 = 2 := (Lmono hL2 t₀ hσt).1
  rcases perm_fix2 σρ hσρ2 with rfl | rfl
  · rcases perm_fix2 σt hσt2 with rfl | rfl
    · exfalso
      exact hg.not_comm (Subtype.ext (HasPerm.comm_of_one hσt hσρ))
    · exact (frame_a_false h2 h hm hc2 hL2 hcover hg hσρ hσt).elim
  · rcases perm_fix2 σt hσt2 with rfl | rfl
    · exact frame_b_core h2 hL2 h.refl hcover hg hσρ 0 (by simpa using hσt)
    · refine frame_b_core h2 hL2 h.refl hcover hg hσρ 1 ?_
      have := hσt.mul hσρ
      rw [swap_mul_self] at this
      simpa using this

end CFSG.RankThree.PartOne.N1322
