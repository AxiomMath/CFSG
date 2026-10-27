module

public import CFSG.LocalAnalysis.StandardType.GGTWModelPsi

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nTM_finRotate_last {N : ℕ} (hN : 2 ≤ N) :
    (finRotate (N - 1)) (⟨N - 2, by omega⟩ : Fin (N-1)) = ⟨0, by omega⟩ := by
  ext
  simp only [finRotate_apply, Fin.val_add, Fin.val_mk, Fin.val_zero]
  norm_num
  have h : N - 2 + 1 = N - 1 := by omega
  rw [h, Nat.mod_self]

private noncomputable def l05nTMu {p N : ℕ} (v : GGTWE p N) : Fin (N-1) → ZMod p :=
  fun k => if k.val = 0 then 0 else v ⟨k.val - 1, by omega⟩

private lemma l05nTM_dot_step {p N : ℕ} (c : Fin (N-1)) (hc : c.val + 3 ≤ N)
    (v : GGTWE p N) (j : Fin (N-1)) :
    ggTWα p N c j * v j =
      (CartanMatrix.A (N-1) c ((finRotate (N-1)) j) : ZMod p) *
        l05nTMu v ((finRotate (N-1)) j) := by
  by_cases hk : j.val + 2 = N
  · have hσ : (finRotate (N-1)) j = ⟨0, by omega⟩ := by
      have hj : j = (⟨N - 2, by omega⟩ : Fin (N-1)) := Fin.ext (by simp; omega)
      rw [hj]
      exact l05nTM_finRotate_last (by omega)
    have hα : ggTWα p N c j = 0 := by simp [ggTWα, hk]
    rw [hα, hσ]
    simp [l05nTMu]
  · have hσ : (finRotate (N-1)) j = ⟨j.val + 1, by have := j.isLt; omega⟩ :=
      l05nTM_finRotate_succ j hk
    rw [l05nTM_alpha_coeff c j hk, hσ]
    have hu : l05nTMu v ⟨j.val + 1, by have := j.isLt; omega⟩ = v j := by
      simp only [l05nTMu]
      rw [if_neg (by simp : ¬ (j.val + 1 = 0))]
      rfl
    rw [hu]

private lemma l05nTM_dot_eq_cartan {p N : ℕ} (c : Fin (N-1)) (hc : c.val + 3 ≤ N)
    (v : GGTWE p N) :
    ggTWdot (ggTWα p N c) v =
      ∑ k : Fin (N-1), (CartanMatrix.A (N-1) c k : ZMod p) * l05nTMu v k := by
  rw [ggTWdot, ggDepAdot]
  rw [Finset.sum_congr rfl (fun j _ => l05nTM_dot_step c hc v j)]
  exact Equiv.sum_comp (finRotate (N-1))
    (fun k => (CartanMatrix.A (N-1) c k : ZMod p) * l05nTMu v k)

private lemma l05nTM_rec {p N : ℕ} (v : GGTWE p N) (c : Fin (N-1)) (hc1 : 1 ≤ c.val)
    (hc : c.val + 3 ≤ N) (h : ggTWdot (ggTWα p N c) v = 0) :
    2 * v ⟨c.val - 1, by omega⟩ - v ⟨c.val, by omega⟩
      - (if 2 ≤ c.val then v ⟨c.val - 2, by omega⟩ else 0) = 0 := by
  have hd := l05nTM_dot_eq_cartan c hc v
  have hsum : ∑ k : Fin (N-1), (CartanMatrix.A (N-1) c k : ZMod p) * l05nTMu v k = 0 := by
    rw [← hd]; exact h
  rw [cartanA_row (l05nTMu v) c] at hsum
  have hc1lt : c.val < N - 1 := c.isLt
  have hcp1 : c.val + 1 < N - 1 := by omega
  have hcm1 : c.val - 1 < N - 1 := by omega
  simp only [dif_pos hc1lt, dif_pos hcp1, dif_pos hcm1] at hsum
  rw [if_neg (by omega : ¬ c.val = 0)] at hsum
  have hu1 : l05nTMu v ⟨c.val, hc1lt⟩ = v ⟨c.val - 1, by omega⟩ := by
    simp only [l05nTMu]
    rw [if_neg (by omega : ¬ c.val = 0)]
    try rfl
  have hu2 : l05nTMu v ⟨c.val + 1, hcp1⟩ = v ⟨c.val, by omega⟩ := by
    simp only [l05nTMu]
    rw [if_neg (by omega : ¬ c.val + 1 = 0)]
    try rfl
  have hu3 : l05nTMu v ⟨c.val - 1, hcm1⟩ =
      (if 2 ≤ c.val then v ⟨c.val - 2, by omega⟩ else 0) := by
    by_cases h2 : 2 ≤ c.val
    · rw [if_pos h2]
      simp only [l05nTMu]
      rw [if_neg (by omega : ¬ c.val - 1 = 0)]
      rfl
    · rw [if_neg h2]
      have hzero : c.val - 1 = 0 := by omega
      rw [show (⟨c.val - 1, hcm1⟩ : Fin (N-1)) = ⟨0, by omega⟩ from Fin.ext hzero]
      simp [l05nTMu]
  rw [hu1, hu2, hu3] at hsum
  exact hsum

private lemma l05nTM_dot_zero {p N : ℕ} (hN : 5 ≤ N) (v : GGTWE p N) :
    ggTWdot (ggTWα p N (⟨0, by omega⟩ : Fin (N-1))) v = - v ⟨0, by omega⟩ := by
  rw [ggTWdot, ggDepAdot]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (N-1))]
  · have h0 : ¬ ((⟨0, by omega⟩ : Fin (N-1)).val + 2 = N) := by simp; omega
    have h1 : ¬ ((⟨0, by omega⟩ : Fin (N-1)).val + 1 = 0) := by simp
    simp [ggTWα, h0, h1]
  · intro b _ hb
    have hb0 : b.val ≠ 0 := by intro h; exact hb (Fin.ext h)
    by_cases hbN : b.val + 2 = N
    · simp [ggTWα, hbN]
    · have hb1 : ¬ (b.val + 1 = 0) := by omega
      have hb2 : ¬ (b.val + 2 = 0 ∨ b.val = 0) := by omega
      simp [ggTWα, hbN, hb0, hb1, hb2]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma l05nTM_ends_coord {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) (v : GGTWE p N)
    (hv : ∀ c : Fin (N-1), ggTWInJ N .ends c.val → ggTWdot (ggTWα p N c) v = 0)
    (k : Fin (N-1)) (hk : k.val + 2 ≠ N) :
    v k = ((k.val : ZMod p) + 1) * v ⟨0, by omega⟩ := by
  let i0 : Fin (N-1) := ⟨0, by omega⟩
  have hnat : ∀ m, m + 2 ≠ N → ∀ (hm : m < N - 1),
      v ⟨m, hm⟩ = ((m : ZMod p) + 1) * v i0 := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero =>
      intro hk hm
      simp [i0]
    | one =>
      intro hk hm
      have hJ : ggTWInJ N .ends 1 := by simp [ggTWInJ]; omega
      have hrec := l05nTM_rec v ⟨1, hm⟩ (by simp) (by simp only [Fin.val_mk]; omega) (hv ⟨1, hm⟩ hJ)
      simp only [Fin.val_mk] at hrec
      rw [if_neg (by omega : ¬ 2 ≤ (1:ℕ))] at hrec
      have h0 : v ⟨0, by omega⟩ = ((0 : ZMod p) + 1) * v i0 := by simp [i0]
      rw [h0] at hrec
      linear_combination -hrec
    | more n ih0 ih1 =>
      intro hk hm
      have hn : n < N - 1 := by omega
      have hn1 : n + 1 < N - 1 := by omega
      have hJ : ggTWInJ N .ends (n+2) := by simp [ggTWInJ]; omega
      have hrec := l05nTM_rec v ⟨n+2, hm⟩ (by simp) (by simp only [Fin.val_mk]; omega)
        (hv ⟨n+2, hm⟩ hJ)
      simp only [Fin.val_mk] at hrec
      rw [show (⟨(n+2) - 1, by omega⟩ : Fin (N-1)) = ⟨n+1, hn1⟩ from Fin.ext (by simp)] at hrec
      rw [show (⟨(n+2) - 2, by omega⟩ : Fin (N-1)) = ⟨n, hn⟩ from Fin.ext (by simp)] at hrec
      rw [if_pos (by omega : 2 ≤ n+2)] at hrec
      rw [ih1 (by omega) hn1, ih0 (by omega) hn] at hrec
      push_cast at hrec ⊢
      linear_combination -hrec
      all_goals (push_cast; ring)
  have hklt : k.val < N - 1 := k.isLt
  exact hnat k.val hk hklt

private lemma l05nTM_adj_coord {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) (v : GGTWE p N)
    (hv : ∀ c : Fin (N-1), ggTWInJ N .adj c.val → ggTWdot (ggTWα p N c) v = 0)
    (k : Fin (N-1)) (hk : k.val + 4 ≤ N) : v k = 0 := by
  have hnat : ∀ m, m + 4 ≤ N → ∀ (hm : m < N - 1), v ⟨m, hm⟩ = 0 := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero =>
      intro hk hm
      have hdot := hv ⟨0, hm⟩ (by simp [ggTWInJ]; omega)
      rw [l05nTM_dot_zero hN v] at hdot
      simpa using neg_eq_zero.mp hdot
    | one =>
      intro hk hm
      have hJ : ggTWInJ N .adj 1 := by simp [ggTWInJ]; omega
      have hrec := l05nTM_rec v ⟨1, hm⟩ (by simp) (by simp only [Fin.val_mk]; omega) (hv ⟨1, hm⟩ hJ)
      simp only [Fin.val_mk] at hrec
      rw [if_neg (by omega : ¬ 2 ≤ (1:ℕ))] at hrec
      have h0 : v ⟨0, by omega⟩ = 0 := by
        have hdot := hv ⟨0, by omega⟩ (by simp [ggTWInJ]; omega)
        rw [l05nTM_dot_zero hN v] at hdot
        simpa using neg_eq_zero.mp hdot
      rw [h0] at hrec
      linear_combination -hrec
    | more n ih0 ih1 =>
      intro hk hm
      have hn : n < N - 1 := by omega
      have hn1 : n + 1 < N - 1 := by omega
      have hJ : ggTWInJ N .adj (n+2) := by simp [ggTWInJ]; omega
      have hrec := l05nTM_rec v ⟨n+2, hm⟩ (by simp) (by simp only [Fin.val_mk]; omega)
        (hv ⟨n+2, hm⟩ hJ)
      simp only [Fin.val_mk] at hrec
      rw [show (⟨(n+2) - 1, by omega⟩ : Fin (N-1)) = ⟨n+1, hn1⟩ from Fin.ext (by simp)] at hrec
      rw [show (⟨(n+2) - 2, by omega⟩ : Fin (N-1)) = ⟨n, hn⟩ from Fin.ext (by simp)] at hrec
      rw [if_pos (by omega : 2 ≤ n+2)] at hrec
      rw [ih1 (by omega) hn1, ih0 (by omega) hn] at hrec
      push_cast at hrec ⊢
      linear_combination -hrec
      all_goals (push_cast; ring)
  have hklt : k.val < N - 1 := k.isLt
  exact hnat k.val hk hklt

theorem ggTW_model_iso {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (hdim : Module.finrank (ZMod p) V = N - 1)
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (hF : GGDepAFrame p N h α x) :
    ∃ θ : V ≃ₗ[ZMod p] GGTWE p N, θ x = ggTWx p N ∧ (∀ i, θ (h i) = ggTWh p N i) ∧
      ∀ i v, α i v = ggTWdot (ggTWα p N i) (θ v) := by

  haveI : FiniteDimensional (ZMod p) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; omega)
  have hinj : Function.Injective (l05nTMψ (p := p) (N := N) h x) := l05nTM_ψ_inj hN hF
  have hfin : Module.finrank (ZMod p) (Fin (N - 1) → ZMod p) = Module.finrank (ZMod p) V := by
    rw [Module.finrank_fin_fun, hdim]
  let e : (Fin (N - 1) → ZMod p) ≃ₗ[ZMod p] V :=
    (l05nTMψ h x).linearEquivOfInjective hinj hfin
  have he : ∀ w, e w = l05nTMψ h x w := fun w =>
    LinearMap.linearEquivOfInjective_apply hinj hfin w
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · rw [LinearEquiv.symm_apply_eq, he, l05nTM_x_single hN, l05nTMψ_single]
    rw [dif_pos (show (⟨N - 2, by omega⟩ : Fin (N - 1)).val + 2 = N by
      simp only [Fin.val_mk]; omega)]
  · intro i
    rw [LinearEquiv.symm_apply_eq, he]
    by_cases hi : i.val = 0
    · have hieq : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi)
      rw [hieq]
      exact (l05nTM_ψ_ggTWh_zero hN hF).symm
    · exact (l05nTMψ_ggTWh_succ (p := p) (N := N) h x i hi).symm
  · intro i v
    rw [← l05nTM_alpha_ψ hF i (e.symm v), ← he (e.symm v), LinearEquiv.apply_symm_apply]

theorem ggTW_fixedJ {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 5 ≤ N)
    (pos : GGTWPos) (v : GGTWE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val → ggTWdot (ggTWα p N c) v = 0) :
    ∃ lam mu : ZMod p, v = lam • ggTWx p N + mu • ggTWz p N pos := by

  cases pos with
  | ends =>
    refine ⟨v ⟨N-2, by omega⟩, v ⟨0, by omega⟩, ?_⟩
    funext j
    by_cases hj : j.val + 2 = N
    · have hj' : j = ⟨N-2, by omega⟩ := Fin.ext (by simp; omega)
      rw [hj']
      simp [ggTWx, ggTWz, show N - 2 + 2 = N by omega]
    · have hcoord := l05nTM_ends_coord hN v hv j hj
      rw [hcoord]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [ggTWx, ggTWz, if_neg hj]
      simp [if_neg hj]
      ring
  | adj =>
    refine ⟨v ⟨N-2, by omega⟩, v ⟨N-3, by omega⟩, ?_⟩
    funext j
    by_cases hjL : j.val + 2 = N
    · have hj' : j = ⟨N-2, by omega⟩ := Fin.ext (by simp; omega)
      rw [hj']
      simp [ggTWx, ggTWz, show N - 2 + 2 = N by omega, show ¬ (N - 2 + 3 = N) by omega]
    · by_cases hjK : j.val + 3 = N
      · have hj' : j = ⟨N-3, by omega⟩ := Fin.ext (by simp; omega)
        rw [hj']
        simp [ggTWx, ggTWz, show N - 3 + 3 = N by omega, show ¬ (N - 3 + 2 = N) by omega]
      · have hzero : v j = 0 := l05nTM_adj_coord hN v hv j (by omega)
        rw [hzero]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [ggTWx, ggTWz, if_neg hjL, if_neg hjK]
        ring

end CFSG.StandardType
