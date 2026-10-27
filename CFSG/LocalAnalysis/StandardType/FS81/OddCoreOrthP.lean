module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def sgnOn {k : ℕ} (T : Finset (Fin k)) : Fin k → ZMod 3 := fun i => if i ∈ T then -1 else 1

theorem isSign_sgnOn {k : ℕ} (T : Finset (Fin k)) : IsSign (sgnOn T) := by
  intro i
  unfold sgnOn
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem sign_mul_self {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k) : s i * s i = 1 := by
  rcases hs i with h | h <;> rw [h] <;> rfl

theorem prod_sgnOn {k : ℕ} (T : Finset (Fin k)) : ∏ i, sgnOn T i = (-1) ^ T.card := by
  unfold sgnOn
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

theorem prod_succ_sgnOn {n : ℕ} (T : Finset (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∉ T) :
    ∏ i : Fin n, sgnOn T i.succ = (-1) ^ T.card := by
  rw [← prod_sgnOn T, Fin.prod_univ_succ]
  unfold sgnOn
  rw [if_neg h0, one_mul]

theorem sgnOn_mem_evenFix0 {n : ℕ} (T : Finset (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∉ T)
    (heven : Even T.card) : spMat 1 (sgnOn T) ∈ evenFix0 n := by
  refine ⟨1, sgnOn T, isSign_sgnOn T, ⟨rfl, ?_, ?_⟩, rfl⟩
  · unfold sgnOn
    rw [if_neg h0]
  · rw [prod_succ_sgnOn T h0, heven.neg_one_pow]

theorem eq_zero_of_mulVec_sgnOn {k : ℕ} {T : Finset (Fin k)} {v : Fin k → ZMod 3}
    (h : spMat 1 (sgnOn T) *ᵥ v = v) {i : Fin k} (hi : i ∈ T) : v i = 0 := by
  have h' := congrFun h i
  simp only [spMat_mulVec, Equiv.Perm.one_symm, Equiv.Perm.one_apply] at h'
  rw [show sgnOn T i = -1 from if_pos hi, neg_one_mul] at h'
  exact eq_zero_of_neg_eq_self h'

theorem mulVec_swap_sgnOn {k : ℕ} {a b : Fin k} {T : Finset (Fin k)} (ha : a ∉ T) (hb : b ∉ T)
    {v : Fin k → ZMod 3} (h : spMat (Equiv.swap a b) (sgnOn T) *ᵥ v = v) :
    (∀ i ∈ T, v i = 0) ∧ v a = v b := by
  have hc : ∀ i, sgnOn T ((Equiv.swap a b).symm i) * v ((Equiv.swap a b).symm i) = v i := by
    intro i
    have := congrFun h i
    simp only [spMat_mulVec] at this
    exact this
  refine ⟨fun i hi => ?_, ?_⟩
  · have hia : i ≠ a := fun h => ha (h ▸ hi)
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    have := hc i
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hia hib,
      show sgnOn T i = -1 from if_pos hi, neg_one_mul] at this
    exact eq_zero_of_neg_eq_self this
  · have := hc a
    rw [Equiv.symm_swap, Equiv.swap_apply_left, show sgnOn T b = 1 from if_neg hb, one_mul] at this
    exact this.symm

theorem spMat_congr {k : ℕ} {σ σ' : Equiv.Perm (Fin k)} {s s' : Fin k → ZMod 3} (h1 : σ = σ')
    (h2 : ∀ j, s j = s' j) : spMat σ s = spMat σ' s' := by
  subst h1
  rw [show s = s' from funext h2]

theorem orth_eq_one_of_fix {n : ℕ} (hn : 3 ≤ n) {Xg Mg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hC : ∀ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 → (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoFix0 n)
    (hW : ∀ A ∈ evenFix0 n, ∃ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = A)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hMp : ∀ m ∈ Mg, m ^ p = 1)
    {m : GL (Fin (n + 1)) (ZMod 3)} (hm : m ∈ Mg)
    (he : (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    m = 1 := by
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hsq : ∀ x ∈ Mg, x * x = 1 → x = 1 := by
    intro x hx hxx
    have h1 : x ^ p.gcd 2 = 1 := pow_gcd_eq_one.mpr ⟨hMp x hx, by rw [pow_two]; exact hxx⟩
    rwa [hcop, pow_one] at h1
  obtain ⟨π, s, hs, ⟨hπ0, hs0⟩, hmat⟩ := hC m (hMX hm) he
  have hδ : ∀ T : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ T → Even T.card →
      ∀ i, sgnOn T i = sgnOn T (π.symm i) := by
    intro T hT0 hTe i
    obtain ⟨x, hxX, hx⟩ := hW _ (sgnOn_mem_evenFix0 T hT0 hTe)
    have hxx : x * x = 1 := by
      apply Units.ext
      rw [Units.val_mul, hx, Units.val_one]
      exact spMat_mul_self 1 _ (by rw [one_mul]) (fun j => sign_mul_self (isSign_sgnOn T) j)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    set ε : Fin (n + 1) → ZMod 3 := fun i => sgnOn T i * sgnOn T (π.symm i) with hε
    set d := x * m * x⁻¹ * m⁻¹ with hd
    have hdM : d ∈ Mg := Mg.mul_mem (hMn x hxX m hm) (Mg.inv_mem hm)
    have hdmat : (d : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = spMat 1 ε := by
      have hconj : spMat 1 (sgnOn T) * spMat π s * spMat 1 (sgnOn T) = spMat 1 ε * spMat π s := by
        rw [spMat_mul, spMat_mul, spMat_mul]
        refine spMat_congr (by simp) (fun j => ?_)
        simp only [Equiv.Perm.coe_one, id, hε, Equiv.symm_apply_apply]
        ring
      have hmm : (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *
          ((m⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hd, hxinv, Units.val_mul, Units.val_mul, Units.val_mul, hx, hmat, hconj, ← hmat,
        mul_assoc, hmm, mul_one]
    have hdd : d * d = 1 := by
      apply Units.ext
      rw [Units.val_mul, hdmat, Units.val_one]
      refine spMat_mul_self 1 ε (by rw [one_mul]) (fun j => ?_)
      simp only [Equiv.Perm.coe_one, id, hε]
      have h1 := sign_mul_self (isSign_sgnOn T) j
      have h2 := sign_mul_self (isSign_sgnOn T) (π.symm j)
      calc sgnOn T j * sgnOn T (π.symm j) * (sgnOn T j * sgnOn T (π.symm j)) =
          (sgnOn T j * sgnOn T j) * (sgnOn T (π.symm j) * sgnOn T (π.symm j)) := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    have hd1 := hsq d hdM hdd
    have hε1 : spMat 1 ε = 1 := by rw [← hdmat, hd1, Units.val_one]
    have hεi : ε i = 1 := by
      have := congrFun (congrFun hε1 i) i
      simpa [spMat_apply, Matrix.one_apply] using this
    have h1 := sign_mul_self (isSign_sgnOn T) i
    calc sgnOn T i = sgnOn T i * (sgnOn T i * sgnOn T (π.symm i)) := by
          rw [show sgnOn T i * sgnOn T (π.symm i) = ε i from rfl, hεi, mul_one]
      _ = sgnOn T (π.symm i) := by rw [← mul_assoc, h1, one_mul]
  have hπ : π = 1 := by
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, π j ≠ j := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    have hj0 : j ≠ 0 := fun h => hj (h ▸ hπ0)
    have hπj0 : π j ≠ 0 := fun h => hj0 (π.injective (h.trans hπ0.symm))
    obtain ⟨l, hl⟩ : ∃ l : Fin (n + 1), l ≠ 0 ∧ l ≠ j ∧ l ≠ π j := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (Fin (n + 1))) ⊆ {0, j, π j} := by
        intro x _
        by_cases hx0 : x = 0
        · simp [hx0]
        · by_cases hxj : x = j
          · simp [hxj]
          · simp [h x hx0 hxj]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      have h3 : ({0, j, π j} : Finset (Fin (n + 1))).card ≤ 3 := Finset.card_le_three
      omega
    have hT0 : (0 : Fin (n + 1)) ∉ ({j, l} : Finset (Fin (n + 1))) := by
      simp [hj0.symm, hl.1.symm]
    have hTe : Even ({j, l} : Finset (Fin (n + 1))).card := by
      rw [Finset.card_pair hl.2.1.symm]
      exact even_two
    have := hδ {j, l} hT0 hTe (π j)
    rw [Equiv.symm_apply_apply] at this
    unfold sgnOn at this
    rw [if_neg (by simp [hj, hl.2.2.symm]), if_pos (by simp)] at this
    exact absurd this (by decide)
  refine hsq m hm (Units.ext ?_)
  rw [Units.val_mul, hmat, hπ, Units.val_one]
  exact spMat_mul_self 1 s (by rw [one_mul]) (fun j => sign_mul_self hs j)

theorem orth_inverts {n : ℕ} (hn : 3 ≤ n) {Xg Mg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hC : ∀ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 → (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) ∈ monoFix0 n)
    (hW : ∀ A ∈ evenFix0 n, ∃ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = A)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hMc : ∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMp : ∀ m ∈ Mg, m ^ p = 1)
    {σ : GL (Fin (n + 1)) (ZMod 3)} (hσX : σ ∈ Xg) (hσ2 : σ * σ = 1)
    (hσe : (σ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    {w : Fin (n + 1) → ZMod 3}
    (hfix : ∀ v, (σ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v →
      ∃ c d : ZMod 3, v = c • Pi.single 0 1 + d • w)
    {m : GL (Fin (n + 1)) (ZMod 3)} (hm : m ∈ Mg) : σ * m * σ⁻¹ = m⁻¹ :=
  inv_of_centralizer_trivial hMn hMc hσX hσ2 (fun m' hm' hcomm =>
    orth_eq_one_of_fix hn hC hW hMX hMn hp (by omega) hMp hm'
      (mulVec_fix_of_commute hp hp5 (hMp m' hm') hcomm hσe hfix)) hm

theorem eq_bot_of_inverting {Γ : Type} [Group Γ] {M : Subgroup Γ} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hMp : ∀ m ∈ M, m ^ p = 1)
    {σt : Γ} (hinv : ∀ m ∈ M, σt * m * σt⁻¹ = m⁻¹) (hcent : ∀ m ∈ M, σt * m = m * σt) :
    M = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  have h1 : m⁻¹ = m := by
    rw [← hinv m hm, hcent m hm, mul_assoc, mul_inv_cancel, mul_one]
  have hsq : m ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [← h1]; exact mul_inv_cancel m
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have := pow_gcd_eq_one.mpr ⟨hMp m hm, hsq⟩
  rw [hcop, pow_one] at this
  rw [this]
  exact Subgroup.one_mem _

theorem cent_mul {Γ : Type} [Group Γ] {M : Subgroup Γ} {g h : Γ} (hg : ∀ m ∈ M, g * m = m * g)
    (hh : ∀ m ∈ M, h * m = m * h) : ∀ m ∈ M, g * h * m = m * (g * h) := by
  intro m hm
  rw [mul_assoc, hh m hm, ← mul_assoc, hg m hm, mul_assoc]

theorem cent_conj {Γ : Type} [Group Γ] {X M : Subgroup Γ}
    (hMn : ∀ g ∈ X, ∀ m ∈ M, g * m * g⁻¹ ∈ M) {g y : Γ} (hg : ∀ m ∈ M, g * m = m * g)
    (hy : y ∈ X) : ∀ m ∈ M, y * g * y⁻¹ * m = m * (y * g * y⁻¹) := by
  intro m hm
  have hm' : y⁻¹ * m * y⁻¹⁻¹ ∈ M := hMn y⁻¹ (X.inv_mem hy) m hm
  rw [inv_inv] at hm'
  have := hg _ hm'
  calc y * g * y⁻¹ * m = y * (g * (y⁻¹ * m * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * m * y) * g) * y⁻¹ := by rw [this]
    _ = m * (y * g * y⁻¹) := by group

theorem cent_of_inverts {Γ : Type} [Group Γ] {M : Subgroup Γ} {a b : Γ}
    (ha : ∀ m ∈ M, a * m * a⁻¹ = m⁻¹) (hb : ∀ m ∈ M, b * m * b⁻¹ = m⁻¹) :
    ∀ m ∈ M, a * b * m = m * (a * b) := by
  intro m hm
  have h1 : b * m = m⁻¹ * b := by rw [← hb m hm]; group
  have h2 : a * m⁻¹ = m * a := by
    have := ha m hm
    rw [show a * m⁻¹ = (a * m * a⁻¹)⁻¹ * a by group, this, inv_inv]
  rw [mul_assoc, h1, ← mul_assoc, h2, mul_assoc]

end CFSG.StandardType.FrameRoute.FS81

end
