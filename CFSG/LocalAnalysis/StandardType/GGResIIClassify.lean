module

public import CFSG.LocalAnalysis.StandardType.GGResIINonegDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Inv

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[expose] def ggDeg (K : Matrix ι ι ℤ) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => j ≠ i ∧ K i j = -1).card

@[expose] def ggInv (K : Matrix ι ι ℤ) : ℕ × ℕ × ℕ × ℕ :=
  (∑ i, ggDeg K i, (Finset.univ.filter fun i => ggDeg K i = 3).card,
    (Finset.univ.filter fun i => 4 ≤ ggDeg K i).card,
    (Finset.univ.filter fun ij : ι × ι =>
      ij.1 ≠ ij.2 ∧ K ij.1 ij.2 = -1 ∧ ggDeg K ij.1 = 3 ∧ ggDeg K ij.2 = 1).card)

theorem ggDeg_submatrix (K : Matrix κ κ ℤ) (σ : ι ≃ κ) (i : ι) :
    ggDeg (K.submatrix σ σ) i = ggDeg K (σ i) := by
  rw [ggDeg, ggDeg, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (σ.subtypeEquiv fun j => by simp [σ.injective.ne_iff])

theorem ggInv_submatrix (K : Matrix κ κ ℤ) (σ : ι ≃ κ) : ggInv (K.submatrix σ σ) = ggInv K := by
  simp only [ggInv, ggDeg_submatrix]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact Equiv.sum_comp σ (fun i => ggDeg K i)
  · simp only
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (σ.subtypeEquiv fun i => Iff.rfl)
  · simp only
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (σ.subtypeEquiv fun i => Iff.rfl)
  · simp only
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr ((σ.prodCongr σ).subtypeEquiv fun ij => ?_)
    simp [Matrix.submatrix_apply, σ.injective.ne_iff]

end Inv

@[expose] def ggKmat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib : Fin n) (r : Fin n → Bool) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = ib then (if j = ib then 2 else if r j then -1 else 0)
    else if j = ib then (if r i then -1 else 0) else C i j

theorem ggResII_leaf_cut {Λ : Type} {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) (hconn : GGDeletedConnected ML b) {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    {ib : Fin n} (hib : e ib = b) (S : Finset (Fin n)) (j₁ j₂ : Fin n) (h₁ : j₁ ∈ S)
    (h₂ : j₂ ∉ S) (hj₁ : j₁ ≠ ib) (hj₂ : j₂ ≠ ib)
    (hcut : ∀ a ∈ S, ∀ c, c ∉ S → c ≠ ib → C a c = 0) : False := by
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  have hpath := hconn ⟨e j₁, hne j₁ hj₁⟩ ⟨e j₂, hne j₂ hj₂⟩
  have key : ∀ w : {i : Λ // i ≠ b},
      Relation.ReflTransGen (fun u v : {i : Λ // i ≠ b} => u ≠ v ∧ ML.M u v ≠ 2)
        ⟨e j₁, hne j₁ hj₁⟩ w → e.symm w.val ∈ S := by
    intro w hw
    induction hw with
    | refl => simpa using h₁
    | @tail u v _ huv ih =>
      by_contra hv
      have hvb : e.symm v.val ≠ ib := fun h => v.2 (by
        have := congrArg e h
        rwa [e.apply_symm_apply, hib] at this)
      have h0 := hcut _ ih _ hv hvb
      rw [← hCe, e.apply_symm_apply, e.apply_symm_apply] at h0
      have huv' : u.val ≠ v.val := fun h => huv.1 (Subtype.ext h)
      rcases hCL.2 u.val v.val huv' with ⟨hm, -, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩
      · exact huv.2 hm
      · rw [h0] at h1; norm_num at h1
      · rw [h0] at h1; exact lt_irrefl 0 h1
      · rw [h0] at h1; exact lt_irrefl 0 h1
  have := key _ hpath
  simp only [Equiv.symm_apply_apply] at this
  exact h₂ this

theorem ggResII_arow {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p))
    (hKtype : GGResIINonegType CK) {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = C i j) (hCsl : C.IsSimplyLaced) (hCdiag : ∀ i, C i i = 2)
    {ib : Fin n} (hib : e ib = b)
    (targets : List (ℕ × ℕ × ℕ × ℕ)) (allowed : List (Fin n))
    (htA : 2 ≤ n → ggInv (CartanMatrix.A n) ∈ targets)
    (htD : 5 ≤ n → Odd n → ggInv (CartanMatrix.D n) ∈ targets)
    (htE : ∀ hn : 6 = n, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm) (Fin.cast hn.symm))
      ∈ targets)
    (hcert : ∀ r : Fin n → Bool, ggInv (ggKmat C ib r) ∈ targets →
      ∃ ic ∈ allowed, ic ≠ ib ∧ ∀ j, j ≠ ib → r j = decide (j = ic)) :
    ∃ ic ∈ allowed, ic ≠ ib ∧
      (∀ (j : Fin n) (hj : e j ≠ b), CK none (some ⟨e j, hj⟩) = if j = ic then -1 else 0) ∧
      (∀ (j : Fin n) (hj : e j ≠ b), CK (some ⟨e j, hj⟩) none = if j = ic then -1 else 0) ∧
      CK none none = 2 := by
  classical
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  let ψ : Fin n ≃ Option {i : Λ // i ≠ b} :=
    { toFun := fun j => if hj : j = ib then none else some ⟨e j, hne j hj⟩
      invFun := fun o => match o with
        | none => ib
        | some l => e.symm l.val
      left_inv := fun j => by
        by_cases hj : j = ib
        · simp [hj]
        · simp [hj]
      right_inv := fun o => by
        cases o with
        | none => simp
        | some l =>
          have : e.symm l.val ≠ ib := fun h => l.2 (by
            have := congrArg e h
            rwa [e.apply_symm_apply, hib] at this)
          simp [this] }
  have hψib : ψ ib = none := by simp [ψ]
  have hψ : ∀ j (hj : j ≠ ib), ψ j = some ⟨e j, hne j hj⟩ := fun j hj => by simp [ψ, hj]
  have hfacts : ∃ (m : ℕ) (e' : Fin m ≃ Option {i : Λ // i ≠ b}) (C' : Matrix (Fin m) (Fin m) ℤ),
      (∀ i j, CK (e' i) (e' j) = C' i j) ∧ C'.IsSimplyLaced ∧ (∀ i, C' i i = 2) ∧
        (∀ i j, C' i j = C' j i) ∧ ggInv C' ∈ targets := by
    have hcard : Fintype.card (Option {i : Λ // i ≠ b}) = n := by
      rw [Fintype.card_congr (Equiv.optionSubtypeNe b), ← Fintype.card_congr e, Fintype.card_fin]
    rcases hKtype with ⟨m, e', hm, hC'⟩ | ⟨m, e', hm, hodd, hC'⟩ | ⟨e', hC'⟩
    · have hmn : m = n := by rw [← hcard, ← Fintype.card_fin m, Fintype.card_congr e']
      subst hmn
      exact ⟨m, e', _, hC', CartanMatrix.isSimplyLaced_A m, fun i => by simp [CartanMatrix.A],
        fun i j => (CartanMatrix.A_isSymm m).apply j i, htA hm⟩
    · have hmn : m = n := by rw [← hcard, ← Fintype.card_fin m, Fintype.card_congr e']
      subst hmn
      exact ⟨m, e', _, hC', CartanMatrix.isSimplyLaced_D m, fun i => by simp [CartanMatrix.D],
        fun i j => (CartanMatrix.D_isSymm (n := m)).apply j i, htD hm hodd⟩
    · have hmn : 6 = n := by rw [← hcard, ← Fintype.card_fin 6, Fintype.card_congr e']
      subst hmn
      refine ⟨6, e', _, hC', CartanMatrix.isSimplyLaced_E 6, fun i => by simp [CartanMatrix.E],
        fun i j => (CartanMatrix.E_isSymm 6).apply j i, ?_⟩
      simpa using htE rfl
  obtain ⟨m, e', C', hC', hsl', hdiag', hsymm', hinv'⟩ := hfacts
  have hKsl : ∀ o o', o ≠ o' → CK o o' = 0 ∨ CK o o' = -1 := by
    intro o o' hoo
    rw [← e'.apply_symm_apply o, ← e'.apply_symm_apply o', hC']
    exact hsl' (fun h => hoo (by rw [← e'.apply_symm_apply o, ← e'.apply_symm_apply o', h]))
  have hKdiag : ∀ o, CK o o = 2 := fun o => by rw [← e'.apply_symm_apply o, hC', hdiag']
  have hKsymm : ∀ o o', CK o o' = CK o' o := fun o o' => by
    rw [← e'.apply_symm_apply o, ← e'.apply_symm_apply o', hC', hC', hsymm']
  have hKL : ∀ i j (hi : i ≠ ib) (hj : j ≠ ib),
      CK (some ⟨e i, hne i hi⟩) (some ⟨e j, hne j hj⟩) = C i j := by
    intro i j hi hj
    by_cases hij : i = j
    · subst hij
      rw [hKdiag, hCdiag]
    · have h1 := hK (some ⟨e i, hne i hi⟩) (some ⟨e j, hne j hj⟩)
      simp only [Option.map_some] at h1
      rw [hL, hCe] at h1
      have hoo : (some ⟨e i, hne i hi⟩ : Option {i : Λ // i ≠ b}) ≠ some ⟨e j, hne j hj⟩ :=
        fun h => hij (e.injective (by simpa using h))
      rcases hKsl _ _ hoo with hk | hk <;> rcases hCsl hij with hc | hc
      · rw [hk, hc]
      · exfalso
        rw [hk, hc] at h1
        simp at h1
      · exfalso
        rw [hk, hc] at h1
        simp at h1
      · rw [hk, hc]
  let r : Fin n → Bool := fun j => if hj : j = ib then false else decide (CK none (ψ j) = -1)
  have hKmat : ggKmat C ib r = CK.submatrix ψ ψ := by
    funext i j
    simp only [ggKmat, Matrix.submatrix_apply]
    by_cases hi : i = ib
    · subst hi
      rw [hψib]
      by_cases hj : j = i
      · subst hj; rw [if_pos rfl, if_pos rfl, hψib, hKdiag]
      · rw [if_pos rfl, if_neg hj, hψ j hj]
        simp only [r, dif_neg hj, hψ j hj]
        rcases hKsl none (some ⟨e j, hne j hj⟩) (by simp) with h0 | h0 <;> simp [h0]
    · rw [if_neg hi, hψ i hi]
      by_cases hj : j = ib
      · subst hj
        rw [if_pos rfl, hψib, hKsymm]
        simp only [r, dif_neg hi, hψ i hi]
        rcases hKsl none (some ⟨e i, hne i hi⟩) (by simp) with h0 | h0 <;> simp [h0]
      · rw [if_neg hj, hψ j hj, hKL i j hi hj]
  have hinv : ggInv (ggKmat C ib r) ∈ targets := by
    rw [hKmat, ggInv_submatrix]
    have : ggInv C' = ggInv CK := by
      rw [show C' = CK.submatrix e' e' from funext fun i => funext fun j => (hC' i j).symm,
        ggInv_submatrix]
    rwa [← this]
  obtain ⟨ic, hic, hbc, hr⟩ := hcert r hinv
  have hrow : ∀ (j : Fin n) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then -1 else 0 := by
    intro j hj
    have hj' : j ≠ ib := fun h => hj (by rw [h, hib])
    have := hr j hj'
    simp only [r, dif_neg hj', hψ j hj'] at this
    rcases hKsl none (some ⟨e j, hj⟩) (by simp) with h0 | h0
    · rw [h0] at this ⊢
      by_cases hjc : j = ic
      · simp [hjc] at this
      · simp [hjc]
    · rw [h0] at this ⊢
      by_cases hjc : j = ic
      · simp [hjc]
      · simp [hjc] at this
  refine ⟨ic, hic, hbc, hrow, fun j hj => by rw [hKsymm]; exact hrow j hj, hKdiag none⟩

end CFSG.StandardType
