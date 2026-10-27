module

public import CFSG.Quasithin.Background.HMultFix

public section

namespace CFSG.Quasithin.H.Mult

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def blockSub {k : ℕ} (R : Submodule K (Fin k → K)) :
    Subgroup (StdMod (Fin k × ι) K) where
  carrier := {v | ∀ i, (fun j => Multiplicative.toAdd v (j, i)) ∈ R}
  one_mem' := fun i => by
    have h : (fun j => Multiplicative.toAdd (1 : StdMod (Fin k × ι) K) (j, i)) = 0 := by
      funext j
      simp
    rw [h]
    exact R.zero_mem
  mul_mem' := by
    intro a b ha hb i
    have h : (fun j => Multiplicative.toAdd (a * b) (j, i)) =
        (fun j => Multiplicative.toAdd a (j, i)) + fun j => Multiplicative.toAdd b (j, i) := by
      funext j
      simp
    rw [h]
    exact R.add_mem (ha i) (hb i)
  inv_mem' := by
    intro a ha i
    have h : (fun j => Multiplicative.toAdd a⁻¹ (j, i)) =
        -fun j => Multiplicative.toAdd a (j, i) := by
      funext j
      simp
    rw [h]
    exact R.neg_mem (ha i)

omit [Fintype ι] [DecidableEq ι] in
theorem blockSub_mono {k : ℕ} {R R' : Submodule K (Fin k → K)} (h : R ≤ R') :
    blockSub (ι := ι) R ≤ blockSub (ι := ι) R' := fun _ hv i => h (hv i)

omit [DecidableEq ι] in
theorem natCard_blockSub [Finite K] {k : ℕ} (R : Submodule K (Fin k → K)) :
    Nat.card ↥(blockSub (ι := ι) R) = Nat.card ↥R ^ Fintype.card ι := by
  let f : ↥(blockSub (ι := ι) R) → (ι → ↥R) := fun v i =>
    ⟨fun j => Multiplicative.toAdd (v.1 : StdMod (Fin k × ι) K) (j, i), v.2 i⟩
  let g : (ι → ↥R) → ↥(blockSub (ι := ι) R) := fun x =>
    ⟨Multiplicative.ofAdd fun p : Fin k × ι => (x p.2 : ↥R).1 p.1, fun i => (x i).2⟩
  have hgf : ∀ v, g (f v) = v := by
    intro v
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext p
    rfl
  have hfg : ∀ x, f (g x) = x := by
    intro x
    funext i
    apply Subtype.ext
    rfl
  have hcard : Nat.card ↥(blockSub (ι := ι) R) = Nat.card (ι → ↥R) :=
    Nat.card_congr (Equiv.ofBijective f
      ⟨fun a b hab => by rw [← hgf a, ← hgf b, hab], fun x => ⟨g x, hfg x⟩⟩)
  rw [hcard, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

omit [Fintype ι] [DecidableEq ι] in
theorem blockSub_inf_le {k n : ℕ} {R : Fin n → Submodule K (Fin k → K)} (hR : iSupIndep R)
    (i : Fin n) :
    blockSub (ι := ι) (R i) ⊓ (⊥ ⊔ ⨆ (j : Fin n) (_ : j ≠ i), blockSub (ι := ι) (R j)) ≤ ⊥ := by
  intro v hv
  rw [Subgroup.mem_bot]
  rw [bot_sup_eq] at hv
  have hle : (⨆ (j : Fin n) (_ : j ≠ i), blockSub (ι := ι) (R j)) ≤
      blockSub (ι := ι) (⨆ (j : Fin n) (_ : j ≠ i), R j) :=
    iSup_le fun j => iSup_le fun hj =>
      blockSub_mono (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have hdisj : Disjoint (R i) (⨆ (j : Fin n) (_ : j ≠ i), R j) := iSupIndep_def.mp hR i
  have hzero : ∀ c : ι, (fun l => Multiplicative.toAdd v (l, c)) = 0 := by
    intro c
    have hmem : (fun l => Multiplicative.toAdd v (l, c)) ∈
        R i ⊓ ⨆ (j : Fin n) (_ : j ≠ i), R j :=
      ⟨hv.1 c, hle hv.2 c⟩
    simpa using hdisj.le_bot hmem
  apply Multiplicative.toAdd.injective
  funext p
  obtain ⟨l, c⟩ := p
  exact congrFun (hzero c) l

omit [Fintype ι] [DecidableEq ι] in
theorem sup_iSup_blockSub_eq_top {k n : ℕ} {R : Fin n → Submodule K (Fin k → K)}
    (hR : iSup R = ⊤) : (⊥ ⊔ ⨆ i, blockSub (ι := ι) (R i)) = ⊤ := by
  classical
  rw [bot_sup_eq, eq_top_iff]
  intro v _
  have hcol : ∀ c : ι, (fun l => Multiplicative.toAdd v (l, c)) ∈ ⨆ j : Fin n, R j := by
    intro c
    rw [hR]
    exact Submodule.mem_top
  choose r hr using fun c =>
    (Submodule.mem_iSup_finset_iff_exists_sum (s := Finset.univ) R
      (fun l => Multiplicative.toAdd v (l, c))).mp (by simpa using hcol c)
  set w : Fin n → StdMod (Fin k × ι) K :=
    fun j => Multiplicative.ofAdd fun p => (r p.2 j : Fin k → K) p.1 with hwdef
  have hw : ∀ j, w j ∈ blockSub (ι := ι) (R j) := fun j c => (r c j).2
  have hprod : v = ∏ j, w j := by
    apply Multiplicative.toAdd.injective
    funext p
    obtain ⟨l, c⟩ := p
    rw [toAdd_prod, Finset.sum_apply]
    have hc := congrFun (hr c) l
    rw [Finset.sum_apply] at hc
    exact hc.symm
  rw [hprod]
  exact Subgroup.prod_mem _ fun j _ => Subgroup.mem_iSup_of_mem j (hw j)

theorem matAut_diagGL_mem_blockSub {k : ℕ} {R : Submodule K (Fin k → K)} (γ : GL ι K)
    {v : StdMod (Fin k × ι) K} (hv : v ∈ blockSub R) : matAut (diagGL k γ) v ∈ blockSub R := by
  intro i
  have hcol : (fun l => Multiplicative.toAdd (matAut (diagGL k γ) v) (l, i)) =
      ∑ i' : ι, (γ : Matrix ι ι K) i i' • (fun l => Multiplicative.toAdd v (l, i')) := by
    funext l
    have h1 : Multiplicative.toAdd (matAut (diagGL k γ) v) =
        toAddMap (matAut (diagGL k γ)) (Multiplicative.toAdd v) := by
      simp [toAddMap]
    rw [h1, toAddMap_matAut, diagGL_mulVec]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcol]
  exact Submodule.sum_mem _ fun i' _ => Submodule.smul_mem _ _ (hv i')

theorem matAut_kronGL_mem_blockSub {k : ℕ} {R : Submodule K (Fin k → K)} (B : GL (Fin k) K)
    (hB : ∀ x ∈ R, (B : Matrix (Fin k) (Fin k) K) *ᵥ x ∈ R) {v : StdMod (Fin k × ι) K}
    (hv : v ∈ blockSub R) : matAut (kronGL ι k B) v ∈ blockSub R := by
  intro i
  have hcol : (fun l => Multiplicative.toAdd (matAut (kronGL ι k B) v) (l, i)) =
      (B : Matrix (Fin k) (Fin k) K) *ᵥ fun l => Multiplicative.toAdd v (l, i) := by
    funext l
    have h1 : Multiplicative.toAdd (matAut (kronGL ι k B) v) =
        toAddMap (matAut (kronGL ι k B)) (Multiplicative.toAdd v) := by
      simp [toAddMap]
    rw [h1, toAddMap_matAut, kronGL_mulVec]
    simp [Matrix.mulVec, dotProduct]
  rw [hcol]
  exact hB _ (hv i)

end CFSG.Quasithin.H.Mult
