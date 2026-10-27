module

public import CFSG.LocalAnalysis.StandardType.FS81.AutMat
public import CFSG.LocalAnalysis.StandardType.FS81.Realized
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G]

private theorem list_prod_pow_of_pairwise {G : Type} [Monoid G] (l : List G) (n : ℕ)
    (h : l.Pairwise Commute) : l.prod ^ n = (l.map fun x => x ^ n).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨ha, hl⟩ := h
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      Commute.mul_pow (Commute.list_prod_right l a ha), ih hl]

namespace Basis3

variable {k : ℕ}

private theorem vec_list_sum (B : Basis3 G k) (l : List (Coords k)) :
    B.vec l.sum = (l.map B.vec).prod := by
  induction l with
  | nil => rw [List.sum_nil, List.map_nil, List.prod_nil, B.vec_zero]
  | cons e l ih => rw [List.sum_cons, List.map_cons, List.prod_cons, B.vec_add, ih]

theorem vec_neg (B : Basis3 G k) (e : Coords k) :
    B.vec (-e) = (B.vec e)⁻¹ := by
  have h : B.vec e * B.vec (-e) = 1 := by
    rw [← B.vec_add]
    rw [show e + -e = 0 by ext i; exact add_neg_cancel (e i), B.vec_zero]
  exact eq_inv_of_mul_eq_one_right h

private theorem vec_smul (B : Basis3 G k) (c : ZMod 3) (e : Coords k) :
    B.vec (c • e) = B.vec e ^ c.val := by
  have hpair : (List.ofFn fun i => B.b i ^ (e i).val).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j _
    exact ((B.comm i j).pow_left _).pow_right _
  have hterm : ∀ i, B.b i ^ ((c • e) i).val = (B.b i ^ (e i).val) ^ c.val := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, ← pow_mul, ZMod.val_mul,
      Nat.mul_comm (e i).val c.val]
    have hmod : (c.val * (e i).val) % 3 =
        (c.val * (e i).val) % orderOf (B.b i) := by rw [B.ord i]
    rw [hmod, pow_mod_orderOf]
  unfold Basis3.vec
  rw [list_prod_pow_of_pairwise _ _ hpair, ← List.ofFn_comp']
  apply congrArg List.prod
  rw [List.ofFn_inj]
  funext i
  exact hterm i

private theorem mulVec_eq_sum_col (M : Matrix (Fin k) (Fin k) (ZMod 3)) (e : Coords k) :
    M.mulVec e = ∑ j, e j • M.col j := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm (M i j) (e j)

private theorem vec_mulVec (B : Basis3 G k) (M : Matrix (Fin k) (Fin k) (ZMod 3))
    (e : Coords k) :
    B.vec (M.mulVec e) =
      (List.ofFn fun j => B.vec (fun i => M i j) ^ (e j).val).prod := by
  have hmv : M.mulVec e = (List.ofFn fun j => e j • M.col j).sum := by
    rw [List.sum_ofFn]
    exact mulVec_eq_sum_col M e
  rw [hmv, vec_list_sum, ← List.ofFn_comp']
  apply congrArg List.prod
  rw [List.ofFn_inj]
  funext j
  rw [B.vec_smul]
  congr 1

theorem acts_vec (B : Basis3 G k) {g : G} {M : Matrix (Fin k) (Fin k) (ZMod 3)} (h : B.Acts g M)
    (e : Coords k) : g * B.vec e * g⁻¹ = B.vec (M.mulVec e) := by
  have hconj : g * B.vec e * g⁻¹ =
      (List.ofFn fun j => B.vec (fun i => M i j) ^ (e j).val).prod := by
    calc
      g * B.vec e * g⁻¹ = (MulAut.conj g) (B.vec e) := by rw [MulAut.conj_apply]
      _ = (List.ofFn fun j => ((MulAut.conj g) (B.b j)) ^ (e j).val).prod := by
        rw [Basis3.vec, map_list_prod, ← List.ofFn_comp']
        apply congrArg List.prod
        rw [List.ofFn_inj]
        funext j
        simp only [Function.comp_apply, map_pow]
      _ = (List.ofFn fun j => (g * B.b j * g⁻¹) ^ (e j).val).prod := by
        apply congrArg List.prod
        rw [List.ofFn_inj]
        funext j
        rw [MulAut.conj_apply]
      _ = (List.ofFn fun j => (B.vec (fun i => M i j)) ^ (e j).val).prod := by
        apply congrArg List.prod
        rw [List.ofFn_inj]
        funext j
        rw [h j]
  rw [B.vec_mulVec]
  exact hconj

theorem acts_unique (B : Basis3 G k) {g : G} {M M' : Matrix (Fin k) (Fin k) (ZMod 3)}
    (h : B.Acts g M) (h' : B.Acts g M') : M = M' := by
  ext i j
  have hcol : B.vec (fun i => M i j) = B.vec (fun i => M' i j) := by
    rw [← h j, h' j]
  exact congrFun (B.vec_injective hcol) i

theorem acts_one (B : Basis3 G k) : B.Acts 1 1 := by
  intro j
  rw [one_mul, inv_one, mul_one, ← B.vec_single j]
  apply congrArg B.vec
  funext i
  rw [Matrix.one_eq_pi_single, Pi.single_apply, Pi.single_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem acts_mul (B : Basis3 G k) {g h : G} {M M' : Matrix (Fin k) (Fin k) (ZMod 3)}
    (hg : B.Acts g M) (hh : B.Acts h M') : B.Acts (g * h) (M * M') := by
  intro j
  have hstep : (g * h) * B.b j * (g * h)⁻¹ = g * (h * B.b j * h⁻¹) * g⁻¹ := by
    rw [mul_inv_rev]
    group
  rw [hstep, hh j, B.acts_vec hg]
  apply congrArg B.vec
  funext i
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mul_apply]

theorem exists_acts [Finite G] (B : Basis3 G k) {g : G}
    (hg : g ∈ Subgroup.normalizer (B.span : Set G)) : ∃ M, B.Acts g M := by
  have hmem : ∀ j, g * B.b j * g⁻¹ ∈ B.span := fun j =>
    ((Subgroup.mem_normalizer_iff.mp hg (B.b j)).mp (B.b_mem_span j))
  choose e he using fun j => B.exists_vec_eq (hmem j)
  exact ⟨fun i j => e j i, fun j => (he j).symm⟩

theorem acts_spMat_iff (B : Basis3 G k) {g : G} {σ : Equiv.Perm (Fin k)} {s : Fin k → ZMod 3} :
    B.Acts g (spMat σ s) ↔ ∀ j, g * B.b j * g⁻¹ = B.b (σ j) ^ (s j).val := by
  have hcol : ∀ j, (fun i => spMat σ s i j) = Pi.single (σ j) (s j) := by
    intro j
    funext i
    rw [spMat, Pi.single_apply]
  have hsingle : ∀ (i : Fin k) (c : ZMod 3), B.vec (Pi.single i c) = B.b i ^ c.val := by
    intro i c
    rw [show Pi.single i c = c • Pi.single i (1 : ZMod 3) by
      rw [← Pi.single_smul]
      simp]
    rw [B.vec_smul, B.vec_single]
  constructor
  · intro h j
    rw [h j, hcol j, hsingle (σ j) (s j)]
  · intro h j
    rw [h j, hcol j, hsingle (σ j) (s j)]

end Basis3

theorem realized_mono {k : ℕ} (B : Basis3 G k) {H H' : Subgroup G} (h : H ≤ H') :
    B.realized H ⊆ B.realized H' := by
  rintro A ⟨g, hg, hA⟩
  exact ⟨g, h hg, hA⟩

private theorem centralizer_le_normalizer_zpowers (x : G) :
    Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  rw [Subgroup.zpowers_eq_closure]
  calc Subgroup.centralizer ({x} : Set G) = Subgroup.normalizer ({x} : Set G) :=
        (Subgroup.normalizer_singleton x).symm
    _ ≤ Subgroup.normalizer (Subgroup.closure ({x} : Set G)) :=
        Subgroup.normalizer_le_normalizer_closure _

theorem realized_one {k : ℕ} (B : Basis3 G k) (H : Subgroup G) :
    (1 : Matrix (Fin k) (Fin k) (ZMod 3)) ∈ B.realized H :=
  ⟨1, H.one_mem, B.acts_one⟩

theorem realized_mul {k : ℕ} (B : Basis3 G k) {H : Subgroup G}
    {A A' : Matrix (Fin k) (Fin k) (ZMod 3)}
    (hA : A ∈ B.realized H) (hA' : A' ∈ B.realized H) : A * A' ∈ B.realized H := by
  rcases hA with ⟨g, hg, hAg⟩
  rcases hA' with ⟨h, hh, hAh⟩
  exact ⟨g * h, H.mul_mem hg hh, B.acts_mul hAg hAh⟩

theorem realized_inv {k : ℕ} [Finite G] (B : Basis3 G k) {H : Subgroup G}
    {A : Matrix (Fin k) (Fin k) (ZMod 3)} (hA : A ∈ B.realized H) : A⁻¹ ∈ B.realized H := by
  rcases hA with ⟨g, hg, hAg⟩
  have hgN : g ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hAg
  have hgN' : g⁻¹ ∈ Subgroup.normalizer (B.span : Set G) :=
    (Subgroup.normalizer (B.span : Set G)).inv_mem hgN
  obtain ⟨M', hM'⟩ := B.exists_acts hgN'
  have hprod : A * M' = 1 := by
    have h1 : B.Acts (g * g⁻¹) (A * M') := B.acts_mul hAg hM'
    rw [mul_inv_cancel] at h1
    exact B.acts_unique h1 B.acts_one
  have hM'A : M' = A⁻¹ := (Matrix.inv_eq_right_inv hprod).symm
  exact ⟨g⁻¹, H.inv_mem hg, by simpa [hM'A] using hM'⟩

private theorem spMat_col {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) (j : Fin k) :
    (fun i => spMat σ s i j) = Pi.single (σ j) (s j) := by
  funext i
  rw [spMat, Pi.single_apply]

private theorem spMat_col_zero_eq_single {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    {s : Fin (n + 1) → ZMod 3} (hσ : σ 0 = 0) (hs : s 0 = 1) :
    (fun i => spMat σ s i 0) = Pi.single 0 1 := by
  rw [spMat_col, hσ, hs]

private theorem s_zero_of_spMat_col {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    {s : Fin (n + 1) → ZMod 3} (hσ : σ 0 = 0)
    (hcol : (fun i => spMat σ s i 0) = Pi.single 0 1) : s 0 = 1 := by
  have h := congrFun hcol 0
  simpa [spMat, hσ] using h

private theorem perm_inv_zero {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} (h : σ 0 = 0) :
    σ⁻¹ 0 = 0 := by
  simpa [h] using Equiv.symm_apply_apply σ (0 : Fin (n + 1))

private theorem isSign_ne_zero {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k) :
    s i ≠ 0 := by
  rcases hs i with h | h <;> rw [h] <;> decide

private theorem single_eq_single_of_ne_zero {k : ℕ} {i j : Fin k} {a b : ZMod 3}
    (ha : a ≠ 0)
    (h : Pi.single (M := fun _ => ZMod 3) i a =
      Pi.single (M := fun _ => ZMod 3) j b) : i = j ∧ a = b := by
  have hi := congrFun h i
  rw [Pi.single_eq_same, Pi.single_apply] at hi
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl] at hi
    exact ⟨rfl, hi⟩
  · rw [if_neg hij] at hi
    exact absurd hi ha

private theorem spMat_inj_of_isSign {k : ℕ} {σ τ : Equiv.Perm (Fin k)}
    {s t : Fin k → ZMod 3} (hs : IsSign s) (ht : IsSign t) (h : spMat σ s = spMat τ t) :
    σ = τ ∧ s = t := by
  have hcol : ∀ j, Pi.single (M := fun _ => ZMod 3) (σ j) (s j) =
      Pi.single (M := fun _ => ZMod 3) (τ j) (t j) := by
    intro j
    rw [← spMat_col σ s j, ← spMat_col τ t j, h]
  constructor
  · apply Equiv.ext
    intro j
    exact (single_eq_single_of_ne_zero (isSign_ne_zero hs j) (hcol j)).1
  · funext j
    exact (single_eq_single_of_ne_zero (isSign_ne_zero hs j) (hcol j)).2

private theorem spMat_one_one {k : ℕ} :
    spMat (1 : Equiv.Perm (Fin k)) (fun _ => (1 : ZMod 3)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [spMat, Matrix.one_apply, h]

private theorem spMat_inv {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3)
    (hs : IsSign s) :
    (spMat σ s)⁻¹ = spMat σ⁻¹ (fun i => (s (σ⁻¹ i))⁻¹) := by
  have hmain : spMat σ s * spMat σ⁻¹ (fun i => (s (σ⁻¹ i))⁻¹) =
      spMat (1 : Equiv.Perm (Fin k)) (fun _ => (1 : ZMod 3)) := by
    rw [spMat_mul]
    congr 1
    · ext j
      simp [Equiv.Perm.mul_apply]
    · funext j
      rw [mul_inv_cancel₀ (isSign_ne_zero hs (σ⁻¹ j))]
  have h : spMat σ s * spMat σ⁻¹ (fun i => (s (σ⁻¹ i))⁻¹) = 1 := by
    rw [hmain, spMat_one_one]
  exact Matrix.inv_eq_right_inv h

private theorem isSign_inv {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) :
    IsSign (fun i => (s i)⁻¹) := by
  intro i
  change (s i)⁻¹ = 1 ∨ (s i)⁻¹ = -1
  rcases hs i with h | h
  · rw [h]
    simp
  · rw [h]
    exact Or.inr inv_neg_one

private theorem isSign_mul {k : ℕ} {s t : Fin k → ZMod 3} (hs : IsSign s) (ht : IsSign t) :
    IsSign (fun i => s i * t i) := by
  intro i
  change s i * t i = 1 ∨ s i * t i = -1
  rcases hs i with h1 | h1 <;> rcases ht i with h2 | h2
  · rw [h1, h2]; left; decide
  · rw [h1, h2]; right; decide
  · rw [h1, h2]; right; decide
  · rw [h1, h2]; left; decide

private theorem isSign_comp {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s)
    (σ : Equiv.Perm (Fin k)) : IsSign (fun i => s (σ i)) := fun i => hs (σ i)

private theorem prod_all_mul {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (s t : Fin (n + 1) → ZMod 3) :
    (∏ j, s (σ j) * t j) = (∏ j, s j) * (∏ j, t j) := by
  rw [Finset.prod_mul_distrib, Equiv.prod_comp]

private theorem prod_all_inv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (s : Fin (n + 1) → ZMod 3) :
    (∏ i, (s (σ⁻¹ i))⁻¹) = (∏ i, s i)⁻¹ := by
  rw [Finset.prod_inv_distrib, Equiv.prod_comp]

private theorem prod_succ_eq_prod_all_of_zero {n : ℕ} {s : Fin (n + 1) → ZMod 3}
    (h : s 0 = 1) : (∏ i : Fin n, s i.succ) = ∏ i, s i := by
  rw [Fin.prod_univ_succ, h, one_mul]

private theorem prod_succ_eq_neg_prod_all_of_zero {n : ℕ} {s : Fin (n + 1) → ZMod 3}
    (h : s 0 = -1) : (∏ i : Fin n, s i.succ) = -(∏ i, s i) := by
  have hfull : (-1 : ZMod 3) * (∏ i : Fin n, s i.succ) = ∏ i, s i := by
    rw [Fin.prod_univ_succ, h]
  have hneg : (-1 : ZMod 3) * (∏ i : Fin n, s i.succ) =
      -(∏ i : Fin n, s i.succ) := neg_one_mul _
  have hfull' : -(∏ i : Fin n, s i.succ) = ∏ i, s i := hneg.symm.trans hfull
  exact neg_eq_iff_eq_neg.mp hfull'

private theorem prod_eq_one_or_neg_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ZMod 3) (h : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i, f i) = 1 ∨ (∏ i, f i) = -1 := by
  classical
  have hprod := Finset.prod_induction (s := Finset.univ) (f := f)
    (p := fun x => x = 1 ∨ x = -1)
    (fun a b ha hb => by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide)
    (Or.inl rfl) (fun x _ => h x)
  simpa using hprod

private theorem prod_eq_one_of_ne_neg_one {n : ℕ} {s : Fin (n + 1) → ZMod 3} (hs : IsSign s)
    (h : (∏ i : Fin n, s i.succ) ≠ -1) : (∏ i : Fin n, s i.succ) = 1 := by
  rcases prod_eq_one_or_neg_one (fun i : Fin n => s i.succ) (fun i => hs i.succ) with h1 | h1
  · exact h1
  · exact absurd h1 h

private theorem mem_monoN0_iff {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} :
    A ∈ monoN0 n ↔ ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ A = spMat σ s := Iff.rfl

private theorem mem_monoFix0_iff {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} :
    A ∈ monoFix0 n ↔
      ∃ σ s, IsSign s ∧ (σ 0 = 0 ∧ s 0 = 1) ∧ A = spMat σ s := Iff.rfl

private theorem mem_evenFix0_iff {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} :
    A ∈ evenFix0 n ↔ ∃ σ s, IsSign s ∧
      (σ 0 = 0 ∧ s 0 = 1 ∧ (∏ i : Fin n, s i.succ) = 1) ∧ A = spMat σ s := Iff.rfl

private theorem mem_evenN0_iff {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} :
    A ∈ evenN0 n ↔ ∃ σ s, IsSign s ∧
      (σ 0 = 0 ∧ (∏ i : Fin n, s i.succ) = 1) ∧ A = spMat σ s := Iff.rfl

private theorem mem_evenAll0_iff {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} :
    A ∈ evenAll0 n ↔ ∃ σ s, IsSign s ∧
      (σ 0 = 0 ∧ (∏ i : Fin (n + 1), s i) = 1) ∧ A = spMat σ s := Iff.rfl

private theorem realized_centralizer_col_zero {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G}
    (h0 : B.b 0 = b₀) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G))) :
    (fun i => A i 0) = Pi.single 0 1 := by
  rcases hA with ⟨g, hg, hAg⟩
  have hgcomm : g * b₀ = b₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hsingle : B.vec (Pi.single 0 1) = b₀ := by
    rw [B.vec_single, h0]
  have hcol : B.vec (fun i => A i 0) = B.vec (Pi.single 0 1) := by
    rw [← hAg 0, hsingle]
    rw [h0, hgcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact B.vec_injective hcol

private theorem mem_centralizer_of_acts_col_zero {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G}
    (h0 : B.b 0 = b₀) {g : G} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hActs : B.Acts g M) (hcol : (fun i => M i 0) = Pi.single 0 1) :
    g ∈ Subgroup.centralizer ({b₀} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hActs0 : g * B.b 0 * g⁻¹ = B.vec (fun i => M i 0) := hActs 0
  have hMvec : B.vec (fun i => M i 0) = b₀ := by
    rw [hcol, B.vec_single, h0]
  have h : g * b₀ * g⁻¹ = b₀ := by
    have hMvec' : B.vec (fun i => M i 0) = B.b 0 := by rw [hMvec, h0]
    rw [← h0]
    exact hActs0.trans hMvec'
  calc g * b₀ = (g * b₀ * g⁻¹) * g := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = b₀ * g := by rw [h]

private theorem realized_centralizer_subset_monoFix0 {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G}
    (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ monoFix0 n := by
  intro A hA
  have hAN : A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :=
    realized_mono B (centralizer_le_normalizer_zpowers b₀) hA
  have hAm := hmono hAN
  rw [mem_monoN0_iff] at hAm
  rcases hAm with ⟨σ, s, hs, hσ, hEq⟩
  rw [hEq] at hA ⊢
  refine ⟨σ, s, hs, ⟨hσ, ?_⟩, rfl⟩
  exact s_zero_of_spMat_col hσ (realized_centralizer_col_zero B h0 hA)

private theorem realized_centralizer_of_mem_normalizer_of_s0_one {n : ℕ} (B : Basis3 G (n + 1))
    {b₀ : G} (h0 : B.b 0 = b₀) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    (hrep : ∃ σ s, IsSign s ∧ (σ 0 = 0 ∧ s 0 = 1) ∧ A = spMat σ s) :
    A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
  rcases hA with ⟨g, hg, hActs⟩
  rcases hrep with ⟨σ, s, hs, ⟨hσ, hs0⟩, hEq⟩
  have hcol : (fun i => A i 0) = Pi.single 0 1 := by
    rw [hEq, spMat_col_zero_eq_single hσ hs0]
  exact ⟨g, mem_centralizer_of_acts_col_zero B h0 hActs hcol, hActs⟩

private theorem realized_normalizer_subset_centralizer_of_no_neg {n : ℕ}
    (B : Basis3 G (n + 1)) {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hno : ¬ ∃ A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)),
      ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = -1 ∧ A = spMat σ s) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆
      B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
  intro A hA
  have hAm := hmono hA
  rw [mem_monoN0_iff] at hAm
  rcases hAm with ⟨σ, s, hs, hσ, hEq⟩
  by_cases hs0 : s 0 = 1
  · exact realized_centralizer_of_mem_normalizer_of_s0_one B h0 hA ⟨σ, s, hs, ⟨hσ, hs0⟩, hEq⟩
  · exfalso
    apply hno
    refine ⟨A, hA, σ, s, hs, hσ, ?_, hEq⟩
    rcases hs 0 with h | h
    · exact absurd h hs0
    · exact h

private theorem spMat_mul_inv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (s : Fin (n + 1) → ZMod 3) (hs : IsSign s) :
    spMat σ s * (spMat σ s)⁻¹ = 1 := by
  rw [spMat_inv σ s hs]
  have hmain : spMat σ s * spMat σ⁻¹ (fun i => (s (σ⁻¹ i))⁻¹) =
      spMat (1 : Equiv.Perm (Fin (n + 1))) (fun _ => (1 : ZMod 3)) := by
    rw [spMat_mul]
    congr 1
    · ext j
      simp [Equiv.Perm.mul_apply]
    · funext j
      rw [mul_inv_cancel₀ (isSign_ne_zero hs (σ⁻¹ j))]
  rw [hmain, spMat_one_one]

private theorem spMat_mul_inv_mul {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (s : Fin (n + 1) → ZMod 3) (hs : IsSign s)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) :
    spMat σ s * ((spMat σ s)⁻¹ * M) = M := by
  rw [← mul_assoc, spMat_mul_inv σ s hs, one_mul]

private theorem prod_succ_of_mem_evenFix0 {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hA : A ∈ evenFix0 n)
    {σ : Equiv.Perm (Fin (n + 1))} {s : Fin (n + 1) → ZMod 3} (hs : IsSign s)
    (hEq : A = spMat σ s) : (∏ i : Fin n, s i.succ) = 1 := by
  rw [mem_evenFix0_iff] at hA
  rcases hA with ⟨τ, t, ht, ⟨hτ, ht0, htp⟩, hAt⟩
  have hst : s = t := (spMat_inj_of_isSign hs ht (hEq.symm.trans hAt)).2
  rw [hst]
  exact htp

private theorem spMat_inv_mul_eq {n : ℕ} (σ₀ σ : Equiv.Perm (Fin (n + 1)))
    (s₀ s : Fin (n + 1) → ZMod 3) (hs₀ : IsSign s₀) :
    (spMat σ₀ s₀)⁻¹ * spMat σ s =
      spMat (σ₀⁻¹ * σ) (fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) := by
  rw [spMat_inv σ₀ s₀ hs₀, spMat_mul]

private theorem spMat_inv_mul_sign_zero {n : ℕ} {σ₀ σ : Equiv.Perm (Fin (n + 1))}
    {s₀ s : Fin (n + 1) → ZMod 3} (hσ₀ : σ₀ 0 = 0) (hσ : σ 0 = 0)
    (hs₀0 : s₀ 0 = -1) (hs0 : s 0 = -1) :
    (fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) 0 = 1 := by
  change (s₀ (σ₀⁻¹ (σ 0)))⁻¹ * s 0 = 1
  rw [hσ, perm_inv_zero hσ₀, hs₀0, hs0]
  exact inv_mul_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0)

private theorem prod_succ_eq_one_of_full_eq_one_even {n : ℕ}
    {σ₀ σ : Equiv.Perm (Fin (n + 1))} {s₀ s : Fin (n + 1) → ZMod 3}
    (hs₀0 : s₀ 0 = -1) (hs0 : s 0 = -1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = 1)
    (hFt : (∏ j, (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) = 1) :
    (∏ i : Fin n, s i.succ) = 1 := by
  have hF₀ : (∏ i : Fin (n + 1), s₀ i) = -1 := by
    rw [Fin.prod_univ_succ, hs₀0, hp₀, mul_one]
  have hF : (∏ i : Fin (n + 1), s i) = -(∏ i : Fin n, s i.succ) := by
    rw [Fin.prod_univ_succ, hs0]
    exact neg_one_mul _
  have hFt' : (∏ j, (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) =
      (∏ i : Fin (n + 1), s₀ i)⁻¹ * (∏ i : Fin (n + 1), s i) := by
    change (∏ j, (fun i => (s₀ (σ₀⁻¹ i))⁻¹) (σ j) * s j) = _
    rw [prod_all_mul σ (fun i => (s₀ (σ₀⁻¹ i))⁻¹) s, prod_all_inv σ₀ s₀]
  have h1 : (∏ i : Fin (n + 1), s₀ i)⁻¹ * (∏ i : Fin (n + 1), s i) = 1 :=
    hFt'.symm.trans hFt
  rw [hF₀] at h1
  have h2 : (-1 : ZMod 3) * (∏ i : Fin (n + 1), s i) = 1 :=
    (congrArg (fun x => x * (∏ i : Fin (n + 1), s i)) inv_neg_one).symm.trans h1
  have h3 : -(∏ i : Fin (n + 1), s i) = 1 :=
    (neg_one_mul (∏ i : Fin (n + 1), s i)).symm.trans h2
  have hF_eq : (∏ i : Fin (n + 1), s i) = -1 := neg_eq_iff_eq_neg.mp h3
  have h4 : -(∏ i : Fin n, s i.succ) = -1 := by
    rw [← hF]
    exact hF_eq
  exact neg_inj.mp h4

private theorem prod_all_eq_one_of_full_eq_one_odd {n : ℕ}
    {σ₀ σ : Equiv.Perm (Fin (n + 1))} {s₀ s : Fin (n + 1) → ZMod 3}
    (hs₀0 : s₀ 0 = -1) (hp₀ : (∏ i : Fin n, s₀ i.succ) = -1)
    (hFt : (∏ j, (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) = 1) :
    (∏ i : Fin (n + 1), s i) = 1 := by
  have hF₀ : (∏ i : Fin (n + 1), s₀ i) = 1 := by
    rw [Fin.prod_univ_succ, hs₀0, hp₀]
    decide
  have hFt' : (∏ j, (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) =
      (∏ i : Fin (n + 1), s₀ i)⁻¹ * (∏ i : Fin (n + 1), s i) := by
    change (∏ j, (fun i => (s₀ (σ₀⁻¹ i))⁻¹) (σ j) * s j) = _
    rw [prod_all_mul σ (fun i => (s₀ (σ₀⁻¹ i))⁻¹) s, prod_all_inv σ₀ s₀]
  have h1 : (∏ i : Fin (n + 1), s₀ i)⁻¹ * (∏ i : Fin (n + 1), s i) = 1 :=
    hFt'.symm.trans hFt
  rw [hF₀] at h1
  have h2 : (1 : ZMod 3) * (∏ i : Fin (n + 1), s i) = 1 :=
    (congrArg (fun x => x * (∏ i : Fin (n + 1), s i)) inv_one).symm.trans h1
  exact (one_mul (∏ i : Fin (n + 1), s i)).symm.trans h2

private theorem prod_succ_inv_mul_sign_even_even {n : ℕ}
    {σ₀ σ : Equiv.Perm (Fin (n + 1))} {s₀ s : Fin (n + 1) → ZMod 3}
    (hσ₀ : σ₀ 0 = 0) (hσ : σ 0 = 0)
    (hs₀0 : s₀ 0 = -1) (hs0 : s 0 = -1)
    (hP₀ : (∏ i : Fin n, s₀ i.succ) = 1) (hP : (∏ i : Fin n, s i.succ) = 1) :
    (∏ i : Fin n, (fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) i.succ) = 1 := by
  have hF₀ : (∏ i : Fin (n + 1), s₀ i) = -1 := by
    rw [Fin.prod_univ_succ, hs₀0, hP₀, mul_one]
  have hF : (∏ i : Fin (n + 1), s i) = -1 := by
    rw [Fin.prod_univ_succ, hs0, hP, mul_one]
  have ht0 := spMat_inv_mul_sign_zero hσ₀ hσ hs₀0 hs0
  have hfull : (∏ j : Fin (n + 1), (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) = 1 := by
    change (∏ j, (fun i => (s₀ (σ₀⁻¹ i))⁻¹) (σ j) * s j) = 1
    rw [prod_all_mul σ (fun i => (s₀ (σ₀⁻¹ i))⁻¹) s, prod_all_inv σ₀ s₀, hF₀, hF]
    exact inv_mul_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0)
  rw [prod_succ_eq_prod_all_of_zero (s := fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) ht0]
  exact hfull

private theorem prod_succ_inv_mul_sign_odd_odd {n : ℕ}
    {σ₀ σ : Equiv.Perm (Fin (n + 1))} {s₀ s : Fin (n + 1) → ZMod 3}
    (hσ₀ : σ₀ 0 = 0) (hσ : σ 0 = 0)
    (hs₀0 : s₀ 0 = -1) (hs0 : s 0 = -1)
    (hP₀ : (∏ i : Fin n, s₀ i.succ) = -1) (hP : (∏ i : Fin n, s i.succ) = -1) :
    (∏ i : Fin n, (fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) i.succ) = 1 := by
  have hF₀ : (∏ i : Fin (n + 1), s₀ i) = 1 := by
    rw [Fin.prod_univ_succ, hs₀0, hP₀]
    decide
  have hF : (∏ i : Fin (n + 1), s i) = 1 := by
    rw [Fin.prod_univ_succ, hs0, hP]
    decide
  have ht0 := spMat_inv_mul_sign_zero hσ₀ hσ hs₀0 hs0
  have hfull : (∏ j : Fin (n + 1), (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) = 1 := by
    change (∏ j, (fun i => (s₀ (σ₀⁻¹ i))⁻¹) (σ j) * s j) = 1
    rw [prod_all_mul σ (fun i => (s₀ (σ₀⁻¹ i))⁻¹) s, prod_all_inv σ₀ s₀, hF₀, hF]
    exact inv_mul_cancel₀ (by decide : (1 : ZMod 3) ≠ 0)
  rw [prod_succ_eq_prod_all_of_zero (s := fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j) ht0]
  exact hfull

private theorem spMat_inv_mul_mem_monoFix0 {n : ℕ}
    {σ₀ σ : Equiv.Perm (Fin (n + 1))} {s₀ s : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hs : IsSign s) (hσ₀ : σ₀ 0 = 0) (hσ : σ 0 = 0)
    (hs₀0 : s₀ 0 = -1) (hs0 : s 0 = -1) :
    (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ monoFix0 n := by
  rw [spMat_inv σ₀ s₀ hs₀, spMat_mul]
  refine ⟨σ₀⁻¹ * σ, fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j, ?_, ⟨?_, ?_⟩, rfl⟩
  · exact isSign_mul (isSign_inv (isSign_comp (isSign_comp hs₀ σ₀⁻¹) σ)) hs
  · rw [Equiv.Perm.mul_apply, hσ, perm_inv_zero hσ₀]
  · change (s₀ (σ₀⁻¹ (σ 0)))⁻¹ * s 0 = 1
    rw [hσ, perm_inv_zero hσ₀, hs₀0, hs0]
    exact inv_mul_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0)

private theorem spMat_inv_mul_mem_evenFix0 {n : ℕ}
    {σ₀ σ : Equiv.Perm (Fin (n + 1))} {s₀ s : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hs : IsSign s) (hσ₀ : σ₀ 0 = 0) (hσ : σ 0 = 0)
    (hs₀0 : s₀ 0 = 1) (hs0 : s 0 = 1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = -1) (hp : (∏ i : Fin n, s i.succ) = -1) :
    (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ evenFix0 n := by
  rw [spMat_inv σ₀ s₀ hs₀, spMat_mul]
  let u : Fin (n + 1) → ZMod 3 := fun i => (s₀ (σ₀⁻¹ i))⁻¹
  let t : Fin (n + 1) → ZMod 3 := fun j => u (σ j) * s j
  change spMat (σ₀⁻¹ * σ) t ∈ evenFix0 n
  have hsign0 : t 0 = 1 := by
    change (s₀ (σ₀⁻¹ (σ 0)))⁻¹ * s 0 = 1
    rw [hσ, perm_inv_zero hσ₀, hs₀0, hs0]
    exact inv_mul_cancel₀ (by decide : (1 : ZMod 3) ≠ 0)
  have hfull : (∏ j : Fin (n + 1), t j) = 1 := by
    change (∏ j, u (σ j) * s j) = 1
    rw [prod_all_mul σ u s, prod_all_inv σ₀ s₀,
      ← prod_succ_eq_prod_all_of_zero hs₀0, ← prod_succ_eq_prod_all_of_zero hs0, hp₀, hp]
    exact inv_mul_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0)
  refine ⟨σ₀⁻¹ * σ, t, ?_, ⟨?_, ?_, ?_⟩, rfl⟩
  · exact isSign_mul (isSign_inv (isSign_comp (isSign_comp hs₀ σ₀⁻¹) σ)) hs
  · rw [Equiv.Perm.mul_apply, hσ, perm_inv_zero hσ₀]
  · exact hsign0
  · rw [prod_succ_eq_prod_all_of_zero hsign0]
    exact hfull

private theorem monoFix0_subset_of_odd {n : ℕ}
    {R : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))}
    (hRmul : ∀ A ∈ R, ∀ B ∈ R, A * B ∈ R)
    (hevenR : evenFix0 n ⊆ R)
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hA₀R : A₀ ∈ R)
    (hA₀ : ∃ σ s, IsSign s ∧ (σ 0 = 0 ∧ s 0 = 1) ∧ A₀ = spMat σ s ∧
      (∏ i : Fin n, s i.succ) = -1) :
    monoFix0 n ⊆ R := by
  intro M hM
  rw [mem_monoFix0_iff] at hM
  rcases hM with ⟨σ, s, hs, ⟨hσ, hs0⟩, hEq⟩
  by_cases hp : (∏ i : Fin n, s i.succ) = -1
  · rcases hA₀ with ⟨σ₀, s₀, hs₀, ⟨hσ₀, hs₀0⟩, hA₀Eq, hp₀⟩
    have hB : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ evenFix0 n :=
      spMat_inv_mul_mem_evenFix0 hs₀ hs hσ₀ hσ hs₀0 hs0 hp₀ hp
    have hmul := hRmul (spMat σ₀ s₀) (by rwa [← hA₀Eq])
      ((spMat σ₀ s₀)⁻¹ * spMat σ s) (hevenR hB)
    rw [hEq]
    have hEqM : spMat σ₀ s₀ * ((spMat σ₀ s₀)⁻¹ * spMat σ s) = spMat σ s :=
      spMat_mul_inv_mul σ₀ s₀ hs₀ (spMat σ s)
    rwa [hEqM] at hmul
  · exact hevenR ⟨σ, s, hs, ⟨hσ, hs0, prod_eq_one_of_ne_neg_one hs hp⟩, hEq⟩

private theorem realized_centralizer_subset_evenFix0 {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G}
    (hRmono : B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ monoFix0 n)
    (hno : ¬ ∃ A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)),
      ∃ σ s, IsSign s ∧ (σ 0 = 0 ∧ s 0 = 1) ∧ A = spMat σ s ∧
        (∏ i : Fin n, s i.succ) = -1) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ evenFix0 n := by
  intro A hA
  have hAm := hRmono hA
  rw [mem_monoFix0_iff] at hAm
  rcases hAm with ⟨σ, s, hs, ⟨hσ, hs0⟩, hEq⟩
  have hp1 : (∏ i : Fin n, s i.succ) = 1 := by
    by_contra hp
    apply hno
    refine ⟨A, hA, σ, s, hs, ⟨hσ, hs0⟩, hEq, ?_⟩
    rcases prod_eq_one_or_neg_one (fun i : Fin n => s i.succ) (fun i => hs i.succ) with h1 | h1
    · exact absurd h1 hp
    · exact h1
  exact ⟨σ, s, hs, ⟨hσ, hs0, hp1⟩, hEq⟩

private theorem realized_normalizer_eq_monoFix0_of_no_neg {n : ℕ} (B : Basis3 G (n + 1))
    {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hno : ¬ ∃ A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)),
      ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = -1 ∧ A = spMat σ s)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = monoFix0 n := by
  apply Set.Subset.antisymm
  · intro A hA
    have hAC := realized_normalizer_subset_centralizer_of_no_neg B h0 hmono hno hA
    rwa [hR] at hAC
  · intro A hA
    have hAC : A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    exact realized_mono B (centralizer_le_normalizer_zpowers b₀) hAC

private theorem realized_normalizer_eq_evenFix0_of_no_neg {n : ℕ} (B : Basis3 G (n + 1))
    {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hno : ¬ ∃ A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)),
      ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = -1 ∧ A = spMat σ s)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenFix0 n := by
  apply Set.Subset.antisymm
  · intro A hA
    have hAC := realized_normalizer_subset_centralizer_of_no_neg B h0 hmono hno hA
    rwa [hR] at hAC
  · intro A hA
    have hAC : A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    exact realized_mono B (centralizer_le_normalizer_zpowers b₀) hAC

private theorem realized_normalizer_eq_monoN0_of_neg {n : ℕ} (B : Basis3 G (n + 1))
    {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n)
    (hneg : ∃ A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)),
      ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = -1 ∧ A = spMat σ s) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = monoN0 n := by
  apply Set.Subset.antisymm hmono
  intro M hM
  rw [mem_monoN0_iff] at hM
  rcases hM with ⟨σ, s, hs, hσ, hEq⟩
  by_cases hs0 : s 0 = 1
  · have hfix : M ∈ monoFix0 n := ⟨σ, s, hs, ⟨hσ, hs0⟩, hEq⟩
    have hAC : M ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    exact realized_mono B (centralizer_le_normalizer_zpowers b₀) hAC
  · have hs0neg : s 0 = -1 := by
      rcases hs 0 with h | h
      · exact absurd h hs0
      · exact h
    rcases hneg with ⟨A₀, hA₀N, σ₀, s₀, hs₀, hσ₀, hs₀neg, hA₀Eq⟩
    have hBfix : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ monoFix0 n :=
      spMat_inv_mul_mem_monoFix0 hs₀ hs hσ₀ hσ hs₀neg hs0neg
    have hBR : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈
        B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    have hBN : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :=
      realized_mono B (centralizer_le_normalizer_zpowers b₀) hBR
    have hA₀N' : spMat σ₀ s₀ ∈
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
      rwa [← hA₀Eq]
    have hmul := realized_mul B hA₀N' hBN
    rw [hEq]
    have hEqM : spMat σ₀ s₀ * ((spMat σ₀ s₀)⁻¹ * spMat σ s) = spMat σ s :=
      spMat_mul_inv_mul σ₀ s₀ hs₀ (spMat σ s)
    rwa [hEqM] at hmul

private theorem spMat_inv_mul_mem_centralizer {n : ℕ} [Finite G] (B : Basis3 G (n + 1)) {b₀ : G}
    (h0 : B.b 0 = b₀) {A₀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA₀N : A₀ ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    (hAN : A ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {σ₀ σ : Equiv.Perm (Fin (n + 1))} {s₀ s : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hs : IsSign s) (hσ₀ : σ₀ 0 = 0) (hσ : σ 0 = 0)
    (hs₀0 : s₀ 0 = -1) (hs0 : s 0 = -1)
    (hA₀Eq : A₀ = spMat σ₀ s₀) (hAEq : A = spMat σ s) :
    (spMat σ₀ s₀)⁻¹ * spMat σ s ∈
      B.realized (Subgroup.centralizer ({b₀} : Set G)) := by
  have hA₀N' : spMat σ₀ s₀ ∈
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by rwa [← hA₀Eq]
  have hAN' : spMat σ s ∈
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by rwa [← hAEq]
  have hInvN := realized_inv B hA₀N'
  have hBN := realized_mul B hInvN hAN'
  have hBfix : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ monoFix0 n :=
    spMat_inv_mul_mem_monoFix0 hs₀ hs hσ₀ hσ hs₀0 hs0
  rw [mem_monoFix0_iff] at hBfix
  rcases hBfix with ⟨τ, t, ht, ⟨hτ, ht0⟩, hBt⟩
  exact realized_centralizer_of_mem_normalizer_of_s0_one B h0 hBN ⟨τ, t, ht, ⟨hτ, ht0⟩, hBt⟩

private theorem realized_normalizer_subset_evenN0_of_neg_even {n : ℕ} [Finite G] (B : Basis3 G (n + 1))
    {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA₀N : A₀ ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {σ₀ : Equiv.Perm (Fin (n + 1))} {s₀ : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hσ₀ : σ₀ 0 = 0) (hs₀0 : s₀ 0 = -1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = 1) (hA₀Eq : A₀ = spMat σ₀ s₀) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ evenN0 n := by
  intro A hA
  have hAm := hmono hA
  rw [mem_monoN0_iff] at hAm
  rcases hAm with ⟨σ, s, hs, hσ, hEq⟩
  by_cases hs0 : s 0 = 1
  · have hAC := realized_centralizer_of_mem_normalizer_of_s0_one B h0 hA
      ⟨σ, s, hs, ⟨hσ, hs0⟩, hEq⟩
    have hFix : A ∈ evenFix0 n := by rwa [hR] at hAC
    have hp := prod_succ_of_mem_evenFix0 hFix hs hEq
    exact ⟨σ, s, hs, ⟨hσ, hp⟩, hEq⟩
  · have hs0neg : s 0 = -1 := by
      rcases hs 0 with h | h
      · exact absurd h hs0
      · exact h
    have hBC := spMat_inv_mul_mem_centralizer B h0 hA₀N hA hs₀ hs hσ₀ hσ hs₀0 hs0neg
      hA₀Eq hEq
    have hBFix : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ evenFix0 n := by rwa [hR] at hBC
    let texp : Fin (n + 1) → ZMod 3 := fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j
    have hBexp : (spMat σ₀ s₀)⁻¹ * spMat σ s = spMat (σ₀⁻¹ * σ) texp :=
      spMat_inv_mul_eq σ₀ σ s₀ s hs₀
    have htsign : IsSign texp :=
      isSign_mul (isSign_inv (isSign_comp (isSign_comp hs₀ σ₀⁻¹) σ)) hs
    have hPt : (∏ i : Fin n, texp i.succ) = 1 :=
      prod_succ_of_mem_evenFix0 hBFix htsign hBexp
    have ht0 : texp 0 = 1 := spMat_inv_mul_sign_zero hσ₀ hσ hs₀0 hs0neg
    have hFt : (∏ i : Fin (n + 1), texp i) = 1 := by
      rw [← prod_succ_eq_prod_all_of_zero ht0]
      exact hPt
    have hp : (∏ i : Fin n, s i.succ) = 1 :=
      prod_succ_eq_one_of_full_eq_one_even hs₀0 hs0neg hp₀ hFt
    exact ⟨σ, s, hs, ⟨hσ, hp⟩, hEq⟩

private theorem realized_normalizer_subset_evenAll0_of_neg_odd {n : ℕ} [Finite G] (B : Basis3 G (n + 1))
    {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA₀N : A₀ ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {σ₀ : Equiv.Perm (Fin (n + 1))} {s₀ : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hσ₀ : σ₀ 0 = 0) (hs₀0 : s₀ 0 = -1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = -1) (hA₀Eq : A₀ = spMat σ₀ s₀) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ evenAll0 n := by
  intro A hA
  have hAm := hmono hA
  rw [mem_monoN0_iff] at hAm
  rcases hAm with ⟨σ, s, hs, hσ, hEq⟩
  by_cases hs0 : s 0 = 1
  · have hAC := realized_centralizer_of_mem_normalizer_of_s0_one B h0 hA
      ⟨σ, s, hs, ⟨hσ, hs0⟩, hEq⟩
    have hFix : A ∈ evenFix0 n := by rwa [hR] at hAC
    have hp : (∏ i : Fin n, s i.succ) = 1 := prod_succ_of_mem_evenFix0 hFix hs hEq
    have hF : (∏ i : Fin (n + 1), s i) = 1 := by
      rw [← prod_succ_eq_prod_all_of_zero hs0]
      exact hp
    exact ⟨σ, s, hs, ⟨hσ, hF⟩, hEq⟩
  · have hs0neg : s 0 = -1 := by
      rcases hs 0 with h | h
      · exact absurd h hs0
      · exact h
    have hBC := spMat_inv_mul_mem_centralizer B h0 hA₀N hA hs₀ hs hσ₀ hσ hs₀0 hs0neg
      hA₀Eq hEq
    have hBFix : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ evenFix0 n := by rwa [hR] at hBC
    let texp : Fin (n + 1) → ZMod 3 := fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j
    have hBexp : (spMat σ₀ s₀)⁻¹ * spMat σ s = spMat (σ₀⁻¹ * σ) texp :=
      spMat_inv_mul_eq σ₀ σ s₀ s hs₀
    have htsign : IsSign texp :=
      isSign_mul (isSign_inv (isSign_comp (isSign_comp hs₀ σ₀⁻¹) σ)) hs
    have hPt : (∏ i : Fin n, texp i.succ) = 1 :=
      prod_succ_of_mem_evenFix0 hBFix htsign hBexp
    have ht0 : texp 0 = 1 := spMat_inv_mul_sign_zero hσ₀ hσ hs₀0 hs0neg
    have hFt : (∏ i : Fin (n + 1), texp i) = 1 := by
      rw [← prod_succ_eq_prod_all_of_zero ht0]
      exact hPt
    have hF : (∏ i : Fin (n + 1), s i) = 1 :=
      prod_all_eq_one_of_full_eq_one_odd hs₀0 hp₀ hFt
    exact ⟨σ, s, hs, ⟨hσ, hF⟩, hEq⟩

private theorem realized_evenN0_subset_normalizer_of_neg {n : ℕ} [Finite G]
    (B : Basis3 G (n + 1)) {b₀ : G} (h0 : B.b 0 = b₀)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA₀N : A₀ ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {σ₀ : Equiv.Perm (Fin (n + 1))} {s₀ : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hσ₀ : σ₀ 0 = 0) (hs₀0 : s₀ 0 = -1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = 1) (hA₀Eq : A₀ = spMat σ₀ s₀) :
    evenN0 n ⊆ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
  intro A hA
  rw [mem_evenN0_iff] at hA
  rcases hA with ⟨σ, s, hs, ⟨hσ, hp⟩, hEq⟩
  by_cases hs0 : s 0 = 1
  · have hFix : A ∈ evenFix0 n := ⟨σ, s, hs, ⟨hσ, hs0, hp⟩, hEq⟩
    have hAC : A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    exact realized_mono B (centralizer_le_normalizer_zpowers b₀) hAC
  · have hs0neg : s 0 = -1 := by
      rcases hs 0 with h | h
      · exact absurd h hs0
      · exact h
    have hσprod : (σ₀⁻¹ * σ) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, hσ, perm_inv_zero hσ₀]
    let texp : Fin (n + 1) → ZMod 3 := fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j
    have htsign : IsSign texp :=
      isSign_mul (isSign_inv (isSign_comp (isSign_comp hs₀ σ₀⁻¹) σ)) hs
    have ht0 : texp 0 = 1 := spMat_inv_mul_sign_zero hσ₀ hσ hs₀0 hs0neg
    have hPt : (∏ i : Fin n, texp i.succ) = 1 :=
      prod_succ_inv_mul_sign_even_even hσ₀ hσ hs₀0 hs0neg hp₀ hp
    have hBexp : (spMat σ₀ s₀)⁻¹ * spMat σ s = spMat (σ₀⁻¹ * σ) texp :=
      spMat_inv_mul_eq σ₀ σ s₀ s hs₀
    have hBFix : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ evenFix0 n :=
      ⟨σ₀⁻¹ * σ, texp, htsign, ⟨hσprod, ht0, hPt⟩, hBexp⟩
    have hBR : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈
        B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    have hBN : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :=
      realized_mono B (centralizer_le_normalizer_zpowers b₀) hBR
    have hA₀N' : spMat σ₀ s₀ ∈
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by rwa [← hA₀Eq]
    have hmul := realized_mul B hA₀N' hBN
    rw [hEq]
    have hEqM : spMat σ₀ s₀ * ((spMat σ₀ s₀)⁻¹ * spMat σ s) = spMat σ s :=
      spMat_mul_inv_mul σ₀ s₀ hs₀ (spMat σ s)
    rwa [hEqM] at hmul

private theorem realized_evenAll0_subset_normalizer_of_neg {n : ℕ} [Finite G]
    (B : Basis3 G (n + 1)) {b₀ : G} (h0 : B.b 0 = b₀)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA₀N : A₀ ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {σ₀ : Equiv.Perm (Fin (n + 1))} {s₀ : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hσ₀ : σ₀ 0 = 0) (hs₀0 : s₀ 0 = -1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = -1) (hA₀Eq : A₀ = spMat σ₀ s₀) :
    evenAll0 n ⊆ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
  intro A hA
  rw [mem_evenAll0_iff] at hA
  rcases hA with ⟨σ, s, hs, ⟨hσ, hp⟩, hEq⟩
  by_cases hs0 : s 0 = 1
  · have hps : (∏ i : Fin n, s i.succ) = 1 := by
      rw [prod_succ_eq_prod_all_of_zero hs0]
      exact hp
    have hFix : A ∈ evenFix0 n := ⟨σ, s, hs, ⟨hσ, hs0, hps⟩, hEq⟩
    have hAC : A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    exact realized_mono B (centralizer_le_normalizer_zpowers b₀) hAC
  · have hs0neg : s 0 = -1 := by
      rcases hs 0 with h | h
      · exact absurd h hs0
      · exact h
    have hP : (∏ i : Fin n, s i.succ) = -1 := by
      rw [prod_succ_eq_neg_prod_all_of_zero hs0neg, hp]
    have hσprod : (σ₀⁻¹ * σ) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, hσ, perm_inv_zero hσ₀]
    let texp : Fin (n + 1) → ZMod 3 := fun j => (s₀ (σ₀⁻¹ (σ j)))⁻¹ * s j
    have htsign : IsSign texp :=
      isSign_mul (isSign_inv (isSign_comp (isSign_comp hs₀ σ₀⁻¹) σ)) hs
    have ht0 : texp 0 = 1 := spMat_inv_mul_sign_zero hσ₀ hσ hs₀0 hs0neg
    have hPt : (∏ i : Fin n, texp i.succ) = 1 :=
      prod_succ_inv_mul_sign_odd_odd hσ₀ hσ hs₀0 hs0neg hp₀ hP
    have hBexp : (spMat σ₀ s₀)⁻¹ * spMat σ s = spMat (σ₀⁻¹ * σ) texp :=
      spMat_inv_mul_eq σ₀ σ s₀ s hs₀
    have hBFix : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈ evenFix0 n :=
      ⟨σ₀⁻¹ * σ, texp, htsign, ⟨hσprod, ht0, hPt⟩, hBexp⟩
    have hBR : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈
        B.realized (Subgroup.centralizer ({b₀} : Set G)) := by rwa [hR]
    have hBN : (spMat σ₀ s₀)⁻¹ * spMat σ s ∈
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :=
      realized_mono B (centralizer_le_normalizer_zpowers b₀) hBR
    have hA₀N' : spMat σ₀ s₀ ∈
        B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by rwa [← hA₀Eq]
    have hmul := realized_mul B hA₀N' hBN
    rw [hEq]
    have hEqM : spMat σ₀ s₀ * ((spMat σ₀ s₀)⁻¹ * spMat σ s) = spMat σ s :=
      spMat_mul_inv_mul σ₀ s₀ hs₀ (spMat σ s)
    rwa [hEqM] at hmul

private theorem realized_normalizer_eq_evenN0_of_neg_even {n : ℕ} [Finite G]
    (B : Basis3 G (n + 1)) {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA₀N : A₀ ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {σ₀ : Equiv.Perm (Fin (n + 1))} {s₀ : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hσ₀ : σ₀ 0 = 0) (hs₀0 : s₀ 0 = -1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = 1) (hA₀Eq : A₀ = spMat σ₀ s₀) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 n := by
  apply Set.Subset.antisymm
  · exact realized_normalizer_subset_evenN0_of_neg_even B h0 hmono hR hA₀N hs₀ hσ₀ hs₀0
      hp₀ hA₀Eq
  · exact realized_evenN0_subset_normalizer_of_neg B h0 hR hA₀N hs₀ hσ₀ hs₀0 hp₀ hA₀Eq

private theorem realized_normalizer_eq_evenAll0_of_neg_odd {n : ℕ} [Finite G]
    (B : Basis3 G (n + 1)) {b₀ : G} (h0 : B.b 0 = b₀)
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (hR : B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA₀N : A₀ ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {σ₀ : Equiv.Perm (Fin (n + 1))} {s₀ : Fin (n + 1) → ZMod 3}
    (hs₀ : IsSign s₀) (hσ₀ : σ₀ 0 = 0) (hs₀0 : s₀ 0 = -1)
    (hp₀ : (∏ i : Fin n, s₀ i.succ) = -1) (hA₀Eq : A₀ = spMat σ₀ s₀) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 n := by
  apply Set.Subset.antisymm
  · exact realized_normalizer_subset_evenAll0_of_neg_odd B h0 hmono hR hA₀N hs₀ hσ₀ hs₀0
      hp₀ hA₀Eq
  · exact realized_evenAll0_subset_normalizer_of_neg B h0 hR hA₀N hs₀ hσ₀ hs₀0 hp₀ hA₀Eq

private theorem localOrth_case_odd [Finite G] {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G}
    {K : Subgroup G} (h0 : B.b 0 = b₀) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (heven : evenFix0 n ⊆ B.realized K)
    (hodd : ∃ A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)),
      ∃ σ s, IsSign s ∧ (σ 0 = 0 ∧ s 0 = 1) ∧ A = spMat σ s ∧
        (∏ i : Fin n, s i.succ) = -1) :
    LocalOrthI B b₀ := by
  let R := B.realized (Subgroup.centralizer ({b₀} : Set G))
  let N := B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))
  have hRmono : R ⊆ monoFix0 n := realized_centralizer_subset_monoFix0 B h0 hmono
  have hevenR : evenFix0 n ⊆ R := fun A hA => realized_mono B hKC (heven hA)
  have hRmul : ∀ A ∈ R, ∀ A' ∈ R, A * A' ∈ R :=
    fun A hA A' hA' => realized_mul B hA hA'
  have hR : R = monoFix0 n := by
    apply Set.Subset.antisymm hRmono
    rcases hodd with ⟨A₀, hA₀, hrep⟩
    exact monoFix0_subset_of_odd hRmul hevenR hA₀ hrep
  by_cases hNeg : ∃ A ∈ N, ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = -1 ∧ A = spMat σ s
  · have hN : N = monoN0 n := realized_normalizer_eq_monoN0_of_neg B h0 hmono hR hNeg
    exact ⟨hR, Or.inr hN⟩
  · have hN : N = monoFix0 n := realized_normalizer_eq_monoFix0_of_no_neg B h0 hmono hNeg hR
    exact ⟨hR, Or.inl hN⟩

private theorem localOrth_case_even [Finite G] {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G}
    {K : Subgroup G} (h0 : B.b 0 = b₀) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (heven : evenFix0 n ⊆ B.realized K)
    (hno : ¬ ∃ A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)),
      ∃ σ s, IsSign s ∧ (σ 0 = 0 ∧ s 0 = 1) ∧ A = spMat σ s ∧
        (∏ i : Fin n, s i.succ) = -1) :
    LocalOrthII B b₀ := by
  let R := B.realized (Subgroup.centralizer ({b₀} : Set G))
  let N := B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))
  have hRmono : R ⊆ monoFix0 n := realized_centralizer_subset_monoFix0 B h0 hmono
  have hevenR : evenFix0 n ⊆ R := fun A hA => realized_mono B hKC (heven hA)
  have hR : R = evenFix0 n := by
    apply Set.Subset.antisymm
    · exact realized_centralizer_subset_evenFix0 B hRmono hno
    · exact hevenR
  by_cases hNeg : ∃ A ∈ N, ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = -1 ∧ A = spMat σ s
  · rcases hNeg with ⟨A₀, hA₀N, σ₀, s₀, hs₀, hσ₀, hs₀0, hA₀Eq⟩
    by_cases hEven : (∏ i : Fin n, s₀ i.succ) = 1
    · have hN : N = evenN0 n :=
        realized_normalizer_eq_evenN0_of_neg_even B h0 hmono hR hA₀N hs₀ hσ₀ hs₀0 hEven hA₀Eq
      exact ⟨hR, Or.inr (Or.inl hN)⟩
    · have hOdd₀ : (∏ i : Fin n, s₀ i.succ) = -1 := by
        rcases prod_eq_one_or_neg_one (fun i : Fin n => s₀ i.succ)
          (fun i => hs₀ i.succ) with h1 | h1
        · exact absurd h1 hEven
        · exact h1
      have hN : N = evenAll0 n :=
        realized_normalizer_eq_evenAll0_of_neg_odd B h0 hmono hR hA₀N hs₀ hσ₀ hs₀0 hOdd₀ hA₀Eq
      exact ⟨hR, Or.inr (Or.inr hN)⟩
  · have hN : N = evenFix0 n := realized_normalizer_eq_evenFix0_of_no_neg B h0 hmono hNeg hR
    exact ⟨hR, Or.inl hN⟩

theorem localOrth_of_monomial [Finite G] {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G}
    {K : Subgroup G} (h0 : B.b 0 = b₀) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hmono : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoN0 n)
    (heven : evenFix0 n ⊆ B.realized K) :
    LocalOrthI B b₀ ∨ LocalOrthII B b₀ := by
  by_cases hodd : ∃ A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)),
      ∃ σ s, IsSign s ∧ (σ 0 = 0 ∧ s 0 = 1) ∧ A = spMat σ s ∧
        (∏ i : Fin n, s i.succ) = -1
  · exact Or.inl (localOrth_case_odd B h0 hKC hmono heven hodd)
  · exact Or.inr (localOrth_case_even B h0 hKC hmono heven hodd)

end CFSG.StandardType.FrameRoute.FS81
