module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameLines
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.FS81.D6InnerAux
public import CFSG.LocalAnalysis.StandardType.FS81.RootLineRigid

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open Matrix RootLineAux

variable {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}

theorem vec_mem_K {n : ℕ} {B : Basis3 G (n + 1)} (hB : Adapted B b₀ K E) {v : Coords (n + 1)}
    (hv : v 0 = 0) : B.vec v ∈ K := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  by_cases hi : i = 0
  · subst hi
    rw [hv, ZMod.val_zero, pow_zero]
    exact K.one_mem
  · exact K.pow_mem (hB.2.2 i hi) _

theorem zero_of_vec_mem_K {n : ℕ} {B : Basis3 G (n + 1)} (hB : Adapted B b₀ K E)
    (hb₀ord : orderOf b₀ = 3) (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)) (hb₀E : b₀ ∈ E)
    {v : Coords (n + 1)} (hv : B.vec v ∈ K) : v 0 = 0 := by
  obtain ⟨-, hb0, hbiK⟩ := hB
  have hrest : (List.ofFn fun i : Fin n => B.b i.succ ^ (v i.succ).val).prod ∈ K := by
    apply Subgroup.list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.pow_mem K (hbiK i.succ (Fin.succ_ne_zero i)) _
  have hsplit : B.vec v = B.b 0 ^ (v 0).val *
      (List.ofFn fun i : Fin n => B.b i.succ ^ (v i.succ).val).prod := by
    unfold Basis3.vec
    rw [List.ofFn_succ, List.prod_cons]
  have hpowK : B.b 0 ^ (v 0).val ∈ K := by
    rw [hsplit] at hv
    exact (Subgroup.mul_mem_cancel_right K hrest).mp hv
  have hzp : B.b 0 ^ (v 0).val ∈ Subgroup.zpowers b₀ := by
    rw [hb0]
    exact Subgroup.pow_mem (Subgroup.zpowers b₀) (Subgroup.mem_zpowers b₀) _
  have hE : B.b 0 ^ (v 0).val ∈ E := by
    rw [hb0]
    exact (Subgroup.zpowers_le.mpr hb₀E) (Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _)
  have hone : B.b 0 ^ (v 0).val = 1 :=
    (Subgroup.disjoint_def.mp hdisj) hzp ⟨hE, hpowK⟩
  have hval : (v 0).val = 0 := by
    have hpow1 : b₀ ^ (v 0).val = 1 := by
      rwa [hb0] at hone
    have hdvd : orderOf b₀ ∣ (v 0).val := orderOf_dvd_iff_pow_eq_one.mpr hpow1
    have hdvd3 : 3 ∣ (v 0).val := by
      rwa [hb₀ord] at hdvd
    exact Nat.eq_zero_of_dvd_of_lt hdvd3 (ZMod.val_lt (v 0))
  exact (ZMod.val_eq_zero (v 0)).mp hval

theorem single_add_smul_eq_cons (i j : Fin 6) (c : ZMod 3) :
    (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1 : Coords 8) =
      Fin.cons 0 (Fin.cons 0 (Pi.single i 1 + c • Pi.single j 1)) := by
  ext k
  cases k using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
      smul_zero, add_zero]
  | succ k =>
    cases k using Fin.cases with
    | zero =>
      rw [Fin.cons_succ, Fin.cons_zero, Pi.add_apply, Pi.smul_apply, single_succ, single_succ,
        Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
        Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm, smul_zero, add_zero]
    | succ k =>
      rw [Fin.cons_succ, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, single_succ, single_succ,
        single_succ, single_succ]
      rfl

theorem single_eq_cons (j : Fin 6) :
    (Pi.single j.succ.succ 1 : Coords 8) = Fin.cons 0 (Fin.cons 0 (Pi.single j 1)) := by
  have h := single_add_smul_eq_cons j j 0
  simpa using h

theorem wt_cons_cons (x : Coords 6) : wt (Fin.cons 0 (Fin.cons 0 x) : Coords 8) = wt x := by
  rw [wt_cons_zero, wt_cons_zero]

theorem good_iff_of_acts [Finite G] {B : Basis3 G 8} (hrec : RecOutE7 B b₀) {g : G}
    {X : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hX : B.Acts g X) (v : Coords 8) :
    e7Good v ↔ e7Good (X *ᵥ v) := by
  have hgood : ∀ {g : G} {P : Matrix (Fin 8) (Fin 8) (ZMod 3)}, B.Acts g P →
      (∃ P' : Matrix (Fin 8) (Fin 8) (ZMod 3), P' * P = 1) →
        ∀ v, e7Good v → e7Good (P *ᵥ v) := by
    intro g P hP hPinv v hv
    obtain ⟨P', hP'⟩ := hPinv
    have hPv : P *ᵥ v ≠ 0 := by
      intro h0
      apply hv.ne_zero
      rw [← Matrix.one_mulVec v, ← hP', ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    have hc := isConjLine_map_conj ((hrec.2.1 v hv.ne_zero).mpr hv) g
    rw [line_map_conj hP v] at hc
    exact (hrec.2.1 _ hPv).mp hc
  have hgN : g ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hX
  obtain ⟨X', hX'⟩ := B.exists_acts (Subgroup.inv_mem _ hgN)
  have h1 : X' * X = 1 := by
    have := B.acts_mul hX' hX
    rw [inv_mul_cancel] at this
    exact B.acts_unique this B.acts_one
  have h2 : X * X' = 1 := by
    have := B.acts_mul hX hX'
    rw [mul_inv_cancel] at this
    exact B.acts_unique this B.acts_one
  refine ⟨hgood hX ⟨X', h1⟩ v, fun hv => ?_⟩
  have := hgood hX' ⟨X, h2⟩ _ hv
  rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this

theorem cent_mat [Finite G] (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) {h : G}
    (hh : h ∈ Subgroup.centralizer ({b₀} : Set G)) {N : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hN : B.Acts h N) :
    (∀ i, N i 0 = if i = 0 then 1 else 0) ∧ (∀ j : Fin 7, N 0 j.succ = 0) ∧
      (∃ N' : Matrix (Fin 8) (Fin 8) (ZMod 3), N' * N = 1 ∧ N * N' = 1 ∧ B.Acts h⁻¹ N') ∧
      ∀ v : Coords 8, e7Good v ↔ e7Good (N *ᵥ v) := by
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hA, -, hb₀E, -, -, -⟩ := hHyp
  obtain ⟨hb₀ord, hKC, hKn, -, -, -, -, -⟩ := hA
  obtain ⟨-, hdisj, -, -, -, -⟩ := hCanon
  have hCK : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  have hc_b0 : h * b₀ * h⁻¹ = b₀ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hh]
    simp
  have hcol0 : (fun i => N i 0) = Pi.single (0 : Fin 8) 1 := by
    apply B.vec_injective
    rw [← hN 0, hB.2.1, hc_b0, B.vec_single, hB.2.1]
  have hhN : h ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hN
  obtain ⟨N', hN'⟩ := B.exists_acts (Subgroup.inv_mem _ hhN)
  have h1 : N' * N = 1 := by
    have := B.acts_mul hN' hN
    rw [inv_mul_cancel] at this
    exact B.acts_unique this B.acts_one
  have h2 : N * N' = 1 := by
    have := B.acts_mul hN hN'
    rw [mul_inv_cancel] at this
    exact B.acts_unique this B.acts_one
  refine ⟨fun i => by rw [congrFun hcol0 i, Pi.single_apply], fun j => ?_, ⟨N', h1, h2, hN'⟩,
    good_iff_of_acts hrec hN⟩
  have hconjK : h * B.b j.succ * h⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hCK hh) _).mp (hB.2.2 j.succ (Fin.succ_ne_zero j))
  rw [hN j.succ] at hconjK
  exact zero_of_vec_mem_K hB hb₀ord hdisj hb₀E hconjK

theorem mulVec_apply_zero {N : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hc0 : ∀ i, N i 0 = if i = 0 then 1 else 0) (hr0 : ∀ j : Fin 7, N 0 j.succ = 0)
    (v : Coords 8) : (N *ᵥ v) 0 = v 0 := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp [hc0, hr0]

private instance (x : Fin 6 → ZMod 3) : Decidable (IsSign x) := by
  unfold IsSign
  infer_instance

set_option maxRecDepth 100000 in
private theorem sign_check : ∀ x : Fin 6 → ZMod 3, IsSign x →
    e7Good (Pi.single 1 1 + Fin.cons 0 (Fin.cons 0 x)) → ∏ i, x i = 1 := by
  decide +kernel

theorem stab_e1 [Finite G] (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀) {h : G}
    (hh : h ∈ Subgroup.centralizer ({b₀} : Set G)) {N : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hN : B.Acts h N) (h1 : N *ᵥ Pi.single 1 1 = Pi.single 1 1) :
    (∀ x : Coords 6, N *ᵥ Fin.cons 0 (Fin.cons 0 x) = Fin.cons 0 (Fin.cons 0
      (N.submatrix (fun i : Fin 6 => i.succ.succ) (fun i : Fin 6 => i.succ.succ) *ᵥ x))) ∧
    ∃ σ s, IsSign s ∧ ∏ i, s i = 1 ∧
      N.submatrix (fun i : Fin 6 => i.succ.succ) (fun i : Fin 6 => i.succ.succ) = spMat σ s := by
  obtain ⟨hc0, hr0, ⟨N', hN'N, -, -⟩, hgood⟩ := cent_mat hstd hB hrec hh hN
  have hinj : ∀ u w : Coords 8, N *ᵥ u = N *ᵥ w → u = w := fun u w huw => by
    rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← hN'N, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, huw]
  have hd6 : ∀ i j : Fin 6, i ≠ j → ∀ c : ZMod 3, c ≠ 0 →
      wt (N *ᵥ (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1)) = 2 ∧
      (N *ᵥ (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1)) 1 = 0 := by
    intro i j hij c hc
    obtain ⟨hg, hp, hm⟩ := d6_vec i j hij c hc
    have hu : (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1 : Coords 8) =
        Fin.cons 0 (Fin.cons 0 (Pi.single i 1 + c • Pi.single j 1)) :=
      single_add_smul_eq_cons i j c
    have hu1p : (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1 : Coords 8) ≠
        Pi.single 1 1 := by
      intro h
      have := congrFun h 1
      rw [hu] at this
      simp at this
    have hu1m : Pi.single 1 1 + (Pi.single i.succ.succ 1 + c • Pi.single j.succ.succ 1 : Coords 8) ≠
        0 := by
      intro h
      have := congrFun h 1
      rw [hu] at this
      simp at this
    refine orth_e1 ((hgood _).mp hg) ?_ ?_ ?_ ?_ ?_
    · rw [mulVec_apply_zero hc0 hr0, hu]
      rfl
    · rw [← h1, ← Matrix.mulVec_add]
      exact fun h => hp ((hgood _).mpr h)
    · rw [← h1, ← Matrix.mulVec_sub]
      exact fun h => hm ((hgood _).mpr h)
    · rw [← h1]
      exact fun h => hu1p (hinj _ _ h)
    · intro h
      apply hu1m
      apply hinj
      rw [Matrix.mulVec_add, h1, h, Matrix.mulVec_zero]
  have hr1 : ∀ j : Fin 6, N 1 j.succ.succ = 0 := by
    intro j
    have hjk : j ≠ j + 1 := by
      revert j
      decide
    have hp := (hd6 j (j + 1) hjk 1 one_ne_zero).2
    have hm := (hd6 j (j + 1) hjk (-1) (by decide)).2
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
      Matrix.mulVec_single, smul_eq_mul] at hp hm
    have key : ∀ x y : ZMod 3, x * 1 + 1 * (y * 1) = 0 → x * 1 + -1 * (y * 1) = 0 → x = 0 := by
      decide
    exact key _ _ hp hm
  let N₆ : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
    N.submatrix (fun i : Fin 6 => i.succ.succ) (fun i : Fin 6 => i.succ.succ)
  have hlift : ∀ x : Coords 6,
      N *ᵥ Fin.cons 0 (Fin.cons 0 x) = Fin.cons 0 (Fin.cons 0 (N₆ *ᵥ x)) := by
    intro x
    rw [mulVec_cons_zero N hr0, mulVec_cons_zero (N.submatrix Fin.succ Fin.succ) hr1]
    rfl
  have hinv6 : ∃ P : Matrix (Fin 6) (Fin 6) (ZMod 3), P * N₆ = 1 := by
    refine ⟨N'.submatrix (fun i : Fin 6 => i.succ.succ) (fun i : Fin 6 => i.succ.succ), ?_⟩
    ext a b
    have hab := congrFun (congrFun hN'N a.succ.succ) b.succ.succ
    have hb0 : N 0 b.succ.succ = 0 := hr0 b.succ
    have hb1 : N (Fin.succ 0) b.succ.succ = 0 := hr1 b
    rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, hb0, hb1, mul_zero, mul_zero,
      zero_add, zero_add] at hab
    rw [Matrix.mul_apply]
    convert hab using 1
    · rfl
    · simp [Matrix.one_apply, Fin.succ_inj]
  have h2 : ∀ i j : Fin 6, i ≠ j → wt (N₆ *ᵥ (Pi.single i 1 + Pi.single j 1)) = 2 ∧
      wt (N₆ *ᵥ (Pi.single i 1 - Pi.single j 1)) = 2 := by
    intro i j hij
    constructor
    · have h := (hd6 i j hij 1 one_ne_zero).1
      rw [single_add_smul_eq_cons, hlift, wt_cons_cons, one_smul] at h
      exact h
    · have h := (hd6 i j hij (-1) (by decide)).1
      rw [single_add_smul_eq_cons, hlift, wt_cons_cons, neg_one_smul, ← sub_eq_add_neg] at h
      exact h
  obtain ⟨σ, s, hs, hN₆⟩ := exists_spMat_of_wt_two (n := 6) (by norm_num) N₆ hinv6 h2
  refine ⟨hlift, σ, s, hs, ?_, hN₆⟩
  have hw : e7Good (Pi.single 1 1 + Fin.cons 0 (Fin.cons 0 (fun _ : Fin 6 => (1 : ZMod 3)))) := by
    decide +kernel
  have hNw := (hgood _).mp hw
  rw [Matrix.mulVec_add, h1, hlift, hN₆, spMat_mulVec] at hNw
  simp only [mul_one] at hNw
  have hprod := sign_check (fun k => s (σ.symm k)) (fun i => hs (σ.symm i)) hNw
  rwa [Equiv.prod_comp σ.symm s] at hprod

set_option maxRecDepth 100000 in
private theorem sign_count :
    (Finset.univ.filter fun s : Fin 6 → ZMod 3 => IsSign s ∧ ∏ i, s i = 1).card = 32 := by
  decide +kernel

theorem mulVec_single_one_col (N : Matrix (Fin 8) (Fin 8) (ZMod 3)) (j : Fin 8) :
    N *ᵥ Pi.single j 1 = fun i => N i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem exists_finset_spMat :
    ∃ T : Finset (Matrix (Fin 6) (Fin 6) (ZMod 3)), T.card ≤ 23040 ∧
      ∀ σ s, IsSign s → ∏ i, s i = 1 → spMat σ s ∈ T := by
  refine ⟨((Finset.univ : Finset (Equiv.Perm (Fin 6))) ×ˢ (Finset.univ.filter
    fun s : Fin 6 → ZMod 3 => IsSign s ∧ ∏ i, s i = 1)).image fun p => spMat p.1 p.2, ?_,
    fun σ s hs hp => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, sign_count]
    decide
  · rw [Finset.mem_image]
    refine ⟨(σ, s), ?_, rfl⟩
    rw [Finset.mem_product]
    exact ⟨Finset.mem_univ σ, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs, hp⟩⟩

theorem exists_conj_b1 [Finite G] (hstd : StdAssumptions b₀ K E Row.E7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutE7 B b₀)
    (hcard : Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) = 2903040)
    {v : Coords 8} (hv : e7Good v) (hv0 : v 0 = 0) :
    ∃ k ∈ Subgroup.centralizer ({b₀} : Set G), k ∈ Subgroup.normalizer (B.span : Set G) ∧
      k * B.b 1 * k⁻¹ = B.vec v := by
  classical
  let C := Subgroup.centralizer ({b₀} : Set G)
  obtain ⟨S, hSmem⟩ : ∃ S : Finset (Matrix (Fin 8) (Fin 8) (ZMod 3)),
      ∀ M, M ∈ S ↔ M ∈ B.realized C :=
    ⟨Finset.univ.filter (· ∈ B.realized C), fun M => by simp⟩
  have hS : S.card = 2903040 := by
    have hset : (S : Set (Matrix (Fin 8) (Fin 8) (ZMod 3))) = B.realized C := by
      ext M
      exact hSmem M
    rw [← hcard, ← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  obtain ⟨T, hT, hTmem⟩ := exists_finset_spMat
  let f : Matrix (Fin 8) (Fin 8) (ZMod 3) → Coords 8 := fun M => M *ᵥ Pi.single 1 1
  let Γ : Finset (Coords 8) := Finset.univ.filter fun w => e7Good w ∧ w 0 = 0
  have himg : S.image f ⊆ Γ := by
    intro w hw
    obtain ⟨M, hM, hMw⟩ := Finset.mem_image.mp hw
    obtain ⟨g, hgC, hg⟩ := (hSmem M).mp hM
    obtain ⟨hc0, hr0, -, hgood⟩ := cent_mat hstd hB hrec hgC hg
    rw [← hMw]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hgood _).mp e7Good_e1, ?_⟩
    show (M *ᵥ Pi.single 1 1) 0 = 0
    rw [mulVec_apply_zero hc0 hr0]
    rfl
  have hfib : ∀ w ∈ S.image f, (S.filter fun M => f M = w).card ≤ 23040 := by
    intro w hw
    obtain ⟨M₀, hM₀, hM₀w⟩ := Finset.mem_image.mp hw
    obtain ⟨g₀, hg₀C, hg₀⟩ := (hSmem M₀).mp hM₀
    obtain ⟨-, -, ⟨N₀, hN₀M₀, hM₀N₀, hN₀⟩, -⟩ := cent_mat hstd hB hrec hg₀C hg₀
    have hstab : ∀ M ∈ S.filter (fun M => f M = w),
        ((N₀ * M) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ (N₀ * M) *ᵥ Pi.single 1 1 = Pi.single 1 1) ∧
        (∀ x : Coords 6, (N₀ * M) *ᵥ Fin.cons 0 (Fin.cons 0 x) = Fin.cons 0 (Fin.cons 0
          ((N₀ * M).submatrix (fun i : Fin 6 => i.succ.succ) (fun i : Fin 6 => i.succ.succ) *ᵥ
            x))) ∧
        ∃ σ s, IsSign s ∧ ∏ i, s i = 1 ∧
          (N₀ * M).submatrix (fun i : Fin 6 => i.succ.succ) (fun i : Fin 6 => i.succ.succ) =
            spMat σ s := by
      intro M hM
      obtain ⟨hMS, hfM⟩ := Finset.mem_filter.mp hM
      obtain ⟨g, hgC, hg⟩ := (hSmem M).mp hMS
      have hact : B.Acts (g₀⁻¹ * g) (N₀ * M) := B.acts_mul hN₀ hg
      have hC : g₀⁻¹ * g ∈ C := C.mul_mem (C.inv_mem hg₀C) hgC
      have h1 : (N₀ * M) *ᵥ Pi.single 1 1 = Pi.single 1 1 := by
        rw [← Matrix.mulVec_mulVec]
        change N₀ *ᵥ f M = _
        rw [hfM, ← hM₀w]
        change N₀ *ᵥ (M₀ *ᵥ Pi.single 1 1) = _
        rw [Matrix.mulVec_mulVec, hN₀M₀, Matrix.one_mulVec]
      obtain ⟨hc0, -, -, -⟩ := cent_mat hstd hB hrec hC hact
      refine ⟨⟨?_, h1⟩, stab_e1 hstd hB hrec hC hact h1⟩
      rw [mulVec_single_one_col]
      funext i
      rw [hc0, Pi.single_apply]
    refine (Finset.card_le_card_of_injOn
      (fun M => (N₀ * M).submatrix (fun i : Fin 6 => i.succ.succ) (fun i : Fin 6 => i.succ.succ))
      (fun M hM => ?_) ?_).trans hT
    · obtain ⟨-, -, σ, s, hs, hprod, hsub⟩ := hstab M hM
      simp only [Finset.mem_coe]
      rw [hsub]
      exact hTmem σ s hs hprod
    · intro M hM M' hM' heq
      obtain ⟨⟨h0, h1⟩, hl, -⟩ := hstab M hM
      obtain ⟨⟨h0', h1'⟩, hl', -⟩ := hstab M' hM'
      have hP : N₀ * M = N₀ * M' := by
        refine Matrix.ext_of_mulVec_single fun i => ?_
        cases i using Fin.cases with
        | zero => rw [h0, h0']
        | succ i =>
          cases i using Fin.cases with
          | zero => exact h1.trans h1'.symm
          | succ i =>
            rw [single_eq_cons, hl, hl']
            exact congrArg (fun P => (Fin.cons 0 (Fin.cons 0 (P *ᵥ Pi.single i 1)) : Coords 8))
              heq
      calc M = (M₀ * N₀) * M := by rw [hM₀N₀, one_mul]
        _ = M₀ * (N₀ * M') := by rw [mul_assoc, hP]
        _ = M' := by rw [← mul_assoc, hM₀N₀, one_mul]
  have hle := Finset.card_le_mul_card_image S 23040 hfib
  have hΓ : Γ.card = 126 := card_good_zero
  have heq : S.image f = Γ := Finset.eq_of_subset_of_card_le himg (by omega)
  have hvΓ : v ∈ S.image f := heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hv0⟩
  obtain ⟨M, hM, hMv⟩ := Finset.mem_image.mp hvΓ
  obtain ⟨g, hgC, hg⟩ := (hSmem M).mp hM
  refine ⟨g, hgC, B.mem_normalizer_of_acts hg, ?_⟩
  rw [hg 1, ← hMv]
  change B.vec (fun i => M i 1) = B.vec (M *ᵥ Pi.single 1 1)
  rw [mulVec_single_one_col]

end CFSG.StandardType.FrameRoute.FS81.E7Frame
