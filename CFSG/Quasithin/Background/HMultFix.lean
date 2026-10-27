module

public import CFSG.Quasithin.Background.HMult
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LinearAlgebra.SchurElemAbelianTwo

public section

namespace CFSG.Quasithin.H.Mult

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix Kronecker LinearAlgebra.Projectivization Pointwise

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

variable (ι) in
@[expose] def kronRightHom (k : ℕ) :
    Matrix (Fin k) (Fin k) K →* Matrix (Fin k × ι) (Fin k × ι) K where
  toFun B := B ⊗ₖ (1 : Matrix ι ι K)
  map_one' := Matrix.one_kronecker_one
  map_mul' B C := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

variable (ι) in
@[expose] def kronGL (k : ℕ) : GL (Fin k) K →* GL (Fin k × ι) K :=
  Units.map (kronRightHom ι k)

theorem kronGL_mulVec (k : ℕ) (B : GL (Fin k) K) (v : Fin k × ι → K) (p : Fin k × ι) :
    (((kronGL ι k B : GL (Fin k × ι) K) : Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ v) p =
      ∑ j, (B : Matrix (Fin k) (Fin k) K) p.1 j * v (j, p.2) := by
  simp only [kronGL, kronRightHom, Units.coe_map, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single p.2]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply, Ne.symm hb]
  · intro hp
    exact (hp (Finset.mem_univ p.2)).elim

theorem kronGL_commute_diagGL (k : ℕ) (B : GL (Fin k) K) (γ : GL ι K) :
    kronGL ι k B * diagGL k γ = diagGL k γ * kronGL ι k B := by
  apply Units.ext
  change ((B : Matrix (Fin k) (Fin k) K) ⊗ₖ (1 : Matrix ι ι K)) *
      ((1 : Matrix (Fin k) (Fin k) K) ⊗ₖ (γ : Matrix ι ι K)) =
    ((1 : Matrix (Fin k) (Fin k) K) ⊗ₖ (γ : Matrix ι ι K)) *
      ((B : Matrix (Fin k) (Fin k) K) ⊗ₖ (1 : Matrix ι ι K))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

theorem kronGL_injective [Nonempty ι] (k : ℕ) :
    Function.Injective (kronGL (ι := ι) (K := K) k) := by
  intro B C h
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  apply Units.ext
  ext p q
  have h2 := congrArg (fun M : Matrix (Fin k × ι) (Fin k × ι) K => M (p, i₀) (q, i₀))
    (congrArg Units.val h)
  simpa [kronGL, kronRightHom, Matrix.kroneckerMap_apply, Matrix.one_apply] using h2

theorem commutant_diag {k : ℕ} {Γ : Subgroup (GL ι K)} (hΓ : HasScalarCommutant Γ)
    (f : (Fin k × ι → K) →+ (Fin k × ι → K))
    (hf : ∀ γ ∈ Γ, ∀ v, f (((diagGL k γ : GL (Fin k × ι) K) :
        Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ v) =
      ((diagGL k γ : GL (Fin k × ι) K) : Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ f v) :
    ∃ B : Matrix (Fin k) (Fin k) K, ∀ v p, f v p = ∑ j, B p.1 j * v (j, p.2) := by
  let blk (j' j : Fin k) : (ι → K) →+ (ι → K) :=
    AddMonoidHom.mk' (fun x i => f (blockVec (k := k) j x) (j', i))
      fun x y => by
        have h : blockVec j (x + y) = blockVec j x + blockVec j y := blockVec_add j x y
        funext i
        rw [h, map_add]
        rfl
  have hblk : ∀ (j' j : Fin k) (γ : GL ι K), γ ∈ Γ → ∀ x : ι → K,
      blk j' j ((γ : Matrix ι ι K) *ᵥ x) =
        (γ : Matrix ι ι K) *ᵥ blk j' j x := by
    intro j' j γ hγ x
    funext i
    have h := congrFun (hf γ hγ (blockVec j x)) (j', i)
    rw [diagGL_blockVec, diagGL_mulVec] at h
    exact h
  choose c hc using fun j' j => hΓ (blk j' j) (hblk j' j)
  refine ⟨Matrix.of fun j' j => c j' j, fun v p => ?_⟩
  calc f v p = f (∑ j : Fin k, blockVec (k := k) j (fun i => v (j, i))) p := by
        rw [sum_blockVec]
    _ = (∑ j : Fin k, f (blockVec (k := k) j (fun i => v (j, i)))) p := by rw [map_sum]
    _ = ∑ j : Fin k, f (blockVec (k := k) j (fun i => v (j, i))) p := by
      rw [Finset.sum_apply]
    _ = ∑ j : Fin k, c p.1 j * v (j, p.2) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := congrFun (hc p.1 j (fun i => v (j, i))) p.2
      simpa [blk, Pi.smul_apply, Prod.mk.eta] using h

theorem mem_centralizer_diag_iff [Finite K] {k : ℕ} {Γ : Subgroup (GL ι K)}
    (hΓ : HasScalarCommutant Γ) {c : MulAut (StdMod (Fin k × ι) K)} :
    c ∈ Subgroup.centralizer (natImage (diagSub k Γ) : Set (MulAut (StdMod (Fin k × ι) K))) ↔
      ∃ B : GL (Fin k) K, c = matAut (kronGL ι k B) := by
  constructor
  · intro hc
    have hf : ∀ γ ∈ Γ, ∀ v, toAddMap c (((diagGL k γ : GL (Fin k × ι) K) :
        Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ v) =
        ((diagGL k γ : GL (Fin k × ι) K) : Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ
          toAddMap c v := by
      intro γ hγ v
      have hmem : matAut (diagGL k γ) ∈ natImage (diagSub k Γ) := by
        exact ⟨⟨diagGL k γ, Subgroup.mem_map_of_mem (diagGL k) hγ⟩, rfl⟩
      have h := Subgroup.mem_centralizer_iff.mp hc (matAut (diagGL k γ)) hmem
      have h2 := congrArg (fun g => toAddMap g v) h
      simpa only [toAddMap_mul, toAddMap_matAut] using h2.symm
    let fc : (Fin k × ι → K) →+ (Fin k × ι → K) :=
      AddMonoidHom.mk' (toAddMap c) (toAddMap_add c)
    obtain ⟨B, hB⟩ := commutant_diag hΓ fc hf
    have hBc : ∀ v p, toAddMap c v p = ∑ j, B p.1 j * v (j, p.2) := by
      intro v p
      simpa [fc] using hB v p
    by_cases hι : Nonempty ι
    · obtain ⟨i₀⟩ := hι
      have hsurj : Function.Surjective B.mulVec := by
        intro w
        let z : Fin k × ι → K := fun p => w p.1
        obtain ⟨g, hg⟩ := c.surjective (Multiplicative.ofAdd z)
        refine ⟨fun j => Multiplicative.toAdd g (j, i₀), ?_⟩
        have hcv : toAddMap c (Multiplicative.toAdd g) = z := by
          simp [toAddMap, ofAdd_toAdd, hg]
        funext i
        have h := hBc (Multiplicative.toAdd g) (i, i₀)
        rw [hcv] at h
        have hz : z (i, i₀) = w i := rfl
        rw [hz] at h
        exact h.symm
      have hunit : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
      refine ⟨hunit.unit, toAddMap_injective fun v => ?_⟩
      funext p
      rw [toAddMap_matAut, kronGL_mulVec, hunit.unit_spec]
      exact hBc v p
    · refine ⟨1, ?_⟩
      apply MulEquiv.ext
      intro x
      apply Multiplicative.toAdd.injective
      funext p
      exact (hι ⟨p.2⟩).elim
  · rintro ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    change matHom (diagGL k γ) * matHom (kronGL ι k B) =
      matHom (kronGL ι k B) * matHom (diagGL k γ)
    rw [← map_mul, ← map_mul, kronGL_commute_diagGL]

private theorem subsingleton_stdMod_of_isEmpty_left {k : ℕ} (h : IsEmpty ι) :
    Subsingleton (StdMod (Fin k × ι) K) := by
  refine ⟨fun x y => ?_⟩
  apply Multiplicative.toAdd.injective
  funext p
  exact (h.false p.2).elim

private theorem subsingleton_stdMod_of_fin_zero {k : ℕ} (hk : k = 0) :
    Subsingleton (StdMod (Fin k × ι) K) := by
  subst hk
  refine ⟨fun x y => ?_⟩
  apply Multiplicative.toAdd.injective
  funext p
  exact absurd p.1.isLt (Nat.not_lt_zero _)

private theorem subgroup_subsingleton_of_subsingleton {W : Type} [Group W]
    (h : Subsingleton W) : Subsingleton (Subgroup W) := by
  refine ⟨fun L L' => Subgroup.ext fun x => ?_⟩
  rw [h.allEq x 1]
  exact ⟨fun _ => L'.one_mem, fun _ => L.one_mem⟩

private theorem exists_ne_zero_fun [Nonempty ι] : ∃ x : ι → K, x ≠ 0 := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨fun i => if i = i₀ then 1 else 0, ?_⟩
  intro h
  have := congrFun h i₀
  simpa using this

private theorem lineSub_eq_of_smul {k : ℕ} {u v : Fin k → K} {c : K} (hc : c ≠ 0)
    (h : u = c • v) : lineSub (ι := ι) u = lineSub (ι := ι) v := by
  subst h
  apply le_antisymm
  · intro w hw
    obtain ⟨x, hx⟩ := hw
    refine ⟨fun i => c * x i, ?_⟩
    rw [hx]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro w hw
    obtain ⟨x, hx⟩ := hw
    refine ⟨fun i => c⁻¹ * x i, ?_⟩
    rw [hx]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp

private theorem lineSub_eq_lineSub_iff (hι : Nonempty ι) {k : ℕ} {u v : Fin k → K}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    lineSub (ι := ι) u = lineSub (ι := ι) v ↔
      Projectivization.mk K u hu = Projectivization.mk K v hv := by
  constructor
  · intro h
    obtain ⟨i₀⟩ := hι
    have hmem : lineEmb (ι := ι) u (Multiplicative.ofAdd (Pi.single i₀ (1 : K))) ∈
        lineSub (ι := ι) v := by
      rw [← h, ← range_lineEmb]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨y i₀, ?_⟩
    funext j
    have hp := congrFun hy (j, i₀)
    simp only [lineEmb_toAdd, toAdd_ofAdd, Pi.single_eq_same,
      mul_one, Pi.smul_apply, smul_eq_mul] at hp ⊢
    rw [hp, mul_comm]
  · intro h
    rw [Projectivization.mk_eq_mk_iff'] at h
    obtain ⟨c, hc⟩ := h
    have hc0 : c ≠ 0 := by
      intro h0
      apply hu
      rw [← hc, h0, zero_smul]
    exact lineSub_eq_of_smul hc0 hc.symm

private def tensorLineSet (k : ℕ) : Set (Subgroup (StdMod (Fin k × ι) K)) :=
  {L | ∃ u : Fin k → K, u ≠ 0 ∧ L = lineSub (ι := ι) u}

private noncomputable def tensorLineSetToProj (k : ℕ) :
    ↥(tensorLineSet (ι := ι) (K := K) k) → ℙ K (Fin k → K) :=
  fun L => Projectivization.mk K (Classical.choose L.2) (Classical.choose_spec L.2).1

private noncomputable def projToLineSet (k : ℕ) :
    ℙ K (Fin k → K) → ↥(tensorLineSet (ι := ι) (K := K) k) :=
  fun p => ⟨lineSub (ι := ι) p.rep, ⟨p.rep, p.rep_nonzero, rfl⟩⟩

private noncomputable def tensorLineSetEquiv (hι : Nonempty ι) (k : ℕ) :
    ↥(tensorLineSet (ι := ι) (K := K) k) ≃ ℙ K (Fin k → K) where
  toFun := tensorLineSetToProj (ι := ι) (K := K) k
  invFun := projToLineSet (ι := ι) (K := K) k
  left_inv L := by
    apply Subtype.ext
    change lineSub (ι := ι) (tensorLineSetToProj (ι := ι) (K := K) k L).rep =
      (L : Subgroup (StdMod (Fin k × ι) K))
    have hrep : Projectivization.mk K (tensorLineSetToProj (ι := ι) (K := K) k L).rep
        (tensorLineSetToProj (ι := ι) (K := K) k L).rep_nonzero =
        tensorLineSetToProj (ι := ι) (K := K) k L := Projectivization.mk_rep _
    have hline : lineSub (ι := ι) (tensorLineSetToProj (ι := ι) (K := K) k L).rep =
        lineSub (ι := ι) (Classical.choose L.2) :=
      (lineSub_eq_lineSub_iff hι
        (tensorLineSetToProj (ι := ι) (K := K) k L).rep_nonzero
        (Classical.choose_spec L.2).1).mpr (by
        simpa [tensorLineSetToProj] using hrep)
    exact hline.trans (Classical.choose_spec L.2).2.symm
  right_inv p := by
    change tensorLineSetToProj (ι := ι) (K := K) k
      (projToLineSet (ι := ι) (K := K) k p) = p
    have hspec := Classical.choose_spec
      (projToLineSet (ι := ι) (K := K) k p).2
    rw [← Projectivization.mk_rep p]
    have hline : lineSub (ι := ι) (Classical.choose
        (projToLineSet (ι := ι) (K := K) k p).2) = lineSub (ι := ι) p.rep :=
      hspec.2.symm
    have hmk : Projectivization.mk K (Classical.choose
          (projToLineSet (ι := ι) (K := K) k p).2) hspec.1 =
        Projectivization.mk K p.rep p.rep_nonzero :=
      (lineSub_eq_lineSub_iff hι hspec.1 p.rep_nonzero).mp hline
    simpa [tensorLineSetToProj] using hmk

private theorem natCard_tensorLineSet (hι : Nonempty ι) [Finite K] :
    Nat.card ↥(tensorLineSet (ι := ι) (K := K) 2) = Nat.card K + 1 := by
  rw [Nat.card_congr (tensorLineSetEquiv (ι := ι) (K := K) hι 2),
    Projectivization.card_of_finrank_two K (Fin 2 → K) (by rw [Module.finrank_fin_fun])]

private theorem odd_sum_pow_of_even {q d : ℕ} (hq : Even q) (hd : 1 ≤ d) :
    Odd (∑ i ∈ Finset.range d, q ^ i) := by
  induction d with
  | zero => omega
  | succ d ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      simpa using (show Odd (1 : ℕ) by norm_num)
    · exact Odd.add_even (ih (by omega)) (hq.pow_of_ne_zero (by omega))

private theorem not_two_dvd_natCard_proj (hι : Nonempty ι) [Finite K] [CharP K 2] :
    ¬ 2 ∣ Nat.card (ℙ K (ι → K)) := by
  have hq : Even (Nat.card K) := by
    have hchar : ringChar K = 2 := ringChar.eq K 2
    have hmod : @Fintype.card K (Fintype.ofFinite K) % 2 = 0 :=
      @FiniteField.even_card_of_char_two K inferInstance (Fintype.ofFinite K) hchar
    rw [@Nat.card_eq_fintype_card K (Fintype.ofFinite K), Nat.even_iff]
    exact hmod
  have hd : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr hι
  rw [Projectivization.card_of_finrank K (ι → K) (n := Fintype.card ι)
    (Module.finrank_fintype_fun_eq_card K)]
  exact (odd_sum_pow_of_even hq hd).not_two_dvd_nat

private theorem not_two_dvd_natCard_tensorLineSet (hι : Nonempty ι) [Finite K] [CharP K 2] :
    ¬ 2 ∣ Nat.card ↥(tensorLineSet (ι := ι) (K := K) 2) := by
  have hq : Even (Nat.card K) := by
    have hchar : ringChar K = 2 := ringChar.eq K 2
    have hmod : @Fintype.card K (Fintype.ofFinite K) % 2 = 0 :=
      @FiniteField.even_card_of_char_two K inferInstance (Fintype.ofFinite K) hchar
    rw [@Nat.card_eq_fintype_card K (Fintype.ofFinite K), Nat.even_iff]
    exact hmod
  rw [natCard_tensorLineSet hι]
  obtain ⟨a, ha⟩ := hq
  rintro ⟨b, hb⟩
  omega

@[expose] def colSub {k : ℕ} (L : Submodule K (ι → K)) : Subgroup (StdMod (Fin k × ι) K) where
  carrier := {v | ∀ j, (fun i => Multiplicative.toAdd v (j, i)) ∈ L}
  one_mem' := fun j => by
    have h : (fun i => Multiplicative.toAdd (1 : StdMod (Fin k × ι) K) (j, i)) = 0 := by
      funext i
      simp
    rw [h]
    exact L.zero_mem
  mul_mem' := by
    intro a b ha hb j
    have h : (fun i => Multiplicative.toAdd (a * b) (j, i)) =
        (fun i => Multiplicative.toAdd a (j, i)) + fun i => Multiplicative.toAdd b (j, i) := by
      funext i
      simp
    rw [h]
    exact L.add_mem (ha j) (hb j)
  inv_mem' := by
    intro a ha j
    have h : (fun i => Multiplicative.toAdd a⁻¹ (j, i)) =
        -fun i => Multiplicative.toAdd a (j, i) := by
      funext i
      simp
    rw [h]
    exact L.neg_mem (ha j)

private theorem natCard_colSub_span_singleton {k : ℕ} {x : ι → K} (hx : x ≠ 0) :
    Nat.card ↥(colSub (k := k) (K ∙ x)) = Nat.card K ^ k := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (funext h)
  let f : (Fin k → K) → ↥(colSub (k := k) (K ∙ x)) := fun c =>
    ⟨Multiplicative.ofAdd fun p => c p.1 * x p.2, by
      intro j
      rw [Submodule.mem_span_singleton]
      exact ⟨c j, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' hcc
      funext j
      have h1 := congrArg
        (fun v : ↥(colSub (k := k) (K ∙ x)) =>
          Multiplicative.toAdd (v : StdMod (Fin k × ι) K) (j, i₀)) hcc
      simp only [f, toAdd_ofAdd] at h1
      exact mul_right_cancel₀ hi₀ h1
    · intro v
      have hmem : ∀ l : Fin k, ∃ c : K, c • x =
          fun i => Multiplicative.toAdd (v : StdMod (Fin k × ι) K) (l, i) :=
        fun l => Submodule.mem_span_singleton.mp (v.2 l)
      choose c hc using hmem
      refine ⟨c, Subtype.ext ?_⟩
      apply Multiplicative.toAdd.injective
      funext p
      have hp := congrFun (hc p.1) p.2
      simp only [f, toAdd_ofAdd, Pi.smul_apply, smul_eq_mul] at hp ⊢
      simpa using hp
  have hcard : Nat.card ↥(colSub (k := k) (K ∙ x)) = Nat.card (Fin k → K) :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [hcard, Module.natCard_eq_pow_finrank (K := K) (V := Fin k → K),
    Module.finrank_fin_fun]

private theorem colSub_span_singleton_injective {k : ℕ} (hk : 0 < k)
    {x y : ι → K}
    (h : colSub (k := k) (K ∙ x) = colSub (k := k) (K ∙ y)) :
    K ∙ x = K ∙ y := by
  have hsub : ∀ {a b : ι → K},
      colSub (k := k) (K ∙ a) = colSub (k := k) (K ∙ b) → K ∙ a ≤ K ∙ b := by
    intro a b hab
    rw [Submodule.span_le]
    let j₀ : Fin k := ⟨0, hk⟩
    let z : StdMod (Fin k × ι) K :=
      Multiplicative.ofAdd fun p => if p.1 = j₀ then a p.2 else 0
    have hza : z ∈ colSub (k := k) (K ∙ a) := by
      intro j
      by_cases hj : j = j₀
      · subst hj
        have hfun : (fun i => Multiplicative.toAdd z (j₀, i)) = a := by
          funext i
          simp [z]
        rw [hfun]
        exact Submodule.subset_span (Set.mem_singleton a)
      · have hzero : (fun i => Multiplicative.toAdd z (j, i)) = 0 := by
          funext i
          simp [z, hj]
        rw [hzero]
        exact (K ∙ a).zero_mem
    rw [hab] at hza
    have hb := hza j₀
    simpa [z] using hb
  exact le_antisymm (hsub h) (hsub h.symm)

private def colLineSet (k : ℕ) : Set (Subgroup (StdMod (Fin k × ι) K)) :=
  {L | ∃ x : ι → K, x ≠ 0 ∧ L = colSub (k := k) (K ∙ x)}

private noncomputable def colLineSetToProj (k : ℕ) :
    ↥(colLineSet (ι := ι) (K := K) k) → ℙ K (ι → K) :=
  fun L => Projectivization.mk K (Classical.choose L.2) (Classical.choose_spec L.2).1

private noncomputable def projToColLineSet (k : ℕ) :
    ℙ K (ι → K) → ↥(colLineSet (ι := ι) (K := K) k) :=
  fun p => ⟨colSub (k := k) (K ∙ p.rep), ⟨p.rep, p.rep_nonzero, rfl⟩⟩

private noncomputable def colLineSetEquiv (hι : Nonempty ι) (k : ℕ) (hk : 0 < k) :
    ↥(colLineSet (ι := ι) (K := K) k) ≃ ℙ K (ι → K) where
  toFun := colLineSetToProj (ι := ι) (K := K) k
  invFun := projToColLineSet (ι := ι) (K := K) k
  left_inv L := by
    apply Subtype.ext
    change colSub (k := k) (K ∙ (colLineSetToProj (ι := ι) (K := K) k L).rep) =
      (L : Subgroup (StdMod (Fin k × ι) K))
    have hrep : Projectivization.mk K (colLineSetToProj (ι := ι) (K := K) k L).rep
        (colLineSetToProj (ι := ι) (K := K) k L).rep_nonzero =
        colLineSetToProj (ι := ι) (K := K) k L := Projectivization.mk_rep _
    have hproj : Projectivization.mk K (colLineSetToProj (ι := ι) (K := K) k L).rep
        (colLineSetToProj (ι := ι) (K := K) k L).rep_nonzero =
        Projectivization.mk K (Classical.choose L.2) (Classical.choose_spec L.2).1 := by
      simpa [colLineSetToProj] using hrep
    have hspan : K ∙ (colLineSetToProj (ι := ι) (K := K) k L).rep =
        K ∙ Classical.choose L.2 := by
      rw [Projectivization.mk_eq_mk_iff] at hproj
      obtain ⟨c, hc⟩ := hproj
      exact (Submodule.span_singleton_eq_span_singleton.mpr ⟨c, hc⟩).symm
    rw [hspan]
    exact (Classical.choose_spec L.2).2.symm
  right_inv p := by
    change colLineSetToProj (ι := ι) (K := K) k
      (projToColLineSet (ι := ι) (K := K) k p) = p
    have hspec := Classical.choose_spec
      (projToColLineSet (ι := ι) (K := K) k p).2
    rw [← Projectivization.mk_rep p]
    have hspan : K ∙ p.rep = K ∙ Classical.choose
        (projToColLineSet (ι := ι) (K := K) k p).2 :=
      colSub_span_singleton_injective hk hspec.2
    have hmk : Projectivization.mk K (Classical.choose
          (projToColLineSet (ι := ι) (K := K) k p).2) hspec.1 =
        Projectivization.mk K p.rep p.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      have hmem : Classical.choose
          (projToColLineSet (ι := ι) (K := K) k p).2 ∈ K ∙ p.rep := by
        rw [hspan]
        exact Submodule.subset_span (Set.mem_singleton _)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨c, hc⟩
    simpa [colLineSetToProj] using hmk

private theorem natCard_colLineSet (hι : Nonempty ι) (k : ℕ) (hk : 0 < k) :
    Nat.card ↥(colLineSet (ι := ι) (K := K) k) = Nat.card (ℙ K (ι → K)) :=
  Nat.card_congr (colLineSetEquiv hι k hk)

private theorem not_two_dvd_natCard_colLineSet (hι : Nonempty ι) (k : ℕ) (hk : 0 < k)
    [Finite K] [CharP K 2] :
    ¬ 2 ∣ Nat.card ↥(colLineSet (ι := ι) (K := K) k) := by
  rw [natCard_colLineSet hι k hk]
  exact not_two_dvd_natCard_proj hι

private theorem map_lineSub_of_normalForm {k : ℕ} {a : MulAut (StdMod (Fin k × ι) K)}
    {A' : MulAut (StdMod ι K)} {σ : K ≃+* K} {B : GL (Fin k) K}
    (hA' : IsSemilinear A' σ)
    (h : ∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap a v p =
      toAddMap A' (fun i => ∑ j, (B : Matrix (Fin k) (Fin k) K) p.1 j * v (j, i)) p.2)
    {u : Fin k → K} (hu : u ≠ 0) :
    (lineSub (ι := ι) u).map a.toMonoidHom =
      lineSub (ι := ι) (fun j => σ (((B : Matrix (Fin k) (Fin k) K) *ᵥ u) j)) := by
  have hBu : (fun j => σ (((B : Matrix (Fin k) (Fin k) K) *ᵥ u) j)) ≠ 0 := by
    intro hzero
    apply hu
    have hB : ((B : Matrix (Fin k) (Fin k) K) *ᵥ u) = 0 := by
      funext j
      exact σ.injective (by simpa using congrFun hzero j)
    have hBinv : ((B⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ
        (((B : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hB, Matrix.mulVec_zero] at hBinv
    exact hBinv.symm
  rw [← range_lineEmb, ← MonoidHom.range_comp, ← range_lineEmb]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨A' x, (normalForm_lineEmb hA' h u x).symm⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := A'.surjective y
    exact MonoidHom.mem_range.mpr ⟨x, normalForm_lineEmb hA' h u x⟩

private theorem map_colSub_of_normalForm [Finite K] {k : ℕ}
    {a : MulAut (StdMod (Fin k × ι) K)}
    {A' : MulAut (StdMod ι K)} {σ : K ≃+* K} {B : GL (Fin k) K}
    (hA' : IsSemilinear A' σ)
    (h : ∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap a v p =
      toAddMap A' (fun i => ∑ j, (B : Matrix (Fin k) (Fin k) K) p.1 j * v (j, i)) p.2)
    {x : ι → K} (hx : x ≠ 0) :
    (colSub (k := k) (K ∙ x)).map a.toMonoidHom =
      colSub (k := k) (K ∙ toAddMap A' x) := by
  have hA'x : toAddMap A' x ≠ 0 := by
    simpa [toAddMap_eq_zero_iff] using hx
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro w ⟨v, hv, rfl⟩
    intro j
    have hmem : ∀ l : Fin k, ∃ c : K, c • x =
        fun i => Multiplicative.toAdd (v : StdMod (Fin k × ι) K) (l, i) :=
      fun l => Submodule.mem_span_singleton.mp (hv l)
    choose c hc using hmem
    have hinner : (fun i => ∑ l, (B : Matrix (Fin k) (Fin k) K) j l *
        Multiplicative.toAdd (v : StdMod (Fin k × ι) K) (l, i)) =
        (∑ l, (B : Matrix (Fin k) (Fin k) K) j l * c l) • x := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← congrFun (hc l) i, Pi.smul_apply, smul_eq_mul]
      ring
    change (fun i => Multiplicative.toAdd (a (v : StdMod (Fin k × ι) K)) (j, i)) ∈
      K ∙ toAddMap A' x
    have hblock : (fun i => Multiplicative.toAdd (a (v : StdMod (Fin k × ι) K)) (j, i)) =
        fun i => toAddMap A' (fun i' => ∑ l, (B : Matrix (Fin k) (Fin k) K) j l *
          Multiplicative.toAdd (v : StdMod (Fin k × ι) K) (l, i')) i := by
      funext i
      have := h (Multiplicative.toAdd (v : StdMod (Fin k × ι) K)) (j, i)
      simpa [toAddMap, ofAdd_toAdd] using this
    rw [hblock]
    refine Submodule.mem_span_singleton.mpr
      ⟨σ (∑ l, (B : Matrix (Fin k) (Fin k) K) j l * c l), ?_⟩
    funext i
    rw [hinner, hA', Pi.smul_apply]
  · rw [Subgroup.card_map_of_injective (by simpa using a.injective),
      natCard_colSub_span_singleton hx, natCard_colSub_span_singleton hA'x]

@[instance_reducible]
private def subgroupSetMulAction {W : Type} [Group W] {A : Subgroup (MulAut W)}
    (S : Set (Subgroup W))
    (hS : ∀ a ∈ A, ∀ L ∈ S, L.map (a.toMonoidHom) ∈ S) : MulAction A ↥S where
  smul a L :=
    ⟨(L : Subgroup W).map (a : MulAut W).toMonoidHom,
      hS (a : MulAut W) a.2 (L : Subgroup W) L.2⟩
  one_smul L := by
    apply Subtype.ext
    change (L : Subgroup W).map ((1 : A) : MulAut W).toMonoidHom = (L : Subgroup W)
    rw [Subgroup.coe_one]
    have h1 : (1 : MulAut W).toMonoidHom = MonoidHom.id W := MonoidHom.ext fun _ => rfl
    rw [h1, Subgroup.map_id]
  mul_smul a b L := by
    apply Subtype.ext
    change (L : Subgroup W).map ((a * b : A) : MulAut W).toMonoidHom =
      ((L : Subgroup W).map ((b : A) : MulAut W).toMonoidHom).map
        ((a : A) : MulAut W).toMonoidHom
    rw [Subgroup.map_map, Subgroup.coe_mul]
    congr 1

theorem exists_fixed_lineSub [Finite K] [CharP K 2]
    {A : Subgroup (MulAut (StdMod (Fin 2 × ι) K))} (hA : IsPGroup 2 A)
    (hform : ∀ a ∈ A, ∃ (A' : MulAut (StdMod ι K)) (σ : K ≃+* K) (B : GL (Fin 2) K),
      IsSemilinear A' σ ∧ ∀ (v : Fin 2 × ι → K) (p : Fin 2 × ι), toAddMap a v p =
        toAddMap A' (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j * v (j, i)) p.2) :
    ∃ u : Fin 2 → K, u ≠ 0 ∧ ∀ a ∈ A,
      (lineSub (ι := ι) u).map a.toMonoidHom = lineSub u := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun i => if i = 0 then 1 else 0, ?_, fun a ha => ?_⟩
    · intro h
      have := congrFun h 0
      simpa using this
    · exact (subgroup_subsingleton_of_subsingleton
        (subsingleton_stdMod_of_isEmpty_left (K := K) (k := 2) hι)).allEq _ _
  · let S := tensorLineSet (ι := ι) (K := K) 2
    have hS : ∀ a ∈ A, ∀ L ∈ S, L.map (a.toMonoidHom) ∈ S := by
      intro a ha L hL
      obtain ⟨A', σ, B, hA', h⟩ := hform a ha
      obtain ⟨u, hu, hL'⟩ := hL
      refine ⟨fun j => σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ u) j), ?_, ?_⟩
      · intro hzero
        apply hu
        have hB : ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ u) = 0 := by
          funext j
          exact σ.injective (by simpa using congrFun hzero j)
        have hBinv : ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
            (((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u) = u := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        rw [hB, Matrix.mulVec_zero] at hBinv
        exact hBinv.symm
      · rw [hL', map_lineSub_of_normalForm hA' h hu]
    let act : MulAction A ↥S := subgroupSetMulAction S hS
    have hodd : ¬ 2 ∣ Nat.card ↥S := not_two_dvd_natCard_tensorLineSet hι
    obtain ⟨L, hL⟩ := @IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card 2 A
      inferInstance hA (Fact.mk Nat.prime_two) ↥S act hodd
    have hfix : ∀ a : A, act.smul a L = L := fun a =>
      (@MulAction.mem_fixedPoints A ↥S inferInstance act L).mp hL a
    obtain ⟨u, hu, hLu⟩ := L.2
    refine ⟨u, hu, fun a ha => ?_⟩
    have h := congrArg Subtype.val (hfix ⟨a, ha⟩)
    change (L : Subgroup (StdMod (Fin 2 × ι) K)).map
      (a : MulAut (StdMod (Fin 2 × ι) K)).toMonoidHom = (L : Subgroup (StdMod (Fin 2 × ι) K)) at h
    rw [hLu] at h
    simpa using h

theorem exists_fixed_colSub_line [Finite K] [CharP K 2] [Nonempty ι] {k : ℕ}
    {A : Subgroup (MulAut (StdMod (Fin k × ι) K))} (hA : IsPGroup 2 A)
    (hform : ∀ a ∈ A, ∃ (A' : MulAut (StdMod ι K)) (σ : K ≃+* K) (B : GL (Fin k) K),
      IsSemilinear A' σ ∧ ∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap a v p =
        toAddMap A' (fun i => ∑ j, (B : Matrix (Fin k) (Fin k) K) p.1 j * v (j, i)) p.2) :
    ∃ x : ι → K, x ≠ 0 ∧ ∀ a ∈ A,
      (colSub (k := k) (K ∙ x)).map a.toMonoidHom = colSub (K ∙ x) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨x, hx⟩ := exists_ne_zero_fun (ι := ι) (K := K)
    refine ⟨x, hx, fun a ha => ?_⟩
    exact (subgroup_subsingleton_of_subsingleton
      (subsingleton_stdMod_of_fin_zero (K := K) (k := 0) rfl)).allEq _ _
  · let S := colLineSet (ι := ι) (K := K) k
    have hS : ∀ a ∈ A, ∀ L ∈ S, L.map (a.toMonoidHom) ∈ S := by
      intro a ha L hL
      obtain ⟨A', σ, B, hA', h⟩ := hform a ha
      obtain ⟨x, hx, hL'⟩ := hL
      refine ⟨toAddMap A' x, ?_, ?_⟩
      · intro hzero
        exact hx ((toAddMap_eq_zero_iff A').mp hzero)
      · rw [hL', map_colSub_of_normalForm hA' h hx]
    let act : MulAction A ↥S := subgroupSetMulAction S hS
    have hodd : ¬ 2 ∣ Nat.card ↥S :=
      not_two_dvd_natCard_colLineSet ‹Nonempty ι› k hk
    obtain ⟨L, hL⟩ := @IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card 2 A
      inferInstance hA (Fact.mk Nat.prime_two) ↥S act hodd
    have hfix : ∀ a : A, act.smul a L = L := fun a =>
      (@MulAction.mem_fixedPoints A ↥S inferInstance act L).mp hL a
    obtain ⟨x, hx, hLx⟩ := L.2
    refine ⟨x, hx, fun a ha => ?_⟩
    have h := congrArg Subtype.val (hfix ⟨a, ha⟩)
    change (L : Subgroup (StdMod (Fin k × ι) K)).map
      (a : MulAut (StdMod (Fin k × ι) K)).toMonoidHom =
        (L : Subgroup (StdMod (Fin k × ι) K)) at h
    rw [hLx] at h
    simpa using h

theorem card_le_of_isElemAbelian_two_centralizer_diag [Finite K] [CharP K 2] [Nonempty ι]
    {Γ : Subgroup (GL ι K)} (hΓ : HasScalarCommutant Γ)
    {A : Subgroup (MulAut (StdMod (Fin 2 × ι) K))} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hAc : A ≤ Subgroup.centralizer
      (natImage (diagSub (ι := ι) (K := K) 2 Γ) : Set (MulAut (StdMod (Fin 2 × ι) K)))) :
    Nat.card A ≤ Nat.card K := by
  let Bof : A → GL (Fin 2) K := fun a =>
    Classical.choose ((mem_centralizer_diag_iff (ι := ι) (K := K) (k := 2) (Γ := Γ) hΓ).mp
      (hAc a.2))
  have hBof : ∀ a : A, (a : MulAut (StdMod (Fin 2 × ι) K)) =
      matAut (kronGL (ι := ι) (K := K) 2 (Bof a)) := fun a =>
    Classical.choose_spec
      ((mem_centralizer_diag_iff (ι := ι) (K := K) (k := 2) (Γ := Γ) hΓ).mp (hAc a.2))
  have hinj : Function.Injective
      (fun B : GL (Fin 2) K => matAut (kronGL (ι := ι) (K := K) 2 B)) :=
    matHom_injective.comp (kronGL_injective (ι := ι) (K := K) 2)
  have hkronOne : kronGL (ι := ι) (K := K) 2 (1 : GL (Fin 2) K) = 1 := by
    apply Units.ext
    ext p q
    simp [kronGL, kronRightHom, Matrix.kroneckerMap_apply, Matrix.one_apply]
  have hkronMul : ∀ B C : GL (Fin 2) K,
      kronGL (ι := ι) (K := K) 2 (B * C) =
        kronGL (ι := ι) (K := K) 2 B * kronGL (ι := ι) (K := K) 2 C :=
    fun B C => map_mul (Units.map (kronRightHom (ι := ι) (K := K) 2)) B C
  let φ : A →* GL (Fin 2) K :=
  { toFun := Bof
    map_one' := by
      apply hinj
      calc matAut (kronGL (ι := ι) (K := K) 2 (Bof 1)) =
          ((1 : A) : MulAut (StdMod (Fin 2 × ι) K)) := (hBof 1).symm
        _ = 1 := Subgroup.coe_one A
        _ = matAut (kronGL (ι := ι) (K := K) 2 (1 : GL (Fin 2) K)) := by
            rw [hkronOne]
            exact (map_one (matHom : GL (Fin 2 × ι) K →*
              MulAut (StdMod (Fin 2 × ι) K))).symm
    map_mul' := by
      intro a b
      apply hinj
      calc matAut (kronGL (ι := ι) (K := K) 2 (Bof (a * b))) =
          ((a * b : A) : MulAut (StdMod (Fin 2 × ι) K)) := (hBof (a * b)).symm
        _ = (a : MulAut (StdMod (Fin 2 × ι) K)) *
            (b : MulAut (StdMod (Fin 2 × ι) K)) := Subgroup.coe_mul A a b
        _ = matAut (kronGL (ι := ι) (K := K) 2 (Bof a)) *
            matAut (kronGL (ι := ι) (K := K) 2 (Bof b)) := by rw [hBof a, hBof b]
        _ = matAut (kronGL (ι := ι) (K := K) 2 (Bof a * Bof b)) := by
            rw [hkronMul]
            exact (map_mul (matHom : GL (Fin 2 × ι) K →*
              MulAut (StdMod (Fin 2 × ι) K)) _ _).symm }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hab' : Bof a = Bof b := hab
    apply Subtype.ext
    calc (a : MulAut (StdMod (Fin 2 × ι) K)) =
        matAut (kronGL (ι := ι) (K := K) 2 (Bof a)) := hBof a
      _ = matAut (kronGL (ι := ι) (K := K) 2 (Bof b)) := by rw [hab']
      _ = (b : MulAut (StdMod (Fin 2 × ι) K)) := (hBof b).symm
  have hAtop : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup A) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hA.1.is_comm.comm x.1 y.1)⟩⟩, fun x hx => ?_⟩
    exact Subtype.ext (by simpa using hA.2 x.1 x.2)
  have hE : CFSG.Open.IsElemAbelian 2 φ.range := by
    have h := CFSG.Open.IsElemAbelian.map hAtop φ
    rwa [Subgroup.map_top] at h
  have hcard : Nat.card φ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hφinj)).symm
  calc Nat.card A = Nat.card φ.range := hcard.symm
    _ ≤ Nat.card K ^ (2 * 2 / 4) :=
        CFSG.LinearAlgebra.SchurElemAbelianTwo.card_le_pow_of_isElemAbelian_two hE
    _ = Nat.card K := by norm_num

end CFSG.Quasithin.H.Mult

end
