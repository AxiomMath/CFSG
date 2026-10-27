module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameMatrix
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusNorm
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField

public section

namespace CFSG.StandardType.SpJoin

open Polynomial Module Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.StandardType.SpNS

variable {F : Type} [Field F] {p : ℕ}

private def planeIdx {n : ℕ} (i : Fin n) : Fin 2 → Fin n ⊕ Fin n :=
  Fin.cases (Sum.inl i) (fun _ => Sum.inr i)

@[simp] private theorem planeIdx_zero {n : ℕ} (i : Fin n) : planeIdx i 0 = Sum.inl i := rfl

@[simp] private theorem planeIdx_one {n : ℕ} (i : Fin n) : planeIdx i 1 = Sum.inr i := rfl

private theorem eq_of_planeIdx_eq_inl {n : ℕ} {i j : Fin n} {a : Fin 2}
    (h : planeIdx i a = Sum.inl j) : i = j := by
  by_cases ha : a = 0
  · subst ha; rw [planeIdx_zero] at h; exact Sum.inl.inj h
  · have ha1 : a = 1 := by fin_cases a <;> simp_all
    subst ha1
    rw [planeIdx_one] at h
    exact absurd h Sum.inr_ne_inl

private theorem eq_of_planeIdx_eq_inr {n : ℕ} {i j : Fin n} {a : Fin 2}
    (h : planeIdx i a = Sum.inr j) : i = j := by
  by_cases ha : a = 0
  · subst ha; rw [planeIdx_zero] at h; exact absurd h Sum.inl_ne_inr
  · have ha1 : a = 1 := by fin_cases a <;> simp_all
    subst ha1
    rw [planeIdx_one] at h
    exact Sum.inr.inj h

private theorem pairMat_mulVec_planeIdx {n : ℕ} (i : Fin n) (g : Matrix (Fin 2) (Fin 2) F)
    (a : Fin 2) :
    pairMat (Sum.inl i) (Sum.inr i) g *ᵥ (Pi.single (planeIdx i a) 1) =
      ∑ b, g b a • (Pi.single (planeIdx i b) 1) := by
  rw [Matrix.mulVec_single_one, Fin.sum_univ_two]
  funext x
  fin_cases a <;>
    · simp only [planeIdx_zero, planeIdx_one, Matrix.col_def, Matrix.transpose_apply, pairMat,
        Pi.single_apply]
      by_cases h1 : x = Sum.inl i <;> by_cases h2 : x = Sum.inr i <;>
        simp [h1, h2, Sum.inl_ne_inr, Sum.inr_ne_inl]

private theorem pairMat_mulVec_single_of_ne {n : ℕ} {x : Fin n ⊕ Fin n} {i : Fin n}
    (h1 : x ≠ Sum.inl i) (h2 : x ≠ Sum.inr i) (g : Matrix (Fin 2) (Fin 2) F) :
    pairMat (Sum.inl i) (Sum.inr i) g *ᵥ (Pi.single x 1) = Pi.single x 1 := by
  rw [Matrix.mulVec_single_one]
  funext y
  by_cases hy1 : y = Sum.inl i
  · subst hy1
    simp [Matrix.col_def, Matrix.transpose_apply, pairMat, h1, h2]
  by_cases hy2 : y = Sum.inr i
  · subst hy2
    simp [Matrix.col_def, Matrix.transpose_apply, pairMat, h1, h2]
  · simp [Matrix.col_def, Matrix.transpose_apply, pairMat_apply_of_ne hy1 hy2, one_apply,
      Pi.single_apply, eq_comm]

private noncomputable def frameTorusMatrix (t : F) (ht : spCompanion t ^ p = 1) {n : ℕ}
    (k : Fin n → ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  ((spPlaneTorus n (spPlaneZetaCompanion t ht)
    (fun i => Multiplicative.ofAdd (k i : ZMod p)) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)

private theorem spPlaneTorus_mulVec_eq_of_support_subset {n : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F) (i : Fin n) (a : Fin 2) :
    ∀ (s : Finset (Fin n)) (f : Fin n → Multiplicative (ZMod p)),
      f i = 1 → (∀ j ∉ s, f j = 1) →
      (((spPlaneTorus n ζ f : StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ (Pi.single (planeIdx i a) 1) =
      Pi.single (planeIdx i a) 1 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro f _ hf
    have hf1 : f = 1 := funext fun j => hf j (Finset.notMem_empty j)
    rw [hf1, map_one, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  | insert j s hj ih =>
    intro f hi hf
    by_cases hfj : f j = 1
    · refine ih f hi fun k hk => ?_
      by_cases hkj : k = j
      · subst hkj; exact hfj
      · exact hf k (by simp [Finset.mem_insert, hkj, hk])
    · have hji : j ≠ i := fun h => hfj (h ▸ hi)
      set g : Fin n → Multiplicative (ZMod p) := fun k => if k = j then 1 else f k with hg
      have hgi : g i = 1 := by simp [hg, Ne.symm hji, hi]
      have hgs : ∀ k ∉ s, g k = 1 := by
        intro k hk
        by_cases hkj : k = j
        · subst hkj; simp [hg]
        · simp only [hg, if_neg hkj]
          exact hf k (by simp [Finset.mem_insert, hkj, hk])
      have hfg : f = Pi.mulSingle j (f j) * g := by
        funext k
        by_cases hkj : k = j
        · subst hkj; simp [hg]
        · simp [hg, hkj, Pi.mulSingle_eq_of_ne hkj]
      have hfix := ih g hgi hgs
      rw [hfg, map_mul]
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [← Matrix.mulVec_mulVec, hfix, spPlaneTorus_mulSingle, coe_lam]
      refine pairMat_mulVec_single_of_ne ?_ ?_ _
      · intro h; exact hji (eq_of_planeIdx_eq_inl (by simpa using h)).symm
      · intro h; exact hji (eq_of_planeIdx_eq_inr (by simpa using h)).symm

private theorem coe_spPlaneTorus_mulVec_planeIdx
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) (a : Fin 2) :
    (((spPlaneTorus n ζ f : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) *ᵥ
        (Pi.single (planeIdx i a) 1) =
      ∑ b, (((ζ (f i) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) b a) •
        (Pi.single (planeIdx i b) 1) := by
  classical
  set g : Fin n → Multiplicative (ZMod p) := fun k => if k = i then 1 else f k with hg
  have hgi : g i = 1 := by simp [hg]
  have hgs : ∀ k ∉ Finset.univ.erase i, g k = 1 := by
    intro k hk
    have hki : k = i := by
      by_contra hne
      exact hk (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩)
    subst hki
    simp [hg]
  have hfg : f = Pi.mulSingle i (f i) * g := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [hg]
    · simp [hg, hk, Pi.mulSingle_eq_of_ne hk]
  have hfix := spPlaneTorus_mulVec_eq_of_support_subset ζ i a (Finset.univ.erase i) g hgi hgs
  conv_lhs =>
    rw [hfg, map_mul]
    simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← Matrix.mulVec_mulVec, hfix, spPlaneTorus_mulSingle, coe_lam]
  exact pairMat_mulVec_planeIdx i ((ζ (f i) : SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) a

private theorem spCompanion_action_of_sq {L : Type*} [Field L] [Algebra F L] (t : F) (ζ : L)
    (hζ2 : ζ ^ 2 = -(algebraMap F L t) * ζ - 1) :
    ∀ (k : ℕ) (a : Fin 2),
      ζ ^ (k + a.val) =
        ∑ b : Fin 2, algebraMap F L
          (((spCompanion t ^ k : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) b a) *
          ζ ^ b.val := by
  intro k
  induction k with
  | zero =>
    intro a
    rw [pow_zero, Nat.zero_add, Matrix.SpecialLinearGroup.coe_one, Fin.sum_univ_two]
    fin_cases a <;> simp [Matrix.one_apply]
  | succ k ih =>
    intro a
    have hk : k + 1 + a.val = (k + a.val) + 1 := by omega
    rw [hk, pow_succ', ih, Finset.mul_sum]
    set m : Matrix (Fin 2) (Fin 2) F :=
      ((spCompanion t ^ k : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hm
    have hmul : ((spCompanion t ^ (k + 1) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        ((spCompanion t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * m := by
      rw [pow_succ', Matrix.SpecialLinearGroup.coe_mul, hm]
    rw [hmul, coe_spCompanion]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, one_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, zero_mul, mul_zero, add_zero, zero_add, map_add, map_mul, map_neg, map_sub,
      map_one]
    ring_nf
    rw [hζ2]
    ring

private theorem normalize_alt {L : Type*} [Field L] [Algebra F L] [Finite F]
    (hF : ringChar F = 2) (ζ : L) (β : LinearMap.BilinForm F L) (hβone : β 1 ζ ≠ 0) :
    ∃ u₀ : L, β u₀ (ζ * u₀) = 1 := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two hF (β 1 ζ)⁻¹
  refine ⟨c • (1 : L), ?_⟩
  have hζu₀ : ζ * (c • (1 : L)) = c • ζ := by rw [mul_smul_comm, mul_one]
  rw [hζu₀]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hcc : c * (c * β 1 ζ) = (c * c) * β 1 ζ := by ring
  rw [hcc, ← hc, inv_mul_cancel₀ hβone]

private theorem alt_frame_values {L : Type*} [Field L] [Algebra F L] (ζ u₀ : L)
    (β : LinearMap.BilinForm F L) (hβalt : β.IsAlt) (hβu₀ : β u₀ (ζ * u₀) = 1) :
    ∀ a b : Fin 2, β (ζ ^ a.val * u₀) (ζ ^ b.val * u₀) =
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul]
  · change β u₀ u₀ = 0; exact hβalt.self_eq_zero u₀
  · change β u₀ (ζ * u₀) = 1; exact hβu₀
  · change β (ζ * u₀) u₀ = -1
    rw [← hβalt.neg_eq u₀ (ζ * u₀), hβu₀]
  · change β (ζ * u₀) (ζ * u₀) = 0; exact hβalt.self_eq_zero _

private theorem linearIndependent_of_pairFrame {V : Type*} [AddCommGroup V] [Module F V]
    (B : V →ₗ[F] V →ₗ[F] F) {n : ℕ} (u : Fin n → Fin 2 → V)
    (hform : ∀ i j a b, B (u i a) (u j b) =
      if i = j then (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b else 0) :
    LinearIndependent F (fun x : Fin n × Fin 2 => u x.1 x.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rintro ⟨i, a⟩
  let b' : Fin 2 := if a = 0 then 1 else 0
  have hMab : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b' ≠ 0 := by
    fin_cases a <;> simp [b']
  have hMb : ∀ c : Fin 2, c ≠ a → (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) c b' = 0 := by
    intro c hc
    fin_cases a <;> fin_cases c <;> first | rfl | (exfalso; exact hc rfl)
  have h := congrArg (fun v => B v (u i b')) hg
  rw [map_sum] at h
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply] at h
  rw [Finset.sum_eq_single (i, a)] at h
  · rw [hform i i a b', if_pos rfl] at h
    have h0 : B 0 (u i b') = 0 := by simp
    rw [h0] at h
    exact (mul_eq_zero.mp h).resolve_right hMab
  · intro x _ hx
    rw [hform x.1 i x.2 b']
    by_cases hxi : x.1 = i
    · rw [if_pos hxi]
      have hx2 : x.2 ≠ a := fun h2 => hx (Prod.ext hxi h2)
      rw [hMb x.2 hx2, mul_zero]
    · rw [if_neg hxi, mul_zero]
  · intro hmem; exact absurd (Finset.mem_univ (i, a)) hmem

private theorem frameForm_single {L : Type*} [Field L] [Algebra F L] {n : ℕ}
    (Φ' : (Fin n → L) ≃ₗ[F] (Fin n ⊕ Fin n → F)) (β : LinearMap.BilinForm F L)
    (hdec' : ∀ d d' : Fin n → L, jForm n F (Φ' d) (Φ' d') = ∑ i, β (d i) (d' i))
    (ζ u₀ : L)
    (hβframe : ∀ a b : Fin 2, β (ζ ^ a.val * u₀) (ζ ^ b.val * u₀) =
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b) :
    ∀ i j a b, jForm n F (Φ' (Pi.single i (ζ ^ a.val * u₀)))
        (Φ' (Pi.single j (ζ ^ b.val * u₀))) =
      if i = j then (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b else 0 := by
  intro i j a b
  rw [hdec']
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, Pi.single_eq_same, hβframe]
      simp
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, LinearMap.map_zero₂]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro l _
      by_cases hl : l = i
      · subst hl
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hij]
        simp
      · rw [Pi.single_eq_of_ne hl]
        simp

private theorem frame_action_of_diagonal {L : Type*} [Field L] [Algebra F L] {n : ℕ}
    (t : F) (ζ u₀ : L) (hζ2 : ζ ^ 2 = -(algebraMap F L t) * ζ - 1)
    (Φ' : (Fin n → L) ≃ₗ[F] (Fin n ⊕ Fin n → F)) (E : Subgroup (StatedSp n F))
    (hdiag : ∀ x ∈ E, ∃ k : Fin n → ℕ, ∀ d : Fin n → L,
      (((x : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).mulVec (Φ' d) =
        Φ' (fun i => ζ ^ k i * d i)) :
    ∀ x ∈ E, ∃ k : Fin n → ℕ, ∀ i a,
      (((x : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).mulVec (Φ' (Pi.single i (ζ ^ a.val * u₀))) =
        ∑ b, (((spCompanion t ^ k i : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) b a) • Φ' (Pi.single i (ζ ^ b.val * u₀)) := by
  intro x hx
  obtain ⟨k, hk⟩ := hdiag x hx
  refine ⟨k, fun i a => ?_⟩
  have h1 : (((x : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).mulVec (Φ' (Pi.single i (ζ ^ a.val * u₀))) =
      Φ' (Pi.single i (ζ ^ (k i + a.val) * u₀)) := by
    rw [hk]
    congr 1
    funext l
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same, Pi.single_eq_same, pow_add, mul_assoc]
    · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, mul_zero]
  have hcomp := spCompanion_action_of_sq (L := L) t ζ hζ2 (k i) a
  have key : Φ' (Pi.single i (ζ ^ (k i + a.val) * u₀)) =
      ∑ b', (((spCompanion t ^ k i : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) b' a) • Φ' (Pi.single i (ζ ^ b'.val * u₀)) := by
    rw [hcomp, Finset.sum_mul]
    have hR : (∑ b', (((spCompanion t ^ k i : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) b' a) • Φ' (Pi.single i (ζ ^ b'.val * u₀))) =
        Φ' (∑ b', (((spCompanion t ^ k i : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) b' a) • Pi.single i (ζ ^ b'.val * u₀)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [map_smul]
    rw [hR, Φ'.injective.eq_iff]
    funext l
    rw [Finset.sum_apply]
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same]
      apply Finset.sum_congr rfl
      intro b' _
      rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def]
      ring
    · rw [Pi.single_eq_of_ne hl]
      symm
      apply Finset.sum_eq_zero
      intro b' _
      rw [Pi.smul_apply, Pi.single_eq_of_ne hl, smul_zero]
  rw [h1, key]

theorem exists_plane_frame [Finite F] (h2 : (2 : F) = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {t : F} (hirr : Irreducible (X ^ 2 + C t * X + 1 : F[X]))
    (hgd : (X ^ 2 + C t * X + 1 : F[X]) ∣ cyclotomic p F) {n : ℕ}
    (E : Subgroup (StatedSp n F)) (hE : IsElemAbelian p E) (hcard : p ^ n ≤ Nat.card E) :
    ∃ u : Fin n → Fin 2 → (Fin n ⊕ Fin n → F),
      LinearIndependent F (fun x : Fin n × Fin 2 => u x.1 x.2) ∧
      (∀ i j a b, jForm n F (u i a) (u j b) =
        if i = j then (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b else 0) ∧
      ∀ x ∈ E, ∃ k : Fin n → ℕ, ∀ i a,
        ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec (u i a) =
          ∑ b, (((spCompanion t ^ k i : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) b a) • u i b := by
  classical
  haveI hchar2 : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK : (p : F) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨fun i => i.elim0, ?_, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      rintro g hg ⟨i, a⟩
      exact i.elim0
    · intro i; exact i.elim0
    · intro x hx
      exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  · set g : F[X] := X ^ 2 + C t * X + 1 with hg
    haveI : Fact (Irreducible g) := ⟨hirr⟩
    have hgd' : g ∣ cyclotomic p F := hgd
    have hdeg : (CoordSL.rootPB g).dim = 2 := SpNS.rootPB_dim_eq_two hp hp2 hpK hgd' hpq
    haveI : Module.Finite F (AdjoinRoot g) := (CoordSL.rootPB g).finite
    have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd'
    have hζp : AdjoinRoot.root g ^ p = 1 := hζo.pow_eq_one
    let ψ : StatedSp n F →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
      (Units.coeHom (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).comp (StatedSp n F).subtype
    have hψ : ∀ y : StatedSp n F, ψ y =
        (((y : GL (Fin n ⊕ Fin n) F)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
      fun _ => rfl
    set S : Set (Module.End F (Fin n ⊕ Fin n → F)) :=
      { y | ∃ x ∈ E, Matrix.toLinAlgEquiv' (((x : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) = y } with hS
    have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have h1 : (a : StatedSp n F) * b = b * a :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      show Matrix.toLinAlgEquiv' (ψ a) * Matrix.toLinAlgEquiv' (ψ b) =
        Matrix.toLinAlgEquiv' (ψ b) * Matrix.toLinAlgEquiv' (ψ a)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h1]
    have hSp : ∀ x ∈ S, x ^ p = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      have h3 : (⟨a, ha⟩ : E) ^ p = 1 := Subtype.ext (hE.2 a ha)
      have h5 : (ψ.comp E.subtype) ⟨a, ha⟩ ^ p = 1 := by rw [← map_pow, h3, map_one]
      change (Matrix.toLinAlgEquiv' (ψ a)) ^ p = 1
      rw [← map_pow, show ψ a ^ p = 1 from h5, map_one]
    have hSB : ∀ x ∈ S, ∀ u w, jForm n F (x u) (x w) = jForm n F u w := by
      rintro _ ⟨a, ha, rfl⟩ u w
      rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
      exact jForm_mulVec_of_eq (mem_statedSp_iff.mp a.2) u w
    obtain ⟨s, κ, hκ, Φ, β, hβalt, hact, hdec⟩ := SpNS.exists_nframe hp hp2 hpK hgd' hdeg
      (SpNS.aeval_root_pow_pred hp hpK hgd' hpq) (jForm_isAlt (n := n) (K := F))
      (jForm_nondegenerate (n := n) (K := F)) S hSc hSp hSB
    let kOf : E → (Fin s → ℕ) := fun x =>
      Classical.choose (hact _ ⟨(x : StatedSp n F), x.2, rfl⟩)
    have hkOf : ∀ x : E, ∀ d w,
        Matrix.toLinAlgEquiv' (ψ (x : StatedSp n F)) (Φ (d, w)) =
          Φ (fun i => AdjoinRoot.root g ^ kOf x i * d i, w) := fun x =>
      Classical.choose_spec (hact _ ⟨(x : StatedSp n F), x.2, rfl⟩)
    let f : E → (Fin s → ZMod p) := fun x i => (kOf x i : ZMod p)
    have hf : Function.Injective f := by
      intro x y hxy
      have hmod : ∀ i, (kOf x i : ZMod p) = (kOf y i : ZMod p) := fun i => congrFun hxy i
      have hpow : ∀ i, AdjoinRoot.root g ^ kOf x i = AdjoinRoot.root g ^ kOf y i := by
        intro i
        have hm : kOf x i % p = kOf y i % p :=
          (ZMod.natCast_eq_natCast_iff' (kOf x i) (kOf y i) p).mp (hmod i)
        calc AdjoinRoot.root g ^ kOf x i
            = AdjoinRoot.root g ^ (kOf x i % p) := pow_eq_pow_mod _ hζp
          _ = AdjoinRoot.root g ^ (kOf y i % p) := by rw [hm]
          _ = AdjoinRoot.root g ^ kOf y i := (pow_eq_pow_mod _ hζp).symm
      have hend : Matrix.toLinAlgEquiv' (ψ (x : StatedSp n F)) =
          Matrix.toLinAlgEquiv' (ψ (y : StatedSp n F)) := by
        apply LinearMap.ext
        intro v
        obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
        rw [hkOf x d w, hkOf y d w]
        congr 2
        funext i
        rw [hpow i]
      have hmat : ψ (x : StatedSp n F) = ψ (y : StatedSp n F) :=
        Matrix.toLinAlgEquiv'.injective hend
      have hgl : ((x : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
          ((y : StatedSp n F) : GL (Fin n ⊕ Fin n) F) :=
        Units.coeHom_injective hmat
      exact Subtype.ext (Subtype.ext hgl)
    have hcardE : Nat.card E ≤ Nat.card (Fin s → ZMod p) :=
      Nat.card_le_card_of_injective f hf
    have hpowcard : Nat.card (Fin s → ZMod p) = p ^ s := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hcardE' : Nat.card E ≤ p ^ s := by rw [hpowcard] at hcardE; exact hcardE
    have hle : n ≤ s :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp (le_trans hcard hcardE')
    have hdimL : Module.finrank F (AdjoinRoot g) = 2 := by
      rw [(CoordSL.rootPB g).finrank, hdeg]
    have hdimV : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    have h1 := LinearEquiv.finrank_eq Φ
    rw [hdimV, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype,
      hdimL, Module.finrank_self] at h1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
    have hcardκ : Fintype.card κ = 0 := by omega
    have hsn : s = n := by omega
    haveI : IsEmpty κ := Fintype.card_eq_zero_iff.mp hcardκ
    subst s
    have hζ2 : (AdjoinRoot.root g) ^ 2 =
        -(algebraMap F (AdjoinRoot g) t) * AdjoinRoot.root g - 1 := by
      have h := AdjoinRoot.aeval_eq (f := g) (p := g)
      rw [AdjoinRoot.mk_self] at h
      change aeval (AdjoinRoot.root g) (X ^ 2 + C t * X + 1) = 0 at h
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_one] at h
      have h' : (AdjoinRoot.root g) ^ 2 + (algebraMap F (AdjoinRoot g) t) *
          AdjoinRoot.root g + 1 = 0 := h
      rw [show -(algebraMap F (AdjoinRoot g) t) * AdjoinRoot.root g - 1 =
          -((algebraMap F (AdjoinRoot g) t) * AdjoinRoot.root g + 1) by ring]
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_assoc] using h'
    haveI : Unique (κ → F) := Pi.uniqueOfIsEmpty _
    set e₀ : (Fin n → AdjoinRoot g) ≃ₗ[F] ((Fin n → AdjoinRoot g) × (κ → F)) :=
      LinearEquiv.ofLinearMap (LinearMap.inl F _ _) (LinearMap.fst F _ _)
        (LinearMap.ext fun x => Prod.ext rfl (Subsingleton.elim _ _))
        (LinearMap.ext fun _ => rfl) with he₀
    set Φ' : (Fin n → AdjoinRoot g) ≃ₗ[F] (Fin n ⊕ Fin n → F) := e₀.trans Φ with hΦ'
    have hΦ'app : ∀ d, Φ' d = Φ (d, 0) := fun _ => rfl
    have hdec' : ∀ d d' : Fin n → AdjoinRoot g,
        jForm n F (Φ' d) (Φ' d') = ∑ i, β (d i) (d' i) := by
      intro d d'
      rw [hΦ'app, hΦ'app, hdec d d' 0 0]
      have h0 : Φ ((0 : Fin n → AdjoinRoot g), (0 : κ → F)) = 0 := by
        rw [show ((0 : Fin n → AdjoinRoot g), (0 : κ → F)) = 0 from rfl, map_zero]
      rw [h0]
      simp
    have hβnd : ∀ u : AdjoinRoot g, (∀ v, β u v = 0) → u = 0 := by
      intro u hu
      have h0 : Φ' (Pi.single (⟨0, hn⟩ : Fin n) u) = 0 := by
        apply (jForm_nondegenerate (n := n) (K := F)).1
        intro y
        obtain ⟨d', rfl⟩ := Φ'.surjective y
        rw [hdec' (Pi.single (⟨0, hn⟩ : Fin n) u) d']
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i = ⟨0, hn⟩
        · subst hi; rw [Pi.single_eq_same, hu]
        · rw [Pi.single_eq_of_ne hi, LinearMap.map_zero₂]
      have h1 : Pi.single (⟨0, hn⟩ : Fin n) u = 0 := Φ'.injective (h0.trans (map_zero Φ').symm)
      simpa using congrFun h1 ⟨0, hn⟩
    let b : Basis (Fin 2) F (AdjoinRoot g) := (CoordSL.rootPB g).basis.reindex (finCongr hdeg)
    have hb0 : b 0 = 1 := by
      have hb : b 0 = AdjoinRoot.root g ^ ((0 : Fin 2) : ℕ) := by
        rw [show b = (CoordSL.rootPB g).basis.reindex (finCongr hdeg) from rfl,
          Module.Basis.reindex_apply, PowerBasis.coe_basis]
        simp only [CoordSL.rootPB, AdjoinRoot.powerBasis_gen]
        rfl
      rw [hb]; simp
    have hb1 : b 1 = AdjoinRoot.root g := by
      have hb : b 1 = AdjoinRoot.root g ^ ((1 : Fin 2) : ℕ) := by
        rw [show b = (CoordSL.rootPB g).basis.reindex (finCongr hdeg) from rfl,
          Module.Basis.reindex_apply, PowerBasis.coe_basis]
        simp only [CoordSL.rootPB, AdjoinRoot.powerBasis_gen]
        rfl
      rw [hb]; simp
    have hβ0 : β 1 (AdjoinRoot.root g) ≠ 0 := by
      have h := SpNS.alt_two_ne_zero b hβalt hβnd
      rw [hb0, hb1] at h
      exact h
    have hF : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two h2
    obtain ⟨u₀, hβu₀⟩ := normalize_alt hF (AdjoinRoot.root g) β hβ0
    have hβframe : ∀ a b' : Fin 2, β ((AdjoinRoot.root g) ^ a.val * u₀)
        ((AdjoinRoot.root g) ^ b'.val * u₀) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b' :=
      alt_frame_values (AdjoinRoot.root g) u₀ β hβalt hβu₀
    let u : Fin n → Fin 2 → (Fin n ⊕ Fin n → F) :=
      fun i a => Φ' (Pi.single i ((AdjoinRoot.root g) ^ a.val * u₀))
    have hform : ∀ i j a b', jForm n F (u i a) (u j b') =
        if i = j then (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b' else 0 :=
      frameForm_single Φ' β hdec' (AdjoinRoot.root g) u₀ hβframe
    have hli : LinearIndependent F (fun x : Fin n × Fin 2 => u x.1 x.2) :=
      linearIndependent_of_pairFrame (jForm n F) u hform
    have hdiag : ∀ x ∈ E, ∃ k : Fin n → ℕ, ∀ d : Fin n → AdjoinRoot g,
        (((x : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).mulVec (Φ' d) =
          Φ' (fun i => AdjoinRoot.root g ^ k i * d i) := by
      intro x hx
      obtain ⟨k, hk⟩ := hact (Matrix.toLinAlgEquiv' (ψ x)) ⟨x, hx, rfl⟩
      refine ⟨k, fun d => ?_⟩
      rw [← Matrix.toLinAlgEquiv'_apply, ← hψ x, hΦ'app d, hk]
      rfl
    have hact' := frame_action_of_diagonal t (AdjoinRoot.root g) u₀ hζ2 Φ' E hdiag
    exact ⟨u, hli, hform, hact'⟩

theorem exists_conj_range_planeTorus_of_frame (t : F) (ht : spCompanion t ^ p = 1) {n : ℕ}
    (E : Subgroup (StatedSp n F)) (u : Fin n → Fin 2 → (Fin n ⊕ Fin n → F))
    (hind : LinearIndependent F (fun x : Fin n × Fin 2 => u x.1 x.2))
    (hform : ∀ i j a b, jForm n F (u i a) (u j b) =
      if i = j then (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) a b else 0)
    (hact : ∀ x ∈ E, ∃ k : Fin n → ℕ, ∀ i a,
      ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec (u i a) =
        ∑ b, (((spCompanion t ^ k i : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) b a) • u i b) :
    ∃ c : StatedSp n F,
      E.map (MulAut.conj c).toMonoidHom ≤ (spPlaneTorus n (spPlaneZetaCompanion t ht)).range := by
  classical
  set v : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → F) :=
    Sum.elim (fun i => u i 0) (fun i => u i 1) with hv
  have hv_apply : ∀ (i : Fin n) (a : Fin 2), v (planeIdx i a) = u i a := by
    intro i a
    fin_cases a <;> rfl
  have hvli : LinearIndependent F v := by
    have hφ : Function.Injective
        (fun s : Fin n ⊕ Fin n => Sum.elim (fun i => (i, (0 : Fin 2)))
          (fun i => (i, (1 : Fin 2))) s) := by
      intro s t h
      cases s with
      | inl i =>
        cases t with
        | inl j => simpa using congrArg Prod.fst h
        | inr j => simp at h
      | inr i =>
        cases t with
        | inl j => simp at h
        | inr j => simpa using congrArg Prod.fst h
    have hcomp := hind.comp (fun s : Fin n ⊕ Fin n => Sum.elim (fun i => (i, (0 : Fin 2)))
      (fun i => (i, (1 : Fin 2))) s) hφ
    convert hcomp using 2
    ext s
    cases s <;> rfl
  have hformJ : ∀ r s : Fin n ⊕ Fin n, jForm n F (v r) (v s) = jMat n F r s := by
    rintro (i | i) (j | j)
    · have h := hform i j 0 0
      simpa [hv, jMat, Matrix.fromBlocks_apply₁₁] using h
    · have h := hform i j 0 1
      simpa [hv, jMat, Matrix.fromBlocks_apply₁₂, Matrix.one_apply] using h
    · have h := hform i j 1 0
      by_cases hij : i = j
      · subst hij
        simpa [hv, jMat, Matrix.fromBlocks_apply₂₁, Matrix.one_apply] using h
      · have h' : jForm n F (u i 1) (u j 0) = 0 := by simpa [hij] using h
        simpa [hv, jMat, Matrix.fromBlocks_apply₂₁, Matrix.one_apply, Pi.neg_apply, hij]
          using h'
    · have h := hform i j 1 1
      simpa [hv, jMat, Matrix.fromBlocks_apply₂₂] using h
  set c₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.of fun r s => v s r with hc₀
  have hc₀col : c₀.col = v := by
    funext s
    rfl
  have hli : LinearIndependent F c₀.col := by
    rw [hc₀col]
    exact hvli
  have hunit : IsUnit c₀ := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hdet : c₀.det ≠ 0 := by
    have h := (Matrix.isUnit_iff_isUnit_det c₀).mp hunit
    exact IsUnit.ne_zero h
  set A₀ : GL (Fin n ⊕ Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero c₀ hdet with hA₀
  have hA₀mat : ((A₀ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = c₀ := by
    rw [hA₀]
    rfl
  have hJ : c₀ᵀ * jMat n F * c₀ = jMat n F := by
    ext r s
    have h1 := jForm_mulVec (n := n) (K := F) c₀ (Pi.single r 1) (Pi.single s 1)
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, hc₀col,
      hformJ r s] at h1
    simpa [Matrix.toBilin'_single] using h1.symm
  have hsp : A₀ ∈ StatedSp n F := by
    rw [mem_statedSp_iff]
    simpa [jMat, hA₀mat] using hJ
  set c₁ : StatedSp n F := ⟨A₀, hsp⟩ with hc₁
  have hc₁mat : ((c₁ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = c₀ := by
    rw [hc₁]
    exact hA₀mat
  have hxT : ∀ x ∈ E, ∃ k : Fin n → ℕ,
      ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * c₀ =
        c₀ * frameTorusMatrix t ht k := by
    intro x hx
    obtain ⟨k, hk⟩ := hact x hx
    refine ⟨k, ?_⟩
    apply Matrix.ext
    intro r s
    have hcols : ∀ s' : Fin n ⊕ Fin n,
        (((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * c₀) *ᵥ
          (Pi.single s' 1) =
        (c₀ * frameTorusMatrix t ht k) *ᵥ (Pi.single s' 1) := by
      rintro (i | i)
      · have hζ : spPlaneZetaCompanion t ht
            (Multiplicative.ofAdd (((k i : ℕ) : ZMod p))) = spCompanion t ^ k i := by
          rw [spPlaneZetaCompanion]
          exact CFSG.StandardType.TableBSymp.zmodPowHom_natCast ht (k i)
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        have hcv : c₀ *ᵥ (Pi.single (Sum.inl i) 1) = u i 0 := by
          rw [Matrix.mulVec_single_one, hc₀col]
          exact hv_apply i 0
        rw [hcv, hk i 0]
        rw [show (Sum.inl i : Fin n ⊕ Fin n) = planeIdx i 0 from rfl]
        rw [frameTorusMatrix]
        rw [coe_spPlaneTorus_mulVec_planeIdx]
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, hc₀col, hv_apply, hζ]
      · have hζ : spPlaneZetaCompanion t ht
            (Multiplicative.ofAdd (((k i : ℕ) : ZMod p))) = spCompanion t ^ k i := by
          rw [spPlaneZetaCompanion]
          exact CFSG.StandardType.TableBSymp.zmodPowHom_natCast ht (k i)
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        have hcv : c₀ *ᵥ (Pi.single (Sum.inr i) 1) = u i 1 := by
          rw [Matrix.mulVec_single_one, hc₀col]
          exact hv_apply i 1
        rw [hcv, hk i 1]
        rw [show (Sum.inr i : Fin n ⊕ Fin n) = planeIdx i 1 from rfl]
        rw [frameTorusMatrix]
        rw [coe_spPlaneTorus_mulVec_planeIdx]
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, hc₀col, hv_apply, hζ]
    have h := congrFun (hcols s) r
    simpa [Matrix.mulVec_single_one] using h
  refine ⟨c₁⁻¹, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := hxT x hx
  refine ⟨fun i => Multiplicative.ofAdd (k i : ZMod p), ?_⟩
  have hxTc : x * c₁ = c₁ * (spPlaneTorus n (spPlaneZetaCompanion t ht)
      (fun i => Multiplicative.ofAdd (k i : ZMod p))) := by
    apply statedSp_ext
    simpa [Subgroup.coe_mul, Units.val_mul, hc₁mat, frameTorusMatrix] using hk
  have hconj : c₁⁻¹ * x * c₁ = spPlaneTorus n (spPlaneZetaCompanion t ht)
      (fun i => Multiplicative.ofAdd (k i : ZMod p)) := by
    calc c₁⁻¹ * x * c₁ = c₁⁻¹ * (x * c₁) := by group
      _ = c₁⁻¹ * (c₁ * (spPlaneTorus n (spPlaneZetaCompanion t ht)
            (fun i => Multiplicative.ofAdd (k i : ZMod p)))) := by rw [hxTc]
      _ = spPlaneTorus n (spPlaneZetaCompanion t ht)
            (fun i => Multiplicative.ofAdd (k i : ZMod p)) := by group
  change spPlaneTorus n (spPlaneZetaCompanion t ht)
      (fun i => Multiplicative.ofAdd (k i : ZMod p)) = MulAut.conj c₁⁻¹ x
  rw [MulAut.conj_apply, inv_inv]
  exact hconj.symm

end CFSG.StandardType.SpJoin

