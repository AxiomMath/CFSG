module
public import CFSG.RankThree.GF2n.Smith81.LinTLOfConj
public import CFSG.RankThree.GF2n.Smith81.SubConfigWidth

public section

namespace CFSG.RankThree.GF2n.Smith81.MS80NoA2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

private theorem s81w_charP_two {K : Type} [Field K] [Finite K] {f : ℕ} (h : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, h]
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 2 ^ f := by
    rw [← hcard, hn]
    exact dvd_pow_self _ (PNat.ne_zero n)
  have hpar : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  have hc := ringChar.charP K
  rw [hpar] at hc
  exact hc


private lemma mem_ker_iff_dot {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) :
    v ∈ LinearMap.ker (Matrix.mulVecLin A) ↔ ∀ w, (Aᵀ *ᵥ w) ⬝ᵥ v = 0 := by
  have key : ∀ w, (Aᵀ *ᵥ w) ⬝ᵥ v = w ⬝ᵥ (A *ᵥ v) := by
    intro w
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  simp only [key, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h w
    rw [h]; simp
  · intro h
    ext i
    have := h (Pi.single i 1)
    simpa using this

private lemma mem_range_self' {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) : X *ᵥ v ∈ LinearMap.range (Matrix.mulVecLin X) := ⟨v, by simp⟩

theorem ker_eq_of_range_transpose_eq {K : Type} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K)
    (h : LinearMap.range (Matrix.mulVecLin Aᵀ) = LinearMap.range (Matrix.mulVecLin Bᵀ)) :
    LinearMap.ker (Matrix.mulVecLin A) = LinearMap.ker (Matrix.mulVecLin B) := by
  ext v
  rw [mem_ker_iff_dot, mem_ker_iff_dot]
  constructor
  · intro hv w
    have : Bᵀ *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin Aᵀ) := by
      rw [h]; exact mem_range_self' Bᵀ w
    obtain ⟨u, hu⟩ := this
    simp only [Matrix.mulVecLin_apply] at hu
    rw [← hu]; exact hv u
  · intro hv w
    have : Aᵀ *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin Bᵀ) := by
      rw [← h]; exact mem_range_self' Aᵀ w
    obtain ⟨u, hu⟩ := this
    simp only [Matrix.mulVecLin_apply] at hu
    rw [← hu]; exact hv u

private lemma range_le_ker {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (hX : X * X = 0) (v : Fin n → K)
    (hv : v ∈ LinearMap.range (Matrix.mulVecLin X)) : X *ᵥ v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  simp [Matrix.mulVec_mulVec, hX]

private lemma mem_ker_of_range {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (hX : X * X = 0) (v : Fin n → K)
    (hv : v ∈ LinearMap.range (Matrix.mulVecLin X)) :
    v ∈ LinearMap.ker (Matrix.mulVecLin X) := by
  simpa using range_le_ker X hX v hv

private lemma mem_range_self {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) : X *ᵥ v ∈ LinearMap.range (Matrix.mulVecLin X) := ⟨v, by simp⟩

theorem flag_of_range_eq {K : Type} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (hA : A * A = 0) (hB : B * B = 0)
    (h : LinearMap.range (Matrix.mulVecLin A) = LinearMap.range (Matrix.mulVecLin B) ∨
      LinearMap.ker (Matrix.mulVecLin A) = LinearMap.ker (Matrix.mulVecLin B)) :
    ∀ v, A *ᵥ v ∈ LinearMap.ker (Matrix.mulVecLin B) ∧
      (v ∈ LinearMap.ker (Matrix.mulVecLin B) → A *ᵥ v ∈ LinearMap.range (Matrix.mulVecLin B)) ∧
      (v ∈ LinearMap.range (Matrix.mulVecLin B) → A *ᵥ v = 0) := by
  intro v
  rcases h with h | h
  · refine ⟨?_, ?_, ?_⟩
    · exact mem_ker_of_range B hB _ (h ▸ mem_range_self A v)
    · intro _; exact h ▸ mem_range_self A v
    · intro hv; exact range_le_ker A hA v (h ▸ hv)
  · have hrk : ∀ w, w ∈ LinearMap.range (Matrix.mulVecLin A) →
        w ∈ LinearMap.ker (Matrix.mulVecLin B) := fun w hw => h ▸ mem_ker_of_range A hA w hw
    refine ⟨?_, ?_, ?_⟩
    · exact hrk _ (mem_range_self A v)
    · intro hv
      have : A *ᵥ v = 0 := by
        rw [← h] at hv; simpa using hv
      rw [this]; exact Submodule.zero_mem _
    · intro hv
      have hv' := mem_ker_of_range B hB v hv
      rw [← h] at hv'; simpa using hv'

private def Pf {K : Type} [Field K] {n : ℕ} (c H : Submodule K (Fin n → K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) : Prop :=
  ∀ v : Fin n → K, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ H ∧
      (v ∈ H → (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ c) ∧
      (v ∈ c → (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v)

private lemma Pf_one {K : Type} [Field K] {n : ℕ} (c H : Submodule K (Fin n → K)) :
    Pf c H (1 : Matrix.GeneralLinearGroup (Fin n) K) := by
  intro v
  simp

private lemma Pf_preserve_H {K : Type} [Field K] {n : ℕ} {c H : Submodule K (Fin n → K)}
    {g : Matrix.GeneralLinearGroup (Fin n) K} (hg : Pf c H g) {v : Fin n → K} (hv : v ∈ H) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ H := by
  have := H.add_mem (hg v).1 hv
  simpa using this

private lemma Pf_mul {K : Type} [Field K] {n : ℕ} {c H : Submodule K (Fin n → K)}
    (hcH : c ≤ H) {g h : Matrix.GeneralLinearGroup (Fin n) K} (hg : Pf c H g) (hh : Pf c H h) :
    Pf c H (g * h) := by
  intro v
  have e : ((g * h : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
      = (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    rw [Units.val_mul, Matrix.mulVec_mulVec]
  rw [e]
  have dec : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v) - v
      = ((g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v)
          - (h : Matrix (Fin n) (Fin n) K) *ᵥ v)
        + ((h : Matrix (Fin n) (Fin n) K) *ᵥ v - v) := by abel
  refine ⟨?_, ?_, ?_⟩
  · rw [dec]; exact H.add_mem ((hg _).1) ((hh v).1)
  · intro hv
    rw [dec]
    exact c.add_mem ((hg _).2.1 (Pf_preserve_H hh hv)) ((hh v).2.1 hv)
  · intro hv
    rw [(hh v).2.2 hv, (hg v).2.2 hv]

private lemma Pf_inv {K : Type} [Field K] {n : ℕ} {c H : Submodule K (Fin n → K)}
    {g : Matrix.GeneralLinearGroup (Fin n) K} (hg : Pf c H g) : Pf c H g⁻¹ := by
  intro v
  set u : Fin n → K := ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
    with hu
  have hgu : (g : Matrix (Fin n) (Fin n) K) *ᵥ u = v := by
    rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e : u - v = -((g : Matrix (Fin n) (Fin n) K) *ᵥ u - u) := by rw [hgu]; abel
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; exact H.neg_mem (hg u).1
  · intro hv
    have huH : u ∈ H := by
      have h1 : u = v - ((g : Matrix (Fin n) (Fin n) K) *ᵥ u - u) := by rw [hgu]; abel
      rw [h1]; exact H.sub_mem hv (hg u).1
    rw [e]; exact c.neg_mem ((hg u).2.1 huH)
  · intro hv
    have : (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v := (hg v).2.2 hv
    rw [hu]
    calc _ = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) := by rw [this]
      _ = v := by rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp

private lemma Pf_pow_four {K : Type} [Field K] [CharP K 2] {n : ℕ} {c H : Submodule K (Fin n → K)}
    {g : Matrix.GeneralLinearGroup (Fin n) K} (hg : Pf c H g) : g ^ 4 = 1 := by
  set M : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hM
  let N : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.mulVecLin M - LinearMap.id
  have hN : ∀ v, N v = M *ᵥ v - v := fun v => by simp [N]
  have hMv : ∀ v, M *ᵥ v = v + N v := fun v => by rw [hN]; abel
  have h3 : ∀ v, N (N (N v)) = 0 := by
    intro v
    have h1 : N v ∈ H := by rw [hN]; exact (hg v).1
    have h2 : N (N v) ∈ c := by rw [hN]; exact (hg _).2.1 h1
    have := (hg (N (N v))).2.2 h2
    rw [hN, this]; simp
  have hdbl : ∀ x : Fin n → K, x + x = 0 := by
    intro x; ext i; simp [CharTwo.add_self_eq_zero]
  have hsq : ∀ x, M *ᵥ (M *ᵥ x) = x + N (N x) := by
    intro x
    rw [hMv x, Matrix.mulVec_add, hMv x, hMv (N x)]
    have := hdbl (N x)
    calc x + N x + (N x + N (N x)) = x + (N x + N x) + N (N x) := by abel
      _ = _ := by rw [this]; abel
  have h4 : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ (M *ᵥ v))) = v := by
    intro v
    rw [hsq, hsq]
    have e : N (N (v + N (N v))) = N (N v) := by
      rw [map_add, map_add]
      have : N (N (N (N v))) = 0 := h3 (N v)
      rw [this]; simp
    rw [e]
    have := hdbl (N (N v))
    calc v + N (N v) + N (N v) = v + (N (N v) + N (N v)) := by abel
      _ = v := by rw [this]; simp
  have hpow : M ^ 4 = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, Matrix.one_mulVec]
    have : M ^ 4 *ᵥ v = M *ᵥ (M *ᵥ (M *ᵥ (M *ᵥ v))) := by
      simp [pow_succ, Matrix.mulVec_mulVec, mul_assoc]
    rw [this, h4]
  apply Units.ext
  simpa [hM] using hpow

theorem pow_four_of_mem_closure_flag {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (c H : Submodule K (Fin n → K)) (hcH : c ≤ H) (S : Set (Matrix.GeneralLinearGroup (Fin n) K))
    (hS : ∀ g ∈ S, ∀ v : Fin n → K, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ H ∧
      (v ∈ H → (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ c) ∧
      (v ∈ c → (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v)) :
    ∀ g ∈ Subgroup.closure S, g ^ 4 = 1 := by
  intro g hg
  have : Pf c H g := by
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hS x hx
    | one => exact Pf_one c H
    | mul x y _ _ hx hy => exact Pf_mul hcH hx hy
    | inv x _ hx => exact Pf_inv hx
  exact Pf_pow_four this

private lemma sq_sub_one_eq_zero {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) K) (hg : g * g = 1) :
    ((g : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  have h1 : (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, hg]; rfl
  have h2 : ∀ X : Matrix (Fin n) (Fin n) K, X + X = 0 := by
    intro X; ext i j; simp [CharTwo.add_self_eq_zero]
  calc ((g : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1)
      = (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) + 1
        - ((g : Matrix (Fin n) (Fin n) K) + (g : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
    _ = 0 := by rw [h1, h2, h2]; simp

private lemma zpow_parity {H : Type} [Group H] (g : H) (hg : g * g = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have hs2' : g ^ (2 : ℤ) = 1 := by rw [zpow_two, hg]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hs2', one_zpow]
  · right
    rw [zpow_add, zpow_mul, hs2', one_zpow, one_mul, zpow_one]

section Helpers

variable {G : Type} [Group G]

theorem mem_comm_sup_iff_of_coord' {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (hN : S ≤ Subgroup.normalizer (V : Set G))
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (hψ : ∀ (s : S) (v w : V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        act (φ s) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hZV : Z ≤ V) {s : S}
    (hrel : ∀ k : ℤ, LinearMap.range (act (φ (s ^ k)) - 1).mulVecLin ≤
      LinearMap.range (act (φ s) - 1).mulVecLin) {g : G} (hg : g ∈ V) :
    g ∈ ⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z ↔
      Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨g, hg⟩)) ∈
        LinearMap.range (act (φ s) - 1).mulVecLin := by
  let F : ↥V → (ι → K) := fun v => Multiplicative.toAdd (ψ (QuotientGroup.mk v))
  have Fmul : ∀ a b : ↥V, F (a * b) = F a + F b := by
    intro a b
    show Multiplicative.toAdd (ψ (QuotientGroup.mk (a * b))) = _
    rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
  have Finv : ∀ a : ↥V, F a⁻¹ = - F a := by
    intro a
    show Multiplicative.toAdd (ψ (QuotientGroup.mk a⁻¹)) = _
    rw [QuotientGroup.mk_inv, map_inv, toAdd_inv]
  have Fzero : ∀ a : ↥V, F a = 0 ↔ (a : G) ∈ Z := by
    intro a
    have e : F a = 0 ↔ ψ (QuotientGroup.mk a) = 1 := by
      show Multiplicative.toAdd (ψ (QuotientGroup.mk a)) = 0 ↔ _
      constructor
      · intro h
        have := congrArg Multiplicative.ofAdd h
        simpa using this
      · intro h; rw [h]; rfl
    rw [e, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hsV : ∀ (u : S), ∀ v ∈ V, (u : G) * v * (u : G)⁻¹ ∈ V := fun u v hv =>
    (Subgroup.mem_normalizer_iff.mp (hN u.2) v).mp hv
  have hcV : ∀ (u : S), ∀ v ∈ V, ⁅v, (u : G)⁆ ∈ V := by
    intro u v hv
    have e : ⁅v, (u : G)⁆ = v * ((u : G) * v⁻¹ * (u : G)⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv (hsV u _ (V.inv_mem hv))
  have hψF : ∀ (u : S) (v w : ↥V), (w : G) = (u : G) * v * (u : G)⁻¹ →
      F w = act (φ u) *ᵥ F v :=
    fun u v w h => hψ u v w h
  have Fcomm : ∀ (u : S) (v : ↥V),
      F ⟨⁅(v : G), (u : G)⁆, hcV u v v.2⟩ = (act (φ u) - 1) *ᵥ (- F v) := by
    intro u v
    have hw : (u : G) * (v⁻¹ : ↥V) * (u : G)⁻¹ ∈ V := hsV u _ (v⁻¹).2
    have e : (⟨⁅(v : G), (u : G)⁆, hcV u v v.2⟩ : ↥V) = v * ⟨_, hw⟩ := by
      ext; simp [commutatorElement_def, mul_assoc]
    rw [e, Fmul, hψF u v⁻¹ ⟨_, hw⟩ rfl, Finv, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_neg]
    abel
  constructor
  · intro hmem
    let P : Subgroup G :=
      { carrier := {x | ∃ hx : x ∈ V, F ⟨x, hx⟩ ∈ LinearMap.range (act (φ s) - 1).mulVecLin}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨V.mul_mem ha hb, ?_⟩
          have : F ⟨a * b, V.mul_mem ha hb⟩ = F ⟨a, ha⟩ + F ⟨b, hb⟩ := Fmul ⟨a, ha⟩ ⟨b, hb⟩
          rw [this]; exact Submodule.add_mem _ ha' hb'
        one_mem' := ⟨V.one_mem, by
          have : F ⟨1, V.one_mem⟩ = 0 := (Fzero _).mpr Z.one_mem
          rw [this]; exact Submodule.zero_mem _⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨V.inv_mem ha, ?_⟩
          have : F ⟨a⁻¹, V.inv_mem ha⟩ = - F ⟨a, ha⟩ := Finv ⟨a, ha⟩
          rw [this]; exact Submodule.neg_mem _ ha' }
    have hle : ⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z ≤ P := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro v hv t ht
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
        have e : ((s : G) ^ k) = ((s ^ k : S) : G) := by simp
        rw [e]
        refine ⟨hcV (s ^ k) v hv, ?_⟩
        rw [Fcomm (s ^ k) ⟨v, hv⟩]
        exact hrel k (LinearMap.mem_range.mpr ⟨_, rfl⟩)
      · intro z hz
        exact ⟨hZV hz, by rw [(Fzero ⟨z, hZV hz⟩).mpr hz]; exact Submodule.zero_mem _⟩
    obtain ⟨_, h⟩ := hle hmem
    exact h
  · rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ := ψ.surjective (Multiplicative.ofAdd (- u))
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    have hFw : F w = - u := by
      show Multiplicative.toAdd (ψ (QuotientGroup.mk w)) = _
      rw [hw]; rfl
    have hFc : F ⟨_, hcV s w w.2⟩ = F ⟨g, hg⟩ := by
      rw [Fcomm s w, hFw, neg_neg]
      exact hu
    have hz : g * (⁅(w : G), (s : G)⁆)⁻¹ ∈ Z := by
      have h0 : F (⟨g, hg⟩ * (⟨_, hcV s w w.2⟩ : ↥V)⁻¹) = 0 := by
        rw [Fmul, Finv, hFc, add_neg_cancel]
      simpa using (Fzero _).mp h0
    have e : g = (g * (⁅(w : G), (s : G)⁆)⁻¹) * ⁅(w : G), (s : G)⁆ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz)
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator w.2 (Subgroup.mem_zpowers _)))

theorem range_eq_of_comm_sup_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (h : SectionAct K S V Z φ act) (hZV : Z ≤ V) (hact1 : act 1 = 1) {s t : S}
    (hs2 : φ s * φ s = 1) (ht2 : φ t * φ t = 1)
    (he : ⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z = ⁅V, Subgroup.zpowers (t : G)⁆ ⊔ Z) :
    LinearMap.range (act (φ s) - 1).mulVecLin = LinearMap.range (act (φ t) - 1).mulVecLin := by
  obtain ⟨hN, hZn, ψ, hψ⟩ := h
  have hrel_of : ∀ u : S, φ u * φ u = 1 → ∀ k : ℤ,
      LinearMap.range (act (φ (u ^ k)) - 1).mulVecLin ≤
        LinearMap.range (act (φ u) - 1).mulVecLin := by
    intro u hu k
    rw [map_zpow]
    rcases zpow_parity (φ u) hu k with h | h
    · rw [h, hact1, sub_self]; simp
    · rw [h]
  have key : ∀ (a b : S), φ a * φ a = 1 → φ b * φ b = 1 →
      ⁅V, Subgroup.zpowers (a : G)⁆ ⊔ Z = ⁅V, Subgroup.zpowers (b : G)⁆ ⊔ Z →
      LinearMap.range (act (φ a) - 1).mulVecLin ≤ LinearMap.range (act (φ b) - 1).mulVecLin := by
    intro a b ha2 hb2 hab u hu
    obtain ⟨w, hw⟩ := ψ.surjective (Multiplicative.ofAdd u)
    obtain ⟨gv, rfl⟩ := QuotientGroup.mk_surjective w
    have hc1 : Multiplicative.toAdd (ψ (QuotientGroup.mk gv)) = u := by rw [hw]; rfl
    have h1 := (mem_comm_sup_iff_of_coord' hN ψ hψ hZV (hrel_of a ha2) gv.2).mpr
      (by show Multiplicative.toAdd (ψ (QuotientGroup.mk gv)) ∈ _; rw [hc1]; exact hu)
    rw [hab] at h1
    have h2 := (mem_comm_sup_iff_of_coord' hN ψ hψ hZV (hrel_of b hb2) gv.2).mp h1
    have h3 : Multiplicative.toAdd (ψ (QuotientGroup.mk gv)) ∈
        LinearMap.range (act (φ b) - 1).mulVecLin := h2
    rwa [hc1] at h3
  exact le_antisymm (key s t hs2 ht2 he) (key t s ht2 hs2 he.symm)

end Helpers

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem isPGroup_Rt (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) {t : G}
    (ht : t ∈ LB M Q B) (htQ : t ∉ Q) : IsPGroup 2 (Rt M (LB M Q B) t) := by
  obtain ⟨K, fK, finK, hcard, φ, hrange, hker', hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hs₁, hs₂,
    hswap, hcent⟩ := id hS
  obtain ⟨f, -, hf, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := s81w_charP_two (hcard.trans hf)
  have hker : ∀ s : ↥(Lgen M (LB M Q B)), φ s = 1 ↔ (s : G) ∈ Q := fun s => by
    rw [← MonoidHom.mem_ker, hker', Subgroup.mem_subgroupOf]
  have htS : t ∈ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B) ht
  have hsq : ∀ m ∈ M, ∀ x : ↥(Lgen M (LB M Q B)), (x : G) ∈ conjSubgroup m (LB M Q B) →
      φ x * φ x = 1 := by
    intro m hm x hx
    rw [← map_mul]
    apply (hker _).mpr
    show (x : G) * (x : G) ∈ Q
    rw [← pow_two]
    apply (hc.conj_of_mem hm).sq_mem_Q_of_mem_LB
    rw [hc.LB_conj hm]
    exact hx
  have ht2 : φ ⟨t, htS⟩ * φ ⟨t, htS⟩ = 1 := by
    rw [← map_mul]
    apply (hker _).mpr
    show t * t ∈ Q
    rw [← pow_two]
    exact hc.sq_mem_Q_of_mem_LB ht
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) K,
      T = ((φ ⟨t, htS⟩ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 := ⟨_, rfl⟩
  have hTT : T * T = 0 := by rw [hT]; exact sq_sub_one_eq_zero _ ht2
  have hcH : LinearMap.range (Matrix.mulVecLin T) ≤ LinearMap.ker (Matrix.mulVecLin T) :=
    fun v hv => mem_ker_of_range T hTT v hv
  let Sset : Set (GL (Fin n) K) := {g | ∀ v : Fin n → K,
    (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ LinearMap.ker (Matrix.mulVecLin T) ∧
      (v ∈ LinearMap.ker (Matrix.mulVecLin T) →
        (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ LinearMap.range (Matrix.mulVecLin T)) ∧
      (v ∈ LinearMap.range (Matrix.mulVecLin T) →
        (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v)}
  have hmat : ∀ g : GL (Fin n) K, g * g = 1 →
      (LinearMap.range (Matrix.mulVecLin ((g : Matrix (Fin n) (Fin n) K) - 1)) =
          LinearMap.range (Matrix.mulVecLin T) ∨
        LinearMap.ker (Matrix.mulVecLin ((g : Matrix (Fin n) (Fin n) K) - 1)) =
          LinearMap.ker (Matrix.mulVecLin T)) → g ∈ Sset := by
    intro g hg h v
    have hA := sq_sub_one_eq_zero g hg
    obtain ⟨h1, h2, h3⟩ := flag_of_range_eq _ T hA hTT h v
    have e : ∀ w, ((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w =
        (g : Matrix (Fin n) (Fin n) K) *ᵥ w - w := by
      intro w; rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e] at h1 h2 h3
    refine ⟨h1, h2, fun hv => ?_⟩
    exact sub_eq_zero.mp (h3 hv)
  have hone : (1 : GL (Fin n) K) ∈ Sset := by
    intro v
    simp
  have hkey : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) → ∀ x : ↥(Lgen M (LB M Q B)),
      (x : G) ∈ conjSubgroup m (LB M Q B) → φ x ∈ Sset := by
    intro m hm hmt x hx
    by_cases hxQ : (x : G) ∈ Q
    · rw [(hker x).mpr hxQ]
      exact hone
    · have hx2 := hsq m hm x hx
      have hB' := hc.conj_of_mem hm
      have hxB' : (x : G) ∈ LB M Q (conjSubgroup m B) := by rw [hc.LB_conj hm]; exact hx
      have htB' : t ∈ LB M Q (conjSubgroup m B) := by rw [hc.LB_conj hm]; exact hmt
      rcases (hS.transv_of_conj hc hn hB').1 with hle | hle
      · have hS' := hS.of_conj hc hn hB'
        have he := (LinSetup.transv_of_le_V₁ hB' hS' hn hle hxB' hxQ).1
        have het := (LinSetup.transv_of_le_V₁ hB' hS' hn hle htB' htQ).1
        have hr := range_eq_of_comm_sup_eq hs₁ hZV₁ (by simp) hx2 ht2 (he.trans het.symm)
        refine hmat _ hx2 (Or.inl ?_)
        rw [hT]
        exact hr
      · have hS' := hS.of_conj hc hn hB'
        have he := (LinSetup.transv_of_le_V₁ hB' hS'.symm hn hle hxB' hxQ).1
        have het := (LinSetup.transv_of_le_V₁ hB' hS'.symm hn hle htB' htQ).1
        have hr := range_eq_of_comm_sup_eq hs₂ hZV₂ (by simp) hx2 ht2 (he.trans het.symm)
        have e1 : ∀ g : GL (Fin n) K, g * g = 1 →
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1) =
              ((g : Matrix (Fin n) (Fin n) K) - 1)ᵀ := by
          intro g hg
          rw [inv_eq_of_mul_eq_one_right hg, Matrix.transpose_sub, Matrix.transpose_one]
        have hr' : LinearMap.range
            ((((φ x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin =
            LinearMap.range
              ((((φ ⟨t, htS⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin := hr
        rw [e1 _ hx2, e1 _ ht2] at hr'
        refine hmat _ hx2 (Or.inr ?_)
        rw [hT]
        exact ker_eq_of_range_transpose_eq _ _ hr'
  let C : Subgroup ↥(Lgen M (LB M Q B)) := (Subgroup.closure Sset).comap φ
  have hRC : Rt M (LB M Q B) t ≤ C.map (Lgen M (LB M Q B)).subtype := by
    unfold Rt
    refine iSup_le fun m => iSup_le fun hm => iSup_le fun hmt => ?_
    intro x hx
    have hxS : x ∈ Lgen M (LB M Q B) :=
      (le_iSup₂ (f := fun (m : G) (_ : m ∈ M) => conjSubgroup m (LB M Q B)) m hm) hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxS⟩, ?_, rfl⟩
    exact Subgroup.subset_closure (hkey m hm hmt ⟨x, hxS⟩ hx)
  intro g
  obtain ⟨c, hcC, hcr⟩ := Subgroup.mem_map.mp (hRC g.2)
  have h4 : φ (c ^ 4) = 1 := by
    rw [map_pow]
    exact pow_four_of_mem_closure_flag (LinearMap.range (Matrix.mulVecLin T))
      (LinearMap.ker (Matrix.mulVecLin T)) hcH Sset (fun g hg => hg) _ hcC
  have hq : ((c : G) ^ 4) ∈ Q := (hker (c ^ 4)).mp h4
  obtain ⟨k, hk⟩ := isPGroup_Q' hc.hyp ⟨_, hq⟩
  refine ⟨k + 2, ?_⟩
  have hk' : ((c : G) ^ 4) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  apply Subtype.ext
  have hcg : (c : G) = (g : G) := hcr
  show (g : G) ^ 2 ^ (k + 2) = 1
  rw [← hcg]
  calc (c : G) ^ 2 ^ (k + 2) = ((c : G) ^ 4) ^ 2 ^ k := by
        rw [← pow_mul]
        congr 1
        ring
    _ = 1 := hk'

theorem rt_quot_absurd {t : G} {m f : ℕ} (hm : 3 ≤ m) (hq4 : 4 ≤ Nat.card Z)
    (hf : Nat.card Z = 2 ^ f) (hP : IsPGroup 2 (Rt M (LB M Q B) t))
    (hR : QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus m (Nat.card Z))) :
    False := by
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup G, R = Rt M (LB M Q B) t := ⟨_, rfl⟩
  have hNR : Nt M (LB M Q B) t = inSubgroup (pCore 2) R := by
    rw [hRdef]
    rfl
  rw [← hRdef] at hP hR
  rw [hNR] at hR
  have hP' : IsPGroup 2 (⊤ : Subgroup ↥R) := fun g => by
    obtain ⟨j, hj⟩ := hP g.1
    exact ⟨j, Subtype.ext hj⟩
  have hpc : (⊤ : Subgroup ↥R) ≤ CFSG.pCore 2 ↥R := le_sSup ⟨inferInstance, hP'⟩
  have htop : (⊤ : Subgroup ↥R) ≤ (inSubgroup (pCore 2) R).subgroupOf R := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨x, hpc hx, rfl⟩
  have hidx : ((inSubgroup (pCore 2) R).subgroupOf R).index = 1 :=
    Subgroup.index_eq_one.mpr (top_le_iff.mp htop)
  have hcard1 : Nat.card (↥R ⧸ (inSubgroup (pCore 2) R).subgroupOf R) = 1 := hidx
  unfold QuotSat IsOmegaPlus at hR
  obtain ⟨hNR', K₂, fK₂, finK₂, ⟨hK₂, hne⟩⟩ := hR
  obtain ⟨e⟩ := hne
  haveI : CharP K₂ 2 := s81w_charP_two (hK₂.trans hf)
  have hdvd := SubCfg.pow_two_mul_sub_one_dvd_card_omegaPlus (K := K₂) (m := m) hm
    (i := 1) le_rfl (by omega)
  rw [← Nat.card_congr e.toEquiv, hcard1, Nat.dvd_one] at hdvd
  have h16 : 16 ≤ Nat.card K₂ ^ (2 * 1) := by
    rw [hK₂, mul_one, pow_two]
    nlinarith
  omega

theorem not_caseVI_of_caseE4 (hc : Cfg M Q Z B) {t : G} (ht : CtxD4 M Q Z B t)
    (hE : CaseE4 M Q Z B t) : ¬ CaseVI M Q Z (Lgen M (LB M Q B)) := by
  intro hVI
  obtain ⟨hQ, hNt, hR, -⟩ := hE
  obtain ⟨-, htL, htQ, -⟩ := ht
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  obtain ⟨f, -, hf, -⟩ := hc.ctx.hyp.cp
  obtain ⟨n, hn⟩ : ∃ n, CaseE6 M Q Z B n := hVI
  obtain ⟨V₁, V₂, hL⟩ := CaseE6.exists_linSetup hn
  have hWn : Nat.card Q = Nat.card Z ^ (2 * n + 1) := LinSetup.width hc.ctx.hyp hL
  have hn16 : n = 16 := by
    have h := Nat.pow_right_injective hq2 (hWn.symm.trans hQ)
    omega
  have hP := isPGroup_Rt hc.ctx hL (by omega) htL htQ
  exact rt_quot_absurd (m := 4) (by omega) hq4 hf hP hR

theorem not_caseVI_of_caseE5 (hc : Cfg M Q Z B) {t : G} (ht : CtxD4 M Q Z B t)
    (hE : CaseE5 M Q Z B t) : ¬ CaseVI M Q Z (Lgen M (LB M Q B)) := by
  intro hVI
  obtain ⟨hQ, hNt, hR, -⟩ := hE
  obtain ⟨-, htL, htQ, -⟩ := ht
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  obtain ⟨f, -, hf, -⟩ := hc.ctx.hyp.cp
  obtain ⟨n, hn⟩ : ∃ n, CaseE6 M Q Z B n := hVI
  obtain ⟨V₁, V₂, hL⟩ := CaseE6.exists_linSetup hn
  have hWn : Nat.card Q = Nat.card Z ^ (2 * n + 1) := LinSetup.width hc.ctx.hyp hL
  have hn28 : n = 28 := by
    have h := Nat.pow_right_injective hq2 (hWn.symm.trans hQ)
    omega
  have hP := isPGroup_Rt hc.ctx hL (by omega) htL htQ
  exact rt_quot_absurd (m := 6) (by omega) hq4 hf hP hR

end CFSG.RankThree.GF2n.Smith81.MS80NoA2
