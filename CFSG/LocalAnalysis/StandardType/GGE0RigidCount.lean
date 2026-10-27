module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.StandardType

private lemma card_filter_diagonal_sub_eq {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [DecidableEq F] {p : ℕ} (hp : p.Prime) {a : F} (ha : IsPrimitiveRoot a p)
    (d : ι → F) {S : Matrix ι ι F} (hS : IsUnit S)
    (hcomm : S * Matrix.diagonal d = a • (Matrix.diagonal d * S)) (μ : F) :
    (Finset.univ.filter (fun i => d i = a⁻¹ * μ)).card =
      (Finset.univ.filter (fun i => d i = μ)).card := by
  classical
  have ha0 : a ≠ 0 := ha.ne_zero hp.ne_zero
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hkey : S * (Matrix.diagonal d - μ • 1) =
      a • ((Matrix.diagonal d - (a⁻¹ * μ) • 1) * S) := by
    calc
      S * (Matrix.diagonal d - μ • 1)
          = S * Matrix.diagonal d - μ • S := by simp [mul_sub]
      _ = a • (Matrix.diagonal d * S) - μ • S := by rw [hcomm]
      _ = a • (Matrix.diagonal d * S) - a • ((a⁻¹ * μ) • S) := by
            rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
      _ = a • ((Matrix.diagonal d - (a⁻¹ * μ) • 1) * S) := by
            rw [← smul_sub, sub_mul, Matrix.smul_mul, one_mul]
  have hrank : (Matrix.diagonal d - μ • 1).rank =
      (Matrix.diagonal d - (a⁻¹ * μ) • 1).rank := by
    have h1 : (S * (Matrix.diagonal d - μ • 1)).rank =
        (Matrix.diagonal d - μ • 1).rank :=
      Matrix.rank_mul_eq_right_of_isUnit_det S _ hdet
    have h2 : (S * (Matrix.diagonal d - μ • 1)).rank =
        (a • ((Matrix.diagonal d - (a⁻¹ * μ) • 1) * S)).rank := by rw [hkey]
    have h3 : (a • ((Matrix.diagonal d - (a⁻¹ * μ) • 1) * S)).rank =
        ((Matrix.diagonal d - (a⁻¹ * μ) • 1) * S).rank :=
      Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero ha0)
    have h4 : ((Matrix.diagonal d - (a⁻¹ * μ) • 1) * S).rank =
        (Matrix.diagonal d - (a⁻¹ * μ) • 1).rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det S _ hdet
    rw [h2, h3, h4] at h1
    exact h1.symm
  have hcard : ∀ ν : F, (Matrix.diagonal d - ν • 1).rank =
      Fintype.card ι - (Finset.univ.filter (fun i => d i = ν)).card := by
    intro ν
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.rank_diagonal,
      Fintype.card_subtype]
    have hcompl : (Finset.univ.filter (fun i => d i - ν ≠ 0)) =
        (Finset.univ.filter (fun i => d i = ν))ᶜ := by
      rw [Finset.compl_filter]
      congr 1
      ext i
      simp [sub_ne_zero]
    rw [hcompl, Finset.card_compl]
  rw [hcard μ, hcard (a⁻¹ * μ)] at hrank
  exact ((tsub_right_inj (Finset.card_le_univ _) (Finset.card_le_univ _)).mp hrank).symm

private lemma card_filter_pow_mul_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [DecidableEq F] {p : ℕ} (hp : p.Prime) {a : F} (ha : IsPrimitiveRoot a p)
    (d : ι → F) (i₀ : ι) {S : Matrix ι ι F} (hS : IsUnit S)
    (hcomm : S * Matrix.diagonal d = a • (Matrix.diagonal d * S)) (j : ℕ) :
    (Finset.univ.filter (fun i => d i = a⁻¹ ^ j * d i₀)).card =
      (Finset.univ.filter (fun i => d i = d i₀)).card := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', mul_assoc,
        card_filter_diagonal_sub_eq hp ha d hS hcomm (μ := a⁻¹ ^ j * d i₀)]
      exact ih

private lemma card_filter_mem_image_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [DecidableEq F] {p : ℕ} (hp : p.Prime) {a : F} (ha : IsPrimitiveRoot a p)
    (d : ι → F) (i₀ : ι) (hd : d i₀ ≠ 0) {S : Matrix ι ι F} (hS : IsUnit S)
    (hcomm : S * Matrix.diagonal d = a • (Matrix.diagonal d * S)) :
    (Finset.univ.filter (fun i => d i ∈ (Finset.range p).image
      (fun j => a⁻¹ ^ j * d i₀))).card =
      p * (Finset.univ.filter (fun i => d i = d i₀)).card := by
  classical
  have hinj : Set.InjOn (fun j => a⁻¹ ^ j * d i₀) ↑(Finset.range p) := by
    intro i hi j hj hij
    exact ha.inv.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (mul_right_cancel₀ hd hij)
  have hTcard : ((Finset.range p).image (fun j => a⁻¹ ^ j * d i₀)).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hconst : ∀ μ ∈ (Finset.range p).image (fun j => a⁻¹ ^ j * d i₀),
      (Finset.univ.filter (fun i => d i = μ)).card =
        (Finset.univ.filter (fun i => d i = d i₀)).card := by
    intro μ hμ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hμ
    exact card_filter_pow_mul_eq hp ha d i₀ hS hcomm j
  have hsum := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset ι)
    ((Finset.range p).image (fun j => a⁻¹ ^ j * d i₀)) d
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.nsmul_eq_mul, hTcard] at hsum
  exact hsum.symm

theorem card_mul_card_fiber_le_of_mul_diagonal_eq_smul {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] [DecidableEq F] {p : ℕ} (hp : p.Prime) {a : F}
    (ha : IsPrimitiveRoot a p) (d : ι → F) (i₀ : ι) (hd : d i₀ ≠ 0) {S : Matrix ι ι F}
    (hS : IsUnit S)
    (hcomm : S * Matrix.diagonal d = a • (Matrix.diagonal d * S)) :
    p * (Finset.univ.filter (fun i => d i = d i₀)).card ≤ Fintype.card ι := by
  classical
  calc
    p * (Finset.univ.filter (fun i => d i = d i₀)).card
        = (Finset.univ.filter (fun i => d i ∈ (Finset.range p).image
            (fun j => a⁻¹ ^ j * d i₀))).card :=
          (card_filter_mem_image_eq hp ha d i₀ hd hS hcomm).symm
    _ ≤ Fintype.card ι :=
          Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset ι))

theorem card_eq_mul_card_fiber_of_mul_diagonal_eq_smul {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] [DecidableEq F] {p : ℕ} (hp : p.Prime) {a : F}
    (ha : IsPrimitiveRoot a p) (d : ι → F) (i₀ : ι) (hd : d i₀ ≠ 0)
    (hpow : ∀ i, d i ^ p = d i₀ ^ p) {S : Matrix ι ι F} (hS : IsUnit S)
    (hcomm : S * Matrix.diagonal d = a • (Matrix.diagonal d * S)) :
    Fintype.card ι = p * (Finset.univ.filter (fun i => d i = d i₀)).card := by
  classical
  have hne : NeZero p := ⟨hp.ne_zero⟩
  have hcover : Finset.univ.filter (fun i => d i ∈ (Finset.range p).image
      (fun j => a⁻¹ ^ j * d i₀)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    have hdi : d i ≠ 0 := by
      intro h0
      have h : d i₀ ^ p = 0 := by rw [← hpow i, h0, zero_pow hp.ne_zero]
      exact pow_ne_zero p hd h
    have hroot : (d i / d i₀) ^ p = 1 := by
      rw [div_pow, hpow i, div_self (pow_ne_zero p hd)]
    obtain ⟨j, hj, hjeq⟩ :=
      letI : NeZero p := hne
      ha.inv.eq_pow_of_pow_eq_one hroot
    have hdj : a⁻¹ ^ j * d i₀ = d i := by rw [hjeq, div_mul_cancel₀ _ hd]
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj, hdj⟩
  calc
    Fintype.card ι = (Finset.univ.filter (fun i => d i ∈ (Finset.range p).image
        (fun j => a⁻¹ ^ j * d i₀))).card := by rw [hcover, Finset.card_univ]
    _ = p * (Finset.univ.filter (fun i => d i = d i₀)).card :=
        card_filter_mem_image_eq hp ha d i₀ hd hS hcomm

theorem card_le_pow_of_forall_pow_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {p : ℕ} (hp : 0 < p) {I : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ I) (T : Finset (ι → F))
    (hT₀ : ∀ g ∈ T, g i₀ = 1) (hTI : ∀ g ∈ T, ∀ i ∉ I, g i = 1)
    (hTp : ∀ g ∈ T, ∀ i ∈ I, g i ^ p = 1) :
    T.card ≤ p ^ (I.card - 1) := by
  classical
  let R : Finset F := Polynomial.nthRootsFinset p (1 : F)
  have hR : (Polynomial.nthRootsFinset p (1 : F)).card ≤ p := by
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots p 1)
  let φ : T → (I.erase i₀ → R) := fun g i =>
    ⟨(g : ι → F) i, (Polynomial.mem_nthRootsFinset hp 1).mpr
      (hTp g g.2 i (Finset.mem_of_mem_erase i.2))⟩
  have hφ : Function.Injective φ := by
    intro g g' h
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ I
    · by_cases hi0 : i = i₀
      · rw [hi0, hT₀ g g.2, hT₀ g' g'.2]
      · exact congrArg Subtype.val (congrFun h ⟨i, Finset.mem_erase.mpr ⟨hi0, hi⟩⟩)
    · rw [hTI g g.2 i hi, hTI g' g'.2 i hi]
  have h1 := Fintype.card_le_of_injective φ hφ
  rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
    Finset.card_erase_of_mem hi₀] at h1
  exact h1.trans (Nat.pow_le_pow_left hR _)

private theorem card_le_card_mul_card_image {G Y : Type} [Group G] [Fintype G] [DecidableEq Y]
    (K : Subgroup G) (f : G → Y) (hfib : ∀ a b : G, f a = f b → a⁻¹ * b ∈ K) :
    Fintype.card G ≤ Nat.card ↥K * (Finset.univ.image f).card := by
  classical
  have : Fintype ↥K := Fintype.ofFinite ↥K
  refine Finset.card_le_mul_card_image Finset.univ (Nat.card ↥K) ?_
  intro y _
  by_cases hne : (Finset.filter (fun a => f a = y) Finset.univ).Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    rw [Finset.mem_filter] at hg₀
    let F : G → ↥K := fun a =>
      if h : f a = y then ⟨g₀⁻¹ * a, hfib g₀ a (by rw [hg₀.2, h])⟩ else ⟨1, K.one_mem⟩
    have hinj : Set.InjOn F ↑(Finset.filter (fun a => f a = y) Finset.univ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      simp only [F] at hab
      rw [dif_pos ha, dif_pos hb] at hab
      exact mul_left_cancel (congrArg Subtype.val hab)
    have h1 : (Finset.filter (fun a => f a = y) Finset.univ).card
        = ((Finset.filter (fun a => f a = y) Finset.univ).image F).card :=
      (Finset.card_image_of_injOn hinj).symm
    have h2 : ((Finset.filter (fun a => f a = y) Finset.univ).image F).card
        ≤ Fintype.card ↥K := Finset.card_le_univ _
    rw [h1, Nat.card_eq_fintype_card]
    exact h2
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

theorem card_le_card_inf_mul_pow_of_fibres {X ι F : Type} [Group X] [Finite X] [Fintype ι]
    [DecidableEq ι] [Field F] (B K : Subgroup X) {p : ℕ} (hp : 0 < p) {I : Finset ι} {i₀ : ι}
    (hi₀ : i₀ ∈ I) (f : B → ι → F) (hf₀ : ∀ g, f g i₀ = 1) (hfI : ∀ g, ∀ i ∉ I, f g i = 1)
    (hfp : ∀ g, ∀ i ∈ I, f g i ^ p = 1)
    (hfib : ∀ a b : B, f a = f b → ((a⁻¹ * b : B) : X) ∈ K) :
    Nat.card B ≤ Nat.card ↥(B ⊓ K) * p ^ (I.card - 1) := by
  classical
  have : Fintype B := Fintype.ofFinite B
  have h1 := card_le_card_mul_card_image (K.subgroupOf B) f
    (fun a b h => Subgroup.mem_subgroupOf.mpr (hfib a b h))
  have h2 := card_le_pow_of_forall_pow_eq_one hp hi₀ (Finset.univ.image f)
    (by simp only [Finset.mem_image]; rintro g ⟨b, -, rfl⟩; exact hf₀ b)
    (by simp only [Finset.mem_image]; rintro g ⟨b, -, rfl⟩; exact hfI b)
    (by simp only [Finset.mem_image]; rintro g ⟨b, -, rfl⟩; exact hfp b)
  have h3 : Nat.card ↥(K.subgroupOf B) = Nat.card ↥(B ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Nat.card_eq_fintype_card, ← h3]
  exact h1.trans (Nat.mul_le_mul_left _ h2)

end CFSG.StandardType
