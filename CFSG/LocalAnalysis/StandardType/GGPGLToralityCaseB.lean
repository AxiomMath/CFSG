module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}

omit [Fintype ι] in
theorem eq_diagonal_of_offDiag_eq_zero {M : Matrix ι ι K} (h : ∀ i j, i ≠ j → M i j = 0) :
    M = diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij, h i j hij]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_isPrimitiveRoot_of_dvd [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by
  have := Fact.mk hp
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p
    (by rw [Nat.card_units]; exact hpK)
  exact ⟨ζ, IsPrimitiveRoot.coe_units_iff.mpr (hζ ▸ IsPrimitiveRoot.orderOf ζ)⟩

theorem pow_eq_one_of_pow_eq_scalar_pow {x : GL ι K} {c : Kˣ}
    (hx : x ^ p = GeneralLinearGroup.scalar ι (c ^ p)) :
    (GeneralLinearGroup.scalar ι c⁻¹ * x) ^ p = 1 := by
  rw [(commute_scalar c⁻¹ x).mul_pow, hx, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]

theorem isMulCommutative_of_central_order_p [Finite K] [Nonempty ι]
    (hp : p.Prime) (hp2 : p ≠ 2) {G : Subgroup (GL ι K)} (hG : IsProjElem p G)
    (hcent : ∀ h ∈ G, h ^ p = 1 → ∀ x ∈ G, x * h = h * x) :
    IsMulCommutative G := by
  classical
  let ψ : G →* PowQuot K p := (QuotientGroup.mk' _).comp (lam hp hp2 hG)
  apply ψ.isMulCommutative_of_isCyclic_of_ker_le_center
  intro x hx
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, c ^ p = lam hp hp2 hG x := by
    rw [MonoidHom.mem_ker] at hx
    change (QuotientGroup.mk (lam hp hp2 hG x) : PowQuot K p) = 1 at hx
    exact powQuot_mk_eq_one_iff.mp hx
  let z : GL ι K := GeneralLinearGroup.scalar ι c⁻¹ * x
  have hz : z ∈ G := G.mul_mem (hG.scalar_mem _) x.2
  have hzp : z ^ p = 1 := by
    apply pow_eq_one_of_pow_eq_scalar_pow
    rw [hc]
    exact lam_spec hp hp2 hG x
  have hxz : (x : GL ι K) = GeneralLinearGroup.scalar ι c * z := by
    dsimp only [z]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [Subgroup.mem_center_iff]
  intro y
  have hyx : Commute (y : GL ι K) (x : GL ι K) := by
    rw [hxz]
    exact (commute_scalar c (y : GL ι K)).symm.mul_right
      (hcent z hz hzp y y.2)
  apply Subtype.ext
  exact hyx.eq

@[expose] def conjMatrix (A x : GL ι K) : Matrix ι ι K :=
  (A : Matrix ι ι K) * (x : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)

theorem conjMatrix_mul (A x y : GL ι K) :
    conjMatrix A (x * y) = conjMatrix A x * conjMatrix A y := by
  have h1 : ((A⁻¹ : GL ι K) : Matrix ι ι K) * (A : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc conjMatrix A (x * y)
      = (A : Matrix ι ι K) * (x : Matrix ι ι K) *
          (((A⁻¹ : GL ι K) : Matrix ι ι K) * (A : Matrix ι ι K)) * (y : Matrix ι ι K) *
            ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
        rw [h1, Matrix.mul_one, conjMatrix, Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [conjMatrix, Matrix.mul_assoc]

theorem conjMatrix_one (A : GL ι K) : conjMatrix A 1 = 1 := by
  rw [conjMatrix, Units.val_one, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conjMatrix_pow (A x : GL ι K) (n : ℕ) : conjMatrix A (x ^ n) = conjMatrix A x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, conjMatrix_one]
  | succ n ih => rw [pow_succ, conjMatrix_mul, ih, pow_succ]

theorem conjMatrix_scalar_mul (A : GL ι K) (c : Kˣ) (x : GL ι K) :
    conjMatrix A (GeneralLinearGroup.scalar ι c * x) = (c : K) • conjMatrix A x := by
  rw [conjMatrix, conjMatrix, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
    ← smul_eq_diagonal_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem conjMatrix_scalar (A : GL ι K) (c : Kˣ) :
    conjMatrix A (GeneralLinearGroup.scalar ι c) = scalar ι (c : K) := by
  have h1 := conjMatrix_scalar_mul A c 1
  rw [mul_one, conjMatrix_one] at h1
  rw [h1, scalar_apply, smul_eq_diagonal_mul, Matrix.mul_one]
structure CentralBlockModel (p : ℕ) (G : Subgroup (GL ι K)) where
  numBlocks : ℕ
  basis : GL ι K
  block : ι → Fin numBlocks
  block_surjective : Function.Surjective block
  point : ι
  commutative : IsMulCommutative G
  kernel : Subgroup (GL ι K)
  kernel_le : kernel ≤ G
  kernel_mem_iff : ∀ x ∈ G, x ∈ kernel ↔ ∃ c : Kˣ,
    x ^ p = GeneralLinearGroup.scalar ι (c ^ p)
  card_le_kernel_mul : Nat.card G ≤ Nat.card kernel * p
  kernel_diagonal : ∀ x ∈ kernel, ∃ δ : ι → K,
    conjMatrix basis x = diagonal δ ∧
      (∀ i j, block i = block j → δ i = δ j) ∧ ∀ i, δ i ^ p = δ point ^ p
  isBlockDiag : ∀ x ∈ G, IsBlockDiag block (conjMatrix basis x)
  primitive : G
  scalar : Kˣ
  primitive_pow : (primitive : GL ι K) ^ p = GeneralLinearGroup.scalar ι scalar
  scalar_not_pow : ∀ c : Kˣ, c ^ p ≠ scalar
  block_dvd : ∀ b, p ∣ Fintype.card {i // block i = b}

theorem toral_or_exists_centralBlockModel [Finite K] [Nonempty ι] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {G : Subgroup (GL ι K)} (hG : IsProjElem p G)
    (hcent : ∀ h ∈ G, h ^ p = 1 → ∀ x ∈ G, x * h = h * x) :
    IsToral G ∨ Nonempty (CentralBlockModel p G) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp hpK
  set H₁ : Set (GL ι K) := {y | y ∈ G ∧ y ^ p = 1} with hH₁
  have hH₁fin : Finite H₁ := Subtype.finite
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal hζ H₁ (fun x hx y hy => hcent y hy.1 hy.2 x hx.1)
    (fun x hx => hx.2)
  have hH₁diag : ∀ y ∈ H₁, conjMatrix A₀ y = diagonal (fun i => conjMatrix A₀ y i i) :=
    fun y hy => eq_diagonal_of_offDiag_eq_zero (hA₀ y hy)
  have hdecomp : ∀ x ∈ G, ∀ c : Kˣ, x ^ p = GeneralLinearGroup.scalar ι (c ^ p) →
      ∃ y ∈ H₁, x = GeneralLinearGroup.scalar ι c * y := fun x hx c hc =>
    ⟨GeneralLinearGroup.scalar ι c⁻¹ * x,
      ⟨G.mul_mem (hG.scalar_mem _) hx, pow_eq_one_of_pow_eq_scalar_pow hc⟩, by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]⟩
  by_cases hall : ∀ x ∈ G, ∃ c : Kˣ, x ^ p = GeneralLinearGroup.scalar ι (c ^ p)
  · left
    refine ⟨A₀, fun x hx i j hij => ?_⟩
    obtain ⟨c, hc⟩ := hall x hx
    obtain ⟨y, hy, rfl⟩ := hdecomp x hx c hc
    change conjMatrix A₀ _ i j = 0
    rw [conjMatrix_scalar_mul, Matrix.smul_apply,
      show conjMatrix A₀ y i j = 0 from hA₀ y hy i j hij, smul_zero]
  right
  push Not at hall
  obtain ⟨g, hgG, hg⟩ := hall
  set lm := lam hp hp2 hG with hlm
  set ψ : G →* PowQuot K p := (QuotientGroup.mk' _).comp lm with hψ
  have hψker : ∀ x : G, x ∈ ψ.ker ↔ ∃ c : Kˣ, c ^ p = lm x := fun x => by
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      powQuot_mk_eq_one_iff]
  set G₀ := ψ.ker.map G.subtype with hG₀
  have hGcard : Nat.card G ≤ Nat.card G₀ * p := by
    rw [hG₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective G),
      ← Subgroup.card_ker_mul_card_range ψ]
    exact Nat.mul_le_mul_left _ ((Subgroup.card_le_card_group _).trans card_powQuot_le)
  let w : ι → (H₁ → K) := fun i y => conjMatrix A₀ y i i
  have hwp : ∀ (y : H₁) i, w i y ^ p = 1 := by
    intro y i
    have h1 := conjMatrix_pow A₀ y p
    rw [y.2.2, conjMatrix_one, hH₁diag y y.2, diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [one_apply_eq] using h2.symm
  have hG₀diag : ∀ x ∈ G₀, ∃ δ : ι → K, (A₀ : Matrix ι ι K) * (x : Matrix ι ι K) *
        ((A₀⁻¹ : GL ι K) : Matrix ι ι K) = diagonal δ ∧
      (∀ i j, w i = w j → δ i = δ j) ∧ ∀ i, δ i ^ p = δ i₀ ^ p := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hψker x).mp hx
    have hxp : (x : GL ι K) ^ p = GeneralLinearGroup.scalar ι (c ^ p) := by
      rw [lam_spec hp hp2 hG x, ← hlm, hc]
    obtain ⟨y, hy, hxy⟩ := hdecomp x x.2 c hxp
    refine ⟨fun i => (c : K) * w i ⟨y, hy⟩, ?_, ?_, ?_⟩
    · change conjMatrix A₀ (x : GL ι K) = _
      rw [hxy, conjMatrix_scalar_mul, hH₁diag y hy, smul_eq_diagonal_mul, diagonal_mul_diagonal]
    · intro i j hij
      simp only [hij]
    · intro i
      rw [mul_pow, mul_pow, hwp, hwp]
  have hcount := card_le_of_diag (p := p) A₀ w i₀ hG₀diag
  have hblock_all : ∀ x ∈ G, IsBlockDiag w (conjMatrix A₀ x) := by
    intro x hxG i j hij
    obtain ⟨y, hy⟩ : ∃ y : H₁, w i y ≠ w j y := by
      by_contra hcon
      push Not at hcon
      exact hij (funext hcon)
    have hcomm : conjMatrix A₀ x * diagonal (fun k => w k y) =
        diagonal (fun k => w k y) * conjMatrix A₀ x := by
      rw [show diagonal (fun k => w k y) = conjMatrix A₀ y from (hH₁diag y y.2).symm,
        ← conjMatrix_mul, ← conjMatrix_mul, hcent y y.2.1 y.2.2 x hxG]
    exact isBlockDiag_of_commute_diagonal hcomm i j hy
  have hblock : IsBlockDiag w (conjMatrix A₀ g) := hblock_all g hgG
  have hgp : conjMatrix A₀ g ^ p = scalar ι (lm ⟨g, hgG⟩ : K) := by
    rw [← conjMatrix_pow, show g ^ p = GeneralLinearGroup.scalar ι (lm ⟨g, hgG⟩) from
      lam_spec hp hp2 hG ⟨g, hgG⟩, conjMatrix_scalar]
  have hdvd : ∀ b, p ∣ Fintype.card {i // w i = b} := by
    intro b
    by_contra hnd
    obtain ⟨c, hc⟩ := exists_pow_eq_of_pow_eq_scalar hp
      (M := (conjMatrix A₀ g).toSquareBlock w b) (μ := lm ⟨g, hgG⟩)
      (by rw [← toSquareBlock_pow_of_isBlockDiag hblock, hgp, toSquareBlock_scalar]) hnd
    exact hg c (by rw [hc]; exact lam_spec hp hp2 hG ⟨g, hgG⟩)
  let J := Set.range w
  let : Fintype J := Fintype.ofFinite J
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let β : ι → Fin (Fintype.card J) := fun i => e ⟨w i, Set.mem_range_self i⟩
  have hβ : Function.Surjective β := by
    intro b
    obtain ⟨i, hi⟩ := (e.symm b).2
    refine ⟨i, ?_⟩
    change e ⟨w i, Set.mem_range_self i⟩ = b
    rw [show (⟨w i, Set.mem_range_self i⟩ : J) = e.symm b from Subtype.ext hi]
    exact e.apply_symm_apply b
  have heq : ∀ i j, β i = β j ↔ w i = w j := by
    intro i j
    constructor
    · intro hij
      exact congrArg Subtype.val (e.injective hij)
    · intro hij
      exact congrArg e (show (⟨w i, Set.mem_range_self i⟩ : J) =
        ⟨w j, Set.mem_range_self j⟩ from Subtype.ext hij)
  have hG₀le : G₀ ≤ G := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hG₀iff : ∀ x ∈ G, x ∈ G₀ ↔ ∃ c : Kˣ,
      x ^ p = GeneralLinearGroup.scalar ι (c ^ p) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc⟩ := (hψker y).mp hy
      refine ⟨c, ?_⟩
      rw [hc]
      exact lam_spec hp hp2 hG y
    · rintro ⟨c, hc⟩
      refine ⟨⟨x, hx⟩, (hψker _).mpr ⟨c, ?_⟩, rfl⟩
      apply scalar_injective (ι := ι)
      rw [← lam_spec hp hp2 hG ⟨x, hx⟩]
      exact hc.symm
  refine ⟨{
    numBlocks := Fintype.card J
    basis := A₀
    block := β
    block_surjective := hβ
    point := i₀
    commutative := isMulCommutative_of_central_order_p hp hp2 hG hcent
    kernel := G₀
    kernel_le := hG₀le
    kernel_mem_iff := hG₀iff
    card_le_kernel_mul := hGcard
    kernel_diagonal := ?_
    isBlockDiag := ?_
    primitive := ⟨g, hgG⟩
    scalar := lm ⟨g, hgG⟩
    primitive_pow := lam_spec hp hp2 hG ⟨g, hgG⟩
    scalar_not_pow := ?_
    block_dvd := ?_ }⟩
  · intro x hx
    obtain ⟨δ, hδ, hconst, hpow⟩ := hG₀diag x hx
    exact ⟨δ, hδ, fun i j hij => hconst i j ((heq i j).mp hij), hpow⟩
  · intro x hx i j hij
    apply hblock_all x hx i j
    exact fun he => hij ((heq i j).mpr he)
  · intro c hc
    apply hg c
    rw [hc]
    exact lam_spec hp hp2 hG ⟨g, hgG⟩
  · intro b
    obtain ⟨i, rfl⟩ := hβ b
    let q : {j // β j = β i} ≃ {j // w j = w i} := {
      toFun := fun j => ⟨j, (heq j i).mp j.2⟩
      invFun := fun j => ⟨j, (heq j i).mpr j.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Fintype.card_congr q]
    exact hdvd (w i)

theorem CentralBlockModel.numBlocks_mul_prime_le {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) :
    D.numBlocks * p ≤ Fintype.card ι := by
  classical
  have hcount := Finset.card_eq_sum_card_fiberwise (f := D.block) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hcount
  have hsum : (Finset.univ : Finset (Fin D.numBlocks)).card • p ≤
      ∑ b : Fin D.numBlocks, (Finset.univ.filter fun i => D.block i = b).card := by
    refine Finset.card_nsmul_le_sum _ _ _ fun b _ => ?_
    obtain ⟨i, hi⟩ := D.block_surjective b
    have hdvd := D.block_dvd b
    rw [Fintype.card_subtype] at hdvd
    refine Nat.le_of_dvd (Finset.card_pos.mpr ⟨i, ?_⟩) hdvd
    simp [hi]
  simpa only [Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← hcount] using hsum

theorem CentralBlockModel.card_kernel_le [Finite K] [NeZero p]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G) :
    Nat.card D.kernel ≤ p ^ (D.numBlocks - 1) * (Nat.card K - 1) := by
  classical
  have hcount := card_le_of_diag (p := p) D.basis D.block D.point D.kernel_diagonal
  have himage : Finset.univ.image D.block = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro b
    obtain ⟨i, rfl⟩ := D.block_surjective b
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  rw [himage, Finset.card_univ, Fintype.card_fin] at hcount
  simpa only [mul_comm] using hcount

theorem CentralBlockModel.card_le [Finite K] [NeZero p]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G) :
    Nat.card G ≤ p ^ D.numBlocks * (Nat.card K - 1) := by
  have hpos : 0 < D.numBlocks := by have := (D.block D.point).isLt; omega
  calc Nat.card G ≤ Nat.card D.kernel * p := D.card_le_kernel_mul
    _ ≤ p ^ (D.numBlocks - 1) * (Nat.card K - 1) * p :=
      Nat.mul_le_mul_right _ D.card_kernel_le
    _ = p ^ D.numBlocks * (Nat.card K - 1) := by
      rw [mul_right_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ D.numBlocks)]

theorem CentralBlockModel.numBlocks_eq_three_of_card_ge [Finite K]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G) (hp : p.Prime)
    (hdim : Fintype.card ι = 3 * p)
    (hcard : p ^ 3 * (Nat.card K - 1) ≤ Nat.card G) : D.numBlocks = 3 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hblocks : D.numBlocks ≤ 3 := by
    have h := D.numBlocks_mul_prime_le
    rw [hdim] at h
    exact Nat.le_of_mul_le_mul_right h hp.pos
  have hK : 0 < Nat.card K - 1 := by have := Finite.one_lt_card (α := K); omega
  have hpow : p ^ 3 ≤ p ^ D.numBlocks :=
    Nat.le_of_mul_le_mul_right (hcard.trans D.card_le) hK
  by_contra hne
  have hlt : D.numBlocks < 3 := by omega
  have hpowlt := Nat.pow_lt_pow_right hp.one_lt hlt
  omega

theorem CentralBlockModel.card_kernel_eq_of_card_ge [Finite K]
    {G : Subgroup (GL ι K)} (D : CentralBlockModel p G) (hp : p.Prime)
    (hdim : Fintype.card ι = 3 * p)
    (hcard : p ^ 3 * (Nat.card K - 1) ≤ Nat.card G) :
    Nat.card D.kernel = p ^ 2 * (Nat.card K - 1) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hn := D.numBlocks_eq_three_of_card_ge hp hdim hcard
  have hupper := D.card_kernel_le
  rw [hn] at hupper
  have hlower : p ^ 2 * (Nat.card K - 1) ≤ Nat.card D.kernel := by
    have hmul : p ^ 2 * (Nat.card K - 1) * p ≤ Nat.card D.kernel * p := by
      calc p ^ 2 * (Nat.card K - 1) * p = p ^ 3 * (Nat.card K - 1) := by ring
        _ ≤ Nat.card D.kernel * p := hcard.trans D.card_le_kernel_mul
    exact Nat.le_of_mul_le_mul_right hmul hp.pos
  exact Nat.le_antisymm hupper hlower

theorem CentralBlockModel.block_card_eq_prime {G : Subgroup (GL ι K)}
    (D : CentralBlockModel p G) (hdim : Fintype.card ι = D.numBlocks * p)
    (b : Fin D.numBlocks) : Fintype.card {i // D.block i = b} = p := by
  classical
  have hsize : ∀ a, p ≤ Fintype.card {i // D.block i = a} := by
    intro a
    obtain ⟨i, hi⟩ := D.block_surjective a
    have hdvd := D.block_dvd a
    rw [Fintype.card_subtype] at hdvd ⊢
    exact Nat.le_of_dvd (Finset.card_pos.mpr ⟨i, by simp [hi]⟩) hdvd
  have hcount := Finset.card_eq_sum_card_fiberwise (f := D.block) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hcount
  have htotal : (∑ a : Fin D.numBlocks, p) =
      ∑ a : Fin D.numBlocks, Fintype.card {i // D.block i = a} := by
    calc (∑ a : Fin D.numBlocks, p) = D.numBlocks * p := by simp [smul_eq_mul]
      _ = Fintype.card ι := hdim.symm
      _ = _ := by simpa only [Fintype.card_subtype] using hcount
  by_contra hne
  have hgt : p < Fintype.card {i // D.block i = b} := by have := hsize b; omega
  have hlt := Finset.sum_lt_sum (fun a _ => hsize a) ⟨b, Finset.mem_univ b, hgt⟩
  exact (ne_of_lt hlt) htotal

theorem exists_three_blockModel_of_central_of_not_toral [Finite K] [Nonempty ι]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    {G : Subgroup (GL ι K)} (hG : IsProjElem p G)
    (hcent : ∀ h ∈ G, h ^ p = 1 → ∀ x ∈ G, x * h = h * x)
    (hNT : ¬ IsToral G) (hdim : Fintype.card ι = 3 * p)
    (hcard : p ^ 3 * (Nat.card K - 1) ≤ Nat.card G) :
    ∃ D : CentralBlockModel p G, D.numBlocks = 3 ∧
      ∀ b, Fintype.card {i // D.block i = b} = p := by
  rcases toral_or_exists_centralBlockModel hp hp2 hpK hG hcent with h | h
  · exact (hNT h).elim
  · obtain ⟨D⟩ := h
    have hn := D.numBlocks_eq_three_of_card_ge hp hdim hcard
    refine ⟨D, hn, fun b => D.block_card_eq_prime ?_ b⟩
    rw [hn]
    exact hdim

theorem toral_or_card_le_of_central_sharp [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {G : Subgroup (GL ι K)} (hG : IsProjElem p G)
    (hcent : ∀ h ∈ G, h ^ p = 1 → ∀ x ∈ G, x * h = h * x) :
    IsToral G ∨ Nat.card G ≤ p ^ (Fintype.card ι / p) * (Nat.card K - 1) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Or.inl ⟨1, fun _ _ i => isEmptyElim i⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases toral_or_exists_centralBlockModel hp hp2 hpK hG hcent with h | h
  · exact Or.inl h
  · right
    obtain ⟨D⟩ := h
    exact D.card_le.trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right hp.pos ((Nat.le_div_iff_mul_le hp.pos).mpr
        (D.numBlocks_mul_prime_le))))

theorem toral_or_card_le_of_central [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {G : Subgroup (GL ι K)} (hG : IsProjElem p G)
    (hcent : ∀ h ∈ G, h ^ p = 1 → ∀ x ∈ G, x * h = h * x) :
    IsToral G ∨ Nat.card G ≤ p ^ (Fintype.card ι / p + 1) * (Nat.card K - 1) :=
  (toral_or_card_le_of_central_sharp hp hp2 hpK hG hcent).imp_right fun h =>
    h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (Nat.le_succ _)))

end CFSG.StandardType.TypeA.PGLTor
