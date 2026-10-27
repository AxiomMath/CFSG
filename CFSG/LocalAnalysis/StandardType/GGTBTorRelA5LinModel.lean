module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Model
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24SlNsNorm

@[expose] public section

namespace CFSG.StandardType.RelA5

open CFSG CFSG.StandardType.CoordSL Matrix Polynomial Multiplicative

noncomputable abbrev muPlus {K : Type} [Field K] (g : K[X]) : Subgroup (AdjoinRoot g)ˣ :=
  rootsOfUnity (Nat.card K + 1) (AdjoinRoot g)

section Arith

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem odd_card_add_one : Odd (Nat.card K + 1) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hK]
  have hn0 : (n : ℕ) ≠ 0 := by
    have := n.pos
    omega
  rw [hcard]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hm, pow_succ]
  exact ⟨2 ^ m, by ring⟩

theorem coprime_card_add_one_card_sub_one : Nat.Coprime (Nat.card K + 1) (Nat.card K - 1) := by
  have hodd : Odd (Nat.card K + 1) := odd_card_add_one
  have hne : ¬ 2 ∣ Nat.card K + 1 := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd
  rw [Nat.coprime_iff_gcd_eq_one]
  have h1 : Nat.gcd (Nat.card K + 1) (Nat.card K - 1) ∣ Nat.card K + 1 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (Nat.card K + 1) (Nat.card K - 1) ∣ Nat.card K - 1 := Nat.gcd_dvd_right _ _
  have hd : Nat.gcd (Nat.card K + 1) (Nat.card K - 1) ∣ 2 := by
    have hsub := Nat.dvd_sub h1 h2
    rwa [show Nat.card K + 1 - (Nat.card K - 1) = 2 by
      have := Nat.card_pos (α := K); omega] at hsub
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact h
  · exact absurd (h ▸ h1) hne

theorem eq_one_of_pow_card_add_one {c : K} (hc : c ^ (Nat.card K + 1) = 1) : c = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by have := Nat.card_pos (α := K); omega)] at hc
    exact zero_ne_one hc
  have hsub : c ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one c hc0
  exact (pow_eq_one_iff_of_coprime coprime_card_add_one_card_sub_one).mp ⟨hc, hsub⟩

theorem norm_eq_one_of_pow_card_add_one {g : K[X]} [Fact (Irreducible g)] {x : AdjoinRoot g}
    (hx : x ^ (Nat.card K + 1) = 1) : Algebra.norm K x = 1 := by
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have h : (Algebra.norm K) x ^ (Nat.card K + 1) = 1 := by
    rw [← map_pow (Algebra.norm K) x, hx, map_one]
  exact eq_one_of_pow_card_add_one h

end Arith

section Mu

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)]

theorem card_muPlus (hdim : (rootPB g).dim = 2) : Nat.card (muPlus g) = Nat.card K + 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcardL : Nat.card (AdjoinRoot g) = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot g), (rootPB g).finrank, hdim]
  have hcard : Nat.card (AdjoinRoot g)ˣ = (Nat.card K - 1) * (Nat.card K + 1) := by
    rw [Nat.card_units, hcardL]
    simpa [Nat.mul_comm] using Nat.sq_sub_sq (Nat.card K) 1
  have hq : 0 < Nat.card K := Nat.card_pos
  have hne : (Nat.card K + 1) ≠ 0 := by omega
  have : NeZero (Nat.card K + 1) := ⟨hne⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (AdjoinRoot g)ˣ)
  have hgprim : IsPrimitiveRoot u (Nat.card (AdjoinRoot g)ˣ) := IsPrimitiveRoot.iff_orderOf.mpr hu
  have hprim : IsPrimitiveRoot (u ^ (Nat.card K - 1)) (Nat.card K + 1) :=
    hgprim.pow Nat.card_pos hcard
  exact IsPrimitiveRoot.card_rootsOfUnity' hprim

theorem exists_rootMu {p : ℕ} (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hpK : p ∣ Nat.card K + 1) :
    ∃ ζ : muPlus g, (((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) = AdjoinRoot.root g ∧
      IsPrimitiveRoot ζ p := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    have h1 : Nat.card K + 1 = 0 := Nat.eq_zero_of_zero_dvd hpK
    have h2 := Nat.card_pos (α := K)
    omega
  have hroot : AdjoinRoot.root g ≠ 0 := hprim.ne_zero hp0
  have hmem : Units.mk0 (AdjoinRoot.root g) hroot ∈ muPlus g := by
    rw [muPlus, mem_rootsOfUnity]
    obtain ⟨k, hk⟩ := hpK
    rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, Units.val_mk0, hk, pow_mul,
      hprim.pow_eq_one, one_pow]
  let ζ : muPlus g := ⟨Units.mk0 (AdjoinRoot.root g) hroot, hmem⟩
  have hζcoe : (((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) = AdjoinRoot.root g := rfl
  refine ⟨ζ, hζcoe, ?_⟩
  refine IsPrimitiveRoot.of_map_of_injective (f := Subgroup.subtype (muPlus g)) ?_
    (Subgroup.subtype_injective _)
  rw [← IsPrimitiveRoot.coe_units_iff]
  change IsPrimitiveRoot (AdjoinRoot.root g) p
  exact hprim

omit [Finite K] in
theorem mem_range_embPow_iff_muPlus {p : ℕ} [Fact p.Prime] {ζ : muPlus g}
    (hζ : IsPrimitiveRoot ζ p) (z : Fin 3 → muPlus g) :
    z ∈ (embPow ζ hζ.pow_eq_one).range ↔ ∀ i, z i ^ p = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · rintro ⟨f, rfl⟩ i
    show (ζ ^ (toAdd (f i)).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · intro h
    have hζL : IsPrimitiveRoot (((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) p := by
      rw [IsPrimitiveRoot.coe_units_iff]
      exact hζ.map_of_injective (Subgroup.subtype_injective _)
    have hzL : ∀ i, (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) ^ p = 1 := by
      intro i
      have hi := congrArg (fun u : muPlus g => (((u : (AdjoinRoot g)ˣ)) : AdjoinRoot g)) (h i)
      simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using hi
    have hex : ∀ i : Fin 3, ∃ k : ℕ, k < p ∧
        (((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) ^ k =
          (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) := fun i =>
      hζL.eq_pow_of_pow_eq_one (hzL i)
    refine MonoidHom.mem_range.mpr
      ⟨fun i => Multiplicative.ofAdd ((Classical.choose (hex i) : ℕ) : ZMod p), ?_⟩
    funext i
    apply Subtype.ext
    apply Units.ext
    rw [embPow_apply, toAdd_ofAdd, ZMod.val_natCast_of_lt (Classical.choose_spec (hex i)).1,
      SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    exact (Classical.choose_spec (hex i)).2

end Mu

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem thetaMat_pow (ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0)
    (M : Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) (k : ℕ) :
    thetaMat g ε (M ^ k) = thetaMat g ε M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, thetaMat_one]
  | succ k ih => rw [pow_succ, pow_succ, thetaMat_mul, ih]

omit [Finite K] [CharP K 2] in
theorem thetaMat_injective (ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0) :
    Function.Injective (thetaMat g ε) := by
  intro M N h
  have h1 := congrArg (frameForm g ε) h
  simp only [frameForm_thetaMat] at h1
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  have h2 := congrArg (fun φ => (φ (y, (0 : Fin 0 → K))).1) h1
  simpa [blockAct_apply, Matrix.toLin'_apply] using h2

omit [Finite K] [CharP K 2] in
theorem thetaMat_diagonal_algebraMap (ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0) (c : K) :
    thetaMat g ε (diagonal fun _ => algebraMap K (AdjoinRoot g) c) = scalar (Fin n) c := by
  have hscalar : frameForm g ε (scalar (Fin n) c) = c • LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    rw [frameForm_apply, Matrix.scalar_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hc : (diagonal fun _ => c) *ᵥ frameCoords g ε x = c • frameCoords g ε x := by
      funext i
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [hc, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply]
  apply frameForm_injective g ε
  rw [frameForm_thetaMat, hscalar]
  refine LinearMap.ext fun x => ?_
  rw [blockAct_apply, LinearMap.smul_apply, LinearMap.id_apply]
  refine Prod.ext ?_ ?_
  · funext i
    simp [Matrix.mulVec_diagonal, Algebra.smul_def]
  · exact Subsingleton.elim _ _

theorem exists_linTorus (ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0) :
    ∃ F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K, ∀ z,
      (F z : Matrix (Fin n) (Fin n) K) =
        thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) := by
  classical
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have hdet : ∀ z : Fin 3 → muPlus g,
      (thetaMat g ε
        (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g))).det = 1 := by
    intro z
    rw [det_thetaMat, Matrix.det_diagonal]
    have hnorm : ∀ i : Fin 3,
        Algebra.norm K (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) = 1 := by
      intro i
      apply norm_eq_one_of_pow_card_add_one
      have hi : ((z i : muPlus g) : (AdjoinRoot g)ˣ) ^ (Nat.card K + 1) = 1 :=
        (mem_rootsOfUnity _ _).mp (z i).2
      have hc := congrArg (fun u : (AdjoinRoot g)ˣ => (u : AdjoinRoot g)) hi
      simpa [Units.val_pow_eq_pow_val] using hc
    have hmul : Algebra.norm K (∏ i, (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
        ∏ i, Algebra.norm K (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) := by
      exact map_prod (Algebra.norm K) _ _
    rw [hmul]
    exact Finset.prod_eq_one fun i _ => hnorm i
  let F0 : (Fin 3 → muPlus g) → SpecialLinearGroup (Fin n) K := fun z =>
    ⟨thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)),
      hdet z⟩
  have hmul' : ∀ z w, F0 (z * w) = F0 z * F0 w := by
    intro z w
    apply Subtype.ext
    show thetaMat g ε
        (diagonal fun i => ((((z * w) i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) *
        thetaMat g ε (diagonal fun i => (((w i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g))
    rw [← thetaMat_mul, diagonal_mul_diagonal]
    congr 1
  exact ⟨MonoidHom.mk' F0 hmul', fun z => rfl⟩

omit [Finite K] [CharP K 2] in
theorem exists_linFullTorus (ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0) :
    ∃ TH : Subgroup (SpecialLinearGroup (Fin n) K), ∀ x, x ∈ TH ↔
      ∃ c : Fin 3 → (AdjoinRoot g)ˣ, (x : Matrix (Fin n) (Fin n) K) =
        thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) := by
  classical
  let S : Set (SpecialLinearGroup (Fin n) K) :=
    {x | ∃ c : Fin 3 → (AdjoinRoot g)ˣ, (x : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g))}
  have hS : ∀ x, x ∈ S ↔ ∃ c : Fin 3 → (AdjoinRoot g)ˣ,
      (x : Matrix (Fin n) (Fin n) K) =
        thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) :=
    fun x => Iff.rfl
  refine ⟨{ carrier := S, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun x => hS x⟩
  · rintro x y hx hy
    rw [hS] at hx hy ⊢
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hc, hd, ← thetaMat_mul, diagonal_mul_diagonal]
    congr 1
  · rw [hS]
    refine ⟨fun _ => 1, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_one, diagonal_one, thetaMat_one]
  · rintro x hx
    rw [hS] at hx ⊢
    obtain ⟨c, hc⟩ := hx
    refine ⟨c⁻¹, ?_⟩
    have hM' : (x : Matrix (Fin n) (Fin n) K) *
        thetaMat g ε (diagonal fun i => ((c⁻¹ i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) = 1 := by
      rw [hc, ← thetaMat_mul, diagonal_mul_diagonal]
      have h1 : (fun i : Fin 3 => (((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g) *
          (((c⁻¹ i : (AdjoinRoot g)ˣ) : AdjoinRoot g)))) = fun _ => 1 := by
        funext i
        rw [show ((c⁻¹ i : (AdjoinRoot g)ˣ)) = (c i)⁻¹ from rfl, ← Units.val_mul, mul_inv_cancel,
          Units.val_one]
      rw [h1, diagonal_one, thetaMat_one]
    have hx1 : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    calc ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * 1 := by
            rw [mul_one]
      _ = ((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((x : Matrix (Fin n) (Fin n) K) *
              thetaMat g ε (diagonal fun i => ((c⁻¹ i : (AdjoinRoot g)ˣ) : AdjoinRoot g))) := by
            rw [hM']
      _ = (((x⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (x : Matrix (Fin n) (Fin n) K)) *
              thetaMat g ε (diagonal fun i => ((c⁻¹ i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) := by
            rw [mul_assoc]
      _ = thetaMat g ε (diagonal fun i => ((c⁻¹ i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) := by
            rw [hx1, one_mul]

variable {ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0}

theorem linTorus_eq_one_of_mem_center {F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K}
    (hF : ∀ z, (F z : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    (z : Fin 3 → muPlus g) (hz : F z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    z = 1 := by
  obtain ⟨r, -, hr2⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h1 : thetaMat g ε
      (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
      scalar (Fin n) r := by
    rw [← hF z, hr2]
  have hdiag : (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
      diagonal (fun _ => algebraMap K (AdjoinRoot g) r) := by
    apply thetaMat_injective ε
    rw [h1, thetaMat_diagonal_algebraMap]
  have hzi : ∀ i, (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) =
      algebraMap K (AdjoinRoot g) r := fun i =>
    congrFun (Matrix.diagonal_injective hdiag) i
  have hr : r ^ (Nat.card K + 1) = 1 := by
    have hzp : (((z 0 : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) ^ (Nat.card K + 1) = 1 := by
      have hi : ((z 0 : muPlus g) : (AdjoinRoot g)ˣ) ^ (Nat.card K + 1) = 1 :=
        (mem_rootsOfUnity _ _).mp (z 0).2
      simpa [Units.val_pow_eq_pow_val] using
        congrArg (fun u : (AdjoinRoot g)ˣ => (u : AdjoinRoot g)) hi
    rw [hzi 0] at hzp
    rw [← map_pow, show ((1 : AdjoinRoot g)) = algebraMap K (AdjoinRoot g) (1 : K) from
      (map_one _).symm, (algebraMap K (AdjoinRoot g)).injective.eq_iff] at hzp
    exact hzp
  have hr1 : r = 1 := eq_one_of_pow_card_add_one hr
  funext i
  apply Subtype.ext
  apply Units.ext
  rw [hzi i, hr1, map_one]
  simp

omit [Finite K] [CharP K 2] in
theorem linFullTorus_commute {TH : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hTH : ∀ x, x ∈ TH ↔ ∃ c : Fin 3 → (AdjoinRoot g)ˣ, (x : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    {x y : SpecialLinearGroup (Fin n) K} (hx : x ∈ TH) (hy : y ∈ TH) : Commute x y := by
  obtain ⟨a, ha⟩ := (hTH x).mp hx
  obtain ⟨b, hb⟩ := (hTH y).mp hy
  have hmat : (x : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) =
      (y : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) := by
    rw [ha, hb, ← thetaMat_mul, ← thetaMat_mul, diagonal_mul_diagonal, diagonal_mul_diagonal]
    have hfun : (fun i : Fin 3 => ((a i : (AdjoinRoot g)ˣ) : AdjoinRoot g) *
        ((b i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
        fun i => ((b i : (AdjoinRoot g)ˣ) : AdjoinRoot g) *
          ((a i : (AdjoinRoot g)ˣ) : AdjoinRoot g) := by
      funext i
      exact mul_comm _ _
    rw [hfun]
  show x * y = y * x
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hmat]

omit [Finite K] [CharP K 2] in
theorem linTorus_mem_linFullTorus {F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K}
    (hF : ∀ z, (F z : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    {TH : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hTH : ∀ x, x ∈ TH ↔ ∃ c : Fin 3 → (AdjoinRoot g)ˣ, (x : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    (z : Fin 3 → muPlus g) : F z ∈ TH :=
  (hTH (F z)).mpr ⟨fun i => (z i : (AdjoinRoot g)ˣ), hF z⟩

omit [Finite K] [CharP K 2] in
theorem exists_eq_linTorus_of_pow {F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K}
    (hF : ∀ z, (F z : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    {TH : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hTH : ∀ x, x ∈ TH ↔ ∃ c : Fin 3 → (AdjoinRoot g)ˣ, (x : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    {t : SpecialLinearGroup (Fin n) K} (ht : t ∈ TH) (htm : t ^ (Nat.card K + 1) = 1) :
    ∃ z, F z = t := by
  obtain ⟨c, hc⟩ := (hTH t).mp ht
  have hmat : thetaMat g ε
      (Matrix.diagonal (fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) ^ (Nat.card K + 1)) =
      1 := by
    rw [thetaMat_pow, ← hc]
    have hcoe : ((t ^ (Nat.card K + 1) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
      rw [htm, Matrix.SpecialLinearGroup.coe_one]
    rw [← hcoe]
    simp
  have hD : Matrix.diagonal (fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) ^
      (Nat.card K + 1) = 1 := by
    apply thetaMat_injective ε
    rw [hmat, thetaMat_one]
  have hDfun : (fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)) ^ (Nat.card K + 1) =
      fun _ => 1 := by
    have h := hD
    rw [diagonal_pow, ← diagonal_one] at h
    exact Matrix.diagonal_injective h
  let z : Fin 3 → muPlus g := fun i => ⟨c i, by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    simpa using congrFun hDfun i⟩
  refine ⟨z, ?_⟩
  have hmat : (F z : Matrix (Fin n) (Fin n) K) = (t : Matrix (Fin n) (Fin n) K) := by
    rw [hF z, hc]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [hmat]

omit [Finite K] [CharP K 2] in
theorem center_le_linFullTorus {TH : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hTH : ∀ x, x ∈ TH ↔ ∃ c : Fin 3 → (AdjoinRoot g)ˣ, (x : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g))) :
    Subgroup.center (SpecialLinearGroup (Fin n) K) ≤ TH := by
  intro x hx
  obtain ⟨r, hr1, hr2⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hn : n ≠ 0 := by
    have hcard : n = (rootPB g).dim * 3 := by
      have h := Fintype.card_congr ε
      simpa [Fintype.card_sum, Fintype.card_prod] using h
    have hpos := rootPB_dim_pos g
    omega
  have hr0 : r ≠ 0 := by
    intro h
    rw [show Fintype.card (Fin n) = n from Fintype.card_fin n, h, zero_pow hn] at hr1
    exact zero_ne_one hr1
  have hc0 : algebraMap K (AdjoinRoot g) r ≠ 0 := by
    intro h0
    apply hr0
    have h1 : algebraMap K (AdjoinRoot g) r = algebraMap K (AdjoinRoot g) 0 := by
      rw [h0, map_zero]
    exact (algebraMap K (AdjoinRoot g)).injective h1
  refine (hTH x).mpr ⟨fun _ => Units.mk0 (algebraMap K (AdjoinRoot g) r) hc0, ?_⟩
  have hfun : (fun i : Fin 3 => (((fun _ => Units.mk0 (algebraMap K (AdjoinRoot g) r) hc0) i :
      (AdjoinRoot g)ˣ) : AdjoinRoot g)) = fun _ => algebraMap K (AdjoinRoot g) r := by
    funext i
    rw [Units.val_mk0]
  rw [← hr2, hfun, thetaMat_diagonal_algebraMap]

omit [Finite K] [CharP K 2] in
theorem linTorus_embPow {p : ℕ} [Fact p.Prime] (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) {F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K}
    (hF : ∀ z, (F z : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    {ζ : muPlus g} (hζp : ζ ^ p = 1)
    (hζr : (((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) = AdjoinRoot.root g)
    (f : Fin 3 → Multiplicative (ZMod p)) :
    F (embPow ζ hζp f) = SlNsRootGen.torusSL ε hC hCp (ofAdd fun i => toAdd (f i)) := by
  have hmat : (F (embPow ζ hζp f) : Matrix (Fin n) (Fin n) K) =
      (SlNsRootGen.torusSL ε hC hCp (ofAdd fun i => toAdd (f i)) :
        Matrix (Fin n) (Fin n) K) := by
    rw [hF, SlNsRootGen.torusSL_apply]
    have h1 : (Matrix.diagonal fun i =>
        (((embPow (p := p) ζ hζp f i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
        Matrix.diagonal (fun i => AdjoinRoot.root g ^ (toAdd (f i)).val) := by
      congr 1
      funext i
      rw [embPow_apply, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hζr]
    rw [h1, thetaMat_diagonal]
    rfl
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [hmat]

theorem linTorus_signedPerm {p : ℕ} [Fact p.Prime] (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1)
    {F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K}
    (hF : ∀ z, (F z : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    {ζ : muPlus g} (hζ : IsPrimitiveRoot ζ p)
    (hζr : (((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) = AdjoinRoot.root g)
    (x : SpecialLinearGroup (Fin n) K)
    (hx : ∀ f, ∃ f', x * F (embPow ζ hζ.pow_eq_one f) * x⁻¹ = F (embPow ζ hζ.pow_eq_one f')) :
    ∃ (π : Equiv.Perm (Fin 3)) (σ : Fin 3 → ZMod p), (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ f f', x * F (embPow ζ hζ.pow_eq_one f) * x⁻¹ = F (embPow ζ hζ.pow_eq_one f') →
        ∀ i, toAdd (f' (π i)) = σ i * toAdd (f i) := by
  have hx' : ∀ t : Fin 3 → ZMod p, ∃ t', x * SlNsRootGen.torusSL ε hC hCp (ofAdd t) * x⁻¹ =
      SlNsRootGen.torusSL ε hC hCp (ofAdd t') := by
    intro t
    obtain ⟨f', hf'⟩ := hx (fun i => ofAdd (t i))
    refine ⟨fun i => toAdd (f' i), ?_⟩
    have e1 : F (embPow ζ hζ.pow_eq_one (fun i => ofAdd (t i))) =
        SlNsRootGen.torusSL ε hC hCp (ofAdd t) := by
      simpa using linTorus_embPow (p := p) hC hCp hF hζ.pow_eq_one hζr
        (fun i => ofAdd (t i))
    have e2 : F (embPow ζ hζ.pow_eq_one f') =
        SlNsRootGen.torusSL ε hC hCp (ofAdd fun i => toAdd (f' i)) :=
      linTorus_embPow hC hCp hF hζ.pow_eq_one hζr f'
    rw [e1, e2] at hf'
    exact hf'
  obtain ⟨π, σ, hσ, hrel⟩ := SlNsRootGen.exists_signedPerm_of_conj hpK hgd ε hC hCp x hx'
  refine ⟨π, σ, hσ, fun f f' hff i => ?_⟩
  have e1 : F (embPow ζ hζ.pow_eq_one f) =
      SlNsRootGen.torusSL ε hC hCp (ofAdd fun j => toAdd (f j)) :=
    linTorus_embPow hC hCp hF hζ.pow_eq_one hζr f
  have e2 : F (embPow ζ hζ.pow_eq_one f') =
      SlNsRootGen.torusSL ε hC hCp (ofAdd fun j => toAdd (f' j)) :=
    linTorus_embPow hC hCp hF hζ.pow_eq_one hζr f'
  refine hrel (fun j => toAdd (f j)) (fun j => toAdd (f' j)) ?_ i
  rw [e1, e2] at hff
  exact hff

end Torus

end CFSG.StandardType.RelA5
