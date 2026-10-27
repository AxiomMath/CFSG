module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSeitzConj
public import CFSG.RankThree.PartTwo.Sec19.Item19ResProofSeitzInner
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

section Cover

variable {X : Type} [Group X]

theorem apply_pow_mul_inv_of_central {ψ : MulAut X} {r y : X} (hy : y ∈ Subgroup.center X)
    (h : ψ r * r⁻¹ = y) (m : ℕ) : ψ (r ^ m) * (r ^ m)⁻¹ = y ^ m := by
  have hψr : ψ r = y * r := by rw [← h]; group
  have hc : Commute y r := (Subgroup.mem_center_iff.mp hy r).symm
  rw [map_pow, hψr, hc.mul_pow, mul_inv_cancel_right]

theorem exists_pow_eq_of_card_center [Finite X] (hZ3 : Nat.card (Subgroup.center X) = 3)
    {y z : X} (hy : y ∈ Subgroup.center X) (hy1 : y ≠ 1) (hz : z ∈ Subgroup.center X) :
    ∃ m : ℕ, z = y ^ m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic (Subgroup.center X) := isCyclic_of_prime_card hZ3
  have hgen : Subgroup.zpowers (⟨y, hy⟩ : Subgroup.center X) = ⊤ := by
    have hord : orderOf (⟨y, hy⟩ : Subgroup.center X) ∣ 3 := by
      rw [← hZ3]; exact orderOf_dvd_natCard _
    have hne : orderOf (⟨y, hy⟩ : Subgroup.center X) ≠ 1 := by
      intro h1
      apply hy1
      have := orderOf_eq_one_iff.mp h1
      exact congrArg Subtype.val this
    have h3 : orderOf (⟨y, hy⟩ : Subgroup.center X) = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hord).resolve_left hne
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, h3, hZ3]
  have hmem : (⟨z, hz⟩ : Subgroup.center X) ∈ Subgroup.zpowers (⟨y, hy⟩ : Subgroup.center X) := by
    rw [hgen]; trivial
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
  exact ⟨n, (congrArg Subtype.val hn).symm.trans (by simp)⟩

theorem pow_mul_mul_inv_of_central {s t ζ : X} (hζ : ζ ∈ Subgroup.center X)
    (h : s * t * s⁻¹ = ζ * t) (m : ℕ) : s ^ m * t * (s ^ m)⁻¹ = ζ ^ m * t := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hζm : ζ ^ m ∈ Subgroup.center X := Subgroup.pow_mem _ hζ m
    calc s ^ (m + 1) * t * (s ^ (m + 1))⁻¹ = s * (s ^ m * t * (s ^ m)⁻¹) * s⁻¹ := by group
      _ = s * (ζ ^ m * t) * s⁻¹ := by rw [ih]
      _ = (s * ζ ^ m) * t * s⁻¹ := by group
      _ = (ζ ^ m * s) * t * s⁻¹ := by rw [Subgroup.mem_center_iff.mp hζm s]
      _ = ζ ^ m * (s * t * s⁻¹) := by group
      _ = ζ ^ (m + 1) * t := by rw [h]; group

theorem closure_fixSet_of_cover [Finite X] (hgen : CFSG.AGLEmbedding.KGenTwoMod 3 X)
    (hZ3 : Nat.card (Subgroup.center X) = 3) {D : Subgroup (MulAut X)}
    (hD : CFSG.Open.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) {e : MulAut X} (he : e ∈ D)
    {s : X} (hsD : MulAut.conj s ∈ D) (hes : e s ≠ s) {t : X}
    (ht : t ∈ Subgroup.closure (fixSet D))
    (htc : s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center X) (ht1 : s * t * s⁻¹ * t⁻¹ ≠ 1) :
    Subgroup.closure (fixSet D) = ⊤ := by
  have hs1 : MulAut.conj s ≠ 1 := by
    intro h
    apply ht1
    have h' : s * t * s⁻¹ = t := by
      have := congrArg (fun ψ : MulAut X => ψ t) h
      simpa [MulAut.conj_apply] using this
    rw [h', mul_inv_cancel]
  have hsfix : s ∈ fixSet D := ⟨MulAut.conj s, hsD, hs1, by simp [MulAut.conj_apply]⟩
  have hs3 : MulAut.conj s ^ 3 = 1 := hD.2 _ hsD
  have hkey : ∀ ψ ∈ D, ψ ≠ 1 → ∃ r ∈ Subgroup.closure (fixSet D),
      ψ r * r⁻¹ ∈ Subgroup.center X ∧ ψ r * r⁻¹ ≠ 1 := by
    intro ψ hψ hψ1
    by_cases hψs : ψ ∈ Subgroup.zpowers (MulAut.conj s)
    ·
      refine ⟨t, ht, ?_⟩
      set ζ : X := s * t * s⁻¹ * t⁻¹ with hζ
      have hst : s * t * s⁻¹ = ζ * t := by rw [hζ]; group
      have hpow : ∀ m : ℕ, (MulAut.conj s ^ m) t * t⁻¹ = ζ ^ m := by
        intro m
        rw [← map_pow, MulAut.conj_apply, pow_mul_mul_inv_of_central htc hst m,
          mul_inv_cancel_right]
      obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr hψs
      simp only at hn
      subst hn
      have hn3 : n % 3 ≠ 0 := by
        intro h0
        apply hψ1
        have : n = 3 * (n / 3) := by omega
        rw [this, pow_mul, hs3, one_pow]
      have hψeq : MulAut.conj s ^ n = MulAut.conj s ^ (n % 3) := by
        have : n = 3 * (n / 3) + n % 3 := by omega
        conv_lhs => rw [this, pow_add, pow_mul, hs3, one_pow, one_mul]
      have hZ : ∀ m : ℕ, ζ ^ m ∈ Subgroup.center X := fun m => Subgroup.pow_mem _ htc m
      have hζ3 : ζ ^ 3 = 1 := by
        have := hpow 3
        rw [hs3] at this
        simpa using this.symm
      refine ⟨by rw [hψeq, hpow]; exact hZ _, ?_⟩
      rw [hψeq, hpow]
      have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
      interval_cases h : n % 3
      · exact absurd rfl hn3
      · simpa using ht1
      · intro h2
        apply ht1
        calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
          _ = 1 := by rw [hζ3, h2]; group
    ·
      refine ⟨s, Subgroup.subset_closure hsfix, ?_, ?_⟩
      · have hc : MulAut.conj s * ψ = ψ * MulAut.conj s :=
          congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hsD⟩ ⟨ψ, hψ⟩)
        have hcen : ∀ y : X, y * (s⁻¹ * ψ s) = (s⁻¹ * ψ s) * y := by
          intro y
          have h1 := congrArg (fun χ : MulAut X => χ (ψ.symm y)) hc
          simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
            MulEquiv.apply_symm_apply] at h1
          calc y * (s⁻¹ * ψ s) = s⁻¹ * (s * y * s⁻¹) * ψ s := by group
            _ = s⁻¹ * (ψ s * y * (ψ s)⁻¹) * ψ s := by rw [h1]
            _ = s⁻¹ * ψ s * y := by group
        have heq : ψ s * s⁻¹ = s⁻¹ * ψ s := by
          calc ψ s * s⁻¹ = s * (s⁻¹ * ψ s) * s⁻¹ := by group
            _ = (s⁻¹ * ψ s) * s * s⁻¹ := by rw [← hcen s]
            _ = s⁻¹ * ψ s := by group
        rw [Subgroup.mem_center_iff, heq]
        exact hcen
      · intro h1
        have hψs1 : ψ s = s := by rw [← mul_inv_eq_one]; exact h1
        apply hes
        have hle : D ≤ MulAction.stabilizer (MulAut X) s :=
          le_of_card_nine hD9 hsD hψ hs3 hs1 hψs
            (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_apply]; group)
            (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hψs1)
        have := hle he
        rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  refine Item19ResProof.closure_fixSet_eq_top_of_cover (hgen D hD (by rw [hD9]; norm_num)) ?_
  intro ψ hψ hψ1 x hx
  obtain ⟨r, hr, hrc, hr1⟩ := hkey ψ hψ hψ1
  obtain ⟨m, hm⟩ := exists_pow_eq_of_card_center hZ3 hrc hr1 hx
  refine ⟨r ^ m, Subgroup.pow_mem _ hr m, ?_⟩
  rw [apply_pow_mul_inv_of_central hrc rfl m, hm]

end Cover

section Semilinear

variable {k : Type} [Field k]

theorem ringEquiv_apply_eq_of_pow_three {σ : k ≃+* k} (hσ : σ ^ 3 = 1) {ω : k} (hω3 : ω ^ 3 = 1) :
    σ ω = ω := by
  by_cases hω1 : ω = 1
  · rw [hω1, map_one]
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω1)
  have hy3 : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hfac : (σ ω - 1) * ((σ ω - ω) * (σ ω - ω ^ 2)) = 0 := by
    linear_combination hy3 - (σ ω) ^ 2 * hω + (σ ω) * (hω + hω3) - hω3
  have hσ3 : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun τ : k ≃+* k => τ x) hσ
    simpa [pow_succ] using this
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (σ.injective ((sub_eq_zero.1 h).trans (map_one σ).symm)) hω1
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have h1 : σ ω = ω ^ 2 := sub_eq_zero.1 h
    have h2 : σ (σ ω) = ω ^ 4 := by rw [h1, map_pow, h1]; ring
    have h3 : σ (σ (σ ω)) = ω ^ 8 := by rw [h2, map_pow, h1]; ring
    rw [hσ3] at h3
    apply hω1
    have h4 : ω ^ 8 = ω ^ 2 := by
      calc ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 := by ring
        _ = ω ^ 2 := by rw [hω3]; ring
    have h5 : ω = ω ^ 2 := h3.trans h4
    have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
    have : ω * (ω - 1) = 0 := by linear_combination h5.symm
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hω0)

theorem semiBy_scalar_mul {φ : MulAut (SpecialLinearGroup (Fin 3) k)} {σ : k ≃+* k}
    {g : GL (Fin 3) k} (h : SemiBy φ σ g) (d : kˣ) :
    SemiBy φ σ (GeneralLinearGroup.scalar (Fin 3) d * g) := by
  intro x
  rw [h x]
  have hc : ∀ y : GL (Fin 3) k, GeneralLinearGroup.scalar (Fin 3) d * y =
      y * GeneralLinearGroup.scalar (Fin 3) d := by
    intro y
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (d : k) (fun _ => Commute.all _ _) _)
  set M := Matrix.GeneralLinearGroup.map (σ : k →+* k) (SpecialLinearGroup.toGL x)
  calc g * M * g⁻¹ = (g * M * g⁻¹) * GeneralLinearGroup.scalar (Fin 3) d *
        (GeneralLinearGroup.scalar (Fin 3) d)⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin 3) d * (g * M * g⁻¹) *
        (GeneralLinearGroup.scalar (Fin 3) d)⁻¹ := by rw [hc]
    _ = GeneralLinearGroup.scalar (Fin 3) d * g * M *
        (GeneralLinearGroup.scalar (Fin 3) d * g)⁻¹ := by group

theorem coe_map_ringEquiv (σ : k ≃+* k) (g : GL (Fin 3) k) :
    ((Matrix.GeneralLinearGroup.map (σ : k →+* k) g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (g : Matrix (Fin 3) (Fin 3) k).map σ := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

theorem exists_semiBy_norm_one [Finite k] {φ : MulAut (SpecialLinearGroup (Fin 3) k)}
    {σ : k ≃+* k} {g : GL (Fin 3) k} (hσ : orderOf σ = 3) (h : SemiBy φ σ g)
    (hφ3 : φ ^ 3 = 1) :
    ∃ g' : GL (Fin 3) k, SemiBy φ σ g' ∧
      (g' : Matrix (Fin 3) (Fin 3) k) * (g' : Matrix (Fin 3) (Fin 3) k).map σ *
        (g' : Matrix (Fin 3) (Fin 3) k).map (σ * σ) = 1 := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσσσ : σ * σ * σ = 1 := by rw [← pow_three', hσ3]
  have hσσσ' : σ * (σ * σ) = 1 := by rw [← mul_assoc, hσσσ]
  have hφφφ : φ * φ * φ = 1 := by rw [← pow_three', hφ3]
  set N : GL (Fin 3) k := g * Matrix.GeneralLinearGroup.map (σ : k →+* k) g *
    Matrix.GeneralLinearGroup.map ((σ * σ : k ≃+* k) : k →+* k) g with hNdef
  have hN : SemiBy (φ * φ * φ) (σ * σ * σ) N := (h.mul h).mul h
  rw [hφφφ, hσσσ] at hN
  have hNc := semiBy_one_iff.mp hN
  have hcomm : ∀ t : SpecialLinearGroup (Fin 3) k, (N : Matrix (Fin 3) (Fin 3) k) *
      (t : Matrix (Fin 3) (Fin 3) k) = (t : Matrix (Fin 3) (Fin 3) k) *
        (N : Matrix (Fin 3) (Fin 3) k) := fun t => comm_of_conj_eq (hNc t)
  obtain ⟨c, hc⟩ := eq_scalar_of_forall_commute N hcomm
  have hNσ : g * Matrix.GeneralLinearGroup.map (σ : k →+* k) N = N * g := by
    rw [hNdef, map_mul, map_mul, map_map_apply, map_map_apply, hσσσ']
    have hid : Matrix.GeneralLinearGroup.map ((1 : k ≃+* k) : k →+* k) g = g := by
      apply Units.ext; ext i j; simp [Matrix.GeneralLinearGroup.map_apply]
    rw [hid]
    group
  have hσc : σ (c : k) = c := by
    have h1 := congrArg Units.val hNσ
    rw [Units.val_mul, Units.val_mul, coe_map_ringEquiv, hc] at h1
    have h2 : ((c : k) • (1 : Matrix (Fin 3) (Fin 3) k)).map σ = σ (c : k) • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      split_ifs <;> simp
    rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at h1
    have h3 : (σ (c : k) - c) • (g : Matrix (Fin 3) (Fin 3) k) = 0 := by
      rw [sub_smul, h1, sub_self]
    have hg0 : (g : Matrix (Fin 3) (Fin 3) k) ≠ 0 := by
      intro h0
      have := g.isUnit
      rw [h0] at this
      exact not_isUnit_zero this
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hg0)
  have hσci : σ ((c⁻¹ : kˣ) : k) = ((c⁻¹ : kˣ) : k) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσc]
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ hσci
  rw [hσ] at hd
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one] at hd
  have hd' : d * σ d * σ (σ d) = ((c⁻¹ : kˣ) : k) := by
    rw [← hd, sq]
    rfl
  have hd0 : d ≠ 0 := by
    intro h0
    have hne : ((c⁻¹ : kˣ) : k) ≠ 0 := Units.ne_zero _
    rw [← hd', h0] at hne
    simp at hne
  refine ⟨GeneralLinearGroup.scalar (Fin 3) (Units.mk0 d hd0) * g, semiBy_scalar_mul h _, ?_⟩
  have hsc : ((GeneralLinearGroup.scalar (Fin 3) (Units.mk0 d hd0) * g : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) = d • (g : Matrix (Fin 3) (Fin 3) k) := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    rfl
  rw [hsc]
  have hmap : ∀ (τ : k ≃+* k) (M : Matrix (Fin 3) (Fin 3) k), (d • M).map τ = τ d • M.map τ := by
    intro τ M; ext i j; simp
  have hNm : (g : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k).map σ *
      (g : Matrix (Fin 3) (Fin 3) k).map (σ * σ) = (c : k) • 1 := by
    rw [← hc, hNdef, Units.val_mul, Units.val_mul, coe_map_ringEquiv, coe_map_ringEquiv]
  have hprod : ∀ (a b e : k) (G H I : Matrix (Fin 3) (Fin 3) k),
      (a • G) * (b • H) * (e • I) = (a * b * e) • (G * H * I) := by
    intro a b e G H I
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  have hσσd : (σ * σ) d = σ (σ d) := rfl
  rw [hmap, hmap, hprod, hNm, smul_smul, hσσd, hd', Units.val_inv_eq_inv_val,
    inv_mul_cancel₀ c.ne_zero, one_smul]

theorem map_ringEquiv_mulVec (σ : k ≃+* k) (M : Matrix (Fin 3) (Fin 3) k) (w : Fin 3 → k) :
    (fun i => σ ((M *ᵥ w) i)) = M.map σ *ᵥ (fun i => σ (w i)) := by
  funext i
  exact RingHom.map_mulVec (σ : k →+* k) M w i

theorem exists_semilinear_basis {σ : k ≃+* k} (hσ3 : σ ^ 3 = 1) {g : GL (Fin 3) k}
    (hN : (g : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k).map σ *
      (g : Matrix (Fin 3) (Fin 3) k).map (σ * σ) = 1)
    {S : Matrix (Fin 3) (Fin 3) k} (hS3 : S ^ 3 = 1) {z : k} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hgs : (g : Matrix (Fin 3) (Fin 3) k) * S.map σ = z • (S * (g : Matrix (Fin 3) (Fin 3) k))) :
    ∃ (P : GL (Fin 3) k) (D : Fin 3 → k), S * (P : Matrix (Fin 3) (Fin 3) k) =
        (P : Matrix (Fin 3) (Fin 3) k) * diagonal D ∧
      (g : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k).map σ =
        (P : Matrix (Fin 3) (Fin 3) k) * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ∧
      D 1 = z⁻¹ * D 0 ∧ D 2 = z⁻¹ * D 1 ∧ D 0 = z⁻¹ * D 2 := by
  classical
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz3
  have hzprim : IsPrimitiveRoot z 3 := by
    refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) hz3 ?_
    intro l hl0 hl3
    interval_cases l
    · simpa using hz1
    · intro h2
      apply hz1
      have h' : z ^ 3 = z ^ 2 * z := by ring
      rw [hz3, h2, one_mul] at h'
      exact h'.symm
  obtain ⟨ξ, v, hξ3, hv0, hSv⟩ := exists_eigenvector_of_pow_eq_one (p := 3) (by norm_num)
    ⟨z, hzprim⟩ (by norm_num) hS3
  have hξ0 : ξ ≠ 0 := by rintro rfl; norm_num at hξ3
  set G : Matrix (Fin 3) (Fin 3) k := (g : Matrix (Fin 3) (Fin 3) k) with hGdef
  have hσ3' : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun τ : k ≃+* k => τ x) hσ3
    simpa [pow_succ] using this
  have hσz : σ z⁻¹ = z⁻¹ := by rw [map_inv₀, ringEquiv_apply_eq_of_pow_three hσ3 hz3]
  have hσξ : σ ξ = ξ := ringEquiv_apply_eq_of_pow_three hσ3 hξ3
  let Φ : (Fin 3 → k) → (Fin 3 → k) := fun w => G *ᵥ (fun i => σ (w i))
  have hSG : S * G = z⁻¹ • (G * S.map σ) := by
    rw [hgs, smul_smul, inv_mul_cancel₀ hz0, one_smul]
  have hΦ : ∀ (w : Fin 3 → k) (l : k), σ l = l → S *ᵥ w = l • w →
      S *ᵥ Φ w = (z⁻¹ * l) • Φ w := by
    intro w l hl hw
    simp only [Φ]
    rw [Matrix.mulVec_mulVec, hSG, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      ← map_ringEquiv_mulVec, hw]
    have h1 : (fun i => σ ((l • w) i)) = l • (fun i => σ (w i)) := by
      funext i; simp [hl]
    rw [h1, Matrix.mulVec_smul, smul_smul]
  have hΦ0 : ∀ w : Fin 3 → k, w ≠ 0 → Φ w ≠ 0 := by
    intro w hw h0
    apply hw
    have h1 : ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Φ w =
        (fun i => σ (w i)) := by
      simp only [Φ, hGdef]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    funext i
    have := congrFun h1 i
    simpa using this.symm
  have hΦ3 : Φ (Φ (Φ v)) = v := by
    have e1 : ∀ w : Fin 3 → k, (fun i => σ (Φ w i)) = G.map σ *ᵥ (fun i => σ (σ (w i))) := by
      intro w
      simp only [Φ]
      rw [map_ringEquiv_mulVec]
    have e2 : ∀ w : Fin 3 → k, Φ (Φ w) = (G * G.map σ) *ᵥ (fun i => σ (σ (w i))) := by
      intro w
      show G *ᵥ (fun i => σ (Φ w i)) = _
      rw [e1, Matrix.mulVec_mulVec]
    have e3 : (G * G.map σ).map σ = G.map σ * G.map (σ * σ) := by
      rw [Matrix.map_mul]
      congr 1
    show G *ᵥ (fun i => σ (Φ (Φ v) i)) = v
    rw [e2]
    rw [map_ringEquiv_mulVec, e3, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hN, Matrix.one_mulVec]
    funext i
    exact hσ3' (v i)
  set u : Fin 3 → (Fin 3 → k) := ![v, Φ v, Φ (Φ v)] with hudef
  set D : Fin 3 → k := ![ξ, z⁻¹ * ξ, z⁻¹ * (z⁻¹ * ξ)] with hDdef
  have hσD : ∀ i, σ (D i) = D i := by
    intro i
    fin_cases i <;> simp [hDdef, hσz, hσξ]
  have hu : ∀ i, S *ᵥ u i = D i • u i := by
    intro i
    fin_cases i
    · simpa [hudef, hDdef] using hSv
    · exact hΦ v ξ hσξ hSv
    · exact hΦ (Φ v) (z⁻¹ * ξ) (by rw [map_mul, hσz, hσξ]) (hΦ v ξ hσξ hSv)
  have hu0 : ∀ i, u i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hudef] using hv0
    · exact hΦ0 v hv0
    · exact hΦ0 _ (hΦ0 v hv0)
  have hinj : Function.Injective D := by
    have hzi : IsPrimitiveRoot z⁻¹ 3 := hzprim.inv
    intro i j h
    have key : ∀ i : Fin 3, D i = z⁻¹ ^ (i : ℕ) * ξ := by
      intro i
      fin_cases i <;> simp [hDdef]
      ring
    rw [key, key] at h
    exact Fin.ext (hzi.pow_inj i.2 j.2 (mul_right_cancel₀ hξ0 h))
  have hli : LinearIndependent k u :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' S) D hinj u
      (fun i => ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hu i, hu0 i⟩)
  let b : Module.Basis (Fin 3) k (Fin 3 → k) :=
    basisOfLinearIndependentOfCardEqFinrank' u hli (by simp)
  have hb : ∀ i, b i = u i := fun i => by simp [b]
  set P : GL (Fin 3) k := basisUnit b with hP
  have hPe : ∀ j : Fin 3, ((P : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single j 1) =
      u j := fun j => by rw [hP, basisUnit_mulVec_single, one_smul, hb]
  have hPe2 : ∀ (j : Fin 3) (c : k),
      ((P : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ (Pi.single j c) = c • u j :=
    fun j c => by rw [hP, basisUnit_mulVec_single, hb]
  refine ⟨P, D, ?_, ?_, ?_, ?_, ?_⟩
  · refine matrix_eq_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe, Matrix.diagonal_mulVec_single,
      mul_one, hPe2, hu]
  · refine matrix_eq_of_mulVec_single fun j => ?_
    have hσs : (fun i => σ ((Pi.single j (1 : k) : Fin 3 → k) i)) = Pi.single j 1 := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hσs, ← map_ringEquiv_mulVec, hσs, hPe]
    have hΦu : ∀ j : Fin 3, G *ᵥ (fun i => σ (u j i)) = u (j + 1) := by
      intro j
      fin_cases j
      · rfl
      · rfl
      · exact hΦ3
    rw [hΦu]
    have hC : ∀ j : Fin 3, (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) k) *ᵥ
        (Pi.single j 1) = Pi.single (j + 1) 1 := by
      intro j
      fin_cases j <;> ext i <;> fin_cases i <;> simp
    rw [hC, hPe]
  · simp [hDdef]
  · simp [hDdef]
  · simp only [hDdef]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have hzinv3 : z⁻¹ ^ 3 = 1 := by rw [inv_pow, hz3, inv_one]
    linear_combination (-ξ) * hzinv3

theorem exists_fixed_of_semiBy [Finite k] {φ : MulAut (SpecialLinearGroup (Fin 3) k)}
    {σ : k ≃+* k} {g : GL (Fin 3) k} (hσ : orderOf σ = 3) (hφ : SemiBy φ σ g)
    (hφ3 : φ ^ 3 = 1) {s : SpecialLinearGroup (Fin 3) k} (hs3 : s ^ 3 = 1)
    (hcomm : MulAut.conj s * φ = φ * MulAut.conj s) (hφs : φ s ≠ s) :
    ∃ t : SpecialLinearGroup (Fin 3) k, φ t = t ∧
      s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin 3) k) ∧
      s * t * s⁻¹ * t⁻¹ ≠ 1 := by
  classical
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨g', hg', hN⟩ := exists_semiBy_norm_one hσ hφ hφ3
  have hcen : s⁻¹ * φ s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) k) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun χ : MulAut (SpecialLinearGroup (Fin 3) k) => χ (φ.symm y)) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    calc y * (s⁻¹ * φ s) = s⁻¹ * (s * y * s⁻¹) * φ s := by group
      _ = s⁻¹ * (φ s * y * (φ s)⁻¹) * φ s := by rw [h1]
      _ = s⁻¹ * φ s * y := by group
  obtain ⟨z, hz3, hzs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  rw [Fintype.card_fin] at hz3
  have hscal : ∀ c : k, (Matrix.scalar (Fin 3) c : Matrix (Fin 3) (Fin 3) k) = c • 1 := by
    intro c
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hφsm : ((φ s : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      z • (s : Matrix (Fin 3) (Fin 3) k) := by
    have e : φ s = s * (s⁻¹ * φ s) := by group
    rw [e, Matrix.SpecialLinearGroup.coe_mul, ← hzs, hscal, Matrix.mul_smul, Matrix.mul_one]
  have hz1 : z ≠ 1 := by
    intro h1
    apply hφs
    apply Subtype.ext
    rw [hφsm, h1, one_smul]
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz3
  have hgs : (g' : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k).map σ =
      z • ((s : Matrix (Fin 3) (Fin 3) k) * (g' : Matrix (Fin 3) (Fin 3) k)) := by
    have h1 := congrArg (fun x : GL (Fin 3) k => (x : Matrix (Fin 3) (Fin 3) k)) (hg' s)
    simp only [Units.val_mul, coe_map_ringEquiv, SpecialLinearGroup.coe_GL_coe_matrix] at h1
    rw [hφsm] at h1
    rw [← Matrix.smul_mul, h1, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hS3 : (s : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hs3, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨P, D, hsP, hgP, hD1, hD2, hD0⟩ := exists_semilinear_basis hσ3 hN hS3 hz3 hz1 hgs
  set C : Matrix (Fin 3) (Fin 3) k := !![0, 0, 1; 1, 0, 0; 0, 1, 0] with hCdef
  have hCs : ((shiftSL : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = C := rfl
  have hCσ : C.map σ = C := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hCdef]
  set t : SpecialLinearGroup (Fin 3) k := conjUnit P shiftSL with htdef
  have htm : (t : Matrix (Fin 3) (Fin 3) k) = (P : Matrix (Fin 3) (Fin 3) k) * C *
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    rw [htdef, conjUnit_coe, hCs]
  have hPi : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
      1 := Units.inv_mul P
  have htP : (t : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
      (P : Matrix (Fin 3) (Fin 3) k) * C := by
    rw [htm, Matrix.mul_assoc, hPi, Matrix.mul_one]
  set Y : GL (Fin 3) k := P * SpecialLinearGroup.toGL shiftSL with hYdef
  have hYm : (Y : Matrix (Fin 3) (Fin 3) k) = (P : Matrix (Fin 3) (Fin 3) k) * C := by
    rw [hYdef, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, hCs]
  have hcancel : ∀ A B : Matrix (Fin 3) (Fin 3) k,
      A * (Y : Matrix (Fin 3) (Fin 3) k) = B * (Y : Matrix (Fin 3) (Fin 3) k) → A = B := by
    intro A B h
    calc A = A * (Y : Matrix (Fin 3) (Fin 3) k) *
          ((Y⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = B := by rw [h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨t, ?_, ?_⟩
  ·
    apply Subtype.ext
    have h1 := congrArg Units.val (hg' t)
    rw [Units.val_mul, Units.val_mul, coe_map_ringEquiv, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.coe_GL_coe_matrix] at h1
    apply hcancel
    rw [hYm, h1]
    have h2 : (g' : Matrix (Fin 3) (Fin 3) k) * (t : Matrix (Fin 3) (Fin 3) k).map σ *
        ((g'⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
          ((P : Matrix (Fin 3) (Fin 3) k) * C) =
        (g' : Matrix (Fin 3) (Fin 3) k) * ((t : Matrix (Fin 3) (Fin 3) k) *
          (P : Matrix (Fin 3) (Fin 3) k)).map σ := by
      rw [← hgP, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((g'⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
        (g' : Matrix (Fin 3) (Fin 3) k), Units.inv_mul, Matrix.one_mul]
    rw [h2, htP, Matrix.map_mul, hCσ, ← Matrix.mul_assoc, hgP, htm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
      (P : Matrix (Fin 3) (Fin 3) k), hPi, Matrix.one_mul]
  ·
    have hDC : diagonal D * C = z⁻¹ • (C * diagonal D) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp [hCdef]
      all_goals first | exact hD0 | exact hD1 | exact hD2
    have hst : (s : Matrix (Fin 3) (Fin 3) k) * (t : Matrix (Fin 3) (Fin 3) k) =
        z⁻¹ • ((t : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k)) := by
      have hPinv : ∀ A B : Matrix (Fin 3) (Fin 3) k,
          A * (P : Matrix (Fin 3) (Fin 3) k) = B * (P : Matrix (Fin 3) (Fin 3) k) → A = B := by
        intro A B h
        calc A = A * (P : Matrix (Fin 3) (Fin 3) k) *
              ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
              rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
          _ = B := by rw [h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      apply hPinv
      rw [Matrix.smul_mul, Matrix.mul_assoc, htP, ← Matrix.mul_assoc, hsP, Matrix.mul_assoc,
        hDC, Matrix.mul_assoc, hsP, ← Matrix.mul_assoc, htP, Matrix.mul_smul, Matrix.mul_assoc]
    set c : SpecialLinearGroup (Fin 3) k := s * t * s⁻¹ * t⁻¹ with hcdef
    have hcm : (c : Matrix (Fin 3) (Fin 3) k) = z⁻¹ • 1 := by
      have e1 : c * (t * s) = s * t := by rw [hcdef]; group
      have e2 := congrArg (fun x : SpecialLinearGroup (Fin 3) k => (x : Matrix (Fin 3) (Fin 3) k))
        e1
      simp only [Matrix.SpecialLinearGroup.coe_mul] at e2
      rw [hst] at e2
      have e3 : (c : Matrix (Fin 3) (Fin 3) k) * ((t * s : SpecialLinearGroup (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) = (z⁻¹ • 1) * ((t * s : SpecialLinearGroup (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.smul_mul, Matrix.one_mul]
        exact e2
      calc (c : Matrix (Fin 3) (Fin 3) k) = (c : Matrix (Fin 3) (Fin 3) k) *
            ((t * s : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
            (((t * s)⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
            rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
              Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
        _ = z⁻¹ • 1 := by
            rw [e3, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
              Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
    refine ⟨Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨z⁻¹, ?_, ?_⟩, ?_⟩
    · rw [Fintype.card_fin, inv_pow, hz3, inv_one]
    · rw [hscal, hcm]
    · intro h1
      apply hz1
      have h2 := congrArg (fun x : SpecialLinearGroup (Fin 3) k =>
        (x : Matrix (Fin 3) (Fin 3) k) 0 0) h1
      simp only [hcm, Matrix.SpecialLinearGroup.coe_one, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one] at h2
      exact inv_eq_one.mp h2

end Semilinear

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
