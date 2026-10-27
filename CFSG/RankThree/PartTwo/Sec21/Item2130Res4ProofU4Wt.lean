module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUModel
public import CFSG.RankThree.Classical.SteinbergBJCharacterSpaces
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof

open Matrix Module CFSG.LieType.BorelTits CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Abstract

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Γ : Type*} [Group Γ] {ρ : Γ →* Module.End K V} {ζ : K}

theorem root_pow_val_sum {ι : Type*} (hζ : ζ ^ 3 = 1) (s : Finset ι) (a : ι → ZMod 3) :
    ζ ^ (∑ i ∈ s, a i).val = ∏ i ∈ s, ζ ^ (a i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, root_pow_val_add hζ, ih]

theorem root_pow_val_inj (hζ : IsPrimitiveRoot ζ 3) {a b : ZMod 3}
    (h : ζ ^ a.val = ζ ^ b.val) : a = b := by
  have e := root_pow_val_add hζ.pow_eq_one (a - b) b
  rw [sub_add_cancel, h] at e
  have hb0 : ζ ^ b.val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by norm_num))
  have h1 : ζ ^ (a - b).val = 1 := by
    have e' : ζ ^ (a - b).val * ζ ^ b.val = 1 * ζ ^ b.val := by rw [one_mul, ← e]
    exact mul_right_cancel₀ hb0 e'
  exact sub_eq_zero.mp ((root_pow_val_eq_one_iff hζ _).mp h1)

theorem form_eq_zero_of_weight_ne (F : ReflForm K V) (hζ : IsPrimitiveRoot ζ 3)
    (hσζ : F.σ ζ = ζ⁻¹) (hρ : ∀ g u v, F.β (ρ g u) (ρ g v) = F.β u v)
    {χ ψ : Additive Γ →+ ZMod 3} (h : χ ≠ ψ) {v w : V}
    (hv : ∀ g, ρ g v = ζ ^ (χ (Additive.ofMul g)).val • v)
    (hw : ∀ g, ρ g w = ζ ^ (ψ (Additive.ofMul g)).val • w) : F.β v w = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : Γ, (ψ - χ) (Additive.ofMul g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (sub_eq_zero.mp (AddMonoidHom.ext fun x => hcon (Additive.toMul x))).symm
  have h1 : ζ ^ ((ψ - χ) (Additive.ofMul g)).val ≠ 1 := fun h1 =>
    hg ((root_pow_val_eq_one_iff hζ _).mp h1)
  have hσ : F.σ (ζ ^ (χ (Additive.ofMul g)).val) = ζ ^ ((-χ) (Additive.ofMul g)).val := by
    rw [map_pow, hσζ, inv_pow, AddMonoidHom.neg_apply]
    exact (eq_inv_of_mul_eq_one_left
      (root_pow_val_neg_mul hζ.pow_eq_one (χ (Additive.ofMul g)))).symm
  have key : F.β v w = ζ ^ ((ψ - χ) (Additive.ofMul g)).val * F.β v w := by
    conv_lhs => rw [← hρ g v w, hv g, hw g]
    rw [F.smul_left, F.smul_right, hσ, ← mul_assoc, ← root_pow_val_add hζ.pow_eq_one,
      AddMonoidHom.sub_apply, AddMonoidHom.neg_apply, neg_add_eq_sub]
  have : (ζ ^ ((ψ - χ) (Additive.ofMul g)).val - 1) * F.β v w = 0 := by
    rw [sub_mul, ← key, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

theorem eq_one_of_weights {n : ℕ} (b : Basis (Fin n) K V) (w : Fin n → Additive Γ →+ ZMod 3)
    (hb : ∀ i g, ρ g (b i) = ζ ^ (w i (Additive.ofMul g)).val • b i)
    (hfaith : ∀ g, ρ g = 1 → g = 1) {g : Γ} (hg : ∀ i, w i (Additive.ofMul g) = 0) : g = 1 := by
  apply hfaith
  apply b.ext
  intro i
  rw [hb, hg i, ZMod.val_zero, pow_zero, one_smul, Module.End.one_apply]

theorem sum_weights_eq_zero (hζ : IsPrimitiveRoot ζ 3) {n : ℕ} (b : Basis (Fin n) K V)
    (w : Fin n → Additive Γ →+ ZMod 3)
    (hb : ∀ i g, ρ g (b i) = ζ ^ (w i (Additive.ofMul g)).val • b i)
    (hdet : ∀ g, LinearMap.det (ρ g) = 1) : ∑ i, w i = 0 := by
  classical
  refine AddMonoidHom.ext fun x => ?_
  set g : Γ := Additive.toMul x with hgx
  have hx : x = Additive.ofMul g := rfl
  have hmat : LinearMap.toMatrix b b (ρ g) =
      Matrix.diagonal fun i => ζ ^ (w i (Additive.ofMul g)).val := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have h1 := hdet g
  rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal] at h1
  have h2 : ∏ i, ζ ^ (w i (Additive.ofMul g)).val =
      ζ ^ ((∑ i, w i) (Additive.ofMul g)).val := by
    rw [AddMonoidHom.finsetSum_apply, root_pow_val_sum hζ.pow_eq_one]
  rw [h2] at h1
  rw [hx, (root_pow_val_eq_one_iff hζ _).mp h1, AddMonoidHom.zero_apply]

end Abstract

section Basis

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {ρ : Γ →* Module.End K V} {ζ : K}

theorem exists_basis_weights [Fintype (Additive Γ →+ ZMod 3)] (hζ : IsPrimitiveRoot ζ 3)
    (hexp : ∀ g : Γ, g ^ 3 = 1) (hΓ : (Fintype.card Γ : K) ≠ 0) {n : ℕ}
    (hn : finrank K V = n) :
    ∃ (b : Basis (Fin n) K V) (w : Fin n → Additive Γ →+ ZMod 3),
      ∀ i g, ρ g (b i) = ζ ^ (w i (Additive.ofMul g)).val • b i := by
  classical
  have hint : DirectSum.IsInternal (charSpace ρ ζ (p := 3)) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨iSupIndep_charSpace hζ hΓ, iSup_charSpace_eq_top Nat.prime_three hζ hexp hΓ⟩
  let bχ := fun χ : Additive Γ →+ ZMod 3 => Module.finBasis K (charSpace ρ ζ χ)
  let B := hint.collectedBasis bχ
  have hcard : Fintype.card (Σ χ : Additive Γ →+ ZMod 3,
      Fin (finrank K (charSpace ρ ζ χ))) = n := by
    rw [← hn, Module.finrank_eq_card_basis B]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨B.reindex e, fun i => (e.symm i).1, fun i g => ?_⟩
  rw [Basis.reindex_apply]
  exact (mem_charSpace.mp (hint.collectedBasis_mem bχ (e.symm i))) g

end Basis

section Pattern

variable {Γ : Type*} [CommGroup Γ] [Fintype Γ]

omit [Fintype Γ] in
theorem weight_three_eq {w : Fin 4 → Additive Γ →+ ZMod 3} (hsum : ∑ i, w i = 0)
    (y : Additive Γ) : w 3 y = -(w 0 y + w 1 y + w 2 y) := by
  have := congrArg (fun χ : Additive Γ →+ ZMod 3 => χ y) hsum
  simp only [Fin.sum_univ_four, AddMonoidHom.add_apply, AddMonoidHom.zero_apply] at this
  exact eq_neg_of_add_eq_zero_right this

theorem exists_weight_values (hcard : Fintype.card Γ = 27) (w : Fin 4 → Additive Γ →+ ZMod 3)
    (hsum : ∑ i, w i = 0) (hsep : ∀ g : Γ, (∀ i, w i (Additive.ofMul g) = 0) → g = 1)
    (a b c : ZMod 3) : ∃ x : Γ, w 0 (Additive.ofMul x) = a ∧ w 1 (Additive.ofMul x) = b ∧
      w 2 (Additive.ofMul x) = c ∧ w 3 (Additive.ofMul x) = -(a + b + c) := by
  have hsplit : ∀ (j : Fin 4) (g g' : Γ), w j (Additive.ofMul (g * g'⁻¹)) =
      w j (Additive.ofMul g) - w j (Additive.ofMul g') := by
    intro j g g'
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, sub_eq_add_neg]
  let ev : Γ → ZMod 3 × ZMod 3 × ZMod 3 := fun g =>
    (w 0 (Additive.ofMul g), w 1 (Additive.ofMul g), w 2 (Additive.ofMul g))
  have hinj : Function.Injective ev := by
    intro g g' hgg'
    simp only [ev, Prod.mk.injEq] at hgg'
    obtain ⟨h0, h1, h2⟩ := hgg'
    have hall : ∀ i, w i (Additive.ofMul (g * g'⁻¹)) = 0 := by
      intro i
      fin_cases i
      · rw [Fin.zero_eta, hsplit, h0, sub_self]
      · rw [Fin.mk_one, hsplit, h1, sub_self]
      · change w 2 _ = 0
        rw [hsplit, h2, sub_self]
      · change w 3 _ = 0
        rw [weight_three_eq hsum, hsplit, hsplit, hsplit, h0, h1, h2]
        simp
    exact mul_inv_eq_one.mp (hsep _ hall)
  have hbij : Function.Bijective ev := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hcard]; rfl⟩
  obtain ⟨x, hx⟩ := hbij.2 (a, b, c)
  simp only [ev, Prod.mk.injEq] at hx
  obtain ⟨ha, hb, hc⟩ := hx
  exact ⟨x, ha, hb, hc, by rw [weight_three_eq hsum, ha, hb, hc]⟩

theorem exists_weight_pattern (hcard : Fintype.card Γ = 27) (w : Fin 4 → Additive Γ →+ ZMod 3)
    (hsum : ∑ i, w i = 0) (hsep : ∀ g : Γ, (∀ i, w i (Additive.ofMul g) = 0) → g = 1) :
    Function.Injective w ∧ ∃ x : Γ, ∀ i, w i (Additive.ofMul x) = if i = 3 then 0 else 1 := by
  have hval := exists_weight_values hcard w hsum hsep
  refine ⟨?_, ?_⟩
  · obtain ⟨x0, a0, b0, c0, d0⟩ := hval 1 0 0
    obtain ⟨x1, a1, b1, c1, d1⟩ := hval 0 1 0
    obtain ⟨x2, a2, b2, c2, d2⟩ := hval 0 0 1
    set T : Fin 4 → Fin 3 → ZMod 3 := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, -1, -1]]
      with hTdef
    have hT : ∀ (i : Fin 4) (k : Fin 3), w i (Additive.ofMul (![x0, x1, x2] k)) = T i k := by
      intro i k
      fin_cases i <;> fin_cases k <;> simp [hTdef, a0, b0, c0, d0, a1, b1, c1, d1, a2, b2, c2, d2]
    have key : ∀ i j : Fin 4, (∀ k : Fin 3, T i k = T j k) → i = j := by
      rw [hTdef]
      decide
    intro i j hij
    exact key i j fun k => by rw [← hT, ← hT, hij]
  · obtain ⟨x, a, b, c, d⟩ := hval 1 1 1
    refine ⟨x, fun i => ?_⟩
    fin_cases i
    · exact a
    · exact b
    · exact c
    · rw [show ((⟨3, by norm_num⟩ : Fin 4) : Fin 4) = 3 from rfl, d]
      decide

end Pattern

section Unitary

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

omit [Fact (Nat.Prime 2)] [CharP K 2] in
theorem exists_cube_root_bar_inv (h : UnitaryFieldData 2 f K) (hf : Odd f) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ h.bar ω = ω⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK := card_sq_of_unitary h
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : (2 ^ f) ^ 2 % 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
      norm_num
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hω3 : (x : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  have hω1 : (x : K) ≠ 1 := fun h1 => hx1 (Units.ext h1)
  refine ⟨x, hω3, hω1, ?_⟩
  have hq : 2 ^ f % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hf
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hω0 : (x : K) ≠ 0 := x.ne_zero
  rw [UnitaryFieldData.bar_apply, ← Nat.mod_add_div (2 ^ f) 3, pow_add, pow_mul, hω3, one_pow,
    mul_one, hq]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, hω3]

variable (h : UnitaryFieldData 2 f K)

omit [Finite K] [Fact (Nat.Prime 2)] in
theorem twentyseven_eq_one : (27 : K) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination 13 * h2

theorem exists_orthonormal_eigen_plus (hf : Odd f) (E : Subgroup (uS h 4))
    (hE : Late.IsE27 E) :
    ∃ (ω : K) (v : Fin 4 → Fin 4 → K) (x y₀ : uS h 4), x ∈ E ∧ y₀ ∈ E ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      h.bar ω = ω⁻¹ ∧ (∀ i j, (uF h 4).β (v i) (v j) = if i = j then 1 else 0) ∧
      (∀ i, ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v i =
        (if i = 3 then 1 else ω) • v i) ∧
      (∀ i, ((y₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v i =
        (![ω, 1, 1, ω ^ 2] : Fin 4 → K) i • v i) ∧
      ∀ y ∈ E, ∃ μ : Fin 4 → K,
        (∀ i, ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v i = μ i • v i) ∧
        (μ 0 = μ 1 → μ 1 = μ 2 → y ∈ Subgroup.zpowers x) := by
  classical
  obtain ⟨ω, hω3, hω1, hωbar⟩ := exists_cube_root_bar_inv h hf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hω3 hω1)
  have hσζ : (uF h 4).σ ω = ω⁻¹ := by rw [uF_σ, hωbar]
  obtain ⟨hEc, hEexp⟩ := hE.1
  let : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => hEc.is_comm.comm a b }
  let ρ : E →* Module.End K (Fin 4 → K) := (natRep (uS h 4)).comp E.subtype
  have hρ : ∀ (g : E) (v : Fin 4 → K),
      ρ g v = (((g : uS h 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v := fun g v => by
    simp [ρ]
  have : Fintype E := Fintype.ofFinite E
  have : Finite (Additive E) := Finite.of_equiv E Additive.ofMul
  have : Finite (Additive E →+ ZMod 3) := Finite.of_injective _ DFunLike.coe_injective
  let : Fintype (Additive E →+ ZMod 3) := Fintype.ofFinite _
  have hcard : Fintype.card E = 27 := by rw [Fintype.card_eq_nat_card, hE.2]
  have hexp : ∀ g : E, g ^ 3 = 1 := fun g => Subtype.ext (hEexp g g.2)
  have hΓ : (Fintype.card E : K) ≠ 0 := by
    rw [hcard, Nat.cast_ofNat, twentyseven_eq_one]
    exact one_ne_zero
  have hfaith : ∀ g : E, ρ g = 1 → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply natRep_injective (uS h 4)
    rw [Subgroup.coe_one, map_one]
    exact hg
  obtain ⟨b, w, hb⟩ := exists_basis_weights (ρ := ρ) hζ hexp hΓ (Module.finrank_fin_fun K)
  have hdet : ∀ g : E, LinearMap.det (ρ g) = 1 := by
    intro g
    have e : ρ g = Matrix.toLin' (((g : uS h 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
      LinearMap.ext fun v => by rw [hρ, Matrix.toLin'_apply]
    rw [e, LinearMap.det_toLin']
    exact (g : uS h 4).2.2
  have hsum := sum_weights_eq_zero hζ b w hb hdet
  have hsep : ∀ g : E, (∀ i, w i (Additive.ofMul g) = 0) → g = 1 :=
    fun g hg => eq_one_of_weights b w hb hfaith hg
  obtain ⟨hwinj, x, hx⟩ := exists_weight_pattern hcard w hsum hsep
  obtain ⟨y0, a0, b0, c0, d0⟩ := exists_weight_values hcard w hsum hsep 1 0 0
  have hiso : ∀ (g : E) (u v : Fin 4 → K), (uF h 4).β (ρ g u) (ρ g v) = (uF h 4).β u v := by
    intro g u v
    rw [hρ, hρ]
    exact uF_isometry_of_mem h (g : uS h 4).2 u v
  have horth : ∀ i j, i ≠ j → (uF h 4).β (b i) (b j) = 0 := fun i j hij =>
    form_eq_zero_of_weight_ne (uF h 4) hζ hσζ hiso (hwinj.ne hij) (hb i) (hb j)
  have hnz : ∀ i, (uF h 4).β (b i) (b i) ≠ 0 := by
    intro i h0
    apply b.ne_zero i
    have hD : (uF h 4).toDual (b i) = 0 := b.ext fun j => by
      rw [ReflForm.toDual_apply, LinearMap.zero_apply]
      by_cases hij : i = j
      · rw [← hij, h0]
      · exact horth i j hij
    exact (uF h 4).nondeg _ fun v => by rw [← ReflForm.toDual_apply, hD, LinearMap.zero_apply]
  have hfix : ∀ i, unitaryInvolution K 2 f ((uF h 4).β (b i) (b i))⁻¹ =
      ((uF h 4).β (b i) (b i))⁻¹ := by
    intro i
    rw [map_inv₀]
    congr 1
    exact (uF_symm h (b i) (b i)).symm
  choose s hs using fun i => CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed
    (card_sq_of_unitary h) (hfix i) (inv_ne_zero (hnz i))
  have hdiag : ∀ (g : E) (i : Fin 4), (((g : uS h 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      *ᵥ (s i • b i) = ω ^ (w i (Additive.ofMul g)).val • (s i • b i) := by
    intro g i
    rw [Matrix.mulVec_smul, ← hρ, hb, smul_comm]
  refine ⟨ω, fun i => s i • b i, x, y0, x.2, y0.2, hω3, hω1, hωbar, fun i j => ?_, fun i => ?_,
    fun i => ?_, fun y hy => ?_⟩
  · rw [(uF h 4).smul_left, (uF h 4).smul_right]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ← mul_assoc]
      change unitaryInvolution K 2 f (s i) * s i * _ = 1
      rw [hs i, inv_mul_cancel₀ (hnz i)]
    · rw [ite_eq_right hij, horth i j hij, mul_zero, mul_zero]
  · rw [hdiag, hx i]
    congr 1
    by_cases hi : i = 3
    · rw [ite_eq_left hi, ite_eq_left hi, ZMod.val_zero, pow_zero]
    · rw [ite_eq_right hi, ite_eq_right hi]
      exact pow_one ω
  · rw [hdiag]
    congr 1
    fin_cases i
    · rw [Fin.zero_eta, a0]
      exact pow_one ω
    · rw [Fin.mk_one, b0, ZMod.val_zero, pow_zero]
      rfl
    · change ω ^ (w 2 _).val = _
      rw [c0, ZMod.val_zero, pow_zero]
      rfl
    · change ω ^ (w 3 _).val = _
      rw [d0]
      rfl
  ·
    set g : E := ⟨y, hy⟩ with hg
    refine ⟨fun i => ω ^ (w i (Additive.ofMul g)).val, fun i => hdiag g i, fun h01 h12 => ?_⟩
    have e01 := root_pow_val_inj hζ h01
    have e12 := root_pow_val_inj hζ h12
    set k := (w 0 (Additive.ofMul g)).val with hk
    have hxk : ∀ i, w i (Additive.ofMul (x ^ k)) = if i = 3 then 0 else w 0 (Additive.ofMul g) := by
      intro i
      rw [ofMul_pow, map_nsmul, hx i]
      by_cases hi : i = 3
      · rw [ite_eq_left hi, ite_eq_left hi, smul_zero]
      · rw [ite_eq_right hi, ite_eq_right hi, nsmul_eq_mul, mul_one, hk, ZMod.natCast_zmod_val]
    have hgx : g * (x ^ k)⁻¹ = 1 := by
      apply hsep
      intro i
      rw [ofMul_mul, ofMul_inv, map_add, map_neg, hxk i]
      fin_cases i
      · simp
      · simp [← e01]
      · change w 2 _ + -(if (2 : Fin 4) = 3 then 0 else w 0 _) = 0
        rw [ite_eq_right (by decide), ← e12, ← e01, add_neg_cancel]
      · change w 3 _ + -(if (3 : Fin 4) = 3 then 0 else w 0 _) = 0
        rw [ite_eq_left rfl, neg_zero, add_zero, weight_three_eq hsum, ← e12, ← e01]
        have h3 : w 0 (Additive.ofMul g) + w 0 (Additive.ofMul g) + w 0 (Additive.ofMul g) =
            3 * w 0 (Additive.ofMul g) := by ring
        rw [h3, show (3 : ZMod 3) = 0 from rfl, zero_mul, neg_zero]
    have hgk : g = x ^ k := mul_inv_eq_one.mp hgx
    have hyk : y = ((x : uS h 4)) ^ k := congrArg Subtype.val hgk
    rw [hyk]
    exact Subgroup.npow_mem_zpowers _ k

end Unitary

end CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof
