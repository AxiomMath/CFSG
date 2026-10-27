module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NZorn
public import CFSG.RankThree.PartTwo.Sec8.Hering88NG2Exp

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open Polynomial CFSG.Open CFSG.Quasithin.H13.Orbit

theorem pow_three_eq_zero_of_isNilpotent {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (hdim : Module.finrank L V ≤ 3) (N : Module.End L V)
    (hN : IsNilpotent N) : N ^ 3 = 0 := by
  obtain ⟨n, hn⟩ := hN
  have h : N ^ Module.finrank L V = 0 := by
    have := Module.End.ker_pow_le_ker_pow_finrank N n
    rw [hn, LinearMap.ker_zero] at this
    exact LinearMap.ker_eq_top.mp (top_unique this)
  rw [show 3 = (3 - Module.finrank L V) + Module.finrank L V by omega, pow_add, h, mul_zero]

theorem commute_aeval_right {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {a b : A}
    (h : Commute a b) (p : R[X]) : Commute a (aeval b p) := by
  refine Polynomial.induction_on p (fun c => ?_) (fun p q hp hq => ?_) (fun n c _ => ?_)
  · rw [aeval_C]
    exact (show Commute a (algebraMap R A c) from (Algebra.commutes c a).symm)
  · rw [map_add]
    exact hp.add_right hq
  · rw [map_mul, map_pow, aeval_C, aeval_X]
    exact (show Commute a (algebraMap R A c) from (Algebra.commutes c a).symm).mul_right
      (h.pow_right (n + 1))

theorem pow_three_eq_zero_of_commute {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hirr : ∀ a : K, a ^ 2 + a + 1 ≠ 0) (g : Module.End K V)
    (hg : g ^ 2 + g + 1 = 0) (hdim : Module.finrank K V ≤ 7) (N : Module.End K V)
    (hNg : Commute N g) (hN : IsNilpotent N) : N ^ 3 = 0 := by
  set f : K[X] := X ^ 2 + X + 1 with hf
  have hfdeg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hfirr : Irreducible f := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hfdeg]; decide)
      fun a ha => hirr a ?_
    simpa [hf, IsRoot] using ha
  haveI : Fact (Irreducible f) := ⟨hfirr⟩
  have hgf : aeval g f = 0 := by
    rw [hf, map_add, map_add, map_pow, aeval_X, map_one]
    exact hg
  let ψ : AdjoinRoot f →+* Module.End K V :=
    Ideal.Quotient.lift (Ideal.span {f}) (aeval g : K[X] →ₐ[K] Module.End K V).toRingHom
      fun a ha => by
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
        show aeval g (f * q) = 0
        rw [map_mul, hgf, zero_mul]
  have hψ : ∀ p : K[X], ψ (AdjoinRoot.mk f p) = aeval g p := fun _ => rfl
  letI : Module (AdjoinRoot f) V := Module.compHom V ψ
  have hsmul : ∀ (l : AdjoinRoot f) (v : V), l • v = ψ l v := fun _ _ => rfl
  haveI : IsScalarTower K (AdjoinRoot f) V := ⟨fun c l v => by
    rw [hsmul, hsmul, Algebra.smul_def, map_mul, Module.End.mul_apply, AdjoinRoot.algebraMap_eq,
      ← AdjoinRoot.mk_C, hψ, aeval_C, Module.algebraMap_end_apply]⟩
  have hL : Module.finrank K (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hfirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hfdeg]
  haveI : Module.Finite (AdjoinRoot f) V :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot f) V
  have htower := Module.finrank_mul_finrank K (AdjoinRoot f) V
  rw [hL] at htower
  have hdimL : Module.finrank (AdjoinRoot f) V ≤ 3 := by omega
  have hcomm : ∀ (l : AdjoinRoot f) (v : V), N (ψ l v) = ψ l (N v) := by
    intro l v
    induction l using AdjoinRoot.induction_on with
    | ih p =>
      rw [hψ]
      exact congrArg (fun φ : Module.End K V => φ v) (commute_aeval_right hNg p).eq
  let NL : V →ₗ[AdjoinRoot f] V :=
    { toFun := N
      map_add' := N.map_add
      map_smul' := fun l v => by
        rw [hsmul, hsmul]
        exact hcomm l v }
  have hpow : ∀ (k : ℕ) (v : V), (NL ^ k) v = (N ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  have hNL : IsNilpotent NL := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, LinearMap.ext fun v => by rw [hpow, hk]; rfl⟩
  have h3 := pow_three_eq_zero_of_isNilpotent hdimL NL hNL
  exact LinearMap.ext fun v => by rw [← hpow, h3]; rfl

theorem restrict_pow_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p : Submodule K V} (f : Module.End K V) (hf : ∀ x ∈ p, f x ∈ p) (k : ℕ) (x : p) :
    (((f.restrict hf) ^ k) x : V) = (f ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    show f ((((f.restrict hf) ^ k) x : p) : V) = _
    rw [ih, pow_succ', Module.End.mul_apply]

theorem quasithinThreeCentTwoExp_holds : QuasithinThreeCentTwoExp := by
  intro K _ _ _ hK3 z hz3 hz1 y hyz hy
  set Z : Module.End K (quasithinZorn K) :=
    ((z : quasithinZorn K ≃ₗ[K] quasithinZorn K) : Module.End K (quasithinZorn K)) with hZdef
  set Y : Module.End K (quasithinZorn K) :=
    ((y : quasithinZorn K ≃ₗ[K] quasithinZorn K) : Module.End K (quasithinZorn K)) with hYdef
  have hZ3 : Z ^ 3 = 1 := by
    rw [hZdef, ← coe_end_pow, ← Subgroup.coe_pow, hz3]
    rfl
  have hYZ : Commute Y Z := by
    have h1 := congrArg (fun w : quasithinG2 K =>
      ((w : quasithinZorn K ≃ₗ[K] quasithinZorn K) : Module.End K (quasithinZorn K))) hyz
    exact h1
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by
      calc (3 : K) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [this]
    exact one_ne_zero
  haveI : CharP (Module.End K (quasithinZorn K)) 2 :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K (quasithinZorn K))).injective 2
  classical
  haveI := Fintype.ofFinite K
  have hirr : ∀ a : K, a ^ 2 + a + 1 ≠ 0 := by
    intro a ha
    have ha3 : a ^ 3 = 1 := by linear_combination (a - 1) * ha
    have ha1 : a ≠ 1 := by
      rintro rfl
      apply h3
      linear_combination ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha3
    let u : Kˣ := Units.mk0 a ha0
    have hu : orderOf u = 3 := by
      apply orderOf_eq_prime
      · exact Units.ext (by simp [u, ha3])
      · intro h
        apply ha1
        have := congrArg Units.val h
        simpa [u] using this
    have hdvd : 3 ∣ Fintype.card Kˣ := hu ▸ orderOf_dvd_card
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card] at hdvd
    have hK2 : 2 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  have hc := isCompl_ker_sub_one_ker_sq_add_add_one h3 Z hZ3
  set B := LinearMap.ker (Z - 1) with hBdef
  set M := LinearMap.ker (Z ^ 2 + Z + 1) with hMdef
  set N := Y - 1 with hNdef
  have hNZ : Commute N Z := hYZ.sub_left (Commute.one_left Z)
  have hBinv : ∀ x ∈ B, N x ∈ B := fun x hx => by
    rw [hBdef, LinearMap.mem_ker] at hx ⊢
    have e : (Z - 1) * N = N * (Z - 1) := (hNZ.sub_right (Commute.one_right N)).eq.symm
    calc (Z - 1 : Module.End K (quasithinZorn K)) (N x) =
          ((Z - 1) * N : Module.End K (quasithinZorn K)) x := rfl
      _ = (N * (Z - 1) : Module.End K (quasithinZorn K)) x := by rw [e]
      _ = 0 := by rw [Module.End.mul_apply, hx, map_zero]
  have hMinv : ∀ x ∈ M, N x ∈ M := fun x hx => by
    rw [hMdef, LinearMap.mem_ker] at hx ⊢
    have e : (Z ^ 2 + Z + 1) * N = N * (Z ^ 2 + Z + 1) :=
      (((hNZ.pow_right 2).add_right hNZ).add_right (Commute.one_right N)).eq.symm
    calc (Z ^ 2 + Z + 1 : Module.End K (quasithinZorn K)) (N x) =
          ((Z ^ 2 + Z + 1) * N : Module.End K (quasithinZorn K)) x := rfl
      _ = (N * (Z ^ 2 + Z + 1) : Module.End K (quasithinZorn K)) x := by rw [e]
      _ = 0 := by rw [Module.End.mul_apply, hx, map_zero]
  have hZM : ∀ x ∈ M, Z x ∈ M := fun x hx => by
    rw [hMdef, LinearMap.mem_ker] at hx ⊢
    have e : (Z ^ 2 + Z + 1) * Z = Z * (Z ^ 2 + Z + 1) :=
      (((Commute.refl Z).pow_left 2).add_left (Commute.refl Z)).add_left (Commute.one_left Z) |>.eq
    calc (Z ^ 2 + Z + 1 : Module.End K (quasithinZorn K)) (Z x) =
          ((Z ^ 2 + Z + 1) * Z : Module.End K (quasithinZorn K)) x := rfl
      _ = (Z * (Z ^ 2 + Z + 1) : Module.End K (quasithinZorn K)) x := by rw [e]
      _ = 0 := by rw [Module.End.mul_apply, hx, map_zero]
  obtain ⟨k, hk⟩ := hy
  have hYk : Y ^ 2 ^ k = 1 := by
    rw [hYdef, ← coe_end_pow, ← Subgroup.coe_pow, hk]
    rfl
  have hNk : N ^ 2 ^ k = 0 := by
    rw [hNdef, sub_pow_char_pow_of_commute (p := 2) (h := Commute.one_right Y), one_pow, hYk,
      sub_self]
  have hBdim : Module.finrank K B ≤ 4 :=
    finrank_ker_sub_one_le_four (g := (z : quasithinZorn K ≃ₗ[K] quasithinZorn K)) z.2
      (by rw [← Subgroup.coe_pow, hz3]; rfl)
      (fun h => hz1 (Subtype.ext h))
  have hB4 : (N.restrict hBinv) ^ 4 = 0 :=
    pow_four_eq_zero_of_isNilpotent hBdim _
      ⟨2 ^ k, LinearMap.ext fun x => Subtype.ext (by rw [restrict_pow_apply, hNk]; rfl)⟩
  have hBne : B ≠ ⊥ := by
    intro hB0
    have h1 : zornOne ∈ B := by
      rw [hBdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact quasithinG2_one z.2
    rw [hB0, Submodule.mem_bot] at h1
    have := congrArg Prod.fst h1
    simp [zornOne] at this
  have hBpos : 0 < Module.finrank K B :=
    Nat.pos_of_ne_zero fun h => hBne (Submodule.finrank_eq_zero.mp h)
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_zorn] at hsum
  have hMdim : Module.finrank K M ≤ 7 := by omega
  have hZMeq : (Z.restrict hZM) ^ 2 + Z.restrict hZM + 1 = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx : (Z ^ 2 + Z + 1 : Module.End K (quasithinZorn K)) x = 0 := LinearMap.mem_ker.mp x.2
    rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add,
      restrict_pow_apply, LinearMap.restrict_apply, Module.End.one_apply, LinearMap.zero_apply,
      Submodule.coe_zero]
    rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply] at hx
    exact hx
  have hNMZ : Commute (N.restrict hMinv) (Z.restrict hZM) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.restrict_apply,
      LinearMap.restrict_apply, LinearMap.restrict_apply, LinearMap.restrict_apply]
    show N (Z x) = Z (N x)
    exact congrArg (fun φ : Module.End K (quasithinZorn K) => φ x) hNZ.eq
  have hM3 : (N.restrict hMinv) ^ 3 = 0 :=
    pow_three_eq_zero_of_commute hirr (Z.restrict hZM) hZMeq hMdim _ hNMZ
      ⟨2 ^ k, LinearMap.ext fun x => Subtype.ext (by rw [restrict_pow_apply, hNk]; rfl)⟩
  have hN4 : N ^ 4 = 0 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨b, hb, m, hm, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top :
      v ∈ B ⊔ M)
    have e1 : (N ^ 4) b = 0 := by
      have := restrict_pow_apply N hBinv 4 ⟨b, hb⟩
      rw [hB4] at this
      exact this.symm
    have e2 : (N ^ 4) m = 0 := by
      have h0 : (N ^ 3) m = 0 := by
        rw [← restrict_pow_apply N hMinv 3 ⟨m, hm⟩, hM3]
        rfl
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ', Module.End.mul_apply, h0, map_zero]
    rw [map_add, e1, e2, add_zero, LinearMap.zero_apply]
  have hY4 : Y ^ 4 = 1 := by
    have e := sub_pow_char_pow_of_commute (p := 2) (n := 2) (h := Commute.one_right Y)
    rw [one_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hNdef, hN4] at e
    exact (sub_eq_zero.mp e.symm)
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  rw [Subgroup.coe_pow]
  show ((y ^ 4 : quasithinZorn K ≃ₗ[K] quasithinZorn K) : Module.End K (quasithinZorn K)) = 1
  rw [coe_end_pow]
  exact hY4

theorem g2ThreeCentTwoExp_holds :
    G2ThreeCentTwoExp :=
  g2ThreeCentTwoExp_of_quasithin quasithinThreeCentTwoExp_holds

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
