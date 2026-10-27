module

public import CFSG.RankThree.PartOne.S11d.RankTwoBlocks
public import CFSG.RankThree.PartOne.S11d.PSLRankTwo

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Subgroup CFSG
open CFSG.RankThree.PartOne.LIT

section Transport

@[expose] def linConjAut {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (Φ : V ≃ₗ[k] W) : (V ≃ₗ[k] V) ≃* (W ≃ₗ[k] W) where
  toFun g := Φ.symm.trans (g.trans Φ)
  invFun h := Φ.trans (h.trans Φ.symm)
  left_inv g := LinearEquiv.ext fun v => by simp
  right_inv h := LinearEquiv.ext fun w => by simp
  map_mul' g h := LinearEquiv.ext fun w => by simp

end Transport

section SLTransport

variable {n : ℕ} {k : Type} [Field k]

abbrev linSL (n : ℕ) (k : Type) [Field k] :
    Matrix.SpecialLinearGroup (Fin n) k →* ((Fin n → k) ≃ₗ[k] (Fin n → k)) :=
  Matrix.SpecialLinearGroup.toLin'

theorem linSL_injective : Function.Injective (linSL n k) :=
  Matrix.SpecialLinearGroup.toLin'_injective

theorem exists_sl_of_det_one {g : (Fin n → k) ≃ₗ[k] (Fin n → k)} (hg : LinearEquiv.det g = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) k, linSL n k A = g := by
  refine ⟨⟨LinearMap.toMatrix' (g : (Fin n → k) →ₗ[k] (Fin n → k)), ?_⟩, ?_⟩
  · rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det, hg]
    rfl
  · apply LinearEquiv.ext
    intro v
    show Matrix.toLin' (LinearMap.toMatrix' (g : (Fin n → k) →ₗ[k] (Fin n → k))) v = g v
    rw [Matrix.toLin'_toMatrix']
    rfl

theorem exists_sl_rank_two {p : ℕ} (R U : Subgroup ((Fin n → k) ≃ₗ[k] (Fin n → k)))
    (hRe : CFSG.IsElementaryAbelian p R) (hRc : Nat.card R = p ^ 2)
    (hRd : ∀ g ∈ R, LinearEquiv.det g = 1) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUd : ∀ g ∈ U, LinearEquiv.det g = 1)
    (hN : R ≤ Subgroup.normalizer (U : Set ((Fin n → k) ≃ₗ[k] (Fin n → k)))) :
    ∃ R' U' : Subgroup (Matrix.SpecialLinearGroup (Fin n) k), CFSG.IsElementaryAbelian p R' ∧
      Nat.card R' = p ^ 2 ∧ U' ≠ ⊥ ∧ IsPGroup 2 U' ∧
      R' ≤ Subgroup.normalizer (U' : Set (Matrix.SpecialLinearGroup (Fin n) k)) := by
  classical
  have hinj := linSL_injective (n := n) (k := k)
  have hRrange : R ≤ (linSL n k).range := fun g hg => exists_sl_of_det_one (hRd g hg)
  refine ⟨R.comap (linSL n k), U.comap (linSL n k), ?_, ?_, ?_, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro a b
      apply Subtype.ext
      apply hinj
      have h := congrArg Subtype.val (hRe.is_comm.comm ⟨linSL n k a, a.2⟩ ⟨linSL n k b, b.2⟩)
      simpa using h
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      apply Subtype.ext
      apply hinj
      have h : (⟨linSL n k a, a.2⟩ : R) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p R) _
      have := congrArg Subtype.val h
      simpa using this
  · have h1 : (R.comap (linSL n k)).map (linSL n k) = R := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hRrange
    calc Nat.card (R.comap (linSL n k))
        = Nat.card ((R.comap (linSL n k)).map (linSL n k)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card R := by rw [h1]
      _ = p ^ 2 := hRc
  · intro hbot
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    obtain ⟨A, hA⟩ := exists_sl_of_det_one (hUd u u.2)
    have hAmem : A ∈ U.comap (linSL n k) := by
      rw [Subgroup.mem_comap, hA]
      exact u.2
    rw [hbot, Subgroup.mem_bot] at hAmem
    apply hu1
    apply Subtype.ext
    rw [← hA, hAmem, map_one]
    rfl
  · intro a
    obtain ⟨j, hj⟩ := hU2 ⟨linSL n k a, a.2⟩
    refine ⟨j, Subtype.ext (hinj ?_)⟩
    have := congrArg Subtype.val hj
    simpa using this
  · intro A hA
    rw [Subgroup.mem_normalizer_iff]
    intro B
    have hAN := hN hA
    rw [Subgroup.mem_normalizer_iff] at hAN
    have := hAN (linSL n k B)
    simpa [Subgroup.mem_comap] using this

end SLTransport

section Quotient

theorem rankTwoCfg_map {G H : Type*} [Group G] [Group H] (f : G →* H) {p : ℕ}
    (R U : Subgroup G) (hRinj : ∀ x ∈ R, ∀ y ∈ R, f x = f y → x = y)
    (hUinj : ∀ x ∈ U, f x = 1 → x = 1) (hRe : CFSG.IsElementaryAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hN : R ≤ Subgroup.normalizer (U : Set G)) :
    CFSG.IsElementaryAbelian p (R.map f) ∧ Nat.card (R.map f) = p ^ 2 ∧ U.map f ≠ ⊥ ∧
      IsPGroup 2 (U.map f) ∧ R.map f ≤ Subgroup.normalizer (U.map f : Set H) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro a b
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      show (a : H) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hRe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
      apply Subtype.ext
      show (a : H) ^ p = 1
      rw [← hxa, ← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
  · have hbij : Function.Bijective
        (fun x : R => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : R.map f)) := by
      refine ⟨fun x y hxy => ?_, fun y => ?_⟩
      · apply Subtype.ext
        exact hRinj x x.2 y y.2 (congrArg Subtype.val hxy)
      · obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    rw [← hRc]
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  · intro hbot
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    have hmem : f u ∈ U.map f := Subgroup.mem_map_of_mem f u.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hu1 (Subtype.ext (hUinj u u.2 hmem))
  · intro a
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨j, hj⟩ := hU2 ⟨x, hx⟩
    refine ⟨j, Subtype.ext ?_⟩
    show (a : H) ^ (2 ^ j) = 1
    rw [← hxa, ← map_pow]
    have : x ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    rw [this, map_one]
  · have key : ∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U := fun r hr u hu =>
      (Subgroup.mem_normalizer_iff.mp (hN hr) u).mp hu
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨r * u * r⁻¹, key r hr u hu, by simp⟩
    · rintro ⟨u, hu, hua⟩
      refine ⟨r⁻¹ * u * r, key r⁻¹ (R.inv_mem hr) u hu |> fun h => by simpa using h, ?_⟩
      have : f (r⁻¹ * u * r) = (f r)⁻¹ * (f r * a * (f r)⁻¹) * f r := by
        rw [map_mul, map_mul, map_inv, hua]
      rw [this]
      group

theorem exists_quotient_rank_two {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    {p : ℕ} (hp : p.Prime) (hZp : ¬ p ∣ Nat.card Z) (hZ2 : ¬ 2 ∣ Nat.card Z) (R U : Subgroup G)
    (hRe : CFSG.IsElementaryAbelian p R) (hRc : Nat.card R = p ^ 2) (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hN : R ≤ Subgroup.normalizer (U : Set G)) :
    ∃ R' U' : Subgroup (G ⧸ Z), CFSG.IsElementaryAbelian p R' ∧ Nat.card R' = p ^ 2 ∧
      U' ≠ ⊥ ∧ IsPGroup 2 U' ∧ R' ≤ Subgroup.normalizer (U' : Set (G ⧸ Z)) := by
  classical
  let π : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hker : ∀ {ℓ : ℕ}, ℓ.Prime → ¬ ℓ ∣ Nat.card Z → ∀ z : G, z ∈ Z →
      (∃ j : ℕ, z ^ (ℓ ^ j) = 1) → z = 1 := by
    intro ℓ hℓ hZℓ z hzZ ⟨j, hj⟩
    have h1 : orderOf (⟨z, hzZ⟩ : Z) ∣ ℓ ^ j := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using hj)
    have h2 : orderOf (⟨z, hzZ⟩ : Z) ∣ Nat.card Z := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (ℓ ^ j) (Nat.card Z) :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hZℓ)
    have h3 : orderOf (⟨z, hzZ⟩ : Z) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have := orderOf_eq_one_iff.mp h3
    exact congrArg Subtype.val this
  have hRinj : ∀ x ∈ R, ∀ y ∈ R, π x = π y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hxy
    have hRz : x⁻¹ * y ∈ R := R.mul_mem (R.inv_mem hx) hy
    have hpow : (x⁻¹ * y) ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian _ hRz
    have h1 := hker hp hZp _ hz ⟨1, by simpa using hpow⟩
    exact inv_mul_eq_one.mp h1
  have hUinj : ∀ x ∈ U, π x = 1 → x = 1 := by
    intro x hx hπx
    have hz : x ∈ Z := (QuotientGroup.eq_one_iff x).mp hπx
    obtain ⟨j, hj⟩ := hU2 ⟨x, hx⟩
    exact hker Nat.prime_two hZ2 x hz ⟨j, by simpa using congrArg Subtype.val hj⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := rankTwoCfg_map π R U hRinj hUinj hRe hRc hU1 hU2 hN
  exact ⟨R.map π, U.map π, h1, h2, h3, h4, h5⟩

end Quotient

section Final

@[expose] noncomputable def splitEquiv (n e : ℕ) (k : Type) [Field k] (h : e ≤ n) :
    (Fin n → k) ≃ₗ[k] (Fin e → k) × (Fin (n - e) → k) :=
  (LinearEquiv.funCongrLeft k k (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h)))).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin e) (Fin (n - e)) k k)

theorem det_linConjAut {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] (Φ : V ≃ₗ[k] W) (g : V ≃ₗ[k] V) :
    LinearEquiv.det (linConjAut Φ g) = LinearEquiv.det g := by
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
  have : ((linConjAut Φ g : W ≃ₗ[k] W) : W →ₗ[k] W) =
      (Φ : V →ₗ[k] W) ∘ₗ (g : V →ₗ[k] V) ∘ₗ (Φ.symm : W →ₗ[k] V) := rfl
  rw [this]
  exact LinearMap.det_conj (g : V →ₗ[k] V) Φ

variable {n : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]

theorem exists_rank_two_unip_psl [NeZero n] {p e : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card kˣ) (he1 : 1 ≤ e) (hdvd : p ∣ Nat.card k ^ e - 1) (hn : 2 * e ≤ n) :
    ∃ R U : Subgroup (projectiveSL n k), CFSG.IsElementaryAbelian p R ∧ Nat.card R = p ^ 2 ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ R ≤ Subgroup.normalizer (U : Set (projectiveSL n k)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hen : e ≤ n := by omega
  have hrk : ¬ p ∣ Fintype.card k - 1 := by
    rwa [Nat.card_units, Nat.card_eq_fintype_card] at hpK
  have hdvd' : p ∣ Fintype.card k ^ e - 1 := by rwa [Nat.card_eq_fintype_card] at hdvd
  have : NeZero e := ⟨by omega⟩
  have hnA : Nontrivial (Fin e → k) := inferInstance
  have hB : e ≤ n - e := by omega
  have : NeZero (n - e) := ⟨by omega⟩
  obtain ⟨R₁, hR₁e, hR₁c, hR₁d, hR₁N⟩ := exists_rank_two_block (k := k) (A := Fin e → k)
    (B := Fin (n - e) → k) hp hrk he1 hdvd' (by rw [Module.finrank_fin_fun]) (by
      rw [Module.finrank_fin_fun]; exact hB)
  let Φ := splitEquiv n e k hen
  let θ : (((Fin e → k) × (Fin (n - e) → k)) ≃ₗ[k] ((Fin e → k) × (Fin (n - e) → k))) ≃*
      ((Fin n → k) ≃ₗ[k] (Fin n → k)) := (linConjAut Φ).symm
  have hθdet : ∀ g, LinearEquiv.det (θ g) = LinearEquiv.det g := by
    intro g
    have := det_linConjAut Φ (θ g)
    rw [show linConjAut Φ (θ g) = g from (linConjAut Φ).apply_symm_apply g] at this
    exact this.symm
  have hU1 := unip_ne_bot (k := k) (A := Fin e → k) (B := Fin (n - e) → k)
  have hU2 := isPGroup_unip (k := k) (A := Fin e → k) (B := Fin (n - e) → k)
  obtain ⟨a1, a2, a3, a4, a5⟩ := rankTwoCfg_map θ.toMonoidHom R₁
    (unip k (Fin e → k) (Fin (n - e) → k)) (fun x _ y _ h => θ.injective h)
    (fun x _ h => θ.injective (by simpa using h)) hR₁e hR₁c hU1 hU2 hR₁N
  have hRd : ∀ g ∈ R₁.map θ.toMonoidHom, LinearEquiv.det g = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show LinearEquiv.det (θ x) = 1
    rw [hθdet]
    exact hR₁d x hx
  have hUd : ∀ g ∈ (unip k (Fin e → k) (Fin (n - e) → k)).map θ.toMonoidHom,
      LinearEquiv.det g = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show LinearEquiv.det (θ x) = 1
    rw [hθdet]
    exact det_unip hx
  obtain ⟨R₃, U₃, b1, b2, b3, b4, b5⟩ := exists_sl_rank_two _ _ a1 a2 hRd a3 a4 hUd a5
  have hZp : ¬ p ∣ Nat.card (scalars n k) := not_dvd_card_scalars_psl hp hpK
  have hZ2 : ¬ 2 ∣ Nat.card (scalars n k) := by
    refine not_dvd_card_scalars_psl Nat.prime_two ?_
    obtain ⟨f, -, hcard⟩ := FiniteField.card k 2
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    intro h2
    have hf : 2 ∣ Fintype.card k := by
      rw [hcard]
      exact dvd_pow_self 2 (PNat.ne_zero f)
    have hpos : 0 < Fintype.card k := Fintype.card_pos
    have h3 := Nat.dvd_sub hf h2
    have h4 : Fintype.card k - (Fintype.card k - 1) = 1 := by omega
    rw [h4] at h3
    omega
  exact exists_quotient_rank_two (scalars n k) hp hZp hZ2 R₃ U₃ b1 b2 b3 b4 b5

end Final

end CFSG.RankThree.PartOne
