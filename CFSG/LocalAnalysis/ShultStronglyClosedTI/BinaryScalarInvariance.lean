module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.RankThree.Classical2.CentralLiftCommutator

public section

namespace CFSG.ShultStronglyClosedTI

open scoped commutatorElement
open CFSG.RankThree.Classical2

universe u v

theorem exists_scalar_quadratic_ne_zero (K : Type u) [Field K] [Finite K]
    (hcard : 4 < Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ a ^ 2 + a + 1 ≠ 0 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let p : Polynomial K := Polynomial.X ^ 2 + Polynomial.X + 1
  have hp : p ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun q : Polynomial K => q.coeff 2) h
    norm_num [p, Polynomial.coeff_X, Polynomial.coeff_one] at hcoeff
  have hdegree : p.natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le <;> simp
    · simp
  let bad : Finset K := insert 0 (insert 1 p.roots.toFinset)
  have hbad : bad.card ≤ 4 := by
    have hroot := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
    have h1 := Finset.card_insert_le (1 : K) p.roots.toFinset
    have h0 := Finset.card_insert_le (0 : K) (insert 1 p.roots.toFinset)
    dsimp only [bad]
    omega
  have hlt : bad.card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact lt_of_le_of_lt hbad hcard
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have ha0 : a ≠ 0 := by
    intro h
    exact ha (by simp [bad, h])
  have ha1 : a ≠ 1 := by
    intro h
    exact ha (by simp [bad, h])
  refine ⟨a, ha0, ha1, ?_⟩
  intro h
  have hroot : a ∈ p.roots := (Polynomial.mem_roots hp).mpr (by
    simpa [p, Polynomial.IsRoot] using h)
  exact ha (by simp [bad, hroot])

theorem binaryScalarInvariantBiadditive_eq_zero
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {A : Type v} [AddCommGroup A] (hcard : 4 < Nat.card K)
    (b : K → K → A)
    (hleft : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hright : ∀ x y y', b x (y + y') = b x y + b x y')
    (hinvariant : ∀ a : K, a ≠ 0 → ∀ x y, b (a * x) (a * y) = b x y) :
    ∀ x y, b x y = 0 := by
  have hzero (y : K) : b 0 y = 0 := by
    have h := hleft 0 0 y
    simpa using h
  have htwo (x y : K) : b x y + b x y = 0 := by
    rw [← hleft, CharTwo.add_self_eq_zero, hzero]
  obtain ⟨a, ha0, ha1, hquad⟩ := exists_scalar_quadratic_ne_zero K hcard
  have hap : a + 1 ≠ 0 := by
    intro h
    exact ha1 (CharTwo.add_eq_zero.mp h)
  have hmove (x y : K) : b (a * x) y = b x (a⁻¹ * y) := by
    have h := hinvariant a ha0 x (a⁻¹ * y)
    simpa only [← mul_assoc, mul_inv_cancel₀ ha0, one_mul] using h
  have hcross (x y : K) : b x y = b (a * x) y + b x (a * y) := by
    calc
      b x y = b ((a + 1) * x) ((a + 1) * y) := (hinvariant (a + 1) hap x y).symm
      _ = (b (a * x) (a * y) + b (a * x) y) +
          (b x (a * y) + b x y) := by
        rw [add_mul, add_mul, one_mul, one_mul, hleft, hright, hright]
      _ = b (a * x) y + b x (a * y) := by
        rw [hinvariant a ha0]
        calc
          (b x y + b (a * x) y) + (b x (a * y) + b x y) =
              (b x y + b x y) + (b (a * x) y + b x (a * y)) := by abel
          _ = b (a * x) y + b x (a * y) := by rw [htwo, zero_add]
  let c : K := a + a⁻¹ + 1
  have hc : c ≠ 0 := by
    intro h
    have heq : a * c = a ^ 2 + a + 1 := by
      dsimp only [c]
      rw [mul_add, mul_add, mul_inv_cancel₀ ha0]
      ring
    exact hquad (heq.symm.trans (by rw [h, mul_zero]))
  have hkill (x y : K) : b x (c * y) = 0 := by
    have heq : b x ((a + a⁻¹) * y) = b x y := by
      rw [add_mul, hright, ← hmove]
      exact (add_comm _ _).trans (hcross x y).symm
    dsimp only [c]
    rw [add_mul, one_mul, hright, heq, htwo]
  intro x y
  have h := hkill x (c⁻¹ * y)
  simpa only [← mul_assoc, mul_inv_cancel₀ hc, one_mul] using h

theorem binaryScalarInvariantAddHom_eq_zero
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {A : Type v} [AddCommGroup A] (hcard : 4 < Nat.card K)
    (b : K →+ K →+ A)
    (hinvariant : ∀ a : Kˣ, ∀ x y, b ((a : K) * x) ((a : K) * y) = b x y) :
    ∀ x y, b x y = 0 := by
  apply binaryScalarInvariantBiadditive_eq_zero hcard (fun x y => b x y)
  · intro x x' y
    exact DFunLike.congr_fun (map_add b x x') y
  · intro x y y'
    exact map_add (b x) y y'
  · intro a ha x y
    exact hinvariant (Units.mk0 a ha) x y

theorem isMulCommutative_of_central_kernel_scalar
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {H : Type v} [Group H]
    (hcard : 4 < Nat.card K)
    (eta : H →* Multiplicative K)
    (heta : Function.Surjective eta)
    (hcentral : eta.ker ≤ Subgroup.center H)
    (sigma : MulAut H) {mu : K}
    (hmu : ∀ w : K, w ≠ 0 → ∃ m : ℕ, mu ^ m = w)
    (hscalar : ∀ x : H,
      Multiplicative.toAdd (eta (sigma x)) =
        mu * Multiplicative.toAdd (eta x))
    (hfix : ∀ a ∈ eta.ker, sigma a = a) :
    IsMulCommutative H := by
  classical
  let : IsMulCommutative eta.ker :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral a.2) b.1).symm)
  let : CommGroup eta.ker := IsMulCommutative.instCommGroup
  let b : K → K → Additive eta.ker := fun x y =>
    Additive.ofMul
      ⟨liftComm eta heta (Multiplicative.ofAdd x) (Multiplicative.ofAdd y),
        liftComm_mem_ker heta (Commute.all _ _)⟩
  have hleft : ∀ x x' y, b (x + x') y = b x y + b x' y := by
    intro x x' y
    apply Additive.toMul.injective
    simp only [b, toMul_add, toMul_ofMul]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [ofAdd_add, liftComm_mul_left heta hcentral (Commute.all _ _)]
  have hright : ∀ x y y', b x (y + y') = b x y + b x y' := by
    intro x y y'
    apply Additive.toMul.injective
    simp only [b, toMul_add, toMul_ofMul]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [ofAdd_add, liftComm_mul_right heta hcentral (Commute.all _ _)]
  have hmu_inv : ∀ x y : K, b (mu * x) (mu * y) = b x y := by
    intro x y
    let p : H := Function.surjInv heta (Multiplicative.ofAdd x)
    let q : H := Function.surjInv heta (Multiplicative.ofAdd y)
    have hp : eta p = Multiplicative.ofAdd x := Function.surjInv_eq heta _
    have hq : eta q = Multiplicative.ofAdd y := Function.surjInv_eq heta _
    have hsp : eta (sigma p) = Multiplicative.ofAdd (mu * x) := by
      apply Multiplicative.toAdd.injective
      rw [hscalar p, hp, toAdd_ofAdd, toAdd_ofAdd]
    have hsq : eta (sigma q) = Multiplicative.ofAdd (mu * y) := by
      apply Multiplicative.toAdd.injective
      rw [hscalar q, hq, toAdd_ofAdd, toAdd_ofAdd]
    have hmem : ⁅p, q⁆ ∈ eta.ker :=
      commutatorElement_mem_ker eta (by rw [hp, hq]; exact Commute.all _ _)
    apply Additive.toMul.injective
    simp only [b, toMul_ofMul]
    apply Subtype.ext
    calc
      liftComm eta heta (Multiplicative.ofAdd (mu * x))
          (Multiplicative.ofAdd (mu * y)) = ⁅sigma p, sigma q⁆ :=
        liftComm_eq heta hcentral hsp hsq
      _ = sigma ⁅p, q⁆ := (map_commutatorElement sigma p q).symm
      _ = ⁅p, q⁆ := hfix _ hmem
      _ = liftComm eta heta (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) :=
        (liftComm_eq heta hcentral hp hq).symm
  have hpow : ∀ m : ℕ, ∀ x y : K, b ((mu ^ m) * x) ((mu ^ m) * y) = b x y := by
    intro m
    induction m with
    | zero => intro x y; simp
    | succ m ih =>
        intro x y
        rw [pow_succ', mul_assoc, mul_assoc, hmu_inv (mu ^ m * x) (mu ^ m * y), ih]
  have hinvariant : ∀ a : K, a ≠ 0 → ∀ x y : K, b (a * x) (a * y) = b x y := by
    intro a ha x y
    obtain ⟨m, hm⟩ := hmu a ha
    rw [← hm]
    exact hpow m x y
  have hzero :=
    binaryScalarInvariantBiadditive_eq_zero hcard b hleft hright hinvariant
  refine IsMulCommutative.of_comm fun x y => ?_
  have hcomm : ⁅x, y⁆ = 1 := by
    have hlift : liftComm eta heta
        (Multiplicative.ofAdd (Multiplicative.toAdd (eta x)))
        (Multiplicative.ofAdd (Multiplicative.toAdd (eta y))) = 1 := by
      have h := hzero (Multiplicative.toAdd (eta x)) (Multiplicative.toAdd (eta y))
      dsimp only [b] at h
      rw [ofMul_eq_zero] at h
      simpa using congrArg Subtype.val h
    calc
      ⁅x, y⁆ = liftComm eta heta (eta x) (eta y) :=
        commutatorElement_eq_liftComm heta hcentral x y
      _ = liftComm eta heta
            (Multiplicative.ofAdd (Multiplicative.toAdd (eta x)))
            (Multiplicative.ofAdd (Multiplicative.toAdd (eta y))) := by
        rw [ofAdd_toAdd, ofAdd_toAdd]
      _ = 1 := hlift
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

theorem isElementaryAbelian_two_of_central_kernel_scalar
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {H : Type v} [Group H]
    (hcard : 4 < Nat.card K)
    (eta : H →* Multiplicative K)
    (heta : Function.Surjective eta)
    (hcentral : eta.ker ≤ Subgroup.center H)
    (hker_two : ∀ a ∈ eta.ker, a ^ 2 = 1)
    (sigma : MulAut H) {mu : K}
    (hmu : ∀ w : K, w ≠ 0 → ∃ m : ℕ, mu ^ m = w)
    (hscalar : ∀ x : H,
      Multiplicative.toAdd (eta (sigma x)) =
        mu * Multiplicative.toAdd (eta x))
    (hfix : ∀ a ∈ eta.ker, sigma a = a) :
    CFSG.IsElementaryAbelian 2 H := by
  classical
  have hcomm : IsMulCommutative H :=
    isMulCommutative_of_central_kernel_scalar hcard eta heta hcentral sigma hmu hscalar hfix
  let : CommGroup H := IsMulCommutative.instCommGroup
  have hsq_ker : ∀ x : H, x ^ 2 ∈ eta.ker := by
    intro x
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [map_pow, toAdd_pow, toAdd_one]
    exact CharTwo.two_nsmul _
  let delta : H → H := fun x => sigma x * x⁻¹
  have hmu_ne_one : mu ≠ 1 := by
    obtain ⟨w, hw0, hw1, -⟩ := exists_scalar_quadratic_ne_zero K hcard
    obtain ⟨m, hm⟩ := hmu w hw0
    intro h
    exact hw1 (by rw [h, one_pow] at hm; exact hm.symm)
  have hdelta_sq : ∀ x : H, delta x ^ 2 = 1 := by
    intro x
    have hfix2 : sigma (x ^ 2) = x ^ 2 := hfix _ (hsq_ker x)
    calc
      delta x ^ 2 = sigma (x ^ 2) * (x ^ 2)⁻¹ := by
        dsimp only [delta]
        rw [mul_pow, ← map_pow, inv_pow]
      _ = x ^ 2 * (x ^ 2)⁻¹ := by rw [hfix2]
      _ = 1 := mul_inv_cancel _
  have hdelta_map : ∀ x : H,
      Multiplicative.toAdd (eta (delta x)) =
        (mu - 1) * Multiplicative.toAdd (eta x) := by
    intro x
    dsimp only [delta]
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hscalar x]
    ring
  have hsub : mu - 1 ≠ 0 := sub_ne_zero.mpr hmu_ne_one
  have hsurj : ∀ w : K, ∃ y : K, (mu - 1) * y = w := by
    intro w
    exact ⟨(mu - 1)⁻¹ * w, by rw [← mul_assoc, mul_inv_cancel₀ hsub, one_mul]⟩
  have hexists : ∀ h : H, ∃ x : H, eta (delta x) = eta h := by
    intro h
    obtain ⟨y, hy⟩ := hsurj (Multiplicative.toAdd (eta h))
    obtain ⟨x, hx⟩ := heta (Multiplicative.ofAdd y)
    refine ⟨x, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hdelta_map x, hx, toAdd_ofAdd, hy]
  have hsq_one : ∀ h : H, h ^ 2 = 1 := by
    intro h
    obtain ⟨x, hx⟩ := hexists h
    let k : H := (delta x)⁻¹ * h
    have hk_ker : k ∈ eta.ker := by
      rw [MonoidHom.mem_ker]
      dsimp only [k]
      rw [map_mul, map_inv, hx, inv_mul_cancel]
    have hk2 : k ^ 2 = 1 := hker_two k hk_ker
    have hh : delta x * k = h := by
      dsimp only [k]
      group
    calc
      h ^ 2 = (delta x * k) ^ 2 := by rw [hh]
      _ = delta x ^ 2 * k ^ 2 := by rw [mul_pow]
      _ = 1 := by rw [hdelta_sq x, hk2, one_mul]
  exact
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq_one }

end CFSG.ShultStronglyClosedTI
