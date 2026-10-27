module

public import CFSG.Quasithin.Background.SmithD310UMat
public import CFSG.Quasithin.EmptyFaithful.SmithD391Q
public import CFSG.Quasithin.EmptyFaithful.SmithD391Count

public section

namespace CFSG.Quasithin.SmithD310U

open Matrix Module

section Transvection

variable {K : Type*} [Field K]

@[expose] def tv (i j : Fin 3) (hij : i ≠ j) (c : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem tv_mulVec (i j : Fin 3) (hij : i ≠ j) (c : K) (v : Fin 3 → K) :
    ((tv i j hij c : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      v + Pi.single i (c * v j) := by
  show transvection i j c *ᵥ v = _
  rw [transvection, add_mulVec, one_mulVec, single_mulVec]
  rfl

theorem tv_inv (i j : Fin 3) (hij : i ≠ j) (c : K) : (tv i j hij c)⁻¹ = tv i j hij (-c) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  show transvection i j c * transvection i j (-c) = 1
  rw [transvection_mul_transvection_same i j hij, add_neg_cancel]
  exact transvection_zero i j

theorem tv_inv_transpose_mulVec (i j : Fin 3) (hij : i ≠ j) (c : K) (v : Fin 3 → K) :
    (((tv i j hij c)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ v =
      v - Pi.single j (c * v i) := by
  rw [tv_inv]
  show (transvection i j (-c))ᵀ *ᵥ v = _
  rw [transvection, transpose_add, transpose_one, transpose_single, add_mulVec, one_mulVec,
    single_mulVec, neg_mul, sub_eq_add_neg, ← Pi.single_neg]
  rfl

private theorem map_single_of_comm (f : (Fin 3 → K) →+ (Fin 3 → K))
    (hf : ∀ (i j : Fin 3), i ≠ j → ∀ (c : K) (v : Fin 3 → K),
      f (v + Pi.single i (c * v j)) = f v + Pi.single i (c * f v j))
    (i j : Fin 3) (hij : i ≠ j) (c : K) :
    f (Pi.single i c) = Pi.single i (c * f (Pi.single j 1) j) := by
  have h := hf i j hij c (Pi.single j 1)
  rw [map_add, Pi.single_eq_same, mul_one, add_right_inj] at h
  exact h

theorem exists_smul_of_comm (f : (Fin 3 → K) →+ (Fin 3 → K))
    (hf : ∀ (i j : Fin 3), i ≠ j → ∀ (c : K) (v : Fin 3 → K),
      f (v + Pi.single i (c * v j)) = f v + Pi.single i (c * f v j)) :
    ∃ l : K, ∀ v, f v = l • v := by
  set l : Fin 3 → K := fun j => f (Pi.single j 1) j with hl
  have key := map_single_of_comm f hf
  have e01 : l 0 = l 1 := by
    have h1 := key 2 0 (by decide) 1
    have h2 := key 2 1 (by decide) 1
    rw [h1] at h2
    simpa using congrFun h2 2
  have e12 : l 1 = l 2 := by
    have h1 := key 0 1 (by decide) 1
    have h2 := key 0 2 (by decide) 1
    rw [h1] at h2
    simpa using congrFun h2 0
  have hs : ∀ (i : Fin 3) (c : K), f (Pi.single i c) = l 0 • Pi.single i c := by
    intro i c
    obtain ⟨j, hj, hlj⟩ : ∃ j : Fin 3, j ≠ i ∧ l j = l 0 := by
      fin_cases i
      · exact ⟨1, by decide, e01.symm⟩
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨0, by decide, rfl⟩
    rw [key i j (Ne.symm hj) c]
    show Pi.single i (c * l j) = l 0 • Pi.single i c
    rw [hlj, ← Pi.single_smul, smul_eq_mul, mul_comm]
  refine ⟨l 0, fun v => ?_⟩
  calc f v = f (∑ i, Pi.single i (v i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, f (Pi.single i (v i)) := map_sum _ _ _
    _ = ∑ i, l 0 • Pi.single i (v i) := Finset.sum_congr rfl fun i _ => hs i (v i)
    _ = l 0 • ∑ i, Pi.single i (v i) := Finset.smul_sum.symm
    _ = l 0 • v := by rw [Finset.univ_sum_single]

theorem eq_zero_of_graph (h : (Fin 3 → K) →+ (Fin 3 → K))
    (hh : ∀ (i j : Fin 3), i ≠ j → ∀ (c : K) (v : Fin 3 → K),
      h (v + Pi.single i (c * v j)) = h v - Pi.single j (c * h v i)) :
    h = 0 := by
  have key : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      h (Pi.single i c) = - Pi.single j (c * h (Pi.single j 1) i) := by
    intro i j hij c
    have e := hh i j hij c (Pi.single j 1)
    rw [map_add, Pi.single_eq_same, mul_one, sub_eq_add_neg, add_right_inj] at e
    exact e
  have hs : ∀ (i : Fin 3) (c : K), h (Pi.single i c) = 0 := by
    intro i c
    obtain ⟨j₁, j₂, h1, h2, h12⟩ : ∃ j₁ j₂ : Fin 3, j₁ ≠ i ∧ j₂ ≠ i ∧ j₁ ≠ j₂ := by
      fin_cases i
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    have e1 := key i j₁ h1.symm c
    have e2 := key i j₂ h2.symm c
    have ej : c * h (Pi.single j₁ 1) i = 0 := by
      have := congrFun (e1.symm.trans e2) j₁
      simpa [Pi.single_eq_of_ne h12] using this
    rw [e1, ej, Pi.single_zero, neg_zero]
  refine AddMonoidHom.ext fun v => ?_
  calc h v = h (∑ i, Pi.single i (v i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, h (Pi.single i (v i)) := map_sum _ _ _
    _ = 0 := Finset.sum_eq_zero fun i _ => hs i (v i)

end Transvection

section OddDegree

variable {K : Type*} [Field K] [Finite K]

theorem charP_two_of_card {m : ℕ} (hK : Nat.card K = 2 ^ m) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [Fintype.card_eq_nat_card, hK] at hn
  have h1 : ringChar K ∣ 2 ^ m := by rw [hn]; exact dvd_pow_self _ n.ne_zero
  have h3 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  exact ringChar.of_eq h3

theorem two_eq_zero_of_card {m : ℕ} (hK : Nat.card K = 2 ^ m) : (2 : K) = 0 := by
  have := charP_two_of_card hK
  exact CharTwo.two_eq_zero

theorem ringEquiv_apply_eq_of_sq {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) (σ : K ≃+* K)
    (hσ : ∀ x, σ (σ x) = x) (x : K) : σ x = x := by
  have := charP_two_of_card hK
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcomm : ∀ r : ZMod 2, σ (algebraMap (ZMod 2) K r) = algebraMap (ZMod 2) K r := fun r =>
    congrArg (fun f : ZMod 2 →+* K => f r)
      (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))
  let σ' : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv hcomm
  have hcard : Nat.card (K ≃ₐ[ZMod 2] K) = m := by
    rw [IsGalois.card_aut_eq_finrank]
    have h := FiniteField.pow_finrank_eq_natCard 2 K
    rw [hK] at h
    exact Nat.pow_right_injective le_rfl h
  have h2 : σ' ^ 2 = 1 := by
    ext y
    simp [σ', pow_two, hσ]
  have hdvd : orderOf σ' ∣ Nat.gcd 2 m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (hcard ▸ orderOf_dvd_natCard σ')
  rw [Nat.coprime_two_left.mpr hm, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  have := congrArg (fun f : K ≃ₐ[ZMod 2] K => f x) hdvd
  simpa [σ'] using this

theorem eq_one_of_pow_three {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) {r : K}
    (hr : r ^ 3 = 1) : r = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at hr
  have h1 := FiniteField.pow_card_sub_one_eq_one r hr0
  rw [Fintype.card_eq_nat_card, hK] at h1
  have hg : Nat.gcd 3 (2 ^ m - 1) = 1 := by
    obtain ⟨j, rfl⟩ := hm
    have h4 : 2 ^ (2 * j + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h5 : (2 ^ (2 * j + 1) - 1) % 3 = 1 := by
      have : 1 ≤ 2 ^ (2 * j + 1) := Nat.one_le_two_pow
      omega
    rw [Nat.gcd_rec, h5, Nat.gcd_one_left]
  have := pow_gcd_eq_one.mpr ⟨hr, h1⟩
  rwa [hg, pow_one] at this

theorem eq_one_of_mem_center {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m)
    {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) : g = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [Fintype.card_fin] at hr
  rw [eq_one_of_pow_three hK hm hr] at hrg
  apply Subtype.ext
  rw [← hrg]
  simp

end OddDegree

section Natural

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.F918X CFSG.RankThree.PartOne.AUTSL

variable {K : Type} [Field K]

@[expose] def semiMap (B : Matrix (Fin 3) (Fin 3) K) (τ : K ≃+* K) :
    (Fin 3 → K) →+ (Fin 3 → K) where
  toFun v i := τ ((B *ᵥ v) i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [mulVec_add]

theorem semiMap_apply (B : Matrix (Fin 3) (Fin 3) K) (τ : K ≃+* K) (v : Fin 3 → K) :
    semiMap B τ v = fun i => τ ((B *ᵥ v) i) := rfl

theorem symm_mulVec_map (σ : K ≃+* K) (N : Matrix (Fin 3) (Fin 3) K) (w : Fin 3 → K) :
    (fun i => σ.symm ((N.map σ *ᵥ w) i)) = N *ᵥ fun i => σ.symm (w i) := by
  funext i
  simp only [mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, RingEquiv.symm_apply_apply]

theorem inv_mul_mulVec (A : GL (Fin 3) K) (w : Fin 3 → K) :
    ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
      w := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mul_inv_mulVec (A : GL (Fin 3) K) (w : Fin 3 → K) :
    (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
      w := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem inv_conj_mulVec (A : GL (Fin 3) K) (N : Matrix (Fin 3) (Fin 3) K) (w : Fin 3 → K) :
    ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((A : Matrix (Fin 3) (Fin 3) K) * N * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
          *ᵥ w) =
      N *ᵥ (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, inv_mul_mulVec]

theorem conj_mulVec_eq_iff (A : GL (Fin 3) K) (σ : K ≃+* K) (N : Matrix (Fin 3) (Fin 3) K)
    (w : Fin 3 → K) :
    ((A : Matrix (Fin 3) (Fin 3) K) * N.map σ * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        *ᵥ w = w ↔
      N *ᵥ semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm w =
        semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm w := by
  rw [semiMap_apply, ← symm_mulVec_map]
  constructor
  · intro h
    funext i
    rw [← inv_conj_mulVec A (N.map σ) w, h]
  · intro h
    have h1 : N.map σ *ᵥ (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w := by
      funext i
      exact σ.symm.injective (congrFun h i)
    rw [← mulVec_mulVec, ← mulVec_mulVec, h1, mul_inv_mulVec]

theorem semiMap_mulVec_map (A : GL (Fin 3) K) (σ : K ≃+* K) (w : Fin 3 → K) :
    semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm
      ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ fun i => σ (w i)) = w := by
  rw [semiMap_apply, inv_mul_mulVec]
  funext i
  exact σ.symm_apply_apply (w i)

theorem mulVec_map_semiMap (A : GL (Fin 3) K) (σ : K ≃+* K) (v : Fin 3 → K) :
    ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ fun i =>
      σ (semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm v i)) = v := by
  simp only [semiMap_apply, RingEquiv.apply_symm_apply]
  exact mul_inv_mulVec A v

variable {U : Type*} [CommGroup U] {H : Subgroup (MulAut U)} {π : ↥(StatedSL 3 K) →* ↥H}

theorem exists_coord (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π) :
    ∃ E : U ≃* Multiplicative (Fin 3 → K), ∀ (γ : ↥(StatedSL 3 K)) (u : U),
      Multiplicative.toAdd (E (((π γ : ↥H) : MulAut U) u)) =
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (E u) := by
  set D := FFModel.nat (StatedSL 3 K) with hD
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  let q : (↥D.sec ⧸ D.ker.subgroupOf D.sec) →* D.Amb :=
    QuotientGroup.lift _ D.sec.subtype (by
      intro m hm
      rw [Subgroup.mem_subgroupOf] at hm
      exact Subgroup.mem_bot.mp hm)
  have hq : ∀ m : ↥D.sec, q (QuotientGroup.mk m) = (m : D.Amb) := fun m => rfl
  let e0 : U →* D.Amb :=
    q.comp (β.comp Subgroup.topEquiv.symm.toMonoidHom)
  have he0 : ∀ u, e0 u = q (β ⟨u, trivial⟩) := fun u => rfl
  have hinj : Function.Injective e0 := by
    rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, trivial⟩)
    rw [he0, ← hm, hq] at hu
    have h1 : β ⟨u, trivial⟩ = 1 := by
      rw [← hm, show m = 1 from Subtype.ext hu]
      rfl
    exact Subgroup.mem_bot.mp ((hβk ⟨u, trivial⟩).mp h1)
  have hsurj : Function.Surjective e0 := by
    intro y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, trivial⟩)
    refine ⟨u, ?_⟩
    rw [he0, show (⟨(u : U), trivial⟩ : ↥(⊤ : Subgroup U)) = u from rfl, hu]
    rfl
  refine ⟨MulEquiv.ofBijective e0 ⟨hinj, hsurj⟩, fun γ u => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, trivial⟩)
  have h1 : β ⟨((π γ : ↥H) : MulAut U) u, trivial⟩ =
      QuotientGroup.mk ⟨D.act γ (m : D.Amb), trivial⟩ :=
    hβe γ ⟨u, trivial⟩ m trivial trivial hm.symm
  show Multiplicative.toAdd (e0 _) = _ *ᵥ Multiplicative.toAdd (e0 u)
  rw [he0, he0, h1, ← hm, hq, hq]
  rfl

theorem bijective_of_realizesVia (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π) :
    Function.Bijective π :=
  ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩

@[expose] def coordMap (E : U ≃* Multiplicative (Fin 3 → K)) (φ : MulAut U) :
    (Fin 3 → K) →+ (Fin 3 → K) where
  toFun v := Multiplicative.toAdd (E (φ (E.symm (Multiplicative.ofAdd v))))
  map_zero' := by simp
  map_add' x y := by
    rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]

theorem coordMap_apply (E : U ≃* Multiplicative (Fin 3 → K)) (φ : MulAut U) (u : U) :
    coordMap E φ (Multiplicative.toAdd (E u)) = Multiplicative.toAdd (E (φ u)) := by
  simp [coordMap]

theorem coordMap_injective (E : U ≃* Multiplicative (Fin 3 → K)) (φ : MulAut U) :
    Function.Injective (coordMap E φ) := by
  intro v w h
  simpa [coordMap] using h

variable [Finite K]

omit [Finite K] in
theorem eq_one_of_mul_self (h2 : (2 : K) = 0) {x : K} (hx : x * x = 1) : x = 1 := by
  have h : (x - 1) * (x - 1) = 0 := by linear_combination hx + (1 - x) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h)

@[expose] noncomputable def slEquiv (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π) :
    SpecialLinearGroup (Fin 3) K ≃* ↥H :=
  (specialLinearGroupEquivStatedSL 3 K).trans
    (MulEquiv.ofBijective π (bijective_of_realizesVia hπ))

omit [Finite K] in
theorem slEquiv_apply (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π)
    (g : SpecialLinearGroup (Fin 3) K) :
    slEquiv hπ g = π (specialLinearGroupEquivStatedSL 3 K g) := rfl

theorem mem_of_sq_eq_one {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m)
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π) {φ : MulAut U}
    (hφH : ∀ h ∈ H, φ * h * φ⁻¹ ∈ H) (hφ2 : φ * φ = 1) : φ ∈ H := by
  classical
  obtain ⟨E, hE⟩ := exists_coord hπ
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hK
  have hφi : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφ2
  have hφφ : ∀ x, φ (φ x) = x := fun x => by
    simpa using congrArg (fun F : MulAut U => F x) hφ2
  have hφn : φ ∈ Subgroup.normalizer (H : Set (MulAut U)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hφH x hx, fun hx => ?_⟩
    have := hφH _ hx
    rwa [hφi, ← mul_assoc, ← mul_assoc, hφ2, one_mul, mul_assoc, hφ2, mul_one] at this
  set ψ := slEquiv hπ with hψdef
  let c : MulAut ↥H := H.normalizerMonoidHom ⟨φ, hφn⟩
  let β : MulAut (SpecialLinearGroup (Fin 3) K) := MulAut.congr ψ.symm c
  have hβ : ∀ g, ((ψ (β g) : ↥H) : MulAut U) = φ * (ψ g : MulAut U) * φ⁻¹ := by
    intro g
    show ((ψ (ψ.symm (c (ψ.symm.symm g))) : ↥H) : MulAut U) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hψE : ∀ (g : SpecialLinearGroup (Fin 3) K) (u : U),
      Multiplicative.toAdd (E (((ψ g : ↥H) : MulAut U) u)) =
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (E u) := by
    intro g u
    rw [hψdef, slEquiv_apply, hE]
    rfl
  set f := coordMap E φ with hf
  have hsurjE : ∀ v : Fin 3 → K, ∃ u, Multiplicative.toAdd (E u) = v :=
    fun v => ⟨E.symm (Multiplicative.ofAdd v), by simp⟩
  have hfg : ∀ (g : SpecialLinearGroup (Fin 3) K) (v : Fin 3 → K),
      f ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = (β g : Matrix (Fin 3) (Fin 3) K) *ᵥ f v := by
    intro g v
    obtain ⟨u, rfl⟩ := hsurjE v
    have e2 : φ (((ψ g : ↥H) : MulAut U) u) = ((ψ (β g) : ↥H) : MulAut U) (φ u) := by
      rw [hβ]
      simp only [MulAut.mul_apply, hφi, hφφ]
    rw [← hψE, hf, coordMap_apply, coordMap_apply, e2, hψE]
  have hff : ∀ v, f (f v) = v := by
    intro v
    obtain ⟨u, rfl⟩ := hsurjE v
    rw [hf, coordMap_apply, coordMap_apply, hφφ]
  have hf0 : f (Pi.single 0 1) ≠ 0 := by
    intro h0
    have := coordMap_injective E φ (h0.trans (map_zero f).symm)
    have h1 := congrFun this 0
    simp at h1
  obtain ⟨A, σ, hA | hA⟩ := exists_matrix_form_of_mulAut_sl (by norm_num : 3 ≤ 3) β
  ·
    set h' := (semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm).comp f with hh'
    have hcomm : ∀ (i j : Fin 3), i ≠ j → ∀ (c : K) (v : Fin 3 → K),
        h' (v + Pi.single i (c * v j)) = h' v + Pi.single i (c * h' v j) := by
      intro i j hij c v
      rw [← tv_mulVec i j hij c (h' v), ← tv_mulVec i j hij c v]
      simp only [hh', AddMonoidHom.comp_apply, semiMap_apply]
      rw [hfg, hA, inv_conj_mulVec, symm_mulVec_map]
    obtain ⟨l, hl⟩ := exists_smul_of_comm h' hcomm
    set μ := σ l with hμ
    have hfv : ∀ v, f v = μ • ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ fun i => σ (v i)) := by
      intro v
      have e1 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f v =
          μ • fun i => σ (v i) := by
        funext i
        have := congrFun (hl v) i
        simp only [hh', AddMonoidHom.comp_apply, semiMap_apply, Pi.smul_apply,
          smul_eq_mul] at this
        rw [Pi.smul_apply, smul_eq_mul, hμ, ← map_mul, ← this, RingEquiv.apply_symm_apply]
      rw [← mul_inv_mulVec A (f v), e1, mulVec_smul]
    have hlin : ∀ (c : K) (v : Fin 3 → K), f (c • v) = σ c • f v := by
      intro c v
      have e : (fun i => σ ((c • v) i)) = σ c • fun i => σ (v i) := by
        funext i
        simp [map_mul]
      rw [hfv, hfv, e, mulVec_smul, smul_comm]
    have hσ2 : ∀ x, σ (σ x) = x := by
      intro x
      have e := hff (x • Pi.single 0 1)
      rw [hlin, hlin, hff] at e
      have := congrFun e 0
      simpa using this
    have hσ1 := ringEquiv_apply_eq_of_sq hK hm σ hσ2
    set X : Matrix (Fin 3) (Fin 3) K := μ • (A : Matrix (Fin 3) (Fin 3) K) with hX
    have hfX : ∀ v, f v = X *ᵥ v := by
      intro v
      rw [hfv, hX, smul_mulVec]
      congr 2
      funext i
      exact hσ1 (v i)
    have hXX : X * X = 1 := by
      refine ext_of_mulVec_single fun i => ?_
      rw [← mulVec_mulVec, ← hfX, ← hfX, hff, one_mulVec]
    have hdet : X.det = 1 := by
      have := congrArg Matrix.det hXX
      rw [det_mul, det_one] at this
      exact eq_one_of_mul_self h2 this
    let g₀ : SpecialLinearGroup (Fin 3) K := ⟨X, hdet⟩
    have hφg : φ = ((ψ g₀ : ↥H) : MulAut U) := by
      refine MulEquiv.ext fun u => E.injective (Multiplicative.toAdd.injective ?_)
      rw [hψE, ← coordMap_apply, ← hf, hfX]
    rw [hφg]
    exact (ψ g₀).2
  ·
    exfalso
    set h' := (semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm).comp f with hh'
    have hgr : ∀ (i j : Fin 3), i ≠ j → ∀ (c : K) (v : Fin 3 → K),
        h' (v + Pi.single i (c * v j)) = h' v - Pi.single j (c * h' v i) := by
      intro i j hij c v
      rw [← tv_inv_transpose_mulVec i j hij c (h' v), ← tv_mulVec i j hij c v]
      simp only [hh', AddMonoidHom.comp_apply, semiMap_apply]
      rw [hfg, hA, inv_conj_mulVec, symm_mulVec_map]
    have h0 := eq_zero_of_graph h' hgr
    apply hf0
    have e1 := DFunLike.congr_fun h0 (Pi.single 0 1)
    rw [AddMonoidHom.zero_apply] at e1
    have e2 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f (Pi.single 0 1) = 0 := by
      funext i
      have := congrFun e1 i
      simp only [hh', AddMonoidHom.comp_apply, semiMap_apply, Pi.zero_apply,
        map_eq_zero_iff _ σ.symm.injective] at this
      exact this
    rw [← mul_inv_mulVec A (f (Pi.single 0 1)), e2, mulVec_zero]

omit [Finite K] in
theorem coe_symm_apply (γ : ↥(StatedSL 3 K)) :
    (((specialLinearGroupEquivStatedSL 3 K).symm γ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have := specialLinearGroupEquivStatedSL_coe 3 K ((specialLinearGroupEquivStatedSL 3 K).symm γ)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem eq_one_of_forall_comm {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m)
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π) {x : ↥H}
    (hx : ∀ y : ↥H, x * y = y * x) : x = 1 := by
  set ψ := slEquiv hπ
  obtain ⟨g, rfl⟩ := ψ.surjective x
  have hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply ψ.injective
    rw [map_mul, map_mul, hx (ψ y)]
  rw [eq_one_of_mem_center hK hm hg, map_one]

theorem exists_graph_form (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π)
    {θ : MulAut ↥H} (hθ : θ ∉ realized H) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), ∀ γ γ' : ↥(StatedSL 3 K), θ (π γ) = π γ' →
      ((γ' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) *
          (((γ⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ.map σ *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  set s := specialLinearGroupEquivStatedSL 3 K with hs
  set ψ := slEquiv hπ with hψdef
  let β : MulAut (SpecialLinearGroup (Fin 3) K) := MulAut.congr ψ.symm θ
  have hβ : ∀ γ : ↥(StatedSL 3 K), π (s (β (s.symm γ))) = θ (π γ) := by
    intro γ
    have h1 : ψ (β (s.symm γ)) = θ (ψ (s.symm γ)) := by
      show ψ (ψ.symm (θ (ψ.symm.symm (s.symm γ)))) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    rwa [hψdef, slEquiv_apply, slEquiv_apply, MulEquiv.apply_symm_apply] at h1
  have hinj := (bijective_of_realizesVia hπ).1
  obtain ⟨A, σ, hA | hA⟩ := exists_matrix_form_of_mulAut_sl (by norm_num : 3 ≤ 3) β
  · exfalso
    apply hθ
    refine mem_realized_of_semilinear hπ θ (MulAut.congr s β) (fun γ => (hβ γ).symm) A σ ?_
    intro γ
    show (((s (β (s.symm γ)) : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [specialLinearGroupEquivStatedSL_coe, hA, coe_symm_apply]
  · refine ⟨A, σ, fun γ γ' h => ?_⟩
    have h1 : γ' = s (β (s.symm γ)) := hinj (by rw [← h, hβ])
    rw [h1, specialLinearGroupEquivStatedSL_coe, hA, ← map_inv, coe_symm_apply]

end Natural

section Module

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.F918X CFSG.Quasithin.SmithD391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]
  {Λ : Subgroup Γ} {Vt : Subgroup Q}

theorem smul_mem_of_stab (b : ↥(MulAction.stabilizer Γ Vt)) {v : Q} (hv : v ∈ Vt) :
    b • v ∈ Vt := by
  have hb : (b : Γ) • Vt = Vt := b.2
  have h1 : (b : Γ) • v ∈ (b : Γ) • Vt := Subgroup.smul_mem_pointwise_smul v (b : Γ) Vt hv
  rw [hb] at h1
  exact h1

@[expose] noncomputable def stabAct (Vt : Subgroup Q) :
    ↥(MulAction.stabilizer Γ Vt) →* MulAut ↥Vt :=
  actAut (MulAction.stabilizer Γ Vt) Vt fun b _ hv => smul_mem_of_stab b hv

theorem stabAct_apply (b : ↥(MulAction.stabilizer Γ Vt)) (v : ↥Vt) :
    ((stabAct Vt b v : ↥Vt) : Q) = (b : Γ) • (v : Q) := rfl

theorem stabAct_inv_apply (b : ↥(MulAction.stabilizer Γ Vt)) (v : ↥Vt) :
    (((stabAct Vt b)⁻¹ v : ↥Vt) : Q) = (b : Γ)⁻¹ • (v : Q) := by
  rw [← map_inv, stabAct_apply]
  rfl

variable (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hVt : ∀ l : ↥Λ, ∀ v ∈ Vt, l • v ∈ Vt)

include hΛ in
theorem stabAct_conj (b : ↥(MulAction.stabilizer Γ Vt)) (l : ↥Λ) :
    stabAct Vt b * actAut Λ Vt hVt l * (stabAct Vt b)⁻¹ =
      actAut Λ Vt hVt ⟨(b : Γ) * l * (b : Γ)⁻¹, hΛ b l l.2⟩ := by
  refine MulEquiv.ext fun v => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, stabAct_apply, actAut_apply, stabAct_inv_apply,
    actAut_apply, smul_smul, smul_smul]

variable (hinj : Function.Injective (actAut Λ Vt hVt))

include hΛ hinj in
theorem comm_of_stabAct_eq_one {b : ↥(MulAction.stabilizer Γ Vt)} (hb : stabAct Vt b = 1)
    {l : Γ} (hl : l ∈ Λ) : l * b = b * l := by
  have h := stabAct_conj hΛ hVt b ⟨l, hl⟩
  rw [hb, one_mul, inv_one, mul_one] at h
  have h2 : (⟨l, hl⟩ : ↥Λ) = ⟨(b : Γ) * l * (b : Γ)⁻¹, hΛ b l hl⟩ := hinj h
  have h3 : l = (b : Γ) * l * (b : Γ)⁻¹ := congrArg Subtype.val h2
  calc l * b = (b : Γ) * l * (b : Γ)⁻¹ * b := by rw [← h3]
    _ = b * l := by group

variable {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m)
  {π : ↥(StatedSL 3 K) →* ↥(actAut Λ Vt hVt).range}
  (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia (actAut Λ Vt hVt).range ⊤ ⊥ π)

include hΛ hK hm hπ in
theorem stabAct_mem {b : ↥(MulAction.stabilizer Γ Vt)} (hb : (b : Γ) * b = 1) :
    stabAct Vt b ∈ (actAut Λ Vt hVt).range := by
  refine mem_of_sq_eq_one hK hm hπ ?_ ?_
  · rintro _ ⟨l, rfl⟩
    rw [stabAct_conj hΛ hVt b l]
    exact ⟨_, rfl⟩
  · rw [← map_mul, show b * b = 1 from Subtype.ext hb, map_one]

include hK hm hπ in
theorem stabAct_twist {g : Γ} {b b' : ↥(MulAction.stabilizer Γ Vt)}
    (hb' : (b' : Γ) = g⁻¹ * b * g) (h1 : stabAct Vt b ∈ (actAut Λ Vt hVt).range)
    (h2 : stabAct Vt b' ∈ (actAut Λ Vt hVt).range) :
    (⟨stabAct Vt b', h2⟩ : ↥(actAut Λ Vt hVt).range) =
      twistAut hΛ hVt hinj g⁻¹ ⟨stabAct Vt b, h1⟩ := by
  set θ := twistAut hΛ hVt hinj g⁻¹ with hθ
  set x : ↥(actAut Λ Vt hVt).range := ⟨stabAct Vt b', h2⟩ with hx
  set y : ↥(actAut Λ Vt hVt).range := ⟨stabAct Vt b, h1⟩ with hy
  have key : ∀ l : ↥Λ, x * actEquiv hVt hinj l * x⁻¹ =
      θ y * actEquiv hVt hinj l * (θ y)⁻¹ := by
    intro l
    have e1 : actEquiv hVt hinj l = θ (actEquiv hVt hinj ⟨g * l * g⁻¹, hΛ g l l.2⟩) := by
      apply Subtype.ext
      rw [hθ, twistAut_actEquiv, actEquiv_apply]
      congr 1
      apply Subtype.ext
      show (l : Γ) = g⁻¹ * (g * l * g⁻¹) * g⁻¹⁻¹
      group
    have e2 : y * actEquiv hVt hinj ⟨g * l * g⁻¹, hΛ g l l.2⟩ * y⁻¹ =
        actEquiv hVt hinj ⟨(b : Γ) * (g * l * g⁻¹) * (b : Γ)⁻¹, hΛ b _ (hΛ g l l.2)⟩ :=
      Subtype.ext (stabAct_conj hΛ hVt b ⟨g * l * g⁻¹, hΛ g l l.2⟩)
    have eR : θ y * actEquiv hVt hinj l * (θ y)⁻¹ = actEquiv hVt hinj
        ⟨g⁻¹ * ((b : Γ) * (g * l * g⁻¹) * (b : Γ)⁻¹) * g⁻¹⁻¹,
          hΛ g⁻¹ _ (hΛ b _ (hΛ g l l.2))⟩ := by
      conv_lhs => rw [e1]
      rw [← map_mul, ← map_inv, ← map_mul, e2]
      apply Subtype.ext
      rw [hθ, twistAut_actEquiv, actEquiv_apply]
    have eL : x * actEquiv hVt hinj l * x⁻¹ =
        actEquiv hVt hinj ⟨(b' : Γ) * l * (b' : Γ)⁻¹, hΛ b' l l.2⟩ :=
      Subtype.ext (stabAct_conj hΛ hVt b' l)
    rw [eL, eR]
    congr 1
    apply Subtype.ext
    show (b' : Γ) * l * (b' : Γ)⁻¹ = g⁻¹ * ((b : Γ) * (g * l * g⁻¹) * (b : Γ)⁻¹) * g⁻¹⁻¹
    rw [hb']
    group
  have hc : ∀ z : ↥(actAut Λ Vt hVt).range, x⁻¹ * θ y * z = z * (x⁻¹ * θ y) := by
    intro z
    obtain ⟨l, rfl⟩ := (actEquiv hVt hinj).surjective z
    calc x⁻¹ * θ y * actEquiv hVt hinj l =
        x⁻¹ * (θ y * actEquiv hVt hinj l * (θ y)⁻¹) * θ y := by group
      _ = x⁻¹ * (x * actEquiv hVt hinj l * x⁻¹) * θ y := by rw [← key]
      _ = actEquiv hVt hinj l * (x⁻¹ * θ y) := by group
  exact inv_mul_eq_one.mp (eq_one_of_forall_comm hK hm hπ hc)

include hΛ hinj hK hm hπ in
theorem exists_matrices_abs [Finite Γ] {g : Γ} (hg : ¬ XMod.Iso ↥Λ Vt (g • Vt))
    {P : Subgroup Γ} (hPV : ∀ a ∈ P, a • Vt = Vt) (hPg : ∀ a ∈ P, (g⁻¹ * a * g) • Vt = Vt)
    (hP2 : ∀ a ∈ P, a * a = 1) :
    ∃ S : Set (Matrix (Fin 3) (Fin 3) K), (∀ x ∈ S, x * x = 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
      Nat.card ↥P ≤ Nat.card ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ)) * Nat.card S ∧
      Nat.card ↥(Vt ⊓ XMod.fixed ↥P ⊤) = Nat.card (fixVec S) ∧
      Nat.card ↥(g • Vt ⊓ XMod.fixed ↥P ⊤) = Nat.card (fixVecT S) ∧
      (¬ P ≤ Subgroup.centralizer (Λ : Set Γ) → ∃ x ∈ S, x ≠ 1) := by
  classical
  have hPN : P ≤ MulAction.stabilizer Γ Vt := fun a ha => hPV a ha
  have hmem : ∀ a : ↥P, stabAct Vt (Subgroup.inclusion hPN a) ∈ (actAut Λ Vt hVt).range := fun a =>
    stabAct_mem hΛ hVt hK hm hπ (hP2 a a.2)
  set e : ↥(StatedSL 3 K) ≃* ↥(actAut Λ Vt hVt).range :=
    MulEquiv.ofBijective π (bijective_of_realizesVia hπ) with he
  let χ : ↥P →* ↥(StatedSL 3 K) :=
    e.symm.toMonoidHom.comp (((stabAct Vt).comp (Subgroup.inclusion hPN)).codRestrict _ hmem)
  have hχ : ∀ a : ↥P, π (χ a) = ⟨stabAct Vt (Subgroup.inclusion hPN a), hmem a⟩ := by
    intro a
    show e (e.symm _) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hχv : ∀ (a : ↥P) (u : ↥Vt),
      ((((π (χ a) : ↥(actAut Λ Vt hVt).range) : MulAut ↥Vt) u : ↥Vt) : Q) = (a : Γ) • (u : Q) := by
    intro a u
    rw [hχ]
    rfl
  let mat : ↥(StatedSL 3 K) → Matrix (Fin 3) (Fin 3) K :=
    fun γ => ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hmat_inj : Function.Injective mat := fun γ γ' h => Subtype.ext (Units.ext h)
  have hmat_mul : ∀ γ γ', mat (γ * γ') = mat γ * mat γ' := fun _ _ => rfl
  have hmat_one : mat 1 = 1 := rfl
  set S := Set.range (fun a : ↥P => mat (χ a)) with hS
  have hPi : ∀ a : ↥P, a⁻¹ = a := fun a =>
    inv_eq_of_mul_eq_one_right (Subtype.ext (hP2 a a.2))
  have hPc : ∀ a b : ↥P, a * b = b * a := by
    intro a b
    have hab := hPi (a * b)
    rw [_root_.mul_inv_rev, hPi, hPi] at hab
    exact hab.symm
  have hker : ∀ a : ↥P, χ a = 1 → (a : Γ) ∈ Subgroup.centralizer (Λ : Set Γ) := by
    intro a ha
    have h1 : stabAct Vt (Subgroup.inclusion hPN a) = 1 := by
      have := hχ a
      rw [ha, map_one] at this
      exact (congrArg Subtype.val this).symm
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact comm_of_stabAct_eq_one hΛ hVt hinj h1 hl
  obtain ⟨E, hE⟩ := exists_coord hπ
  have hfixU : ∀ u : ↥Vt, (∀ a : ↥P, (a : Γ) • (u : Q) = u) ↔
      Multiplicative.toAdd (E u) ∈ fixVec S := by
    intro u
    rw [mem_fixVec]
    constructor
    · rintro h _ ⟨a, rfl⟩
      show mat (χ a) *ᵥ _ = _
      rw [← hE]
      congr 2
      apply Subtype.ext
      rw [hχv]
      exact h a
    · intro h a
      have h1 := h (mat (χ a)) ⟨a, rfl⟩
      rw [← hE] at h1
      have h2 := E.injective (Multiplicative.toAdd.injective h1)
      rw [← hχv a u, h2]
  have hcardV : Nat.card ↥(Vt ⊓ XMod.fixed ↥P ⊤) = Nat.card (fixVec S) := by
    refine Nat.card_congr
      { toFun := fun q => ⟨Multiplicative.toAdd (E ⟨q, q.2.1⟩),
          (hfixU _).1 fun a => (XMod.mem_fixed.1 q.2.2).2 a⟩
        invFun := fun w => ⟨(E.symm (Multiplicative.ofAdd w) : Q),
          (E.symm (Multiplicative.ofAdd w)).2,
          XMod.mem_fixed.2 ⟨trivial, fun a => (hfixU _).2 (by simp) a⟩⟩
        left_inv := fun q => by ext; simp
        right_inv := fun w => by ext; simp }
  refine ⟨S, ?_, ?_, ?_, hcardV, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    show mat (χ a) * mat (χ a) = 1
    rw [← hmat_mul, ← map_mul, show a * a = 1 from Subtype.ext (hP2 a a.2), map_one, hmat_one]
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    show mat (χ a) * mat (χ b) = mat (χ b) * mat (χ a)
    rw [← hmat_mul, ← hmat_mul, ← map_mul, ← map_mul, hPc]
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv] at h1
    have h2 : Nat.card ↥χ.ker ≤ Nat.card ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ)) := by
      refine Nat.card_le_card_of_injective
        (fun k => ⟨((k : ↥P) : Γ), (k : ↥P).2, hker k k.2⟩) ?_
      intro k k' h
      have h' : ((k : ↥P) : Γ) = ((k' : ↥P) : Γ) :=
        congrArg (fun x : ↥(P ⊓ Subgroup.centralizer (Λ : Set Γ)) => (x : Γ)) h
      exact Subtype.ext (Subtype.ext h')
    have h3 : Nat.card ↥χ.range = Nat.card S := by
      have : S = mat '' (χ.range : Set ↥(StatedSL 3 K)) := by
        rw [hS, MonoidHom.coe_range, ← Set.range_comp]
        rfl
      rw [this, Nat.card_image_of_injective hmat_inj]
      rfl
    rw [h1, h3, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  ·
    have hθ : twistAut hΛ hVt hinj g⁻¹ ∉ realized (actAut Λ Vt hVt).range := fun h =>
      hg (iso_of_twistAut_mem hΛ hVt hinj g h)
    obtain ⟨A, σ, hAσ⟩ := exists_graph_form hπ hθ
    let b' : ↥P → ↥(MulAction.stabilizer Γ Vt) := fun a => ⟨g⁻¹ * a * g, hPg a a.2⟩
    have hb'2 : ∀ a : ↥P, ((b' a : ↥(MulAction.stabilizer Γ Vt)) : Γ) * (b' a) = 1 := by
      intro a
      show g⁻¹ * a * g * (g⁻¹ * a * g) = 1
      calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * ((a : Γ) * a) * g := by group
        _ = 1 := by rw [hP2 a a.2]; group
    have hmem' : ∀ a : ↥P, stabAct Vt (b' a) ∈ (actAut Λ Vt hVt).range := fun a =>
      stabAct_mem hΛ hVt hK hm hπ (hb'2 a)
    have hmat' : ∀ a : ↥P, ∃ γ' : ↥(StatedSL 3 K),
        ((π γ' : ↥(actAut Λ Vt hVt).range) : MulAut ↥Vt) = stabAct Vt (b' a) ∧
          mat γ' = (A : Matrix (Fin 3) (Fin 3) K) * (mat (χ a))ᵀ.map σ *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro a
      obtain ⟨γ', hγ'⟩ := (bijective_of_realizesVia hπ).2 ⟨stabAct Vt (b' a), hmem' a⟩
      refine ⟨γ', by rw [hγ'], ?_⟩
      have htw : (⟨stabAct Vt (b' a), hmem' a⟩ : ↥(actAut Λ Vt hVt).range) =
          twistAut hΛ hVt hinj g⁻¹ (π (χ a)) := by
        rw [hχ]
        exact stabAct_twist hΛ hVt hinj hK hm hπ (b := Subgroup.inclusion hPN a) (b' := b' a)
          rfl (hmem a) (hmem' a)
      have h1 := hAσ (χ a) γ' (by rw [hγ', htw])
      rw [← map_inv, hPi] at h1
      exact h1
    have hfixT : ∀ u : ↥Vt, (∀ a : ↥P, (a : Γ) • g • (u : Q) = g • (u : Q)) ↔
        semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm
          (Multiplicative.toAdd (E u)) ∈ fixVecT S := by
      intro u
      have step : ∀ a : ↥P, ((a : Γ) • g • (u : Q) = g • (u : Q)) ↔
          (mat (χ a))ᵀ *ᵥ semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm
              (Multiplicative.toAdd (E u)) =
            semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm
              (Multiplicative.toAdd (E u)) := by
        intro a
        obtain ⟨γ', hγ'1, hγ'2⟩ := hmat' a
        rw [← conj_mulVec_eq_iff, ← hγ'2]
        show _ ↔ ((γ' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
        rw [← hE, hγ'1]
        have hconj : (a : Γ) • g • (u : Q) = g • ((g⁻¹ * a * g) • (u : Q)) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
        constructor
        · intro h
          congr 2
          apply Subtype.ext
          rw [stabAct_apply]
          show (g⁻¹ * a * g) • (u : Q) = u
          rw [mul_smul, mul_smul, h, inv_smul_smul]
        · intro h
          have h2 : stabAct Vt (b' a) u = u := E.injective (Multiplicative.toAdd.injective h)
          have h3 : (g⁻¹ * a * g) • (u : Q) = u := by
            have := congrArg Subtype.val h2
            rwa [stabAct_apply] at this
          rw [hconj, h3]
      rw [mem_fixVecT]
      constructor
      · rintro h _ ⟨a, rfl⟩
        exact (step a).1 (h a)
      · intro h a
        exact (step a).2 (h _ ⟨a, rfl⟩)
    refine Nat.card_congr
      { toFun := fun q => ⟨semiMap ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ.symm
            (Multiplicative.toAdd (E ⟨g⁻¹ • (q : Q),
              Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp q.2.1⟩)),
          (hfixT _).1 fun a => by
            show (a : Γ) • g • g⁻¹ • (q : Q) = g • g⁻¹ • (q : Q)
            rw [smul_inv_smul]
            exact (XMod.mem_fixed.1 q.2.2).2 a⟩
        invFun := fun w => ⟨g • (E.symm (Multiplicative.ofAdd
            ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ fun i => σ ((w : Fin 3 → K) i))) : Q),
          Subgroup.smul_mem_pointwise_smul _ g Vt (E.symm _).2,
          XMod.mem_fixed.2 ⟨trivial, (hfixT _).2 (by
            rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, semiMap_mulVec_map]
            exact w.2)⟩⟩
        left_inv := fun q => by
          apply Subtype.ext
          simp only [mulVec_map_semiMap, ofAdd_toAdd, MulEquiv.symm_apply_apply, smul_inv_smul]
        right_inv := fun w => by
          apply Subtype.ext
          simp only [inv_smul_smul, Subtype.coe_eta, MulEquiv.apply_symm_apply, toAdd_ofAdd,
            semiMap_mulVec_map] }
  · intro hP
    obtain ⟨a, ha, hac⟩ := IsConcreteLE.not_le_iff_exists.mp hP
    refine ⟨mat (χ ⟨a, ha⟩), ⟨⟨a, ha⟩, rfl⟩, fun h1 => hac ?_⟩
    exact hker ⟨a, ha⟩ (hmat_inj (h1.trans hmat_one.symm))

end Module

section Concrete

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.F918X CFSG.Quasithin.SmithD391
  CFSG.Quasithin.Z391
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem exists_matrices (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g)
    {n : ℕ} (hn : Odd n) (hα : BinaryNaturalSL L V (V ⊓ fixV L) 3 n)
    {t : MulAut W} (htT : t ∈ T) (htM : t ∈ M) (htn : t ∉ stabSub V)
    {A : Subgroup (MulAut W)} (hAM : A ≤ M) (hAV : A ≤ stabSub V)
    (hAt : ∀ a ∈ A, t⁻¹ * a * t ∈ stabSub V) (hA2 : ∀ a ∈ A, a * a = 1) :
    letI := qAct hD.hyp.Mp_normal
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (S : Set (Matrix (Fin 3) (Fin 3) K)),
      Nat.card K = 2 ^ n ∧ Nat.card ↥(tilde L ⊤ V) = Nat.card K ^ 3 ∧
      (∀ x ∈ S, x * x = 1) ∧ (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
      Nat.card ↥A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) * Nat.card S ∧
      Nat.card ↥(tilde L ⊤ V ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤) = Nat.card (fixVec S) ∧
      Nat.card ↥((⟨t, htM⟩ : ↥M) • tilde L ⊤ V ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤) =
        Nat.card (fixVecT S) ∧
      (¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) → ∃ x ∈ S, x ≠ 1) := by
  let _i := qAct hD.hyp.Mp_normal
  have h5 : D35Five L V := Or.inl ⟨n, hα⟩
  have hirr := isIrr_tildeQ hD
  obtain ⟨hinj, -⟩ := injective_twoClass_tildeQ hD h5
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  obtain ⟨K, _, _, hK, π₀, hR⟩ := hα
  let ψ : ↥L →* ↥(L.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom
  have hψ : Function.Surjective ψ := (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
  let f : ↥V →* ↥(tilde L ⊤ V) :=
    (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))).subgroupMap V
  have hf : Function.Surjective f :=
    (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))).subgroupMap_surjective V
  have hfker : ∀ u : ↥V, f u = 1 ↔ (u : W) ∈ V ⊓ fixV L := by
    intro u
    constructor
    · intro h1
      have h2 : (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq] at h2
      exact ⟨u.2, h2⟩
    · intro h1
      apply Subtype.ext
      show (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq]
      exact h1.2
  have hR' := realizesVia_actAut hirr.1 hR ψ hψ f hf hfker (fun h u hu => rfl)
  have hnot := not_iso_tildeQ hD hlt hC htT htM htn
  have hnot' : ¬ XMod.Iso ↥(L.subgroupOf M) (tilde L ⊤ V) ((⟨t, htM⟩ : ↥M) • tilde L ⊤ V) :=
    fun h => hnot (XMod.Iso.symm hirr.1 h)
  have hstab : ∀ b : ↥M, (b : MulAut W) ∈ stabSub V → b • tilde L ⊤ V = tilde L ⊤ V := by
    intro b hb
    rw [smul_tildeQ hD.hyp.Mp_normal b V]
    have h1 : (b : MulAut W) • V = V := mem_stabSub_iff_map_eq.1 hb
    rw [h1]
  have hPV : ∀ a ∈ A.subgroupOf M, a • tilde L ⊤ V = tilde L ⊤ V := fun a ha =>
    hstab a (hAV ha)
  have hPg : ∀ a ∈ A.subgroupOf M,
      ((⟨t, htM⟩ : ↥M)⁻¹ * a * ⟨t, htM⟩) • tilde L ⊤ V = tilde L ⊤ V := fun a ha =>
    hstab _ (hAt a ha)
  have hP2 : ∀ a ∈ A.subgroupOf M, a * a = 1 := fun a ha => Subtype.ext (hA2 a ha)
  obtain ⟨S, h1, h2, h3, h4, h6, h7⟩ :=
    exists_matrices_abs (d391_Λ_normal hD) hirr.1 hinj hK hn hR' hnot' hPV hPg hP2
  obtain ⟨E, -⟩ := exists_coord hR'
  refine ⟨K, inferInstance, inferInstance, S, hK, ?_, h1, h2, ?_, h4, h6, ?_⟩
  · rw [Nat.card_congr E.toEquiv]
    show Nat.card (Fin 3 → K) = _
    rw [Nat.card_fun, Nat.card_fin]
  · have e1 : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
    have e2 : Nat.card ↥(A.subgroupOf M ⊓ Subgroup.centralizer ((L.subgroupOf M) : Set ↥M)) ≤
        Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) := by
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥M) : MulAut W), x.2.1, ?_⟩) ?_
      · show ((x : ↥M) : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W))
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have := Subgroup.mem_centralizer_iff.1 x.2.2 ⟨l, hLM hl⟩ hl
        exact congrArg Subtype.val this
      · intro x y hxy
        have h' : ((x : ↥M) : MulAut W) = ((y : ↥M) : MulAut W) :=
          congrArg (fun z : ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) => (z : MulAut W))
            hxy
        exact Subtype.ext (Subtype.ext h')
    rw [← e1]
    exact h3.trans (Nat.mul_le_mul_right _ e2)
  · intro hA
    refine h7 fun hle => hA fun a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := Subgroup.mem_centralizer_iff.1 (hle (show (⟨a, hAM ha⟩ : ↥M) ∈ A.subgroupOf M from ha))
      ⟨l, hLM hl⟩ hl
    exact congrArg Subtype.val this

end Concrete

end CFSG.Quasithin.SmithD310U
