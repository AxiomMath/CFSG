module

public import CFSG.RankThree.GF2n.Stroth80.SL2KDescent
public import CFSG.RankThree.GF2n.Smith81.TiD3Hyp

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Descent

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.GF2n.Smith81
open scoped MatrixGroups

section Compat

variable {k₀ : Type*} [Field k₀] {G : Type*} [Monoid G] {W : Type*} [AddCommGroup W]
  [Module k₀ W] {ρ : Representation k₀ G W} [Fact ρ.IsIrreducible] [Finite W]

theorem algebraMap_smul_endRing (c : k₀) (w : W) :
    (algebraMap k₀ (EndRing ρ) c) • w = c • w := rfl

theorem repr_smul_endRing {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) (c : k₀) (w : W)
    (i : Fin m) : b.repr (c • w) i = algebraMap k₀ (EndRing ρ) c * b.repr w i := by
  rw [← algebraMap_smul_endRing (ρ := ρ) c w, map_smul]
  rfl

end Compat


section Triple

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] [CharP E 2]

theorem exists_equiv_triple {a k : ℕ} (hk : 0 < k) {J : Finset ℕ} (hJ : J = {a, a + k, a + 2 * k}) :
    Nonempty ((frobTensor F E J).Equiv (tensorRep F E ![a, a + k, a + 2 * k])) := by
  subst hJ
  let e' : Fin 3 → ℕ := ![a, a + k, a + 2 * k]
  have hmem : ∀ s, e' s ∈ ({a, a + k, a + 2 * k} : Finset ℕ) := by
    intro s
    fin_cases s <;> simp [e']
  let g3 : Fin 3 → ↥({a, a + k, a + 2 * k} : Finset ℕ) := fun s => ⟨e' s, hmem s⟩
  have hinj : Function.Injective g3 := by
    intro s t h
    have h' : e' s = e' t := congrArg Subtype.val h
    fin_cases s <;> fin_cases t <;> simp [e'] at h' ⊢ <;> omega
  have hcard : Fintype.card (Fin 3) = Fintype.card ↥({a, a + k, a + 2 * k} : Finset ℕ) := by
    rw [Fintype.card_coe, Finset.card_eq_three.mpr ⟨a, a + k, a + 2 * k, by omega, by omega,
      by omega, rfl⟩]
    simp
  have hbij : Function.Bijective g3 :=
    (Fintype.bijective_iff_injective_and_card g3).mpr ⟨hinj, hcard⟩
  refine ⟨reindexEquiv (Equiv.ofBijective g3 hbij).symm (fun i => (i : ℕ)) e' (fun i => ?_)⟩
  exact congrArg Subtype.val ((Equiv.ofBijective g3 hbij).apply_symm_apply i)

end Triple


theorem eq_triple_of_shift {k : ℕ} (hk : 0 < k) {J : Finset ℕ} (hJ : ∀ i ∈ J, i < 3 * k)
    (hshift : J.image (fun i => (i + k) % (3 * k)) = J) (hcard : J.card = 3) :
    ∃ a, a < k ∧ J = {a, a + k, a + 2 * k} := by
  have hstep : ∀ x ∈ J, (x + k) % (3 * k) ∈ J := by
    intro x hx
    rw [← hshift]
    exact Finset.mem_image_of_mem (fun i => (i + k) % (3 * k)) hx
  have hiter : ∀ m : ℕ, ∀ x ∈ J, (x + m * k) % (3 * k) ∈ J := by
    intro m
    induction m with
    | zero =>
      intro x hx
      rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (hJ x hx)]
      exact hx
    | succ m ih =>
      intro x hx
      have h1 : (x + (m + 1) * k) % (3 * k) = ((x + m * k) % (3 * k) + k) % (3 * k) := by
        rw [Nat.mod_add_mod, show x + (m + 1) * k = x + m * k + k by ring]
      rw [h1]
      exact hstep _ (ih x hx)
  have hne : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj⟩ := hne
  have hjk : j < 3 * k := hJ j hj
  obtain ⟨a, ha_def⟩ : ∃ a, a = j % k := ⟨_, rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ q, q = j / k := ⟨_, rfl⟩
  have hdm : a + k * q = j := by
    rw [ha_def, hq_def]
    exact Nat.mod_add_div j k
  have hak : a < k := by
    rw [ha_def]
    exact Nat.mod_lt j hk
  have hq : q < 3 := by
    rw [hq_def]
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm]
    exact hjk
  have ha : a ∈ J := by
    obtain ⟨t, ht⟩ : ∃ t, q + t = 3 := ⟨3 - q, by omega⟩
    have h3k : (q + t) * k = q * k + t * k := by ring
    rw [ht] at h3k
    rw [Nat.mul_comm k q] at hdm
    have h3 : j + t * k = a + 3 * k := by linarith
    have h := hiter t j hj
    rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a < 3 * k)] at h
    exact h
  have h1 : a + k ∈ J := by
    have h := hiter 1 a ha
    rw [Nat.one_mul, Nat.mod_eq_of_lt (by omega : a + k < 3 * k)] at h
    exact h
  have h2 : a + 2 * k ∈ J := by
    have h := hiter 2 a ha
    rw [Nat.mod_eq_of_lt (by omega : a + 2 * k < 3 * k)] at h
    exact h
  have hsub : ({a, a + k, a + 2 * k} : Finset ℕ) ⊆ J := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact h1
    · exact h2
  have hc3 : ({a, a + k, a + 2 * k} : Finset ℕ).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, a + k, a + 2 * k, by omega, by omega, by omega, rfl⟩
  exact ⟨a, hak, (Finset.eq_of_subset_of_card_le hsub (by omega)).symm⟩

section HypMap

open CFSG.RankThree.GF2n.Smith81.D3 in
theorem exists_hyp_map {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F]
    [Algebra K F] {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk2 : 2 ≤ k)
    (hcardF : Fintype.card F = Fintype.card K ^ 3) {E : Type} [AddCommGroup E] [Module K E]
    [Module.Finite K E] (hdim : Module.finrank K E = 8) (ρ : Representation K SL(2, F) E)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) :
    ∃ (a : ℕ) (σ : F ≃+* F) (θ : E →ₗ[K] Hyp F), (∀ x, σ x = x ^ 2 ^ a) ∧ Function.Injective θ ∧
      ∀ (g : SL(2, F)) (e : E), θ (ρ g e) = act (FiniteField.frobeniusAlgHom K F : F →+* F)
        ((D2.slMap σ g : SL(2, F)) : Mat2 F) (θ e) := by
  classical
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  have hk0 : 0 < k := by omega
  have hn : 1 ≤ 3 * k := by omega
  have hF : Fintype.card F = 2 ^ (3 * k) := by rw [hcardF, hk, ← pow_mul, mul_comm]
  haveI : Finite E := Module.finite_of_finite K
  obtain ⟨f, J₀, hf1, hDk, hfn, hJ₀ne, hJ₀n, hshift₀, hdim₀⟩ :=
    kDescent (ρ := ρ) hk hn hF (algebraMap K F) hnt
  have hf3 : f ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hk0 (by rw [mul_comm 3 k] at hfn; exact hfn)
  have hf : f = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hf3 with h1 | h3
    · exact h1
    · exfalso
      rw [hdim, h3] at hdim₀
      omega
  subst hf
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  have hDK : Nat.card (EndRing ρ) = Fintype.card K := by rw [hDk, mul_one, hk]
  have hbij : Function.Bijective (algebraMap K (EndRing ρ)) :=
    (algebraMap K (EndRing ρ)).injective.bijective_of_nat_card_le
      (by rw [hDK, Nat.card_eq_fintype_card])
  let γ : EndRing ρ ≃+* K := (RingEquiv.ofBijective (algebraMap K (EndRing ρ)) hbij).symm
  have hγ : ∀ c : K, γ (algebraMap K (EndRing ρ) c) = c := fun c =>
    (RingEquiv.ofBijective (algebraMap K (EndRing ρ)) hbij).symm_apply_apply c
  let ιD : EndRing ρ →+* F := (algebraMap K F).comp γ.toRingHom
  have hιD : ∀ c : K, ιD (algebraMap K (EndRing ρ) c) = algebraMap K F c := fun c => by
    show algebraMap K F (γ (algebraMap K (EndRing ρ) c)) = _
    rw [hγ]
  haveI : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) E
  have hm : Module.finrank (EndRing ρ) E = 8 := by
    have h1 := natCard_eq_pow_finrank (ρ := ρ)
    have h2 := Module.natCard_eq_pow_finrank (K := K) (V := E)
    rw [h1, hDK, hdim, Nat.card_eq_fintype_card (α := K)] at h2
    have hq : 2 ≤ Fintype.card K := by
      rw [hk]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.pow_right_injective hq h2.symm.symm
  obtain ⟨J, hJne, hJn, ⟨Φ⟩, hshift, hdimJ⟩ :=
    descent_core_alg (F := F) (E := F) hn hF ρ hnt hDk b ιD
  have hJcard : J.card = 3 := by
    have h8 : 2 ^ J.card = 2 ^ 3 := by rw [← hdimJ, hm]; norm_num
    exact Nat.pow_right_injective le_rfl h8
  rw [mul_one] at hshift
  obtain ⟨a, hak, hJa⟩ := eq_triple_of_shift hk0 hJn hshift hJcard
  obtain ⟨Ψ⟩ := exists_equiv_triple (F := F) (E := F) hk0 hJa
  let Φ' := Φ.trans Ψ
  haveI : ExpChar F 2 := ExpChar.prime Nat.prime_two
  let σ : F ≃+* F := iterateFrobeniusEquiv F 2 a
  have hσ : ∀ x, σ x = x ^ 2 ^ a := fun x => iterateFrobeniusEquiv_def F 2 a x
  let τ : F →+* F := (FiniteField.frobeniusAlgHom K F : F →+* F)
  have hτ : ∀ x, τ x = x ^ 2 ^ k := fun x => by
    show x ^ Fintype.card K = _
    rw [hk]
  let θ₀ : E → (Fin (Module.finrank (EndRing ρ) E) → F) := fun e i => ιD (b.repr e i)
  have hθ₀add : ∀ e e', θ₀ (e + e') = θ₀ e + θ₀ e' := by
    intro e e'
    funext i
    show ιD (b.repr (e + e') i) = ιD (b.repr e i) + ιD (b.repr e' i)
    rw [b.repr.map_add, Finsupp.add_apply, ιD.map_add]
  have hθ₀smul : ∀ (c : K) e, θ₀ (c • e) = algebraMap K F c • θ₀ e := by
    intro c e
    funext i
    simp only [θ₀, Pi.smul_apply, smul_eq_mul]
    rw [repr_smul_endRing, ιD.map_mul, hιD]
  have hθ₀rep : ∀ g e, θ₀ (ρ g e) = ((matRep b g).map ιD).mulVec (θ₀ e) := by
    intro g e
    funext i
    have h1 := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) e
    have h2 := congrFun h1 i
    rw [repD_apply] at h2
    show ιD (b.repr (ρ g e) i) =
      (((matRep b g).map ιD).mulVec (fun j => ιD (b.repr e j))) i
    rw [← h2]
    exact ιD.map_mulVec (matRep b g) (⇑(b.repr e)) i
  let θ : E →ₗ[K] Hyp F :=
    { toFun := fun e => hyp (Φ'.toLinearEquiv (θ₀ e))
      map_add' := fun e e' => by
        simp only [hθ₀add, map_add]
        funext i j k
        rfl
      map_smul' := fun c e => by
        simp only [hθ₀smul, map_smul, RingHom.id_apply]
        funext i j k
        simp [hyp, Algebra.smul_def] }
  have hequiv : ∀ (g : SL(2, F)) (e : E), θ (ρ g e) = act τ ((D2.slMap σ g : SL(2, F)) : Mat2 F)
      (θ e) := by
    intro g e
    show hyp (Φ'.toLinearEquiv (θ₀ (ρ g e))) = act τ _ (hyp (Φ'.toLinearEquiv (θ₀ e)))
    rw [hθ₀rep, ← matRepE_apply]
    have h3 := equiv_apply Φ' g (θ₀ e)
    exact (congrArg hyp h3).trans (hyp_tensorRep_act a k σ hσ τ hτ g _)
  have hinj : Function.Injective θ := by
    intro e e' h
    have h1 : hyp (Φ'.toLinearEquiv (θ₀ e)) = hyp (Φ'.toLinearEquiv (θ₀ e')) := h
    have h2 : Φ'.toLinearEquiv (θ₀ e) = Φ'.toLinearEquiv (θ₀ e') := by
      funext x
      have h3 := congrFun (congrFun (congrFun h1 (x 0)) (x 1)) (x 2)
      have hx : (![x 0, x 1, x 2] : Fin 3 → Fin 2) = x := by
        funext s
        fin_cases s <;> rfl
      simpa [hyp, hx] using h3
    have h4 := Φ'.toLinearEquiv.injective h2
    apply b.repr.injective
    exact Finsupp.ext fun i => ιD.injective (congrFun h4 i)
  exact ⟨a, σ, θ, hσ, hinj, hequiv⟩

end HypMap

end CFSG.RankThree.GF2n.Stroth80.SL2Descent
