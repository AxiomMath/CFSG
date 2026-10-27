module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityTransvection
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityFrame
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityExact

public section

namespace CFSG.RankThree.PartOne.KCUnitaryMixTau

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryTransvection CFSG.RankThree.PartOne.KCUnitaryFrame

section Roots

variable {ℓ f p : ℕ} {K : Type} [Field K]

theorem exists_primitiveRoot_of_dvd_sub (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f - 1) : ∃ ζ : K, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  classical
  have hcard : Fintype.card Kˣ = ℓ ^ (2 * f) - 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
  have hdvd : p ∣ Fintype.card Kˣ := by
    rw [hcard]
    have h1 : ℓ ^ (2 * f) - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      have hpos : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
      obtain ⟨k, hk⟩ : ∃ k, ℓ ^ f = k + 1 := ⟨ℓ ^ f - 1, by omega⟩
      rw [pow_mul', pow_two, hk]
      simp only [Nat.add_sub_cancel]
      rw [show (k + 1) * (k + 1) - 1 = k * (k + 2) by ring_nf; omega]
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_eq_fintype_card])
  refine ⟨(z : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hz]
  exact IsPrimitiveRoot.orderOf z

theorem exists_eq_X_sub_C {ζ : K} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) {a : K[X]}
    (ham : a.Monic) (hair : Irreducible a) (had : a ∣ X ^ p - 1) :
    ∃ μ : K, a = X - C μ ∧ μ ^ p = 1 := by
  classical
  have hprod := Polynomial.X_pow_sub_one_eq_prod hp.pos hζ
  rw [hprod] at had
  obtain ⟨μ, hμmem, hμ⟩ := (hair.prime.dvd_finsetProd_iff _).mp had
  refine ⟨μ, eq_of_monic_of_associated ham (monic_X_sub_C μ)
    (hair.associated_of_dvd (irreducible_X_sub_C μ) hμ), ?_⟩
  exact (mem_nthRootsFinset hp.pos (1 : K)).mp hμmem

end Roots

section Transvection

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem tau_eq_one_of_transvection (S : PlaneSetup h n p Ahat) {x : gramSU h (idGram K n)}
    (hx : x ∈ Ahat) (a : GoodBlockIdx h x) (hne : (a.1 : K[X]) ≠ dualPoly h.bar (a.1 : K[X]))
    {u w : Fin n → K} (hu : u ∈ primaryComponent (xlin h n x) (a.1 : K[X]))
    (hw : w ∈ primaryComponent (xlin h n x) (a.1 : K[X])) (hu0 : u ≠ 0)
    (hind : LinearIndependent (AdjoinRoot (a.1 : K[X]))
      ![(⟨u, hu⟩ : primaryComponent (xlin h n x) (a.1 : K[X])), ⟨w, hw⟩])
    (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hstab : ∀ v ∈ primaryComponent (xlin h n x) (a.1 : K[X]),
      semilinRep ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (τ : K →+* K) v ∈
        primaryComponent (xlin h n x) (a.1 : K[X]))
    (hblock : ∀ g ∈ idSpecialBlock h x (a.1 : K[X]),
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    τ = RingEquiv.refl K := by
  classical
  have H := (S.planeData hx).primaryData
  have hF := isPerfect_idSpecialBlock S hx a
  set W := primaryComponent (xlin h n x) (a.1 : K[X]) with hWdef
  set E := AdjoinRoot (a.1 : K[X]) with hEdef
  set u₀ : W := ⟨u, hu⟩ with hu₀
  set w₀ : W := ⟨w, hw⟩ with hw₀
  set γ := semilinRep ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (τ : K →+* K) with hγ
  have hγinj : Function.Injective γ := semilinRep_injective (M : GL (Fin n) K).isUnit _
  have hγu : γ u ≠ 0 := by
    intro h0
    apply hu0
    apply hγinj
    rw [h0, map_zero]
  have hwnot : w₀ ∉ Submodule.span E {u₀} := by
    intro hmem
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hmem
    have := (LinearIndependent.pair_iff.mp hind) e (-1) (by
      simp only [neg_smul, one_smul]
      rw [he]
      exact add_neg_cancel _)
    exact one_ne_zero (neg_eq_zero.mp this.2)
  obtain ⟨φ₀, hφ₀w, hφ₀u⟩ := Submodule.exists_le_ker_of_notMem hwnot
  set φ : Module.Dual E W := (φ₀ w₀)⁻¹ • φ₀ with hφ
  have hφw : φ w₀ = 1 := by
    rw [hφ, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀w]
  have hφu : φ u₀ = 0 := by
    have : φ₀ u₀ = 0 := hφ₀u (Submodule.mem_span_singleton_self u₀)
    rw [hφ, LinearMap.smul_apply, this, smul_zero]
  have hγw : γ w ∈ W := hstab w hw
  set d : E := φ ⟨γ w, hγw⟩ with hd
  have key : ∀ c : K, (τ c) • γ u = c • ((d • u₀ : W) : Fin n → K) := by
    intro c
    have hφc : φ (algebraMap K E c • u₀) = 0 := by
      rw [map_smul, hφu, smul_zero]
    obtain ⟨g, hg, hgval⟩ := exists_mem_specialBlock_transvection H a.1.2 hne φ
      (algebraMap K E c • u₀) hφc
    have hgs : g ∈ sesqUnitaryGroup (idForm h n) := (specialBlock_le_unitaryCentralizer hg).1
    obtain ⟨Y, hY⟩ := exists_toLinU hgs
    have hYmem : Y ∈ idSpecialBlock h x (a.1 : K[X]) := by
      rw [mem_idSpecialBlock, hY]
      exact hg
    have hcomm := matrix_comm_of_perfect S.three_le S.ne hF M τ hblock Y hYmem
    have hgY : ∀ v : Fin n → K, (g : Module.End K (Fin n → K)) v =
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := fun v => by
      rw [← hY]
      rfl
    have hcg : ∀ v : Fin n → K, γ ((g : Module.End K (Fin n → K)) v) =
        (g : Module.End K (Fin n → K)) (γ v) := fun v => by
      rw [hgY, hgY]
      exact semilinRep_mulVec_comm (τ : K →+* K) hcomm v
    have h1 := hcg w
    rw [hgval w hw, hφw, one_smul, map_add, coe_algebraMap_smul_primaryComponent,
      map_smulₛₗ, hgval (γ w) hγw] at h1
    have h2 := add_left_cancel h1
    have h3 : ((d • (algebraMap K E c • u₀) : W) : Fin n → K) =
        c • ((d • u₀ : W) : Fin n → K) := by
      rw [smul_comm, ← coe_algebraMap_smul_primaryComponent]
    rw [h3] at h2
    exact h2
  have h1 := key 1
  rw [map_one, one_smul, one_smul] at h1
  refine RingEquiv.ext fun c => ?_
  have h2 := key c
  rw [← h1] at h2
  have h3 : (τ c - c) • γ u = 0 := by rw [sub_smul, h2, sub_self]
  have h4 := (smul_eq_zero.mp h3).resolve_right hγu
  exact sub_eq_zero.mp h4

end Transvection

end CFSG.RankThree.PartOne.KCUnitaryMixTau
