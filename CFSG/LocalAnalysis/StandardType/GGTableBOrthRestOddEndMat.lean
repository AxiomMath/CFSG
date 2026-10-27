module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddAdm
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge

public section

namespace CFSG.StandardType

namespace OrthRestOdd

open Module CFSG.RankThree.Classical2 CFSG.Assembly CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.PartOne.AUTSL

variable {K : Type} [Field K] {d : ℕ}

@[expose] def GoodOuterInv (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ u : MulAut (matrixDerived Q), u ∉ OuterAutomorphisms.inner (matrixDerived Q) → u ^ 2 = 1 →
    ∃ β : MulAut (matrixDerived Q), ∃ g : matrixDerived Q, ∃ r : matrixIsometries Q,
      r.val * r.val = 1 ∧ β * u * β⁻¹ = MulAut.conj g * conjAct Q (matrixIsometryInclusion Q r)

variable {Q : QuadraticForm K (Fin d → K)}

theorem conj_map_mulAut {X : Type*} [Group X] (α : MulAut X) (g : X) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext y
  simp [MulAut.conj_apply]

theorem center_matrixDerived_eq_bot [Finite K] [CharP K 2]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 8 ≤ d) :
    Subgroup.center (matrixDerived Q) = ⊥ := by
  have hdim : 6 ≤ finrank K (Fin d → K) := by rw [Module.finrank_fin_fun]; omega
  have hZ := (orthDerived_facts Q hQ hdim).2.1
  have hmap := OuterAutomorphisms.center_map_equiv
    (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q)
  rw [hZ] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q).injective).mp hmap

theorem ggEndNodeEltAdm_of_goodOuterInv [Finite K] [CharP K 2]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {ℓ : ℕ} (hd : d = 2 * ℓ) (hℓ : 4 ≤ ℓ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    (hgood : GoodOuterInv Q) : TableBUR.GGEndNodeEltAdm p (ℓ - 1) (matrixDerived Q) := by
  classical
  set ψ := CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q with hψ
  have hdim : finrank K (Fin d → K) = 2 * ℓ := by rw [Module.finrank_fin_fun, hd]
  have hV8 : 8 ≤ finrank K (Fin d → K) := by omega
  have hZ := center_matrixDerived_eq_bot hQ (by omega : 8 ≤ d)
  have hinj := OrthRest.conj_injective hZ
  have : Finite (GL (Fin d) K) := Finite.of_injective (fun g : GL (Fin d) K =>
    (g : Matrix (Fin d) (Fin d) K)) Units.val_injective
  have : Finite (matrixDerived Q) := inferInstance
  have : Finite (MulAut (matrixDerived Q)) :=
    Finite.of_injective (fun α : MulAut (matrixDerived Q) => (α : matrixDerived Q → _))
      fun a b h => MulEquiv.ext (congrFun h)
  have hψval : ∀ X : matrixDerived Q, ((ψ X : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearIso X.val := fun X => rfl
  refine ggEndNodeEltAdm_of_isEndNode fun A hA hr _ ⟨U, hU1, hU2, hUN⟩ => ?_
  suffices hred : ∃ β : MulAut (matrixDerived Q), ∃ Y : Submodule K (Fin d → K), Y ≠ ⊥ ∧
      (∀ a ∈ A, ∀ y ∈ Y, ((ψ (β a) : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) y ∈ Y) ∧
      ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polar Q y y' = 0 by
    obtain ⟨β, Y, hY, hYinv, hYiso⟩ := hred
    set e := β.trans ψ with he
    have hA' : IsElemAbelian p (A.map e.toMonoidHom) := TableB.isElemAbelian_map hA _
    have hcard : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
      (Nat.card_congr (A.equivMapOfInjective _ e.injective).toEquiv).symm
    obtain ⟨t, ht⟩ := exists_isEndNode_of_isotropic hQ hV8 hp hp2 hK1 hA'
      (by rw [hcard, hdim]; convert hr using 2; omega) hY
      (by rintro _ ⟨a, ha, rfl⟩ y hy; exact hYinv a ha y hy) hYiso
    exact ⟨_, isEndNode_of_map e ht⟩
  have hNA : ∀ a ∈ A, ∀ n : MulAut (matrixDerived Q),
      n ∈ U ↔ MulAut.conj a * n * (MulAut.conj a)⁻¹ ∈ U := fun a ha =>
    Subgroup.mem_normalizer_iff.mp (hUN ⟨a, ha, rfl⟩)
  by_cases hUI : U ⊓ OuterAutomorphisms.inner (matrixDerived Q) = ⊥
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2U : 2 ∣ Nat.card U := by
      rcases hU2.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hU1
      · exact h1
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2U
    have hu1 : (u : MulAut (matrixDerived Q)) ≠ 1 := by
      intro h
      have : u = 1 := Subtype.ext h
      rw [this, orderOf_one] at hu
      exact absurd hu (by norm_num)
    have hu2 : (u : MulAut (matrixDerived Q)) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hu, pow_orderOf_eq_one, OneMemClass.coe_one]
    have huI : (u : MulAut (matrixDerived Q)) ∉ OuterAutomorphisms.inner (matrixDerived Q) := by
      intro h
      have : (u : MulAut (matrixDerived Q)) ∈ U ⊓ OuterAutomorphisms.inner (matrixDerived Q) :=
        ⟨u.2, h⟩
      rw [hUI, Subgroup.mem_bot] at this
      exact hu1 this
    have hcommA : ∀ a ∈ A, MulAut.conj a * (u : MulAut (matrixDerived Q)) =
        (u : MulAut (matrixDerived Q)) * MulAut.conj a := by
      intro a ha
      set c := MulAut.conj a * (u : MulAut (matrixDerived Q)) * (MulAut.conj a)⁻¹ *
        (u : MulAut (matrixDerived Q))⁻¹ with hc
      have hcU : c ∈ U := mul_mem ((hNA a ha _).mp u.2) (inv_mem u.2)
      have hcI : c ∈ OuterAutomorphisms.inner (matrixDerived Q) := by
        have h1 : (u : MulAut (matrixDerived Q)) * (MulAut.conj a)⁻¹ *
            (u : MulAut (matrixDerived Q))⁻¹ ∈ OuterAutomorphisms.inner (matrixDerived Q) :=
          (OuterAutomorphisms.inner_normal _).conj_mem _ (inv_mem ⟨a, rfl⟩) _
        rw [hc, mul_assoc, mul_assoc]
        rw [mul_assoc] at h1
        exact mul_mem ⟨a, rfl⟩ h1
      have : c ∈ U ⊓ OuterAutomorphisms.inner (matrixDerived Q) := ⟨hcU, hcI⟩
      rw [hUI, Subgroup.mem_bot, hc] at this
      calc MulAut.conj a * (u : MulAut (matrixDerived Q)) =
          (MulAut.conj a * (u : MulAut (matrixDerived Q)) * (MulAut.conj a)⁻¹ *
            (u : MulAut (matrixDerived Q))⁻¹) * u * MulAut.conj a := by group
        _ = u * MulAut.conj a := by rw [this, one_mul]
    obtain ⟨β, g, r, hr2, hβ⟩ := hgood u huI hu2
    set B := A.map β.toMonoidHom with hB
    have hβu1 : β * (u : MulAut (matrixDerived Q)) * β⁻¹ ≠ 1 := by
      intro h
      apply hu1
      calc (u : MulAut (matrixDerived Q)) = β⁻¹ * (β * u * β⁻¹) * β := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
    have hβu2 : (β * (u : MulAut (matrixDerived Q)) * β⁻¹) ^ 2 = 1 := by
      rw [pow_two]
      calc β * (u : MulAut (matrixDerived Q)) * β⁻¹ * (β * u * β⁻¹) =
          β * ((u : MulAut (matrixDerived Q)) * u) * β⁻¹ := by group
        _ = 1 := by rw [← pow_two, hu2, mul_one, mul_inv_cancel]
    have hcommB : ∀ b ∈ B, MulAut.conj b * (β * (u : MulAut (matrixDerived Q)) * β⁻¹) =
        (β * (u : MulAut (matrixDerived Q)) * β⁻¹) * MulAut.conj b := by
      rintro _ ⟨a, ha, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← conj_map_mulAut]
      calc β * MulAut.conj a * β⁻¹ * (β * (u : MulAut (matrixDerived Q)) * β⁻¹) =
          β * (MulAut.conj a * u) * β⁻¹ := by group
        _ = β * (u * MulAut.conj a) * β⁻¹ := by rw [hcommA a ha]
        _ = _ := by group
    rw [hβ] at hβu1 hβu2 hcommB
    obtain ⟨hhO, hh2, hh1, hhc⟩ := exists_involution_of_conj hZ g r hr2 hβu1 hβu2 hcommB
    set hl := matrixLinearIso (g.val * r.val) with hhl
    have hlO : hl ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hhO
    have hl2 : hl * hl = 1 := by rw [hhl, ← map_mul, hh2, map_one]
    have hl1 : hl ≠ 1 := by
      intro h
      apply hh1
      apply matrixLinearIso.injective
      rw [map_one]
      exact h
    obtain ⟨hY, hYinv, hYiso⟩ := isotropic_of_involution hlO hl2 hl1
      (A := B.map ψ.toMonoidHom) (by
        rintro _ ⟨b, hb, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hψval, hhl, ← map_mul, ← map_mul, hhc b hb])
    exact ⟨β, _, hY, fun a ha y hy => hYinv _ ⟨β a, ⟨a, ha, rfl⟩, rfl⟩ y hy, hYiso⟩
  ·
    set V₀ := (U ⊓ OuterAutomorphisms.inner (matrixDerived Q)).comap
      (MulAut.conj : matrixDerived Q →* _) with hV₀
    have hV₀1 : V₀ ≠ ⊥ := by
      intro h0
      apply hUI
      rw [eq_bot_iff]
      rintro x ⟨hxU, ⟨v, rfl⟩⟩
      have hv : v ∈ V₀ := ⟨hxU, ⟨v, rfl⟩⟩
      rw [h0, Subgroup.mem_bot] at hv
      rw [hv, map_one]
      exact one_mem _
    have hV₀2 : IsPGroup 2 V₀ := by
      intro v
      obtain ⟨k, hk⟩ := hU2 ⟨MulAut.conj (v : matrixDerived Q), v.2.1⟩
      refine ⟨k, Subtype.ext (hinj ?_)⟩
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
      rw [Subgroup.coe_pow, map_pow, this, OneMemClass.coe_one, map_one]
    have hnorm : ∀ a ∈ A, ∀ v ∈ V₀, a * v * a⁻¹ ∈ V₀ := by
      intro a ha v hv
      refine ⟨?_, ⟨a * v * a⁻¹, rfl⟩⟩
      rw [map_mul, map_mul, map_inv]
      exact (hNA a ha _).mp hv.1
    obtain ⟨Y, hY, hYinv, hYiso⟩ := isotropic_of_two_subgroup (Q := Q)
      (V₀ := V₀.map ψ.toMonoidHom) (A := A.map ψ.toMonoidHom)
      (fun h0 => hV₀1 ((Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp h0))
      (hV₀2.map _) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
        exact ⟨a * v * a⁻¹, hnorm a ha v hv, by simp⟩)
    exact ⟨1, Y, hY, fun a ha y hy => hYinv _ ⟨a, ha, rfl⟩ y hy, hYiso⟩

end OrthRestOdd

end CFSG.StandardType
