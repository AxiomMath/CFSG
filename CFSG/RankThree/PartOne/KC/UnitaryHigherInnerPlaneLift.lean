module

public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneKernel
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneLift

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane

theorem KCUnitaryPlane.exists_primitiveRoot_of_dvd {ℓ f p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by
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
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_eq_fintype_card])
  refine ⟨(z : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hz]
  exact IsPrimitiveRoot.orderOf z

theorem higher_unitary_inner_plane_commuting_lift_and_kernel_decomposition
    {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (hn : 3 ≤ n) (hnp : n < p) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (A : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hAH : A ≤ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    (∃! Ahat : Subgroup (gramSU h (idGram K n)), IsPlaneLift h n p A Ahat) ∧
      ∀ Ahat : Subgroup (gramSU h (idGram K n)), IsPlaneLift h n p A Ahat →
        (∀ a ∈ A, a ≠ 1 → ∃ x ∈ Ahat, innerLift h n x = a ∧ orderOf x = p ∧
          ∀ y : gramSU h (idGram K n), innerLift h n y = a → y ^ p = 1 → y = x) ∧
        PlaneKernelDecomposition h n p Ahat ∧
        (ordNegQ ℓ f p = 1 → p ∣ ℓ ^ f + 1 ∧ 3 < ℓ ^ f ∧
          ∃ b : Module.Basis (Fin n) K (Fin n → K),
            (∀ i j, idForm h n (b i) (b j) = if i = j then 1 else 0) ∧
              ∀ (x : ↥Ahat) (i : Fin n), ∃ c : K, act (planeRep h n Ahat) x (b i) = c • b i) ∧
        (1 < ordNegQ ℓ f p → ∀ L : Subgroup ↥Ahat, Nat.card L = p →
          lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥ →
            2 ≤ Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L)) ∧
        (ordNegQ ℓ f p = 2 → p ∣ ℓ ^ f - 1 ∧ 3 < ℓ ^ f) ∧
        (ℓ ^ f = 2 → 4 ≤ ordNegQ ℓ f p) ∧ (ℓ ^ f = 3 → 3 ≤ ordNegQ ℓ f p) := by
  have hp3 : 3 < p := by omega
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c _ hcn hcp
    have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    have h3 : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one hcn
    rcases (Nat.dvd_prime hp).mp h2 with h4 | h4
    · exact orderOf_eq_one_iff.mp h4
    · have := Nat.le_of_dvd (by omega) (h4 ▸ h3)
      omega
  have hlift := KCUnitaryPlane.exists_unique_planeLift hn hne hp hZp A hAH hA hAcard
  refine ⟨hlift, fun Ahat hAhat => ?_⟩
  obtain ⟨hel, hcard, -, -⟩ := id hAhat
  have hdec := planeKernelDecomposition hp hpℓ hel hcard
  refine ⟨fun a ha ha1 => planeLift_unique_lift hn hne hp hZp hAhat ha ha1, hdec, ?_, ?_,
    fun h2 => ordNegQ_eq_two hp hp3 h.prime h2 h.one_le,
    fun hq => four_le_ordNegQ_of_two hp hp3 hpℓ h.prime hq,
    fun hq => three_le_ordNegQ_of_three hp hp3 hpℓ h.prime hq⟩
  · intro he1
    have hpq : p ∣ ℓ ^ f + 1 := (ordNegQ_eq_one_iff hp).mp he1
    refine ⟨hpq, ?_, ?_⟩
    · have h1 := Nat.le_of_dvd (by omega) hpq
      omega
    · obtain ⟨ζ, hζ⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp hpq
      have : NeZero p := ⟨hp.ne_zero⟩
      have := h.finite
      have : Finite ↥Ahat := inferInstance
      have hP : IsPlane p ↥Ahat := isPlane_of_elementaryAbelian hp hel hcard
      have hcomm : ∀ x y : ↥Ahat, Commute (act (planeRep h n Ahat) x) (act (planeRep h n Ahat) y) :=
        fun x y => by
          have := hel
          have hxy : x * y = y * x := (IsMulCommutative.is_comm (M := ↥Ahat)).comm x y
          change act (planeRep h n Ahat) x * act (planeRep h n Ahat) y =
            act (planeRep h n Ahat) y * act (planeRep h n Ahat) x
          rw [← act_mul, ← act_mul, hxy]
      have hpow : ∀ x : ↥Ahat, act (planeRep h n Ahat) x ^ p = 1 := fun x => by
        rw [← act_pow, hP.pow x, act_one]
      have hiso : ∀ (x : ↥Ahat) (v w : Fin n → K),
          idForm h n (act (planeRep h n Ahat) x v) (act (planeRep h n Ahat) x w) =
            idForm h n v w := fun x v w => planeRep_mem Ahat x v w
      obtain ⟨b, μ, hbμ, hbo⟩ := exists_orthonormal_common_eigenbasis h hζ hpq
        (idForm_isSymm h n) (idForm_separatingLeft h n)
        (fun x : ↥Ahat => act (planeRep h n Ahat) x) hcomm hpow hiso
      refine ⟨b.reindex (finCongr (Module.finrank_fin_fun K)), fun i j => ?_, fun x i => ?_⟩
      · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
        simp
      · rw [Module.Basis.reindex_apply]
        exact ⟨μ x _, hbμ x _⟩
  · intro he1 L hL hne0
    have hd := hdec.dvd_finrank L hL
    have hpos : 0 < Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L) := by
      rcases Nat.eq_zero_or_pos (Module.finrank K
        (lineSpace (planeRep h n Ahat) (idForm h n) L)) with h0 | h0
      · exact absurd (Submodule.finrank_eq_zero.mp h0) hne0
      · exact h0
    have := Nat.le_of_dvd hpos hd
    omega

end CFSG.RankThree.PartOne
