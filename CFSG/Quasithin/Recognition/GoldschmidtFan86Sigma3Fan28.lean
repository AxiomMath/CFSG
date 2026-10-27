module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Fan28
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Split
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Stmt

public section

namespace CFSG.Quasithin.Fan86

theorem card_eq_three_mul {H : Type*} [Group H] [Finite H] {S : Subgroup H} (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index)
    (hq : Nonempty (H ⧸ CFSG.Open.pCore 2 H ≃* Equiv.Perm (Fin 3))) :
    Nat.card H = 3 * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hq
  have hQ : Nat.card H = 6 * Nat.card (CFSG.Open.pCore 2 H) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 H)
    rw [h1, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card]
    simp [Nat.factorial]
  obtain ⟨m, hm⟩ := (Sigma3.oQ_two (H := H)).exists_card_eq
  let P : Sylow 2 H := hS.toSylow hodd
  have h2 : Nat.card S = 2 ^ (Nat.card H).factorization 2 := P.card_eq_multiplicity
  have h6 : (6 : ℕ).factorization 2 = 1 := by
    have : (6 : ℕ) = 2 * 3 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  have h3 : (Nat.card H).factorization 2 = m + 1 := by
    rw [hQ, hm, Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply, h6,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
    simp [add_comm]
  rw [h2, h3, hQ, hm]
  ring

theorem fan28_of_sigma3PushingUp (h : Sigma3PushingUp) : Fan28 := by
  intro H _ _ S hS hq hK
  have hodd : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have hcard : Nat.card H = 3 * Nat.card S := card_eq_three_mul hS.2.1 hodd hq
  have hno : ∀ K : Subgroup H, K ≤ S → (K.subgroupOf S).Characteristic → K.Normal → K = ⊥ := by
    intro K hKS hc hn
    by_contra hne
    exact hK K hKS hne hc hn
  rcases h H S hq hS.2.1 hcard hno with ⟨T, E, ⟨eT⟩, hE, hc, hd, hs⟩ | ⟨T, C, ⟨eT⟩, hC, hc, hd, hs⟩
  · refine ⟨3, Or.inl rfl, ↥E, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
    · intro g
      exact ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
    · exact (Sigma3.prodEquivOfSplit T E hc hd hs).symm.trans
        (MulEquiv.prodCongr eT (MulEquiv.refl _))
  · refine ⟨4, Or.inr rfl, ↥C, inferInstance, inferInstance, hC, ⟨?_⟩⟩
    exact (Sigma3.prodEquivOfSplit T C hc hd hs).symm.trans
      (MulEquiv.prodCongr eT (MulEquiv.refl _))

end CFSG.Quasithin.Fan86
