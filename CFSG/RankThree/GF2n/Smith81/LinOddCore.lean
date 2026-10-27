module

public import CFSG.RankThree.GF2n.Smith81.LinOddAssembly

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem lin28aOdd_core (hF : LinSwapStatement) (hN : LinNonswapStatement)
    (hΓ : LinGammaStatement) (hRB : LinRankBoundStatement)
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) {m : ℕ} (hn : n = 2 * m + 1)
    (hm : 1 ≤ m) (S : OddSetup M Q Z B V₁ V₂) (hcond : Lin212CondProp M Q Z B V₁ V₂)
    {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) : Q ⊓ QB X ≠ ⊥ := by
  intro hQX
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hn3 : 3 ≤ n := by omega
  have hX4 : 4 ≤ Nat.card X := by
    rw [IsZConjugate.card_eq (Z := Z) hs.conj]; exact H.q4
  obtain ⟨x₀, hx₀X, hx₀1, hx₀V₁, -⟩ := exists_nonswap hX4 hs.X_sq
    (fun t ht => hF G M Q Z B n V₁ V₂ hc hS hn3 t (h12.1 ht))
  have hs0 : Sit M Q Z X x₀ :=
    ⟨hs.hyp, hs.conj, hx₀X, hx₀1, (h12.1 hx₀X).1, fun hxQ => hx₀1 (by
      have : x₀ ∈ X ⊓ Q := ⟨hx₀X, hxQ⟩
      rw [h12.2, Subgroup.mem_bot] at this
      exact this)⟩
  have hx₀L : x₀ ∈ Lgen M (LB M Q B) :=
    hN G M Q Z B n V₁ V₂ hc hS hn3 x₀ (h12.1 hx₀X) (by rw [hs0.x_sq]; exact Q.one_mem) hx₀V₁
  obtain ⟨hKx, hcx, V, hVmem, hVc, hVz, hVcard⟩ :=
    hΓ G M Q Z B X x₀ n m V₁ V₂ hc hS hn hm S.sqV S.sqV' hs0 hx₀L hQX
  obtain ⟨g, hg⟩ := hs.conj
  obtain ⟨y₁, hsY, hQY⟩ := exists_sit_Y hs hQX hg
  have hQXg : QB X = conjSubgroup g Q := by rw [hg]; exact QB_conj_eq H g
  have hnormX : Subgroup.normalizer (X : Set G) = conjSubgroup g M := by
    rw [hg]; exact normalizer_conj_eq H g
  have hQYg : QB (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ Q := QB_conj_eq H g⁻¹
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    have hm1 : m = 1 := by omega
    have hLx : Lx M (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ (Kx Q X) := by
      unfold Lx Kx
      rw [conjSubgroup_inf, hnormX, conjSubgroup_inv_conj, hQYg]
    have hcardT : Nat.card ↥(Lx M (conjSubgroup g⁻¹ Z)) = Nat.card Z ^ (n + 1) := by
      rw [hLx, card_conjSubgroup, hKx]
    have hsq : ∀ t ∈ Lx M (conjSubgroup g⁻¹ Z), t * t = 1 := fun t ht => by
      rw [← pow_two]; exact Lx_sq_eq_one hsY hQY ht
    refine step6 hF hN hΓ hc hS S hn hm hsY hQY _ le_rfl ?_ ?_
    · intro t ht ht1 htL
      have htQ : t ∉ Q := by
        intro htQ
        have : t ∈ Q ⊓ QB (conjSubgroup g⁻¹ Z) := ⟨htQ, ht.1⟩
        rw [hQY, Subgroup.mem_bot] at this
        exact ht1 this
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hRB G M Q Z B n V₁ V₂ hc hS t htL htQ
        (by rw [hsq t ht]; exact Q.one_mem)
      have hk : k = m := by omega
      rw [hk] at hk3 hk4
      exact ⟨hk3, hk4⟩
    · rw [hcardT, hn]
      exact Nat.pow_lt_pow_right (by have := H.q4; omega) (by omega)
  ·
    have hSV : ∃ V', OddSetup M Q Z B V V' ∧ Lin212CondProp M Q Z B V V' := by
      rcases hVmem with h | h
      · subst h; exact ⟨V₂, S, hcond⟩
      · have h' : V = V₂ := h
        subst h'; exact ⟨V₁, S.symm, hcond.symm⟩
    obtain ⟨V', S', hcond'⟩ := hSV
    set S₁ : Subgroup G := V ⊓ Subgroup.centralizer ({x₀} : Set G) with hS₁
    have hclaim : ∀ a ∈ S₁, a ∉ Z → ∀ A : Subgroup G, IsZConjugate Z A → a ∈ A →
        QB A ⊓ QB X = ⊥ := fun a ha haZ A hA haA =>
      S'.QB_inf_QB_eq_bot hcond' hs0 hQX hx₀L hcx hm2 hVz hVcard hA haA ha.1
        (Subgroup.mem_centralizer_singleton_iff.mp ha.2) haZ
    have hmemT : ∀ t ∈ conjSubgroup g⁻¹ S₁, g * t * g⁻¹ ∈ S₁ := fun t ht => by
      have := mem_conjSubgroup.mp ht
      simpa using this
    have hTL : conjSubgroup g⁻¹ S₁ ≤ Lx M (conjSubgroup g⁻¹ Z) := by
      intro t ht
      have ha := hmemT t ht
      refine ⟨?_, ?_⟩
      · have h1 : t ∈ conjSubgroup g⁻¹ Q := mem_conjSubgroup.mpr (by simpa using S'.VQ ha.1)
        rw [← hQYg] at h1
        exact h1
      · have hcomm : g * t * g⁻¹ * x₀ = x₀ * (g * t * g⁻¹) :=
          Subgroup.mem_centralizer_singleton_iff.mp ha.2
        have hnorm := Tim77.mem_normalizer_of_commute_of_isTI hs0.X_isTI hs0.mem hs0.ne_one
          hcomm
        rw [hnormX, mem_conjSubgroup] at hnorm
        simpa [mul_assoc] using hnorm
    refine step6 hF hN hΓ hc hS S hn hm hsY hQY (conjSubgroup g⁻¹ S₁) hTL ?_ ?_
    · intro t ht ht1 htL
      have ha := hmemT t ht
      have ha1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
        have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
        rw [this, h]; group)
      have htQ : t ∉ Q := by
        intro htQ
        have : t ∈ Q ⊓ QB (conjSubgroup g⁻¹ Z) := ⟨htQ, (hTL ht).1⟩
        rw [hQY, Subgroup.mem_bot] at this
        exact ht1 this
      by_cases haZ : g * t * g⁻¹ ∈ Z
      ·
        have htY : t ∈ conjSubgroup g⁻¹ Z := by
          rw [mem_conjSubgroup]; simpa using haZ
        have h12Y := smith_1_12 hsY
        have hsYt : Sit M Q Z (conjSubgroup g⁻¹ Z) t :=
          ⟨hsY.hyp, hsY.conj, htY, ht1, (h12Y.1 htY).1, htQ⟩
        exact hasDim_of_sit hc hS hn hm hsYt hQY htL
      · obtain ⟨ga, z, hz, hz1, hae⟩ :=
          (S'.p31 _ (S'.VQ ha.1) ha1).mpr (Or.inl ha.1)
        have hA : IsZConjugate Z (conjSubgroup ga Z) := ⟨ga, rfl⟩
        have haA : g * t * g⁻¹ ∈ conjSubgroup ga Z := by
          rw [mem_conjSubgroup, hae]; simpa [mul_assoc] using hz
        have hQA := hclaim _ ha haZ _ hA haA
        have hAt : IsZConjugate Z (conjSubgroup g⁻¹ (conjSubgroup ga Z)) := hA.conj g⁻¹
        have htA : t ∈ conjSubgroup g⁻¹ (conjSubgroup ga Z) := by
          rw [mem_conjSubgroup]; simpa using haA
        have hsAt : Sit M Q Z (conjSubgroup g⁻¹ (conjSubgroup ga Z)) t :=
          ⟨H, hAt, htA, ht1, (hTL ht).2, htQ⟩
        have hQAt : Q ⊓ QB (conjSubgroup g⁻¹ (conjSubgroup ga Z)) = ⊥ := by
          rw [QB_conj_of_isZConjugate H hA]
          have h1 : Q = conjSubgroup g⁻¹ (QB X) := by rw [hQXg, conjSubgroup_inv_conj]
          have h2 : conjSubgroup g⁻¹ (QB X ⊓ QB (conjSubgroup ga Z)) = ⊥ := by
            rw [inf_comm, hQA]; exact Subgroup.map_bot _
          rw [conjSubgroup_inf] at h2
          rw [h1]; exact h2
        exact hasDim_of_sit hc hS hn hm hsAt hQAt htL
    · rw [card_conjSubgroup, hS₁, hVc]
      exact Nat.pow_lt_pow_right (by have := H.q4; omega) (by omega)

end CFSG.RankThree.GF2n.Smith81
