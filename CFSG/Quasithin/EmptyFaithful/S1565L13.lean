module

public import CFSG.Quasithin.EmptyFaithful.S1565L11
public import CFSG.Quasithin.EmptyFaithful.S1565L5

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

variable {W : Type} [CommGroup W]

theorem natfree_sl2_of_big {L : Subgroup (MulAut W)} {V C : Subgroup W} (hL : 6 < Nat.card ↥L)
    {n' : ℕ} (h : BinaryNaturalSL L V (V ⊓ C) 2 n') (S : Sylow 2 ↥L) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ V, ((b : MulAut W) u) * u⁻¹ ∈ V ⊓ C → u ∈ V ⊓ C := by
  have hn' : 2 ≤ n' := by
    by_contra hlt
    exact absurd (card_le_six_of_natural_sl2_small h (by omega)) (by omega)
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨ω, hω1, hodd⟩ := exists_unit_odd_order_ne_one hK hn'
  obtain ⟨b, hb, hbr, hnf⟩ :=
    natural_sl2_borel_element ω hω1 (orderOf ω) (pow_orderOf_eq_one ω) hπ S
  exact ⟨b, hb, orderOf ω, hodd, hbr, hnf⟩

theorem natfree_sz {L : Subgroup (MulAut W)} {V C : Subgroup W} {f : ℕ}
    (h : BinaryNaturalSz L V (V ⊓ C) f) (S : Sylow 2 ↥L) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ V, ((b : MulAut W) u) * u⁻¹ ∈ V ⊓ C → u ∈ V ⊓ C := by
  obtain ⟨a, ha1, hf, K, _, _, hK, π, hπ⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  obtain ⟨l, hl1, hodd⟩ := exists_unit_odd_order_ne_one hK (by omega : 2 ≤ f)
  obtain ⟨b, hb, hbr, hnf⟩ :=
    natural_sz_borel_element hK' l hl1 (orderOf l) (pow_orderOf_eq_one l) hπ S
  exact ⟨b, hb, orderOf l, hodd, hbr, hnf⟩

theorem exists_natfree_of_modFiveA {Mp L₀ : Subgroup (MulAut W)}
    {V : Subgroup W} {n : ℕ} (hn3 : 3 ≤ n) (hshape : IsPSL 2 2 n ↥L₀ ∨ IsSz n ↥L₀)
    (hOrth : ¬ ∃ a, 1 ≤ a ∧ BinaryOrthogonalFour L₀ V (V ⊓ fixV Mp) a)
    (hA : ModFiveA Mp L₀ V) (S : Sylow 2 ↥L₀) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L₀) : Set ↥L₀), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ commV L₀, ((b : MulAut W) u) * u⁻¹ ∈ commV L₀ ⊓ fixV Mp → u ∈ fixV Mp := by
  obtain ⟨hcomm, h⟩ := hA
  have h504 := le_card_of_psl2_or_sz hn3 hshape
  rw [hcomm]
  rcases h with ⟨n', hn'⟩ | h3 | ⟨f, hf⟩ | ⟨a, ha1, ha⟩ | h5
  · obtain ⟨b, hb, r, hr, hbr, hnf⟩ := natfree_sl2_of_big (by omega) hn' S
    exact ⟨b, hb, r, hr, hbr, fun u hu hb' => (hnf u hu hb').2⟩
  · exact absurd (card_le_168_of_natural_sl3 h3) (by omega)
  · obtain ⟨b, hb, r, hr, hbr, hnf⟩ := natfree_sz hf S
    exact ⟨b, hb, r, hr, hbr, fun u hu hb' => (hnf u hu hb').2⟩
  · exact absurd ⟨a, ha1, ha⟩ hOrth
  · exact absurd (card_le_sixty_of_alternating_five h5) (by omega)

theorem exists_natfree_of_D321Three {Mp L₀ : Subgroup (MulAut W)}
    (hLMp : L₀ ≤ Mp) (h504 : 504 ≤ Nat.card ↥L₀) (h : D321Three Mp L₀)
    (S : Sylow 2 ↥L₀) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L₀) : Set ↥L₀), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ commV L₀, ((b : MulAut W) u) * u⁻¹ ∈ commV L₀ ⊓ fixV Mp → u ∈ fixV Mp := by
  obtain ⟨n', hpsl, K, _, _, hK, I, π, hZI, hind, hsup, hR⟩ := h
  have hn3 : 3 ≤ n' := by
    obtain ⟨h1, hc⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hpsl
    by_contra hlt
    have : n' ≤ 2 := by omega
    rw [hc] at h504
    interval_cases n' <;> simp [Vol2.Ch11.SecA.oSL2] at h504
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨ω, hω1, hodd⟩ := exists_unit_odd_order_ne_one hK (by omega)
  obtain ⟨b, hb, hbr, hnf⟩ := natural_sl2_borel_element_family ω hω1 (orderOf ω)
    (pow_orderOf_eq_one ω) (hR 0).1 hR S
  refine ⟨b, hb, orderOf ω, hodd, hbr, ?_⟩
  intro a ha hba
  set Z : Subgroup W := commV L₀ ⊓ fixV Mp with hZ
  have hsup2 : (⨆ i, I i) = I 0 ⊔ I 1 := by
    refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  rw [← hsup, hsup2] at ha
  obtain ⟨z, hz, y, hy, rfl⟩ := Subgroup.mem_sup.mp ha
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Subgroup.mem_sup.mp hy
  have hbz : ((b : MulAut W)) z = z := hz.2 (b : MulAut W) (hLMp b.2)
  have hinv : ∀ i, ∀ u ∈ I i, ((b : MulAut W)) u ∈ I i := fun i u hu =>
    (hR i).2.2.2.1 b u hu
  set y₀ : W := (b : MulAut W) x₀ * x₀⁻¹ with hy₀
  set y₁ : W := (b : MulAut W) x₁ * x₁⁻¹ with hy₁
  have hy₀I : y₀ ∈ I 0 := (I 0).mul_mem (hinv 0 x₀ hx₀) ((I 0).inv_mem hx₀)
  have hy₁I : y₁ ∈ I 1 := (I 1).mul_mem (hinv 1 x₁ hx₁) ((I 1).inv_mem hx₁)
  have hprod : y₀ * y₁ ∈ Z := by
    have e : (b : MulAut W) (z * (x₀ * x₁)) * (z * (x₀ * x₁))⁻¹ = y₀ * y₁ := by
      rw [map_mul, map_mul, hbz]
      apply Additive.ofMul.injective
      simp only [hy₀, hy₁, ofMul_mul, ofMul_inv]
      abel
    rw [← e]
    exact hba
  have hy₀Z : y₀ ∈ Z := by
    have hmem : y₀ ∈ I 0 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) := by
      refine ⟨hy₀I, ?_⟩
      have e : y₀ = (y₀ * y₁) * y₁⁻¹ := by group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hprod) (Subgroup.mem_sup_right ?_)
      refine Subgroup.inv_mem _ ?_
      exact Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (by decide) hy₁I)
    rw [hind 0] at hmem
    exact hmem
  have hy₁Z : y₁ ∈ Z := by
    have hmem : y₁ ∈ I 1 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 1), I j) := by
      refine ⟨hy₁I, ?_⟩
      have e : y₁ = (y₀ * y₁) * y₀⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hprod) (Subgroup.mem_sup_right ?_)
      refine Subgroup.inv_mem _ ?_
      exact Subgroup.mem_iSup_of_mem 0 (Subgroup.mem_iSup_of_mem (by decide) hy₀I)
    rw [hind 1] at hmem
    exact hmem
  have hx₀Z : x₀ ∈ Z := hnf 0 x₀ hx₀ hy₀Z
  have hx₁Z : x₁ ∈ Z := hnf 1 x₁ hx₁ hy₁Z
  exact (fixV Mp).mul_mem hz.2 ((fixV Mp).mul_mem hx₀Z.2 hx₁Z.2)

end CFSG.Quasithin
