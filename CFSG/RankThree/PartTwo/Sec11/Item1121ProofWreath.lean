module

public import CFSG.RankThree.PartTwo.Sec11.WreathFacts

public section

namespace CFSG.RankThree.PartTwo.Sec11

open scoped commutatorElement

namespace Item1121Proof

theorem pow_three_zmod : ∀ q : Multiplicative (ZMod 3), q ^ 3 = 1 := by
  decide

theorem eq_or_eq_mul_self_of_ne_one :
    ∀ q q' : Multiplicative (ZMod 3), q ≠ 1 → q' ≠ 1 → q' = q ∨ q' = q * q := by
  decide

theorem right_pow_three (w : W33) : (w ^ 3).right = 1 := by
  have h : (w ^ 3).right = w.right ^ 3 := map_pow RegularWreathProduct.rightHom w 3
  rw [h, pow_three_zmod]

theorem pow_nine_eq_one (w : W33) : w ^ 9 = 1 := by
  rw [show 9 = 3 * 3 from rfl, pow_mul]
  exact pow_three_eq_one_of_right_eq_one (right_pow_three w)

theorem right_mul (u v : W33) : (u * v).right = u.right * v.right := rfl

theorem mem_zpowers_wreathZ_of_commute {u γ : W33} (hu : u.right = 1) (hγ : γ.right ≠ 1)
    (hc : u * γ = γ * u) : u ∈ Subgroup.zpowers wreathZ := by
  obtain ⟨γ', hγ't, hc'⟩ : ∃ γ' : W33, γ'.right = wreathT ∧ u * γ' = γ' * u := by
    by_cases ht : γ.right = wreathT
    · exact ⟨γ, ht, hc⟩
    · refine ⟨γ⁻¹, inv_eq_wreathT_of_ne _ hγ ht, ?_⟩
      calc u * γ⁻¹ = γ⁻¹ * (γ * u) * γ⁻¹ := by group
        _ = γ⁻¹ * (u * γ) * γ⁻¹ := by rw [hc]
        _ = γ⁻¹ * u := by group
  obtain ⟨f, q⟩ := u
  obtain ⟨f₁, q₁⟩ := γ'
  change q = 1 at hu
  change q₁ = wreathT at hγ't
  subst hu hγ't
  rcases eq_of_commute_base f f₁ (congrArg RegularWreathProduct.left hc') with h | h | h
  · have e : (⟨f, 1⟩ : W33) = 1 := RegularWreathProduct.ext h rfl
    rw [e]
    exact Subgroup.one_mem _
  · have e : (⟨f, 1⟩ : W33) = wreathZ := RegularWreathProduct.ext h wreathZ_right.symm
    rw [e]
    exact Subgroup.mem_zpowers _
  · have e : (⟨f, 1⟩ : W33) = wreathZ⁻¹ := RegularWreathProduct.ext h wreathZ_inv_right.symm
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem wreathZ_pow_three : wreathZ ^ 3 = 1 :=
  pow_three_eq_one_of_right_eq_one wreathZ_right

theorem commute_wreathZ_left (w : W33) : wreathZ * w = w * wreathZ :=
  (Subgroup.mem_center_iff.mp wreathZ_mem_center w).symm

@[expose] def wreathSigma (f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3)) :
    Multiplicative (ZMod 3) :=
  f 1 * f wreathT * f wreathT⁻¹

theorem wreathSigma_eq_one_aux :
    ∀ (f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3)) (q : Multiplicative (ZMod 3)),
      q ≠ 1 → ((⟨f, q⟩ : W33) ^ 3).left = (1 : W33).left → wreathSigma f = 1 := by
  unfold wreathSigma
  decide

theorem wreathSigma_eq_one_of_pow_three {y : W33} (hq : y.right ≠ 1) (h3 : y ^ 3 = 1) :
    wreathSigma y.left = 1 :=
  wreathSigma_eq_one_aux y.left y.right hq (by rw [h3])

theorem wreathSigma_mul_inv :
    ∀ f f' : Multiplicative (ZMod 3) → Multiplicative (ZMod 3),
      wreathSigma (f * f'⁻¹) = wreathSigma f * (wreathSigma f')⁻¹ := by
  unfold wreathSigma
  decide

theorem exists_eq_of_wreathSigma_aux :
    ∀ f : Multiplicative (ZMod 3) → Multiplicative (ZMod 3), wreathSigma f = 1 →
      ∃ i j : Fin 3, (wreathK ^ (i : ℕ) * wreathZ ^ (j : ℕ)).left = f ∧
        (wreathK ^ (i : ℕ) * wreathZ ^ (j : ℕ)).right = 1 := by
  unfold wreathSigma
  decide

theorem mem_closure_of_wreathSigma_eq_one {y : W33} (hy : y.right = 1)
    (hσ : wreathSigma y.left = 1) : y ∈ Subgroup.closure {wreathK, wreathZ} := by
  obtain ⟨i, j, h1, h2⟩ := exists_eq_of_wreathSigma_aux y.left hσ
  have e : wreathK ^ (i : ℕ) * wreathZ ^ (j : ℕ) = y :=
    RegularWreathProduct.ext h1 (h2.trans hy.symm)
  rw [← e]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem closure_wreathK_wreathZ_le_commutator :
    Subgroup.closure {wreathK, wreathZ} ≤ ⁅(⊤ : Subgroup W33), ⊤⁆ := by
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem mul_inv_of_right_eq {y γ : W33} (h : y.right = γ.right) :
    (y * γ⁻¹).right = 1 ∧ (y * γ⁻¹).left = y.left * γ.left⁻¹ := by
  refine ⟨by simp [h], ?_⟩
  funext z
  simp [h]
  rfl

theorem mem_sup_zpowers_of_pow_three_eq_one {N : Subgroup W33}
    (hN : ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ N) {γ : W33} (hγ : γ.right ≠ 1) (hγ3 : γ ^ 3 = 1) {y : W33}
    (hy : y.right ≠ 1) (hy3 : y ^ 3 = 1) : y ∈ N ⊔ Subgroup.zpowers γ := by
  obtain ⟨γ', hγ'mem, hγ'r, hγ'3⟩ : ∃ γ' ∈ Subgroup.zpowers γ, γ'.right = y.right ∧
      γ' ^ 3 = 1 := by
    rcases eq_or_eq_mul_self_of_ne_one γ.right y.right hγ hy with h | h
    · exact ⟨γ, Subgroup.mem_zpowers γ, h.symm, hγ3⟩
    · refine ⟨γ * γ, Subgroup.mul_mem _ (Subgroup.mem_zpowers γ) (Subgroup.mem_zpowers γ),
        h.symm, ?_⟩
      rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hγ3, one_pow]
  obtain ⟨hq, hleft⟩ := mul_inv_of_right_eq hγ'r.symm
  have hσ : wreathSigma (y * γ'⁻¹).left = 1 := by
    rw [hleft, wreathSigma_mul_inv, wreathSigma_eq_one_of_pow_three hy hy3,
      wreathSigma_eq_one_of_pow_three (hγ'r ▸ hy) hγ'3]
    decide
  have hmem : y * γ'⁻¹ ∈ N :=
    hN (closure_wreathK_wreathZ_le_commutator (mem_closure_of_wreathSigma_eq_one hq hσ))
  have e : y = (y * γ'⁻¹) * γ' := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hγ'mem)

theorem wreathK_wreathZ_injective_aux :
    ∀ i j i' j' : Fin 3, (wreathK ^ (i : ℕ) * wreathZ ^ (j : ℕ)).left =
      (wreathK ^ (i' : ℕ) * wreathZ ^ (j' : ℕ)).left → i = i' ∧ j = j' := by
  decide

theorem nine_le_card_commutator : 9 ≤ Nat.card (⁅(⊤ : Subgroup W33), ⊤⁆ : Subgroup W33) := by
  have hK : wreathK ∈ ⁅(⊤ : Subgroup W33), ⊤⁆ :=
    closure_wreathK_wreathZ_le_commutator (Subgroup.subset_closure (by simp))
  have hZ : wreathZ ∈ ⁅(⊤ : Subgroup W33), ⊤⁆ :=
    closure_wreathK_wreathZ_le_commutator (Subgroup.subset_closure (by simp))
  let f : Fin 3 × Fin 3 → (⁅(⊤ : Subgroup W33), ⊤⁆ : Subgroup W33) := fun p =>
    ⟨wreathK ^ (p.1 : ℕ) * wreathZ ^ (p.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.pow_mem _ hK _) (Subgroup.pow_mem _ hZ _)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 := congrArg (fun w : (⁅(⊤ : Subgroup W33), ⊤⁆ : Subgroup W33) => (w : W33).left) h
    obtain ⟨hi, hj⟩ := wreathK_wreathZ_injective_aux i j i' j' h1
    rw [hi, hj]
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h
  omega

theorem commutator_le_of_normal_card_nine {N : Subgroup W33} (hN : N.Normal)
    (h9 : Nat.card N = 9) : ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardQ : Nat.card (W33 ⧸ N) = 3 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [card_wreath, h9] at h1
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    omega
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardQ).is_comm.comm
  rw [Subgroup.commutator_le]
  intro w _ w' _
  have h1 := hcomm (w : W33 ⧸ N) (w' : W33 ⧸ N)
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h1]
  group

theorem eq_of_normal_card_nine {N N' : Subgroup W33} (hN : N.Normal) (hN' : N'.Normal)
    (h9 : Nat.card N = 9) (h9' : Nat.card N' = 9) : N = N' := by
  have h1 := commutator_le_of_normal_card_nine hN h9
  have h2 := commutator_le_of_normal_card_nine hN' h9'
  have hc := nine_le_card_commutator
  have e1 : ⁅(⊤ : Subgroup W33), ⊤⁆ = N := Subgroup.eq_of_le_of_card_ge h1 (by omega)
  have e2 : ⁅(⊤ : Subgroup W33), ⊤⁆ = N' := Subgroup.eq_of_le_of_card_ge h2 (by omega)
  rw [← e1, ← e2]

end Item1121Proof

end CFSG.RankThree.PartTwo.Sec11
