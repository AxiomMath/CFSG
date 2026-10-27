module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NAbStep
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NAbAct
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NAbGL

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG.RankThree.Classical.GL3

variable {G : Type} [Group G] {Q L : Subgroup G} {b : G}

@[expose] def sevenTorsion (Q : Subgroup G) (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    Subgroup G where
  carrier := {x | x ∈ Q ∧ x ^ 7 = 1}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    rw [(show Commute x y from hab x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem Q, one_pow 7⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem sevenTorsion_eq (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hn : L ≤ Subgroup.normalizer (Q : Set G)) (hmin : NLeast Q L) :
    sevenTorsion Q hab = ⊥ ∨ sevenTorsion Q hab = Q :=
  hmin (sevenTorsion Q hab) (fun x hx => hx.1)
    (fun q hq r hr => by
      have h1 : q * r = r * q := hab q hq r hr.1
      have : q * r * q⁻¹ = r := by rw [h1]; group
      rw [this]; exact hr)
    (fun l hl r hr => ⟨conj_mem_of_normalizes hn hl hr.1, by
      rw [conj_pow, hr.2]; group⟩)

theorem orderOf_symm_eq_three {φ : L ≃* GL (Fin 3) (ZMod 2)} {u : GL (Fin 3) (ZMod 2)}
    (h1 : u ^ 3 = 1) (h2 : u ≠ 1) : orderOf (φ.symm u) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [MulEquiv.orderOf_eq]
  exact orderOf_eq_prime h1 h2

theorem nBase_abelian [Finite G] (h : NHyp Q L b) (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hmin : NLeast Q L) : Q ≤ Subgroup.centralizer (L : Set G) := by
  by_contra hnot
  obtain ⟨φ⟩ := h.iso
  haveI : Finite L := Finite.of_equiv _ φ.symm.toEquiv
  haveI : IsSimpleGroup L := by
    haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    exact φ.isSimpleGroup
  have hZ := inf_centralizer_eq_bot hab hmin hnot
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun x y => Subtype.ext (hab x x.2 y y.2) }
  letI act : DistribMulAction L (Additive Q) :=
    { smul := fun l a => Additive.ofMul
        (⟨l * (Additive.toMul a : Q) * l⁻¹, conj_mem_of_normalizes h.normalizes l.2
          (Additive.toMul a).2⟩ : Q)
      one_smul := fun a => Additive.toMul.injective (Subtype.ext (by
        change ((1 : L) : G) * ((Additive.toMul a : Q) : G) * ((1 : L) : G)⁻¹ = _
        simp))
      mul_smul := fun l l' a => Additive.toMul.injective (Subtype.ext (by
        change ((l * l' : L) : G) * ((Additive.toMul a : Q) : G) * ((l * l' : L) : G)⁻¹ =
          (l : G) * ((l' : G) * ((Additive.toMul a : Q) : G) * (l' : G)⁻¹) * (l : G)⁻¹
        simp [mul_assoc]))
      smul_zero := fun l => Additive.toMul.injective (Subtype.ext (by
        change (l : G) * ((1 : Q) : G) * (l : G)⁻¹ = _
        simp))
      smul_add := fun l a a' => Additive.toMul.injective (Subtype.ext (by
        change (l : G) * (((Additive.toMul a : Q) * (Additive.toMul a' : Q) : Q) : G) *
          (l : G)⁻¹ = (l * (Additive.toMul a : Q) * l⁻¹ : G) * (l * (Additive.toMul a' : Q) * l⁻¹)
        simp [mul_assoc])) }
  have hact : ∀ (l : L) (a : Additive Q),
      ((Additive.toMul (l • a) : Q) : G) = l * (Additive.toMul a : Q) * l⁻¹ := fun _ _ => rfl
  have hnorm : ∀ c : L, orderOf c = 3 → ∀ a : Additive Q, a + c • a + (c * c) • a = 0 := by
    intro c hc3 a
    have hc3' : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc3
    have hpow : (c : G) ^ 3 = 1 := by rw [← hc3']; exact pow_orderOf_eq_one _
    have e := norm_eq_one hab h.normalizes hZ c.2 hpow (cent_of_order_three h c.2 hc3')
      (Additive.toMul a).2
    rw [mul_smul]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_add, toMul_zero, Subgroup.coe_mul, Subgroup.coe_one, hact]
    exact e
  have hdich : (∀ d : Additive Q, 7 • d = 0 → d = 0) ∨ (∀ d : Additive Q, 7 • d = 0) := by
    rcases sevenTorsion_eq hab h.normalizes hmin with hR | hR
    · left
      intro d hd
      have hd' : ((Additive.toMul d : Q) : G) ^ 7 = 1 := by
        have := congrArg (fun z => ((Additive.toMul z : Q) : G)) hd
        simpa [toMul_nsmul] using this
      have hmem : ((Additive.toMul d : Q) : G) ∈ sevenTorsion Q hab :=
        ⟨(Additive.toMul d).2, hd'⟩
      rw [hR] at hmem
      apply Additive.toMul.injective
      exact Subtype.ext (by simpa using Subgroup.mem_bot.1 hmem)
    · right
      intro d
      have hmem : ((Additive.toMul d : Q) : G) ∈ sevenTorsion Q hab := by
        rw [hR]; exact (Additive.toMul d).2
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa [toMul_nsmul] using hmem.2
  have hs : ∃ s : L, s ≠ 1 ∧ ∀ a : Additive Q, s • a = a := by
    rcases hdich with h0 | h7
    · refine ⟨φ.symm frobS, fun heq => frobS_ne_one ?_, fun a => ?_⟩
      · simpa using congrArg φ heq
      · have key := frob21_seven_smul (A := Additive Q) (H := L) (σ := φ.symm frobS)
          (c := φ.symm frobX) (by rw [← map_pow, frobS_pow_seven, map_one])
          (by rw [← map_pow, ← map_mul, ← map_mul, frobS_mul_frobX])
          (fun i hi a => by
            have hcs : φ.symm frobX * (φ.symm frobS) ^ i = φ.symm (frobX * frobS ^ i) := by
              rw [map_mul, map_pow]
            have := hnorm (φ.symm frobX * (φ.symm frobS) ^ i) (by
              rw [hcs]
              exact orderOf_symm_eq_three (φ := φ) (frob_order_three i hi).1
                (frob_order_three i hi).2) a
            rwa [← sq] at this) a
        have h1 : 7 • (φ.symm frobS • a - a) = 0 := by rw [nsmul_sub, key, sub_self]
        exact sub_eq_zero.1 (h0 _ h1)
    · refine ⟨φ.symm klE1, fun heq => klE1_ne_one ?_, fun a => ?_⟩
      · simpa using congrArg φ heq
      · have key := a4_four_smul (A := Additive Q) (H := L) (c := φ.symm frobX)
          (e1 := φ.symm klE1) (e2 := φ.symm klE2) (e3 := φ.symm klE3)
          (by rw [← map_mul, klE1_mul_klE1, map_one])
          (by rw [← map_mul, klE1_mul_klE2])
          (by rw [← map_mul, klE1_mul_klE3])
          (by rw [← map_mul, ← map_pow, ← map_pow, ← map_mul, kl_sq_one])
          (by rw [← map_mul, ← map_pow, ← map_pow, ← map_mul, kl_sq_two])
          (by rw [← map_mul, ← map_pow, ← map_pow, ← map_mul, kl_sq_three])
          (fun a => by
            have := hnorm (φ.symm frobX) (by
              exact orderOf_symm_eq_three (φ := φ) frobX_pow_three frobX_ne_one) a
            rwa [← sq] at this)
          (fun a => by
            have := hnorm (φ.symm frobX * φ.symm klE1) (by
              rw [← map_mul]
              exact orderOf_symm_eq_three (φ := φ) kl_order_three_one.1 kl_order_three_one.2) a
            rwa [← sq] at this)
          (fun a => by
            have := hnorm (φ.symm frobX * φ.symm klE2) (by
              rw [← map_mul]
              exact orderOf_symm_eq_three (φ := φ) kl_order_three_two.1 kl_order_three_two.2) a
            rwa [← sq] at this)
          (fun a => by
            have := hnorm (φ.symm frobX * φ.symm klE3) (by
              rw [← map_mul]
              exact orderOf_symm_eq_three (φ := φ) kl_order_three_three.1
                kl_order_three_three.2) a
            rwa [← sq] at this) a
        have h4 : 4 • (φ.symm klE1 • a - a) = 0 := by rw [nsmul_sub, key, sub_self]
        have h7' := h7 (φ.symm klE1 • a - a)
        have h8 : (4 + 4) • (φ.symm klE1 • a - a) = 0 := by rw [add_nsmul, h4, add_zero]
        have h8' : (7 + 1) • (φ.symm klE1 • a - a) = 0 := h8
        rw [add_nsmul, h7', zero_add, one_nsmul] at h8'
        exact sub_eq_zero.1 h8'
  obtain ⟨s, hs1, hsa⟩ := hs
  refine hnot (le_centralizer_of_simple h.normalizes s.2 (fun h1 => hs1 (Subtype.ext h1)) ?_)
  intro x hx
  have := congrArg (fun z => ((Additive.toMul z : Q) : G)) (hsa (Additive.ofMul ⟨x, hx⟩))
  simp only [hact, toMul_ofMul] at this
  exact mul_inv_eq_iff_eq_mul.1 this

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

