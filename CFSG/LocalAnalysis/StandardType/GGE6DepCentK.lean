module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKClassForm

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem fixS_all : ∀ v : Vec6, (∀ i : Fin 5, (gS i).mulVec v = v) →
    v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by decide +kernel

private theorem xx_eq_single : (xx : Vec6) = Pi.single 5 1 := by decide +kernel

private theorem vec_eq_smul_xs_add_smul_xx : ∀ u : Vec6,
    u 0 = 0 → u 1 = 0 → u 2 = 0 → u 3 = 0 → u = u 4 • xs + u 5 • xx := by
  decide +kernel

private theorem three_smul_xx : (3 : ℕ) • (xx : Vec6) = 0 := by decide +kernel

private theorem zmod3_ne_zero : ∀ w : ZMod 3, w ≠ 0 → w = 1 ∨ w = 2 := by decide +kernel

private theorem smul_xs_xx (a d c : ZMod 3) :
    a • (xs : Vec6) + d • xx + (-a) • (xs + c • xx) = (d - a * c) • xx := by
  funext j
  fin_cases j <;> simp [xs, xx]
  all_goals
    first
      | exact add_neg_cancel _
      | rw [sub_eq_add_neg]

theorem ggE6Dep_centK {Bs K : Subgroup G} {x y : G} (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    {ι : Additive ↥Bs ≃+ Vec6} (hι : ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1)
    {c : ZMod 3} (hy : ι (Additive.ofMul ⟨y, hyBs⟩) = xs + c • xx)
    (hS : ∀ i : Fin 5, ∃ φ ∈ ggAutomizer K Bs, ActsAs ι φ (gS i))
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G))
    (hxK : x ∉ Subgroup.centralizer (K : Set G)) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hyCent : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  have hle1 : Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.zpowers_le]
    exact ⟨hyBs, hyCent⟩
  have hfix : ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (K : Set G) →
      ∀ φ ∈ ggAutomizer K Bs, φ b = b := by
    intro b hb φ hφ
    have hsub : ggInduced K Bs ⊆
        (MulAction.stabilizer (MulAut ↥Bs) b : Set (MulAut ↥Bs)) := by
      rintro ψ ⟨n, hnK, _hnN, hnψ⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      apply Subtype.ext
      rw [hnψ]
      have hcomm : n * (b : G) = (b : G) * n :=
        Subgroup.mem_centralizer_iff.mp hb n hnK
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : φ ∈ MulAction.stabilizer (MulAut ↥Bs) b :=
      (Subgroup.closure_le (MulAction.stabilizer (MulAut ↥Bs) b)).mpr hsub
        (show φ ∈ Subgroup.closure (ggInduced K Bs) from hφ)
    simpa [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hmem
  have hfixu : ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (K : Set G) →
      ∀ i : Fin 5, (gS i).mulVec (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
    intro b hb i
    obtain ⟨φ, hφA, hφS⟩ := hS i
    have hφfix : φ b = b := hfix b hb φ hφA
    have h := hφS b
    rw [hφfix] at h
    exact h.symm
  have hle2 : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
    intro b hb
    obtain ⟨hbBs, hbK⟩ := Subgroup.mem_inf.mp hb
    let β : ↥Bs := ⟨b, hbBs⟩
    let γ : ↥Bs := ⟨y, hyBs⟩
    let γx : ↥Bs := ⟨x, hxBs⟩
    have hγy : ι (Additive.ofMul γ) = xs + c • xx := hy
    have hγx : ι (Additive.ofMul γx) = Pi.single 5 1 := hι
    have hxx : (xx : Vec6) = ι (Additive.ofMul γx) := by
      rw [xx_eq_single]
      exact hι.symm
    have hu_fixed : ∀ i : Fin 5, (gS i).mulVec (ι (Additive.ofMul β)) = ι (Additive.ofMul β) :=
      hfixu β (show (β : G) ∈ Subgroup.centralizer (K : Set G) from hbK)
    obtain ⟨hu0, hu1, hu2, hu3⟩ := fixS_all (ι (Additive.ofMul β)) hu_fixed
    have hu : ι (Additive.ofMul β) =
        (ι (Additive.ofMul β)) 4 • xs + (ι (Additive.ofMul β)) 5 • xx :=
      vec_eq_smul_xs_add_smul_xx _ hu0 hu1 hu2 hu3
    let a : ZMod 3 := (ι (Additive.ofMul β)) 4
    let d : ZMod 3 := (ι (Additive.ofMul β)) 5
    let z : ℤ := -(a.val : ℤ)
    let β' : ↥Bs := β * γ ^ z
    have hβ'cent : (β' : G) ∈ Subgroup.centralizer (K : Set G) := by
      have hcoe : (β' : G) = (β : G) * (γ : G) ^ z := by
        simp [β', Subgroup.coe_mul, Subgroup.coe_zpow]
      rw [hcoe]
      exact Subgroup.mul_mem _ (show (β : G) ∈ Subgroup.centralizer (K : Set G) from hbK)
        (Subgroup.zpow_mem _ hyCent z)
    have hβ'of : (Additive.ofMul β' : Additive ↥Bs) =
        Additive.ofMul β + z • Additive.ofMul γ := by
      rw [show β' = β * γ ^ z from rfl, ofMul_mul, ofMul_zpow]
    have hz : ((z : ℤ) : ZMod 3) = -a := by
      dsimp [z]
      rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hcoorde : ι (Additive.ofMul β') = (d - a * c) • xx := by
      have hsmul : z • ι (Additive.ofMul γ) = (-a) • (xs + c • xx) := by
        rw [hγy, ← Int.cast_smul_eq_zsmul (ZMod 3), hz]
      calc
        ι (Additive.ofMul β')
            = ι (Additive.ofMul β + z • Additive.ofMul γ) := by rw [hβ'of]
        _ = ι (Additive.ofMul β) + z • ι (Additive.ofMul γ) := by rw [map_add, map_zsmul]
        _ = (a • xs + d • xx) + (-a) • (xs + c • xx) := by
              rw [hsmul, show ι (Additive.ofMul β) = a • xs + d • xx from hu]
        _ = (d - a * c) • xx := by
              show a • xs + d • xx + (-a) • (xs + c • xx) = (d - a * c) • xx
              exact smul_xs_xx a d c
    have hx3 : x ^ 3 = 1 := by
      have h3 : (3 : ℕ) • Additive.ofMul γx = (0 : Additive ↥Bs) := by
        apply ι.injective
        rw [map_nsmul, map_zero, hγx, ← xx_eq_single, three_smul_xx]
      have hof : Additive.ofMul (γx ^ 3) = (0 : Additive ↥Bs) := by
        rw [ofMul_pow, h3]
      have hγx3 : γx ^ 3 = 1 := by
        rw [← ofMul_eq_zero]
        exact hof
      simpa [Subgroup.coe_pow] using Subtype.ext_iff.mp hγx3
    have hwzero : d - a * c = 0 := by
      by_contra hw
      have hw12 : d - a * c = 1 ∨ d - a * c = 2 := zmod3_ne_zero _ hw
      have hxCent : x ∈ Subgroup.centralizer (K : Set G) := by
        rcases hw12 with hw1 | hw2
        · have hβ'x : β' = γx := by
            apply Additive.ofMul.injective
            apply ι.injective
            rw [hcoorde, hw1]
            simpa using hxx
          have hxβ' : x = (β' : G) := by
            rw [hβ'x]
          rw [hxβ']
          exact hβ'cent
        · have hβ'x2 : β' = γx ^ 2 := by
            apply Additive.ofMul.injective
            apply ι.injective
            have hpow : (2 : ZMod 3) • ι (Additive.ofMul γx) = ι (Additive.ofMul (γx ^ 2)) := by
              change ((2 : ℕ) : ZMod 3) • ι (Additive.ofMul γx) = ι (Additive.ofMul (γx ^ 2))
              rw [Nat.cast_smul_eq_nsmul, ← map_nsmul ι 2 (Additive.ofMul γx), ← ofMul_pow 2 γx]
            rw [hcoorde, hw2, hxx, ← hpow]
          have hx2Cent : x ^ 2 ∈ Subgroup.centralizer (K : Set G) := by
            have hc : (β' : G) = x ^ 2 := by
              rw [hβ'x2]
              simp [Subgroup.coe_pow, γx]
            rw [← hc]
            exact hβ'cent
          have hx4 : x ^ 4 = x := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hx3, one_mul]
          have hxeq : x = (x ^ 2) ^ 2 := by
            rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num, hx4]
          rw [hxeq]
          exact Subgroup.pow_mem _ hx2Cent 2
      exact hxK hxCent
    have hβ'one : β' = 1 := by
      rw [← ofMul_eq_zero]
      apply ι.injective
      rw [hcoorde, hwzero, map_zero]
      simp
    rw [Subgroup.mem_zpowers_iff]
    have hb_eq : b = y ^ (a.val : ℤ) := by
      have h1 : b * y ^ z = 1 := by
        have hcoe : (β' : G) = b * y ^ z := by
          simp [β', β, γ, Subgroup.coe_mul, Subgroup.coe_zpow]
        rw [← hcoe, hβ'one]
        rfl
      have h2 : b = (y ^ z)⁻¹ := by
        calc b = b * y ^ z * (y ^ z)⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
          _ = 1 * (y ^ z)⁻¹ := by rw [h1]
          _ = (y ^ z)⁻¹ := one_mul _
      rw [h2, ← zpow_neg]
      congr 1
      dsimp [z]
      rw [neg_neg]
    refine ⟨(a.val : ℤ), ?_⟩
    rw [hb_eq]
  exact le_antisymm hle2 hle1

end E6Dep

end CFSG.StandardType

end
