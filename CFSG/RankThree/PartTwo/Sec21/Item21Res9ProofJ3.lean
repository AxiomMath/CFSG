module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofLift
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.RankThree.Asc83Table.E27

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof

open Subgroup CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.J3
open scoped Matrix

namespace J3

section Basis

variable {L : Type*} [Group L] {n : ℕ} {x : Fin n → L} (hx : ∀ i, x i ^ 3 = 1)
  (hc : ∀ i j, Commute (x i) (x j)) (hinj : Function.Injective (basisProd x))
include hx hc hinj

theorem conj_basisProd (g : normalizer (closure (Set.range x) : Set L)) (v : Fin n → ZMod 3) :
    (g : L) * basisProd x v * (g : L)⁻¹ =
      basisProd x (((rho (basisEquiv hx hc hinj) g : GL (Fin n) (ZMod 3)) :
        Matrix (Fin n) (Fin n) (ZMod 3)) *ᵥ v) := by
  rw [coe_rho, conjMat, LinearMap.toMatrix'_mulVec]
  change _ = basisProd x (conjAdd (basisEquiv hx hc hinj) g v)
  rw [← coe_basisEquiv hx hc hinj (conjAdd _ g v), conjAdd_apply, ofAdd_toAdd,
    MulEquiv.apply_symm_apply, ← coe_basisEquiv hx hc hinj v]
  rfl

theorem basisProd_add (v w : Fin n → ZMod 3) :
    basisProd x (v + w) = basisProd x v * basisProd x w := by
  rw [← coe_basisEquiv hx hc hinj, ← coe_basisEquiv hx hc hinj, ← coe_basisEquiv hx hc hinj,
    ofAdd_add, map_mul, Subgroup.coe_mul]

end Basis

@[expose] def vJ : Fin 3 → ZMod 3 := ![1, 2, 2]

theorem t33C_vJ : ((t33C : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ vJ = -vJ := by
  decide +kernel

theorem t33A_vJ : ((t33A : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ vJ ≠ vJ := by
  decide +kernel

theorem three_vJ : vJ + vJ + vJ = 0 := by decide +kernel

theorem neg_vJ_add : -vJ + vJ = 0 := by decide +kernel

section Elements


@[expose] noncomputable def uJ : CFSG.Sporadic.J3.J D := basisProd x vJ

theorem uJ_cube : uJ ^ 3 = 1 := by
  rw [uJ, pow_succ, pow_two, ← basisProd_add x_pow x_comm x_inj,
    ← basisProd_add x_pow x_comm x_inj, three_vJ]
  simp [basisProd]

theorem h2_conj : h 2 * uJ * (h 2)⁻¹ = uJ⁻¹ := by
  have e := conj_basisProd x_pow x_comm x_inj ⟨h 2, mem_normalizer_h x_pow x_comm h_conj 2⟩ vJ
  rw [rho_h x_pow x_comm x_inj h_conj 2] at e
  change h 2 * uJ * (h 2)⁻¹ = _ at e
  rw [e, show (t33 2 : GL (Fin 3) (ZMod 3)) = t33C from rfl, t33C_vJ]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [uJ, ← basisProd_add x_pow x_comm x_inj, neg_vJ_add]
  simp [basisProd]

theorem h0_ne : h 0 * uJ ≠ uJ * h 0 := by
  intro h1
  have e := conj_basisProd x_pow x_comm x_inj ⟨h 0, mem_normalizer_h x_pow x_comm h_conj 0⟩ vJ
  rw [rho_h x_pow x_comm x_inj h_conj 0] at e
  change h 0 * uJ * (h 0)⁻¹ = _ at e
  rw [h1, mul_inv_cancel_right, show (t33 0 : GL (Fin 3) (ZMod 3)) = t33A from rfl] at e
  exact t33A_vJ (x_inj e).symm

theorem hb_pow_nine {cert : CFSG.RankThree.Asc83Table.Native.J3Cert}
    (hJ : CFSG.RankThree.Asc83Table.Native.j3Check CFSG.Blueprint.NativeSporadic.J3Seed1
      CFSG.Blueprint.NativeSporadic.J3Seed2 D.pts D.n cert = true)
    (hrh0 : CFSG.RankThree.Asc83Table.Native.MFact.ord (rhF cert 0) 9 ∈ cert.facts) :
    hb hJ 0 ^ 9 = 1 := by
  rw [hb, X, ← map_pow, regUnit_pow (CFSG.SectionRank.spec2fr 80) (mcert_ok hJ) (C := cert.mcert)
    hrh0, map_one]

theorem h0_pow_nine : h 0 ^ 9 = 1 := hb_pow_nine CFSG.RankThree.Asc83Table.J3.j3_check hrh.1

theorem isPGroup_closure_uJ :
    IsPGroup 3 (Subgroup.closure ({uJ, h 0} : Set (CFSG.Sporadic.J3.J D))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB : IsPGroup 3 (Subgroup.closure (Set.range x)) :=
    IsPGroup.of_card (n := 3) (by rw [card_basis x_pow x_comm x_inj]; norm_num)
  rw [Set.pair_comm]
  have h9 : h 0 ^ 3 ^ 2 = 1 := by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h0_pow_nine
  exact isPGroup_closure_pair h9 hB (basisProd_mem x_pow x_comm vJ) fun n hn =>
    (mem_normalizer_iff.mp (mem_normalizer_h x_pow x_comm h_conj 0) n).mp hn

theorem realPair_J : RealPair (CFSG.Sporadic.J3.J D) :=
  ⟨_, _, _, uJ_cube, h2_conj, fun h1 => h0_ne h1.symm, isPGroup_closure_uJ⟩

end Elements

end J3

theorem exists_noncentral_J3
    {X : Type} [Group X] [Finite X] (e : X ⧸ center X ≃* CFSG.Blueprint.NativeSporadic.J3)
    (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s :=
  exists_noncentral_of_realPair (RealPair.of_mulEquiv (H := X ⧸ center X)
    (H' := CFSG.Blueprint.NativeSporadic.J3) e
    (RealPair.of_mulEquiv (H := CFSG.Blueprint.NativeSporadic.J3)
      (H' := CFSG.Sporadic.J3.J D) φ J3.realPair_J)) S

end CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof
