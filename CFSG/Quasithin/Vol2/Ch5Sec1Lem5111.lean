module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_1_11_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D : Subgroup G) (n : ℕ), Hyp5_1_8 G T M L H n →
    IsNotation5_1_9 T M L H B D → IsLieRankTwoK T H →
      (∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
          pCoreOf 2 (M ⊓ H) ≤ Subgroup.normalizer (P : Set G)) ∨
        (LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 ∧
          (oTwoUpper H ⊔ pCoreOf 2 H).relIndex (oTwoUpper H ⊔ pCoreOf 2 (M ⊓ H)) = 2 ∧
          E2.IsDiagramNontrivial (pCoreOf 2 (M ⊓ H)) (oTwoUpper H) (T ⊓ oTwoUpper H))

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem pCoreOf_inf_le (h : Hyp5_0_1 G T M L n) {H : Subgroup G} (hTH : T ≤ H) :
    pCoreOf 2 (M ⊓ H) ≤ T :=
  F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf (le_inf h.T_le hTH))

theorem inf_L_eq (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    {H : Subgroup G} (hH : IsHStar T M H) : pCoreOf 2 (M ⊓ H) ⊓ L = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm (inf_le_inf_right L (h.pCoreOf_inf_le hH.1.1))
  refine le_inf ?_ inf_le_right
  have hN : M ⊓ H ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [inf_comm]
    exact h.inf_le_normalizer_inf h331 hR hH
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans (le_inf h.T_le hH.1.1)) hN
    (h.sylow.1.to_le inf_le_left)

end Hyp5_0_1

namespace Hyp5_1_8

variable {G : Type} [Group G] [Finite G] {T M L H : Subgroup G} {n : ℕ}

theorem borel_eq (hyp : Hyp5_1_8 G T M L H n)
    (hBorel : E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H)) :
    M ⊓ oTwoUpper H =
      oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨S₀, hS₀, hMK⟩ := hBorel
  have hTKM : T ⊓ oTwoUpper H ≤ M ⊓ oTwoUpper H := inf_le_inf_right _ h.T_le
  have hS₀MK : S₀ ≤ M ⊓ oTwoUpper H := by
    rw [hMK]
    exact le_inf hS₀.1 Subgroup.le_normalizer
  have hMKS : M ⊓ oTwoUpper H ≤ Subgroup.normalizer (S₀ : Set G) := by
    rw [hMK]
    exact inf_le_right
  have hTsyl : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
    A4.isSylowTwoOf_mono hTK hTKM inf_le_right
  have hS₀O : S₀ ≤ pCoreOf 2 (M ⊓ oTwoUpper H) :=
    le_pCoreOf_of_le_normalizer 2 hS₀MK hMKS hS₀.2.1
  have hS₀T : S₀ ≤ T ⊓ oTwoUpper H := hS₀O.trans (F7.isSylowTwoOf_pCoreOf_le hTsyl)
  have hS₀eq : T ⊓ oTwoUpper H = S₀ := eq_of_isSylowTwoOf_of_le hS₀ hS₀T inf_le_right hTK.2.1
  rw [hMK, hS₀eq]

theorem inf_oTwoUpper_eq (hyp : Hyp5_1_8 G T M L H n)
    (hBorel : E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H)) :
    pCoreOf 2 (M ⊓ H) ⊓ oTwoUpper H = T ⊓ oTwoUpper H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hMK := hyp.borel_eq hBorel
  apply le_antisymm (inf_le_inf_right _ (h.pCoreOf_inf_le hyp.hStar.1.1))
  refine le_inf ?_ inf_le_right
  have hTKM : T ⊓ oTwoUpper H ≤ M ⊓ oTwoUpper H := inf_le_inf_right _ h.T_le
  have hMKN :
      M ⊓ oTwoUpper H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [hMK]
    exact inf_le_right
  have hTsyl : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
    A4.isSylowTwoOf_mono hTK hTKM inf_le_right
  have hO : pCoreOf 2 (M ⊓ oTwoUpper H) = T ⊓ oTwoUpper H :=
    le_antisymm (F7.isSylowTwoOf_pCoreOf_le hTsyl)
      (le_pCoreOf_of_le_normalizer 2 hTKM hMKN hTK.2.1)
  have hMHN : M ⊓ H ≤ Subgroup.normalizer ((M ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans (le_normalizer_oTwoUpper H))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hMHT : M ⊓ H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hO]
    exact hMHN.trans (normalizer_le_normalizer_pCoreOf 2 _)
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans (le_inf h.T_le hyp.hStar.1.1)) hMHT
    (h.sylow.1.to_le inf_le_left)

end Hyp5_1_8

theorem stmt5_1_11_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (h510 : Stmt5_1_10)
    (h3 : Stmt5_1_11_three) : Stmt5_1_11 := by
  intro G _ _ T M L H B D n hyp hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left h.sup_le_normalizer
  obtain ⟨k, -, hBorel, -⟩ := h510 G T M L H B D n hyp hN
  refine ⟨?_, ?_, h3 G T M L H B D n hyp hN⟩
  · rw [hyp.inf_oTwoUpper_eq hBorel]
    exact hTK
  · rw [h.inf_L_eq h331 hR hyp.hStar]
    exact hSL

end CFSG.Quasithin.H13
