module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2L2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Z2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Main

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem false_of_lin2_block [Finite G] {I S K P Zs Mc X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hS : IsSylowTwoOf S I) (hKI : K ≤ I)
    (hPK : P ≤ K) (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Zs, k * z = z * k)
    (hZS : ∀ z ∈ Zs, z ∈ S ∧ z ^ 2 = 1 ∧ ∀ s ∈ S, z * s = s * z)
    (hMc : ∀ g : G, (∀ z ∈ Zs, g * z = z * g) → g ∈ Mc) (hKsolv : Group.IsSolvable ↥K)
    (hP1 : ∀ Y : Subgroup G, GenByOrderThree Y → Y ≤ I →
      I ≤ Subgroup.normalizer (Y : Set G) → Y ≤ Mc → ¬ Y ≤ K → quasithinV2 Y = ⊥)
    {n : ℕ} (hn : 1 < n) (hX : IsBlock2 I X) (hlin : IsLin2Type X n) : False := by
  have hconj : ∀ g ∈ I, IsBlock2 I (conjByElt g X) ∧ IsLin2Type (conjByElt g X) n := fun g hg =>
    ⟨IsBlock2.conjByElt_of_mem hX hg, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj g)⟩
  have hcen : ∀ g ∈ I, ∀ y ∈ conjByElt g X, ∀ z ∈ Zs, y * z = z * y := fun g hg y hy z hz =>
    commute_block_of_central hC19 hchar hrank hS hKI hPK hP hP9 hKZ hZS (hconj g hg).1
      (Or.inr ⟨n, hn, (hconj g hg).2⟩) z hz y hy
  have hmemc : ∀ g ∈ I, ∀ x ∈ X, g * x * g⁻¹ ∈ conjByElt g X := fun g hg x hx => by
    rw [mem_conjByElt]
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [this]
    exact hx
  set X₀ := conjClosure X I with hX₀
  have hX₀I : X₀ ≤ I := conjClosure_le fun g hg x hx =>
    I.mul_mem (I.mul_mem hg (hX.2.1 hx)) (I.inv_mem hg)
  have hIN : I ≤ Subgroup.normalizer (X₀ : Set G) := le_normalizer_conjClosure X I
  have hXX₀ : X ≤ X₀ := le_conjClosure X I
  have hX₀cent : X₀ ≤ Subgroup.centralizer (Zs : Set G) := conjClosure_le fun g hg x hx =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => (hcen g hg _ (hmemc g hg x hx) z hz).symm
  have hX₀Mc : X₀ ≤ Mc := fun y hy =>
    hMc y fun z hz => (Subgroup.mem_centralizer_iff.mp (hX₀cent hy) z hz).symm
  have hX₀N : X₀ ≤ Subgroup.normalizer (X : Set G) := conjClosure_le fun g hg x hx => by
    by_cases hgX : g ∈ Subgroup.normalizer (X : Set G)
    · exact Subgroup.le_normalizer ((Subgroup.mem_normalizer_iff.mp hgX x).mp hx)
    · have hne : X ≠ conjByElt g X := fun h =>
        hgX (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
      have hcm := mul_comm_of_commutator_bot (hC19 I X (conjByElt g X) hchar hX (hconj g hg).1 hne)
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
      exact hcm a ha _ (hmemc g hg x hx)
  have hgen : GenByOrderThree X₀ := by
    refine conjClosure_le fun g hg x hx => ?_
    have hY : conjByElt g X ≤ X₀ := fun y hy => by
      have := mem_conjClosure hg (show g⁻¹ * y * g ∈ X from mem_conjByElt.mp hy)
      simpa [mul_assoc] using this
    have hYgen := genByOrderThree_of_lin2 (hconj g hg).1.1 hn (hconj g hg).2
    exact closure_orderThree_mono hY (hYgen (hmemc g hg x hx))
  have hXK : ¬ X₀ ≤ K := by
    intro h
    have : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hXX₀.trans h))
    exact Lin2.OddRank.not_isSolvable hlin hn this
  have hV := hP1 X₀ hgen hX₀I hIN hX₀Mc hXK
  rw [quasithinV2_eq_commutator] at hV
  have hQ₂ : pCoreOf 2 X ≤ pCoreOf 2 X₀ :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 X).trans hXX₀)
      (hX₀N.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  have hUz : blockU X ≤ z2Of X₀ := by
    intro u hu
    have huQ : u ∈ blockQ X := C1.blockU_le_blockQ hX.1 hu
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hQ₂ huQ, ?_⟩, C1.blockU_sq hX.1 u hu⟩
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hqX₀ : q ∈ X₀ := pCoreOf_le 2 X₀ hq
    exact (C1.commute_blockU_of_mem hX.1 (hX₀N hqX₀)
      (C1.exists_pow_eq_one_of_isPGroup (pCoreOf_isPGroup 2 X₀) hq)
      (fun l hl => C1.commutator_mem_blockQ_of_mem_pCoreOf hXX₀ hX₀N hq hl) u hu).symm
  have hUU : blockU X ≤ ⁅z2Of X₀, X₀⁆ :=
    calc blockU X = ⁅blockU X, X⁆ := (C1.commutator_blockU hX.1).symm
      _ ≤ ⁅z2Of X₀, X₀⁆ := Subgroup.commutator_mono hUz hXX₀
  rw [hV] at hUU
  have hZU : blockZ X < blockU X := hX.1.2.2.2.2.1
  have hbot : blockU X = ⊥ := le_bot_iff.mp hUU
  exact (not_lt_of_ge (hbot ▸ bot_le : blockU X ≤ blockZ X)) hZU

end CFSG.Quasithin.S15223
