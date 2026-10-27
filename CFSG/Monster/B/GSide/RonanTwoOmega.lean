module

public import CFSG.Monster.B.GSide.MuFourOmega

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisCert CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary

def muWit : Array ℕ :=
  #[15, 15, 15, 15, 15, 15, 15, 44, 15, 15, 15, 15, 44, 15, 15, 0, 15, 44, 44, 85, 44, 44, 15, 44,
    15, 15, 44, 15, 15, 44, 85, 85, 15, 0, 0, 15, 15, 15, 0, 15, 15, 44, 15, 0, 0, 44, 44, 85, 44,
    44, 85, 85, 85, 44, 15, 44, 85, 0, 0, 15, 15, 76, 85, 85, 85, 15, 33, 0, 0, 0, 0, 15, 33, 15,
    34, 15, 0, 0, 0, 15, 34, 44, 15, 34, 0, 0, 0, 15, 76, 85, 0, 0, 76, 76, 44, 76, 44, 44, 76,
    15, 15, 85, 85, 44, 44, 85, 0, 0, 0, 0, 34, 15, 33, 33, 15, 44, 44, 76, 33, 15, 85, 0, 0, 33,
    33, 33, 0, 0, 0, 0, 33, 0, 0, 0, 34, 34, 0, 33, 33, 34, 15, 44, 34, 34, 0, 0, 0, 0, 15, 34, 0,
    15, 0, 15, 15, 34, 0, 0, 44, 0, 34, 34, 0, 0, 0, 0, 0, 0, 43, 38, 0, 0, 0, 0, 33, 0, 33, 0, 0,
    0, 76, 0, 44, 0, 0, 44, 0, 0, 15, 15, 15, 15, 0, 43, 76, 33, 15, 34, 0, 15, 34, 15, 33, 33,
    15, 34, 43, 0, 0, 33, 34, 0, 15, 0, 0, 0, 76, 0, 15, 33, 34, 0, 0, 15, 15, 33, 15, 38, 15, 0,
    33, 15, 76, 38, 76, 15, 34, 44, 15, 34, 15, 15, 0, 33, 15, 33, 0, 33, 33, 0, 33, 0, 33, 0, 33,
    0, 0, 15, 0, 0, 33, 33, 0, 0, 0, 0, 0, 15, 15, 0, 15, 0, 15, 38, 0, 0, 34, 76, 34, 76, 44, 15,
    34, 33, 34, 0, 0, 76, 76, 44, 76, 76, 76, 44, 15, 34, 33, 0, 0, 0, 44, 0, 34, 15, 0, 15, 0, 0,
    15, 0, 15, 0, 34, 15, 15, 0, 33, 0, 33, 38, 0, 44, 44, 15, 0, 0, 0, 44, 44, 76, 15, 0, 15, 0,
    0, 15, 0, 0, 38, 0, 0, 0, 0, 76, 0, 76, 15, 0, 0, 15, 0, 0, 0, 0, 44, 38, 0, 0, 33, 76, 0, 15,
    0, 0, 0, 0, 15, 15, 0, 0, 0, 0, 0, 0, 0, 34, 0, 33, 15, 0, 38, 15, 0, 0, 0, 15, 15, 15, 15, 0,
    44, 44, 44, 76, 44, 76, 34, 0, 0, 44, 38, 0, 38, 76, 44, 76, 76, 76, 15, 0, 15, 57, 0, 0, 34,
    0, 34, 44, 0, 34, 15, 76, 38, 44, 34, 15, 0, 0, 43, 15, 0, 0, 33, 33, 15, 33, 33, 34, 33, 0,
    15, 15, 34, 0, 0, 0, 0, 44, 44, 34, 44, 33, 15, 0, 0, 0, 15, 34, 33, 33, 0, 15, 15, 34, 0, 0,
    0, 33, 0, 0, 0, 15, 0, 33, 0, 15, 15, 33, 44, 33, 33, 15, 15, 0, 15, 33, 15, 33, 34, 0, 15,
    33, 15, 15, 15, 0, 15, 15, 33, 15, 15, 15, 0, 76, 33, 0, 44, 38, 15, 0, 33, 57, 34, 33, 15,
    15, 15, 0, 34, 33, 34, 15, 15, 33, 15, 76, 15, 15, 0, 33, 15, 0, 15, 15, 15, 15, 0, 33, 33, 0,
    15, 0, 33, 33, 33, 15, 0, 0, 0, 0, 0, 38, 38, 33, 0, 15, 0, 0, 33, 15, 15, 38, 0, 34, 38, 0,
    0, 0, 33, 33, 0, 33, 0, 0, 15, 0, 0, 0, 43, 15, 33, 15, 15, 15, 15, 33, 44, 0, 0, 57, 0, 43,
    33, 57, 33, 34, 15, 43, 15, 15, 0, 0, 15, 0, 0, 0, 0, 15, 0, 33, 0, 0, 34, 0, 34, 15, 0, 15,
    43, 33, 15, 33, 0, 33, 0, 0, 43, 0, 15, 34, 34, 0, 34, 15, 0, 0, 33, 15, 15, 0, 33, 15, 15, 0,
    0, 0, 15, 15, 33, 15, 33, 34, 33, 15, 0, 33, 43, 0, 15, 0, 15, 0, 0, 0, 0, 0, 33, 33, 0, 34,
    0, 0, 0, 0, 0, 34, 0, 0, 0, 15, 0, 15, 15, 34, 34, 0, 0, 34, 15, 0, 0, 0, 0, 33, 33, 33, 0, 0,
    43, 0, 33, 15, 0, 33, 15, 33, 33, 15, 0, 0, 33, 0, 0, 15, 0, 0, 0, 15, 33, 0, 34, 34, 34, 0,
    0, 15, 33, 33, 33, 33, 33, 34, 34, 15, 15, 43, 15, 0, 34, 15, 0, 0, 0, 15, 15, 33, 15, 33, 34,
    0, 33, 0, 33, 0, 0, 0, 0, 0, 0, 15, 0, 33, 33, 15, 15, 0, 34, 0, 0, 33, 33, 0, 0, 0, 0, 34,
    15, 0, 15, 0, 0, 34, 15, 0, 15, 0, 15, 0, 0, 34, 15, 15, 33, 33, 0, 15, 15, 33, 33, 15, 0, 15,
    15, 0, 15, 0, 0, 34, 33, 34, 15, 33, 0, 34, 15, 15, 43, 33, 0, 15, 34, 0, 33, 0, 15, 15, 34,
    15, 15, 33, 33, 0, 0, 15, 0, 0, 15, 15, 15, 0, 0, 43, 33, 0, 0, 0, 33, 0, 33, 0, 43, 43, 0,
    33, 15, 15, 0, 15, 15, 15, 34, 33, 0, 15, 33, 15, 0, 33, 33, 15, 15, 15, 15, 0, 15, 15, 33,
    33, 0, 0, 15, 0, 0, 15, 0, 15, 33, 15, 15, 15, 33]

def muWitCheck (a n : ℕ) : Bool :=
  (List.range' a n).all fun j => bWcode 60 (6144 ^^^ n6VecArr[j]!) == 0 ||
    (decide (muWit[j]! < 891) && bWcode 60 (6144 ^^^ n6VecArr[muWit[j]!]!) == 0 &&
      bWcode (6144 ^^^ n6VecArr[j]!) (6144 ^^^ n6VecArr[muWit[j]!]!) == 0)

theorem muWitCheck_0 : muWitCheck 0 150 = true := by decide +kernel
theorem muWitCheck_1 : muWitCheck 150 150 = true := by decide +kernel
theorem muWitCheck_2 : muWitCheck 300 150 = true := by decide +kernel
theorem muWitCheck_3 : muWitCheck 450 150 = true := by decide +kernel
theorem muWitCheck_4 : muWitCheck 600 150 = true := by decide +kernel
theorem muWitCheck_5 : muWitCheck 750 141 = true := by decide +kernel

theorem muWitCheck_of_lt {j : ℕ} (hj : j < 891) :
    ∃ a n, muWitCheck a n = true ∧ a ≤ j ∧ j < a + n := by
  rcases Nat.lt_or_ge j 150 with h0 | h0
  · exact ⟨0, 150, muWitCheck_0, by omega, by omega⟩
  rcases Nat.lt_or_ge j 300 with h1 | h1
  · exact ⟨150, 150, muWitCheck_1, h0, by omega⟩
  rcases Nat.lt_or_ge j 450 with h2 | h2
  · exact ⟨300, 150, muWitCheck_2, h1, by omega⟩
  rcases Nat.lt_or_ge j 600 with h3 | h3
  · exact ⟨450, 150, muWitCheck_3, h2, by omega⟩
  rcases Nat.lt_or_ge j 750 with h4 | h4
  · exact ⟨600, 150, muWitCheck_4, h3, by omega⟩
  · exact ⟨750, 141, muWitCheck_5, h4, by omega⟩

theorem muWit_spec (j : ℕ) (hj : j < 891) (h : bWcode 60 (6144 ^^^ n6VecArr[j]!) ≠ 0) :
    muWit[j]! < 891 ∧ bWcode 60 (6144 ^^^ n6VecArr[muWit[j]!]!) = 0 ∧
      bWcode (6144 ^^^ n6VecArr[j]!) (6144 ^^^ n6VecArr[muWit[j]!]!) = 0 := by
  obtain ⟨a, n, hc, haj, hjn⟩ := muWitCheck_of_lt hj
  have h' := List.all_eq_true.1 hc j (List.mem_range'_1.2 ⟨haj, hjn⟩)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h'
  rcases h' with h' | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h' h
  · exact ⟨h1, h2, h3⟩

def deltaPt
    (j : Fin 891) : OmegaPt := ⟨sigmaW + n6vec j, DeltaW_subset ⟨j, rfl⟩⟩

theorem coe_deltaPt
    (j : Fin 891) :
    (deltaPt j : Wv v0) = decW (6144 ^^^ n6VecArr[(j : ℕ)]!) :=
  sigmaW_add_n6vec j

theorem tauPt_ne_deltaPt
    (j : Fin 891) : tauPt ≠ deltaPt j := fun e => by
  have hτ : tauW ∈ DeltaW := by
    rw [show tauW = (deltaPt j : Wv v0) from congrArg Subtype.val e]
    exact ⟨j, rfl⟩
  exact Set.disjoint_left.1 disjoint_DeltaW_tauOrb hτ (mem_usigOrbit_self tauW)

theorem exists_adj_mu_sigmaPt_tauPt
    {y : OmegaPt} (hy : omegaGraph.Adj sigmaPt y)
    (hyτ : ¬ omegaGraph.Adj tauPt y) :
    ∃ c ∈ omegaGraph.commonNeighbors sigmaPt tauPt, omegaGraph.Adj c y := by
  obtain ⟨j, hj⟩ := (adj_sigmaPt_iff y).1 hy
  obtain rfl : y = deltaPt j := Subtype.ext hj.symm
  have hb : bWcode 60 (6144 ^^^ n6VecArr[(j : ℕ)]!) ≠ 0 := by
    intro h0
    apply hyτ
    refine (omegaGraph_adj_iff_bW _ _).2 ⟨tauPt_ne_deltaPt j, ?_⟩
    rw [coe_deltaPt, show (tauPt : Wv v0) = decW 60 from rfl, bW_decW, h0, Nat.cast_zero]
  obtain ⟨hlt, hτ, hw⟩ := muWit_spec j j.2 hb
  have hcτ : omegaGraph.Adj tauPt (deltaPt ⟨_, hlt⟩) := by
    refine (omegaGraph_adj_iff_bW _ _).2 ⟨tauPt_ne_deltaPt _, ?_⟩
    rw [coe_deltaPt, show (tauPt : Wv v0) = decW 60 from rfl, bW_decW, hτ, Nat.cast_zero]
  refine ⟨deltaPt ⟨_, hlt⟩, (SimpleGraph.mem_commonNeighbors _).2
    ⟨(adj_sigmaPt_iff _).2 ⟨_, rfl⟩, hcτ⟩, (omegaGraph_adj_iff_bW _ _).2 ⟨fun e => ?_, ?_⟩⟩
  · rw [← e] at hyτ
    exact hyτ hcτ
  · rw [Unitary.bW_comm, coe_deltaPt, coe_deltaPt, bW_decW, hw, Nat.cast_zero]

theorem exists_adj_mu_omega
    {x v y : OmegaPt} (hxv : x ≠ v) (hn : ¬ omegaGraph.Adj x v)
    (hy : y = x ∨ omegaGraph.Adj x y) (hvy : ¬ omegaGraph.Adj v y) :
    ∃ c ∈ omegaGraph.commonNeighbors x v, omegaGraph.Adj c y := by
  obtain ⟨k, rfl, rfl⟩ := exists_smul_sigmaPt_tauPt hxv hn
  have hmem : ∀ c ∈ omegaGraph.commonNeighbors sigmaPt tauPt,
      k • c ∈ omegaGraph.commonNeighbors (k • sigmaPt) (k • tauPt) := fun c hc => by
    rw [SimpleGraph.mem_commonNeighbors] at hc ⊢
    exact ⟨(Amalgam.omegaGraph_adj_smul k _ _).2 hc.1, (Amalgam.omegaGraph_adj_smul k _ _).2 hc.2⟩
  rcases hy with rfl | hy
  · exact ⟨_, hmem _ (muPt_mem 0), (((SimpleGraph.mem_commonNeighbors _).1
      (hmem _ (muPt_mem 0))).1).symm⟩
  · have hy' : omegaGraph.Adj sigmaPt (k⁻¹ • y) := by
      rw [← Amalgam.omegaGraph_adj_smul k, smul_inv_smul]
      exact hy
    have hvy' : ¬ omegaGraph.Adj tauPt (k⁻¹ • y) := by
      rw [← Amalgam.omegaGraph_adj_smul k, smul_inv_smul]
      exact hvy
    obtain ⟨c, hc, hcy⟩ := exists_adj_mu_sigmaPt_tauPt hy' hvy'
    refine ⟨k • c, hmem c hc, ?_⟩
    rw [← smul_inv_smul k y]
    exact (Amalgam.omegaGraph_adj_smul k _ _).2 hcy

end CFSG.Monster.B.GSide
