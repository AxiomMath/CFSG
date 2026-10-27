
module

public import CFSG.Monster.B.GSide.MuFourOmegaBase

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisCert CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary

theorem mem_DeltaW_iff
    (z : OmegaPt) :
    (z : Wv v0) ∈ DeltaW ↔ sigmaPt ≠ z ∧ Unitary.bW sigmaW z = 0 := by
  rcases (Set.ext_iff.1 OmegaW_eq_union (z : Wv v0)).1 z.2 with (h | h) | h
  · have hz : z = sigmaPt := Subtype.ext (Set.mem_singleton_iff.1 h)
    subst hz
    exact iff_of_false sigmaW_notMem_DeltaW fun h' => h'.1 rfl
  · refine iff_of_true h ⟨fun e => ?_, ?_⟩
    · subst e
      exact sigmaW_notMem_DeltaW h
    · obtain ⟨j, hj⟩ := h
      rw [← hj, map_add, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, qWv_sigmaW,
        smul_zero, zero_add]
      exact LinearMap.mem_ker.1 (n6vec_mem_sigmaPerp j)
  · refine iff_of_false (fun h' => Set.disjoint_left.1 disjoint_DeltaW_tauOrb h' h) ?_
    rintro ⟨-, h0⟩
    exact one_ne_zero ((Amalgam.bV_sigmaW_of_mem_tauOrb h).symm.trans h0)

theorem omegaGraph_adj_iff_bW
    (x y : OmegaPt) :
    omegaGraph.Adj x y ↔ x ≠ y ∧ Unitary.bW (x : Wv v0) y = 0 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Kstab v0) x sigmaPt
  have hb : Unitary.bW sigmaW ((g • y : OmegaPt) : Wv v0) = Unitary.bW (x : Wv v0) y := by
    have e : sigmaW = ((g • x : OmegaPt) : Wv v0) := by rw [hg]; rfl
    rw [e, coe_smul_OmegaPt, coe_smul_OmegaPt, bW_wAct]
  rw [← Amalgam.omegaGraph_adj_smul g, hg, adj_sigmaPt_iff, mem_DeltaW_iff, hb, ← hg,
    Ne, smul_left_cancel_iff]

attribute [local irreducible] muIdx muPar

def muPt
    (i : Fin 324) : OmegaPt := ⟨sigmaW + n6vec (muJ i), DeltaW_subset ⟨_, rfl⟩⟩

theorem coe_muPt
    (i : Fin 324) :
    (muPt i : Wv v0) = decW (6144 ^^^ n6VecArr[muIdx[(i : ℕ)]!]!) :=
  sigmaW_add_n6vec _

theorem muPt_injective :
    Function.Injective muPt := fun _ _ h =>
  muJ_injective (sigmaW_add_injective (congrArg Subtype.val h))

theorem muPt_mem
    (i : Fin 324) : muPt i ∈ omegaGraph.commonNeighbors sigmaPt tauPt := by
  rw [SimpleGraph.mem_commonNeighbors]
  refine ⟨(adj_sigmaPt_iff _).2 ⟨_, rfl⟩, (omegaGraph_adj_iff_bW _ _).2 ⟨fun e => ?_, ?_⟩⟩
  · have hτ : tauW ∈ DeltaW := by
      rw [show tauW = (muPt i : Wv v0) from congrArg Subtype.val e]
      exact ⟨_, rfl⟩
    exact Set.disjoint_left.1 disjoint_DeltaW_tauOrb hτ (mem_usigOrbit_self tauW)
  · rw [coe_muPt, show (tauPt : Wv v0) = decW 60 from rfl, bW_decW, (muTree_spec i i.2).2.1,
      Nat.cast_zero]

theorem muPt_adj_par
    (i : Fin 324) (hi : (i : ℕ) ≠ 0) :
    omegaGraph.Adj (muPt i) (muPt ⟨muPar[(i : ℕ)]!, ((muTree_spec i i.2).2.2 hi).1.trans i.2⟩) := by
  obtain ⟨hlt, hb⟩ := (muTree_spec i i.2).2.2 hi
  refine (omegaGraph_adj_iff_bW _ _).2 ⟨fun e => ?_, ?_⟩
  · have := congrArg Fin.val (muPt_injective e)
    simp only at this
    omega
  · rw [coe_muPt, coe_muPt, bW_decW, hb, Nat.cast_zero]

theorem muPt_range :
    Set.range muPt = omegaGraph.commonNeighbors sigmaPt tauPt := by
  refine Set.eq_of_subset_of_ncard_le (Set.range_subset_iff.2 muPt_mem) ?_ (Set.toFinite _)
  rw [ncard_commonNeighbors_sigmaPt_tauPt, Set.ncard_range_of_injective muPt_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem preconnected_mu_sigmaPt_tauPt :
    (omegaGraph.induce (omegaGraph.commonNeighbors sigmaPt tauPt)).Preconnected := by
  set M := omegaGraph.induce (omegaGraph.commonNeighbors sigmaPt tauPt)
  have hreach : ∀ n, ∀ i : Fin 324, (i : ℕ) ≤ n →
      M.Reachable ⟨muPt 0, muPt_mem 0⟩ ⟨muPt i, muPt_mem i⟩ := by
    intro n
    induction n with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := Fin.ext (by omega)
      rfl
    | succ n ih =>
      intro i hi
      by_cases hi0 : (i : ℕ) = 0
      · obtain rfl : i = 0 := Fin.ext hi0
        rfl
      · have hlt := ((muTree_spec i i.2).2.2 hi0).1
        refine (ih ⟨muPar[(i : ℕ)]!, hlt.trans i.2⟩ (by simp only; omega)).trans ?_
        exact (SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.2 (muPt_adj_par i hi0))).symm
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  rw [← muPt_range] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨i', rfl⟩ := hb
  exact (hreach i i le_rfl).symm.trans (hreach i' i' le_rfl)

theorem exists_smul_sigmaPt_tauPt
    {x y : OmegaPt} (hxy : x ≠ y) (hn : ¬ omegaGraph.Adj x y) :
    ∃ k : Kstab v0, k • sigmaPt = x ∧ k • tauPt = y := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Kstab v0) sigmaPt x
  have hσ : g⁻¹ • y ≠ sigmaPt := fun e => hxy (by rw [← hg, ← e, smul_inv_smul])
  have hna : ¬ omegaGraph.Adj sigmaPt (g⁻¹ • y) := fun h => hn (by
    rw [← hg, ← smul_inv_smul g y]
    exact (Amalgam.omegaGraph_adj_smul g _ _).2 h)
  have hτ : ((g⁻¹ • y : OmegaPt) : Wv v0) ∈ usigOrbit tauW := by
    rcases (Set.ext_iff.1 OmegaW_eq_union _).1 (g⁻¹ • y).2 with (h | h) | h
    · exact absurd (Subtype.ext (Set.mem_singleton_iff.1 h)) hσ
    · exact absurd ((adj_sigmaPt_iff _).2 h) hna
    · exact h
  obtain ⟨u, hu, hut⟩ := hτ
  have h1 : u⁻¹ • sigmaPt = sigmaPt := Subtype.ext (by
    rw [coe_smul_OmegaPt, inv_inv]
    exact mem_Usig.1 hu)
  have h2 : u⁻¹ • tauPt = g⁻¹ • y := Subtype.ext (by
    rw [coe_smul_OmegaPt, inv_inv]
    exact hut)
  exact ⟨g * u⁻¹, by rw [mul_smul, h1, hg], by rw [mul_smul, h2, smul_inv_smul]⟩

theorem preconnected_mu_omega
    {x y : OmegaPt} (hxy : x ≠ y) (hn : ¬ omegaGraph.Adj x y) :
    (omegaGraph.induce (omegaGraph.commonNeighbors x y)).Preconnected := by
  obtain ⟨k, rfl, rfl⟩ := exists_smul_sigmaPt_tauPt hxy hn
  refine preconnected_induce_of_surjOn (omegaSMulHom k) (fun z hz => ?_) (fun z hz => ?_)
    preconnected_mu_sigmaPt_tauPt
  · rw [SimpleGraph.mem_commonNeighbors] at hz ⊢
    exact ⟨(Amalgam.omegaGraph_adj_smul k _ _).2 hz.1, (Amalgam.omegaGraph_adj_smul k _ _).2 hz.2⟩
  · refine ⟨k⁻¹ • z, ?_, smul_inv_smul k z⟩
    rw [SimpleGraph.mem_commonNeighbors] at hz ⊢
    refine ⟨(Amalgam.omegaGraph_adj_smul k _ _).1 ?_, (Amalgam.omegaGraph_adj_smul k _ _).1 ?_⟩
    · rw [smul_inv_smul]
      exact hz.1
    · rw [smul_inv_smul]
      exact hz.2

end CFSG.Monster.B.GSide
