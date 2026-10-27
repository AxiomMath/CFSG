module

public import CFSG.Quasithin.MS93.S33SpF2
public import CFSG.Quasithin.MS93.S33I

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem relIndex_qv_zm_ne_two_gen (h : PUHyp M T L)
    (hfour : ∀ m ∈ M, ¬ Uq M T L ≤ Subgroup.centralizer ({m} : Set G) →
      4 ≤ (Subgroup.centralizer ({m} : Set G)).relIndex (Uq M T L))
    {δ δ' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) δ δ') :
    (Qv _ δ').relIndex (ZM (puAmalgam h.le) δ) ≠ 2 := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hc.1
  have hc' : IsCritical (puAmalgam h.le) (baseA _) (g⁻¹ • δ') := by
    have := (isCritical_smul _ g⁻¹ (g • baseA _) δ').mpr hc
    rwa [inv_smul_smul] at this
  have hne := relIndex_qv_zm_ne_two_of_four h hfour hc'
  rwa [qv_smul, ← inv_smul_smul g (baseA (puAmalgam h.le)), zm_smul _ g⁻¹ (g • baseA _),
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hne

section Sp4

variable {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(StatedSp 2 F)}
  {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)}

theorem pre_zm_props (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ (baseA _)) :
    (∀ x ∈ pre h.le (ZM _ γ), ∀ y ∈ pre h.le (ZM _ γ), x * y = y * x) ∧
    (∀ x ∈ pre h.le (ZM _ γ), x ^ 2 = 1) ∧ ⁅Uq M T L, pre h.le (ZM _ γ)⁆ ≤ pre h.le (ZM _ γ) ∧
    (∀ e ∈ pre h.le (ZM _ γ), e ∈ Subgroup.centralizer (Uq M T L : Set G) → e ∈ pCoreOf 2 M) ∧
    imM h.le (pre h.le (ZM _ γ)) = ZM (puAmalgam h.le) γ := by
  have hb := h.critDist_pos
  have h20 := h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist γ (baseA _) = critDist (puAmalgam h.le) := hc.2.1
  have hd1 : 0 < (puAmalgam h.le).treeGraph.dist (baseA _) γ := by
    rw [SimpleGraph.dist_comm, hd]
    exact hb
  have hρadj : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA _) γ 1) := adj_geo_one _ hd1
  have hZρ : ZM (puAmalgam h.le) γ ≤ Qv _ (geo _ (baseA _) γ 1) := by
    refine zm_le_qv_of_dist_lt _ hc.1 ?_
    rw [SimpleGraph.dist_comm, dist_geo_right _ (show 1 ≤ _ from hd1), SimpleGraph.dist_comm, hd]
    omega
  have hZS : ZM (puAmalgam h.le) γ ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact hZρ.trans (qv_le_stab_of_adj _ hρadj.symm)
  have hEim := imM_pre h.le hZS
  have hEA := isElemAbelian_zm _ h20 hb hc.1
  refine ⟨pre_comm h.le (isMulCommutative_subgroup_iff.mp hEA.1), pre_sq h.le hEA.2, ?_, ?_, hEim⟩
  ·
    have hd2 : 0 < (puAmalgam h.le).treeGraph.dist γ (baseA _) := by rw [hd]; exact hb
    have hadj : (puAmalgam h.le).treeGraph.Adj γ (geo _ γ (baseA _) 1) := adj_geo_one _ hd2
    have hZn : ZM (puAmalgam h.le) (baseA _) ≤
        Subgroup.normalizer (ZM (puAmalgam h.le) γ : Set (puAmalgam h.le).Universal) := by
      refine le_trans ?_ ((qv_le_stab_of_adj _ hadj.symm).trans (stab_le_normalizer_zm _ γ))
      refine zm_le_qv_of_dist_lt _ (PU.isMVtx_baseA _) ?_
      rw [SimpleGraph.dist_comm, dist_geo_right _ (show 1 ≤ _ from hd2), hd]
      omega
    have hUM : Uq M T L ≤ M := Uq_le h.L_le
    rw [← imM_le_imM_iff h.le (commutator_le_of_le hUM (pre_le h.le _)),
      imM_commutator h.le hUM (pre_le h.le _), hEim]
    refine (Subgroup.commutator_mono (imM_mono h.le (Uq_le_Z0q h.L_le)) le_rfl).trans ?_
    rw [← puAmalgam.zm_baseA, Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hZn
  · intro e he hcU
    obtain ⟨e', he', rfl⟩ := (mem_pre_iff' h.le).1 he
    have hmem : (puAmalgam h.le).ofA e' ∈ Qv _ (baseA (puAmalgam h.le)) := by
      rw [← qv_inf_centralizer_puTrans h (PU.isMVtx_baseA _) hρadj,
        puTrans_baseA h.le (uq_subgroupOf_normal h)]
      refine ⟨hZρ he', Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      obtain ⟨u, hu, rfl⟩ := hx
      have h1 := Subgroup.mem_centralizer_iff.mp hcU u (Subgroup.mem_subgroupOf.mp hu)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1
    rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, ofA_mem_imM_iff] at hmem
    exact hmem

variable (h : PUHyp M T L) (hα : Function.Surjective α) (hβ : Function.Surjective β)
  (hβker : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L))
  (hβα : ∀ l : ↥L, IsCoordAct β l (MSP.mat (α l)).mulVec)
include h hα hβ hβker hβα

theorem linear_of_isCritical_sp {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hF : 4 ≤ Fintype.card F) {γ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ (baseA _)) :
    ∀ e ∈ pre h.le (ZM _ γ), ∀ f : MSP.V4 F → MSP.V4 F, IsCoordAct β e f →
      ∀ (c : F) (x : MSP.V4 F), f (c • x) = c • f x := by
  obtain ⟨hEab, hE2, hUE, hEQ, hEim⟩ := pre_zm_props h hc
  by_contra hnl
  apply relIndex_qv_zm_ne_two_gen h
    (fun _ hm hnt => four_le_relIndex_centralizer_sp h hα hβ hβker hβα hF hm hnt) hc
  rw [← hEim, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    relIndex_imM h.le (pre_le h.le _)]
  refine relIndex_eq_two_of_nonlinear_sp h hα hβ hβker hβα hcard (pre_le h.le _) hEQ hEab hE2
    hUE ?_
  by_contra hall
  apply hnl
  intro e he f hf
  by_contra hne
  exact hall ⟨e, he, f, hf, hne⟩

theorem exists_sp4_mat_of_isCritical {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hF : 4 ≤ Fintype.card F) {γ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ (baseA _)) :
    ∀ e ∈ pre h.le (ZM _ γ), ∃ g : MSP.Sp4 F, IsCoordAct β e (MSP.mat g).mulVec := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  obtain ⟨-, hE2, -, -, -⟩ := pre_zm_props h hc
  intro e he
  have heM : e ∈ M := pre_le h.le _ he
  have hLV : L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.L_le.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨f, hf⟩ := exists_isCoordAct_sp h hβ hβker heM
  obtain ⟨f', hf'⟩ := exists_isCoordAct_sp h hβ hβker (inv_mem heM)
  exact exists_sp4_of_linear hα hLV hβ hβα (le_normalizer_Uq h.le_normalizer heM)
    (h.le_normalizer heM) hf hf' (linear_of_isCritical_sp h hα hβ hβker hβα hcard hF hc e he f hf)
    (e := 1) (by simpa using hE2 e he)

end Sp4

end CFSG.Quasithin.MS93.S33
