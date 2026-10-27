module

public import CFSG.Quasithin.H13.U3L14B
public import CFSG.Quasithin.H13.U3L14K

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def StepD (T V Lp : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((pCoreOf 2 Lp).subgroupOf (A6.g1 T V)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V))) ≤
      centralizer (CFSG.pCore p (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)) :
        Set (↥(A6.g1 T V) ⧸ CFSG.pCore 2 ↥(A6.g1 T V)))

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem exists_K (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G))
    (hd : StepD T V Lp) :
    ∃ K ∈ cComp (A6.g1 T V), CFSG.IsComponent ((K.subgroupOf (A6.g1 T V)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)))) ∧
      ¬ ⁅K, pCoreOf 2 Lp⁆ ≤ pCoreOf 2 (A6.g1 T V) := by
  set H := A6.g1 T V with hH
  set A : Subgroup ↥H := (pCoreOf 2 Lp).subgroupOf H with hAdef
  have hOLp : pCoreOf 2 Lp ≤ H := (LieType.BorelTits.pCoreOf_le 2 Lp).trans S.Lp_G1
  have hmem : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := fun x =>
    coe_mem_pCoreOf_iff
  have hA : IsPGroup 2 A :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 Lp).of_equiv (subgroupOfEquivOfLe hOLp).symm
  have hAO : ¬ A ≤ CFSG.pCore 2 ↥H := by
    intro h
    apply S.stepC hQ
    intro x hx
    exact (hmem ⟨x, hOLp hx⟩).2 (h (mem_subgroupOf.2 hx))
  obtain ⟨K', hK', hcK', hKA⟩ := exists_cComp_comm_not_le hA hAO hd
  refine ⟨K'.map H.subtype, map_subtype_mem_cComp hK', ?_, fun h => hKA ?_⟩
  · rw [show (K'.map H.subtype).subgroupOf H = K' from
      comap_map_eq_self_of_injective H.subtype_injective K']
    exact hcK'
  rw [commutator_le]
  intro k hk a ha
  have h1 : ((⁅k, a⁆ : ↥H) : G) ∈ pCoreOf 2 H := by
    have : ((⁅k, a⁆ : ↥H) : G) = ⁅(k : G), (a : G)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact h (commutator_mem_commutator (mem_map_of_mem _ hk) (mem_subgroupOf.1 ha))
  exact (hmem _).1 h1

omit S in
theorem perfect_le_Y {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKU : K ≤ centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) :
    K ≤ oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) :=
  perfect_le_oTwoUpper hKU (Subgroup.isPerfect_iff.2 hK)

omit S in
theorem charTwo_of_isSubnormal' {X M : Subgroup G} (hM : CharTwo M)
    (h : CFSG.Open.IsSubnormal X M) : CharTwo X := by
  induction h with
  | refl => exact hM
  | step hle hN _ ih => exact (ih hM).of_normal hle hN

theorem U_omega (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) :
    conjClosure V₃ (A6.g1 T V) ≤ omegaOneCenterOf (pCoreOf 2 (A6.g1 T V)) := by
  obtain ⟨hUQ, hQU, hUE⟩ := S.stepA hQ
  intro u hu
  refine mem_omegaOneCenterOf (hUQ hu) (fun y hy => ?_) (hUE.2 u hu)
  exact ((mem_centralizer_iff.1 (hQU hy)) u hu).symm

theorem stepE (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) {K : Subgroup G}
    (hK : K ∈ cComp (A6.g1 T V)) :
    ⁅omegaOneCenterOf (pCoreOf 2 (A6.g1 T V)), K⁆ ≠ ⊥ ∧ quasithinIsFaithfulLocal T K ∧
      T ≤ normalizer (K : Set G) ∧ A6.g1 T V ≤ normalizer (K : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) ∧ ¬ K ≤ normalizer (L : Set G) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := A6.g1 T V with hH
  set U := conjClosure V₃ H with hU
  obtain ⟨hsolv, -⟩ := S.stepB h1336 h37 h38 h39
  have hKperf := perfect_of_mem_cComp hK
  have hKne := ne_bot_of_mem_cComp hK
  have hKH := le_of_mem_cComp hK
  have hUK : ⁅U, K⁆ ≠ ⊥ := by
    intro h
    have hKC : K ≤ centralizer (U : Set G) := by
      rw [commutator_eq_bot_iff_le_centralizer] at h
      exact le_centralizer_iff.1 h
    have hKY := perfect_le_Y hKperf hKC
    have : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKY)
    exact not_isSolvable_of_mem_cComp hK this
  have hΩK : ⁅omegaOneCenterOf (pCoreOf 2 H), K⁆ ≠ ⊥ := fun h =>
    hUK (le_bot_iff.1 (h ▸ commutator_mono (S.U_omega hQ) le_rfl))
  have hKsub := subnormal_of_mem_cComp hK
  have hKc : CharTwo K := charTwo_of_isSubnormal' S.charTwo_G1 hKsub
  have hK2 : K = oTwoUpper K :=
    le_antisymm (perfect_le_oTwoUpper le_rfl (Subgroup.isPerfect_iff.2 hKperf)) (oTwoUpper_le K)
  have hKX : IsXClass K := ⟨hKne, hK2, hKc⟩
  have hVK : VY K ≠ ⊥ := (a4_9 hKX hKsub).1 hΩK
  have hQne : pCoreOf 2 H ≠ ⊥ := fun h => S.V1_ne (le_bot_iff.1 (h ▸ S.ash.V₁_le_pCoreOf))
  have hKT : K ⊔ T ≤ H := sup_le hKH S.T_G1
  have hO2KT : pCoreOf 2 (K ⊔ T) ≠ ⊥ := by
    intro hb
    apply hQne
    have := CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (S.Q1_T.trans le_sup_right)
      (hKT.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (LieType.BorelTits.pCoreOf_isPGroup 2 H)
    rw [hb] at this
    exact le_bot_iff.1 this
  have hfK : quasithinIsFaithfulLocal T K := by
    refine ⟨⟨S.isP_T, cComp_mem_of_le hK le_sup_left hKT, (S.syl le_sup_right).2.2, hO2KT⟩,
      fun N hNK _ hN => le_antisymm hNK (hK2.le.trans (oTwoUpper_le_of_pow_mem hN)), ?_, hVK⟩
    exact (quasithinGenFitting_eq_pCoreOf_iff K 2).2 hKc
  obtain ⟨-, ⟨hTK, -, hMK, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K hfK
  have hloc : IsTwoLocal H := ⟨fsuV1 T V, S.V1_ne, S.isP_V1, rfl⟩
  obtain ⟨M'', hM'', hHM''⟩ := exists_maxTwoLocal_ge hloc
  have hM''K := huniqK M'' hM'' (hKT.trans hHM'')
  have hHK : H ≤ normalizer (K : Set G) := hM''K ▸ hHM''
  have hHM : ¬ H ≤ normalizer (L : Set G) := by
    rcases h1336 G T L V S.h13 S.irr with h | ⟨h, -⟩
    · exact h
    · exact absurd S.zv h
  refine ⟨hΩK, hfK, hTK, hHK, fun hLK => ?_, fun hKM => ?_⟩
  · have := S.uniq _ hMK (sup_le hLK hTK)
    exact hHM (this ▸ hHK)
  · have := huniqK _ S.Mmax (sup_le hKM S.T_L)
    exact hHM (this ▸ hHK)

theorem stepF {K : Subgroup G} (hHK : A6.g1 T V ≤ normalizer (K : Set G))
    (hLK : ¬ L ≤ normalizer (K : Set G)) : ¬ L₁Of L V₂ ≤ normalizer (K : Set G) := fun h =>
  hLK (S.genL.trans (sup_le hHK h))

end Set14

end CFSG.Quasithin.H13.U3
