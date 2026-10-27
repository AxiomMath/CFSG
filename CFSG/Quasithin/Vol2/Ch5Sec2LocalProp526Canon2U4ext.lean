module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526U4ext
import CFSG.Quasithin.H13.U4ParOuterFacts
import CFSG.Quasithin.Recognition.F112RShapes

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

@[expose] def Stmt5_2_6_U4extC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → 2 ≤ f → IsU4ExtTwo f (sec52Alpha M L H B D L₂) →
    IsL2Quot f (oTwoQuot ↥L₂) → IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (sec52G2 M H D L₂)) →
    IsBlock2 L L → IsL2Quot (2 * f) (oTwoQuot ↥L) → IsOmega4MinusType L f →
      pCoreOf 2 (sec52G1 M L H B L₂) = pCoreOf 2 L ∧
      pCoreOf 2 (sec52G2 M H D L₂) = pCoreOf 2 L₂ ∧
      ∃ t : G, orderOf t = 2 ∧ t ∉ pCoreOf 2 L₂ ∧
        pCoreOf 2 (L₂ ⊔ sec52S M H) = pCoreOf 2 L₂ ⊔ Subgroup.zpowers t ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
          ∃ P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F), IsMaxParabolic2 ⊤ P ∧
            Nonempty (↥(L₂ ⊓ Subgroup.centralizer ({t} : Set G)) ≃* ↥(perfectCore P))

section Transport

variable {G : Type} [Group G] {Y : Type} [Group Y] {G' : Subgroup G} {M : Subgroup Y}

theorem isSpecialPow_core_of_equiv (e : ↥G' ≃* ↥M) {q w : ℕ}
    (h : IsSpecialPow 2 q w ↥(pCoreOf 2 G')) : IsSpecialPow 2 q w ↥(pCoreOf 2 M) := by
  have hg : Function.Injective G'.subtype := G'.subtype_injective
  have hf : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have h1 := U4Par.pCoreOf_map_of_inj hg 2 (⊤ : Subgroup ↥G')
  have h2 := U4Par.pCoreOf_map_of_inj hf 2 (⊤ : Subgroup ↥G')
  rw [← eq_map_subtype_top G'] at h1
  rw [← eq_map_comp_top e] at h2
  let e1 : ↥(pCoreOf 2 G') ≃* ↥(pCoreOf 2 (⊤ : Subgroup ↥G')) :=
    (MulEquiv.subgroupCongr h1).trans
      ((pCoreOf 2 (⊤ : Subgroup ↥G')).equivMapOfInjective G'.subtype hg).symm
  let e2 : ↥(pCoreOf 2 (⊤ : Subgroup ↥G')) ≃* ↥(pCoreOf 2 M) :=
    ((pCoreOf 2 (⊤ : Subgroup ↥G')).equivMapOfInjective _ hf).trans
      (MulEquiv.subgroupCongr h2.symm)
  exact IsSpecialPow.of_mulEquiv (e1.trans e2) h

end Transport

open F1

theorem stmt5_2_6_U4extC_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hRL : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2) (hbor : Stmt5_2_6_borel) :
    Stmt5_2_6_U4extC := by
  intro G _ _ T M L V H B D L₂ n f hyp hf hA _ hsp _ _ _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  obtain ⟨hG1, hG2, -⟩ := hyp.parabolics_eq h331 hR (hbor G T M L V H B D L₂ n hyp)
  have h111₀ := hF11 G T M L V H B D L₂ n hyp
  have h111 := Hyp111R.of_hyp111 hRL h111₀
  have hL₂perf : ⁅L₂, L₂⁆ = L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact hK₁.2.1
    · exact hL₂P.2.1
  have hG1core : perfectCore (sec52G1 M L H B L₂) = L := by
    rw [hG1]
    have hAn : (L.subgroupOf (L ⊔ bigB L L₂ S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left h111).1)
    exact le_antisymm
      (perfectCore_le_of_sup_solvable le_sup_left hAn rfl (F1.isSolvable_bigB h111))
      (le_perfectCore_of_perfect le_sup_left h.commutator_eq)
  have hG2core : perfectCore (sec52G2 M H D L₂) = L₂ := by
    rw [hG2]
    have hAn : (L₂.subgroupOf (L₂ ⊔ bigB L L₂ S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left h111).2)
    exact le_antisymm
      (perfectCore_le_of_sup_solvable le_sup_left hAn rfl (F1.isSolvable_bigB h111))
      (le_perfectCore_of_perfect le_sup_left hL₂perf)
  have hLG₁ : L ≤ sec52G1 M L H B L₂ := le_sup_left.trans le_sup_left
  have hSG₁ : S ≤ sec52G1 M L H B L₂ := le_sup_right.trans le_sup_left
  have hL₂G₂ : L₂ ≤ sec52G2 M H D L₂ := le_sup_right
  have hSG₂ : S ≤ sec52G2 M H D L₂ := le_sup_right.trans le_sup_left
  obtain ⟨Y₀, _, Yh, _, ι, hY₀, hι, hidx, Th, Mh₁, Mh₂, hpair, ⟨Φ⟩⟩ := hA
  obtain ⟨K', _, hK', ⟨e⟩⟩ := U4Par.exists_hypSU_equiv_of_lieModel hY₀
  have hfin : Finite Yh :=
    (U4Par.exists_embedding (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩)).1
  have hψ₀ : Function.Injective (ι.comp e.toMonoidHom) := hι.comp e.injective
  have hidx₀ : (ι.comp e.toMonoidHom).range.index ≤ 2 := by
    rw [F431.U42.Am.range_comp_mulEquiv, hidx]
  obtain ⟨ψ, hψ, hrange, hU⟩ := U4V.exists_adapted hK' hψ₀ hidx₀ hpair.1
  have hidx2 : ψ.range.index = 2 := by
    rw [hrange, F431.U42.Am.range_comp_mulEquiv]
    exact hidx
  rw [← hrange] at hidx₀ hU
  have hC : Subgroup.centralizer (ψ.range : Set Yh) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hz2, hzc⟩ := U4Ext.mem_center_of_mem_centralizer_range hK' hψ hidx2 hz
    have hzN : z ∈ Subgroup.normalizer (Th : Set Yh) := Subgroup.center_le_normalizer _ hzc
    have hz₁ : z ∈ Mh₁ := ((hpair.2.2 Mh₁).mpr (Or.inl rfl)).2 hzN
    have hz₂ : z ∈ Mh₂ := ((hpair.2.2 Mh₂).mpr (Or.inr rfl)).2 hzN
    obtain ⟨x, hxz⟩ : ∃ x : ↥(sec52G1 M L H B L₂ ⊓ sec52G2 M H D L₂),
        ((isoφ12 Φ x : ↥(Mh₁ ⊓ Mh₂)) : Yh) = z :=
      ⟨(isoφ12 Φ).symm ⟨z, Subgroup.mem_inf.mpr ⟨hz₁, hz₂⟩⟩, by rw [MulEquiv.apply_symm_apply]⟩
    have hx2 : x * x = 1 := (isoφ12 Φ).injective (by
      apply Subtype.ext
      rw [map_mul, map_one, Subgroup.coe_mul, hxz, hz2, OneMemClass.coe_one])
    have hcen := le_centralizer_of_isoφ12_mem_center Φ x (by rw [hxz]; exact hzc)
    have hX : L ⊔ L₂ ⊔ S ≤ sec52G1 M L H B L₂ ⊔ sec52G2 M H D L₂ :=
      sup_le (sup_le (hLG₁.trans le_sup_left) (hL₂G₂.trans le_sup_right))
        (hSG₁.trans le_sup_left)
    have hG₁X : sec52G1 M L H B L₂ ≤ L ⊔ L₂ ⊔ S :=
      sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (inf_le_right.trans (le_sup_right.trans le_sup_left))
    have hmem := mem_pCoreOf_of_le_centralizer (hG₁X (Subgroup.mem_inf.mp x.2).1)
      (congrArg Subtype.val hx2) (hX.trans hcen)
    rw [h111₀.o2, Subgroup.mem_bot] at hmem
    rw [← hxz, show x = 1 from Subtype.ext hmem, map_one, OneMemClass.coe_one]
  have hspM : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 Mh₂) :=
    isSpecialPow_core_of_equiv (isoφ2 Φ) hsp
  obtain ⟨i₂, hM₂N, hM₂R⟩ :=
    U4V.inf_eq_of_adapted hK' ψ hψ hidx₀ hpair hU
  obtain ⟨i₁, hM₁N, hM₁R⟩ :=
    U4V.inf_eq_of_adapted hK' ψ hψ hidx₀ (U4V.isYAmalgamPair_swap hpair) hU
  obtain ⟨y₀, hy₀, -, hact⟩ := U4Par.exists_frob_elt hK' ψ hψ hidx2 hC
  have hM₂ : Mh₂ = Subgroup.normalizer (((U4Par.parP hK').map ψ : Subgroup Yh) : Set Yh) ∧
      Mh₂ ⊓ ψ.range = (U4Par.parP hK').map ψ := by
    fin_cases i₂
    · exact ⟨hM₂N, hM₂R⟩
    · exfalso
      have hcore := U4Par.pCoreOf_normalizer_parP2 hK' hact hf hψ hidx2 hy₀ hM₂N hM₂R
      have hq : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hcore] at hspM
      refine U4Par.false_of_isSpecialPow_of_comm hq ?_ hspM
      rw [U4Par.comm_map_iff hψ]
      exact fun a ha b hb => U4Par.radQ2_comm hK' ha hb
  have hM₁ : Mh₁ = Subgroup.normalizer (((U4Par.parP2 hK').map ψ : Subgroup Yh) : Set Yh) ∧
      Mh₁ ⊓ ψ.range = (U4Par.parP2 hK').map ψ := by
    fin_cases i₁
    · exact absurd (hM₁N.trans hM₂.1.symm) hpair.2.1
    · exact ⟨hM₁N, hM₁R⟩
  have hS12 : IsSylowTwoOf S (sec52G1 M L H B L₂ ⊓ sec52G2 M H D L₂) := by
    rw [hG1, hG2, F1.parabolic_inf_parabolic h111]
    exact F112W.isSylowTwoOf_bigB h111
  obtain ⟨hO1, hO2, tY, htYS, htYo, htYQ, htYsup, F, _, _, hF, P, hP, ⟨eP⟩⟩ :=
    U4Par.ext_facts hK' hf hψ hidx2 hC hpair hU hM₁.1 hM₁.2 hM₂.1 hM₂.2
      (isSylowTwoOf_map_equiv (isoφ12 Φ) hS12)
  refine ⟨?_, ?_, ?_⟩
  · rw [pCoreOf_eq_of_equiv (isoφ1 Φ) hO1, hG1core]
  · rw [pCoreOf_eq_of_equiv (isoφ2 Φ) hO2, hG2core]
  obtain ⟨s, -, rfl⟩ := htYS
  have hs₂ : (s : G) ∈ sec52G2 M H D L₂ := (Subgroup.mem_inf.mp s.2).2
  have hts : ((isoφ2 Φ ⟨s, hs₂⟩ : ↥Mh₂) : Yh) =
      ((Mh₁ ⊓ Mh₂).subtype.comp (isoφ12 Φ).toMonoidHom) s :=
    (coe_isoφ12_eq_φ2 Φ s).symm
  refine ⟨(s : G), ?_, ?_, ?_, F, inferInstance, inferInstance, hF, P, hP, ?_⟩
  · rw [← U4Ext.orderOf_coe_equiv (isoφ12 Φ) s]
    exact htYo
  · intro htQ
    apply htYQ
    rw [← hts]
    exact (mem_pCoreOf_perfectCore_iff_of_equiv (isoφ2 Φ) ⟨s, hs₂⟩).mp
      (by rw [hG2core]; exact htQ)
  · have hsup := pCoreOf_sup_zpowers_of_equiv (isoφ2 Φ) hSG₂ ⟨s, hs₂⟩
      (by rw [map_subgroupOf_isoφ2 Φ hSG₁, hts]; exact htYsup)
    rw [hG2core] at hsup
    exact hsup
  · have hne := inf_centralizer_equiv (isoφ2 Φ) ⟨s, hs₂⟩
    rw [hG2core, hts] at hne
    obtain ⟨e₁⟩ := hne
    exact ⟨e₁.trans eP⟩

end CFSG.Quasithin.H13
