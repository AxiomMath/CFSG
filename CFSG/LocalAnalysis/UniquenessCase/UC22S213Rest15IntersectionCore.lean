module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R875O2HM
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs
public import CFSG.LocalAnalysis.UniquenessCase.UC6Star36b

public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsSL3 IsSU3)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
variable {G : Type} [Group G] [Finite G]

theorem r6_7_dataOfSetup4
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : TheoremCAt S.M) :
    UC6.R6_7 (dataOfSetup4 hS hU S) :=
  PartTwo.r6_7_of_K36_at _ (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree)
    (r6_3_dataOfSetup4 hS hU S hC) (star36At_dataOfSetup4 hS hU S hMS hC)



theorem pCore_two_inf_eq_bot_of_local_shape
    {D : Data G} (hSg : UC6S846.SigmaStd D) (h67 : UC6.R6_7 D)
    {X H E : Subgroup G} (hHtop : H ≠ ⊤) (hHM : ¬ H ≤ D.M)
    (hXHM : X ≤ H ⊓ D.M) (hperf : ⁅X, X⁆ = X)
    (hbar : IsSL3 (Bar2 X) 2 ∨ IsSU3 (Bar2 X) 3)
    (hEX : E ≤ X) (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 2)
    (hΓE : rankThreeGamma 1 3 E ≤ D.M) : pCoreOf 2 (H ⊓ D.M) = ⊥ := by
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXM : X ≤ D.M := hXHM.trans inf_le_right
  have hEM : E ≤ D.M := hEX.trans hXM
  have hEH : E ≤ H := hEX.trans (hXHM.trans inf_le_left)
  by_contra hne
  have hEnt : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card E = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
      rw [hcon a a.2, hcon b b.2]
    rw [hEcard] at h1
    norm_num at h1
  obtain ⟨e, heE, he1⟩ := hEnt
  have hns : ¬ Group.IsSolvable ↥D.M := by
    intro hsol
    have : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXM)
        (Subgroup.inclusion_injective hXM)
    have hXtop : commutator ↥X = ⊤ := by
      apply Subgroup.map_injective X.subtype_injective
      rw [Subgroup.map_top, Subgroup.range_subtype, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top, Subgroup.range_subtype]
      exact hperf
    have : Nontrivial ↥X :=
      nontrivial_of_ne (⟨e, hEX heE⟩ : ↥X) 1 fun h => he1 (congrArg Subtype.val h)
    exact (IsSolvable.commutator_lt_top_of_nontrivial ↥X).ne hXtop
  have hsig : D.sig ⊆ D.sig1 := UC6S846.sig_subset_sig1 hSg hns
  obtain ⟨-, t, ht2, hpt, L₀, hL₀H, hL₀n, hHeq, hshape⟩ :=
    h67 hsig 3 Nat.prime_three (by norm_num) E hEM hEel hEcard hΓE H hEH hHtop hne hHM
  have hXt : X ≤ centralizer ({t} : Set G) := r5o_centralizes_of_pCoreOf hXHM ht2 hpt
  have hXN : X ≤ normalizer (L₀ : Set G) :=
    (hXHM.trans inf_le_left).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hL₀H).1 hL₀n)
  have hXc : X ≤ centralizer (L₀ : Set G) := by
    rcases hshape with hgf | ⟨-, hA⟩
    · rcases hgf with ⟨hK, hind⟩ | ⟨K₁, K₂, hL₀eq, hcomm, h₁, h₂, -, hi₁, hi₂⟩
      · exact r5o_graphField_commute r5o_graphField_quotTrivial hK hind ht2
          hperf hXN hXt
      · rw [hL₀eq] at hXN ⊢
        obtain ⟨hN₁, hN₂⟩ := r5o_prod_normalizes hcomm h₁ h₂ hperf hXN
        have hc₁ := r5o_graphField_commute r5o_graphField_quotTrivial
          (Or.inr h₁) hi₁ ht2 hperf hN₁ hXt
        have hc₂ := r5o_graphField_commute r5o_graphField_quotTrivial
          (Or.inr h₂) hi₂ ht2 hperf hN₂ hXt
        intro x hx
        have hx₁ := Subgroup.mem_centralizer_iff.1 (hc₁ hx)
        have hx₂ := Subgroup.mem_centralizer_iff.1 (hc₂ hx)
        refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        have hle : K₁ ⊔ K₂ ≤ centralizer ({x} : Set G) :=
          sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hx₁ k hk))
            (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hx₂ k hk))
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
    · exact r5o_alt_commute hperf hbar hXN hXt hA
  have he3 : e ^ 3 = 1 := hEel.2 e heE
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hY : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.2 heE
  have hYcard : Nat.card (Subgroup.zpowers e) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hord]
    norm_num
  have hYrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers e) :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl (hEel.mono hY) hYcard
  have hNM : normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) ≤ D.M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 E D.M).1 hΓE (Subgroup.zpowers e) hY
      hYrank
  have hL₀M : L₀ ≤ D.M := by
    intro l hl
    apply hNM
    have hlc : l ∈ centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hXc (hEX heE)) l hl)
    have hlc' : l ∈ centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hlc
    exact Subgroup.centralizer_le_normalizer _ hlc'
  exact hHM (hHeq ▸ sup_le inf_le_right hL₀M)



end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
