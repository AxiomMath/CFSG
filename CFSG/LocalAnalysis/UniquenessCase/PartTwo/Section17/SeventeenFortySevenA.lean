module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanProductRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFactsSmallRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Defs
public import CFSG.Quasithin.Vol2.Ch11SecA15Theta
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwo

public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
theorem s17_47_L_eq_X {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h : IsL3 (BarInf L) n) (h43 : R17_43At D V₀ V)
    (h44_1 : R17_44_1AtB D V₀ V) (h44_3 : R17_44_3AtB D V₀ V)
    (hK4 : Inputs1719.K_CartanRankLeThree)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwo)
    (hK17 : Inputs1719.K_L3CartanThree)
    (hN : uc22p20rNativeGriess) :
    L = X := by
  classical
  by_contra hLX
  have hB : Inputs1719.BorelChevOver (BarInf L) n :=
    Inputs1719.BorelChevOver.of_on hK3 h (by decide)
  have hL : L ∈ calC D.M := ctx.mem_calC
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := uc22p22l_odd_center_quotient
  have hmodelK : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 3 2 n :=
    LieModel.of_mulEquiv (uc22p21k_barInf_equiv_of_calC hL).some h
  have hZcard : Nat.card (Subgroup.center (Bar2 L)) ∣ 3 := by
    have hZ := uc22p20v_card_center_dvd hN hq hodd hmodelK
    simp only [CFSG.Blueprint.Multiplier.genericOrders] at hZ
    exact hZ.trans (by simpa using Nat.gcd_dvd_left 3 (2 ^ n - 1))
  have hΓ2 : 2 ≤ Gamma.ncard := by
    rw [ctx.ncard_Gamma_eq_card_conjSet]
    have hpos : 0 < (conjSetOf D.M L).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨L, ⟨1, D.M.one_mem, by ext y; simp⟩⟩
    have hne1 : (conjSetOf D.M L).ncard ≠ 1 := fun h1 =>
      hLX (ctx.X_eq.trans (uc22s217_conjClosure_eq_of_ncard_eq_one h1)).symm
    omega
  have h43' : 2 < 2 ^ n := h43 L X p n l C Dc Gamma ctx
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp at h43'
    · exact hn
  rcases lt_or_eq_of_le hn2 with hlt | heq
  ·
    obtain ⟨r, hr, hrdvd, hr3⟩ :=
      CFSG.Quasithin.Vol2.Ch11.SecA.exists_prime_gt_three_dvd (by omega : 3 ≤ n)
    have hr2 : r ≠ 2 := by have := hr.two_le; omega
    have hZr : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L)) := by
      intro hd
      rcases (Nat.dvd_prime Nat.prime_three).mp (hd.trans hZcard) with h1 | h3
      · exact hr.ne_one h1
      · omega
    have hC2 : 2 ≤ CFSG.Open.pRank r C := by
      have hbound := cartanRank_le_pRank_cartan_on (hK4 := hK4) (t := .PSL) (m := 3)
        (n := n) (r := r) hL ctx.cartan (by decide) h hr hr2 hrdvd
        (fun _ hd => by have := Nat.le_of_dvd (by norm_num : 0 < 3) hd; omega)
        (fun h => absurd h (by decide))
      simpa [CS17LieRank] using hbound
    have hprod := ctx.ncard_mul_pRank_le_pRank_Dc (r := r) hr hr2 hZr
    have hle3 : CFSG.Open.pRank r Dc ≤ 3 :=
      h44_1 L X p n l C Dc Gamma ctx n hB r hr hr2
    have hle1 : Gamma.ncard ≤ 1 := by
      have h1 : Gamma.ncard * 2 ≤ CFSG.Open.pRank r Dc :=
        (Nat.mul_le_mul_left Gamma.ncard hC2).trans hprod
      omega
    omega
  ·
    have h2n : n = 2 := heq.symm
    have hC3 : (if 3 ∣ Nat.card (Subgroup.center (Bar2 L)) then 2 else 1) ≤
        CFSG.Open.pRank 3 C := by
      let Smap : Subgroup (Bar2 L) :=
        ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      have hS : CFSG.QuasithinUnique.IsSylowTwoOf Smap ⊤ := isSylowTwoOf_sylowBar2 hL
      have happ := hK17 (Bar2 L) n h.admissible (by rw [h2n]; exact ⟨1, rfl⟩) hmodelK
        hq hodd Smap hS
      have hO2 : CFSG.pCore 2 ↥L ≤ (D.T ⊓ L).subgroupOf L := pCore_le_sylow_of_mem_calC hL
      have htrans : CFSG.Open.pRank 3 (⊤ : Subgroup
            (TauCeti.Subgroup.normalizerQuotient ((D.T ⊓ L).subgroupOf L))) =
          CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Smap)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
          (CFSG.GroupTheory.normalizerQuotient_quotientEquiv (CFSG.pCore 2 ↥L)
            ((D.T ⊓ L).subgroupOf L) hO2)
      have hcoeeq : CFSG.pRank 3 ↥(⊤ : Subgroup
            (TauCeti.Subgroup.normalizerQuotient Smap)) =
          CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient Smap)) :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top 3 _).trans
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
      have hbridge := pRank_normalizerQuotient_le_pRank_cartan hL ctx.cartan
        Nat.prime_three (by norm_num)
      exact (happ.trans (le_of_eq hcoeeq)).trans (htrans.symm ▸ hbridge)
    have hLrank : 2 ≤ CFSG.Open.pRank 3 L := by
      by_cases h3Z : 3 ∣ Nat.card (Subgroup.center (Bar2 L))
      · have hC2 : 2 ≤ CFSG.Open.pRank 3 C := by
          have h' := hC3
          rwa [if_pos h3Z] at h'
        exact hC2.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) ctx.cartan.1)
      · have hZ1 : Nat.card (Subgroup.center (Bar2 L)) = 1 := by
          rcases (Nat.dvd_prime Nat.prime_three).mp hZcard with h1 | h3
          · exact h1
          · exact absurd (by rw [h3]) h3Z
        have hZbot : Subgroup.center (Bar2 L) = ⊥ := Subgroup.card_eq_one.mp hZ1
        obtain ⟨e0⟩ := uc22p21k_barInf_equiv_of_center_bot hq hZbot
        obtain ⟨-, Kf, hFld, hFin, hKcard, ⟨e1⟩⟩ :=
          (LieModel.classical_iff (t := .PSL) (n := 3) (p := 2) (f := 2) (by decide)).1
            (h2n ▸ h)
        have htop : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := by
          have he : Bar2 L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 Kf) :=
            e0.symm.trans e1
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) he]
          exact CFSG.Quasithin.A3Facts.psl_three_four_two_le_pRank hKcard
        rwa [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_bar_top Nat.prime_three
          (by norm_num) L] at htop
    obtain ⟨γ, hγ⟩ := (Set.ncard_pos (Set.toFinite Gamma)).mp (by omega : 0 < Gamma.ncard)
    obtain ⟨δ, hδ, hδγ⟩ :=
      Set.exists_ne_of_one_lt_ncard (show 1 < Gamma.ncard by omega) γ
    let K1 : Subgroup (Bar2 X) := barImage X (CFSG.Quasithin.conjSubgroup L γ)
    let K2 : Subgroup (Bar2 X) := barImage X (CFSG.Quasithin.conjSubgroup L δ)
    have hmem : ∀ θ ∈ Gamma, CFSG.Quasithin.conjSubgroup L θ ∈ conjSetOf D.M L :=
      fun θ hθ => ⟨θ⁻¹, D.M.inv_mem (ctx.reps.1 hθ).1, rfl⟩
    have hcomp : ∀ θ ∈ Gamma, CFSG.IsComponent (barImage X (CFSG.Quasithin.conjSubgroup L θ)) :=
      fun θ hθ => s13_barImage_isComponent (mem_calC_of_mem_conjSetOf ctx (hmem θ hθ))
    have hle : ∀ θ ∈ Gamma, CFSG.Quasithin.conjSubgroup L θ ≤ X := by
      intro θ hθ
      rw [ctx.X_eq]
      exact le_iSup₂_of_le _ (hmem θ hθ) le_rfl
    have hKrank : ∀ θ ∈ Gamma, 2 ≤ CFSG.Open.pRank 3
        (barImage X (CFSG.Quasithin.conjSubgroup L θ)) := by
      intro θ hθ
      rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_barImage Nat.prime_three
        (by norm_num) (hle θ hθ), pRank_conjSubgroup_eq Nat.prime_three]
      exact hLrank
    have hKcomm : ⁅K1, K2⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute (hcomp γ hγ) (hcomp δ hδ)).resolve_left
        (fun heq' => hδγ (ctx.barImage_conjSubgroup_injOn_Gamma hγ hδ heq').symm)
    have hcent : K2 ≤ Subgroup.centralizer (K1 : Set (Bar2 X)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K2) (H₂ := K1)).mp
        ((Subgroup.commutator_comm K2 K1).trans hKcomm)
    have hcenter_le : K1 ⊓ K2 ≤ (Subgroup.center K1).map K1.subtype := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hx.2) (y : Bar2 X) y.2)
    have hZc : Nat.card (Subgroup.center K1) ∣ 3 :=
      ctx.card_center_barImage_conjSubgroup hγ ▸ hZcard
    have hcard_inf : Nat.card ↥(K1 ⊓ K2) ∣ 3 := by
      have h1 : Nat.card ↥(K1 ⊓ K2) ∣ Nat.card ↥((Subgroup.center K1).map K1.subtype) :=
        Subgroup.card_dvd_of_le hcenter_le
      rw [Subgroup.card_map_of_injective K1.subtype_injective] at h1
      exact h1.trans hZc
    have hdisj : CFSG.Open.pRank 3 (K1 ⊓ K2) ≤ 1 := by
      refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 3) (H := K1 ⊓ K2) (k := 1) ?_
      intro E hE _
      have hdvd : Nat.card E ∣ 3 := (Subgroup.card_dvd_of_le hE).trans hcard_inf
      simpa using Nat.le_of_dvd (by norm_num) hdvd
    have hcomm2 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (hcent hb) a ha
    have h2f := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_add_pRank_inf
      (A := K1) (B := K2) hcomm2 Nat.prime_three
    have hK1rank : 2 ≤ CFSG.Open.pRank 3 K1 := hKrank γ hγ
    have hK2rank : 2 ≤ CFSG.Open.pRank 3 K2 := hKrank δ hδ
    have hsup : 3 ≤ CFSG.Open.pRank 3 (K1 ⊔ K2) := by omega
    have hXrank : 2 < CFSG.Open.pRank 3 X := by
      have hbarX : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 X)) := by
        have hle' : CFSG.Open.pRank 3 (K1 ⊔ K2) ≤
            CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 X)) :=
          CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top
        omega
      rwa [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_bar_top Nat.prime_three
        (by norm_num) X] at hbarX
    have hDc1 : CFSG.Open.pRank 3 Dc ≤ 1 :=
      (h44_3 L X p n l C Dc Gamma ctx n hB).2 (Or.inr hXrank)
    have hDc2 : 2 ≤ CFSG.Open.pRank 3 Dc := by
      by_cases h3Z : 3 ∣ Nat.card (Subgroup.center (Bar2 L))
      · have hC2 : 2 ≤ CFSG.Open.pRank 3 C := by
          have h' := hC3
          rwa [if_pos h3Z] at h'
        exact hC2.trans (pRank_cartan_le_pRank_Dc (ctx := ctx) Nat.prime_three)
      · have hC1 : 1 ≤ CFSG.Open.pRank 3 C := by
          have h' := hC3
          rwa [if_neg h3Z] at h'
        have hP := ctx.ncard_mul_pRank_le_pRank_Dc Nat.prime_three (by norm_num) h3Z
        have hmul : Gamma.ncard ≤ Gamma.ncard * CFSG.Open.pRank 3 C := by
          simpa using Nat.mul_le_mul_left Gamma.ncard hC1
        omega
    omega

theorem s17_47_isSL3Four_of_q4 {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hLX : L = X) (h : IsL3 (BarInf L) 2) (hN : uc22p20rNativeGriess) :
    IsSL3 (Bar2 L) 2 ∧ Nat.card (Subgroup.center (Bar2 L)) = 3 := by
  have hL : L ∈ calC D.M := ctx.mem_calC
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := uc22p22l_odd_center_quotient
  have hmodelK : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 3 2 2 :=
    LieModel.of_mulEquiv (uc22p21k_barInf_equiv_of_calC hL).some h
  have hZcard : Nat.card (Subgroup.center (Bar2 L)) ∣ 3 := by
    have hZ := uc22p20v_card_center_dvd hN hq hodd hmodelK
    simp only [CFSG.Blueprint.Multiplier.genericOrders] at hZ
    exact hZ.trans (by simpa using Nat.gcd_dvd_left 3 (2 ^ 2 - 1))
  have hZne : Subgroup.center (Bar2 L) ≠ ⊥ := by
    intro hbot
    have hL3 : IsL3 (Bar2 L) 2 :=
      LieModel.of_mulEquiv (uc22p21k_quotCenter_equiv hbot).some hmodelK
    refine ctx.counter (Concl17_42.of_p1 (Or.inr (Or.inr ?_)))
    rwa [← hLX]
  refine ⟨isSL3_of_isL3_barInf hL h, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hZcard with h1 | h3
  · exact absurd (Subgroup.card_eq_one.mp h1) hZne
  · exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
