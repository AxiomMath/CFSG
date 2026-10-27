module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFitting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsUniqueN
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s2338_exists_b1 (D : Data G) {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (hn3 : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ c.n) :
    ∃ b1 : G, b1 ∈ c.B0 ∧ b1 ≠ 1 ∧
      b1 ∈ CFSG.Quasithin.opResidual 3 c.B0 := by
  have hn : 3 ≤ c.n := hn3 h1930 c
  obtain ⟨p, hp, hpdvd, hpne3⟩ := uc22p20o_prime_sub_one_ne_three hn
  have hpi : p ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hp, hpdvd⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b1, hb1ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) p hpi.2
  have hb1ordG : orderOf (b1 : G) = p := by
    rw [Subgroup.orderOf_coe, hb1ord]
  refine ⟨(b1 : G), b1.2, ?_, ?_⟩
  · intro h1
    have hord1 : orderOf (b1 : G) = 1 := by rw [h1, orderOf_one]
    rw [hb1ordG] at hord1
    exact hp.ne_one hord1
  · refine CFSG.Quasithin.mem_opResidual_of_coprime b1.2 ?_
    rw [hb1ordG]
    exact (Nat.coprime_primes hp Nat.prime_three).mpr hpne3

theorem uc22s2338_b1bar_centralizes_layer
    (D : Data G) (Ch : Choice2011 G) (h37 : S23_37 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {b1 : G} (hb1B0 : b1 ∈ c.B0) (hb1res : b1 ∈ CFSG.Quasithin.opResidual 3 c.B0) :
    uc22p21cPi D.M (⟨b1, c.hBM hb1B0⟩ : ↥D.M) ∈
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
  let c' : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  let bbar : Bar2 D.M := uc22p21cPi D.M ⟨b1, c.hBM hb1B0⟩
  have hb1res' : b1 ∈ CFSG.Quasithin.opResidual 3 c'.B := hb1res
  have hKbar : ∀ K ∈ calC D.M,
      bbar ∈ Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) := by
    intro K hK
    have h37K : ⁅CFSG.Quasithin.opResidual 3 c'.B, K⁆ ≤ CFSG.Open.pCoreOf 2 K :=
      (h37 h1930 c' K hK).2
    have hcommP : ∀ k ∈ K, ⁅b1, k⁆ ∈ CFSG.Open.pCoreOf 2 D.M := by
      intro k hk
      have hmem : ⁅b1, k⁆ ∈ ⁅CFSG.Quasithin.opResidual 3 c'.B, K⁆ :=
        Subgroup.commutator_mem_commutator hb1res' hk
      exact (uc22p21c_pCoreOf_le_of_subnormal hK.1) (h37K hmem)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, hmK, rfl⟩ := uc22p21c_mem_barImage.1 hy
    have hbm : (b1 : G) ∈ D.M := c.hBM hb1B0
    have hxM : ⁅b1, (m : G)⁆ ∈ D.M := by
      rw [commutatorElement_def]
      exact D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hbm m.2) (D.M.inv_mem hbm)) (D.M.inv_mem m.2)
    have hpcmem : ⁅b1, (m : G)⁆ ∈ CFSG.Open.pCoreOf 2 D.M := hcommP (m : G) hmK
    have hq : uc22p21cPi D.M ⟨⁅b1, (m : G)⁆, hxM⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((CFSG.mem_openPCoreOf_iff ⟨_, hxM⟩).1 hpcmem)
    have hmap : uc22p21cPi D.M ⟨⁅b1, (m : G)⁆, hxM⟩ = ⁅bbar, uc22p21cPi D.M m⁆ := by
      rw [← map_commutatorElement (uc22p21cPi D.M) (⟨b1, hbm⟩ : ↥D.M) m]
      congr 1
    have hcomm : ⁅bbar, uc22p21cPi D.M m⁆ = 1 := by rw [← hmap]; exact hq
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  have hcentC : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C →
      bbar ∈ Subgroup.centralizer (C : Set (Bar2 D.M)) := by
    intro C hC
    obtain ⟨K, hK, hKC⟩ := uc22p21c_exists_calC_of_component D.M hC
    rw [← hKC]
    exact hKbar K hK
  have hlayer_le : CFSG.layer (Bar2 D.M) ≤
      Subgroup.centralizer ({bbar} : Set (Bar2 D.M)) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le ?_
    intro C hC
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hcentC C hC) x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hlayer_le hy)

theorem uc22s2338_barImage_closure_le_centralizer_layer
    (D : Data G) (Ch : Choice2011 G) (h37 : S23_37 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {b1 : G} (hb1B0 : b1 ∈ c.B0) (hb1res : b1 ∈ CFSG.Quasithin.opResidual 3 c.B0)
    {Y : Subgroup G} (hYM : Y ≤ D.M) :
    barImage D.M (Subgroup.closure {x : G | ∃ s ∈ Y, x = ⁅s, b1⁆}) ≤
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
  have hbbar_centE : uc22p21cPi D.M (⟨b1, c.hBM hb1B0⟩ : ↥D.M) ∈
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) :=
    uc22s2338_b1bar_centralizes_layer D Ch h37 h1930 c hb1B0 hb1res
  haveI hEchar : (CFSG.layer (Bar2 D.M)).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hEnorm : (CFSG.layer (Bar2 D.M)).Normal := Subgroup.normal_of_characteristic _
  haveI hCnorm : (Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M))).Normal :=
    Subgroup.normal_centralizer
  have hpre : Subgroup.closure {x : G | ∃ s ∈ Y, x = ⁅s, b1⁆} ≤
      barPreimage D.M (Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M))) :=
    closure_le_barPreimage hYM (c.hBM hb1B0) hCnorm hbbar_centE
  calc barImage D.M (Subgroup.closure {x : G | ∃ s ∈ Y, x = ⁅s, b1⁆})
      ≤ barImage D.M (barPreimage D.M
          (Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)))) :=
        barImage_mono hpre
    _ = Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) :=
        barImage_barPreimage D.M _

theorem le_pCoreOf_two_of_barImage_centralizes
    {M R : Subgroup G} (hRM : R ≤ M) (hR2 : IsPGroup 2 R)
    (hF : barImage M R ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 M) : Set (Bar2 M)))
    (hE : barImage M R ≤
      Subgroup.centralizer (CFSG.layer (Bar2 M) : Set (Bar2 M))) :
    R ≤ CFSG.Open.pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRbar2 : IsPGroup 2 (barImage M R) := by
    change IsPGroup 2 ((R.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
    exact (hR2.comap_subtype (K := M)).map _
  have hRbar_le_F : barImage M R ≤ CFSG.fittingSubgroup (Bar2 M) := by
    have h : barImage M R ≤
        Subgroup.centralizer (CFSG.generalizedFitting (Bar2 M) : Set (Bar2 M)) := by
      rw [CFSG.generalizedFitting.eq_sup]
      exact Subgroup.le_centralizer_iff.mpr (sup_le
        (Subgroup.le_centralizer_iff.mp hF) (Subgroup.le_centralizer_iff.mp hE))
    exact h.trans
      (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup (G := Bar2 M))
  have hbot : barImage M R = ⊥ := le_bot_iff.mp
    ((CFSG.ABGLocalTools.le_pCore_of_isPGroup_of_le_fitting hRbar2 hRbar_le_F).trans
      (le_of_eq (uc22p20c_pCore_quotient_pCore (H := ↥M) (p := 2))))
  exact le_pCoreOf_of_barImage_eq_bot hRM hbot

end CFSG.LocalAnalysis.UniquenessCase.UC22
