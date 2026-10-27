module

public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
public import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseE8TwoFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGRk1ConclExSix
import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
import CFSG.LocalAnalysis.StandardType.GGTWReflConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Obstruction

theorem GGRk1ConclEx.eq_one_of_mem_center {p : ℕ} {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {r : MulAut ↥Bs} (h : GGRk1ConclEx p Bs X r) {z : ↥X}
    (hz : z ∈ Subgroup.center ↥X)
    (hzH : (z : G) ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G)) {k : ℕ}
    (hk : z ^ 2 ^ k = 1) : z = 1 := by
  obtain ⟨F, hF, -, θ, hchar, hinj, hrange, -, -, -, -, -, -⟩ := h
  letI : Field F := hF
  letI : CharP F 2 := hchar
  have hz2 : (z : G) ^ (2 ^ k) = 1 := by
    simpa using congrArg (fun w : ↥X => (w : G)) hk
  have hzR : (z : G) ∈ ggRankOneIn X Bs r :=
    Subgroup.subset_closure ⟨⟨z.2, hzH⟩, k, hz2⟩
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (hrange ▸ hzR)
  have hcenter : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply hinj
    rw [map_mul, map_mul, hs]
    have htX : θ t ∈ X := by
      have ht : θ t ∈ ggRankOneIn X Bs r := hrange ▸ MonoidHom.mem_range.mpr ⟨t, rfl⟩
      exact (ggOTwoPrime_le (X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G))) ht |>.1
    simpa using congrArg (fun w : ↥X => (w : G))
      ((Subgroup.mem_center_iff.mp hz) ⟨θ t, htX⟩)
  obtain ⟨c, hc2, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc2)
  have hs1 : s = 1 := by
    apply Subtype.ext
    rw [← hcA, hc1]
    simpa using map_one (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F)
  refine Subtype.ext ?_
  rw [← hs, hs1, map_one]
  rfl

end Obstruction

theorem GGConfig.odd_card_center_of_innerDiagOnLabel {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hlt : B < Bs) {S : ℕ → LargeEvenLabel → Prop} (h : GGInnerDiagOnLabel S p Bs X) :
    Odd (Nat.card (Subgroup.center ↥X)) := by
  refine hcfg.odd_card_center_of_B_lt_Bs hlt ?_
  exact GGDichotomy.marking_elim_const
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) h)

section Holds

theorem ggRk1ConclEx_of_esu_nbr_of_odd {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hXns : ¬ GGSplitLie p X)
    {P : ℕ → LargeEvenLabel → Prop} (hP : ∀ p lab, P p lab → ggRowP_ESU p lab)
    (h : GGInnerDiagOnLabel P p Bs X) (hodd : Odd (Nat.card (Subgroup.center ↥X)))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) :
    GGRk1ConclEx p Bs X r := by
  obtain ⟨-, K, _, _, _, f, n, ψ, -, -, -, hcard, hn, hker, hrange, hdvd, hacts, hlab⟩ :=
    ggNSLie_cover_of_esu_odd hP hodd h
  exact ggRk1ConclEx_of_unitaryCover_nbr hcfg hpres hX hXns hcard hn hker hrange hdvd hacts hlab
    hrA hrC

theorem ggRk1ConclEx_of_esu_nbr_of_lt {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hXns : ¬ GGSplitLie p X)
    {P : ℕ → LargeEvenLabel → Prop} (hP : ∀ p lab, P p lab → ggRowP_ESU p lab)
    (h : GGInnerDiagOnLabel P p Bs X) (hlt : B < Bs)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) :
    GGRk1ConclEx p Bs X r :=
  ggRk1ConclEx_of_esu_nbr_of_odd hcfg hpres hX hXns hP h
    (GGConfig.odd_card_center_of_innerDiagOnLabel hcfg.1.1 hlt h) hrA hrC

theorem ggRk1ConclEx_of_esuTwo_cell {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {X : Subgroup G}
    (hX : X = L ∨ X ∈ 𝒦 ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hXns : ¬ GGSplitLie p X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧
      (lab.rank = 3 ∨ (lab.rank = 5 ∧ X ≠ L))) p Bs X)
    (hlt : X ≠ L → B < Bs) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  by_cases hXL : X = L
  · subst hXL
    refine absurd (h.mono_label (fun lab hlab => ?_)) (not_ggInnerDiagOnLabel_unitary_four hcfg.1.1)
    obtain ⟨hESU, -, hr⟩ := hlab
    have hr3 : lab.rank = 3 := hr.resolve_right (fun h5 => h5.2 rfl)
    rcases hESU.1 with ⟨ht, -⟩ | ⟨ht, -⟩
    · exact ⟨Or.inl ht, hr3, hESU.2⟩
    · exact ⟨Or.inr ht, hr3, hESU.2⟩
  · have hnb : ∃ y : G, GGNbr p B x D J y X := by
      rcases hX with h1 | hK | hw
      · exact absurd h1 hXL
      · exact (GGSecFiveWeakNbr.of_mem hcfg hK).1
      · exact hw.1
    exact fun r hrA hrC => ggRk1ConclEx_of_esu_nbr_of_lt hcfg hpres (Or.inr hnb) hXns
      (fun _ _ hl => hl.1) h (hlt hXL) hrA hrC

end Holds

section WeylTypeA

private theorem mem_ggCoxRefl_of_typeA {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 2 ≤ n)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W : Subgroup (MulAut ↥Bs)} {f : (CoxeterMatrix.A n).Group ≃* ↥W}
    (hf : ∀ i, GGIsReflection p ((f ((CoxeterMatrix.A n).simple i) : ↥W) : MulAut ↥Bs))
    {s : MulAut ↥Bs} (hs : s ∈ W) (hr : GGIsReflection p s) :
    s ∈ ggCoxRefl (CoxeterMatrix.A n) f := by
  obtain ⟨w, hw, i, hsi⟩ :=
    ggTW_refl_conj_of_typeA hp2 hn hBs (Equiv.refl (Fin n))
      (ggCoxeterMatrix_reindex_refl (CoxeterMatrix.A n)).symm W f
      (fun i => ((f ((CoxeterMatrix.A n).simple i) : ↥W) : MulAut ↥Bs)) (fun _ => rfl) hf s hs hr
  obtain ⟨u, hu⟩ := MulEquiv.surjective f ⟨w, hw⟩
  refine ⟨u, i, ?_⟩
  have hcoe : ((f u : ↥W) : MulAut ↥Bs) = w := by rw [hu]
  rw [hsi]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hcoe]

theorem GGWeylOfType.exists_conj_of_typeA {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p (CoxeterMatrix.A n) W)
    {r₀ r : MulAut ↥Bs} (hr₀ : r₀ ∈ W) (hr₀R : GGIsReflection p r₀)
    (hr : r ∈ W) (hrR : GGIsReflection p r) :
    ∃ a ∈ W, r = a * r₀ * a⁻¹ := by
  obtain ⟨f, hf⟩ := hW
  have hWeyl : GGIsWeylMatrix (CoxeterMatrix.A n) :=
    Or.inl ⟨n, Equiv.refl (Fin n), by omega,
      Or.inl (ggCoxeterMatrix_reindex_refl (CoxeterMatrix.A n)).symm⟩
  have h3 : ∀ i j : Fin n, i ≠ j → (CoxeterMatrix.A n).M i j ≤ 3 :=
    GGIsWeylMatrixAD.le_three (Or.inl ⟨n, Equiv.refl (Fin n), hn,
      (ggCoxeterMatrix_reindex_refl (CoxeterMatrix.A n)).symm⟩)
  have hconn : GGSimplyLacedConnected (CoxeterMatrix.A n) :=
    ggSimplyLacedConnected_of_weyl hWeyl h3
  exact ggCoxRefl_conj_of_connected f hconn
    (mem_ggCoxRefl_of_typeA hp2 (by omega) hBs hf hr₀ hr₀R)
    (mem_ggCoxRefl_of_typeA hp2 (by omega) hBs hf hr hrR)

end WeylTypeA

section TwA5TwoL

theorem ggRk1ConclEx_of_twA5_two_L (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hA : ¬ (GGIsWeylMatrixA M ∧
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card ↥(ggRankOneIn L Bs r) ≠ 6))
    (hns : ¬ GGSplitLie p L) (hU : ¬ GGMemberUnitary p Bs L)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs L r := by
  by_cases hsix : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      Nat.card ↥(ggRankOneIn L Bs r) ≠ 6
  · exfalso
    have hTA : ¬ GGIsWeylMatrixA M := fun hA' => hA ⟨hA', hsix⟩
    by_cases hD : NSJoin.NSTypeD M
    · exact NSJoin.not_innerDiagOnLabel_two_L_typeD hTB hU62 hcfg hpres hD hns hU hsix
        (h.mono_label (fun lab hl => hl.2.1))
    · exact NSJoin.false_of_twA5_two_L_typeE hTB hU62 hcfg hpres
        (GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 hle3 hTA hD) hsix h
  · push Not at hsix
    obtain ⟨r₀, hr₀A, hr₀C, hr₀6⟩ := hsix
    have hconf : GGConfig p B Bs x L D J := hcfg.1.1
    have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) →
        (b : G) ∈ Subgroup.zpowers x := by
      obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
      intro b hb
      exact hTB G p B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K' hN
        (hcfg.2.1 y K' hN) (Or.inr hcfg.2.1) b hb
    obtain ⟨rfl, hW, -⟩ := nsQ2U62_weyl hconf hFix h
    have hBs : IsElemAbelian 3 Bs := ggRouteCfg_isElemAbelian hcfg
    have hr₀R : GGIsReflection 3 r₀ := ggCoxRefl_isReflection hpres.2 hr₀C
    have hconc₀ : GGRk1ConclEx 3 Bs L r₀ := by
      obtain ⟨lab, hΛ, hhas, -, -, -, -, -, hrow, -⟩ := largeEvenMarking_exists_hasLabel h
      have htag : lab.tag = .twA := by
        rcases hrow.1.1 with ⟨ht, -⟩ | ⟨ht, hr3⟩
        · exact ht
        · omega
      refine ggRk1ConclEx_of_card_six rfl hns hr₀A hr₀R.1 hr₀6 ⟨lab, hΛ, hhas⟩ ?_
      intro lab' hΛ' hhas'
      have hn := NSJoin.ggLabelIso_n_eq (ggLabelRigidInput_holds lab lab' _ hΛ hΛ' hhas hhas')
        (by rw [htag]; decide) (fun ht => by rw [htag] at ht; exact absurd ht (by decide))
      omega
    intro r hrA hrC
    have hrR : GGIsReflection 3 r := ggCoxRefl_isReflection hpres.2 hrC
    obtain ⟨a, ha, hconj⟩ := GGWeylOfType.exists_conj_of_typeA (p := 3) (n := 5)
      (by norm_num) (by norm_num) hBs hW hr₀A hr₀R hrA hrR
    rw [hconj]
    exact ggRk1ConclEx_conj hconc₀ ha

end TwA5TwoL

end CFSG.StandardType

end
