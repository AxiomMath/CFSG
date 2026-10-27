module

public import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwo
public import CFSG.LocalAnalysis.StandardType.GGTwA5TwoMemberSize
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGRk1ConclExSix
import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwoNbr
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem exists_rankOne_card_six_of_twA5_member
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hBB : B = Bs) {X : Subgroup G} (hX : X ∈ 𝒦)
    (h : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs X)
    (h720 : Nat.card ↥(ggAutomizer X Bs) = 720) :
    ∃ r ∈ ggAutomizer X Bs, GGIsReflection 3 r ∧
      Nat.card ↥(ggRankOneIn X Bs r) = 6 := by
  obtain ⟨y, hnbr⟩ := hcfg.2.2.2.1.2 X hX
  have hcentX : Nat.card ↥(B ⊓ Subgroup.centralizer (X : Set G)) = 3 :=
    ggNSPosPD_routeCfg_cent_K Nat.prime_three hnbr
  have hcentBsX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    have h := hcentX
    rw [hBB] at h
    exact h.le
  have h3pow : 720 ≤ Nat.card ↥(ggAutomizer X Bs) →
      3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥X = ⊥ :=
    fun _ => GGSecFiveRouteCfg.three_pow_six_le_card_or_center_eq_bot_of_twA5_member
      hTB hcfg hpres hle3 hBB hX hlab h720
  obtain ⟨K, _hf, _hfin, lab, m', θ, hK, -, hmrank, hSide, hdvd, hperf, -, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore h (fun p lab hl => hl.1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn, hr5⟩ := hSide
  change n = 1 at hn
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  exact ggNsq2Member_exists_rankOne_of_or hU62 hcfg hcentX hcentBsX hK hdvd θ hperf hBsN hbs
    h3pow

theorem ggRk1ConclEx_of_twA5_two_member
    (hRig : GGLabelRigidInput) (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hBB : B = Bs) {X : Subgroup G} (hX : X ∈ 𝒦)
    (hnsX : ¬ GGSplitLie p X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  have hp3 : p = 3 := by
    obtain ⟨hp, -, -, -, -⟩ := hcfg.1.1.tableB_facts
    obtain ⟨-, lab, -, hraw⟩ := h
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨⟨hrow, hn1, -⟩, -, -⟩ := hP
    refine (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ?_
    have h := hrow.2
    rw [hn1] at h
    norm_num at h
    exact h
  subst hp3
  have hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)
      3 Bs X := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) h
    obtain ⟨⟨hrow, hn1, hr5⟩, hN', hBsI⟩ := hP
    refine ⟨⟨?_, hr5, hn1⟩, hN', hBsI⟩
    rcases hrow.1 with ⟨htw, -⟩ | ⟨-, hr3⟩
    · exact htw
    · omega
  have hW : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer X Bs) :=
    (nsQ2U62_member_weyl hRig hLB hPJ hcfg hBB hX hlab).1
  have h720 : Nat.card ↥(ggAutomizer X Bs) = 720 := by
    obtain ⟨eA, -⟩ := hW
    obtain ⟨eP, -⟩ := ggCoxeterA_mulEquivPerm 5
    rw [← Nat.card_congr eA.toEquiv, Nat.card_congr eP.toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  obtain ⟨r₀, hr₀A, hr₀R, hr₀6⟩ :=
    exists_rankOne_card_six_of_twA5_member hTB hU62 hcfg hpres hle3 hBB hX h hlab h720
  intro r hrA hrC
  exact ggRk1ConclEx_of_twA5_two_of_card_six hRig (ggRouteCfg_isElemAbelian hcfg) hnsX h hW
    hr₀A hr₀R hr₀6 r hrA (ggCoxRefl_isReflection hpres.2 hrC)

theorem ggRk1ConclEx_of_twA5_two_ne_L
    (hRig : GGLabelRigidInput) (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hBB : B = Bs) {X : Subgroup G}
    (hX : X = L ∨
      (X ∈ 𝒦 ∧ ¬ (NSJoin.NSTypeD M ∧
        ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) ∨
      (T M ∧ (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) ∧
        GGSecFiveWeakNbr p B Bs x L D J 𝒦 X))
    (hXL : X ≠ L) (hnsX : ¬ GGSplitLie p X)
    (hQ4X : ¬ NSJoin.NSTypeD M →
      (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
      p = 3 → GGInnerDiagOnLabel GGLabQFour p Bs X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  rcases hX with hXL' | ⟨hXK, -⟩ | ⟨-, hbig, hnb⟩
  · exact absurd hXL' hXL
  · exact ggRk1ConclEx_of_twA5_two_member hRig hTB hU62 hLB hPJ hcfg hpres hle3 hBB hXK hnsX h
  have hp3 : p = 3 := NSJoin.eq_three_of_innerDiagOnLabel_n_one (ggRouteCfg_prime hcfg).1
    (fun _ hl => ⟨hl.2.1, hl.1.2⟩) h
  by_cases hD : NSJoin.NSTypeD M
  · obtain ⟨y, hy⟩ := hnb.1
    have hC := ggNSPosPD_routeCfg_cent_K (ggRouteCfg_prime hcfg).1 hy
    rw [hBB] at hC
    exact ggRk1ConclEx_of_twA5_two_nbr hRig hTB hU62 hLB hPJ hcfg hpres (Or.inr hD) hnb hnsX h
      (by omega)
  refine absurd (hQ4X hD hbig hp3) (NSJoin.not_innerDiagOnLabel_qFour_of_n_one hRig
    (fun lab hl => ⟨hl.2.1, ?_, fun _ => by rw [hl.2.2]; decide⟩) h)
  rcases hl.1.1 with ⟨ht, -⟩ | ⟨ht, -⟩ <;> rw [ht] <;> decide

end CFSG.StandardType

end
