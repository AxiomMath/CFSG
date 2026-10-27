module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanGlue
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanProjection
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanMemberOut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1MovingLine
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1Absorb
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1SolvBlock
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRankOneOfRk1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

open scoped MatrixGroups

section Local

variable {G : Type} [Group G] [Finite G]

private theorem ggL1_card_eq {F : Type} [Field F] [Finite F] {θ : SL(2, F) →* G}
    (hθinj : Function.Injective θ) {S : Subgroup G} (hθrange : θ.range = S) :
    Nat.card ↥S = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← hθrange, ← ggSL2_card F]
  exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm

private theorem ggL1_four_le_card {F : Type} [Field F] [Finite F] [CharP F 2]
    (h6 : Nat.card F * (Nat.card F ^ 2 - 1) ≠ 6) : 4 ≤ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn] at h6 ⊢
  rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
  · have hn1 : (n : ℕ) = 1 := by have := n.pos; omega
    rw [hn1] at h6
    norm_num at h6
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h

private theorem ggL1_perfect_of_quasisimple {S : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple ↥S) :
    ⁅S, S⁆ = S := by
  rw [← Subgroup.map_subtype_commutator, hq.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem ggL1_hyperplane_le (Bs : Subgroup G) (r : MulAut ↥Bs) : ggHyperplane Bs r ≤ Bs :=
  Subgroup.map_subtype_le _

theorem ggL1_fixes_of_le_centralizer {Bs X : Subgroup G} {y : G} (hy : y ∈ Bs)
    (hXy : X ≤ Subgroup.centralizer ({y} : Set G)) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer X Bs) : y ∈ ggHyperplane Bs φ := by
  obtain ⟨g, hgX, -, hact⟩ := mem_ggAutomizer_iff.mp hφ
  have hgy : g * y * g⁻¹ = y := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hXy hgX)
    rw [h]; group
  refine ⟨⟨y, hy⟩, ?_, rfl⟩
  change φ ⟨y, hy⟩ = ⟨y, hy⟩
  apply Subtype.ext
  rw [hact]
  exact hgy

end Local

section Seed

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem ggL1_seed_of_concl (ha₀ : GGLNoncyclicInput)
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer (Bs : Set G)))
    (hOutL : CFSG.Quasithin.OutSolvable ↥L)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) (hrefl : GGIsReflection p r)
    (h6 : Nat.card ↥(ggRankOneIn L Bs r) ≠ 6) (hRkL : GGRk1Concl p Bs L r) :
    ggRankOnePerf Bs r = ggRankOneIn L Bs r := by
  obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
  have hBs : IsElemAbelian p Bs := ggRouteCfg_isElemAbelian hcfg
  have hr2 : r * r = 1 := by simpa [pow_two] using hrefl.1
  have hrC : r ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hrefl
  obtain ⟨F, _, _, θ, hchar, hinj, hrange, ⟨n, hnS, hnN, hnact⟩, -, -, -⟩ := id hRkL
  obtain ⟨hSq, -⟩ := ggRankOneIn_isQuasisimple_of_concl hRkL h6
  have hSperf : ⁅ggRankOneIn L Bs r, ggRankOneIn L Bs r⁆ = ggRankOneIn L Bs r :=
    ggL1_perfect_of_quasisimple hSq
  have hSL : ggRankOneIn L Bs r ≤ L := (ggOTwoPrime_le _).trans inf_le_left
  have hxBs : x ∈ Bs := SecFiveL1Odd.le_bstar hcfg hcfg.1.1.2.2.1.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hxH : x ∈ ggHyperplane Bs r := ggL1_fixes_of_le_centralizer hxBs hLx hrA
  have hMx : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (by simpa using hxH)
  have hMN : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun g hg => mem_normalizer_of_sstar hcfg.1.1.1.2.2.2.2.2.2.1
      (ha₀ G p B x L hcfg.1.1.1) (hMx hg)
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  have hHBs : ggHyperplane Bs r ≤ Bs := ggL1_hyperplane_le Bs r
  have hHN : ggHyperplane Bs r ≤ Subgroup.normalizer (L : Set G) := hHBs.trans hBsN
  have hPN : ggRankOnePerf Bs r ≤ Subgroup.normalizer (L : Set G) :=
    (perfectCore_le _).trans hMN
  have hpi := ggRankOnePerf_le_of_normalizer_outSolvable hHN hPN hOutL
  have hBsHL : Bs ≤ ggHyperplane Bs r ⊔ L :=
    ggBs_le_hyperplane_sup_of_rep hpp hp2 hBs hr2 hBsN (hSL hnS) hnact
  have hker : Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer (Bs : Set G) := by
    rw [SecFiveL1Solv.commonKernel hHBs hBsHL]
    exact inf_le_right
  haveI := hsolv
  have hsolv' : Group.IsSolvable ↥(Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer (ggHyperplane Bs r : Set G)) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hker)
  exact ggRankOnePerf_eq_of_solvable_pieces hSperf hpi hsolv'

theorem ggL1_seed (hRk1 : GGSecFiveRk1PhanInput) (ha₀ : GGLNoncyclicInput)
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer (Bs : Set G)))
    (hOutL : CFSG.Quasithin.OutSolvable ↥L)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) (hrefl : GGIsReflection p r)
    (h6 : Nat.card ↥(ggRankOneIn L Bs r) ≠ 6) :
    ggRankOnePerf Bs r = ggRankOneIn L Bs r :=
  ggL1_seed_of_concl ha₀ hsolv hOutL hcfg hns hpres h3 hrA hrefl h6
    (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 L (Or.inl rfl) r hrA
      (ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hrefl))

end Seed

section Transfer

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem ggL1_nbr_subnormal (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) :
    ∃ y : G, y ∈ Bs ∧ X ≤ Subgroup.centralizer ({y} : Set G) ∧
      IsSubnormal X (Subgroup.centralizer ({y} : Set G)) := by
  rcases hX with rfl | ⟨y, hy⟩
  · exact ⟨x, SecFiveL1Odd.le_bstar hcfg hcfg.1.1.2.2.1.2.2.2.1,
      hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1, hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1⟩
  · obtain ⟨-, hyB, -, hXC, ⟨-, hsub, -, -⟩, -⟩ := hy.1
    exact ⟨y, hcfg.1.1.2.1.1 hyB, hXC, hsub⟩

private theorem ggL1_absorb_nbr_aux
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hr₀C : r₀ ∈ ggCoxRefl M e)
    (h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6)
    (hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) (hRkL : GGRk1Concl p Bs L r₀)
    {n : G} (hnS : n ∈ ggRankOneIn X Bs r)
    (hnact : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) :
    ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r ∧
      CFSG.Assembly.IsQuasisimple ↥(ggRankOnePerf Bs r) ∧
      60 ≤ Nat.card ↥(ggRankOnePerf Bs r) := by
  obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
  have hBs : IsElemAbelian p Bs := ggRouteCfg_isElemAbelian hcfg
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hr2 : r * r = 1 := by simpa [pow_two] using hrefl.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 h3
  obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr₀C hrC
  obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_top L Bs 𝒦 haA)
  have hPconj : (ggRankOnePerf Bs r₀).map (MulAut.conj g).toMonoidHom = ggRankOnePerf Bs r := by
    rw [ggRankOnePerf_map_conj hg r₀, ← hra]
  obtain ⟨hS₀q, -⟩ := ggRankOneIn_isQuasisimple_of_concl hRkL h6₀
  obtain ⟨F₀, _, _, θ₀, hchar₀, hinj₀, hrange₀, ⟨n₀, hn₀S, -, hn₀act⟩, -, -, -⟩ := id hRkL
  have hP₀q : CFSG.Assembly.IsQuasisimple ↥(ggRankOnePerf Bs r₀) := by rw [hseed]; exact hS₀q
  have hPq : CFSG.Assembly.IsQuasisimple ↥(ggRankOnePerf Bs r) := by
    rw [← hPconj]
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      ((ggRankOnePerf Bs r₀).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm hP₀q
  have hcard₀ : Nat.card ↥(ggRankOneIn L Bs r₀) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) :=
    ggL1_card_eq hinj₀ hrange₀
  haveI := hchar₀
  have h4₀ : 4 ≤ Nat.card F₀ := ggL1_four_le_card (hcard₀ ▸ h6₀)
  have h60 : 60 ≤ Nat.card ↥(ggRankOnePerf Bs r) := by
    have h1 : Nat.card ↥(ggRankOnePerf Bs r) = Nat.card ↥(ggRankOnePerf Bs r₀) := by
      rw [← hPconj]
      exact (Nat.card_congr ((ggRankOnePerf Bs r₀).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    rw [h1, hseed, hcard₀]
    have h15 : 15 ≤ Nat.card F₀ ^ 2 - 1 := by
      have : 16 ≤ Nat.card F₀ ^ 2 := by simpa using Nat.pow_le_pow_left h4₀ 2
      omega
    calc (60 : ℕ) = 4 * 15 := by norm_num
      _ ≤ Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := Nat.mul_le_mul h4₀ h15
  obtain ⟨b', hb'⟩ := ggExists_moved_of_isReflection hpp hrefl
  have hBsN₀ : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  set b : ↥Bs := a⁻¹ b' with hbdef
  have hab : a b = b' := by simp [hbdef]
  have hrb : r b' = a (r₀ b) := by
    rw [hra]; simp [hbdef, MulAut.mul_apply]
  set u₀ : G := (b : G) * ((r₀ b : ↥Bs) : G)⁻¹ with hu₀def
  have hu₀S : u₀ ∈ ggRankOneIn L Bs r₀ :=
    ggMovingElem_mem_rankOneIn hBs hBsN₀ hn₀S hn₀act b
  have hu : g * u₀ * g⁻¹ = (b' : G) * ((r b' : ↥Bs) : G)⁻¹ := by
    have e1 : g * (b : G) * g⁻¹ = (b' : G) := by rw [← hg b, hab]
    have e2 : g * ((r₀ b : ↥Bs) : G) * g⁻¹ = ((r b' : ↥Bs) : G) := by rw [← hg (r₀ b), ← hrb]
    calc g * u₀ * g⁻¹ = (g * (b : G) * g⁻¹) * (g * ((r₀ b : ↥Bs) : G) * g⁻¹)⁻¹ := by
          rw [hu₀def]; group
      _ = _ := by rw [e1, e2]
  have huP : (b' : G) * ((r b' : ↥Bs) : G)⁻¹ ∈ ggRankOnePerf Bs r := by
    rw [← hPconj, ← hu]
    refine Subgroup.mem_map.mpr ⟨u₀, ?_, by simp [MulAut.conj_apply]⟩
    rw [hseed]
    exact hu₀S
  have hnX : n ∈ X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) := ggOTwoPrime_le _ hnS
  have hnu : n * ((b' : G) * ((r b' : ↥Bs) : G)⁻¹) ≠ ((b' : G) * ((r b' : ↥Bs) : G)⁻¹) * n :=
    ggMovingElem_noncomm hpp hp2 hBs hr2 hnact hb'
  obtain ⟨y, hyBs, hXy, hXS⟩ := ggL1_nbr_subnormal hcfg hX
  have hyH : y ∈ ggHyperplane Bs r := ggL1_fixes_of_le_centralizer hyBs hXy hrA
  have hMZ : Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤
      Subgroup.centralizer ({y} : Set G) :=
    Subgroup.centralizer_le (by simpa using hyH)
  exact ⟨ggRankOnePerf_le_rankOneIn_of_subnormal hXS hMZ hPq hnX huP hnu, hPq, h60⟩

theorem ggL1_absorb_nbr
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hr₀A : r₀ ∈ ggAutomizer L Bs) (hr₀C : r₀ ∈ ggCoxRefl M e)
    (h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6)
    (hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) (hRkL : GGRk1Concl p Bs L r₀)
    {n : G} (hnS : n ∈ ggRankOneIn X Bs r) (hnN : n ∈ Subgroup.normalizer (Bs : Set G))
    (hnact : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) :
    ggRankOnePerf Bs r ≤ ggRankOneIn X Bs r ∧
      CFSG.Assembly.IsQuasisimple ↥(ggRankOnePerf Bs r) := by
  obtain ⟨hPS, hPq, -⟩ :=
    ggL1_absorb_nbr_aux hcfg hpres h3 hr₀C h6₀ hseed hX hrA hrC hRkL hnS hnact
  exact ⟨hPS, hPq⟩

theorem ggL1_absorb_nbr_card_ge_sixty
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hr₀A : r₀ ∈ ggAutomizer L Bs) (hr₀C : r₀ ∈ ggCoxRefl M e)
    (h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6)
    (hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) (hRkL : GGRk1Concl p Bs L r₀)
    {n : G} (hnS : n ∈ ggRankOneIn X Bs r) (hnN : n ∈ Subgroup.normalizer (Bs : Set G))
    (hnact : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) :
    60 ≤ Nat.card ↥(ggRankOneIn X Bs r) := by
  obtain ⟨hPS, -, h60⟩ :=
    ggL1_absorb_nbr_aux hcfg hpres h3 hr₀C h6₀ hseed hX hrA hrC hRkL hnS hnact
  exact h60.trans (Subgroup.card_le_of_le hPS)

theorem ggL1_absorb_nbr_ne_six
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hr₀A : r₀ ∈ ggAutomizer L Bs) (hr₀C : r₀ ∈ ggCoxRefl M e)
    (h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6)
    (hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) (hRkL : GGRk1Concl p Bs L r₀)
    {n : G} (hnS : n ∈ ggRankOneIn X Bs r) (hnN : n ∈ Subgroup.normalizer (Bs : Set G))
    (hnact : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) :
    Nat.card ↥(ggRankOneIn X Bs r) ≠ 6 := by
  have h60 := ggL1_absorb_nbr_card_ge_sixty hcfg hns hpres h3 hr₀A hr₀C h6₀ hseed hX hrA hrC
    hRkL hnS hnN hnact
  omega

theorem ggL1_transfer_nbr
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hr₀A : r₀ ∈ ggAutomizer L Bs) (hr₀C : r₀ ∈ ggCoxRefl M e)
    (h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6)
    (hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) (hRkL : GGRk1Concl p Bs L r₀)
    (hRkX : GGRk1Concl p Bs X r) :
    ggRankOnePerf Bs r = ggRankOneIn X Bs r := by
  obtain ⟨_, _, _, _, _, _, _, ⟨n, hnS, hnN, hnact⟩, -⟩ := id hRkX
  obtain ⟨hPS, -⟩ :=
    ggL1_absorb_nbr hcfg hns hpres h3 hr₀A hr₀C h6₀ hseed hX hrA hrC hRkL hnS hnN hnact
  have h6X := ggL1_absorb_nbr_ne_six hcfg hns hpres h3 hr₀A hr₀C h6₀ hseed hX hrA hrC hRkL
    hnS hnN hnact
  obtain ⟨hSXq, -⟩ := ggRankOneIn_isQuasisimple_of_concl hRkX h6X
  exact (ggRankOnePerf_eq_iff_rankOneIn_perfect hPS).mpr (ggL1_perfect_of_quasisimple hSXq)

theorem ggL1_transfer (hRk1 : GGSecFiveRk1PhanInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hr₀A : r₀ ∈ ggAutomizer L Bs) (hr₀C : r₀ ∈ ggCoxRefl M e)
    (h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6)
    (hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hrC : r ∈ ggCoxRefl M e) :
    ggRankOnePerf Bs r = ggRankOneIn X Bs r :=
  ggL1_transfer_nbr hcfg hns hpres h3 hr₀A hr₀C h6₀ hseed (hX.imp_right (hcfg.2.2.2.1.2 X)) hrA hrC
    (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 L (Or.inl rfl) r₀ hr₀A hr₀C)
    (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX r hrA hrC)

end Transfer

end CFSG.StandardType

end
