module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.LieType.Steinberg.CentralExt.SUThreeThree
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNbrRefl
import CFSG.LocalAnalysis.StandardType.GGRankOneRootMatch
import CFSG.LocalAnalysis.StandardType.GGRankOneTags
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.Models.UnitaryPairs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open CFSG.ClassicalInvolution.Models CFSG.LieType.Steinberg

open scoped MatrixGroups

private lemma ggPhanNSARk1Aux_le_three_A (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (CoxeterMatrix.A m).M i j ≤ 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

theorem ggPhanNSARk1Aux_blockEmb_range (K : Type) [Field K] [Finite K]
    (p f : ℕ) [Fact p.Prime] [CharP K p] {n : ℕ} (hn : 2 ≤ n) :
    (blockEmb K p f n 2 0 (by omega)).range =
      ggSuPairBlock K p f n (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
  apply le_antisymm
  · rintro x ⟨A, rfl⟩
    intro i j hij
    rw [coe_coe_blockEmb]
    rcases hij with ⟨hi0, hi1⟩ | ⟨hj0, hj1⟩
    · refine blockMat_apply_of_not_mem_left _ (a := i) (fun hc => ?_) j
      have hi0' : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      have hi1' : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
      omega
    · refine blockMat_apply_of_not_mem_right _ i (fun hc => ?_)
      have hj0' : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      have hj1' : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
      omega
  · intro x hx
    have h0 : 0 + 2 ≤ n := by omega
    set M : Matrix (Fin 2) (Fin 2) K :=
      Matrix.of fun u v => suMat x (blockIdx 0 h0 u) (blockIdx 0 h0 v) with hMdef
    have hblock : blockMat n 0 M = suMat x := by
      ext a b
      rw [blockMat_apply]
      by_cases ha : a.val < 2
      · by_cases hb : b.val < 2
        · rw [dite_eq_left ⟨⟨Nat.zero_le _, by omega⟩, ⟨Nat.zero_le _, by omega⟩⟩, hMdef]
          exact congrArg₂ (suMat x) (Fin.ext (by simp [blockIdx])) (Fin.ext (by simp [blockIdx]))
        · rw [dite_eq_right (by intro h; exact hb (by omega))]
          symm
          apply hx
          right
          exact ⟨fun h => hb (by rw [h]; simp), fun h => hb (by rw [h]; simp)⟩
      · rw [dite_eq_right (by intro h; exact ha (by omega))]
        symm
        apply hx
        left
        exact ⟨fun h => ha (by rw [h]; simp), fun h => ha (by rw [h]; simp)⟩
    have hdet : M.det = 1 := by
      rw [← det_blockMat (m := n) (i := 0) (k := 2) h0 M, hblock, det_suMat]
    have hiso : conjTr (unitaryInvolution K p f) M * M = 1 := by
      have hx1 : conjTr (unitaryInvolution K p f) (suMat x) * suMat x = 1 := x.2.2
      rw [← hblock, conjTr_blockMat, ← blockMat_mul h0] at hx1
      exact blockMat_injective h0 (by rw [hx1, blockMat_one])
    refine ⟨mkSU K p f M hdet hiso, ?_⟩
    apply suMat_injective
    rw [suMat_blockEmb, suMat_mkSU, hblock]

private theorem ggPhanNSARk1Aux_exists_sl2_range_rankOne {K : Type*} [Group K]
    {D : UniversalRootDatum K}
    {k : Type*} [Field k] (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective φ ∧
      φ.range = CFSG.LieType.CurtisTits.rankOne D.rootGroup i := by
  unfold GGRankOneModel at hM
  obtain ⟨x, C, O, hE, -⟩ := hM
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  refine ⟨φ, hφinj, ?_⟩
  apply le_antisymm
  · rintro y ⟨M, rfl⟩
    have hM' : M ∈ Subgroup.closure
        (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
          Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) := by
      rw [CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top]
      exact Subgroup.mem_top M
    have hs : (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
        Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ := by
      rintro x (hx | hx)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Upper c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφu c]
        exact Subgroup.mem_sup_left
          (((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Lower c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφl c]
        exact Subgroup.mem_sup_right
          (((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
    exact Subgroup.mem_comap.mp
      (Subgroup.mem_closure.mp hM'
        ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ) hs)
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ φ.range
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, by rw [hφu c, hc]⟩
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Lower c, by rw [hφl c, hc]⟩

theorem ggLabel_n_eq_of_twA (hRig : GGLabelRigidInput) {R : Type} [Group R] {b f : ℕ} (hb : 3 ≤ b)
    (hf : 1 ≤ f) (hl : GGHasLabel ⟨.twA, b, f⟩ R) {lab' : LargeEvenLabel}
    (hlam' : LargeEvenInLambda2 lab') (hl' : GGHasLabel lab' R) : lab'.n = f := by
  have hlam : LargeEvenInLambda2 (⟨.twA, b, f⟩ : LargeEvenLabel) :=
    ⟨hf, show 2 ≤ b by omega, fun h => absurd (show b = 2 from h) (by omega)⟩
  rcases hRig _ _ R hlam hlam' hl hl' with h | h | h | h | h | h | h | h <;>
    first
    | (subst h; rfl)
    | (exfalso; simp at h; done)
    | (obtain ⟨-, h2⟩ := h; subst h2; rfl)

theorem ggSecFiveRk1PhanA_of_nonSplit
    (hNS : GGSecFiveNSKGPosAInput) (hL1 : GGSecFiveL1PhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (htypeA : ∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) (hXs : ¬ GGSplitLie p X) :
    (∃ r₀ ∈ ggAutomizer X Bs, r₀ ∈ ggCoxRefl M e) ∧
      ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
        ∃ (F : Type) (_ : Field F) (_ : Finite F)
          (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
          Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
          (∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
            ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
          (GGSplitLie p X → p ∣ Nat.card F - 1) ∧
          (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
          ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
            GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    obtain ⟨m, σ, -, hM⟩ := htypeA
    intro i j hij
    rw [hM, CoxeterMatrix.reindex_apply]
    exact ggPhanNSARk1Aux_le_three_A m (σ.symm i) (σ.symm j)
      (fun h => hij (σ.symm.injective h))
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  obtain ⟨K, hKfield, hKfin, hKchar, f, n, ψ, hKcard, hn4, hker, hrange, hpf, hpos, hlab⟩ :=
    hNS G p B Bs x L D J 𝒦 hcfg hns ι M e hpres htypeA hbig X hX hXs
  unfold GGTableBPosSU at hpos
  obtain ⟨ε, hεrefl, hεlevi⟩ := hpos
  have hn2 : 2 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  let r₀ : MulAut ↥Bs :=
    ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
  have hr₀A : r₀ ∈ ggAutomizer X Bs := (ε (Equiv.swap a b)).2
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin hX hr₀A) (hεrefl a b hab)
  have hlevi : ggRankOneIn X Bs r₀ = (ggSuPairBlock K 2 f n a b).map ψ := hεlevi a b hab
  have hperf₀ : ggRankOnePerf Bs r₀ = ggRankOneIn X Bs r₀ :=
    hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX r₀ hr₀A hr₀C
  refine ⟨⟨r₀, hr₀A, hr₀C⟩, fun r hrA hrC => ?_⟩
  have hperf : ggRankOnePerf Bs r = ggRankOneIn X Bs r :=
    hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX r hrA hrC
  obtain ⟨aa, haaA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr₀C hrC
  obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_top L Bs 𝒦 haaA)
  have hconj : (ggRankOnePerf Bs r₀).map (MulAut.conj g).toMonoidHom =
      ggRankOnePerf Bs r := by
    rw [ggRankOnePerf_map_conj hg r₀, ← hra]
  have hblockrange : (blockEmb K 2 f n 2 0 (by omega)).range = ggSuPairBlock K 2 f n a b := by
    simpa [a, b] using ggPhanNSARk1Aux_blockEmb_range K 2 f hn2
  obtain ⟨eSL⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUThreeThree.nonempty_sl2_mulEquiv_SUid_two
      (p := 2) (f := f) hKcard
  let blockMap : Su K 2 f 2 →* Su K 2 f n := blockEmb K 2 f n 2 0 (by omega)
  let θ₀ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f) →* G :=
    ψ.comp (blockMap.comp eSL.toMonoidHom)
  have hblockMap_inj : Function.Injective blockMap := blockEmb_injective (by omega)
  have hφ : Function.Injective (blockMap.comp eSL.toMonoidHom) :=
    hblockMap_inj.comp eSL.injective
  haveI : CharP (fixedSubfield K 2 f) 2 := inferInstance
  have hθ₀inj : Function.Injective θ₀ :=
    PsiDiag.injective_comp_of_ker_le_center (blockMap.comp eSL.toMonoidHom) hφ ψ hker
  have hrangeθ₀ : θ₀.range = ggRankOneIn X Bs r₀ := by
    change (ψ.comp (blockMap.comp eSL.toMonoidHom)).range = ggRankOneIn X Bs r₀
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr eSL.surjective, Subgroup.map_top, hblockrange, ← hlevi]
  let θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f) →* G :=
    (MulAut.conj g).toMonoidHom.comp θ₀
  have hθinj : Function.Injective θ := (MulAut.conj g).injective.comp hθ₀inj
  have hθrange : θ.range = ggRankOneIn X Bs r := by
    change ((MulAut.conj g).toMonoidHom.comp θ₀).range = ggRankOneIn X Bs r
    rw [MonoidHom.range_comp, hrangeθ₀, ← hperf₀, hconj, hperf]
  have hr2 : r * r = 1 := by
    have h := (ggCoxRefl_isReflection hpres.2 hrC).1
    simpa [pow_two] using h
  obtain ⟨n', hn'in, hn'N, hn'act⟩ := ggExists_weylElt_of_mem_ggAutomizer hrA hr2
  refine ⟨fixedSubfield K 2 f, inferInstance, inferInstance, θ, ?_, hθinj, hθrange,
    ⟨n', hn'in, hn'N, hn'act⟩, ?_, ?_, ?_⟩
  · exact inferInstance
  · intro hs
    exact absurd hs hXs
  · intro _
    rw [card_fixedSubfield hKcard]
    exact hpf
  · intro lab' hlam' hl'
    obtain ⟨bb, hnb, hlabX⟩ := hlab
    have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · exfalso
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        rw [hKcard, h0] at h1
        norm_num at h1
      · exact h0
    have hnn : lab'.n = f :=
      ggLabel_n_eq_of_twA ggLabelRigidInput_holds (by omega) hf1 hlabX hlam' hl'
    exact le_of_eq (by rw [card_fixedSubfield hKcard, hnn])

theorem ggSecFiveRk1PhanAInput_of_nsKGPos
    (hNS : GGSecFiveNSKGPosAInput) (hL1 : GGSecFiveL1PhanInput) : GGSecFiveRk1PhanAInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres htypeA
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    obtain ⟨m, σ, -, hM⟩ := htypeA
    intro i j hij
    rw [hM, CoxeterMatrix.reindex_apply]
    exact ggPhanNSARk1Aux_le_three_A m (σ.symm i) (σ.symm j)
      (fun h => hij (σ.symm.injective h))
  intro hbig X hX r hrA hrC
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  by_cases hXs : GGSplitLie p X
  · exfalso
    obtain ⟨t, n, f, ψ, hadm, h3, hker, hrange, htag, hpf, hpos⟩ :=
      ggSecFiveKGPosAt_splitMember (G := G) (p := p) (B := B) (Bs := Bs) (x := x)
        (L := L) (D := D) (J := J) (𝒦 := 𝒦) hcfg hX hXs
    unfold GGTableBPos at hpos
    obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
    have hrk : 2 ≤ (ggU t n f).D.rank :=
      two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm h3
    let i₁ : Fin (ggU t n f).D.rank := ⟨0, by omega⟩
    let r₀ : MulAut ↥Bs :=
      ((ε ((CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁) :
        ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
    have hr₀A : r₀ ∈ ggAutomizer X Bs :=
      (ε ((CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁)).2
    have hr₀C : r₀ ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
        (ggAutomizer_le_ggAutomizerJoin hX hr₀A) (hεrefl i₁)
    have hperf₀ : ggRankOnePerf Bs r₀ = ggRankOneIn X Bs r₀ :=
      hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX r₀ hr₀A hr₀C
    have hperf : ggRankOnePerf Bs r = ggRankOneIn X Bs r :=
      hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX r hrA hrC
    have hlevi₁ : ggRankOneIn X Bs r₀ =
        (ggRootLevi (ggU t n f).D (Pi.single i₁ 1)).map ψ := by
      have h := hεlevi 1 i₁
      simp only [one_mul, inv_one, mul_one, map_one, Module.End.one_apply] at h
      exact h
    obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr₀C hrC
    obtain ⟨g, -, -, hg⟩ :=
      mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_top L Bs 𝒦 haA)
    have hconj : (ggRankOnePerf Bs r₀).map (MulAut.conj g).toMonoidHom = ggRankOnePerf Bs r := by
      rw [ggRankOnePerf_map_conj hg r₀, ← hra]
    have hMod : GGRankOneModel (ggU t n f).D (GaloisField 2 f) :=
      ggRankOneModel_of_tag htag hadm h3
    obtain ⟨φ, hφinj, hφrange⟩ := ggPhanNSARk1Aux_exists_sl2_range_rankOne hMod i₁
    let θ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* G :=
      (MulAut.conj g).toMonoidHom.comp (ψ.comp φ)
    haveI hchar : CharP (GaloisField 2 f) 2 := inferInstance
    have hψφinj : Function.Injective (ψ.comp φ) :=
      PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker
    have hθinj : Function.Injective θ := (MulAut.conj g).injective.comp hψφinj
    have hθrange : θ.range = ggRankOneIn X Bs r := by
      change ((MulAut.conj g).toMonoidHom.comp (ψ.comp φ)).range = ggRankOneIn X Bs r
      rw [← MonoidHom.map_range (MulAut.conj g).toMonoidHom (ψ.comp φ)]
      rw [← MonoidHom.map_range ψ φ]
      rw [hφrange]
      have hlevi' : (CFSG.LieType.CurtisTits.rankOne (ggU t n f).D.rootGroup i₁).map ψ =
          (ggRootLevi (ggU t n f).D (Pi.single i₁ 1)).map ψ := rfl
      rw [hlevi']
      rw [← hlevi₁]
      rw [← hperf₀]
      rw [hconj, hperf]
    obtain ⟨⟨rL, hrLA, hrLC⟩, hLdata⟩ :=
      ggSecFiveRk1PhanA_of_nonSplit hNS hL1 hcfg hns hpres htypeA hbig (Or.inl rfl) hns
    obtain ⟨F, hF, hFfin, θL, -, hθLinj, hθLrange, -, -, hpF, -⟩ := hLdata rL hrLA hrLC
    obtain ⟨aL, haLA, hraL⟩ := ggCoxRefl_conj_of_connected e hconn hrLC hrC
    have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs :=
      ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
    obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
    have hperfL : ggRankOnePerf Bs rL = ggRankOneIn L Bs rL :=
      hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) rL hrLA hrLC
    have hc₀ : Nat.card (ggRankOnePerf Bs rL) = Nat.card SL(2, F) := by
      rw [hperfL, ← hθLrange]
      exact Nat.card_congr (MonoidHom.ofInjective hθLinj).toEquiv.symm
    have hc : Nat.card (ggRankOnePerf Bs r) = Nat.card SL(2, GaloisField 2 f) := by
      rw [hperf, ← hθrange]
      exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
    have hcr : Nat.card (ggRankOnePerf Bs r) = Nat.card (ggRankOnePerf Bs rL) := by
      rw [hraL]
      exact (ggRankOnePerf_conj_card_le (hAH haLA) rL).1
    have hFF : Nat.card F = Nat.card (GaloisField 2 f) :=
      ggSL2_card_inj (by rw [← hc₀, ← hc, hcr])
    have hq : 1 ≤ Nat.card F := le_of_lt Finite.one_lt_card
    have h1 : p ∣ Nat.card F + 1 := hpF hns
    have h2 : p ∣ Nat.card F - 1 := by
      rw [hFF, GaloisField.card 2 f (by have hf : 1 ≤ f := hadm.2.1; omega)]
      exact hpf
    have h3' : p ∣ 2 := by
      have h4 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub h1 h2
      have h5 : (Nat.card F + 1) - (Nat.card F - 1) = 2 := by omega
      rwa [h5] at h4
    have h6 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3'
    have h7 : 2 ≤ p := hpp.two_le
    omega
  · exact (ggSecFiveRk1PhanA_of_nonSplit hNS hL1 hcfg hns hpres htypeA hbig hX hXs).2 r hrA hrC

end CFSG.StandardType

end
