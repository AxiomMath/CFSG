module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.ClassicalInvolution.Phan.Standard
import CFSG.ClassicalInvolution.Phan.Center
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

private theorem ggPhanNSAGenAux_block_eq (K : Type) [Field K] [Finite K] (p f m : ℕ)
    [Fact p.Prime] [CharP K p] (i : Fin m) :
    ggSuPairBlock K p f (m + 1) (blockIdx (i : ℕ) (by omega) (0 : Fin 2))
        (blockIdx (i : ℕ) (by omega) (1 : Fin 2)) =
      (blockEmb2 K p f m i).range := by
  rw [blockEmb2]
  apply le_antisymm
  ·
    intro A hA
    let Bm : Matrix (Fin 2) (Fin 2) K :=
      Matrix.of fun x y => (((A : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
        (blockIdx (i : ℕ) (by omega) x) (blockIdx (i : ℕ) (by omega) y)
    have hAmat : (((A : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        blockMat (m + 1) (i : ℕ) Bm := by
      ext x y
      rw [blockMat_apply]
      by_cases hxy : ((i : ℕ) ≤ (x : ℕ) ∧ (x : ℕ) < (i : ℕ) + 2) ∧
          ((i : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) < (i : ℕ) + 2)
      · rw [dif_pos hxy]
        obtain ⟨⟨hix, hxi⟩, hyx, hyi⟩ := hxy
        simp only [Bm, Matrix.of_apply]
        refine congrArg₂ _ ?_ ?_
        · apply Fin.ext
          rw [blockIdx_val]
          show (x : ℕ) = (i : ℕ) + ((x : ℕ) - (i : ℕ))
          omega
        · apply Fin.ext
          rw [blockIdx_val]
          show (y : ℕ) = (i : ℕ) + ((y : ℕ) - (i : ℕ))
          omega
      · rw [dif_neg hxy]
        exact hA x y (by
          rcases not_and_or.mp hxy with hx | hy
          · left
            exact ⟨fun hx0 => hx (by rw [hx0, blockIdx_val]; omega),
              fun hx1 => hx (by rw [hx1, blockIdx_val]; omega)⟩
          · right
            exact ⟨fun hy0 => hy (by rw [hy0, blockIdx_val]; omega),
              fun hy1 => hy (by rw [hy1, blockIdx_val]; omega)⟩)
    have hBdet : Bm.det = 1 := by
      have h1 : (blockMat (m + 1) (i : ℕ) Bm).det = 1 := by rw [← hAmat]; exact A.2.1
      rwa [det_blockMat (by omega : (i : ℕ) + 2 ≤ m + 1)] at h1
    have hBiso : conjTr (unitaryInvolution K p f) Bm * Bm = 1 := by
      have h2 := A.2.2
      rw [hAmat, conjTr_blockMat,
        ← blockMat_mul (by omega : (i : ℕ) + 2 ≤ m + 1)] at h2
      rw [← blockMat_one (m := m + 1) (i := (i : ℕ)) (k := 2) (F := K)] at h2
      exact blockMat_injective (by omega : (i : ℕ) + 2 ≤ m + 1) h2
    let B : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Bm (by rw [hBdet]; norm_num)
    have hBval : (B : Matrix (Fin 2) (Fin 2) K) = Bm :=
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero Bm _
    have hBmem : B ∈ SUid (unitaryInvolution K p f) 2 := by
      rw [mem_SUid, hBval]
      exact ⟨hBdet, hBiso⟩
    rw [MonoidHom.mem_range]
    refine ⟨⟨B, hBmem⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_coe_blockEmb]
    simp only [Subtype.coe_mk]
    rw [hBval]
    exact hAmat.symm
  ·
    rintro A hA
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hA
    intro x y hxy
    rw [coe_coe_blockEmb]
    rcases hxy with ⟨hx0, hx1⟩ | ⟨hy0, hy1⟩
    · refine blockMat_apply_of_not_mem_left _ ?_ y
      rintro ⟨h1, h2⟩
      have hx : (x : ℕ) = (i : ℕ) ∨ (x : ℕ) = (i : ℕ) + 1 := by omega
      rcases hx with hx | hx
      · exact hx0 (Fin.ext (by rw [blockIdx_val]; exact hx))
      · exact hx1 (Fin.ext (by rw [blockIdx_val]; exact hx))
    · refine blockMat_apply_of_not_mem_right _ x ?_
      rintro ⟨h1, h2⟩
      have hy : (y : ℕ) = (i : ℕ) ∨ (y : ℕ) = (i : ℕ) + 1 := by omega
      rcases hy with hy | hy
      · exact hy0 (Fin.ext (by rw [blockIdx_val]; exact hy))
      · exact hy1 (Fin.ext (by rw [blockIdx_val]; exact hy))

private theorem ggPhanNSAGenAux_card_map (K : Type) [Field K] [Finite K] (p f m : ℕ)
    [Fact p.Prime] [CharP K p] {G : Type} [Group G] (ψ : Su K p f (m + 1) →* G)
    (hK : Nat.card K = (p ^ f) ^ 2) (hker : ψ.ker ≤ Subgroup.center (Su K p f (m + 1)))
    (hm : 3 ≤ m + 1) (i : Fin m) :
    Nat.card ((ggSuPairBlock K p f (m + 1) (blockIdx (i : ℕ) (by omega) (0 : Fin 2))
        (blockIdx (i : ℕ) (by omega) (1 : Fin 2))).map ψ) = Nat.card (Su K p f 2) := by
  rw [ggPhanNSAGenAux_block_eq K p f m i, blockEmb2]
  rw [MonoidHom.map_range ψ (blockEmb K p f (m + 1) 2 (i : ℕ)
    (by omega : (i : ℕ) + 2 ≤ m + 1))]
  rw [MonoidHom.range_eq_map (ψ.comp (blockEmb K p f (m + 1) 2 (i : ℕ)
    (by omega : (i : ℕ) + 2 ≤ m + 1)))]
  have hinj : Function.Injective (ψ.comp (blockEmb K p f (m + 1) 2 (i : ℕ)
      (by omega : (i : ℕ) + 2 ≤ m + 1))) :=
    comp_blockEmb_injective hK hker (by omega) (by omega) (by omega)
  rw [Subgroup.card_map_of_injective (K := ⊤) hinj]
  simp

private theorem ggPhanNSAGenAux_card_su_two (K : Type) [Field K] [Finite K] (p f : ℕ)
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (Su K p f 2) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := K) (p := p) (f := f) hK 2
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv]
  exact CFSG.LieType.Steinberg.card_SU_two hK

theorem ggSecFiveGenPhanAInput_of_nsKGPos
    (hNS : GGSecFiveNSKGPosAInput) (hL1 : GGSecFiveL1PhanInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) →
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
          ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
            X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
              ggRankOneIn X Bs r := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres htype hbig X hX hnsX
  have hAD : GGIsWeylMatrixAD M := by
    obtain ⟨m, σ, hm, hMeq⟩ := htype
    exact Or.inl ⟨m, σ, by omega, hMeq⟩
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hAD.le_three
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 h3
  obtain ⟨K, _, _, _, f, n, ψ, hKcard, hn4, hker, hrange, hpdvd, hpos, -⟩ :=
    hNS G p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres htype hbig X hX hnsX
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold GGTableBPosSU at hpos
  obtain ⟨ε, hεrefl, hεpair⟩ := hpos
  have hq : 2 ^ f ≠ 2 := by
    intro hf
    let a : Fin (m + 1) := blockIdx 0 (by omega : 0 + 2 ≤ m + 1) (0 : Fin 2)
    let b : Fin (m + 1) := blockIdx 0 (by omega : 0 + 2 ≤ m + 1) (1 : Fin 2)
    have hab : a ≠ b := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [a, b, blockIdx_val] at hv
      omega
    have hrXA : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggAutomizer X Bs :=
      (ε (Equiv.swap a b)).2
    have hrXC : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (ggAutomizer_le_ggAutomizerJoin hX hrXA) (hεrefl a b hab)
    have h6X : Nat.card (ggRankOneIn X Bs
        ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) = 6 := by
      rw [hεpair a b hab, ggPhanNSAGenAux_card_map K 2 f m ψ hKcard hker (by omega) ⟨0, by omega⟩,
        ggPhanNSAGenAux_card_su_two K 2 f hKcard, hf]
      norm_num
    obtain ⟨KL, _, _, _, fL, nL, ψL, hKLcard, hnL4, hkerL, hrangeL, hpL, hposL, -⟩ :=
      hNS G p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres htype hbig L (Or.inl rfl) hnsL
    obtain ⟨mL, rfl⟩ : ∃ mL, nL = mL + 1 := ⟨nL - 1, by omega⟩
    unfold GGTableBPosSU at hposL
    obtain ⟨εL, hεreflL, hεpairL⟩ := hposL
    let aL : Fin (mL + 1) := blockIdx 0 (by omega : 0 + 2 ≤ mL + 1) (0 : Fin 2)
    let bL : Fin (mL + 1) := blockIdx 0 (by omega : 0 + 2 ≤ mL + 1) (1 : Fin 2)
    have habL : aL ≠ bL := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [aL, bL, blockIdx_val] at hv
      omega
    have hrLA : ((εL (Equiv.swap aL bL) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs :=
      (εL (Equiv.swap aL bL)).2
    have hrLC : ((εL (Equiv.swap aL bL) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrLA) (hεreflL aL bL habL)
    obtain ⟨a', ha'A, hra'⟩ := ggCoxRefl_conj_of_connected e hconn hrLC hrXC
    obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_top L Bs 𝒦 ha'A)
    have hperf : Nat.card (ggRankOnePerf Bs
        ((εL (Equiv.swap aL bL) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) =
        Nat.card (ggRankOnePerf Bs
          ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) := by
      have hmap := ggRankOnePerf_map_conj hg
        ((εL (Equiv.swap aL bL) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
      rw [← hra'] at hmap
      rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hL1X := hL1 G p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres h3 hbig X hX
      ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) hrXA hrXC
    have hL1L := hL1 G p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres h3 hbig L (Or.inl rfl)
      ((εL (Equiv.swap aL bL) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) hrLA hrLC
    have h6perfX : Nat.card (ggRankOnePerf Bs
        ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) = 6 := by
      rw [hL1X]; exact h6X
    have h6inL : Nat.card (ggRankOneIn L Bs
        ((εL (Equiv.swap aL bL) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) = 6 := by
      rw [← hL1L, hperf]; exact h6perfX
    exact hbig ((εL (Equiv.swap aL bL) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) hrLA hrLC h6inL
  refine le_antisymm ?_ ?_
  ·
    conv_lhs => rw [← hrange]
    rw [MonoidHom.range_eq_map, ← iSup_range_blockEmb2 hKcard hq m]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    let a : Fin (m + 1) := blockIdx (i : ℕ) (by omega) (0 : Fin 2)
    let b : Fin (m + 1) := blockIdx (i : ℕ) (by omega) (1 : Fin 2)
    have hab : a ≠ b := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [a, b, blockIdx_val] at hv
      omega
    have hrXA : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggAutomizer X Bs :=
      (ε (Equiv.swap a b)).2
    have hrXC : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (ggAutomizer_le_ggAutomizerJoin hX hrXA) (hεrefl a b hab)
    refine le_trans ?_ (le_iSup₂ (f := fun r (_ : r ∈ {r : MulAut ↥Bs |
        r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e}) => ggRankOneIn X Bs r) _ ⟨hrXA, hrXC⟩)
    rw [hεpair a b hab]
    rw [ggPhanNSAGenAux_block_eq K 2 f m i]
  ·
    exact iSup₂_le fun r _ => ggRankOneIn_le X Bs r

end CFSG.StandardType

end
