module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatLeviDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGRankOneRootMatch
public import CFSG.LocalAnalysis.StandardType.GGRankOneTags
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

private theorem three_le_rank_of_weyl {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) {r : ℕ} (σ : Fin r ≃ ι) : 3 ≤ r := by
  rcases hM with hAD | hE
  · rcases hAD with ⟨n, e, hn, -⟩ | ⟨n, e, hn, -⟩
    · have h : Fintype.card (Fin r) = Fintype.card (Fin n) :=
        Fintype.card_congr (σ.trans e.symm)
      simp only [Fintype.card_fin] at h
      omega
    · have h : Fintype.card (Fin r) = Fintype.card (Fin n) :=
        Fintype.card_congr (σ.trans e.symm)
      simp only [Fintype.card_fin] at h
      omega
  · rcases hE with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · have h : Fintype.card (Fin r) = Fintype.card (Fin 6) :=
        Fintype.card_congr (σ.trans e.symm)
      simp only [Fintype.card_fin] at h
      omega
    · have h : Fintype.card (Fin r) = Fintype.card (Fin 7) :=
        Fintype.card_congr (σ.trans e.symm)
      simp only [Fintype.card_fin] at h
      omega
    · have h : Fintype.card (Fin r) = Fintype.card (Fin 8) :=
        Fintype.card_congr (σ.trans e.symm)
      simp only [Fintype.card_fin] at h
      omega

private theorem three_le_bnRank_of_three_le_rank
    {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h : 3 ≤ (ggU t n f).D.rank) : 3 ≤ bnRank t n := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · cases n with
    | zero =>
      simp only [ggU, lieUniversal] at h
      change 3 ≤ 0 at h
      omega
    | succ m =>
      simp only [ggU, lieUniversal] at h
      change 3 ≤ m at h
      simp only [bnRank]
      omega
  · by_cases hge : 3 ≤ n
    · have hrank : (ggU .POmegaPlus n f).D.rank = n := by
        have e : ggU .POmegaPlus n f =
            ⟨↥(spinGroup (Spin.quadPlus n (GaloisField 2 f))),
              Spin.plusDatum n (GaloisField 2 f) hge⟩ := by
          simp only [ggU, lieUniversal, hge, ↓reduceDIte]
        rw [e]
        rfl
      simp only [bnRank]
      omega
    · have hrank : (ggU .POmegaPlus n f).D.rank = 0 := by
        have e : ggU .POmegaPlus n f = trivialUniversal := by
          simp only [ggU, lieUniversal, hge, ↓reduceDIte]
        rw [e]
        rfl
      rw [hrank] at h
      omega
  · simp only [bnRank]
    omega
  · simp only [bnRank]
    omega
  · simp only [bnRank]
    omega

theorem ggSecFiveCompatLeviInput_of_kgPos
    (hKG : GGSecFiveKGPosInput) (hL1 : GGSecFiveL1CoxInput) : GGSecFiveCompatLeviInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hM t n f ψ htag hψ σ hσ
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hψ
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    rcases hM with hM | hM
    · exact fun i j hij => hM.le_three i j hij
    · exact fun i j hij => hM.le_three i j hij
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs :=
    ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  obtain ⟨t', n', f', ψL, hadm', h3', hker', hrange', ht', -, hpos⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) hsplit
  have hrk' : 2 ≤ (ggU t' n' f').D.rank :=
    two_le_lieUniversal_rank t' n' 2 f' Nat.prime_two hadm' h3'
  let i₁ : Fin (ggU t' n' f').D.rank := ⟨0, by omega⟩
  unfold GGTableBPos at hpos
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  let r₀ : MulAut ↥Bs :=
    ((ε ((coxeterMatrix (ggU t' n' f').D.isFiniteType).simple i₁) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hr₀A : r₀ ∈ ggAutomizer L Bs := (ε _).2
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) (hεrefl i₁)
  have hperf : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
    hL1 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) r₀ hr₀A hr₀C
  have hlevi₁ : ggRankOneIn L Bs r₀ =
      (ggRootLevi (ggU t' n' f').D (Pi.single i₁ 1)).map ψL := by
    have h := hεlevi 1 i₁
    simp only [one_mul, inv_one, mul_one, map_one, Module.End.one_apply] at h
    exact h
  have hS₀ : ggRankOnePerf Bs r₀ =
      (CFSG.LieType.CurtisTits.rankOne (ggU t' n' f').D.rootGroup i₁).map ψL := by
    rw [hperf, hlevi₁]
    rfl
  have h3rank : 3 ≤ (ggU t n f).D.rank := three_le_rank_of_weyl hM σ
  have h3bn : 3 ≤ bnRank t n := three_le_bnRank_of_three_le_rank htag h3rank
  let k : Fin (ggU t n f).D.rank := ⟨0, by omega⟩
  let r_k : MulAut ↥Bs := ((e (M.simple (σ k)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  have hr_kC : r_k ∈ ggCoxRefl M e := by
    refine ⟨1, σ k, ?_⟩
    change ((e (M.simple (σ k)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((e (1 * M.simple (σ k) * 1⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
    simp only [one_mul, inv_one, mul_one]
  obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr_kC hr₀C
  obtain ⟨g, hgH, -, hg⟩ := mem_ggAutomizer_iff.mp (hAH haA)
  rw [← hrange] at hgH
  obtain ⟨ũ, hũ⟩ := MonoidHom.mem_range.mp hgH
  subst hũ
  have hcomp : (MulAut.conj (ψ ũ)).toMonoidHom.comp ψ =
      ψ.comp (MulAut.conj ũ).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hS : ((CFSG.LieType.CurtisTits.rankOne (ggU t n f).D.rootGroup k).map
      (ψ.comp (MulAut.conj ũ).toMonoidHom)) =
      (CFSG.LieType.CurtisTits.rankOne (ggU t' n' f').D.rootGroup i₁).map ψL := by
    rw [← hcomp, ← Subgroup.map_map, hσ k, ggRankOnePerf_map_conj (g := ψ ũ) hg r_k,
      ← hra, hS₀]
  have hM₁ : GGRankOneModel (ggU t n f).D (GaloisField 2 f) :=
    ggRankOneModel_of_tag htag hadm h3bn
  have hM₂ : GGRankOneModel (ggU t' n' f').D (GaloisField 2 f') :=
    ggRankOneModel_of_tag ht' hadm' h3'
  obtain ⟨u, hmatch⟩ :=
    CFSG.StandardType.RankOneXfer.ggRootMatch_of_rankOne_map_eq hM₁ hM₂ ψ ψL hker hker'
      k i₁ ũ hS
  unfold GGCompatPresented
  exact ⟨t', n', f', ψL, hadm', hrk', hker', hrange',
    Pi.single i₁ 1, single_mem_roots i₁, Pi.single k 1, single_mem_roots k, u, hmatch⟩


end CFSG.StandardType

end
