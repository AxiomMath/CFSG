module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Comp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankBlk
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Mat
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open scoped Matrix commutatorElement

namespace Sec1211Ns

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}

theorem lv_le_Xv (S : Setting T L V V₁ V₂ n a₀ c₀) :
    Sec1216Lv.lv L (a₀ * c₀) ≤ Xv L V₁ (a₀ * c₀) := fun _ hl =>
  ⟨⟨Subgroup.le_normalizer (Sec1216Lv.lv_le_L L _ hl), S.hyp.norm₁ (Sec1216Lv.lv_le_L L _ hl)⟩,
    Sec1216Lv.lv_le_centralizer L _ hl⟩

variable {S : Setting T L V V₁ V₂ n a₀ c₀} {m : ℕ} (F : Frame S m)

theorem frameMat_psi_lv (l : ↥(Sec1216Lv.lv L (a₀ * c₀))) :
    frameMat F (psi F S.lv_le_Xv l) = S.C₁.ρ ⟨l, Sec1216Lv.lv_le_L L _ l.2⟩ := by
  refine PairStab.eq_of_mulVec_eq fun ξ => ?_
  have h1 := psi_spec₁ F S.lv_le_Xv l (S.C₁.inv_mem ξ)
  have h2 := S.C₁.conj ⟨l, Sec1216Lv.lv_le_L L _ l.2⟩ _ (S.C₁.inv_mem ξ)
  rw [S.C₁.E_inv] at h1 h2
  rw [← h1]
  exact h2

theorem psi_lv_surjective : Function.Surjective (psi F S.lv_le_Xv) := by
  intro D
  have hD : frameMat F D ∈ PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀) := by
    rw [PairStab.eq_map_levE F.h F.hs₁ F.hs₂]
    exact ⟨PairStab.levE F.h D, ⟨D, rfl⟩, rfl⟩
  obtain ⟨l, hl, hlD⟩ := S.exists_mem_lv hD
  refine ⟨⟨l, hl⟩, frameMat_injective F ?_⟩
  rw [frameMat_psi_lv]
  exact hlD

theorem isPGroup_ker_psi_lv : IsPGroup 2 (psi F S.lv_le_Xv).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := S.hyp.iso
  have hkerρ : S.C₁.ρ.ker = CFSG.pCore 2 ↥L := S.C₁.ker_eq S.hn ι
  rintro ⟨l, hl⟩
  have h1 : S.C₁.ρ ⟨l, Sec1216Lv.lv_le_L L _ l.2⟩ = 1 := by
    rw [← frameMat_psi_lv F, MonoidHom.mem_ker.mp hl]
    simp [frameMat]
  have hmem : (⟨l, Sec1216Lv.lv_le_L L _ l.2⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
    hkerρ ▸ (MonoidHom.mem_ker.mpr h1)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h2 := congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hk
  simpa using h2

theorem lv_mem_lFamily (F : Frame S m) (hm : 3 ≤ m) {R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G)) :
    Sec1216Lv.lv L (a₀ * c₀) ∈ lFamily R := by
  show Sec1216Lv.lv L (a₀ * c₀) ∈ cComp (Sec1216Lv.lv L (a₀ * c₀) ⊔ R)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
    Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) hm
  refine Sec1216Lv.mem_cComp_of_hom (Sec1216Lv.lv_perfect L _) ?_ hR (psi F S.lv_le_Xv)
    (psi_lv_surjective F) (isPGroup_ker_psi_lv F)
  intro h
  obtain ⟨y, hy, hy0, -⟩ := VecStab.exists_perp_ne S.three_le' S.y₀_ne 0
  have hy' : y ⬝ᵥ S.C₂.E c₀ = 0 := by rw [dotProduct_comm]; exact hy
  have hw := S.W₁_le_lv (S.inv_mem_W₁ hy')
  rw [h, Subgroup.mem_bot] at hw
  exact hy0 (by rw [← S.C₁.E_inv y, hw, S.C₁.E_one])

omit [Finite G] in
theorem commutator_pCoreOf_eq_bot [Finite G] {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K) :
    ⁅pCoreOf 2 K, K⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hx' : x ∈ CFSG.pCore 2 ↥K := by exact hx
  have h1 := Subgroup.mem_center_iff.mp (Lin2.OddRank.pCore_le_center hq hx') ⟨k, hk⟩
  exact congrArg Subtype.val h1

theorem lv_le_of_isComponentIn (F : Frame S m) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hm : 3 ≤ m) {R : Subgroup G}
    (hR : IsSylowTwoOf R (Subgroup.centralizer ({a₀ * c₀} : Set G)))
    (hRM : R ≤ Subgroup.normalizer (L : Set G)) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({a₀ * c₀} : Set G))) :
    Sec1216Lv.lv L (a₀ * c₀) ≤ K := by
  have : IsSimpleGroup G := S.hyp.simple
  have hqtke : QTKECore G := qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke
  have hRN : R ≤ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) :=
    Sec1216Lv.le_normalizer_lv hRM hR.1
  obtain ⟨K', hK', hlvK'⟩ := Vol2Native.lemma_1_2_4_exists hqtke.1 h37 h39 S.pCoreOf_ne_bot hR
    (Sec1216Lv.lv_le_centralizer L _) (lv_mem_lFamily F hm hRN)
  have hKc : K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)) :=
    Sec1216Lv.cComp_of_isComponentIn hK
  by_cases hKK : K = K'
  · rw [hKK]
    exact hlvK'
  exfalso
  have h1 := (Vol2Native.lemma_1_2_1_two hqtke.1 h37 S.pCoreOf_ne_bot hKc hK' hKK).1
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hc : ⁅K, Sec1216Lv.lv L (a₀ * c₀)⁆ ≤ pCoreOf 2 K :=
    (Subgroup.commutator_mono le_rfl hlvK').trans (h1.trans inf_le_left)
  have hZ := commutator_pCoreOf_eq_bot hq
  have h3 : ⁅⁅K, Sec1216Lv.lv L (a₀ * c₀)⁆, K⁆ = ⊥ :=
    le_bot_iff.mp (hZ ▸ Subgroup.commutator_mono hc le_rfl)
  have h4 : ⁅⁅Sec1216Lv.lv L (a₀ * c₀), K⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Sec1216Lv.lv L (a₀ * c₀)) K]
    exact h3
  have h5 := Subgroup.commutator_commutator_eq_bot_of_rotate h3 h4
  rw [perfect_of_mem_cComp hKc] at h5
  obtain ⟨u, huW, huV, hu1, huU, hus⟩ := S.exists_singular
  have hulv : u ∈ Sec1216Lv.lv L (a₀ * c₀) := sup_le S.W₁_le_lv S.W₂_le_lv huW
  apply S.not_le_centralizer huV hu1 huU hus hK
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h6 : ⁅k, u⁆ = 1 := by
    have := Subgroup.commutator_mem_commutator hk hulv
    rwa [h5, Subgroup.mem_bot] at this
  rw [commutatorElement_eq_one_iff_mul_comm] at h6
  exact h6

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
