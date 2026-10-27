module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCentJLieKnown

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.centralizer_le_ggM_of_data' (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    {R J₀ : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hJ₀J : J₀ ≤ J)
    (hgen : ggQR p B x L D J R ⊔ J₀ = ggG0 p B x L D J)
    (h67i : ggSR p B x L D J R ≤ (ggSR p B x L D J R ⊓ ggQR p B x L D J R) ⊔
      (ggSR p B x L D J R ⊓ Subgroup.centralizer (J : Set G)))
    (hSQC : ggSR p B x L D J R ≤ ggM p B x L D J →
      ⁅ggSR p B x L D J R, ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G)⁆ ≤
        ggQR p B x L D J R →
      ggSR p B x L D J R ≤
        ggQR p B x L D J R ⊔ Subgroup.centralizer (ggG0 p B x L D J : Set G))
    (hcase : ggCenterOf (ggQR p B x L D J R) ≤ ggPR R → ggPR R ≤ ggQR p B x L D J R →
      ggPR R ≠ ggQR p B x L D J R →
      ¬ ggQR p B x L D J R ≤ Subgroup.centralizer (ggPR R : Set G) →
        (⁅ggQR p B x L D J R, ggQR p B x L D J R⁆ ≤ R ∧
          ggQR p B x L D J R ≤ Subgroup.centralizer (R : Set G)) ∨
        ∀ g ∈ Subgroup.centralizer (J : Set G), ∃ h ∈ ggG0 p B x L D J,
          g * h⁻¹ ∈ Subgroup.centralizer ((J ⊔ ggPR R : Subgroup G) : Set G)) :
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J := by
  set G₀ := ggG0 p B x L D J with hG₀
  set N := Subgroup.normalizer (R : Set G) with hN
  set P := ggPR R with hP
  set N₀ := G₀ ⊓ N with hN₀
  set Q := ggQR p B x L D J R with hQ
  set S := ggSR p B x L D J R with hS
  have hQN₀ : Q ≤ N₀ := Subgroup.map_subtype_le _
  have hQG₀ : Q ≤ G₀ := hQN₀.trans inf_le_left
  have hQN : Q ≤ N := hQN₀.trans inf_le_right
  have hPN : P ≤ N := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := ggPCoreOf_two_isPGroup N
  have hQ2 : IsPGroup 2 Q := ggPCoreOf_two_isPGroup N₀
  have hNP : N ≤ Subgroup.normalizer (P : Set G) := fun g hg => mem_normalizer_pCoreOf hg
  have hchar : N ⊓ Subgroup.centralizer (P : Set G) ≤ P := hctx.charTwo N ⟨R, hR1, hR2, rfl⟩
  have hCJN : Subgroup.centralizer (J : Set G) ≤ N :=
    (Subgroup.centralizer_le hRJ).trans (Subgroup.centralizer_le_normalizer _)
  have hCJ₀ : Subgroup.centralizer (J : Set G) ≤ Subgroup.normalizer (J₀ : Set G) :=
    (Subgroup.centralizer_le hJ₀J).trans (Subgroup.centralizer_le_normalizer _)
  have hSM : S ≤ ggM p B x L D J := by
    refine h67i.trans (sup_le ?_ ?_)
    · exact (inf_le_right.trans hQG₀).trans Subgroup.le_normalizer
    · intro s hs
      show s ∈ Subgroup.normalizer ((G₀ : Subgroup G) : Set G)
      rw [← hgen]
      exact ggMem_normalizer_sup ((inf_le_left : S ⊓ _ ≤ S).trans inf_le_right hs) (hCJ₀ hs.2)
  have hPN₀ : P ⊓ N₀ ≤ Q := ggPR_inf_le_ggQR p B x L D J R
  have hSN₀ : ⁅S, N₀⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr fun s hs m hm => ?_
    have hsP : s ∈ P := hs.1
    have hsM : s ∈ ggM p B x L D J := hSM hs
    refine hPN₀ ⟨ggCommutatorElement_mem_left hsP (hNP hm.2), ?_, ?_⟩
    · exact ggCommutatorElement_mem_right hm.1 hsM
    · exact N.mul_mem (N.mul_mem (N.mul_mem (hPN hsP) hm.2) (N.inv_mem (hPN hsP)))
        (N.inv_mem hm.2)
  have hSQ : S ≤ Q := by
    refine ggLe_of_le_sup_of_odd (hP2.to_le inf_le_left) hQ2 inf_le_right ?_ hodd (hSQC hSM hSN₀)
    exact hQG₀.trans fun g hg => mem_normalizer_centralizer (Subgroup.le_normalizer hg)
  have hPQ : P ≤ Q := ggLe_of_inf_normalizer_le hP2 hQ2 (hQN.trans hNP) hSQ
  have hCJP : Subgroup.centralizer (J : Set G) ≤ Subgroup.normalizer (P : Set G) := hCJN.trans hNP
  by_cases hPQe : P = Q
  · intro g hg
    show g ∈ Subgroup.normalizer ((G₀ : Subgroup G) : Set G)
    rw [← hgen]
    exact ggMem_normalizer_sup (hPQe ▸ hCJP hg) (hCJ₀ hg)
  · by_cases hQcent : Q ≤ Subgroup.centralizer (P : Set G)
    · exact absurd (le_antisymm hPQ (le_inf hQN hQcent |>.trans hchar)) hPQe
    · have hZ : ggCenterOf Q ≤ P := by
        refine le_trans (le_inf ((Subgroup.map_subtype_le _).trans hQN) ?_) hchar
        rw [Subgroup.le_centralizer_iff]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨z, hz, rfl⟩
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, hPQ ha⟩)).symm
      rcases hcase hZ hPQ hPQe hQcent with ⟨hQQ, hQR⟩ | hJP
      · exfalso
        apply hPQe
        refine le_antisymm hPQ (le_pCoreOf_of_stability le_rfl hR2 hchar hQN (fun q hq a ha => ?_)
          hQR)
        have := hQQ (Subgroup.commutator_mem_commutator hq (hPQ ha))
        rwa [commutatorElement_def] at this
      · intro g hg
        obtain ⟨h, hh, hgh⟩ := hJP g hg
        have hghP : g * h⁻¹ ∈ P :=
          hchar ⟨hCJN (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hgh),
            Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hgh⟩
        have hgG₀ : g ∈ G₀ := by
          have := G₀.mul_mem (hQG₀ (hPQ hghP)) hh
          rwa [inv_mul_cancel_right] at this
        exact Subgroup.le_normalizer hgG₀

theorem ggSixHcase_of_itemFour' {R : Subgroup G} (hRJ : R ≤ J)
    (h4 : ∀ V : Subgroup G, ggCenterOf (ggQR p B x L D J R) ≤ V → V ≤ ggQR p B x L D J R →
      V ≠ ggQR p B x L D J R → ¬ ggQR p B x L D J R ≤ Subgroup.centralizer (V : Set G) →
      ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (V : Set G) →
      ∀ g ∈ Subgroup.centralizer (J : Set G), g ∈ Subgroup.normalizer (V : Set G) →
        ∃ h ∈ ggG0 p B x L D J, g * h⁻¹ ∈ Subgroup.centralizer ((J ⊔ V : Subgroup G) : Set G)) :
    ggCenterOf (ggQR p B x L D J R) ≤ ggPR R → ggPR R ≤ ggQR p B x L D J R →
      ggPR R ≠ ggQR p B x L D J R →
      ¬ ggQR p B x L D J R ≤ Subgroup.centralizer (ggPR R : Set G) →
        (⁅ggQR p B x L D J R, ggQR p B x L D J R⁆ ≤ R ∧
          ggQR p B x L D J R ≤ Subgroup.centralizer (R : Set G)) ∨
        ∀ g ∈ Subgroup.centralizer (J : Set G), ∃ h ∈ ggG0 p B x L D J,
          g * h⁻¹ ∈ Subgroup.centralizer ((J ⊔ ggPR R : Subgroup G) : Set G) := by
  intro hZ hPQ hne hQc
  have hNP : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (ggPR R : Set G) :=
    fun g hg => mem_normalizer_pCoreOf hg
  have hCJN : Subgroup.centralizer (J : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.centralizer_le hRJ).trans (Subgroup.centralizer_le_normalizer _)
  exact Or.inr fun g hg => h4 (ggPR R) hZ hPQ hne hQc (inf_le_right.trans hNP) g hg (hNP (hCJN hg))

end Ctx

section Inputs

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}

theorem GGSixCtxV2.centralizer_le_ggM_of_knownStarAt {ψ : (ggU t n f).K →* G}
    (hK : GGSixLieKnownStarFour) (ht : t = .PSL)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    (hZJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hZ : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    (hF : GGSixLSevenFieldExtCase J t f) (hcop : Nat.Coprime n (2 ^ f - 1)) :
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J := by
  subst ht
  obtain ⟨-, -, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf0, hmodel⟩, ⟨hBsN, hVI⟩, -, -⟩ := hctx.2
  have hBBs : B ≤ Bs := hctx.bstar.1
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hctx.sstar.2.2.2.1
  have hLc : IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL
      (le_inf le_sup_left hL.1) inf_le_right
  have hmkL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hctx.stdType.1
  obtain ⟨R, J₀, hRJ, hR1, hR2, hJ₀J, hgen, hper, h3, h4⟩ :=
    hK G n f ψ p (ggG0 p B x L D J) B D J L x hrange hker hmodel hodd hctx.prime hctx.ne_two
      (hBBs.trans hBsN) (fun b hb => hVI b (hBBs hb)) hctx.sstar.1.1 hctx.pow_four_le_card_b
      hctx.stdSub.1.1 hctx.card_d hBJ hctx.stdSub.1.2.2.2.2.2.2.symm hctx.j_isComponentOf_inf
      hZJ hctx.x_mem_d hctx.sstar.2.2.1 le_sup_left hLc (hctx.j_le_inf.trans inf_le_left)
      hctx.not_le_centralizer_L hmkL hF hcop
  have h67i := hctx.ggSR_le_of_items hZJ hZ hcomp hRJ hR1 hR2 hper
  exact hctx.centralizer_le_ggM_of_data' hodd hRJ hR1 hR2 hJ₀J hgen h67i
    (fun hSM hSQ => hctx.sQC_of_inner hRJ hodd
      (h3 _ (ggSR_isPGroup R) hSM (ggSR_le_normalizer R) hSQ))
    (ggSixHcase_of_itemFour' hRJ h4)

theorem ggSixLSixSevenCentJLieInput_of_known (hK : GGSixLieKnownTags)
    (hK4 : GGSixLieKnownStarFour) (hTC : GGSixFieldExtTableCInput) (hA6 : GGSixJNotA6Input)
    (h64 : GGSixCentreOddInput) (hnc : GGLNoncyclicInput) : GGSixLSixSevenCentJLieInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC2 hodd hcomp hZ hA hE
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    hctx.bstar.1.trans (hctx.bstar_le_normalizer_j hnc)
  have hZJ : Odd (Nat.card (Subgroup.center ↥J)) :=
    (h64 G p B Bs x L D J t n f ψ hctx hodd).1
  have hTCf := hTC G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp hZ hA hE
  by_cases hFe : GGSixLSevenFieldExtCase J t f
  · obtain ⟨ht, hcop⟩ := hTCf hFe
    exact hctx.centralizer_le_ggM_of_knownStarAt hK4 ht hBJ hodd hZJ hZ hcomp hFe hcop
  · exact hctx.centralizer_le_ggM_of_knownAt (hK t) hBJ hodd hZJ hZ hcomp hA hE
      (hA6 G p B Bs x L D J t n f ψ hctx) hFe

end Inputs

end CFSG.StandardType
