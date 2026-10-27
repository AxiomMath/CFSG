module

public import CFSG.Quasithin.EmptyFaithful.SzN15Br1
public import CFSG.Quasithin.EmptyFaithful.SzN15Br2
public import CFSG.Quasithin.EmptyFaithful.SzN2Main
public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.Background.B69Red

public section

namespace CFSG.Quasithin.SzN15

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

@[expose] def NoGraphAutOnFFModule3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R A S₀ : Subgroup G), (IsSL3Quot L ∨ IsSp4Quot L) →
    SQTKGroup ↥L → IsSylowTwoOf S₀ L → IsPGroup 2 ↥R → R ≤ Subgroup.normalizer (L : Set G) →
    A ≤ Subgroup.normalizer (L : Set G) → A ≤ Subgroup.normalizer (R : Set G) →
    A ≤ Subgroup.normalizer (S₀ : Set G) →
    C27OneTwo L R (omegaOneCenterOf (pCoreOf 2 (L ⊔ R))) →
      ∀ P : Subgroup G, IsMaxParabolic2 L P → L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P →
        A ≤ Subgroup.normalizer (P : Set G)

private theorem isQuasisimple_quot_of_lie {G : Type} [Group G] {L : Subgroup G}
    (hlie : IsSL3Quot L ∨ IsSp4Quot L) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  rcases hlie with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · have : Finite F := inferInstance
    exact isQuasisimple_of_equiv_sl3 e
  · have : Finite F := inferInstance
    exact isQuasisimple_of_equiv_sp4 (by rw [Nat.card_eq_fintype_card]; exact hF) e

theorem exists_normalized_parabolic (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (hcover : AsA36NoOddCover) {G : Type} [Group G] [Finite G] {L R A S₀ W : Subgroup G}
    [IsMulCommutative ↥W] (hlie : IsSL3Quot L ∨ IsSp4Quot L) (hSQ : SQTKGroup ↥L)
    (hS₀ : IsSylowTwoOf S₀ L) (hR2 : IsPGroup 2 ↥R) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hAS : A ≤ Subgroup.normalizer (S₀ : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (h1a : pCoreOf 2 (L ⊔ R) ≤ (L ⊔ R) ⊓ Subgroup.centralizer (W : Set G))
    (hred : IsTwoReducedIn (L ⊔ R) W) {A' : Subgroup (MulAut ↥W)} (hA'R : A' ≤ autOn R W)
    (hA' : IsFFStarOffender (autOn (L ⊔ R) W) A') :
    ∃ P : Subgroup G, IsMaxParabolic2 L P ∧ L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P ∧
      A ≤ Subgroup.normalizer (P : Set G) := by
  have hYL : L ⊔ R ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRL
  have hLY : L ≤ L ⊔ R := le_sup_left
  have hYW : L ⊔ R ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hLY.trans hYW
  have hVe : IsElemAbelian 2 W := hred.2.2.1
  have hO2 : pCoreOf 2 (autOn (L ⊔ R) W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hD := autOn_inf_centralizer_eq_bot hR2 hRL hYW hO2
  have hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) := by
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ R) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLY)
        (hYL.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
    exact (h1.trans h1a).trans inf_le_right
  have hcomm_le : ∀ B : Subgroup (MulAut ↥W), B ≤ autOn R W → ⁅autOn L W, B⁆ = ⊥ → B = ⊥ := by
    intro B hB hc
    rw [eq_bot_iff, ← hD]
    refine le_inf hB (fun a ha => Subgroup.mem_centralizer_iff.2 fun k hk => ?_)
    have h1 : autOn L W ≤ Subgroup.centralizer (B : Set (MulAut ↥W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    exact (Subgroup.mem_centralizer_iff.1 (h1 hk) a ha).symm
  have hnt : ¬ L ≤ Subgroup.centralizer (W : Set G) := by
    intro hc
    have h0 : autOn L W = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hx
      exact Subgroup.mem_bot.2 (InternalSec.conjAct_eq_one_of_mem_centralizer g (hc hg))
    exact hA'.2.1 (hcomm_le A' hA'R (by rw [h0, Subgroup.commutator_bot_left]))
  have hq := isQuasisimple_quot_of_lie hlie
  have hqa : CFSG.IsQuasisimple ↥(autOn L W) := S153D.isQuasisimple_autOn hLW hq hker hnt
  have hsq : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L) := S153D.sqtkGroup_quot_pCore hSQ
  have hSQa : SQTKGroup ↥(autOn L W) := by
    refine B69.sqtk_of_surj hA21 hSQ (Hs := ⊤)
      ((S153D.autOnHom hLW).comp (⊤ : Subgroup ↥L).subtype) ?_ hqa
    intro y
    obtain ⟨l, rfl⟩ := S153D.autOnHom_surjective hLW y
    exact ⟨⟨l, trivial⟩, rfl⟩
  have hnormA' : A' ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) :=
    hA'R.trans (autOn_le_normalizer hRL)
  have hLA : ⁅autOn L W, A'⁆ = autOn L W := by
    rcases commutator_eq_or_eq_bot1527d hqa hnormA' with h | h
    · exact h
    · exact absurd (hcomm_le A' hA'R h) hA'.2.1
  have h2 : ∀ y ∈ L ⊔ R, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (W : Set G) := fun y hy => by
    obtain ⟨e, he⟩ := InternalSec.two_of_sup hR2 hRL y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩
  have hB := InternalSec.b51Hyp_ffJ_autOn hYW hLY hYL h2 hO2 hqa hSQa hA' hLA
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hVe.2 v v.2)
  have hconcl := hB51 ↥W hV2 _ _ hB.1
  have hN := xOrd_autOn hLW hker hnt hq hlie
  have hL45 := not_surjective_autOn hcover hLW hker hnt hq hsq hlie
  have hNat := natOutcome_of_part1 hconcl.1 hN hL45
  have hSyl : IsSylowTwoOf (autOn S₀ W) (autOn L W) := Setup.isSylowTwoOf_autOn hS₀ hLW
  have hgood := goodCoatom_of_natOutcome hNat hSyl
  exact exists_good_parabolic hLW hS₀ hAL hAW hAS hgood

theorem noGraphAutOnFFModule3_of_b51 (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (hcover : AsA36NoOddCover) : NoGraphAutOnFFModule3 := by
  intro G _ _ L R A S₀ hlie hSQ hS₀ hR2 hRL hAL hAR hAS hC P hP hBP
  obtain ⟨⟨h1a, -, hred⟩, -, hV0, -, A', hA'R, hA'⟩ := hC
  have : IsMulCommutative ↥(omegaOneCenterOf (pCoreOf 2 (L ⊔ R))) := hred.2.2.1.1
  have hAW : A ≤ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 (L ⊔ R)) : Subgroup G) : Set G) := by
    intro g hg
    exact normalizer_le_normalizer_omegaOneCenterOf'
      (normalizer_le_normalizer_pCoreOf 2 (L ⊔ R) (mem_normalizer_sup (hAL hg) (hAR hg)))
  obtain ⟨P₀, hP₀, hBP₀, hAP₀⟩ := exists_normalized_parabolic hB51 hA21 hcover hlie hSQ hS₀ hR2 hRL
    hAL hAS hAW h1a hred hA'R hA'
  obtain ⟨P₁, P₂, hP₁, hP₂, hne, hB₁, hB₂, huniq⟩ := rankTwoMaxParabolics_holds G L S₀ hlie hS₀
  have hyB : ∀ g ∈ A, B6.conjSub g (L ⊓ Subgroup.normalizer (S₀ : Set G)) =
      L ⊓ Subgroup.normalizer (S₀ : Set G) := by
    intro g hg
    rw [OrderIso.map_inf, B6.conjSub_eq_self (hAL hg),
      B6.conjSub_eq_self (Subgroup.le_normalizer (hAS hg))]
  have hmem : ∀ g ∈ A, ∀ Q : Subgroup G, IsMaxParabolic2 L Q →
      L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ Q → B6.conjSub g Q = P₁ ∨ B6.conjSub g Q = P₂ := by
    intro g hg Q hQ hBQ
    refine huniq _ (S153D.isMaxParabolic2_conjSub (hAL hg) hQ) ?_
    have := (B6.conjSub g).monotone hBQ
    rwa [hyB g hg] at this
  have hfix : ∀ g ∈ A, B6.conjSub g P₁ = P₁ ∧ B6.conjSub g P₂ = P₂ := by
    intro g hg
    have h0 : B6.conjSub g P₀ = P₀ := B6.conjSub_eq_self (hAP₀ hg)
    have h1 := hmem g hg P₁ hP₁ hB₁
    have h2 := hmem g hg P₂ hP₂ hB₂
    rcases huniq P₀ hP₀ hBP₀ with he | he
    · rw [he] at h0
      refine ⟨h0, ?_⟩
      rcases h2 with h | h
      · exact absurd ((B6.conjSub g).injective (h.trans h0.symm)) hne.symm
      · exact h
    · rw [he] at h0
      refine ⟨?_, h0⟩
      rcases h1 with h | h
      · exact h
      · exact absurd ((B6.conjSub g).injective (h.trans h0.symm)) hne
  rcases huniq P hP hBP with he | he
  · intro g hg
    rw [he]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix g hg).1
  · intro g hg
    rw [he]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (hfix g hg).2

end CFSG.Quasithin.SzN15
