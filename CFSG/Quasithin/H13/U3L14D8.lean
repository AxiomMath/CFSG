module

public import CFSG.Quasithin.H13.U3L14
public import CFSG.Quasithin.H13.U3L14D5
public import CFSG.Quasithin.H13.U3L14D7
public import CFSG.Quasithin.H13.NQCoreLemma139
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318T

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem exists_isHStar_normalizer (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) {p : ℕ}
    {P : Subgroup G} {x : G} (hD : DData T V Lp p P x)
    (hM : quasithinIsMaxTwoLocal (normalizer (P : Set G))) :
    ∃ H : Subgroup G, IsHStar T (normalizer (P : Set G)) H := by
  have hLT : ¬ L ⊔ T ≤ normalizer (P : Set G) := by
    intro hle
    obtain ⟨-, ⟨-, -, -, huniq⟩, -⟩ := h1332 G T L S.h13 L S.h13.faithful
    have hPL : normalizer (P : Set G) = normalizer (L : Set G) := huniq _ hM hle
    rcases h1336 G T L V S.h13 S.irr with h | ⟨h, -⟩
    · exact h (hPL ▸ hD.G1_le)
    · exact h S.zv
  obtain ⟨H, hH, -⟩ := A5.exists_isHStar_le' ⟨le_sup_right, S.h13.faithful.1.2.2.2⟩ hLT
  exact ⟨H, hH⟩

theorem false_of_dData (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6)
    (h137 : EmptyFaithfulMultiple.Input137) (h141 : Vol2.Ch10.Tmp1_4_1_four)
    (h316 : Theorem316Statement) {P : Subgroup G} {x : G} (hD : DData T V Lp 3 P x)
    (hXS : IsXiStarF T P) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := hD.xi
  have hTP : T ≤ normalizer (P : Set G) := hP.2.1
  have hT2 : IsPGroup 2 T := S.isP_T
  have hsyl : IsSylowTwoOf T (P ⊔ T) := S.syl le_sup_right
  have h9 : (pCoreOf 2 P).relIndex P = 9 := by
    rw [hD.e9 rfl]
    norm_num
  have hexp : ∀ y ∈ P, y ^ 3 ∈ pCoreOf 2 P := hD.exp
  have hab : ⁅P, P⁆ ≤ pCoreOf 2 P :=
    commutator_le_of_relIndex_eq_sq (LieType.BorelTits.pCoreOf_le 2 P)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 P) (p := 3) (by rw [h9]; norm_num)
  have hfsu : fsuL0 T P = P :=
    le_antisymm (conjClosure_le fun t ht y hy => (mem_normalizer_iff.1 (hTP ht) y).1 hy)
      (le_conjClosure P T)
  obtain ⟨V', hV'le, hV'red, hV'ne⟩ := h141 G T P S.h13.simple S.h13.nonabelian S.h13.qtke
    S.h13.sylow (Or.inr hXS.1) hXS.2
  rw [hfsu] at hV'le hV'red hV'ne
  have hV' : IsTwoReducedIn (P ⊔ T) V' :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hV'le, hV'red⟩
  have hV'2 : IsPGroup 2 V' := fun v =>
    ⟨1, Subtype.ext (by simpa using hV'.2.2.1.2 v v.2)⟩
  have hV'T : V' ≤ T :=
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV'.1 hV'.2.1 hV'2).trans
      (pCoreOf_two_le_of_isSylowTwoOf hsyl)
  have h3 : ∀ y ∈ P, y ^ 3 ∈ centralizer (V' : Set G) := fun y hy =>
    ((pCoreOf_le_pCoreOf_sup_of_le hTP).trans (pCoreOf_le_centralizer_of_reduced hV')) (hexp y hy)
  have hWred : IsTwoReducedIn (P ⊔ T) (wOf T P V') := isTwoReducedIn_wOf hT2 hTP hV' h3
  have hWP : wOf T P V' ⊓ centralizer (P : Set G) = ⊥ :=
    wOf_inf_centralizer hTP hV'.2.1 hV'.2.2.1 h3
  have hW1 : wOf T P V' ≠ ⊥ := wOf_ne_bot hT2 hTP hV'.2.1 hV'T hV'ne
  have hgen : wOf T P V' ≤
      conjClosure (wOf T P V' ⊓ centralizer (T : Set G)) (P ⊔ T) :=
    conjClosure_le fun h hh z hz => subset_closure
      ⟨h, hh, z, mem_inf.2 ⟨le_wOf T P V' hz, (mem_inf.1 (mem_inf.1 hz).2).2⟩, rfl⟩
  have hPW : ¬ P ≤ centralizer (wOf T P V' : Set G) := by
    intro h
    apply hW1
    rw [eq_bot_iff, ← hWP]
    exact le_inf le_rfl (le_centralizer_iff.1 h)
  have hN : P ⊔ T ≤ normalizer (wOf T P V' : Set G) := hWred.2.1
  have hC : P ⊓ centralizer (wOf T P V' : Set G) ≤ pCoreOf 2 P :=
    inf_centralizer_le_of_isXi hP hab (le_sup_right.trans hN) (le_sup_left.trans hN) hPW
  have huniq : IsUniqueM (P ⊔ T) (normalizer (P : Set G)) :=
    h137 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow P hXS.1
  have h318 : Hyp318 T (normalizer (P : Set G)) P (wOf T P V') :=
    ⟨⟨huniq.1.1, le_sup_right.trans huniq.1.2⟩,
      S.exists_isHStar_normalizer h1332 h1336 hD huniq.1.1, hP.1, le_normalizer, le_rfl, huniq,
      hWred, pCoreOf_sup_eq_inf_centralizer hsyl hTP hWred hC⟩
  have hq := theorem318_one_of_316 h316 S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow
    h318
  have hO2 : pCoreOf 2 (P ⊔ T) ≠ ⊥ := hP.2.2.1
  obtain ⟨b₁, hb₁, b₂, hb₂, h₁, h₂, h₁₂, hc⟩ := hD.q8 rfl
  have hO2Lp : pCoreOf 2 Lp ≤ T := S.pCoreOf_Lp_le_R1.trans S.R1_le_T
  exact false_of_q8 hP h9 hexp hsyl hWred hWP hW1 hgen hq
    (stronglyQuasithin_of_pCoreOf_ne_bot S.h13.qtke hO2)
    (kGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hO2)
    (hO2Lp hb₁) (hO2Lp hb₂) h₁ h₂ h₁₂ hc

theorem stepD_holds
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) (h1332 : Stmt13_3_2)
    (h1336 : A6.Stmt13_3_6) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (h36c : Vol2Native.A36CoreForSQTKCat) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h3213 : EmptyFaithfulMultiple.Input3213)
    (h137 : EmptyFaithfulMultiple.Input137) (h141 : Vol2.Ch10.Tmp1_4_1_four)
    (h316 : Theorem316Statement) : StepD T V Lp := by
  intro p hp hp2
  by_contra hfail
  obtain ⟨P, x, hD⟩ := S.exists_dData hp hp2 hfail
  have hXS := S.isXiStarF_P hQ h1332 h1336 h37 h38 h39 NQCore.lemma139Two h134 h36c h37c h38c
    hD
  have hp3 := S.p_eq_three h3213 hD hXS
  subst hp3
  exact S.false_of_dData h1332 h1336 h137 h141 h316 hD hXS

end Set14

theorem stmt13_3_14d_of
    (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (h36c : Vol2Native.A36CoreForSQTKCat) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h3213 : EmptyFaithfulMultiple.Input3213)
    (h137 : EmptyFaithfulMultiple.Input137) (h141 : Vol2.Ch10.Tmp1_4_1_four)
    (h316 : Theorem316Statement) : Stmt13_3_14d := by
  intro G _ _ T L V V₂ V₃ Lp S hQ
  exact S.stepD_holds hQ h1332 h1336 h37 h38 h39 h134 h36c h37c h38c h3213 h137 h141 h316

end CFSG.Quasithin.H13.U3
