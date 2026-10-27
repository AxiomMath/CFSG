module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzFour
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzE
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzSz
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzCard

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P31
open scoped IsMulCommutative

@[expose] def NoSzEqF_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T = K →
        ∀ n : ℕ, 2 ≤ n → ¬ IsSz n (starMod_w31 H K)

@[expose] def NoSzLtF_w31 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T ≠ K →
        ∀ n : ℕ, 2 ≤ n → ¬ IsSz n (starMod_w31 H K)

theorem noSzF_w31_of (hEq : NoSzEqF_w31) (hLt : NoSzLtF_w31) : NoSzF_w31 := by
  intro h1229 G _ _ T L V _ F hH hZ H K hIs h918 n hn
  by_cases hK : conjClosure K T = K
  · exact hEq h1229 G T L V F hH hZ H K hIs h918 hK n hn
  · exact hLt h1229 G T L V F hH hZ H K hIs h918 hK n hn

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31
open CFSG.QuasithinUnique
open scoped IsMulCommutative

section Eq

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_isSz_eq_w31
    (h310 : D310) (h391 : D391) (hI4 : Insp4) (h1222 : Stmt12_2_2)
    {F : Frame126 T L V} (hH : Hyp126 G T L V) {H K : Subgroup G} (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hKK : conjClosure K T = K) {n : ℕ}
    (hSz : IsSz n (starMod_w31 H K)) : False := by
  have h91 := h918.toHypF98.toHypF91
  have hHq : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian (pCoreOf_ne_bot h91)
  have hKc : K ∈ cComp H := h918.K_cComp
  obtain ⟨E, -, hEodd, -, hES, hEC, hfpf⟩ := exists_odd_normal_fpf h1222 hH hIs h918 hKK hSz
  have hE3 : ∀ e ∈ E, ∃ k : ℕ, e ^ 3 ^ k = 1 :=
    isThreeGroup_of_odd_le_star h1222 F hH h918.T_le_H (le_sup_left.trans h918.L₁T_le_H)
      hH.hyp.sylow.1 hES hEodd
  have hq : CFSG.IsQuasisimple ↥(star H K) :=
    CFSG.Quasithin.H13.P31Sec.isQuasisimple_star hKc h918.K_quasisimple
  haveI hNn : (star H K).Normal := normal_star (by simpa [hKK] using h918.K₀_normal)
  haveI : Group.IsPerfect ↥(star H K) := hq.1
  have hSzN : IsSz n ↥(star H K) :=
    suzukiModel_of_normal (fun M hM hMp => eq_bot_of_isPGroup hM hMp) (star H K) hSz
  have hs : IsSimpleGroup ↥(star H K) := isSimpleGroup_of_psl2_or_sz (Or.inr hSzN)
  exact false_of_isSz_eq h310 h391 hI4 h918 hHq hKK hSzN hs E hE3 hEC hfpf

theorem noSzEqF_w31_of
    (h310 : D310) (h391 : D391) (hI4 : Insp4) (h1222 : Stmt12_2_2) : NoSzEqF_w31 := by
  intro _ G _ _ T L V _ F hH _ H K hIs h918 hKK n _ hSz
  exact false_of_isSz_eq_w31 h310 h391 hI4 h1222 hH hIs h918 hKK hSz

end Eq

end CFSG.Quasithin.H13.P31Sz
