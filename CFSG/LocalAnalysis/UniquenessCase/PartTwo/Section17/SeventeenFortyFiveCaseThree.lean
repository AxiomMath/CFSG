module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveBot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveMBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_45_InFSq (A B T : Subgroup G) : Prop :=
  CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (A ⊔ B ⊔ T)

@[expose] def Gap17_45_UniqueMaxFive (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
    (A₀ A B : Subgroup G),
    V₀ ≠ ⊥ → Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X →
    F08.Case8100FourR D ![L, conjSubgroup L x] p X →
    CFSG.ABGLocalTools.IsSylowOf r A X → Permutes A D.T → B ≤ D.M →
    Nat.card B = p → ⁅A, B⁆ = A → Permutes B D.T →
    centralizer (D.Z : Set G) ≤ D.M → UniqueMax D.M (A ⊔ B ⊔ D.T)

theorem centralizer_Z_le_of_centralizersUnique (D : Data G)
    (hcu : CentralizersUnique D.M D.T) : centralizer (D.Z : Set G) ≤ D.M := by
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (uc22main1_Z_ne_bot D)
  refine (Subgroup.centralizer_le ?_).trans
    ((hcu z (uc22main1_Z_le_T D hzZ) ?_ (fun h => hz1 (Subtype.ext h))).1)
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    exact hw ▸ hzZ
  · intro t ht
    exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hzZ).2.1 t ht).symm

theorem s17_45_uniqueMax_ABT (D : Data G) (h147 : Inputs1719.UC2_14_7Three D)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (hg5 : Gap17_45_UniqueMaxFive D V₀ V)
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hV₀ : V₀ ≠ ⊥)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T) (hBM : B ≤ D.M)
    (hBcard : Nat.card B = p) (hAB : ⁅A, B⁆ = A) (hBT : Permutes B D.T) :
    UniqueMax D.M (A ⊔ B ⊔ D.T) := by
  rcases hc with hc3 | hc4
  · have h := (h147 ![L, conjSubgroup L x] ![n, n] r p A₀ X B A h8100 hc3 hAsyl hAT hBM hBcard
      hAB hBT).1
    rwa [show B ⊔ A ⊔ D.T = A ⊔ B ⊔ D.T by rw [sup_comm B A]] at h
  · rcases ctx.hyp125.1 with ⟨-, hbot⟩ | ⟨-, hcu, -⟩
    · exact absurd hbot hV₀
    · exact hg5 L X p n l r C Dc Gamma x A₀ A B hV₀ ctx h8100 hc4 hAsyl hAT hBM hBcard hAB hBT
        (centralizer_Z_le_of_centralizersUnique D hcu)

theorem s17_45_wZeroA_of_ANormT {D : Data G} {V₀ A B : Subgroup G}
    (hANT : A ≤ B ⊔ normalizer (D.T : Set G))
    (hBT : B ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G)) :
    A ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
  hANT.trans (sup_le (le_sup_left.trans hBT)
    (E3.normalizer_le_normalizer_wClos (V := V₀) (i := 0) D.T))

section Certified


theorem s17_45_ne_bot_branch (D : Data G) (h147 : Inputs1719.UC2_14_7Three D)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h126 : R126 D) (h86 : W3Lem86_1 G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D) (hW4a : Inputs1719.W4Lem14_6aSmall)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hg5 : Gap17_45_UniqueMaxFive D V₀ V)
    (hV₀ : V₀ ≠ ⊥)
    (hxM : x ∈ D.M) (hXsup : X = L ⊔ conjSubgroup L x) (hXne : X ≠ L)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T) (hBM : B ≤ D.M)
    (hBcard : Nat.card B = p) (hAB : ⁅A, B⁆ = A) (hBT : Permutes B D.T)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h93 : Thm93 V₀ D.T) (hInF : Gap17_45_InFSq A B D.T)
    (hANT : A ≤ B ⊔ normalizer (D.T : Set G)) : False := by
  have hmu : UniqueMax D.M (A ⊔ B ⊔ D.T) :=
    s17_45_uniqueMax_ABT D h147 hg5 ctx hV₀ h8100 hc hAsyl hAT hBM hBcard hAB hBT
  have hm3 : mBar D.M V₀ V ctx.hyp125.isElemAbelian ≤ 3 :=
    s17_45_mBar_le_three (A₀ := A₀) D hx h61 h66 h127 h1114 h162 hTor h1482 h183 h1214 h869 hW4a
      ctx hV₀ hxM hXsup hXne hc hAsyl hBM hBcard hsp hInF hmu
  have hbig : 2 < mSub V₀ := by
    by_contra hle
    have hm2 : mSub V₀ ≤ 2 := by omega
    have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub ctx.hyp125.pairFacts.elemAbelian₀.isPGroup
    have hcard : Nat.card V₀ ≤ 4 := by
      rw [hcardV0]
      calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    have hgt : MBarGT D.M V₀ V 3 := h1669 hcard
    have : 3 < mBar D.M V₀ V ctx.hyp125.isElemAbelian :=
      (ctx.hyp125.mBarGT_iff_lt_mBar 3).1 hgt
    omega
  have h8 : 8 ≤ Nat.card V₀ := by
    have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub ctx.hyp125.pairFacts.elemAbelian₀.isPGroup
    rw [hcardV0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have hBp : IsPGroup p B := IsPGroup.of_card (hBcard.trans (pow_one p).symm)
  have hXM : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → B ⊓ conjSubgroup D.M g = ⊥ :=
    fun g hg _ => s17_45_B_inf_conj_eq_bot hp hBM hBcard hsp g hg
  have hΓ : rankThreeGamma 1 p B ≤ D.M :=
    ElevenNine.gamma_le_of_stronglyEmbedded D hp hsp hBM hBp
  have h16 := twelve_sixteen hTim hcat D h66 h88 ctx.hyp125 h8 h93 hp hp2 hBp hXM hΓ hBT
  have hW0A : A ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    s17_45_wZeroA_of_ANormT hANT h16.2
  have hABTnorm : A ⊔ B ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
    rw [sup_assoc]
    exact sup_le hW0A h16.2
  have hV₀cal : InCalV D.M V₀ := by
    rcases ctx.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV₀
    · exact h0.1
  have hW0ne : E3.wClos V₀ 0 D.T ≠ ⊥ := TwelveShort.wClos_zero_ne_bot D hV₀cal
  have hW0p : IsPGroup 2 (E3.wClos V₀ 0 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T)
  have hloc : IsTwoLocal (normalizer (E3.wClos V₀ 0 D.T : Set G)) :=
    ⟨E3.wClos V₀ 0 D.T, hW0ne, hW0p, rfl⟩
  have hNle : normalizer (E3.wClos V₀ 0 D.T : Set G) ≤ D.M :=
    uc22p22p_le_of_uniqueMax hmu hloc hABTnorm
  have hTI : IsTI V₀ := by
    rcases ctx.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV₀
    · exact h0.2.2.2.1
  have h127' := twelve_seven_one hTim hcat D h86 h126 ctx.hyp125.2 hV₀cal hTI h8
  apply h127'
  rw [inf_eq_right.mpr hNle]
  exact uc22p22u_uniqueMax_mono D hABTnorm hNle hmu

theorem s17_45_case34_false (D : Data G)
    (h147 : Inputs1719.UC2_14_7Three D)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h126 : R126 D) (h86 : W3Lem86_1 G)
    (h111 : W3Thm111 G) (h61 : UC6.R6_1 D)
    (hx : DataExt D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D) (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) (hW4a : Inputs1719.W4Lem14_6aSmall)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hg5 : Gap17_45_UniqueMaxFive D V₀ V)
    (hxM : x ∈ D.M) (hXsup : X = L ⊔ conjSubgroup L x) (hXne : X ≠ L)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T) (hBM : B ≤ D.M)
    (hBcard : Nat.card B = p) (hAB : ⁅A, B⁆ = A) (hBT : Permutes B D.T)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h93 : Thm93 V₀ D.T)
    (hInF : Gap17_45_InFSq A B D.T)
    (hANT : A ≤ B ⊔ normalizer (D.T : Set G)) : False := by
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    have hp3 : p = 3 :=
      s17_45_p_eq_three_of_bot D hx h61 h126 h111 h127 h1214 h869 h640 hFF hW4a h1669 ctx
        hxM hXsup hXne h8100 hc
    exact s17_45_bot_false D h147 h126 h111 h1669 ctx hp3 h8100 hc hAsyl hAT hBM hBcard hAB
      hBT hInF
  · exact s17_45_ne_bot_branch D h147 hTim hcat h66 h88 h126 h86 hx h61 h127 h1114
      h162 hTor h1482 h183 h1214 h869 hW4a h1669 ctx hg5 hV₀ hxM hXsup hXne h8100 hc hAsyl hAT
      hBM hBcard hAB hBT hsp h93 hInF hANT

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
