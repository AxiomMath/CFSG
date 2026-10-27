module

public import CFSG.LocalAnalysis.StandardType.GGE8A8Field
public import CFSG.LocalAnalysis.StandardType.GGLangData
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGResTrialityNbr
public import CFSG.LocalAnalysis.StandardType.GGTCJD4Tag

public section

namespace CFSG.StandardType

section Assembly

open CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTCJE8A8Sign
    : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (n' f p : ℕ) (Bs : Subgroup (GGAutU .E8 n' f))
    (S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)),
    GGLangData L .E8 n' f p Bs S π coord → p.Prime → p ≠ 2 → ∀ b : Bs, b ≠ 1 →
      ∀ Jm : Subgroup (GGAutU .E8 n' f),
        CFSG.Assembly.IsComponentOf Jm ((ggPsiU .E8 n' f).range ⊓
          Subgroup.centralizer ({(b : GGAutU .E8 n' f)} : Set (GGAutU .E8 n' f))) →
        ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
          GGHasLabel labJ (↥Jm ⧸ Subgroup.center ↥Jm) →
          (labJ.tag = .A ∨ labJ.tag = .twA) → labJ.rank = 8 → labJ.n = f →
          p = 3 ∧ (labJ.tag = .A → 3 ∣ 2 ^ f - 1) ∧ (labJ.tag = .twA → 3 ∣ 2 ^ f + 1)

@[expose] def GGE8LangWitness
    {G : Type} [Group G] (n p : ℕ) (J : Subgroup G) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (n' : ℕ) (Bs : Subgroup (GGAutU .E8 n' n))
    (S : Matrix (Fin (ggU (absTag .E8) 6 n).D.rank) (Fin (ggU (absTag .E8) 6 n).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag .E8) 6 n).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 n).D.rank → ZMod p))
    (_ : GGLangData L .E8 n' n p Bs S π coord) (b : Bs) (Jm : Subgroup (GGAutU .E8 n' n)),
    b ≠ 1 ∧
      CFSG.Assembly.IsComponentOf Jm ((ggPsiU .E8 n' n).range ⊓
        Subgroup.centralizer ({(b : GGAutU .E8 n' n)} : Set (GGAutU .E8 n' n))) ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* (↥Jm ⧸ Subgroup.center ↥Jm))

theorem ggTBJ_maxRank_row_L
    (hSign : GGTCJE8A8Sign)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hn : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (htag : labJ.tag = .A ∨ labJ.tag = .twA) (hrank : labJ.rank = 8) (hdvd : n ∣ labJ.n)
    (hW : GGE8LangWitness n p J) :
    GGResRowAt ggRowMaxRank p J L := by
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  obtain ⟨L₀, _, _, n', Bm, S, π, coord, Bl, b, Jm, hb, hJm, ⟨θ⟩⟩ := hW
  have hJ' : GGHasLabel labJ (↥Jm ⧸ Subgroup.center ↥Jm) := ggHasLabel_of_mulEquiv θ hJ
  have hfield : labJ.n = n := ggE8_A8_field hJL hn hL hΛJ hJ htag hrank hdvd
  obtain ⟨hp3, hA, htwA⟩ :=
    hSign L₀ n' n p Bm S π coord Bl hp hp2 b hb Jm hJm labJ hΛJ hJ' htag hrank hfield
  refine ⟨labJ, ⟨.E8, 0, n⟩, hΛJ, hn, hJ, hL, ?_⟩
  rcases labJ with ⟨t, r, k⟩
  simp only [ggRowMaxRank, LargeEvenLabel.tag, LargeEvenLabel.rank, LargeEvenLabel.n] at *
  rcases htag with ht | ht
  · left
    exact ⟨by simp [hrank, ht], hp3, by simpa [hfield] using hA ht, by simp [hfield]⟩
  · right
    exact ⟨by simp [hrank, ht], hp3, by simpa [hfield] using htwA ht, by simp [hfield]⟩

theorem ggTBJ_maxRank_row_K
    (hSign : GGTCJE8A8Sign) (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hn : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (htag : labJ.tag = .A ∨ labJ.tag = .twA) (hrank : labJ.rank = 8) (hdvd : n ∣ labJ.n)
    (hW : GGE8LangWitness n p J) :
    GGResRowAt ggRowMaxRank p J K := by
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hcfg.1 hcfg.2.2 y K hnb
  obtain ⟨L₀, _, _, n', Bm, S, π, coord, Bl, b, Jm, hb, hJm, ⟨θ⟩⟩ := hW
  have hJ' : GGHasLabel labJ (↥Jm ⧸ Subgroup.center ↥Jm) := ggHasLabel_of_mulEquiv θ hJ
  have hfield : labJ.n = n := ggE8_A8_field hJK hn hK hΛJ hJ htag hrank hdvd
  obtain ⟨hp3, hA, htwA⟩ :=
    hSign L₀ n' n p Bm S π coord Bl hp hp2 b hb Jm hJm labJ hΛJ hJ' htag hrank hfield
  refine ⟨labJ, ⟨.E8, 0, n⟩, hΛJ, hn, hJ, hK, ?_⟩
  rcases labJ with ⟨t, r, k⟩
  simp only [ggRowMaxRank, LargeEvenLabel.tag, LargeEvenLabel.rank, LargeEvenLabel.n] at *
  rcases htag with ht | ht
  · left
    exact ⟨by simp [hrank, ht], hp3, by simpa [hfield] using hA ht, by simp [hfield]⟩
  · right
    exact ⟨by simp [hrank, ht], hp3, by simpa [hfield] using htwA ht, by simp [hfield]⟩

end Assembly

end CFSG.StandardType

end
