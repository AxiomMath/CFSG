module

public import CFSG.Quasithin.MS93.S45Fin
public import CFSG.Quasithin.EmptyFaithful.SzMSWTrans
public import CFSG.Quasithin.EmptyFaithful.SzMSWVtx

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45 CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

@[expose] def S45W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) → IsSL3Full M T L → MS93Case13W (Vq M L) L

theorem s45W_of (h43 : S43) (h44 : S44) (h14 : MS14AS) (hSQ : SQTKQuot) (hQ2a : S45Q2a) :
    S45W := by
  intro G _ _ M T L h hmin hb hfull
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have c : Ctx M T L φ := Ctx.ofItems h43 h44 h hmin hb hφ
  have hZV : c.HZV := by
    by_cases hq : Fintype.card F = 2
    · exact hQ2a G M T L F φ c hq
    · exact c.hZV_of_ne_two hq
  obtain ⟨p, hp⟩ := c.exists_isGoodPath_of_ctx 28
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) (by decide)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα (isMVtx_baseA _)
  obtain ⟨W, h₁, h₂, h₃, h₄, h₅⟩ :=
    exists_W_of_isGoodPath c h14 hSQ hZV (hp.smul g) (by omega) hg
  exact caseW_of_baseA h h₁ h₂ ((ltil_le_stab h _).trans h₃) h₄ h₅

end CFSG.Quasithin.SzMSW
