module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qf
public import CFSG.Quasithin.Background.G25Comm
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.AGLEmbedding
variable {G : Type} [Group G] [Finite G]

theorem s16h_center_eq_bot_of_center_quotient_psl2_eight {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsQuasisimple X) (e : X ⧸ Subgroup.center X ≃* PSL2GF 2 3) :
    Subgroup.center X = ⊥ := by
  haveI : Group.IsPerfect X := ⟨hX.1⟩
  let q : X →* PSL2GF 2 3 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hqker : q.ker = Subgroup.center X := by
    ext x
    simp only [q, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  let g : PSL2GF 2 3 →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3)).toMonoidHom
  have hginj : Function.Injective g := fun a b h =>
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3)).injective h
  let π : X →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3) := g.comp q
  have hπker : π.ker = Subgroup.center X := by
    have h1 : π.ker = q.ker := MonoidHom.ker_comp_of_injective q g hginj
    rw [h1, hqker]
  have hπsurj : Function.Surjective π :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3)).surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hbot : π.ker = ⊥ :=
    CFSG.LocalAnalysis.EvenBN.Common.ker_eq_bot_of_perfect_central_sl2_two_pow
      (m := 3) (k := GaloisField 2 3) (by norm_num) (GaloisField.card 2 3 (by norm_num))
      hπsurj (by rw [hπker])
  rwa [hπker] at hbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
