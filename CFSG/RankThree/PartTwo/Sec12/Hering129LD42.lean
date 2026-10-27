module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd
import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof418
public import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KF3D42 : Prop :=
  ∀ (Q : Type) [Group Q] (r : TauCeti.PrimePower)
    (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid), r.card = 2 →
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) →
    ∀ β : MulAut Q, orderOf β = 3 →
      ∀ P : Subgroup Q, P ≤ MonoidHom.eqLocus (β : Q →* Q) (MonoidHom.id Q) →
        Group.IsPerfect ↥P →
        (P.subgroupOf (MonoidHom.eqLocus (β : Q →* Q) (MonoidHom.id Q))).IsSubnormal →
        ∀ (p n : ℕ) [Fact p.Prime], 4 ≤ p ^ n →
          (∃ f : ↥P →* projSL 2 (GaloisField p n), Function.Surjective f) → p ^ n = 8

@[expose] def Gap129EndENotD42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b → x ∉ L →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y → NoLieParamInRange Y →
        Typ129IIIcType L Y →
        (∀ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid),
          r.card = 2 → ¬ Nonempty (Y ⧸ CFSG.pCore 2 Y ≃*
            (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group)) →
        ∀ E : Subgroup G, Typ129IIIcE A c Y x E →
      ∀ d ∈ D129 a b, d ∉ Subgroup.zpowers b → d ∈ L → ∀ Y' J : Subgroup G,
        Core129 A c d Y' → resCent K d ≤ Y' → JData129 A c L Y' J → b ∈ J →
        ∀ r : TauCeti.PrimePower,
          Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) r.card →
          ¬ PiModNine r.card → ¬ PiModNine q.card →
          ∃ F : Subgroup G, Late.IsE27 F ∧ c ∈ F ∧ F ≤ lcBar c L ∧
            ¬ Subgroup.normalizer (F : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

section Aux

variable {G : Type} [Group G] [Finite G]

theorem exists_surjective_imageModTheta {Y X : Subgroup G} (hXY : X ≤ Y) :
    ∃ g : ↥(Sec8.imageModTheta Y X) →* (↥X ⧸ aschbacherSolvableCore 3 ↥X),
      Function.Surjective g := by
  set φ := Sec8.Item87Res2Proof.toQuot hXY with hφ
  have hrange : φ.range = Sec8.imageModTheta Y X := Sec8.Item87Res2Proof.range_toQuot hXY
  have hker : φ.ker ≤ aschbacherSolvableCore 3 ↥X := Sec8.Item87Res2Proof.ker_toQuot_le hXY
  let ψ : (↥X ⧸ φ.ker) →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    QuotientGroup.map φ.ker (aschbacherSolvableCore 3 ↥X) (MonoidHom.id _) hker
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(x : ↥X ⧸ φ.ker), rfl⟩
  let e : ↥(Sec8.imageModTheta Y X) ≃* (↥X ⧸ φ.ker) :=
    (MulEquiv.subgroupCongr hrange.symm).trans (QuotientGroup.quotientKerEquivRange φ).symm
  exact ⟨ψ.comp e.toMonoidHom, hψ.comp e.surjective⟩

end Aux

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
