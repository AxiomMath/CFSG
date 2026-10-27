module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedSpRoot
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedSp
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelectedPSU
import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Main
import CFSG.RankThree.PartOne.S11d.OrthCaseN
import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
import CFSG.Quasithin.H13.A6S1372L76X
import CFSG.Quasithin.EmptyFaithful.S152He8Aut
import CFSG.Quasithin.H13.A5Quad
import CFSG.Quasithin.H13.A5S1523
import CFSG.Quasithin.H13.A5Sit15d
import CFSG.Quasithin.H13.A6S1372L19b
import CFSG.Quasithin.H13.A6S1372L76V
import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFL2
import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFSmall
import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFSp4

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open Matrix CFSG.StandardType.ClassicalPosition

theorem GGPresentsG0.range_comp_PSp_source
    {G : Type} [Group G] {G₀ X : Subgroup G} {n r f : ℕ}
    {ψ : (ggU .PSp n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ)
    (ι : (ggU .PSp r f).K →* (ggU .PSp n f).K)
    (hrange : ι.range = X.comap ψ) (hmap : (X.comap ψ).map ψ = X) :
    (ψ.comp ι).range = X := by
  rw [MonoidHom.range_comp, hrange, hmap]

theorem GGPresentsG0.isPerfect_PSp_source
    {G : Type} [Group G] {G₀ X : Subgroup G} {n r f : ℕ}
    {ψ : (ggU .PSp n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab))
    (ι : (ggU .PSp r f).K →* (ggU .PSp n f).K)
    (hι : Function.Injective ι) (hrange : ι.range = X.comap ψ)
    (hmap : (X.comap ψ).map ψ = X) : Group.IsPerfect (ggU .PSp r f).K := by
  have hcomp_inj : Function.Injective (ψ.comp ι) := hpres.injective_PSp.comp hι
  let e : (ggU .PSp r f).K ≃* ↥X :=
    (MonoidHom.ofInjective hcomp_inj).trans
      (MulEquiv.subgroupCongr (hpres.range_comp_PSp_source ι hrange hmap))
  letI : Group.IsPerfect ↥X := ⟨hmark.1⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem GGPresentsG0.admissible_PSp_source
    {G : Type} [Group G] [Finite G] {G₀ X : Subgroup G} {n r f : ℕ}
    {ψ : (ggU .PSp n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab))
    (ι : (ggU .PSp r f).K →* (ggU .PSp n f).K)
    (hι : Function.Injective ι) (hrange : ι.range = X.comap ψ)
    (hmap : (X.comap ψ).map ψ = X)
    {β : Fin (ggU .PSp r f).D.rank → ℤ} (hβ : GGLongRoot (ggU .PSp r f).D β) :
    StatedLieAdmissible .PSp r 2 f ∧ 2 ≤ (ggU .PSp r f).D.rank := by
  classical
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  letI : Group.IsPerfect (StatedSp r (GaloisField 2 f)) :=
    hpres.isPerfect_PSp_source hmark ι hι hrange hmap
  have hcomp_inj : Function.Injective (ψ.comp ι) := hpres.injective_PSp.comp hι
  let e : (ggU .PSp r f).K ≃* ↥X :=
    (MonoidHom.ofInjective hcomp_inj).trans
      (MulEquiv.subgroupCongr (hpres.range_comp_PSp_source ι hrange hmap))
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    obtain ⟨w, γ, hγ, -, -⟩ := hβ
    rcases hγ with ⟨w', i, -⟩ | ⟨w', i, -, -⟩ <;> exact Fin.elim0 i
  have hr1 : r ≠ 1 := by
    intro h
    subst r
    obtain ⟨eSp⟩ :=
      CFSG.RankThree.GF2n.Stroth80.nonempty_statedSp_one_mulEquiv_statedSL_two (GaloisField 2 f)
    let eSL : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
      e.symm.trans (eSp.trans
        (CFSG.HardMathSupport.Solomon.Coordinator.l2opStatedSLEquiv 2 (GaloisField 2 f)))
    by_cases hf1 : f = 1
    · have hcard : Nat.card (GaloisField 2 f) = 2 := by simpa [hf1] using hK
      letI : Group.IsPerfect ↥X := ⟨hmark.1⟩
      letI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
        Group.IsPerfect.ofSurjective (f := eSL.toMonoidHom) eSL.surjective
      have hne : CFSG.LieType.Steinberg.sl2Upper (1 : GaloisField 2 f) ≠ 1 := by
        intro h
        have he := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) =>
          (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1) h
        change (1 : GaloisField 2 f) = 0 at he
        exact one_ne_zero he
      letI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
        ⟨⟨CFSG.LieType.Steinberg.sl2Upper 1, 1, hne⟩⟩
      exact Group.IsPerfect.not_isSolvable
        (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
        (isSolvable_specialLinear_of_card_eq_two (by simp) hcard)
    · have hf2 : 2 ≤ f := by omega
      obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_markedModel hmark
      obtain ⟨R, _, I, F, _, _, θ, hg, hMR⟩ := largeEvenRawDatum_exists hraw
      have hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X) :=
        MarkedModel.of_mulEquiv θ.symm hMR
      exact false_of_guardedLabel_of_linear_unitary_model hg hM (Or.inl rfl)
        (fun _ => hf2) (CFSG.RankThree.PartOne.lieModel_quotient_of_SL2 hK hf2 eSL)
  have hr : 2 ≤ r := by omega
  have hsmall : (r, 2 ^ f) ≠ (2, 2) := by
    intro h
    obtain ⟨rfl, hq⟩ := Prod.mk.inj h
    have hcard : Nat.card (GaloisField 2 f) = 2 := hK.trans hq
    exact CFSG.Quasithin.H13.Prop711.not_isPerfect_statedSp_two hcard inferInstance
  exact ⟨⟨Nat.prime_two, hf, hr, hsmall⟩, hr⟩

theorem GGPresentsG0.exists_selected_PSp_of_source
    {G : Type} [Group G] [Finite G] {G₀ X : Subgroup G} {n r f : ℕ}
    {ψ : (ggU .PSp n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab))
    (ι : (ggU .PSp r f).K →* (ggU .PSp n f).K)
    (hι : Function.Injective ι) (hrange : ι.range = X.comap ψ)
    (hmap : (X.comap ψ).map ψ = X)
    {β : Fin (ggU .PSp r f).D.rank → ℤ} (hβ : GGLongRoot (ggU .PSp r f).D β)
    {v w : Fin n ⊕ Fin n → GaloisField 2 f}
    (hvw : v ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w = 1)
    (hX : (((ggU .PSp r f).D.rootGroup β).map ι).map
      (StatedSp n (GaloisField 2 f)).subtype =
        matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0) v))
    (hXm : (((ggU .PSp r f).D.rootGroup (-β)).map ι).map
      (StatedSp n (GaloisField 2 f)).subtype =
        matTransvGroup w (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0) w)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  obtain ⟨hadm, hr⟩ := hpres.admissible_PSp_source hmark ι hι hrange hmap hβ
  have hn : 2 ≤ n := hpres.1.1.2.2.1
  have hcomp_inj : Function.Injective (ψ.comp ι) := hpres.injective_PSp.comp hι
  have hker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSp r f).K := by
    rw [(MonoidHom.ker_eq_bot_iff (ψ.comp ι)).2 hcomp_inj]
    exact bot_le
  obtain ⟨δ, model, hselected⟩ := presentedSelectedSL2At_of_transvPair hn hr ψ ι hβ hvw hX hXm
  exact ⟨((ψ.comp ι).comp model.phi).range,
    ⟨.PSp, r, f, ψ.comp ι, hadm, hr, hker, hpres.range_comp_PSp_source ι hrange hmap,
      GaloisField 2 f, inferInstance, inferInstance, inferInstance, δ, model, rfl⟩,
    hselected⟩

theorem ggActualMember_PSp_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (ψ : (ggU .PSp n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSp n f).D .PSp n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  obtain ⟨r, ι, β, hι, hrange, hmap, hβ, v, w, hvw, hX, hXm⟩ :=
    ggActualMember_PSp_explicit_source hcfg ψ hpres horigin hmark
  exact hpres.exists_selected_PSp_of_source hmark ι hι hrange hmap hβ hvw hX hXm

end CFSG.StandardType
