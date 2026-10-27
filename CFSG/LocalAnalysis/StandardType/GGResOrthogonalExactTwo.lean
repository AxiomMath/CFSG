module

public import CFSG.LocalAnalysis.StandardType.GGResSingularAExactTwo

public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public import Mathlib.Data.ZMod.Basic

public import Mathlib.Data.Fintype.Card

public import CFSG.RankThree.PartOne.KF.ClsPOmegaPlus

public import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus

public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFrame

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPiece

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearQuadratic

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp3

public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo

public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalCentre

public import CFSG.GroupTheory.ElementaryAbelianTransport

public import CFSG.RankThree.PartOne.KFR4.Row4

public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGCentre
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiGrpSq
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOrthModel
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryExactTwo
public import CFSG.LocalAnalysis.StandardType.GGTorsionPOmegaComp
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import CFSG.RankThree.PartOne.S12.Sec136Inputs
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec138Loc
public import CFSG.RankThree.PartOne.S12.Sec1511Y3

public section

namespace CFSG.StandardType.OrthKExactTwo

open CFSG CFSG.Assembly

theorem actualImageHom_selfCentralizing
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (hRig : GGLabelRigidInput)
    (hmarkK : GGInnerDiagOn Bs K)
    (hBs : CFSG.Assembly.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hKlab : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hrank : 4 ≤ lab.rank)
    (hcp : ¬ p ∣ Nat.card (Subgroup.center ↥K))
    :
    ∃ ρ : Bs →* (↥K ⧸ Subgroup.center ↥K),
      CFSG.Assembly.IsElemAbelian p ρ.range ∧
        (∀ g ∈ Subgroup.centralizer (ρ.range : Set (↥K ⧸ Subgroup.center ↥K)),
          g ^ p = 1 → g ∈ ρ.range) ∧
        (∀ (b : Bs) (y : ↥K),
          QuotientGroup.mk (ggGamma K (GGInnerDiagOn.le_normalizer hmarkK) b y) =
            MulAut.conj (ρ b) (QuotientGroup.mk y)) := by
  classical
  let Kq := ↥K ⧸ Subgroup.center ↥K
  let hN := GGInnerDiagOn.le_normalizer hmarkK
  have hZq : Subgroup.center Kq = ⊥ := center_quotient_eq_bot_of_innerDiagOn hmarkK
  have hforall : ∀ b : Bs, ∃ β : MulAut Kq, β ∈ LargeEvenInnSet Kq ∧
      ∀ y : ↥K, QuotientGroup.mk (ggGamma K hN b y) = β (QuotientGroup.mk y) :=
    fun b => ggInnerDiagOn_orthogonal_quotient_gamma_inner (hRig := hRig) (p := p)
      (Bs := Bs) (K := K) (x := (b : G)) hmarkK b.2 hΛ hKlab htag hrank
  choose β hβInn hβact using hforall
  have hβmul : ∀ a b : Bs, β (a * b) = β a * β b := by
    intro a b
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← hβact (a * b) y]
    rw [show ggGamma K hN (a * b) y = ggGamma K hN a (ggGamma K hN b y) from by
      rw [map_mul]; rfl]
    rw [hβact a (ggGamma K hN b y), hβact b y]
    rfl
  let βhom : Bs →* MulAut Kq := MonoidHom.mk' β hβmul
  have hβrange : βhom.range ≤ (MulAut.conj : Kq →* MulAut Kq).range := by
    rintro _ ⟨b, rfl⟩
    exact hβInn b
  let conjInj := CFSG.mulAutConj_injective_of_center_eq_bot hZq
  let r : Bs → Kq := fun b =>
    (MonoidHom.ofInjective conjInj).symm ⟨βhom b, hβrange ⟨b, rfl⟩⟩
  have hrconj : ∀ b : Bs, MulAut.conj (r b) = βhom b :=
    fun b => MonoidHom.apply_ofInjective_symm conjInj ⟨βhom b, hβrange ⟨b, rfl⟩⟩
  have hrmul : ∀ a b : Bs, r (a * b) = r a * r b := by
    intro a b
    apply CFSG.mulAutConj_injective_of_center_eq_bot hZq
    simpa [hrconj, βhom, map_mul]
  let rhom : Bs →* Kq := MonoidHom.mk' r hrmul
  refine ⟨rhom, ?_, ?_, ?_⟩
  · exact CFSG.StandardType.isElemAbelian_range
      (fun a b : Bs => Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs a.2 b.2))
      (fun b : Bs => Subtype.ext (by simpa using hBs.2 b b.2)) rhom
  · intro g hg hgp
    obtain ⟨n, hnq, hnp⟩ := CFSG.StandardType.exists_lift_pow_eq_one
      (L' := ↥K) (ψ := QuotientGroup.mk' (Subgroup.center ↥K)) (Fact.out)
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hcp hgp
    have hfix : ∀ b : Bs, ggGamma K hN b n = n := by
      intro b
      apply CFSG.StandardType.eq_of_lift_pow_eq_one
        (L' := ↥K) (ψ := QuotientGroup.mk' (Subgroup.center ↥K)) (Fact.out)
        (by rw [QuotientGroup.ker_mk']) hcp
      · have h1 : QuotientGroup.mk (ggGamma K hN b n) = βhom b (QuotientGroup.mk n) := by
          simpa [βhom] using hβact b n
        have h2 : βhom b (QuotientGroup.mk n) = QuotientGroup.mk n := by
          have hrb : r b ∈ rhom.range := ⟨b, rfl⟩
          have hcomm : r b * g = g * r b := hg (r b) hrb
          rw [← hrconj b]
          change r b * QuotientGroup.mk n * (r b)⁻¹ = QuotientGroup.mk n
          rw [show QuotientGroup.mk n = g from hnq, hcomm, mul_assoc, mul_inv_cancel, mul_one]
        change QuotientGroup.mk (ggGamma K hN b n) = QuotientGroup.mk n
        exact h1.trans h2
      · rw [← map_pow, hnp, map_one]
      · exact hnp
    have hfixRange : ∀ a ∈ (ggGamma K hN).range, a n = n := by
      intro a ha
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
      exact hfix b
    have hmemAut : MulAut.conj n ∈ (ggGamma K hN).range :=
      ggTorusSelfCent_ggGamma hN hSC n hfixRange hnp
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hmemAut
    have h1 : βhom b = MulAut.conj (QuotientGroup.mk n) := by
      ext x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      calc
        βhom b (QuotientGroup.mk y) = QuotientGroup.mk (ggGamma K hN b y) :=
          (hβact b y).symm
        _ = (MulAut.conj (QuotientGroup.mk n)) (QuotientGroup.mk y) := by
          rw [hb]
          rfl
    have h2 : r b = QuotientGroup.mk n := by
      apply CFSG.mulAutConj_injective_of_center_eq_bot hZq
      rw [hrconj b, h1]
    rw [← hnq]
    simpa [h2] using (⟨b, rfl⟩ : r b ∈ rhom.range)
  · intro b y
    calc
      QuotientGroup.mk (ggGamma K hN b y) = βhom b (QuotientGroup.mk y) := hβact b y
      _ = (MulAut.conj (rhom b)) (QuotientGroup.mk y) := by
        change βhom b (QuotientGroup.mk y) = (MulAut.conj (r b)) (QuotientGroup.mk y)
        rw [hrconj b]

theorem center_not_dvd_of_orthogonal_marking
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hmarkK : GGInnerDiagOn Bs K)
    {lab : LargeEvenLabel} (hKlab : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hrank : 4 ≤ lab.rank) :
    ¬ p ∣ Nat.card (Subgroup.center ↥K) := by
  have hCPall : LargeEvenLabelAll lab (fun R _ _ _ => GGCenterPrime p R) := by
    rcases htag with hD | hD
    · exact largeEvenLabelAll_centerPrime_omegaPlus hD hrank hp hp2
    · exact largeEvenLabelAll_omegaMinus hD hrank fun _ _ _ _ _ _ _ hirr =>
        CorFourTwoOpen.ggCenterPrime_omegaMinus hp hp2 (by omega) hirr
  obtain ⟨R, hGroup, I, F, hQ⟩ := largeEvenRawDatum_exists (hCPall _ hKlab)
  letI : Group R := hGroup
  obtain ⟨⟨θ⟩, hCP⟩ := hQ
  exact hCP K (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))
    (θ.surjective.comp (QuotientGroup.mk'_surjective _))
    (by
      intro z hz
      have hz1 : θ (QuotientGroup.mk' (Subgroup.center ↥K) z) = 1 := hz
      have hz2 : QuotientGroup.mk' (Subgroup.center ↥K) z = 1 := by
        apply θ.injective
        simpa using hz1
      exact (QuotientGroup.eq_one_iff z).mp hz2) hmarkK.1

theorem exists_quadratic_image_of_orthogonal_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} (hRig : GGLabelRigidInput) (hp2 : p ≠ 2)
    (hmarkK : GGInnerDiagOn Bs K) (hBs : CFSG.Assembly.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hKlab : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hrank : 4 ≤ lab.rank) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module F V)
      (_ : FiniteDimensional F V) (_ : Nontrivial V) (Q : QuadraticForm F V)
      (hQ : Q.polarBilin.Nondegenerate)
      (eQ : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.RankThree.Classical2.ProjOrthDerived Q)
      (ρ : Bs →* (↥K ⧸ Subgroup.center ↥K)),
      Nat.card F = 2 ^ lab.n ∧ ringChar F = 2 ∧
      (∃ U : Submodule F V, Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      Module.finrank F V = 2 * lab.rank ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ lab.tag = .D) ∧
      (let σ := eQ.trans (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
       let E_Q := ρ.range.map σ.toMonoidHom
       CFSG.Assembly.IsElemAbelian p E_Q ∧
         ∀ g ∈ Subgroup.centralizer
           (E_Q : Set (CFSG.RankThree.Classical2.orthDerived Q)),
           g ^ p = 1 → g ∈ E_Q) ∧
      (∀ (b : Bs) (z : ↥K),
        eQ (QuotientGroup.mk (ggGamma K
          (GGInnerDiagOn.le_normalizer hmarkK) b z)) =
          MulAut.conj (eQ (ρ b)) (eQ (QuotientGroup.mk z))) := by
  classical
  obtain ⟨ρ, hρE, hρSC, hρconj⟩ :=
    actualImageHom_selfCentralizing hRig hmarkK hBs hSC hΛ hKlab htag hrank
      (center_not_dvd_of_orthogonal_marking Fact.out hp2 hmarkK hKlab htag hrank)
  rcases lab with ⟨tag, rank, n⟩
  have hrank' : 4 ≤ rank := by simpa using hrank
  have hmodel : ∃ t : CFSG.Open.StatedLieTag,
      (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      (t = .POmegaPlus ↔ tag = .D) ∧
      CFSG.Open.StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) t rank 2 n := by
    rcases htag with hD | htwD
    · cases hD
      refine ⟨.POmegaPlus, Or.inl rfl, iff_of_true rfl rfl, ?_⟩
      simpa using statedClassicalModel_of_hasLabel_typeD
        (X := ↥K ⧸ Subgroup.center ↥K) (by omega) (by simpa using hKlab)
    · cases htwD
      refine ⟨.POmegaMinus, Or.inr rfl, ?_, ?_⟩
      · exact iff_of_false (by decide) (by decide)
      · simpa using statedClassicalModel_of_hasLabel_typeTwD
          (X := ↥K ⧸ Subgroup.center ↥K) (by omega) (by simpa using hKlab)
  obtain ⟨t, ht, hsign, hG⟩ := hmodel
  have hn : 0 < n := by
    rcases ht with rfl | rfl <;> exact hG.1.2.1
  obtain ⟨F, hField, hFinite, V, hAdd, hMod, hFinDim, Q,
      hQ, hT, hcard, hdim, hplus, ⟨eQ⟩⟩ := TCJ.exists_projOrth_model_type ht hG
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : AddCommGroup V := hAdd
  letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  have hring : ringChar F = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hn hcard
  haveI : CharP F 2 := ringChar.of_eq hring
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  have htype : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ tag = .D :=
    hplus.trans hsign
  let σ := eQ.trans (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
  have himage : CFSG.Assembly.IsElemAbelian p (ρ.range.map σ.toMonoidHom) ∧
      ∀ g ∈ Subgroup.centralizer
        (ρ.range.map σ.toMonoidHom : Set (CFSG.RankThree.Classical2.orthDerived Q)),
        g ^ p = 1 → g ∈ ρ.range.map σ.toMonoidHom := by
    refine ⟨hρE.map σ.toMonoidHom, ?_⟩
    intro g hg hgp
    have hcent : σ.symm g ∈ Subgroup.centralizer (ρ.range : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      apply σ.injective
      have hσe : σ e ∈ ρ.range.map σ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨e, he, rfl⟩
      have hc := hg (σ e) hσe
      simpa only [map_mul, σ.apply_symm_apply] using hc
    have hpow : (σ.symm g) ^ p = 1 := by
      apply σ.injective
      simpa only [map_pow, map_one, σ.apply_symm_apply] using hgp
    exact Subgroup.mem_map.mpr
      ⟨σ.symm g, hρSC (σ.symm g) hcent hpow, σ.apply_symm_apply g⟩
  refine ⟨F, hField, hFinite, inferInstance, V, hAdd, hMod, hFinDim, inferInstance,
    Q, hQ, eQ, ρ, hcard, hring, hT, hdim, htype, himage, ?_⟩
  intro b z
  rw [hρconj b z]
  simp [MulAut.conj_apply, map_mul, map_inv]

end CFSG.StandardType.OrthKExactTwo

end
