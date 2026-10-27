module

public import CFSG.Quasithin.Vol2.KGFactInspBase
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Bender
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Certificate43
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.H13.KGInsp43

open CFSG.Quasithin
open scoped MatrixGroups

namespace Cfg

variable {X : Type} [Group X] {S R K : Subgroup X} {n : ℕ}

theorem not_isSolvable [Finite X] (h : Cfg S R K n) : ¬ Group.IsSolvable K := by
  have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr h.perfect
  have : Nontrivial K := by
    have h3 := h.three_dvd_card
    refine (Subgroup.nontrivial_iff_ne_bot K).mpr fun hb => ?_
    rw [hb, Subgroup.card_bot] at h3
    omega
  exact Group.IsPerfect.not_isSolvable K

theorem inf_eq_bot_of_psl2 [Finite X] (h : Cfg S R K n) {F : Type}
    [Field F] [Finite F] (e : ↥S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    R ⊓ S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    ((R ⊓ S).subgroupOf S).map e.toMonoidHom with hT
  set C : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (K.subgroupOf S).map e.toMonoidHom with hC
  have hCns : ¬ Group.IsSolvable C := by
    intro hs
    apply h.not_isSolvable
    have e1 : ↥K ≃* ↥C :=
      (Subgroup.subgroupOfEquivOfLe h.le).symm.trans
        ((K.subgroupOf S).equivMapOfInjective e.toMonoidHom e.injective)
    exact Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective
  have hTs : Group.IsSolvable T := by
    have h2 : IsPGroup 2 ↥T :=
      ((h.isPGroup.to_le inf_le_left).comap_of_injective S.subtype S.subtype_injective).map _
    have : Group.IsNilpotent T := h2.isNilpotent
    infer_instance
  have hle : C ≤ Subgroup.normalizer (T : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨s, rfl⟩ := e.surjective y
    have hkN := h.le_normalizer_inf (Subgroup.mem_subgroupOf.mp hk)
    have e2 : (e.toMonoidHom k) * e s * (e.toMonoidHom k)⁻¹ = e (k * s * k⁻¹) := by
      simp [map_mul, map_inv]
    rw [e2]
    simp only [hT, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hkN s
  by_contra hRS
  apply CFSG.SignalizerFunctorTheorem.CatalogBridge.nonLocalized_of_not_isSolvable_psl2 C hCns T
    _ hTs hle
  intro hTb
  apply hRS
  rw [eq_bot_iff]
  intro x hx
  have hxT : e ⟨x, (Subgroup.mem_inf.mp hx).2⟩ ∈ T :=
    ⟨⟨x, (Subgroup.mem_inf.mp hx).2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [hTb, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at hxT
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxT)

theorem false_of_psl2 [Finite X] (h : Cfg S R K n) (hRS : R ≤ S)
    {p f : ℕ} (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥S .PSL 2 p f) : False := by
  obtain ⟨-, F, _, _, -, ⟨e⟩⟩ := hm
  have hb := h.inf_eq_bot_of_psl2
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)
  rw [inf_eq_left.mpr hRS] at hb
  exact h.ne_bot hb

theorem false_of_twoLocalsSolvable [Finite X] (h : Cfg S R K n) (hRS : R ≤ S)
    (hT : CFSG.Quasithin.H13.Cor332.TwoLocalsSolvable ↥S) : False := by
  apply h.not_isSolvable
  have hR : R.subgroupOf S ≠ ⊥ := by
    intro hb
    apply h.ne_bot
    rw [eq_bot_iff]
    intro r hr
    have hr' : (⟨r, hRS hr⟩ : ↥S) ∈ R.subgroupOf S := hr
    rw [hb, Subgroup.mem_bot] at hr'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hr')
  have hR2 : IsPGroup 2 ↥(R.subgroupOf S) :=
    h.isPGroup.comap_of_injective S.subtype S.subtype_injective
  have hKN : K.subgroupOf S ≤ Subgroup.normalizer ((R.subgroupOf S : Subgroup ↥S) : Set ↥S) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have hkN := h.le_normalizer (Subgroup.mem_subgroupOf.mp hk)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hkN s
  have hs := hT _ _ hR hR2 hKN
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe h.le).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h.le).surjective

theorem false_of_psu3_two [Finite X] (h : Cfg S R K n) (hRS : R ≤ S) {f : ℕ} (hf : 2 ≤ f)
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥S .PSU 3 2 f) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
  have hcard : Nat.card F = 2 ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  let e' : ↥S ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) F (2 ^ f)) := e
  have e'' := e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)
  exact h.false_of_twoLocalsSolvable hRS
    (CFSG.Quasithin.H13.Cor332.twoLocalsSolvable_of_fusionIsBenderGroup
      (Or.inr (Or.inl ⟨f, hf, ⟨e''⟩⟩)))

end Cfg

end CFSG.Quasithin.H13.KGInsp43
