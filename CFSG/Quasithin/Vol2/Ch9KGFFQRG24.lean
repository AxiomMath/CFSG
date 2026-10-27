module

public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Background.KGRankG24
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Centralizers
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Assembly.QuasithinDefs
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
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem autRankLe_adjG2_four
    (hR : RankG24Fact) (hF : RankG24FrobCentFact) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) : AutRankLe ↥(adjointGroup .G2 K) 6 := by
  classical
  have : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  have : Finite (MulAut ↥(adjointGroup .G2 K)) :=
    Finite.of_injective (fun α : MulAut ↥(adjointGroup .G2 K) => (α : _ → _))
      DFunLike.coe_injective
  have hinj := conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := .G2) (K := K))
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (f := 2) le_rfl K (by rw [hK]; norm_num)
  have hΘ : Nat.card (K ≃+* K) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K (n := 2)
      (by rw [hK]; norm_num)).1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hΘ]; norm_num)
  intro E hE
  refine rk_le_of_card_le_two_pow hE.isPGroup ?_
  by_cases hin : E ≤ Θ.ker
  · have hEr : E ≤ (MulAut.conj : ↥(adjointGroup .G2 K) →* _).range := hker ▸ hin
    have h1 := hR K hK (E.comap MulAut.conj) (IsElemAb2.isElemAbelian (hE.comap _ hinj))
    rwa [card_comap_of_le_range hinj hEr] at h1
  · obtain ⟨α, hαE, hαo⟩ := Set.not_subset.mp hin
    have hα1 : α ≠ 1 := fun h => hαo (h ▸ Θ.ker.one_mem)
    have hα2 : orderOf α = 2 := orderOf_eq_prime (hE.2 α hαE) hα1
    have hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(adjointGroup .G2 K) := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, ← hker]
      exact hαo
    obtain ⟨x, hx⟩ := CFSG.EvenSmallLie.GTwoFour.exists_conj_eq_frobenius hK (frobenius K 2)
      (fun c => frobenius_def 2 c) hα2 hout
    set c : MulAut ↥(adjointGroup .G2 K) := MulAut.conj x with hc
    set β : MulAut ↥(adjointGroup .G2 K) := c * α * c⁻¹ with hβ
    set E' : Subgroup (MulAut ↥(adjointGroup .G2 K)) := E.map (MulAut.conj c).toMonoidHom
      with hE'
    have hcard' : Nat.card ↥E' = Nat.card ↥E :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have hβE : β ∈ E' := ⟨α, hαE, rfl⟩
    have hE'el : IsElemAb2 E' := hE.map _
    have h1 := card_le_mul_card_inf_ker Θ E'
    rw [hΘ] at h1
    set G₀ : Subgroup ↥(adjointGroup .G2 K) := (E' ⊓ Θ.ker).comap MulAut.conj with hG₀
    have hfix : ∀ g ∈ G₀, Units.map (entrywiseHom (frobenius K 2))
        (g : ModGL .G2 K) = (g : ModGL .G2 K) := by
      intro g hg
      have hcomm : MulAut.conj g * β = β * MulAut.conj g := hE'el.1 _ hg.1 β hβE
      have h2 : MulAut.conj (β g) = MulAut.conj g := by
        refine MulEquiv.ext fun y => ?_
        have h3 := congrArg (fun γ : MulAut ↥(adjointGroup .G2 K) => γ (β.symm y)) hcomm
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at h3
        rw [MulAut.conj_apply, MulAut.conj_apply, h3, map_mul, map_mul, map_inv,
          MulEquiv.apply_symm_apply]
      have h4 : β g = g := hinj h2
      rw [← hx g]
      exact congrArg Subtype.val h4
    have hG₀el : CFSG.Open.IsElemAbelian 2 G₀ :=
      IsElemAb2.isElemAbelian ((hE'el.mono inf_le_left).comap _ hinj)
    have h5 := hF K hK (frobenius K 2) (fun c => frobenius_def 2 c) G₀ hG₀el hfix
    have h6 : Nat.card ↥G₀ = Nat.card ↥(E' ⊓ Θ.ker) :=
      card_comap_of_le_range hinj (by rw [← hker]; exact inf_le_right)
    calc Nat.card ↥E = Nat.card ↥E' := hcard'.symm
      _ ≤ 2 * Nat.card ↥(E' ⊓ Θ.ker) := h1
      _ ≤ 2 * 2 ^ 3 := by rw [← h6]; exact Nat.mul_le_mul_left _ h5
      _ ≤ 2 ^ 6 := by norm_num

theorem autRankLe_g24
    (hR : RankG24Fact) (hF : RankG24FrobCentFact) {X : Type} [Group X] (hX : IsG2 2 2 X) :
    AutRankLe X 6 := by
  obtain ⟨-, hm⟩ := hX
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  exact AutRankLe.of_mulEquiv e (autRankLe_adjG2_four hR hF (by rw [hK]; norm_num))

end CFSG.Quasithin.H13.Ch9.KGFF
