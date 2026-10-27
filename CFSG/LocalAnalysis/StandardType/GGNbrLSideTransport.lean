module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideDefs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.Assembly.Subnormal
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.StandardType

open Subgroup CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup map_fixSubgroup_le
  normal_map_fixSubgroup)

theorem ggNbrLSide_centralQuot_equiv {H H' : Type} [Group H] [Group H'] (ψ : H →* H')
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center H) (hH : commutator H = ⊤) :
    ∃ e : H ⧸ Subgroup.center H ≃* H' ⧸ Subgroup.center H',
      ∀ h : H, e (QuotientGroup.mk h) = QuotientGroup.mk (ψ h) := by
  let χ : H →* H' ⧸ Subgroup.center H' := (QuotientGroup.mk' (Subgroup.center H')).comp ψ
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hψ
  have hker' : χ.ker = Subgroup.center H := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.comap_center_of_surjective hH ψ hψ hker]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff (ψ x)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hχ), fun h => rfl⟩

private theorem ggNbrLSide_comap_inf_centralizer_eq_fixSubgroup {G : Type} [Group G]
    (L : Subgroup G) (g : G) (hg : g ∈ normalizer (L : Set G)) :
    (L ⊓ centralizer ({g} : Set G)).comap L.subtype =
      fixSubgroup (L.normalizerMonoidHom ⟨g, hg⟩) := by
  ext l
  rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_fixSubgroup,
    Subtype.ext_iff, normalizerMonoidHom_coe, Subgroup.coe_subtype, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.2.symm, fun h => ⟨l.2, h.symm⟩⟩

theorem ggNbrLSide_comp_transport {G : Type} [Group G] [Finite G] {L K : Subgroup G} {g : G}
    (hL : CFSG.Assembly.IsQuasisimple L) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hg : g ∈ normalizer (L : Set G))
    (hK : CFSG.Assembly.IsComponentOf K (L ⊓ centralizer ({g} : Set G))) :
    ∃ (K' : Subgroup R) (ψK : ↥K →* ↥K') (e : ↥K ⧸ Subgroup.center ↥K ≃*
        ↥K' ⧸ Subgroup.center ↥K'),
      CFSG.Open.IsComponentOf K' (fixSubgroup (ggLAut L θ ⟨g, hg⟩)) ∧
        Function.Surjective ψK ∧
        (∀ k : ↥K, (ψK k : R) = ggQuotHom θ ⟨k, (hK.1.trans inf_le_left) k.2⟩) ∧
        ∀ k : ↥K, e (QuotientGroup.mk k) = QuotientGroup.mk (ψK k) := by
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨g, hg⟩
  let φ : MulAut R := ggLAut L θ ⟨g, hg⟩
  let π : ↥L →* R := ggQuotHom θ
  have hπ : Function.Surjective π := ggQuotHom_surjective θ
  have hker : π.ker ≤ Subgroup.center ↥L := (ker_ggQuotHom θ).le
  have hαφ : ∀ l, π (α l) = φ (π l) := fun l => by
    simp only [π, φ, α, ggQuotHom_apply]
    exact (ggLAut_apply L θ ⟨g, hg⟩ l).symm
  have hKL : K ≤ L := hK.1.trans inf_le_left
  have hsub₀ : IsSubnormal (K.subgroupOf L) (fixSubgroup α) := by
    have h := hK.2.1.comap L.subtype
    rw [ggNbrLSide_comap_inf_centralizer_eq_fixSubgroup L g hg] at h
    exact h
  let K' : Subgroup R := (K.subgroupOf L).map π
  have hsub : IsSubnormal K' (fixSubgroup φ) :=
    (hsub₀.map π).trans (.step (map_fixSubgroup_le π hker α φ hαφ)
      (normal_map_fixSubgroup π hker α φ hαφ hπ) (.refl _))
  let e₀ : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  let ψ : ↥K →* ↥K' := (π.subgroupMap (K.subgroupOf L)).comp e₀.symm.toMonoidHom
  have hψ : Function.Surjective ψ := (π.subgroupMap_surjective _).comp e₀.symm.surjective
  have hψker : ψ.ker ≤ Subgroup.center ↥K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g'
    have h1 : π ⟨k, hKL k.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
    have hz := Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 h1)) ⟨g', hKL g'.2⟩
    have hz' : (g' : G) * k = (k : G) * g' := congrArg Subtype.val hz
    exact Subtype.ext hz'
  haveI : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  obtain ⟨e, he⟩ := ggNbrLSide_centralQuot_equiv ψ hψ hψker hK.2.2.1
  exact ⟨K', ψ, e, ⟨hsub.le, isSubnormal_iff_open.1 hsub,
    (Group.IsPerfect.ofSurjective hψ).commutator_eq_top, e.symm.isSimpleGroup⟩, hψ,
    fun k => rfl, he⟩

theorem ggNbrLSide_induces_transport {G : Type} [Group G] {L K : Subgroup G} {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hKL : K ≤ L) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G))
    {K' : Subgroup R} (ψK : ↥K →* ↥K') (hψK : Function.Surjective ψK)
    (hψK' : ∀ k : ↥K, (ψK k : R) = ggQuotHom θ ⟨k, hKL k.2⟩)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* ↥K' ⧸ Subgroup.center ↥K')
    (he : ∀ k : ↥K, e (QuotientGroup.mk k) = QuotientGroup.mk (ψK k)) :
    GGNbrLSideInduces (ggLAut L θ ⟨b, hbL⟩) K' (MulAut.congr e (ggJQAut K b hbK)) := by
  intro j'
  obtain ⟨j, rfl⟩ := hψK j'
  let j₂ : ↥K := K.normalizerMonoidHom ⟨b, hbK⟩ j
  refine ⟨ψK j₂, ?_, ?_⟩
  · rw [hψK' j₂, hψK' j]
    have h := ggLAut_apply L θ ⟨b, hbL⟩ ⟨j, hKL j.2⟩
    simp only [ggQuotHom_apply]
    rw [h]
    rfl
  · have h1 : e.symm (QuotientGroup.mk (ψK j)) = QuotientGroup.mk j := by
      rw [← he j, MulEquiv.symm_apply_apply]
    have h2 : ggJQAut K b hbK (QuotientGroup.mk j) = QuotientGroup.mk j₂ := rfl
    show e (ggJQAut K b hbK (e.symm (QuotientGroup.mk (ψK j)))) = QuotientGroup.mk (ψK j₂)
    rw [h1, h2, he j₂]

theorem ggInnDiagPSL3_of_congr {Q : ℕ} {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {α : MulAut X} (h : GGInnDiagPSL3 Q X' (MulAut.congr e α)) : GGInnDiagPSL3 Q X α := by
  obtain ⟨K, _, _, e', hK, hmem⟩ := h
  refine ⟨K, inferInstance, inferInstance, e.trans e', hK, ?_⟩
  have h2 : MulAut.congr (e.trans e') α = MulAut.congr e' (MulAut.congr e α) := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2]

end CFSG.StandardType

end
