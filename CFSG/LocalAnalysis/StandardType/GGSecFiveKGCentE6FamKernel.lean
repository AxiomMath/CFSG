module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.Steinberg.Isogeny.E6
import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
import CFSG.RankThree.PartOne.KE.CTTorusFixed
import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.ClassicalInvolution.Balance.PassTwoFinal
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

theorem exists_ne_one_le_centralizer_of_routeCfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) :
    ∃ e ∈ D, e ≠ 1 ∧ X ≤ Subgroup.centralizer ({e} : Set G) := by
  rcases hX with rfl | hK
  · exact ⟨x, hcfg.1.1.2.2.1.2.2.2.1, hcfg.1.1.1.2.2.2.2.2.2.1.2.2.1,
      hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1⟩
  · obtain ⟨y, hnbr⟩ := hcfg.2.2.2.1.2 X hK
    refine ⟨y, ?_, hnbr.1.2.2.1, hnbr.1.2.2.2.1⟩
    rw [hnbr.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ggInduces_one_of_le_centralizer {L C G : Type*} [Group L] [Group C] [Group G]
    {π : L →* C} {ψ : L →* G} (hkπ : ψ.ker ≤ π.ker) {e : G}
    (he : ψ.range ≤ Subgroup.centralizer ({e} : Set G)) : LayerSixE.GGInduces π ψ e 1 := by
  intro y y' h
  have hc : ψ y * e = e * ψ y := Subgroup.mem_centralizer_singleton_iff.1 (he ⟨y, rfl⟩)
  refine LayerSixE.GGInduces.one hkπ y y' ?_
  rw [h, ← hc, one_mul, inv_one, mul_one, mul_inv_cancel_right]

theorem rootChar_eq_one_of_commute_E6
    {k : Type} [Field k] [Finite k] {G : Type*} [Group G]
    {ψ : ↥(Minuscule.e6Data_valid.minGroup k) →* G} {d : G} {a : Fin Tag.E6.rank → kˣ}
    (ha : LayerSixE.GGInduces (Isogeny.e6Isogeny k) ψ d (rootDiagAutHom .E6 k a))
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hd : Commute d (ψ (Minuscule.e6Data_valid.xm k β 1))) : rootChar a β = 1 := by
  have h1 := ha (Minuscule.e6Data_valid.xm k β 1) (Minuscule.e6Data_valid.xm k β 1)
    (by rw [hd.eq, mul_inv_cancel_right])
  rw [Isogeny.e6Isogeny_xm k hβ, Isogeny.yPar] at h1
  change _ = rootDiagAut .E6 k a _ at h1
  rw [CFSG.ClassicalInvolution.Balance.rootDiagAut_xPar a hβ] at h1
  have h3 := Adjoint.xPar_injective hβ h1
  rw [mul_one] at h3
  have hs : (Isogeny.relSignOr (rootOperatorFamily .E6) Adjoint.e6AdjData_valid β : k) *
      (Isogeny.relSignOr (rootOperatorFamily .E6) Adjoint.e6AdjData_valid β : k) = 1 :=
    Isogeny.relSignOr_mul_self β
  refine Units.val_eq_one.1 (mul_right_cancel₀ (left_ne_zero_of_mul_eq_one hs) ?_)
  rw [one_mul]
  exact h3.symm

theorem exists_famKernel_eq_singleton
    {τ : Tag} {k : Type} [Field k] {L G : Type*} [Group L] [Group G] [Finite G]
    {π : L →* adjointGroup τ k} (hπ : Function.Surjective π) {ψ : L →* G}
    (hkπ : ψ.ker ≤ π.ker) {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hDcard : Nat.card D = p ^ 2)
    (hDN : D ≤ Subgroup.normalizer (ψ.range : Set G))
    (hDa : ∀ d ∈ D, ∃ a, LayerSixE.GGInduces π ψ d (rootDiagAutHom τ k a)) {e : G} (heD : e ∈ D)
    (he : e ≠ 1) (hep : e ^ p = 1) (he1 : LayerSixE.GGInduces π ψ e 1)
    {F : Set (Fin τ.rank → kˣ)}
    (hFD : F = {a | ∃ d ∈ D, LayerSixE.GGInduces π ψ d (rootDiagAutHom τ k a)}) :
    ∃ z ∈ F, famKernel F = famKernel {z} := by
  subst hFD
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf e = p := orderOf_eq_prime hep he
  obtain ⟨d₁, hd₁D, hd₁⟩ : ∃ d₁ ∈ D, d₁ ∉ Subgroup.zpowers e := by
    by_contra! h
    have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers e from h)
    rw [hDcard, Nat.card_zpowers, hord, pow_two] at hle
    nlinarith [hp.two_le]
  obtain ⟨z, hz⟩ := hDa d₁ hd₁D
  let H : Subgroup G :=
    { carrier := {d | d ∈ D ∧ ∃ a, LayerSixE.GGInduces π ψ d (rootDiagAutHom τ k a) ∧
        ∀ β ∈ famKernel ({z} : Set (Fin τ.rank → kˣ)), rootChar a β = 1}
      one_mem' := ⟨D.one_mem, 1, by rw [map_one]; exact LayerSixE.GGInduces.one hkπ,
        fun β _ => CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one β⟩
      mul_mem' := by
        rintro c d ⟨hc, a, ha, hχa⟩ ⟨hd, b, hb, hχb⟩
        refine ⟨D.mul_mem hc hd, a * b, ?_, fun β hβ => ?_⟩
        · rw [map_mul]
          exact ha.mul (hDN hd) hb
        · rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul, hχa β hβ, hχb β hβ, one_mul]
      inv_mem' := by
        rintro c ⟨hc, a, ha, hχa⟩
        refine ⟨D.inv_mem hc, a⁻¹, ?_, fun β hβ => ?_⟩
        · rw [map_inv]
          exact ha.inv
        · rw [rootChar_inv_apply, hχa β hβ, inv_one] }
  have heH : e ∈ H := ⟨heD, 1, by rw [map_one]; exact he1,
    fun β _ => CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one β⟩
  have hd₁H : d₁ ∈ H := ⟨hd₁D, z, hz, fun β hβ => hβ.2 z (Set.mem_singleton z)⟩
  have hHD : H ≤ D := fun d hd => hd.1
  have hlt : Nat.card (Subgroup.zpowers e) < Nat.card H :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne (Subgroup.zpowers_le.2 heH) fun h => hd₁ (by
      rw [h]
      exact hd₁H))
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow hp).1 (hDcard ▸ Subgroup.card_dvd_of_le hHD)
  rw [Nat.card_zpowers, hord, hm'] at hlt
  have hm2 : 2 ≤ m := by
    by_contra h
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · rw [pow_zero] at hlt
      exact absurd hlt (by have := hp.two_le; omega)
    · rw [pow_one] at hlt
      exact lt_irrefl p hlt
  have hHeq : H = D := by
    refine Subgroup.eq_of_le_of_card_ge hHD ?_
    rw [hDcard, hm']
    exact Nat.pow_le_pow_right hp.pos hm2
  refine ⟨z, ⟨d₁, hd₁D, hz⟩, Set.Subset.antisymm (fun β hβ => ⟨hβ.1, fun a ha => ?_⟩)
    fun β hβ => ⟨hβ.1, ?_⟩⟩
  · rw [Set.mem_singleton_iff.1 ha]
    exact hβ.2 z ⟨d₁, hd₁D, hz⟩
  · rintro a ⟨d, hd, had⟩
    obtain ⟨-, a', ha', hχ⟩ := hHeq.ge hd
    rw [rootDiagAutHom_injective (had.unique hπ (hDN hd) ha')]
    exact hχ β hβ

end KGCentE6

end CFSG.StandardType

end
