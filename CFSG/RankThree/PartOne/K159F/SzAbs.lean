module

public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartOne.K159.AutSzAbs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Certificates.Certificate113
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG.RankThree.PartOne.K159.SzAbs CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.Census3 (IsoLie)

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem isSylowOf_map' {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : CFSG.ABGLocalTools.IsSylowOf p P K) (f : X →* Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isElemAb_of_le' {p : ℕ} {G : Type*} [Group G] {A K : Subgroup G}
    (hA : IsElementaryAbelian p ↥A) (hKA : K ≤ A) : IsElementaryAbelian p ↥K :=
  CFSG.IsElementaryAbelian.of_le hA hKA

section Inner

variable {Q : Type} [Group Q]

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem conj_injective_of_center_eq_bot (hc : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut Q => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc h * g = (g * h * g⁻¹) * g := by rw [this]
      _ = g * h := by group
  rw [hc] at this
  exact Subgroup.mem_bot.1 this

theorem centralizer_inner_eq_bot (hc : Subgroup.center Q = ⊥) :
    Subgroup.centralizer (Inn Q : Set (MulAut Q)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro g
  rw [MulAut.one_apply]
  have h1 : MulAut.conj g * φ = φ * MulAut.conj g :=
    (Subgroup.mem_centralizer_iff.1 hφ (MulAut.conj g) ⟨g, rfl⟩)
  have h4 : MulAut.conj (φ g) = φ * MulAut.conj g * φ⁻¹ := by
    apply MulEquiv.ext
    intro m
    simp [MulAut.conj_apply, map_mul, map_inv]
  have h2 : MulAut.conj (φ g) = MulAut.conj g := by
    rw [h4, ← h1, mul_inv_cancel_right]
  exact conj_injective_of_center_eq_bot hc h2

end Inner

section Main

open CFSG.RankThree.PartOne (IsSylowOf)

theorem sz_inner_of_commute
    {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q] (hnab : ∃ a b : Q, a * b ≠ b * a)
    (hiso : IsoLie Q (.suzuki 2)) {M : Type} [Group M] [Finite M] (ρ : M →* MulAut Q)
    {X₁ P₁ E₁ K₁ : Subgroup M} (hX : X₁.map ρ = Inn Q) (hXK : X₁ ≤ K₁)
    (hK : K₁ ≤ Subgroup.normalizer (X₁ : Set M))
    (hP : IsSylowOf 5 P₁ K₁) (hEP : E₁ ≤ P₁)
    (hcomm : ∀ y ∈ P₁ ⊓ X₁, ∀ e ∈ E₁, ρ y * ρ e = ρ e * ρ y) :
    E₁.map ρ ≤ Inn Q := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Subgroup.center Q = ⊥ := center_eq_bot_of_simple hnab
  have hconj := conj_injective_of_center_eq_bot hc
  let eS : Q ≃* ↥(Inn Q) := MonoidHom.ofInjective hconj
  have hSz : SzSylow ↥(Inn Q) := SzSylow.of_mulEquiv eS.symm (szSylow_of_isoLie hiso)
  have hsimple : IsSimpleGroup ↥(Inn Q) := MulEquiv.isSimpleGroup eS.symm
  have hC := centralizer_inner_eq_bot hc
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  by_contra hE
  obtain ⟨ê, hêE, hêS⟩ := Set.not_subset.1 hE
  set T : Subgroup (MulAut Q) := (P₁ ⊓ X₁).map ρ with hT
  set Ph : Subgroup (MulAut Q) := P₁.map ρ with hPh
  set Eh : Subgroup (MulAut Q) := E₁.map ρ with hEh
  have hP' : CFSG.ABGLocalTools.IsSylowOf 5 P₁ K₁ := CFSG.ABGLocalTools.isSylowOf_iff.2 hP
  have hTsyl₁ : CFSG.ABGLocalTools.IsSylowOf 5 (P₁ ⊓ X₁) X₁ :=
    hP'.inf_of_le_normalizer hXK hK
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 5 T (Inn Q) := by
    have := isSylowOf_map' hTsyl₁ ρ
    rwa [hX] at this
  have hTS : T ≤ Inn Q := hTsyl.le
  have hTcard : Nat.card T = 25 := by
    rw [hTsyl.card_eq, hSz.card, factorization_five]
    norm_num
  obtain ⟨Qs, hQs⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hcycQ : IsCyclic ↥(T.subgroupOf (Inn Q)) := by
    have h1 : IsCyclic ↥(Qs : Subgroup ↥(Inn Q)) := hSz.cyclic Qs
    rwa [hQs] at h1
  have hcycT : IsCyclic ↥T := (Subgroup.subgroupOfEquivOfLe hTS).isCyclic.1 hcycQ
  have hPhp : IsPGroup 5 Ph := hP.2.1.map ρ
  have hTPh : T ≤ Ph := Subgroup.map_mono inf_le_left
  have hEhPh : Eh ≤ Ph := Subgroup.map_mono hEP
  set P'' : Subgroup (MulAut Q) := T ⊔ Eh with hP''
  have hP''Ph : P'' ≤ Ph := sup_le hTPh hEhPh
  have hP''p : IsPGroup 5 P'' := hPhp.to_le hP''Ph
  have hTP'' : T ≤ P'' := le_sup_left
  have hêP'' : ê ∈ P'' := Subgroup.mem_sup_right hêE
  have hêT : ê ∉ T := fun h => hêS (hTS h)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP''p
  have hgt : 25 < Nat.card P'' := by
    by_contra hle
    push Not at hle
    have : T = P'' := Subgroup.eq_of_le_of_card_ge hTP'' (by rw [hTcard]; exact hle)
    exact hêT (this ▸ hêP'')
  have h125 : 125 ∣ Nat.card P'' := by
    rw [hn] at hgt ⊢
    have h3 : 3 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> omega
    have := pow_dvd_pow 5 h3
    simpa using this
  have hTcomm : ∀ t ∈ T, ∀ e ∈ Eh, t * e = e * t := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨e, he, rfl⟩
    exact hcomm y hy e he
  have hcomm' : ∀ x ∈ P'', ∀ t ∈ T, x * t = t * x := by
    have hle : P'' ≤ Subgroup.centralizer (T : Set (MulAut Q)) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have : (⟨t, ht⟩ : ↥T) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨t, ht⟩ := by
          let _ := hcycT.commGroup
          exact mul_comm _ _
        exact congrArg Subtype.val this
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact hTcomm t ht x hx
    intro x hx t ht
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) t ht).symm
  exact sz_core hSz hsimple hC hTS hTcard hP''p hTP'' h125 hcomm'

end Main

section Order

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem card_outer_dvd_five
    (hiso : IsoLie Q (.suzuki 2)) : Nat.card (Outer Q) ∣ 5 := by
  have h := CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} Q 2 5
    (CTP.suzukiModel_of_isoLie 2 hiso)
  exact h.1.2.1

omit [Finite Q] in
theorem card_le_five_of_elemAb_inner
    [IsSimpleGroup Q] (hnab : ∃ a b : Q, a * b ≠ b * a) (hiso : IsoLie Q (.suzuki 2))
    {R : Subgroup (MulAut Q)} (hR : R ≤ Inn Q) (hRab : IsElementaryAbelian 5 ↥R) :
    Nat.card R ≤ 5 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Subgroup.center Q = ⊥ := center_eq_bot_of_simple hnab
  have hconj := conj_injective_of_center_eq_bot hc
  let eS : Q ≃* ↥(Inn Q) := MonoidHom.ofInjective hconj
  have hSz : SzSylow ↥(Inn Q) := SzSylow.of_mulEquiv eS.symm (szSylow_of_isoLie hiso)
  have hRp : IsPGroup 5 (R.subgroupOf (Inn Q)) := (hRab.isPGroup 5 ↥R).comap_subtype
  obtain ⟨Qs, hQs⟩ := hRp.exists_le_sylow
  have hcyc : IsCyclic ↥(Qs : Subgroup ↥(Inn Q)) := hSz.cyclic Qs
  have hcycR : IsCyclic ↥(R.subgroupOf (Inn Q)) := Subgroup.isCyclic_of_le hQs
  have hcycR' : IsCyclic ↥R := (Subgroup.subgroupOfEquivOfLe hR).isCyclic.1 hcycR
  have hexp : Monoid.exponent ↥R ∣ 5 := IsElementaryAbelian.exponent_dvd_p 5 _
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

theorem card_map_le_twentyfive
    [IsSimpleGroup Q] (hnab : ∃ a b : Q, a * b ≠ b * a) (hiso : IsoLie Q (.suzuki 2))
    {M : Type} [Group M] (ρ : M →* MulAut Q) {E₁ : Subgroup M} (hE : IsElementaryAbelian 5 ↥E₁) :
    Nat.card (E₁.map ρ) ≤ 25 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfin : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  set Eh : Subgroup (MulAut Q) := E₁.map ρ with hEh
  have hEhab : IsElementaryAbelian 5 ↥Eh := by
    have := hE
    exact CFSG.IsElementaryAbelian.map ρ
  let χ : ↥Eh →* Outer Q := (QuotientGroup.mk' (Inn Q)).comp Eh.subtype
  have hmul := Subgroup.card_ker_mul_card_range χ
  have hrange : Nat.card χ.range ≤ 5 := by
    have h1 : Nat.card χ.range ∣ Nat.card (Outer Q) := Subgroup.card_subgroup_dvd_card _
    exact Nat.le_of_dvd (by norm_num) (h1.trans (card_outer_dvd_five hiso))
  have hker : Nat.card χ.ker ≤ 5 := by
    set K : Subgroup (MulAut Q) := χ.ker.map Eh.subtype with hK
    have hKS : K ≤ Inn Q := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
    have hKab : IsElementaryAbelian 5 ↥K :=
      isElemAb_of_le' hEhab (Subgroup.map_subtype_le _)
    have := card_le_five_of_elemAb_inner hnab hiso hKS hKab
    rwa [hK, Subgroup.card_map_of_injective Eh.subtype_injective] at this
  calc Nat.card Eh = Nat.card χ.ker * Nat.card χ.range := hmul.symm
    _ ≤ 5 * 5 := Nat.mul_le_mul hker hrange
    _ = 25 := by norm_num

end Order

end CFSG.RankThree.PartOne.K159F
