module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedProj StatedSp)

namespace FieldFixSp

theorem eq_one_of_forall_comm {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {x : G} (h : ∀ g : G, g * x = x * g) : x = 1 := by
  have hx : x ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop
  · rwa [hbot, Subgroup.mem_bot] at hx
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center G := htop ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

variable {m : ℕ} {K : Type} [Field K]

theorem fieldAut_injective [CharP K 2] [NeZero m] : Function.Injective (fieldAut m K) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  ext t
  set ρ : TauCeti.GLSymplecticFin.RootSubgroupIndex m := .positiveLong 0
  have h := congrArg (fun α : MulAut (StatedProj (StatedSp m K)) => α (proj m K (elt ρ t))) hσ
  simp only [fieldAut_proj, AutPSp.fieldSp_elt, MulAut.one_apply] at h
  exact elt_injective ρ (AutPSp.proj_injective h)

theorem exists_fixGeom [Finite K] [CharP K 2] [NeZero m] (hm : 3 ≤ m) {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ n)
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K m)))
    (hna : ∃ a b : LargeEvenProj (LargeEvenSpGroup K m), a * b ≠ b * a)
    {f : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m)))
    (hord : orderOf f = p) :
    LargeEvenRecipeSymplectic m (2 ^ (n / p)) false fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
          (LargeEvenGSpSet K m)) f I₀ θ₀ := by
  obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (fieldAut m K) fieldAut_injective σ]
    exact hord
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two hn hK hσ
  obtain ⟨hS₀, hP₀⟩ := simple_perfect_statedProj (r := m) (k := descentField σ) (by omega)
    (by omega)
  haveI := hS
  haveI := hS₀
  haveI := hP₀
  have hι : Function.Injective (subfieldInj (r := m) σ) := subfieldInj_injective σ
  have hrange : (subfieldInj (r := m) σ).range = ggFixSub (fieldAut m K σ) := by
    rw [range_subfieldInj, ← spFixedGroup_fieldAut_eq_range hodd hσp]
    exact Subgroup.ext fun x => Iff.rfl
  have hder : ggFixDer (fieldAut m K σ) = (subfieldInj (r := m) σ).range := by
    haveI : Group.IsPerfect (subfieldInj (r := m) σ).range :=
      Group.IsPerfect.range (subfieldInj (r := m) σ)
    calc ggFixDer (fieldAut m K σ)
        = ⁅(subfieldInj (r := m) σ).range, (subfieldInj (r := m) σ).range⁆ := by
          rw [ggFixDer, hrange]
      _ = (subfieldInj (r := m) σ).range := Subgroup.commutator_eq_self
  let θ₀ : ggFixDer (fieldAut m K σ) ≃* StatedProj (StatedSp m (descentField σ)) :=
    (MulEquiv.subgroupCongr hder).trans (MonoidHom.ofInjective hι).symm
  have hna₀ : ∃ a b : StatedProj (StatedSp m (descentField σ)), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative (StatedProj (StatedSp m (descentField σ))) :=
      isMulCommutative_iff.mpr hcon
    exact Group.IsPerfect.not_isMulCommutative (StatedProj (StatedSp m (descentField σ))) ‹_›
  have key : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m), φ * fieldAut m K σ = fieldAut m K σ * φ →
        ∃ y ∈ ggFixDer (fieldAut m K σ), φ = MulAut.conj y := by
    intro φ hφI hφ
    obtain ⟨y, rfl⟩ := RecipeFieldSp.mem_conjImage_iff_inn.mp hφI
    refine ⟨y, ?_, rfl⟩
    have hc : ∀ u : StatedProj (StatedSp m K),
        u * (y⁻¹ * fieldAut m K σ y) = (y⁻¹ * fieldAut m K σ y) * u := by
      intro u
      obtain ⟨z, rfl⟩ := MulEquiv.surjective (fieldAut m K σ) u
      have e := congrArg (fun α : MulAut (StatedProj (StatedSp m K)) => α z) hφ
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at e
      calc fieldAut m K σ z * (y⁻¹ * fieldAut m K σ y)
          = y⁻¹ * (y * fieldAut m K σ z * y⁻¹) * fieldAut m K σ y := by group
        _ = y⁻¹ * (fieldAut m K σ y * fieldAut m K σ z * (fieldAut m K σ y)⁻¹) *
              fieldAut m K σ y := by rw [e]
        _ = (y⁻¹ * fieldAut m K σ y) * fieldAut m K σ z := by group
    have h1 : y⁻¹ * fieldAut m K σ y = 1 := eq_one_of_forall_comm hna hc
    have hy : fieldAut m K σ y = y := by
      have := congrArg (y * ·) h1
      simpa using this
    rw [hder, hrange]
    exact hy
  refine ⟨descentField σ, inferInstance, inferInstance, hcard, hS₀, hna₀, θ₀, ?_, ?_⟩
  · intro φ hφI hφ
    obtain ⟨y, hy, rfl⟩ := key φ hφI hφ
    refine ⟨MulAut.conj (θ₀ ⟨y, hy⟩), RecipeFieldSp.mem_conjImage_iff_inn.mpr ⟨_, rfl⟩,
      fun g hg => ?_⟩
    have h1 : (⟨MulAut.conj y g, ggFixDer_map_mem hφ hg⟩ : ggFixDer (fieldAut m K σ)) =
        ⟨y, hy⟩ * ⟨g, hg⟩ * ⟨y, hy⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  · intro φ hφI hφ hg
    obtain ⟨y, hy, rfl⟩ := key φ hφI hφ
    have hc : ∀ r₀ : StatedProj (StatedSp m (descentField σ)),
        r₀ * θ₀ ⟨y, hy⟩ = θ₀ ⟨y, hy⟩ * r₀ := by
      intro r₀
      obtain ⟨⟨g, hg'⟩, rfl⟩ := MulEquiv.surjective θ₀ r₀
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show g * y = y * g
      have e := hg g hg'
      simp only [MulAut.conj_apply] at e
      calc g * y = (y * g * y⁻¹) * y := by rw [e]
        _ = y * g := by group
    have h1 := eq_one_of_forall_comm hna₀ hc
    have h2 : (⟨y, hy⟩ : ggFixDer (fieldAut m K σ)) = 1 :=
      θ₀.injective (by rw [h1, map_one])
    rw [show y = 1 from congrArg Subtype.val h2, map_one]

end FieldFixSp

open FieldFixSp in
theorem ggFieldFixKnown_sp : GGFieldFixKnown GGFieldFixSpLabel := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨-, -, hrow⟩, hBC⟩ := hS
  have h3 : 3 ≤ lab.rank := by
    rcases hBC with hB | hB <;>
    rcases hrow with (h | h | h) | ⟨-, h3⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      first | exact h3 | (rw [hB] at h; cases h)
  have hn : 1 ≤ lab.n := hlab.1
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hBC h3 hn
  haveI : NeZero l := ⟨by omega⟩
  rcases hBC with ht | ht <;> subst ht <;>
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    haveI : CharP K 2 := charP_two_of_card hK
    intro hS hna f hf hord
    exact exists_fixGeom h3 hn hp hp2 hK hS hna hf hord

end CFSG.StandardType

end
