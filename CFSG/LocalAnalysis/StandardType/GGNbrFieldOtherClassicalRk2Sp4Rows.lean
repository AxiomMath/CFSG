module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Rows
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2Sp4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedProj StatedSp)

namespace FieldFixSp4

variable {m : ℕ} {K : Type} [Field K]

theorem exists_fixGeom_of_two_le [Finite K] [CharP K 2] [NeZero m] (hm : 2 ≤ m) {n p : ℕ}
    (hm2 : m = 2 → 2 ≤ n / p) (hn : 1 ≤ n)
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
    rw [← orderOf_injective (fieldAut m K) FieldFixSp.fieldAut_injective σ]
    exact hord
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two hn hK hσ
  have hne : ¬ (m = 2 ∧ Nat.card (descentField σ) = 2) := by
    rintro ⟨h2, hc⟩
    have h4 : 4 ≤ 2 ^ (n / p) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n / p) := Nat.pow_le_pow_right (by norm_num) (hm2 h2)
    rw [hcard] at hc
    omega
  obtain ⟨hS₀, hP₀⟩ := simple_perfect_statedProj (r := m) (k := descentField σ) hm hne
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
    have h1 : y⁻¹ * fieldAut m K σ y = 1 := FieldFixSp.eq_one_of_forall_comm hna hc
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
    have h1 := FieldFixSp.eq_one_of_forall_comm hna₀ hc
    have h2 : (⟨y, hy⟩ : ggFixDer (fieldAut m K σ)) = 1 :=
      θ₀.injective (by rw [h1, map_one])
    rw [show y = 1 from congrArg Subtype.val h2, map_one]

end FieldFixSp4

@[expose] def GGFieldOtherSp4RowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1) ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2

@[expose] def GGFieldOtherSp4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ 2 ≤ lab.n / p ∧ GGFieldOtherSp4RowLabel p lab ∧
    GGFieldOtherSp4RowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

theorem ggFieldOtherSp4RowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherSp4RowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, hBC, -⟩ := h
  refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rcases hBC with h'' | h'' <;> rw [h''] at h' <;> cases h'

theorem largeEvenInLambda2_subfieldSp4 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherSp4Label p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨-, h2, ⟨-, hBC, hl⟩, -⟩ := h
  refine ⟨show 1 ≤ lab.n / p by omega, ?_⟩
  dsimp only
  rcases hBC with h | h <;> rw [h] <;> exact ⟨by omega, fun _ => h2⟩

theorem ggFieldFixKnown_sp4 : GGFieldFixKnown GGFieldOtherSp4Label := by
  intro p lab hp hp2 hlab hS
  obtain ⟨-, h2, ⟨-, hBC, hl⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hBC hl hn h2
  subst hl
  rcases hBC with ht | ht <;> subst ht <;>
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    haveI : CharP K 2 := charP_two_of_card hK
    intro hS hna f hf hord
    exact FieldFixSp4.exists_fixGeom_of_two_le le_rfl (fun _ => h2) hn hp hp2 hK hS hna hf hord

section Sp4


theorem ggFieldKLevel_sp4 (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherSp4Label p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRowTwo (Rw := GGFieldOtherSp4RowLabel)
    (fun _ _ ⟨hd, _, hr, hr₀⟩ => ⟨hd, hr, hr₀⟩) (fun _ _ _ h => largeEvenInLambda2_subfieldSp4 h)
    (fun _ _ h => ggFieldOtherSp4RowLabel_not h) ggFieldFixKnown_sp4
    (fun _ _ hp hp2 hlab ⟨hpq, hBC, hl⟩ =>
      largeEvenLabelAll_rowPlainTwo_sp4 hp hp2 hlab ⟨hBC, hl, hpq⟩) hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_sp4 (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherSp4Label p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_sp4 hpc hconj hcen hinn) hT

end Sp4

end CFSG.StandardType

end
