module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelAdj
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section YOdd

theorem ggG5_index_dvd_three_E6
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum (langTag .E6) GGL)
    (hΦ : D.Φ = ggPhi .E6 f) {C : Type} [Group C] (ι : C →* ModGL (langTag .E6) GGL)
    (hpkg : GGLangPkg D ι) : ι.range.relIndex D.fix ∣ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hΦ' : D.Φ = Units.map (entrywiseHom (ggFrobT f)) := hΦ
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card (GaloisField 2 f) := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  letI : Algebra (GaloisField 2 f) GGL := (ggRatEmb f).toAlgebra
  have hcomm : ∀ r : ZMod 2,
      ggRatEmb f (algebraMap (ZMod 2) (GaloisField 2 f) r) = algebraMap (ZMod 2) GGL r :=
    fun r => (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 f) (M := GGL)).commutes r
  haveI : Module.IsTorsionFree (GaloisField 2 f) GGL := {
    isSMulRegular := by
      intro r hr
      have hr0 : r ≠ 0 := hr.ne_zero
      have hfr0 : ggRatEmb f r ≠ 0 :=
        fun h => hr0 ((ggRatEmb f).injective (by rw [h, map_zero]))
      intro x y hxy
      change ggRatEmb f r * x = ggRatEmb f r * y at hxy
      exact mul_left_cancel₀ hfr0 hxy }
  have hcomp : RingHom.comp (algebraMap (GaloisField 2 f) GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)) =
      RingHom.comp (RingHom.id GGL) (algebraMap (ZMod 2) GGL) := by
    ext r
    exact hcomm r
  haveI : IsAlgClosure (GaloisField 2 f) GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.ringHom_of_comp_eq
        (f := algebraMap (ZMod 2) (GaloisField 2 f)) (g := RingHom.id GGL)
        (algebraMap (ZMod 2) (GaloisField 2 f)).injective Function.surjective_id hcomp }
  have hXC : D.fix ≤ adjointGroup .E6 GGL := fun x hx =>
    ((LangDatum.mem_fix (D := D)).1 hx).1
  have hXF : ∀ x ∈ D.fix, Units.map (entrywiseHom (ggFrobT f)) x = x := fun x hx => by
    have h := ((LangDatum.mem_fix (D := D)).1 hx).2
    rwa [hΦ'] at h
  have hidx : ((adjointGroup .E6 (GaloisField 2 f)).map
        (baseChangeGL (ggRatEmb f))).relIndex D.fix ∣ 3 := by
    let X : Subgroup (ModGL Tag.E6 GGL) := D.fix
    haveI : Finite X := hpkg.desc.finite_fix
    exact (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational
      (τ := .E6) (K := GaloisField 2 f) (L := GGL)
      3 (Or.inl ⟨rfl, rfl⟩) (ggFrobT f) hFr X hXC hXF).1
  have hpkg0 := ggLangPkg_adjoint (Or.inr (Or.inl rfl)) hf D hΦ'
  have hrange : ι.range =
      (adjointGroup .E6 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f)) := by
    have h1 : ι.range = ((baseChangeGL (ggRatEmb f)).comp
        (adjointGroup .E6 (GaloisField 2 f)).subtype).range :=
      hpkg.desc.derived.symm.trans hpkg0.desc.derived
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  rwa [← hrange] at hidx

theorem ggG5_involution_mem_range_E6
    {f : ℕ} (hf : 1 ≤ f) (D : LangDatum (langTag .E6) GGL)
    (hΦ : D.Φ = ggPhi .E6 f) {C : Type} [Group C] (ι : C →* ModGL (langTag .E6) GGL)
    (hpkg : GGLangPkg D ι) {y : ModGL (langTag .E6) GGL} (hy : y ∈ D.fix) (hy2 : y * y = 1) :
    y ∈ ι.range := by
  have hidx : ι.range.relIndex D.fix ∣ 3 := ggG5_index_dvd_three_E6 hf D hΦ (ι := ι) hpkg
  let N : Subgroup (ModGL (langTag .E6) GGL) := ι.range
  have hN : N = ⁅D.fix, D.fix⁆ := hpkg.desc.derived.symm
  have hNnorm : (N.subgroupOf D.fix).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hcomm : ⁅(g : ModGL (langTag .E6) GGL), (n : ModGL (langTag .E6) GGL)⁆ ∈ N := by
      rw [hN]
      exact Subgroup.commutator_mem_commutator g.2 n.2
    have hmul : (g : ModGL (langTag .E6) GGL) * (n : ModGL (langTag .E6) GGL) *
        (g : ModGL (langTag .E6) GGL)⁻¹ =
        ⁅(g : ModGL (langTag .E6) GGL), (n : ModGL (langTag .E6) GGL)⁆ *
          (n : ModGL (langTag .E6) GGL) := by
      rw [commutatorElement_def]
      group
    change (g : ModGL (langTag .E6) GGL) * (n : ModGL (langTag .E6) GGL) *
      (g : ModGL (langTag .E6) GGL)⁻¹ ∈ N
    rw [hmul]
    exact N.mul_mem hcomm hn
  letI : (N.subgroupOf D.fix).Normal := hNnorm
  let q : D.fix ⧸ N.subgroupOf D.fix := QuotientGroup.mk ⟨y, hy⟩
  have hsq : (⟨y, hy⟩ : D.fix) * ⟨y, hy⟩ = 1 := by
    apply Subtype.ext
    simpa using hy2
  have hmulq : q * q = QuotientGroup.mk ((⟨y, hy⟩ : D.fix) * ⟨y, hy⟩) := by
    simpa [q] using (QuotientGroup.mk_mul (N.subgroupOf D.fix)
      (⟨y, hy⟩ : D.fix) ⟨y, hy⟩).symm
  have hq2 : q * q = 1 := by
    rw [hmulq, hsq]
    rfl
  have hord2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hq2)
  have hcard : Nat.card (D.fix ⧸ N.subgroupOf D.fix) = N.relIndex D.fix := by
    rw [← Subgroup.index_eq_card]
    rfl
  have hord3 : orderOf q ∣ 3 := (orderOf_dvd_natCard q).trans (hcard ▸ hidx)
  have hord1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord2 with h | h
    · exact h
    · rw [h] at hord3
      omega
  have hq1 : q = 1 := orderOf_eq_one_iff.mp hord1
  have hm : (⟨y, hy⟩ : D.fix) ∈ N.subgroupOf D.fix := by
    rw [← QuotientGroup.eq_one_iff]
    exact hq1
  exact (Subgroup.mem_subgroupOf).1 hm

end YOdd

end CFSG.StandardType.GGFinModel.G5
