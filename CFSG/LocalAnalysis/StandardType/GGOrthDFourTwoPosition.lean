module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3Sp
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGResOrthogonalExactTwo
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCharSum
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.Assembly
open CFSG.RankThree.Classical2
open Module

theorem eq_bot_of_full_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {G₁ : Type*} [Group G₁] [Finite G₁] (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (hrefl : B.IsRefl) (heven : Even (finrank F V)) (ρ : G₁ →* Module.End F V)
    (hρinj : Function.Injective ρ) (hρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    {E T : Subgroup G₁} (hcomm : ∀ a b : ↥E, a * b = b * a) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hT : IsPGroup 2 ↥T) (hN : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T)
    (hcard : 3 ^ (finrank F V / 2) ≤ Nat.card E) : T = ⊥ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hF])
  let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have hφ : Function.Bijective φ := by
    refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨φ.injective, ?_⟩
    rw [ZMod.card, Fintype.card_eq_nat_card, hF]
  let e : ZMod 2 ≃+* F := RingEquiv.ofBijective φ hφ
  have he : ∀ c, e.symm (φ c) = c := fun c => e.symm_apply_apply c
  letI : Module (ZMod 2) V := Module.compHom V φ
  haveI : Finite V := Module.finite_of_finite F
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hfin : finrank (ZMod 2) V = finrank F V := by
    haveI : Fintype V := Fintype.ofFinite V
    have h1 : 2 ^ finrank (ZMod 2) V = Nat.card V := FiniteField.pow_finrank_eq_natCard 2 V
    have h2 : Fintype.card V = Fintype.card F ^ finrank F V := Module.card_eq_pow_finrank
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF] at h2
    exact Nat.pow_right_injective le_rfl (h1.trans h2)
  let B' : LinearMap.BilinForm (ZMod 2) V :=
    LinearMap.mk₂ (ZMod 2) (fun x y => e.symm (B x y))
      (fun x x' y => by simp only [map_add, LinearMap.add_apply])
      (fun c x y => by
        change e.symm (B (φ c • x) y) = c * e.symm (B x y)
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, he])
      (fun x y y' => by simp only [map_add])
      (fun c x y => by
        change e.symm (B x (φ c • y)) = c * e.symm (B x y)
        rw [map_smul, smul_eq_mul, map_mul, he])
  have hB'0 : ∀ x y, B' x y = 0 ↔ B x y = 0 := fun x y => by
    change e.symm (B x y) = 0 ↔ B x y = 0
    exact map_eq_zero_iff e.symm e.symm.injective
  let ρ' : G₁ →* Module.End (ZMod 2) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := (ρ g).map_add
          map_smul' := fun c v => (ρ g).map_smul (φ c) v }
      map_one' := by
        refine LinearMap.ext fun v => ?_
        change ρ 1 v = v
        rw [map_one, Module.End.one_apply]
      map_mul' := fun g h => by
        refine LinearMap.ext fun v => ?_
        change ρ (g * h) v = ρ g (ρ h v)
        rw [map_mul, Module.End.mul_apply] }
  refine CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3.eq_bot_of_full B' ⟨?_, ?_⟩ ?_ (hfin ▸ heven)
    ρ' ?_ ?_ hcomm hE3 hT hN (hfin ▸ hcard)
  · intro x hx
    exact hB.1 x fun y => (hB'0 x y).mp (hx y)
  · intro y hy
    exact hB.2 y fun x => (hB'0 x y).mp (hy x)
  · intro x y h
    exact (hB'0 y x).mpr (hrefl x y ((hB'0 x y).mp h))
  · intro g h hgh
    apply hρinj
    exact LinearMap.ext fun v => DFunLike.congr_fun hgh v
  · intro g x y
    change e.symm (B (ρ g x) (ρ g y)) = e.symm (B x y)
    rw [hρ]

section

theorem exists_full_quadratic_image_of_D4two_marking {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} (hRig : GGLabelRigidInput) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) 3 Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hact : ∃ b : ↥Bs, ggGamma L hN b ≠ 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module F V) (_ : FiniteDimensional F V) (_ : Nontrivial V)
      (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
      (σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q))
      (ρ : Bs →* (↥L ⧸ Subgroup.center ↥L)),
      Nat.card F = 2 ∧ finrank F V = 2 * 4 ∧
      IsElemAbelian 3 (ρ.range.map σ.toMonoidHom) ∧
      Nat.card (ρ.range.map σ.toMonoidHom) = 3 ^ 4 ∧
      ∀ (b : ↥Bs) (z : ↥L), (QuotientGroup.mk (ggGamma L hN b z) : ↥L ⧸ Subgroup.center ↥L) =
        ρ b * QuotientGroup.mk z * (ρ b)⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmarkK : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hperf : commutator ↥L = ⊤ := hmark.1
  obtain ⟨lab, hΛ, hhas, R, hRgrp, I, F', θ, hPm⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨⟨⟨htagD, -, -, hpd⟩, hn1, hr4⟩, -, -⟩ := hPm
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial, Q, hQ, eQ, ρ,
    hcard, -, hT, hdim, hplus, himage, hcompat0⟩ :=
    OrthKExactTwo.exists_quadratic_image_of_orthogonal_marking hRig hp2 hmarkK hBs hSC
      hΛ hhas (Or.inl htagD) hr4.ge
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  have hcard2 : Nat.card F = 2 := by rw [hcard, hn1, pow_one]
  have hdim8 : Module.finrank F V = 2 * 4 := by rw [hdim, hr4]
  have hpq : 3 ∣ Nat.card F + 1 := by rw [hcard2]
  have hconjq : ∀ (b : ↥Bs) (z : ↥L), (QuotientGroup.mk (ggGamma L hN b z) :
      ↥L ⧸ Subgroup.center ↥L) = ρ b * QuotientGroup.mk z * (ρ b)⁻¹ := by
    intro b z
    apply eQ.injective
    rw [hcompat0 b z, MulAut.conj_apply, map_mul, map_mul, map_inv]
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q) :=
    eQ.trans (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
  let EQ : Subgroup ↥(orthDerived Q) := ρ.range.map σ.toMonoidHom
  let A : Subgroup (V ≃ₗ[F] V) := EQ.map (orthDerived Q).subtype
  have hEimage : IsElemAbelian 3 EQ ∧
      ∀ g ∈ Subgroup.centralizer (EQ : Set ↥(orthDerived Q)), g ^ 3 = 1 → g ∈ EQ := by
    simpa [σ, EQ] using himage
  have hAΩ : A ≤ orthDerived Q := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [Subgroup.coe_pow] using congrArg Subtype.val (hEimage.1.2 x hx)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg Subtype.val (CFSG.Open.IsElemAbelian.comm hEimage.1 hx hy)
  have hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    apply hEimage.2 ⟨g, hg⟩
    · intro e he
      exact Subtype.ext (by
        change (e : V ≃ₗ[F] V) * g = g * (e : V ≃ₗ[F] V)
        exact (hgc (e : V ≃ₗ[F] V) ⟨e, he, rfl⟩).symm)
    · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)
  have hne : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨b, hb⟩ := hact
    refine ⟨((σ (ρ b) : ↥(orthDerived Q)) : V ≃ₗ[F] V), ⟨σ (ρ b), ⟨ρ b, ⟨b, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    intro h1
    apply hb
    have hρb : ρ b = 1 := by
      apply σ.injective
      rw [map_one]
      exact Subtype.ext h1
    have hc : ∀ z : ↥L, z⁻¹ * ggGamma L hN b z ∈ Subgroup.center ↥L := by
      intro z
      have h := hconjq b z
      rw [hρb, one_mul, inv_one, mul_one] at h
      exact QuotientGroup.eq.mp h.symm
    let f : ↥L →* ↥(Subgroup.center ↥L) :=
      { toFun := fun z => ⟨z⁻¹ * ggGamma L hN b z, hc z⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun z w => Subtype.ext (by
          have hw : w⁻¹ * (z⁻¹ * ggGamma L hN b z) = (z⁻¹ * ggGamma L hN b z) * w⁻¹ :=
            Subgroup.mem_center_iff.mp (hc z) w⁻¹
          change (z * w)⁻¹ * ggGamma L hN b (z * w) =
            (z⁻¹ * ggGamma L hN b z) * (w⁻¹ * ggGamma L hN b w)
          rw [map_mul, mul_inv_rev]
          calc w⁻¹ * z⁻¹ * (ggGamma L hN b z * ggGamma L hN b w)
              = (w⁻¹ * (z⁻¹ * ggGamma L hN b z)) * ggGamma L hN b w := by group
            _ = ((z⁻¹ * ggGamma L hN b z) * w⁻¹) * ggGamma L hN b w := by rw [hw]
            _ = (z⁻¹ * ggGamma L hN b z) * (w⁻¹ * ggGamma L hN b w) := by group) }
    refine MulEquiv.ext fun z => ?_
    have hzc : z ∈ commutator ↥L := by
      rw [hperf]
      exact Subgroup.mem_top z
    have hz : f z = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker f hzc)
    have h2 : z⁻¹ * ggGamma L hN b z = 1 := congrArg Subtype.val hz
    rw [MulAut.one_apply]
    calc ggGamma L hN b z = z * (z⁻¹ * ggGamma L hN b z) := by group
      _ = z := by rw [h2, mul_one]
  obtain ⟨r, τ, hτ, hτr, -, -, -, -⟩ :=
    exists_torus (K := F) (V := V) hp2 (Or.inr hpq) hQ hT hAΩ hApow hAcomm hmax hne
  have hchar := charSum_top_modEq_one_of_witt hQ (r := 4) (by norm_num) hdim8 hpq
    (Or.inl ⟨hplus.mpr htagD, even_two_mul 2⟩)
  have hr : Module.finrank F V = 2 * r :=
    finrank_eq_two_mul_of_charSum hp2 (Or.inr hpq) hQ hT hAΩ hApow hAcomm hmax hne hτ hτr hchar
  have hcardA : Nat.card A = 3 ^ 4 := by
    rw [← hτr, ← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv,
      Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
    congr 1
    omega
  have hcardE : Nat.card EQ = 3 ^ 4 := by
    rw [← hcardA]
    exact (Subgroup.card_map_of_injective (orthDerived Q).subtype_injective).symm
  exact ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial,
    Q, hQ, σ, ρ, hcard2, hdim8, hEimage.1, hcardE, hconjq⟩

theorem card_range_ggGamma_of_D4two_marking {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} (hRig : GGLabelRigidInput) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) 3 Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hact : ∃ b : ↥Bs, ggGamma L hN b ≠ 1) :
    Nat.card (ggGamma L hN).range = 3 ^ 4 := by
  classical
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial, Q, hQ, σ, ρ,
      -, -, -, hcard, hconj⟩ :=
    exists_full_quadratic_image_of_D4two_marking hRig hBs hSC hmark hN hact
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  letI : AddCommGroup V := hAdd
  letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  have hmarkK : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hZq := center_quotient_eq_bot_of_innerDiagOn hmarkK
  have hker : ρ.ker = (ggGamma L hN).ker := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hb
      have hhom : (ggGamma L hN b : ↥L →* ↥L) = MonoidHom.id ↥L :=
        TypeA.eq_of_inv_mul_mem_center hmark.1 _ _ fun z => by
          change (ggGamma L hN b z)⁻¹ * z ∈ Subgroup.center ↥L
          apply QuotientGroup.eq.mp
          simpa only [hb, one_mul, inv_one, mul_one, MonoidHom.id_apply] using hconj b z
      apply MulEquiv.ext
      intro z
      exact congrArg (fun f : ↥L →* ↥L => f z) hhom
    · intro hb
      have hc : ρ b ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
        have h := hconj b w
        rw [hb, MulAut.one_apply] at h
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (fun t => t * ρ b) h
      rwa [hZq, Subgroup.mem_bot] at hc
  rw [Subgroup.card_map_of_injective σ.injective] at hcard
  have hρcard := Subgroup.card_ker_mul_card_range ρ
  rw [hker, hcard] at hρcard
  have hprod := (Subgroup.card_ker_mul_card_range (ggGamma L hN)).trans hρcard.symm
  rw [Nat.mul_comm (Nat.card (ggGamma L hN).ker) (Nat.card (ggGamma L hN).range),
    Nat.mul_comm (Nat.card (ggGamma L hN).ker) (3 ^ 4)] at hprod
  have hpos : 0 < Nat.card (ggGamma L hN).ker := Nat.card_pos
  exact le_antisymm (Nat.le_of_mul_le_mul_right hprod.le hpos)
    (Nat.le_of_mul_le_mul_right hprod.ge hpos)

private theorem ggGamma_eq_one_of_map_eq_one {G : Type} [Group G] {L Bs : Subgroup G}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} (hperf : commutator ↥L = ⊤)
    {ρ : Bs →* (↥L ⧸ Subgroup.center ↥L)}
    (hconj : ∀ (b : ↥Bs) (z : ↥L),
      QuotientGroup.mk (ggGamma L hN b z) = ρ b * QuotientGroup.mk z * (ρ b)⁻¹)
    (b : ↥Bs) (hb : ρ b = 1) : ggGamma L hN b = 1 := by
  have hc : ∀ z : ↥L, z⁻¹ * ggGamma L hN b z ∈ Subgroup.center ↥L := by
    intro z
    have h := hconj b z
    rw [hb, one_mul, inv_one, mul_one] at h
    exact QuotientGroup.eq.mp h.symm
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    { toFun := fun z => ⟨z⁻¹ * ggGamma L hN b z, hc z⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun z w => Subtype.ext (by
        have hw : w⁻¹ * (z⁻¹ * ggGamma L hN b z) = (z⁻¹ * ggGamma L hN b z) * w⁻¹ :=
          Subgroup.mem_center_iff.mp (hc z) w⁻¹
        change (z * w)⁻¹ * ggGamma L hN b (z * w) =
          (z⁻¹ * ggGamma L hN b z) * (w⁻¹ * ggGamma L hN b w)
        rw [map_mul, mul_inv_rev]
        calc w⁻¹ * z⁻¹ * (ggGamma L hN b z * ggGamma L hN b w)
            = (w⁻¹ * (z⁻¹ * ggGamma L hN b z)) * ggGamma L hN b w := by group
          _ = ((z⁻¹ * ggGamma L hN b z) * w⁻¹) * ggGamma L hN b w := by rw [hw]
          _ = (z⁻¹ * ggGamma L hN b z) * (w⁻¹ * ggGamma L hN b w) := by group) }
  refine MulEquiv.ext fun z => ?_
  have hzc : z ∈ commutator ↥L := by
    rw [hperf]
    exact Subgroup.mem_top z
  have hz : f z = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker f hzc)
  have h2 : z⁻¹ * ggGamma L hN b z = 1 := congrArg Subtype.val hz
  rw [MulAut.one_apply]
  calc ggGamma L hN b z = z * (z⁻¹ * ggGamma L hN b z) := by group
    _ = z := by rw [h2, mul_one]

theorem ggRowP_EOmP_or_EOmM_data {p : ℕ} [Fact p.Prime] {lab : LargeEvenLabel}
    (hrow : ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) (hn1 : lab.n = 1) :
    p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank := by
  have hp3 : ∀ h : p ∣ 2 ^ lab.n + 1, p = 3 := by
    intro h
    rw [hn1] at h
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h
  rcases hrow with ⟨hD, h4, -, hpq⟩ | ⟨hM, h5, -, hpq⟩
  · exact ⟨hp3 hpq, Or.inl hD, h4⟩
  · exact ⟨hp3 hpq, Or.inr hM, by omega⟩

private theorem map_subtype_orthDerived_properties {p : ℕ} {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {E : Subgroup ↥(orthDerived Q)}
    (hE : IsElemAbelian p E ∧
      ∀ g ∈ Subgroup.centralizer (E : Set ↥(orthDerived Q)), g ^ p = 1 → g ∈ E) :
    let A : Subgroup (V ≃ₗ[F] V) := E.map (orthDerived Q).subtype
    A ≤ orthDerived Q ∧ (∀ a ∈ A, a ^ p = 1) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩
    simpa [Subgroup.coe_pow] using congrArg Subtype.val (hE.1.2 x hx)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg Subtype.val (CFSG.Open.IsElemAbelian.comm hE.1 hx hy)
  · intro g hg hgp hgc
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    apply hE.2 ⟨g, hg⟩
    · intro e he
      exact Subtype.ext (by
        change (e : V ≃ₗ[F] V) * g = g * (e : V ≃ₗ[F] V)
        exact (hgc (e : V ≃ₗ[F] V) ⟨e, he, rfl⟩).symm)
    · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)

private theorem card_eq_three_pow_of_orthTwo {p : ℕ} [Fact p.Prime] {F : Type} [Field F]
    [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[F] V)} (hAΩ : A ≤ orthDerived Q)
    (hApow : ∀ a ∈ A, a ^ p = 1) (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) {lab : LargeEvenLabel}
    (hrow : ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) (hn1 : lab.n = 1)
    (hdim : finrank F V = 2 * lab.rank) (hcard2 : Nat.card F = 2)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ lab.tag = .D) :
    Nat.card A = 3 ^ lab.rank := by
  have hp3 : p = 3 := by
    rw [hcard2] at hpq
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hpq
  subst hp3
  have hrank : 4 ≤ lab.rank := by
    rcases hrow with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩
    · exact h
    · omega
  have htype : (CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Even lab.rank) ∨
      (¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Odd lab.rank) := by
    rcases hrow with ⟨hD, -, heven, -⟩ | ⟨hM, -, hodd, -⟩
    · exact Or.inl ⟨hplus.mpr hD, heven⟩
    · refine Or.inr ⟨?_, hodd⟩
      rw [hplus]
      intro h
      rw [hM] at h
      cases h
  obtain ⟨r, τ, hτ, hτr, -, -, -, -⟩ :=
    exists_torus (K := F) (V := V) hp2 (Or.inr hpq) hQ hT hAΩ hApow hAcomm hmax hne
  have hchar := charSum_top_modEq_one_of_witt hQ (r := lab.rank) (by omega) hdim hpq htype
  have hr : finrank F V = 2 * r :=
    finrank_eq_two_mul_of_charSum hp2 (Or.inr hpq) hQ hT hAΩ hApow hAcomm hmax hne hτ hτr hchar
  rw [← hτr, ← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv,
    Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  congr 1
  omega

private def orthQuotImage {G : Type} [Group G] {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} {L : Subgroup G}
    (σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q)) (P : Subgroup G) :
    Subgroup ↥(orthDerived Q) :=
  ((P.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map σ.toMonoidHom

private theorem orthQuotImage_isPGroup {G : Type} [Group G] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {L P : Subgroup G}
    {σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q)}
    (hP : IsPGroup 2 P) : IsPGroup 2 (orthQuotImage σ P) := by
  dsimp only [orthQuotImage]
  exact ((hP.comap_of_injective L.subtype L.subtype_injective).map _).map _

private theorem orthQuotImage_normalized {G : Type} [Group G] {F : Type} [Field F] {V : Type}
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {L Bs P : Subgroup G}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q)}
    {ρ : Bs →* (↥L ⧸ Subgroup.center ↥L)}
    (hconj : ∀ (b : ↥Bs) (z : ↥L),
      QuotientGroup.mk (ggGamma L hN b z) = ρ b * QuotientGroup.mk z * (ρ b)⁻¹)
    (hBsP : Bs ≤ Subgroup.normalizer (P : Set G)) :
    ∀ e ∈ ρ.range.map σ.toMonoidHom, ∀ t ∈ orthQuotImage σ P,
      e * t * e⁻¹ ∈ orthQuotImage σ P := by
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩ _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  have hγ : ggGamma L hN b l ∈ P.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf, ggGamma_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hBsP b.2) l).mp hl
  refine ⟨QuotientGroup.mk (ggGamma L hN b l), ⟨_, hγ, rfl⟩, ?_⟩
  change σ (QuotientGroup.mk (ggGamma L hN b l)) =
    σ (ρ b) * σ (QuotientGroup.mk l) * (σ (ρ b))⁻¹
  rw [hconj b l, map_mul, map_mul, map_inv]

private theorem eq_bot_of_orthQuotImage {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {L Bs P : Subgroup G} {σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q)}
    {ρ : Bs →* (↥L ⧸ Subgroup.center ↥L)} {lab : LargeEvenLabel}
    (hcard2 : Nat.card F = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hE : IsElemAbelian 3 (ρ.range.map σ.toMonoidHom) ∧
      ∀ g ∈ Subgroup.centralizer (ρ.range.map σ.toMonoidHom : Set ↥(orthDerived Q)),
        g ^ 3 = 1 → g ∈ ρ.range.map σ.toMonoidHom)
    (hcardE : Nat.card (ρ.range.map σ.toMonoidHom) = 3 ^ lab.rank)
    (hdim : finrank F V = 2 * lab.rank)
    (hPΩ : IsPGroup 2 (orthQuotImage σ P))
    (hNE : ∀ e ∈ ρ.range.map σ.toMonoidHom, ∀ t ∈ orthQuotImage σ P,
      e * t * e⁻¹ ∈ orthQuotImage σ P) :
    orthQuotImage σ P = ⊥ := by
  classical
  let EQ : Subgroup ↥(orthDerived Q) := ρ.range.map σ.toMonoidHom
  let PΩ : Subgroup ↥(orthDerived Q) := orthQuotImage σ P
  have hE' : IsElemAbelian 3 EQ ∧
      ∀ g ∈ Subgroup.centralizer (EQ : Set ↥(orthDerived Q)), g ^ 3 = 1 → g ∈ EQ := hE
  have hcardE' : Nat.card EQ = 3 ^ lab.rank := hcardE
  have hPΩ' : IsPGroup 2 PΩ := hPΩ
  have hNE' : ∀ e ∈ EQ, ∀ t ∈ PΩ, e * t * e⁻¹ ∈ PΩ := hNE
  change PΩ = ⊥
  let ρ₁ : ↥(orthDerived Q) →* Module.End F V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (orthDerived Q).subtype
  have hρ₁inj : Function.Injective ρ₁ := fun g h hgh =>
    (orthDerived Q).subtype_injective (LinearEquiv.toLinearMap_injective hgh)
  have hρ₁ : ∀ g x y, QuadraticMap.polarBilin Q (ρ₁ g x) (ρ₁ g y) =
      QuadraticMap.polarBilin Q x y := by
    intro g x y
    have hg : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self _ g.2
    have hgQ : ∀ v, Q ((g : V ≃ₗ[F] V) v) = Q v := fun v =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
    change Q ((g : V ≃ₗ[F] V) x + (g : V ≃ₗ[F] V) y) - Q ((g : V ≃ₗ[F] V) x) -
      Q ((g : V ≃ₗ[F] V) y) = Q (x + y) - Q x - Q y
    rw [← map_add, hgQ, hgQ, hgQ]
  have hrefl : (QuadraticMap.polarBilin Q).IsRefl := fun x y h => by
    rw [QuadraticMap.polarBilin_apply_apply] at h ⊢
    rwa [QuadraticMap.polar_comm]
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V)) DFunLike.coe_injective
  exact eq_bot_of_full_of_card_two hcard2 (QuadraticMap.polarBilin Q) hQ hrefl
    (by rw [hdim]; exact even_two_mul lab.rank) ρ₁ hρ₁inj hρ₁
    (fun a b => Subtype.ext (CFSG.Open.IsElemAbelian.comm hE'.1 a.2 b.2)) hE'.1.2
    hPΩ' hNE' (le_of_eq (by
      rw [hcardE', hdim, Nat.mul_div_cancel_left lab.rank (by norm_num : 0 < 2)]))

private theorem le_centralizer_of_orthQuotImage_eq_bot {G : Type} [Group G] {F : Type} [Field F]
    {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {L P : Subgroup G}
    {σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q)}
    (hPL : P ≤ L) (hbot : orthQuotImage σ P = ⊥) :
    P ≤ Subgroup.centralizer (L : Set G) := by
  intro g hg
  have hl : (⟨g, hPL hg⟩ : ↥L) ∈ P.subgroupOf L := hg
  have h1 : σ (QuotientGroup.mk (⟨g, hPL hg⟩ : ↥L)) ∈ orthQuotImage σ P :=
    ⟨_, ⟨_, hl, rfl⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨y, hy⟩)

theorem le_centralizer_of_isPGroup_two_orthTwo {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs L : Subgroup G} (hRig : GGLabelRigidInput) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) p Bs L)
    (hact : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G), ∃ b : ↥Bs, ggGamma L hN b ≠ 1)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPL : P ≤ L)
    (hBsP : Bs ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ Subgroup.centralizer (L : Set G) := by
  classical
  have hmarkK : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmark
  have hperf : commutator ↥L = ⊤ := hmark.1
  obtain ⟨lab, hΛ, hhas, R, hRgrp, I, F', θ, hPm⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨⟨hrow, hn1⟩, -, -⟩ := hPm
  obtain ⟨hp3, htag, hrank⟩ := ggRowP_EOmP_or_EOmM_data hrow hn1
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hmarkK
  obtain ⟨F, hField, hFinite, hChar, V, hAdd, hMod, hFinDim, hNontrivial, Q, hQ, eQ, ρ,
    hcard, -, hT, hdim, hplus, himage, hcompat0⟩ :=
    OrthKExactTwo.exists_quadratic_image_of_orthogonal_marking hRig hp2 hmarkK hBs hSC
      hΛ hhas htag hrank
  letI : Field F := hField; letI : Finite F := hFinite; letI : CharP F 2 := hChar
  letI : AddCommGroup V := hAdd; letI : Module F V := hMod
  letI : FiniteDimensional F V := hFinDim
  have hcard2 : Nat.card F = 2 := by rw [hcard, hn1, pow_one]
  have hpq : 3 ∣ Nat.card F + 1 := by rw [hcard2]
  have hconjq : ∀ (b : ↥Bs) (z : ↥L), (QuotientGroup.mk (ggGamma L hN b z) :
      ↥L ⧸ Subgroup.center ↥L) = ρ b * QuotientGroup.mk z * (ρ b)⁻¹ := by
    intro b z
    apply eQ.injective
    rw [hcompat0 b z, MulAut.conj_apply, map_mul, map_mul, map_inv]
  let σ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(orthDerived Q) :=
    eQ.trans (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hQ).symm
  let EQ : Subgroup ↥(orthDerived Q) := ρ.range.map σ.toMonoidHom
  let A : Subgroup (V ≃ₗ[F] V) := EQ.map (orthDerived Q).subtype
  have hEimage : IsElemAbelian 3 EQ ∧
      ∀ g ∈ Subgroup.centralizer (EQ : Set ↥(orthDerived Q)), g ^ 3 = 1 → g ∈ EQ := by
    simpa [σ, EQ] using himage
  obtain ⟨hAΩ, hApow, hAcomm, hmax⟩ := map_subtype_orthDerived_properties hEimage
  have hne : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨b, hb⟩ := hact hN
    have hρb : ρ b ≠ 1 := fun h1 => hb (ggGamma_eq_one_of_map_eq_one hperf hconjq b h1)
    refine ⟨((σ (ρ b) : ↥(orthDerived Q)) : V ≃ₗ[F] V),
      ⟨σ (ρ b), ⟨ρ b, ⟨b, rfl⟩, rfl⟩, rfl⟩, fun h1 => ?_⟩
    exact hρb (σ.injective (by rw [map_one]; exact Subtype.ext h1))
  have hcardA : Nat.card A = 3 ^ lab.rank :=
    card_eq_three_pow_of_orthTwo hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne hrow hn1 hdim hcard2
      hplus
  have hcardE : Nat.card EQ = 3 ^ lab.rank :=
    (Subgroup.card_map_of_injective (orthDerived Q).subtype_injective).symm.trans hcardA
  let PΩ : Subgroup ↥(orthDerived Q) := orthQuotImage σ P
  have hPΩ : IsPGroup 2 PΩ := orthQuotImage_isPGroup hP
  have hNE : ∀ e ∈ EQ, ∀ t ∈ PΩ, e * t * e⁻¹ ∈ PΩ :=
    orthQuotImage_normalized hconjq hBsP
  have hbot : PΩ = ⊥ :=
    eq_bot_of_orthQuotImage hcard2 hQ hEimage hcardE hdim hPΩ hNE
  exact le_centralizer_of_orthQuotImage_eq_bot hPL hbot

end

end OrthTorus

end CFSG.StandardType

end

