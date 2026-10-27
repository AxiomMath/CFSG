module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.S152SProd
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isElementaryAbelian_prod {p : ℕ} {A B : Type*} [Group A] [Group B]
    [CFSG.IsElementaryAbelian p A] [CFSG.IsElementaryAbelian p B] :
    CFSG.IsElementaryAbelian p (A × B) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    rw [Monoid.exponent_prod]
    exact Nat.lcm_dvd (CFSG.IsElementaryAbelian.exponent_dvd_p p A)
      (CFSG.IsElementaryAbelian.exponent_dvd_p p B)

theorem isExtraspecial_sup_of_two_extraspecial_27
    {A B : Subgroup G}
    (hA : CFSG.IsExtraspecial 3 A) (hB : CFSG.IsExtraspecial 3 B)
    (hAc : Nat.card A = 27) (hBc : Nat.card B = 27)
    (hAexp : ∀ a : A, a ^ 3 = 1) (hBexp : ∀ b : B, b ^ 3 = 1)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZA : A ⊓ B = (Subgroup.center A).map A.subtype)
    (hZB : A ⊓ B = (Subgroup.center B).map B.subtype) :
    CFSG.IsExtraspecial 3 ↥(A ⊔ B) ∧ Nat.card ↥(A ⊔ B) = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hAcardZ : Nat.card (Subgroup.center A) = 3 := hA.center_order_p
  have hBcardZ : Nat.card (Subgroup.center B) = 3 := hB.center_order_p
  have hZAcard : Nat.card ↥((Subgroup.center A).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hAcardZ]
  have hinfcard : Nat.card ↥(A ⊓ B) = 3 := by rw [hZA, hZAcard]
  have hsupcard : Nat.card ↥(A ⊔ B) = 3 ^ 5 := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hcomm
    rw [hAc, hBc, hinfcard] at h
    have h' : Nat.card ↥(A ⊔ B) * 3 = 3 ^ 5 * 3 := by
      calc Nat.card ↥(A ⊔ B) * 3 = 27 * 27 := h
        _ = 3 ^ 5 * 3 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  haveI : Finite ↥(A ⊔ B) := Nat.finite_of_card_ne_zero (by rw [hsupcard]; norm_num)
  let P : Subgroup G := A ⊔ B
  let A' : Subgroup ↥P := A.subgroupOf P
  let B' : Subgroup ↥P := B.subgroupOf P
  have hAle : A ≤ P := le_sup_left
  have hBle : B ≤ P := le_sup_right
  have hA'B'comm : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hcomm (a : G) (Subgroup.mem_subgroupOf.mp ha) (b : G) (Subgroup.mem_subgroupOf.mp hb)
  have htop : A' ⊔ B' = ⊤ := by
    have h := Subgroup.subgroupOf_sup hAle hBle
    rw [← h]
    rw [show A ⊔ B = P from rfl, Subgroup.subgroupOf_self]
  have hIso := CFSG.Quasithin.S152S.centralProductQuotEquiv A' B' hA'B'comm htop
  have hAqcard : Nat.card (A ⧸ Subgroup.center A) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center A)
    rw [hAc, hAcardZ] at h
    omega
  have hBqcard : Nat.card (B ⧸ Subgroup.center B) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center B)
    rw [hBc, hBcardZ] at h
    omega
  have hA'qcard : Nat.card (A' ⧸ Subgroup.center A') = 9 := by
    rw [← Nat.card_congr (CFSG.Quasithin.S152S.quotCenterEquiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := P) hAle).symm).toEquiv]
    exact hAqcard
  have hB'qcard : Nat.card (B' ⧸ Subgroup.center B') = 9 := by
    rw [← Nat.card_congr (CFSG.Quasithin.S152S.quotCenterEquiv
      (Subgroup.subgroupOfEquivOfLe (H := B) (K := P) hBle).symm).toEquiv]
    exact hBqcard
  have hAq : CFSG.IsElementaryAbelian 3 (A' ⧸ Subgroup.center A') :=
    CFSG.IsElementaryAbelian.of_mulEquiv
      (CFSG.Quasithin.S152S.quotCenterEquiv
        (Subgroup.subgroupOfEquivOfLe (H := A) (K := P) hAle).symm)
      hA.quotient_elementary_abelian
  have hBq : CFSG.IsElementaryAbelian 3 (B' ⧸ Subgroup.center B') :=
    CFSG.IsElementaryAbelian.of_mulEquiv
      (CFSG.Quasithin.S152S.quotCenterEquiv
        (Subgroup.subgroupOfEquivOfLe (H := B) (K := P) hBle).symm)
      hB.quotient_elementary_abelian
  have hQelem : CFSG.IsElementaryAbelian 3
      ((A' ⧸ Subgroup.center A') × (B' ⧸ Subgroup.center B')) := by
    haveI := hAq
    haveI := hBq
    exact isElementaryAbelian_prod
  have hPelem : CFSG.IsElementaryAbelian 3 (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsElementaryAbelian.of_mulEquiv hIso.symm hQelem
  have hPQcard : Nat.card (↥P ⧸ Subgroup.center ↥P) = 81 := by
    rw [Nat.card_congr hIso.toEquiv, Nat.card_prod, hA'qcard, hB'qcard]
  have hZPcard : Nat.card (Subgroup.center ↥P) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
    rw [hPQcard, hsupcard] at h
    omega
  have hPext : CFSG.IsExtraspecial 3 ↥P :=
    { center_order_p := hZPcard
      quotient_elementary_abelian := hPelem
      quotient_nontrivial :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hPQcard]; norm_num) }
  exact ⟨by simpa [P] using hPext, hsupcard⟩

theorem exists_elemAbelian_card_nine_of_extraspecial
    {A : Subgroup G}
    (hA : CFSG.IsExtraspecial 3 A) (hAc : Nat.card A = 27)
    (hAexp : ∀ a : A, a ^ 3 = 1) :
    ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      (Subgroup.center A).map A.subtype ≤ E := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hZcard : Nat.card (Subgroup.center A) = 3 := hA.center_order_p
  have hZtop : Subgroup.center A ≠ ⊤ := by
    intro h
    have : Nat.card (Subgroup.center A) = 27 := by rw [h, Subgroup.card_top, hAc]
    omega
  obtain ⟨x, hxZ⟩ : ∃ x : A, x ∉ Subgroup.center A := by
    by_contra h
    exact hZtop (top_unique fun x _ => by
      by_contra hx
      exact h ⟨x, hx⟩)
  let Z : Subgroup G := (Subgroup.center A).map A.subtype
  let E : Subgroup G := Z ⊔ Subgroup.zpowers (x : G)
  have hxpow : (x : G) ^ 3 = 1 := by
    simpa using congrArg Subtype.val (hAexp x)
  have hxne : (x : G) ≠ 1 := by
    intro hx1
    apply hxZ
    have hx1' : x = 1 := Subtype.ext hx1
    rw [hx1']
    exact Subgroup.one_mem _
  have hxord : orderOf (x : G) = 3 := orderOf_eq_prime hxpow hxne
  have hZclass : CFSG.IsElementaryAbelian 3 Z := by
    have hcenter : CFSG.IsElementaryAbelian 3 (Subgroup.center A) := by
      refine CFSG.RankThree.PartTwo.isElementaryAbelian_of_isMulCommutative ?_ ?_
      · infer_instance
      · intro z
        exact Subtype.ext (hAexp z.1)
    exact CFSG.IsElementaryAbelian.map_subtype
  have hzpowy : CFSG.IsElementaryAbelian 3 (Subgroup.zpowers (x : G)) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxpow
  have hcent : Subgroup.zpowers (x : G) ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw x).symm
  have hEclass : CFSG.IsElementaryAbelian 3 E :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (E := Z)
      (C := Subgroup.zpowers (x : G)) hcent
  have hZcardG : Nat.card Z = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hZcard]
  have hinf : Z ⊓ Subgroup.zpowers (x : G) = ⊥ := by
    haveI : Finite ↥(Subgroup.zpowers (x : G)) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hxord]; norm_num)
    have hdvd : Nat.card ↥(Z ⊓ Subgroup.zpowers (x : G)) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (H := Z ⊓ Subgroup.zpowers (x : G))
        (K := Subgroup.zpowers (x : G)) inf_le_right
      rwa [Nat.card_zpowers, hxord] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq (Z ⊓ Subgroup.zpowers (x : G)) h1
    · exfalso
      have hle : Z ⊓ Subgroup.zpowers (x : G) = Subgroup.zpowers (x : G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hxord])
      have hxmem : (x : G) ∈ Z ⊓ Subgroup.zpowers (x : G) := by
        rw [hle]
        exact Subgroup.mem_zpowers (x : G)
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxmem.1
      have hzx' : z = x := Subtype.ext hzx
      exact hxZ (hzx' ▸ hz)
  have hcommZ : ∀ z ∈ Z, ∀ w ∈ Subgroup.zpowers (x : G), z * w = w * z := by
    intro z hz w hw
    exact Subgroup.mem_centralizer_iff.mp (hcent hw) z hz
  have hcardE : Nat.card E = 9 := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
      (A := Z) (B := Subgroup.zpowers (x : G)) hcommZ
    rw [hinf, Subgroup.card_bot, hZcardG, Nat.card_zpowers, hxord] at h
    change Nat.card ↥(Z ⊔ Subgroup.zpowers (x : G)) = 9
    omega
  refine ⟨E, ?_, ?_, hcardE, le_sup_left⟩
  · exact sup_le (Subgroup.map_subtype_le _) (Subgroup.zpowers_le.mpr x.2)
  · exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hEclass

theorem triple_commutator_eq_bot_of_isExtraspecial {p : ℕ} {P : Subgroup G}
    (hP : CFSG.IsExtraspecial p ↥P) : ⁅⁅P, P⁆, P⁆ = ⊥ := by
  have hcommP : _root_.commutator ↥P ≤ Subgroup.center ↥P :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      hP.quotient_elementary_abelian.toIsMulCommutative
  have hmap : Subgroup.map P.subtype (_root_.commutator ↥P) = ⁅P, P⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype]
  have hcommP' : ⁅P, P⁆ ≤ (Subgroup.center ↥P).map P.subtype := by
    rw [← hmap]
    exact Subgroup.map_mono hcommP
  rw [eq_bot_iff]
  calc ⁅⁅P, P⁆, P⁆ ≤ ⁅(Subgroup.center ↥P).map P.subtype, P⁆ :=
        Subgroup.commutator_mono hcommP' le_rfl
    _ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro x hx y hy
        obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
        rw [Subgroup.mem_bot, ← hzx, commutatorElement_eq_one_iff_mul_comm]
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm

theorem exponent_sup_eq_three
    {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAexp : ∀ a : A, a ^ 3 = 1) (hBexp : ∀ b : B, b ^ 3 = 1)
    (hsupcard : Nat.card ↥(A ⊔ B) = 3 ^ 5) :
    Monoid.exponent ↥(A ⊔ B) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite ↥(A ⊔ B) := Nat.finite_of_card_ne_zero (by rw [hsupcard]; norm_num)
  haveI : Nontrivial ↥(A ⊔ B) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hsupcard]; norm_num)
  have hdvd : Monoid.exponent ↥(A ⊔ B) ∣ 3 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hcomm x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hab]
    have hcab : Commute a b := hcomm a ha b hb
    have ha3 : a ^ 3 = 1 := by
      simpa using congrArg Subtype.val (hAexp ⟨a, ha⟩)
    have hb3 : b ^ 3 = 1 := by
      simpa using congrArg Subtype.val (hBexp ⟨b, hb⟩)
    exact (hcab.mul_pow 3).trans (by rw [ha3, hb3, mul_one])
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    have := Monoid.one_lt_exponent (G := ↥(A ⊔ B))
    omega
  · exact h3

theorem finrank_le_half_of_isotropic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {U : Submodule K V} (hU : U ≤ B.orthogonal U) :
    2 * Module.finrank K U ≤ Module.finrank K V := by
  have h1 : Module.finrank K U ≤ Module.finrank K (B.orthogonal U) :=
    Submodule.finrank_mono hU
  rw [LinearMap.BilinForm.finrank_orthogonal hB U] at h1
  omega


theorem pRank_three_sup_of_two_extraspecial_27 [Finite G]
    {A B : Subgroup G}
    (hA : CFSG.IsExtraspecial 3 A) (hB : CFSG.IsExtraspecial 3 B)
    (hAc : Nat.card A = 27) (hBc : Nat.card B = 27)
    (hAexp : ∀ a : A, a ^ 3 = 1) (hBexp : ∀ b : B, b ^ 3 = 1)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZA : A ⊓ B = (Subgroup.center A).map A.subtype)
    (hZB : A ⊓ B = (Subgroup.center B).map B.subtype) :
    CFSG.Open.pRank 3 (A ⊔ B) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hPext, hsupcard⟩ :=
    isExtraspecial_sup_of_two_extraspecial_27 hA hB hAc hBc hAexp hBexp hcomm hZA hZB
  let P : Subgroup G := A ⊔ B
  have hPext' : CFSG.IsExtraspecial 3 ↥P := by simpa [P] using hPext
  have hsupcard' : Nat.card ↥P = 3 ^ 5 := by simpa [P] using hsupcard
  haveI : Finite ↥P := Subtype.finite
  have htriple : ⁅⁅P, P⁆, P⁆ = ⊥ :=
    triple_commutator_eq_bot_of_isExtraspecial hPext'
  have hexpP : Monoid.exponent ↥P = 3 := by
    simpa [P] using exponent_sup_eq_three hcomm hAexp hBexp hsupcard
  haveI hclass : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨htriple⟩
  haveI hexpFact : Fact (Monoid.exponent ↥P = 3) := ⟨hexpP⟩
  have hPQcard : Nat.card (↥P ⧸ Subgroup.center ↥P) = 81 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
    rw [hsupcard', hPext'.center_order_p] at h
    omega
  let V := Additive (↥P ⧸ Subgroup.center ↥P)
  haveI : Finite (↥P ⧸ Subgroup.center ↥P) := inferInstance
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVcard : Nat.card V = 81 := by
    exact (Nat.card_congr (Additive.ofMul (α := ↥P ⧸ Subgroup.center ↥P))).symm.trans hPQcard
  have hVfr : Module.finrank (ZMod 3) V = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [hVcard, Nat.card_zmod] at h
    have h4 : 3 ^ 4 = 3 ^ Module.finrank (ZMod 3) V := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h4.symm
  let ζ : Subgroup.center ↥P ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq hPext'.center_order_p (by simp)
  have hform_nd :
      (CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form ζ).Nondegenerate := by
    refine ⟨fun a h =>
      CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form_nondegenerate ζ a h,
      fun b h => ?_⟩
    apply CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form_nondegenerate ζ b
    intro a
    have h1 := h a
    have h2 := CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form_alt ζ (a + b)
    simp only [map_add, LinearMap.add_apply,
      CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form_alt, h1] at h2
    simpa using h2
  have hupper : CFSG.Open.pRank 3 P ≤ 3 := by
    refine CFSG.SectionRank.pRank_le (p := 3) (H := P) (k := 3) (by norm_num) ?_
    intro E hEP hE
    haveI hEcomm : IsMulCommutative E := hE.1
    let q : ↥P →* (↥P ⧸ Subgroup.center ↥P) := QuotientGroup.mk' _
    let incl : E →* ↥P := Subgroup.inclusion hEP
    let f : E →* (↥P ⧸ Subgroup.center ↥P) := q.comp incl
    have hmem_center : ∀ x : f.ker, incl (x : E) ∈ Subgroup.center ↥P := by
      intro x
      have hx : f (x : E) = 1 := MonoidHom.mem_ker.mp x.2
      have hx' : q (incl (x : E)) = 1 := by simpa [f] using hx
      exact (QuotientGroup.eq_one_iff (incl (x : E))).mp hx'
    let toC : f.ker → Subgroup.center ↥P := fun x => ⟨incl (x : E), hmem_center x⟩
    have hker_le : Nat.card f.ker ≤ 3 := by
      have hinj : Function.Injective toC := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        have hxy' : incl (x : E) = incl (y : E) :=
          congrArg (fun z : Subgroup.center ↥P => (z : ↥P)) hxy
        exact congrArg (fun z : ↥P => (z : G)) hxy'
      calc Nat.card f.ker ≤ Nat.card (Subgroup.center ↥P) :=
            Nat.card_le_card_of_injective toC hinj
        _ = 3 := hPext'.center_order_p
    let K : Subgroup (↥P ⧸ Subgroup.center ↥P) := f.range
    let U : Submodule (ZMod 3) V := AddSubgroup.toZModSubmodule 3 K.toAddSubgroup
    have hKU : Nat.card K = Nat.card U := by
      refine Nat.card_congr ?_
      refine ⟨fun x => ⟨Additive.ofMul x.1, ?_⟩, fun x => ⟨Additive.toMul x.1, ?_⟩, ?_, ?_⟩
      · exact x.2
      · exact x.2
      · intro x
        apply Subtype.ext
        exact toMul_ofMul x.1
      · intro x
        apply Subtype.ext
        exact ofMul_toMul x.1
    haveI : Finite U := Subtype.finite
    haveI : Module.Finite (ZMod 3) U := Module.Finite.of_finite
    have hKUcard : Nat.card K = 3 ^ Module.finrank (ZMod 3) U := by
      rw [hKU, Module.natCard_eq_pow_finrank (K := ZMod 3) (V := U), Nat.card_zmod]
    have hform_zero : ∀ a ∈ U, ∀ b ∈ U,
        (CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form ζ) a b = 0 := by
      intro a ha b hb
      have haK : Additive.toMul a ∈ K := by
        exact (Additive.mem_toAddSubgroup K a).mp ha
      have hbK : Additive.toMul b ∈ K := by
        exact (Additive.mem_toAddSubgroup K b).mp hb
      obtain ⟨ea, hea⟩ := MonoidHom.mem_range.mp haK
      obtain ⟨eb, heb⟩ := MonoidHom.mem_range.mp hbK
      have haeq : a = Additive.ofMul (QuotientGroup.mk (incl ea) : ↥P ⧸ Subgroup.center ↥P) := by
        calc a = Additive.ofMul (Additive.toMul a) := (ofMul_toMul a).symm
          _ = Additive.ofMul (f ea) := by rw [hea]
          _ = Additive.ofMul (QuotientGroup.mk (incl ea) : ↥P ⧸ Subgroup.center ↥P) := rfl
      have hbeq : b = Additive.ofMul (QuotientGroup.mk (incl eb) : ↥P ⧸ Subgroup.center ↥P) := by
        calc b = Additive.ofMul (Additive.toMul b) := (ofMul_toMul b).symm
          _ = Additive.ofMul (f eb) := by rw [heb]
          _ = Additive.ofMul (QuotientGroup.mk (incl eb) : ↥P ⧸ Subgroup.center ↥P) := rfl
      rw [haeq, hbeq,
        CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form_spec ζ
          (incl ea) (incl eb)
          (CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient.commutator_mem_center htriple
            (incl ea) (incl eb))]
      have h1 : ⁅(incl ea), (incl eb)⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        rw [← map_mul, ← map_mul, mul_comm' ea eb]
      have hcenter_eq :
          (⟨⁅incl ea, incl eb⁆,
            CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient.commutator_mem_center htriple
              (incl ea) (incl eb)⟩ : Subgroup.center ↥P) = 1 := by
        apply Subtype.ext
        exact h1
      rw [hcenter_eq, map_one]
      rfl
    have hiso : U ≤ LinearMap.BilinForm.orthogonal
        (CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form ζ) U := by
      intro a ha
      change ∀ b ∈ U,
        (CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form ζ) b a = 0
      intro b hb
      exact hform_zero b hb a ha
    have hfrU : Module.finrank (ZMod 3) U ≤ 2 := by
      have hle := finrank_le_half_of_isotropic
        (B := CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm.form ζ) hform_nd hiso
      have hV4 : Module.finrank (ZMod 3) (Additive (↥P ⧸ Subgroup.center ↥P)) = 4 := by
        simpa [V] using hVfr
      rw [hV4] at hle
      have hle' : 2 * Module.finrank (ZMod 3) U ≤ 4 := by
        simpa [V] using hle
      omega
    have hKle : Nat.card K ≤ 9 := by
      rw [hKUcard]
      calc 3 ^ Module.finrank (ZMod 3) U ≤ 3 ^ 2 :=
            Nat.pow_le_pow_right (by norm_num) hfrU
        _ = 9 := by norm_num
    have hEcard : Nat.card f.ker * Nat.card K = Nat.card E := by
      have h := Subgroup.card_ker_mul_card_range f
      simpa [K] using h
    rw [← hEcard]
    calc Nat.card f.ker * Nat.card K ≤ 3 * 9 := Nat.mul_le_mul hker_le hKle
      _ = 3 ^ 3 := by norm_num
  have hZAcard : Nat.card ↥((Subgroup.center A).map A.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hA.center_order_p]
  have hinfcard : Nat.card ↥(A ⊓ B) = 3 := by rw [hZA, hZAcard]
  have hlower : 3 ≤ CFSG.Open.pRank 3 P := by
    obtain ⟨EA, hEAleA, hEAelem, hEAcard, hZAleEA⟩ :=
      exists_elemAbelian_card_nine_of_extraspecial hA hAc hAexp
    obtain ⟨EB, hEBleB, hEBelem, hEBCard, hZBleEB⟩ :=
      exists_elemAbelian_card_nine_of_extraspecial hB hBc hBexp
    have hZAEB : (Subgroup.center A).map A.subtype ≤ EB := by
      have hEq : (Subgroup.center A).map A.subtype = (Subgroup.center B).map B.subtype := by
        rw [← hZA, ← hZB]
      rw [hEq]
      exact hZBleEB
    have hcommEAEB : ∀ a ∈ EA, ∀ b ∈ EB, a * b = b * a :=
      fun a ha b hb => hcomm a (hEAleA ha) b (hEBleB hb)
    have hcent : EB ≤ Subgroup.centralizer (EA : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a (hEAleA ha) b (hEBleB hb)
    haveI hEAclass : CFSG.IsElementaryAbelian 3 EA :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hEAelem
    haveI hEBclass : CFSG.IsElementaryAbelian 3 EB :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hEBelem
    have hEABclass : CFSG.IsElementaryAbelian 3 ↥(EA ⊔ EB) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer (p := 3) (E := EA) (C := EB) hcent
    have hEABelem : CFSG.Open.IsElemAbelian 3 (EA ⊔ EB) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hEABclass
    have hinfEAEB : EA ⊓ EB = A ⊓ B := by
      apply le_antisymm
      · exact le_inf (inf_le_left.trans hEAleA) (inf_le_right.trans hEBleB)
      · rw [hZA]
        exact le_inf hZAleEA hZAEB
    have hEAEBcard : Nat.card ↥(EA ⊔ EB) = 27 := by
      have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
        (A := EA) (B := EB) hcommEAEB
      rw [hinfEAEB, hinfcard, hEAcard, hEBCard] at h
      omega
    refine CFSG.SectionRank.le_pRank (p := 3) (H := P) (E := EA ⊔ EB) (k := 3)
      (by norm_num) ?_ hEABelem ?_
    · exact sup_le (hEAleA.trans le_sup_left) (hEBleB.trans le_sup_right)
    · rw [hEAEBcard]
      norm_num
  exact le_antisymm hupper hlower

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
