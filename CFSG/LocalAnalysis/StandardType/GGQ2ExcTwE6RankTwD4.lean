module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthNonFull
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRankR
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import CFSG.GroupTheory.ElemAbelianLiftOddKernel
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)

noncomputable section

theorem exists_fixed_singular_of_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {E : Subgroup ↥(orthDerived Q)}
    (h3 : 3 ∣ Nat.card {v : V // Q v = 0})
    (hE : IsPGroup 3 ↥E) :
    ∃ u : V, u ≠ 0 ∧ Q u = 0 ∧ ∀ g ∈ E, (g : V ≃ₗ[K] V) u = u := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : ∀ g : ↥E, ((g : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun g =>
    CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q (g : ↥(orthDerived Q)).2
  letI : MulAction ↥E {v : V // Q v = 0} :=
    { smul := fun g v => ⟨(g : V ≃ₗ[K] V) v.1, by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hO g)]
        exact v.2⟩
      one_smul := fun v => by ext; rfl
      mul_smul := fun g h v => by ext; rfl }
  have hmod := hE.card_modEq_card_fixedPoints {v : V // Q v = 0}
  have hdvd : 3 ∣ Nat.card (MulAction.fixedPoints ↥E {v : V // Q v = 0}) :=
    Nat.modEq_zero_iff_dvd.mp
      (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3))
  have h0fix : (⟨0, QuadraticMap.map_zero Q⟩ : {v : V // Q v = 0}) ∈
      MulAction.fixedPoints ↥E {v : V // Q v = 0} := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (map_zero _)
  obtain ⟨b, hb, hbne⟩ :=
    hE.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := {v : V // Q v = 0})
      (a := (⟨0, QuadraticMap.map_zero Q⟩ : {v : V // Q v = 0})) h3 h0fix
  exact ⟨b.1, fun h => hbne (Subtype.ext h).symm, b.2,
    fun g hg => congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨g, hg⟩)⟩

theorem three_dvd_card_singular_qMinus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) (heven : Even m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    3 ∣ Nat.card {v : LargeEvenMinusIdx (m - 1) → K //
      TableBOrth.qMinusForm K (m - 1) b c v = 0} := by
  have hsub : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have hiso := CFSG.Timmesfeld.ClassicalOrders.card_singular_congr
    (TableBOrth.qMinusIsometry (K := K) (m - 1) b c)
  rw [hsub] at hiso
  have hcard := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) (m := m - 1)
    (b := b) (c := c) hbc).1
  rw [hsub, hK] at hcard
  have hpow : (2 : ℤ) ^ m = (2 : ℤ) ^ (m - 1) * 2 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  have hmain : (1 : ℤ) + ((2 : ℤ) ^ m + 1) * ((2 : ℤ) ^ (m - 1) - 1) =
      (2 : ℤ) ^ (m - 1) * ((2 : ℤ) ^ m - 1) := by
    rw [hpow]
    ring
  have hsZ : ((Nat.card {v : LargeEvenMinusIdx (m - 1) → K //
      TableBOrth.qMinusForm K (m - 1) b c v = 0} : ℕ) : ℤ) =
      (2 : ℤ) ^ (m - 1) * ((2 : ℤ) ^ m - 1) := by
    rw [hiso, hcard]
    push_cast
    exact hmain
  have hsNat : Nat.card {v : LargeEvenMinusIdx (m - 1) → K //
      TableBOrth.qMinusForm K (m - 1) b c v = 0} = 2 ^ (m - 1) * (2 ^ m - 1) := by
    apply Nat.cast_injective (R := ℤ)
    rw [hsZ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_sub (Nat.one_le_pow m 2 (by norm_num)),
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have h3 : 3 ∣ 2 ^ m - 1 := by
    obtain ⟨k, rfl⟩ := heven
    have h := Nat.sub_one_dvd_pow_sub_one 4 k
    have h4 : 4 ^ k = 2 ^ (k + k) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, two_mul]
    rw [h4] at h
    simpa using h
  rw [hsNat]
  exact dvd_mul_of_dvd_right h3 _

theorem rootGroup_isPGroup_two {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (u : V) : IsPGroup 2 (rootGroup Q u) := by
  intro g
  obtain ⟨w, hw, hwv⟩ := mem_rootGroup.mp g.2
  have hww : w + w = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h : w + w = (2 : K) • w := by
      rw [show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
    rw [h, h2, zero_smul]
  have hsq : eichler Q u w * eichler Q u w = 1 := by
    rw [eichler_mul hw hw, hww, eichler_zero_right]
  have hg2 : g * g = 1 := by
    refine Subtype.ext ?_
    show (g : V ≃ₗ[K] V) * (g : V ≃ₗ[K] V) = 1
    rw [show (g : V ≃ₗ[K] V) = eichler Q u w from hwv.symm]
    exact hsq
  refine ⟨1, ?_⟩
  show g ^ 2 = 1
  rw [pow_two]
  exact hg2

theorem exists_anisotropic_mem_perp {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) (hdim : 3 ≤ Module.finrank K V) :
    ∃ x ∈ P.perp, Q x ≠ 0 := by
  classical
  have hsum := Submodule.finrank_add_eq_of_isCompl P.isCompl_perp
  have hle : Module.finrank K (Submodule.span K ({P.e, P.f} : Set V)) ≤ 2 := by
    have h2 : Module.finrank K (Submodule.span K ({P.e, P.f} : Set V)) ≤
        ({P.e, P.f} : Set V).toFinset.card := finrank_span_le_card _
    refine h2.trans ?_
    simpa using (Finset.card_le_two (a := P.e) (b := P.f))
  have hpos : 0 < Module.finrank K P.perp := by omega
  haveI : Nontrivial P.perp := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨z, hz0⟩ := exists_ne (0 : P.perp)
  have hzmem : (z : V) ∈ P.perp := z.2
  have hzne : (z : V) ≠ 0 := fun h => hz0 (Subtype.ext h)
  by_cases hQz : Q (z : V) ≠ 0
  · exact ⟨z, hzmem, hQz⟩
  · push Not at hQz
    obtain ⟨w, hwP, hzw⟩ :=
      (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hzmem hzne
    set w' : V := (polar Q (z : V) w)⁻¹ • w with hw'def
    have hw'P : w' ∈ P.perp := P.perp.smul_mem _ hwP
    have hzw' : polar Q (z : V) w' = 1 := by
      rw [hw'def, polar_smul_right_eq, inv_mul_cancel₀ hzw]
    by_cases hQw : Q w' ≠ 0
    · exact ⟨w', hw'P, hQw⟩
    · push Not at hQw
      exact ⟨(z : V) + w', P.perp.add_mem hzmem hw'P, by
        rw [QuadraticMap.map_add Q, hQz, hQw, hzw']
        simp⟩


theorem comap_rootGroup_sq_eq_one {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (u : V) :
    ∀ g ∈ (rootGroup Q u).comap (orthDerived Q).subtype, g ^ 2 = 1 := by
  intro g hg
  obtain ⟨w, hw, hwg⟩ := mem_rootGroup.mp (Subgroup.mem_comap.mp hg)
  have hww : w + w = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h : w + w = (2 : K) • w := by
      rw [show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
    rw [h, h2, zero_smul]
  have hsq : eichler Q u w * eichler Q u w = 1 := by
    rw [eichler_mul hw hw, hww, eichler_zero_right]
  rw [pow_two]
  refine Subtype.ext ?_
  show (g : V ≃ₗ[K] V) * (g : V ≃ₗ[K] V) = 1
  rw [show (g : V ≃ₗ[K] V) = eichler Q u w from hwg.symm]
  exact hsq

theorem conj_mem_comap_rootGroup {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {E : Subgroup ↥(orthDerived Q)}
    {u : V} (hEfix : ∀ e ∈ E, (e : V ≃ₗ[K] V) u = u) {e h : ↥(orthDerived Q)} (he : e ∈ E)
    (hh : h ∈ (rootGroup Q u).comap (orthDerived Q).subtype) :
    e * h * e⁻¹ ∈ (rootGroup Q u).comap (orthDerived Q).subtype := by
    obtain ⟨w, hw, hwh⟩ := mem_rootGroup.mp (Subgroup.mem_comap.mp hh)
    have heO : (e : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q e.2
    have hev : (e : V ≃ₗ[K] V) u = u := hEfix e he
    rw [Subgroup.mem_comap]
    have hroot : (e : V ≃ₗ[K] V) * (h : V ≃ₗ[K] V) * (e : V ≃ₗ[K] V)⁻¹ ∈ rootGroup Q u := by
      have h1 := conj_mem_rootGroup (Q := Q) heO (u := u) (x := (h : V ≃ₗ[K] V))
        (Subgroup.mem_comap.mp hh)
      rwa [hev] at h1
    exact hroot

theorem mulAut_congr_apply_apply {R Ω : Type} [Group R] [Group Ω] (η : R ≃* Ω) (g : MulAut R)
    (z : R) : ((MulAut.congr η) g) (η z) = η (g z) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem excTwE6_twD4_twoSub
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hhas : GGHasLabel ⟨.twD, 4, 1⟩ (↥L ⧸ Subgroup.center ↥L)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ L ∧ Bs ≤ Subgroup.normalizer (S : Set G) ∧
      ¬ S ≤ Subgroup.centralizer (L : Set G) := by
  classical
  have hID : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hS.2.1
  have hΛ : LargeEvenInLambda2 ⟨.twD, 4, 1⟩ := by
    refine ⟨le_rfl, ?_⟩
    show 2 ≤ 4
    norm_num
  have hmark := ggInnerDiagOn_relabel ggLabelRigidInput_holds hID hΛ hhas
  have hNF : GGInnerDiagOnLabel (fun _ lab => GGQ2VACLabOrthNonFull 3 lab ∧ lab.tag = .twD)
      3 Bs L := by
    refine largeEvenMarking_mono ?_ hmark
    rintro lab R _ I F θ ⟨rfl, hN, hI⟩
    have h1 : GGLabQTwo 3 (⟨.twD, 4, 1⟩ : LargeEvenLabel) := by
      simp only [GGLabQTwo]
      norm_num
    have h2 : GGQ2VACLabOrth 3 (⟨.twD, 4, 1⟩ : LargeEvenLabel) := ⟨h1, Or.inr rfl⟩
    have h3 : Even 4 := ⟨2, rfl⟩
    have hnf : GGQ2VACLabOrthNonFull 3 (⟨.twD, 4, 1⟩ : LargeEvenLabel) := by
      unfold GGQ2VACLabOrthNonFull
      exact ⟨h2, le_rfl, Or.inr ⟨rfl, h3⟩⟩
    exact ⟨⟨hnf, rfl⟩, hN, hI⟩
  obtain ⟨K, i1, i2, rest⟩ := ggQ2OrthNonFull_extract_minus hNF
  letI : Field K := i1
  letI : Finite K := i2
  obtain ⟨hK, m, hm4, hmeven, b, c, hbc, θ, hN, hcomm, hBsI0⟩ := rest
  letI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (K := K) (f := 1)
      (by rw [hK, pow_one])
  let Q : QuadraticForm K (LargeEvenMinusIdx (m - 1) → K) := TableBOrth.qMinusForm K (m - 1) b c
  have hQnd : (polarBilin Q).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm (m - 1) hbc
  have hdimV : 3 ≤ Module.finrank K (LargeEvenMinusIdx (m - 1) → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨E, hEea, hEcard, hEsc, hEconj⟩ :=
    ggQ2OrthNonFull_exists_E_minus (hN := hN) hm4 hbc hS hBsI0
  obtain ⟨v, hv0, hvQ, hvfix⟩ :=
    exists_fixed_singular_of_three (E := E)
      (three_dvd_card_singular_qMinus hK hm4 hmeven hbc)
      (CFSG.Open.IsElemAbelian.isPGroup hEea)
  obtain ⟨P, hPe⟩ := exists_hypPair hQnd hvQ hv0
  obtain ⟨x, hxP, hQx⟩ := exists_anisotropic_mem_perp hQnd P hdimV
  have hxperp : polar Q v x = 0 := by
    rw [← hPe]
    exact (HypPair.mem_perp.mp hxP).1
  have hxmem : eichler Q v x ∈ orthDerived Q :=
    eichler_mem_commutator_of_anisotropic hQnd P
      (u := v) (x := x) (fun y hy => by rw [← hPe]; exact (HypPair.mem_perp.mp hy).1) hxP hQx
  have hxne : eichler Q v x ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ :=
      (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.eichler_eq_one_iff hQnd hvQ hv0
        hxperp).mp h1
    have h0 : polar Q P.f x = 0 := (HypPair.mem_perp.mp hxP).2
    rw [ha, polar_smul_right_eq, ← hPe, P.polar_fe, mul_one] at h0
    rw [h0, zero_smul] at ha
    exact hQx (by rw [ha]; exact QuadraticMap.map_zero Q)
  set U : Subgroup ↥(orthDerived Q) := (rootGroup Q v).comap (orthDerived Q).subtype with hU
  haveI hU2 : IsPGroup 2 U := hU ▸ (rootGroup_isPGroup_two (Q := Q) v).comap_subtype
  have hxu : (⟨eichler Q v x, hxmem⟩ : ↥(orthDerived Q)) ∈ U :=
    hU ▸ Subgroup.mem_comap.mpr (mem_rootGroup.mpr ⟨x, hxperp, rfl⟩)
  have hu₀ne : (⟨eichler Q v x, hxmem⟩ : ↥(orthDerived Q)) ≠ 1 := by
    intro h
    exact hxne (congrArg Subtype.val h)
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot] at hxu
    exact hu₀ne (Subgroup.mem_bot.mp hxu)
  have hEU : ∀ e ∈ E, ∀ h ∈ U, e * h * e⁻¹ ∈ U := by
    intro e he h hh
    rw [hU] at hh ⊢
    exact conj_mem_comap_rootGroup (Q := Q) (E := E)
      (u := v) hvfix he hh
  set η : OrthRest.RMinus K (m - 1) b c ≃* ↥(orthDerived Q) :=
    OrthTorus.rMinusEquiv K (m - 1) b c with hη
  set ψ : ↥L →* ↥(orthDerived Q) := η.toMonoidHom.comp (ggQuotHom θ) with hψ
  have hψsurj : Function.Surjective ψ := by
    rw [hψ]
    exact η.surjective.comp (ggQuotHom_surjective θ)
  have hψker : ψ.ker = Subgroup.center ↥L := by
    rw [hψ, MonoidHom.ker_comp_of_injective (ggQuotHom θ) η.toMonoidHom η.injective,
      ker_ggQuotHom]
  set P₀ : Subgroup ↥L := U.comap ψ with hP₀
  have hZP₀ : Subgroup.center ↥L ≤ P₀ := by
    intro z hz
    rw [hP₀, Subgroup.mem_comap]
    have hz' : z ∈ ψ.ker := by rw [hψker]; exact hz
    rw [MonoidHom.mem_ker.mp hz']
    exact U.one_mem
  have hUexp : ∀ u ∈ U, u ^ 2 = 1 := hU ▸ comap_rootGroup_sq_eq_one v
  have hP₀exp : ∀ z : ↥P₀, ((z : ↥L) ^ 2) ∈ Subgroup.center ↥L := by
    intro z
    have hz : ψ (z : ↥L) ∈ U := show ψ (z : ↥L) ∈ U from z.2
    have h1 : ψ ((z : ↥L) ^ 2) = 1 := by
      rw [map_pow, hUexp (ψ (z : ↥L)) hz]
    rw [← hψker]
    exact MonoidHom.mem_ker.mpr h1
  haveI hquotnil : IsPGroup 2 (↥P₀ ⧸ Subgroup.center ↥P₀) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥P₀) y
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_center_iff.mpr (fun w => ?_)
    refine Subtype.ext ?_
    show (w : ↥L) * ((z : ↥P₀) : ↥L) ^ 2 = ((z : ↥P₀) : ↥L) ^ 2 * (w : ↥L)
    exact Subgroup.mem_center_iff.mp (hP₀exp z) (w : ↥P₀)
  haveI hnil : Group.IsNilpotent ↥P₀ :=
    Group.of_quotient_center_nilpotent (IsPGroup.isNilpotent (p := 2) hquotnil)
  have hact : ∀ bb : ↥Bs, ∃ e ∈ E, ∀ y : ↥L, ψ (ggGamma L hN bb y) = e * ψ y * e⁻¹ := by
    intro bb
    have hmem : (MulAut.congr η) (ggBeta L θ hN bb) ∈ E.map
        (MulAut.conj : ↥(orthDerived Q) →*
          MulAut ↥(orthDerived Q)) := by
      have h1 : (MulAut.congr η) (ggBeta L θ hN bb) ∈
          (ggBeta L θ hN).range.map (MulAut.congr η).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨bb, rfl⟩)
      rwa [← hEconj] at h1
    obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hmem
    refine ⟨e, he, fun y => ?_⟩
    have h1 : ψ (ggGamma L hN bb y) = η (ggQuotHom θ (ggGamma L hN bb y)) := rfl
    rw [h1, ← ggBeta_ggQuotHom]
    have h2 : (MulAut.congr η) (ggBeta L θ hN bb) = MulAut.conj e := hee.symm
    calc η ((ggBeta L θ hN bb) (ggQuotHom θ y))
        = ((MulAut.congr η) (ggBeta L θ hN bb)) (η (ggQuotHom θ y)) :=
          (mulAut_congr_apply_apply η (ggBeta L θ hN bb) (ggQuotHom θ y)).symm
      _ = (MulAut.conj e) (η (ggQuotHom θ y)) := by rw [h2]
      _ = e * η (ggQuotHom θ y) * e⁻¹ := by rw [MulAut.conj_apply]
      _ = e * ψ y * e⁻¹ := by rfl
  set φ : ↥P₀ →* U :=
    { toFun := fun z => ⟨ψ (z : ↥L), show ψ (z : ↥L) ∈ U from z.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp } with hφ
  have hφsurj : Function.Surjective φ := by
    intro u
    obtain ⟨l, hl⟩ := hψsurj (u : ↥(orthDerived Q))
    refine ⟨⟨l, ?_⟩, Subtype.ext hl⟩
    show ψ l ∈ U
    rw [hl]
    exact u.2
  set Sp : Sylow 2 ↥P₀ := Sylow.nonempty.some with hSp
  haveI hSpNormal : ((Sp : Subgroup ↥P₀)).Normal := inferInstance
  have hUtope : IsPGroup 2 (⊤ : Subgroup U) :=
    hU2.of_equiv (Subgroup.topEquiv (G := U)).symm
  have hStope : ((Sp.mapSurjective hφsurj : Sylow 2 U) : Subgroup U) = ⊤ :=
    ((Sp.mapSurjective hφsurj).is_maximal' hUtope le_top).symm
  have hSpmapφ : ((Sp : Subgroup ↥P₀)).map φ = ⊤ := by
    rw [← Sylow.coe_mapSurjective (P := Sp) (f := φ) hφsurj]
    exact hStope
  have hSpchar : ((Sp : Subgroup ↥P₀)).Characteristic :=
    Sylow.characteristic_of_normal Sp hSpNormal
  refine ⟨((Sp : Subgroup ↥P₀).map P₀.subtype).map L.subtype, ?_, ?_, ?_, ?_⟩
  · exact (Sp.isPGroup'.map P₀.subtype).map L.subtype
  · rintro _ ⟨y, hy, rfl⟩
    exact y.2
  · intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    obtain ⟨e, he, hacte⟩ := hact ⟨b, hb⟩
    have hγle : P₀.map (↑(ggGamma L hN ⟨b, hb⟩) : ↥L →* ↥L) ≤ P₀ := by
      rintro _ ⟨z, hz, rfl⟩
      show ψ (ggGamma L hN ⟨b, hb⟩ z) ∈ U
      rw [hacte z]
      exact hEU e he (ψ z) hz
    have hγeq : P₀.map (↑(ggGamma L hN ⟨b, hb⟩) : ↥L →* ↥L) = P₀ := by
      refine Subgroup.eq_of_le_of_card_ge hγle ?_
      rw [Subgroup.card_map_of_injective (f := (↑(ggGamma L hN ⟨b, hb⟩) : ↥L →* ↥L))
        (ggGamma L hN ⟨b, hb⟩).injective]
    set β : MulAut ↥P₀ :=
      ((ggGamma L hN ⟨b, hb⟩).subgroupMap P₀).trans (MulEquiv.subgroupCongr hγeq) with hβ
    have hβcoe : ∀ z : ↥P₀, ((β z : ↥P₀) : ↥L) = ggGamma L hN ⟨b, hb⟩ (z : ↥L) := by
      intro z
      rw [hβ]
      simp only [MulEquiv.trans_apply]
      rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]
    have hβSp : ((Sp : Subgroup ↥P₀)).map β.toMonoidHom = (Sp : Subgroup ↥P₀) :=
      Subgroup.characteristic_iff_map_eq.mp hSpchar β
    have hβSp' : ((Sp : Subgroup ↥P₀)).map (↑β : ↥P₀ →* ↥P₀) = (Sp : Subgroup ↥P₀) := hβSp
    have hQ₁ : ((Sp : Subgroup ↥P₀).map P₀.subtype).map
        (↑(ggGamma L hN ⟨b, hb⟩) : ↥L →* ↥L) = (Sp : Subgroup ↥P₀).map P₀.subtype := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        have hβz : (β z : ↥P₀) ∈ (Sp : Subgroup ↥P₀) := by
          rw [← hβSp']
          exact Subgroup.mem_map_of_mem _ hz
        show (ggGamma L hN ⟨b, hb⟩) ((z : ↥P₀) : ↥L) ∈ (Sp : Subgroup ↥P₀).map P₀.subtype
        rw [← hβcoe z]
        exact Subgroup.mem_map_of_mem _ hβz
      · rintro _ ⟨z, hz, rfl⟩
        have h1 : z ∈ ((Sp : Subgroup ↥P₀)).map (↑β : ↥P₀ →* ↥P₀) := by
          rw [hβSp']; exact hz
        obtain ⟨z', hz', rfl⟩ := h1
        refine Subgroup.mem_map.mpr
          ⟨(z' : ↥L), Subgroup.mem_map.mpr ⟨z', hz', rfl⟩, ?_⟩
        show (ggGamma L hN ⟨b, hb⟩) ((z' : ↥P₀) : ↥L) = ((β z' : ↥P₀) : ↥L)
        rw [hβcoe z']
    have hcomp2 : (↑(MulAut.conj b) : G →* G).comp L.subtype =
        L.subtype.comp (↑(ggGamma L hN ⟨b, hb⟩) : ↥L →* ↥L) := by
      ext y
      show b * (y : G) * b⁻¹ = ((ggGamma L hN ⟨b, hb⟩ y : ↥L) : G)
      rw [ggGamma_coe]
    rw [Subgroup.map_map, hcomp2, ← Subgroup.map_map, hQ₁]
  · intro hScent
    have hmem : (⟨⟨eichler Q v x, hxmem⟩, hxu⟩ : ↥U) ∈ (Sp : Subgroup ↥P₀).map φ := by
      rw [hSpmapφ]
      exact Subgroup.mem_top _
    obtain ⟨z, hz, hzφ⟩ := hmem
    have hz1 : ψ (z : ↥L) ≠ 1 := by
      intro h
      apply hu₀ne
      have h2 : (φ z : ↥(orthDerived Q)) = ⟨eichler Q v x, hxmem⟩ := by rw [hzφ]
      rw [← h2]
      exact h
    have hzG : (z : G) ∈ Subgroup.centralizer (L : Set G) :=
      hScent (Subgroup.mem_map.mpr ⟨(z : ↥L), Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩)
    have hzc : (z : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      refine Subtype.ext ?_
      have h2 := Subgroup.mem_centralizer_iff.mp hzG (l : G) l.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact h2
    have hz1' : ψ (z : ↥L) = 1 := by
      rw [← MonoidHom.mem_ker, hψker]
      exact hzc
    exact hz1 hz1'

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement
