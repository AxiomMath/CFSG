module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralSectionBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSectionCharacteristic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCount

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_conj_mem_of_characteristic {A : Subgroup G} {R : Subgroup A}
    (hR : R.Characteristic) {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) {n : G}
    (hn : n ∈ R.map A.subtype) : g * n * g⁻¹ ∈ R.map A.subtype := by
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hn
  let σ := A.normalizerMonoidHom ⟨g, hg⟩
  have hσ : σ r ∈ R := by
    have := (Subgroup.characteristic_iff_comap_eq.mp hR σ).symm ▸ hr
    exact this
  refine Subgroup.mem_map.mpr ⟨σ r, hσ, ?_⟩
  exact Subgroup.normalizerMonoidHom_apply_apply_coe A ⟨g, hg⟩ r

omit [Finite G] in
theorem isElementaryAbelian_subgroupOf {E A : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsElementaryAbelian 2 (E.subgroupOf A) :=
  { toIsMulCommutative := isMulCommutative_iff.mpr fun a b => Subtype.ext (Subtype.ext (by
      have h := isMulCommutative_iff.mp hE.1 ⟨(a : G), a.2⟩ ⟨(b : G), b.2⟩
      simpa using congrArg Subtype.val h))
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      Subtype.ext (Subtype.ext (hE.2 (a : G) a.2)) }

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem section_inf_J
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    A ⊓ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) = ⊥ := by
  obtain ⟨hAH, hAN, hQA, hAM, hAQ, hA2⟩ := d.section_basic hA
  obtain ⟨-, hAn, hQltA, -, hmin, hcomm, hsq⟩ := hA
  obtain ⟨hQH, hQn, hQ, hQ4, ⟨e, hQe⟩, hBH, hXB, hXK, hXcyc, hXcard, -⟩ := d.point_data
  obtain ⟨hJeq, -, hJB, hJM, -, -, hQJ, hJQ, -⟩ := d.core_data
  obtain ⟨-, hEA, -, hord⟩ := d.J_data
  by_contra hT
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set J := Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)
    with hJdef
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  have hXN : X ≤ Subgroup.normalizer (A : Set G) := (hXB.trans hBH).trans hAN
  let φ : X →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  have hφ : ∀ (x : X) (a : A), ((φ x a : A) : G) = (x : G) * a * (x : G)⁻¹ := fun x a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe A _ a
  let Q' : Subgroup A := Q.subgroupOf A
  let T' : Subgroup A := J.subgroupOf A
  have hQ'Z : Q' ≤ Subgroup.center A := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hAQ a a.2 y hy)
  have : Q'.Normal := Subgroup.normal_of_le_center hQ'Z
  have hQ'el : IsElementaryAbelian 2 Q' := isElementaryAbelian_subgroupOf hQ
  have hQ'card : Nat.card Q' = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv
  have hAQel : IsElementaryAbelian 2 (A ⧸ Q') :=
    { toIsMulCommutative := isMulCommutative_iff.mpr fun u v => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ Q := hcomm a a.2 b (hAM b.2)
        have hab : ((a : G) * b) * ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)⁻¹ =
            ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)⁻¹ * ((a : G) * b) :=
          hAQ _ (mul_mem a.2 b.2) _ (inv_mem hc)
        change (((a * b)⁻¹ * (b * a) : A) : G) ∈ Q
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        have : ((a : G) * b)⁻¹ * (b * a) = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)⁻¹ := by
          calc ((a : G) * b)⁻¹ * (b * a) = ((a : G) * b)⁻¹ *
                (((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)⁻¹ * ((a : G) * b)) := by group
            _ = ((a : G) * b)⁻¹ *
                (((a : G) * b) * ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)⁻¹) := by rw [hab]
            _ = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem hc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hsq a a.2 }
  have hφQ : ∀ x : X, Q'.map (φ x).toMonoidHom = Q' := by
    intro x
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      change ((φ x a : A) : G) ∈ Q
      rw [hφ]
      have := hQn.conj_mem ⟨a, hQH ha⟩ ha ⟨x, hBH (hXB x.2)⟩
      exact this
    · intro a ha
      refine ⟨(φ x)⁻¹ a, ?_, by simp⟩
      change (((φ x⁻¹) a : A) : G) ∈ Q
      rw [hφ]
      have := hQn.conj_mem ⟨a, hQH ha⟩ ha ⟨(x⁻¹ : X), hBH (hXB (x⁻¹ : X).2)⟩
      exact this
  have hreg : ∀ a ∈ Q', a ≠ 1 → ∀ b ∈ Q', b ≠ 1 → ∃! x : X, φ x a = b := by
    intro a ha ha1 b hb hb1
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨x, hx, huniq⟩ := d.X_regular a ha ha1' b hb hb1'
    refine ⟨x, Subtype.ext ((hφ x a).trans hx), fun y hy => huniq y ?_⟩
    show (y : G) * a * (y : G)⁻¹ = b
    rw [← hφ]
    exact congrArg Subtype.val hy
  have hXne : ∃ x₀ : X, x₀ ≠ 1 := by
    have h1 : 1 < Nat.card X := by omega
    have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne (1 : X)
  obtain ⟨x₀, hx₀⟩ := hXne
  have hx₀' : (x₀ : G) ≠ 1 := fun h => hx₀ (Subtype.ext h)
  have hCx := d.section_centralizer_X hAM x₀.2 hx₀'
  have hT' : ∀ p : A, p ∈ T' ↔ ∀ x : X, φ x p = p := by
    intro p
    constructor
    · intro hp x
      apply Subtype.ext
      have hxp : (x : G) * (p : G) = (p : G) * (x : G) := d.X_commute_J x.2 hp
      rw [hφ, hxp, mul_inv_cancel_right]
    · intro hp
      have hpx : (p : G) ∈ A ⊓ Subgroup.centralizer ({(x₀ : G)} : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨p.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h := congrArg Subtype.val (hp x₀)
        rw [hφ] at h
        calc (p : G) * x₀ = (x₀ * p * (x₀ : G)⁻¹) * x₀ := by rw [h]
          _ = x₀ * p := by group
      rw [hCx] at hpx
      exact hpx.2
  have hT'bot : T' ≠ ⊥ := by
    intro h0
    apply hT
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, ha.1⟩ : A) ∈ T' := ha.2
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hT'el : IsElementaryAbelian 2 T' := isElementaryAbelian_subgroupOf hEA
  have hQT' : Q' ⊓ T' = ⊥ := by
    rw [eq_bot_iff]
    intro a ⟨haQ, haJ⟩
    have : (a : G) ∈ Q ⊓ J := ⟨haQ, haJ⟩
    rw [hQJ, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hCT : ∀ s ∈ T', s ≠ 1 → Subgroup.centralizer {s} = Q' ⊔ T' := by
    intro s hs hs1
    have hs1' : (s : G) ≠ 1 := fun h => hs1 (Subtype.ext h)
    have hC := d.section_centralizer_J hQA hAM hs hs1'
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hQA, inf_comm J A, ← hC]
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subgroup.mem_inf]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, congrArg Subtype.val ha⟩
    · rintro ⟨hgA, hg⟩
      exact ⟨⟨g, hgA⟩, Subtype.ext hg, rfl⟩
  have hinvA := (d.card_involutions hAH hAn hQA hAM).1
  have hT'card : Nat.card T' = Nat.card (A ⊓ J : Subgroup G) := by
    show Nat.card (J.subgroupOf A) = _
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have he2 : 2 ≤ e := by
    by_contra hlt
    have : e ≤ 1 := by omega
    have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have : IsCyclic X := hXcyc
  obtain ⟨-, -, ⟨R, -, -, hRchar, hQR, hRtop⟩, -⟩ :=
    CentralSection.singer_central_section_characteristic_abelian_subgroup (P := A) (X := X)
      hQe he2 hA2 hQ'Z hQ'el hQ'card hAQel hXcard φ hφQ hreg hT' hT'bot hT'el hQT' hCT
      (by rw [hinvA, hT'card])
  let N : Subgroup G := R.map A.subtype
  have hNA : N ≤ A := Subgroup.map_subtype_le R
  have hQN : Q ≤ N := by
    have h := Subgroup.map_mono (f := A.subtype) hQR.le
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQA] at h
  have hNn : (N.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact map_subtype_conj_mem_of_characteristic hRchar (hAN g.2) hn
  rcases hmin N (hNA.trans hAH) hNn hQN hNA with hNQ | hNA'
  · apply hQR.ne
    apply Subgroup.map_injective A.subtype_injective
    change Q'.map A.subtype = N
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQA, hNQ]
  · apply hRtop.ne
    apply Subgroup.map_injective A.subtype_injective
    change N = (⊤ : Subgroup A).map A.subtype
    rw [hNA', ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end FinalHyps

end CFSG.ShultStronglyClosedTI.FinalChain
