module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.S1567Z6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section QuotAct

variable {X : Type*} [Group X]

@[expose] noncomputable def quotPCoreAut (σ : MulAut X) : MulAut (X ⧸ CFSG.Open.pCore 2 X) :=
  QuotientGroup.congr (CFSG.Open.pCore 2 X) (CFSG.Open.pCore 2 X) σ
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 σ)

theorem quotPCoreAut_mk (σ : MulAut X) (x : X) :
    quotPCoreAut σ (QuotientGroup.mk x) = QuotientGroup.mk (σ x) :=
  QuotientGroup.congr_mk _ _ _ _ x

@[expose] noncomputable def quotPCoreHom : MulAut X →* MulAut (X ⧸ CFSG.Open.pCore 2 X) :=
  MonoidHom.mk' quotPCoreAut (by
    intro σ τ
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [quotPCoreAut_mk])

theorem eq_one_of_odd_of_card_two {H A : Type*} [Group H] [Group A] (hA : Nat.card A = 2)
    (φ : H →* A) {x : H} (hx : Odd (orderOf x)) : φ x = 1 := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hd1 : orderOf (φ x) ∣ orderOf x := orderOf_map_dvd φ x
  have hd2 : orderOf (φ x) ∣ 2 := by
    have := orderOf_dvd_natCard (φ x)
    rwa [hA] at this
  have hodd : Odd (orderOf (φ x)) := Odd.of_dvd_nat hx hd1
  have h1 : orderOf (φ x) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

end QuotAct

section Alpha

variable {G : Type} [Group G] (Y : Subgroup G)

@[expose] noncomputable def alphaHom :
    ↥(Subgroup.normalizer (Y : Set G)) →* MulAut (↥Y ⧸ CFSG.Open.pCore 2 ↥Y) :=
  quotPCoreHom.comp Y.normalizerMonoidHom

theorem alphaHom_mk {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) (y : ↥Y) :
    alphaHom Y ⟨g, hg⟩ (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩ := by
  unfold alphaHom quotPCoreHom
  rw [MonoidHom.comp_apply, MonoidHom.mk'_apply, quotPCoreAut_mk]
  congr 1

theorem mem_pCoreOf_iff (x : ↥Y) : (x : G) ∈ pCoreOf 2 Y ↔ x ∈ CFSG.Open.pCore 2 ↥Y :=
  CFSG.mem_openPCoreOf_iff_open x

theorem alphaHom_eq_one_iff {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    alphaHom Y ⟨g, hg⟩ = 1 ↔ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 Y := by
  constructor
  · intro h y hy
    have h1 := DFunLike.congr_fun h (QuotientGroup.mk ⟨y⁻¹, Y.inv_mem hy⟩)
    rw [alphaHom_mk, MulAut.one_apply, QuotientGroup.eq] at h1
    have h2 := (mem_pCoreOf_iff Y _).mpr h1
    simpa [mul_assoc] using h2
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [alphaHom_mk, MulAut.one_apply, QuotientGroup.eq]
      refine (mem_pCoreOf_iff Y _).mp ?_
      have := h (y : G)⁻¹ (Y.inv_mem y.2)
      simpa [mul_assoc] using this

end Alpha

section G0Facts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

@[expose] noncomputable def alpha153 (T Mc M E : Subgroup G) (s : G)
    (h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)) :
    ↥(G0_153 T Mc M E s) →*
      MulAut (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E)) :=
  (alphaHom (YE153 Mc M E)).comp (Subgroup.inclusion h1)

omit [Finite G] in
theorem alpha153_eq_one_iff {h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)}
    {g : G} (hg : g ∈ G0_153 T Mc M E s) :
    alpha153 T Mc M E s h1 ⟨g, hg⟩ = 1 ↔
      ∀ y ∈ YE153 Mc M E, g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 (YE153 Mc M E) :=
  alphaHom_eq_one_iff (YE153 Mc M E) (h1 hg)

theorem card_quot_YE (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) :
    Nat.card (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E)) = 3 := by
  obtain ⟨e⟩ := YE_quot h113 c L r66
  rw [Nat.card_congr e.toEquiv]
  simp

theorem card_mulAut_quot_YE (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) :
    Nat.card (MulAut (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E))) = 2 := by
  have hcard := card_quot_YE h113 c L r66
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E)) :=
    isCyclic_of_prime_card hcard
  have : Finite (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E)) :=
    Nat.finite_of_card_ne_zero (by omega)
  rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime Nat.prime_three]

theorem alpha153_eq_one_of_mem_centralizer_E (c : Ctx153 G T Mc M V₁ V₂ t)
    (r66 : Res15366B T Mc M V₁ V₂ E)
    {h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)} {q : G}
    (hq : q ∈ G0_153 T Mc M E s) (hqC : q ∈ Subgroup.centralizer (E : Set G)) :
    alpha153 T Mc M E s h1 ⟨q, hq⟩ = 1 := by
  rw [alpha153_eq_one_iff hq]
  intro y hy
  rw [pCoreOf_YE c r66]
  have hqN : q ∈ Subgroup.normalizer (YE153 Mc M E : Set G) := h1 hq
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hy
  refine ⟨?_, ?_⟩
  · have h2 : q * y * q⁻¹ ∈ YE153 Mc M E := (Subgroup.mem_normalizer_iff.mp hqN y).mp hy
    exact (YE153 Mc M E).mul_mem h2 ((YE153 Mc M E).inv_mem hy)
  · show q * y * q⁻¹ * y⁻¹ ∈ Subgroup.centralizer (E : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hqe : ∀ x ∈ E, Commute q x := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hqC x hx).symm
    have he₁ : y⁻¹ * e * y ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyE) e).mp he
    have hc₁ : q⁻¹ * (y⁻¹ * e * y) = (y⁻¹ * e * y) * q⁻¹ := (hqe _ he₁).inv_left.eq
    have h4 : q * e * q⁻¹ = e := by
      have := (hqe e he).eq
      calc q * e * q⁻¹ = (e * q) * q⁻¹ := by rw [this]
        _ = e := by group
    symm
    calc q * y * q⁻¹ * y⁻¹ * e
        = q * y * (q⁻¹ * (y⁻¹ * e * y)) * y⁻¹ := by group
      _ = q * y * ((y⁻¹ * e * y) * q⁻¹) * y⁻¹ := by rw [hc₁]
      _ = (q * e * q⁻¹) * (q * y * q⁻¹ * y⁻¹) := by group
      _ = e * (q * y * q⁻¹ * y⁻¹) := by rw [h4]

theorem exists_y_eps (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) :
    ∃ y ∈ YE153 Mc M E, ∃ hyN : y ∈ Subgroup.normalizer (E : Set G),
      conjAct E ⟨y, hyN⟩ ≠ 1 ∧ conjAct E ⟨y, hyN⟩ ^ 3 = 1 := by
  obtain ⟨-, y, hyYE, ⟨e₁, he₁E, hye₁⟩, hy3⟩ := Y_facts h113 c L
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := ((oTwoUpper_le _).trans inf_le_right) hyYE
  refine ⟨y, hyYE, hyN, fun h => ?_, ?_⟩
  · have h0 := (conjAct_eq_one_iff''' E ⟨y, hyN⟩).1 h
    apply hye₁
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e₁ he₁E
    rw [← h1]
    group
  · have hy3N : y ^ 3 ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hyN 3
    have e1 : conjAct E ⟨y, hyN⟩ ^ 3 = conjAct E ⟨y ^ 3, hy3N⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact Subgroup.centralizer_le L.le_V hy3

theorem mem_centralizer_E_of_alpha_eq_one (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    {h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)} {q : G}
    (hq : q ∈ G0_153 T Mc M E s) (hqT : q ∈ TE153 T E)
    (h : alpha153 T Mc M E s h1 ⟨q, hq⟩ = 1) : q ∈ Subgroup.centralizer (E : Set G) := by
  have := isKleinFour_E k.c k.L
  obtain ⟨y, hyY, hyN, hε1, hε3⟩ := exists_y_eps h113 k.c k.L
  have hqN : q ∈ Subgroup.normalizer (E : Set G) := hqT.2
  have hcomm : q * y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 (YE153 Mc M E) := (alpha153_eq_one_iff hq).mp h y hyY
  rw [pCoreOf_YE k.c k.r66] at hcomm
  have hmemN : q * y * q⁻¹ * y⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcomm.2
  have h0 : conjAct E ⟨q * y * q⁻¹ * y⁻¹, hmemN⟩ = 1 := (conjAct_eq_one_iff''' E _).2 hcomm.2
  have e : (⟨q * y * q⁻¹ * y⁻¹, hmemN⟩ : ↥(Subgroup.normalizer (E : Set G))) =
      ⟨q, hqN⟩ * ⟨y, hyN⟩ * ⟨q, hqN⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h0
  have hc : conjAct E ⟨y, hyN⟩ * conjAct E ⟨q, hqN⟩ = conjAct E ⟨q, hqN⟩ * conjAct E ⟨y, hyN⟩ := by
    have h2 : conjAct E ⟨q, hqN⟩ * conjAct E ⟨y, hyN⟩ * (conjAct E ⟨q, hqN⟩)⁻¹ =
        conjAct E ⟨y, hyN⟩ := mul_inv_eq_one.mp h0
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  obtain ⟨n, hn⟩ := k.r2.sylow_GE.2.1 ⟨q, hqT⟩
  have hqn : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hσn : conjAct E ⟨q, hqN⟩ ^ 2 ^ n = 1 := by
    have hqnN : q ^ 2 ^ n ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer _).pow_mem hqN _
    have e1 : conjAct E ⟨q, hqN⟩ ^ 2 ^ n = conjAct E ⟨q ^ 2 ^ n, hqnN⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    show q ^ 2 ^ n ∈ Subgroup.centralizer (E : Set G)
    rw [hqn]
    exact Subgroup.one_mem _
  have hσ1 := mulAut_eq_one_of_commute_two_pow (conjAct E ⟨y, hyN⟩) (conjAct E ⟨q, hqN⟩) hε1 hε3
    hc n hσn
  exact (conjAct_eq_one_iff''' E ⟨q, hqN⟩).1 hσ1

theorem exists_alpha153_ne_one (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)) :
    ∃ (τ : G) (hτ : τ ∈ G0_153 T Mc M E s), alpha153 T Mc M E s h1 ⟨τ, hτ⟩ ≠ 1 := by
  obtain ⟨τ, -, hτT, -, e, he, hmove⟩ := exists_tau k
  have hτG : τ ∈ G0_153 T Mc M E s :=
    ((le_sup_right : TE153 T E ≤ G1_153 T Mc M E s).trans le_sup_left) hτT
  refine ⟨τ, hτG, fun h => ?_⟩
  have hC := mem_centralizer_E_of_alpha_eq_one h113 k hτG hτT h
  apply hmove
  have := Subgroup.mem_centralizer_iff.mp hC e he
  calc τ * e * τ⁻¹ = (e * τ) * τ⁻¹ := by rw [this]
    _ = e := by group

theorem oTwoUpper_ne_top_of_pCore_le_centralizer (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t)
    (h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G))
    (h2 : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G))
    (h5 : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) =
      (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s)) :
    oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≠ ⊤ := by
  intro htop
  have hK : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≤ (alpha153 T Mc M E s h1).ker := by
    intro x hx
    rw [h5, Subgroup.mem_subgroupOf] at hx
    have := alpha153_eq_one_of_mem_centralizer_E k.c k.r66 (h1 := h1) x.2 (h2 hx)
    exact this
  let α' := QuotientGroup.lift (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (alpha153 T Mc M E s h1) hK
  have hcard := card_mulAut_quot_YE h113 k.c k.L k.r66
  have hker : (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤
      α'.ker := by
    rw [← htop]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact eq_one_of_odd_of_card_two hcard α' hx.2
  obtain ⟨τ, hτ, hne⟩ := exists_alpha153_ne_one h113 k h1
  apply hne
  have := hker (Subgroup.mem_top (QuotientGroup.mk (⟨τ, hτ⟩ : ↥(G0_153 T Mc M E s))))
  rw [MonoidHom.mem_ker] at this
  exact this

end G0Facts

end S1567

end CFSG.Quasithin
