module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {J E : Subgroup G}

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma isPGroup_of_forall_pow_eq_one {H : Subgroup G} (h : ∀ x ∈ H, x ^ p = 1) :
    IsPGroup p H := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by simpa using h x x.2)

omit [Finite G] in
private lemma le_normalizer_of_forall_inner
    (hinn : ∀ e ∈ E, ∃ x ∈ J, ∀ y ∈ J, e * y * e⁻¹ = x * y * x⁻¹) :
    E ≤ Subgroup.normalizer (J : Set G) := by
  intro e he
  obtain ⟨x, hx, hxe⟩ := hinn e he
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hxe y hy]
    exact J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)
  · intro hy
    have hz : x⁻¹ * (e * y * e⁻¹) * x ∈ J :=
      J.mul_mem (J.mul_mem (J.inv_mem hx) hy) hx
    have h1 : e * (x⁻¹ * (e * y * e⁻¹) * x) * e⁻¹ = e * y * e⁻¹ := by
      rw [hxe _ hz]
      group
    have hzy : x⁻¹ * (e * y * e⁻¹) * x = y := by
      have h2 := mul_right_cancel h1
      exact mul_left_cancel h2
    rw [← hzy]
    exact hz

omit [Finite G] in
private lemma natCard_subgroupOf_eq {H K : Subgroup G} :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Subgroup.subgroupOf_map_subtype H K, Subgroup.card_map_of_injective K.subtype_injective]

omit [Finite G] in
private lemma map_center_eq_inf_centralizer :
    (Subgroup.center J).map J.subtype = J ⊓ Subgroup.centralizer (J : Set G) := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    exact congrArg Subtype.val ((Subgroup.mem_center_iff (G := J)).mp hz ⟨h, hh⟩)
  · rintro ⟨hgJ, hgc⟩
    refine ⟨⟨g, hgJ⟩, (Subgroup.mem_center_iff (G := J)).mpr fun y => ?_, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.mp hgc (y : G) y.2

omit [Finite G] in
private lemma natCard_center_eq_natCard_inf_centralizer :
    Nat.card (Subgroup.center J) =
      Nat.card (J ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) := by
  rw [← map_center_eq_inf_centralizer, Subgroup.card_subtype]

omit [Finite G] in
private lemma exists_mul_mem_sup (hE_N : E ≤ Subgroup.normalizer (J : Set G)) {m : G}
    (hm : m ∈ E ⊔ J) : ∃ e ∈ E, ∃ j ∈ J, e * j = m := by
  have hmS : m ∈ (↑(E ⊔ J) : Set G) := hm
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E J hE_N] at hmS
  exact Set.mem_mul.mp hmS

omit [Finite G] in
private lemma exists_mul_mem_sup_of_le_centralizer {F A : Subgroup G}
    (hFc : F ≤ Subgroup.centralizer (J : Set G)) (hAJ : A ≤ J) {m : G}
    (hm : m ∈ F ⊔ A) : ∃ f ∈ F, ∃ a ∈ A, f * a = m := by
  have hFnA : F ≤ Subgroup.normalizer (A : Set G) :=
    hFc.trans ((Subgroup.centralizer_le fun x hx => hAJ hx).trans
      (Subgroup.centralizer_le_normalizer (A : Set G)))
  have hmS : m ∈ (↑(F ⊔ A) : Set G) := hm
  rw [Subgroup.coe_mul_of_left_le_normalizer_right F A hFnA] at hmS
  exact Set.mem_mul.mp hmS

omit [Finite G] in
private lemma exists_mem_inf_centralizer_of_mem_sup
    (hinn : ∀ e ∈ E, ∃ x ∈ J, ∀ y ∈ J, e * y * e⁻¹ = x * y * x⁻¹)
    {m : G} (hm : m ∈ E ⊔ J) :
    ∃ d ∈ (E ⊔ J) ⊓ Subgroup.centralizer (J : Set G), ∃ j ∈ J, d * j = m := by
  obtain ⟨e, he, j, hj, hje⟩ : ∃ e ∈ E, ∃ j ∈ J, e * j = m :=
    exists_mul_mem_sup (le_normalizer_of_forall_inner hinn) hm
  obtain ⟨x, hx, hxe⟩ := hinn e he
  refine ⟨e * x⁻¹, ⟨?_, ?_⟩, x * j, J.mul_mem hx hj, ?_⟩
  · exact (E ⊔ J).mul_mem (Subgroup.mem_sup_left he)
      ((E ⊔ J).inv_mem (Subgroup.mem_sup_right hx))
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hxy : x⁻¹ * y * x ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hx) hy) hx
    have h1 : e * x⁻¹ * y * x * e⁻¹ = y := by
      calc e * x⁻¹ * y * x * e⁻¹ = e * (x⁻¹ * y * x) * e⁻¹ := by group
        _ = x * (x⁻¹ * y * x) * x⁻¹ := hxe _ hxy
        _ = y := by group
    calc y * (e * x⁻¹) = (e * x⁻¹ * y * x * e⁻¹) * (e * x⁻¹) := by rw [h1]
      _ = (e * x⁻¹) * y := by group
  · calc e * x⁻¹ * (x * j) = e * j := by group
      _ = m := hje

omit [Finite G] in
private lemma surjective_inclusion_quotient [hN : (J.subgroupOf (E ⊔ J)).Normal]
    {K : Subgroup G} (hKM : K ≤ E ⊔ J)
    (hcover : ∀ m ∈ E ⊔ J, ∃ k ∈ K, ∃ j ∈ J, k * j = m) :
    Function.Surjective
      ((QuotientGroup.mk' (J.subgroupOf (E ⊔ J))).comp (Subgroup.inclusion hKM)) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (J.subgroupOf (E ⊔ J)) q
  obtain ⟨k, hk, j, hj, hkj⟩ := hcover m m.2
  refine ⟨⟨k, hk⟩, ?_⟩
  have hj1 : QuotientGroup.mk' (J.subgroupOf (E ⊔ J)) ⟨j, Subgroup.mem_sup_right hj⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hj
  have hmk : (m : ↥(E ⊔ J)) = ⟨k, hKM hk⟩ * ⟨j, Subgroup.mem_sup_right hj⟩ := by
    ext
    exact hkj.symm
  show QuotientGroup.mk' (J.subgroupOf (E ⊔ J)) ⟨k, hKM hk⟩
    = QuotientGroup.mk' (J.subgroupOf (E ⊔ J)) m
  rw [hmk, map_mul, hj1, mul_one]

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma quotient_isMulCommutative_and_pow_eq_one
    (hE_N : E ≤ Subgroup.normalizer (J : Set G))
    (hEc : IsMulCommutative E) (hEp : ∀ e ∈ E, e ^ p = 1)
    [hN : (J.subgroupOf (E ⊔ J)).Normal] :
    IsMulCommutative (↥(E ⊔ J) ⧸ J.subgroupOf (E ⊔ J)) ∧
      (∀ x : ↥(E ⊔ J) ⧸ J.subgroupOf (E ⊔ J), x ^ p = 1) := by
  have hπsurj : Function.Surjective ((QuotientGroup.mk' (J.subgroupOf (E ⊔ J))).comp
      (Subgroup.inclusion (le_sup_left : E ≤ E ⊔ J))) :=
    surjective_inclusion_quotient le_sup_left
      (fun m hm => exists_mul_mem_sup hE_N hm)
  constructor
  · rw [isMulCommutative_iff]
    intro x y
    obtain ⟨a, ha⟩ := hπsurj x
    obtain ⟨b, hb⟩ := hπsurj y
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg _ (isMulCommutative_iff.mp hEc a b)
  · intro x
    obtain ⟨a, ha⟩ := hπsurj x
    rw [← ha, ← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hEp (a : G) a.2),
      map_one]

private lemma natCard_quotient_sup_eq (hE_N : E ≤ Subgroup.normalizer (J : Set G))
    [hN : (J.subgroupOf (E ⊔ J)).Normal] :
    Nat.card (↥(E ⊔ J) ⧸ J.subgroupOf (E ⊔ J)) = Nat.card (↥E ⧸ J.subgroupOf E) := by
  have hπsurj := surjective_inclusion_quotient (K := E) le_sup_left
    (fun m hm => exists_mul_mem_sup hE_N hm)
  have hker : ((QuotientGroup.mk' (J.subgroupOf (E ⊔ J))).comp
      (Subgroup.inclusion (le_sup_left : E ≤ E ⊔ J))).ker = J.subgroupOf E := by
    ext e
    have hfe : ((QuotientGroup.mk' (J.subgroupOf (E ⊔ J))).comp
        (Subgroup.inclusion (le_sup_left : E ≤ E ⊔ J))) e
        = QuotientGroup.mk' (J.subgroupOf (E ⊔ J)) ⟨e, Subgroup.mem_sup_left e.2⟩ := rfl
    rw [MonoidHom.mem_ker, hfe, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have h1 : Nat.card (J.subgroupOf E) * Nat.card (↥(E ⊔ J) ⧸ J.subgroupOf (E ⊔ J))
      = Nat.card ↥E := by
    have := Subgroup.card_ker_mul_card_of_surjective
      (f := (QuotientGroup.mk' (J.subgroupOf (E ⊔ J))).comp
        (Subgroup.inclusion (le_sup_left : E ≤ E ⊔ J))) hπsurj
    rwa [hker] at this
  have h2 : Nat.card ↥E = Nat.card (↥E ⧸ J.subgroupOf E) * Nat.card (J.subgroupOf E) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (J.subgroupOf E)
  have hpos : 0 < Nat.card (J.subgroupOf E) := Nat.card_pos
  exact Nat.mul_left_cancel hpos (by rw [h1, h2, mul_comm (Nat.card (↥E ⧸ J.subgroupOf E))])

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma pow_mem_of_mem_sup [hN : (J.subgroupOf (E ⊔ J)).Normal]
    (hQexp : ∀ x : ↥(E ⊔ J) ⧸ J.subgroupOf (E ⊔ J), x ^ p = 1) {m : G} (hm : m ∈ E ⊔ J) :
    m ^ p ∈ J := by
  have h1 : QuotientGroup.mk' (J.subgroupOf (E ⊔ J)) ⟨m ^ p, (E ⊔ J).pow_mem hm p⟩ = 1 := by
    rw [show (⟨m ^ p, (E ⊔ J).pow_mem hm p⟩ : ↥(E ⊔ J)) = ⟨m, hm⟩ ^ p from rfl, map_pow]
    exact hQexp _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

omit [Finite G] in
private lemma commutator_mem_of_mem_sup [hN : (J.subgroupOf (E ⊔ J)).Normal]
    (hQcomm : IsMulCommutative (↥(E ⊔ J) ⧸ J.subgroupOf (E ⊔ J)))
    {m m' : G} (hm : m ∈ E ⊔ J) (hm' : m' ∈ E ⊔ J) :
    m * m' * m⁻¹ * m'⁻¹ ∈ J := by
  have hmem : m * m' * m⁻¹ * m'⁻¹ ∈ E ⊔ J :=
    (E ⊔ J).mul_mem ((E ⊔ J).mul_mem ((E ⊔ J).mul_mem hm hm')
      ((E ⊔ J).inv_mem hm)) ((E ⊔ J).inv_mem hm')
  have h1 : QuotientGroup.mk' (J.subgroupOf (E ⊔ J)) ⟨m * m' * m⁻¹ * m'⁻¹, hmem⟩ = 1 := by
    rw [show (⟨m * m' * m⁻¹ * m'⁻¹, hmem⟩ : ↥(E ⊔ J))
        = ⟨m, hm⟩ * ⟨m', hm'⟩ * ⟨m, hm⟩⁻¹ * ⟨m', hm'⟩⁻¹ from rfl]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : (QuotientGroup.mk' (J.subgroupOf (E ⊔ J))) ⟨m, hm⟩
        * (QuotientGroup.mk' (J.subgroupOf (E ⊔ J))) ⟨m', hm'⟩
        = (QuotientGroup.mk' (J.subgroupOf (E ⊔ J))) ⟨m', hm'⟩
          * (QuotientGroup.mk' (J.subgroupOf (E ⊔ J))) ⟨m, hm⟩ :=
      isMulCommutative_iff.mp hQcomm _ _
    rw [hc]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma isMulCommutative_and_pow_of_le_centralizer
    (hE_N : E ≤ Subgroup.normalizer (J : Set G))
    (hEc : IsMulCommutative E) (hEp : ∀ e ∈ E, e ^ p = 1)
    {F : Subgroup G} (hFJ : F ⊓ J = ⊥) (hFM : F ≤ E ⊔ J) :
    IsMulCommutative F ∧ ∀ x ∈ F, x ^ p = 1 := by
  have hN : (J.subgroupOf (E ⊔ J)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hE_N
  obtain ⟨hQcomm, hQexp⟩ :=
    quotient_isMulCommutative_and_pow_eq_one (J := J) (E := E) hE_N hEc hEp
  have hbot : ∀ x : G, x ∈ F → x ∈ J → x = 1 := by
    intro x hxF hxJ
    have h1 : x ∈ F ⊓ J := ⟨hxF, hxJ⟩
    rw [hFJ] at h1
    simpa using h1
  constructor
  · refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    have hJ := commutator_mem_of_mem_sup hQcomm (hFM a.2) (hFM b.2)
    have hF : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ F :=
      F.mul_mem (F.mul_mem (F.mul_mem a.2 b.2) (F.inv_mem a.2)) (F.inv_mem b.2)
    have hone : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = 1 := hbot _ hF hJ
    calc (a : G) * (b : G)
        = ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by group
      _ = (b : G) * (a : G) := by rw [hone, one_mul]
  · intro x hx
    exact hbot _ (F.pow_mem hx p) (pow_mem_of_mem_sup hQexp (hFM hx))

private lemma exists_subgroup_centralizer_card
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hinn : ∀ e ∈ E, ∃ x ∈ J, ∀ y ∈ J, e * y * e⁻¹ = x * y * x⁻¹) :
    ∃ F : Subgroup G, F ≤ Subgroup.centralizer (J : Set G) ∧ F ≤ E ⊔ J ∧ F ⊓ J = ⊥ ∧
      Nat.card F = Nat.card (↥E ⧸ J.subgroupOf E) := by
  have hE_N : E ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_forall_inner hinn
  have hne : (J.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hE_N
  have hN : (J.subgroupOf (E ⊔ J)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hE_N
  set D : Subgroup G := (E ⊔ J) ⊓ Subgroup.centralizer (J : Set G) with hD
  have hDM : D ≤ E ⊔ J := by rw [hD]; exact inf_le_left
  have hDc : D ≤ Subgroup.centralizer (J : Set G) := by rw [hD]; exact inf_le_right
  have hsurjD : Function.Surjective
      ((QuotientGroup.mk' (J.subgroupOf (E ⊔ J))).comp (Subgroup.inclusion hDM)) :=
    surjective_inclusion_quotient hDM fun m hm => exists_mem_inf_centralizer_of_mem_sup hinn hm
  have hEk : IsPGroup p (↥E ⧸ J.subgroupOf E) :=
    (isPGroup_of_forall_pow_eq_one hEp).to_quotient (J.subgroupOf E)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEk
  have hQcard : Nat.card (↥(E ⊔ J) ⧸ J.subgroupOf (E ⊔ J)) = Nat.card (↥E ⧸ J.subgroupOf E) :=
    natCard_quotient_sup_eq hE_N
  have hdvd : p ^ n ∣ Nat.card ↥D := by
    rw [← hn, ← hQcard]
    exact Subgroup.card_dvd_of_surjective hsurjD
  obtain ⟨P, hPcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥D) p hdvd
  set F : Subgroup G := P.map D.subtype with hF
  have hFD : F ≤ D := by rw [hF]; exact Subgroup.map_subtype_le (H := D) P
  have hFcard : Nat.card F = p ^ n := by rw [hF, Subgroup.card_subtype D P, hPcard]
  have hDJ : D ⊓ J = J ⊓ Subgroup.centralizer (J : Set G) := by
    rw [hD]
    ext x
    constructor
    · rintro ⟨⟨-, hc⟩, hJ⟩
      exact ⟨hJ, hc⟩
    · rintro ⟨hJ, hc⟩
      exact ⟨⟨Subgroup.mem_sup_right hJ, hc⟩, hJ⟩
  have hcardDJ : Nat.card (D ⊓ J : Subgroup G) = Nat.card (Subgroup.center J) := by
    rw [hDJ, ← natCard_center_eq_natCard_inf_centralizer]
  have hcop : Nat.Coprime (p ^ n) (Nat.card (D ⊓ J : Subgroup G)) := by
    rw [hcardDJ]
    exact (Nat.Prime.coprime_pow_of_not_dvd Fact.out hZ).symm
  have hdiv1 : Nat.card (F ⊓ J : Subgroup G) ∣ p ^ n := by
    rw [← hFcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdiv2 : Nat.card (F ⊓ J : Subgroup G) ∣ Nat.card (D ⊓ J : Subgroup G) :=
    Subgroup.card_dvd_of_le fun x hx => ⟨hFD hx.1, hx.2⟩
  have hFJ : F ⊓ J = ⊥ :=
    Subgroup.eq_bot_of_card_eq (F ⊓ J) (Nat.eq_one_of_dvd_coprimes hcop hdiv1 hdiv2)
  exact ⟨F, hFD.trans hDc, hFD.trans hDM, hFJ, by rw [hFcard, ← hn]⟩

theorem exists_centralizer_elemAbelian_of_forall_inner
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hEc : IsMulCommutative E)
    (hEp : ∀ e ∈ E, e ^ p = 1) (hinn : ∀ e ∈ E, ∃ x ∈ J, ∀ y ∈ J, e * y * e⁻¹ = x * y * x⁻¹) :
    ∃ F : Subgroup G, F ≤ Subgroup.centralizer (J : Set G) ∧ IsMulCommutative F ∧
      (∀ x ∈ F, x ^ p = 1) ∧ F ⊓ J = ⊥ ∧
        Nat.card E = Nat.card F * Nat.card (E ⊓ J : Subgroup G) := by
  have hE_N : E ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_forall_inner hinn
  have hne : (J.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hE_N
  have hN : (J.subgroupOf (E ⊔ J)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hE_N
  obtain ⟨F, hFc, hFM, hFJ, hFcard⟩ := exists_subgroup_centralizer_card hZ hEp hinn
  obtain ⟨hFcomm, hFexp⟩ :=
    isMulCommutative_and_pow_of_le_centralizer hE_N hEc hEp hFJ hFM
  refine ⟨F, hFc, hFcomm, hFexp, hFJ, ?_⟩
  have hsub : Nat.card (J.subgroupOf E) = Nat.card (E ⊓ J : Subgroup G) := by
    rw [natCard_subgroupOf_eq, inf_comm]
  have hEcard : Nat.card E = Nat.card (↥E ⧸ J.subgroupOf E) * Nat.card (J.subgroupOf E) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (J.subgroupOf E)
  calc Nat.card E = Nat.card (↥E ⧸ J.subgroupOf E) * Nat.card (J.subgroupOf E) := hEcard
    _ = Nat.card F * Nat.card (J.subgroupOf E) := by rw [hFcard]
    _ = Nat.card F * Nat.card (E ⊓ J : Subgroup G) := by rw [hsub]

omit [Finite G] in
private lemma isMulCommutative_sup_of_le_centralizer {F A : Subgroup G}
    (hFc : F ≤ Subgroup.centralizer (J : Set G)) (hAJ : A ≤ J)
    (hFcomm : IsMulCommutative F) (hAcomm : IsMulCommutative A) :
    IsMulCommutative (F ⊔ A : Subgroup G) := by
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨f, hf, a, ha, hx⟩ : ∃ f ∈ F, ∃ a ∈ A, f * a = (x : G) :=
    exists_mul_mem_sup_of_le_centralizer hFc hAJ x.2
  obtain ⟨f', hf', a', ha', hy⟩ : ∃ f' ∈ F, ∃ a' ∈ A, f' * a' = (y : G) :=
    exists_mul_mem_sup_of_le_centralizer hFc hAJ y.2
  have hFcA : F ≤ Subgroup.centralizer (A : Set G) :=
    hFc.trans (Subgroup.centralizer_le fun x hx => hAJ hx)
  have h1 : Commute f f' := (commute_iff_eq f f').mpr <| by
    simpa using congrArg Subtype.val (isMulCommutative_iff.mp hFcomm ⟨f, hf⟩ ⟨f', hf'⟩)
  have h2 : Commute f a' :=
    (commute_iff_eq f a').mpr ((Subgroup.mem_centralizer_iff.mp (hFcA hf)) a' ha').symm
  have h3 : Commute a f' :=
    (commute_iff_eq a f').mpr ((Subgroup.mem_centralizer_iff.mp (hFcA hf')) a ha)
  have h4 : Commute a a' := (commute_iff_eq a a').mpr <| by
    simpa using congrArg Subtype.val (isMulCommutative_iff.mp hAcomm ⟨a, ha⟩ ⟨a', ha'⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy]
  exact Commute.mul_left (h1.mul_right h2) (h3.mul_right h4)

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma pow_eq_one_of_mem_sup {F A : Subgroup G}
    (hFc : F ≤ Subgroup.centralizer (J : Set G)) (hAJ : A ≤ J)
    (hFexp : ∀ x ∈ F, x ^ p = 1) (hAexp : ∀ a ∈ A, a ^ p = 1) {x : G} (hx : x ∈ F ⊔ A) :
    x ^ p = 1 := by
  obtain ⟨f, hf, a, ha, hfx⟩ : ∃ f ∈ F, ∃ a ∈ A, f * a = x :=
    exists_mul_mem_sup_of_le_centralizer hFc hAJ hx
  have hFcA : F ≤ Subgroup.centralizer (A : Set G) :=
    hFc.trans (Subgroup.centralizer_le fun x hx => hAJ hx)
  have hcomm : Commute f a :=
    (commute_iff_eq f a).mpr ((Subgroup.mem_centralizer_iff.mp (hFcA hf)) a ha).symm
  rw [← hfx, hcomm.mul_pow, hFexp f hf, hAexp a ha, one_mul]

private lemma card_mul_le_card_sup {F A : Subgroup G} (hAJ : A ≤ J)
    (hFJ : F ⊓ J = ⊥) : Nat.card F * Nat.card A ≤ Nat.card (F ⊔ A : Subgroup G) := by
  have hFA : F ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ F ⊓ J := ⟨hx.1, hAJ hx.2⟩
    rw [hFJ] at hx'
    exact hx'
  have hinj : Function.Injective (fun x : ↥F × ↥A =>
      (⟨(x.1 : G) * (x.2 : G), Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(F ⊔ A))) := by
    rintro ⟨f, a⟩ ⟨f', a'⟩ h
    have hval : (f : G) * (a : G) = (f' : G) * (a' : G) := Subtype.ext_iff.mp h
    have hmem : (f : G)⁻¹ * (f' : G) ∈ F ⊓ A := by
      refine ⟨F.mul_mem (F.inv_mem f.2) f'.2, ?_⟩
      have hEq : (a : G) * (a' : G)⁻¹ = (f : G)⁻¹ * (f' : G) := by
        calc (a : G) * (a' : G)⁻¹ = (f : G)⁻¹ * ((f : G) * (a : G)) * (a' : G)⁻¹ := by group
          _ = (f : G)⁻¹ * ((f' : G) * (a' : G)) * (a' : G)⁻¹ := by rw [hval]
          _ = (f : G)⁻¹ * (f' : G) := by group
      rw [← hEq]
      exact A.mul_mem a.2 (A.inv_mem a'.2)
    rw [hFA] at hmem
    have hff' : f = f' := by
      have h2 : (f : G)⁻¹ * (f' : G) = 1 := by simpa using hmem
      exact Subtype.ext (inv_mul_eq_one.mp h2)
    have hff'' : (f : G) = (f' : G) := by rw [hff']
    have haa' : a = a' := by
      have h2 : (f : G) * (a : G) = (f : G) * (a' : G) := by
        calc (f : G) * (a : G) = (f' : G) * (a' : G) := hval
          _ = (f : G) * (a' : G) := by rw [← hff'']
      exact Subtype.ext (mul_left_cancel h2)
    exact Prod.ext hff' haa'
  calc Nat.card F * Nat.card A = Nat.card (↥F × ↥A) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card ↥(F ⊔ A) := Nat.card_le_card_of_injective _ hinj

theorem card_le_mul_card_inf_of_forall_inner {k : ℕ} {A : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) (hAJ : A ≤ J) (hAc : IsMulCommutative A)
    (hAp : ∀ a ∈ A, a ^ p = 1) (hAk : p ^ k ≤ Nat.card A)
    (hm : ∀ B : Subgroup G, IsMulCommutative B → (∀ b ∈ B, b ^ p = 1) → Nat.card B ≤ p ^ (k + 1))
    (hEc : IsMulCommutative E) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hinn : ∀ e ∈ E, ∃ x ∈ J, ∀ y ∈ J, e * y * e⁻¹ = x * y * x⁻¹) :
    Nat.card E ≤ p * Nat.card (E ⊓ J : Subgroup G) := by
  obtain ⟨F, hFc, hFcomm, hFexp, hFbot, hEcard⟩ :=
    exists_centralizer_elemAbelian_of_forall_inner hZ hEc hEp hinn
  have hBcomm : IsMulCommutative (F ⊔ A : Subgroup G) :=
    isMulCommutative_sup_of_le_centralizer hFc hAJ hFcomm hAc
  have hBexp : ∀ b ∈ F ⊔ A, b ^ p = 1 :=
    fun b hb => pow_eq_one_of_mem_sup hFc hAJ hFexp hAp hb
  have hBcard : Nat.card (F ⊔ A : Subgroup G) ≤ p ^ (k + 1) := hm _ hBcomm hBexp
  have hle : Nat.card F * Nat.card A ≤ Nat.card (F ⊔ A : Subgroup G) :=
    card_mul_le_card_sup hAJ hFbot
  have h1 : Nat.card F * p ^ k ≤ p ^ (k + 1) := by
    calc Nat.card F * p ^ k ≤ Nat.card F * Nat.card A := Nat.mul_le_mul_left _ hAk
      _ ≤ Nat.card (F ⊔ A : Subgroup G) := hle
      _ ≤ p ^ (k + 1) := hBcard
  rw [pow_succ, mul_comm (p ^ k) p] at h1
  have hF : Nat.card F ≤ p := Nat.le_of_mul_le_mul_right h1 (pow_pos (Fact.out : p.Prime).pos k)
  calc Nat.card E = Nat.card F * Nat.card (E ⊓ J : Subgroup G) := hEcard
    _ ≤ p * Nat.card (E ⊓ J : Subgroup G) := Nat.mul_le_mul_right _ hF

end CFSG
