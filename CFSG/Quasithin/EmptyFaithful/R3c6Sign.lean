module

public import CFSG.Quasithin.Background.A4Four
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.R3c6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section BD

variable {A : Type} [Group A]

structure BorelData (P Q : Subgroup A) : Prop where
  strong : ∀ U : Subgroup A, U ≤ Q → U ≠ ⊥ →
    Subgroup.normalizer (U : Set A) ⊓ P ≤ Subgroup.normalizer (Q : Set A)
  cyclic : ∀ R : Subgroup A, R ≤ P → R ≤ Subgroup.normalizer (Q : Set A) → IsPGroup 3 R →
    IsCyclic R
  elem : ∃ Z : Subgroup A, Z ≤ Q ∧ CFSG.IsElementaryAbelian 2 ↥Z ∧ 2 ^ 2 ≤ Nat.card Z

end BD

section Transport

variable {A : Type} [Group A]

theorem mem_map_subtype_iff {P : Subgroup A} {X : Subgroup ↥P} {y : ↥P} :
    (y : A) ∈ X.map P.subtype ↔ y ∈ X :=
  ⟨fun ⟨z, hz, hzy⟩ => by rwa [← Subtype.ext hzy], fun hy => ⟨y, hy, rfl⟩⟩

theorem mem_normalizer_map_subtype {P : Subgroup A} {X : Subgroup ↥P} {x : ↥P} :
    (x : A) ∈ Subgroup.normalizer ((X.map P.subtype : Subgroup A) : Set A) ↔
      x ∈ Subgroup.normalizer (X : Set ↥P) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (y : A)
    have e : (x : A) * y * (x : A)⁻¹ = ((x * y * x⁻¹ : ↥P) : A) := rfl
    rw [e, mem_map_subtype_iff, mem_map_subtype_iff] at h1
    exact h1
  · intro h a
    by_cases ha : a ∈ P
    · have h1 := h ⟨a, ha⟩
      have e : (x : A) * a * (x : A)⁻¹ = ((x * ⟨a, ha⟩ * x⁻¹ : ↥P) : A) := rfl
      rw [e]
      exact (mem_map_subtype_iff (y := ⟨a, ha⟩)).trans
        (h1.trans (mem_map_subtype_iff (y := x * ⟨a, ha⟩ * x⁻¹)).symm)
    · have h1 : a ∉ X.map P.subtype := fun hm => ha (by obtain ⟨y, -, rfl⟩ := hm; exact y.2)
      have h2 : (x : A) * a * (x : A)⁻¹ ∉ X.map P.subtype := fun hm => by
        obtain ⟨y, -, hy⟩ := hm
        apply ha
        have hy' : (y : A) = (x : A) * a * (x : A)⁻¹ := hy
        have : a = (x : A)⁻¹ * (y : A) * (x : A) := by rw [hy']; group
        rw [this]
        exact P.mul_mem (P.mul_mem (P.inv_mem x.2) y.2) x.2
      exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩

end Transport

section Conv

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElementaryAbelian_of_forall (Z : Subgroup G) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (he : ∀ a ∈ Z, a ^ 2 = 1) : CFSG.IsElementaryAbelian 2 ↥Z :=
  CFSG.IsElementaryAbelian.of_forall hc he

theorem borelData_of_components {A : Type} [Group A] {P : Subgroup A} {Q' : Subgroup ↥P}
    (hstrong : ∀ U : Subgroup ↥P, U ≤ Q' → U ≠ ⊥ →
      Subgroup.normalizer (U : Set ↥P) ≤ Subgroup.normalizer (Q' : Set ↥P))
    (hcyc : ∀ R : Subgroup ↥P, R ≤ Subgroup.normalizer (Q' : Set ↥P) → IsPGroup 3 ↥R →
      IsCyclic ↥R)
    (hZ : ∃ Z : Subgroup ↥P, Z ≤ Q' ∧ (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧ (∀ a ∈ Z, a ^ 2 = 1) ∧
      2 ^ 2 ≤ Nat.card Z) :
    BorelData P (Q'.map P.subtype) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U hUQ hU
    have hUP : U ≤ P := hUQ.trans (Subgroup.map_subtype_le Q')
    set U' : Subgroup ↥P := U.subgroupOf P with hU'
    have hUQ' : U' ≤ Q' := by
      intro u hu
      have : (u : A) ∈ Q'.map P.subtype := hUQ hu
      exact mem_map_subtype_iff.1 this
    have hU'ne : U' ≠ ⊥ := by
      intro h
      apply hU
      rw [eq_bot_iff]
      intro u hu
      have : (⟨u, hUP hu⟩ : ↥P) ∈ U' := hu
      rw [h] at this
      simpa using this
    have hle := hstrong U' hUQ' hU'ne
    rintro x ⟨hxU, hxP⟩
    have hxn : (⟨x, hxP⟩ : ↥P) ∈ Subgroup.normalizer (U' : Set ↥P) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact Subgroup.mem_normalizer_iff.1 hxU (y : A)
    exact mem_normalizer_map_subtype.2 (hle hxn)
  · intro R hRP hRN hR3
    set R' : Subgroup ↥P := R.subgroupOf P with hR'
    have hR'N : R' ≤ Subgroup.normalizer (Q' : Set ↥P) := by
      intro r hr
      exact mem_normalizer_map_subtype.1 (hRN hr)
    have hR'3 : IsPGroup 3 ↥R' := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRP).symm
    have hc := hcyc R' hR'N hR'3
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hRP).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRP).symm.injective
  · obtain ⟨Z, hZQ, hZc, hZe, hZcard⟩ := hZ
    refine ⟨Z.map P.subtype, Subgroup.map_mono hZQ, ?_, ?_⟩
    · refine isElementaryAbelian_of_forall _ ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        show (a : A) * b = b * a
        exact congrArg Subtype.val (hZc a ha b hb)
      · rintro _ ⟨a, ha, rfl⟩
        show (a : A) ^ 2 = 1
        exact congrArg Subtype.val (hZe a ha)
    · rw [Subgroup.card_map_of_injective P.subtype_injective]
      exact hZcard

end Conv

section Core

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem exists_sylow_of_isSylowTwoOf' {Q P : Subgroup A} (h : IsSylowTwoOf Q P) :
    ∃ S : Sylow 2 ↥P, (S : Subgroup ↥P) = Q.subgroupOf P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Q.subgroupOf P) := h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  exact ⟨hp.toSylow h.2.2, rfl⟩

omit [Finite A] in
theorem le_of_isSylowTwoOf {Q P X : Subgroup A} (hQ : IsSylowTwoOf Q P) (hXP : X ≤ P)
    (hX : IsPGroup 2 X) (hQX : Q ≤ X) : X ≤ Q := by
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowTwoOf' hQ
  have hX' : IsPGroup 2 (X.subgroupOf P) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXP).symm
  have hle : (S : Subgroup ↥P) ≤ X.subgroupOf P := by
    rw [hS]
    exact Subgroup.comap_mono hQX
  have h1 := S.is_maximal' hX' hle
  intro x hx
  have hxP : x ∈ P := hXP hx
  have hx' : (⟨x, hxP⟩ : ↥P) ∈ X.subgroupOf P := hx
  rw [h1] at hx'
  have hx'' : (⟨x, hxP⟩ : ↥P) ∈ (S : Subgroup ↥P) := hx'
  rw [hS] at hx''
  exact hx''

omit [Finite A] in
theorem isPGroup_three_of_pCoreOf_eq_bot {Y : Subgroup A} (hY : pCoreOf 2 Y = ⊥)
    (h3 : IsPGroup 3 (OTwoQuot Y)) : IsPGroup 3 ↥Y := by
  have h0 : CFSG.Open.pCore 2 ↥Y = ⊥ := by
    unfold pCoreOf at hY
    exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 hY
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', h0]
  exact h3.of_injective _ hinj

omit [Finite A] in
theorem le_of_forall_inf_centralizer_le' [Finite A] {p : ℕ} [Fact p.Prime] {B V W : Subgroup A}
    (hB : CFSG.IsElementaryAbelian p ↥B) (hBcard : p ^ 2 ≤ Nat.card B) (hpV : ¬ p ∣ Nat.card V)
    (hBV : B ≤ Subgroup.normalizer (V : Set A))
    (hle : ∀ b ∈ B, b ≠ 1 → V ⊓ Subgroup.centralizer ({b} : Set A) ≤ W) : V ≤ W := by
  let : MulDistribMulAction B V := MulDistribMulAction.compHom V (Subgroup.inclusion hBV)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := B) (H := V) hBcard hpV
  have hle' : (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) ≤
      W.comap V.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro v hv
    have hfix : a • v = v :=
      (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a v).mp hv
    have hc : (a : A) * v * (a : A)⁻¹ = v := congrArg Subtype.val hfix
    have hcomm : (v : A) ∈ Subgroup.centralizer ({(a : A)} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (v : A) * a = a * v * (a : A)⁻¹ * a := by rw [hc]
        _ = a * v := by group
    exact hle a a.2 (fun h => ha (Subtype.ext h)) ⟨v.2, hcomm⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : V) ∈
      (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle' hmem

omit [Finite A] in
theorem mem_normalizer_zpowers_of_commute {b x : A} (h : x * b = b * x) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup A) : Set A) := by
  have hcomm : Commute x b := h
  refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers b : Subgroup A) : Set A)
    (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact (hcomm.zpow_right k).symm.eq

theorem sign_of_borelData {P Q Y : Subgroup A} (hQ : IsSylowTwoOf Q P) (hB : BorelData P Q)
    (hYP : Y ≤ P) (hQY : Q ≤ Subgroup.normalizer (Y : Set A))
    (hY3 : IsPGroup 3 (OTwoQuot Y)) (hr : 2 ≤ CFSG.Open.pRank 3 Y) : False := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
  have hYN : Y ≤ Subgroup.normalizer (Q : Set A) := by
    by_cases hU : pCoreOf 2 Y = ⊥
    · have hY3' : IsPGroup 3 ↥Y := isPGroup_three_of_pCoreOf_eq_bot hU hY3
      obtain ⟨Z, hZQ, hZ, hZcard⟩ := hB.elem
      have hodd : ¬ 2 ∣ Nat.card Y := by
        obtain ⟨k, hk⟩ := hY3'.exists_card_eq
        rw [hk]
        intro h
        have h' := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
          (Nat.prime_two.dvd_of_dvd_pow h)
        omega
      refine le_of_forall_inf_centralizer_le'
        (p := 2) (B := Z) (V := Y) (W := Subgroup.normalizer (Q : Set A)) hZ hZcard hodd
        (fun z hz => hQY (hZQ hz)) ?_
      intro b hb hb1 x hx
      have hbQ : b ∈ Q := hZQ hb
      have hU1 : Subgroup.zpowers b ≠ ⊥ := fun h => hb1 (Subgroup.zpowers_eq_bot.1 h)
      have hUQ : Subgroup.zpowers b ≤ Q := Subgroup.zpowers_le.2 hbQ
      obtain ⟨hxY, hxC⟩ := hx
      have hxc : x * b = b * x := by
        have := Subgroup.mem_centralizer_iff.1 hxC b (Set.mem_singleton b)
        exact this.symm
      exact hB.strong _ hUQ hU1 ⟨mem_normalizer_zpowers_of_commute hxc, hYP hxY⟩
    · set U := pCoreOf 2 Y with hUdef
      have hU2 : IsPGroup 2 ↥U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
      have hQU : Q ≤ Subgroup.normalizer (U : Set A) :=
        hQY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
      have hUP : U ≤ P := (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYP
      have hUQ : U ≤ Q :=
        (le_sup_left (a := U) (b := Q)).trans
          (le_of_isSylowTwoOf hQ (sup_le hUP hQ.1) (hU2.to_sup_of_normal_left' hQ2 hQU)
            le_sup_right)
      intro y hy
      exact hB.strong U hUQ hU ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hy, hYP hy⟩
  obtain ⟨E, hEY, hE, hcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := Y) (k := 2) hr
  have hEp : IsPGroup 3 ↥E := IsPGroup.of_card hcard
  have hcyc : IsCyclic ↥E := hB.cyclic E (hEY.trans hYP) (hEY.trans hYN) hEp
  obtain ⟨g, hg⟩ := hcyc.exists_ofOrder_eq_natCard
  have hg3 : g ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hE.2 g g.2, Subgroup.coe_one])
  have h9 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg, hcard] at h9
  have := Nat.le_of_dvd (by norm_num) h9
  norm_num at this

end Core

end CFSG.Quasithin.R3c6
