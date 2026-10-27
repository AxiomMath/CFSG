module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporCore
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporArith

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

section Centre

variable {A : Type} [Group A] (L : Subgroup A)

@[expose] def zOf : Subgroup A := (Subgroup.center ↥L).map L.subtype

variable {L}

theorem mem_zOf {x : A} : x ∈ zOf L ↔ ∃ h : x ∈ L, (⟨x, h⟩ : ↥L) ∈ Subgroup.center ↥L := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨x, h⟩, hc, rfl⟩

theorem card_zOf : Nat.card (zOf L) = Nat.card (Subgroup.center ↥L) :=
  Nat.card_congr (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).toEquiv.symm

theorem zOf_normal (hL : L.Normal) : (zOf L).Normal := by
  have := hL
  exact ConjAct.normal_of_characteristic_of_normal

theorem inf_eq_bot_of_card_dvd_three {S Z : Subgroup A} {q : ℕ} [hq : Fact q.Prime] (hq3 : q ≠ 3)
    (hZ : Nat.card Z = 1 ∨ Nat.card Z = 3) (hS : IsPGroup q S) : S ⊓ Z = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := hS ⟨x, hx.1⟩
  have hxk : x ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ q ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h2 : orderOf x ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hx.2
  have h3 : orderOf x ∣ 3 := by
    rcases hZ with h | h
    · rw [h] at h2; exact h2.trans (one_dvd _)
    · rwa [h] at h2
  have hcop : Nat.Coprime 3 (q ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hq.out).mpr (Ne.symm hq3))
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h1)

theorem eq_of_pow_eq_one_of_mem {Z : Subgroup A} {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    (hZ : Nat.card Z = 1 ∨ Nat.card Z = 3) {x y : A} (hxy : x⁻¹ * y ∈ Z)
    (hc : Commute x (x⁻¹ * y)) (hx : x ^ p = 1) (hy : y ^ p = 1) : x = y := by
  have h1 : y = x * (x⁻¹ * y) := by group
  have hz : (x⁻¹ * y) ^ p = 1 := by
    rw [h1, hc.mul_pow, hx, one_mul] at hy
    exact hy
  have h2 : orderOf (x⁻¹ * y) ∣ p := orderOf_dvd_of_pow_eq_one hz
  have h3 : orderOf (x⁻¹ * y) ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hxy
  have h4 : orderOf (x⁻¹ * y) ∣ 3 := by
    rcases hZ with h | h
    · rw [h] at h3; exact h3.trans (one_dvd _)
    · rwa [h] at h3
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp.out Nat.prime_three).mpr hp3
  have h5 : orderOf (x⁻¹ * y) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h4
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h5)

theorem injOn_of_inf_eq_bot {Z S : Subgroup A} [Z.Normal] (h : S ⊓ Z = ⊥) :
    ∀ x ∈ S, ∀ y ∈ S, QuotientGroup.mk' Z x = QuotientGroup.mk' Z y → x = y := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ Z := QuotientGroup.eq.mp hxy
  have h3 : x⁻¹ * y ∈ S ⊓ Z := ⟨S.mul_mem (S.inv_mem hx) hy, h1⟩
  rw [h, Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp h3

theorem index_odd_of_isSylowTwoOf_top {S : Subgroup A} (h : IsSylowTwoOf S ⊤) : ¬ 2 ∣ S.index := by
  have := h.2.2
  rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this

theorem commutator_self_le (P : Subgroup A) : ⁅P, P⁆ ≤ P :=
  Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hg₁ hg₂) (P.inv_mem hg₁)) (P.inv_mem hg₂)

end Centre

section Descent

variable {A : Type} [Group A] [Finite A] {p : ℕ} {L P T : Subgroup A}

theorem OddCfg.descend [hp : Fact p.Prime] (hp5 : 5 ≤ p) (h : OddCfg p L P T)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) :
    ∃ (A' : Type) (_ : Group A') (_ : Finite A') (L' P' T' : Subgroup A'),
      OddCfg p L' P' T' ∧ Nonempty (↥L' ≃* (↥L ⧸ Subgroup.center ↥L)) ∧
        Nat.card P' = Nat.card P ∧ (AutCyclic T' P' → AutCyclic T P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := h.normal
  have hZn : (zOf L).Normal := zOf_normal hLn
  have hZc : Nat.card (zOf L) = 1 ∨ Nat.card (zOf L) = 3 := by rwa [card_zOf]
  set Z := zOf L with hZdef
  let π : A →* A ⧸ Z := QuotientGroup.mk' Z
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hPZ : P ⊓ Z = ⊥ := inf_eq_bot_of_card_dvd_three (by omega) hZc h.isPGroup
  have hinjP := injOn_of_inf_eq_bot hPZ
  have hcardP : Nat.card (P.map π) = Nat.card P := card_map_of_injOn π P hinjP
  have hmapN : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), π t ∈ T.map π ⊓
      Subgroup.normalizer ((P.map π : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)) := by
    rintro t ⟨htT, htN⟩
    refine ⟨⟨t, htT, rfl⟩, Subgroup.mem_normalizer_fintype ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN x).mp hx, by simp⟩
  refine ⟨A ⧸ Z, inferInstance, inferInstance, L.map π, P.map π, T.map π, ?_, ?_, hcardP, ?_⟩
  ·
    refine ⟨Subgroup.Normal.map hLn π hπs, Subgroup.map_mono h.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, h.exp x hx, map_one]
    · rw [hcardP]; exact h.card
    · intro h3
      rw [hcardP] at h3
      obtain ⟨a, ha, b, hb, hab⟩ := h.nonab h3
      refine ⟨π a, ⟨a, ha, rfl⟩, π b, ⟨b, hb, rfl⟩, fun hc => hab ?_⟩
      rw [← map_mul, ← map_mul] at hc
      exact hinjP _ (P.mul_mem ha hb) _ (P.mul_mem hb ha) hc
    · exact isSylowTwoOf_top_of (h.sylow.2.1.map π) fun hd =>
        index_odd_of_isSylowTwoOf_top h.sylow (hd.trans (Subgroup.index_map_dvd T hπs))
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht x hx
      exact ⟨π y, ⟨y, hy, rfl⟩, π s, ⟨s, hs, rfl⟩, by rw [← map_mul, ← map_mul, he]⟩
    · intro U' hcomm hUP hN
      set U : Subgroup A := P ⊓ U'.comap π with hUdef
      have hcommP : ⁅P, P⁆ ≤ U := by
        refine le_inf (commutator_self_le P) ?_
        rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
        exact hcomm
      have hNU : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (U : Set A) := by
        intro t ht
        obtain ⟨htT, htN⟩ := ht
        have hπN := hN (hmapN t ⟨htT, htN⟩)
        refine Subgroup.mem_normalizer_fintype fun u hu => ?_
        refine ⟨(Subgroup.mem_normalizer_iff.mp htN u).mp hu.1, ?_⟩
        show π (t * u * t⁻¹) ∈ U'
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hπN (π u)).mp hu.2
      have hU' : U.map π = U' := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨u, hu, rfl⟩
          exact hu.2
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := hUP hy
          exact ⟨x, ⟨hx, hy⟩, rfl⟩
      rcases h.irred U hcommP inf_le_left hNU with hU | hU
      · left
        rw [← hU', hU, Subgroup.map_commutator]
      · right
        rw [← hU', hU]
  ·
    let φ : ↥L →* A ⧸ Z := π.comp L.subtype
    have hker : φ.ker = Subgroup.center ↥L := by
      ext x
      rw [MonoidHom.mem_ker]
      change π x = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zOf]
      exact ⟨fun ⟨hx, hc⟩ => hc, fun hc => ⟨x.2, hc⟩⟩
    have hrange : φ.range = L.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
      ((QuotientGroup.quotientKerEquivRange φ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker))).symm.symm⟩
  ·
    rintro ⟨c', hc'mem, hc'⟩
    obtain ⟨⟨c, hcT, rfl⟩, hcN⟩ := hc'mem
    have hcP : c ∈ Subgroup.normalizer (P : Set A) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨x₁, hx₁, hx₁'⟩ := (Subgroup.mem_normalizer_iff.mp hcN (π x)).mp ⟨x, hx, rfl⟩
      have hπ : π x₁ = π (c * x * c⁻¹) := by rw [hx₁']; simp
      have hz : x₁⁻¹ * (c * x * c⁻¹) ∈ Z := QuotientGroup.eq.mp hπ
      obtain ⟨hzL, hzc⟩ := mem_zOf.mp hz
      have hcomm : Commute x₁ (x₁⁻¹ * (c * x * c⁻¹)) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨x₁, h.le hx₁⟩)
      have hy : (c * x * c⁻¹) ^ p = 1 := by
        rw [conj_pow, h.exp x hx]; group
      rw [← eq_of_pow_eq_one_of_mem (Z := Z) (by omega) hZc hz hcomm (h.exp x₁ hx₁) hy]
      exact hx₁
    refine ⟨c, ⟨hcT, hcP⟩, fun s hs => ?_⟩
    obtain ⟨k, hk⟩ := hc' (π s) (hmapN s hs)
    refine ⟨k, fun x hx => ?_⟩
    have h1 : π (s * x * s⁻¹) = π (c ^ k * x * (c ^ k)⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_pow]
      exact hk (π x) ⟨x, hx, rfl⟩
    have hs1 : s * x * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hs.2 x).mp hx
    have hc1 : c ^ k * x * (c ^ k)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hcP k) x).mp hx
    exact hinjP _ hs1 _ hc1 h1

end Descent

end CFSG.Quasithin.H13.NQCore
