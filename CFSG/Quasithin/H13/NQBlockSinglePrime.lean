module

public import CFSG.Quasithin.H13.NQBlockCanonicalWitnesses

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement Pointwise

theorem aut_eq_one_of_fixes_canonical {M : Type*} [Group M] [Finite M]
    (hSQT : CFSG.IsStronglyQuasithin M) (hO2 : CFSG.pCore 2 M = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup M)) (hq : ¬ CFSG.IsQuasisimple M) {p : ℕ}
    [hp : Fact p.Prime] (hpF : p ∈ (Nat.card (CFSG.fittingSubgroup M)).primeFactors)
    (hFQ : CFSG.fittingSubgroup M = CFSG.pCore p M) {α : MulAut M} {k : ℕ}
    (hα : α ^ 2 ^ k = 1) (hfix : ∀ a ∈ CFSG.pCore p M, a ^ p = 1 → α a = a) : α = 1 := by
  classical
  obtain ⟨-, -, hodd, hCF, -, -⟩ := odd_Fitting_cores_self hSQT hO2 hLC hq
  obtain ⟨-, hcrit⟩ := all_prime_critical_actions_self hSQT hO2 hLC hq
  obtain ⟨-, B, hBc, hB, -⟩ := hcrit p hpF
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hpF))
  set β : MulAut (CFSG.pCore p M) :=
    autRestrict (CFSG.pCore p M) (mem_of_characteristic (CFSG.pCore p M)) α with hβ
  have hβapp : ∀ q : CFSG.pCore p M, (β q : M) = α q := fun _ => rfl
  have hβB : β ∈ (frattiniAction B).ker := by
    rw [MonoidHom.mem_ker]
    ext w
    induction w using QuotientGroup.induction_on with
    | H b =>
      rw [frattiniAction_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      rw [hβapp]
      apply hfix _ ((b : CFSG.pCore p M)).2
      have h1 := hB.pow_eq_one (b : CFSG.pCore p M) b.2
      have h2 := congrArg Subtype.val h1
      rwa [SubgroupClass.coe_pow] at h2
  have hβ1 : β = 1 := by
    have hβk : (⟨β, hβB⟩ : (frattiniAction B).ker) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      show β ^ 2 ^ k = 1
      rw [hβ, ← map_pow, hα, map_one]
    obtain ⟨m, hm⟩ := hB.ker_isPGroup ⟨β, hβB⟩
    have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
      Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
    have h1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hβk) hcop)
      (orderOf_dvd_of_pow_eq_one hm)
    rw [orderOf_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hQfix : ∀ q ∈ CFSG.pCore p M, α q = q := by
    intro q hq
    have h1 := congrArg (fun σ : MulAut (CFSG.pCore p M) => ((σ ⟨q, hq⟩ : CFSG.pCore p M) : M))
      hβ1
    simpa [hβapp] using h1
  ext l
  rw [MulAut.one_apply]
  set c := l⁻¹ * α l with hc
  have hcQ : c ∈ CFSG.pCore p M := by
    rw [← hFQ]
    apply hCF
    rw [mem_centralizer_iff]
    intro f hf
    rw [hFQ] at hf
    have h1 : l * f * l⁻¹ ∈ CFSG.pCore p M :=
      (inferInstance : (CFSG.pCore p M).Normal).conj_mem f hf l
    have h2 := hQfix _ h1
    rw [map_mul, map_mul, map_inv, hQfix f hf] at h2
    rw [hc]
    calc f * (l⁻¹ * α l) = l⁻¹ * (l * f * l⁻¹) * α l := by group
      _ = l⁻¹ * (α l * f * (α l)⁻¹) * α l := by rw [h2]
      _ = l⁻¹ * α l * f := by group
  have hαc : α c = c := hQfix c hcQ
  have hlc : l * c = α l := by rw [hc, mul_inv_cancel_left]
  have hpow : ∀ j : ℕ, (α ^ j) l = l * c ^ j := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, mul_one, MulAut.one_apply]
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαc, pow_succ', ← mul_assoc, hlc]
  have hck : c ^ 2 ^ k = 1 := by
    have h1 := hpow (2 ^ k)
    rw [hα, MulAut.one_apply] at h1
    have h2 : l * c ^ 2 ^ k = l * 1 := by rw [← h1, mul_one]
    exact mul_left_cancel h2
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup p (CFSG.pCore p M)) ⟨c, hcQ⟩
  have hcm : c ^ p ^ m = 1 := by
    have h1 := congrArg Subtype.val hm
    rwa [SubgroupClass.coe_pow] at h1
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
  have h1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hck) hcop)
    (orderOf_dvd_of_pow_eq_one hcm)
  rw [orderOf_eq_one_iff, hc] at h1
  have h2 : α l = l := by
    have h3 : l * (l⁻¹ * α l) = l * 1 := by rw [h1]
    rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h3
  exact h2

theorem mem_normalizer_map_of_characteristic {G : Type*} [Group G] {L : Subgroup G}
    (C : Subgroup L) [C.Characteristic] {g : G} (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer ((C.map L.subtype : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (L : Set G), ∀ c ∈ C, g * (c : G) * g⁻¹ ∈ C.map L.subtype := by
    intro g hg c hc
    exact ⟨_, mem_of_characteristic C (L.normalizerMonoidHom ⟨g, hg⟩) c hc, rfl⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact key g hg c hc
  · rintro ⟨c, hc, hce⟩
    have h2 := key g⁻¹ (inv_mem hg) c hc
    have e : g⁻¹ * (c : G) * g⁻¹⁻¹ = h := by
      rw [show (c : G) = g * h * g⁻¹ from hce]
      group
    rwa [e] at h2

theorem le_of_isSylowOf_of_normalizes {G : Type*} [Group G] [Finite G] {A T H : Subgroup G}
    (hA : IsPGroup 2 A) (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) : A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := hT
  have hn : (A.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hAH).mpr hHA
  have hA' : IsPGroup 2 (A.subgroupOf H) := by
    rw [← comap_subtype]
    exact hA.comap_subtype
  have hle := hA'.le_sylow_of_normal S
  intro a ha
  exact ⟨⟨a, hAH ha⟩, hle (mem_subgroupOf.mpr ha), rfl⟩

theorem isSylowOf_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T K H : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf p T H) (hTK : T ≤ K) (hKH : K ≤ H) :
    CFSG.ABGLocalTools.IsSylowOf p T K := by
  obtain ⟨S, hS⟩ := hT
  have hTp : IsPGroup p T := hS ▸ S.isPGroup'.map _
  have hTH : T.subgroupOf H = S := by
    ext x
    rw [mem_subgroupOf, ← hS]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hidx : ¬ p ∣ (T.subgroupOf K).index := by
    change ¬ p ∣ T.relIndex K
    intro h
    have h1 := Subgroup.relIndex_mul_relIndex T K H hTK hKH
    have h2 : p ∣ T.relIndex H := h1 ▸ dvd_mul_of_dvd_left h _
    apply S.not_dvd_index
    change p ∣ (T.subgroupOf H).index at h2
    rwa [hTH] at h2
  have hTpK : IsPGroup p (T.subgroupOf K) := by
    rw [← comap_subtype]
    exact hTp.comap_subtype
  refine ⟨hTpK.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe, subgroupOf_map_subtype, inf_eq_left.mpr hTK]

theorem exists_isMaximalTwoLocal_le {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : CFSG.IsPLocal 2 H) : ∃ M : Subgroup G, CFSG.IsMaximalTwoLocal M ∧ H ≤ M := by
  obtain ⟨M, hM⟩ := Set.Finite.exists_maximal
    (s := {K : Subgroup G | CFSG.IsPLocal 2 K ∧ H ≤ K}) (Set.toFinite _) ⟨H, hH, le_rfl⟩
  exact ⟨M, ⟨hM.1.1, fun K hMK hK => (hMK.not_ge (hM.2 ⟨hK, hM.1.2.trans hMK.le⟩ hMK.le))⟩,
    hM.1.2⟩

theorem commutator_mem_two_core_of_mem_radical {G : Type*} [Group G] [Finite G]
    {L T : Subgroup G} (hTL : T ≤ normalizer (L : Set G)) {X : Subgroup L} [X.Characteristic]
    {r : G}
    (hr : r ∈ (CFSG.pCore 2 (X.map L.subtype ⊔ T : Subgroup G)).map
      (X.map L.subtype ⊔ T).subtype) (x : X) :
    ⁅r, ((x : L) : G)⁆ ∈ ((CFSG.pCore 2 X).map X.subtype).map L.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set XG := X.map L.subtype with hXG
  set R := (CFSG.pCore 2 (XG ⊔ T : Subgroup G)).map (XG ⊔ T).subtype with hR
  have hXTR : XG ⊔ T ≤ normalizer (R : Set G) := fun g hg =>
    mem_normalizer_map_of_characteristic (CFSG.pCore 2 (XG ⊔ T : Subgroup G))
      (le_normalizer hg)
  have hRXT : R ≤ XG ⊔ T := map_subtype_le _
  have hXGn : XG ⊔ T ≤ normalizer (XG : Set G) := by
    refine sup_le (fun g hg => ?_) (fun t ht => mem_normalizer_map_of_characteristic X (hTL ht))
    obtain ⟨l, -, rfl⟩ := hg
    exact mem_normalizer_map_of_characteristic X (le_normalizer l.2)
  have hxG : ((x : L) : G) ∈ XG := ⟨x, x.2, rfl⟩
  have h1 : ⁅r, ((x : L) : G)⁆ ∈ R := by
    rw [commutatorElement_def]
    have h2 := (mem_normalizer_iff.mp (hXTR (mem_sup_left hxG)) r⁻¹).mp (inv_mem hr)
    have h3 := mul_mem hr h2
    simpa [mul_assoc] using h3
  have h2 : ⁅r, ((x : L) : G)⁆ ∈ XG := by
    rw [commutatorElement_def]
    have h3 := (mem_normalizer_iff.mp (hXGn (hRXT hr)) _).mp hxG
    exact mul_mem h3 (inv_mem hxG)
  obtain ⟨y, hyX, hy⟩ := h2
  set C : Subgroup X := R.comap (L.subtype.comp X.subtype) with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hC, mem_comap] at hc ⊢
    have hgG : (((g : X) : L) : G) ∈ XG ⊔ T := mem_sup_left ⟨g, g.2, rfl⟩
    have h3 := (mem_normalizer_iff.mp (hXTR hgG) _).mp hc
    simpa using h3
  have hC2 : IsPGroup 2 C := by
    have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup.map _
    exact hR2.comap_of_injective _ ((L.subtype_injective).comp X.subtype_injective)
  have hCle := CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup hCn hC2
  have hyC : (⟨y, hyX⟩ : X) ∈ C := by
    rw [hC, mem_comap]
    change (y : G) ∈ R
    rw [show ((y : L) : G) = _ from hy]
    exact h1
  refine ⟨y, ⟨⟨y, hyX⟩, hCle hyC, rfl⟩, ?_⟩
  exact hy

theorem single_odd_prime_radical_gives_pre_singleton_characteristic_normalizer_control
    {G : Type*} [Group G] [Finite G] {L T : Subgroup G} (hTL : T ≤ normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (L ⊔ T)) (hSQT : CFSG.IsStronglyQuasithin L)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {X : Subgroup L} (hX : IsOddResidualWitness p X) (hO2X : CFSG.pCore 2 X ≠ ⊥)
    (hFQ : CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L) = CFSG.pCore p (L ⧸ CFSG.pCore 2 L)) :
    let R := (CFSG.pCore 2 (X.map L.subtype ⊔ T : Subgroup G)).map
      (X.map L.subtype ⊔ T).subtype
    (CFSG.pCore 2 L).map L.subtype ≠ ⊥ ∧ (CFSG.pCore 2 L).map L.subtype ≤ R ∧
      ⁅R, L⁆ ≤ (CFSG.pCore 2 L).map L.subtype ∧ R ≤ L ⊔ T ∧
      L ⊔ T ≤ normalizer (R : Set G) ∧
      ∀ M : Subgroup G, CFSG.maximalTwoLocalsContaining ((L ⊔ T : Subgroup G) : Set G) = {M} →
        (∀ D : Subgroup G, D ≤ R → (D.subgroupOf R).Characteristic → D ≠ ⊥ →
          normalizer (D : Set G) ≤ M) ∧ normalizer (R : Set G) ≤ M := by
  intro R
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXc := hX.characteristic
  have hLTL : L ⊔ T ≤ normalizer (L : Set G) := sup_le le_normalizer hTL
  have hLTn : ∀ (C : Subgroup L) [C.Characteristic],
      L ⊔ T ≤ normalizer ((C.map L.subtype : Subgroup G) : Set G) :=
    fun C _ g hg => mem_normalizer_map_of_characteristic C (hLTL hg)
  have hXTLT : X.map L.subtype ⊔ T ≤ L ⊔ T := sup_le ((map_subtype_le X).trans le_sup_left)
    le_sup_right
  have hRXT : R ≤ X.map L.subtype ⊔ T := map_subtype_le _
  have hXTR : X.map L.subtype ⊔ T ≤ normalizer (R : Set G) := fun g hg =>
    mem_normalizer_map_of_characteristic (CFSG.pCore 2 (X.map L.subtype ⊔ T : Subgroup G))
      (le_normalizer hg)
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup.map _
  have hN2 : IsPGroup 2 ((CFSG.pCore 2 L).map L.subtype) := CFSG.pCore_isPGroup.map _
  have hNT : (CFSG.pCore 2 L).map L.subtype ≤ T :=
    le_of_isSylowOf_of_normalizes hN2 ((map_subtype_le _).trans le_sup_left)
      (hLTn (CFSG.pCore 2 L)) hT
  have hTXT := isSylowOf_of_le hT le_sup_right hXTLT
  have hRT : R ≤ T := le_of_isSylowOf_of_normalizes hR2 hRXT hXTR hTXT
  have hNR : (CFSG.pCore 2 L).map L.subtype ≤ R := by
    have hNXT : (CFSG.pCore 2 L).map L.subtype ≤ X.map L.subtype ⊔ T := hNT.trans le_sup_right
    have hn : (((CFSG.pCore 2 L).map L.subtype).subgroupOf (X.map L.subtype ⊔ T)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hNXT).mpr ((hXTLT.trans (hLTn (CFSG.pCore 2 L))))
    have hle := CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup hn
      hN2.comap_subtype
    intro n hn'
    exact ⟨⟨n, hNXT hn'⟩, hle (mem_subgroupOf.mpr hn'), rfl⟩
  have hO2N : (CFSG.pCore 2 X).map X.subtype ≤ CFSG.pCore 2 L :=
    CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup inferInstance
      (CFSG.pCore_isPGroup.map _)
  have hNne : (CFSG.pCore 2 L).map L.subtype ≠ ⊥ := by
    intro h
    apply hO2X
    rw [eq_bot_iff]
    intro x hx
    have h1 : (((x : X) : L) : G) ∈ (CFSG.pCore 2 L).map L.subtype :=
      ⟨_, hO2N ⟨x, hx, rfl⟩, rfl⟩
    rw [h, mem_bot] at h1
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨hQne, hXD, -, -, -, -, -, -, -⟩ :=
    original_characteristic_radical_witness_is_canonical_prime_residual hSQT hLC hq hp5 hX
      (CFSG.pCore p (L ⧸ CFSG.pCore 2 L))
      (closure {a | a ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧ a ^ p = 1})
      ((closure {a | a ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧ a ^ p = 1}).comap
        (QuotientGroup.mk' (CFSG.pCore 2 L))) rfl rfl rfl
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  have hpF : p ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hp.out, ?_, Nat.card_pos.ne'⟩
    rw [hFQ]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup :
      IsPGroup p (CFSG.pCore p (L ⧸ CFSG.pCore 2 L))).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hk
      exact hQne hk
    rw [hk]
    exact dvd_pow_self p hk0
  have hact : ∀ r (hr : r ∈ R) (l : L),
      QuotientGroup.mk' (CFSG.pCore 2 L) (L.normalizerMonoidHom ⟨r, hTL (hRT hr)⟩ l) =
        QuotientGroup.mk' (CFSG.pCore 2 L) l := by
    intro r hr l
    set α : MulAut (L ⧸ CFSG.pCore 2 L) :=
      autQuotient (CFSG.pCore 2 L) (L.normalizerMonoidHom ⟨r, hTL (hRT hr)⟩) with hα
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    have hαk : α ^ 2 ^ k = 1 := by
      have h1 : (⟨r, hTL (hRT hr)⟩ : normalizer (L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by
        have h2 := congrArg Subtype.val hk
        rw [SubgroupClass.coe_pow] at h2 ⊢
        exact h2)
      rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
    have hfix : ∀ a ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L), a ^ p = 1 → α a = a := by
      intro a ha hap
      have haD : a ∈ X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) := by
        rw [hXD]
        exact subset_closure ⟨ha, hap⟩
      obtain ⟨x, hx, rfl⟩ := haD
      rw [hα, QuotientGroup.mk'_apply, autQuotient_mk, ← QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq]
      obtain ⟨z, hz, hzx⟩ := commutator_mem_two_core_of_mem_radical hTL hr ⟨x, hx⟩
      have hzN : z ∈ CFSG.pCore 2 L := hO2N hz
      have hzval : (z : G) = r * (x : G) * r⁻¹ * (x : G)⁻¹ := by
        rw [← commutatorElement_def]
        exact hzx
      have e : (L.normalizerMonoidHom ⟨r, hTL (hRT hr)⟩ x)⁻¹ * x = x⁻¹ * z⁻¹ * x⁻¹⁻¹ := by
        apply Subtype.ext
        change (r * (x : G) * r⁻¹)⁻¹ * (x : G) = (x : G)⁻¹ * (z : G)⁻¹ * ((x : G)⁻¹)⁻¹
        rw [hzval]
        group
      rw [e]
      exact (inferInstance : (CFSG.pCore 2 L).Normal).conj_mem _ (inv_mem hzN) _
    have hα1 := aut_eq_one_of_fixes_canonical hSQT' hO2' hLC' hq hpF hFQ hαk hfix
    have h2 := congrArg (fun σ : MulAut (L ⧸ CFSG.pCore 2 L) =>
      σ (QuotientGroup.mk' (CFSG.pCore 2 L) l)) hα1
    simp only [MulAut.one_apply] at h2
    rw [hα, QuotientGroup.mk'_apply, autQuotient_mk] at h2
    exact h2
  have hRL : ⁅R, L⁆ ≤ (CFSG.pCore 2 L).map L.subtype := by
    rw [commutator_le]
    intro r hr g hg
    have h1 := hact r hr ⟨g, hg⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    set σl := L.normalizerMonoidHom ⟨r, hTL (hRT hr)⟩ ⟨g, hg⟩ with hσl
    have h2 : σl * (⟨g, hg⟩ : L)⁻¹ ∈ CFSG.pCore 2 L := by
      have h3 := (inferInstance : (CFSG.pCore 2 L).Normal).conj_mem _ h1 σl
      have e : σl * (σl⁻¹ * ⟨g, hg⟩) * σl⁻¹ = (σl * (⟨g, hg⟩ : L)⁻¹)⁻¹ := by group
      rw [e] at h3
      simpa using inv_mem h3
    refine ⟨_, h2, ?_⟩
    rw [subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rfl
  have hLR : L ≤ normalizer (R : Set G) := by
    have key : ∀ l ∈ L, ∀ h ∈ R, l * h * l⁻¹ ∈ R := by
      intro l hl h hh
      have h1 : ⁅h, l⁆ ∈ R := hNR (hRL (commutator_mem_commutator hh hl))
      have e : l * h * l⁻¹ = ⁅h, l⁆⁻¹ * h := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (inv_mem h1) hh
    intro l hl
    rw [mem_normalizer_iff]
    intro h
    refine ⟨key l hl h, fun hh => ?_⟩
    have h1 := key l⁻¹ (inv_mem hl) _ hh
    have e : l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h := by group
    rwa [e] at h1
  have hLTR : L ⊔ T ≤ normalizer (R : Set G) :=
    sup_le hLR (le_sup_right.trans hXTR)
  refine ⟨hNne, hNR, hRL, hRXT.trans hXTLT, hLTR, fun M hM => ?_⟩
  have hD : ∀ D : Subgroup G, D ≤ R → (D.subgroupOf R).Characteristic → D ≠ ⊥ →
      normalizer (D : Set G) ≤ M := by
    intro D hDR hDc hD1
    have hRD : normalizer (R : Set G) ≤ normalizer (D : Set G) := by
      intro g hg
      have h1 := mem_normalizer_map_of_characteristic (D.subgroupOf R) hg
      rwa [subgroupOf_map_subtype, inf_eq_left.mpr hDR] at h1
    have hloc : CFSG.IsPLocal 2 (normalizer (D : Set G)) := ⟨D, hD1, hR2.to_le hDR, rfl⟩
    obtain ⟨A, hAmax, hDA⟩ := exists_isMaximalTwoLocal_le hloc
    have hAM : A ∈ CFSG.maximalTwoLocalsContaining ((L ⊔ T : Subgroup G) : Set G) :=
      ⟨hAmax, fun g hg => hDA (hRD (hLTR hg))⟩
    rw [hM, Set.mem_singleton_iff] at hAM
    rw [← hAM]
    exact hDA
  refine ⟨hD, hD R le_rfl ?_ (fun h => hNne (le_bot_iff.mp (h ▸ hNR)))⟩
  rw [subgroupOf_self]
  infer_instance

end CFSG.Quasithin.H13.NQBlock
