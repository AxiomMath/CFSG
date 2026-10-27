module

public import CFSG.Quasithin.H13.NQSetupPlaneAction
public import CFSG.Quasithin.SteinbergCDPrimePlaneSylowNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.LowRankFacts
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Quasithin.SteinbergCCLocalSylowAction

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped Pointwise

theorem eq_one_of_orderOf_dvd_prime_pow {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {H : Subgroup E} (hH : ¬ p ∣ Nat.card H) {g : E} (hg : g ∈ H) {k : ℕ}
    (hk : orderOf g ∣ p ^ k) : g = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hk
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · exact absurd ((dvd_pow_self p j.succ_ne_zero).trans
      (hj ▸ Subgroup.orderOf_dvd_natCard H hg)) hH

variable {G : Type} [Group G] [Finite G]

theorem original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {Y K : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hXK : X ≤ K) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)))
    (P : Subgroup G) (hP : IsSylowOf p P X) :
    let σ : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
      (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 K))
    let A := (P.subgroupOf K).map σ
    let U := (T.subgroupOf K).map σ
    Function.Injective (σ.comp (P.subgroupOf K).subtype) ∧
      (∃ U' : Sylow 2 ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)),
        (U' : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) = U) ∧
      ((A : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) * U = U * A) ∧
      ¬ IsCyclic (pairAutRestrict A U).range := by
  intro σ A U
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hPX, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hPK : P ≤ K := hPX.trans hXK
  have hTY : T ≤ Y := le_sup_right.trans hXTY
  have hYK : Y ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKY).mp hKn
  have hTK : T ≤ normalizer (K : Set G) := hTY.trans hYK
  have hLN : normalizer (L : Set G) ≤ normalizer (X : Set G) :=
    NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc
  have hTN : T ≤ normalizer (X : Set G) := (h.t_le.trans h.eq_normalizer.le).trans hLN
  have hLX : L ≤ normalizer (X : Set G) := le_normalizer.trans hLN
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, h.sylow.1, h.sylow.2⟩
  set AX := (CFSG.pCore 2 X).map X.subtype with hAXdef
  have hAX2 : IsPGroup 2 AX := CFSG.pCore_isPGroup.map _
  have hmemA : ∀ x : X, (x : G) ∈ AX ↔ x ∈ CFSG.pCore 2 X := fun x =>
    mem_map_iff_mem (subtype_injective X)
  have hNAX : normalizer (X : Set G) ≤ normalizer (AX : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hNA : ∀ g ∈ normalizer (X : Set G), ∀ a ∈ AX, g * a * g⁻¹ ∈ AX := fun g hg a ha =>
    (mem_normalizer_iff.mp (hNAX hg) a).mp ha
  have hAXT : AX ≤ T := by
    have h1 := hTtop.eq_of_le le_sup_left le_top
      (h.sylow.1.to_sup_of_normal_right' hAX2 (hTN.trans hNAX))
    rw [← h1]
    exact le_sup_right
  have hπP : (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ := by
    obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
    have h1 := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
      (hXA.to_subgroup ⊤) le_top
    rw [h1, Sylow.coe_mapSurjective, hS₁]
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ AX := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩ ∈
        (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := hπP ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    exact ⟨y, mem_subgroupOf.mp hy, (hmemA _).mpr (QuotientGroup.eq.mp hyx)⟩
  have hσinj : Function.Injective (σ.comp (P.subgroupOf K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨((y : K) : G), mem_subgroupOf.mp y.2⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hk
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 K) (y : K) ∈ center (K ⧸ CFSG.pCore 2 K) :=
      (QuotientGroup.eq_one_iff _).mp hy
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 K) (y : K) = 1 :=
      eq_one_of_orderOf_dvd_prime_pow hp hZ h1 ((orderOf_map_dvd _ _).trans hk.dvd)
    have h3 : (y : K) ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff _).mp h2
    have h4 : ¬ p ∣ Nat.card (CFSG.pCore 2 K) := by
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).exists_card_eq
      rw [hm]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    exact Subtype.ext (eq_one_of_orderOf_dvd_prime_pow hp h4 h3 hk.dvd)
  have hσs : Function.Surjective σ := fun z => by
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center (K ⧸ CFSG.pCore 2 K)) z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) j
    exact ⟨k, rfl⟩
  have hU : ∃ U' : Sylow 2 ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)),
      (U' : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) = U := by
    obtain ⟨S₁, hS₁⟩ :=
      ((hTtop.of_le hTY le_top).inf_of_le_normalizer hKY hYK).exists_sylow_eq_subgroupOf
    refine ⟨S₁.mapSurjective hσs, ?_⟩
    rw [Sylow.coe_mapSurjective, hS₁, inf_subgroupOf_right]
  have hPT : ∀ y ∈ P, ∀ q ∈ T, ∃ q' ∈ T, ∃ y' ∈ P, y * q = q' * y' := by
    intro y hy q hq
    have hx : q⁻¹ * y * q⁻¹⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hTN (inv_mem hq)) y).mp (hPX hy)
    rw [inv_inv] at hx
    obtain ⟨y', hy', hya⟩ := hXPA _ hx
    refine ⟨q * (y' * (y'⁻¹ * (q⁻¹ * y * q)) * y'⁻¹),
      mul_mem hq (hAXT (hNA y' (le_normalizer (hPX hy')) _ hya)), y', hy', by group⟩
  have hTP : ∀ q ∈ T, ∀ y ∈ P, ∃ y' ∈ P, ∃ q' ∈ T, q * y = y' * q' := by
    intro q hq y hy
    obtain ⟨y', hy', hya⟩ := hXPA _ ((mem_normalizer_iff.mp (hTN hq) y).mp (hPX hy))
    exact ⟨y', hy', y'⁻¹ * (q * y * q⁻¹) * q, mul_mem (hAXT hya) hq, by group⟩
  have hAU : (A : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) * U = U * A := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨q', hq', y', hy', he⟩ :=
        hPT _ (mem_subgroupOf.mp hy) _ (mem_subgroupOf.mp hu)
      have hq'K : q' ∈ K := by
        rw [show q' = (y : G) * u * y'⁻¹ by rw [he]; group]
        exact mul_mem (mul_mem y.2 u.2) (inv_mem (hPK hy'))
      refine ⟨σ ⟨q', hq'K⟩, ⟨⟨q', hq'K⟩, mem_subgroupOf.mpr hq', rfl⟩, σ ⟨y', hPK hy'⟩,
        ⟨⟨y', hPK hy'⟩, mem_subgroupOf.mpr hy', rfl⟩, ?_⟩
      change σ ⟨q', hq'K⟩ * σ ⟨y', hPK hy'⟩ = σ y * σ u
      rw [← map_mul, ← map_mul]
      exact congrArg σ (Subtype.ext he.symm)
    · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨y', hy', q', hq', he⟩ :=
        hTP _ (mem_subgroupOf.mp hu) _ (mem_subgroupOf.mp hy)
      have hq'K : q' ∈ K := by
        rw [show q' = y'⁻¹ * ((u : G) * y) by rw [he]; group]
        exact mul_mem (inv_mem (hPK hy')) (mul_mem u.2 y.2)
      refine ⟨σ ⟨y', hPK hy'⟩, ⟨⟨y', hPK hy'⟩, mem_subgroupOf.mpr hy', rfl⟩, σ ⟨q', hq'K⟩,
        ⟨⟨q', hq'K⟩, mem_subgroupOf.mpr hq', rfl⟩, ?_⟩
      change σ ⟨y', hPK hy'⟩ * σ ⟨q', hq'K⟩ = σ u * σ y
      rw [← map_mul, ← map_mul]
      exact congrArg σ (Subtype.ext he.symm)
  refine ⟨hσinj, hU, hAU, fun hcyc => ?_⟩
  set N := T ⊓ normalizer (P : Set G) with hN
  have hQdec : ∀ q ∈ T, ∃ a ∈ AX, a⁻¹ * q ∈ N := by
    intro q hq
    have hqP : IsSylowOf p (P.map (MulAut.conj q).toMonoidHom) X := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (hTN hq) y).mp (hPX hy)
      · rw [card_map_of_injective (MulAut.conj q).injective, hP.card_eq]
    obtain ⟨x, hx, hxP⟩ := SteinbergCC.exists_conj_eq_of_isSylowOf hP hqP
    obtain ⟨y, hy, hya⟩ := hXPA x hx
    have haA : x * y⁻¹ ∈ AX := by
      have h1 := hNA y (le_normalizer (hPX hy)) _ hya
      rwa [show y * (y⁻¹ * x) * y⁻¹ = x * y⁻¹ by group] at h1
    refine ⟨x * y⁻¹, haA, mem_inf.mpr ⟨mul_mem (inv_mem (hAXT haA)) hq,
      mem_normalizer_iff.mpr fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩⟩
    · have h1 : q * z * q⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom := by
        rw [hxP]
        exact ⟨z, hz, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : x * z' * x⁻¹ = q * z * q⁻¹ := hzz'
      have e : (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ = y * z' * y⁻¹ := by
        rw [show (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ =
          y * x⁻¹ * (q * z * q⁻¹) * x * y⁻¹ by group, ← hzz']
        group
      rw [e]
      exact mul_mem (mul_mem hy hz') (inv_mem hy)
    · have hu : y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y ∈ P :=
        mul_mem (mul_mem (inv_mem hy) hz) hy
      have h1 : x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ ∈
          P.map (MulAut.conj q).toMonoidHom := by
        rw [← hxP]
        exact ⟨_, hu, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : q * z' * q⁻¹ =
          x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ := hzz'
      have e : z = z' := by
        have h2 : q * z' * q⁻¹ = q * z * q⁻¹ := by rw [hzz']; group
        exact (mul_left_cancel (mul_right_cancel h2)).symm
      rw [e]
      exact hz'
  have hconjmk : ∀ (g : G) (hg : g ∈ normalizer (X : Set G)) (x : X),
      normalizerFrattiniConj X ⟨g, hg⟩
        (QuotientGroup.mk' _ (QuotientGroup.mk' (CFSG.pCore 2 X) x)) =
      QuotientGroup.mk' _ (QuotientGroup.mk' (CFSG.pCore 2 X) (X.normalizerMonoidHom ⟨g, hg⟩ x)) :=
    fun _ _ _ => rfl
  have hAtriv : ∀ (a : G) (ha : a ∈ AX) (haN : a ∈ normalizer (X : Set G)),
      normalizerFrattiniConj X ⟨a, haN⟩ = 1 := by
    intro a ha haN
    ext w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    rw [hconjmk, MulAut.one_apply]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply (hmemA _).mp
    change (a * x * a⁻¹)⁻¹ * x ∈ AX
    have h1 := hNA (x : G)⁻¹ (le_normalizer (inv_mem x.2)) a⁻¹ (inv_mem ha)
    rw [inv_inv] at h1
    rw [show (a * (x : G) * a⁻¹)⁻¹ * x = a * ((x : G)⁻¹ * a⁻¹ * x) by group]
    exact mul_mem ha h1
  have hcentriv : ∀ (g : G) (hg : g ∈ normalizer (X : Set G)), (∀ z ∈ P, g * z * g⁻¹ = z) →
      normalizerFrattiniConj X ⟨g, hg⟩ = 1 := by
    intro g hg hgP
    ext w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    obtain ⟨y, hy, hya⟩ := hXPA x x.2
    have hxy : QuotientGroup.mk' (CFSG.pCore 2 X) x =
        QuotientGroup.mk' (CFSG.pCore 2 X) ⟨y, hPX hy⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have h1 := inv_mem hya
      rw [mul_inv_rev, inv_inv] at h1
      exact (hmemA _).mp h1
    rw [hxy, hconjmk, MulAut.one_apply]
    congr 2
    exact Subtype.ext (hgP y hy)
  let τ : normalizer (K : Set G) →*
      MulAut ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
    (CFSG.SectionRank.Ccomm.autQuotient (center (K ⧸ CFSG.pCore 2 K))).comp
      ((CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 K)).comp K.normalizerMonoidHom)
  have hτ : ∀ (n : normalizer (K : Set G)) (k : K), τ n (σ k) = σ (K.normalizerMonoidHom n k) :=
    fun _ _ => rfl
  have hΓ : ∀ n : normalizer (K : Set G), (n : G) ∈ normalizer (P : Set G) → (n : G) ∈ T →
      τ n ∈ pairAutSubgroup A U := by
    intro n hnP hnT
    have key : ∀ B : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)),
        (∀ b ∈ B, τ n b ∈ B) → B.map (τ n).toMonoidHom = B := by
      intro B hB
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨b, hb, rfl⟩
        exact hB b hb
      · exact (Subgroup.card_map_of_injective (f := (τ n).toMonoidHom) (τ n).injective).symm.le
    refine ⟨key A ?_, key U ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      refine ⟨K.normalizerMonoidHom n k, ?_, (hτ n k).symm⟩
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hnP k).mp (mem_subgroupOf.mp hk))
    · rintro _ ⟨k, hk, rfl⟩
      refine ⟨K.normalizerMonoidHom n k, ?_, (hτ n k).symm⟩
      exact mem_subgroupOf.mpr (mul_mem (mul_mem hnT (mem_subgroupOf.mp hk)) (inv_mem hnT))
  have hNK : N ≤ normalizer (K : Set G) := inf_le_left.trans hTK
  have hNX : N ≤ normalizer (X : Set G) := inf_le_left.trans hTN
  let ψ : N →* pairAutSubgroup A U :=
    (τ.comp (inclusion hNK)).codRestrict _ fun n =>
      hΓ (inclusion hNK n) (mem_inf.mp n.2).2 (mem_inf.mp n.2).1
  let bres : N →* MulAut A := (pairAutRestrict A U).comp ψ
  let ρN : N →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (inclusion hNX)
  have hker : bres.rangeRestrict.ker ≤ ρN.rangeRestrict.ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    have hn' : bres n = 1 := congrArg Subtype.val hn
    have hcent : ∀ z ∈ P, (n : G) * z * (n : G)⁻¹ = z := by
      intro z hz
      have hk : (⟨z, hPK hz⟩ : K) ∈ P.subgroupOf K := mem_subgroupOf.mpr hz
      have hc : K.normalizerMonoidHom (inclusion hNK n) ⟨z, hPK hz⟩ ∈ P.subgroupOf K := by
        rw [mem_subgroupOf]
        exact (mem_normalizer_iff.mp (mem_inf.mp n.2).2 z).mp hz
      have h1 := congrArg (fun φ : MulAut A => ((φ ⟨σ ⟨z, hPK hz⟩, ⟨_, hk, rfl⟩⟩ : A) :
        (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) hn'
      change σ (K.normalizerMonoidHom (inclusion hNK n) ⟨z, hPK hz⟩) = σ ⟨z, hPK hz⟩ at h1
      have h2 : (⟨_, hc⟩ : P.subgroupOf K) = ⟨_, hk⟩ := hσinj h1
      exact congrArg (fun w : P.subgroupOf K => ((w : K) : G)) h2
    exact Subtype.ext (hcentriv n (hNX n.2) hcent)
  let f := (MonoidHom.liftOfSurjective bres.rangeRestrict bres.rangeRestrict_surjective)
    ⟨ρN.rangeRestrict, hker⟩
  have hf : ∀ n, f (bres.rangeRestrict n) = ρN.rangeRestrict n := fun n =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hfsurj : Function.Surjective f := fun w => by
    obtain ⟨n, rfl⟩ := ρN.rangeRestrict_surjective w
    exact ⟨_, hf n⟩
  have hbres : bres.range ≤ (pairAutRestrict A U).range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨ψ n, rfl⟩
  have : IsCyclic bres.range := Subgroup.isCyclic_of_le hbres
  have hNcyc : IsCyclic ρN.range := isCyclic_of_surjective f hfsurj
  set R := ((T ⊓ L).subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X)
    with hRdef
  have hRle : R ≤ ρN.range := by
    rintro _ ⟨q, hq, rfl⟩
    have hqT : (q : G) ∈ T := (mem_inf.mp (mem_subgroupOf.mp hq)).1
    obtain ⟨a, ha, han⟩ := hQdec q hqT
    have haN : a ∈ normalizer (X : Set G) := hTN (hAXT ha)
    refine ⟨⟨a⁻¹ * q, han⟩, ?_⟩
    change normalizerFrattiniConj X (⟨a, haN⟩⁻¹ * q) = normalizerFrattiniConj X q
    rw [map_mul, map_inv, hAtriv a ha haN, inv_one, one_mul]
  have : Group.IsPerfect L :=
    ⟨by rw [commutator_def]; exact (NQSetup.isCComponent_top_of_qtnq h).2.1⟩
  let ρL : L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (inclusion hLX)
  have : Finite (MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) :=
    Finite.of_injective _ DFunLike.coe_injective
  have : Group.IsPerfect ρL.range := Group.IsPerfect.range ρL
  have hTL : IsSylowOf 2 (T ⊓ L) L :=
    (hTtop.of_le h.t_le le_top).inf_of_le_normalizer h.l_le h.eq_normalizer.le
  obtain ⟨SL, hSL⟩ := hTL.exists_sylow_eq_subgroupOf
  have hSLR : ∀ s ∈ (SL : Subgroup L), ρL s ∈ R := by
    intro s hs
    have hs' : s ∈ (T ⊓ L).subgroupOf L := hSL ▸ hs
    exact ⟨⟨s, hLX s.2⟩, mem_subgroupOf.mpr (mem_subgroupOf.mp hs'), rfl⟩
  set SI := SL.mapSurjective ρL.rangeRestrict_surjective with hSI
  have hSIcyc : IsCyclic (SI : Subgroup ρL.range) := by
    have hle : (SI : Subgroup ρL.range).map ρL.range.subtype ≤ ρN.range := by
      rintro _ ⟨_, hz, rfl⟩
      rw [hSI, Sylow.coe_mapSurjective] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      exact hRle (hSLR s hs)
    have : IsCyclic ((SI : Subgroup ρL.range).map ρL.range.subtype) := Subgroup.isCyclic_of_le hle
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective (SI : Subgroup ρL.range)
      ρL.range.subtype ρL.range.subtype_injective).symm (MulEquiv.surjective _)
  obtain ⟨-, hWc, hWpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hXA
  have : IsMulCommutative ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := hWc
  have hρL : ρL ≠ 1 := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 : ρL ⟨l, hlL⟩ = 1 := by rw [h1, MonoidHom.one_apply]
    have h3 : inclusion hLX ⟨(l : G), hlL⟩ = l := Subtype.ext rfl
    change (normalizerFrattiniConj X).comp (inclusion hLX) ⟨l, hlL⟩ = 1 at h2
    rwa [MonoidHom.comp_apply, h3] at h2
  have hR1 : R ≠ ⊥ := by
    intro hRbot
    have hW1 : 1 < Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := by
      rw [hW]
      exact Nat.one_lt_pow two_ne_zero hp.one_lt
    have : Nontrivial ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
      Finite.one_lt_card_iff_nontrivial.mp hW1
    obtain ⟨w, hw⟩ := exists_ne (1 : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))
    have hirr := SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWpow hW ρL hρL SL
      (zpowers w) fun s hs w' hw' => by
        have h1 : ρL s ∈ R := hSLR s hs
        rw [hRbot, mem_bot] at h1
        rw [h1, MulAut.one_apply]
        exact hw'
    rcases hirr with hbot | htop
    · exact hw (zpowers_eq_bot.mp hbot)
    · have h1 : Nat.card (zpowers w) ≤ p := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one hp.pos (hWpow w)
      rw [htop, card_top, hW] at h1
      nlinarith
  have hR2 : IsPGroup 2 R :=
    ((h.sylow.1.to_inf_left (K := L)).comap_subtype (K := normalizer (X : Set G))).map _
  have hRI : R ≤ ρL.range := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨⟨q, (mem_inf.mp (mem_subgroupOf.mp hq)).2⟩, rfl⟩
  have heven : Even (Nat.card ρL.range) := by
    obtain ⟨m, hm⟩ := hR2.exists_card_eq
    have hm1 : m ≠ 0 := by
      rintro rfl
      exact hR1 (Subgroup.eq_bot_of_card_eq R (by rw [hm, pow_zero]))
    have h2R : 2 ∣ Nat.card R := by
      rw [hm]
      exact dvd_pow_self 2 hm1
    exact even_iff_two_dvd.mpr (h2R.trans (Subgroup.card_dvd_of_le hRI))
  exact perfect_even_sylow_noncyclic heven SI hSIcyc

end CFSG.Quasithin.H13.NQTerm
