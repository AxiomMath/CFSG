module

public import CFSG.Quasithin.H13.NQCatLargeRee
public import CFSG.Quasithin.H13.NQBlockSinglePrime
public import CFSG.Quasithin.H13.NQBlockNormalizedCore
public import CFSG.Quasithin.SteinbergCCLocalSylowAction

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.LieType.Ree CFSG.Blueprint CFSG.LieType.Chevalley CFSG.SectionRank.Ccomm
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup)
open scoped commutatorElement Pointwise

theorem exists_mulEquiv_reeGamma_of_reeTitsModel
    {S : Type} [Group S] {a : ℕ} (ha : 1 ≤ a)
    (hS : ReeTitsModel S .twistedF4 2 (2 * a + 1)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      Nat.card K = 2 ^ (2 * a + 1) ∧ Nonempty (S ≃* ReeTag.F4.reeGamma K a) := by
  classical
  obtain ⟨-, a', hfa, K, hKf, hKfin, hKchar, hKcard, ⟨e1⟩⟩ :=
    ((ree_tits_relation_graph_identification.2 S 2 (2 * a + 1)).2.1).mp hS
  have haa : a' = a := by omega
  subst haa
  set Γ := ReeTag.F4.reeGamma K a' with hΓ
  have hKcard' : Nat.card K = ReeTag.F4.prime ^ (2 * a' + 1) := hKcard
  obtain ⟨-, hperf, -, -⟩ := ReeTag.ree_generic_fixed_group_perfect ReeTag.F4 a' ha K hKcard'
  have hZ : center Γ = ⊥ := ReeTag.large_Ree_fixed_group_center_trivial a' K hKcard
  have hΓΓ : ⁅Γ, Γ⁆ = Γ := by
    rw [← Subgroup.range_subtype Γ, MonoidHom.range_eq_map, ← map_commutator,
      ← _root_.commutator_def, hperf]
  set e3 : (⁅Γ, Γ⁆ : Subgroup _) ≃* Γ := MulEquiv.subgroupCongr hΓΓ with he3
  have hcen : center (⁅Γ, Γ⁆ : Subgroup _) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : e3 z ∈ center Γ := by
      rw [mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e3.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
    rw [hZ, mem_bot] at h1
    rw [mem_bot]
    exact e3.injective (h1.trans (map_one e3).symm)
  exact ⟨K, hKf, hKfin, hKchar, hKcard, ⟨e1.trans (((QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot).trans e3)⟩⟩

theorem ree_two_prime_rigid
    {S : Type} [Group S] [Finite S] {a : ℕ} (ha : 1 ≤ a)
    (hS : ReeTitsModel S .twistedF4 2 (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P₀ : Subgroup S) (hP₀ : IsPGroup p P₀) (U₀ : Sylow 2 S)
    (hPU : (P₀ : Set S) * (U₀ : Set S) = (U₀ : Set S) * (P₀ : Set S))
    (Δ : Subgroup (MulAut S)) (hΔ : IsPGroup 2 Δ)
    (hΔP : ∀ β ∈ Δ, P₀.map β.toMonoidHom = P₀ ∧ (U₀ : Subgroup S).map β.toMonoidHom = U₀) :
    ∀ β ∈ Δ, ∀ x ∈ P₀, β x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKf, hKfin, hKchar, hKcard, ⟨ψ⟩⟩ := exists_mulEquiv_reeGamma_of_reeTitsModel ha hS
  set Γ := ReeTag.F4.reeGamma K a with hΓ
  set A : Subgroup Γ := P₀.map ψ.toMonoidHom with hA
  have hAp : IsPGroup p A := hP₀.map _
  set U : Sylow 2 Γ := U₀.mapSurjective (f := ψ.toMonoidHom) ψ.surjective with hU
  have hUcoe : (U : Subgroup Γ) = (U₀ : Subgroup S).map ψ.toMonoidHom := rfl
  have hUset : (U : Set Γ) = ψ.toMonoidHom '' (U₀ : Set S) := rfl
  have hAset : (A : Set Γ) = ψ.toMonoidHom '' (P₀ : Set S) := rfl
  have hAU : (A : Set Γ) * (U : Set Γ) = (U : Set Γ) * (A : Set Γ) := by
    rw [hUset, hAset, ← Set.image_mul, hPU, Set.image_mul]
  set Δ' : Subgroup (MulAut Γ) := Δ.map (MulAut.congr ψ).toMonoidHom with hΔ'
  have hcongr : ∀ (β : MulAut S) (x : S), MulAut.congr ψ β (ψ x) = ψ (β x) := by
    intro β x
    simp [MulAut.congr_apply]
  have hmapA : ∀ β : MulAut S, A.map (MulAut.congr ψ β).toMonoidHom =
      (P₀.map β.toMonoidHom).map ψ.toMonoidHom := by
    intro β
    rw [hA, map_map, map_map]
    congr 1
    exact MonoidHom.ext fun x => hcongr β x
  have hmapU : ∀ β : MulAut S, (U : Subgroup Γ).map (MulAut.congr ψ β).toMonoidHom =
      ((U₀ : Subgroup S).map β.toMonoidHom).map ψ.toMonoidHom := by
    intro β
    rw [hUcoe, map_map, map_map]
    congr 1
    exact MonoidHom.ext fun x => hcongr β x
  have hΔ'le : Δ' ≤ pairAutSubgroup A (U : Subgroup Γ) := by
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨?_, ?_⟩
    · change A.map (MulAut.congr ψ β).toMonoidHom = A
      rw [hmapA, (hΔP β hβ).1]
    · change (U : Subgroup Γ).map (MulAut.congr ψ β).toMonoidHom = U
      rw [hmapU, (hΔP β hβ).2]
      exact hUcoe.symm
  set Δ0 : Subgroup (pairAutSubgroup A (U : Subgroup Γ)) := Δ'.subgroupOf _ with hΔ0
  have hΔ0p : IsPGroup 2 Δ0 :=
    (hΔ.map _).of_equiv (subgroupOfEquivOfLe hΔ'le).symm
  have hrig :=
    (CFSG.Quasithin.H13.NQCat.large_Ree_common_sylow_prime_subgroup_normalizer_action_is_cyclic
      ha hKcard hp hp2 U A hAp hAU).2.2.2 Δ0 hΔ0p
  intro β hβ x hx
  have hmem : (MulAut.congr ψ β) ∈ pairAutSubgroup A (U : Subgroup Γ) := hΔ'le ⟨β, hβ, rfl⟩
  have h1 := hrig ⟨MulAut.congr ψ β, hmem⟩ (mem_subgroupOf.mpr ⟨β, hβ, rfl⟩) (ψ x) ⟨x, hx, rfl⟩
  rw [hcongr] at h1
  exact ψ.injective h1

theorem exists_mul_of_sylow_of_isPGroup_quotient {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {X : Subgroup H} (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (P' : Sylow p X) :
    ∀ x ∈ X, ∃ a ∈ (CFSG.pCore 2 X).map X.subtype, ∃ y ∈ (P' : Subgroup X).map X.subtype,
      x = a * y := by
  classical
  have hsurj : ((P' : Subgroup X).map (QuotientGroup.mk' (CFSG.pCore 2 X))) = ⊤ := by
    have h1 := (P'.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
      (Q := ⊤) (hP.to_subgroup ⊤) le_top
    rw [h1]
    rfl
  intro x hx
  have h2 : (QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩) ∈
      (P' : Subgroup X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    rw [hsurj]
    exact mem_top _
  obtain ⟨y, hy, hyx⟩ := h2
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have h3 : (⟨x, hx⟩ : X) * y⁻¹ ∈ CFSG.pCore 2 X := by
    have h4 := (inferInstance : (CFSG.pCore 2 X).Normal).conj_mem _ hyx y
    have e : y * (y⁻¹ * ⟨x, hx⟩) * y⁻¹ = (⟨x, hx⟩ : X) * y⁻¹ := by group
    rwa [e] at h4
  refine ⟨_, ⟨_, h3, rfl⟩, _, ⟨y, hy, rfl⟩, ?_⟩
  simp

theorem exists_mul_normalizer_of_sylow {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {X : Subgroup H} (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (P' : Sylow p X) {q : H}
    (hq : q ∈ normalizer (X : Set H)) :
    ∃ a ∈ (CFSG.pCore 2 X).map X.subtype,
      a⁻¹ * q ∈ normalizer (((P' : Subgroup X).map X.subtype : Subgroup H) : Set H) := by
  classical
  set σ : MulAut X := X.normalizerMonoidHom ⟨q, hq⟩ with hσ
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X (σ • P') P'
  have hx' := congrArg (fun S : Sylow p X => (S : Subgroup X)) hx
  have hmem : ∀ z ∈ (P' : Subgroup X), MulAut.conj x (σ z) ∈ (P' : Subgroup X) := by
    intro z hz
    have h1 : MulAut.conj x • (σ • z) ∈ MulAut.conj x • (σ • (P' : Subgroup X)) :=
      smul_mem_pointwise_smul _ _ _ (smul_mem_pointwise_smul _ _ _ hz)
    have h2 : (P' : Subgroup X) = MulAut.conj x • (σ • (P' : Subgroup X)) := hx'.symm
    rw [h2]
    exact h1
  set P := ((P' : Subgroup X).map X.subtype : Subgroup H) with hPdef
  set n : H := (x : H) * q with hn
  have hle : P.map (MulAut.conj n).toMonoidHom ≤ P := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨_, hmem z hz, ?_⟩
    simp [hn, hσ, mul_assoc]
  have heq : P.map (MulAut.conj n).toMonoidHom = P :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective])
  have hnP : n ∈ normalizer (P : Set H) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← heq]
      exact ⟨z, hz, rfl⟩
    · intro hz
      rw [← heq] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      have hwz' : w = z := by
        have h1 : n * w * n⁻¹ = n * z * n⁻¹ := hwz
        simpa using h1
      rwa [← hwz']
  obtain ⟨a, ha, y, hy, hxy⟩ :=
    exists_mul_of_sylow_of_isPGroup_quotient hP P' _ (inv_mem x.2)
  refine ⟨a, ha, ?_⟩
  have e : a⁻¹ * q = y * n := by
    rw [hn, ← mul_assoc]
    have h1 : y = a⁻¹ * (x : H)⁻¹ := by rw [hxy]; group
    rw [h1]
    group
  rw [e]
  exact mul_mem (le_normalizer hy) hnP

theorem exists_sylow_subgroupOf_normal {H : Type*} [Group H] [Finite H] (Q : Sylow 2 H)
    (K : Subgroup H) [K.Normal] :
    ∃ Q' : Sylow 2 K, (Q' : Subgroup K) = (Q : Subgroup H).subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQK2 : IsPGroup 2 ((Q : Subgroup H).subgroupOf K) := by
    rw [← comap_subtype]
    exact Q.isPGroup'.comap_subtype
  have hidx : ¬ 2 ∣ ((Q : Subgroup H).subgroupOf K).index := by
    change ¬ 2 ∣ (Q : Subgroup H).relIndex K
    rw [← CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal K (Q : Subgroup H)]
    intro h
    exact Q.not_dvd_index (h.trans (relIndex_dvd_index_of_le le_sup_right))
  exact ⟨hQK2.toSylow hidx, rfl⟩

theorem normalizer_centralizes_sylow_of_ree
    {H : Type} [Group H] [Finite H] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) {D : Subgroup H} (Q : Sylow 2 H)
    (hQD : (Q : Subgroup H) ≤ D) {K : Subgroup H} [K.Normal] {X : Subgroup H} (hXD : X ≤ D)
    (hDX : D ≤ normalizer (X : Set H)) (hXK : X ≤ K) (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {a : ℕ} (ha : 1 ≤ a)
    (hRee : ReeTitsModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))
      .twistedF4 2 (2 * a + 1)) (P' : Sylow p X)
    (hAQ : (CFSG.pCore 2 X).map X.subtype ≤ Q) :
    ∀ n ∈ (Q : Subgroup H) ⊓ normalizer (((P' : Subgroup X).map X.subtype : Subgroup H) : Set H),
      ∀ y ∈ (P' : Subgroup X).map X.subtype, n * y * n⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := (CFSG.pCore 2 X).map X.subtype with hA
  set P := ((P' : Subgroup X).map X.subtype : Subgroup H) with hPdef
  have hPX : P ≤ X := map_subtype_le _
  have hPp : IsPGroup p P := P'.isPGroup'.map _
  have hDA : D ≤ normalizer (A : Set H) := fun g hg =>
    mem_normalizer_map_of_characteristic (CFSG.pCore 2 X) (hDX hg)
  set J := K ⧸ CFSG.pCore 2 K with hJ
  set σ : K →* J ⧸ center J :=
    (QuotientGroup.mk' (center J)).comp (QuotientGroup.mk' (CFSG.pCore 2 K)) with hσ
  have hσs : Function.Surjective σ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  set χ : H →* MulAut (J ⧸ center J) := (autQuotient (center J)).comp
    ((autQuotient (CFSG.pCore 2 K)).comp MulAut.conjNormal) with hχ
  have hχσ : ∀ (h : H) (k : K), χ h (σ k) = σ (MulAut.conjNormal h k) := fun _ _ => rfl
  have hσP : ∀ y (hyP : y ∈ P) (hyK : y ∈ K), σ ⟨y, hyK⟩ = 1 → y = 1 := by
    intro y hyP hyK h1
    obtain ⟨m, hm⟩ := hPp ⟨y, hyP⟩
    have hym : y ^ p ^ m = 1 := by
      have h2 := congrArg Subtype.val hm
      rwa [SubgroupClass.coe_pow] at h2
    have hjZ : QuotientGroup.mk' (CFSG.pCore 2 K) ⟨y, hyK⟩ ∈ center J := by
      have h2 : QuotientGroup.mk' (center J) (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨y, hyK⟩) = 1 :=
        h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    set j : center J := ⟨_, hjZ⟩ with hj
    have hjm : j ^ p ^ m = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hj]
      show (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨y, hyK⟩) ^ p ^ m = 1
      rw [← map_pow]
      have h2 : (⟨y, hyK⟩ : K) ^ p ^ m = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hym)
      rw [h2, map_one]
    have hcop : Nat.Coprime (p ^ m) (Nat.card (center J)) :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hZ)
    have hj1 : orderOf j = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hjm) hcop) (orderOf_dvd_natCard j)
    rw [orderOf_eq_one_iff] at hj1
    have hyN : (⟨y, hyK⟩ : K) ∈ CFSG.pCore 2 K := by
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 K) ⟨y, hyK⟩ = 1 := congrArg Subtype.val hj1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨_, hyN⟩
    have hyk : y ^ 2 ^ k = 1 := by
      have h2 := congrArg Subtype.val (congrArg Subtype.val hk)
      rwa [SubgroupClass.coe_pow, SubgroupClass.coe_pow] at h2
    have hcop2 : Nat.Coprime (2 ^ k) (p ^ m) :=
      Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
    have h3 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hyk) hcop2)
      (orderOf_dvd_of_pow_eq_one hym)
    exact orderOf_eq_one_iff.mp h3
  have hXAP := exists_mul_of_sylow_of_isPGroup_quotient hP P'
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, ∃ b ∈ A, x = y * b := by
    intro x hx
    obtain ⟨b, hb, y, hy, rfl⟩ := hXAP x hx
    refine ⟨y, hy, y⁻¹ * b * y⁻¹⁻¹, ?_, by group⟩
    exact (mem_normalizer_iff.mp (hDA (hXD (hPX (inv_mem hy)))) b).mp hb
  have hPQ : ∀ u ∈ P, ∀ v ∈ (Q : Subgroup H), ∃ v' ∈ (Q : Subgroup H), ∃ u' ∈ P,
      u * v = v' * u' := by
    intro u hu v hv
    have h1 : v⁻¹ * u * v⁻¹⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hDX (hQD (inv_mem hv))) u).mp (hPX hu)
    obtain ⟨b, hb, y, hy, hby⟩ := hXAP _ h1
    refine ⟨v * b, mul_mem hv (hAQ hb), y, hy, ?_⟩
    rw [mul_assoc, ← hby]
    group
  have hQP : ∀ v ∈ (Q : Subgroup H), ∀ u ∈ P, ∃ u' ∈ P, ∃ v' ∈ (Q : Subgroup H),
      v * u = u' * v' := by
    intro v hv u hu
    have h1 : v * u * v⁻¹ ∈ X := (mem_normalizer_iff.mp (hDX (hQD hv)) u).mp (hPX hu)
    obtain ⟨y, hy, b, hb, hyb⟩ := hXPA _ h1
    refine ⟨y, hy, b * v, mul_mem (hAQ hb) hv, ?_⟩
    rw [← mul_assoc, ← hyb]
    group
  obtain ⟨QK, hQK⟩ := exists_sylow_subgroupOf_normal Q K
  set U₀ : Sylow 2 (J ⧸ center J) := QK.mapSurjective (f := σ) hσs with hU₀
  set P₀ : Subgroup (J ⧸ center J) := (P.subgroupOf K).map σ with hP₀
  have hP₀p : IsPGroup p P₀ := by
    have h1 : IsPGroup p (P.subgroupOf K) := by
      rw [← comap_subtype]
      exact hPp.comap_subtype
    exact h1.map σ
  have hPK : P ≤ K := hPX.trans hXK
  have hPUK : ((P.subgroupOf K : Subgroup K) : Set K) * ((QK : Subgroup K) : Set K) =
      ((QK : Subgroup K) : Set K) * ((P.subgroupOf K : Subgroup K) : Set K) := by
    rw [hQK]
    ext z
    simp only [Set.mem_mul, SetLike.mem_coe, mem_subgroupOf]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      obtain ⟨v', hv', u', hu', he⟩ := hPQ u hu v hv
      have hv'K : v' ∈ K := by
        have e : v' = (u : H) * v * (u' : H)⁻¹ := by rw [he]; group
        rw [e]
        exact mul_mem (mul_mem u.2 v.2) (inv_mem (hPK hu'))
      refine ⟨⟨v', hv'K⟩, hv', ⟨u', hPK hu'⟩, hu', Subtype.ext ?_⟩
      rw [Subgroup.coe_mul]
      exact he.symm
    · rintro ⟨v, hv, u, hu, rfl⟩
      obtain ⟨u', hu', v', hv', he⟩ := hQP v hv u hu
      have hv'K : v' ∈ K := by
        have e : v' = (u' : H)⁻¹ * v * u := by rw [mul_assoc, he]; group
        rw [e]
        exact mul_mem (mul_mem (inv_mem (hPK hu')) v.2) u.2
      refine ⟨⟨u', hPK hu'⟩, hu', ⟨v', hv'K⟩, hv', Subtype.ext ?_⟩
      rw [Subgroup.coe_mul]
      exact he.symm
  have hPU : (P₀ : Set (J ⧸ center J)) * (U₀ : Set (J ⧸ center J)) =
      (U₀ : Set (J ⧸ center J)) * (P₀ : Set (J ⧸ center J)) := by
    have hU₀set : (U₀ : Set (J ⧸ center J)) = σ '' ((QK : Subgroup K) : Set K) := rfl
    have hP₀set : (P₀ : Set (J ⧸ center J)) = σ '' ((P.subgroupOf K : Subgroup K) : Set K) := rfl
    rw [hU₀set, hP₀set, ← Set.image_mul, hPUK, Set.image_mul]
  set Δ : Subgroup (MulAut (J ⧸ center J)) :=
    ((Q : Subgroup H) ⊓ normalizer (P : Set H)).map χ with hΔ
  have hΔ2 : IsPGroup 2 Δ := (Q.isPGroup'.to_le inf_le_left).map χ
  have hΔP : ∀ β ∈ Δ, P₀.map β.toMonoidHom = P₀ ∧
      (U₀ : Subgroup (J ⧸ center J)).map β.toMonoidHom = U₀ := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨hnQ, hnP⟩ := mem_inf.mp hn
    have hnK : n ∈ normalizer (K : Set H) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top n
    refine ⟨?_, ?_⟩
    · refine eq_of_le_of_card_ge ?_ (by
        rw [card_map_of_injective (f := (χ n).toMonoidHom) (χ n).injective])
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨MulAut.conjNormal n k, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply]
        exact (mem_normalizer_iff.mp hnP _).mp (mem_subgroupOf.mp hk)
      · exact (hχσ n k).symm
    · refine eq_of_le_of_card_ge ?_ (by
        rw [card_map_of_injective (f := (χ n).toMonoidHom) (χ n).injective])
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨MulAut.conjNormal n k, ?_, ?_⟩
      · change MulAut.conjNormal n k ∈ (QK : Subgroup K)
        rw [hQK] at hk ⊢
        rw [mem_subgroupOf, MulAut.conjNormal_apply]
        exact mul_mem (mul_mem hnQ (mem_subgroupOf.mp hk)) (inv_mem hnQ)
      · exact (hχσ n k).symm
  have hrig := ree_two_prime_rigid ha hRee hp.out hp2 P₀ hP₀p U₀ hPU Δ hΔ2 hΔP
  intro n hn y hy
  have hnP := (mem_inf.mp hn).2
  have hyK : y ∈ K := hPK hy
  have hny : n * y * n⁻¹ ∈ P := (mem_normalizer_iff.mp hnP y).mp hy
  have h1 := hrig (χ n) ⟨n, hn, rfl⟩ (σ ⟨y, hyK⟩) ⟨⟨y, hyK⟩, mem_subgroupOf.mpr hy, rfl⟩
  rw [hχσ] at h1
  have h2 : σ ⟨n * y * n⁻¹ * y⁻¹, mul_mem (hPK hny) (inv_mem hyK)⟩ = 1 := by
    have e : (⟨n * y * n⁻¹ * y⁻¹, mul_mem (hPK hny) (inv_mem hyK)⟩ : K) =
        MulAut.conjNormal n ⟨y, hyK⟩ * (⟨y, hyK⟩ : K)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := hσP _ (mul_mem hny (inv_mem hy)) _ h2
  rw [mul_inv_eq_one] at h3
  exact h3

theorem normalizerResidualAction_eq_normalizerFrattiniConj {H : Type*} [Group H]
    (X : Subgroup H) :
    normalizerResidualAction X = CFSG.Quasithin.SteinbergCC.normalizerFrattiniConj X :=
  rfl

theorem large_Ree_normal_quotient_forces_local_Sylow_centralization_of_prime_witness
    {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {D : Subgroup H} (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D) {K : Subgroup H} [K.Normal]
    {X : Subgroup H} (hXD : X ≤ D) (hDX : D ≤ normalizer (X : Set H)) (hXK : X ≤ K)
    (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)))
    (hS : ∃ a : ℕ, 1 ≤ a ∧ ReeTitsModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))
      .twistedF4 2 (2 * a + 1)) :
    ⁅(Q : Subgroup H), X⁆ ≤ (CFSG.pCore 2 X).map X.subtype ∧
      ∀ q (hq : q ∈ (Q : Subgroup H)),
        CFSG.Quasithin.SteinbergCC.normalizerFrattiniConj X ⟨q, hDX (hQD hq)⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, hRee⟩ := hS
  set A := (CFSG.pCore 2 X).map X.subtype with hA
  have hAX : A ≤ X := map_subtype_le _
  have hA2 : IsPGroup 2 A := CFSG.pCore_isPGroup.map _
  have hDA : D ≤ normalizer (A : Set H) := fun g hg =>
    mem_normalizer_map_of_characteristic (CFSG.pCore 2 X) (hDX hg)
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Q : Subgroup H) D :=
    ⟨Q.subtype hQD, by rw [Sylow.coe_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hQD]⟩
  have hAQ : A ≤ Q := le_of_isSylowOf_of_normalizes hA2 (hAX.trans hXD) hDA hQsyl
  obtain ⟨P'⟩ : Nonempty (Sylow p X) := inferInstance
  set P := ((P' : Subgroup X).map X.subtype : Subgroup H) with hPdef
  have hPX : P ≤ X := map_subtype_le _
  have hcent := normalizer_centralizes_sylow_of_ree hp2 Q hQD hXD hDX hXK hP hZ ha hRee P' hAQ
  have hXAP := exists_mul_of_sylow_of_isPGroup_quotient hP P'
  have hQX : ⁅(Q : Subgroup H), X⁆ ≤ A := by
    rw [commutator_le]
    intro q hq x hx
    obtain ⟨a0, ha0, hn⟩ := exists_mul_normalizer_of_sylow hP P' (hDX (hQD hq))
    set n := a0⁻¹ * q with hndef
    have hnQ : n ∈ (Q : Subgroup H) := mul_mem (inv_mem (hAQ ha0)) hq
    obtain ⟨a1, ha1, y, hy, rfl⟩ := hXAP x hx
    have hny : n * y * n⁻¹ = y := hcent n (mem_inf.mpr ⟨hnQ, hn⟩) y hy
    have hq' : q = a0 * n := by rw [hndef]; group
    have e : ⁅q, a1 * y⁆ = a0 * (n * a1 * n⁻¹) * ((n * y * n⁻¹) * a0⁻¹ * (n * y * n⁻¹)⁻¹) *
        ((n * y * n⁻¹) * y⁻¹) * a1⁻¹ := by
      rw [hq', commutatorElement_def]
      group
    rw [e, hny, mul_inv_cancel, mul_one]
    refine mul_mem (mul_mem (mul_mem ha0 ?_) ?_) (inv_mem ha1)
    · exact (mem_normalizer_iff.mp (hDA (hQD hnQ)) a1).mp ha1
    · exact (mem_normalizer_iff.mp (hDA (hXD (hPX hy))) _).mp (inv_mem ha0)
  refine ⟨hQX, fun q hq => ?_⟩
  rw [← normalizerResidualAction_eq_normalizerFrattiniConj]
  ext w
  induction w using QuotientGroup.induction_on with
  | H w =>
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [normalizerResidualAction_mk, MulAut.one_apply]
      congr 1
      rw [QuotientGroup.eq]
      have h1 : ⁅q, (x : H)⁆ ∈ A := hQX (commutator_mem_commutator hq x.2)
      have h2 : (x : H)⁻¹ * ⁅q, (x : H)⁆ * (x : H)⁻¹⁻¹ ∈ A :=
        (mem_normalizer_iff.mp (hDA (hXD (inv_mem x.2))) _).mp h1
      have e : (x : H)⁻¹ * ⁅q, (x : H)⁆ * (x : H)⁻¹⁻¹ =
          (((X.normalizerMonoidHom ⟨q, hDX (hQD hq)⟩ x : X)⁻¹ * x : X) : H)⁻¹ := by
        rw [commutatorElement_def]
        change _ = ((q * (x : H) * q⁻¹)⁻¹ * (x : H))⁻¹
        group
      rw [e] at h2
      have h3 := inv_mem h2
      rw [inv_inv] at h3
      exact (mem_map_iff_mem X.subtype_injective).mp h3

end CFSG.Quasithin.H13.NQBlock
