module

public import CFSG.RankThree.PartOne.S9.Extraction.FittingDetection
public import CFSG.RankThree.PartOne.S9.Extraction.SylowComplement
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.RankThree.PartOne.Extract

open Subgroup CFSG
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem exists_fixed_in_coset {p : ℕ} [Fact p.Prime] (b : H) (hb : IsPGroup p (zpowers b))
    (J U : Subgroup H) [J.Normal] (hJ : ¬ p ∣ Nat.card J)
    (hbU : b ∈ normalizer (U : Set H))
    (htriv : ∀ a ∈ zpowers b, ∀ u ∈ U, u⁻¹ * (a * u * a⁻¹) ∈ J) {u : H} (hu : u ∈ U) :
    ∃ c ∈ U ⊓ centralizer ({b} : Set H), u⁻¹ * c ∈ J := by
  have hzU : zpowers b ≤ normalizer (U : Set H) := zpowers_le.mpr hbU
  have hKcop : ¬ p ∣ Nat.card (J ⊓ U : Subgroup H) := fun h =>
    hJ (h.trans (card_dvd_of_le inf_le_left))
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed
    (A := ↥(zpowers b)) (G := H) p hb (MulAut.conj.comp (zpowers b).subtype) (J ⊓ U) hKcop
    u).2 (fun a x hx => by
      have hxu : u⁻¹ * x ∈ J ⊓ U := hx
      have hau : (a : H) ∈ normalizer (U : Set H) := hzU a.2
      have hJn : ∀ y ∈ J, (a : H) * y * (a : H)⁻¹ ∈ J := fun y hy =>
        Normal.conj_mem inferInstance y hy a
      have e : u⁻¹ * ((MulAut.conj.comp (zpowers b).subtype) a x) =
          (u⁻¹ * ((a : H) * u * (a : H)⁻¹)) * ((a : H) * (u⁻¹ * x) * (a : H)⁻¹) := by
        simp only [MonoidHom.comp_apply, coe_subtype, MulAut.conj_apply]
        group
      rw [e]
      have hxu' := mem_inf.mp hxu
      refine mul_mem (mem_inf.mpr ⟨htriv a a.2 u hu, ?_⟩) (mem_inf.mpr ⟨hJn _ hxu'.1, ?_⟩)
      · exact mul_mem (inv_mem hu) ((mem_normalizer_iff.mp hau u).mp hu)
      · exact (mem_normalizer_iff.mp hau _).mp hxu'.2)
  have hcU : c ∈ U := by
    have := mul_mem hu (mem_inf.mp hc).2
    simpa using this
  refine ⟨c, mem_inf.mpr ⟨hcU, ?_⟩, (mem_inf.mp hc).1⟩
  rw [mem_centralizer_singleton_iff]
  have h := hfix ⟨b, mem_zpowers b⟩
  change b * c * b⁻¹ = c at h
  calc c * b = b * c * b⁻¹ * b := by rw [h]
    _ = b * c := by group

theorem coprime_card_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup H}
    (hK : IsPGroup 2 K) : Nat.Coprime p (Nat.card K) := by
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

theorem commutator_commutator_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A K : Subgroup H}
    (hA : IsPGroup p A) (hK : IsPGroup 2 K) (hAK : A ≤ normalizer (K : Set H)) :
    ⁅⁅K, A⁆, A⁆ = ⁅K, A⁆ :=
  CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp A K hA hAK
    (coprime_card_of_isPGroup_two hp hp2 hK)

theorem front_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (A S X : Subgroup H) (b : H)
    (hA : IsPGroup p A) (hSn : S.Normal) (hSs : Group.IsSolvable S) (hpS : ¬ p ∣ Nat.card S)
    (hbA : b ∈ A) (hbc : ∀ a ∈ A, a * b = b * a)
    (hXA : A ≤ normalizer (X : Set H)) (hX2 : IsPGroup 2 X) (hXS : X ≤ S) (hXc : ⁅X, A⁆ = X)
    (hXJ : ¬ X ≤ pCore 2 H) (hbX : ∀ x ∈ X, b * x = x * b) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ R Q : Subgroup H, R ≤ pCore 2 H ⊔ X ∧
      A ≤ normalizer (R : Set H) ∧ ⁅R, A⁆ = R ∧ ¬ R ≤ pCore 2 H ∧
      (∀ U : Subgroup H, U < R → A ≤ normalizer (U : Set H) → ⁅U, A⁆ = U → U ≤ pCore 2 H) ∧
      IsSylowOf q Q ((pCore q (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))) ∧
      R ≤ normalizer (Q : Set H) ∧ A ≤ normalizer (Q : Set H) ∧ ⁅R, Q⁆ ≠ ⊥ ∧
      (∀ r ∈ R, b * r = r * b) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hSn' : S.Normal := hSn
  set J := pCore 2 H with hJ
  set π := QuotientGroup.mk' J with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hJ2 : IsPGroup 2 J := pCore_isPGroup
  have hJn : J.Normal := inferInstance
  have hker : ∀ Y : Subgroup H, Y.map π = ⊥ ↔ Y ≤ J := fun Y => by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  obtain ⟨R₀, hR₀X, hAR₀, hR₀c, hR₀J, hR₀min⟩ := exists_minimal_commGen A J X hXA hXc hXJ
  have hR₀2 : IsPGroup 2 R₀ := hX2.to_le hR₀X
  have hbR₀ : ∀ x ∈ R₀, b * x = x * b := fun x hx => hbX x (hR₀X hx)
  have hSbn : (S.map π).Normal := hSn'.map π hπs
  have hSbs : Group.IsSolvable (S.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective S)
  have hpSb : ¬ p ∣ Nat.card (S.map π) := fun h => hpS (h.trans (card_map_dvd S π))
  have hYbS : R₀.map π ≤ S.map π := map_mono (hR₀X.trans hXS)
  have hYb2 : IsPGroup 2 (R₀.map π) := hR₀2.map π
  have hYb : R₀.map π ≠ ⊥ := fun h => hR₀J ((hker R₀).mp h)
  obtain ⟨q, hq, hq2, hqp, hcomm⟩ := exists_prime_core_not_centralized p (S.map π) (R₀.map π)
    hSbs pCore_two_quotient_eq_bot hpSb hYbS hYb2 hYb
  obtain ⟨Q, hQ, hQA, hπQ, hFr⟩ := exists_invariant_sylow hp hq hp2 hq2 hqp A hA
  set U : Subgroup H := normalizer (Q : Set H) ⊓ (R₀ ⊔ J) with hU
  have hRJ2 : IsPGroup 2 (R₀ ⊔ J : Subgroup H) := hR₀2.to_sup_of_normal_right hJ2
  have hU2 : IsPGroup 2 U := hRJ2.to_le inf_le_right
  have hAU : A ≤ normalizer (U : Set H) :=
    le_normalizer_inf (hQA.trans le_normalizer) (le_normalizer_sup hAR₀ le_normalizer_of_normal)
  have hπRJ : (R₀ ⊔ J).map π = R₀.map π := by
    rw [Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hπU : U.map π = R₀.map π := by
    refine le_antisymm (hπRJ ▸ map_mono inf_le_right) ?_
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨m, hm, j, hj, hrmj⟩ := hFr r
    have hmr : m = r * j⁻¹ := by rw [hrmj]; group
    have hmU : m ∈ U := mem_inf.mpr ⟨hm, hmr ▸ mul_mem (mem_sup_left hr)
      (inv_mem (mem_sup_right hj))⟩
    refine ⟨m, hmU, ?_⟩
    have hπj : π j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    rw [hrmj, map_mul, hπj, mul_one]
  set U₁ : Subgroup H := U ⊓ centralizer ({b} : Set H) with hU₁
  have hU₁2 : IsPGroup 2 U₁ := hU2.to_le inf_le_left
  have hAU₁ : A ≤ normalizer (U₁ : Set H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro x
    have hax : (a : H) ∈ normalizer (U : Set H) := hAU ha
    have hcb : Commute b a := (hbc a ha).symm
    constructor
    · intro hx
      have hx' := mem_inf.mp hx
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hax x).mp hx'.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hxb : Commute b x := (mem_centralizer_singleton_iff.mp hx'.2).symm
      exact ((hcb.mul_right hxb).mul_right hcb.inv_right).symm.eq
    · intro hx
      have hx' := mem_inf.mp hx
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hax x).mpr hx'.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hxb : Commute b (a * x * a⁻¹) := (mem_centralizer_singleton_iff.mp hx'.2).symm
      have : Commute b x := by
        have h1 := (hcb.inv_right.mul_right hxb).mul_right hcb
        rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h1
      exact this.symm.eq
  have hJp : ¬ p ∣ Nat.card J :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (coprime_card_of_isPGroup_two hp hp2 hJ2)
  have htriv : ∀ a ∈ zpowers b, ∀ u ∈ U, u⁻¹ * (a * u * a⁻¹) ∈ J := by
    intro a ha u hu
    have hu' : u ∈ ((R₀ ⊔ J : Subgroup H) : Set H) := (mem_inf.mp hu).2
    rw [mul_normal R₀ J] at hu'
    obtain ⟨r, hr, j, hj, rfl⟩ := hu'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    have hcr : (b ^ n) * r = r * (b ^ n) := (Commute.zpow_left (hbR₀ r hr) n).eq
    have e : (r * j)⁻¹ * (b ^ n * (r * j) * (b ^ n)⁻¹) =
        j⁻¹ * (b ^ n * j * (b ^ n)⁻¹) := by
      calc (r * j)⁻¹ * (b ^ n * (r * j) * (b ^ n)⁻¹)
          = j⁻¹ * (r⁻¹ * (b ^ n * r) * j * (b ^ n)⁻¹) := by group
        _ = j⁻¹ * (b ^ n * j * (b ^ n)⁻¹) := by rw [hcr]; group
    rw [e]
    exact mul_mem (inv_mem hj) (Normal.conj_mem hJn j hj (b ^ n))
  have hπU₁ : U₁.map π = R₀.map π := by
    refine le_antisymm (hπU ▸ map_mono inf_le_left) ?_
    rw [← hπU]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨c, hcU₁, hcu⟩ := exists_fixed_in_coset b (hA.to_le (zpowers_le.mpr hbA)) J U hJp
      (hAU hbA) htriv hu
    exact ⟨c, hcU₁, (QuotientGroup.eq.mpr hcu).symm⟩
  set W : Subgroup H := ⁅U₁, A⁆ with hW
  have hWA : A ≤ normalizer (W : Set H) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A U₁ hAU₁
  have hWc : ⁅W, A⁆ = W := commutator_commutator_eq hp hp2 hA hU₁2 hAU₁
  have hπW : W.map π = R₀.map π := by
    rw [hW, map_commutator, hπU₁, ← map_commutator, hR₀c]
  have hWJ : ¬ W ≤ J := fun h => hR₀J ((hker R₀).mp (hπW ▸ (hker W).mpr h))
  obtain ⟨R, hRW, hAR, hRc, hRJ, hRmin⟩ := exists_minimal_commGen A J W hWA hWc hWJ
  have hRU₁ : R ≤ U₁ :=
    hRW.trans (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing U₁ A hAU₁)
  have hRU : R ≤ U := hRU₁.trans inf_le_left
  have hπR_le : R.map π ≤ R₀.map π := hπRJ ▸ map_mono (hRU.trans inf_le_right)
  set M : Subgroup H := R₀ ⊓ (R ⊔ J) with hM
  have hMA : A ≤ normalizer (M : Set H) :=
    le_normalizer_inf hAR₀ (le_normalizer_sup hAR le_normalizer_of_normal)
  have hM2 : IsPGroup 2 M := hR₀2.to_le inf_le_left
  set M₁ : Subgroup H := ⁅M, A⁆ with hM₁
  have hM₁M : M₁ ≤ M := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing M A hMA
  have hM₁A : A ≤ normalizer (M₁ : Set H) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A M hMA
  have hM₁c : ⁅M₁, A⁆ = M₁ := commutator_commutator_eq hp hp2 hA hM2 hMA
  have hπRJ' : (R ⊔ J).map π = R.map π := by
    rw [Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hπM : M.map π = R.map π := by
    refine le_antisymm (hπRJ' ▸ map_mono inf_le_right) ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxRJ : x ∈ ((R₀ ⊔ J : Subgroup H) : Set H) := (mem_inf.mp (hRU hx)).2
    rw [mul_normal R₀ J] at hxRJ
    obtain ⟨r, hr, j, hj, rfl⟩ := hxRJ
    have hπj : π j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    refine ⟨r, mem_inf.mpr ⟨hr, ?_⟩, ?_⟩
    · have : r = (r * j) * j⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left hx) (inv_mem (mem_sup_right hj))
    · rw [map_mul, hπj, mul_one]
  have hπM₁ : M₁.map π = R.map π := by
    rw [hM₁, map_commutator, hπM, ← map_commutator, hRc]
  have hM₁J : ¬ M₁ ≤ J := fun h => hRJ ((hker R).mp (hπM₁ ▸ (hker M₁).mpr h))
  have hM₁eq : M₁ = R₀ := by
    by_contra hne
    exact hM₁J (hR₀min M₁ (lt_of_le_of_ne (hM₁M.trans inf_le_left) hne) hM₁A hM₁c)
  have hR₀M : R₀ ≤ M := hM₁eq ▸ hM₁M
  have hπR : R.map π = R₀.map π := le_antisymm hπR_le ((map_mono hR₀M).trans hπM.le)
  refine ⟨q, hq, hq2, hqp, R, Q, ?_, hAR, hRc, hRJ, hRmin, hQ, hRU.trans inf_le_left, hQA, ?_, ?_⟩
  · exact (hRU.trans inf_le_right).trans ((sup_le_sup_right hR₀X J).trans_eq (sup_comm X J))
  · intro hRQ
    apply hcomm
    have := congrArg (Subgroup.map π) hRQ
    rwa [map_commutator, hπR, hπQ, Subgroup.map_bot] at this
  · intro r hr
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp (hRU₁ hr)).2).symm

end CFSG.RankThree.PartOne.Extract
