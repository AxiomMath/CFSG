module

public import CFSG.RankThree.PartOne.S9.Extraction.FrattiniAction
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartOne.Extract

open Subgroup CFSG
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem critical_tail {p q : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    {A S R Q : Subgroup H} [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 3)
    (hSn : S.Normal) (hpS : ¬ p ∣ Nat.card S) (hRS : R ≤ S) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ normalizer (R : Set H)) (hRc : ⁅R, A⁆ = R) (hRJ : ¬ R ≤ pCore 2 H)
    (hmin : ∀ U : Subgroup H, U < R → A ≤ normalizer (U : Set H) → ⁅U, A⁆ = U →
      U ≤ pCore 2 H)
    (hQp : IsPGroup q Q) (hRQ : R ≤ normalizer (Q : Set H)) (hRQ' : ⁅R, Q⁆ ≠ ⊥) :
    ∃ D : Subgroup H, D ≤ Q ∧ (D.subgroupOf Q).Characteristic ∧ D ≠ ⊥ ∧ ⁅R, D⁆ ≠ ⊥ ∧
      (∀ d ∈ D, d ^ q = 1) ∧ ⁅D, Q⁆ ≤ D ⊓ centralizer (D : Set H) ∧
      (∀ U : Subgroup H, U < R → A ≤ normalizer (U : Set H) → ⁅U, A⁆ = U →
        U ≤ pCore 2 H ∧ U ≤ centralizer (D : Set H)) ∧
      Nat.card (A ⊓ centralizer (R : Set H) : Subgroup H) = p ^ 2 ∧
      ∀ C : Subgroup H, C ≤ A → C.Normal → C ≤ A ⊓ centralizer (R : Set H) := by
  have hp : p.Prime := Fact.out
  have : Fact q.Prime := ⟨hq⟩
  have hJ2 : IsPGroup 2 (pCore 2 H) := pCore_isPGroup
  have hJn : (pCore 2 H).Normal := inferInstance
  have hJdisj : Disjoint (pCore 2 H) Q := IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) _ _ hJ2 hQp
  have hQnt : Nontrivial Q := by
    refine (nontrivial_iff_ne_bot Q).mpr fun h => hRQ' ?_
    rw [h]
    exact commutator_bot_right R
  obtain ⟨D', hD'char, hD'ne, hD'comm, hD'exp, hD'fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hQp
  set D : Subgroup H := D'.map Q.subtype with hD
  have hDQ : D ≤ Q := map_subtype_le D'
  have hmapTop : (⊤ : Subgroup Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hRD : ⁅R, D⁆ ≠ ⊥ := by
    intro hRD
    let : MulDistribMulAction R Q := conjMulDistribMulActionOfLeNormalizer R Q hRQ
    let φ : R →* MulAut Q := MulDistribMulAction.toMulAut R Q
    have hle : φ.range ≤ fixingSubgroup (MulAut Q) (D' : Set Q) := by
      rintro _ ⟨r, rfl⟩
      rw [mem_fixingSubgroup_iff (MulAut Q)]
      intro y hy
      have hcomm : ⁅(r : H), ((y : Q) : H)⁆ ∈ ⁅R, D⁆ :=
        commutator_mem_commutator r.2 (mem_map_of_mem Q.subtype hy)
      rw [hRD, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
      apply Subtype.ext
      change (r : H) * (y : H) * (r : H)⁻¹ = y
      rw [hcomm]
      group
    have hq' : IsPGroup q φ.range := hD'fix.to_le hle
    have h2' : IsPGroup 2 φ.range := hR2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have hbot : φ.range = ⊥ :=
      disjoint_self.mp (IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) _ _ h2' hq')
    apply hRQ'
    rw [commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [mem_centralizer_iff]
    intro x hx
    have h1 : φ ⟨r, hr⟩ = 1 := by
      have : φ ⟨r, hr⟩ ∈ φ.range := ⟨_, rfl⟩
      rwa [hbot, mem_bot] at this
    have h2 := congrArg (fun τ : MulAut Q => ((τ ⟨x, hx⟩ : Q) : H)) h1
    change r * x * r⁻¹ = x at h2
    calc x * r = (r * x * r⁻¹) * r := by rw [h2]
      _ = r * x := by group
  have hUQ : ∀ U : Subgroup H, U ≤ R → U ≤ pCore 2 H → U ≤ centralizer (Q : Set H) := by
    intro U hUR hUJ u hu
    rw [mem_centralizer_iff]
    intro x hx
    have huN : u ∈ normalizer (Q : Set H) := hRQ (hUR hu)
    have h1 : u * x * u⁻¹ ∈ Q := (mem_normalizer_iff.mp huN x).mp hx
    have hQ' : u * x * u⁻¹ * x⁻¹ ∈ Q := mul_mem h1 (inv_mem hx)
    have hJ' : u * x * u⁻¹ * x⁻¹ ∈ pCore 2 H := by
      have : u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
      rw [this]
      exact mul_mem (hUJ hu) (Normal.conj_mem hJn u⁻¹ (inv_mem (hUJ hu)) x)
    have h2 : u * x * u⁻¹ * x⁻¹ ∈ pCore 2 H ⊓ Q := ⟨hJ', hQ'⟩
    rw [hJdisj.eq_bot, mem_bot] at h2
    have h3 : x * u = u * x := by
      calc x * u = (u * x * u⁻¹ * x⁻¹)⁻¹ * (u * x) := by group
        _ = u * x := by rw [h2]; group
    exact h3
  refine ⟨D, hDQ, ?_, ?_, hRD, ?_, ?_, ?_, ?_, ?_⟩
  · have : D.subgroupOf Q = D' := comap_map_eq_self_of_injective Q.subtype_injective D'
    rw [this]
    exact hD'char
  · exact (map_eq_bot_iff_of_injective _ Q.subtype_injective).not.mpr hD'ne
  · rintro _ ⟨x, hx, rfl⟩
    have := hD'exp x hx
    change (x : H) ^ q = 1
    rw [← coe_pow, this, coe_one]
  · have h1 : ⁅D, Q⁆ = ⁅D', (⊤ : Subgroup Q)⁆.map Q.subtype := by
      rw [map_commutator, hmapTop]
    rw [h1]
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hD'comm hz
    refine mem_inf.mpr ⟨⟨z, hz'.1, rfl⟩, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := mem_centralizer_iff.mp hz'.2 y hy
    exact congrArg Subtype.val this
  · intro U hUR hAU hUc
    have hUJ := hmin U hUR hAU hUc
    exact ⟨hUJ, (hUQ U hUR.le hUJ).trans (centralizer_le (SetLike.coe_subset_coe.mpr hDQ))⟩
  · exact card_inf_centralizer_eq hp2 hA hAR hR2 hRc hRJ hmin
  · intro C hCA hCn
    refine le_inf hCA ?_
    have hCp : IsPGroup p C := (IsElementaryAbelian.isPGroup p A).to_le hCA
    have hCS : C ⊓ S = ⊥ := by
      have hp' : IsPGroup p (C ⊓ S : Subgroup H) := hCp.to_le inf_le_left
      obtain ⟨j, hj⟩ := hp'.exists_card_eq
      have hdvd : Nat.card (C ⊓ S : Subgroup H) ∣ Nat.card S := card_dvd_of_le inf_le_right
      have hj0 : j = 0 := by
        by_contra hne
        apply hpS
        rw [hj] at hdvd
        exact (dvd_pow_self p hne).trans hdvd
      rw [hj0, pow_zero] at hj
      exact (eq_bot_iff_card _).mpr hj
    intro c hc
    rw [mem_centralizer_iff]
    intro r hr
    have hn : S.Normal := hSn
    have h1 : ⁅c, r⁆ ∈ ⁅C, S⁆ := commutator_mem_commutator hc (hRS hr)
    have h2 : ⁅C, S⁆ ≤ C ⊓ S := commutator_le_inf C S
    rw [hCS] at h2
    have h3 := h2 h1
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm

end CFSG.RankThree.PartOne.Extract
