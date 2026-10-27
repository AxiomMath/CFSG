module

public import CFSG.RankThree.PartOne.S9.Extraction.Basic
public import CFSG.Dihedral.OriginalSylowControl

public section

namespace CFSG.RankThree.PartOne.Extract

open Subgroup CFSG CFSG.DihedralBlueprint

variable {H : Type} [Group H] [Finite H]

theorem isSylowOf_of_isSylowIn {q : ℕ} [Fact q.Prime] {Q F : Subgroup H} (h : IsSylowIn q Q F) :
    IsSylowOf q Q F := by
  obtain ⟨Q', hQ'⟩ := (isSylowIn_iff_exists_sylow q Q F).mp h
  refine ⟨h.1, h.2.1, ?_⟩
  have hsub : Q.subgroupOf F = (Q' : Subgroup F) := by
    rw [← hQ']
    exact comap_map_eq_self_of_injective F.subtype_injective _
  have : Q.relIndex F = (Q' : Subgroup F).index := by
    rw [Subgroup.relIndex, hsub]
  rw [this]
  exact Sylow.not_dvd_index Q'

theorem exists_invariant_sylow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (A : Subgroup H) (hA : IsPGroup p A) :
    ∃ Q : Subgroup H,
      IsSylowOf q Q ((pCore q (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))) ∧
      A ≤ normalizer (Q : Set H) ∧
      Q.map (QuotientGroup.mk' (pCore 2 H)) = pCore q (H ⧸ pCore 2 H) ∧
      (∀ r : H, ∃ m ∈ normalizer (Q : Set H), ∃ j ∈ pCore 2 H, r = m * j) := by
  have : Fact q.Prime := ⟨hq⟩
  set J := pCore 2 H with hJ
  set π := QuotientGroup.mk' J with hπ
  set Oq := pCore q (H ⧸ J) with hOq
  set F := Oq.comap π with hF
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hFn : F.Normal := (inferInstance : Oq.Normal).comap π
  have hFcard : Nat.card F = Nat.card J * Nat.card Oq := card_comap_mk' J Oq
  obtain ⟨a, ha⟩ := (pCore_isPGroup : IsPGroup 2 J).exists_card_eq
  obtain ⟨c, hc⟩ := (pCore_isPGroup : IsPGroup q Oq).exists_card_eq
  have hpF : Nat.Coprime p (Nat.card F) := by
    rw [hFcard, ha, hc]
    exact Nat.Coprime.mul_right
      (Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
      (Nat.Coprime.pow_right c ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp)))
  obtain ⟨Q, hQ, hQA⟩ := normalized_exists_sylow p q hp hq A F hA le_normalizer_of_normal hpF
  have hQF : Q ≤ F := hQ.1
  have hQp : IsPGroup q Q := hQ.2.1
  obtain ⟨Q', hQ'⟩ := (isSylowIn_iff_exists_sylow q Q F).mp hQ
  have hQcard : Nat.card Q = q ^ c := by
    have h1 : Nat.card Q = Nat.card (Q' : Subgroup F) := by
      rw [← hQ']
      exact card_map_of_injective F.subtype_injective
    rw [h1, Sylow.card_eq_multiplicity Q', hFcard, ha, hc]
    congr 1
    rw [Nat.factorization_mul (pow_ne_zero a two_ne_zero) (pow_ne_zero c hq.ne_zero),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.Prime.factorization_pow hq, Finsupp.single_apply, Finsupp.single_apply]
    simp [Ne.symm hq2]
  have hJ2 : IsPGroup 2 J := pCore_isPGroup
  have hdisj : Disjoint J Q := IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) J Q hJ2 hQp
  have hkerQ : (π.comp Q.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxJ : (x : H) ∈ J := (QuotientGroup.eq_one_iff (x : H)).mp (MonoidHom.mem_ker.mp hx)
    have : (x : H) ∈ J ⊓ Q := ⟨hxJ, x.2⟩
    rw [hdisj.eq_bot, mem_bot] at this
    exact Subtype.ext this
  have hπQcard : Nat.card (Q.map π) = Nat.card Q := by
    have h := card_ker_mul_card_range (π.comp Q.subtype)
    rw [hkerQ, MonoidHom.range_comp, range_subtype] at h
    simpa using h
  have hπQle : Q.map π ≤ Oq := map_le_iff_le_comap.mpr hQF
  have hπQ : Q.map π = Oq :=
    eq_of_le_of_card_ge hπQle (by rw [hπQcard, hQcard, hc])
  have hFQJ : F = Q ⊔ J := by
    rw [hF, ← hπQ, comap_map_eq, hπ, QuotientGroup.ker_mk']
  refine ⟨Q, isSylowOf_of_isSylowIn hQ, hQA, hπQ, fun r => ?_⟩
  have htop := Sylow.normalizer_sup_eq_top Q'
  rw [hQ'] at htop
  have hr : r ∈ ((normalizer (Q : Set H) ⊔ F : Subgroup H) : Set H) := by
    rw [htop]
    exact mem_top r
  rw [mul_normal (normalizer (Q : Set H)) F] at hr
  obtain ⟨n, hn, f, hf, rfl⟩ := hr
  have hf' : f ∈ ((Q ⊔ J : Subgroup H) : Set H) := hFQJ ▸ hf
  rw [mul_normal Q J] at hf'
  obtain ⟨z, hz, j, hj, rfl⟩ := hf'
  exact ⟨n * z, mul_mem hn (le_normalizer hz), j, hj, by rw [mul_assoc]⟩

end CFSG.RankThree.PartOne.Extract
