module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.CanonicalSection

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.AGLEmbedding
open scoped commutatorElement

theorem exists_perfect_normal_sup_eq_top {G : Type} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) {H : Subgroup G} (N : Subgroup H) [N.Normal]
    (hN : IsPGroup 2 N) (hQ : Group.IsPerfect (H ⧸ N)) :
    ∃ S : Subgroup H, S.Normal ∧ Group.IsPerfect S ∧ S ⊔ N = ⊤ ∧ Nat.Coprime S.index p := by
  classical
  have hex : ({S : Subgroup H | S.Normal ∧ S ⊔ N = ⊤} : Set (Subgroup H)).Nonempty :=
    ⟨⊤, inferInstance, top_sup_eq _⟩
  obtain ⟨S, ⟨hSn, hSN⟩, hmin⟩ := WellFounded.has_min (measure fun S : Subgroup H => Nat.card S).wf
    _ hex
  have hSmap : S.map (QuotientGroup.mk' N) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N x
    have : h ∈ S ⊔ N := hSN ▸ Subgroup.mem_top h
    obtain ⟨s, hs, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 this
    refine ⟨s, hs, ?_⟩
    simp [(QuotientGroup.eq_one_iff n).2 hn]
  have hcomm : ⁅S, S⁆ ⊔ N = ⊤ := by
    have h1 : (⁅S, S⁆).map (QuotientGroup.mk' N) = ⊤ := by
      rw [Subgroup.map_commutator, hSmap, ← _root_.commutator_def,
        Group.IsPerfect.commutator_eq_top]
    rw [eq_top_iff]
    intro h _
    have : QuotientGroup.mk' N h ∈ (⁅S, S⁆).map (QuotientGroup.mk' N) := h1 ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hch⟩ := this
    have hcn : c⁻¹ * h ∈ N := by
      have : ((c : H) : H ⧸ N) = (h : H ⧸ N) := hch
      exact QuotientGroup.eq.1 this
    have := Subgroup.mul_mem_sup (Subgroup.mem_sup_left hc : c ∈ ⁅S, S⁆ ⊔ N)
      (Subgroup.mem_sup_right hcn : c⁻¹ * h ∈ ⁅S, S⁆ ⊔ N)
    simpa using this
  have hle : ⁅S, S⁆ ≤ S := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
    S.mul_mem (S.mul_mem (S.mul_mem h₁ h₂) (S.inv_mem h₁)) (S.inv_mem h₂)
  have hSS : ⁅S, S⁆ = S := by
    by_contra hne
    have hlt : Nat.card (⁅S, S⁆ : Subgroup H) < Nat.card S :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
    exact hmin ⁅S, S⁆ ⟨inferInstance, hcomm⟩ hlt
  have hSperf : Group.IsPerfect S := by
    rw [Group.isPerfect_def]
    have h1 := Subgroup.map_subtype_commutator S
    rw [hSS] at h1
    refine Subgroup.map_injective S.subtype_injective ?_
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨S, hSn, hSperf, hSN, ?_⟩
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' S).comp N.subtype) := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective S q
      have : h ∈ S ⊔ N := hSN ▸ Subgroup.mem_top h
      obtain ⟨s, hs, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 this
      refine ⟨⟨n, hn⟩, ?_⟩
      show (n : H ⧸ S) = ((s * n : H) : H ⧸ S)
      rw [QuotientGroup.eq]
      have : n⁻¹ * (s * n) ∈ S := by
        have := hSn.conj_mem s hs n⁻¹
        simpa [mul_assoc] using this
      exact this
    have hdvd : Nat.card (H ⧸ S) ∣ Nat.card N := Subgroup.card_dvd_of_surjective hsurj
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hN
    rw [hk] at hdvd
    rw [← Subgroup.index_eq_card] at hdvd
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hpd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
        (hp.out.dvd_of_dvd_pow (hpd.trans hdvd))))


section MapSubtype

variable {G : Type} [Group G] {H : Subgroup G} (S : Subgroup H)

theorem conj_mem_map_subtype [hSn : S.Normal] :
    ∀ h ∈ H, ∀ l ∈ S.map H.subtype, h * l * h⁻¹ ∈ S.map H.subtype := by
  intro h hh l hl
  obtain ⟨s, hs, rfl⟩ := hl
  exact ⟨(⟨h, hh⟩ : H) * s * (⟨h, hh⟩ : H)⁻¹, hSn.conj_mem s hs _, rfl⟩

theorem isPerfect_map_subtype (hS : Group.IsPerfect S) : Group.IsPerfect (S.map H.subtype) := by
  have : Group.IsPerfect S := hS
  let e : S ≃* S.map H.subtype := Subgroup.equivMapOfInjective S H.subtype H.subtype_injective
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem relIndex_map_subtype : (S.map H.subtype).relIndex H = S.index := by
  have h0 : (S.map H.subtype).subgroupOf H = S :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective S
  rw [Subgroup.relIndex, h0]

theorem perfectCoreOf_of_normal_perfect {p : ℕ} [S.Normal] (hS : Group.IsPerfect S)
    (hidx : Nat.Coprime S.index p) : PerfectCoreOf p H :=
  ⟨S.map H.subtype, Subgroup.map_subtype_le S, conj_mem_map_subtype S, isPerfect_map_subtype S hS,
    by rw [relIndex_map_subtype]; exact hidx⟩

theorem perfectCoreCell_of_normal_perfect {p : ℕ} [S.Normal] (hS : Group.IsPerfect S)
    (hidx : Nat.Coprime S.index p) (hKT : KernelTrivialAt S p) : PerfectCoreCell p H := by
  refine ⟨S.map H.subtype, Subgroup.map_subtype_le S, conj_mem_map_subtype S,
    isPerfect_map_subtype S hS, by rw [relIndex_map_subtype]; exact hidx, ?_⟩
  exact (kernelTrivialAt_iff_of_mulEquiv
    (Subgroup.equivMapOfInjective S H.subtype H.subtype_injective) p).1 hKT

end MapSubtype

theorem perfectCoreOf_of_quotient {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {H : Subgroup G} (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N)
    (hQ : Group.IsPerfect (H ⧸ N)) : PerfectCoreOf p H := by
  obtain ⟨S, hSn, hSperf, -, hidx⟩ := exists_perfect_normal_sup_eq_top hp2 N hN hQ
  exact perfectCoreOf_of_normal_perfect S hSperf hidx

theorem perfectCoreOf_of_mulEquiv {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {H : Subgroup G} (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N) {Q : Type}
    [Group Q] (hQ : Group.IsPerfect Q) (e : (↥H ⧸ N) ≃* Q) : PerfectCoreOf p H := by
  have : Group.IsPerfect Q := hQ
  exact perfectCoreOf_of_quotient hp2 N hN
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
