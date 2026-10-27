module

public import CFSG.RankThree.LocalRank.ThetaCoreQuotients
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.RankThree.PartOne.S8

open CFSG CFSG.RankThree.LocalRank

variable {X : Type*} [Group X]

theorem exists_lift_orderOf_pow [Finite X] {p : ℕ} (hp : p.Prime) (N : Subgroup X) [N.Normal]
    {e : X ⧸ N} (he : ∃ k : ℕ, orderOf e = p ^ k) :
    ∃ x : X, (x : X ⧸ N) = e ∧ ∃ k : ℕ, orderOf x = p ^ k := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective e
  obtain ⟨b, hb⟩ := he
  have hn : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  by_cases hb0 : b = 0
  · refine ⟨1, ?_, 0, by simp⟩
    rw [hb0, pow_zero] at hb
    rw [orderOf_eq_one_iff.mp hb]
    rfl
  · have hpb : 1 < p ^ b := Nat.one_lt_pow hb0 hp.one_lt
    have hcop : Nat.Coprime m (p ^ b) :=
      Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
    obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpb
    refine ⟨y ^ (m * m'), ?_, ?_⟩
    · have : ((y ^ (m * m') : X) : X ⧸ N) = (y : X ⧸ N) ^ (m * m') := by simp
      rw [this, ← pow_mod_orderOf, hb, hm', pow_one]
    · have hdvd : orderOf (y ^ (m * m')) ∣ p ^ a := by
        apply orderOf_dvd_of_pow_eq_one
        have h1 : m * m' * p ^ a = (p ^ a * m) * m' := by ring
        rw [← pow_mul, h1, ← hnm, pow_mul, pow_orderOf_eq_one, one_pow]
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      exact ⟨k, hk⟩

theorem isPGroup_zpowers_of_orderOf_pow {p : ℕ} {a : X} (ha : ∃ k : ℕ, orderOf a = p ^ k) :
    IsPGroup p (Subgroup.zpowers a) := by
  obtain ⟨k, hk⟩ := ha
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

theorem map_theta_centralizer_singleton [Finite X] {p : ℕ} (hp : p.Prime) (N : Subgroup X)
    [N.Normal]
    (hNs : Group.IsSolvable N) (hNp : ¬ p ∣ Nat.card N) {a : X}
    (ha : ∃ k : ℕ, orderOf a = p ^ k) :
    (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set X))).map
        (QuotientGroup.mk' N) =
      inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({(a : X ⧸ N)} : Set (X ⧸ N))) := by
  have h := (solvable_prime_complement_core_quotient_centralizers hp N hNs hNp).2.2.2
    (Subgroup.zpowers a) (isPGroup_zpowers_of_orderOf_pow ha)
  rwa [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

theorem map_thetaT_le [Finite X] {p : ℕ} (hp : p.Prime) (N : Subgroup X) [N.Normal]
    (hNs : Group.IsSolvable N) (hNp : ¬ p ∣ Nat.card N) {E : Subgroup X} (hE : IsPGroup p E) :
    (thetaT p E).map (QuotientGroup.mk' N) ≤ thetaT p (E.map (QuotientGroup.mk' N)) := by
  have : Fact p.Prime := ⟨hp⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : x ∈ thetaT p E := hx
  simp only [thetaT, Subgroup.mem_iInf]
  intro ē hē hē1
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hē
  have he1 : e ≠ 1 := fun h => hē1 (by rw [h]; exact map_one _)
  have hx' : x ∈ inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({e} : Set X)) := by
    simp only [thetaT, Subgroup.mem_iInf] at hx0
    exact hx0 e he he1
  have hord : ∃ k : ℕ, orderOf e = p ^ k := by
    obtain ⟨n, hn⟩ := hE.exists_orderOf_eq_pow ⟨e, he⟩
    exact ⟨n, (Subgroup.orderOf_coe (⟨e, he⟩ : E)).trans hn⟩
  have hx'' : (QuotientGroup.mk' N) x ∈
      (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set X))).map
        (QuotientGroup.mk' N) := Subgroup.mem_map_of_mem _ hx'
  rw [map_theta_centralizer_singleton hp N hNs hNp hord] at hx''
  exact hx''

theorem map_localCoreProduct_le [Finite X] {p : ℕ} (hp : p.Prime) (N : Subgroup X) [N.Normal]
    (hNs : Group.IsSolvable N) (hNp : ¬ p ∣ Nat.card N) {E : Subgroup X} (hE : IsPGroup p E)
    {t : X} (ht : t ∈ E) :
    (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set X)), E⁆ ⊔
        thetaT p E).map (QuotientGroup.mk' N) ≤
      ⁅inSubgroup (aschbacherSolvableCore p)
          (Subgroup.centralizer ({(t : X ⧸ N)} : Set (X ⧸ N))), E.map (QuotientGroup.mk' N)⁆ ⊔
        thetaT p (E.map (QuotientGroup.mk' N)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : ∃ k : ℕ, orderOf t = p ^ k := by
    obtain ⟨n, hn⟩ := hE.exists_orderOf_eq_pow ⟨t, ht⟩
    exact ⟨n, (Subgroup.orderOf_coe (⟨t, ht⟩ : E)).trans hn⟩
  rw [Subgroup.map_sup, Subgroup.map_commutator, map_theta_centralizer_singleton hp N hNs hNp hord]
  exact sup_le_sup le_rfl (map_thetaT_le hp N hNs hNp hE)

theorem disjoint_of_isPGroup_of_not_dvd [Finite X] {p : ℕ} (hp : p.Prime) {E : Subgroup X}
    (hE : IsPGroup p E) (N : Subgroup X) (hNp : ¬ p ∣ Nat.card N) : Disjoint E N := by
  have : Fact p.Prime := ⟨hp⟩
  apply Subgroup.disjoint_of_coprime_natCard
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp)

theorem card_map_mk'_of_disjoint (N : Subgroup X) [N.Normal] (E : Subgroup X)
    (hd : Disjoint E N) : Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).domRestrict E) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [eq_bot_iff]
    intro x hx
    have : (x : X) ∈ E ⊓ N := ⟨x.2, hx⟩
    rw [hd.eq_bot] at this
    exact Subtype.ext (by simpa using this)
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.domRestrict_range] at h
  exact h.symm

theorem card_map_mk'_eq_relIndex (N : Subgroup X) [N.Normal] (W : Subgroup X) :
    Nat.card (W.map (QuotientGroup.mk' N)) = N.relIndex W := by
  have hker : ((QuotientGroup.mk' N).domRestrict W).ker = N.subgroupOf W := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have h := Subgroup.index_ker ((QuotientGroup.mk' N).domRestrict W)
  rw [hker, MonoidHom.domRestrict_range] at h
  exact h.symm

theorem twoPrimeResidual_le_of_odd_card_map (N : Subgroup X) [N.Normal] {W : Subgroup X}
    (hodd : Odd (Nat.card (W.map (QuotientGroup.mk' N)))) :
    CFSG.Quasithin.twoPrimeResidual W ≤ N := by
  have hnorm : W ≤ Subgroup.normalizer ((W ⊓ N : Subgroup X) : Set X) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxW, hxN⟩
      exact ⟨W.mul_mem (W.mul_mem hw hxW) (W.inv_mem hw), ‹N.Normal›.conj_mem x hxN w⟩
    · rintro ⟨hxW, hxN⟩
      refine ⟨?_, ?_⟩
      · have := W.mul_mem (W.mul_mem (W.inv_mem hw) hxW) hw
        simpa [mul_assoc] using this
      · have := ‹N.Normal›.conj_mem _ hxN w⁻¹
        simpa [mul_assoc] using this
  have hodd' : ¬ 2 ∣ (W ⊓ N).relIndex W := by
    rw [inf_comm, Subgroup.inf_relIndex_right, ← card_map_mk'_eq_relIndex]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hres : CFSG.Quasithin.twoPrimeResidual W ≤ W ⊓ N :=
    iInf₂_le (W ⊓ N) ⟨inf_le_left, hnorm, hodd'⟩
  exact hres.trans inf_le_right

end CFSG.RankThree.PartOne.S8
