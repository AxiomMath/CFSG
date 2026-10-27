module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

private theorem exists_pow_conj_of_le_normalizer {L S E₀ Q : Subgroup G} {n p r : ℕ}
    (hS : IsSylowOf 2 S L) (hX : IsSp4 (Bar2 L) n) (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hr2 : r ≠ 2) (hpr : p ≠ r) (hE₀L : E₀ ≤ L) (hE₀S : E₀ ≤ normalizer (S : Set G))
    (hE₀el : IsElemAbelian r E₀) (hE₀c : Nat.card E₀ = r ^ 2) (hQL : Q ≤ normalizer (L : Set G))
    (hQS : Q ≤ normalizer (S : Set G)) (hQel : IsElemAbelian p Q) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ h ∈ L, h ∈ normalizer (S : Set G) →
      x * h * x⁻¹ * (h ^ k)⁻¹ ∈ S :=
    fun x hx => uc22p218d_exists_pow_conj_mem_sp4 hS hX (hQL hx) (hQS hx) (hp.odd_of_ne_two hp2)
      (hQel.2 x hx)
  have hWL : S ⊔ E₀ ≤ L := sup_le hS.le hE₀L
  have hWN : S ⊔ E₀ ≤ normalizer (S : Set G) := sup_le le_normalizer hE₀S
  have hQW : Q ≤ normalizer ((S ⊔ E₀ : Subgroup G) : Set G) := by
    have hW : S ⊔ E₀ = closure ((S : Set G) ∪ E₀) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [hW, le_normalizer_closure_iff]
    intro x hx g hg
    rw [← hW]
    rcases hg with hg | hg
    · exact mem_sup_left ((mem_normalizer_iff.1 (hQS hx) g).1 hg)
    · obtain ⟨k, hk⟩ := hpow x hx
      have h1 := hk g (hE₀L hg) (hE₀S hg)
      have h2 : x * g * x⁻¹ = (x * g * x⁻¹ * (g ^ k)⁻¹) * g ^ k := by group
      rw [h2]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (pow_mem hg k))
  obtain ⟨a, ha⟩ := hS.isPGroup.exists_card_eq
  have hWc : Nat.card (S ⊔ E₀ : Subgroup G) = 2 ^ a * r ^ 2 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S E₀ hE₀S
      (IsPGroup.disjoint_of_ne 2 r hr2.symm S E₀ hS.isPGroup hE₀el.isPGroup), ha, hE₀c]
  have hpW : ¬ p ∣ Nat.card (S ⊔ E₀ : Subgroup G) := by
    rw [hWc]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨P, hP⟩ :=
    CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hQel.isPGroup hQW hpW
  obtain ⟨E, hE, hQE⟩ : ∃ E : Subgroup G, IsSylowOf r E (S ⊔ E₀) ∧ Q ≤ normalizer (E : Set G) :=
    ⟨_, ⟨P, rfl⟩, hP⟩
  have hE₀ : IsSylowOf r E₀ (S ⊔ E₀) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hE₀el.isPGroup, fun h => ?_⟩
    have h1 := relIndex_mul_card E₀ (S ⊔ E₀)
    rw [inf_eq_left.2 (le_sup_right : E₀ ≤ S ⊔ E₀), hWc, hE₀c] at h1
    have h2 : E₀.relIndex (S ⊔ E₀) = 2 ^ a := Nat.eq_of_mul_eq_mul_right (pow_pos hr.pos 2) h1
    rw [h2] at h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  obtain ⟨w, -, hw⟩ := hE₀.exists_mem_conj hE
  have hEeq : E = E₀.map (MulAut.conj w).toMonoidHom := by
    ext x
    rw [mem_map_equiv, MulAut.conj_symm_apply]
    exact hw x
  have hEel : IsElemAbelian r E := by
    rw [hEeq]
    exact hE₀el.map _
  have hEc : Nat.card E = r ^ 2 := by
    rw [hEeq, card_map_of_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective,
      hE₀c]
  have hEW : E ≤ S ⊔ E₀ := hE.le
  have hdisj : Disjoint E S := IsPGroup.disjoint_of_ne r 2 hr2 E S hE.isPGroup hS.isPGroup
  refine ⟨E, hEW.trans hWL, hEel, hEc, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hpow x hx
  refine ⟨k, fun e he => ?_⟩
  have h1 := hk e (hWL (hEW he)) (hWN (hEW he))
  have h2 : x * e * x⁻¹ * (e ^ k)⁻¹ ∈ E :=
    mul_mem ((mem_normalizer_iff.1 (hQE hx) e).1 he) (inv_mem (pow_mem he k))
  exact mul_inv_eq_one.1 (disjoint_def.1 hdisj h2 h1)

theorem uc22s218n_exists_pow_torus_inner {L : Subgroup G} {n p r : ℕ} (hX : IsSp4 (Bar2 L) n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ n - 1) (hpr : p ≠ r) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ L ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀L, hE₀el, hE₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hr (uc22p218c_pRank_eq_two_of_bar2 hX hr hrn).ge
  obtain ⟨S', hS'⟩ := uc22p218s_exists_sylow_le_normalizer hr Nat.prime_two hE₀el.isPGroup
    (hE₀L.trans le_normalizer) (uc22p218d_not_dvd_card_sylow_of_bar2 hX hr hrn)
  obtain ⟨S, hS, hE₀S⟩ : ∃ S : Subgroup G, IsSylowOf 2 S L ∧ E₀ ≤ normalizer (S : Set G) :=
    ⟨_, ⟨S', rfl⟩, hS'⟩
  obtain ⟨Q₀, hQ₀L, hQ₀el, hQ₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (uc22p218c_pRank_eq_two_of_bar2 hX hp hpn).ge
  obtain ⟨P', hP'⟩ := uc22p218s_exists_sylow_le_normalizer hp Nat.prime_two hQ₀el.isPGroup
    (hQ₀L.trans le_normalizer) (uc22p218d_not_dvd_card_sylow_of_bar2 hX hp hpn)
  obtain ⟨P, hP, hQ₀P⟩ : ∃ P : Subgroup G, IsSylowOf 2 P L ∧ Q₀ ≤ normalizer (P : Set G) :=
    ⟨_, ⟨P', rfl⟩, hP'⟩
  obtain ⟨w, hwL, hw⟩ := hP.exists_mem_conj hS
  have hQL : Q₀.map (MulAut.conj w).toMonoidHom ≤ L := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    exact L.mul_mem (L.mul_mem hwL (hQ₀L hq)) (L.inv_mem hwL)
  have hQS : Q₀.map (MulAut.conj w).toMonoidHom ≤ normalizer (S : Set G) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_normalizer_iff]
    intro x
    show x ∈ S ↔ w * q * w⁻¹ * x * (w * q * w⁻¹)⁻¹ ∈ S
    have e : w⁻¹ * (w * q * w⁻¹ * x * (w * q * w⁻¹)⁻¹) * w = q * (w⁻¹ * x * w) * q⁻¹ := by
      group
    rw [hw x, hw (w * q * w⁻¹ * x * (w * q * w⁻¹)⁻¹), e]
    exact mem_normalizer_iff.1 (hQ₀P hq) (w⁻¹ * x * w)
  obtain ⟨E, hEL, hEel, hEc, hpow⟩ := exists_pow_conj_of_le_normalizer hS hX hp hp2 hr hr2 hpr hE₀L
    hE₀S hE₀el hE₀c (hQL.trans le_normalizer) hQS (hQ₀el.map _)
  refine ⟨E, _, hEL, hEel, hEc, hQL, hQ₀el.map _, ?_, hpow⟩
  rw [card_map_of_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective, hQ₀c]

theorem uc22s218n_stronglyEmbedded_of_torus (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M) (hML : D.M ≤ normalizer (L : Set G))
    {n p r : ℕ} (hX : IsSp4 (Bar2 L) n) (hp : p.Prime) (h76 : Conclusion76 D.M p) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) (hrσ : r ∉ D.sig) {E Q : Subgroup G} (hEL : E ≤ L)
    (hEel : IsElemAbelian r E) (hEc : Nat.card E = r ^ 2) (hQM : Q ≤ D.M)
    (hQel : IsElemAbelian p Q) (hQc : Nat.card Q = p ^ 2)
    (hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k) : IsStronglyPEmbedded r D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hEM : E ≤ D.M := hEL.trans hL.1.le
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [card_bot] at hEc
    exact (Nat.one_lt_pow two_ne_zero hr.one_lt).ne hEc
  obtain ⟨x, hxQ, hx1, hxC⟩ := uc22p218s_exists_mem_centralizer hp hr hQel hQc hEel hE1 hpow
  have hxle : zpowers x ≤ D.M ⊓ centralizer (E : Set G) := zpowers_le.2 ⟨hQM hxQ, hxC⟩
  have hpos : 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hp hxle (isElemAbelian_zpowers (hQel.2 x hxQ))
      (by rw [Nat.card_zpowers, orderOf_eq_prime (hQel.2 x hxQ) hx1, pow_one])
  have hXN : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      1 < CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE _
    have hQX : Q ≤ normalizer (X : Set G) := le_normalizer_iff.2 fun x hx y hy => by
      obtain ⟨k, hk⟩ := hpow x hx
      rw [hk y (hXE hy)]
      exact pow_mem hy k
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) :=
      UC6S846.le_pRank' hp (le_inf hQM hQX) hQel hQc
    omega
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  have hEC : E ≤ centralizer (R : Set G) :=
    uc22p218s_le_centralizer hX hr hr2 hrn hML hR hER hEL hEel.2
  exact h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E (le_inf hER hEC) hEel hEc
    (h76 r hr E hEM hEel hEc hpos hXN)

end CFSG.LocalAnalysis.UniquenessCase.UC22
