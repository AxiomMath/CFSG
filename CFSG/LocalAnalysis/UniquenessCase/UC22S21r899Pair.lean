module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Syl
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uj
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r899_exists_elemAbelian_pair {M A₀ : Subgroup G} {W₁ W₂ : Subgroup (Bar2 M)}
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r)
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) (hint : W₁ ⊓ W₂ = ⊥)
    (hW₁ : CFSG.Open.pRank r W₁ ≤ 1 ∧ r ∣ Nat.card W₁ ∧ ¬ p ∣ Nat.card (Sylow r ↥W₁))
    (hW₂ : CFSG.Open.pRank r W₂ ≤ 1 ∧ r ∣ Nat.card W₂ ∧ ¬ p ∣ Nat.card (Sylow r ↥W₂))
    (hNp : ∀ x : ↥M, (x : G) ∈ A₀ →
      uc22p21cPi M x ∈ normalizer (W₁ : Set (Bar2 M)) ⊓ normalizer (W₂ : Set (Bar2 M)))
    (hNr : ∀ x : ↥M, (∃ k : ℕ, x ^ r ^ k = 1) →
      uc22p21cPi M x ∈ normalizer (W₁ : Set (Bar2 M)) ⊓ normalizer (W₂ : Set (Bar2 M)))
    (hA₀M : A₀ ≤ M) (hA₀ : IsPGroup p A₀) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      A₀ ≤ normalizer (E : Set G) ∧
      ∀ R : Subgroup G, R ≤ M → IsPGroup r R → E ≤ R → E ≤ centralizer (R : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAb : IsPGroup p (barImage M A₀) := hA₀.comap_subtype.map _
  have hAbN : ∀ a ∈ barImage M A₀,
      a ∈ normalizer (W₁ : Set (Bar2 M)) ⊓ normalizer (W₂ : Set (Bar2 M)) := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 ha
    exact hNp m hm
  obtain ⟨y₁, hy₁W, hy₁o, hy₁N⟩ := uc22ine229_exists_orderOf_le_normalizer hp hr hW₁.1 hW₁.2.1
    hW₁.2.2 hAb fun a ha => (mem_inf.1 (hAbN a ha)).1
  obtain ⟨y₂, hy₂W, hy₂o, hy₂N⟩ := uc22ine229_exists_orderOf_le_normalizer hp hr hW₂.1 hW₂.2.1
    hW₂.2.2 hAb fun a ha => (mem_inf.1 (hAbN a ha)).2
  have hy₂n : y₂ ∉ zpowers y₁ := fun h => by
    have h1 : y₂ ∈ W₁ ⊓ W₂ := mem_inf.2 ⟨zpowers_le.2 hy₁W h, hy₂W⟩
    rw [hint, mem_bot] at h1
    rw [h1, orderOf_one] at hy₂o
    exact hr.one_lt.ne hy₂o
  obtain ⟨hEbel, hEbcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    ((Nat.card_zpowers y₁).trans hy₁o) hy₂o hy₂n
    fun a ha => hcomm a (zpowers_le.2 hy₁W ha) y₂ hy₂W
  obtain ⟨Eb, hEb⟩ : ∃ Eb : Subgroup (Bar2 M), Eb = zpowers y₁ ⊔ zpowers y₂ := ⟨_, rfl⟩
  rw [← hEb] at hEbel hEbcard
  have hy₁E : y₁ ∈ Eb := by rw [hEb]; exact mem_sup_left (mem_zpowers y₁)
  have hy₂E : y₂ ∈ Eb := by rw [hEb]; exact mem_sup_right (mem_zpowers y₂)
  have hAbE : ∀ a ∈ barImage M A₀, a ∈ normalizer (Eb : Set (Bar2 M)) := fun a ha => by
    rw [mem_normalizer_iff_map_conj_eq, hEb, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.1 (hy₁N ha), mem_normalizer_iff_map_conj_eq.1 (hy₂N ha)]
  have hA₀Y : A₀ ≤ normalizer (barPreimage M Eb : Set G) := fun a ha =>
    uc22ine229_mem_normalizer_barPreimage (x := ⟨a, hA₀M ha⟩)
      (hAbE _ (uc22p21c_mem_barImage.2 ⟨⟨a, hA₀M ha⟩, ha, rfl⟩))
  have hYp : ¬ p ∣ Nat.card (barPreimage M Eb) := by
    obtain ⟨a, ha⟩ := (uc22p21c_isPGroup_pCoreOf M).exists_card_eq
    rw [uc22p22u_card_barPreimage, hEbcard, ha]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hA₀ hA₀Y hYp
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G,
      E = (S : Subgroup ↥(barPreimage M Eb)).map (barPreimage M Eb).subtype := ⟨_, rfl⟩
  have hbar : barImage M E = Eb := by
    rw [hE]
    exact uc22ine229_barImage_map_sylow hEbel.isPGroup S
  have hEM : E ≤ M := by
    rw [hE]
    exact (map_subtype_le _).trans (uc22p21c_barPreimage_le M Eb)
  have hEr : IsPGroup r E := by
    rw [hE]
    exact S.isPGroup'.map _
  have hdisj : Disjoint (E.subgroupOf M) (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
    rw [QuotientGroup.ker_mk']
    refine Subgroup.disjoint_def.2 fun {x} hxE hxO => Subtype.ext ?_
    exact UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hr hr2 hEr
      (uc22p21c_isPGroup_pCoreOf M) (Subgroup.mem_subgroupOf.1 hxE) ⟨x, hxO, rfl⟩
  have hcardE : Nat.card E = r ^ 2 := by
    rw [← hEbcard, ← hbar, barImage, UC6S846.card_map_of_disjoint_ker _ _ hdisj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv).symm
  have hEel : IsElemAbelian r E := by
    have h1 : IsElemAbelian r (barImage M E) := by rw [hbar]; exact hEbel
    have h2 := CFSG.SectionRank.isElemAbelian_map
      (UC6S846.isElemAbelian_of_disjoint_ker _ _ hdisj h1) M.subtype
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEM] at h2
  refine ⟨E, hEM, hEel, hcardE, by rw [hE]; exact hS, fun R hRM hRr hER e he => ?_⟩
  rw [mem_centralizer_iff]
  intro x hx
  have hxM : x ∈ M := hRM hx
  have heM : e ∈ M := hEM he
  obtain ⟨k, hk⟩ := uc22ine229_exists_pow_eq_one (M := M) (x := ⟨x, hxM⟩) hRr hx
  have hcN := hNr _ ⟨k, hk⟩
  have hRb : IsPGroup r (barImage M R) := hRr.comap_subtype.map _
  have hcR : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M R := uc22p21c_mem_barImage.2 ⟨_, hx, rfl⟩
  have hEbR : Eb ≤ barImage M R := by
    rw [← hbar]
    exact uc22p22u_barImage_mono hER
  have h₁ := uc22ine229_commute_of_pRank_le_one hW₁.1 hRb hy₁W (hEbR hy₁E) hy₁o hcR
    (mem_inf.1 hcN).1
  have h₂ := uc22ine229_commute_of_pRank_le_one hW₂.1 hRb hy₂W (hEbR hy₂E) hy₂o hcR
    (mem_inf.1 hcN).2
  have hcE : Eb ≤ centralizer ({uc22p21cPi M ⟨x, hxM⟩} : Set (Bar2 M)) := by
    rw [hEb]
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact h₁.symm
    · exact h₂.symm
  have heE : uc22p21cPi M ⟨e, heM⟩ ∈ Eb := by
    rw [← hbar]
    exact uc22p21c_mem_barImage.2 ⟨⟨e, heM⟩, he, rfl⟩
  have hxe := uc22p22u_commutator_mem_pCoreOf hxM heM
    (mem_centralizer_singleton_iff.1 (hcE heE)).symm
  rw [commutatorElement_def] at hxe
  have hxeR : x * e * x⁻¹ * e⁻¹ ∈ R :=
    mul_mem (mul_mem (mul_mem hx (hER he)) (inv_mem hx)) (inv_mem (hER he))
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1
    (UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hr hr2 hRr (uc22p21c_isPGroup_pCoreOf M) hxeR
      hxe))

end CFSG.LocalAnalysis.UniquenessCase.UC22
