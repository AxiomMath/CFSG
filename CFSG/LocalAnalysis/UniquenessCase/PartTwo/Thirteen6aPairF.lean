module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Syl
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uj
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s136a_isElemAbelian_sup_zpowers {Q : Type} [Group Q] [Finite Q] {W₁ W₂ : Subgroup Q}
    {r : ℕ} (hr : r.Prime) {y₁ y₂ : Q} (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a)
    (hint : W₁ ⊓ W₂ = ⊥) (hy₁ : y₁ ∈ W₁) (hy₂ : y₂ ∈ W₂) (hy₁o : orderOf y₁ = r)
    (hy₂o : orderOf y₂ = r) :
    IsElemAbelian r (zpowers y₁ ⊔ zpowers y₂) ∧
      Nat.card (zpowers y₁ ⊔ zpowers y₂ : Subgroup Q) = r ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have hy₂n : y₂ ∉ zpowers y₁ := fun h => by
    have h1 : y₂ ∈ W₁ ⊓ W₂ := mem_inf.2 ⟨zpowers_le.2 hy₁ h, hy₂⟩
    rw [hint, mem_bot] at h1
    rw [h1, orderOf_one] at hy₂o
    exact hr.one_lt.ne hy₂o
  exact CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    ((Nat.card_zpowers y₁).trans hy₁o) hy₂o hy₂n
    (fun a ha => hcomm a (zpowers_le.2 hy₁ ha) y₂ hy₂)

private theorem s136a_pairF_not_dvd_sylow {M : Subgroup G} {Y : Subgroup (Bar2 M)} {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hfact : Fact r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2)
    (hYcard : Nat.card Y = r ^ 2) :
    ¬ p ∣ Nat.card (Sylow r ↥(barPreimage M Y)) := by
  have hHcard := uc22p22u_card_barPreimage M Y
  have hpO : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := (uc22p21c_isPGroup_pCoreOf M).exists_card_eq
    rw [hk]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hrO : ¬ r ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := (uc22p21c_isPGroup_pCoreOf M).exists_card_eq
    rw [hk]
    exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hfac : (Nat.card ↥(barPreimage M Y)).factorization r = 2 := by
    rw [hHcard, hYcard,
      Nat.factorization_mul (Nat.card_pos.ne') (pow_ne_zero 2 hr.ne_zero),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hrO, zero_add,
      Nat.Prime.factorization_pow hr, Finsupp.single_eq_same]
  obtain ⟨P⟩ : Nonempty (Sylow r ↥(barPreimage M Y)) := inferInstance
  have hPcard : Nat.card P = r ^ 2 := by
    rw [@Sylow.card_eq_multiplicity (↥(barPreimage M Y)) _ _ r hfact P, hfac]
  have hPindex : (P : Subgroup ↥(barPreimage M Y)).index = Nat.card (pCoreOf 2 M) := by
    have hmul := Subgroup.card_mul_index (P : Subgroup ↥(barPreimage M Y))
    rw [hPcard, hHcard, hYcard] at hmul
    rw [mul_comm (Nat.card (pCoreOf 2 M)) (r ^ 2)] at hmul
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hr.pos 2) hmul
  have hdvd := @Sylow.card_dvd_index r (↥(barPreimage M Y)) _ hfact _ P
  rw [hPindex] at hdvd
  exact fun hpdvd => hpO (hpdvd.trans hdvd)

private theorem s136a_pairF_exists_lift {M A₀ : Subgroup G} {Y : Subgroup (Bar2 M)} {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hfact : Fact r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2)
    (hYr : IsPGroup r Y) (hYel : IsElemAbelian r Y) (hYcard : Nat.card Y = r ^ 2)
    (hA₀M : A₀ ≤ M) (hA₀ : IsPGroup p ↥A₀)
    (hA₀C : ∀ a (ha : a ∈ A₀), uc22p21cPi M ⟨a, hA₀M ha⟩ ∈
      centralizer (Y : Set (Bar2 M))) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      A₀ ≤ centralizer (E : Set G) ∧ barImage M E = Y := by
  have hA₀Y : A₀ ≤ normalizer (barPreimage M Y : Set G) := fun a ha =>
    uc22ine229_mem_normalizer_barPreimage (x := ⟨a, hA₀M ha⟩)
      (Subgroup.centralizer_le_normalizer (Y : Set (Bar2 M)) (hA₀C a ha))
  have hnotdvd := s136a_pairF_not_dvd_sylow hp hr hfact hp2 hr2 hYcard
  obtain ⟨S, hS⟩ := @uc22ine229_exists_sylow_le_normalizer G _ _ p r hp hfact
    (barPreimage M Y) A₀ hA₀ hA₀Y hnotdvd
  let E : Subgroup G := (S : Subgroup ↥(barPreimage M Y)).map (barPreimage M Y).subtype
  have hEM : E ≤ M := (Subgroup.map_subtype_le _).trans (uc22p21c_barPreimage_le M Y)
  have hEr : IsPGroup r E := S.isPGroup'.map _
  have hbar : barImage M E = Y :=
    @uc22ine229_barImage_map_sylow G _ _ M r hfact Y hYr S
  have hdisj : Disjoint (E.subgroupOf M) (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
    rw [QuotientGroup.ker_mk']
    refine Subgroup.disjoint_def.2 fun {x} hxE hxO => Subtype.ext ?_
    exact UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hr hr2 hEr
      (uc22p21c_isPGroup_pCoreOf M) (Subgroup.mem_subgroupOf.1 hxE) ⟨x, hxO, rfl⟩
  have hcardE : Nat.card E = r ^ 2 := by
    rw [← hYcard, ← hbar, barImage, UC6S846.card_map_of_disjoint_ker _ _ hdisj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv).symm
  have hEel : IsElemAbelian r E := by
    have h1 : IsElemAbelian r (barImage M E) := by rw [hbar]; exact hYel
    have h2 := CFSG.SectionRank.isElemAbelian_map
      (UC6S846.isElemAbelian_of_disjoint_ker _ _ hdisj h1) M.subtype
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEM] at h2
  have hAcE : A₀ ≤ centralizer (E : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro e he
    have heM : e ∈ M := hEM he
    have heY : uc22p21cPi M ⟨e, heM⟩ ∈ Y := by
      rw [← hbar]
      exact uc22p21c_mem_barImage.2 ⟨⟨e, heM⟩, he, rfl⟩
    have hae := uc22p22u_commutator_mem_pCoreOf (hA₀M ha) heM
      (mem_centralizer_iff.1 (hA₀C a ha) _ heY).symm
    rw [commutatorElement_def] at hae
    have haeE : a * e * a⁻¹ * e⁻¹ ∈ E :=
      mul_mem ((mem_normalizer_iff.1 (hS ha) e).1 he) (inv_mem he)
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1
      (UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hr hr2 hEr
        (uc22p21c_isPGroup_pCoreOf M) haeE hae))).symm
  exact ⟨E, hEM, hEel, hcardE, hAcE, hbar⟩

private theorem s136a_pairF_centralizes {M : Subgroup G} {W₁ W₂ : Subgroup (Bar2 M)} {r : ℕ}
    (hr : r.Prime) (hfact : Fact r.Prime) (hr2 : r ≠ 2)
    (hW₁ : CFSG.Open.pRank r W₁ ≤ 1) (hW₂ : CFSG.Open.pRank r W₂ ≤ 1)
    (hN₁ : W₁.Normal) (hN₂ : W₂.Normal) {y₁ y₂ : Bar2 M} (hy₁ : y₁ ∈ W₁) (hy₂ : y₂ ∈ W₂)
    (hy₁o : orderOf y₁ = r) (hy₂o : orderOf y₂ = r) {E : Subgroup G} (hEM : E ≤ M)
    (hbar : barImage M E = zpowers y₁ ⊔ zpowers y₂) :
    ∀ R : Subgroup G, R ≤ M → IsPGroup r ↥R → E ≤ R → E ≤ centralizer (R : Set G) := by
  intro R hRM hRr hER e he
  rw [mem_centralizer_iff]
  intro x hx
  have hxM : x ∈ M := hRM hx
  have heM : e ∈ M := hEM he
  have hRb : IsPGroup r (barImage M R) := hRr.comap_subtype.map _
  have hcR : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M R :=
    uc22p21c_mem_barImage.2 ⟨_, hx, rfl⟩
  have hEbR : (zpowers y₁ ⊔ zpowers y₂ : Subgroup (Bar2 M)) ≤ barImage M R := by
    rw [← hbar]
    exact uc22p22u_barImage_mono hER
  have hy₁R : y₁ ∈ barImage M R := hEbR (mem_sup_left (mem_zpowers y₁))
  have hy₂R : y₂ ∈ barImage M R := hEbR (mem_sup_right (mem_zpowers y₂))
  have hcN : uc22p21cPi M ⟨x, hxM⟩ ∈
      normalizer (W₁ : Set (Bar2 M)) ⊓ normalizer (W₂ : Set (Bar2 M)) :=
    mem_inf.2 ⟨by rw [Subgroup.normalizer_eq_top_iff.2 hN₁]; exact mem_top _,
      by rw [Subgroup.normalizer_eq_top_iff.2 hN₂]; exact mem_top _⟩
  have h₁ := @uc22ine229_commute_of_pRank_le_one (Bar2 M) _ _ W₁ (barImage M R) r hfact
    hW₁ hRb y₁ (uc22p21cPi M ⟨x, hxM⟩) hy₁ hy₁R hy₁o hcR (mem_inf.1 hcN).1
  have h₂ := @uc22ine229_commute_of_pRank_le_one (Bar2 M) _ _ W₂ (barImage M R) r hfact
    hW₂ hRb y₂ (uc22p21cPi M ⟨x, hxM⟩) hy₂ hy₂R hy₂o hcR (mem_inf.1 hcN).2
  have hcE : (zpowers y₁ ⊔ zpowers y₂ : Subgroup (Bar2 M)) ≤
      centralizer ({uc22p21cPi M ⟨x, hxM⟩} : Set (Bar2 M)) := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact h₁.symm
    · exact h₂.symm
  have heE : uc22p21cPi M ⟨e, heM⟩ ∈ zpowers y₁ ⊔ zpowers y₂ := by
    rw [← hbar]
    exact uc22p21c_mem_barImage.2 ⟨⟨e, heM⟩, he, rfl⟩
  have hxe := uc22p22u_commutator_mem_pCoreOf hxM heM
    (mem_centralizer_singleton_iff.1 (hcE heE)).symm
  rw [commutatorElement_def] at hxe
  have hxeR : x * e * x⁻¹ * e⁻¹ ∈ R :=
    mul_mem (mul_mem (mul_mem hx (hER he)) (inv_mem hx)) (inv_mem (hER he))
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1
    (UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hr hr2 hRr
      (uc22p21c_isPGroup_pCoreOf M) hxeR hxe))

theorem s136a_exists_elemAbelian_pair_of_mem {M A₀ : Subgroup G} {W₁ W₂ : Subgroup (Bar2 M)}
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2)
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) (hint : W₁ ⊓ W₂ = ⊥)
    (hW₁ : CFSG.Open.pRank r W₁ ≤ 1) (hW₂ : CFSG.Open.pRank r W₂ ≤ 1) (hN₁ : W₁.Normal)
    (hN₂ : W₂.Normal) {y₁ y₂ : Bar2 M} (hy₁ : y₁ ∈ W₁) (hy₂ : y₂ ∈ W₂) (hy₁o : orderOf y₁ = r)
    (hy₂o : orderOf y₂ = r) (hA₀M : A₀ ≤ M) (hA₀ : IsPGroup p ↥A₀)
    (hA₀y : barImage M A₀ ≤ centralizer ({y₁, y₂} : Set (Bar2 M))) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      A₀ ≤ centralizer (E : Set G) ∧
      ∀ R : Subgroup G, R ≤ M → IsPGroup r ↥R → E ≤ R → E ≤ centralizer (R : Set G) := by
  have hfact : Fact r.Prime := ⟨hr⟩
  have hY := s136a_isElemAbelian_sup_zpowers hr hcomm hint hy₁ hy₂ hy₁o hy₂o
  let Y : Subgroup (Bar2 M) := zpowers y₁ ⊔ zpowers y₂
  have hYr : IsPGroup r Y := hY.1.isPGroup
  have hA₀C : ∀ a (ha : a ∈ A₀), uc22p21cPi M ⟨a, hA₀M ha⟩ ∈
      centralizer (Y : Set (Bar2 M)) := by
    intro a ha
    have hcE : Y ≤ centralizer ({uc22p21cPi M ⟨a, hA₀M ha⟩} : Set (Bar2 M)) := by
      change (zpowers y₁ ⊔ zpowers y₂ : Subgroup (Bar2 M)) ≤
        centralizer ({uc22p21cPi M ⟨a, hA₀M ha⟩} : Set (Bar2 M))
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_) <;> rw [mem_centralizer_singleton_iff]
      · exact mem_centralizer_iff.1
          (hA₀y (uc22p21c_mem_barImage.2 ⟨⟨a, hA₀M ha⟩, ha, rfl⟩)) y₁ (by simp)
      · exact mem_centralizer_iff.1
          (hA₀y (uc22p21c_mem_barImage.2 ⟨⟨a, hA₀M ha⟩, ha, rfl⟩)) y₂ (by simp)
    exact mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hcE hh)
  have hYel : IsElemAbelian r Y := hY.1
  have hYcard : Nat.card Y = r ^ 2 := hY.2
  obtain ⟨E, hEM, hEel, hEcard, hAcE, hbar⟩ :=
    s136a_pairF_exists_lift hp hr hfact hp2 hr2 hYr hYel hYcard hA₀M hA₀ hA₀C
  exact ⟨E, hEM, hEel, hEcard, hAcE,
    s136a_pairF_centralizes hr hfact hr2 hW₁ hW₂ hN₁ hN₂ hy₁ hy₂ hy₁o hy₂o hEM hbar⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
