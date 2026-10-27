module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uj
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217v_mem_centralizer_barImage {M L : Subgroup G} (hL : L ∈ calC M) {a : G}
    (haM : a ∈ M) (ha : CentralizesBar a L) :
    uc22p21cPi M ⟨a, haM⟩ ∈ centralizer (barImage M L : Set (Bar2 M)) := by
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨m, hmL, rfl⟩ := uc22p21c_mem_barImage.1 hy
  have h0 : (⟨a, haM⟩ * m * ⟨a, haM⟩⁻¹ * m⁻¹ : ↥M) ∈ CFSG.pCore 2 ↥M :=
    (CFSG.mem_openPCoreOf_iff _).1 (uc22p21c_pCoreOf_le_of_subnormal hL.1 (ha.2 m hmL))
  have h1 : uc22p21cPi M (⟨a, haM⟩ * m * ⟨a, haM⟩⁻¹ * m⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact h0
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm

theorem uc22s217v_exists_centralizesBar_le {L A : Subgroup G} (hJ1 : IsJ1 (Bar2 L)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsPGroup p A) (hAN : A ≤ normalizer (L : Set G)) :
    ∃ A' ≤ A, Nat.card A ≤ p * Nat.card A' ∧ ∀ a ∈ A', CentralizesBar a L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ↥A →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hAN)
  obtain ⟨hcard, -, hinn⟩ := kJ1_holds (Bar2 L) hJ1
  have hsurj : Function.Surjective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) := fun θ => by
    obtain ⟨x, hx⟩ := hinn θ
    exact ⟨x, hx.symm⟩
  have hR : Nat.card f.range ∣ 175560 :=
    (Subgroup.card_subgroup_dvd_card f.range).trans
      ((Subgroup.card_dvd_of_surjective hsurj).trans (dvd_of_eq hcard))
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hkr := Subgroup.card_ker_mul_card_range f
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ (hkr.trans hn))
  have hR' : p ^ j ∣ 175560 := by
    rw [← hj]
    exact hR
  have hj1 : j ≤ 1 := by
    by_contra h
    exact uc22s217v_not_sq_dvd hp hp2 ((pow_dvd_pow p (by omega)).trans hR')
  refine ⟨f.ker.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hpj : p ^ j ≤ p := (Nat.pow_le_pow_right hp.pos hj1).trans_eq (pow_one p)
    calc Nat.card A = Nat.card f.ker * Nat.card f.range := hkr.symm
      _ = Nat.card f.ker * p ^ j := by rw [hj]
      _ ≤ Nat.card f.ker * p := Nat.mul_le_mul_left _ hpj
      _ = p * Nat.card (f.ker.map A.subtype) := by
        rw [Subgroup.card_map_of_injective A.subtype_injective, mul_comm]
  · rintro a ⟨x, hx, rfl⟩
    have h1 : UC6S846.rhoL L ⟨(x : G), hAN x.2⟩ = 1 := hx
    refine ⟨hAN x.2, fun l hl => (UC6S846.rhoL_fix_iff L ⟨(x : G), hAN x.2⟩ ⟨l, hl⟩).1 ?_⟩
    rw [h1, MulAut.one_apply]

theorem uc22s217v_exists_elemAbelian_centralizer {M A : Subgroup G} {W₁ W₂ : Subgroup (Bar2 M)}
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r)
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) (hint : W₁ ⊓ W₂ = ⊥)
    (hW₁ : CFSG.Open.pRank r W₁ ≤ 1 ∧ r ∣ Nat.card W₁)
    (hW₂ : CFSG.Open.pRank r W₂ ≤ 1 ∧ r ∣ Nat.card W₂)
    (hN : ∀ x : ↥M, Odd (orderOf x) →
      uc22p21cPi M x ∈ normalizer (W₁ : Set (Bar2 M)) ⊓ normalizer (W₂ : Set (Bar2 M)))
    (hAM : A ≤ M) (hA : IsPGroup p A)
    (hAC : ∀ a (ha : a ∈ A), uc22p21cPi M ⟨a, hAM ha⟩ ∈
      centralizer (W₁ : Set (Bar2 M)) ⊓ centralizer (W₂ : Set (Bar2 M))) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      A ≤ centralizer (E : Set G) ∧
      ∀ R : Subgroup G, R ≤ M → IsPGroup r R → E ≤ R → E ≤ centralizer (R : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y₁, hy₁W, hy₁o⟩ : ∃ y ∈ W₁, orderOf y = r := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥W₁) r hW₁.2
    exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩
  obtain ⟨y₂, hy₂W, hy₂o⟩ : ∃ y ∈ W₂, orderOf y = r := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥W₂) r hW₂.2
    exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩
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
  have hAE : ∀ a (ha : a ∈ A), uc22p21cPi M ⟨a, hAM ha⟩ ∈ centralizer (Eb : Set (Bar2 M)) := by
    intro a ha
    have hcE : Eb ≤ centralizer ({uc22p21cPi M ⟨a, hAM ha⟩} : Set (Bar2 M)) := by
      rw [hEb]
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_) <;> rw [mem_centralizer_singleton_iff]
      · exact mem_centralizer_iff.1 (mem_inf.1 (hAC a ha)).1 y₁ hy₁W
      · exact mem_centralizer_iff.1 (mem_inf.1 (hAC a ha)).2 y₂ hy₂W
    exact mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hcE hh)
  have hAY : A ≤ normalizer (barPreimage M Eb : Set G) := fun a ha =>
    uc22ine229_mem_normalizer_barPreimage (x := ⟨a, hAM ha⟩)
      (Subgroup.centralizer_le_normalizer _ (hAE a ha))
  have hYp : ¬ p ∣ Nat.card (barPreimage M Eb) := by
    obtain ⟨a, ha⟩ := (uc22p21c_isPGroup_pCoreOf M).exists_card_eq
    rw [uc22p22u_card_barPreimage, hEbcard, ha]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hA hAY hYp
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
  have hAN : A ≤ normalizer (E : Set G) := by rw [hE]; exact hS
  have hAcE : A ≤ centralizer (E : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro e he
    have heM : e ∈ M := hEM he
    have heE : uc22p21cPi M ⟨e, heM⟩ ∈ Eb := by
      rw [← hbar]
      exact uc22p21c_mem_barImage.2 ⟨⟨e, heM⟩, he, rfl⟩
    have hae := uc22p22u_commutator_mem_pCoreOf (hAM ha) heM
      (mem_centralizer_iff.1 (hAE a ha) _ heE).symm
    rw [commutatorElement_def] at hae
    have haeE : a * e * a⁻¹ * e⁻¹ ∈ E :=
      mul_mem ((mem_normalizer_iff.1 (hAN ha) e).1 he) (inv_mem he)
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1
      (UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hr hr2 hEr (uc22p21c_isPGroup_pCoreOf M)
        haeE hae))).symm
  refine ⟨E, hEM, hEel, hcardE, hAcE, fun R hRM hRr hER e he => ?_⟩
  rw [mem_centralizer_iff]
  intro x hx
  have hxM : x ∈ M := hRM hx
  have heM : e ∈ M := hEM he
  obtain ⟨k, hk⟩ := uc22ine229_exists_pow_eq_one (M := M) (x := ⟨x, hxM⟩) hRr hx
  have hcN := hN _ (uc22ine229_odd_orderOf hr hr2 hk)
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
