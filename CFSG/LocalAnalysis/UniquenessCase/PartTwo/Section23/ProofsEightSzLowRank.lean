module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveOrbit
import CFSG.GroupTheory.CoprimeLiftElementaryAbelian
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

private theorem exists_odd_prime_dvd_card_bar2 {H K : Subgroup G} (hK : K ∈ calC H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (Bar2 K) := by
  classical
  have hqs : CFSG.IsQuasisimple (Bar2 K) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hK.2.2
  haveI : Nontrivial (Bar2 K) := CFSG.LocalCores.isQuasisimple_nontrivial hqs
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card (Bar2 K)) with
    ⟨k, hk⟩ | ⟨p, hp, hpdvd, hodd⟩
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent (Bar2 K) :=
      (IsPGroup.of_card (p := 2) hk).isNilpotent
    haveI : Group.IsPerfect (Bar2 K) := ⟨hK.2.2.1⟩
    exact Group.IsPerfect.not_isNilpotent (Bar2 K) inferInstance
  · exact ⟨p, hp, hodd.ne_two_of_dvd_nat dvd_rfl, hpdvd⟩

private theorem exists_conjugate_family {Q : Type*} [Group Q] {r p : ℕ}
    (L : Subgroup Q) (a : Q) (u0 : ↥L) (hu0ord : orderOf u0 = p)
    (hu0nc : u0 ∉ Subgroup.center ↥L) :
    ∃ x : Fin r → Q,
      (∀ i : Fin r, x i ∈ conjugatePower a L (i : ℕ)) ∧
      (∀ i : Fin r, x i ^ p = 1) ∧
      (∀ i : Fin r, ∃ b ∈ conjugatePower a L (i : ℕ), b * x i ≠ x i * b) := by
  classical
  have hnc : ∃ w : ↥L, (u0 : Q) * (w : Q) ≠ (w : Q) * (u0 : Q) := by
    by_contra h
    push Not at h
    apply hu0nc
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (h w).symm
  obtain ⟨w, hw⟩ := hnc
  refine ⟨fun i : Fin r => a ^ (i : ℕ) * (u0 : Q) * (a ^ (i : ℕ))⁻¹, ?_, ?_, ?_⟩
  · intro i
    exact Subgroup.mem_map.mpr ⟨u0, u0.2, by
      change (MulAut.conj (a ^ (i : ℕ))) (u0 : Q) =
        a ^ (i : ℕ) * (u0 : Q) * (a ^ (i : ℕ))⁻¹
      rw [MulAut.conj_apply]⟩
  · intro i
    have hxord : orderOf (a ^ (i : ℕ) * (u0 : Q) * (a ^ (i : ℕ))⁻¹) = p := by
      rw [show a ^ (i : ℕ) * (u0 : Q) * (a ^ (i : ℕ))⁻¹ =
          (MulAut.conj (a ^ (i : ℕ))) (u0 : Q) from by rw [MulAut.conj_apply],
        MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hu0ord]
    rw [← hxord]
    exact pow_orderOf_eq_one _
  · intro i
    refine ⟨(MulAut.conj (a ^ (i : ℕ))) (w : Q), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨w, w.2, rfl⟩
    · intro heq
      apply hw
      have hxeq : a ^ (i : ℕ) * (u0 : Q) * (a ^ (i : ℕ))⁻¹ =
          (MulAut.conj (a ^ (i : ℕ))) (u0 : Q) := by rw [MulAut.conj_apply]
      dsimp only at heq
      rw [hxeq] at heq
      have h' : (MulAut.conj (a ^ (i : ℕ))) ((w : Q) * (u0 : Q)) =
          (MulAut.conj (a ^ (i : ℕ))) ((u0 : Q) * (w : Q)) := by
        rw [map_mul, map_mul]
        exact heq
      exact ((MulAut.conj (a ^ (i : ℕ))).injective h').symm

private theorem exists_isElemAbelian_map_of_barImage {H : Subgroup G} {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (Bar2 H)}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ k) :
    ∃ F : Subgroup G, F ≤ H ∧ IsElemAbelian p F ∧ Nat.card F = p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hpN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥H) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
    rw [hn]
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  have hcentbot : Subgroup.centralizer ((⊥ : Subgroup ↥H) : Set ↥H) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro z hz
    rw [Subgroup.mem_bot.mp hz]
    exact Subgroup.mem_center_iff.mpr (fun b => by simp)
  obtain ⟨E', hE'ea, -, hE'card, -⟩ :=
    exists_isElemAbelian_centralizer_lift (G := ↥H) (p := p)
      (N := CFSG.pCore 2 ↥H) (A := ⊥) hpN hE (by
        rw [hcentbot,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        exact le_top)
  refine ⟨E'.map H.subtype, Subgroup.map_subtype_le E', hE'ea.map H.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective H.subtype_injective, hE'card, hEcard]

theorem orderOf_le_evenRank_of_not_mem_normalizer {H C K : Subgroup G} (hC : C ≠ ⊥)
    (hC2 : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G)) (hK : K ∈ calC H)
    {y : G} (hyH : y ∈ H) (hy : (orderOf y).Prime)
    (hyK : y ∉ Subgroup.normalizer (K : Set G)) :
    orderOf y ≤ CFSG.Open.evenRank G := by
  classical
  haveI : Fact (orderOf y).Prime := ⟨hy⟩
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  let a : Bar2 H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩
  let L : Subgroup (Bar2 H) := barImage H K
  have hcomm : ConjugatesCommute a L (orderOf y) := by
    simpa [a, L] using
      conjugatesCommute_barImage (M := H) (L := K) hK hyH hy hyK
  obtain ⟨p, hp, hp2, hpdvd⟩ := exists_odd_prime_dvd_card_bar2 hK
  obtain ⟨u0, hu0ord, hu0nc⟩ :=
    exists_orderOf_prime_not_mem_center_barImage (M := H) (L := K) hK hp hp2 hpdvd
  obtain ⟨x, hx, hxp, hxz⟩ :=
    exists_conjugate_family (r := orderOf y) (p := p) L a u0 hu0ord
      (by simpa [L] using hu0nc)
  obtain ⟨E, -, hEea, hEcard⟩ :=
    uc22p20d_elemAbelian_of_commuting p (orderOf y) hp
      (fun i : Fin (orderOf y) => conjugatePower a L (i : ℕ)) x hcomm hx hxp hxz
  obtain ⟨F, hFH, hFea, hFcard⟩ :=
    exists_isElemAbelian_map_of_barImage hp hp2 hEea hEcard
  have hFle : F ≤ Subgroup.normalizer (C : Set G) := hFH.trans hHC
  exact (CFSG.SectionRank.le_pRank hp.one_lt hFle hFea hFcard).trans
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _
      ⟨C, hC, hC2, rfl⟩)

theorem mem_normalizer_of_evenRank_lt {H C K : Subgroup G} (hC : C ≠ ⊥)
    (hC2 : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G)) (hK : K ∈ calC H)
    {y : G} (hyH : y ∈ H) (hy : (orderOf y).Prime)
    (hlt : CFSG.Open.evenRank G < orderOf y) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hyK
  exact not_le.mpr hlt
    (orderOf_le_evenRank_of_not_mem_normalizer hC hC2 hHC hK hyH hy hyK)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
