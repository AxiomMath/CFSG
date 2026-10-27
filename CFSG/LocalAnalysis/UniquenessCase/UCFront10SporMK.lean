module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporOdd
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InThompson
import CFSG.GroupTheory.TISylowLocal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.MK

open Subgroup CFSG.Monster.Existence
open CFSG.QuasithinUnique (IsSylowTwoOf)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem not_two_dvd_index {T : Subgroup G} (hT : IsSylowTwoOf T ⊤) : ¬ 2 ∣ T.index := by
  have h := hT.2.2
  rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h

private theorem monsterOrder_eq : CFSG.Open.monsterOrder =
    2 ^ 46 * (3 ^ 20 * (5 ^ 9 * (7 ^ 6 * (11 ^ 2 * (13 ^ 3 * (17 * (19 * (23 * (29 *
      (31 * (41 * (47 * (59 * 71))))))))))))) := by
  have h : CFSG.Open.monsterOrder =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 *
        47 * 59 * 71 := rfl
  rw [h]
  ring

theorem pCore_map_le {z : G} {T : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hTz : T ≤ centralizer {z}) : (pCore 2 (cent z)).map (cent z).subtype ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTidx := not_two_dvd_index hT
  let P : Sylow 2 G := hT.2.1.toSylow hTidx
  have hP : (P : Subgroup G) = T := IsPGroup.toSylow_coe hT.2.1 hTidx
  have h := CFSG.GroupTheory.inSubgroup_pCore_le_of_isSylow (p := 2) (T := P) (M := cent z)
    (by rw [hP]; exact hTz)
  rwa [hP] at h

theorem self_mem_quasithinOmegaOneCenter {z : G} (hz2 : orderOf z = 2) {T : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hTz : T ≤ centralizer {z}) :
    z ∈ CFSG.Open.quasithinOmegaOneCenter T := by
  refine Subgroup.subset_closure ⟨⟨pCore_map_le hT hTz (self_mem_twoCore hz2), ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mp (hTz ht))
  · simpa [hz2] using pow_orderOf_eq_one z

theorem eq_one_or_eq_of_central {z : G} (hz2 : orderOf z = 2) (hz : IsTwoBCentralizer z)
    {T : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTz : T ≤ centralizer {z}) {t : G} (ht : t ∈ T)
    (hts : ∀ s ∈ T, s * t = t * s) : t = 1 ∨ t = z := by
  have hQT : (pCore 2 (cent z)).map (cent z).subtype ≤ T := pCore_map_le hT hTz
  have hcent : t ∈ cent z ⊓ centralizer (twoCore z : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hTz ht, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hts q (hQT hq)
  rw [hz.inf_centralizer_eq hz2] at hcent
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcent
  have hk2 : z ^ (k % (orderOf z : ℤ)) = z ^ k := zpow_mod_orderOf z k
  rw [hz2, Nat.cast_ofNat, hk] at hk2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero] at hk2
    exact hk2.symm
  · right
    rw [h, zpow_one] at hk2
    exact hk2.symm

theorem k105In_centralizer_of_isTwoBCentralizer
    {z : G} (hz : IsTwoBCentralizer z) {T : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hTz : T ≤ centralizer {z}) : K105In (centralizer {z}) T := by
  obtain ⟨e⟩ := hz.2.2.2.1
  refine k105In_of_quotient hT hTz (pCore 2 (cent z)) ?_ (MulEquiv.refl _)
    (k105SporAt_Co1 _ ⟨e⟩)
  exact pCore_map_le hT hTz

theorem oddLocal_of_isTwoBCentralizer {z : G} (hz2 : orderOf z = 2) (hz : IsTwoBCentralizer z)
    (hG : Nat.card G = CFSG.Open.monsterOrder) {T : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hTz : T ≤ centralizer {z}) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : Subgroup G)
    (hA : CFSG.Open.IsElemAbelian p A) (hA1 : A ≠ ⊥) (hTA : T ≤ normalizer (A : Set G)) :
    A ⊓ centralizer {z} ≠ ⊥ := by
  intro hAz
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have hzT : z ∈ T := pCore_map_le hT hTz (self_mem_twoCore hz2)
  have hzz : z * z = 1 := by
    rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one z
  have hdvd := card_dvd_card_GL_of_inf_centralizer_eq_bot hp (by omega) hT.2.1 hzT hzz
    (fun t ht hts => eq_one_or_eq_of_central hz2 hz hT hTz ht hts) hA hn hA1 hTA hAz
  have hmul : Nat.card T * T.index = CFSG.Open.monsterOrder := by
    rw [← hG]
    exact Subgroup.card_mul_index T
  have hTidx := not_two_dvd_index hT
  have h246T : 2 ^ 46 ∣ Nat.card T := by
    have hcop : Nat.Coprime (2 ^ 46) T.index :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hTidx).pow_left 46
    have h : 2 ^ 46 ∣ Nat.card T * T.index := by
      rw [hmul, monsterOrder_eq]
      exact dvd_mul_right _ _
    exact hcop.dvd_of_dvd_mul_right h
  have hpn : p ^ n ∣ CFSG.Open.monsterOrder := by
    rw [← hn, ← hG]
    exact Subgroup.card_subgroup_dvd_card A
  have hpM : p ∣ CFSG.Open.monsterOrder := (dvd_pow_self p hn0).trans hpn
  have hpL : p ∣ ([2 ^ 46, 3 ^ 20, 5 ^ 9, 7 ^ 6, 11 ^ 2, 13 ^ 3, 17, 19, 23, 29, 31, 41, 47,
      59, 71] : List ℕ).prod := by
    rw [show ([2 ^ 46, 3 ^ 20, 5 ^ 9, 7 ^ 6, 11 ^ 2, 13 ^ 3, 17, 19, 23, 29, 31, 41, 47, 59,
      71] : List ℕ).prod = CFSG.Open.monsterOrder from monsterOrder_eq.symm]
    exact hpM
  obtain ⟨a, ha, hpa⟩ := hp.prime.dvd_prod_iff.1 hpL
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨
      p = 31 ∨ p = 41 ∨ p = 47 ∨ p = 59 ∨ p = 71 := by
    fin_cases ha
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpa))
        (by omega)
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hpa))
        (by omega)
    all_goals
      first
      | rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow hpa)]; decide
      | rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa]; decide
  have h2 : 2 ^ 46 ∣ Nat.card (GL (Fin n) (ZMod p)) := h246T.trans hdvd
  have hle : ∀ k : ℕ, ¬ p ^ (k + 1) ∣ CFSG.Open.monsterOrder → n ≤ k := fun k hk => by
    by_contra h
    exact hk ((pow_dvd_pow p (by omega)).trans hpn)
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hn9 := hle 9 (by norm_num [CFSG.Open.monsterOrder])
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn6 := hle 6 (by norm_num [CFSG.Open.monsterOrder])
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn2 := hle 2 (by norm_num [CFSG.Open.monsterOrder])
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn3 := hle 3 (by norm_num [CFSG.Open.monsterOrder])
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  all_goals
    have hn1 := hle 1 (by norm_num [CFSG.Open.monsterOrder])
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2

theorem k105SporAt_M_of_thompsonJ
    (hJ : ∃ T : Subgroup CFSG.Monster.Generated.Gmat, IsSylowTwoOf T ⊤ ∧
      T ≤ centralizer {xGmat} ∧
      K105In (normalizer (CFSG.Quasithin.thompsonJ T : Set CFSG.Monster.Generated.Gmat)) T) :
    K105SporAt .M := by
  obtain ⟨T, hT, hTz, hJT⟩ := hJ
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_gmat
  have hz := isTwoBCentralizer_Gmat xGmat (IsConj.refl _)
  exact k105SporAt_of_k105In (s := .M) hT
    (k105In_top_of_thompson hT (self_mem_quasithinOmegaOneCenter orderOf_xGmat hT hTz)
      (k105In_centralizer_of_isTwoBCentralizer hz hT hTz) hJT
      (oddLocal_of_isTwoBCentralizer orderOf_xGmat hz
        CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder hT hTz)) e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.MK
