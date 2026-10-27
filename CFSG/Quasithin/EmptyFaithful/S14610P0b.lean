module

public import CFSG.Quasithin.EmptyFaithful.S1469Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.exists_pow_mul_mem_pCoreOf (S : Setting146 G T M) {x y : G}
    (hxL : x ∈ yOfL22 T M) (hyL : y ∈ yOfL22 T M) (hxodd : Odd (orderOf x))
    (hyodd : Odd (orderOf y)) (hy1 : y ≠ 1) :
    ∃ k : ℕ, (y ^ k)⁻¹ * x ∈ pCoreOf 2 (yOfL22 T M) := by
  obtain ⟨φ⟩ := S.hyp1281.sThree
  set L := yOfL22 T M with hLdef
  have hLT : ∀ g ∈ L, g ∈ L ⊔ T := fun g hg => Subgroup.mem_sup_left hg
  have hy_LT : y ∈ L ⊔ T := hLT y hyL
  have hx_LT : x ∈ L ⊔ T := hLT x hxL
  have hyO : y ∉ pCoreOf 2 (L ⊔ T) := fun h =>
    hy1 (eq_one_of_mem_isPGroup_of_odd_orderOf (pCoreOf_isPGroup 2 (L ⊔ T)) h hyodd)
  have hc1 : Der6A.piS3 φ ⟨y, hy_LT⟩ ≠ 1 := fun h => hyO ((Der6A.piS3_eq_one_iff φ hy_LT).mp h)
  have hcube : ∀ (g : G) (hg : g ∈ L ⊔ T), Odd (orderOf g) →
      (Der6A.piS3 φ ⟨g, hg⟩) ^ 3 = 1 := by
    intro g hg hgodd
    have h1 : orderOf (Der6A.piS3 φ ⟨g, hg⟩) ∣ orderOf g := by
      have := orderOf_map_dvd (Der6A.piS3 φ) (⟨g, hg⟩ : ↥(L ⊔ T))
      have e : orderOf (⟨g, hg⟩ : ↥(L ⊔ T)) = orderOf g :=
        (Subgroup.orderOf_coe (⟨g, hg⟩ : ↥(L ⊔ T))).symm
      rwa [e] at this
    have h2 : orderOf (Der6A.piS3 φ ⟨g, hg⟩) ∣ 3 * 2 := by
      have := orderOf_dvd_natCard (Der6A.piS3 φ ⟨g, hg⟩)
      have hc : Nat.card (Equiv.Perm (Fin 3)) = 3 * 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
      rwa [hc] at this
    have h3 : Nat.Coprime (orderOf (Der6A.piS3 φ ⟨g, hg⟩)) 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr (Odd.of_dvd_nat hgodd h1).not_two_dvd_nat).symm
    exact orderOf_dvd_iff_pow_eq_one.mp (h3.dvd_of_dvd_mul_right h2)
  have hmain : ∀ k : ℕ, Der6A.piS3 φ ⟨x, hx_LT⟩ = Der6A.piS3 φ ⟨y, hy_LT⟩ ^ k →
      ∃ k : ℕ, (y ^ k)⁻¹ * x ∈ pCoreOf 2 L := by
    intro k hk
    refine ⟨k, ?_⟩
    have hyk : y ^ k ∈ L := L.pow_mem hyL k
    have hykLT : (y ^ k)⁻¹ * x ∈ L ⊔ T :=
      (L ⊔ T).mul_mem ((L ⊔ T).inv_mem ((L ⊔ T).pow_mem hy_LT k)) hx_LT
    have h1 : Der6A.piS3 φ ⟨(y ^ k)⁻¹ * x, hykLT⟩ = 1 := by
      have e : (⟨(y ^ k)⁻¹ * x, hykLT⟩ : ↥(L ⊔ T)) =
          (⟨y, hy_LT⟩ ^ k)⁻¹ * ⟨x, hx_LT⟩ := Subtype.ext (by simp)
      rw [e, map_mul, map_inv, map_pow, ← hk, inv_mul_cancel]
    exact inf_pCoreOf_sup_le L T ⟨L.mul_mem (L.inv_mem hyk) hxL,
      (Der6A.piS3_eq_one_iff φ hykLT).mp h1⟩
  rcases perm3_odd_order_fact _ _ (hcube x hx_LT hxodd) (hcube y hy_LT hyodd) hc1 with h | h | h
  · exact hmain 0 (by rw [h, pow_zero])
  · exact hmain 1 (by rw [h, pow_one])
  · exact hmain 2 h

theorem Setting146.lI_le_of_odd_mem (S : Setting146 G T M) {I P : Subgroup G} (hPI : P ≤ I)
    (hPinv : lI T M I ≤ Subgroup.normalizer (P : Set G)) {y : G} (hyL : y ∈ yOfL22 T M)
    (hyP : y ∈ P) (hodd : Odd (orderOf y)) (hy1 : y ≠ 1) : lI T M I ≤ P := by
  have hylI : y ∈ lI T M I := Subgroup.subset_closure ⟨⟨hyL, hPI hyP⟩, hodd⟩
  set N := conjClosure (Subgroup.zpowers y) (lI T M I) with hN
  have hNP : N ≤ P := conjClosure_le fun h hh z hz => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have : h * y * h⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hPinv hh) y).mp hyP
    have e : h * y ^ k * h⁻¹ = (h * y * h⁻¹) ^ k := by simp [conj_zpow]
    rw [e]
    exact P.zpow_mem this k
  have hNlI : N ≤ lI T M I := conjClosure_le fun h hh z hz => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have e : h * y ^ k * h⁻¹ = (h * y * h⁻¹) ^ k := by simp [conj_zpow]
    rw [e]
    exact (lI T M I).zpow_mem ((lI T M I).mul_mem ((lI T M I).mul_mem hh hylI)
      ((lI T M I).inv_mem hh)) k
  have hNn : lI T M I ≤ Subgroup.normalizer (N : Set G) := le_normalizer_conjClosure _ _
  refine le_trans ?_ hNP
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨⟨hxL, hxI⟩, hxodd⟩ := hx
  have hxlI : x ∈ lI T M I := Subgroup.subset_closure ⟨⟨hxL, hxI⟩, hxodd⟩
  obtain ⟨k, hk⟩ := S.exists_pow_mul_mem_pCoreOf hxL hyL hxodd hodd hy1
  have hyk : y ^ k ∈ N := N.pow_mem (le_conjClosure _ _ (Subgroup.mem_zpowers y)) k
  have hq : (y ^ k)⁻¹ * x ∈ pCoreOf 2 (yOfL22 T M) ⊓ lI T M I :=
    ⟨hk, (lI T M I).mul_mem ((lI T M I).inv_mem ((lI T M I).pow_mem hylI k)) hxlI⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 (yOfL22 T M) ⊓ lI T M I : Subgroup G) :=
    (pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hQN : (pCoreOf 2 (yOfL22 T M) ⊓ lI T M I : Subgroup G) ≤ Subgroup.normalizer (N : Set G) :=
    inf_le_right.trans hNn
  have hxNQ : x ∈ N ⊔ (pCoreOf 2 (yOfL22 T M) ⊓ lI T M I : Subgroup G) := by
    have e : x = y ^ k * ((y ^ k)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hyk hq
  exact mem_of_odd_orderOf_of_sup_pGroup hQ2 hQN hxNQ hxodd

theorem Setting146.no_odd_of_not_lI_le (S : Setting146 G T M) {I P : Subgroup G} (hPI : P ≤ I)
    (hPinv : lI T M I ≤ Subgroup.normalizer (P : Set G)) (hnot : ¬ lI T M I ≤ P) {y : G}
    (hyL : y ∈ yOfL22 T M) (hyP : y ∈ P) (hodd : Odd (orderOf y)) : y = 1 := by
  by_contra hy1
  exact hnot (S.lI_le_of_odd_mem hPI hPinv hyL hyP hodd hy1)

end CFSG.Quasithin
