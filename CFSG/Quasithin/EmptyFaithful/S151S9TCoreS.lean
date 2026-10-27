module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace CoreS

theorem oPrimeResidualOf_le {G : Type*} [Group G] {p : ℕ} (X : Subgroup G) :
    oPrimeResidualOf p X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem conj_mem_oPrimeResidualOf {G : Type*} [Group G] {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {y : G} (hy : y ∈ oPrimeResidualOf p X) :
    g * y * g⁻¹ ∈ oPrimeResidualOf p X := by
  have h : oPrimeResidualOf p X ≤ (oPrimeResidualOf p X).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨?_, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx.1
    · obtain ⟨k, hk⟩ := hx.2
      refine ⟨k, ?_⟩
      rw [← hk]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  exact h hy

theorem mem_normalizer_oPrimeResidualOf {G : Type*} [Group G] {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (oPrimeResidualOf p X : Set G) :=
  B6.mem_normalizer_of_forall_mem (fun _ hx => conj_mem_oPrimeResidualOf hg hx) fun x hx => by
    simpa using conj_mem_oPrimeResidualOf ((Subgroup.normalizer (X : Set G)).inv_mem hg) hx

theorem exists_orderOf_eq_two_pow_mul_three_pow {G : Type*} [Group G] {P : Subgroup G} {a : ℕ}
    (hP : Nat.card ↥P = 3 * 2 ^ a) : ∀ x ∈ P, ∃ i j : ℕ, orderOf x = 2 ^ i * 3 ^ j := by
  intro x hx
  have hdvd : orderOf x ∣ 3 * 2 ^ a := by
    rw [← hP]
    exact (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥P)) ▸ orderOf_dvd_natCard (⟨x, hx⟩ : ↥P)
  obtain ⟨u, v, hu, hv, huv⟩ := Nat.dvd_mul.mp hdvd
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hv
  rcases (Nat.dvd_prime Nat.prime_three).mp hu with rfl | rfl
  · exact ⟨i, 0, by rw [← huv]; ring⟩
  · exact ⟨i, 1, by rw [← huv]; ring⟩

theorem relIndex_sup_eq_three {G : Type*} [Group G] [Finite G] {P S : Subgroup G}
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hcard : Nat.card ↥P = 3 * Nat.card ↥(S ⊓ P)) :
    S.relIndex (P ⊔ S) = 3 := by
  have h1 : (S ⊓ P).relIndex P = S.relIndex (S ⊔ P) := B6.relIndex_inf_eq_relIndex_sup hSP
  have h2 : (S ⊓ P).relIndex P * Nat.card ↥(S ⊓ P ⊓ P) = Nat.card ↥P :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr inf_le_right] at h2
  have hpos : 0 < Nat.card ↥(S ⊓ P) := Nat.card_pos
  rw [sup_comm, ← h1]
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans hcard)

theorem isMaxSubgroupIn_of_prime_relIndex {G : Type*} [Group G] {H S : Subgroup G} (hSH : S ≤ H)
    (hp : (S.relIndex H).Prime) : IsMaxSubgroupIn H S := by
  refine ⟨lt_of_le_of_ne hSH fun h => ?_, fun K hSK hKH => ?_⟩
  · rw [h, Subgroup.relIndex_self] at hp
    exact Nat.not_prime_one hp
  · have hmul := Subgroup.relIndex_mul_relIndex S K H hSK.le hKH
    have hdvd : S.relIndex K ∣ S.relIndex H := hmul ▸ dvd_mul_right _ _
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (Subgroup.relIndex_eq_one.mp h1) (not_le_of_gt hSK)
    · rw [h1] at hmul
      have h2 : K.relIndex H = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hmul)
      exact le_antisymm hKH (Subgroup.relIndex_eq_one.mp h2)

end CoreS

theorem twoResidual_sup_eq {G : Type} [Group G] [Finite G] {P S : Subgroup G}
    (hS2 : IsPGroup 2 ↥S) (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hP : ∀ x ∈ P, ∃ i j : ℕ, orderOf x = 2 ^ i * 3 ^ j) :
    twoResidual (P ⊔ S) = oPrimeResidualOf 3 P := by
  have hHN : P ⊔ S ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hSP
  have hquot : ∀ x ∈ P ⊔ S, ∃ k : ℕ, x ^ 2 ^ k ∈ P :=
    B6.isTwoQuotient_of_sup_eq hS2 hHN (sup_comm S P)
  refine le_antisymm (twoResidual_le_of_isTwoQuotient ?_ ?_ ?_) ?_
  · exact (CoreS.oPrimeResidualOf_le P).trans le_sup_left
  · exact sup_le (fun _ hg => CoreS.mem_normalizer_oPrimeResidualOf (Subgroup.le_normalizer hg))
      fun _ hg => CoreS.mem_normalizer_oPrimeResidualOf (hSP hg)
  · intro x hx
    obtain ⟨k, hk⟩ := hquot x hx
    obtain ⟨i, j, hij⟩ := hP _ hk
    refine ⟨k + i, ?_⟩
    have hord : orderOf ((x ^ 2 ^ k) ^ 2 ^ i) = 3 ^ j := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hij ▸ dvd_mul_right _ _), hij]
      exact Nat.mul_div_cancel_left _ (pow_pos two_pos _)
    rw [pow_add, pow_mul]
    exact Subgroup.subset_closure ⟨P.pow_mem hk _, j, hord⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxP, k, hxk⟩
    obtain ⟨m, hm⟩ := twoResidual_isTwoQuotient (P ⊔ S) x (Subgroup.mem_sup_left hxP)
    have hcop : (2 ^ m).gcd (orderOf x) = 1 := by
      rw [hxk]
      exact Nat.Coprime.pow m k (by norm_num)
    exact (Subgroup.zpowers_le.mpr hm) (mem_zpowers_pow_iff.mpr hcop)

theorem isMinParabolic_sup {G : Type} [Group G] [Finite G] {P S : Subgroup G}
    (hS2 : IsPGroup 2 ↥S) (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hcard : Nat.card ↥P = 3 * Nat.card ↥(S ⊓ P))
    (hnS : ¬ P ≤ Subgroup.normalizer (S : Set G)) :
    IsMinParabolicOf (P ⊔ S) (P ⊔ S) := by
  have hidx : S.relIndex (P ⊔ S) = 3 := CoreS.relIndex_sup_eq_three hSP hcard
  have hmax : IsMaxSubgroupIn (P ⊔ S) S :=
    CoreS.isMaxSubgroupIn_of_prime_relIndex le_sup_right (hidx ▸ Nat.prime_three)
  have hsyl : IsSylowTwoOf S (P ⊔ S) :=
    ⟨le_sup_right, hS2, by show ¬ 2 ∣ S.relIndex (P ⊔ S); rw [hidx]; decide⟩
  have hnn : ¬ P ⊔ S ≤ Subgroup.normalizer (S : Set G) := fun h => hnS (le_sup_left.trans h)
  refine (minParabolic_iff.mp ⟨hsyl, hnn, isUniqueMaxOver_iff.mpr ⟨hmax, le_rfl, ?_⟩⟩).1
  intro N hN hSN
  by_contra hne
  exact hN.1.ne (hmax.2 N (lt_of_le_of_ne hSN (Ne.symm hne)) hN.le)

end CFSG.Quasithin.S151S9T
