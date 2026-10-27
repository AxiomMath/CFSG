module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27B
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27P
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.SBc17
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {H R M K J : Subgroup G} (c : Ctx H R M K J) (hC27 : ASC27Statement G)
include c hC27

theorem false_of_no_large_prime {X : Subgroup (MulAut ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))}
    (hJX : autOn J (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ≤ X)
    (h : ∀ x ∈ X, ∀ r : ℕ, r.Prime → 5 ≤ r → orderOf x = r → False) : False := by
  refine c.false_of_two_three hC27 fun r hr hrd => ?_
  by_contra hne
  push Not at hne
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrd
  exact h x (hJX x.2) r hr (hr.five_le_of_ne_two_of_ne_three hne.1 hne.2)
    (by rw [Subgroup.orderOf_coe]; exact hx)

theorem false_of_borel
    (hB : IsBorelIn (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
      (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) : False :=
  c.not_le_of_isSolvable hC27 (isSolvable_of_isBorelIn hB) (autOn_mono' c.J_le)

theorem false_of_partition {sizes : Multiset ℕ} (hs : ∀ k ∈ sizes, k < 5)
    (hcard : Multiset.card sizes < 5) {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P sizes)
    (e : ↥(autOn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃* Equiv.Perm (Fin 7))
    (hmap : ((autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))).subgroupOf
        (autOn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))).map e.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) : False := by
  refine c.false_of_no_large_prime hC27 (autOn_mono' c.J_le) fun x hx r hr h5 hxr => ?_
  have hx2 : x ∈ autOn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
    autOn_mono' (inf_le_right.trans le_sup_left) hx
  have hmem : e ⟨x, hx2⟩ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7) :=
    hmap ▸ Subgroup.mem_map_of_mem _ (show (⟨x, hx2⟩ : ↥(autOn (K ⊔ R) _)) ∈ _ from hx)
  have hord : orderOf (e ⟨x, hx2⟩) = r := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxr]
  have h1 := eq_one_of_mem_stabilizer hr (by rw [← hord]; exact pow_orderOf_eq_one _)
    (fun k hk => (hs k hk).trans_le h5) (hcard.trans_le h5) hP (Subgroup.mem_inf.mp hmem).1
  rw [h1, orderOf_one] at hord
  exact hr.one_lt.ne hord

omit hC27 in
theorem false_of_index {m : ℕ} (hidx : M.relIndex K = m)
    (hq : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = m * 72) : False := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  have hK : Nat.card ↥K = m * (2 ^ a * 72) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hq, ha]
    ring
  have hmul := Subgroup.relIndex_mul_card (H := M) (K := K)
  rw [hidx, hK] at hmul
  have hm : m ≠ 0 := by
    rintro rfl
    exact Subgroup.index_ne_zero_of_finite hidx
  have hMK : Nat.card ↥(M ⊓ K) = 2 ^ (a + 3) * 3 ^ 2 := by
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) hmul
    rw [this]
    ring
  apply c.nonsolv
  refine isSolvable_of_prime_dvd Nat.prime_two Nat.prime_three fun r hr hrd => ?_
  have h1 : r ∣ 2 ^ (a + 3) * 3 ^ 2 := hMK ▸ hrd.trans (Subgroup.card_dvd_of_le c.J_le)
  rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3))

omit hC27 in
theorem false_of_hatA6 (hA : IsHatA6Block K) (hidx : M.relIndex K = 15) : False := by
  obtain ⟨-, ⟨-, hZ3, ⟨e⟩⟩, -⟩ := hA
  refine c.false_of_index hidx ?_
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))
  rw [hZ3, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
  rw [h1]
  decide

omit hC27 in
theorem false_of_excA7 (hA : IsExcA7Block K) (hidx : M.relIndex K = 35) : False := by
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := hA
  refine c.false_of_index hidx ?_
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

end Ctx

end CFSG.Quasithin.H13.Ch4.T425C27
