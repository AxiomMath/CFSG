module

public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.RankThree.PartTwo.KFacts.K72List

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open scoped commutatorElement

section Odd

variable {G : Type*} [Group G] [Finite G]

theorem le_center_of_isCyclic_normal (hperf : commutator G = ⊤) (T : Subgroup G) [T.Normal]
    [IsCyclic T] : T ≤ Subgroup.center G := by
  let e := IsCyclic.mulAutMulEquiv T
  letI : CommGroup (MulAut T) := e.toMonoidHom.commGroupOfInjective e.injective
  have h := Abelianization.commutator_subset_ker (MulAut.conjNormal : G →* MulAut T)
  rw [hperf] at h
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : (MulAut.conjNormal g : MulAut T) = 1 := h (Subgroup.mem_top g)
  have h1 := congrArg (fun φ : MulAut T => ((φ ⟨x, hx⟩ : T) : G)) hg
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

@[expose] def torsionSub (N : Subgroup G) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (ℓ : ℕ) :
    Subgroup G where
  carrier := {x | x ∈ N ∧ x ^ ℓ = 1}
  mul_mem' := fun {a b} ha hb =>
    ⟨N.mul_mem ha.1 hb.1, by
      rw [Commute.mul_pow (show Commute a b from hN a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨N.one_mem, one_pow ℓ⟩
  inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

instance (N : Subgroup G) [N.Normal] (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (ℓ : ℕ) :
    (torsionSub N hN ℓ).Normal where
  conj_mem := fun n hn g => ⟨(inferInstance : N.Normal).conj_mem n hn.1 g, by
    rw [conj_pow, hn.2]
    group⟩

theorem eq_bot_of_normal_of_odd (hperf : commutator G = ⊤)
    (hcyc : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ P : Sylow q G, IsCyclic P) :
    ∀ (n : ℕ) (N : Subgroup G), N.Normal → Nat.card N = n → Odd n → N = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hNn hcard hodd
  by_contra hne
  haveI := hNn
  haveI : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hcard ▸ hodd)
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  have hlt : (⁅N, N⁆ : Subgroup G) < N := by
    rw [← N.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial N
  have hcardlt : Nat.card (⁅N, N⁆ : Subgroup G) < n := by
    rw [← hcard]
    refine lt_of_not_ge fun hge => hlt.ne ?_
    exact Subgroup.eq_of_le_of_card_ge hlt.le hge
  have hodd' : Odd (Nat.card (⁅N, N⁆ : Subgroup G)) :=
    Odd.of_dvd_nat (hcard ▸ hodd) (Subgroup.card_dvd_of_le hlt.le)
  have hcomm : (⁅N, N⁆ : Subgroup G) = ⊥ := ih _ hcardlt _ inferInstance rfl hodd'
  have hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ (⁅N, N⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hn1 : n ≠ 1 := fun h1 => hne (Subgroup.eq_bot_of_card_eq N (hcard.trans h1))
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hℓn)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) ℓ (hcard ▸ hℓn)
  have hzo : orderOf (x : G) = ℓ := by rw [Subgroup.orderOf_coe, hx]
  have hzT : (x : G) ∈ torsionSub N hab ℓ := ⟨x.2, by rw [← hzo]; exact pow_orderOf_eq_one _⟩
  have hTp : IsPGroup ℓ (torsionSub N hab ℓ) := fun y => ⟨1, Subtype.ext (by simpa using y.2.2)⟩
  obtain ⟨P, hTP⟩ := hTp.exists_le_sylow
  haveI : IsCyclic P := hcyc ℓ hℓ2 P
  haveI : IsCyclic (torsionSub N hab ℓ) := Subgroup.isCyclic_of_le hTP
  have hzc : (x : G) ∈ Subgroup.center G :=
    le_center_of_isCyclic_normal hperf (torsionSub N hab ℓ) hzT
  have h1 : (x : G) = 1 :=
    CFSG.RankThree.PartTwo.KFacts.eq_one_of_mem_center_of_isCyclic_sylow hperf
      (fun Q => hcyc ℓ hℓ2 Q) hzc (hzo ▸ pow_orderOf_eq_one _)
  rw [h1, orderOf_one] at hzo
  exact hℓ.one_lt.ne hzo

theorem oddCore_eq_bot_of_isPerfect (hperf : commutator G = ⊤)
    (hcyc : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ P : Sylow q G, IsCyclic P) :
    CFSG.oddCore G = ⊥ := by
  rw [CFSG.ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two,
    CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  exact eq_bot_of_normal_of_odd hperf hcyc _ K hK rfl (Nat.coprime_two_left.mp hcop)

end Odd

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
