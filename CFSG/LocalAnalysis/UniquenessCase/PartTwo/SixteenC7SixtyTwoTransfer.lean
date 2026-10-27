module

public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Da

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c7_isPGroup_two_ker {Q Y : Type*} [Group Q] [Finite Q] [Group Y]
    (hQ : commutator Q = ⊤) (π : Q →* Y) (hcen : π.ker ≤ center Q)
    (hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup Y, IsPGroup p P → IsCyclic P) :
    IsPGroup 2 π.ker := by
  classical
  by_contra hne
  have hodd : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card π.ker := by
    by_contra hno
    push Not at hno
    apply hne
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => by
      by_contra h
      exact hno d hd h hdvd⟩
  obtain ⟨p, hp, hp2, hpd⟩ := hodd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) p hpd
  have hzQ : orderOf (z : Q) = p := by rw [Subgroup.orderOf_coe]; exact hz
  have hzp : IsPGroup p (zpowers (z : Q)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzQ, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  let f : ↥(P : Subgroup Q) →* ↥((P : Subgroup Q).map π) :=
    (π.comp (P : Subgroup Q).subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hPmap : IsPGroup p ↥((P : Subgroup Q).map π) := IsPGroup.of_surjective P.isPGroup' f hf
  haveI : IsCyclic ↥((P : Subgroup Q).map π) := hcyc p hp hp2 _ hPmap
  have hfker : f.ker ≤ center ↥(P : Subgroup Q) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxπ : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxc : (x : Q) ∈ center Q := hcen (MonoidHom.mem_ker.2 hxπ)
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc (y : Q))
  haveI : IsMulCommutative (P : Subgroup Q) := f.isMulCommutative_of_isCyclic_of_ker_le_center hfker
  have hbot := UCK.M591D.sylow_inf_center_eq_bot hQ P
  have hmem : (z : Q) ∈ (P : Subgroup Q) ⊓ center Q :=
    ⟨hP (mem_zpowers _), hcen z.2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hzQ
  exact hp.one_lt.ne hzQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
