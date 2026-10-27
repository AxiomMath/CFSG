module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvTwoElt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Λ : Type} [Group Λ]

theorem odd_orderOf_of_mem_center [Finite Λ]
    (hO2 : ∀ R : Subgroup Λ, R.Normal → IsPGroup 2 R → R = ⊥) {N : Subgroup Λ} [N.Normal]
    {z : Λ} (hzN : z ∈ N) (hzC : z ∈ Subgroup.centralizer (N : Set Λ)) : Odd (orderOf z) := by
  obtain ⟨e, m, hm2, hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 2 (by norm_num)
  have h2 : IsTwoElt (z ^ m) := isTwoElt_iff_pow.mpr ⟨e, by
    rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]⟩
  have h1 : z ^ m = 1 :=
    eq_one_of_isTwoElt_of_mem_center hO2 (N.pow_mem hzN m)
      (Subgroup.pow_mem _ hzC m) h2
  have hdvd : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one h1
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm2)
  have he : 2 ^ e = 1 := by
    rw [hm] at hdvd
    have := Nat.le_of_dvd hm0 hdvd
    have h1e : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    nlinarith
  rw [hm, he, one_mul]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2)

theorem mem_of_isTwoElt_mul {S : Subgroup Λ} {s z : Λ} (hs : s ∈ S) (hc : Commute s z)
    (hz : Odd (orderOf z)) (h2 : IsTwoElt (s * z)) : s * z ∈ S := by
  obtain ⟨k, hk⟩ := isTwoElt_iff_pow.mp h2
  rw [hc.mul_pow] at hk
  have hzS : z ^ (2 ^ k) ∈ S := by
    rw [eq_inv_of_mul_eq_one_right hk]
    exact S.inv_mem (S.pow_mem hs _)
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hz)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hz' : z ∈ S := by
    rw [← hm]
    exact S.pow_mem hzS _
  exact S.mul_mem hs hz'

theorem mem_centralizer_sup {S T : Subgroup Λ} {z : Λ} (hS : ∀ s ∈ S, Commute z s)
    (hT : ∀ t ∈ T, Commute z t) :
    z ∈ Subgroup.centralizer ((S ⊔ T : Subgroup Λ) : Set Λ) := by
  have hle : S ⊔ T ≤ Subgroup.centralizer ({z} : Set Λ) := by
    refine sup_le (fun s hs => ?_) (fun t ht => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hS s hs).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hT t ht).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem exists_mul_central {S T : Subgroup Λ} [T.Normal] (hST : ⁅S, T⁆ = ⊥) {x : Λ}
    (hx : x ∈ S ⊔ T) (hxT : ∀ t ∈ T, Commute x t) :
    ∃ s ∈ S, ∃ z, z ∈ S ⊔ T ∧ z ∈ Subgroup.centralizer ((S ⊔ T : Subgroup Λ) : Set Λ) ∧
      Commute s z ∧ x = s * z := by
  have hST' : S ≤ Subgroup.centralizer (T : Set Λ) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hST
  have hx' : x ∈ ((S ⊔ T : Subgroup Λ) : Set Λ) := hx
  rw [Subgroup.mul_normal S T] at hx'
  obtain ⟨s, hs, t, ht, rfl⟩ := hx'
  have hst : ∀ t' ∈ T, Commute s t' := fun t' ht' =>
    (Subgroup.mem_centralizer_iff.mp (hST' hs) t' ht').symm
  have htT : ∀ t' ∈ T, Commute t t' := fun t' ht' => by
    have h1 := hxT t' ht'
    have h2 := (hst t' ht').symm
    have : t = s⁻¹ * (s * t) := by group
    rw [this]
    exact ((hst t' ht').inv_left).mul_left h1
  have htS : ∀ s' ∈ S, Commute t s' := fun s' hs' =>
    Subgroup.mem_centralizer_iff.mp (hST' hs') t ht
  exact ⟨s, hs, t, Subgroup.mem_sup_right ht, mem_centralizer_sup htS htT,
    (htS s hs).symm, rfl⟩

theorem opp_le_of_forall {X S : Subgroup Λ} (h : ∀ x ∈ X, IsTwoElt x → x ∈ S) :
    Opp 2 X ≤ S :=
  (Subgroup.closure_le S).mpr fun x hx => h x hx.1 hx.2

theorem mem_opp_of_isTwoElt {X : Subgroup Λ} {x : Λ} (hx : x ∈ X) (h2 : IsTwoElt x) :
    x ∈ Opp 2 X :=
  Subgroup.subset_closure ⟨hx, h2⟩

theorem opp_mono {X Y : Subgroup Λ} (h : X ≤ Y) : Opp 2 X ≤ Opp 2 Y :=
  opp_le_of_forall fun _ hx h2 => mem_opp_of_isTwoElt (h hx) h2

theorem opp_le (X : Subgroup Λ) : Opp 2 X ≤ X :=
  opp_le_of_forall fun _ hx _ => hx

theorem isPGroup_of_opp_eq_of_commutator_eq_bot {L : Subgroup Λ} (hL : Opp 2 L = L)
    (hab : ⁅L, L⁆ = ⊥) : IsPGroup 2 L := by
  have hc : L ≤ Subgroup.centralizer (L : Set Λ) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hab
  refine isPGroup_of_forall_isTwoElt fun x hx => ?_
  rw [← hL] at hx
  refine forall_isTwoElt_closure (fun y hy => hy.2) ?_ x hx
  intro a ha b hb _
  exact (Subgroup.mem_centralizer_iff.mp (hc hb.1) a ha.1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
