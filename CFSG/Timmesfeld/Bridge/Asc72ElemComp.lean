module

public import CFSG.Timmesfeld.Bridge.Asc72ZMain

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G] {D : Set G}

theorem commute_of_mem_isElemAbelian {E : Subgroup G} (h : IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : Commute a b :=
  congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem commute_of_reach_of_elemAbelian
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    {x y : G} (hx : x ∈ D) (h : Reach D x y) : Commute x y := by
  induction h with
  | refl => exact Commute.refl x
  | tail _ hbc ih =>
    obtain ⟨hb, hc, hbc'⟩ := hbc
    exact commute_of_mem_isElemAbelian (hE _ hb) (Subgroup.subset_closure ⟨hx, ih⟩)
      (Subgroup.subset_closure ⟨hc, hbc'.symm⟩)

theorem disconnected_of_not_commute_of_elemAbelian
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : ¬ Commute x y) : Disconnected D :=
  ⟨x, hx, y, hy, fun h => hxy (commute_of_reach_of_elemAbelian hE hx h)⟩

theorem isElemAbelian_closure_of_subgroup {H : Subgroup G} {D₁ : Set H}
    (hD₁ : ∀ k ∈ D₁, (k : G) ∈ D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d})) :
    ∀ v ∈ D₁, IsElemAbelian 2 (Subgroup.closure {e : H | e ∈ D₁ ∧ Commute e v}) := by
  intro v hv
  have hv' := hE (v : G) (hD₁ v hv)
  have hle : Subgroup.closure {e : H | e ∈ D₁ ∧ Commute e v} ≤
      (Subgroup.closure {e : G | e ∈ D ∧ Commute e (v : G)}).comap H.subtype := by
    rw [Subgroup.closure_le]
    intro e he
    exact Subgroup.subset_closure ⟨hD₁ e he.1, he.2.map H.subtype⟩
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · exact (commute_of_mem_isElemAbelian hv' (hle a.2) (hle b.2)).eq
  · rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hv'.2 _ (hle hx)

variable [Finite G]

theorem false_of_nonSimple_minimalNormal (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    {M : Subgroup G} (hM : IsMinimalNormal M) (hMs : ¬ IsSimpleGroup M) : False := by
  have := hM.1
  obtain ⟨W⟩ := nonempty_wreathData hS hrad hM hMs
  obtain ⟨d, hd⟩ := hS.nonempty
  obtain ⟨i, j, hij, hπ, -⟩ := W.swap d hd
  have hdd : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hdinv : d⁻¹ = d := hS.oddT.inv_eq hd
  have hconj : ∀ z ∈ W.S i, d * z * d⁻¹ ∈ W.S j := by
    intro z hz
    have h := W.conj d i
    rw [hπ, Equiv.swap_apply_left] at h
    rw [← h]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  have hcomm_ij : ∀ {x y : G}, x ∈ W.S i → y ∈ W.S j → Commute x y := fun hx hy =>
    WreathStruct.commute_of_mem_of_ne W.e_single hij hx hy
  have hinter : ∀ {x : G}, x ∈ W.S i → x ∈ W.S j → x = 1 := fun hx hy =>
    WreathStruct.eq_one_of_mem_of_mem W.e_single hij hx hy
  have aux : ∀ x ∈ W.S i, x * x = 1 →
      x * d * x ∈ D ∧ Commute (x * d * x) d ∧ (x * d * x) * d = x * (d * x * d⁻¹) := by
    intro x hx hxx
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hy : d * x * d⁻¹ ∈ W.S j := hconj x hx
    have hyy : (d * x * d⁻¹) * (d * x * d⁻¹) = 1 := by
      calc (d * x * d⁻¹) * (d * x * d⁻¹) = d * (x * x) * d⁻¹ := by group
        _ = 1 := by rw [hxx, mul_one, mul_inv_cancel]
    have hmem : x * d * x ∈ D := by
      have := hS.conj_mem x hd
      rwa [hxinv] at this
    have heq : (x * d * x) * d = x * (d * x * d⁻¹) := by
      rw [hdinv]
      group
    refine ⟨hmem, ?_, heq⟩
    rw [commute_iff_mul_sq_eq_one (hS.oddT.mul_self_eq_one hmem) hdd, heq,
      (hcomm_ij hx hy).mul_pow, pow_two x, pow_two (d * x * d⁻¹), hxx, hyy, one_mul]
  have key : ∀ x ∈ W.S i, x * x = 1 → ∀ x' ∈ W.S i, x' * x' = 1 → Commute x x' := by
    intro x hx hxx x' hx' hx'x'
    obtain ⟨hD, hcd, hed⟩ := aux x hx hxx
    obtain ⟨hD', hcd', hed'⟩ := aux x' hx' hx'x'
    have hee' : Commute (x * d * x) (x' * d * x') :=
      commute_of_mem_isElemAbelian (hE d hd) (Subgroup.subset_closure ⟨hD, hcd⟩)
        (Subgroup.subset_closure ⟨hD', hcd'⟩)
    have hcomm' : Commute ((x * d * x) * d) ((x' * d * x') * d) :=
      Commute.mul_left (hee'.mul_right hcd) (hcd'.symm.mul_right (Commute.refl d))
    rw [hed, hed'] at hcomm'
    have hy : d * x * d⁻¹ ∈ W.S j := hconj x hx
    have hy' : d * x' * d⁻¹ ∈ W.S j := hconj x' hx'
    set y := d * x * d⁻¹
    set y' := d * x' * d⁻¹
    have h1 : x * y * (x' * y') = (x * x') * (y * y') :=
      (hcomm_ij hx' hy).symm.mul_mul_mul_comm x y'
    have h2 : x' * y' * (x * y) = (x' * x) * (y' * y) :=
      (hcomm_ij hx hy').symm.mul_mul_mul_comm x' y
    have h4 : (x * x') * (y * y') = (x' * x) * (y' * y) := by
      rw [← h1, ← h2]
      exact hcomm'.eq
    have h3 : (x' * x)⁻¹ * (x * x') = (y' * y) * (y * y')⁻¹ := by
      calc (x' * x)⁻¹ * (x * x') = (x' * x)⁻¹ * ((x * x') * (y * y')) * (y * y')⁻¹ := by group
        _ = (x' * x)⁻¹ * ((x' * x) * (y' * y)) * (y * y')⁻¹ := by rw [h4]
        _ = (y' * y) * (y * y')⁻¹ := by group
    have h5 : (x' * x)⁻¹ * (x * x') = 1 := by
      apply hinter
      · exact (W.S i).mul_mem ((W.S i).inv_mem ((W.S i).mul_mem hx' hx))
          ((W.S i).mul_mem hx hx')
      · rw [h3]
        exact (W.S j).mul_mem ((W.S j).mul_mem hy' hy)
          ((W.S j).inv_mem ((W.S j).mul_mem hy hy'))
    exact (inv_mul_eq_one.mp h5).symm
  obtain ⟨a, haS, ha⟩ : ∃ a ∈ W.S i, orderOf a = 2 := by
    have heven : 2 ∣ Nat.card (W.S i) := by
      by_contra hodd
      exact W.S_ne_bot i (eq_bot_of_le_of_isSolvable hrad (W.le i)
        (fun m hm x hx => W.conj_mem_of_mem hm hx)
        (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))))
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by decide)
  haveI := W.simple i
  set Inv : Set (W.S i) := {x | x * x = 1} with hInv
  have hInvC : ∀ x ∈ Inv, ∀ y ∈ Inv, Commute x y := fun x hx y hy =>
    Subtype.ext (key x x.2 (congrArg Subtype.val hx) y y.2 (congrArg Subtype.val hy)).eq
  have hconjInv : ∀ x ∈ Group.conjugatesOfSet Inv, x ∈ Inv := by
    intro x hx
    obtain ⟨b, hb, hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hbx
    show c * b * c⁻¹ * (c * b * c⁻¹) = 1
    calc c * b * c⁻¹ * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
      _ = 1 := by rw [show b * b = 1 from hb, mul_one, mul_inv_cancel]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure Inv) with hT | hT
  · rw [Subgroup.normalClosure_eq_bot_iff] at hT
    have h1 : (⟨a, haS⟩ : W.S i) ∈ ({1} : Set (W.S i)) :=
      hT (show (⟨a, haS⟩ : W.S i) * ⟨a, haS⟩ = 1 from Subtype.ext haa)
    exact ha1 (congrArg Subtype.val h1)
  · obtain ⟨p, q, hpq⟩ := W.not_comm i
    have hp : p ∈ Subgroup.normalClosure Inv := by rw [hT]; exact Subgroup.mem_top p
    have hq : q ∈ Subgroup.normalClosure Inv := by rw [hT]; exact Subgroup.mem_top q
    exact hpq (commute_of_mem_closure (fun x hx y hy => hInvC x (hconjInv x hx) y (hconjInv y hy))
      hp hq).eq

theorem radical_eq_bot_of_ge_normal
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {M : Subgroup G} [M.Normal] (hC : Subgroup.centralizer (M : Set G) = ⊥) {H : Subgroup G}
    (hMH : M ≤ H) (N : Subgroup H) (hN : N.Normal) (hNs : Group.IsSolvable N) : N = ⊥ := by
  set N' : Subgroup G := N.map H.subtype with hN'
  have hconj : ∀ h ∈ H, ∀ n ∈ N', h * n * h⁻¹ ∈ N' := by
    rintro h hh _ ⟨n, hn, rfl⟩
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hN.conj_mem n hn ⟨h, hh⟩, by simp⟩
  have hinf : N' ⊓ M = ⊥ := by
    refine eq_bot_of_le_of_isSolvable hrad inf_le_right (fun m hm n hn => ?_) ?_
    · exact ⟨hconj m (hMH hm) n hn.1, ‹M.Normal›.conj_mem n hn.2 m⟩
    · have : Group.IsSolvable N' :=
        Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective N)
      exact Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_left : N' ⊓ M ≤ N'))
  have hcent : ∀ n ∈ N', n ∈ Subgroup.centralizer (M : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 : n * m * n⁻¹ * m⁻¹ ∈ N' ⊓ M := by
      refine ⟨?_, M.mul_mem (‹M.Normal›.conj_mem m hm n) (M.inv_mem hm)⟩
      have := N'.mul_mem hn (hconj m (hMH hm) n⁻¹ (N'.inv_mem hn))
      simpa [mul_assoc] using this
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [eq_bot_iff]
  intro n hn
  have h2 := hcent _ (show (n : G) ∈ N' from ⟨n, hn, rfl⟩)
  rw [hC, Subgroup.mem_bot] at h2
  exact Subgroup.mem_bot.mpr (Subtype.ext h2)

theorem false_of_almostSimple_elemComponents (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d}))
    {M : Subgroup G} (hM : IsMinimalNormal M) (hMs : IsSimpleGroup M)
    (hcomm : ¬ commutator G ≤ M)
    (ih : ∀ (K : Type) [Group K] [Finite K], Nat.card K < Nat.card G → ∀ E : Set K,
      Setup K E → (∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected E →
      (∀ d ∈ E, IsElemAbelian 2 (Subgroup.closure {e | e ∈ E ∧ Commute e d})) →
      CFSG.BenderSuzuki.IsBenderGroup K) : False := by
  have := hM.1
  have hC := centralizer_eq_bot_of_minimal hS hrad hM
  obtain ⟨u, hu⟩ := hS.nonempty
  have huM : u ∉ M := by
    rcases hS.subset_or_disjoint M with h | h
    · exact absurd (by rw [hS.eq_top_of_subset M h]; exact le_top) hcomm
    · exact h u hu
  have hMH : M ≤ M ⊔ Subgroup.zpowers u := le_sup_left
  have huH : u ∈ M ⊔ Subgroup.zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hHtop : M ⊔ Subgroup.zpowers u ≠ ⊤ := fun h =>
    hcomm (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top h inferInstance)
  have hcard : Nat.card ↥(M ⊔ Subgroup.zpowers u) < Nat.card G :=
    lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _))
      fun h => hHtop (Subgroup.eq_top_of_card_eq _ h)
  have hcls := isOddTranspClass_conjSet hS hrad hM hMs hu
  have hSH : Setup ↥(M ⊔ Subgroup.zpowers u) (conjSet M u) := ⟨hcls.1, hcls.2.1, hcls.2.2⟩
  have hD₁ : ∀ k ∈ conjSet M u, (k : G) ∈ D := by
    rintro k ⟨m, hm, hk⟩
    rw [hk]
    exact hS.conj_mem m hu
  have hE₁ := isElemAbelian_closure_of_subgroup hD₁ hE
  have hnc : ∃ x ∈ conjSet M u, ∃ y ∈ conjSet M u, ¬ Commute x y := by
    by_contra hcon
    push Not at hcon
    apply hM.2.1
    refine hrad M hM.1 (Group.isSolvable_of_comm fun a b => Subtype.ext ?_)
    have ha : (⟨a, hMH a.2⟩ : ↥(M ⊔ Subgroup.zpowers u)) ∈ Subgroup.closure (conjSet M u) := by
      rw [hSH.gen]
      exact Subgroup.mem_top _
    have hb : (⟨b, hMH b.2⟩ : ↥(M ⊔ Subgroup.zpowers u)) ∈ Subgroup.closure (conjSet M u) := by
      rw [hSH.gen]
      exact Subgroup.mem_top _
    have h := congrArg Subtype.val (commute_of_mem_closure hcon ha hb).eq
    exact h
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hB := ih ↥(M ⊔ Subgroup.zpowers u) hcard (conjSet M u) hSH
    (radical_eq_bot_of_ge_normal hrad hC hMH)
    (disconnected_of_not_commute_of_elemAbelian hE₁ hx hy hxy) hE₁
  haveI := IsBenderGroup.isSimpleGroup hB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (M.subgroupOf (M ⊔ Subgroup.zpowers u)) with h | h
  · apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    have h1 : (⟨m, hMH hm⟩ : ↥(M ⊔ Subgroup.zpowers u)) ∈
        M.subgroupOf (M ⊔ Subgroup.zpowers u) := hm
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · have h1 : (⟨u, huH⟩ : ↥(M ⊔ Subgroup.zpowers u)) ∈
        M.subgroupOf (M ⊔ Subgroup.zpowers u) := by
      rw [h]
      exact Subgroup.mem_top _
    exact huM h1

section Certified


theorem isBenderGroup_of_reduced (hT : ThirdKindExclusion) (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hdisc : Disconnected D)
    (hZ : Subgroup.center G = ⊥) (hnorm : ∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K)
    (hIH : SmallerHolds (Nat.card G)) : CFSG.BenderSuzuki.IsBenderGroup G := by
  by_cases hnp : Moufang.NoPolar D
  · exact isBenderGroup_of_noPolar hS hrad hdisc hnp
  · exfalso
    simp only [Moufang.NoPolar, not_forall] at hnp
    obtain ⟨u, hu, v, hv, hc, hne, hnot⟩ := hnp
    obtain ⟨w, hw, huw, htri, h3⟩ := exists_thirdKind hS hdisc hnorm hu hv hne hc hnot
    exact hT G D hS hrad hdisc hZ hnorm hIH u hu w hw v hv htri h3 huw hnot

theorem isBenderGroup_of_elemComponents {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hdisc : Disconnected D)
    (hE : ∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d})) :
    CFSG.BenderSuzuki.IsBenderGroup G := by
  have hT : ThirdKindExclusion := thirdKindExclusion_of_lemma316L24 lemma316L24Input
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (D : Set G), Nat.card G = n →
      Setup G D → (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → Disconnected D →
      (∀ d ∈ D, IsElemAbelian 2 (Subgroup.closure {e | e ∈ D ∧ Commute e d})) →
      CFSG.BenderSuzuki.IsBenderGroup G from key _ G D rfl hS hrad hdisc hE
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ D hn hS hrad hdisc hE
  obtain ⟨M, hM⟩ := exists_minimalNormal hS
  have := hM.1
  have hC := centralizer_eq_bot_of_minimal hS hrad hM
  have hZ : Subgroup.center G = ⊥ := le_bot_iff.mp (hC ▸ center_le_centralizer M)
  by_cases hMs : IsSimpleGroup M
  · by_cases hcomm : commutator G ≤ M
    · have hnorm : ∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K := by
        intro K hK
        rcases hM.2.2 (K ⊓ M) inferInstance inf_le_right with h | h
        · left
          rw [eq_bot_iff, ← hC]
          intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          exact (Subgroup.commute_of_normal_of_disjoint K M hK hM.1 (disjoint_iff.mpr h) k m hk
            hm).eq.symm
        · exact Or.inr (hcomm.trans (inf_eq_right.mp h))
      exact isBenderGroup_of_reduced hT hS hrad hdisc hZ hnorm
        (fun K _ _ _ E hSK hradK hdiscK =>
          strongConclusion_of_inputs wreathInput hT K E hSK hradK hdiscK)
    · exact (false_of_almostSimple_elemComponents hS hrad hE hM hMs hcomm
        (fun K _ _ hK E hSK hradK hdiscK hEK =>
          ih _ (hn ▸ hK) K E rfl hSK hradK hdiscK hEK)).elim
  · exact (false_of_nonSimple_minimalNormal hS hrad hE hM hMs).elim

end Certified

end CFSG.Timmesfeld.Bridge.Asc72
