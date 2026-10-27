module

public import CFSG.Quasithin.EmptyFaithful.LRed6Mod
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases2
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearG2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace LRed6

section Perfect

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_perfect_two_index {H L : Subgroup G} (hLH : L ≤ H) (hP : Group.IsPerfect ↥H)
    (hN : (L.subgroupOf H).Normal) (hj : ∃ j : ℕ, Nat.card ↥H = 2 ^ j * Nat.card ↥L) : L = H := by
  obtain ⟨j, hj⟩ := hj
  set N : Subgroup ↥H := L.subgroupOf H with hNdef
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 : Nat.card ↥N = Nat.card ↥L := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have hQ : Nat.card (↥H ⧸ N) = 2 ^ j := by
    rw [h2, hj] at h1
    exact (Nat.eq_of_mul_eq_mul_right hLpos h1).symm
  have hPQ : IsPGroup 2 (↥H ⧸ N) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.iff_card (p := 2)).mpr ⟨j, hQ⟩
  have hnil : Group.IsNilpotent (↥H ⧸ N) := hPQ.isNilpotent
  have hsolv : Group.IsSolvable (↥H ⧸ N) := inferInstance
  have hperf : Group.IsPerfect (↥H ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  by_cases hnt : Nontrivial (↥H ⧸ N)
  · exact absurd hsolv (Group.IsPerfect.not_isSolvable _)
  · have hsub : Subsingleton (↥H ⧸ N) := not_nontrivial_iff_subsingleton.mp hnt
    have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : (QuotientGroup.mk x : ↥H ⧸ N) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp this
    have hHL : H ≤ L := (Subgroup.subgroupOf_eq_top.mp hNtop)
    exact le_antisymm hLH hHL

theorem isPerfect_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) [Group.IsPerfect Y] :
    Group.IsPerfect X :=
  Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

omit [Finite G] in
theorem ne_bot_of_quasisimple {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) : L ≠ ⊥ := by
  intro h
  apply Insp9.qs_center_ne_top hq
  have : Subsingleton ↥L := by rw [h]; infer_instance
  rw [eq_top_iff]
  intro x _
  exact Subgroup.mem_center_iff.mpr fun g => Subsingleton.elim _ _

end Perfect

section Perm

variable {G : Type} [Group G]

theorem card_L_of_perm {H L : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (e : ↥H ≃* Equiv.Perm (Fin n))
    (hLH : L ≤ H) (hN : (L.subgroupOf H).Normal) (hq : CFSG.IsQuasisimple ↥L) :
    Nat.card ↥L = n.factorial / 2 := by
  have e' : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  have hLp : Group.IsPerfect ↥L := hq.1
  have hperf : commutator ↥(L.subgroupOf H) = ⊤ := by
    have : Group.IsPerfect ↥(L.subgroupOf H) := isPerfect_of_equiv e' 
    exact Group.isPerfect_def.mp this
  have hnonab : ∃ a b : ↥(L.subgroupOf H), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply Insp9.qs_not_commutative hq
    intro a b
    have h1 := congrArg e' (hcon (e'.symm a) (e'.symm b))
    simpa using h1
  obtain ⟨f⟩ := CFSG.QuasithinUnique.Bridge.TypeList.perm_perfect_normal_equiv hn
    e.symm.toMonoidHom e.symm.surjective (L.subgroupOf H) hN hperf hnonab
  calc Nat.card ↥L = Nat.card ↥(L.subgroupOf H) := Nat.card_congr e'.symm.toEquiv
    _ = Nat.card ↥(alternatingGroup (Fin n)) := Nat.card_congr f.symm.toEquiv
    _ = n.factorial / 2 := card_alternatingGroup1527d n (by omega)

end Perm

section G2

open CFSG.Quasithin.FFC EmptyFaithfulMultiple.FFL

variable {G : Type} [Group G]

theorem card_L_of_g2
    {H L : Subgroup G} (e : ↥H ≃* ↥(CFSG.Open.quasithinG2 (ZMod 2)))
    (hLH : L ≤ H) (hN : (L.subgroupOf H).Normal) (hq : CFSG.IsQuasisimple ↥L) :
    Nat.card ↥L = 6048 := by
  obtain ⟨hs, -, -⟩ := commutator_data_g2 (K := ZMod 2) (Nat.card_zmod 2) e
  obtain ⟨f⟩ := nonempty_commutator_equiv e
  have hD : Nat.card ↥⁅H, H⁆ = 6048 := by
    rw [Nat.card_congr f.toEquiv]
    exact card_commutator_quasithinG2 (F := ZMod 2) (Nat.card_zmod 2)
  have hLp : Group.IsPerfect ↥L := hq.1
  have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLp
  have hLD : L ≤ ⁅H, H⁆ := by
    rw [← hLL]
    exact Subgroup.commutator_mono hLH hLH
  have hDH : ⁅H, H⁆ ≤ H := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hND : (L.subgroupOf ⁅H, H⁆).Normal := by
    refine ⟨fun l hl d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    have hl' : (⟨(l : G), hDH l.2⟩ : ↥H) ∈ L.subgroupOf H := hl
    have := hN.conj_mem _ hl' ⟨(d : G), hDH d.2⟩
    exact this
  rcases hs.eq_bot_or_eq_top_of_normal (L.subgroupOf ⁅H, H⁆) with hb | ht
  · exfalso
    apply ne_bot_of_quasisimple hq
    rw [eq_bot_iff]
    intro l hl
    have : (⟨l, hLD hl⟩ : ↥⁅H, H⁆) ∈ L.subgroupOf ⁅H, H⁆ := hl
    rw [hb, Subgroup.mem_bot] at this
    have h1 : l = 1 := congrArg Subtype.val this
    rw [h1]
    exact Subgroup.one_mem _
  · have hDL : ⁅H, H⁆ ≤ L := Subgroup.subgroupOf_eq_top.mp ht
    have hEq : L = ⁅H, H⁆ := le_antisymm hLD hDL
    rw [hEq]
    exact hD

end G2

section Main

open CFSG.Quasithin.FFC EmptyFaithfulMultiple.FFL

variable {G : Type} [Group G] [Finite G]

theorem inS_of_inspList
    {H L : Subgroup G} (hI : IsInspList ↥H)
    (hL3 : ¬ Nonempty (↥H ≃* ↥(CFSG.Open.StatedSL 3 (ZMod 2)))) (hLH : L ≤ H)
    (hN : (L.subgroupOf H).Normal) (hq : CFSG.IsQuasisimple ↥L)
    (hj : ∃ j : ℕ, Nat.card ↥H = 2 ^ j * Nat.card ↥L) : InS (Nat.card ↥L) := by
  unfold IsInspList at hI
  rcases hI with he | he | he | he | he | hhat | he | he
  · exact absurd he hL3
  · obtain ⟨e⟩ := he
    have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    have hperf : Group.IsPerfect ↥H := isPerfect_of_equiv e
    have hEq : L = H := eq_of_perfect_two_index hLH hperf hN hj
    left
    rw [hEq, Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    norm_num [Nat.factorial]
  · obtain ⟨e⟩ := he
    left
    rw [card_L_of_perm (by norm_num) e hLH hN hq]
    norm_num [Nat.factorial]
  · obtain ⟨e⟩ := he
    have : Group.IsPerfect (alternatingGroup (Fin 7)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    have hperf : Group.IsPerfect ↥H := isPerfect_of_equiv e
    have hEq : L = H := eq_of_perfect_two_index hLH hperf hN hj
    right; right; left
    rw [hEq, Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
    norm_num [Nat.factorial]
  · obtain ⟨e⟩ := he
    right; right; left
    rw [card_L_of_perm (by norm_num) e hLH hN hq]
    norm_num [Nat.factorial]
  · have hperf : Group.IsPerfect ↥H := Group.isPerfect_def.mpr hhat.1.1
    have hEq : L = H := eq_of_perfect_two_index hLH hperf hN hj
    right; left
    rw [hEq, Insp9.card_hatAlt hhat (by norm_num)]
    norm_num [Nat.factorial]
  · obtain ⟨e⟩ := he
    right; right; right
    exact card_L_of_g2 e hLH hN hq
  · obtain ⟨e⟩ := he
    obtain ⟨hs, hnc, -⟩ := commutator_data_g2
      (Ω := (CFSG.Open.quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] CFSG.Open.quasithinZorn (ZMod 2)))
      (H := CFSG.Open.quasithinG2 (ZMod 2)) (K := ZMod 2) (Nat.card_zmod 2) (MulEquiv.refl _)
    have hP0 : Group.IsPerfect ↥⁅CFSG.Open.quasithinG2 (ZMod 2), CFSG.Open.quasithinG2 (ZMod 2)⁆ :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1.1
    have hperf : Group.IsPerfect ↥H := isPerfect_of_equiv e
    have hEq : L = H := eq_of_perfect_two_index hLH hperf hN hj
    right; right; right
    rw [hEq, Nat.card_congr e.toEquiv]
    exact card_commutator_quasithinG2 (F := ZMod 2) (Nat.card_zmod 2)

end Main

end LRed6

end CFSG.Quasithin
