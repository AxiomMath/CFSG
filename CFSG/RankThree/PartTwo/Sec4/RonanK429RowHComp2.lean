module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    IsQuasisimple Q := by
  obtain ⟨hp, hs⟩ := h
  haveI : Group.IsPerfect Q := ⟨hp⟩
  refine ⟨inferInstance, hs, ?_⟩
  by_contra hc
  push_neg at hc
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hs.toNontrivial
  have hnc := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  exact hnc ⟨⟨hc⟩⟩

section Model

variable {S G' : Type} [Group S] [Group G']

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem noCfgS429_of_subgroupModel [Finite S] {P : Subgroup G'} (e : S ≃* P)
    (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (h : ∀ x ∈ P, orderOf x = 3 → Good429 (Subgroup.centralizer ({x} : Set G') ⊓ P)) :
    NoCfgS429 S := by
  refine noCfgS429_of_inner hZ hout fun s hs => ?_
  let f : S →* G' := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hr : f.range = P := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  refine Good429.of_map f hf ?_
  rw [map_centralizer_singleton f hf s, hr]
  exact h (f s) (e s).2 (by rw [orderOf_injective f hf s]; exact hs)

end Model

section Free

variable {S : Type} [Group S]

theorem normal_subgroupOf_of_forall_conj' {R C : Subgroup S}
    (h : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) : (R.subgroupOf C).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h g g.2 x hx⟩

end Free

section Criteria


variable {S : Type} [Group S] [Finite S]

theorem good429_of_selfCentralizing' {C R : Subgroup S} (hRC : R ≤ C)
    (hRn : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR3 : IsPGroup 3 R)
    (hcent : Subgroup.centralizer (R : Set S) ⊓ C ≤ R) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R' : Subgroup C := R.subgroupOf C
  have hR'n : R'.Normal := normal_subgroupOf_of_forall_conj' hRn
  have hO : CFSG.pCore 2 C = ⊥ := by
    set O := CFSG.pCore 2 C
    have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
    have hR'3 : IsPGroup 3 R' := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
    have hdisj : O ⊓ R' = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime ?_
      obtain ⟨a, ha⟩ := hO2.exists_card_eq
      obtain ⟨b, hb⟩ := hR'3.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow a b (by norm_num)
    haveI := hR'n
    have hcomm : ⁅O, R'⁆ = ⊥ := by
      rw [eq_bot_iff, ← hdisj]
      exact le_inf (Subgroup.commutator_le_left O R') (Subgroup.commutator_le_right O R')
    have hOR : O ≤ R' := by
      intro x hx
      have hxc : (x : S) ∈ Subgroup.centralizer (R : Set S) ⊓ C := by
        refine ⟨?_, x.2⟩
        show (x : S) ∈ Subgroup.centralizer (R : Set S)
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
        rw [Subgroup.mem_centralizer_iff] at this
        have h' := this ⟨r, hRC hr⟩ hr
        exact congrArg Subtype.val h'
      exact hcent hxc
    rw [eq_bot_iff, ← hdisj]
    exact le_inf le_rfl hOR
  obtain ⟨hcomp, -⟩ := isComponent_subgroupOf_of_isType429 hKC hKs hT hO
  rcases CFSG.LocalCores.component_normal_subgroup hcomp hR'n with hle | hcomm
  · refine not_isPGroup_three_of_isType429 hT (hR3.to_le fun k hk => ?_)
    have := hle (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    exact this
  · refine not_isPGroup_three_of_isType429 hT (hR3.to_le fun k hk => hcent ⟨?_, hKC hk⟩)
    show k ∈ Subgroup.centralizer (R : Set S)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    rw [Subgroup.mem_centralizer_iff] at this
    have h' := this ⟨r, hRC hr⟩ hr
    exact congrArg Subtype.val h'

theorem good429_of_simpleNormal' {C L : Subgroup S} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) [hLs : IsSimpleGroup L]
    (hLna : ∃ a b : L, a * b ≠ b * a) {B : ℕ} (hB : Nat.card L < B ^ 3)
    (hLt : Nat.card L ∉ typeOrders (Nat.card L) B)
    (hcent : ∀ g ∈ C, (∀ l ∈ L, l * g = g * l) → g ^ 3 = 1) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L' : Subgroup C := L.subgroupOf C
  have hL'n : L'.Normal := normal_subgroupOf_of_forall_conj' hLn
  haveI := hL'n
  have eL : L' ≃* L := Subgroup.subgroupOfEquivOfLe hLC
  haveI : IsSimpleGroup L' := eL.isSimpleGroup
  have hO : CFSG.pCore 2 C = ⊥ := by
    set O := CFSG.pCore 2 C
    have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
    have hOL : O ⊓ L' = ⊥ := by
      have hN : ((O ⊓ L').subgroupOf L').Normal := by
        haveI : (O ⊓ L').Normal := inferInstance
        exact Subgroup.normal_subgroupOf
      rcases hN.eq_bot_or_eq_top with h | h
      · rw [Subgroup.subgroupOf_eq_bot] at h
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hx hx.2)
      · exfalso
        rw [Subgroup.subgroupOf_eq_top] at h
        have h2 : IsPGroup 2 L' := (hO2.to_le (le_trans h inf_le_left))
        have h2' : IsPGroup 2 L := h2.of_equiv eL
        obtain ⟨a, b, hab⟩ := hLna
        haveI : Nontrivial L := ⟨⟨a * b, b * a, hab⟩⟩
        haveI := h2'.center_nontrivial
        have hc : Subgroup.center L = ⊤ := by
          rcases (inferInstance : (Subgroup.center L).Normal).eq_bot_or_eq_top with hc | hc
          · exfalso
            have hnt : Nontrivial (Subgroup.center L) := inferInstance
            rw [hc] at hnt
            exact not_nontrivial _ hnt
          · exact hc
        have ha : a ∈ Subgroup.center L := hc ▸ Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp ha b).symm
    have hcomm : ⁅O, L'⁆ = ⊥ := by
      rw [eq_bot_iff, ← hOL]
      exact le_inf (Subgroup.commutator_le_left O L') (Subgroup.commutator_le_right O L')
    rw [eq_bot_iff]
    intro x hx
    have hx3 : (x : S) ^ 3 = 1 := by
      refine hcent x x.2 ?_
      intro l hl
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
      rw [Subgroup.mem_centralizer_iff] at this
      exact congrArg Subtype.val (this ⟨l, hLC hl⟩ hl)
    obtain ⟨n, hn⟩ := hO2 ⟨x, hx⟩
    have hx3' : (⟨x, hx⟩ : O) ^ 3 = 1 := Subtype.ext (Subtype.ext hx3)
    have hord : orderOf (⟨x, hx⟩ : O) ∣ Nat.gcd (2 ^ n) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hx3')
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n (by norm_num))] at hord
    have h1 : (⟨x, hx⟩ : O) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  obtain ⟨hcomp, hK2⟩ := isComponent_subgroupOf_of_isType429 hKC hKs hT hO
  haveI := nontrivial_of_isType429 hT
  rcases CFSG.LocalCores.component_normal_subgroup hcomp hL'n with hle | hcomm
  · have hKL : K ≤ L := fun k hk => hle (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    have hsL : (K.subgroupOf L).IsSubnormal := isSubnormal_subgroupOf_of_le hLC hKL hKs
    rcases hsL.eq_bot_or_top_of_isSimpleGroup hLs with hbot | htop
    · rw [Subgroup.subgroupOf_eq_bot] at hbot
      have : K = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hbot hk (hKL hk))
      subst this
      have : Subsingleton (↥(⊥ : Subgroup S) ⧸ CFSG.pCore 2 ↥(⊥ : Subgroup S)) := inferInstance
      exact not_subsingleton _ this
    · have hKeq : K = L := le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp htop)
      subst hKeq
      have eQ : K ⧸ CFSG.pCore 2 K ≃* K :=
        (QuotientGroup.quotientMulEquivOfEq hK2).trans QuotientGroup.quotientBot
      haveI : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := inferInstance
      have hmem := card_mem_typeOrders (M := Nat.card K) (B := B) Nat.card_pos hB hT
        (by rw [Nat.card_congr eQ.toEquiv])
      rw [Nat.card_congr eQ.toEquiv] at hmem
      exact hLt hmem
  · apply not_isPGroup_three_of_isType429 hT
    refine isPGroup_three_of_pow_three fun k hk => hcent k (hKC hk) ?_
    intro l hl
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)
    rw [Subgroup.mem_centralizer_iff] at this
    exact congrArg Subtype.val (this ⟨l, hLC hl⟩ hl)

end Criteria

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
