module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Ind

public section

namespace CFSG.Quasithin.E6.Alt

open Subgroup CFSG.Quasithin.E6.Bar
open scoped commutatorElement

variable {Y : Type} [Group Y] {L R A : Subgroup Y} {G : Type} [Group G] {D : Subgroup G}

@[expose] noncomputable def rankHom (L : Subgroup Y) (e : Qbar L ≃* G) (A : Subgroup Y)
    (hAN : A ≤ normalizer (L : Set Y)) : ↥A →* MulAut G :=
  (indHom L e).comp (Subgroup.inclusion hAN)

theorem ker_rankHom (e : Qbar L ≃* G) (hperf : Group.IsPerfect ↥L)
    (hAN : A ≤ normalizer (L : Set Y)) :
    (rankHom L e A hAN).ker = (A ⊓ centralizer (L : Set Y)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  change indHom L e ⟨(a : Y), hAN a.2⟩ = 1 ↔ _
  rw [indHom_eq_one_iff e hperf]
  constructor
  · intro h
    exact ⟨a.2, fun x hx => (h ⟨x, hx⟩).symm⟩
  · rintro ⟨-, h⟩ x
    exact (h x x.2).symm

theorem relIndex_eq_card_range (e : Qbar L ≃* G) (hperf : Group.IsPerfect ↥L)
    (hAN : A ≤ normalizer (L : Set Y)) :
    (A ⊓ centralizer (L : Set Y)).relIndex A = Nat.card (rankHom L e A hAN).range := by
  rw [Subgroup.relIndex, ← ker_rankHom e hperf hAN, Subgroup.index_ker]

theorem eq_top_of_perfect_of_center_mul {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    (M : Subgroup X) (h : ∀ x : X, ∃ m ∈ M, ∃ z ∈ Subgroup.center X, x = m * z) : M = ⊤ := by
  have hcomm : ∀ (g h' z : X), z ∈ Subgroup.center X → ⁅g * z, h'⁆ = ⁅g, h'⁆ := by
    intro g h' z hz
    have hzh : z * h' * z⁻¹ = h' := by
      rw [← Subgroup.mem_center_iff.1 hz h']
      group
    calc ⁅g * z, h'⁆ = g * (z * h' * z⁻¹) * g⁻¹ * h'⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅g, h'⁆ := by rw [hzh, commutatorElement_def]
  have hcomm' : ∀ (g h' z : X), z ∈ Subgroup.center X → ⁅g, h' * z⁆ = ⁅g, h'⁆ := by
    intro g h' z hz
    rw [← inv_inj, commutatorElement_inv, commutatorElement_inv]
    exact hcomm h' g z hz
  rw [eq_top_iff, ← Group.isPerfect_def.1 hperf, _root_.commutator, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := h g₁
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := h g₂
  rw [hcomm _ _ _ hz₁, hcomm' _ _ _ hz₂]
  rw [commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

theorem card_le_of_encard_le {α : Type*} (S : Set α) {n : ℕ} (h : S.encard ≤ n) :
    Nat.card S ≤ n := by
  rw [Nat.card_coe_set_eq, Set.ncard_def]
  exact ENat.toNat_le_of_le_natCast h

section Main

variable (hM : AltModel G D) (e : Qbar L ≃* G) (hperf : Group.IsPerfect ↥L)
  (hD : (imgBar L R).map e.toMonoidHom = D) (hRN : R ≤ normalizer (L : Set Y)) (hAR : A ≤ R)
  (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hcomm : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a)

include hD hRN hAR hA2 hcomm in
theorem range_subset :
    ((rankHom L e A (hAR.trans hRN)).range : Set (MulAut G)) ⊆ insert 1 (InvSet D) := by
  rintro _ ⟨a, rfl⟩
  by_cases h1 : rankHom L e A (hAR.trans hRN) a = 1
  · exact Or.inl h1
  · refine Or.inr ⟨h1, ?_, fun d hd => ?_⟩
    · rw [← map_mul]
      have : a * a = 1 := Subtype.ext (by simpa [pow_two] using hA2 a a.2)
      rw [this, map_one]
    · exact indHom_commute e hD ⟨(a : Y), hAR.trans hRN a.2⟩
        (fun p hp => hcomm a a.2 p hp) d hd

theorem encard_insert_le (hM : AltModel G D) : (insert (1 : MulAut G) (InvSet D)).encard ≤ 4 := by
  calc (insert (1 : MulAut G) (InvSet D)).encard ≤ (InvSet D).encard + 1 :=
        Set.encard_insert_le _ _
    _ ≤ 3 + 1 := by gcongr; exact hM.encard_le
    _ = 4 := by norm_num

include hM hperf hD hRN hAR hA2 hcomm in
theorem relIndex_le_four :
    (A ⊓ centralizer (L : Set Y)).relIndex A ≤ 4 := by
  rw [relIndex_eq_card_range e hperf (hAR.trans hRN)]
  have h3 : ((rankHom L e A (hAR.trans hRN)).range : Set (MulAut G)).encard ≤ 4 :=
    (Set.encard_le_encard (range_subset e hD hRN hAR hA2 hcomm)).trans (encard_insert_le hM)
  exact card_le_of_encard_le _ h3

variable [Finite Y]

include hM hperf hD hRN hAR hA2 hcomm in
theorem le_iSup_of_relIndex_eq_four (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (h4 : (A ⊓ centralizer (L : Set Y)).relIndex A = 4) :
    L ≤ ⨆ (a : Y) (_ : a ∈ A ∧ a ∉ centralizer (L : Set Y)),
      L ⊓ centralizer ({a} : Set Y) := by
  set M : Subgroup Y := ⨆ (a : Y) (_ : a ∈ A ∧ a ∉ centralizer (L : Set Y)),
    L ⊓ centralizer ({a} : Set Y) with hMdef
  have hAN : A ≤ normalizer (L : Set Y) := hAR.trans hRN
  have hsub := range_subset e hD hRN hAR hA2 hcomm
  have hcard : Nat.card (rankHom L e A hAN).range = 4 := by
    rw [← relIndex_eq_card_range e hperf hAN]
    exact h4
  have henc := encard_insert_le hM
  have hfin : (insert (1 : MulAut G) (InvSet D)).Finite := Set.finite_of_encard_le_coe henc
  have hrfin : ((rankHom L e A hAN).range : Set (MulAut G)).Finite := hfin.subset hsub
  have hrenc : ((rankHom L e A hAN).range : Set (MulAut G)).encard = 4 := by
    rw [← hrfin.cast_ncard_eq, ← Nat.card_coe_set_eq]
    exact_mod_cast hcard
  have heq : ((rankHom L e A hAN).range : Set (MulAut G)) = insert 1 (InvSet D) :=
    hrfin.eq_of_subset_of_encard_le hsub (henc.trans hrenc.ge)
  have hex : ∀ β ∈ InvSet D, ∃ a : Y, a ∈ A ∧ a ∉ centralizer (L : Set Y) ∧
      ∃ h : a ∈ normalizer (L : Set Y), indHom L e ⟨a, h⟩ = β := by
    intro β hβ
    have hmem : β ∈ ((rankHom L e A hAN).range : Set (MulAut G)) := heq ▸ Or.inr hβ
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, a.2, ?_, hAN a.2, ha⟩
    intro hc
    apply hβ.1
    rw [← ha]
    refine (indHom_eq_one_iff e hperf _).2 fun x => ?_
    exact (Subgroup.mem_centralizer_iff.1 hc x x.2).symm
  let ML : Subgroup ↥L := M.subgroupOf L
  have hq : ∀ q : Qbar L, ∃ m ∈ ML, (QuotientGroup.mk m : Qbar L) = q := by
    intro q
    have hmem : e q ∈ (⨆ β ∈ InvSet D, fixedSub β : Subgroup G) := by
      rw [hM.gen]
      exact Subgroup.mem_top _
    have hle : (⨆ β ∈ InvSet D, fixedSub β : Subgroup G) ≤
        (ML.map (QuotientGroup.mk' (Subgroup.center ↥L))).map e.toMonoidHom := by
      refine iSup₂_le fun β hβ g hg => ?_
      obtain ⟨a, haA, haC, haN, hia⟩ := hex β hβ
      have hg' : indHom L e ⟨a, haN⟩ g = g := by
        rw [hia]
        exact hg
      obtain ⟨q', rfl⟩ := e.surjective g
      have hq' : barHom L ⟨a, haN⟩ q' = q' := by
        have := indHom_apply e ⟨a, haN⟩ q'
        rw [hg'] at this
        exact e.injective this.symm
      obtain ⟨x, hx1, hx2⟩ := exists_fixed_lift hodd ⟨a, haN⟩
        (by simpa using hA2 a haA) q' hq'
      refine ⟨QuotientGroup.mk' _ x, ⟨x, ?_, rfl⟩, ?_⟩
      · show (x : Y) ∈ M
        have hxc : (x : Y) ∈ centralizer ({a} : Set Y) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := congrArg Subtype.val hx1
          change a * x * a⁻¹ = x at this
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this.symm
        exact (le_iSup₂ (f := fun (a : Y) (_ : a ∈ A ∧ a ∉ centralizer (L : Set Y)) =>
          L ⊓ centralizer ({a} : Set Y)) a ⟨haA, haC⟩) ⟨x.2, hxc⟩
      · exact congrArg e hx2
    obtain ⟨_, ⟨m, hm, rfl⟩, hmq⟩ := hle hmem
    exact ⟨m, hm, e.injective hmq⟩
  have hML : ML = ⊤ := by
    refine eq_top_of_perfect_of_center_mul hperf ML fun x => ?_
    obtain ⟨m, hm, hmx⟩ := hq (QuotientGroup.mk x)
    exact ⟨m, hm, m⁻¹ * x, QuotientGroup.eq.1 hmx, by simp⟩
  intro x hx
  have : (⟨x, hx⟩ : ↥L) ∈ ML := by rw [hML]; exact Subgroup.mem_top _
  exact this

end Main

end CFSG.Quasithin.E6.Alt
