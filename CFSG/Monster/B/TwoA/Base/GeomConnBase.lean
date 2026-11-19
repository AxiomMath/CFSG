
module

public import CFSG.Monster.B.TwoA.Base.GeomObjBase
public import CFSG.Monster.B.TwoA.Base.PetersenData

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module Relation

open scoped IsMulCommutative

attribute [local instance] parAction

def parGraph : SimpleGraph ParGeom where
  Adj x y := x ≠ y ∧ parInc x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, parInc_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def RAdj (R : Set ParGeom) (x y : ParGeom) : Prop := x ∈ R ∧ y ∈ R ∧ parInc x y

abbrev RReach (R : Set ParGeom) : ParGeom → ParGeom → Prop := ReflTransGen (RAdj R)

theorem RAdj.symm {R : Set ParGeom} {x y : ParGeom} (h : RAdj R x y) : RAdj R y x :=
  ⟨h.2.1, h.1, parInc_symm h.2.2⟩

theorem RReach.symm {R : Set ParGeom} {x y : ParGeom} (h : RReach R x y) : RReach R y x := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head hbc.symm ih

theorem RAdj.reach {R : Set ParGeom} {x y : ParGeom} (hx : x ∈ R) (hy : y ∈ R)
    (h : parInc x y) : RReach R x y := ReflTransGen.single ⟨hx, hy, h⟩

theorem reachable_of_reach {R : Set ParGeom} {x₀ x : ParGeom} (hx₀ : x₀ ∈ R)
    (h : RReach R x₀ x) (hx : x ∈ R) : (parGraph.induce R).Reachable ⟨x₀, hx₀⟩ ⟨x, hx⟩ := by
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    refine (ih hbc.1).trans ?_
    by_cases e : b = c
    · subst e
      rfl
    · exact SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.2 ⟨e, hbc.2.2⟩)

theorem connected_of_reach {R : Set ParGeom} {x₀ : ParGeom} (hx₀ : x₀ ∈ R)
    (h : ∀ x ∈ R, RReach R x₀ x) : (parGraph.induce R).Connected :=
  (SimpleGraph.connected_iff_exists_forall_reachable _).2
    ⟨⟨x₀, hx₀⟩, fun x => reachable_of_reach hx₀ (h x.1 x.2) x.2⟩

theorem RReach.smul {R : Set ParGeom} (g : Shat) {x y : ParGeom} (h : RReach R x y) :
    RReach ((g • ·) '' R) (g • x) (g • y) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.tail ⟨⟨_, hbc.1, rfl⟩, ⟨_, hbc.2.1, rfl⟩, (parInc_smul_iff g _ _).2 hbc.2.2⟩

def mkObj (t : ℕ) (A : Subgroup Dfull) (h : IsObj t A) : ParGeom := ⟨(t, A), h⟩

theorem natCard_ofSub_of_finrank
    {E : Subgroup Dfull} [CFSG.IsElementaryAbelian 2 E]
    {U : Submodule (ZMod 2) (Additive E)} {k : ℕ} (hU : finrank (ZMod 2) U = k) :
    Nat.card (ofSub E U) = 2 ^ k :=
  (finrank_subOf_iff (ofSub_le U)).1 (by rw [subOf_ofSub, hU])

theorem RReach.smul_of {R : Set ParGeom} {h : Shat} (hR : ∀ x ∈ R, h • x ∈ R) {u v : ParGeom}
    (huv : RReach R u v) : RReach R (h • u) (h • v) := by
  induction huv with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hR _ hbc.1, hR _ hbc.2.1, (parInc_smul_iff h _ _).2 hbc.2.2⟩

theorem reach_of_sup {R : Set ParGeom} {H₁ H₂ : Subgroup Shat}
    (hR : ∀ h ∈ H₁ ⊔ H₂, ∀ x ∈ R, h • x ∈ R) {r₁ r₂ : ParGeom} (h12 : RReach R r₁ r₂)
    (hfix₁ : ∀ h ∈ H₁, h • r₁ = r₁) (hfix₂ : ∀ h ∈ H₂, h • r₂ = r₂)
    (htr : ∀ x ∈ R, ∃ h ∈ H₁ ⊔ H₂, ∃ y, RReach R r₁ y ∧ h • y = x) :
    ∀ x ∈ R, RReach R r₁ x := by
  have hP : ∀ h ∈ H₁ ⊔ H₂, ∀ y, RReach R r₁ y → RReach R r₁ (h • y) := by
    intro h hh
    rw [Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction'' with
    | mem h hh =>
      intro y hy
      rcases hh with hh | hh
      · have h1 := RReach.smul_of (hR h (Subgroup.mem_sup_left hh)) hy
        rwa [hfix₁ h hh] at h1
      · have h1 := RReach.smul_of (hR h (Subgroup.mem_sup_right hh)) (h12.symm.trans hy)
        rw [hfix₂ h hh] at h1
        exact h12.trans h1
    | inv_mem h hh =>
      intro y hy
      rcases hh with hh | hh
      · have hh' := H₁.inv_mem hh
        have h1 := RReach.smul_of (hR _ (Subgroup.mem_sup_left hh')) hy
        rwa [hfix₁ _ hh'] at h1
      · have hh' := H₂.inv_mem hh
        have h1 := RReach.smul_of (hR _ (Subgroup.mem_sup_right hh')) (h12.symm.trans hy)
        rw [hfix₂ _ hh'] at h1
        exact h12.trans h1
    | one => intro y hy; rwa [one_smul]
    | mul h h' _ _ ih ih' =>
      intro y hy
      rw [mul_smul]
      exact ih _ (ih' y hy)
  intro x hx
  obtain ⟨h, hh, y, hy, rfl⟩ := htr x hx
  exact hP h hh y hy

theorem std_reach {R : Set ParGeom} {s t : ℕ} (hs1 : 1 ≤ s) (hs5 : s ≤ 5) (ht1 : 1 ≤ t)
    (ht5 : t ≤ 5) (hs : stdObj s hs1 hs5 ∈ R) (ht : stdObj t ht1 ht5 ∈ R) :
    RReach R (stdObj s hs1 hs5) (stdObj t ht1 ht5) :=
  RAdj.reach hs ht (stdParFlag_isParFlag.1 _ (stdObj_mem s hs1 hs5) _ (stdObj_mem t ht1 ht5))

theorem smul_stdObj_of_mem {i : ℕ} (h1 : 1 ≤ i) (h5 : i ≤ 5) {h : Shat}
    (hh : (h : Dfull) ∈ Kchain i) : h • stdObj i h1 h5 = stdObj i h1 h5 :=
  obj_ext rfl (conjSub_eq_self_iff.2 hh)

theorem subgroupOf_sup_eq {A B C : Subgroup Dfull} (hA : A ≤ Shat) (hB : B ≤ Shat)
    (h : C = A ⊔ B) : C.subgroupOf Shat = A.subgroupOf Shat ⊔ B.subgroupOf Shat := by
  rw [h, Subgroup.subgroupOf_sup hA hB]

theorem petersen_diam : ∀ d : Fin 10, d = 0 ∨
    (∃ c, (ev4 c 0 = 0 ∧ ev4 c 1 = d) ∨ (ev4 c 0 = d ∧ ev4 c 1 = 0)) ∨
    ∃ c c' : Fin 15, ∃ d' : Fin 10, ((ev4 c 0 = 0 ∧ ev4 c 1 = d') ∨ (ev4 c 0 = d' ∧ ev4 c 1 = 0)) ∧
      ((ev4 c' 0 = d' ∧ ev4 c' 1 = d) ∨ (ev4 c' 0 = d ∧ ev4 c' 1 = d')) := by
  decide

theorem card_filter_notMem_ge {J : Set ℕ} [DecidablePred (· ∈ J)] (hJ : J ⊆ Set.Icc 1 5)
    (hc : J.ncard ≤ 3) : 2 ≤ ((Finset.Icc 1 5).filter (· ∉ J)).card := by
  have hJf : J = ↑((Finset.Icc 1 5).filter (· ∈ J)) := by
    ext t
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun ht => ⟨hJ ht, ht⟩, fun ht => ht.2⟩
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 5) (· ∈ J)
  rw [hJf, Set.ncard_coe_finset] at hc
  simp only [Nat.card_Icc, Nat.add_one_sub_one] at h1
  omega

end CFSG.Monster.B.TwoA
