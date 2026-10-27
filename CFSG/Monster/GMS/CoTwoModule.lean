module

public import CFSG.Monster.GMS.CoTwoRep
import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.GMS.Leech.Linear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act

namespace CoTwoModule

theorem co1Act_mul_apply (c d : Co1) (x : Fin 24 → ZMod 2) :
    co1Act (c * d) x = co1Act c (co1Act d x) := by
  rw [map_mul, Module.End.mul_apply]

theorem co1Act_inv_apply (c : Co1) (x : Fin 24 → ZMod 2) : co1Act c⁻¹ (co1Act c x) = x := by
  rw [← co1Act_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply]

theorem co1Act_apply_inv (c : Co1) (x : Fin 24 → ZMod 2) : co1Act c (co1Act c⁻¹ x) = x := by
  rw [← co1Act_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply]

theorem co1Act_injective (c : Co1) : Function.Injective (co1Act c) := fun x y h => by
  have := congrArg (co1Act c⁻¹) h
  rwa [co1Act_inv_apply, co1Act_inv_apply] at this

theorem mem_co1Stab {a : Fin 24 → ZMod 2} {A : Co1} : A ∈ co1Stab a ↔ co1Act A a = a := Iff.rfl

theorem conj_mem_co1Stab {a : Fin 24 → ZMod 2} {A : Co1} (hA : A ∈ co1Stab a) (c : Co1) :
    c * A * c⁻¹ ∈ co1Stab (co1Act c a) := by
  rw [mem_co1Stab, co1Act_mul_apply, co1Act_mul_apply, co1Act_inv_apply, mem_co1Stab.1 hA]

theorem co1Act_conj_add (c A : Co1) (x : Fin 24 → ZMod 2) :
    co1Act (c * A * c⁻¹) (co1Act c x) + co1Act c x = co1Act c (co1Act A x + x) := by
  rw [co1Act_mul_apply, co1Act_mul_apply, co1Act_inv_apply, map_add]

theorem bil₀_smul_left (a : ZMod 2) (x y : Fin 24 → ZMod 2) : bil₀ (a • x) y = a * bil₀ x y := by
  unfold bil₀
  rw [smul_dotProduct, smul_eq_mul]

theorem bil₀_zero_left (y : Fin 24 → ZMod 2) : bil₀ 0 y = 0 := by
  unfold bil₀
  rw [zero_dotProduct]

def perpSpace (v : Fin 24 → ZMod 2) : Submodule (ZMod 2) (Fin 24 → ZMod 2) where
  carrier := {y | bil₀ y v = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Leech.bil₀_add_left, ha, hb, add_zero]
  zero_mem' := bil₀_zero_left v
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [bil₀_smul_left, hx, mul_zero]

theorem mem_perpSpace {v y : Fin 24 → ZMod 2} : y ∈ perpSpace v ↔ bil₀ y v = 0 := Iff.rfl

theorem bil₀_eq_one_of_pair
    {u v : Fin 24 → ZMod 2} (hu : u ∈ co1Orbit 0) (hv : v ∈ co1Orbit 0)
    (huv : u + v ∈ co1Orbit 1) : bil₀ u v = 1 := by
  have h := q₀_add u v
  rw [Leech.q₀_eq_one_of_mem_co1Orbit_one huv, Leech.q₀_eq_zero_of_mem_co1Orbit_zero hu,
    Leech.q₀_eq_zero_of_mem_co1Orbit_zero hv] at h
  linear_combination -h

theorem v₂_mem_co1Orbit : v₂ ∈ co1Orbit 0 :=
  ⟨1, by simp only [map_one, Module.End.one_apply]; rfl⟩

theorem exists_co1Act_eq_v₂ {u : Fin 24 → ZMod 2} (hu : u ∈ co1Orbit 0) :
    ∃ c : Co1, co1Act c v₂ = u := hu

variable {c₁ c₂ : Co1} {y₀ : Fin 24 → ZMod 2}

theorem pair_of_conj (h : McLRepFacts c₁ c₂ y₀) (c : Co1) :
    co1Act c v₂ ∈ co1Orbit 0 ∧ co1Act c y₀ ∈ co1Orbit 0 ∧
      co1Act c v₂ + co1Act c y₀ ∈ co1Orbit 1 := by
  refine ⟨Leech.co1Act_mem_co1Orbit v₂_mem_co1Orbit c, Leech.co1Act_mem_co1Orbit h.mem_y₀ c, ?_⟩
  have := Leech.co1Act_mem_co1Orbit h.sum_mem c
  rwa [map_add] at this

theorem exists_conj_pair
    (h : McLRepFacts c₁ c₂ y₀) {u v : Fin 24 → ZMod 2}
    (hu : u ∈ co1Orbit 0) (hv : v ∈ co1Orbit 0) (huv : u + v ∈ co1Orbit 1) :
    ∃ c : Co1, co1Act c v₂ = u ∧ co1Act c y₀ = v :=
  co1PairFacts.2.2.2.1 v₂ y₀ u v v₂_mem_co1Orbit h.mem_y₀ h.sum_mem hu hv huv

theorem irred_conj
    (h : McLRepFacts c₁ c₂ y₀) (c : Co1)
    (Y : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hY : ∀ y ∈ Y, bil₀ y (co1Act c v₂) = 0 ∧ bil₀ y (co1Act c y₀) = 0)
    (hinv : ∀ A ∈ co1Stab (co1Act c v₂) ⊓ co1Stab (co1Act c y₀), ∀ x ∈ Y, co1Act A x ∈ Y) :
    Y = ⊥ ∨ ∀ y : Fin 24 → ZMod 2, bil₀ y (co1Act c v₂) = 0 → bil₀ y (co1Act c y₀) = 0 →
      y ∈ Y := by
  have key : ∀ c' : Co1, co1Act c' v₂ = v₂ → co1Act c' y₀ = y₀ →
      ∀ y, y ∈ Y.comap (co1Act c) → co1Act c' y ∈ Y.comap (co1Act c) := by
    intro c' h₁ h₂ y hy
    have hA : c * c' * c⁻¹ ∈ co1Stab (co1Act c v₂) ⊓ co1Stab (co1Act c y₀) :=
      ⟨conj_mem_co1Stab h₁ c, conj_mem_co1Stab h₂ c⟩
    have := hinv _ hA _ (Submodule.mem_comap.1 hy)
    rw [co1Act_mul_apply, co1Act_mul_apply, co1Act_inv_apply] at this
    exact Submodule.mem_comap.2 this
  have hY₀ : ∀ y ∈ Y.comap (co1Act c), bil₀ y v₂ = 0 ∧ bil₀ y y₀ = 0 := by
    intro y hy
    have := hY _ (Submodule.mem_comap.1 hy)
    rwa [Leech.bil₀_co1Act, Leech.bil₀_co1Act] at this
  rcases h.irred (Y.comap (co1Act c)) hY₀ (key c₁ h.fix_c₁.1 h.fix_c₁.2)
      (key c₂ h.fix_c₂.1 h.fix_c₂.2) with h0 | h1
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : co1Act c⁻¹ x ∈ Y.comap (co1Act c) := by
      rw [Submodule.mem_comap, co1Act_apply_inv]
      exact hx
    rw [h0, Submodule.mem_bot] at hx'
    calc x = co1Act c (co1Act c⁻¹ x) := (co1Act_apply_inv c x).symm
      _ = 0 := by rw [hx', map_zero]
  · right
    intro y hy₁ hy₂
    have hy : co1Act c⁻¹ y ∈ Y.comap (co1Act c) := by
      refine h1 _ ?_ ?_
      · rw [← Leech.bil₀_co1Act c, co1Act_apply_inv]
        exact hy₁
      · rw [← Leech.bil₀_co1Act c, co1Act_apply_inv]
        exact hy₂
    rw [Submodule.mem_comap, co1Act_apply_inv] at hy
    exact hy

theorem nondeg_mcl_of_rep
    (h : McLRepFacts c₁ c₂ y₀) :
    ∀ u ∈ co1Orbit 0, ∀ v ∈ co1Orbit 0, u + v ∈ co1Orbit 1 →
      ∃ y₁ y₂ : Fin 24 → ZMod 2, bil₀ y₁ u = 0 ∧ bil₀ y₁ v = 0 ∧ bil₀ y₂ u = 0 ∧
        bil₀ y₂ v = 0 ∧ bil₀ y₁ y₂ = 1 := by
  intro u hu v hv huv
  obtain ⟨c, rfl, rfl⟩ := exists_conj_pair h hu hv huv
  obtain ⟨y₁, y₂, h₁, h₂, h₃, h₄, h₅⟩ := h.nondeg
  refine ⟨co1Act c y₁, co1Act c y₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Leech.bil₀_co1Act]
    exact h₁
  · rw [Leech.bil₀_co1Act]
    exact h₂
  · rw [Leech.bil₀_co1Act]
    exact h₃
  · rw [Leech.bil₀_co1Act]
    exact h₄
  · rw [Leech.bil₀_co1Act]
    exact h₅

theorem comm_span_mcl_of_rep
    (h : McLRepFacts c₁ c₂ y₀) :
    ∀ u ∈ co1Orbit 0, ∀ v ∈ co1Orbit 0, u + v ∈ co1Orbit 1 →
    ∀ X : Submodule (ZMod 2) (Fin 24 → ZMod 2),
    (∀ x ∈ X, bil₀ x u = 0 ∧ bil₀ x v = 0) →
    (∀ A ∈ co1Stab u ⊓ co1Stab v, ∀ x ∈ X, co1Act A x ∈ X) →
    (∀ A ∈ co1Stab u ⊓ co1Stab v, ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → bil₀ y v = 0 →
      co1Act A y + y ∈ X) →
    ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → bil₀ y v = 0 → y ∈ X := by
  intro u hu v hv huv X hX hinv hcomm
  obtain ⟨c, rfl, rfl⟩ := exists_conj_pair h hu hv huv
  rcases irred_conj h c X hX hinv with h0 | h1
  · exfalso
    obtain ⟨y, hy₁, hy₂, hy⟩ := h.nontriv
    have key : ∀ c' : Co1, co1Act c' v₂ = v₂ → co1Act c' y₀ = y₀ → co1Act c' y ≠ y → False := by
      intro c' h₁ h₂ hne
      have hA : c * c' * c⁻¹ ∈ co1Stab (co1Act c v₂) ⊓ co1Stab (co1Act c y₀) :=
        ⟨conj_mem_co1Stab h₁ c, conj_mem_co1Stab h₂ c⟩
      have hy₁' : bil₀ (co1Act c y) (co1Act c v₂) = 0 := by
        rw [Leech.bil₀_co1Act]
        exact hy₁
      have hy₂' : bil₀ (co1Act c y) (co1Act c y₀) = 0 := by
        rw [Leech.bil₀_co1Act]
        exact hy₂
      have hmem := hcomm _ hA (co1Act c y) hy₁' hy₂'
      rw [co1Act_conj_add, h0, Submodule.mem_bot] at hmem
      have h3 : co1Act c' y + y = 0 := co1Act_injective c (hmem.trans (map_zero (co1Act c)).symm)
      exact hne ((eq_neg_of_add_eq_zero_left h3).trans (Leech.neg_eq_self y))
    rcases hy with hy | hy
    · exact key c₁ h.fix_c₁.1 h.fix_c₁.2 hy
    · exact key c₂ h.fix_c₂.1 h.fix_c₂.2 hy
  · exact h1

theorem irred_co2_of_mcl
    {u v : Fin 24 → ZMod 2} (huv : bil₀ u v = 1)
    (hirr : ∀ Y : Submodule (ZMod 2) (Fin 24 → ZMod 2),
      (∀ y ∈ Y, bil₀ y u = 0 ∧ bil₀ y v = 0) →
      (∀ A ∈ co1Stab u ⊓ co1Stab v, ∀ x ∈ Y, co1Act A x ∈ Y) →
      Y = ⊥ ∨ ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → bil₀ y v = 0 → y ∈ Y)
    (Y : Submodule (ZMod 2) (Fin 24 → ZMod 2)) (huY : u ∈ Y)
    (hperp : ∀ y ∈ Y, bil₀ y u = 0) (hinv : ∀ A ∈ co1Stab u, ∀ y ∈ Y, co1Act A y ∈ Y) :
    Y = Submodule.span (ZMod 2) {u} ∨ ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → y ∈ Y := by
  have huu : bil₀ u u = 0 := bil₀_self u
  have hπ : ∀ y, bil₀ y u = 0 →
      bil₀ (y + bil₀ y v • u) u = 0 ∧ bil₀ (y + bil₀ y v • u) v = 0 := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Leech.bil₀_add_left, bil₀_smul_left, hy, huu, mul_zero, add_zero]
    · rw [Leech.bil₀_add_left, bil₀_smul_left, huv, mul_one]
      exact CharTwo.add_self_eq_zero _
  have hY₁ : ∀ y ∈ Y ⊓ perpSpace v, bil₀ y u = 0 ∧ bil₀ y v = 0 := fun y hy =>
    ⟨hperp y hy.1, mem_perpSpace.1 hy.2⟩
  have hinv₁ : ∀ A ∈ co1Stab u ⊓ co1Stab v, ∀ x ∈ Y ⊓ perpSpace v,
      co1Act A x ∈ Y ⊓ perpSpace v := by
    intro A hA x hx
    refine ⟨hinv A hA.1 x hx.1, mem_perpSpace.2 ?_⟩
    have h1 : bil₀ (co1Act A x) (co1Act A v) = bil₀ x v := Leech.bil₀_co1Act A x v
    rw [mem_co1Stab.1 hA.2] at h1
    exact h1.trans (mem_perpSpace.1 hx.2)
  rcases hirr (Y ⊓ perpSpace v) hY₁ hinv₁ with h0 | h1
  · left
    refine le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem u Y).2 huY)
    have hπy : y + bil₀ y v • u ∈ Y ⊓ perpSpace v :=
      ⟨Y.add_mem hy (Y.smul_mem _ huY), mem_perpSpace.2 (hπ y (hperp y hy)).2⟩
    rw [h0, Submodule.mem_bot] at hπy
    rw [Submodule.mem_span_singleton]
    exact ⟨bil₀ y v, ((eq_neg_of_add_eq_zero_left hπy).trans (Leech.neg_eq_self _)).symm⟩
  · right
    intro z hz
    have h2 := h1 (z + bil₀ z v • u) (hπ z hz).1 (hπ z hz).2
    have h3 : (z + bil₀ z v • u) + bil₀ z v • u ∈ Y := Y.add_mem h2.1 (Y.smul_mem _ huY)
    rwa [add_assoc, vec_add_self, add_zero] at h3

theorem irred_co2_of_rep
    (h : McLRepFacts c₁ c₂ y₀) :
    ∀ u ∈ co1Orbit 0, ∀ Y : Submodule (ZMod 2) (Fin 24 → ZMod 2), u ∈ Y →
    (∀ y ∈ Y, bil₀ y u = 0) → (∀ A ∈ co1Stab u, ∀ y ∈ Y, co1Act A y ∈ Y) →
    Y = Submodule.span (ZMod 2) {u} ∨ ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → y ∈ Y := by
  intro u hu Y huY hperp hinv
  obtain ⟨c, rfl⟩ := exists_co1Act_eq_v₂ hu
  obtain ⟨hu', hv', huv'⟩ := pair_of_conj h c
  exact irred_co2_of_mcl (bil₀_eq_one_of_pair hu' hv' huv') (irred_conj h c) Y huY hperp hinv

theorem nondeg_co2_of_rep
    (h : McLRepFacts c₁ c₂ y₀) :
    ∀ u ∈ co1Orbit 0, ∃ y₁ y₂ : Fin 24 → ZMod 2,
      bil₀ y₁ u = 0 ∧ bil₀ y₂ u = 0 ∧ bil₀ y₁ y₂ = 1 := by
  intro u hu
  obtain ⟨c, rfl⟩ := exists_co1Act_eq_v₂ hu
  obtain ⟨hu', hv', huv'⟩ := pair_of_conj h c
  obtain ⟨y₁, y₂, h₁, -, h₃, -, h₅⟩ := nondeg_mcl_of_rep h _ hu' _ hv' huv'
  exact ⟨y₁, y₂, h₁, h₃, h₅⟩

theorem exists_witness_one :
    ∃ A ∈ co1Stab v₂, ∃ x : Fin 24 → ZMod 2, bil₀ x v₂ = 0 ∧ co1Act A x + x = v₂ := by
  obtain ⟨y, hy, hvy, -⟩ := Pairs.pair_one v₂ (by
    rw [← Pairs.co1Orbit_zero]
    exact v₂_mem_co1Orbit)
  have hy₀ : y ∈ co1Orbit 0 := by
    rw [Pairs.co1Orbit_zero]
    exact hy
  have hvy₀ : v₂ + y ∈ co1Orbit 0 := by
    rw [Pairs.co1Orbit_zero]
    exact hvy
  have hcls : y ∈ Pairs.cls 3 := ⟨hy, hvy⟩
  have hcls' : v₂ + y ∈ Pairs.cls 3 := ⟨hvy, by
    rw [← add_assoc, vec_add_self, zero_add]
    exact hy⟩
  obtain ⟨g, hg₁, hg₂⟩ := Pairs.cls_trans (by norm_num) hcls hcls'
  have hg₁' : co1Act g v₂ = v₂ := (Pairs.co1Act_eq g v₂).trans hg₁
  have hg₂' : co1Act g y = v₂ + y := (Pairs.co1Act_eq g y).trans hg₂
  refine ⟨g, mem_co1Stab.2 hg₁', y, ?_, ?_⟩
  · have h := q₀_add y v₂
    rw [add_comm y v₂, Leech.q₀_eq_zero_of_mem_co1Orbit_zero hvy₀,
      Leech.q₀_eq_zero_of_mem_co1Orbit_zero hy₀,
      Leech.q₀_eq_zero_of_mem_co1Orbit_zero v₂_mem_co1Orbit] at h
    linear_combination -h
  · rw [hg₂', add_assoc, vec_add_self, add_zero]

theorem exists_witness_two
    (h : McLRepFacts c₁ c₂ y₀) :
    ∃ A ∈ co1Stab v₂, ∃ x : Fin 24 → ZMod 2, bil₀ x v₂ = 0 ∧ co1Act A x + x ≠ 0 ∧
      co1Act A x + x ≠ v₂ := by
  have h1 : bil₀ v₂ y₀ = 1 := bil₀_eq_one_of_pair v₂_mem_co1Orbit h.mem_y₀ h.sum_mem
  obtain ⟨y, hy₁, -, hy⟩ := h.nontriv
  have key : ∀ c' : Co1, co1Act c' v₂ = v₂ → co1Act c' y₀ = y₀ → co1Act c' y ≠ y →
      ∃ A ∈ co1Stab v₂, ∃ x : Fin 24 → ZMod 2, bil₀ x v₂ = 0 ∧ co1Act A x + x ≠ 0 ∧
        co1Act A x + x ≠ v₂ := by
    intro c' h₁ h₂ hne
    refine ⟨c', mem_co1Stab.2 h₁, y, hy₁, fun h0 => hne ?_, fun hv => ?_⟩
    · exact (eq_neg_of_add_eq_zero_left h0).trans (Leech.neg_eq_self y)
    · have h3 : bil₀ (co1Act c' y + y) y₀ = 0 := by
        have h4 : bil₀ (co1Act c' y) (co1Act c' y₀) = bil₀ y y₀ := Leech.bil₀_co1Act c' y y₀
        rw [h₂] at h4
        rw [Leech.bil₀_add_left, h4]
        exact CharTwo.add_self_eq_zero _
      rw [hv, h1] at h3
      exact one_ne_zero h3
  rcases hy with hy | hy
  · exact key c₁ h.fix_c₁.1 h.fix_c₁.2 hy
  · exact key c₂ h.fix_c₂.1 h.fix_c₂.2 hy

theorem comm_span_co2_of_rep
    (h : McLRepFacts c₁ c₂ y₀) :
    ∀ u ∈ co1Orbit 0, ∀ X : Submodule (ZMod 2) (Fin 24 → ZMod 2),
    (∀ x ∈ X, bil₀ x u = 0) → (∀ A ∈ co1Stab u, ∀ x ∈ X, co1Act A x ∈ X) →
    (∀ A ∈ co1Stab u, ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → co1Act A y + y ∈ X) →
    ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → y ∈ X := by
  intro u hu X hX hinv hcomm
  obtain ⟨c, rfl⟩ := exists_co1Act_eq_v₂ hu
  have huX : co1Act c v₂ ∈ X := by
    obtain ⟨A, hA, x, hx, hAx⟩ := exists_witness_one
    have h1 := hcomm (c * A * c⁻¹) (conj_mem_co1Stab hA c) (co1Act c x) (by
      rw [Leech.bil₀_co1Act]
      exact hx)
    rwa [co1Act_conj_add, hAx] at h1
  rcases irred_co2_of_rep h _ hu X huX hX hinv with h0 | h1
  · exfalso
    obtain ⟨A, hA, x, hx, hne, hv⟩ := exists_witness_two h
    have hmem := hcomm (c * A * c⁻¹) (conj_mem_co1Stab hA c) (co1Act c x) (by
      rw [Leech.bil₀_co1Act]
      exact hx)
    rw [co1Act_conj_add, h0, Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul] at ha
      exact hne (co1Act_injective c (ha.symm.trans (map_zero (co1Act c)).symm))
    · rw [one_smul] at ha
      exact hv (co1Act_injective c ha.symm)
  · exact h1

end CoTwoModule

theorem co2McLModule_of_rep
    {c₁ c₂ : CFSG.Blueprint.NativeSporadic.Co1}
    {y₀ : Fin 24 → ZMod 2} (h : McLRepFacts c₁ c₂ y₀) : Co2McLModule :=
  ⟨CoTwoModule.comm_span_co2_of_rep h, CoTwoModule.comm_span_mcl_of_rep h,
    CoTwoModule.irred_co2_of_rep h, CoTwoModule.nondeg_co2_of_rep h,
    CoTwoModule.nondeg_mcl_of_rep h⟩

end CFSG.Monster.GMS
