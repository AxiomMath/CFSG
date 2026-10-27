module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C126.A5

open Equiv Equiv.Perm

@[expose] def kleinSet (π : Perm (Fin 5)) : Finset (Perm (Fin 5)) :=
  {1, swap (π 0) (π 1), swap (π 2) (π 3), swap (π 0) (π 1) * swap (π 2) (π 3)}

@[expose] def cyc3 (π : Perm (Fin 5)) : Perm (Fin 5) := swap (π 2) (π 3) * swap (π 3) (π 4)

set_option synthInstance.maxSize 2000 in
theorem inv_odd_isSwap : ∀ h : Perm (Fin 5), h ^ 2 = 1 → sign h = -1 →
    ∃ x y : Fin 5, x ≠ y ∧ h = swap x y := by
  decide +kernel

theorem sign_mulEquiv (φ : Perm (Fin 5) ≃* Perm (Fin 5)) (g : Perm (Fin 5)) :
    sign (φ g) = sign g := by
  have h : (sign.comp φ.toMonoidHom) = sign := by
    apply Equiv.Perm.eq_sign_of_surjective_hom
    intro u
    obtain ⟨g', hg'⟩ := (Equiv.Perm.sign_surjective (Fin 5)) u
    exact ⟨φ.symm g', by simpa using hg'⟩
  have := congrArg (fun f : Perm (Fin 5) →* ℤˣ => f g) h
  simpa using this

theorem isSwap_mulEquiv (φ : Perm (Fin 5) ≃* Perm (Fin 5)) {g : Perm (Fin 5)}
    (hg : g.IsSwap) : (φ g).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := hg
  have h2 : (φ (swap x y)) ^ 2 = 1 := by
    rw [← map_pow, sq, swap_mul_self]; simp
  have h3 : sign (φ (swap x y)) = -1 := by
    rw [sign_mulEquiv, sign_swap hxy]
  obtain ⟨a, b, hab, h⟩ := inv_odd_isSwap _ h2 h3
  exact ⟨a, b, hab, h⟩

theorem isSwap_mulEquiv_iff (φ : Perm (Fin 5) ≃* Perm (Fin 5)) (g : Perm (Fin 5)) :
    (φ g).IsSwap ↔ g.IsSwap := by
  refine ⟨fun h => ?_, isSwap_mulEquiv φ⟩
  simpa using isSwap_mulEquiv φ.symm h

def mkPerm (a b c d : Fin 5) : Perm (Fin 5) :=
  let σ₁ : Perm (Fin 5) := swap a 0
  let σ₂ : Perm (Fin 5) := swap (σ₁ b) 1 * σ₁
  let σ₃ : Perm (Fin 5) := swap (σ₂ c) 2 * σ₂
  swap (σ₃ d) 3 * σ₃

set_option synthInstance.maxSize 2000 in
theorem mkPerm_spec : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    mkPerm a b c d a = 0 ∧ mkPerm a b c d b = 1 ∧ mkPerm a b c d c = 2 ∧
      mkPerm a b c d d = 3 := by
  unfold mkPerm
  decide +kernel

set_option synthInstance.maxSize 2000 in
theorem swap_overlap_cube : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → swap a b ≠ swap c d →
    (a = c ∨ a = d ∨ b = c ∨ b = d) → ((swap a b * swap c d) ^ 3 = 1 ∧
      swap a b * swap c d ≠ 1) := by
  decide +kernel

theorem card_kleinSet : ∀ π : Perm (Fin 5), (kleinSet π).card = 4 := by
  unfold kleinSet
  decide +kernel

theorem orderOf_swap' {a b : Fin 5} (hab : a ≠ b) : orderOf (swap a b) = 2 :=
  orderOf_eq_prime (by rw [sq, swap_mul_self]) (by simpa using hab)

theorem klein_swaps (W : Subgroup (Perm (Fin 5))) (hW : Nat.card W = 4)
    (hgen : W = Subgroup.closure {g | g ∈ W ∧ g.IsSwap}) :
    ∃ π : Perm (Fin 5), W = Subgroup.closure {swap (π 0) (π 1), swap (π 2) (π 3)} := by
  classical
  obtain ⟨s, hsW, a, b, hab, rfl⟩ : ∃ s ∈ W, s.IsSwap := by
    by_contra hcon
    push Not at hcon
    have : {g | g ∈ W ∧ g.IsSwap} = (∅ : Set (Perm (Fin 5))) := by
      ext g; simpa using fun hg => hcon g hg
    rw [this, Subgroup.closure_empty] at hgen
    rw [hgen] at hW
    simp at hW
  obtain ⟨t, htW, ⟨c, d, hcd, rfl⟩, htz⟩ :
      ∃ t ∈ W, t.IsSwap ∧ t ∉ Subgroup.zpowers (swap a b) := by
    by_contra hcon
    push Not at hcon
    have hle : W ≤ Subgroup.zpowers (swap a b) := by
      rw [hgen, Subgroup.closure_le]
      intro g hg
      exact hcon g hg.1 hg.2
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers (swap a b)) = 2 := by
      rw [Nat.card_zpowers, orderOf_swap' hab]
    omega
  have hne : swap a b ≠ swap c d := fun h => htz (h ▸ Subgroup.mem_zpowers _)
  have hdisj : ¬ (a = c ∨ a = d ∨ b = c ∨ b = d) := by
    intro hov
    obtain ⟨h3, h1⟩ := swap_overlap_cube a b c d hab hcd hne hov
    have := orderOf_eq_prime h3 h1
    have hd := Subgroup.orderOf_dvd_natCard W (W.mul_mem hsW htW)
    rw [this, hW] at hd
    omega
  push Not at hdisj
  obtain ⟨hac, had, hbc, hbd⟩ := hdisj
  obtain ⟨σ, h0, h1, h2, h3⟩ : ∃ σ : Perm (Fin 5), σ a = 0 ∧ σ b = 1 ∧ σ c = 2 ∧ σ d = 3 :=
    ⟨mkPerm a b c d, mkPerm_spec a b c d hab hac had hbc hbd hcd⟩
  refine ⟨σ⁻¹, ?_⟩
  have e0 : σ⁻¹ 0 = a := by rw [← h0]; simp
  have e1 : σ⁻¹ 1 = b := by rw [← h1]; simp
  have e2 : σ⁻¹ 2 = c := by rw [← h2]; simp
  have e3 : σ⁻¹ 3 = d := by rw [← h3]; simp
  rw [e0, e1, e2, e3]
  have hc4 := card_kleinSet σ⁻¹
  unfold kleinSet at hc4
  rw [e0, e1, e2, e3] at hc4
  have hFsub : ({1, swap a b, swap c d, swap a b * swap c d} : Finset (Perm (Fin 5))) ⊆
      (W : Set (Perm (Fin 5))).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [W.one_mem]
    · simpa using hsW
    · simpa using htW
    · simpa using W.mul_mem hsW htW
  have hWcard : (W : Set (Perm (Fin 5))).toFinset.card = 4 := by
    rw [← hW, Nat.card_eq_fintype_card, Fintype.card_eq_nat_card]
    simp [Nat.card_eq_fintype_card]
  have hFeq := Finset.eq_of_subset_of_card_le hFsub (by omega)
  ext w
  constructor
  · intro hw
    have : w ∈ (W : Set (Perm (Fin 5))).toFinset := by simpa using hw
    rw [← hFeq] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · intro hw
    have hle : Subgroup.closure ({swap a b, swap c d} : Set (Perm (Fin 5))) ≤ W := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact hsW
      · exact htW
    exact hle hw

theorem cyc3_comm : ∀ π : Perm (Fin 5),
    swap (π 0) (π 1) * cyc3 π = cyc3 π * swap (π 0) (π 1) := by
  unfold cyc3
  decide +kernel

theorem swap_cyc3_swap : ∀ π : Perm (Fin 5),
    swap (π 2) (π 3) * cyc3 π * swap (π 2) (π 3) = (cyc3 π)⁻¹ := by
  unfold cyc3
  decide +kernel

theorem cyc3_pow_three : ∀ π : Perm (Fin 5), cyc3 π ^ 3 = 1 := by
  unfold cyc3
  decide +kernel

theorem cyc3_ne_one : ∀ π : Perm (Fin 5), cyc3 π ≠ 1 := by
  unfold cyc3
  decide +kernel

theorem isThreeCycle_cyc3 (π : Perm (Fin 5)) : (cyc3 π).IsThreeCycle := by
  unfold cyc3
  have h23 : π 2 ≠ π 3 := fun h => by simpa using π.injective h
  have h24 : π 2 ≠ π 4 := fun h => by simpa using π.injective h
  have h34 : π 3 ≠ π 4 := fun h => by simpa using π.injective h
  rw [swap_comm (π 2) (π 3)]
  exact isThreeCycle_swap_mul_swap_same h23.symm h34 h24

theorem cyc3_mem_alternatingGroup (π : Perm (Fin 5)) : cyc3 π ∈ alternatingGroup (Fin 5) :=
  (isThreeCycle_cyc3 π).mem_alternatingGroup

theorem normalClosure_cyc3 (π : Perm (Fin 5)) :
    Subgroup.normalClosure {cyc3 π} = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (by simpa using cyc3_mem_alternatingGroup π)
  · have h3 : Subgroup.closure {σ : Perm (Fin 5) | σ.IsThreeCycle} = alternatingGroup (Fin 5) :=
      Equiv.Perm.closure_three_cycles_eq_alternating
    rw [← h3, Subgroup.closure_le]
    intro τ hτ
    have hτ' : τ.cycleType = {3} := hτ
    obtain ⟨g, hg⟩ := isConj_iff.1
      (isConj_iff_cycleType_eq.2 ((isThreeCycle_cyc3 π).trans hτ'.symm))
    rw [← hg]
    exact (Subgroup.normalClosure_normal (s := {cyc3 π})).conj_mem (cyc3 π)
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) g


theorem comm_cyc3_swap : ∀ π : Perm (Fin 5),
    cyc3 π * swap (π 2) (π 3) * (cyc3 π)⁻¹ * (swap (π 2) (π 3))⁻¹ = cyc3 π * cyc3 π := by
  unfold cyc3
  decide +kernel

theorem cyc3_mul_self_ne_one : ∀ π : Perm (Fin 5), cyc3 π * cyc3 π ≠ 1 := by
  unfold cyc3
  decide +kernel

end CFSG.Quasithin.C126.A5
