module

public import CFSG.Quasithin.AppendixH.H16.H165FourData
public import CFSG.Quasithin.Background.RonanH143Syl
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.RonanH143NF

public section

namespace CFSG.ASVolI.H16

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.RonanH143

theorem mem_of_centralizes_sylow {P H : Subgroup P24} (hP : IsSylowIn 2 P H) {z : P24}
    (hzH : z ∈ H) (hz : z * z = 1) (hc : ∀ s ∈ P, s * z = z * s) : z ∈ P := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let Q : Subgroup P24 :=
    { carrier := {x | ∃ s ∈ P, x = s ∨ x = s * z}
      mul_mem' := by
        intro x y hx hy
        obtain ⟨s, hs, hxs | hxs⟩ := hx <;>
          obtain ⟨s', hs', hys | hys⟩ := hy
        · refine ⟨s * s', P.mul_mem hs hs', Or.inl ?_⟩
          rw [hxs, hys]
        · refine ⟨s * s', P.mul_mem hs hs', Or.inr ?_⟩
          rw [hxs, hys]
          group
        · refine ⟨s * s', P.mul_mem hs hs', Or.inr ?_⟩
          rw [hxs, hys]
          calc (s * z) * s' = s * (z * s') := by group
            _ = s * (s' * z) := by rw [← hc s' hs']
            _ = (s * s') * z := by group
        · refine ⟨s * s', P.mul_mem hs hs', Or.inl ?_⟩
          rw [hxs, hys]
          calc (s * z) * (s' * z) = s * (z * s') * z := by group
            _ = s * (s' * z) * z := by rw [← hc s' hs']
            _ = (s * s') * (z * z) := by group
            _ = s * s' := by rw [hz, mul_one]
      one_mem' := ⟨1, P.one_mem, Or.inl rfl⟩
      inv_mem' := by
        intro x hx
        obtain ⟨s, hs, hxs | hxs⟩ := hx
        · refine ⟨s⁻¹, P.inv_mem hs, Or.inl ?_⟩
          rw [hxs]
        · refine ⟨s⁻¹, P.inv_mem hs, Or.inr ?_⟩
          rw [hxs]
          calc (s * z)⁻¹ = z⁻¹ * s⁻¹ := mul_inv_rev _ _
            _ = z * s⁻¹ := by rw [hzinv]
            _ = s⁻¹ * z := by rw [← hc s⁻¹ (P.inv_mem hs)] }
  have hQH : Q ≤ H := by
    intro x hx
    obtain ⟨s, hs, hxs | hxs⟩ := hx
    · rw [hxs]; exact hP.le hs
    · rw [hxs]; exact H.mul_mem (hP.le hs) hzH
  have hPQ : P ≤ Q := fun s hs => ⟨s, hs, Or.inl rfl⟩
  have hQ2 : IsPGroup 2 Q := by
    intro x
    obtain ⟨s, hs, hxs | hxs⟩ := x.2
    · obtain ⟨k, hk⟩ := hP.isPGroup ⟨s, hs⟩
      refine ⟨k, Subtype.ext ?_⟩
      change (x : P24) ^ 2 ^ k = 1
      rw [hxs]
      exact congrArg Subtype.val hk
    · obtain ⟨k, hk⟩ := hP.isPGroup ⟨s, hs⟩
      refine ⟨k + 1, Subtype.ext ?_⟩
      change (x : P24) ^ 2 ^ (k + 1) = 1
      rw [hxs]
      have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [Commute.mul_pow (hc s hs)]
      have hs1 : s ^ 2 ^ (k + 1) = 1 := by
        rw [Nat.pow_succ, pow_mul, hk', one_pow]
      have hz1 : z ^ 2 ^ (k + 1) = 1 := by
        rw [Nat.pow_succ', pow_mul, show z ^ 2 = 1 by rw [pow_two, hz], one_pow]
      rw [hs1, hz1, mul_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQsub : IsPGroup 2 (Q.subgroupOf H) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hle : P.subgroupOf H ≤ Q.subgroupOf H :=
    fun x hx => hPQ (Subgroup.mem_subgroupOf.1 hx)
  have hEq : Q.subgroupOf H = P.subgroupOf H := by
    have := (hP.toSylow).is_maximal' hQsub (by rwa [hP.coe_toSylow])
    rwa [hP.coe_toSylow] at this
  have hzQ : z ∈ Q := ⟨1, P.one_mem, Or.inr (by rw [one_mul])⟩
  have hzQsub : (⟨z, hzH⟩ : H) ∈ Q.subgroupOf H := Subgroup.mem_subgroupOf.2 hzQ
  rw [hEq] at hzQsub
  exact Subgroup.mem_subgroupOf.1 hzQsub

@[expose] def h165P2Arr (t j b : ℕ) : Array ℕ :=
  if b = 0 then cArr (koArr t) (dArrs.getD j #[]) else cArr (cArr (koArr t) (dArrs.getD j #[])) eArr

@[expose] def h165P2GenArrs : List (Array ℕ) :=
  [koArr 1, koArr 2, koArr 4, koArr 8] ++ (List.range 8).map (fun j => dArrs.getD j #[]) ++ [eArr]

set_option synthInstance.maxSize 1000 in
theorem h165_centerCheck : ∀ t < 16, ∀ j < 8, ∀ b < 2,
    (∀ g ∈ h165P2GenArrs, ∀ i < 24,
      (cArr (h165P2Arr t j b) g)[i]! = (cArr g (h165P2Arr t j b))[i]!) →
    (∀ i < 24, (h165P2Arr t j b)[i]! = i) ∨
      (∀ i < 24, (h165P2Arr t j b)[i]! = (koArr 7)[i]!) := by
  decide +kernel

private theorem h165P2GenArrs_mem : ∀ g ∈ h165P2GenArrs, ∃ s ∈ P2, HasArr s g := by
  intro g hg
  simp only [h165P2GenArrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hg
  rcases hg with ((rfl | rfl | rfl | rfl) | ⟨j, hj, hjg⟩) | rfl
  · exact ⟨koPerm 1, PO_le_P2 (koPerm_mem_PO 1), hasArr_permOfArr (koArr_ok 1).1⟩
  · exact ⟨koPerm 2, PO_le_P2 (koPerm_mem_PO 2), hasArr_permOfArr (koArr_ok 2).1⟩
  · exact ⟨koPerm 4, PO_le_P2 (koPerm_mem_PO 4), hasArr_permOfArr (koArr_ok 4).1⟩
  · exact ⟨koPerm 8, PO_le_P2 (koPerm_mem_PO 8), hasArr_permOfArr (koArr_ok 8).1⟩
  · rw [← hjg]
    exact ⟨dPerm ⟨j, hj⟩, PO_le_P2 (dPerm_mem_PO ⟨j, hj⟩),
      hasArr_permOfArr (dArrs_ok ⟨j, hj⟩).1⟩
  · exact ⟨ePerm, ePerm_mem_P2, hasArr_ePerm⟩

theorem h165_center_P2 {x : P24} (hx : x ∈ P2) (hc : ∀ s ∈ P2, s * x = x * s) :
    x = 1 ∨ x = h165Z0 := by
  obtain ⟨y, hy, hxy | hxy⟩ := mem_P2_iff.1 hx
  · obtain ⟨t, j, rfl⟩ := hy
    set xa : Array ℕ := h165P2Arr (t : ℕ) (j : ℕ) 0 with hxa
    have hxarr : HasArr x xa := by
      have harr : xa = cArr (koArr (t : ℕ)) (dArrs.getD (j : ℕ) #[]) := by
        rw [hxa]; simp [h165P2Arr]
      rw [hxy, harr]
      exact hasArr_mul (hasArr_permOfArr (koArr_ok t).1) (hasArr_permOfArr (dArrs_ok j).1)
    have hcomm : ∀ g ∈ h165P2GenArrs, ∀ i < 24,
        (cArr xa g)[i]! = (cArr g xa)[i]! := by
      intro g hg i hi
      obtain ⟨s, hs, hsg⟩ := h165P2GenArrs_mem g hg
      have h1 : ((s * x) ⟨i, hi⟩ : ℕ) = (cArr g xa)[i]! := hasArr_mul hsg hxarr ⟨i, hi⟩
      have h2 : ((x * s) ⟨i, hi⟩ : ℕ) = (cArr xa g)[i]! := hasArr_mul hxarr hsg ⟨i, hi⟩
      have heq : ((s * x) ⟨i, hi⟩ : ℕ) = ((x * s) ⟨i, hi⟩ : ℕ) := by rw [hc s hs]
      rw [← h2, ← h1]
      exact heq.symm
    rcases h165_centerCheck (t : ℕ) t.isLt (j : ℕ) j.isLt 0 (by norm_num) hcomm with h1 | h7
    · left
      apply Equiv.ext
      intro p
      apply Fin.ext
      rw [hxarr p, h1 (p : ℕ) p.isLt]
      rfl
    · right
      apply Equiv.ext
      intro p
      apply Fin.ext
      rw [hxarr p, h7 (p : ℕ) p.isLt]
      exact (hasArr_h165Z0 p).symm
  · obtain ⟨t, j, rfl⟩ := hy
    set xa : Array ℕ := h165P2Arr (t : ℕ) (j : ℕ) 1 with hxa
    have hxarr : HasArr x xa := by
      have harr : xa = cArr (cArr (koArr (t : ℕ)) (dArrs.getD (j : ℕ) #[])) eArr := by
        rw [hxa]; simp [h165P2Arr]
      rw [hxy, harr]
      exact hasArr_mul (hasArr_mul (hasArr_permOfArr (koArr_ok t).1)
        (hasArr_permOfArr (dArrs_ok j).1)) hasArr_ePerm
    have hcomm : ∀ g ∈ h165P2GenArrs, ∀ i < 24,
        (cArr xa g)[i]! = (cArr g xa)[i]! := by
      intro g hg i hi
      obtain ⟨s, hs, hsg⟩ := h165P2GenArrs_mem g hg
      have h1 : ((s * x) ⟨i, hi⟩ : ℕ) = (cArr g xa)[i]! := hasArr_mul hsg hxarr ⟨i, hi⟩
      have h2 : ((x * s) ⟨i, hi⟩ : ℕ) = (cArr xa g)[i]! := hasArr_mul hxarr hsg ⟨i, hi⟩
      have heq : ((s * x) ⟨i, hi⟩ : ℕ) = ((x * s) ⟨i, hi⟩ : ℕ) := by rw [hc s hs]
      rw [← h2, ← h1]
      exact heq.symm
    rcases h165_centerCheck (t : ℕ) t.isLt (j : ℕ) j.isLt 1 (by norm_num) hcomm with h1 | h7
    · left
      apply Equiv.ext
      intro p
      apply Fin.ext
      rw [hxarr p, h1 (p : ℕ) p.isLt]
      rfl
    · right
      apply Equiv.ext
      intro p
      apply Fin.ext
      rw [hxarr p, h7 (p : ℕ) p.isLt]
      exact (hasArr_h165Z0 p).symm

theorem isTwoCentral_conj {Γ : Subgroup P24} {z : P24}
    (hz : ∃ S : Subgroup P24, IsSylowIn 2 S Γ ∧ ∀ s ∈ S, s * z = z * s) (c : P24) :
    ∃ S : Subgroup P24, IsSylowIn 2 S (conjSubg c Γ) ∧
      ∀ s ∈ S, s * (c * z * c⁻¹) = (c * z * c⁻¹) * s := by
  obtain ⟨S, hS, hSc⟩ := hz
  refine ⟨conjSubg c S, isSylowIn_conj c hS, ?_⟩
  intro s hs
  have hsS : c⁻¹ * s * c ∈ S := mem_conjSubg_iff.1 hs
  have hcomm := hSc (c⁻¹ * s * c) hsS
  calc s * (c * z * c⁻¹) = c * (c⁻¹ * s * c) * c⁻¹ * (c * z * c⁻¹) := by group
    _ = c * ((c⁻¹ * s * c) * z) * c⁻¹ := by group
    _ = c * (z * (c⁻¹ * s * c)) * c⁻¹ := by rw [hcomm]
    _ = (c * z * c⁻¹) * s := by group

theorem orderOf_conj' (c z : P24) : orderOf (c * z * c⁻¹) = orderOf z := by
  rw [← MulAut.conj_apply]
  exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective z

theorem exists_conj_to_z0
    {z : P24} (hz : z ∈ mog22plus) (hz2 : orderOf z = 2)
    (hc : ∃ S : Subgroup P24, IsSylowIn 2 S mog22plus ∧ ∀ s ∈ S, s * z = z * s) :
    ∃ g ∈ mog22plus, g * z * g⁻¹ = h165Z0 := by
  have hzz : z * z = 1 := by
    rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz2
    simp at hz2
  obtain ⟨S, hS, hSc⟩ := hc
  have hzS : z ∈ S := mem_of_centralizes_sylow hS hz hzz hSc
  obtain ⟨γ, hγ, hγS⟩ := exists_conj_sylow_P2 hS
  refine ⟨γ, hγ, ?_⟩
  set x : P24 := γ * z * γ⁻¹ with hx
  have hxP2 : x ∈ P2 := by
    rw [hx, ← hγS]
    refine mem_conjSubg_iff.2 ?_
    rw [show γ⁻¹ * (γ * z * γ⁻¹) * γ = z by group]
    exact hzS
  have hxc : ∀ s ∈ P2, s * x = x * s := by
    intro s hs
    have hsS : γ⁻¹ * s * γ ∈ S := by
      rw [← hγS] at hs
      exact mem_conjSubg_iff.1 hs
    have hcomm := hSc (γ⁻¹ * s * γ) hsS
    rw [hx]
    calc s * (γ * z * γ⁻¹) = γ * (γ⁻¹ * s * γ) * γ⁻¹ * (γ * z * γ⁻¹) := by group
      _ = γ * ((γ⁻¹ * s * γ) * z) * γ⁻¹ := by group
      _ = γ * (z * (γ⁻¹ * s * γ)) * γ⁻¹ := by rw [hcomm]
      _ = (γ * z * γ⁻¹) * s := by group
  rcases h165_center_P2 hxP2 hxc with hx1 | hx0
  · exfalso
    apply hz1
    have h2 : z = γ⁻¹ * (γ * z * γ⁻¹) * γ := by group
    rw [← hx] at h2
    rw [hx1] at h2
    simpa using h2
  · exact hx0
end CFSG.ASVolI.H16
