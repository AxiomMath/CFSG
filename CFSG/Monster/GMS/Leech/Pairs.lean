module

public import CFSG.Monster.GMS.Leech.Count
public import CFSG.Monster.GMS.Leech.Data
public import CFSG.Monster.GMS.Facts.LeechPairs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement Matrix

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem card_inf_centralizer_one
    {q : G} (hq : q ∈ leechQ z) (hv : L.vec q ≠ 0) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({q} : Set G)) =
      2 ^ 24 * Nat.card ↥(co1Stab (L.vec q)) := by
  have hind : LinearIndependent (ZMod 2) fun i : Fin 1 => L.vec (![q] i) := by
    have : (fun i : Fin 1 => L.vec (![q] i)) = ![L.vec q] := by
      funext i
      fin_cases i
      rfl
    rw [this]
    exact Leech.linearIndependent_fin_one hv
  have h := L.card_inf_iInf_centralizer ![q] (fun i => by fin_cases i; exact hq) hind
  have hs1 : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) =
      Subgroup.centralizer ({z} : Set G) ⊓
        ⨅ i : Fin 1, Subgroup.centralizer ({![q] i} : Set G) := by
    ext x
    simp [Subgroup.mem_inf]
  have hs2 : (⨅ i : Fin 1, co1Stab (L.vec (![q] i))) = co1Stab (L.vec q) := by
    ext x
    simp
  rw [hs1, h, hs2]
  simp

theorem card_inf_centralizer_two
    {q₁ q₂ : G} (h₁ : q₁ ∈ leechQ z) (h₂ : q₂ ∈ leechQ z)
    (hind : LinearIndependent (ZMod 2) ![L.vec q₁, L.vec q₂]) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({q₁} : Set G) ⊓
        Subgroup.centralizer ({q₂} : Set G)) =
      2 ^ 23 * Nat.card ↥(co1Stab (L.vec q₁) ⊓ co1Stab (L.vec q₂)) := by
  have hind' : LinearIndependent (ZMod 2) fun i : Fin 2 => L.vec (![q₁, q₂] i) := by
    have : (fun i : Fin 2 => L.vec (![q₁, q₂] i)) = ![L.vec q₁, L.vec q₂] := by
      funext i
      fin_cases i <;> rfl
    rw [this]
    exact hind
  have h := L.card_inf_iInf_centralizer ![q₁, q₂] (fun i => by fin_cases i <;> assumption) hind'
  have hs1 : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({q₁} : Set G) ⊓
      Subgroup.centralizer ({q₂} : Set G) =
      Subgroup.centralizer ({z} : Set G) ⊓
        ⨅ i : Fin 2, Subgroup.centralizer ({![q₁, q₂] i} : Set G) := by
    ext x
    simp [Subgroup.mem_inf, Subgroup.mem_iInf, Fin.forall_fin_two, and_assoc]
  have hs2 : (⨅ i : Fin 2, co1Stab (L.vec (![q₁, q₂] i))) =
      co1Stab (L.vec q₁) ⊓ co1Stab (L.vec q₂) := by
    ext x
    simp [Subgroup.mem_inf, Subgroup.mem_iInf, Fin.forall_fin_two]
  rw [hs1, h, hs2]
  simp

theorem card_inf_centralizer_three
    {q₁ q₂ q₃ : G} (h₁ : q₁ ∈ leechQ z) (h₂ : q₂ ∈ leechQ z)
    (h₃ : q₃ ∈ leechQ z) (hind : LinearIndependent (ZMod 2) ![L.vec q₁, L.vec q₂, L.vec q₃]) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({q₁} : Set G) ⊓
        Subgroup.centralizer ({q₂} : Set G) ⊓ Subgroup.centralizer ({q₃} : Set G)) =
      2 ^ 22 * Nat.card ↥(co1Stab (L.vec q₁) ⊓ co1Stab (L.vec q₂) ⊓ co1Stab (L.vec q₃)) := by
  have hind' : LinearIndependent (ZMod 2) fun i : Fin 3 => L.vec (![q₁, q₂, q₃] i) := by
    have : (fun i : Fin 3 => L.vec (![q₁, q₂, q₃] i)) = ![L.vec q₁, L.vec q₂, L.vec q₃] := by
      funext i
      fin_cases i <;> rfl
    rw [this]
    exact hind
  have h := L.card_inf_iInf_centralizer ![q₁, q₂, q₃] (fun i => by fin_cases i <;> assumption)
    hind'
  have hs1 : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({q₁} : Set G) ⊓
      Subgroup.centralizer ({q₂} : Set G) ⊓ Subgroup.centralizer ({q₃} : Set G) =
      Subgroup.centralizer ({z} : Set G) ⊓
        ⨅ i : Fin 3, Subgroup.centralizer ({![q₁, q₂, q₃] i} : Set G) := by
    ext x
    simp [Subgroup.mem_inf, Subgroup.mem_iInf, Fin.forall_fin_succ, and_assoc]
  have hs2 : (⨅ i : Fin 3, co1Stab (L.vec (![q₁, q₂, q₃] i))) =
      co1Stab (L.vec q₁) ⊓ co1Stab (L.vec q₂) ⊓ co1Stab (L.vec q₃) := by
    ext x
    simp [Subgroup.mem_inf, Subgroup.mem_iInf, Fin.forall_fin_succ, and_assoc]
  rw [hs1, h, hs2]
  simp

theorem isLeechTwo_iff
    {q : G} : IsLeechTwo z q ↔ q ∈ L.typeSet 0 := by
  constructor
  · rintro ⟨hq, h1, hz, hsq, hcard⟩
    rcases L.mem_typeSet_zero_or_two hq h1 hz hsq with h | h
    · exact h
    · exfalso
      have hc := L.card_inf_centralizer_one hq (L.vec_ne_zero_of_mem_typeSet h)
      have ho := Leech.card_co1Stab_mul_ncard_co1Orbit h.2
      rw [Leech.ncard_co1Orbit_two, CFSG.Sporadic.Co1.card_Co1] at ho
      rw [hc] at hcard
      norm_num at hcard
      omega
  · intro h
    refine ⟨h.1, L.ne_one_of_mem_typeSet h, L.ne_z_of_mem_typeSet h,
      L.mul_self_of_mem_typeSet_zero h, ?_⟩
    rw [L.card_inf_centralizer_one h.1 (L.vec_ne_zero_of_mem_typeSet h)]
    have ho := Leech.card_co1Stab_mul_ncard_co1Orbit h.2
    rw [Leech.ncard_co1Orbit_zero, CFSG.Sporadic.Co1.card_Co1] at ho
    have : Nat.card ↥(co1Stab (L.vec q)) = 42305421312000 := by omega
    rw [this]
    norm_num

theorem vec_add_mem_co1Orbit_one
    {q₁ q₂ : G} (h₁ : q₁ ∈ leechQ z) (h₂ : q₂ ∈ leechQ z)
    (hs : (q₁ * q₂) * (q₁ * q₂) = z) : L.vec q₁ + L.vec q₂ ∈ co1Orbit 1 := by
  rw [← L.vec_mul q₁ h₁ q₂ h₂]
  exact Leech.mem_co1Orbit_one_of_q₀_eq_one ((L.mul_self_eq_z_iff (mul_mem h₁ h₂)).1 hs)

theorem leechData_pair_one
    (hP : Co1PairFacts) :
    ∀ q ∈ L.typeSet 0, ∃ q' ∈ L.typeSet 0, q * q' ∈ L.typeSet 0 ∧
      3 ^ 6 * 11 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({q} : Set G) ⊓ Subgroup.centralizer ({q'} : Set G)) := by
  intro q hq
  obtain ⟨y, hy, hxy, hdvd⟩ := hP.1 (L.vec q) hq.2
  obtain ⟨q', hq'Q, hq'v⟩ := L.vec_surj y
  have hq' : q' ∈ L.typeSet 0 := ⟨hq'Q, by rw [hq'v]; exact hy⟩
  refine ⟨q', hq', (L.mul_mem_typeSet_iff hq.1 hq'Q).2 (by rw [hq'v]; exact hxy), ?_⟩
  have hind : LinearIndependent (ZMod 2) ![L.vec q, L.vec q'] :=
    Leech.linearIndependent_pair_of_add_mem (L.vec_ne_zero_of_mem_typeSet hq)
      (L.vec_ne_zero_of_mem_typeSet hq') (by rw [hq'v]; exact hxy)
  rw [L.card_inf_centralizer_two hq.1 hq'Q hind, hq'v]
  exact Dvd.dvd.mul_left hdvd _

theorem leechData_pair_two
    (hP : Co1PairFacts) :
    ∀ q ∈ L.typeSet 0, ∃ q' ∈ L.typeSet 2, q * q' ∈ L.typeSet 0 ∧
      2 ^ 41 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({q} : Set G) ⊓ Subgroup.centralizer ({q'} : Set G)) := by
  intro q hq
  obtain ⟨y, hy, hxy, hdvd⟩ := hP.2.1 (L.vec q) hq.2
  obtain ⟨q', hq'Q, hq'v⟩ := L.vec_surj y
  have hq' : q' ∈ L.typeSet 2 := ⟨hq'Q, by rw [hq'v]; exact hy⟩
  refine ⟨q', hq', (L.mul_mem_typeSet_iff hq.1 hq'Q).2 (by rw [hq'v]; exact hxy), ?_⟩
  have hind : LinearIndependent (ZMod 2) ![L.vec q, L.vec q'] :=
    Leech.linearIndependent_pair_of_add_mem (L.vec_ne_zero_of_mem_typeSet hq)
      (L.vec_ne_zero_of_mem_typeSet hq') (by rw [hq'v]; exact hxy)
  rw [L.card_inf_centralizer_two hq.1 hq'Q hind, hq'v]
  have h41 : (2 : ℕ) ^ 41 = 2 ^ 23 * 2 ^ 18 := by norm_num
  rw [h41]
  exact mul_dvd_mul_left _ hdvd

theorem leechData_pair_three (hP : Co1PairFacts) :
    ∀ q ∈ L.typeSet 0, ∃ q' ∈ L.typeSet 2, q * q' ∈ L.typeSet 2 := by
  intro q hq
  obtain ⟨y, hy, hxy⟩ := hP.2.2.1 (L.vec q) hq.2
  obtain ⟨q', hq'Q, hq'v⟩ := L.vec_surj y
  exact ⟨q', ⟨hq'Q, by rw [hq'v]; exact hy⟩,
    (L.mul_mem_typeSet_iff hq.1 hq'Q).2 (by rw [hq'v]; exact hxy)⟩

theorem leechPairData
    (hP : Co1PairFacts) : LeechPairData z := by
  obtain ⟨-, -, -, hP4, hP5, hP6⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · intro q₁ q₂ q₁' q₂' h₁ h₂ h₁' h₂' hs hs'
    rw [L.isLeechTwo_iff] at h₁ h₂ h₁' h₂'
    have hxy := L.vec_add_mem_co1Orbit_one h₁.1 h₂.1 hs
    have hxy' := L.vec_add_mem_co1Orbit_one h₁'.1 h₂'.1 hs'
    obtain ⟨g, hg1, hg2⟩ := hP4 _ _ _ _ h₁.2 h₂.2 hxy h₁'.2 h₂'.2 hxy'
    obtain ⟨c, rfl⟩ := L.φ_surj g
    have hind : LinearIndependent (ZMod 2) fun i : Fin 2 => L.vec (![q₁', q₂'] i) := by
      have : (fun i : Fin 2 => L.vec (![q₁', q₂'] i)) = ![L.vec q₁', L.vec q₂'] := by
        funext i
        fin_cases i <;> rfl
      rw [this]
      exact Leech.linearIndependent_pair_of_add_mem (L.vec_ne_zero_of_mem_typeSet h₁')
        (L.vec_ne_zero_of_mem_typeSet h₂') hxy'
    obtain ⟨p, hp, hpa⟩ := L.exists_conj_eq
      (a := ![(c : G) * q₁ * (c : G)⁻¹, (c : G) * q₂ * (c : G)⁻¹]) (b := ![q₁', q₂'])
      (fun i => by fin_cases i; exacts [L.conj_mem c h₁.1, L.conj_mem c h₂.1])
      (fun i => by fin_cases i; exacts [h₁'.1, h₂'.1])
      (fun i => by
        fin_cases i
        · show L.vec ((c : G) * q₁ * (c : G)⁻¹) = L.vec q₁'
          rw [L.vec_conj c q₁ h₁.1]
          exact hg1
        · show L.vec ((c : G) * q₂ * (c : G)⁻¹) = L.vec q₂'
          rw [L.vec_conj c q₂ h₂.1]
          exact hg2)
      hind
    refine ⟨p * c, mul_mem (L.mem_centralizer hp) c.2, ?_, ?_⟩
    · have h := hpa 0
      calc p * c * q₁ * (p * c)⁻¹ = p * ((c : G) * q₁ * (c : G)⁻¹) * p⁻¹ := by group
        _ = q₁' := h
    · have h := hpa 1
      calc p * c * q₂ * (p * c)⁻¹ = p * ((c : G) * q₂ * (c : G)⁻¹) * p⁻¹ := by group
        _ = q₂' := h
  · intro q₁ q₂ h₁ h₂ hs
    rw [L.isLeechTwo_iff] at h₁ h₂
    have hxy := L.vec_add_mem_co1Orbit_one h₁.1 h₂.1 hs
    have hind : LinearIndependent (ZMod 2) ![L.vec q₁, L.vec q₂] :=
      Leech.linearIndependent_pair_of_add_mem (L.vec_ne_zero_of_mem_typeSet h₁)
        (L.vec_ne_zero_of_mem_typeSet h₂) hxy
    rw [L.card_inf_centralizer_two h₁.1 h₂.1 hind, hP5 _ _ h₁.2 h₂.2 hxy]
    norm_num
  · intro q₁ q₂ q₃ h₁ h₂ h₃ hs h₁₃ h₃₂
    rw [L.isLeechTwo_iff] at h₁ h₂ h₃ h₁₃ h₃₂
    have hxy := L.vec_add_mem_co1Orbit_one h₁.1 h₂.1 hs
    have hxw : L.vec q₁ + L.vec q₃ ∈ co1Orbit 0 := by
      rw [← L.vec_mul q₁ h₁.1 q₃ h₃.1]
      exact h₁₃.2
    have hwy : L.vec q₃ + L.vec q₂ ∈ co1Orbit 0 := by
      rw [← L.vec_mul q₃ h₃.1 q₂ h₂.1]
      exact h₃₂.2
    have hind : LinearIndependent (ZMod 2) ![L.vec q₁, L.vec q₃, L.vec q₂] := by
      refine Leech.linearIndependent_fin_three (L.vec_ne_zero_of_mem_typeSet h₁)
        (L.vec_ne_zero_of_mem_typeSet h₃) (L.vec_ne_zero_of_mem_typeSet h₂) ?_ ?_ ?_ ?_
      · intro h
        rw [h, CFSG.Sporadic.Co1.Module.vec_add_self] at hxw
        exact Leech.ne_zero_of_mem_co1Orbit hxw rfl
      · intro h
        rw [h, CFSG.Sporadic.Co1.Module.vec_add_self] at hxy
        exact Leech.ne_zero_of_mem_co1Orbit hxy rfl
      · intro h
        rw [h, CFSG.Sporadic.Co1.Module.vec_add_self] at hwy
        exact Leech.ne_zero_of_mem_co1Orbit hwy rfl
      · intro h
        have h1 : L.vec q₁ + L.vec q₂ = L.vec q₃ := by
          rw [← h, ← add_assoc, CFSG.Sporadic.Co1.Module.vec_add_self, zero_add]
        have h0 : L.vec q₃ ∈ co1Orbit 0 := h₃.2
        rw [← h1] at h0
        exact absurd (Leech.eq_of_mem_co1Orbit hxy h0) (by decide)
    rw [L.card_inf_centralizer_three h₁.1 h₃.1 h₂.1 hind,
      hP6 _ _ _ h₁.2 h₂.2 hxy h₃.2 hxw hwy]
    norm_num

end LeechSystem

end CFSG.Monster.GMS
