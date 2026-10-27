module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.RankThree.GF2n

open DihedralGroup

theorem dihedral_eq_conj {m : ℕ} (hm : Odd m) (σ : MulAut (DihedralGroup m))
    (hσ2 : ∀ g, σ (σ g) = g) {k₀ j₀ : ZMod m} (hfix : σ (sr k₀) = sr k₀)
    (hgen : ∀ g : DihedralGroup m,
      g ∈ Subgroup.closure ({sr j₀, σ (sr j₀)} : Set (DihedralGroup m))) :
    ∀ g, σ g = sr k₀ * g * sr k₀ := by
  have : NeZero m := ⟨fun h => by rw [h] at hm; exact Nat.not_odd_zero hm⟩
  obtain ⟨u, hu⟩ : ∃ u, σ (r 1) = r u := by
    rcases h : σ (r 1) with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      have h1 : orderOf (σ (r 1)) = orderOf (r (1 : ZMod m)) := MulEquiv.orderOf_eq σ _
      rw [h, orderOf_sr, orderOf_r_one] at h1
      obtain ⟨k, hk⟩ := hm
      omega
  have hr : ∀ i : ZMod m, σ (r i) = r (u * i) := by
    intro i
    have e : r i = r 1 ^ i.val := by rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [e, map_pow, hu, r_pow, ZMod.natCast_zmod_val]
  have hsr : ∀ i : ZMod m, σ (sr i) = sr (k₀ + u * (i - k₀)) := by
    intro i
    have e : sr i = sr k₀ * r (i - k₀) := by
      rw [sr_mul_r]
      congr 1
      ring
    rw [e, map_mul, hfix, hr, sr_mul_r]
  have hu2 : u * u = 1 := by
    have h := hσ2 (r 1)
    rw [hu, hr] at h
    exact DihedralGroup.r.inj h
  set d : ZMod m := (k₀ + u * (j₀ - k₀)) - j₀ with hd
  let H : Subgroup (DihedralGroup m) :=
    { carrier := {g | ∃ n : ZMod m, g = r (n * d) ∨ g = sr (j₀ + n * d)}
      one_mem' := ⟨0, Or.inl (by rw [zero_mul, r_zero])⟩
      mul_mem' := by
        rintro a b ⟨n, rfl | rfl⟩ ⟨n', rfl | rfl⟩
        · exact ⟨n + n', Or.inl (by rw [r_mul_r]; congr 1; ring)⟩
        · exact ⟨n' - n, Or.inr (by rw [r_mul_sr]; congr 1; ring)⟩
        · exact ⟨n + n', Or.inr (by rw [sr_mul_r]; congr 1; ring)⟩
        · exact ⟨n' - n, Or.inl (by rw [sr_mul_sr]; congr 1; ring)⟩
      inv_mem' := by
        rintro a ⟨n, rfl | rfl⟩
        · exact ⟨-n, Or.inl (by rw [inv_r]; congr 1; ring)⟩
        · exact ⟨n, Or.inr (by rw [inv_sr])⟩ }
  have hcl : Subgroup.closure ({sr j₀, σ (sr j₀)} : Set (DihedralGroup m)) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨0, Or.inr (by rw [zero_mul, add_zero])⟩
    · exact ⟨1, Or.inr (by rw [hsr, one_mul, hd]; congr 1; ring)⟩
  obtain ⟨n, hn⟩ := hcl (hgen (r 1))
  have hn1 : 1 = n * d := by
    rcases hn with hn | hn
    · exact DihedralGroup.r.inj hn
    · exact absurd hn (by simp)
  have hu1 : u = -1 := by
    have h1 : (n * (j₀ - k₀)) * (u - 1) = 1 := by
      calc (n * (j₀ - k₀)) * (u - 1) = n * d := by rw [hd]; ring
        _ = 1 := hn1.symm
    calc u = (n * (j₀ - k₀)) * (u - 1) * (u + 1) - 1 := by rw [h1]; ring
      _ = (n * (j₀ - k₀)) * (u * u - 1) - 1 := by ring
      _ = -1 := by rw [hu2]; ring
  intro g
  rcases g with i | i
  · rw [hr, hu1, sr_mul_r, sr_mul_sr]
    congr 1
    ring
  · rw [hsr, hu1, sr_mul_sr, r_mul_sr]
    congr 1
    ring

end CFSG.RankThree.GF2n
