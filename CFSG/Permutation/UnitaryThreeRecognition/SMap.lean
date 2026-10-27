module

public import CFSG.Permutation.UnitaryThreeRecognition.Basic

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

noncomputable def bruhatTriple (Q : Subgroup G) (a b : Ω) (s g : G) : G × G × G := by
  classical
  exact if h : ∃ xty : G × G × G, xty.1 ∈ Q ∧ xty.2.1 ∈ pairStab G a b ∧ xty.2.2 ∈ Q ∧
      g = xty.1 * xty.2.1 * s * xty.2.2 then Classical.choose h else (1, 1, 1)

noncomputable def sLeft (Q : Subgroup G) (a b : Ω) (s u : G) : G :=
  (bruhatTriple Q a b s (s * u * s)).1

noncomputable def sTor (Q : Subgroup G) (a b : Ω) (s u : G) : G :=
  (bruhatTriple Q a b s (s * u * s)).2.1

noncomputable def sRight (Q : Subgroup G) (a b : Ω) (s u : G) : G :=
  (bruhatTriple Q a b s (s * u * s)).2.2

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem bruhatTriple_spec {b : Ω} (hb : b ≠ a) {s : G} (hsb : s • b = a) {g : G}
    (hg : g • a ≠ a) :
    (bruhatTriple Q a b s g).1 ∈ Q ∧ (bruhatTriple Q a b s g).2.1 ∈ pairStab G a b ∧
      (bruhatTriple Q a b s g).2.2 ∈ Q ∧
      g = (bruhatTriple Q a b s g).1 * (bruhatTriple Q a b s g).2.1 * s *
        (bruhatTriple Q a b s g).2.2 := by
  classical
  have hex : ∃ xty : G × G × G, xty.1 ∈ Q ∧ xty.2.1 ∈ pairStab G a b ∧ xty.2.2 ∈ Q ∧
      g = xty.1 * xty.2.1 * s * xty.2.2 := by
    obtain ⟨x, hx, h, hh, y, hy, e⟩ := hQ.bruhat_exists hb hsb hg
    exact ⟨(x, h, y), hx, hh, hy, e⟩
  unfold bruhatTriple
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

theorem bruhatTriple_eq {b : Ω} (hb : b ≠ a) {s : G} (hsb : s • b = a) {g x h y : G}
    (hx : x ∈ Q) (hh : h ∈ pairStab G a b) (hy : y ∈ Q) (hg : g = x * h * s * y) :
    bruhatTriple Q a b s g = (x, h, y) := by
  have hga : g • a ≠ a := by
    intro e
    have e1 : (x * h * s * y) • a = x • (h • (s • a)) := by
      rw [mul_smul, hQ.smul_self hy, mul_smul, mul_smul]
    rw [← hg, e] at e1
    have e2 : h • (s • a) = a := by
      have := congrArg (x⁻¹ • ·) e1
      simp only [inv_smul_smul] at this
      rw [← this, hQ.smul_self (Q.inv_mem hx)]
    have e3 : s • a = a := by
      have := congrArg (h⁻¹ • ·) e2
      simp only [inv_smul_smul] at this
      rw [this, inv_smul_eq_iff, hh.1]
    exact hb (smul_left_cancel s (hsb.trans e3.symm))
  obtain ⟨h1, h2, h3, h4⟩ := hQ.bruhatTriple_spec hb hsb hga
  obtain ⟨e1, e2, e3⟩ := hQ.bruhat_unique hb hsb h1 h2 h3 hx hh hy (h4.symm.trans hg)
  ext <;> simp [e1, e2, e3]

section Swap

variable {b : Ω} (hb : b ≠ a) {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
include hb hsa hs2

omit hQ hb in
theorem swap_smul_b : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]

theorem conj_smul_ne {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) : (s * u * s) • a ≠ a := by
  have hsb := swap_smul_b hsa hs2
  rw [mul_smul, mul_smul, hsa]
  intro e
  have : u • b = b := by
    calc u • b = (s * s) • (u • b) := by rw [hs2, one_smul]
      _ = s • (s • (u • b)) := mul_smul _ _ _
      _ = b := by rw [e, hsa]
  exact hu1 (hQ.eq_one_of_smul_eq hu hb this)

theorem sLeft_mem {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) : sLeft Q a b s u ∈ Q :=
  (hQ.bruhatTriple_spec hb (swap_smul_b hsa hs2) (conj_smul_ne hQ hb hsa hs2 hu hu1)).1

theorem sTor_mem {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) : sTor Q a b s u ∈ pairStab G a b :=
  (hQ.bruhatTriple_spec hb (swap_smul_b hsa hs2) (conj_smul_ne hQ hb hsa hs2 hu hu1)).2.1

theorem sRight_mem {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) : sRight Q a b s u ∈ Q :=
  (hQ.bruhatTriple_spec hb (swap_smul_b hsa hs2)
    (conj_smul_ne hQ hb hsa hs2 hu hu1)).2.2.1

theorem conj_eq_bruhat {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) :
    s * u * s = sLeft Q a b s u * sTor Q a b s u * s * sRight Q a b s u :=
  (hQ.bruhatTriple_spec hb (swap_smul_b hsa hs2)
    (conj_smul_ne hQ hb hsa hs2 hu hu1)).2.2.2

theorem sFactors_eq {u x h y : G} (hx : x ∈ Q) (hh : h ∈ pairStab G a b)
    (hy : y ∈ Q) (e : s * u * s = x * h * s * y) :
    sLeft Q a b s u = x ∧ sTor Q a b s u = h ∧ sRight Q a b s u = y := by
  have := hQ.bruhatTriple_eq hb (swap_smul_b hsa hs2) hx hh hy e
  exact ⟨congrArg Prod.fst this, congrArg (fun z => z.2.1) this,
    congrArg (fun z => z.2.2) this⟩

theorem smul_sLeft {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) :
    s • (u • b) = sLeft Q a b s u • b := by
  have e := hQ.conj_eq_bruhat hb hsa hs2 hu hu1
  have h1 : (s * u * s) • a = s • (u • b) := by rw [mul_smul, mul_smul, hsa]
  have h2 : (sLeft Q a b s u * sTor Q a b s u * s * sRight Q a b s u) • a =
      sLeft Q a b s u • b := by
    rw [mul_smul, hQ.smul_self (hQ.sRight_mem hb hsa hs2 hu hu1), mul_smul, hsa, mul_smul,
      (hQ.sTor_mem hb hsa hs2 hu hu1).2]
  rw [← h1, e, h2]

theorem sLeft_ne_one {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) : sLeft Q a b s u ≠ 1 := by
  intro e
  have h := hQ.smul_sLeft hb hsa hs2 hu hu1
  rw [e, one_smul] at h
  have : u • b = a := by
    calc u • b = (s * s) • (u • b) := by rw [hs2, one_smul]
      _ = s • (s • (u • b)) := mul_smul _ _ _
      _ = a := by rw [h, swap_smul_b hsa hs2]
  exact hQ.smul_ne hu hb this

theorem sLeft_eq_iff {u v : G} (hu : u ∈ Q) (hu1 : u ≠ 1) (hv : v ∈ Q) :
    sLeft Q a b s u = v ↔ s • (u • b) = v • b := by
  rw [hQ.smul_sLeft hb hsa hs2 hu hu1]
  constructor
  · rintro rfl; rfl
  · intro e
    exact hQ.eq_of_smul_eq (hQ.sLeft_mem hb hsa hs2 hu hu1) hv hb e

theorem sLeft_sLeft {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) :
    sLeft Q a b s (sLeft Q a b s u) = u := by
  rw [hQ.sLeft_eq_iff hb hsa hs2 (hQ.sLeft_mem hb hsa hs2 hu hu1)
    (hQ.sLeft_ne_one hb hsa hs2 hu hu1) hu, ← hQ.smul_sLeft hb hsa hs2 hu hu1, smul_smul, hs2,
    one_smul]

theorem sFactors_inv {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) :
    sLeft Q a b s u⁻¹ = (sRight Q a b s u)⁻¹ ∧
      sTor Q a b s u⁻¹ = s * (sTor Q a b s u)⁻¹ * s ∧
      sRight Q a b s u⁻¹ = (sLeft Q a b s u)⁻¹ := by
  have hsb := swap_smul_b hsa hs2
  have e := hQ.conj_eq_bruhat hb hsa hs2 hu hu1
  have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, hs2]
  have hT : s * (sTor Q a b s u)⁻¹ * s ∈ pairStab G a b := by
    have := conj_mem_pairStab hsa hsb ((pairStab G a b).inv_mem (hQ.sTor_mem hb hsa hs2 hu hu1))
    rwa [hs] at this
  apply hQ.sFactors_eq hb hsa hs2
    (Q.inv_mem (hQ.sRight_mem hb hsa hs2 hu hu1)) hT
    (Q.inv_mem (hQ.sLeft_mem hb hsa hs2 hu hu1))
  have e' : s * u⁻¹ * s = (s * u * s)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hs, mul_assoc]
  rw [e', e]
  calc (sLeft Q a b s u * sTor Q a b s u * s * sRight Q a b s u)⁻¹
      = (sRight Q a b s u)⁻¹ * s⁻¹ * (sTor Q a b s u)⁻¹ * (sLeft Q a b s u)⁻¹ := by group
    _ = (sRight Q a b s u)⁻¹ * s * (sTor Q a b s u)⁻¹ * (sLeft Q a b s u)⁻¹ := by rw [hs]
    _ = (sRight Q a b s u)⁻¹ * s * (sTor Q a b s u)⁻¹ * (s * s) * (sLeft Q a b s u)⁻¹ := by
        rw [hs2, mul_one]
    _ = (sRight Q a b s u)⁻¹ * (s * (sTor Q a b s u)⁻¹ * s) * s *
          (sLeft Q a b s u)⁻¹ := by group

end Swap

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
