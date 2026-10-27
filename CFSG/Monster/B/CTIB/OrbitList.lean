module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Set.Card
public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbitList
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Monster.B.CTIB

open CFSG.Monster.B.CTIB.Kernel

variable {G X : Type*} [Group G] [MulAction G X] {act : ℕ → ℕ → ℕ} {ngen : ℕ}
  {valid : ℕ → Bool} {root size : ℕ} {dec : ℕ → X} {gens : ℕ → G}

theorem mem_orbit_of_reach
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a) {b : ℕ}
    (h : Reach act ngen valid root b) :
    dec b ∈ MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root) := by
  induction h with
  | root => exact MulAction.mem_orbit_self _
  | step k hk ha hb _ hab ih =>
    obtain ⟨g, hg0⟩ := ih
    have hg : g • dec root = _ := hg0
    have hmem : gens k ∈ Subgroup.closure (gens '' {k | k < ngen}) :=
      Subgroup.subset_closure ⟨k, hk, rfl⟩
    rcases hab with rfl | e
    · refine ⟨⟨gens k, hmem⟩ * g, ?_⟩
      change ((⟨gens k, hmem⟩ : Subgroup.closure (gens '' {k | k < ngen})) * g) • dec root = _
      rw [mul_smul]
      change gens k • (g • dec root) = _
      rw [hg, hact k hk _ ha]
    · refine ⟨(⟨gens k, hmem⟩ : Subgroup.closure (gens '' {k | k < ngen}))⁻¹ * g, ?_⟩
      have e' := hact k hk _ hb
      rw [e] at e'
      change ((⟨gens k, hmem⟩ : Subgroup.closure (gens '' {k | k < ngen}))⁻¹ * g) • dec root = _
      rw [mul_smul]
      change (gens k)⁻¹ • (g • dec root) = _
      rw [hg, e', inv_smul_smul]

theorem orbit_of_orbitList (h : OrbitList act ngen valid root size)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    (hinj : ∀ a b, valid a = true → valid b = true → dec a = dec b → a = b) :
    ∃ pts : List ℕ, pts.length = size ∧ (∀ p ∈ pts, valid p = true ∧ root ≤ p) ∧
      MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root) =
        dec '' {p | p ∈ pts} ∧
      (MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root)).ncard = size ∧
      valid root = true := by
  obtain ⟨pts, hlen, hnd, hroot, hval, hcl, hreach⟩ := h
  set H := Subgroup.closure (gens '' {k | k < ngen})
  set S : Set X := dec '' {p | p ∈ pts}
  have hSfin : S.Finite := (List.finite_toSet pts).image dec
  have hgen : ∀ k < ngen, Set.MapsTo (gens k • ·) S S := by
    rintro k hk _ ⟨p, hp, rfl⟩
    exact ⟨act k p, hcl p hp k hk, hact k hk p (hval p hp).1⟩
  have hinv : ∀ g : G, Set.MapsTo (g • ·) S S → Set.MapsTo (g⁻¹ • ·) S S := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ :=
      ((hSfin.injOn_iff_bijOn_of_mapsTo hg).1 (MulAction.injective g).injOn).surjOn hx
    simpa only [inv_smul_smul] using hy
  have hH : ∀ g ∈ H, Set.MapsTo (g • ·) S S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      exact hgen k hk
    | one =>
      intro x hx
      simpa only [one_smul] using hx
    | mul a b _ _ ha hb =>
      intro x hx
      simpa only [mul_smul] using ha (hb hx)
    | inv a _ ha => exact hinv a ha
  have horb : MulAction.orbit H (dec root) = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩
      exact hH g g.2 ⟨root, hroot, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact mem_orbit_of_reach hact (hreach p hp)
  refine ⟨pts, hlen, hval, horb, ?_, (hval root hroot).1⟩
  rw [horb]
  change (dec '' {p | p ∈ pts}).ncard = size
  rw [Set.InjOn.ncard_image (s := {p | p ∈ pts}) (f := dec)
    (fun a ha b hb e => hinj a b (hval a ha).1 (hval b hb).1 e)]
  have e : {p | p ∈ pts} = ↑pts.toFinset := by
    ext p
    simp
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]

end CFSG.Monster.B.CTIB

end
