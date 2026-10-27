module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The uniform fixed centralizer of the reflections in the PSL₂ branch

The linear equation-(10) data needs, for the two reflection classes of the
ambient Sylow `2`-subgroup, the uniform identity `C_U(r) = B` (equation
(5) in its reflection-uniform form).  This module derives it from the two
source facts of equations (5) and (9) of
`refs/bender-dihedral-sylow.tex`:

* equation (5): the fixed part `F = C_{F(U)}(s)` of the Fitting subgroup
  has normalizer `N_G(F) = M`, which upgrades the decomposition's
  `B = C_{U∩M}(s)` to the full centralizer `C_U(s)`; and
* equation (9): `S0 = C_S(U)`, which makes any two reflections
  `r, s ∈ S \ S0` congruent modulo `S0 ≤ C_G(U)`, so `C_U(r) = C_U(s)`.

The two source facts enter as the exact needed identities (`hS0centU` and
`hNF`); the equality `C_U(r) = B` itself is proved, not assumed.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## Membership in `centralizerIn` -/

/-- Membership in the centralizer of `s` inside `X`. -/
private theorem mem_centralizerIn_iff' {G : Type u} [Group G]
    (X : Subgroup G) (s c : G) :
    c ∈ centralizerIn X s ↔ c ∈ X ∧ s * c * s⁻¹ = c := by
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    have hcs : s * c = c * s :=
      (Subgroup.mem_centralizer_iff (g := c) (s := ({s} : Set G))).1 hc.2 s (by simp)
    calc
      s * c * s⁻¹ = c * s * s⁻¹ := by rw [hcs]
      _ = c := by simp
  · intro hc
    refine ⟨hc.1, ?_⟩
    change c ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = s := by simpa using hz
    rw [hzs]
    have hcs : s * c = c * s := by
      calc
        s * c = (s * c * s⁻¹) * s := by group
        _ = c * s := by rw [hc.2]
    exact hcs

/-! ## The index-two reflection congruence -/

/-- The cyclic subgroup `S0` has index two in `S`. -/
private lemma S0_index_of_centralizerSetup {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    ((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)).index = 2 := by
  classical
  have hmap : (c.S0.subgroupOf (c.S : Subgroup G)).map (c.S : Subgroup G).subtype = c.S0 := by
    ext y
    constructor
    · intro hy
      rcases (Subgroup.mem_map.mp hy) with ⟨x, hx, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp hx)
    · intro hy
      refine Subgroup.mem_map.mpr ⟨⟨y, c.S0_le_S hy⟩, ?_, rfl⟩
      exact (Subgroup.mem_subgroupOf (H := c.S0) (K := (c.S : Subgroup G))
        (h := ⟨y, c.S0_le_S hy⟩)).mpr hy
  have h1 := Subgroup.card_mul_index (c.S0.subgroupOf (c.S : Subgroup G))
  have hc : Nat.card ↥(c.S0.subgroupOf (c.S : Subgroup G)) = Nat.card ↥c.S0 := by
    have hcs := Subgroup.card_subtype (c.S : Subgroup G) (c.S0.subgroupOf (c.S : Subgroup G))
    rw [hmap] at hcs
    exact hcs.symm
  rw [hc, c.S_index_two] at h1
  have hpos : 0 < Nat.card ↥c.S0 := Nat.card_pos
  exact Nat.mul_right_cancel hpos (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h1)

/-- The product of two elements of `S \ S0` lies in `S0` (index two). -/
private lemma reflection_product_mem_S0 {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {r s : G} (hrS : r ∈ (c.S : Subgroup G)) (hr0 : r ∉ c.S0)
    (hsS : s ∈ (c.S : Subgroup G)) (hs0 : s ∉ c.S0) :
    r * s ∈ c.S0 := by
  classical
  let K : Subgroup (↥(c.S : Subgroup G)) :=
    (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hiff := Subgroup.mul_mem_iff_of_index_two (S0_index_of_centralizerSetup c)
    (G := ↥(c.S : Subgroup G)) (H := K) (a := ⟨r, hrS⟩) (b := ⟨s, hsS⟩)
  have hmem : (⟨r, hrS⟩ : ↥(c.S : Subgroup G)) * ⟨s, hsS⟩ ∈ K := by
    rw [hiff]
    dsimp [K]
    simp [Subgroup.mem_subgroupOf, hr0, hs0]
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

/-- For `u ∈ U`, centralizing one reflection of `S \ S0` is equivalent to
centralizing any other: two reflections differ by an element of `S0`, and
`S0 ≤ C_G(U)`. -/
private lemma reflection_fixed_subgroup_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hS0centU : (c.S0 : Subgroup G) ≤ Subgroup.centralizer (c.U : Set G))
    {r s : G} (hrS : r ∈ (c.S : Subgroup G)) (hr0 : r ∉ c.S0)
    (hsS : s ∈ (c.S : Subgroup G)) (hs0 : s ∉ c.S0) :
    centralizerIn c.U r = centralizerIn c.U s := by
  classical
  have hw : r * s ∈ c.S0 := reflection_product_mem_S0 c hrS hr0 hsS hs0
  have hwC : r * s ∈ Subgroup.centralizer (c.U : Set G) := hS0centU hw
  ext u
  constructor
  · intro hu
    rw [mem_centralizerIn_iff'] at hu ⊢
    refine ⟨hu.1, ?_⟩
    have hwcom : (r * s) * (u : G) = (u : G) * (r * s) :=
      ((Subgroup.mem_centralizer_iff (g := r * s) (s := (c.U : Set G))).1 hwC (u : G) hu.1).symm
    have hwu : (r * s) * (u : G) * (r * s)⁻¹ = (u : G) := by
      calc
        (r * s) * (u : G) * (r * s)⁻¹ = (u : G) * (r * s) * (r * s)⁻¹ := by rw [hwcom]
        _ = (u : G) := by group
    have hru : r⁻¹ * (u : G) * r = (u : G) := by
      calc
        r⁻¹ * (u : G) * r = r⁻¹ * (r * (u : G) * r⁻¹) * r := by rw [hu.2]
        _ = (u : G) := by group
    calc
      s * (u : G) * s⁻¹ = (r⁻¹ * (r * s)) * (u : G) * (r⁻¹ * (r * s))⁻¹ := by group
      _ = r⁻¹ * ((r * s) * (u : G) * (r * s)⁻¹) * r := by group
      _ = r⁻¹ * (u : G) * r := by rw [hwu]
      _ = (u : G) := hru
  · intro hu
    rw [mem_centralizerIn_iff'] at hu ⊢
    refine ⟨hu.1, ?_⟩
    have hw2 : s * r ∈ c.S0 := reflection_product_mem_S0 c hsS hs0 hrS hr0
    have hw2C : s * r ∈ Subgroup.centralizer (c.U : Set G) := hS0centU hw2
    have hw2com : (s * r) * (u : G) = (u : G) * (s * r) :=
      ((Subgroup.mem_centralizer_iff (g := s * r) (s := (c.U : Set G))).1 hw2C (u : G) hu.1).symm
    have hw2u : (s * r) * (u : G) * (s * r)⁻¹ = (u : G) := by
      calc
        (s * r) * (u : G) * (s * r)⁻¹ = (u : G) * (s * r) * (s * r)⁻¹ := by rw [hw2com]
        _ = (u : G) := by group
    have hsu : s⁻¹ * (u : G) * s = (u : G) := by
      calc
        s⁻¹ * (u : G) * s = s⁻¹ * (s * (u : G) * s⁻¹) * s := by rw [hu.2]
        _ = (u : G) := by group
    calc
      r * (u : G) * r⁻¹ = (s⁻¹ * (s * r)) * (u : G) * (s⁻¹ * (s * r))⁻¹ := by group
      _ = s⁻¹ * ((s * r) * (u : G) * (s * r)⁻¹) * s := by group
      _ = s⁻¹ * (u : G) * s := by rw [hw2u]
      _ = (u : G) := hsu

/-! ## Equation (5): the fixed centralizer `B = C_U(s)` -/

/-- Equation (5) upgrades the decomposition's `B = C_{U∩M}(s)` to the full
centralizer `C_U(s)`: an element of `C_U(s)` normalizes the fixed part
`F = C_{F(U)}(s)` of the Fitting subgroup, hence lies in `N_G(F) = M`
(the equation-(5) normalizer identity `hNF`), so it belongs to `U ∩ M`
and centralizes `s`. -/
private lemma centralizer_U_fixed_eq_B {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (s : G) (B : Subgroup G)
    (hB_eq : B = centralizerIn (c.U ⊓ w.M) (s : G))
    (hNF : Subgroup.normalizer (centralizerIn c.FU (s : G) : Set G) = w.M) :
    centralizerIn c.U s = B := by
  classical
  apply le_antisymm
  · intro u hu
    rw [mem_centralizerIn_iff'] at hu
    have huU : u ∈ c.U := hu.1
    have huC : s * u * s⁻¹ = u := hu.2
    have huH : u ∈ c.H := by
      rcases Subgroup.mem_map.mp huU with ⟨p, hp, rfl⟩
      exact p.2
    have huNorm : u ∈ Subgroup.normalizer (centralizerIn c.FU (s : G) : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro f
      constructor
      · intro hf
        change f ∈ centralizerIn c.FU (s : G) at hf
        change u * f * u⁻¹ ∈ centralizerIn c.FU (s : G)
        rw [mem_centralizerIn_iff'] at hf ⊢
        refine ⟨?_, ?_⟩
        · exact (centralizerSetup_FU_isNormalIn_H c).2 u huH f hf.1
        · have huCinv : s * u⁻¹ * s⁻¹ = u⁻¹ := by
            calc
              s * u⁻¹ * s⁻¹ = (s * u * s⁻¹)⁻¹ := by group
              _ = u⁻¹ := by rw [huC]
          calc
            s * (u * f * u⁻¹) * s⁻¹ = (s * u * s⁻¹) * (s * f * s⁻¹) * (s * u⁻¹ * s⁻¹) := by group
            _ = u * f * u⁻¹ := by rw [huC, hf.2, huCinv]
      · intro huf
        change u * f * u⁻¹ ∈ centralizerIn c.FU (s : G) at huf
        change f ∈ centralizerIn c.FU (s : G)
        rw [mem_centralizerIn_iff'] at huf ⊢
        refine ⟨?_, ?_⟩
        · have huHinv : u⁻¹ ∈ c.H := c.H.inv_mem huH
          have hconj : u⁻¹ * (u * f * u⁻¹) * (u⁻¹)⁻¹ ∈ c.FU :=
            (centralizerSetup_FU_isNormalIn_H c).2 u⁻¹ huHinv (u * f * u⁻¹) huf.1
          have hconj' : u⁻¹ * (u * f * u⁻¹) * u ∈ c.FU := by
            simpa using hconj
          rwa [show u⁻¹ * (u * f * u⁻¹) * u = f by group] at hconj'
        · have huCinv : s * u⁻¹ * s⁻¹ = u⁻¹ := by
            calc
              s * u⁻¹ * s⁻¹ = (s * u * s⁻¹)⁻¹ := by group
              _ = u⁻¹ := by rw [huC]
          calc
            s * f * s⁻¹ = (s * u⁻¹ * s⁻¹) * (s * (u * f * u⁻¹) * s⁻¹) * (s * u * s⁻¹) := by group
            _ = u⁻¹ * (u * f * u⁻¹) * u := by rw [huCinv, huf.2, huC]
            _ = f := by group
    have huM : u ∈ w.M := by
      rw [hNF] at huNorm
      exact huNorm
    rw [hB_eq]
    rw [mem_centralizerIn_iff']
    exact ⟨⟨huU, huM⟩, huC⟩
  · intro u hu
    rw [hB_eq] at hu
    rw [mem_centralizerIn_iff'] at hu ⊢
    exact ⟨hu.1.1, hu.2⟩

/-! ## The uniform reflection identity -/

/-- In the PSL₂ component branch, every reflection of the ambient Sylow
`2`-subgroup has the same centralizer in `U = O(H)`, equal to the fixed
part `B = C_{U∩M}(s)` of the equation-(1)--(3) decomposition.

The source derives this in two steps (`refs/bender-dihedral-sylow.tex`,
L666--682 and L805--815): equation (5) upgrades `B` to the full
centralizer `C_U(s)` via `N_G(F) = M` for `F = C_{F(U)}(s)`, and the
equation-(9) endpoint `S ⊆ E` with `S0 = C_S(U)` makes all reflections of
`S \ S0` congruent modulo `S0 ≤ C_G(U)`.  The two source facts enter as
the exact needed identities `hS0centU` and `hNF`; `hSleE` is the
equation-(9) source endpoint. -/
public theorem secondCase_psl2_uniform_reflection_fixed
    {G : Type u} [Group G] [Finite G]
    (_hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E)
    (B : Subgroup G)
    (hB_eq : B = centralizerIn (c.U ⊓ w.M) (s : G))
    (hsS : (s : G) ∈ (c.S : Subgroup G))
    (hsS0 : (s : G) ∉ c.S0)
    (_hSleE : (c.S : Subgroup G) ≤ d.E)
    (hS0centU : (c.S0 : Subgroup G) ≤ Subgroup.centralizer (c.U : Set G))
    (hNF : Subgroup.normalizer (centralizerIn c.FU (s : G) : Set G) = w.M) :
    ∀ r : G, r ∈ (c.S : Subgroup G) → r ∉ c.S0 →
      centralizerIn c.U r = B := by
  classical
  intro r hrS hr0
  have hcong : centralizerIn c.U r = centralizerIn c.U (s : G) :=
    reflection_fixed_subgroup_eq c hS0centU hrS hr0 hsS hsS0
  have hsB : centralizerIn c.U (s : G) = B :=
    centralizer_U_fixed_eq_B c w (s : G) B hB_eq hNF
  rw [hcong, hsB]

end CFSG.GorensteinWalter
