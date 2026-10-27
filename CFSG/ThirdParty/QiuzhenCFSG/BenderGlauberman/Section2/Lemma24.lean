module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Lemma 2.4

The statement of Lemma 2.4: for `χ ∈ ±Irr(G)`, `χ = Σ_{ν∈B(χ)} (χ,ν̃)_G·ν`
on `T`, and `χ ≡ Σ_{ν∈B(χ)} ν` on `U`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section2

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- A member of an orbit: `ν ∈ orbit ν`. -/
private lemma orbit_self_mem [Fintype ↥(LambdaHom c.H0 c.U)]
    (ν : ClassFunction (↥c.H0)) : ν ∈ orbit c.H0 c.U ν := by
  classical
  refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
  have h1 : LambdaChar (1 : LambdaHom c.H0 c.U).1 = (1 : ClassFunction (↥c.H0)) := by
    ext x
    simp [LambdaChar]
  rw [h1, one_mul]

/-- Orbits are equal-or-disjoint: `μ ∈ orbit ν` implies `orbit μ = orbit ν`. -/
private lemma orbit_eq_of_mem [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν μ : ClassFunction (↥c.H0)} (hμ : μ ∈ orbit c.H0 c.U ν) :
    orbit c.H0 c.U μ = orbit c.H0 c.U ν := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l₀, hl₀, hEq₀⟩
  apply Finset.ext
  intro ψ
  constructor
  · intro hψ
    rcases (Finset.mem_image.mp hψ) with ⟨l, hl, rfl⟩
    refine Finset.mem_image.mpr ⟨l * l₀, Finset.mem_univ _, ?_⟩
    rw [← hEq₀]
    ext x
    simp [LambdaChar, mul_assoc]
  · intro hψ
    rcases (Finset.mem_image.mp hψ) with ⟨l, hl, rfl⟩
    refine Finset.mem_image.mpr ⟨l * l₀⁻¹, Finset.mem_univ _, ?_⟩
    ext x
    simp [LambdaChar, mul_assoc]
    have hμx : μ x = (l₀.1 x : ℂ) * ν x := (congrFun hEq₀ x).symm
    rw [hμx]
    have hne : (l₀.1 x : ℂ) ≠ 0 := unit_val_ne_zero (l₀.1 x)
    rw [← mul_assoc, inv_mul_cancel₀ hne]
    ring

/-- The set of `Λ`-orbits of the irreducible characters of `H0`. -/
private noncomputable def orbitSet (c : Hyp11 G) (_h12 : Hyp12 c) :
    Finset (Finset (ClassFunction (↥c.H0))) := by
  classical
  exact (Finset.univ : Finset (Irr (↥c.H0))).image
    (fun ν : Irr (↥c.H0) => orbit c.H0 c.U ν.1)

/-- An orbit in `orbitSet` is nonempty. -/
private lemma orbitSet_mem_nonempty (c : Hyp11 G) (_h12 : Hyp12 c)
    {L : Finset (ClassFunction (↥c.H0))} (hL : L ∈ orbitSet c _h12) : L.Nonempty := by
  rcases Finset.mem_image.mp hL with ⟨ν, hν, hLν⟩
  refine ⟨ν.1, ?_⟩
  rw [← hLν]
  exact orbit_self_mem c ν.1

/-- A system of orbit representatives for the `Λ`-orbits of `Irr(H0)`. -/
public lemma exists_orbit_reps (c : Hyp11 G) (h12 : Hyp12 c) :
    ∃ (ι : Type u) (_ : Fintype ι) (rep : ι → ClassFunction (↥c.H0)),
      (∀ i : ι, IsIrreducibleCharacter (rep i)) ∧
      (∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i)) := by
  classical
  let ι : Type u := {L : Finset (ClassFunction (↥c.H0)) // L ∈ orbitSet c h12}
  let rep : ι → ClassFunction (↥c.H0) := fun L =>
    Classical.choose (orbitSet_mem_nonempty c h12 L.2)
  refine ⟨ι, inferInstance, rep, ?_, ?_⟩
  · intro L
    rcases Finset.mem_image.mp L.2 with ⟨ν, hν, hLν⟩
    have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSet_mem_nonempty c h12 L.2)
    have hνL' : rep L ∈ orbit c.H0 c.U ν.1 := hLν ▸ hspec
    exact orbit_mem_isIrreducible c.H0 c.U ν.2 hνL'
  · intro ν
    refine ⟨⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩, ?_, ?_⟩
    · have hspec : rep ⟨orbit c.H0 c.U ν.1,
          Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩ ∈ orbit c.H0 c.U ν.1 :=
        Classical.choose_spec (orbitSet_mem_nonempty c h12
          (Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩ :
            orbit c.H0 c.U ν.1 ∈ orbitSet c h12))
      change ν.1 ∈ orbit c.H0 c.U
        (rep ⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩)
      rw [orbit_eq_of_mem c hspec]
      exact orbit_self_mem c ν.1
    · intro L hLmem
      have hEqOrbit : L.1 = orbit c.H0 c.U ν.1 := by
        have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSet_mem_nonempty c h12 L.2)
        rcases Finset.mem_image.mp L.2 with ⟨μ, hμ, hLμ⟩
        have ho1 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U ν.1 :=
          (orbit_eq_of_mem c hLmem).symm
        have ho2 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U μ.1 := by
          rw [← hLμ] at hspec
          exact orbit_eq_of_mem c hspec
        have ho3 : orbit c.H0 c.U μ.1 = L.1 := hLμ
        rw [← ho1, ho2, ho3]
      apply Subtype.ext
      exact hEqOrbit

/-- The sum of the values of the irreducible characters in the fiber of a
representative is the orbit sum of that representative. -/
private lemma orbit_sum_fiber_eq_orbitSum (c : Hyp11 G) (_h12 : Hyp12 c)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i))
    (i : ι) (x : ↥c.H0) :
    (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i), ν.1 x) =
      orbitSum c.H0 c.U (rep i) x := by
  classical
  change (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i), ν.1 x) =
    ∑ μ ∈ orbit c.H0 c.U (rep i), μ x
  symm
  refine Finset.sum_bij (fun μ hμ =>
      (⟨μ, orbit_mem_isIrreducible c.H0 c.U (hrep_irr i) hμ⟩ :
        Irr (↥c.H0))) ?_ ?_ ?_ ?_
  · intro μ hμ
    have hgi : Classical.choose
        (hrep ⟨μ, orbit_mem_isIrreducible c.H0 c.U (hrep_irr i) hμ⟩) = i := by
      exact ((Classical.choose_spec
        (hrep ⟨μ, orbit_mem_isIrreducible c.H0 c.U (hrep_irr i) hμ⟩)).2 i hμ).symm
    simp [hgi]
  · intro a ha b hb hEq
    exact congrArg Subtype.val hEq
  · intro ν hν
    have hmem : ν.1 ∈ orbit c.H0 c.U (rep (Classical.choose (hrep ν))) :=
      (Classical.choose_spec (hrep ν)).1
    have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
    have hνi : ν.1 ∈ orbit c.H0 c.U (rep i) := by rwa [hgi] at hmem
    refine ⟨ν.1, hνi, ?_⟩
    exact Subtype.ext rfl
  · intro μ hμ
    rfl

/-- Regrouping the coefficients of the orbit representatives: the sum over
`ν` of `a(i(ν))·ν(x)` equals the sum over the representatives `i` of
`a i` times the orbit sum `r(Λ rep i)(x)`. -/
private lemma rep_coeff_sum_eq_orbit_sums (c : Hyp11 G) (h12 : Hyp12 c)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i))
    (a : ι → ℂ) (x : ↥c.H0) :
    (∑ ν : Irr (↥c.H0), a (Classical.choose (hrep ν)) * ν.1 x) =
      ∑ i : ι, a i * orbitSum c.H0 c.U (rep i) x := by
  classical
  have hfib : (∑ ν : Irr (↥c.H0), a (Classical.choose (hrep ν)) * ν.1 x) =
      ∑ i : ι, ∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i),
        a (Classical.choose (hrep ν)) * ν.1 x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := fun ν : Irr (↥c.H0) => Classical.choose (hrep ν))
      (f := fun ν => a (Classical.choose (hrep ν)) * ν.1 x)
      (by intro ν hν; simp)
  rw [hfib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i),
        a (Classical.choose (hrep ν)) * ν.1 x)
        = (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i),
            a i * ν.1 x) := by
          refine Finset.sum_congr rfl ?_
          intro ν hν
          have hgi : Classical.choose (hrep ν) = i := (Finset.mem_filter.mp hν).2
          rw [hgi]
    _ = a i * (∑ ν ∈ Finset.univ.filter (fun ν : Irr (↥c.H0) => Classical.choose (hrep ν) = i), ν.1 x) := by
          rw [Finset.mul_sum]
    _ = a i * orbitSum c.H0 c.U (rep i) x := by
          rw [orbit_sum_fiber_eq_orbitSum c h12 rep hrep_irr hrep i x]

set_option maxHeartbeats 8000000 in
/-- Lemma 2.4, `T` part: on `T = H0 \ U`, the Fourier expansion of
Lemma 1.7(ii) reduces to `χ = Σ_ν (χ,ν̃_ν)·ν` for any system of orbit
representatives (the representative coefficients regroup into orbit sums,
which vanish on `T` by Lemma 1.7(i)). -/
private lemma fourier_on_T (c : Hyp11 G) (h12 : Hyp12 c)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i))
    (χ : ClassFunction G) (hχ : IsGeneralizedCharacter χ)
    (x : ↥c.H0) (hx : (x : G) ∉ c.U) :
    χ (x : G) =
      (∑ ν : Irr (↥c.H0), scalarProduct G χ (tildeNu c h12 ν) * ν.1 x) := by
  classical
  have hii := lemma_1_7_ii c.H0 c.U rep hrep_irr hrep χ hχ x
  change χ (x : G) =
      (∑ i : ι, scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) (rep i) *
          orbitSum c.H0 c.U (rep i) x) +
      (∑ ν : Irr (↥c.H0),
        scalarProduct G χ (inducedClassFunction c.H0
          (ν.1 - rep (Classical.choose (hrep ν)))) * ν.1 x) at hii
  have hsum1 : (∑ i : ι, scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) (rep i) *
      orbitSum c.H0 c.U (rep i) x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [lemma_1_7_i c.H0 c.U (U_normal_subgroupOf c h12) (lambda_hcomm c h12) (rep i) x hx]
    simp
  let cν : Irr (↥c.H0) → ℂ := fun ν => scalarProduct G χ (tildeNu c h12 ν)
  let a : ι → ℂ := fun i => scalarProduct G χ (tildeNu c h12 ⟨rep i, hrep_irr i⟩)
  have hcoef (ν : Irr (↥c.H0)) :
      scalarProduct G χ (inducedClassFunction c.H0
        (ν.1 - rep (Classical.choose (hrep ν)))) = cν ν - a (Classical.choose (hrep ν)) := by
    have hL : ν.1 ∈ orbit c.H0 c.U (rep (Classical.choose (hrep ν))) :=
      (Classical.choose_spec (hrep ν)).1
    have hind : inducedClassFunction c.H0 (ν.1 - rep (Classical.choose (hrep ν))) =
        tildeNu c h12 ν - tildeNu c h12
          ⟨rep (Classical.choose (hrep ν)), hrep_irr (Classical.choose (hrep ν))⟩ := by
      exact tildeNu_ind c h12
        (μ := ν)
        (ν := ⟨rep (Classical.choose (hrep ν)), hrep_irr (Classical.choose (hrep ν))⟩) hL
    rw [hind, scalarProduct_sub_right]
  have hsum0 : (∑ ν : Irr (↥c.H0), a (Classical.choose (hrep ν)) * ν.1 x) = 0 := by
    rw [rep_coeff_sum_eq_orbit_sums c h12 rep hrep_irr hrep a x]
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [lemma_1_7_i c.H0 c.U (U_normal_subgroupOf c h12) (lambda_hcomm c h12) (rep i) x hx]
    simp
  calc
    χ (x : G) =
        (∑ i : ι, scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) (rep i) *
            orbitSum c.H0 c.U (rep i) x) +
        (∑ ν : Irr (↥c.H0),
          scalarProduct G χ (inducedClassFunction c.H0
            (ν.1 - rep (Classical.choose (hrep ν)))) * ν.1 x) := hii
    _ = ∑ ν : Irr (↥c.H0), (cν ν - a (Classical.choose (hrep ν))) * ν.1 x := by
          rw [hsum1, zero_add]
          refine Finset.sum_congr rfl ?_
          intro ν hν
          rw [hcoef ν]
    _ = ∑ ν : Irr (↥c.H0), (cν ν * ν.1 x - a (Classical.choose (hrep ν)) * ν.1 x) := by
          refine Finset.sum_congr rfl ?_
          intro ν hν
          rw [sub_mul]
    _ = (∑ ν : Irr (↥c.H0), cν ν * ν.1 x) -
          (∑ ν : Irr (↥c.H0), a (Classical.choose (hrep ν)) * ν.1 x) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ ν : Irr (↥c.H0), cν ν * ν.1 x := by
          rw [hsum0]
          simp

/-- `t·u ∉ U`, so `t·u ∈ T = H0 \ U`. -/
private lemma t_mul_u_not_mem_U (c : Hyp11 G) (u : ↥c.U) :
    c.t * (u : G) ∉ c.U := by
  intro htu
  have hmul : (c.t * (u : G)) * (u : G)⁻¹ ∈ c.U :=
    c.U.mul_mem htu (c.U.inv_mem u.2)
  have ht : c.t ∈ c.U := by
    have hEq : c.t = (c.t * (u : G)) * (u : G)⁻¹ := by group
    rw [hEq]
    exact hmul
  exact t_not_mem_U c ht

/-- `t` is an involution of `H0`. -/
private lemma tH0_isInvolution (c : Hyp11 G) : IsInvolution (tH0 c) := by
  constructor
  · intro h1
    exact c.t_involution.1 (by simpa [tH0] using (Subtype.ext_iff.mp h1))
  · simpa [tH0] using t_H0_sq c

/-- `u ∈ U` centralizes `t` (since `U ≤ H = C_G(t)`). -/
private lemma u_mem_centralizer_t (c : Hyp11 G) (u : ↥c.U) :
    (u : G) ∈ centralizerIn (⊤ : Subgroup G) c.t := by
  have hUleH : c.U ≤ c.H := Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have huH : (u : G) ∈ c.H := hUleH u.2
  have huc : (u : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact huH
  simpa [centralizerIn] using Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, huc⟩

/-- `u ∈ U` centralizes `t` as an element of `H0`. -/
private lemma u_mem_centralizer_tH0 (c : Hyp11 G) (u : ↥c.U) (hu : (u : G) ∈ c.H0) :
    ⟨(u : G), hu⟩ ∈ centralizerIn (⊤ : Subgroup (↥c.H0)) (tH0 c) := by
  rw [centralizerIn]
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (t_central_H0' c ⟨(u : G), hu⟩).symm⟩

/-- For `u ∈ U = O(H)`, `2` is coprime to the order of `u`. -/
private lemma u_orderOf_coprime_two (c : Hyp11 G) (u : ↥c.U) :
    Nat.Coprime 2 (orderOf (u : G)) := by
  classical
  have hcopU : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hordU : orderOf (u : G) ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨u, u.2⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨u, u.2⟩ : ↥c.U)]
    have hdvd : orderOf (⟨u, u.2⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨u, u.2⟩)
    rwa [← Nat.card_eq_fintype_card] at hdvd
  exact (Nat.Coprime.coprime_dvd_left hordU (Nat.Coprime.symm hcopU)).symm

/-- Lemma 1.6 for an irreducible character of `H0`: `ν(t·u) ≡ ν(u)`
(mod 2), for `u ∈ U`. -/
private lemma nu_congr_tu_u (c : Hyp11 G) (_h12 : Hyp12 c) (ν : Irr (↥c.H0))
    (u : ↥c.U) (hu : (u : G) ∈ c.H0) :
    CongruentModTwo (ν.1 ⟨c.t * (u : G), c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) hu⟩)
      (ν.1 ⟨(u : G), hu⟩) := by
  classical
  let uH0 : ↥c.H0 := ⟨(u : G), hu⟩
  have hνg : IsGeneralizedCharacter ν.1 :=
    ⟨ν.1, 0, isCharacter_of_isIrreducibleCharacter ν.2, isCharacter_zero, by simp⟩
  have hcop' : Nat.Coprime 2 (orderOf uH0) := by
    have hordEq : orderOf (u : G) = orderOf uH0 := by
      simp [uH0]
    rw [← hordEq]
    exact u_orderOf_coprime_two c u
  have hcong := lemma_1_6 (G := ↥c.H0) (φ := ν.1) (hφ := hνg) (t := tH0 c) (u := uH0)
    (ht := tH0_isInvolution c)
    (u_mem_centralizer_tH0 c u hu) hcop'
  simpa [uH0, tH0] using hcong

/-- Lemma 1.6 for `χ`: `χ(u) ≡ χ(t·u)` (mod 2), for `u ∈ U`. -/
private lemma cong_u_tu (c : Hyp11 G) (_h12 : Hyp12 c) (χ : ClassFunction G)
    (hχ : IsGeneralizedCharacter χ) (u : ↥c.U) :
    CongruentModTwo (χ (u : G)) (χ (c.t * (u : G))) := by
  classical
  exact CongruentModTwo.symm
    (lemma_1_6 (G := G) (φ := χ) (hφ := hχ) (t := c.t) (u := (u : G)) (ht := c.t_involution)
      (u_mem_centralizer_t c u)
      (u_orderOf_coprime_two c u))

/-- Character values of an irreducible character are algebraic integers. -/
private lemma character_value_isIntegral_irr {G : Type u} [Group G] [Fintype G]
    (ν : Irr G) (g : G) : IsIntegral ℤ (ν.1 g) := by
  rcases ν.2 with ⟨n, ρ, hρ, hνeq⟩
  simpa [hνeq] using character_value_isIntegral ρ g

/-- `±1` are algebraic integers. -/
private lemma pm_one_isIntegral {c : ℂ} (h : c = 1 ∨ c = -1) : IsIntegral ℤ c := by
  rcases h with h1 | hm1
  · rw [h1]
    exact isIntegral_one
  · rw [hm1]
    exact IsIntegral.neg isIntegral_one

/-- Multiplying by an odd integer preserves the mod-2 congruence class:
`±x ≡ x` (mod 2) for an algebraic integer `x`. -/
private lemma pm_one_mul_congr {c x : ℂ} (h : c = 1 ∨ c = -1) (hx : IsIntegral ℤ x) :
    CongruentModTwo (c * x) x := by
  rcases h with h1 | hm1
  · rw [h1, one_mul]
    exact CongruentModTwo.refl x
  · rw [hm1]
    refine ⟨-x, hx.neg, ?_⟩
    ring

/-- Sums of mod-2 congruences. -/
private lemma sum_congr_of_mem {α : Type u} (s : Finset α) {f g : α → ℂ}
    (h : ∀ a ∈ s, CongruentModTwo (f a) (g a)) :
    CongruentModTwo (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by
  classical
  have hsum : CongruentModTwo
      (∑ a : {x : α // x ∈ s}, f a.1) (∑ a : {x : α // x ∈ s}, g a.1) := by
    refine CongruentModTwo.sum ?_
    intro a
    exact h a.1 a.2
  have hs1 : (∑ a ∈ s, f a) = ∑ a : {x : α // x ∈ s}, f a.1 :=
    Finset.sum_subtype s (fun x : α => Iff.rfl) f
  have hs2 : (∑ a ∈ s, g a) = ∑ a : {x : α // x ∈ s}, g a.1 :=
    Finset.sum_subtype s (fun x : α => Iff.rfl) g
  rwa [hs1, hs2]

/-- The full sum over `Irr(H0)` reduces to the sum over `B(χ)` (the
coefficients vanish outside `B(χ)`). -/
private lemma sum_all_eq_sum_BOf (c : Hyp11 G) (h12 : Hyp12 c) (χ : ClassFunction G)
    {x : ↥c.H0} :
    (∑ ν : Irr (↥c.H0), scalarProduct G χ (tildeNu c h12 ν) * ν.1 x) =
      ∑ ν ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 ν) * ν.1 x := by
  classical
  symm
  refine Finset.sum_subset (Finset.subset_univ (BOf c h12 χ)) ?_
  intro ν hνuniv hνnot
  have hν0 : scalarProduct G χ (tildeNu c h12 ν) = 0 := by
    by_contra hne
    exact hνnot ((BOf_mem_iff c h12 χ ν).2 hne)
  rw [hν0]
  simp

/-- `±Irr(G)` are generalized characters. -/
private lemma isGeneralizedCharacter_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : IsGeneralizedCharacter χ := by
  rcases hχ with hχ | hχ
  · exact ⟨χ, 0, isCharacter_of_isIrreducibleCharacter hχ, isCharacter_zero, by simp⟩
  · exact ⟨0, -χ, isCharacter_zero, isCharacter_of_isIrreducibleCharacter hχ, by simp⟩

set_option maxHeartbeats 8000000 in
/-- Lemma 2.4: for `χ ∈ ±Irr(G)`,
`χ = Σ_{ν∈B(χ)} (χ,ν̃)_G·ν` on `T`, and `χ ≡ Σ_{ν∈B(χ)} ν` on `U`. -/
public theorem lemma_2_4 (c : Hyp11 G) (h12 : Hyp12 c) {χ : ClassFunction G}
    (hχ : IsPMIrr G χ) :
    (∀ g : G, g ∈ c.T → (hg : g ∈ c.H0) →
      χ g = ∑ ν ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 ν) * ν.1 ⟨g, hg⟩) ∧
    (∀ u : ↥c.U, (hu : (u : G) ∈ c.H0) →
      CongruentModTwo (χ (u : G)) (∑ ν ∈ BOf c h12 χ, ν.1 ⟨(u : G), hu⟩)) := by
  classical
  have hχg : IsGeneralizedCharacter χ := isGeneralizedCharacter_of_isPMIrr hχ
  rcases exists_orbit_reps c h12 with ⟨ι, hι, rep, hrep_irr, hrep⟩
  let : Fintype ι := hι
  let cν : Irr (↥c.H0) → ℂ := fun ν => scalarProduct G χ (tildeNu c h12 ν)
  constructor
  · intro g hgT hgH0
    have hT : χ g = ∑ ν : Irr (↥c.H0), cν ν * ν.1 ⟨g, hgH0⟩ := by
      simpa [cν] using fourier_on_T c h12 rep hrep_irr hrep χ hχg ⟨g, hgH0⟩ hgT.2
    have hsumB : (∑ ν : Irr (↥c.H0), cν ν * ν.1 ⟨g, hgH0⟩) =
        ∑ ν ∈ BOf c h12 χ, cν ν * ν.1 ⟨g, hgH0⟩ := by
      simpa [cν] using sum_all_eq_sum_BOf c h12 χ (x := ⟨g, hgH0⟩)
    rw [hsumB] at hT
    simpa [cν] using hT
  · intro u hu
    let uH0 : ↥c.H0 := ⟨(u : G), hu⟩
    let tu : G := c.t * (u : G)
    have htuH0 : tu ∈ c.H0 := c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) hu
    have htuNotU : tu ∉ c.U := t_mul_u_not_mem_U c u
    have hT : χ tu = ∑ ν : Irr (↥c.H0), cν ν * ν.1 ⟨tu, htuH0⟩ := by
      simpa [cν, tu] using fourier_on_T c h12 rep hrep_irr hrep χ hχg ⟨tu, htuH0⟩ htuNotU
    have hsumB : (∑ ν : Irr (↥c.H0), cν ν * ν.1 ⟨tu, htuH0⟩) =
        ∑ ν ∈ BOf c h12 χ, cν ν * ν.1 ⟨tu, htuH0⟩ := by
      simpa [cν] using sum_all_eq_sum_BOf c h12 χ (x := ⟨tu, htuH0⟩)
    have htuEq : χ tu = ∑ ν ∈ BOf c h12 χ, cν ν * ν.1 ⟨tu, htuH0⟩ := by
      rwa [hsumB] at hT
    have hχcong : CongruentModTwo (χ (u : G)) (χ tu) := by
      simpa [tu] using cong_u_tu c h12 χ hχg u
    have hsum1 : CongruentModTwo
        (∑ ν ∈ BOf c h12 χ, cν ν * ν.1 ⟨tu, htuH0⟩)
        (∑ ν ∈ BOf c h12 χ, cν ν * ν.1 uH0) := by
      refine sum_congr_of_mem (BOf c h12 χ) ?_
      intro ν hν
      have hcongν := nu_congr_tu_u c h12 ν u hu
      have hcint : IsIntegral ℤ (cν ν) :=
        pm_one_isIntegral (BOf_scalar_eq_pm_one c h12 hχ hν)
      simpa [tu] using CongruentModTwo.mul_right hcongν hcint
    have hsum2 : CongruentModTwo
        (∑ ν ∈ BOf c h12 χ, cν ν * ν.1 uH0)
        (∑ ν ∈ BOf c h12 χ, ν.1 uH0) := by
      refine sum_congr_of_mem (BOf c h12 χ) ?_
      intro ν hν
      exact pm_one_mul_congr (BOf_scalar_eq_pm_one c h12 hχ hν)
        (character_value_isIntegral_irr ν uH0)
    have h1 : CongruentModTwo (χ (u : G)) (∑ ν ∈ BOf c h12 χ, ν.1 uH0) := by
      have hsum1' : CongruentModTwo (χ tu) (∑ ν ∈ BOf c h12 χ, cν ν * ν.1 uH0) := by
        rw [← htuEq] at hsum1
        exact hsum1
      exact CongruentModTwo.trans hχcong (CongruentModTwo.trans hsum1' hsum2)
    simpa [uH0] using h1


end Section2

end CFSG.BenderGlauberman
