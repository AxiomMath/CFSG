module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace CFSG.GL3Monomial

open Matrix
open scoped Pointwise

private abbrev M3 := Matrix (Fin 3) (Fin 3) (ZMod 3)

private abbrev G := Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)

private abbrev V3 := Fin 3 → ZMod 3

private def bvec (i : Fin 3) : V3 := Pi.single i 1

private def nzSign : Finset V3 := Finset.univ.filter fun δ : V3 => ∀ i, δ i ≠ 0

private def monMat (τ : Equiv.Perm (Fin 3)) (δ : V3) : M3 :=
  fun j i => if τ i = j then δ i else 0

private theorem monMat_mulVec (τ : Equiv.Perm (Fin 3)) (δ : V3) (i : Fin 3) :
    Matrix.mulVec (monMat τ δ) (bvec i) = Pi.single (τ i) (δ i) := by
  rw [bvec, Matrix.mulVec_single_one]
  ext j
  by_cases h : τ i = j
  · subst h
    simp [monMat, Matrix.col, Pi.single]
  · have h' : j ≠ τ i := fun hh => h hh.symm
    simp [monMat, Matrix.col, Pi.single, h, h']

private theorem exists_monMat_mem (Y : Subgroup G)
    (hM : ∀ (σ : Equiv.Perm (Fin 3)) (ε : V3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ Y, ∀ i : Fin 3,
        (g : M3).mulVec (Pi.single i 1) = Pi.single (σ i) (ε i))
    (σ : Equiv.Perm (Fin 3)) (ε : V3) (hε : ∀ i, ε i ≠ 0) :
    ∃ g ∈ Y, (g : M3) = monMat σ ε := by
  obtain ⟨g, hgY, hg⟩ := hM σ ε hε
  refine ⟨g, hgY, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [hg i]
  exact (monMat_mulVec σ ε i).symm

private theorem monMat_smul (τ : Equiv.Perm (Fin 3)) (δ : V3) (v : V3) :
    Matrix.mulVec (monMat τ δ) v = fun j => δ (τ.symm j) * v (τ.symm j) := by
  funext j
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (τ.symm j)]
  · simp [monMat]
  · intro i _ hi
    have hne : τ i ≠ j := by
      intro hji
      exact hi ((Equiv.symm_apply_eq τ).mpr hji.symm).symm
    simp [monMat, hne]
  · intro h
    exact absurd (Finset.mem_univ (τ.symm j)) h

private theorem monMat_mul (τ τ' : Equiv.Perm (Fin 3)) (δ δ' : V3) :
    monMat τ δ * monMat τ' δ' = monMat (τ * τ') (fun i => δ (τ' i) * δ' i) := by
  ext j i
  simp only [monMat, Matrix.mul_apply]
  rw [Finset.sum_eq_single (τ' i)]
  · by_cases h : τ (τ' i) = j <;> simp [h]
  · intro k _ hk
    have : τ' i ≠ k := fun h => hk h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem monMat_one : monMat (1 : Equiv.Perm (Fin 3)) (fun _ => (1 : ZMod 3)) = 1 := by
  ext j i
  by_cases h : i = j
  · subst h; simp [monMat]
  · have h' : j ≠ i := fun hh => h hh.symm
    simp [monMat, h, h']

private noncomputable def monMatUnit (τ : Equiv.Perm (Fin 3)) (δ : V3)
    (hδ : ∀ i, δ i ≠ 0) : G :=
  ⟨monMat τ δ, monMat τ⁻¹ (fun j => (δ (τ⁻¹ j))⁻¹), by
      rw [monMat_mul]
      have h : (fun i => δ (τ⁻¹ i) * (δ (τ⁻¹ i))⁻¹) = fun _ => 1 := by
        funext i
        rw [mul_inv_cancel₀ (hδ (τ⁻¹ i))]
      rw [h, mul_inv_cancel, monMat_one]
    , by
      rw [monMat_mul]
      have h : (fun i => (δ (τ⁻¹ (τ i)))⁻¹ * δ i) = fun _ => 1 := by
        funext i
        change (δ (τ.symm (τ i)))⁻¹ * δ i = 1
        rw [Equiv.symm_apply_apply, inv_mul_cancel₀ (hδ i)]
      rw [h, inv_mul_cancel, monMat_one]⟩

@[simp] private theorem monMatUnit_val (τ : Equiv.Perm (Fin 3)) (δ : V3)
    (hδ : ∀ i, δ i ≠ 0) :
    ((monMatUnit τ δ hδ : G) : M3) = monMat τ δ := rfl

private noncomputable def Msub : Subgroup G where
  carrier := Set.range (fun p : Equiv.Perm (Fin 3) × {δ : V3 // ∀ i, δ i ≠ 0} =>
    monMatUnit p.1 p.2.1 p.2.2)
  one_mem' := ⟨(1, ⟨fun _ => 1, fun _ => one_ne_zero⟩), by
    apply Units.ext
    exact monMat_one⟩
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    refine ⟨(p.1 * q.1, ⟨fun i => p.2.1 (q.1 i) * q.2.1 i,
      fun i => mul_ne_zero (p.2.2 (q.1 i)) (q.2.2 i)⟩), ?_⟩
    apply Units.ext
    simp only [Units.val_mul, monMatUnit_val]
    rw [monMat_mul]
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(p.1⁻¹, ⟨fun j => (p.2.1 (p.1⁻¹ j))⁻¹,
      fun j => inv_ne_zero (p.2.2 _)⟩), ?_⟩
    apply Units.ext
    rfl

private theorem Msub_le (Y : Subgroup G)
    (hM : ∀ (σ : Equiv.Perm (Fin 3)) (ε : V3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ Y, ∀ i : Fin 3,
        (g : M3).mulVec (Pi.single i 1) = Pi.single (σ i) (ε i)) : Msub ≤ Y := by
  rintro x ⟨p, rfl⟩
  obtain ⟨g, hgY, hgmat⟩ := exists_monMat_mem Y hM p.1 p.2.1 p.2.2
  have hxg : monMatUnit p.1 p.2.1 p.2.2 = g := by
    apply Units.ext
    rw [monMatUnit_val, hgmat]
  change monMatUnit p.1 p.2.1 p.2.2 ∈ Y
  rwa [hxg]

private theorem Msub_card : Nat.card Msub = 48 := by
  let f : (Equiv.Perm (Fin 3) × {δ : V3 // ∀ i, δ i ≠ 0}) → Msub :=
    fun p => ⟨monMatUnit p.1 p.2.1 p.2.2, ⟨p, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      have hval : monMat p.1 p.2.1 = monMat q.1 q.2.1 := by
        have := congrArg (fun x : Msub => ((x : G) : M3)) hpq
        simpa [f, monMatUnit_val] using this
      have key : ∀ i, q.1 i = p.1 i ∧ q.2.1 i = p.2.1 i := by
        intro i
        have h := congrFun (congrFun hval (p.1 i)) i
        have hp : monMat p.1 p.2.1 (p.1 i) i = p.2.1 i := by simp [monMat]
        rw [hp] at h
        by_cases hq : q.1 i = p.1 i
        · have hq' : monMat q.1 q.2.1 (p.1 i) i = q.2.1 i := by simp [monMat, hq]
          rw [hq'] at h
          exact ⟨hq, h.symm⟩
        · have hq' : monMat q.1 q.2.1 (p.1 i) i = 0 := by simp [monMat, hq]
          rw [hq'] at h
          exact absurd h (p.2.2 i)
      have hτ : p.1 = q.1 := Equiv.ext fun i => (key i).1.symm
      have hδ : p.2.1 = q.2.1 := funext fun i => (key i).2.symm
      exact Prod.ext hτ (Subtype.ext hδ)
    · intro x
      obtain ⟨p, hp⟩ := x.2
      exact ⟨p, Subtype.ext hp⟩
  have hcard : Nat.card Msub =
      Nat.card (Equiv.Perm (Fin 3) × {δ : V3 // ∀ i, δ i ≠ 0}) :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [hcard, Nat.card_eq_fintype_card]
  decide +kernel

private def A : M3 := !![0,0,1; 1,0,1; 0,1,0]

private def Ai : M3 := !![2,1,0; 0,0,1; 1,0,0]

private def Aunit : G := ⟨A, Ai, by decide +kernel, by decide +kernel⟩

private theorem Aunit_pow : Aunit ^ 13 = 1 := by decide +kernel

private theorem Aunit_ne_one : Aunit ≠ 1 := by decide +kernel

private theorem orderOf_Aunit : orderOf Aunit = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact orderOf_eq_prime Aunit_pow Aunit_ne_one

private theorem A_mulVec_bvec0 : Matrix.mulVec A (bvec 0) = bvec 1 := by decide +kernel

private theorem A_mulVec_bvec1 : Matrix.mulVec A (bvec 1) = bvec 2 := by decide +kernel

private theorem centralizer_A_eq_one {u : G}
    (hu : u ∈ Subgroup.centralizer ({Aunit} : Set G))
    (hu1 : (u : M3) *ᵥ bvec 0 = bvec 0) : u = 1 := by
  have hcomm : (u : M3) * A = A * (u : M3) := by
    have h := (Subgroup.mem_centralizer_iff.mp hu) Aunit (by simp)
    have := congrArg (fun x : G => ((x : G) : M3)) h.symm
    simpa [Aunit] using this
  have h1 : (u : M3) *ᵥ bvec 1 = bvec 1 := by
    have h2 : (u : M3) *ᵥ (A *ᵥ bvec 0) = A *ᵥ ((u : M3) *ᵥ bvec 0) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
    rw [A_mulVec_bvec0, hu1, A_mulVec_bvec0] at h2
    exact h2
  have h2 : (u : M3) *ᵥ bvec 2 = bvec 2 := by
    have h3 : (u : M3) *ᵥ (A *ᵥ bvec 1) = A *ᵥ ((u : M3) *ᵥ bvec 1) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
    rw [A_mulVec_bvec1, h1, A_mulVec_bvec1] at h3
    exact h3
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  fin_cases i
  · show (u : M3) *ᵥ bvec 0 = (↑(1 : G) : M3) *ᵥ bvec 0
    rw [hu1]
    simp
  · show (u : M3) *ᵥ bvec 1 = (↑(1 : G) : M3) *ᵥ bvec 1
    rw [h1]
    simp
  · show (u : M3) *ᵥ bvec 2 = (↑(1 : G) : M3) *ᵥ bvec 2
    rw [h2]
    simp

private theorem centralizer_A_card_le :
    Nat.card (Subgroup.centralizer ({Aunit} : Set G)) ≤ 27 := by
  have hinj : Function.Injective (fun u : Subgroup.centralizer ({Aunit} : Set G) =>
      ((u : G) : M3) *ᵥ bvec 0) := by
    intro u v huv
    change ((u : G) : M3) *ᵥ bvec 0 = ((v : G) : M3) *ᵥ bvec 0 at huv
    have hw : ((u : G)⁻¹ * (v : G)) ∈ Subgroup.centralizer ({Aunit} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ u.2) v.2
    have hw1 : ((u : G)⁻¹ * (v : G)) • bvec 0 = bvec 0 := by
      rw [mul_smul]
      have this : (v : G) • bvec 0 = (u : G) • bvec 0 := huv.symm
      rw [this, ← mul_smul, inv_mul_cancel, one_smul]
    have h1 := centralizer_A_eq_one hw hw1
    have this : (u : G) = (v : G) := by
      rw [← mul_inv_cancel_left (u : G) (v : G), h1, mul_one]
    exact Subtype.ext this
  have h := Nat.card_le_card_of_injective _ hinj
  have hV : Nat.card V3 = 27 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rwa [hV] at h

private def orbSP (v : V3) : Finset V3 :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 3))).product nzSign).image
    (fun p : Equiv.Perm (Fin 3) × V3 => fun i => p.2 i * v (p.1.symm i))

private theorem bvec_ne_zero (i : Fin 3) : bvec i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [bvec, Pi.single] at this

private def A1 : Finset V3 := orbSP (bvec 0)

private def A2 : Finset V3 := orbSP (bvec 0 + bvec 1)

private def A3 : Finset V3 := orbSP (bvec 0 + bvec 1 + bvec 2)

private theorem A1_card : A1.card = 6 := by decide +kernel

private theorem A2_card : A2.card = 12 := by decide +kernel

private theorem A3_card : A3.card = 8 := by decide +kernel

private theorem A2_fix : ∀ v : V3, v ∈ A2 → orbSP v = A2 := by decide +kernel

private theorem A3_fix : ∀ v : V3, v ∈ A3 → orbSP v = A3 := by decide +kernel

private theorem bvec_mem_A1 : ∀ i : Fin 3, bvec i ∈ A1 := by decide +kernel

private theorem mem_A1_single :
    ∀ v : V3, v ∈ A1 → ∃ (j : Fin 3) (c : ZMod 3), v = Pi.single j c := by
  decide +kernel

private theorem A1_union_A2_union_A3 : A1 ∪ A2 ∪ A3 = Finset.univ.filter (fun v : V3 => v ≠ 0) := by
  decide +kernel

private theorem A1_disjoint_A2 : Disjoint A1 A2 := by decide +kernel

private theorem A1_disjoint_A3 : Disjoint A1 A3 := by decide +kernel

private theorem A2_disjoint_A3 : Disjoint A2 A3 := by decide +kernel

private theorem nonzero_mem_A : ∀ v : V3, v ≠ 0 → v ∈ A1 ∨ v ∈ A2 ∨ v ∈ A3 := by
  intro v hv
  have h : v ∈ A1 ∪ A2 ∪ A3 := by
    rw [A1_union_A2_union_A3, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hv⟩
  simpa [Finset.mem_union] using h

private noncomputable def orb (Y : Subgroup G) : Finset V3 := by
  classical
  exact Finset.univ.filter (fun v : V3 => v ∈ MulAction.orbit Y (bvec 0))

private theorem orb_card_eq (Y : Subgroup G) :
    (orb Y).card = Nat.card (MulAction.orbit Y (bvec 0)) := by
  classical
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card]
  congr 1
  ext v
  simp [orb]

private theorem orbit_dvd (Y : Subgroup G) :
    Nat.card (MulAction.orbit Y (bvec 0)) ∣ Nat.card Y := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Y (bvec 0))]
  exact Subgroup.card_quotient_dvd_card _

private theorem smul_orbit_mem {Y : Subgroup G} {x : V3} {v : V3}
    (hv : v ∈ MulAction.orbit Y x) (g : Y) : g • v ∈ MulAction.orbit Y x := by
  obtain ⟨y, rfl⟩ := MulAction.mem_orbit_iff.mp hv
  exact MulAction.mem_orbit_iff.mpr ⟨g * y, by rw [mul_smul]⟩

private theorem card_G : Nat.card G = 11232 := by
  change Nat.card (GL (Fin 3) (ZMod 3)) = 11232
  rw [Matrix.card_GL_field]
  decide +kernel

private theorem fac13 : (Fintype.card G).factorization 13 = 1 := by
  rw [← Nat.card_eq_fintype_card, card_G]
  have h : 11232 = 13 * 864 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by decide : Nat.Prime 13),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 13 ∣ 864)]

private theorem exists_conj_of_card_eq_thirteen (H1 H2 : Subgroup G)
    (h1 : Nat.card H1 = 13) (h2 : Nat.card H2 = 13) :
    ∃ g : G, H2 = H1.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  let S1 : Sylow 13 G := Sylow.ofCard (p := 13) H1 (by simp [h1, fac13])
  let S2 : Sylow 13 G := Sylow.ofCard (p := 13) H2 (by simp [h2, fac13])
  have : Finite (Sylow 13 G) := Sylow.finite_of_finiteIndex S1
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) S1 S2
  refine ⟨g, ?_⟩
  have hsub : (H2 : Set G) = MulAut.conj g • (H1 : Set G) := by
    have h := congrArg (fun S : Sylow 13 G => (S : Set G)) hg
    rw [Sylow.coe_smul] at h
    rw [show (S1 : Set G) = (H1 : Set G) from rfl,
      show (S2 : Set G) = (H2 : Set G) from rfl] at h
    exact h.symm
  refine Subgroup.ext ?_
  intro x
  change x ∈ (H2 : Set G) ↔ x ∈ (H1.map (MulAut.conj g).toMonoidHom : Set G)
  rw [hsub]
  simp [Set.mem_smul_set, MulAut.conj_apply]

private theorem orbSP_subset_orb (Y : Subgroup G)
    (hM : ∀ (σ : Equiv.Perm (Fin 3)) (ε : V3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ Y, ∀ i : Fin 3,
        (g : M3).mulVec (Pi.single i 1) = Pi.single (σ i) (ε i)) :
    ∀ v : V3, v ∈ orb Y → orbSP v ⊆ orb Y := by
  classical
  intro v hv w hw
  rw [orb, Finset.mem_filter] at hv
  obtain ⟨-, hv⟩ := hv
  rw [orb, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [orbSP, Finset.mem_image] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  obtain ⟨τ, δ⟩ := p
  obtain ⟨-, hδ⟩ := Finset.mem_product.mp hp
  rw [nzSign, Finset.mem_filter] at hδ
  obtain ⟨-, hδnz⟩ := hδ
  obtain ⟨pp, hppY, hppmat⟩ := exists_monMat_mem Y hM τ (fun _ => 1) (fun _ => one_ne_zero)
  obtain ⟨dd, hddY, hddmat⟩ := exists_monMat_mem Y hM (Equiv.refl (Fin 3)) δ hδnz
  have hpv : pp • v = fun i => v (τ.symm i) := by
    rw [show pp • v = Matrix.mulVec (pp : M3) v from rfl, hppmat, monMat_smul]
    simp
  have hdw : (fun i => δ i * v (τ.symm i)) = dd • (pp • v) := by
    rw [hpv]
    show (fun i => δ i * v (τ.symm i)) = dd • (fun i => v (τ.symm i))
    rw [show dd • (fun i => v (τ.symm i)) =
        Matrix.mulVec (dd : M3) (fun i => v (τ.symm i)) from rfl, hddmat, monMat_smul]
    simp
  rw [hdw]
  exact smul_orbit_mem (smul_orbit_mem hv ⟨pp, hppY⟩) ⟨dd, hddY⟩

private theorem A1_subset_orb (Y : Subgroup G)
    (hM : ∀ (σ : Equiv.Perm (Fin 3)) (ε : V3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ Y, ∀ i : Fin 3,
        (g : M3).mulVec (Pi.single i 1) = Pi.single (σ i) (ε i)) : A1 ⊆ orb Y := by
  classical
  intro v hv
  exact orbSP_subset_orb Y hM (bvec 0) (by
    rw [orb, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, MulAction.mem_orbit_self _⟩) hv

private theorem orb_card_cases (Y : Subgroup G)
    (hM : ∀ (σ : Equiv.Perm (Fin 3)) (ε : V3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ Y, ∀ i : Fin 3,
        (g : M3).mulVec (Pi.single i 1) = Pi.single (σ i) (ε i)) :
    (orb Y).card = 6 ∨ (orb Y).card = 18 ∨ (orb Y).card = 14 ∨ (orb Y).card = 26 := by
  classical
  have hstep := orbSP_subset_orb Y hM
  have h0 : (0 : V3) ∉ MulAction.orbit Y (bvec 0) := by
    intro h
    obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp h
    have : bvec 0 = 0 := by
      calc bvec 0 = y⁻¹ • (y • bvec 0) := (inv_smul_smul y (bvec 0)).symm
        _ = y⁻¹ • 0 := by rw [hy]
        _ = 0 := smul_zero _
    exact bvec_ne_zero 0 this
  have hA1sub : A1 ⊆ orb Y := by
    intro v hv
    exact hstep (bvec 0) (by
      rw [orb, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, MulAction.mem_orbit_self _⟩) hv
  have hOsub : orb Y ⊆ A1 ∪ A2 ∪ A3 := by
    intro v hv
    rw [orb, Finset.mem_filter] at hv
    obtain ⟨-, hv⟩ := hv
    rcases nonzero_mem_A v (fun h0v => h0 (h0v ▸ hv)) with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  have hcase2 : A2 ∩ orb Y = ∅ ∨ A2 ⊆ orb Y := by
    by_cases h : (A2 ∩ orb Y).Nonempty
    · right
      obtain ⟨v, hv⟩ := h
      rw [Finset.mem_inter] at hv
      obtain ⟨hvA2, hvO⟩ := hv
      intro w hw
      have hsub : orbSP v ⊆ orb Y := hstep v hvO
      rw [A2_fix v hvA2] at hsub
      exact hsub hw
    · left
      exact Finset.not_nonempty_iff_eq_empty.mp h
  have hcase3 : A3 ∩ orb Y = ∅ ∨ A3 ⊆ orb Y := by
    by_cases h : (A3 ∩ orb Y).Nonempty
    · right
      obtain ⟨v, hv⟩ := h
      rw [Finset.mem_inter] at hv
      obtain ⟨hvA3, hvO⟩ := hv
      intro w hw
      have hsub : orbSP v ⊆ orb Y := hstep v hvO
      rw [A3_fix v hvA3] at hsub
      exact hsub hw
    · left
      exact Finset.not_nonempty_iff_eq_empty.mp h
  have hOeq : orb Y = A1 ∪ (A2 ∩ orb Y) ∪ (A3 ∩ orb Y) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp (hOsub hv) with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h2, hv⟩))
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h3, hv⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with h1 | h2
        · exact hA1sub h1
        · exact (Finset.mem_inter.mp h2).2
      · exact (Finset.mem_inter.mp hv).2
  have hd1 : Disjoint A1 (A2 ∩ orb Y) := A1_disjoint_A2.mono_right Finset.inter_subset_left
  have hd2 : Disjoint (A1 ∪ (A2 ∩ orb Y)) (A3 ∩ orb Y) := by
    rw [Finset.disjoint_union_left]
    exact ⟨A1_disjoint_A3.mono_right Finset.inter_subset_left,
      A2_disjoint_A3.mono Finset.inter_subset_left Finset.inter_subset_left⟩
  have hcard : (orb Y).card = A1.card + (A2 ∩ orb Y).card + (A3 ∩ orb Y).card := by
    conv_lhs => rw [hOeq]
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  rcases hcase2 with h2 | h2
  · rw [h2, Finset.card_empty] at hcard
    rcases hcase3 with h3 | h3
    · rw [h3, Finset.card_empty, A1_card] at hcard
      exact Or.inl hcard
    · rw [Finset.inter_eq_left.mpr h3, A3_card, A1_card] at hcard
      exact Or.inr (Or.inr (Or.inl hcard))
  · have hc2 : (A2 ∩ orb Y).card = A2.card := by rw [Finset.inter_eq_left.mpr h2]
    rw [hc2, A2_card, A1_card] at hcard
    rcases hcase3 with h3 | h3
    · rw [h3, Finset.card_empty] at hcard
      exact Or.inr (Or.inl hcard)
    · rw [Finset.inter_eq_left.mpr h3, A3_card] at hcard
      exact Or.inr (Or.inr (Or.inr hcard))

private theorem eq_one_of_dvd_96_of_modEq {n : ℕ} (hdvd : n ∣ 96) (hmod : n ≡ 1 [MOD 13]) :
    n = 1 := by
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hnle : n ≤ 96 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;> simp_all [Nat.ModEq]

private theorem card_eq_624_or_1248 {n : ℕ} (h13 : 13 ∣ n) (h48 : 48 ∣ n)
    (hdvd : n ∣ 11232) (h9 : ¬ 9 ∣ n) : n = 624 ∨ n = 1248 := by
  have h624 : 624 ∣ n := by
    have hcop : Nat.Coprime 13 48 := by norm_num [Nat.coprime_iff_gcd_eq_one]
    have := hcop.mul_dvd_of_dvd_of_dvd h13 h48
    norm_num at this
    exact this
  obtain ⟨t, rfl⟩ := h624
  have ht18 : t ∣ 18 := by
    have h : 624 * t ∣ 624 * 18 := by
      rw [show (624:ℕ) * 18 = 11232 by norm_num]
      exact hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 624)).mp h
  have h3t : ¬ 3 ∣ t := by
    intro h
    apply h9
    obtain ⟨u, rfl⟩ := h
    exact ⟨208 * u, by ring⟩
  have htle : t ≤ 18 := Nat.le_of_dvd (by norm_num) ht18
  have htpos : 0 < t := Nat.pos_of_dvd_of_pos ht18 (by norm_num)
  interval_cases t <;> simp_all

private theorem le_normalizer_of_subgroupOf_normal {H K : Subgroup G} (hHK : H ≤ K)
    (hN : (H.subgroupOf K).Normal) : K ≤ Subgroup.normalizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact (Subgroup.normal_subgroupOf_iff hHK).mp hN h k hh hk
  · intro hh
    have hk' : k⁻¹ ∈ K := K.inv_mem hk
    have hthis := (Subgroup.normal_subgroupOf_iff hHK).mp hN (k * h * k⁻¹) k⁻¹ hh hk'
    have hcalc : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
    rwa [hcalc] at hthis

private theorem centralizer_zpowers_card_le (s : G) (hs : orderOf s = 13) :
    Nat.card (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G)) ≤ 27 := by
  set H1 : Subgroup G := Subgroup.zpowers s with hH1
  set H2 : Subgroup G := Subgroup.zpowers Aunit with hH2
  have hsz : Nat.card H1 = 13 := by rw [hH1, Nat.card_zpowers, hs]
  have haz : Nat.card H2 = 13 := by rw [hH2, Nat.card_zpowers, orderOf_Aunit]
  obtain ⟨e, he⟩ := exists_conj_of_card_eq_thirteen H1 H2 hsz haz
  let φ : G →* G := (MulAut.conj e).toMonoidHom
  have hmap : H1.map φ = H2 := he.symm
  have hle := Subgroup.map_centralizer_le_centralizer_image (H1 : Set G) φ
  have hset : φ '' (H1 : Set G) = (H2 : Set G) := by
    rw [← hmap, Subgroup.coe_map]
  have hle' : (Subgroup.centralizer (H1 : Set G)).map φ ≤
      Subgroup.centralizer (H2 : Set G) := by
    rwa [hset] at hle
  have hcardmap : Nat.card ((Subgroup.centralizer (H1 : Set G)).map φ) =
      Nat.card (Subgroup.centralizer (H1 : Set G)) :=
    Subgroup.card_map_of_injective (MulAut.conj e).injective
  have hcardle : Nat.card ((Subgroup.centralizer (H1 : Set G)).map φ) ≤
      Nat.card (Subgroup.centralizer (H2 : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x : (Subgroup.centralizer (H1 : Set G)).map φ =>
        (⟨(x : G), hle' x.2⟩ : Subgroup.centralizer (H2 : Set G))) ?_
    intro a b hab
    exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  have hA : Subgroup.centralizer (H2 : Set G) = Subgroup.centralizer ({Aunit} : Set G) := by
    rw [hH2, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  calc Nat.card (Subgroup.centralizer (H1 : Set G))
      = Nat.card ((Subgroup.centralizer (H1 : Set G)).map φ) := hcardmap.symm
    _ ≤ Nat.card (Subgroup.centralizer (H2 : Set G)) := hcardle
    _ = Nat.card (Subgroup.centralizer ({Aunit} : Set G)) := by rw [hA]
    _ ≤ 27 := centralizer_A_card_le

private theorem card_le_324_of_le_normalizer (Y : Subgroup G) {s : G} (hs : orderOf s = 13)
    (hle : Y ≤ Subgroup.normalizer ((Subgroup.zpowers s : Subgroup G) : Set G)) :
    Nat.card Y ≤ 324 := by
  let P0 : Subgroup G := Subgroup.zpowers s
  let φ : Y →* MulAut P0 := P0.normalizerMonoidHom.comp (Subgroup.inclusion hle)
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker ≤ 27 := by
    have hinj : Function.Injective (fun y : φ.ker =>
        (⟨((y : Y) : G), by
          have hyker : Subgroup.inclusion hle (y : Y) ∈ P0.normalizerMonoidHom.ker := by
            rw [MonoidHom.mem_ker]
            show P0.normalizerMonoidHom (Subgroup.inclusion hle (y : Y)) = 1
            exact y.2
          rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hyker
          exact hyker⟩ : Subgroup.centralizer (P0 : Set G))) := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
    have h1 := Nat.card_le_card_of_injective _ hinj
    exact le_trans h1 (centralizer_zpowers_card_le s hs)
  have hrange : Nat.card φ.range ≤ 12 := by
    have h1 : Nat.card φ.range ≤ Nat.card (MulAut P0) := by
      refine Nat.card_le_card_of_injective (fun x : φ.range => (x : MulAut P0)) ?_
      intro a b hab
      exact Subtype.ext hab
    have h2 : Nat.card (MulAut P0) = 12 := by
      rw [IsCyclic.card_mulAut]
      have : Nat.card P0 = 13 := by
        rw [show P0 = Subgroup.zpowers s from rfl, Nat.card_zpowers, hs]
      rw [this]
      decide +kernel
    omega
  calc Nat.card Y = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ 27 * 12 := Nat.mul_le_mul hker hrange
    _ = 324 := by norm_num

private theorem orbit_card_ne_26 (Y : Subgroup G)
    (hM : ∀ (σ : Equiv.Perm (Fin 3)) (ε : V3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ Y, ∀ i : Fin 3,
        (g : M3).mulVec (Pi.single i 1) = Pi.single (σ i) (ε i))
    (h9 : ¬ 9 ∣ Nat.card Y) (h26 : (orb Y).card = 26) : False := by
  classical
  have hOdvd : (orb Y).card ∣ Nat.card Y := by
    rw [orb_card_eq]
    exact orbit_dvd Y
  have h26dvd : 26 ∣ Nat.card Y := by rw [h26] at hOdvd; exact hOdvd
  have h13dvd : 13 ∣ Nat.card Y := dvd_trans (by norm_num : 13 ∣ 26) h26dvd
  have h48dvd : 48 ∣ Nat.card Y := by
    rw [← Msub_card]
    exact Subgroup.card_dvd_of_le (Msub_le Y hM)
  have hYdvd : Nat.card Y ∣ 11232 := by
    rw [← card_G]
    exact Subgroup.card_subgroup_dvd_card Y
  have hYval : Nat.card Y = 624 ∨ Nat.card Y = 1248 :=
    card_eq_624_or_1248 h13dvd h48dvd hYdvd h9
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Y) 13 h13dvd
  have hsG : orderOf (s : G) = 13 := by rw [Subgroup.orderOf_coe, hs]
  let P0 : Subgroup G := Subgroup.zpowers (s : G)
  let Psub : Subgroup Y := Subgroup.zpowers s
  have hP0le : P0 ≤ Y := Subgroup.zpowers_le.mpr s.2
  have hPsub_card : Nat.card Psub = 13 := by
    rw [show Psub = Subgroup.zpowers s from rfl, Nat.card_zpowers, hs]
  have hfact : (Nat.card Y).factorization 13 = 1 := by
    rcases hYval with h | h <;> rw [h] <;> decide +kernel
  have hcardP : Nat.card Psub = 13 ^ (Nat.card Y).factorization 13 := by
    rw [hPsub_card, hfact, pow_one]
  let P : Sylow 13 Y := Sylow.ofCard Psub hcardP
  have hPcoe : (P : Subgroup Y) = Psub := Sylow.coe_ofCard Psub hcardP
  have : Finite (Sylow 13 Y) := Sylow.finite_of_finiteIndex P
  have hn_dvd_index : Nat.card (Sylow 13 Y) ∣ (P : Subgroup Y).index := by
    rw [Sylow.card_eq_index_normalizer P]
    exact Subgroup.index_dvd_of_le Subgroup.le_normalizer
  have hPindex : (P : Subgroup Y).index = Nat.card Y / 13 := by
    rw [Subgroup.index_eq_card_div, hPcoe, hPsub_card]
  have hn_dvd : Nat.card (Sylow 13 Y) ∣ Nat.card Y / 13 := by
    rw [← hPindex]
    exact hn_dvd_index
  have hYdiv : Nat.card Y / 13 = 48 ∨ Nat.card Y / 13 = 96 := by
    rcases hYval with h | h <;> rw [h] <;> norm_num
  have hn_dvd96 : Nat.card (Sylow 13 Y) ∣ 96 := by
    rcases hYdiv with h | h
    · rw [h] at hn_dvd
      exact dvd_trans hn_dvd (by norm_num : 48 ∣ 96)
    · rw [h] at hn_dvd
      exact hn_dvd
  have hn_mod : Nat.card (Sylow 13 Y) ≡ 1 [MOD 13] := card_sylow_modEq_one 13 Y
  have hn1 : Nat.card (Sylow 13 Y) = 1 := eq_one_of_dvd_96_of_modEq hn_dvd96 hn_mod
  have : Subsingleton (Sylow 13 Y) := (Nat.card_eq_one_iff_unique.mp hn1).1
  have hPnormal : (P : Subgroup Y).Normal := Sylow.normal_of_subsingleton P
  have hPsub_normal : Psub.Normal := by rw [hPcoe] at hPnormal; exact hPnormal
  have hsub_eq : P0.subgroupOf Y = Psub := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    change (x : G) ∈ Subgroup.zpowers (s : G) ↔ x ∈ Subgroup.zpowers s
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hNsub : (P0.subgroupOf Y).Normal := by rw [hsub_eq]; exact hPsub_normal
  have hle : Y ≤ Subgroup.normalizer (P0 : Set G) :=
    le_normalizer_of_subgroupOf_normal hP0le hNsub
  have hYle : Nat.card Y ≤ 324 := card_le_324_of_le_normalizer Y hsG hle
  rcases hYval with h | h <;> rw [h] at hYle <;> norm_num at hYle

theorem exists_mulVec_single_eq (Y : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)))
    (hM : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ Y, ∀ i : Fin 3,
        (g : Matrix (Fin 3) (Fin 3) (ZMod 3)).mulVec (Pi.single i 1) = Pi.single (σ i) (ε i))
    (h9 : ¬ 9 ∣ Nat.card Y) {g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)} (hg : g ∈ Y)
    (i : Fin 3) :
    ∃ (j : Fin 3) (e : ZMod 3),
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)).mulVec (Pi.single i 1) = Pi.single j e := by
  classical
  have hYdvd : Nat.card Y ∣ 11232 := by
    rw [← card_G]
    exact Subgroup.card_subgroup_dvd_card Y
  have hOdvd : (orb Y).card ∣ Nat.card Y := by
    rw [orb_card_eq]
    exact orbit_dvd Y
  rcases orb_card_cases Y hM with h6 | h18 | h14 | h26
  · have hsub : A1 ⊆ orb Y := A1_subset_orb Y hM
    have hcard : (orb Y).card ≤ A1.card := by rw [h6, A1_card]
    have hO : orb Y = A1 := (Finset.eq_of_subset_of_card_le hsub hcard).symm
    have hbi : bvec i ∈ MulAction.orbit Y (bvec 0) := by
      have h : bvec i ∈ orb Y := by rw [hO]; exact bvec_mem_A1 i
      rw [orb, Finset.mem_filter] at h
      exact h.2
    have hmemA1 : g • bvec i ∈ A1 := by
      have hmem : g • bvec i ∈ orb Y := by
        rw [orb, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, smul_orbit_mem hbi ⟨g, hg⟩⟩
      rwa [hO] at hmem
    obtain ⟨j, c, hjc⟩ := mem_A1_single (g • bvec i) hmemA1
    refine ⟨j, c, ?_⟩
    rw [← hjc]
    rfl
  · exfalso
    exact h9 (dvd_trans (by rw [h18]; norm_num) hOdvd)
  · exfalso
    have h7 : 7 ∣ 11232 := dvd_trans (dvd_trans (by rw [h14]; norm_num) hOdvd) hYdvd
    norm_num at h7
  · exact (orbit_card_ne_26 Y hM h9 h26).elim

end CFSG.GL3Monomial

end

