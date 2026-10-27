module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.IsPerfect
import CFSG.RankThree.PartTwo.Sec4.Item426A6Linear

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

open Matrix

variable {E : Type*} [Field E] {P : Type*} [Group P]

theorem restrict_toLin'_mul {A B : Matrix (Fin 3) (Fin 3) E} {W : Submodule E (Fin 3 → E)}
    (hA : ∀ v ∈ W, Matrix.toLin' A v ∈ W) (hB : ∀ v ∈ W, Matrix.toLin' B v ∈ W)
    (hAB : ∀ v ∈ W, Matrix.toLin' (A * B) v ∈ W) :
    (Matrix.toLin' (A * B)).restrict hAB =
      (Matrix.toLin' A).restrict hA ∘ₗ (Matrix.toLin' B).restrict hB := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  simp only [LinearMap.restrict_apply, LinearMap.coe_comp, Function.comp_apply,
    Matrix.toLin'_mul]

theorem toLin'_mem_of_invariant (ρ : P →* Matrix (Fin 3) (Fin 3) E)
    {W : Submodule E (Fin 3 → E)} (hW : ∀ g, ∀ v ∈ W, (ρ g) *ᵥ v ∈ W) (g : P) :
    ∀ v ∈ W, Matrix.toLin' (ρ g) v ∈ W := fun v hv => by
  rw [Matrix.toLin'_apply]
  exact hW g v hv

noncomputable def detRestrict (ρ : P →* Matrix (Fin 3) (Fin 3) E) (W : Submodule E (Fin 3 → E))
    (hW : ∀ g, ∀ v ∈ W, (ρ g) *ᵥ v ∈ W) : P →* E where
  toFun g := LinearMap.det ((Matrix.toLin' (ρ g)).restrict (toLin'_mem_of_invariant ρ hW g))
  map_one' := by
    have h : (Matrix.toLin' (ρ 1)).restrict (toLin'_mem_of_invariant ρ hW 1) =
        LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change Matrix.toLin' (ρ 1) v = v
      rw [map_one, Matrix.toLin'_one, LinearMap.id_apply]
    rw [h, LinearMap.det_id]
  map_mul' g h := by
    have e := restrict_toLin'_mul (toLin'_mem_of_invariant ρ hW g)
      (toLin'_mem_of_invariant ρ hW h) (by
        rw [← map_mul]
        exact toLin'_mem_of_invariant ρ hW (g * h))
    rw [← LinearMap.det_comp, ← e]
    congr 2
    rw [map_mul]

theorem detRestrict_eq_one [Group.IsPerfect P] (ρ : P →* Matrix (Fin 3) (Fin 3) E)
    (W : Submodule E (Fin 3 → E)) (hW : ∀ g, ∀ v ∈ W, (ρ g) *ᵥ v ∈ W) (g : P) :
    detRestrict ρ W hW g = 1 := by
  have hker := Abelianization.commutator_subset_ker (detRestrict ρ W hW).toHomUnits
  rw [Group.IsPerfect.commutator_eq_top (G := P)] at hker
  have hg := hker (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hg
  have := congrArg Units.val hg
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this

theorem pow_finrank_eq_one [Group.IsPerfect P] (ρ : P →* Matrix (Fin 3) (Fin 3) E)
    {W : Submodule E (Fin 3 → E)} (hW : ∀ g, ∀ v ∈ W, (ρ g) *ᵥ v ∈ W) {z : P} {l : E}
    (hl : ∀ v ∈ W, (ρ z) *ᵥ v = l • v) : l ^ Module.finrank E W = 1 := by
  have h := detRestrict_eq_one ρ W hW z
  have hr : (Matrix.toLin' (ρ z)).restrict (toLin'_mem_of_invariant ρ hW z) =
      l • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.restrict_apply, Matrix.toLin'_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Submodule.coe_smul]
    exact hl v v.2
  change LinearMap.det ((Matrix.toLin' (ρ z)).restrict (toLin'_mem_of_invariant ρ hW z)) = 1 at h
  rwa [hr, LinearMap.det_smul, LinearMap.det_id, mul_one] at h

theorem eq_top_of_three_dvd_finrank {W : Submodule E (Fin 3 → E)} (hW : W ≠ ⊥)
    (h3 : 3 ∣ Module.finrank E W) : W = ⊤ := by
  have hle : Module.finrank E W ≤ 3 := by
    have := Submodule.finrank_le W
    rwa [Module.finrank_fin_fun] at this
  have hne : Module.finrank E W ≠ 0 := by
    rwa [Ne, Submodule.finrank_eq_zero]
  have heq : Module.finrank E W = Module.finrank E (Fin 3 → E) := by
    rw [Module.finrank_fin_fun]
    omega
  exact Submodule.eq_top_of_finrank_eq heq

theorem eq_smul_one_of_perfect [IsAlgClosed E] [Group.IsPerfect P] (h3 : (3 : E) ≠ 0)
    (ρ : P →* Matrix (Fin 3) (Fin 3) E) {z : P} (hz : ∀ g, ρ z * ρ g = ρ g * ρ z)
    (hz3 : ρ z ^ 3 = 1) (hz1 : ρ z ≠ 1) :
    ∃ l : E, orderOf l = 3 ∧ ρ z = l • (1 : Matrix (Fin 3) (Fin 3) E) := by
  set C := ρ z with hCdef
  obtain ⟨v, hv⟩ : ∃ v, C.mulVec v ≠ v := by
    by_contra h
    exact hz1 (Item426.eq_one_of_mulVec_eq fun v => by
      by_contra hv
      exact h ⟨v, hv⟩)
  set Q := C ^ 2 + C + 1 with hQ
  set U := LinearMap.ker (Matrix.toLin' Q) with hU
  have hQC : Q * C = C * Q := by rw [hQ]; noncomm_ring
  have hCU : ∀ x ∈ U, Matrix.toLin' C x ∈ U := by
    intro x hx
    rw [hU, LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hQC, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero]
  set w := C.mulVec v - v with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hv
  have hwU : w ∈ U := by
    rw [hU, LinearMap.mem_ker, Matrix.toLin'_apply, hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    have h1 : Q * C = C ^ 3 + C ^ 2 + C := by rw [hQ]; noncomm_ring
    have h2 : C ^ 3 + C ^ 2 + C = Q + (C ^ 3 - 1) := by rw [hQ]; noncomm_ring
    rw [h1, h2, hz3, sub_self, add_zero, sub_self]
  have : Nontrivial U := ⟨⟨⟨w, hwU⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' C).restrict hCU)
  obtain ⟨u, hu, hu0⟩ := hl.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hu
  have hCu : C.mulVec (u : Fin 3 → E) = l • (u : Fin 3 → E) := by
    have := congrArg Subtype.val hu
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
  have hu0' : (u : Fin 3 → E) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hl2 : l ^ 2 + l + 1 = 0 := by
    have hQu : Q.mulVec (u : Fin 3 → E) = 0 := by
      have hu2 : (u : Fin 3 → E) ∈ LinearMap.ker (Matrix.toLin' Q) := u.2
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hu2
      exact hu2
    have hQu' : Q.mulVec (u : Fin 3 → E) = (l ^ 2 + l + 1) • (u : Fin 3 → E) := by
      rw [hQ, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, sq,
        ← Matrix.mulVec_mulVec, hCu, Matrix.mulVec_smul, hCu, smul_smul, add_smul, add_smul,
        one_smul, sq]
    rw [hQu'] at hQu
    exact (smul_eq_zero.mp hQu).resolve_right hu0'
  have hl3 : l ^ 3 = 1 := by linear_combination (l - 1) * hl2
  have hl1 : l ≠ 1 := by
    intro h
    rw [h] at hl2
    apply h3
    linear_combination hl2
  have hlo : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  set W := Module.End.eigenspace (Matrix.toLin' C) l with hWdef
  have huW : (u : Fin 3 → E) ∈ W := by
    rw [hWdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hCu
  have hW : W ≠ ⊥ := fun h => hu0' (by rw [h] at huW; exact huW)
  have hinv : ∀ g, ∀ x ∈ W, (ρ g) *ᵥ x ∈ W := fun g x hx =>
    Item426.mulVec_mem_eigenspace (hz g) hx
  have hlW : ∀ x ∈ W, (ρ z) *ᵥ x = l • x := fun x hx => by
    rw [hWdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
    exact hx
  have hpow := pow_finrank_eq_one ρ hinv hlW
  have htop : W = ⊤ := eq_top_of_three_dvd_finrank hW (by
    have h := orderOf_dvd_of_pow_eq_one hpow
    rwa [hlo] at h)
  refine ⟨l, hlo, Item426.eq_smul_one_of_mulVec_eq fun x => ?_⟩
  exact hlW x (htop ▸ Submodule.mem_top)

theorem eq_smul_one_of_perfect_commute [IsAlgClosed E] [Group.IsPerfect P] (h3 : (3 : E) ≠ 0)
    (ρ : P →* Matrix (Fin 3) (Fin 3) E) {z : P} (hz : ∀ g, ρ z * ρ g = ρ g * ρ z)
    (hz3 : ρ z ^ 3 = 1) (hz1 : ρ z ≠ 1) {Y : Matrix (Fin 3) (Fin 3) E}
    (hY : ∀ g, Y * ρ g = ρ g * Y) : ∃ μ : E, Y = μ • (1 : Matrix (Fin 3) (Fin 3) E) := by
  obtain ⟨l, hlo, hl⟩ := eq_smul_one_of_perfect h3 ρ hz hz3 hz1
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  obtain ⟨u, hu, hu0⟩ := hμ.exists_hasEigenvector
  set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hWdef
  have hW : W ≠ ⊥ := fun h => hu0 (by
    have hu' : u ∈ W := hu
    rw [h] at hu'
    exact hu')
  have hinv : ∀ g, ∀ x ∈ W, (ρ g) *ᵥ x ∈ W := fun g x hx =>
    Item426.mulVec_mem_eigenspace (hY g) hx
  have hlW : ∀ x ∈ W, (ρ z) *ᵥ x = l • x := fun x _ => by
    rw [hl, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hpow := pow_finrank_eq_one ρ hinv hlW
  have htop : W = ⊤ := eq_top_of_three_dvd_finrank hW (by
    have h := orderOf_dvd_of_pow_eq_one hpow
    rwa [hlo] at h)
  refine ⟨μ, Item426.eq_smul_one_of_mulVec_eq fun x => ?_⟩
  have hx : x ∈ W := htop ▸ Submodule.mem_top
  rw [hWdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
  exact hx

theorem exists_scalar_of_perfect {F : Type*} [Field F] [Group.IsPerfect P] (h3 : (3 : F) ≠ 0)
    (ρ : P →* Matrix (Fin 3) (Fin 3) F) {z : P} (hz : ∀ g, ρ z * ρ g = ρ g * ρ z)
    (hz3 : ρ z ^ 3 = 1) (hz1 : ρ z ≠ 1) {y : Matrix (Fin 3) (Fin 3) F}
    (hy : ∀ g, y * ρ g = ρ g * y) : ∃ μ : F, y = Matrix.scalar (Fin 3) μ := by
  set E := AlgebraicClosure F
  set φ := algebraMap F E with hφ
  have hφi : Function.Injective φ := φ.injective
  set Φ := φ.mapMatrix (m := Fin 3) with hΦ
  have hΦi : Function.Injective Φ := by
    intro M N h
    rw [hΦ, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    exact Matrix.map_injective hφi h
  have h3E : (3 : E) ≠ 0 := by
    intro h
    apply h3
    apply hφi
    rw [map_ofNat, h, map_zero]
  let ρE : P →* Matrix (Fin 3) (Fin 3) E := (Φ : Matrix (Fin 3) (Fin 3) F →* _).comp ρ
  have hρE : ∀ g, ρE g = Φ (ρ g) := fun _ => rfl
  obtain ⟨μ, hμ⟩ := eq_smul_one_of_perfect_commute h3E ρE (z := z)
    (fun g => by rw [hρE, hρE, ← map_mul Φ, ← map_mul Φ, hz g])
    (by rw [hρE, ← map_pow Φ, hz3, map_one])
    (fun h => hz1 (hΦi (by rw [← hρE, h, map_one])))
    (Y := Φ y) (fun g => by rw [hρE, ← map_mul Φ, ← map_mul Φ, hy g])
  have hent : ∀ i j, φ (y i j) = if i = j then μ else 0 := fun i j => by
    have := congrFun (congrFun hμ i) j
    rw [hΦ, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨y 0 0, Matrix.ext fun i j => ?_⟩
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    apply hφi
    rw [hent, hent]
    simp
  · apply hφi
    rw [hent, map_zero]
    simp [hij]

end CFSG.RankThree.PartTwo.Sec4.Item426Rest
