module

public import CFSG.Quasithin.H13.HSLocNorm
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R1Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.RankThree.Native CFSG.Open

theorem factHSNormLv_holds :
    CFSG.Quasithin.H13.FactHSNormLv := by
  intro X _ _ hXe B P E hA α hαE hαB
  obtain ⟨φ⟩ := hXe
  let ψ : X ≃* PG := φ.trans hs100Equiv
  obtain ⟨⟨-, -, -, -, -, ⟨e, he, -⟩, -⟩, -⟩ := CTUC_HS_McL_full_automorphism_permutation_models
  let α' : MulAut PG := ψ.symm.trans (α.trans ψ)
  have hα'apply : ∀ x : X, α' (ψ x) = ψ (α x) := by
    intro x
    show ψ (α (ψ.symm (ψ x))) = ψ (α x)
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨r, hr⟩ := e.surjective α'
  have hrconj : ∀ p : PG, ((α' p : PG) : Equiv.Perm (Fin 100)) =
      (r : Equiv.Perm (Fin 100)) * (p : Equiv.Perm (Fin 100)) * (r : Equiv.Perm (Fin 100))⁻¹ := by
    intro p
    rw [← hr]
    exact he r p
  have hcomm : ∀ p : PG, α' p = p →
      (r : Equiv.Perm (Fin 100)) * (p : Equiv.Perm (Fin 100)) =
        (p : Equiv.Perm (Fin 100)) * (r : Equiv.Perm (Fin 100)) := by
    intro p hp
    have h := hrconj p
    rw [hp] at h
    exact mul_inv_eq_iff_eq_mul.mp h.symm
  let E' : Subgroup PG := E.map ψ.toMonoidHom
  let B' : Subgroup PG := B.map ψ.toMonoidHom
  let P' : Subgroup PG := P.map ψ.toMonoidHom
  have hrE : ∀ z ∈ E', (r : Equiv.Perm (Fin 100)) * (z : Equiv.Perm (Fin 100)) =
      (z : Equiv.Perm (Fin 100)) * (r : Equiv.Perm (Fin 100)) := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
    refine hcomm _ ?_
    have := hα'apply z₀
    rw [show ψ.toMonoidHom z₀ = ψ z₀ from rfl, this, hαE z₀ hz₀]
  have hrB : ∀ b ∈ B', (r : Equiv.Perm (Fin 100)) * (b : Equiv.Perm (Fin 100)) =
      (b : Equiv.Perm (Fin 100)) * (r : Equiv.Perm (Fin 100)) := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    refine hcomm _ ?_
    have := hα'apply b₀
    rw [show ψ.toMonoidHom b₀ = ψ b₀ from rfl, this, hαB b₀ hb₀]
  have hperf : ⁅B', B'⁆ = B' := by
    rw [← Subgroup.map_commutator, hA.perfect]
  have hcardB : Nat.card B' = 360 * Nat.card P' := by
    rw [Subgroup.card_map_of_injective ψ.injective, Subgroup.card_map_of_injective ψ.injective]
    exact hA.card
  have hEP : E' ≤ P' := Subgroup.map_mono hA.le_P
  have hEab : IsElemAbelian 2 E' := CFSG.Open.IsElemAbelian.map hA.elemAbelian _
  have hEcard : Nat.card E' = 16 := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hA.card_E
  have hBnorm : B' ≤ Subgroup.normalizer (E' : Set PG) := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    have hbn := Subgroup.mem_normalizer_iff.mp (hA.normalizes_E hb₀)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e1 : h ∈ E' ↔ ψ.symm h ∈ E := Subgroup.mem_map_equiv
    have e2 : ψ.toMonoidHom b₀ * h * (ψ.toMonoidHom b₀)⁻¹ ∈ E' ↔ b₀ * ψ.symm h * b₀⁻¹ ∈ E := by
      rw [show E' = E.map ψ.toMonoidHom from rfl, Subgroup.mem_map_equiv]
      simp
    rw [e1, e2]
    exact hbn (ψ.symm h)
  have hr1 : (r : Equiv.Perm (Fin 100)) = 1 :=
    normLv_PG hperf hcardB hEP hEab hEcard hBnorm r.2 hrE hrB
  have hr1' : r = 1 := Subtype.ext hr1
  have hα'1 : α' = 1 := by rw [← hr, hr1', map_one]
  apply MulEquiv.ext
  intro x
  have h1 := hα'apply x
  rw [hα'1] at h1
  exact ψ.injective h1.symm

end CFSG.Quasithin.H13.LocDbl.HSLoc
