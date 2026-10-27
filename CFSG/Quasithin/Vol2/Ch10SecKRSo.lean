module

public import CFSG.Quasithin.Vol2.Ch10SecKRSg

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin
open scoped Matrix

variable {G : Type} [Group G] {J W : Subgroup G} (C : AltCoord J W)

namespace AltCoord

theorem E_one : C.E 1 = 0 := by
  have h := C.map_mul 1 W.one_mem 1 W.one_mem
  rw [mul_one] at h
  have h2 : C.E 1 + C.E 1 = C.E 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem mem_centralizer_of_rho {j : ↥J} (hj : C.ρ j = 1) :
    (j : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hja : (j : G) * a * (j : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (C.le j.2) a).mp ha
  have h1 := C.conj j a ha
  rw [hj] at h1
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one] at h1
  have h2 := C.inj _ hja a ha h1
  calc a * (j : G) = (j : G) * a * (j : G)⁻¹ * (j : G) := by rw [h2]
    _ = (j : G) * a := by group

theorem ker_two [Finite G] (hCJ : J ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 J) {j : ↥J}
    (hj : C.ρ j = 1) : ∃ m : ℕ, (j : G) ^ 2 ^ m = 1 :=
  C10P4F.exists_two_pow_of_mem_pCoreOf (L := J) (hCJ ▸
    (⟨j.2, C.mem_centralizer_of_rho hj⟩ : (j : G) ∈ J ⊓ Subgroup.centralizer (W : Set G)))

theorem E_eq_B0 {u : G} (huW : u ∈ W) (hu1 : u ≠ 1)
    (hfix : ∀ g ∈ C10P4F.uniSL 5, ∃ j : ↥J, C.ρ j = g ∧ (j : G) * u * (j : G)⁻¹ = u) :
    C.E u = B0 := by
  rcases fix_alt_of_uniSL (C.mem u) (fun g hg => by
    obtain ⟨j, rfl, hj⟩ := hfix g hg
    rw [← C.conj j u huW, hj]) with h | h
  · exact absurd (C.inj u huW 1 W.one_mem (by rw [h, C.E_one])) hu1
  · exact h

theorem mem_centralizer_iff {u : G} (huW : u ∈ W) (hE : C.E u = B0) (j : ↥J) :
    (j : G) ∈ Subgroup.centralizer ({u} : Set G) ↔
      (C.ρ j : Matrix (Fin 5) (Fin 5) (ZMod 2)) * B0 *
        (C.ρ j : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = B0 := by
  have hju : (j : G) * u * (j : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (C.le j.2) u).mp huW
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : (j : G) * u * (j : G)⁻¹ = u := by rw [h]; group
    rw [← hE, ← C.conj j u huW, h1]
  · intro h
    have h1 := C.conj j u huW
    rw [hE, h, ← hE] at h1
    have h2 := C.inj _ hju u huW h1
    calc (j : G) * u = (j : G) * u * (j : G)⁻¹ * (j : G) := by group
      _ = u * (j : G) := by rw [h2]

end AltCoord

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
