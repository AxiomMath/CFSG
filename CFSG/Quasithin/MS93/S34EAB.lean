module

public import CFSG.Quasithin.MS93.S33Trans
public import CFSG.Quasithin.MS93.SkHyp

public section

namespace CFSG.Quasithin.MS93.S34E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem conj_ofT (h : PUHyp M T L) (φ : MulAut ↥T) (t : ↥T) :
    (puAmalgam h.le).ofB (SemidirectProduct.inr φ) * puAmalgam.ofT h.le t *
      ((puAmalgam h.le).ofB (SemidirectProduct.inr φ))⁻¹ = puAmalgam.ofT h.le (φ t) := by
  simp only [puAmalgam.ofT, MonoidHom.coe_comp, Function.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, Hol.inr_mul_inl_mul_inr_inv]

theorem ofT_mem_imM_iff (h : PUHyp M T L) {K : Subgroup G} (t : ↥T) :
    puAmalgam.ofT h.le t ∈ imM h.le K ↔ (t : G) ∈ K := by
  rw [← puAmalgam.ofA_inclusion, S33.ofA_mem_imM_iff]
  rfl

theorem mem_centralizer_of_ofT (h : PUHyp M T L) {K : Subgroup G} (hK : K ≤ M) (t : ↥T)
    (ht : puAmalgam.ofT h.le t ∈
      Subgroup.centralizer (imM h.le K : Set (puAmalgam h.le).Universal)) :
    (t : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : (puAmalgam h.le).ofA ⟨k, hK hk⟩ ∈ imM h.le K := (S33.ofA_mem_imM_iff h.le _).2 hk
  have h1 := Subgroup.mem_centralizer_iff.mp ht _ hk'
  rw [← puAmalgam.ofA_inclusion, ← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)

end Transport

end CFSG.Quasithin.MS93.S34E
