module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4Torus
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeF4TorusDiag

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (torusSU)

theorem rhoTFrame_conj_eq_torusSU {E : Subgroup (GL (Fin 6) F4)} (hE : E ≤ SU0)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h3 : ∀ a ∈ E, a ^ 3 = 1)
    (hcard : 3 ^ 5 ≤ Nat.card E) :
    ∃ y ∈ GU0, E.map (MulAut.conj y⁻¹).toMonoidHom = torusSU 3 6 F4 := by
  obtain ⟨y, hy, hle⟩ := exists_conj_le_torusSU hE hcomm h3
  refine ⟨y, hy, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective]
  exact (CFSG.RankThree.PartOne.KFU.card_torusSU_le (K := F4) (by norm_num) 5).trans hcard

theorem rhoTFrame_mem_torus_iff {E : Subgroup (GL (Fin 6) F4)} {y : GL (Fin 6) F4}
    (hD : E.map (MulAut.conj y⁻¹).toMonoidHom = torusSU 3 6 F4) {d : GL (Fin 6) F4} :
    d ∈ torusSU 3 6 F4 ↔ y * d * y⁻¹ ∈ E := by
  rw [← hD]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have e : y * ((MulAut.conj y⁻¹).toMonoidHom a) * y⁻¹ = a := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact ha
  · intro h
    refine ⟨y * d * y⁻¹, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem rhoTFrame_isDiag {E : Subgroup (GL (Fin 6) F4)} {y z : GL (Fin 6) F4}
    (hD : E.map (MulAut.conj y⁻¹).toMonoidHom = torusSU 3 6 F4)
    (hz : ∀ a ∈ E, ∃ c : F4, (z : Matrix (Fin 6) (Fin 6) F4) * (a : Matrix (Fin 6) (Fin 6) F4) =
      c • ((a : Matrix (Fin 6) (Fin 6) F4) * (z : Matrix (Fin 6) (Fin 6) F4))) :
    ((y⁻¹ * z * y : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).IsDiag := by
  apply isDiag_of_conj_torusSU_eq_smul
  intro d hd
  obtain ⟨a, ha_eq⟩ : ∃ a : GL (Fin 6) F4, a = y * d * y⁻¹ := ⟨_, rfl⟩
  have ha : a ∈ E := by rw [ha_eq]; exact (rhoTFrame_mem_torus_iff hD).1 hd
  have hd' : y⁻¹ * a * y = d := by rw [ha_eq]; group
  obtain ⟨c, hc⟩ := hz a ha
  refine ⟨c, ?_⟩
  have key : ((z * a * z⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      c • (a : Matrix (Fin 6) (Fin 6) F4) := by
    simp only [Units.val_mul]
    rw [hc, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have e : (y⁻¹ * z * y) * d * (y⁻¹ * z * y)⁻¹ = y⁻¹ * (z * a * z⁻¹) * y := by
    rw [← hd']
    group
  rw [e, Units.val_mul, Units.val_mul, key, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
    ← Units.val_mul, hd']

end CFSG.GGQ2Prime
