module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native
open scoped Pointwise

@[expose] def line0 : Finset (Fin 819) := {pt0, ⟨1, by norm_num⟩, ⟨5, by norm_num⟩}


@[expose] def d4H : Subgroup D := Subgroup.centralizer ({d4z} : Set D)

@[expose] noncomputable def d4N : Subgroup D := MulAction.stabilizer D line0

@[expose] noncomputable def d4B : Subgroup D := d4H ⊓ d4N

theorem mem_d4H_iff (g : D) : g ∈ d4H ↔ g • pt0 = pt0 := by
  rw [smul_pt0_iff, d4H, Subgroup.mem_centralizer_singleton_iff]

theorem mem_d4H_iff_act (g : D) : g ∈ d4H ↔ act g pt0 = pt0 := mem_d4H_iff g

theorem smul_line0 (g : D) : g • line0 = line0.image (act g) := by
  ext p
  simp only [Finset.mem_smul_finset, Finset.mem_image, smul_pt_def]

theorem mem_d4N_iff (g : D) : g ∈ d4N ↔ g • line0 = line0 := Iff.rfl

theorem mem_d4N_iff_image (g : D) : g ∈ d4N ↔ line0.image (act g) = line0 := by
  rw [mem_d4N_iff, smul_line0]

theorem mem_d4B_iff (g : D) : g ∈ d4B ↔ g • pt0 = pt0 ∧ g • line0 = line0 := by
  rw [d4B, Subgroup.mem_inf, mem_d4H_iff]
  rfl

end CFSG.Quasithin.D4Hex
