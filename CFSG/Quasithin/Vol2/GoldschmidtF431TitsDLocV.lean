module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Klein

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45
  CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.TitsLoc CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem zD_sq : zD * zD = 1 := ιD_injective (by rw [map_mul, ιD_zD, map_one]; exact zM_sq)

theorem z1D_sq : z1D * z1D = 1 :=
  ιD_injective (by rw [map_mul, ιD_z1D, map_one]; exact z1M_sq)

theorem zD_z1D_comm : zD * z1D = z1D * zD :=
  ιD_injective (by rw [map_mul, map_mul, ιD_zD, ιD_z1D]; exact V_rels.2.1)

theorem zD_mul_z1D : zD * z1D = z2D :=
  ιD_injective (by rw [map_mul, ιD_zD, ιD_z1D, ιD_z2D]; exact V_rels.1)

theorem zD_ne_one : zD ≠ 1 := fun h => zM_ne_one (by rw [← ιD_zD, h, map_one])

theorem z1D_ne_one : z1D ≠ 1 := fun h => z1M_ne_one (by rw [← ιD_z1D, h, map_one])

theorem zD_ne_z1D : zD ≠ z1D := fun h => V_rels.2.2 (by rw [← ιD_zD, ← ιD_z1D, h])

@[expose] noncomputable def VD : Subgroup ↥titsD := kleinFour zD z1D zD_sq z1D_sq zD_z1D_comm

theorem mem_VD {x : ↥titsD} : x ∈ VD ↔ x = 1 ∨ x = zD ∨ x = z1D ∨ x = z2D := by
  rw [VD, mem_kleinFour, zD_mul_z1D]

theorem card_VD : Nat.card VD = 4 := card_kleinFour zD_ne_one z1D_ne_one zD_ne_z1D

theorem ιD_mem_VM {x : ↥titsD} (h : x ∈ VD) : ιD x ∈ VM := by
  rcases mem_VD.1 h with rfl | rfl | rfl | rfl
  · rw [map_one]
    exact VM.one_mem
  · rw [ιD_zD]
    exact mem_VM.2 (Or.inr (Or.inl rfl))
  · rw [ιD_z1D]
    exact mem_VM.2 (Or.inr (Or.inr (Or.inl rfl)))
  · rw [ιD_z2D]
    exact mem_VM.2 (Or.inr (Or.inr (Or.inr rfl)))

theorem mem_VD_of_ιD {x : ↥titsD} (h : ιD x ∈ VM) : x ∈ VD := by
  rw [mem_VD]
  rcases mem_VM.1 h with h | h | h | h
  · exact Or.inl (ιD_injective (by rw [h, map_one]))
  · exact Or.inr (Or.inl (ιD_injective (by rw [h, ιD_zD])))
  · exact Or.inr (Or.inr (Or.inl (ιD_injective (by rw [h, ιD_z1D]))))
  · exact Or.inr (Or.inr (Or.inr (ιD_injective (by rw [h, ιD_z2D]))))

theorem mem_cent_tD_iff {x : ↥titsD} : x ∈ Subgroup.centralizer ({tD} : Set ↥titsD) ↔
    ιD x ∈ Subgroup.centralizer ({tM} : Set ↥twoF4M) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← ιD_tD,
    ← map_mul, ← map_mul]
  exact ⟨fun h => by rw [h], fun h => ιD_injective h⟩

theorem V_le_D : VD ≤ Subgroup.centralizer ({tD} : Set ↥titsD) :=
  fun _ hv => mem_cent_tD_iff.2 (V_le_model (ιD_mem_VM hv))

theorem V_norm_D : ∀ x ∈ Subgroup.centralizer ({tD} : Set ↥titsD), ∀ v ∈ VD, x * v * x⁻¹ ∈ VD := by
  intro x hx v hv
  apply mem_VD_of_ιD
  have := V_norm_model (ιD x) (mem_cent_tD_iff.1 hx) (ιD v) (ιD_mem_VM hv)
  simpa [map_mul, map_inv] using this

theorem cD_mem_cent : cD ∈ Subgroup.centralizer ({tD} : Set ↥titsD) :=
  mem_cent_tD_iff.2 cM_mem_cent

theorem V_conj_D : ∀ v ∈ VD, v ≠ 1 →
    ∃ x ∈ Subgroup.centralizer ({tD} : Set ↥titsD), v = x * zD * x⁻¹ := by
  intro v hv hne
  rcases mem_VD.1 hv with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · exact ⟨1, Subgroup.one_mem _, by simp⟩
  · exact ⟨cD, cD_mem_cent, rfl⟩
  · exact ⟨cD⁻¹, Subgroup.inv_mem _ cD_mem_cent, by unfold z2D; rw [inv_inv]⟩

end CFSG.Quasithin.H13.F431.TitsD
