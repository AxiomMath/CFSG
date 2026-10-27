module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSCode
public import CFSG.Certificates.Kernel.S1277KGmSound
public import CFSG.Quasithin.Vol2.Ch12Sec7Orb

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin S127 CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277MLine
open scoped IsMulCommutative

@[expose] def Orb45 : Prop :=
  ∀ c < 64, (gm6.map (·.app c)).toFinset.card = 45 → ∃ B ∈ gm6, B.app 5 = c

section Orb

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_aut_dc5 (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) (horb : Orb45) {z : G} (hz : z ∈ V)
    (h45 : (Subgroup.centralizer ({z} : Set G)).relIndex L = 45) :
    ∃ a ∈ autOn L V, a (C.dc 5) = ⟨z, hz⟩ := by
  have h1 := card_orbitIn_autOn hLV (⟨z, hz⟩ : ↥V)
  have h2 := card_orbitIn_eq_orbitSize hC (⟨z, hz⟩ : ↥V)
  have h45' : orbitSize gm6 (C.cd ⟨z, hz⟩) = 45 := by
    rw [← h2, h1]
    exact h45
  have hcl : C.cd ⟨z, hz⟩ < 64 := C.cd_lt _
  rw [CFSG.KS.S1277Gm.orbitSize_eq_card] at h45'
  obtain ⟨B, hB, hBapp⟩ := horb _ hcl h45'
  obtain ⟨a, haB⟩ := hC.2 B hB
  have haIn : a ∈ autOn L V := (hC.1 a).2 (by rw [haB]; exact hB)
  refine ⟨a, haIn, C.cd_injective ?_⟩
  rw [C.cd_apply, C.cd_dc 5 (by norm_num), haB, hBapp]

theorem exists_coding_five (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C₀ : Coding ↥V}
    (hC₀ : IdentL C₀ (autOn L V)) (horb : Orb45) {z : G} (hz : z ∈ V)
    (h45 : (Subgroup.centralizer ({z} : Set G)).relIndex L = 45) :
    ∃ C : Coding ↥V, IdentL C (autOn L V) ∧ C.cd ⟨z, hz⟩ = 5 := by
  obtain ⟨a, ha, haz⟩ := exists_aut_dc5 hLV hC₀ horb hz h45
  refine ⟨C₀.recode a⁻¹, hC₀.recode ((autOn L V).inv_mem ha), ?_⟩
  rw [Coding.recode_cd, ← haz]
  have : a⁻¹ (a (C₀.dc 5)) = C₀.dc 5 := by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  rw [this]
  exact C₀.cd_dc 5 (by norm_num)

theorem exists_conj_of_45 (hLV : L ≤ Subgroup.normalizer (V : Set G)) {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) (horb : Orb45) {z z₁ : G} (hz : z ∈ V) (hz₁ : z₁ ∈ V)
    (h45 : (Subgroup.centralizer ({z} : Set G)).relIndex L = 45)
    (h45₁ : (Subgroup.centralizer ({z₁} : Set G)).relIndex L = 45) :
    ∃ l ∈ L, l * z * l⁻¹ = z₁ := by
  obtain ⟨a, ha, haz⟩ := exists_aut_dc5 hLV hC horb hz h45
  obtain ⟨a₁, ha₁, ha₁z⟩ := exists_aut_dc5 hLV hC horb hz₁ h45₁
  have hb : a₁ * a⁻¹ ∈ autOn L V := (autOn L V).mul_mem ha₁ ((autOn L V).inv_mem ha)
  obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).1 hb
  refine ⟨(l : G), l.2, ?_⟩
  have h1 : (a₁ * a⁻¹) (⟨z, hz⟩ : ↥V) = ⟨z₁, hz₁⟩ := by
    rw [← haz, ← ha₁z, MulAut.mul_apply]
    have : a⁻¹ (a (C.dc 5)) = C.dc 5 := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [this]
  rw [← hl] at h1
  exact congrArg Subtype.val h1

end Orb

end CFSG.Quasithin.H13.I1277

end
