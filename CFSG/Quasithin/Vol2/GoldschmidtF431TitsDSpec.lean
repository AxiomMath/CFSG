module

public import Certificates.Certificate4182
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocMain
public import CFSG.Quasithin.Recognition.CertTitsTwoLocal
public import CFSG.Sporadic.Schreier.TitsCentral

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45
  CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.TitsLoc CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false

theorem mem_titsS_of_S {x : Equiv.Perm (Fin 1755)} (h : Certificates.c4182S x) : x ∈ titsS := by
  obtain ⟨hD, h0, hl⟩ := h
  rw [← titsH_inf_titsN]
  exact Subgroup.mem_inf.2 ⟨mem_titsH_of hD h0, mem_titsN_of hD hl⟩

theorem mem_titsS_of_twoF4S {x : Equiv.Perm (Fin 1755)} (hxD : x ∈ titsD) (hxS : x ∈ twoF4S) :
    x ∈ titsS :=
  mem_titsS_of_S ⟨hxD, (mem_twoF4S_iff (titsD_le_titsA hxD)).1 hxS⟩

theorem S_of_mem_titsS {x : Equiv.Perm (Fin 1755)} (h : x ∈ titsS) : Certificates.c4182S x := by
  rw [← titsH_inf_titsN] at h
  obtain ⟨hH, hN⟩ := Subgroup.mem_inf.1 h
  exact ⟨titsH_le_titsD hH, fix_zero_of_mem_titsH hH, line_fix_of_mem_titsN hN⟩

theorem mem_titsSD {x : ↥titsD} (h : Certificates.c4182S x.1) : x ∈ titsSD :=
  Subgroup.mem_subgroupOf.2 (mem_titsS_of_S h)

theorem tEl_mem_titsS : tEl.1 ∈ titsS := by
  obtain ⟨h, -⟩ := Certificates.certificate4182
  rw [← tEl_eq] at h
  exact mem_titsS_of_twoF4S h tEl_mem_S

theorem cEl_mem_titsD : cEl.1 ∈ titsD := by
  have h := Subgroup.sq_mem_of_index_two titsD_index (⟨cEl.1, cEl.2⟩ : ↥TA)
  have h2 : cEl.1 ^ 2 ∈ titsD := h
  have h3 : cEl.1 = (cEl.1 ^ 2)⁻¹ := by
    have := cEl_pow.1
    rw [eq_comm, inv_eq_iff_mul_eq_one]
    rw [← this]
    group
  rw [h3]
  exact titsD.inv_mem h2

theorem qEl_eq : (wEl dqWord).1 = Certificates.c4182Q := by
  have e : decodeWord dqWord =
      [(2, true), (1, true), (1, true), (2, true), (3, true), (0, true), (3, false)] := by decide
  simp [wEl, e, wordElt, letterElt, kgen_val, Certificates.c4182Q, mul_assoc]

theorem qEl_mem_titsS : (wEl dqWord).1 ∈ titsS := by
  obtain ⟨-, ⟨h, -⟩, -⟩ := Certificates.certificate4182
  rw [← qEl_eq] at h
  exact mem_titsS_of_S h

@[expose] noncomputable def zD : ↥titsD := ⟨titsZ, titsZ_mem_titsD⟩

@[expose] noncomputable def tD : ↥titsD := ⟨tEl.1, titsS_le_titsD tEl_mem_titsS⟩

@[expose] noncomputable def cD : ↥titsD := ⟨cEl.1, cEl_mem_titsD⟩

@[expose] noncomputable def qD : ↥titsD := ⟨(wEl dqWord).1, titsS_le_titsD qEl_mem_titsS⟩

@[expose] noncomputable def z1D : ↥titsD := cD * zD * cD⁻¹

@[expose] noncomputable def z2D : ↥titsD := cD⁻¹ * zD * cD

@[expose] noncomputable def ιD : ↥titsD →* ↥twoF4M := Subgroup.inclusion titsD_le_twoF4M

theorem ιD_injective : Function.Injective ιD := Subgroup.inclusion_injective _

theorem ιD_zD : ιD zD = zM := rfl

theorem ιD_tD : ιD tD = tM := rfl

theorem ιD_cD : ιD cD = cM := rfl

theorem ιD_z1D : ιD z1D = z1M := by
  simp only [z1D, z1M, map_mul, map_inv, ιD_zD, ιD_cD]

theorem ιD_z2D : ιD z2D = z2M := by
  simp only [z2D, z2M, map_mul, map_inv, ιD_zD, ιD_cD]

theorem qD_rels : qD * qD = zD ∧ qD * tD = tD * qD ∧ qD * z1D = z1D * qD := by
  obtain ⟨-, ⟨-, h1, h2, h3⟩, -⟩ := Certificates.certificate4182
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · change (wEl dqWord).1 * (wEl dqWord).1 = titsZ
    rw [qEl_eq]
    exact h1
  · change (wEl dqWord).1 * tEl.1 = tEl.1 * (wEl dqWord).1
    rw [qEl_eq, tEl_eq]
    exact h2
  · change (wEl dqWord).1 * (cEl.1 * titsZ * cEl.1⁻¹) = cEl.1 * titsZ * cEl.1⁻¹ * (wEl dqWord).1
    rw [qEl_eq, cEl_eq]
    exact h3

end CFSG.Quasithin.H13.F431.TitsD
