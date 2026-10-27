module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocL
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocVCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocVZ
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocVAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocSyl

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.D4q.Loc CFSG.Quasithin.H13.F431.Lift CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem x5C_mem_VaC (hσ : ∀ c, σ (σ (σ c)) = c) : x5C σ ∈ VaC σ :=
  mem_VaC_of_coord σ hσ (map_one σ) (map_zero σ) (d4x₅_eq_d4v σ 1)

theorem La_normalizes_VaC (hσ : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    ∀ l ∈ La σ, ∀ v ∈ VaC σ, l * v * l⁻¹ ∈ VaC σ := fun l hl v hv =>
  VaC_aut σ hσ hf hK hσq (MulAut.conj l) (by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (La_le_cent_tC σ hσ hl)
    rw [MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.2 h) v hv

theorem stdLoc_d4 (hσ : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    ∃ V L : Subgroup (Cm σ), StdLoc (Cm σ) (Ust σ) (zC σ) (tC σ hσ) V L :=
  ⟨VaC σ, La σ,
    { comm := comm_zC_tC σ hσ
      sylow_t := sylow_t_d4 σ hσ (by omega) hK hσq
      V_le := VaC_le_cent σ hσ
      V_ab := VaC_comm σ hσ
      V_two := VaC_two σ hσ
      V_ne := VaC_ne_bot σ hσ
      V_aut := VaC_aut σ hσ (by omega) hK hσq
      V_z := VaC_conj_z σ hσ
      L_le := La_le_cent_tC σ hσ
      L_ns := not_isSolvable_La σ hf hK (fun c => hσq c)
      L_V := isSolvable_La_inf_cent σ hf hK (fun c => hσq c)
        (La_normalizes_VaC σ hσ (by omega) hK hσq) (x5C_mem_VaC σ hσ) }⟩

end CFSG.Quasithin.H13.F431.D4q.StdLoc
