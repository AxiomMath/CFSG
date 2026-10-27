module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentV
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentL
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentSyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Aut

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.Sec53F.G2
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


variable {K : Type} [Field K] [CharP K 2] [Finite K]

omit [Finite K] in
theorem V_aut_of_fix {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (φ : MulAut (C K))
    (hφ : φ (xv 1) = xv 1) : ∀ v ∈ V K, φ v ∈ V K := by
  obtain ⟨g, σ, rfl⟩ := exists_conj_fieldAut hf hK φ
  intro v hv
  have hσ : fieldAut K σ (xv 1) = xv 1 := fieldAut_xv_one σ
  have hg : g ∈ Subgroup.centralizer ({xv 1} : Set (C K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * xv 1 * g⁻¹ = xv 1 := by
      simpa [MulAut.mul_apply, MulAut.conj_apply, hσ] using hφ
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hv' : fieldAut K σ v ∈ V K := (fieldAut_mem_autStab_V σ v).mp hv
  simpa [MulAut.mul_apply, MulAut.conj_apply] using Cent.V_normalized hg hv'

theorem g2_stdLoc {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    StdLoc (C K) (U K) (xc 1) (xv 1) (V K) (Cent.La K) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact
    { comm := (cc_vc 1 1).eq.symm
      sylow_t := Cent.sylow_cent_xv
      V_le := Cent.V_le_cent_xv
      V_ab := fun _ ha _ hb => Cent.V_comm ha hb
      V_two := fun _ ha => Cent.V_sq ha
      V_ne := Cent.V_ne_bot
      V_aut := fun φ hφ v hv => V_aut_of_fix hf hK φ hφ v hv
      V_z := fun _ hv hv1 => Cent.V_conj_z hv hv1
      L_le := Cent.La_le_cent_xv
      L_ns := Cent.not_isSolvable_La h4
      L_V := Cent.isSolvable_La_inf_cent_V h4 }

end CFSG.Quasithin.H13.F431.G2
