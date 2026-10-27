module

public import CFSG.Quasithin.Vol2.KGFactL52Mod10
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Psi
public import CFSG.Quasithin.Vol2.KGFactJ4L5NSDA

public section

namespace CFSG.Quasithin.H13.Ch4.J4NSD

open CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4 CFSG.Assembly.LowTwoRank

theorem singerInvMat_mul_singerMat : singerInvMat * singerMat = 1 := by decide +kernel

@[expose] noncomputable def singerGL : GL (Fin 5) (ZMod 2) :=
  ⟨singerMat, singerInvMat, singerMat_mul_singerInvMat, singerInvMat_mul_singerMat⟩

@[expose] noncomputable def sS : ↥(StatedSL 5 (ZMod 2)) := B5.Ln.ofGL singerGL

theorem orderOf_sS : orderOf sS = 31 := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ fun h => singerMat_ne_one ?_
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact singerMat_pow_31
  · have h1 := congrArg B5.Ln.mat h
    rwa [B5.Ln.mat_one] at h1

theorem trace_psiMat_sS_ne : Matrix.trace (psiMat sS) ≠ Matrix.trace (psiMat sS⁻¹) := by
  decide +kernel

theorem psi_ne_conj_inv {g : ↥(StatedSL 5 (ZMod 2))} (hg : orderOf g = 31)
    (W : GL (Fin 10) (ZMod 2)) : J4M4.psi g ≠ W * (J4M4.psi g)⁻¹ * W⁻¹ := by
  intro hX
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  obtain ⟨h, j, hj⟩ := exists_conj_zpow_eq (G := ↥(StatedSL 5 (ZMod 2))) (p := 31)
    (by rw [card_statedSL5']; norm_num) hg orderOf_sS
  have h1 : J4M4.psi sS = J4M4.psi h * J4M4.psi g ^ j * (J4M4.psi h)⁻¹ := by
    rw [← hj, map_mul, map_mul, map_zpow, map_inv]
  have e : (h * g ^ j * h⁻¹)⁻¹ = h * g⁻¹ ^ j * h⁻¹ := by group
  have h2 : J4M4.psi sS⁻¹ = J4M4.psi h * (J4M4.psi g)⁻¹ ^ j * (J4M4.psi h)⁻¹ := by
    rw [← hj, e, map_mul, map_mul, map_inv, map_zpow, map_inv]
  have h3 := conj_zpow_of_conj_inv hX (J4M4.psi h) j
  rw [← h1, ← h2] at h3
  apply trace_psiMat_sS_ne
  rw [← psi_coe, ← psi_coe]
  exact trace_eq_of_conj h3

end CFSG.Quasithin.H13.Ch4.J4NSD
