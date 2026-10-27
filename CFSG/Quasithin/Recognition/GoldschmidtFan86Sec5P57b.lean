module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P57a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Run
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P57



section Mirror

variable (F : FanTree Γ G)
include F

theorem comm_mirror (ℓ : Line Γ) {z z' : G} {a b tL tR a' b' tL' tR' : ℤ} (hz2 : z * z = 1)
    (hz'2 : z' * z' = 1) (hd : ℓ.IsCoreFix z a b tL tR) (hd' : ℓ.IsCoreFix z' a' b' tL' tR')
    (hr : 1 ≤ tR - b) (hpl : tR = a') (hpr : tL' = b) :
    z' * (z * z' * z⁻¹) * (z' * (z * z' * z⁻¹)) = 1 ∧
      z' * (z * z' * z⁻¹) ∈ Cen (ℓ.edgeCirc (G := G) (tR - 1)) := by
  have e1 := P55.fix_tL_le hd
  have e2 := P55.fix_a_lt hd
  have e3 := P55.fix_le_tR hd
  have e4 := P55.fix_tL_le hd'
  have e5 := P55.fix_a_lt hd'
  have e6 := P55.fix_le_tR hd'
  have hvp : Γ.Adj (ℓ.vert tR) (ℓ.vert (tR + 1)) := ℓ.adj tR
  have hvq : Γ.Adj (ℓ.vert tR) (ℓ.vert (tR - 1)) := ℓ.adj_pred tR
  have hz'q : z' • ℓ.vert (tR - 1) = ℓ.vert (tR - 1) := (hd'.fix (tR - 1)).2 ⟨by omega, by omega⟩
  have hz'v : z' • ℓ.vert tR = ℓ.vert tR := (hd'.fix tR).2 ⟨by omega, by omega⟩
  have hz'Kv : z' ∈ nbrStab Γ G (ℓ.vert tR) :=
    F.fix_two_nbrs hvq hvp (ℓ.vert_pred_ne_succ tR) hz'q ((hd'.fix (tR + 1)).2 ⟨by omega, by omega⟩)
  have hzK : z ∉ nbrStab Γ G (ℓ.vert tR) := fun h => by
    have := (hd.fix (tR + 1)).1 (mem_nbrStab.1 h _ hvp)
    omega
  have hzv : z • ℓ.vert tR = ℓ.vert tR := (hd.fix tR).2 ⟨by omega, le_rfl⟩
  have hzq : z • ℓ.vert (tR - 1) = ℓ.vert (tR - 1) := (hd.fix (tR - 1)).2 ⟨by omega, by omega⟩
  obtain ⟨hu2, hcomm⟩ := P57.mech F hvp hvq hz'2 hz2 hz'Kv
    (fun h h1 h2 => P58.central_first hd' (i := tR) (j := tR + 1) (by omega) (by omega) h h2 h1)
    hzv hzq hzK
  refine ⟨hu2, ?_, fun g hg => ?_⟩
  · have hz0 : z⁻¹ • ℓ.vert (tR - 1) = ℓ.vert (tR - 1) := inv_smul_eq_iff.2 hzq.symm
    have hz0' : z⁻¹ • ℓ.vert tR = ℓ.vert tR := inv_smul_eq_iff.2 hzv.symm
    refine P55.mem_edgeCirc_of_fix hu2 ?_ ?_
    · simp only [mul_smul, hz0, hz'q, hzq]
    · rw [sub_add_cancel]
      simp only [mul_smul, hz0', hz'v, hzv]
  · have hf := P58.edgeCirc_fix' (i := tR - 1) (j := tR) hg (by ring)
    have hcond := (P57.edgeCirc_cond F ℓ hg).2
    rw [sub_add_cancel] at hcond
    exact hcomm g hf.2 hf.1 hcond

end Mirror

end P57

theorem fan57bT (F : FanTree Γ G) (h53a : Fan53a F) (h53b : Fan53b F) (h53c : Fan53c F)
    (h54 : Fan54 F) (hfin : ZcFin F) : Fan57bT F := by
  intro h40 T z z' a b tL tR a' b' tL' tR' hz hz' hd hd' hpp
  have hr1 : 1 ≤ tR - b := (h53a h40 T.line z a b tL tR hz hd).1
  obtain ⟨-, -, hpl, hpr⟩ := hpp
  by_contra hgt
  have hgt' : 2 < tR - b := not_le.1 hgt
  obtain ⟨hne, hu2, hcen⟩ :=
    fan57a F h53a h53b h54 h40 T.line z z' a b tL tR a' b' tL' tR' hz hz' hd hd' hpr.symm
  obtain ⟨hu'2, hcen'⟩ := P57.comm_mirror F T.line hz.1 hz'.1 hd hd' hr1 hpl hpr
  have hz0 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.1
  have hz'0 : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'.1
  have hinv : z' * (z * z' * z⁻¹) = (fcomm z z')⁻¹ := by
    simp only [fcomm, mul_inv_rev, hz0, hz'0, mul_assoc]
  rw [hinv, inv_eq_of_mul_eq_one_right hu2] at hcen'
  have hZu : fcomm z z' ∈ T.line.Zc := ⟨hu2, b, hcen⟩
  obtain ⟨tL₂, tR₂, hfin'⟩ := hfin T _ hZu hne
  obtain ⟨a₁, b₁, hC₁, ha₁, hb₁⟩ := P55.core_exists hfin' hcen
  obtain ⟨a₂, b₂, hC₂, ha₂, hb₂⟩ := P55.core_exists hfin' hcen'
  obtain ⟨he1, he2⟩ := fan55b F h54 h40 T _ a₁ b₁ tL₂ tR₂ a₂ b₂ hZu ⟨hfin', hC₁⟩ hC₂
  have hlen := h53c h40 T.line _ a₁ b₁ hZu hC₁
  omega

end CFSG.Quasithin.Fan86
