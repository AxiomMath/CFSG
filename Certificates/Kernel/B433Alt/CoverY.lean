module

public import Certificates.Kernel.B433Alt.Stab
public import Certificates.Kernel.B433Alt.Omega

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.YGroups.Y442Tw CFSG.Certificates.CosetEnumeration
  CertificateChecks.KernelY442 CFSG.YGroups.DCE.B433 CFSG.KD.B4AN

theorem tfix_all : ∀ c ∈ yL, colAt CB c 0 = 0 := by
  intro c hc
  simp only [yL, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix0
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix1
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix2
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix3
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix4
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix5
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix6
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix8
  · exact Nat.eq_of_beq_eq_true CFSG.KD.B4AN.tfix9

@[expose] noncomputable def rootE (j i : ℕ) : ℕ := fld (RL j) (20 * i) (ones 20)

section

theorem cover_y {j : ℕ} (hj : j < 64) (hlive : 0 < LIVE &&& (1 <<< j)) (y : YGroup 4 3 2) :
    ∃ i < RN j, entryOK CFSG.KD.B4A.RD LIVE j (rootE j i) = true ∧
      ∃ z ∈ Subgroup.closure ((fun t => wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (genOf GS j t))) ''
        {t | t < GN j}), ∃ t ∈ lsub yL,
        psi y = psi z * psi (wVal (yGen 4 3 2) (CFSG.KD.B4A.PW (dPt (CFSG.KD.B4A.RD (rootE j i))))) *
          psi t := by
  obtain ⟨ρΩ, hcol, hF, hnet, htr⟩ := om
  have hF' : F432 ∈ ρΩ.ker := by rw [F432_eq_evalWord]; exact hF
  obtain ⟨i, hi, hent, s, hs, hx⟩ := cover_sound (MS := MS) (RD := CFSG.KD.B4A.RD)
    (RW := CFSG.KD.B4A.RW) (PW := CFSG.KD.B4A.PW) (CB := CB) (RN := RN) (RL := RL) (GS := GS)
    (GN := GN) (XO := XO) (SJ := SJ) (ST := ST) (SA := SA) (SN := SN) (STL := STL) (LIVE := LIVE)
    (NS := NSEG) (j := j) ρΩ rw_stab pw_ok hcol hnet (by decide +kernel) (fun k hk => seg_all k hk)
    (fin_all j hj)
    hlive (ρΩ y 0)
  refine ⟨i, hi, hent, ?_⟩
  rw [← Set.image_image (g := ρΩ) (f := fun t => wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (genOf GS j t))),
    ← MonoidHom.map_closure] at hs
  obtain ⟨z, hz, rfl⟩ := hs
  set p := wVal (yGen 4 3 2) (CFSG.KD.B4A.PW (dPt (CFSG.KD.B4A.RD (rootE j i))))
  have h0 : ρΩ ((z * p)⁻¹ * y) 0 = 0 := by
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, hx, map_mul, ← Equiv.Perm.mul_apply (ρΩ z),
      ← Equiv.Perm.mul_apply]
    simp [p, rootE]
  obtain ⟨t, ht, he⟩ := stab0 ρΩ (fun c hc => Fin.ext (by
      rw [hcol c (by simp only [yL, List.mem_cons, List.not_mem_nil, or_false] at hc; omega)]
      exact tfix_all c hc)) hF' htr h0
  have hk : t⁻¹ * ((z * p)⁻¹ * y) ∈ psi.ker := ker_rho432F_le_ker_psi (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel])
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, map_mul, map_inv, map_mul] at hk
  refine ⟨z, hz, t, ht, ?_⟩
  rw [hk]
  group

end

end CertificateChecks.KernelB433

end
