module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D3
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48GeomOf
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Inn
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexXD

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F48Gen CFSG.D4Hex
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Sec


@[expose] noncomputable def d3Sec : d3Setting.ι.G0 →* ↥(autStab d4H ⊔ autStab d4N) :=
  Subgroup.subtype _

theorem d3Phi_d3Sec (g : d3Setting.ι.G0) : d3Phi (d3Sec g) = g := rfl

theorem d3Sec_d3Phi (x : ↥(autStab d4H ⊔ autStab d4N)) : d3Sec (d3Phi x) = x := rfl

theorem d3Psi_mem_N (x : D) : d3Phi (d3Psi x) ∈ d3Setting.N :=
  (mem_d3NN_iff _).2 ⟨x, rfl⟩

end Sec

section Holds


theorem d3_qN (hN : ∀ α : MulAut D, α ∈ autStab d4N ↔ autLn α 0 = 0) :
    MulAut.conj (d4Word f48QWord) ∈ autStab d4N := by
  refine (hN _).2 ((autLn_zero_iff _).2 ?_)
  rw [autPt_conj]
  exact (hexAct_D4.mem_N _).1 d4_qN

@[expose] noncomputable def d3Rho1 : d3Setting.α.G1 →* Equiv.Perm (Fin 819) :=
  autPt.comp (autStab d4H).subtype

@[expose] noncomputable def d3Rho2 : d3Setting.α.G2 →* Equiv.Perm (Fin 819) :=
  autPt.comp (autStab d4N).subtype

theorem d3_ptRigid (hH : ∀ α : MulAut D, α ∈ autStab d4H ↔ autPt α pt0 = pt0)
    (hN : ∀ α : MulAut D, α ∈ autStab d4N ↔ autLn α 0 = 0)
    (Gm : HexGeomOf d3Setting ↥(autStab d4H ⊔ autStab d4N) d3Phi d3Sec) :
    PtRigid d3Setting ⟨MulAut.conj (d4Word f48NWord), d3_nH hH⟩
      ⟨MulAut.conj (d4Word f48QWord), d3_qN hN⟩ f48Order3 := by
  refine ptRigid_of_fin d3Setting Gm.κ d3Rho1 d3Rho2 lay0 (fun y z => ?_) (fun q z => ?_)
    Gm.κ_near ?_
  · have h : f1 (c := d3Setting.ι) y = d3Phi ⟨(show ↥(autStab d4H) from y).1,
        Subgroup.mem_sup_left (show ↥(autStab d4H) from y).2⟩ := rfl
    rw [h, Gm.κ_phi]
    rfl
  · have h : f2 (c := d3Setting.ι) q = d3Phi ⟨(show ↥(autStab d4N) from q).1,
        Subgroup.mem_sup_right (show ↥(autStab d4N) from q).2⟩ := rfl
    rw [h, Gm.κ_phi]
    rfl
  · intro π' hB hN' hX y
    refine d3_rigid hH hN π' (fun x hx hxN => ?_) (fun x hx p hp => ?_) hX y
    · exact hB ⟨x, Subgroup.mem_inf.2 ⟨hx, hxN⟩⟩
    · exact hN' ⟨x, hx⟩ p hp

theorem d3Psi_mem_B (x : D) (hx : x ∈ d4B) : d3Phi (d3Psi x) ∈ d3Setting.N ⊓
    (stv d3Setting.ι d3Setting.ι.xv ⊓ stv d3Setting.ι d3Setting.ι.lv) := by
  refine Subgroup.mem_inf.2 ⟨d3Psi_mem_N x, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · refine MulAction.mem_stabilizer_iff.2 ((d4_smul_xv_iff d3Setting.ι _).2 ?_)
    exact (mem_range_φ1_iff_d3 _).2 (conj_mem_autStab_of_mem (Subgroup.mem_inf.1 hx).1)
  · refine MulAction.mem_stabilizer_iff.2 ((d4_smul_lv_iff d3Setting.ι _).2 ?_)
    exact (mem_range_φ2_iff_d3 _).2 (conj_mem_autStab_of_mem (Subgroup.mem_inf.1 hx).2)

theorem d3_hfix_pts {w : Fin 819}
    (hw : ∀ b ∈ d3Setting.N ⊓ (stv d3Setting.ι d3Setting.ι.xv ⊓ stv d3Setting.ι d3Setting.ι.lv),
      d3Sec b • w = w) : w = pt0 :=
  d4_fixed_point fun x hx => by
    have h1 := hw _ (d3Psi_mem_B x hx)
    rw [d3Sec_d3Phi] at h1
    have e : (d3Psi x : ↥(autStab d4H ⊔ autStab d4N)) • w = act x w := by
      show autPt (MulAut.conj x) w = act x w
      rw [autPt_conj]
    rw [← e]
    exact h1

theorem d3_hNtr_pts (m : Fin 819) : ∃ g ∈ d3Setting.N, d3Sec g • pt0 = m := by
  obtain ⟨x, hx⟩ := exists_smul_pt0_eq m
  refine ⟨d3Phi (d3Psi x), d3Psi_mem_N x, ?_⟩
  rw [d3Sec_d3Phi]
  show autPt (MulAut.conj x) pt0 = m
  rw [autPt_conj]
  exact hx

theorem d3_toPerm_injective_K3 (hs : IsSimpleGroup D) :
    Function.Injective (MulAction.toPermHom ↥(autStab d4H ⊔ autStab d4N) (Fin 819)) :=
  fun a b h => Subtype.ext (autPt_injective hs (Equiv.ext fun m => by
    have := congrArg (fun σ : Equiv.Perm (Fin 819) => σ m) h
    exact this))

end Holds

end CFSG.Quasithin.D4Hex
