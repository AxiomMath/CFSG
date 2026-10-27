module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsMap
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutStab
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Inn

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

section Theta

@[expose] noncomputable def d3Theta (hK : autStab d4H ⊔ autStab d4N = ⊤) :
    MulAut D ≃* d3Setting.ι.G0 :=
  (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hK.symm)).trans
    (MulEquiv.ofBijective d3Phi ⟨d3Phi_injective, d3Phi_surjective⟩)

theorem d3ToAut_d3Theta (hK : autStab d4H ⊔ autStab d4N = ⊤) (α : MulAut D) :
    d3ToAut (d3Theta hK α) = α := rfl

theorem d3Theta_symm_eq (hK : autStab d4H ⊔ autStab d4N = ⊤) (k : d3Setting.ι.G0) :
    (d3Theta hK).symm k = d3ToAut k := by
  rw [← d3ToAut_d3Theta hK ((d3Theta hK).symm k), MulEquiv.apply_symm_apply]

theorem d3_mem_Mb1_iff (k : d3Setting.ι.G0) : k ∈ d3Setting.Mb1 ↔ d3ToAut k ∈ autStab d4H := by
  rw [← mem_range_φ1_iff_d3]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem d3_mem_Mb2_iff (k : d3Setting.ι.G0) : k ∈ d3Setting.Mb2 ↔ d3ToAut k ∈ autStab d4N := by
  rw [← mem_range_φ2_iff_d3]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem d3_Mb1_eq (hK : autStab d4H ⊔ autStab d4N = ⊤) :
    d3Setting.Mb1 = (autStab d4H).map (d3Theta hK).toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, d3_mem_Mb1_iff, d3Theta_symm_eq hK]

theorem d3_Mb2_eq (hK : autStab d4H ⊔ autStab d4N = ⊤) :
    d3Setting.Mb2 = (autStab d4N).map (d3Theta hK).toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, d3_mem_Mb2_iff, d3Theta_symm_eq hK]

theorem d3_N_eq (hK : autStab d4H ⊔ autStab d4N = ⊤) :
    d3Setting.N = (MulAut.conj : D →* MulAut D).range.map (d3Theta hK).toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, d3Theta_symm_eq hK]
  exact mem_d3NN_iff k

end Theta

section Data

theorem d3_card_Yb (hK : autStab d4H ⊔ autStab d4N = ⊤) :
    Nat.card d3Setting.Yb = Nat.card (MulAut D) := by
  rw [← RankTwoAmalgam.Completion.card_G0 d3Setting.ι]
  exact Nat.card_congr (d3Theta hK).toEquiv.symm

theorem d3_card_N (hK : autStab d4H ⊔ autStab d4N = ⊤)
    (hinj : Function.Injective (MulAut.conj : D →* MulAut D)) :
    Nat.card d3Setting.N = Nat.card D := by
  rw [d3_N_eq hK]
  have e1 : ↥((MulAut.conj : D →* MulAut D).range.map (d3Theta hK).toMonoidHom) ≃*
      ↥(MulAut.conj : D →* MulAut D).range :=
    (Subgroup.equivMapOfInjective _ _ (d3Theta hK).injective).symm
  rw [Nat.card_congr e1.toEquiv]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem d3_F431LieI_G0 (hK : autStab d4H ⊔ autStab d4N = ⊤) {T : Subgroup (MulAut D)}
    {z t : MulAut D} (h : F431LieI T (autStab d4H) (autStab d4N) z t) :
    F431LieI (T.map (d3Theta hK).toMonoidHom) d3Setting.Mb1 d3Setting.Mb2 (d3Theta hK z)
      (d3Theta hK t) := by
  rw [d3_Mb1_eq hK, d3_Mb2_eq hK]
  exact F431LieI.map (d3Theta hK) h

end Data

section Involutions

@[expose] noncomputable def d3ZH : ↥(autStab d4H) :=
  ⟨MulAut.conj d4z, conj_mem_autStab_of_mem ((mem_d4H_iff_mul_z d4z).2 rfl)⟩

theorem d3ZH_val : ((d3ZH : ↥(autStab d4H)) : MulAut D) = MulAut.conj d4z := rfl

@[expose] noncomputable def d3TH : ↥(autStab d4H) :=
  ⟨MulAut.conj d4t, conj_mem_autStab_of_mem (Subgroup.mem_inf.1 (d4U_le_d4B d4t_mem_d4U)).1⟩

end Involutions

end CFSG.Quasithin.D4Hex
