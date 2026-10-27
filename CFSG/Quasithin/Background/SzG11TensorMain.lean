module

public import CFSG.Quasithin.Background.SzG11STensor
public import CFSG.Quasithin.Background.SzG11TensorE
public import CFSG.Quasithin.Background.E11Main
public import CFSG.Quasithin.Background.SzG11TensorD

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

theorem om4PlusTensor : Om4PlusTensor := by
  intro V _ _ _ H C I hhom hI hfix hsum hend hd hfaith eH hcent eC
  obtain ⟨eH⟩ := eH
  obtain ⟨eC⟩ := eC
  obtain ⟨D⟩ := e11 V H I hhom hI hfix hsum
  have hF : Nat.card D.F = 4 := by
    rw [← Nat.card_congr D.endEquiv.toEquiv]
    exact hend
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨κ, hκmem, hκsurj⟩ := Tensor.exists_kappa D hF
  have hHperf := Tensor.commutator_eq_top_of_alt_five eH
  have hHcard := Tensor.natCard_of_alt_five eH
  have hCperf := Tensor.commutator_eq_top_of_alt_five eC
  have hCcard := Tensor.natCard_of_alt_five eC
  obtain ⟨J, φ, hIJ, hφ, hn4⟩ := Tensor.exists_complement_hiso hhom hI hfix hsum hd hfaith
    hHperf hHcard hCperf hCcard hcent κ hκsurj
  obtain ⟨α, ι, hι⟩ := Tensor.natural_module hK4 hn4 κ hHperf hHcard
    (restrictHom H I hI.1) (Tensor.restrictHom_injective hI.1 hfaith)
    (Tensor.kappa_comm κ hκmem hI.1)
  exact Tensor.natural_of_decomposition H C I J hIJ hI.1 α ι hι φ hφ hcent hCperf hCcard

end SzG11S

end G11

end CFSG.Quasithin
