module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDel
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_layer (hBal : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L : Subgroup G} (hThmI : GGThmIHyp p B x L) {b' y : G} (hb'1 : b' ≠ 1)
    (hyH : y ∈ Subgroup.centralizer ({b'} : Set G)) (hy3 : y ^ 3 = 1) {J : Subgroup G}
    (hJ : IsComponentOf J (Subgroup.centralizer ({b'} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G))) (h3 : 3 ∣ Nat.card ↥J) :
    J ≤ LargeEvenPLayer 3 (Subgroup.centralizer ({b'} : Set G)) := by
  have : IsSimpleGroup G := hThmI.1
  have hHne : Subgroup.centralizer ({b'} : Set G) ≠ ⊤ :=
    centralizer_singleton_ne_top_of_isSimpleGroup hThmI.2.1 hb'1
  have hKH : CFSG.Open.lBalanceIsKGroup ↥(Subgroup.centralizer ({b'} : Set G)) :=
    lBalanceIsKGroup_of_kProper hThmI.2.2.1 hHne
  have hJle : J ≤ CFSG.Open.lBalancePLayer 3 (Subgroup.centralizer ({b'} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) :=
    le_sSup (lBalanceIsPComponent_of_isComponentOf hJ (not_le_lBalancePrimeCore_of_dvd h3))
  rw [largeEvenPLayer_eq_lBalancePLayer]
  exact hJle.trans (lBalancePLayer_inf_centralizer_le_of_input hBal Nat.prime_three hKH hyH hy3)

omit [Finite G] in
theorem ggQTwoDUnitSix_centralizer_inv (b : G) :
    Subgroup.centralizer ({b⁻¹} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * b = b * (b⁻¹ * g) * b := by group
      _ = b * (g * b⁻¹) * b := by rw [h]
      _ = b * g := by group
  · intro h
    calc g * b⁻¹ = b⁻¹ * (b * g) * b⁻¹ := by group
      _ = b⁻¹ * (g * b) * b⁻¹ := by rw [h]
      _ = b⁻¹ * g := by group

omit [Finite G] in
theorem ggQTwoDUnitSix_map_centralizer_conj (g y : G) :
    (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g * w * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * w * g⁻¹)
    calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
      _ = g * (y * w) * g⁻¹ := by rw [hw]
      _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group
  · intro hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    refine ⟨g⁻¹ * z * g, ?_, by change g * (g⁻¹ * z * g) * g⁻¹ = z; group⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [hz]
      _ = y * (g⁻¹ * z * g) := by group

omit [Finite G] in
theorem ggQTwoDUnitSix_conj_comp {b' x g : G} (hgb : g * b' * g⁻¹ = b'⁻¹) {J : Subgroup G}
    (hJ : IsComponentOf J (Subgroup.centralizer ({b'} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G))) :
    IsComponentOf (J.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({b'} : Set G) ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G)) := by
  have hmap : (Subgroup.centralizer ({b'} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({b'} : Set G) ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ggQTwoDUnitSix_map_centralizer_conj,
      hgb, ggQTwoDUnitSix_centralizer_inv, ggQTwoDUnitSix_map_centralizer_conj]
  rw [← hmap]
  exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mpr hJ

end CFSG.StandardType.QTwo

end
