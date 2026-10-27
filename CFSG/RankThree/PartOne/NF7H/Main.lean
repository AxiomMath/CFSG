module

public import CFSG.RankThree.PartOne.NF7H.ScalarInv
public import CFSG.RankThree.PartOne.NF7H.Lift
public import CFSG.RankThree.PartOne.N1322.Statements
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore
public import CFSG.RankThree.PartOne.S12.Sec127
public import CFSG.RankThree.PartOne.S12.Sec12FusGen

public section

namespace CFSG.RankThree.PartOne.NF7H

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N1322

theorem kf1322NF7Uinv_of_hGA
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
      ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
      RowModel p L 7 →
      ∀ (y u : G), y ∈ torusNormalizer E → u ∈ L → u ∈ torusNormalizer E →
        (∀ f ∈ E ⊓ L, u * f * u⁻¹ = f⁻¹) →
        ∀ v : G, v ∈ cNormalizer c → v ∈ torusNormalizer E →
          (∀ e ∈ E, v * e * v⁻¹ = (y * u * y⁻¹) * e * (y * u * y⁻¹)⁻¹) →
          ∀ h' : G, h' ∈ L → h' ∈ torusNormalizer E → ∀ k : ℤ,
            (∀ f ∈ E ⊓ L, v * f * v⁻¹ = h' * f ^ k * h'⁻¹) → ∀ f ∈ E ⊓ L, f ^ (k * k) = f := by
  intro G _ _ p A c L E h12 hF12 _ _ _ _ hmodel y u hyW huL huW huinv v hvc hvW hvact h' hh'L hh'W k hk
  classical
  have hrow := hmodel
  obtain ⟨f₀, hf1, -, hmod⟩ := hrow
  have hZL : Subgroup.center ↥L = ⊥ := KF132.psp_two_center_trivial hGA hf1 hF12.isQuasisimple_L hmod
  have hG : Sec12TwoGeneric p c L E := KF132.sec12TwoGeneric_of_center_bot hF12 hZL
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h12 hG
  obtain ⟨u₀, hu₀L, hu₀F, hu₀sq, hu₀inv⟩ := row7_exists_involution_lift hcore hmodel hZL
  have hcomm : ∀ l ∈ L, c * l = l * c := Sec12Three.comm_c_L h12
  have hu₀W : u₀ ∈ torusNormalizer E := by
    have hlc : u₀ ∈ cNormalizer c :=
      Sec12Fus.mem_cNormalizer_of_commute (hcomm u₀ hu₀L).symm
    have hE : E = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
    rw [torusNormalizer, hE]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hu₀F, hlc⟩
  have hinv₀ : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right hu₀sq
  have hcE : c ∈ E := h12.A_le_E h12.c_mem
  set z : G := u₀⁻¹ * u with hz
  have hzF : ∀ f ∈ E ⊓ L, z * f = f * z := by
    intro f hf
    have h1 : u₀ * f⁻¹ * u₀⁻¹ = f⁻¹⁻¹ := hu₀inv f⁻¹ ((E ⊓ L).inv_mem hf)
    have h2 : z * f * z⁻¹ = f := by
      calc z * f * z⁻¹ = u₀⁻¹ * (u * f * u⁻¹) * u₀ := by rw [hz]; group
        _ = u₀⁻¹ * f⁻¹ * u₀ := by rw [huinv f hf]
        _ = u₀ * f⁻¹ * u₀⁻¹ := by rw [hinv₀]
        _ = f := by rw [h1, inv_inv]
    calc z * f = z * f * z⁻¹ * z := by group
      _ = f * z := by rw [h2]
  have hzc : z * c = c * z := by
    have hcu : Commute c u := hcomm u huL
    have hcu₀ : Commute c u₀ := hcomm u₀ hu₀L
    exact (((hcu₀.inv_right).mul_right hcu).eq).symm
  have hEz : ∀ e ∈ E, z * e = e * z := by
    have hE : E = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
    have hle : E ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hE]
      refine sup_le (fun f hf => ?_) (fun e he => ?_)
      · exact (Subgroup.mem_centralizer_singleton_iff.2 (hzF f hf).symm)
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
        exact (Subgroup.mem_centralizer_singleton_iff.2
          ((Commute.zpow_right (show Commute z c from hzc) j).eq.symm))
    intro e he
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm
  set v₀ : G := y * u₀ * y⁻¹ with hv₀
  have hv₀sq : v₀ * v₀ = 1 := by
    calc v₀ * v₀ = y * (u₀ * u₀) * y⁻¹ := by rw [hv₀]; group
      _ = 1 := by rw [hu₀sq]; group
  have hv₀W : v₀ ∈ torusNormalizer E :=
    (torusNormalizer E).mul_mem ((torusNormalizer E).mul_mem hyW hu₀W)
      ((torusNormalizer E).inv_mem hyW)
  have hv₀act : ∀ e ∈ E, v₀ * e * v₀⁻¹ = v * e * v⁻¹ := by
    intro e he
    have he' : y⁻¹ * e * y ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 ((torusNormalizer E).inv_mem hyW) e).1 he
      simpa using this
    have h1 : u * (y⁻¹ * e * y) * u⁻¹ = u₀ * (y⁻¹ * e * y) * u₀⁻¹ := by
      have := hEz _ he'
      calc u * (y⁻¹ * e * y) * u⁻¹ = u₀ * (z * (y⁻¹ * e * y)) * u⁻¹ := by rw [hz]; group
        _ = u₀ * ((y⁻¹ * e * y) * z) * u⁻¹ := by rw [this]
        _ = u₀ * (y⁻¹ * e * y) * u₀⁻¹ := by rw [hz]; group
    rw [hvact e he]
    calc v₀ * e * v₀⁻¹ = y * (u₀ * (y⁻¹ * e * y) * u₀⁻¹) * y⁻¹ := by rw [hv₀]; group
      _ = y * (u * (y⁻¹ * e * y) * u⁻¹) * y⁻¹ := by rw [h1]
      _ = (y * u * y⁻¹) * e * (y * u * y⁻¹)⁻¹ := by group
  have hv₀c : v₀ ∈ cNormalizer c := by
    apply Sec127.mem_cNormalizer_of_conj_mem
    rw [hv₀act c hcE]
    exact (Subgroup.mem_normalizer_iff.1 hvc c).1 (Subgroup.mem_zpowers c)
  have hv₀L : v₀ ∈ Subgroup.normalizer (L : Set G) := hF12.twoB ⟨hv₀c, hv₀W⟩
  have hv₀F : v₀ ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hv₀W, hv₀L⟩
  have hh'F : h' ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hh'W, Subgroup.le_normalizer hh'L⟩
  exact row7_scalar_involution hcore hmodel hv₀L hv₀F hv₀sq hh'L hh'F
    (fun f hf => (hv₀act f (Subgroup.mem_inf.1 hf).1).trans (hk f hf))

end CFSG.RankThree.PartOne.NF7H
