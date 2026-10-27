module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab2Card
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

variable (h : OneSide A B z V)

include h

theorem pCoreOf_inf_centralizer_eq_coreIn :
    pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) =
      coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  apply le_antisymm
  · have hBN : B ≤ Subgroup.normalizer
        ((pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) : Subgroup D) : Set D) :=
      le_normalizer_inf (le_normalizer_pCoreOf 2 B)
        ((le_normalizer_conjClosure V B).trans (normalizer_le_normalizer_centralizer _))
    refine le_coreIn (inf_le_left.trans (pCoreOf_le 2 B)) hBN fun x hx => ⟨?_, hx.1⟩
    have hmem : x ∈ A ⊓ B ⊓ Subgroup.centralizer (V : Set D) :=
      ⟨h.gold.pCoreOf_right_le hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        Subgroup.mem_centralizer_iff.mp hx.2 v (le_conjClosure V B hv)⟩
    rwa [inf_inf_centralizer_eq_pCoreOf h.nat] at hmem
  · intro x hx
    have hxR : x ∈ pCoreOf 2 A ⊓ pCoreOf 2 B := by simpa using hx.2 1 B.one_mem
    refine ⟨hxR.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hUc : conjClosure V B ≤ Subgroup.centralizer ({x} : Set D) := by
      refine conjClosure_le fun k hk v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hq : k⁻¹ * y * k * v = v * (k⁻¹ * y * k) :=
        Subgroup.mem_centralizer_iff.mp (h.nat.le_center hv).2 _ (hx.2 k hk).1
      calc y * (k * v * k⁻¹) = k * ((k⁻¹ * y * k) * v) * k⁻¹ := by group
        _ = k * (v * (k⁻¹ * y * k)) * k⁻¹ := by rw [hq]
        _ = (k * v * k⁻¹) * y := by group
    exact (Subgroup.mem_centralizer_iff.mp (hUc hu) x rfl).symm

end GoldAmLab3

end F6

end CFSG.Quasithin
