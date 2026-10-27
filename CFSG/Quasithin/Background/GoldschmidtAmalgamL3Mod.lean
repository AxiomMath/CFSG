module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem inf_inf_centralizer_eq_pCoreOf (hn : IsNaturalAt A (A ⊓ B) z V) :
    A ⊓ B ⊓ Subgroup.centralizer (V : Set D) = pCoreOf 2 A := by
  rw [hn.cT, hn.centralizer_eq, pCoreOf_pCoreOf]

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem conjClosure_le_pCoreOf_right : conjClosure V B ≤ pCoreOf 2 B :=
  h.hypF91V.conjClosure_Vp_le_pCoreOf

theorem commutator_mem : ∀ u ∈ conjClosure V B, ∀ q ∈ pCoreOf 2 B,
    u * q * u⁻¹ * q⁻¹ ∈ Subgroup.zpowers z :=
  h.hypF91V.commutator_conjClosure_le

theorem pCoreOf_eq_centralizerMod :
    pCoreOf 2 B = centralizerMod (Subgroup.zpowers z) B (conjClosure V B) :=
  h.hypF91V.pCoreOf_eq_centralizerMod

theorem conjClosure_le_pCoreOf_left : conjClosure V B ≤ pCoreOf 2 A := by
  have hF := h.hypF91V
  refine conjClosure_le fun k hk x hx => ?_
  have hx' : k * x * k⁻¹ ∈ conjSub k V := mul_mem_conjSub hx
  have hxQ : k * x * k⁻¹ ∈ pCoreOf 2 B := hF.conjSub_le_pCoreOf h.le_pCoreOf_right hk hx'
  have hxU : k * x * k⁻¹ ∈ conjClosure V B := HypF91.conjSub_le_conjClosure hk hx'
  have hmem : k * x * k⁻¹ ∈ A ⊓ B ⊓ Subgroup.centralizer (V : Set D) :=
    ⟨h.gold.pCoreOf_right_le hxQ, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      isElemAbelian_comm h.abelian (le_conjClosure V B hv) hxU⟩
  rwa [inf_inf_centralizer_eq_pCoreOf h.natural] at hmem

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
    rwa [inf_inf_centralizer_eq_pCoreOf h.natural] at hmem
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
        Subgroup.mem_centralizer_iff.mp (h.natural.le_center hv).2 _ (hx.2 k hk).1
      calc y * (k * v * k⁻¹) = k * ((k⁻¹ * y * k) * v) * k⁻¹ := by group
        _ = k * (v * (k⁻¹ * y * k)) * k⁻¹ := by rw [hq]
        _ = (k * v * k⁻¹) * y := by group
    exact (Subgroup.mem_centralizer_iff.mp (hUc hu) x rfl).symm

theorem conjClosure_le_coreIn : conjClosure V B ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  rw [← h.pCoreOf_inf_centralizer_eq_coreIn]
  intro u hu
  exact ⟨h.conjClosure_le_pCoreOf_right hu, Subgroup.mem_centralizer_iff.mpr fun w hw =>
    isElemAbelian_comm h.abelian hw hu⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
