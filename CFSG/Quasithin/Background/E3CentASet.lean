module

public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

theorem autI_mem_aSet_of_mem_gammaSet_of_add_lt (hV : IsElemAbelian 2 V)
    {H S U A : Subgroup G} (hSH : S ≤ H) (hUn : H ≤ Subgroup.normalizer (U : Set G))
    (hU : IsElemAbelian 2 U) {i n : ℕ} (hin : i + n < sParam hV) (hA : A ∈ gammaSet V i S)
    (hA1 : autI hU A ≠ ⊥) : autI hU A ∈ aSet (n + 1) (autI hU H) := by
  obtain ⟨hAS, g, hAg, hm⟩ := hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAS.trans (hSH.trans hUn)
  refine ⟨autI_mono hU (hAS.trans hSH), hA1, isElemAbelian2_autI hU hAel hAN, ?_⟩
  intro B' hB' hlt
  have hlt' : mQuot A (preI hU A hAN B') ≤ n := by
    rw [← mQuot_autI_preI hU hAN hB']
    omega
  have hBA : preI hU A hAN B' ≤ A := preI_le hU
  have hadd := mQuot_add (V := conjSubgroup V g) hBA hAg
  have hlt2 : mQuot (conjSubgroup V g) (preI hU A hAN B') < sParam hVg := by
    rw [sParam_conj hV g hVg]
    omega
  have hCB := (e3_6 hVg hBA hAg hlt2 (B2F.isPGroup_of_isElemAbelian hU)).1
  have hpre : autI hU (preI hU A hAN B') = B' := autI_preI hU hB'
  have hBN : preI hU A hAN B' ≤ Subgroup.normalizer (U : Set G) := hBA.trans hAN
  ext v
  have e1 : v ∈ fixV B' ↔ v.val ∈ Subgroup.centralizer (preI hU A hAN B' : Set G) := by
    conv_lhs => rw [← hpre]
    exact mem_fixV_autI hU hBN v
  have e2 : v ∈ fixV (autI hU A) ↔ v.val ∈ Subgroup.centralizer (A : Set G) :=
    mem_fixV_autI hU hAN v
  rw [e1, e2]
  have hv : v.val ∈ U := v.val_mem
  constructor
  · intro hc
    have : v.val ∈ U ⊓ Subgroup.centralizer (preI hU A hAN B' : Set G) :=
      Subgroup.mem_inf.2 ⟨hv, hc⟩
    rw [← hCB] at this
    exact (Subgroup.mem_inf.1 this).2
  · intro hc
    have : v.val ∈ U ⊓ Subgroup.centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
    rw [hCB] at this
    exact (Subgroup.mem_inf.1 this).2

end E3

end CFSG.Quasithin
