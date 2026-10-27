module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Realize
public import CFSG.Quasithin.Vol2.GoldschmidtH11Transport
public import CFSG.Quasithin.Vol2.GoldschmidtH11Core

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

open CFSG.Quasithin

theorem h11_main {V : Type} [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)) (a : ℕ)
    (ha : 1 < a) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hmodel : BinaryOrthogonalFour L ⊤ ⊥ a) (A : Subgroup (MulAut V)) (hAM : A ≤ M)
    (hA1 : A ≠ ⊥) (hel : IsElemAbelian2 A) : H11Concl a L A := by
  obtain ⟨K, _, _, _, hcard, hreal⟩ := hmodel
  obtain ⟨e, he⟩ := exists_equiv_of_realizes L a hcard hreal
  have hL : mapAut e L = Lh a hcard := by
    ext x
    rw [mem_mapAut, he, mem_Lh]
    constructor
    · rintro ⟨γ, hγ⟩
      refine ⟨γ, MulEquiv.ext fun w => ?_⟩
      obtain ⟨v, rfl⟩ := e.surjective w
      have := hγ v
      rw [congr_symm_apply', MulEquiv.apply_symm_apply] at this
      exact this.symm
    · rintro ⟨γ, rfl⟩
      refine ⟨γ, fun v => ?_⟩
      rw [congr_symm_apply', MulEquiv.apply_symm_apply]
  have hLM' : Lh a hcard ≤ mapAut e M := hL ▸ mapAut_mono e hLM
  have hMN' : mapAut e M ≤ Subgroup.normalizer (Lh a hcard : Set (MulAut (HV K a))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx0 := Subgroup.mem_normalizer_iff.mp (hMN ((mem_mapAut e).mp hx))
      ((MulAut.congr e).symm y)
    rw [← hL, mem_mapAut, mem_mapAut, map_mul, map_mul, map_inv]
    exact hx0
  have key := core ha hcard hLM' hMN' (mapAut_mono e hAM) (mapAut_ne_bot e hA1)
    (isElemAbelian2_mapAut e hel)
  rw [← hL] at key
  exact H11Concl_of_equiv e key

end CFSG.Quasithin.H11
