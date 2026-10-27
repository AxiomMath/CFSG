module

import CFSG.Quasithin.Background.HZCode22B
import CFSG.Quasithin.Background.HZCoc24C
public import CFSG.Quasithin.Background.HMathieuStd
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ZTrans

theorem card_fin_zmod_two (n : ℕ) : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

theorem vzModCode22_holds :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (z : V),
      MathieuCode22 H ⊤ ⊥ → z ≠ 1 → IsSylowVec82 H z →
      Nat.card ↥(parz82 H z) = 2 ^ 4 * 360 ∧ Nat.card V = 2 ^ 10 := by
  intro V _ _ H z h hz1 hS
  obtain ⟨S, hSH, hS, hzS⟩ := hS
  obtain ⟨e, he, hez⟩ := Code22.exists_equiv_z0 h hz1 hSH hS hzS
  refine ⟨?_, ?_⟩
  · have h1 : (parz82 H z).map (congrHom e) = parZ (Code22.imgC mog22) Code22.z0 := by
      rw [← he, ← hez]
      exact parZ_map e H z
    rw [← card_map_congrHom e (parz82 H z), h1, Code22.parZ_std]
    exact Code22.card_imgC_L22
  · rw [Nat.card_congr e.toEquiv]
    exact card_fin_zmod_two 10

theorem vzModCocode24_holds :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (z : V),
      MathieuCocode24 H ⊤ ⊥ → z ≠ 1 → IsSylowVec82 H z →
      Nat.card ↥(parz82 H z) = 2 ^ 6 * 1080 ∧ Nat.card V = 2 ^ 11 := by
  intro V _ _ H z h hz1 hS
  obtain ⟨S, hSH, hS, hzS⟩ := hS
  obtain ⟨e, he, hez⟩ := Coc24.exists_equiv_z0 h hz1 hSH hS hzS
  refine ⟨?_, ?_⟩
  · have h1 : (parz82 H z).map (congrHom e) =
        parZ (img11 CFSG.Monster.Code.AutPerm) Coc24.z0 := by
      rw [← he, ← hez]
      exact parZ_map e H z
    rw [← card_map_congrHom e (parz82 H z), h1, Coc24.parZ_std]
    exact Coc24.card_img11_Lz
  · rw [Nat.card_congr e.toEquiv]
    exact card_fin_zmod_two 11

end CFSG.Quasithin.H13
