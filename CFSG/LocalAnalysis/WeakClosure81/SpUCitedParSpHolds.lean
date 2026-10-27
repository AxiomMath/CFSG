module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpCore
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem spUCited_parabolic_of_spRootSetup {L : Type} [Group L] [Finite L] {m n : ℕ}
    {R Sy : Subgroup L} (h : SpRootSetup L m n R Sy) :
    ∃ X₂ Pα : Subgroup L, RootParabolic R Sy X₂ Pα 1 := by
  obtain ⟨hm, hL, ⟨hcard, k, hmk, F, hFld, hFin, hF, e, he⟩, hSy, hSyR, hRSy⟩ := h
  letI : Field F := hFld
  letI : Finite F := hFin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_isSpGp hL
  let φ :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hφ : ∀ r : L, φ.toMonoidHom r = e (QuotientGroup.mk r) := fun _ => rfl
  have hk : 2 ≤ k := by omega
  obtain ⟨P, hPsy⟩ := hSy
  have hsurj : Function.Surjective φ.toMonoidHom := fun y => ⟨φ.symm y, by simp⟩
  let P' := Sylow.mapSurjective (f := φ.toMonoidHom) hsurj P
  have hP' : (P' : Subgroup _) = Sy.map φ.toMonoidHom := by
    dsimp only [P']
    rw [Sylow.coe_mapSurjective (f := φ.toMonoidHom), hPsy]
  have hcard' : Nat.card (R.map φ.toMonoidHom) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective φ.injective, hcard]
  have hRt' : ∀ x ∈ R.map φ.toMonoidHom, x ≠ 1 → IsSymplecticTransvectionIn k x := by
    intro x hx hx1
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    have hr1 : r ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    rw [hφ r]
    exact he r hr hr1
  have hRSy' : R.map φ.toMonoidHom ≤ Sy.map φ.toMonoidHom := Subgroup.map_mono hRSy
  have hSyR' : Sy.map φ.toMonoidHom ≤
      Subgroup.normalizer (R.map φ.toMonoidHom : Set _) :=
    (Subgroup.map_mono hSyR).trans (Subgroup.le_normalizer_map φ.toMonoidHom)
  exact rootParabolic_exists_of_mulEquiv φ
    (spUCited_exists_rootParabolic_statedSp (n := n) hF hk (R.map φ.toMonoidHom) hcard' hRt'
      ⟨P', hP'⟩ hRSy' hSyR')

end CFSG.LocalAnalysis.WeakClosure81

end
