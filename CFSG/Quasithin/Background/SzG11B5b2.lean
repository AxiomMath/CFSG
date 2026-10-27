module

public import CFSG.Quasithin.Background.SzG11SB5b
public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.SzG11B5b1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

theorem g115bPart1 : G115bPart1 := by
  intro V _ _ _ B Γ v₁ W X X₀ hG hirr ⟨x, hxX, hx1, hxF⟩
  by_contra hno
  have hcomm : ∀ L : Subgroup (GLV V), IsComponentOf L Γ → ∀ x ∈ X, ∀ l ∈ L, x * l = l * x := by
    intro L hL x hx l hl
    by_contra h
    exact hno ⟨L, hL, x, hx, l, hl, h⟩
  have : Finite (GLV V) :=
    Finite.of_injective (fun e : GLV V => (e : V → V)) DFunLike.coe_injective
  have hxΓ : x ∈ Γ := hG.X_le hxX
  let y : ↥Γ := ⟨x, hxΓ⟩
  have hy : y * y = 1 := Subtype.ext (hG.X_sq x hxX)
  obtain ⟨N, hNn, hNp, hyN⟩ := B5b.exists_normal_two_subgroup (Y := ↥Γ) hy
    (fun f hf => Subtype.ext (hxF (f : GLV V) ⟨f, hf, rfl⟩).symm)
    (fun L hL l hl => Subtype.ext
      (hcomm _ (B5b.isComponentOf_map_subtype Γ hL) x hxX (l : GLV V) ⟨l, hl, rfl⟩).symm)
  have hN2 : N ≤ Open.pCore 2 ↥Γ := CFSG.LieType.BorelTits.le_pCore 2 hNn hNp
  have hxO : x ∈ pCoreOf 2 Γ := Subgroup.map_mono hN2 ⟨y, hyN, rfl⟩
  rw [pCoreOf_eq_bot_of_isIrr_top hirr, Subgroup.mem_bot] at hxO
  exact hx1 hxO

end SzG11S

end G11

end CFSG.Quasithin
