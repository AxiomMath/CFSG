module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.StandardType.SignedPermCount

theorem P9_N3a_card_dvd {K : Type} [Group K] {r : ℕ} {A : Subgroup (MulAut K)}
    (Θ : (Fin r → Multiplicative (ZMod 3)) ≃* ↥A)
    (hreal : ∀ (α : MulAut K) (hn : α ∈ Subgroup.normalizer (A : Set (MulAut K))),
      SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    Nat.card (ggAutomizer (⊤ : Subgroup (MulAut K)) A) ∣ 2 ^ r * r.factorial := by
  let e : MulAut ↥A →* MulAut (Fin r → Multiplicative (ZMod 3)) :=
    (MulAut.congr Θ).symm.toMonoidHom
  have he : Function.Injective e := (MulAut.congr Θ).symm.injective
  have hle : ggAutomizer (⊤ : Subgroup (MulAut K)) A ≤ (signedPermSubgroup 3 r).comap e := by
    intro φ hφ
    rw [Subgroup.mem_comap]
    obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    have hEq : φ = ggConjAut A hgN := MulEquiv.ext fun b => Subtype.ext (hφg b)
    rw [hEq]
    exact hreal g hgN
  have hdvd := (Subgroup.card_dvd_of_le hle).trans
    (Subgroup.card_comap_dvd_of_injective (signedPermSubgroup 3 r) e he)
  rwa [card_signedPermSubgroup Nat.prime_three (by norm_num)] at hdvd

end CFSG.StandardType.FrameRoute

end
