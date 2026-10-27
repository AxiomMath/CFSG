module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggQTwoXInLU_heart {N : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K)
    (s : ↥(unitarySU 2 1 K N)) (t : Fin N → Kˣ) (hs : (s : GL (Fin N) K) = diagHom N t) :
    F.φ s ∈ Bs := by
  have hstar : GGBstar 3 B Bs := hS.1.1.2.1
  have hcard : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, F.field.card]
    norm_num
  have ht3 : t ^ 3 = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← hcard]
    exact pow_card_eq_one'
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hs, ← map_pow, ht3, map_one, Subgroup.coe_one]
  have hcent : F.φ s ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hcommd : diagHom N (F.δ b) * diagHom N t = diagHom N t * diagHom N (F.δ b) := by
      calc diagHom N (F.δ b) * diagHom N t = diagHom N (F.δ b * t) := (map_mul _ _ _).symm
        _ = diagHom N (t * F.δ b) := by rw [mul_comm]
        _ = diagHom N t * diagHom N (F.δ b) := map_mul _ _ _
    have hkey : (s : GL (Fin N) K) =
        diagHom N (F.δ b) * (s : GL (Fin N) K) * (diagHom N (F.δ b))⁻¹ := by
      rw [hs, hcommd, mul_inv_cancel_right]
    have hb1 : b * F.φ s * b⁻¹ = F.φ s := (F.pair b hb).2 s s hkey
    calc b * F.φ s = b * F.φ s * b⁻¹ * b := by group
      _ = F.φ s * b := by rw [hb1]
  exact hstar.2.2.2 (F.φ s) hcent (by rw [← map_pow, hs3, map_one])

end CFSG.StandardType

end
