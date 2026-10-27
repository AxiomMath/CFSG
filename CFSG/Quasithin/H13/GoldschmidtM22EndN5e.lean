module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN3e

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

omit [Finite G] in
include hZ in
theorem Z_sq_eq_one {z : G} (hz : z ∈ quasithinOmegaOneCenter T) : z ^ 2 = 1 := by
  have h1 := pow_card_eq_one' (G := ↥(quasithinOmegaOneCenter T)) (x := ⟨z, hz⟩)
  rw [hZ] at h1
  exact congrArg Subtype.val h1

omit [Finite G] in
include hk hZ in
theorem pow_four_eq_one {d : G} (hd : d ∈ D) : d ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsExtraspecial 2 ↥D := hk.extra.1
  have hQel : CFSG.IsElementaryAbelian 2 (↥D ⧸ Subgroup.center ↥D) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian 2 ↥D
  have h1 : ((⟨d, hd⟩ : ↥D) : ↥D ⧸ Subgroup.center ↥D) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 (↥D ⧸ Subgroup.center ↥D)) _
  have h2 : (⟨d, hd⟩ : ↥D) ^ 2 ∈ Subgroup.center ↥D := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h1
  have h3 : d ^ 2 ∈ quasithinOmegaOneCenter T := by
    rw [← hk.center_eq]
    refine ⟨D.pow_mem hd 2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨y, hy⟩)
  calc d ^ 4 = (d ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := Z_sq_eq_one hZ h3

end KData

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in
theorem CHU_le_T (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1)
    (h629 : Stmt6_2_9) (h6210 : Stmt6_2_10) (h6212 : Stmt6_2_12) : CHU T L V ≤ T := by
  intro x hx
  have : x ∈ HH T ⊓ M :=
    ⟨centralizerMod_le_left _ _ _ hx, (h621 G T M L V h).2 (CHU_le_normalizer_V h h6210 hx)⟩
  rwa [P.HH_inf_M_eq_T h hZ h629 h6210 h6212] at this

end PsiData

end CFSG.Quasithin.H13.GM22
