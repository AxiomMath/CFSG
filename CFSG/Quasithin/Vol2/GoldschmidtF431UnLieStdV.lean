module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieBridgeB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieMapA
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieTwoD

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Quasithin CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Quasithin.H13.F431.Un.OL CFSG.LocalAnalysis.ComponentInitial

theorem centerOf_eq_of_ab {G : Type*} [Group G] {H : Subgroup G}
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : centerOf H = H := by
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
  show x ∈ Subgroup.centralizer (H : Set G)
  rw [Subgroup.mem_centralizer_iff]
  exact fun y hy => hab y hy x hx

section Miyamoto

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem unStdV_Xg (hf : 2 ≤ f) :
    UnStdV (Xg h) (Psy h) (Pt h) (Ln h) (z1X h) (z2X h) (A1X h) where
  V4_le := A1X_le_Psy h
  V4_ab a ha b hb := A1X_ab h ha hb
  V4_sq a ha := A1X_sq h ha
  V4_zt := ⟨z1X_mem_A1X h, z2X_mem_A1X h⟩
  V4_eq := by
    rw [pCoreOf_Ln h]
    exact (centerOf_eq_of_ab fun a ha b hb => A1X_ab h ha hb).symm
  V4_unique E hE hab hsq hcard := V4_unique_Xg h hE hab hsq hcard
  z_ZP := z_ZP_Xg h hf
  ZP_trans x hx hx1 := ZP_trans_Xg h hf hx hx1
  cz := cz_Xg h
  ct := ct_Xg h
  nz := nz_Xg h
  nt := nt_Xg h

end Miyamoto

section Datum

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 f)) [Fact ((ζ : F) ≠ 0)]

theorem unStdV_datum (hf : 2 ≤ f) :
    UnStdV (SU (unitaryInvolution F 2 f) 4) (unU hF 4) (unSystem hF ζ).P₂ (unSystem hF ζ).P₁
      (zUn hF) (tUn hF) (v4Un hF ζ) := by
  have h1 : 1 ≤ f := one_le_two.trans hf
  have := unStdV_map (brEps hF h1) (unStdV_Xg (brFD hF h1) hf)
  rwa [brEps_map_Psy hF h1, brEps_map_Pt hF h1 ζ, brEps_map_Ln hF h1 ζ, brEps_z1X hF h1,
    brEps_z2X hF h1, brEps_map_A1X hF h1 ζ] at this

end Datum

end CFSG.Quasithin.H13.F431.Un
