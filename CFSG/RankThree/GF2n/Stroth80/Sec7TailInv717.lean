module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1617
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec717InvStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) →
      A = Z0 ∨ A = hc.CN t ∨ Sec717L hc t Z0 A

theorem step717MaxAb_of_inv (hInv : Sec717InvStatement) : Step717MaxAbStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hcase hN' hF
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hZK : Z0 ≤ NormH0 M Z Z0 := fun z hz => hRK (hZ0.le hz)
  have hKM : NormH0 M Z Z0 ≤ M := fun x hx => hx.1.1
  have hQN : Q ≤ hc.CN t := fun x hx =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx,
      fun v hv => hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩
  refine ⟨hZK, fun x hx y hy => hZ0.comm_mem hx (hZ0.le hy),
    fun k hk => conjSubgroup_eq_self_iff.mpr hk.2, ?_⟩
  intro A hZA hAK hAn hAab
  have hAN : A ≤ hc.CN t := step716_le_of_fstar hKM hQN hAK hAn hAab hF
  have hRA : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A := fun r hr => hAn r (hRK hr)
  rcases hInv G M Q Z B hc n t hs hp3 Z0 hZ0 A hZA hAN hRA with h | h | hL
  · exact h
  · exfalso
    apply hN'
    refine Subgroup.commutator_le.mpr fun x hx y hy => hAab x ?_ y ?_
    · rw [h]; exact hx
    · rw [h]; exact hy
  · exfalso
    obtain ⟨k, hk, hne⟩ := hcase A hL
    exact hne (hAn k hk)

end CFSG.RankThree.GF2n.Stroth80
