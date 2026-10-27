module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDescent
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDiag
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUJ
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUNbr
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUAut
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQTwoXInL_frame_unitary
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI : GGQTwoI1 Bs D J) (hxL : x ∈ L)
    (hA : GGQTwoXInLAmbOn (fun t => t = .twA) Bs (ggG0 3 B x L D J)) :
    ∃ (n : ℕ) (_ : 3 ∣ n) (_ : 6 ≤ n) (y : G) (K : Subgroup G) (hx : x ∈ Bs) (hy : y ∈ Bs)
      (ι : Additive ↥Bs ≃+ ↥(GGQTwoXInLAug n)), GGNbr 3 B x D J y K ∧
      (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin (n + 1)), σ 0 = 0 ∧
          ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
            ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
              (v : Fin (n + 1) → ZMod 3) (σ i)} ∧
      (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin (n + 1)), σ 1 = 1 ∧
          ∀ (v : ↥(GGQTwoXInLAug n)) (i : Fin (n + 1)),
            ((T v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
              (v : Fin (n + 1) → ZMod 3) (σ i)} ∧
      ((ι (Additive.ofMul ⟨x, hx⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
        (fun i => if i = 0 then 0 else -1) ∧
      ((ι (Additive.ofMul ⟨y, hy⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
        (fun i => if i = 1 then 0 else -1) := by
  obtain ⟨N, F, _, _, ⟨M⟩, hN⟩ := ggQTwoXInLU_descent hS hxL hA
  obtain ⟨Fr⟩ := ggQTwoXInLU_frame hS hA.1 hN M
  obtain ⟨n, hn3, hn6, ⟨C⟩⟩ := ggQTwoXInLU_coord hS hxL hN Fr
  obtain ⟨C', hJ, hD⟩ := ggQTwoXInLU_coordJ hS hI hn3 hn6 C
  obtain ⟨y, hy, hnb, hιy⟩ := ggQTwoXInLU_nbr hS hn3 hn6 C' hJ hD
  have hL := ggQTwoXInLU_automizer hS hn6 C' 0
    (by rw [← C'.L_eq]; exact ggNSPosPD_routeCfg_cent_L hS.1.1)
  have hK := ggQTwoXInLU_automizer hS hn6 C' 1
    (ggNSPosPD_routeCfg_cent_K Nat.prime_three hnb)
  rw [← C'.L_eq] at hL
  exact ⟨n, hn3, hn6, y, _, C'.mem_x, hy, C'.ι, hnb, hL, hK, C'.ι_x, hιy⟩

end CFSG.StandardType

end
