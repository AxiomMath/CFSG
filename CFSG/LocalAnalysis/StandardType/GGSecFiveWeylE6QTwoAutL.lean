module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutLQ
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.USixTwo
open USixTwo TorConj TorHomKernel MainProof TorHyperplanes
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G} {ω : K}

private theorem center_eq_bot_of_mulEquiv (hK : Nat.card K = 4) {H : Type*} [Group H]
    (φ : H ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    Subgroup.center H = ⊥ := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hZR : Subgroup.center
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = ⊥ :=
    TableBUE.center_proj_eq_bot hK' (by norm_num) (by norm_num)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply φ.injective
  have hmem : φ z ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    rw [← Subgroup.map_center_eq φ]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  rw [hZR, Subgroup.mem_bot] at hmem
  simpa using hmem

private noncomputable def centerQuotientEquivTo {H : Type*} [Group H]
    (hZ : Subgroup.center H = ⊥) : H ⧸ Subgroup.center H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot)

private theorem centerQuotientEquivTo_apply {H : Type*} [Group H]
    (hZ : Subgroup.center H = ⊥) (l : H) :
    centerQuotientEquivTo hZ (QuotientGroup.mk' (Subgroup.center H) l) = l := by
  change QuotientGroup.quotientBot ((QuotientGroup.quotientMulEquivOfEq hZ)
    (QuotientGroup.mk' (Subgroup.center H) l)) = l
  have hmk : QuotientGroup.mk' (Subgroup.center H) l = QuotientGroup.mk l := rfl
  rw [hmk, QuotientGroup.quotientMulEquivOfEq_mk]
  change (QuotientGroup.kerLift (MonoidHom.id H)) (QuotientGroup.mk l) = l
  rw [QuotientGroup.kerLift_mk]
  rfl

private theorem exists_centerQuotientEquiv_comp_eq (hK : Nat.card K = 4)
    {Bs L : Subgroup G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K) :
    ∃ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
      IsPGroup 2 (Subgroup.center L) ∧
      (∀ l : L, θ (QuotientGroup.mk' (Subgroup.center L) l) = φ l) ∧
      ((Bs ⊓ L).subgroupOf L).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K := by
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_mulEquiv hK φ
  have hZ2 : IsPGroup 2 (Subgroup.center L) := hZ ▸ IsPGroup.of_bot
  let θ := (centerQuotientEquivTo hZ).trans φ
  have hθ : ∀ l : L, θ (QuotientGroup.mk' (Subgroup.center L) l) = φ l := by
    intro l
    change φ ((centerQuotientEquivTo hZ) (QuotientGroup.mk' (Subgroup.center L) l)) = φ l
    rw [centerQuotientEquivTo_apply]
  have hcomp : θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) = φ.toMonoidHom :=
    MonoidHom.ext hθ
  refine ⟨θ, hZ2, hθ, ?_⟩
  rw [hcomp]
  exact hmap

theorem le_card_ggAutomizer (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x}) :
    720 ≤ Nat.card (ggAutomizer L Bs) := by
  obtain ⟨θ, hZ2, -, hmap'⟩ := exists_centerQuotientEquiv_comp_eq hK φ hmap
  exact le_card_ggAutomizer_of_isPGroup hK θ hZ2 hmap' hBs hcard hx hxL hLx

theorem apply_eq_one_of_forall_ggAutomizer (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x}) (f : ↥Bs →* Multiplicative (ZMod 3))
    (hf : ∀ ψ ∈ ggAutomizer L Bs, ∀ b, f (ψ b) = f b) {b : ↥Bs} (hb : (b : G) ∈ L) :
    f b = 1 := by
  obtain ⟨θ, hZ2, -, hmap'⟩ := exists_centerQuotientEquiv_comp_eq hK φ hmap
  exact apply_eq_one_of_forall_ggAutomizer_of_isPGroup hK θ hZ2 hmap' hBs hcard hx hxL hLx f
    hf hb

theorem exists_reflection_threeA (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {Bs L : Subgroup G} {x : G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hmap : ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x}) :
    ∃ (a : ↥Bs) (ha : (a : G) ∈ L), φ ⟨a, ha⟩ = USixTwo.threeA hω ∧ a ≠ 1 ∧
      ∃ ψ ∈ ggAutomizer L Bs, ψ ^ 2 = 1 ∧ ψ a = a⁻¹ ∧
        ∀ b : ↥Bs, b⁻¹ * ψ b ∈ Subgroup.zpowers a := by
  obtain ⟨θ, hZ2, hθ, hmap'⟩ := exists_centerQuotientEquiv_comp_eq hK φ hmap
  obtain ⟨a, ha, hθa, ha1, ψ, hψmem, hψ2, hψa, hb⟩ :=
    exists_reflection_threeA_of_isPGroup hK hω θ hZ2 hmap' hBs hcard hx hxL hLx
  refine ⟨a, ha, ?_, ha1, ψ, hψmem, hψ2, hψa, hb⟩
  rw [← hθ ⟨a, ha⟩]
  exact hθa

end CFSG.StandardType.E6QTwo

end
