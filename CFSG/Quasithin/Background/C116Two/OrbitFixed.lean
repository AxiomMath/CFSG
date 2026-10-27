module

public import CFSG.Quasithin.Background.C116Two.OrbitSplit
public import CFSG.Quasithin.Background.C116Two.OrbitCtx

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_fixModZ_iff {L B : Subgroup G} (hL : IsShort2 L) {u : G} :
    u ∈ fixModZ hL B ↔ u ∈ blockU L ∧ ∀ b ∈ B, ⁅u, b⁆ ∈ blockZ L :=
  Iff.rfl

theorem mem_blockZ_iff {L : Subgroup G} {z : G} :
    z ∈ blockZ L ↔ z ∈ blockU L ∧ z ∈ Subgroup.centralizer (L : Set G) :=
  Iff.rfl

theorem blockU_le_normalizer_of_le_centralizer {L K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer (L : Set G)) :
    blockU L ≤ Subgroup.normalizer (K : Set G) := fun u hu =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hK hk) u (blockU_le_left L hu)).symm)

theorem fixedPts_le_fixModZ_sup {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    orbitW A L ⊓ Subgroup.centralizer (A : Set G) ≤
      fixModZ h.chi.1.1 (A ⊓ Subgroup.normalizer (L : Set G)) ⊔
        (orbitW A L ⊓ Subgroup.centralizer (L : Set G)) := by
  intro x hx
  obtain ⟨hxW, hxA⟩ := Subgroup.mem_inf.mp hx
  have hK : orbitW A L ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (L : Set G) :=
    inf_le_right
  have hxU : x ∈ ((blockU L ⊔ (orbitW A L ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) :
      Set G) :=
    orbitW_le_blockU_sup h hAT hxW
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (blockU_le_normalizer_of_le_centralizer hK),
    Set.mem_mul] at hxU
  obtain ⟨u, hu, y, hy, rfl⟩ := hxU
  have huU : u ∈ blockU L := hu
  have hyK : y ∈ orbitW A L ⊓ Subgroup.centralizer (L : Set G) := hy
  have hyC : y ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hyK).2
  have hcomm : ∀ b ∈ A ⊓ Subgroup.normalizer (L : Set G), ⁅u, b⁆ ∈ blockZ L := by
    intro b hb
    obtain ⟨hbA, hbN⟩ := Subgroup.mem_inf.mp hb
    have hfix : b * (u * y) = u * y * b := Subgroup.mem_centralizer_iff.mp hxA b hbA
    have hbU : b * u * b⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hbN) u).mp huU
    have hyb : b * y * b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : b⁻¹ * l * b ∈ L := by
        refine (Subgroup.mem_normalizer_iff.mp hbN (b⁻¹ * l * b)).mpr ?_
        have e' : b * (b⁻¹ * l * b) * b⁻¹ = l := by group
        rw [e']
        exact hl
      have key := Subgroup.mem_centralizer_iff.mp hyC (b⁻¹ * l * b) hl'
      calc l * (b * y * b⁻¹) = b * (b⁻¹ * l * b * y) * b⁻¹ := by group
        _ = b * (y * (b⁻¹ * l * b)) * b⁻¹ := by rw [key]
        _ = b * y * b⁻¹ * l := by group
    have hkey : (b * u * b⁻¹) * (b * y * b⁻¹) = u * y := by
      calc (b * u * b⁻¹) * (b * y * b⁻¹) = b * (u * y) * b⁻¹ := by group
        _ = u * y * b * b⁻¹ := by rw [hfix]
        _ = u * y := by group
    have hdiff : (b * u * b⁻¹)⁻¹ * u = (b * y * b⁻¹) * y⁻¹ := by
      calc (b * u * b⁻¹)⁻¹ * u
          = (b * u * b⁻¹)⁻¹ * ((b * u * b⁻¹) * (b * y * b⁻¹)) * y⁻¹ := by rw [hkey]; group
        _ = (b * y * b⁻¹) * y⁻¹ := by group
    have hZ : (b * u * b⁻¹)⁻¹ * u ∈ blockZ L := by
      refine mem_blockZ_iff.mpr ⟨(blockU L).mul_mem ((blockU L).inv_mem hbU) huU, ?_⟩
      rw [hdiff]
      exact (Subgroup.centralizer (L : Set G)).mul_mem hyb
        ((Subgroup.centralizer (L : Set G)).inv_mem hyC)
    have hUc : u * (b * u * b⁻¹)⁻¹ = (b * u * b⁻¹)⁻¹ * u :=
      (C1.elemAb2_blockU h.chi.1.1).1 u huU ((b * u * b⁻¹)⁻¹) ((blockU L).inv_mem hbU)
    have e : ⁅u, b⁆ = u * (b * u * b⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e, hUc]
    exact hZ
  have huY : u ∈ fixModZ h.chi.1.1 (A ⊓ Subgroup.normalizer (L : Set G)) :=
    (mem_fixModZ_iff h.chi.1.1).mpr ⟨huU, hcomm⟩
  exact Subgroup.mul_mem_sup huY hyK

theorem fixModZ_inf_eq {L A : Subgroup G} (hL : IsShort2 L) :
    fixModZ hL (A ⊓ Subgroup.normalizer (L : Set G)) ⊓
        (orbitW A L ⊓ Subgroup.centralizer (L : Set G)) = blockZ L := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨hY, hWC⟩ := Subgroup.mem_inf.mp hz
    exact mem_blockZ_iff.mpr ⟨((mem_fixModZ_iff hL).mp hY).1, (Subgroup.mem_inf.mp hWC).2⟩
  · have hz' := mem_blockZ_iff.mp hz
    refine Subgroup.mem_inf.mpr ⟨(mem_fixModZ_iff hL).mpr ⟨hz'.1, fun b hb => ?_⟩,
      Subgroup.mem_inf.mpr ⟨blockU_le_orbitW A L hz'.1, hz'.2⟩⟩
    have hbZ : b ∈ Subgroup.normalizer (blockZ L : Set G) :=
      C1.mem_normalizer_blockZ (Subgroup.mem_inf.mp hb).2
    have h1 : b * z⁻¹ * b⁻¹ ∈ blockZ L :=
      (Subgroup.mem_normalizer_iff.mp hbZ z⁻¹).mp (inv_mem hz)
    rw [commutatorElement_def]
    have e : z * b * z⁻¹ * b⁻¹ = z * (b * z⁻¹ * b⁻¹) := by group
    rw [e]
    exact (blockZ L).mul_mem hz h1

end CFSG.Quasithin.C116Two
