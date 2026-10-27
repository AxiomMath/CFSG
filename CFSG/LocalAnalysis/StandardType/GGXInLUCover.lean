module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.GH74.Uniqueness.Section14Primary

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

private lemma lup8u1_conj_centralizer {H : Type} [Group H] {L' : Subgroup H} {g b : H}
    (hbC : b ∈ Subgroup.centralizer (L' : Set H))
    (hg : g ∈ Subgroup.normalizer (L' : Set H)) :
    g * b * g⁻¹ ∈ Subgroup.centralizer (L' : Set H) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hg' : g⁻¹ ∈ Subgroup.normalizer (L' : Set H) :=
    (Subgroup.normalizer (L' : Set H)).inv_mem hg
  have hgl : g⁻¹ * l * g ∈ L' := by
    have h := (Subgroup.mem_normalizer_iff.mp hg' l).mp hl
    rwa [inv_inv] at h
  have hcomm : (g⁻¹ * l * g) * b = b * (g⁻¹ * l * g) :=
    Subgroup.mem_centralizer_iff.mp hbC (g⁻¹ * l * g) hgl
  calc l * (g * b * g⁻¹)
      = g * ((g⁻¹ * l * g) * b) * g⁻¹ := by group
    _ = g * (b * (g⁻¹ * l * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * b * g⁻¹) * l := by group

noncomputable def lup8f_central_cover_of_normalizes (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let H := lup8f_HT L Bs
  let L' : Subgroup H := lup8f_L' L Bs
  let E' : Subgroup H := lup8f_E' L Bs
  let Z : Subgroup H := L' ⊓ Subgroup.centralizer (L' : Set H)
  have hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 b
      (Subgroup.mem_inf.mp hb).1).symm
  let N : Subgroup H := CFSG.GH74.Uniqueness.primaryComponent Z hZ 2
  have hN2 : IsPGroup 2 N :=
    CFSG.GH74.Uniqueness.isPGroup_primaryComponent (p := 2) (by norm_num)
  have hE'_norm : E' ≤ Subgroup.normalizer (L' : Set H) := by
    have h : Bs.subgroupOf (L ⊔ Bs) ≤
        (Subgroup.normalizer (L : Set G)).subgroupOf (L ⊔ Bs) :=
      Subgroup.subgroupOf_mono (L ⊔ Bs) hN
    rwa [Subgroup.subgroupOf_normalizer_eq (H := L) (N := L ⊔ Bs) le_sup_left] at h
  have hsup : L' ⊔ E' = ⊤ := by
    change L.subgroupOf (L ⊔ Bs) ⊔ Bs.subgroupOf (L ⊔ Bs) = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hnorm : Subgroup.normalizer (L' : Set H) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le Subgroup.le_normalizer hE'_norm
  have hconjZ : ∀ g : H, ∀ b ∈ Z, g * b * g⁻¹ ∈ Z := by
    intro g b hb
    have hg : g ∈ Subgroup.normalizer (L' : Set H) := by rw [hnorm]; trivial
    obtain ⟨hbL, hbC⟩ := Subgroup.mem_inf.mp hb
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg b).mp hbL,
      lup8u1_conj_centralizer hbC hg⟩
  refine
    { N := N
      normal := Subgroup.Normal.mk fun n hn g =>
        CFSG.GH74.Uniqueness.primaryComponent_conj
          (B := Z) (hB := hZ) (p := 2) (g := g) (a := n)
          (fun b hb => hconjZ g b hb) hn
      le_L := le_trans CFSG.GH74.Uniqueness.primaryComponent_le inf_le_left
      central := ?_
      two_group := hN2
      contains_two := ?_
      coprime := ?_
      E'_le_norm := hE'_norm }
  · intro n hn l hl
    have hnZ : n ∈ Z := (CFSG.GH74.Uniqueness.mem_primaryComponent.mp hn).1
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hnZ).2 l hl
  · intro z hzL hzcent hzp
    have hzZ : z ∈ Z := by
      refine Subgroup.mem_inf.mpr ⟨hzL, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact hzcent l hl
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hzp ⟨z, Subgroup.mem_zpowers z⟩
    exact CFSG.GH74.Uniqueness.mem_primaryComponent_of_orderOf (p := 2) hzZ (by
      rw [← Subgroup.orderOf_mk z (Subgroup.mem_zpowers z)]
      exact hm)
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥N)).mp hN2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)


noncomputable def lup8f_central_cover (M : lup8f_UnitaryMarking Bs L n K) :
    lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs) :=
  lup8f_central_cover_of_normalizes M.normalizes

end CFSG.StandardType.GGXInL

end
