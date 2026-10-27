module

public import CFSG.Quasithin.EmptyFaithful.S152SProd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

namespace S152S

section Shape

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hA : A ≤ (mulHom A B hc).range := fun a ha => ⟨(⟨a, ha⟩, 1), by simp [mulHom_apply]⟩
  have hB : B ≤ (mulHom A B hc).range := fun b hb => ⟨(1, ⟨b, hb⟩), by simp [mulHom_apply]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (sup_le hA hB) hx
  exact ⟨a, a.2, b, b.2, by rw [← hab, mulHom_apply]⟩


theorem shape_of_orbits {S L L₀ : Subgroup G} (hL₀ : L₀ = conjClosure L S)
    (horb : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ S, t ∉ Subgroup.normalizer (L : Set G) ∧ conjSubgroupsBy S L = {L, conjByElt t L}) :
    L₀ = L ∨ ∃ t ∈ S, t ∉ Subgroup.normalizer (L : Set G) ∧ L₀ = L ⊔ conjByElt t L := by
  rcases horb with hn | ⟨t, htS, htn, hset⟩
  · left
    rw [hL₀]
    refine le_antisymm (conjClosure_le fun s hs x hx => ?_) (le_conjClosure L S)
    exact (Subgroup.mem_normalizer_iff.1 (hn s hs) x).1 hx
  · right
    refine ⟨t, htS, htn, ?_⟩
    rw [hL₀]
    refine le_antisymm (conjClosure_le fun s hs x hx => ?_) (sup_le (le_conjClosure L S) ?_)
    · have hmem : conjByElt s L ∈ conjSubgroupsBy S L := ⟨s, hs, rfl⟩
      rw [hset] at hmem
      have hx' : s * x * s⁻¹ ∈ conjByElt s L := ⟨x, hx, by simp [MulAut.conj_apply]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h] at hx'
        exact Subgroup.mem_sup_left hx'
      · rw [h] at hx'
        exact Subgroup.mem_sup_right hx'
    · rintro y ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using mem_conjClosure htS hx

theorem conjByElt_ne_of_not_mem_normalizer {L : Subgroup G} {t : G}
    (htn : t ∉ Subgroup.normalizer (L : Set G)) : L ≠ conjByElt t L := by
  intro heq
  apply htn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 : t * h * t⁻¹ ∈ conjByElt t L ↔ h ∈ L := by
    rw [mem_conjByElt]
    simp [mul_assoc]
  rw [← h1, ← heq]

end Shape

section Main

variable {G : Type} [Group G] [Finite G]

theorem false_of_borel_shape {I S Mi L L₀ : Subgroup G} {z : G} (hA3 : A3Orbits G)
    (hSQ : SQTKGroup ↥I) (hS : IsSylowTwoOf S I) (hzS : z ∈ Subgroup.centralizer (S : Set G))
    (hz2 : z ^ 2 = 1) (hMi : Mi = I ⊓ Subgroup.centralizer ({z} : Set G))
    (hmax : ∀ J : Subgroup G, Mi ≤ J → J ≤ I → J = Mi ∨ J = I)
    (hcomp : IsComponentIn L I) (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (hinn : InducesInner z L)
    (hL₀ : L₀ = conjClosure L S) (hL₀n : (L₀.subgroupOf I).Normal)
    (hBT : BTProps (↥L ⧸ Subgroup.center ↥L)) : False := by
  have hLI : L ≤ I := hcomp.1
  have hL₀I : L₀ ≤ I := by
    rw [hL₀]
    exact conjClosure_le fun s hs l hl =>
      I.mul_mem (I.mul_mem (hS.1 hs) (hLI hl)) (I.inv_mem (hS.1 hs))
  have hLL₀ : L ≤ L₀ := hL₀ ▸ le_conjClosure L S
  have hnc : ¬ ∀ x ∈ L₀, x * z = z * x := by
    intro hall
    have hcomm : ⁅L, Subgroup.zpowers z⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h3 : x * z = z * x := hall x (hLL₀ hx)
      exact (Commute.zpow_left (show Commute z x from h3.symm) n).eq
    rw [hLz] at hcomm
    exact Unc25G2.isComponentIn_ne_bot hcomp hcomm
  obtain ⟨-, horb⟩ := hA3 I S L hSQ hS (Id2519.mem_cComp_of_isComponentIn hcomp)
  have horb' : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ S, t ∉ Subgroup.normalizer (L : Set G) ∧ conjSubgroupsBy S L = {L, conjByElt t L} := by
    rcases horb with h | ⟨t, htS, htn, hset, -⟩
    exacts [Or.inl h, Or.inr ⟨t, htS, htn, hset⟩]
  rcases shape_of_orbits hL₀ horb' with hL₀L | ⟨t, htS, htn, hL₀eq⟩
  · have hinn' : InducesInner z L₀ := by rw [hL₀L]; exact hinn
    have hBT' : BTProps (↥L₀ ⧸ Subgroup.center ↥L₀) := by rw [hL₀L]; exact hBT
    exact false_of_inducesInner_borel hS hzS hz2 hMi hmax hL₀I hL₀n hinn' hnc hBT'.1 hBT'.2
  · have hcomp' : IsComponentIn (conjByElt t L) I := Unc25G2.isComponentIn_map_conj hcomp (hS.1 htS)
    have hcommut : ⁅L, conjByElt t L⁆ = ⊥ :=
      (BenderBranch.eq_or_commute_of_isComponentIn hcomp hcomp').resolve_left
        (conjByElt_ne_of_not_mem_normalizer htn)
    have hc : ∀ a ∈ L, ∀ b ∈ conjByElt t L, a * b = b * a := by
      intro a ha b hb
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcommut
      exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
    have hsup : L ⊔ conjByElt t L = L₀ := hL₀eq.symm
    have hL'L₀ : conjByElt t L ≤ L₀ := hL₀eq ▸ le_sup_right
    have hcAB : ∀ a ∈ L.subgroupOf L₀, ∀ b ∈ (conjByElt t L).subgroupOf L₀, a * b = b * a := by
      intro a ha b hb
      exact Subtype.ext (hc a.1 (Subgroup.mem_subgroupOf.1 ha) b.1 (Subgroup.mem_subgroupOf.1 hb))
    have htopAB : L.subgroupOf L₀ ⊔ (conjByElt t L).subgroupOf L₀ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ L ⊔ conjByElt t L := by rw [hsup]; exact x.2
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hc hx
      have hxe : x = (⟨a, hLL₀ ha⟩ : ↥L₀) * ⟨b, hL'L₀ hb⟩ := Subtype.ext hab
      rw [hxe]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.2 ha) (Subgroup.mem_subgroupOf.2 hb)
    have hA : BTProps (↥(L.subgroupOf L₀) ⧸ Subgroup.center ↥(L.subgroupOf L₀)) :=
      BTProps.of_mulEquiv (quotCenterEquiv (Subgroup.subgroupOfEquivOfLe hLL₀).symm) hBT
    have hB : BTProps (↥((conjByElt t L).subgroupOf L₀) ⧸
        Subgroup.center ↥((conjByElt t L).subgroupOf L₀)) :=
      BTProps.of_mulEquiv (quotCenterEquiv
        ((Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
          (Subgroup.subgroupOfEquivOfLe hL'L₀).symm)) hBT
    have hJ := BTProps.of_central_product _ _ hcAB htopAB hA hB
    have hinn' : InducesInner z L₀ := by
      obtain ⟨l, hl, hact⟩ := hinn
      have hzt : t * z = z * t := Subgroup.mem_centralizer_iff.1 hzS t htS
      have hzt1 : z⁻¹ * t = t * z⁻¹ := by
        calc z⁻¹ * t = z⁻¹ * (t * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * t) * z⁻¹ := by rw [hzt]
          _ = t * z⁻¹ := by group
      have hzt2 : t⁻¹ * z = z * t⁻¹ := by
        calc t⁻¹ * z = t⁻¹ * (z * t) * t⁻¹ := by group
          _ = t⁻¹ * (t * z) * t⁻¹ := by rw [← hzt]
          _ = z * t⁻¹ := by group
      have hl'mem : t * l * t⁻¹ ∈ conjByElt t L := ⟨l, hl, by simp [MulAut.conj_apply]⟩
      refine ⟨l * (t * l * t⁻¹), L₀.mul_mem (hLL₀ hl) (hL'L₀ hl'mem), fun x hx => ?_⟩
      have hx' : x ∈ L ⊔ conjByElt t L := by rw [hsup]; exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hx'
      have hy : t⁻¹ * b * t ∈ L := mem_conjByElt.1 hb
      have e_a : z⁻¹ * a * z = l⁻¹ * a * l := hact a ha
      have e_b : z⁻¹ * b * z = (t * l * t⁻¹)⁻¹ * b * (t * l * t⁻¹) := by
        have h1 := hact _ hy
        calc z⁻¹ * b * z = (z⁻¹ * t) * (t⁻¹ * b * t) * (t⁻¹ * z) := by group
          _ = (t * z⁻¹) * (t⁻¹ * b * t) * (z * t⁻¹) := by rw [hzt1, hzt2]
          _ = t * (z⁻¹ * (t⁻¹ * b * t) * z) * t⁻¹ := by group
          _ = t * (l⁻¹ * (t⁻¹ * b * t) * l) * t⁻¹ := by rw [h1]
          _ = (t * l * t⁻¹)⁻¹ * b * (t * l * t⁻¹) := by group
      have e1 : b * l = l * b := (hc l hl b hb).symm
      have hla : l⁻¹ * a * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) ha) hl
      have hl'inv : (t * l * t⁻¹)⁻¹ ∈ conjByElt t L := (conjByElt t L).inv_mem hl'mem
      have e2 : (t * l * t⁻¹)⁻¹ * (l⁻¹ * a * l) = (l⁻¹ * a * l) * (t * l * t⁻¹)⁻¹ :=
        (hc _ hla _ hl'inv).symm
      calc z⁻¹ * (a * b) * z = (z⁻¹ * a * z) * (z⁻¹ * b * z) := by group
        _ = (l⁻¹ * a * l) * ((t * l * t⁻¹)⁻¹ * b * (t * l * t⁻¹)) := by rw [e_a, e_b]
        _ = ((t * l * t⁻¹)⁻¹ * (l⁻¹ * a * l)) * b * (t * l * t⁻¹) := by rw [e2]; group
        _ = (t * l * t⁻¹)⁻¹ * (l⁻¹ * a * (l * b)) * (t * l * t⁻¹) := by group
        _ = (t * l * t⁻¹)⁻¹ * (l⁻¹ * a * (b * l)) * (t * l * t⁻¹) := by rw [e1]
        _ = (l * (t * l * t⁻¹))⁻¹ * (a * b) * (l * (t * l * t⁻¹)) := by group
    exact false_of_inducesInner_borel hS hzS hz2 hMi hmax hL₀I hL₀n hinn' hnc hJ.1 hJ.2

end Main

end S152S

end CFSG.Quasithin
