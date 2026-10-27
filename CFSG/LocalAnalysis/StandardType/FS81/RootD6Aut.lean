module

public import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.LocalAnalysis.StandardType.GGTBTorItems
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import CFSG.LocalAnalysis.StandardType.GGR4AutInn
public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley

private theorem center_top_eq_bot {L : Type} [Group L] (hZ : Subgroup.center L = ⊥) :
    Subgroup.center ↥(⊤ : Subgroup L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hgc : (g : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := Subgroup.mem_center_iff.mp hg ⟨x, Subgroup.mem_top x⟩
    exact congrArg Subtype.val h
  rw [hZ, Subgroup.mem_bot] at hgc
  exact hgc

private theorem transport_top_conj (L : Type) [Group L] [Finite L] (E : Subgroup L) :
    let ψ : ↥(⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
    let cT : ↥(⊤ : Subgroup L) →* MulAut ↥(⊤ : Subgroup L) := MulAut.conj
    let F : MulAut ↥(⊤ : Subgroup L) →* MulAut L := (MulAut.congr ψ).toMonoidHom
    ((E.subgroupOf ⊤).map cT).map F = E.map (MulAut.conj : L →* MulAut L) ∧
      cT.range.map F = (MulAut.conj : L →* MulAut L).range := by
  let ψ : ↥(⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
  let cT : ↥(⊤ : Subgroup L) →* MulAut ↥(⊤ : Subgroup L) := MulAut.conj
  let F : MulAut ↥(⊤ : Subgroup L) →* MulAut L := (MulAut.congr ψ).toMonoidHom
  have hcomp : F.comp cT = (MulAut.conj : L →* MulAut L).comp ψ.toMonoidHom := by
    ext g x
    show (MulAut.congr ψ (MulAut.conj g)) x = MulAut.conj (ψ g) x
    rw [CFSG.mulAut_congr_conj]
  have hmapψ : (E.subgroupOf ⊤).map ψ.toMonoidHom = E := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : L) ∈ E := Subgroup.mem_subgroupOf.mp hy
      simpa [ψ, Subgroup.topEquiv_apply] using hy'
    · intro hx
      refine ⟨ψ.symm x, ?_, by simp⟩
      rw [Subgroup.mem_subgroupOf]
      simpa [ψ, Subgroup.topEquiv_symm_apply_coe] using hx
  have hB : ((E.subgroupOf ⊤).map cT).map F = E.map (MulAut.conj : L →* MulAut L) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hmapψ]
  have hψtop : Subgroup.map ψ.toMonoidHom ⊤ = ⊤ := by
    simp
  have hH : cT.range.map F = (MulAut.conj : L →* MulAut L).range := by
    rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map, hcomp,
      ← Subgroup.map_map, hψtop]
  exact ⟨hB, hH⟩

private theorem card_ggAutomizer_top_eq_inner {L : Type} [Group L] [Finite L]
    {E : Subgroup L} (hE : IsElemAbelian 3 E) (hZ : Subgroup.center L = ⊥) :
    Nat.card (ggAutomizer ⊤ E) =
      Nat.card (ggAutomizer (MulAut.conj : L →* MulAut L).range
        (E.map (MulAut.conj : L →* MulAut L))) := by
  let ψ : ↥(⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
  let cT : ↥(⊤ : Subgroup L) →* MulAut ↥(⊤ : Subgroup L) := MulAut.conj
  let B : Subgroup (MulAut ↥(⊤ : Subgroup L)) := (E.subgroupOf ⊤).map cT
  let F : MulAut ↥(⊤ : Subgroup L) →* MulAut L := (MulAut.congr ψ).toMonoidHom
  have hZtop : ∀ g ∈ Subgroup.center ↥(⊤ : Subgroup L), Nat.Coprime 3 (orderOf g) := by
    intro g hg
    have hg1 : g = 1 := by
      have h := center_top_eq_bot hZ
      rw [h] at hg
      simpa using hg
    rw [hg1]
    simp
  have hInn := ggAutomizer_card_eq_inn (p := 3) (X := ⊤) (BX := E) le_top hE hZtop
  obtain ⟨hB, hH⟩ := transport_top_conj L E
  have hmap := F4AutWeyl.ggAutomizer_map_eq (f := F) (MulAut.congr ψ).injective cT.range B hB
  rw [hH] at hmap
  rw [hInn, hmap, Subgroup.card_map_of_injective (MulAut.congr _).injective]

theorem card_ggAutomizer_top_of_elemAbelian_E7
    {E : Subgroup ↥(adjointGroup .E7 (ZMod 2))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 7)
    (hSC : ∀ g : ↥(adjointGroup .E7 (ZMod 2)), (∀ x ∈ E, g * x = x * g) → g ^ 3 = 1 → g ∈ E) :
    Nat.card (ggAutomizer ⊤ E) = 2903040 := by
  have hcard6 : 3 ^ 6 ≤ Nat.card E := by rw [hcard]; norm_num
  have hq : 3 ∣ Nat.card (ZMod 2) + 1 := by
    simp
  have hTor : GGTorusTorData 3 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      ↥(adjointGroup .E7 (ZMod 2))
      (E.map (MulAut.conj : ↥(adjointGroup .E7 (ZMod 2)) →*
        MulAut ↥(adjointGroup .E7 (ZMod 2)))) := by
    have h := ggTorusTorData_E7_plus (K := ZMod 2) (p := 3) Nat.prime_three (by norm_num)
      hq E hE hcard6 hSC
    simpa [Nat.card_zmod] using h
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨e, -⟩ := (w.weylOfType hw ggIsWeylMatrix_E7 ggIntCartan_E₇).2.2
  have hcardA : Nat.card (ggAutomizer
      (MulAut.conj : ↥(adjointGroup .E7 (ZMod 2)) →*
        MulAut ↥(adjointGroup .E7 (ZMod 2))).range
      (E.map (MulAut.conj : ↥(adjointGroup .E7 (ZMod 2)) →*
        MulAut ↥(adjointGroup .E7 (ZMod 2))))) = 2903040 := by
    rw [← Nat.card_congr e.toEquiv, card_coxeterE7_group]
  rw [card_ggAutomizer_top_eq_inner hE CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, hcardA]

private theorem d6_preimage_centralizing
    {G : Type} [Group G] {E Y : Subgroup G} {L : Type} [Group L]
    (hEY : E ≤ Y) (e : ↥Y ≃* L) {g : L}
    (hcent : ∀ x ∈ (E.subgroupOf Y).map e.toMonoidHom, g * x = x * g) (hg3 : g ^ 3 = 1) :
    ∃ y : ↥Y, e y = g ∧ (∀ a ∈ E, (y : G) * a = a * (y : G)) ∧ (y : G) ^ 3 = 1 := by
  let y : ↥Y := e.symm g
  have hgy : e y = g := e.apply_symm_apply g
  have hcy : ∀ a ∈ E, (y : G) * a = a * (y : G) := by
    intro a ha
    have haY : a ∈ Y := hEY ha
    have hmem : e ⟨a, haY⟩ ∈ (E.subgroupOf Y).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hcomm := hcent (e ⟨a, haY⟩) hmem
    have h2 : y * (⟨a, haY⟩ : ↥Y) = (⟨a, haY⟩ : ↥Y) * y := by
      have := congrArg e.symm hcomm
      simpa [y, e.symm_apply_apply] using this
    exact congrArg Subtype.val h2
  have hy3' : y ^ 3 = 1 := by
    apply e.injective
    simpa [hgy] using hg3
  have hy3 : (y : G) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hy3'
  exact ⟨y, hgy, hcy, hy3⟩

private theorem d6_map_selfCentralizing
    {G : Type} [Group G] {b₀ : G} {E Y : Subgroup G}
    (hEY : E ≤ Y) (hb₀ : b₀ ∈ E)
    (hmax : IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E)
    {L : Type} [Group L] (e : ↥Y ≃* L) :
    ∀ g : L, (∀ x ∈ (E.subgroupOf Y).map e.toMonoidHom, g * x = x * g) →
      g ^ 3 = 1 → g ∈ (E.subgroupOf Y).map e.toMonoidHom := by
  intro g hcent hg3
  obtain ⟨y, hgy, hcy, hy3⟩ := d6_preimage_centralizing hEY e hcent hg3
  have hyb : (y : G) * b₀ = b₀ * (y : G) := hcy b₀ hb₀
  let F : Subgroup G := E ⊔ Subgroup.zpowers (y : G)
  have hF_le : F ≤ Subgroup.centralizer ({b₀} : Set G) := by
    refine sup_le hmax.1 (Subgroup.zpowers_le.mpr ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hyb.symm
  have hF_ea : IsElemAbelian 3 F := by
    refine hmax.2.1.sup_of_commute (isElemAbelian_zpowers hy3) ?_
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hcomm : Commute a (y : G) := (hcy a ha).symm
    exact (hcomm.zpow_right k).eq
  have hFE : F = E := hmax.2.2 F hF_le hF_ea le_sup_left
  have hyE : (y : G) ∈ E := by
    rw [← hFE]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hySub : y ∈ E.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hyE
  rw [← hgy]
  exact Subgroup.mem_map.mpr ⟨y, hySub, rfl⟩

theorem e8AutAt_D6_of_model
    (hM : IsEmSevenModel) : E8AutAt Row.D6 := by
  intro G _ _ b₀ K E B Y h
  have hmax : IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E := h.std.2.1.2.1
  have hb₀ : b₀ ∈ E := h.std.2.1.2.2.1
  have hE : IsElemAbelian 3 E := hmax.2.1
  have hEY : E ≤ Y := h.torus_le
  have htop : Nat.card (ggAutomizer ⊤ E) = 2903040 := by
    rw [← h.adapted.1]
    exact h.recOut.1
  obtain ⟨ψ⟩ := hM G Y h.isEm
  let E' : Subgroup ↥(adjointGroup .E7 (ZMod 2)) := (E.subgroupOf Y).map ψ.symm.toMonoidHom
  have hE'ab : IsElemAbelian 3 E' := (hE.subgroupOf Y).map ψ.symm.toMonoidHom
  have hE'card : Nat.card E' = 3 ^ 7 := by
    rw [show E' = (E.subgroupOf Y).map ψ.symm.toMonoidHom from rfl,
      Subgroup.card_map_of_injective ψ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv]
    simpa [Row.m, Row.n] using h.std.2.1.2.2.2.1
  have hSC' : ∀ g : ↥(adjointGroup .E7 (ZMod 2)),
      (∀ x ∈ E', g * x = x * g) → g ^ 3 = 1 → g ∈ E' := by
    intro g hg hg3
    exact d6_map_selfCentralizing hEY hb₀ hmax ψ.symm g hg hg3
  have hcardE' : Nat.card (ggAutomizer ⊤ E') = 2903040 :=
    card_ggAutomizer_top_of_elemAbelian_E7 hE'ab hE'card hSC'
  have hA : Nat.card (ggAutomizer Y E) = Nat.card (ggAutomizer ⊤ (E.subgroupOf Y)) := by
    have hmap := F4AutWeyl.ggAutomizer_map_eq (f := Y.subtype) Y.subtype_injective
      (⊤ : Subgroup ↥Y) (E.subgroupOf Y) (B' := E)
      (Subgroup.map_subgroupOf_eq_of_le hEY)
    rw [show (⊤ : Subgroup ↥Y).map Y.subtype = Y from by
      rw [Subgroup.map_top, Subgroup.range_subtype]] at hmap
    rw [hmap, Subgroup.card_map_of_injective (MulAut.congr _).injective]
  have hB : Nat.card (ggAutomizer ⊤ (E.subgroupOf Y)) = Nat.card (ggAutomizer ⊤ E') := by
    have hmap := F4AutWeyl.ggAutomizer_map_eq (f := ψ.symm.toMonoidHom) ψ.symm.injective
      (⊤ : Subgroup ↥Y) (E.subgroupOf Y) (B' := E') rfl
    rw [show (⊤ : Subgroup ↥Y).map ψ.symm.toMonoidHom = ⊤ from by
      simp] at hmap
    rw [hmap, Subgroup.card_map_of_injective (MulAut.congr _).injective]
  rw [hA, hB, hcardE', htop]

end CFSG.StandardType.FrameRoute.FS81
