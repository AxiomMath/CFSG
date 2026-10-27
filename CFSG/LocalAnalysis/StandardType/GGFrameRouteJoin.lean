module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteMain
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSCenter

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

section Join

variable {G : Type} [Group G] [Finite G]

theorem ggAutomizerJoin_le_ggG0 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h𝒦 : GGNbrSet p B x D J 𝒦) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (ggG0 p B x L D J) Bs := by
  refine sup_le (ggAutomizer_mono Bs (le_ggG0_left p B x L D J))
    (iSup₂_le fun K hK => ggAutomizer_mono Bs ?_)
  obtain ⟨y, hy⟩ := h𝒦.2 K hK
  exact le_ggG0_of_ggNbr hy

theorem eq_one_of_fix_ggAutomizerJoin (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hW : GGSecFiveWeylCase 3 B Bs x D J) {𝒦 : Finset (Subgroup G)}
    (h𝒦 : GGNbrSet 3 B x D J 𝒦) (hne : 𝒦.Nonempty) (b : Bs)
    (hb : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ b = b) : b = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨y, hN⟩ := h𝒦.2 K hK
  have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    sup_le le_sup_left
      ((le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) K hK).trans le_sup_right)
  exact eq_one_of_fix_join hTBF hWI hR hW hN b fun φ hφ => hb φ (hle hφ)

theorem card_bstar_of_weylAtJoin {ι : Type} [Fintype ι] {M : CoxeterMatrix ι} {n : ℕ}
    (hn : Fintype.card ι = n)
    (hS : ∃ S : Subgroup M.Group, IsElemAbelian 2 S ∧
      ∃ f : Finset (Fin n) → S, Function.Injective f)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hW : GGSecFiveWeylCase 3 B Bs x D J) {𝒦 : Finset (Subgroup G)}
    (h𝒦 : GGNbrSet 3 B x D J 𝒦) (hne : 𝒦.Nonempty)
    (hM : GGWeylOfType 3 M (ggAutomizerJoin L Bs 𝒦)) : Nat.card Bs = 3 ^ n := by
  refine le_antisymm ?_
    (pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num) hR.1.2.1.2.1 hM hS)
  rw [← hn]
  exact SpJoinRefl.card_le_pow_of_weylOfType hM
    (eq_one_of_fix_ggAutomizerJoin hTBF hWI hR hW h𝒦 hne)

theorem a4_of_weylAtJoin {ι : Type} {M : CoxeterMatrix ι}
    (hconj : ∃ i₀ : ι, ∀ i, ∃ w : M.Group, w * M.simple i₀ = M.simple i * w)
    (hnc : ∃ i j k l : ι, M.simple i * M.simple j * (M.simple k * M.simple l) ≠
      M.simple k * M.simple l * (M.simple i * M.simple j))
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hW : GGSecFiveWeylCase 3 B Bs x D J) {𝒦 : Finset (Subgroup G)}
    (h𝒦 : GGNbrSet 3 B x D J 𝒦) (hne : 𝒦.Nonempty)
    (hM : GGWeylOfType 3 M (ggAutomizerJoin L Bs 𝒦)) :
    ∀ z : G, z ∈ B → z ≠ 1 → ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧
      g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  intro z hzB hz1
  obtain ⟨e, he⟩ := hM
  exact ggFrameA4_of_weylOfType hconj hnc hR.1.2.1.2.1 e he
    ((ggAutomizerJoin_le_ggG0 h𝒦).trans (ggAutomizer_mono Bs le_top))
    (eq_one_of_fix_ggAutomizerJoin hTBF hWI hR hW h𝒦 hne) (hR.1.2.1.1 hzB) hz1

section Coxeter

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

theorem a4_of_weylAtJoin_E7 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hW : GGSecFiveWeylCase 3 B Bs x D J) {𝒦 : Finset (Subgroup G)}
    (h𝒦 : GGNbrSet 3 B x D J 𝒦) (hne : 𝒦.Nonempty)
    (hM : GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦)) :
    ∀ z : G, z ∈ B → z ≠ 1 → ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧
      g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  rw [coxeterE7_eq] at hM
  exact a4_of_weylAtJoin (M := coxeterMatrix (isFiniteType_cartan .E7)) conj_simple_E7 noncomm_E7
    hTBF hWI hR hW h𝒦 hne hM

theorem a4_of_weylAtJoin_E8 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hW : GGSecFiveWeylCase 3 B Bs x D J) {𝒦 : Finset (Subgroup G)}
    (h𝒦 : GGNbrSet 3 B x D J 𝒦) (hne : 𝒦.Nonempty)
    (hM : GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizerJoin L Bs 𝒦)) :
    ∀ z : G, z ∈ B → z ≠ 1 → ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧
      g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  rw [coxeterE8_eq] at hM
  exact a4_of_weylAtJoin (M := coxeterMatrix (isFiniteType_cartan .E8)) conj_simple_E8 noncomm_E8
    hTBF hWI hR hW h𝒦 hne hM

end Coxeter

end Join

theorem ggSecFiveData_of_frameRouteJoin
    (hI : GGFrameRouteJoinInputs) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo p Bs L)
    (hE : GGSecFiveWeylAtJoin p B Bs x L D J CoxeterMatrix.E₇ ∨
      GGSecFiveWeylAtJoin p B Bs x L D J CoxeterMatrix.E₈) :
    GGSecFiveData p B x L D J := by
  have hp : p = 3 := p_eq_three_of_qTwo hR.1 hq
  subst hp
  have hW3 : GGSecFiveWeylCase 3 B Bs x D J := ⟨ggScalarsPmOne_of_prime_three hR.1 rfl, hW⟩
  obtain ⟨hAC, hLSS, hEnd, hFSx, hFSy⟩ := hI
  rcases hE with hAt7 | hAt8
  · have hFS : FSPoint B Bs (fun lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :=
      main_fsPoint_E7 hR ((hEnd G B Bs x L D J hR hW3 hq).1 hAt7)
        (fun hm => ⟨(hFSx G B Bs x L D J hR hW3 hq).1 hAt7 hm,
          center_eq_bot_of_fsEndMarking (fun _ hl => ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩) hm⟩)
        (fun hm => by
          obtain ⟨hc, y, hy, K, hS, hn, hK⟩ := (hFSy G B Bs x L D J hR hW3 hq).1 hAt7 hm
          exact ⟨hc, y, hy, K, hS, hn,
            center_eq_bot_of_fsEndMarking (fun _ hl => ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩) hK, hK⟩)
    obtain ⟨𝒦, h𝒦, hne, hM⟩ := hAt7
    obtain ⟨e, -⟩ := id hM
    obtain ⟨ψ, hker, hrange⟩ :=
      psi_E7_of_fsPoint_of_le hAC hLSS B Bs x L D J hR e (ggAutomizerJoin_le_ggG0 h𝒦)
        (card_bstar_of_weylAtJoin (Fintype.card_fin 7) exists_elemAbelian_two_coxeterE7 hTBF hWI hR
          hW3 h𝒦 hne hM)
        (a4_of_weylAtJoin_E7 hTBF hWI hR hW3 h𝒦 hne hM) hFS
    have hadm : StatedLieAdmissible .E7 0 2 1 := ⟨Nat.prime_two, le_refl 1, rfl⟩
    exact Or.inr (Or.inr ⟨.E7, 0, 1,
      ggSecFivePres_of_psi_of_admissible hadm (by decide) ψ hker hrange⟩)
  · have hFS : FSPoint B Bs (fun lab =>
        ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) :=
      main_fsPoint_E8 hR ((hEnd G B Bs x L D J hR hW3 hq).2 hAt8)
        (fun hm => ⟨(hFSx G B Bs x L D J hR hW3 hq).2 hAt8 hm,
          center_eq_bot_of_fsEndMarking (fun _ hl => by
            rcases hl.1 with h | h
            · exact ⟨Or.inr (Or.inl h), hl.2⟩
            · exact ⟨Or.inr (Or.inr h), hl.2⟩) hm⟩)
        (fun hm => by
          obtain ⟨hc, y, hy, K, hS, hn, hK⟩ := (hFSy G B Bs x L D J hR hW3 hq).2 hAt8 hm
          exact ⟨hc, y, hy, K, hS, hn,
            center_eq_bot_of_fsEndMarking (fun _ hl => by
              rcases hl.1 with h | h
              · exact ⟨Or.inr (Or.inl h), hl.2⟩
              · exact ⟨Or.inr (Or.inr h), hl.2⟩) hK, hK⟩)
    obtain ⟨𝒦, h𝒦, hne, hM⟩ := hAt8
    obtain ⟨e, -⟩ := id hM
    obtain ⟨ψ, hker, hrange⟩ :=
      psi_E8_of_fsPoint_of_le hAC hLSS B Bs x L D J hR e (ggAutomizerJoin_le_ggG0 h𝒦)
        (card_bstar_of_weylAtJoin (Fintype.card_fin 8) exists_elemAbelian_two_coxeterE8 hTBF hWI hR
          hW3 h𝒦 hne hM)
        (a4_of_weylAtJoin_E8 hTBF hWI hR hW3 h𝒦 hne hM) hFS
    have hadm : StatedLieAdmissible .E8 0 2 1 := ⟨Nat.prime_two, le_refl 1, rfl⟩
    exact Or.inr (Or.inr ⟨.E8, 0, 1,
      ggSecFivePres_of_psi_of_admissible hadm (by decide) ψ hker hrange⟩)

end CFSG.StandardType.FrameRoute

end
