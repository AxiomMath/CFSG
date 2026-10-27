module

public import CFSG.RankThree.PartOne.S13K.Pair134Embed
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem exists_thetaComponent_ge {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hS : SchreierFor InCatalog) {M : Subgroup G}
    (hKM : ∀ H : Subgroup G, H ≤ M → CFSG.IsKGroup ↥H) (hrk : CFSG.Assembly.evenRank G ≤ 3) :
    ∀ (n : ℕ) (D : Subgroup G), D ≤ M → Nat.card ↥D = n → IsElementaryAbelian p ↥D →
      ∀ (Y : Subgroup G), Y ≤ M ⊓ Subgroup.centralizer (D : Set G) →
        Y.subgroupOf (M ⊓ Subgroup.centralizer (D : Set G)) ∈
          thetaComponents p ↥(M ⊓ Subgroup.centralizer (D : Set G)) →
        ∃ J ∈ thetaComponents p ↥M, Y.subgroupOf M ≤ J := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hDM hDn hDel Y hYC hYmem
  by_cases hD1 : D = ⊥
  ·
    have hC : M ⊓ Subgroup.centralizer (D : Set G) = M := by
      rw [hD1]
      ext g
      simp [Subgroup.mem_centralizer_iff]
    rw [hC] at hYmem
    exact ⟨Y.subgroupOf M, hYmem, le_rfl⟩
  ·
    obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hD1 (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
    have hZ' : (⊥ : Subgroup ↥D) ≠ ⊤ := by
      intro htop
      have : (⟨d, hdD⟩ : ↥D) ∈ (⊥ : Subgroup ↥D) := htop ▸ Subgroup.mem_top _
      exact hd1 (congrArg Subtype.val ((Subgroup.mem_bot).mp this))
    obtain ⟨Mc, hMc, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hZ'
    obtain ⟨a', ha'⟩ : ∃ a' : ↥D, a' ∉ Mc := by
      by_contra hcon
      push Not at hcon
      exact hMc.1 (eq_top_iff.mpr fun x _ => hcon x)
    set D' : Subgroup G := Mc.map D.subtype with hD'def
    have hD'D : D' ≤ D := Subgroup.map_subtype_le Mc
    have hD'M : D' ≤ M := hD'D.trans hDM
    have hD'el : IsElementaryAbelian p ↥D' := isElementaryAbelian_of_le' hDel hD'D
    have hcardlt : Nat.card ↥D' < n := by
      rw [← hDn, hD'def, Subgroup.card_map_of_injective D.subtype_injective]
      refine lt_of_le_of_ne (Subgroup.card_le_card_group Mc) fun h => hMc.1 ?_
      exact (Subgroup.card_eq_iff_eq_top Mc).mp h
    set a : G := (a' : G) with ha
    have haD : a ∈ D := a'.2
    have ha1 : a ≠ 1 := fun h => ha' (by
      have : a' = 1 := Subtype.ext h
      rw [this]
      exact Mc.one_mem)
    have hDsup : D = D' ⊔ Subgroup.zpowers a := by
      have h1 : Mc ⊔ Subgroup.zpowers a' = ⊤ := by
        refine hMc.2 _ (lt_of_le_of_ne le_sup_left fun h => ha' ?_)
        rw [h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a')
      have h2 := congrArg (Subgroup.map D.subtype) h1
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h2
      exact h2.symm
    have hcenD : ∀ g : G, g ∈ Subgroup.centralizer (D : Set G) ↔
        g ∈ Subgroup.centralizer (D' : Set G) ∧ g ∈ Subgroup.centralizer ({a} : Set G) := by
      intro g
      constructor
      · intro hg
        refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_,
          Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        · exact Subgroup.mem_centralizer_iff.mp hg x (hD'D hx)
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact Subgroup.mem_centralizer_iff.mp hg a haD
      · rintro ⟨h1, h2⟩
        have hle : D ≤ Subgroup.centralizer ({g} : Set G) := by
          rw [hDsup]
          refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.mpr ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.mp h1 x hx
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.mp h2 a rfl
        refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    set H : Subgroup G := M ⊓ Subgroup.centralizer (D' : Set G) with hH
    have haH : a ∈ H := Subgroup.mem_inf.mpr ⟨hDM haD, Subgroup.mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (hDel.is_comm.comm (⟨x, hD'D hx⟩ : ↥D) ⟨a, haD⟩)⟩
    set x : ↥H := ⟨a, haH⟩ with hx
    have hxord : orderOf x = p := by
      rw [← Subgroup.orderOf_coe]
      exact EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp haD ha1
    have hHK : CFSG.IsKGroup ↥H := hKM H inf_le_left
    have hHE : CFSG.Assembly.evenRank ↥H ≤ 3 :=
      (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le H).trans hrk
    set Cx : Subgroup ↥H := Subgroup.centralizer ({x} : Set ↥H) with hCx
    have hYH : Y ≤ H := fun y hy => by
      have h1 := Subgroup.mem_inf.mp (hYC hy)
      exact Subgroup.mem_inf.mpr ⟨h1.1, ((hcenD y).mp h1.2).1⟩
    have hle : Y.subgroupOf H ≤ Cx := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h1 := Subgroup.mem_inf.mp (hYC (Subgroup.mem_subgroupOf.mp hg))
      exact Subgroup.mem_centralizer_singleton_iff.mp ((hcenD g).mp h1.2).2
    let ε : ↥(M ⊓ Subgroup.centralizer (D : Set G)) ≃* ↥Cx :=
      { toFun := fun g => ⟨⟨g.1, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp g.2).1,
          ((hcenD g.1).mp (Subgroup.mem_inf.mp g.2).2).1⟩⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          exact Subgroup.mem_centralizer_singleton_iff.mp
            ((hcenD g.1).mp (Subgroup.mem_inf.mp g.2).2).2⟩
        invFun := fun h => ⟨h.1.1, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h.1.2).1,
          (hcenD h.1.1).mpr ⟨(Subgroup.mem_inf.mp h.1.2).2, by
            have := Subgroup.mem_centralizer_singleton_iff.mp h.2
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact congrArg Subtype.val this⟩⟩⟩
        left_inv := fun g => Subtype.ext rfl
        right_inv := fun h => Subtype.ext (Subtype.ext rfl)
        map_mul' := fun g g' => Subtype.ext (Subtype.ext rfl) }
    have hmapε : (Y.subgroupOf (M ⊓ Subgroup.centralizer (D : Set G))).map ε.toMonoidHom =
        (Y.subgroupOf H).subgroupOf Cx := by
      ext ⟨⟨g, hgH⟩, hgx⟩
      constructor
      · intro hmem
        obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hmem
        have hzg' : (z : G) = g := congrArg (fun w : ↥Cx => ((w : ↥H) : G)) hzg
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hzg' ▸ hz))
      · intro hmem
        have hgY : g ∈ Y := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmem)
        exact Subgroup.mem_map.mpr ⟨⟨g, hYC hgY⟩, hgY, rfl⟩
    have hmem' : (Y.subgroupOf H).subgroupOf Cx ∈ thetaComponents p ↥Cx := by
      rw [← hmapε]
      exact map_mulEquiv_mem_thetaComponents hp ε hYmem
    have hY' : Y.subgroupOf H ∈ thetaComponentsAt p x := mem_thetaComponentsAt_iff.mpr ⟨hle, hmem'⟩
    obtain ⟨L', hL', hYL'⟩ := local_theta_component_embedding_frontier hS H hHK hHE p hp hp3 x
      hxord _ hY'
    set Y'' : Subgroup G := L'.map H.subtype with hY''
    have hY''H : Y'' ≤ H := Subgroup.map_subtype_le _
    have hYY'' : Y ≤ Y'' := fun y hy => ⟨⟨y, hYH hy⟩, hYL' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
    have hY''mem : Y''.subgroupOf H ∈ thetaComponents p ↥H := by
      have : Y''.subgroupOf H = L' := Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [this]
      exact hL'
    obtain ⟨J, hJ, hY''J⟩ := ih (Nat.card ↥D') hcardlt D' hD'M rfl hD'el Y'' hY''H hY''mem
    exact ⟨J, hJ, fun y hy =>
      hY''J (Subgroup.mem_subgroupOf.mpr (hYY'' (Subgroup.mem_subgroupOf.mp hy)))⟩

end CFSG.RankThree.PartOne.Q1327
