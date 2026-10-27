module

public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.Assembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem isElementaryAbelian_of_le' {G : Type} [Group G] {p : ℕ} {A K : Subgroup G}
    (hA : IsElementaryAbelian p ↥A) (hKA : K ≤ A) : IsElementaryAbelian p ↥K :=
  CFSG.IsElementaryAbelian.of_le hA hKA

theorem exists_thetaComponentsAt_ge {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hS : SchreierFor InCatalog) (hKG : ∀ H : Subgroup G, H ≠ ⊤ → CFSG.IsKGroup ↥H)
    (hrk : CFSG.Assembly.evenRank G ≤ 3)
    (hZ : ∀ a : G, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≠ ⊤) {e : G} (he1 : e ≠ 1) :
    ∀ (n : ℕ) (D : Subgroup G), Nat.card ↥D = n → IsElementaryAbelian p ↥D → e ∈ D →
      ∀ (Y : Subgroup G), Y ≤ Subgroup.centralizer (D : Set G) →
        Y.subgroupOf (Subgroup.centralizer (D : Set G)) ∈
          thetaComponents p ↥(Subgroup.centralizer (D : Set G)) →
        ∃ I ∈ thetaComponentsAt p e, Y ≤ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D hDn hDel heD Y hYD hYmem
  by_cases hDe : D ≤ Subgroup.zpowers e
  ·
    have hD' : D = Subgroup.zpowers e := le_antisymm hDe (Subgroup.zpowers_le.mpr heD)
    have hcen : Subgroup.centralizer (D : Set G) = Subgroup.centralizer ({e} : Set G) := by
      rw [hD']
      ext g
      simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
      constructor
      · intro h x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact h e (Subgroup.mem_zpowers e)
      · intro h x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact (Commute.zpow_left (h e rfl) k).eq
    rw [hcen] at hYD hYmem
    exact ⟨Y, mem_thetaComponentsAt_iff.mpr ⟨hYD, hYmem⟩, le_rfl⟩
  ·
    have hZ' : Subgroup.zpowers (⟨e, heD⟩ : ↥D) ≠ ⊤ := by
      intro htop
      apply hDe
      intro d hd
      have : (⟨d, hd⟩ : ↥D) ∈ Subgroup.zpowers (⟨e, heD⟩ : ↥D) := htop ▸ Subgroup.mem_top _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp this
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    obtain ⟨M, hMc, hZM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hZ'
    obtain ⟨a', ha'⟩ : ∃ a' : ↥D, a' ∉ M := by
      by_contra hcon
      push Not at hcon
      exact hMc.1 (eq_top_iff.mpr fun x _ => hcon x)
    set D' : Subgroup G := M.map D.subtype with hD'def
    have hD'D : D' ≤ D := Subgroup.map_subtype_le M
    have heD' : e ∈ D' := ⟨⟨e, heD⟩, hZM (Subgroup.mem_zpowers _), rfl⟩
    have hD'el : IsElementaryAbelian p ↥D' := isElementaryAbelian_of_le' hDel hD'D
    have hcardlt : Nat.card ↥D' < n := by
      rw [← hDn, hD'def, Subgroup.card_map_of_injective D.subtype_injective]
      refine lt_of_le_of_ne (Subgroup.card_le_card_group M) fun h => hMc.1 ?_
      exact (Subgroup.card_eq_iff_eq_top M).mp h
    set a : G := (a' : G) with ha
    have haD : a ∈ D := a'.2
    have ha1 : a ≠ 1 := fun h => ha' (by
      have : a' = 1 := Subtype.ext h
      rw [this]
      exact M.one_mem)
    have hDsup : D = D' ⊔ Subgroup.zpowers a := by
      have h1 : M ⊔ Subgroup.zpowers a' = ⊤ := by
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
    set H : Subgroup G := Subgroup.centralizer (D' : Set G) with hH
    have hHne : H ≠ ⊤ := by
      intro htop
      apply hZ e he1
      rw [eq_top_iff]
      intro g _
      have hgH : g ∈ H := htop ▸ Subgroup.mem_top g
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hgH e heD').symm
    have haH : a ∈ H := Subgroup.mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (hDel.is_comm.comm (⟨x, hD'D hx⟩ : ↥D) ⟨a, haD⟩)
    set x : ↥H := ⟨a, haH⟩ with hx
    have hxord : orderOf x = p := by
      rw [← Subgroup.orderOf_coe]
      exact EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp haD ha1
    have hHK : CFSG.IsKGroup ↥H := hKG H hHne
    have hHE : CFSG.Assembly.evenRank ↥H ≤ 3 := (Sec9A.evenRank_subgroup_le _).trans hrk
    set Cx : Subgroup ↥H := Subgroup.centralizer ({x} : Set ↥H) with hCx
    have hYH : Y ≤ H := fun y hy => ((hcenD y).mp (hYD hy)).1
    have hle : Y.subgroupOf H ≤ Cx := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        ((hcenD g).mp (hYD (Subgroup.mem_subgroupOf.mp hg))).2
    let ε : ↥(Subgroup.centralizer (D : Set G)) ≃* ↥Cx :=
      { toFun := fun g => ⟨⟨g.1, ((hcenD g.1).mp g.2).1⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          exact Subgroup.mem_centralizer_singleton_iff.mp ((hcenD g.1).mp g.2).2⟩
        invFun := fun h => ⟨h.1.1, (hcenD h.1.1).mpr ⟨h.1.2, by
          have := Subgroup.mem_centralizer_singleton_iff.mp h.2
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val this⟩⟩
        left_inv := fun g => Subtype.ext rfl
        right_inv := fun h => Subtype.ext (Subtype.ext rfl)
        map_mul' := fun g g' => Subtype.ext (Subtype.ext rfl) }
    have hmapε : (Y.subgroupOf (Subgroup.centralizer (D : Set G))).map ε.toMonoidHom =
        (Y.subgroupOf H).subgroupOf Cx := by
      ext ⟨⟨g, hgH⟩, hgx⟩
      constructor
      · intro hmem
        obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hmem
        have hzg' : (z : G) = g := congrArg (fun w : ↥Cx => ((w : ↥H) : G)) hzg
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hzg' ▸ hz))
      · intro hmem
        have hgY : g ∈ Y := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmem)
        exact Subgroup.mem_map.mpr ⟨⟨g, hYD hgY⟩, hgY, rfl⟩
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
    obtain ⟨I, hI, hY''I⟩ := ih (Nat.card ↥D') hcardlt D' rfl hD'el heD' Y'' hY''H hY''mem
    exact ⟨I, hI, hYY''.trans hY''I⟩

theorem exists_thetaComponentsAt_ge_of_hyp {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hS : SchreierFor InCatalog) {e : G}
    (he1 : e ≠ 1) {D : Subgroup G} (hD : IsElementaryAbelian p ↥D) (heD : e ∈ D) {Y : Subgroup G}
    (hYD : Y ≤ Subgroup.centralizer (D : Set G))
    (hYmem : Y.subgroupOf (Subgroup.centralizer (D : Set G)) ∈
      thetaComponents p ↥(Subgroup.centralizer (D : Set G))) :
    ∃ I ∈ thetaComponentsAt p e, Y ≤ I := by
  have : IsSimpleGroup G := h.setup.1
  exact exists_thetaComponentsAt_ge h.prime h.three_lt hS h.setup.2.2.1 h.evenRank_eq.le
    (fun a ha => EmbeddingFixedResidual.centralizer_ne_top_of_simple h.setup.2.1 ha) he1 _ D rfl hD
    heD Y hYD hYmem

end CFSG.RankThree.PartOne.S13K
