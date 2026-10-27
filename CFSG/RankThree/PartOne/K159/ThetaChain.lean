module

public import CFSG.RankThree.PartOne.S15K.KtData
public import CFSG.RankThree.PartOne.S12.Sec1510Defs
public import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.RankThree.PartOne.S12.Sec158
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G]

theorem map_centralizer_step (T : Set G) (x : G) (hx : x ∈ Subgroup.centralizer T) :
    (Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Subgroup.centralizer T))} :
        Set ↥(Subgroup.centralizer T))).map (Subgroup.centralizer T).subtype =
      Subgroup.centralizer (insert x T) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · have := Subgroup.mem_centralizer_singleton_iff.1 hy
      exact (congrArg Subtype.val this).symm
    · exact Subgroup.mem_centralizer_iff.1 y.2 h hh
  · intro hg
    have hgT : g ∈ Subgroup.centralizer T := Subgroup.centralizer_le (Set.subset_insert x T) hg
    have hgx : x * g = g * x := Subgroup.mem_centralizer_iff.1 hg x (Set.mem_insert x T)
    refine ⟨⟨g, hgT⟩, ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hgx.symm)

variable [Finite G]

theorem exists_thetaComp_of_centralizer_insert (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {e : G} (heE : e ∈ E) (he1 : e ≠ 1) :
    ∀ S : Finset G, (∀ x ∈ S, x ∈ E) → ∀ Y : Subgroup G,
      Y ∈ (fun L' : Subgroup ↥(Subgroup.centralizer (insert e (S : Set G))) =>
          L'.map (Subgroup.centralizer (insert e (S : Set G))).subtype) ''
        thetaComponents p ↥(Subgroup.centralizer (insert e (S : Set G))) →
      ∃ L₀ ∈ thetaComponentsAt p e, Y ≤ L₀ := by
  classical
  have hp := h.prime
  have hp3 := h.three_lt
  have : Fact p.Prime := ⟨hp⟩
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEab : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  have hsimple : IsSimpleGroup G := h.setup.1
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ Y hY
    have hset : insert e ((∅ : Finset G) : Set G) = {e} := by simp
    rw [hset] at hY
    exact ⟨Y, hY, le_rfl⟩
  | insert x S' hxS' ih =>
    intro hSE Y hY
    have hxE : x ∈ E := hSE x (Finset.mem_insert_self x S')
    have hS'E : ∀ z ∈ S', z ∈ E := fun z hz => hSE z (Finset.mem_insert_of_mem hz)
    set T₀ : Set G := insert e (S' : Set G) with hT₀
    have hset : insert e ((insert x S' : Finset G) : Set G) = insert x T₀ := by
      rw [Finset.coe_insert]
      exact Set.insert_comm e x _
    rw [hset] at hY
    have hx0 : x ∈ Subgroup.centralizer T₀ := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with rfl | hz
      · exact hEab _ heE x hxE
      · exact hEab z (hS'E z hz) x hxE
    by_cases hx1 : x = 1
    ·
      have hC : Subgroup.centralizer (insert x T₀) = Subgroup.centralizer T₀ := by
        ext g
        constructor
        · intro hg
          exact Subgroup.centralizer_le (Set.subset_insert x T₀) hg
        · intro hg
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rcases hz with rfl | hz
          · simp [hx1]
          · exact Subgroup.mem_centralizer_iff.1 hg z hz
      rw [hC] at hY
      exact ih hS'E Y hY
    · have hyord : orderOf (⟨x, hx0⟩ : ↥(Subgroup.centralizer T₀)) = p := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_eq_prime (hexp x hxE) hx1
      have hD := map_centralizer_step T₀ x hx0
      obtain ⟨hYle, hYθ⟩ := mem_image_map_subtype_iff_of_le.1 hY
      have hYy : Y.subgroupOf (Subgroup.centralizer T₀) ∈
          thetaComponentsAt p (⟨x, hx0⟩ : ↥(Subgroup.centralizer T₀)) :=
        Sec158.mem_thetaComponentsAt_subgroupOf_of_centralizer hp ⟨x, hx0⟩ hD hYle hYθ
      have hC0ne : Subgroup.centralizer T₀ ≠ ⊤ := by
        intro htop
        have hb : Subgroup.centralizer ({e} : Set G) ≠ ⊤ :=
          EmbeddingFixedResidual.centralizer_ne_top_of_simple h.setup.2.1 he1
        apply hb
        rw [eq_top_iff, ← htop]
        exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert e _))
      have hHK : CFSG.IsKGroup ↥(Subgroup.centralizer T₀) := h.setup.2.2.1 _ hC0ne
      have hHE : evenRank ↥(Subgroup.centralizer T₀) ≤ 3 :=
        (Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
      obtain ⟨L', hL', hYL'⟩ := h82 hS ↥(Subgroup.centralizer T₀) hHK hHE p hp hp3
        ⟨x, hx0⟩ hyord _ hYy
      have hY'' : L'.map (Subgroup.centralizer T₀).subtype ∈
          (fun L'' : Subgroup ↥(Subgroup.centralizer T₀) =>
            L''.map (Subgroup.centralizer T₀).subtype) '' thetaComponents p
              ↥(Subgroup.centralizer T₀) := ⟨L', hL', rfl⟩
      obtain ⟨L₀, hL₀, hle⟩ := ih hS'E _ hY''
      refine ⟨L₀, hL₀, fun z hz => hle ?_⟩
      have hzC : z ∈ Subgroup.centralizer T₀ := hYle.trans (Subgroup.centralizer_le
        (Set.subset_insert x T₀)) hz
      have hz' : (⟨z, hzC⟩ : ↥(Subgroup.centralizer T₀)) ∈ Y.subgroupOf (Subgroup.centralizer T₀) :=
        hz
      exact ⟨⟨z, hzC⟩, hYL' hz', rfl⟩

theorem exists_thetaComp_of_thetaCompCentralizer (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {F : Subgroup G} (hFE : F ≤ E) {e : G}
    (heF : e ∈ F) (he1 : e ≠ 1) {Y : Subgroup G} (hY : Y ∈ thetaCompCentralizer p F) :
    ∃ L₀ ∈ thetaComponentsAt p e, Y ≤ L₀ := by
  classical
  set S : Finset G := (Set.toFinite (F : Set G)).toFinset with hS'
  have hSF : ∀ x ∈ S, x ∈ E := fun x hx => hFE ((Set.Finite.mem_toFinset _).1 hx)
  have hset : insert e (S : Set G) = (F : Set G) := by
    rw [hS', Set.Finite.coe_toFinset]
    exact Set.insert_eq_of_mem heF
  refine exists_thetaComp_of_centralizer_insert hS h82 h (hFE heF) he1 S hSF Y ?_
  rw [hset]
  exact hY

theorem kZero_le_thetaLayer (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {t : MulAut E}
    (hq : CFSG.IsQuasisimple ↥(kZero p E t)) {e : G} (he : e ∈ autFixedInG E t) (he1 : e ≠ 1) :
    kZero p E t ≤ thetaLayer p e := by
  have hKθ : kZero p E t ∈ thetaCompCentralizer p (autFixedInG E t) :=
    kZero_mem_thetaCompCentralizer h.prime hq rfl
  obtain ⟨L₀, hL₀, hle⟩ := exists_thetaComp_of_thetaCompCentralizer hS h82 h
    ((Subgroup.map_subtype_le _) : autFixedInG E t ≤ E) he he1 hKθ
  exact fun x hx => Subgroup.subset_closure ⟨L₀, hL₀, hle hx⟩

theorem isKt_le_thetaLayer (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {t : MulAut E} {K : Subgroup G}
    (hK : IsKt p E t K) (hq : CFSG.IsQuasisimple ↥(kZero p E t)) {e : G}
    (he : e ∈ autFixedInG E t) (he1 : e ≠ 1) : K ≤ thetaLayer p e := by
  have hKle : K ≤ kZero p E t := by
    by_cases hex : ∃ f, kExceptional p (kZero p E t) f
    · obtain ⟨f, hf⟩ := hex
      exact (hK.1 f hf).1
    · exact (hK.2 hex).le
  exact hKle.trans (kZero_le_thetaLayer hS h82 h hq he he1)

end CFSG.RankThree.PartOne.K159
