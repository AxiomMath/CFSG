module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCoverSpec
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheck

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly Equiv

@[expose] def ggSporKRestPC_sg {K : Type} [Group K] (a b : K) (d : PermCover.Data) : List K :=
  d.sgW.map (fun w => sporKRestEval [a, b] (sporKRestParse w))

@[expose] def ggSporKRestPC_tab {K : Type} [Group K] (a b : K) (d : PermCover.Data) : List K :=
  d.tabW.map (fun w => sporKRestEval (ggSporKRestPC_sg a b d) (sporKRestParse w))

@[expose] def ggSporKRestPC_rep {K : Type} [Group K] (a b : K) (c : PermCover.ClassData) : K :=
  sporKRestEval [a, b] (sporKRestParse c.x)

@[expose] def ggSporKRestPC_letters {K : Type} [Group K] (a b : K) (d : PermCover.Data)
    (c : PermCover.ClassData) : List K :=
  ggSporKRestPC_sg a b d ++ c.ent.flatMap (fun e =>
    e.zs.map (fun w => sporKRestEval [a, b] (sporKRestParse w)))

@[expose] def ggSporKRestPC_ent {K : Type} [Group K] (a b : K) (d : PermCover.Data)
    (c : PermCover.ClassData) : List (K × K × List K) :=
  c.ent.map (fun e =>
    ((ggSporKRestPC_tab a b d).getD e.idx 1,
     sporKRestEval [a, b] (sporKRestParse e.h),
     e.zs.map (fun w => sporKRestEval [a, b] (sporKRestParse w))))

lemma ggSporKRestPC_eval_map {K G : Type} [Group K] [Group G]
    (φ : K →* G) (a b : K) (w : List ℤ) :
    φ (sporKRestEval [a, b] w) = sporKRestEval [φ a, φ b] w := by
  simpa using sporKRestEval_map φ [a, b] w

lemma ggSporKRestPC_sg_map {K : Type} [Group K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (a b : K) (d : PermCover.Data) :
    (ggSporKRestPC_sg a b d).map φ = PermCover.sg (φ a) (φ b) d := by
  simp only [ggSporKRestPC_sg, PermCover.sg, List.map_map, Function.comp_apply]
  apply List.map_congr_left
  intro w _
  exact ggSporKRestPC_eval_map φ a b (sporKRestParse w)

lemma ggSporKRestPC_tab_map {K : Type} [Group K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (a b : K) (d : PermCover.Data) :
    (ggSporKRestPC_tab a b d).map φ = PermCover.tab (φ a) (φ b) d := by
  simp only [ggSporKRestPC_tab, PermCover.tab, List.map_map, Function.comp_apply]
  apply List.map_congr_left
  intro w _
  rw [Function.comp_apply, sporKRestEval_map, ggSporKRestPC_sg_map]

lemma ggSporKRestPC_rep_map {K : Type} [Group K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (a b : K) (c : PermCover.ClassData) :
    φ (ggSporKRestPC_rep a b c) = PermCover.rep (φ a) (φ b) c := by
  simp only [ggSporKRestPC_rep, PermCover.rep]
  exact ggSporKRestPC_eval_map φ a b (sporKRestParse c.x)

lemma ggSporKRestPC_letters_map {K : Type} [Group K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (a b : K) (d : PermCover.Data) (c : PermCover.ClassData) :
    (ggSporKRestPC_letters a b d c).map φ = PermCover.letters (φ a) (φ b) d c := by
  simp only [ggSporKRestPC_letters, PermCover.letters, List.map_append, List.map_flatMap,
    List.map_map, Function.comp_apply, ggSporKRestPC_sg_map]
  congr 1
  apply List.flatMap_congr
  intro e _
  apply List.map_congr_left
  intro w _
  exact ggSporKRestPC_eval_map φ a b (sporKRestParse w)

lemma ggSporKRestPC_ent_flatMap {K : Type} [Group K] (a b : K) (d : PermCover.Data)
    (c : PermCover.ClassData) :
    (ggSporKRestPC_ent a b d c).flatMap (fun e => e.2.2)
      = c.ent.flatMap (fun e =>
          e.zs.map (fun w => sporKRestEval [a, b] (sporKRestParse w))) := by
  simp only [ggSporKRestPC_ent, List.flatMap_map, Function.comp_apply]

lemma ggSporKRestPC_mem_of_map {K G : Type} [Group K] [Group G]
    (φ : K →* G) (hφ : Function.Injective φ) {l : List K} {m : List G}
    (h : l.map φ = m) {x : K} (hx : φ x ∈ m) : x ∈ l := by
  rw [← h] at hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
  rwa [hφ hyx] at hy

lemma ggSporKRestPC_eval_of_map {K G : Type} [Group K] [Group G]
    (φ : K →* G) (hφ : Function.Injective φ) {l : List K} {m : List G}
    (h : l.map φ = m) {w : List ℤ} {x : K} (hx : sporKRestEval m w = φ x) :
    sporKRestEval l w = x := by
  apply hφ
  rw [sporKRestEval_map, h]
  exact hx

lemma ggSporKRestPC_getD_map_one {K G : Type} [Group K] [Group G]
    (φ : K →* G) (l : List K) (n : ℕ) :
    (l.map φ).getD n 1 = φ (l.getD n 1) := by
  rw [← map_one φ, List.getD_map]

lemma ggSporKRestPC_map_getD_tab {K : Type} [Group K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (a b : K) (d : PermCover.Data) (m : ℕ) :
    φ ((ggSporKRestPC_tab a b d).getD m 1) = (PermCover.tab (φ a) (φ b) d).getD m 1 := by
  rw [← ggSporKRestPC_tab_map φ a b d, ggSporKRestPC_getD_map_one]

lemma ggSporKRestPC_permTab_length {K : Type} [Group K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (a b : K) (d : PermCover.Data) :
    (PermCover.tab (φ a) (φ b) d).length = (ggSporKRestPC_tab a b d).length := by
  rw [← ggSporKRestPC_tab_map φ a b d, List.length_map]

theorem sporKRest_cover_of_permModel {K : Type} [Group K] [Finite K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.check (φ a) (φ b) sylowOrder d = true) : SporKRestCover p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hspec := PermCover.check_sound hcheck
  unfold PermCover.spec at hspec
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hspec
  have h1' : (ggSporKRestPC_tab a b d).length = sylowOrder := by
    rw [← ggSporKRestPC_permTab_length φ a b d]
    exact h1
  have h2nd : (ggSporKRestPC_tab a b d).Nodup := by
    apply List.Nodup.of_map φ
    rwa [ggSporKRestPC_tab_map φ a b d]
  have h1mem : (1 : K) ∈ ggSporKRestPC_tab a b d :=
    ggSporKRestPC_mem_of_map φ hφ (ggSporKRestPC_tab_map φ a b d) (by
      rw [map_one]
      exact h3)
  have hcl' : ∀ t ∈ ggSporKRestPC_tab a b d, ∀ g ∈ ggSporKRestPC_sg a b d,
      t * g ∈ ggSporKRestPC_tab a b d ∧ t * g⁻¹ ∈ ggSporKRestPC_tab a b d := by
    intro t ht g hg
    have htφ : φ t ∈ PermCover.tab (φ a) (φ b) d := by
      rw [← ggSporKRestPC_tab_map φ a b d]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    have hgφ : φ g ∈ PermCover.sg (φ a) (φ b) d := by
      rw [← ggSporKRestPC_sg_map φ a b d]
      exact List.mem_map.mpr ⟨g, hg, rfl⟩
    obtain ⟨h4a, h4b⟩ := h4 (φ t) htφ (φ g) hgφ
    refine ⟨ggSporKRestPC_mem_of_map φ hφ (ggSporKRestPC_tab_map φ a b d) ?_,
      ggSporKRestPC_mem_of_map φ hφ (ggSporKRestPC_tab_map φ a b d) ?_⟩
    · simpa only [map_mul] using h4a
    · simpa only [map_mul, map_inv] using h4b
  have hgen' : ∀ t ∈ ggSporKRestPC_tab a b d,
      t ∈ Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d} := by
    intro t ht
    rw [ggSporKRestPC_tab] at ht
    obtain ⟨w, _hw, rfl⟩ := List.mem_map.mp ht
    exact sporKRestEval_mem (ggSporKRestPC_sg a b d) (sporKRestParse w)
      (Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d})
      (fun g hg => Subgroup.subset_closure hg)
  have hcard : Nat.card (Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d}) =
      p ^ (Nat.card K).factorization p := by
    rw [sporKRest_card_closure_of_table (ggSporKRestPC_sg a b d) (ggSporKRestPC_tab a b d)
      h1mem hcl' hgen' h2nd, h1']
    exact hord
  let S : Sylow p K :=
    Sylow.ofCard (Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d}) hcard
  have hS : (S : Subgroup K) = Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d} :=
    Sylow.coe_ofCard _ _
  have hT : ∀ x ∈ (S : Subgroup K), x ∈ ggSporKRestPC_tab a b d := by
    intro x hx
    rw [hS] at hx
    exact (sporKRest_mem_closure_iff_mem_table (ggSporKRestPC_sg a b d)
      (ggSporKRestPC_tab a b d) h1mem hcl' hgen' x).mp hx
  have hent (c : PermCover.ClassData) (hc : c ∈ d.classes) :
      ∀ e ∈ ggSporKRestPC_ent a b d c,
        e.1 ∈ (S : Subgroup K) ∧ e.2.1⁻¹ * ggSporKRestPC_rep a b c * e.2.1 = e.1 ∧
          ∀ z ∈ e.2.2, z * e.1 = e.1 * z := by
    intro e he
    rw [ggSporKRestPC_ent] at he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    obtain ⟨hce, _hwa, _hwb⟩ := h5 c hc
    obtain ⟨hlt, hconj, hcent⟩ := hce e₀ he₀
    have hlt' : e₀.idx < (ggSporKRestPC_tab a b d).length := by
      rw [← ggSporKRestPC_permTab_length φ a b d]
      exact hlt
    refine ⟨?_, ?_, ?_⟩
    · rw [hS]
      apply hgen'
      show (ggSporKRestPC_tab a b d).getD e₀.idx 1 ∈ ggSporKRestPC_tab a b d
      rw [List.getD_eq_getElem (ggSporKRestPC_tab a b d) 1 hlt']
      exact List.getElem_mem hlt'
    · apply hφ
      simp only [map_mul, map_inv, ggSporKRestPC_eval_map, ggSporKRestPC_rep_map,
        ggSporKRestPC_map_getD_tab]
      exact hconj
    · intro z hz
      rw [List.mem_map] at hz
      obtain ⟨zw, hzw, rfl⟩ := hz
      apply hφ
      simp only [map_mul, ggSporKRestPC_eval_map, ggSporKRestPC_map_getD_tab]
      exact hcent zw hzw
  have ha (c : PermCover.ClassData) (hc : c ∈ d.classes) :
      sporKRestEval (ggSporKRestPC_sg a b d ++
        (ggSporKRestPC_ent a b d c).flatMap (fun e => e.2.2)) (sporKRestParse c.wa) = a := by
    obtain ⟨_hce, hwa, _hwb⟩ := h5 c hc
    rw [ggSporKRestPC_ent_flatMap]
    exact ggSporKRestPC_eval_of_map φ hφ (ggSporKRestPC_letters_map φ a b d c) hwa
  have hb (c : PermCover.ClassData) (hc : c ∈ d.classes) :
      sporKRestEval (ggSporKRestPC_sg a b d ++
        (ggSporKRestPC_ent a b d c).flatMap (fun e => e.2.2)) (sporKRestParse c.wb) = b := by
    obtain ⟨_hce, _hwa, hwb⟩ := h5 c hc
    rw [ggSporKRestPC_ent_flatMap]
    exact ggSporKRestPC_eval_of_map φ hφ (ggSporKRestPC_letters_map φ a b d c) hwb
  have hreps : ∀ r ∈ d.classes.map (ggSporKRestPC_rep a b), ∀ x : K,
      IsConj r x → SporKRestGenerating p x := by
    intro r hr x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact sporKRest_generating_of_data hp a b hab S (ggSporKRestPC_sg a b d) hS
      (ggSporKRestPC_rep a b c) (ggSporKRestPC_ent a b d c) (hent c hc)
      (sporKRestParse c.wa) (sporKRestParse c.wb) (ha c hc) (hb c hc) hx
  have hcensus : ∀ t ∈ ggSporKRestPC_tab a b d, t ≠ 1 →
      ∃ r ∈ d.classes.map (ggSporKRestPC_rep a b), ∃ g : K, g⁻¹ * r * g = t := by
    intro t ht htne
    have htφ : φ t ∈ PermCover.tab (φ a) (φ b) d := by
      rw [← ggSporKRestPC_tab_map φ a b d]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    have htneφ : φ t ≠ 1 := by
      intro h
      exact htne (hφ (by rw [h, map_one]))
    obtain ⟨e, _he, hcls, _htabeq, hconj⟩ := h6 (φ t) htφ htneφ
    refine ⟨ggSporKRestPC_rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩), ?_, ?_⟩
    · rw [List.mem_map]
      refine ⟨d.classes.getD e.cls ⟨"", [], "", ""⟩, ?_, rfl⟩
      rw [List.getD_eq_getElem d.classes ⟨"", [], "", ""⟩ hcls]
      exact List.getElem_mem hcls
    · refine ⟨sporKRestEval [a, b] (sporKRestParse e.g), ?_⟩
      apply hφ
      simp only [map_mul, map_inv, ggSporKRestPC_eval_map, ggSporKRestPC_rep_map]
      exact hconj
  exact sporKRest_cover_of_data hp S (ggSporKRestPC_tab a b d) hT
    (d.classes.map (ggSporKRestPC_rep a b)) hreps hcensus

theorem sporKRest_cover_of_permCheck {n : ℕ} (a b : Perm (Fin n)) (Kn : Subgroup (Perm (Fin n)))
    (hKn : Kn = Subgroup.closure ({a, b} : Set (Perm (Fin n)))) {p : ℕ} (hp : p.Prime)
    (sylowOrder : ℕ) (hord : sylowOrder = p ^ (Nat.card Kn).factorization p)
    (d : PermCover.Data) (hcheck : PermCover.check a b sylowOrder d = true) :
    SporKRestCover p ↥Kn := by
  have ha : a ∈ Kn := by
    rw [hKn]
    exact Subgroup.subset_closure (by simp)
  have hb : b ∈ Kn := by
    rw [hKn]
    exact Subgroup.subset_closure (by simp)
  refine sporKRest_cover_of_permModel (K := ↥Kn) Kn.subtype (Subgroup.subtype_injective Kn)
    ⟨a, ha⟩ ⟨b, hb⟩ ?_ hp sylowOrder hord d ?_
  · apply Subgroup.map_injective (Subgroup.subtype_injective Kn)
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.subtype_range]
    have hset : Kn.subtype '' ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥Kn) = {a, b} := by
      simpa using Set.image_pair Kn.subtype (⟨a, ha⟩ : ↥Kn) (⟨b, hb⟩ : ↥Kn)
    rw [hset, hKn]
  · exact hcheck

end CFSG.StandardType.SporadicShape
