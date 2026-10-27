module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCoverSpecPow
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckPow
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCover

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly Equiv

theorem sporKRest_cover_of_permModelPow {K : Type} [Group K] [Finite K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkPow p (φ a) (φ b) sylowOrder d = true) : SporKRestCover p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hspec := PermCover.checkPow_sound hcheck
  unfold PermCover.specPow at hspec
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
  have hcensus : ∀ t ∈ ggSporKRestPC_tab a b d, t ≠ 1 → t ^ p = 1 →
      ∃ r ∈ d.classes.map (ggSporKRestPC_rep a b), ∃ g : K, g⁻¹ * r * g = t := by
    intro t ht htne htp
    have htφ : φ t ∈ PermCover.tab (φ a) (φ b) d := by
      rw [← ggSporKRestPC_tab_map φ a b d]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    have htneφ : φ t ≠ 1 := by
      intro h
      exact htne (hφ (by rw [h, map_one]))
    have htpφ : φ t ^ p = 1 := by
      rw [← map_pow, htp, map_one]
    obtain ⟨e, _he, hcls, _htabeq, hconj⟩ := h6 (φ t) htφ htneφ htpφ
    refine ⟨ggSporKRestPC_rep a b (d.classes.getD e.cls ⟨"", [], "", ""⟩), ?_, ?_⟩
    · rw [List.mem_map]
      refine ⟨d.classes.getD e.cls ⟨"", [], "", ""⟩, ?_, rfl⟩
      rw [List.getD_eq_getElem d.classes ⟨"", [], "", ""⟩ hcls]
      exact List.getElem_mem hcls
    · refine ⟨sporKRestEval [a, b] (sporKRestParse e.g), ?_⟩
      apply hφ
      simp only [map_mul, map_inv, ggSporKRestPC_eval_map, ggSporKRestPC_rep_map]
      exact hconj
  exact sporKRest_cover_of_data_pow hp S (ggSporKRestPC_tab a b d) hT
    (d.classes.map (ggSporKRestPC_rep a b)) hreps hcensus

theorem sporKRest_cover_of_permCheckPow {n : ℕ} (a b : Perm (Fin n))
    (Kn : Subgroup (Perm (Fin n))) (hKn : Kn = Subgroup.closure ({a, b} : Set (Perm (Fin n))))
    {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ) (hord : sylowOrder = p ^ (Nat.card Kn).factorization p)
    (d : PermCover.Data) (hcheck : PermCover.checkPow p a b sylowOrder d = true) :
    SporKRestCover p ↥Kn := by
  have ha : a ∈ Kn := by
    rw [hKn]
    exact Subgroup.subset_closure (by simp)
  have hb : b ∈ Kn := by
    rw [hKn]
    exact Subgroup.subset_closure (by simp)
  refine sporKRest_cover_of_permModelPow (K := ↥Kn) Kn.subtype (Subgroup.subtype_injective Kn)
    ⟨a, ha⟩ ⟨b, hb⟩ ?_ hp sylowOrder hord d ?_
  · apply Subgroup.map_injective (Subgroup.subtype_injective Kn)
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.subtype_range]
    have hset : Kn.subtype '' ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥Kn) = {a, b} := by
      simpa using Set.image_pair Kn.subtype (⟨a, ha⟩ : ↥Kn) (⟨b, hb⟩ : ↥Kn)
    rw [hset, hKn]
  · exact hcheck

end CFSG.StandardType.SporadicShape
