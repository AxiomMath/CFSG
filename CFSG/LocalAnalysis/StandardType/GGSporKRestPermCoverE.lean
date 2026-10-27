module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCoverE
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckE
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCover

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly Equiv

theorem sporKRest_cover_of_permModelE {K : Type} [Group K] [Finite K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card K).factorization p) (d : PermCover.DataE)
    (hcheck : PermCover.checkE p (φ a) (φ b) sylowOrder d = true) : SporKRestCover p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hspec := PermCover.checkE_sound hcheck
  unfold PermCover.specE at hspec
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hspec
  have h1' : (ggSporKRestPC_tab a b d.base).length = sylowOrder := by
    rw [← ggSporKRestPC_permTab_length φ a b d.base]
    exact h1
  have hlen_pos : 0 < (ggSporKRestPC_tab a b d.base).length := by
    rw [h1', hord]
    exact pow_pos hp.pos _
  have h0K : (ggSporKRestPC_tab a b d.base).getD 0 1 = 1 := by
    apply hφ
    rw [ggSporKRestPC_map_getD_tab φ a b d.base 0, map_one]
    exact h3
  have h1mem : (1 : K) ∈ ggSporKRestPC_tab a b d.base := by
    rw [← h0K, List.getD_eq_getElem _ 1 hlen_pos]
    exact List.getElem_mem hlen_pos
  have h2nd : (ggSporKRestPC_tab a b d.base).Nodup := by
    apply List.Nodup.of_map φ
    rwa [ggSporKRestPC_tab_map φ a b d.base]
  have hcl' : ∀ t ∈ ggSporKRestPC_tab a b d.base, ∀ g ∈ ggSporKRestPC_sg a b d.base,
      t * g ∈ ggSporKRestPC_tab a b d.base ∧ t * g⁻¹ ∈ ggSporKRestPC_tab a b d.base := by
    intro t ht g hg
    have htφ : φ t ∈ PermCover.tab (φ a) (φ b) d.base := by
      rw [← ggSporKRestPC_tab_map φ a b d.base]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    have hgφ : φ g ∈ PermCover.sg (φ a) (φ b) d.base := by
      rw [← ggSporKRestPC_sg_map φ a b d.base]
      exact List.mem_map.mpr ⟨g, hg, rfl⟩
    obtain ⟨h4a, h4b⟩ := h4 (φ t) htφ (φ g) hgφ
    refine ⟨ggSporKRestPC_mem_of_map φ hφ (ggSporKRestPC_tab_map φ a b d.base) ?_,
      ggSporKRestPC_mem_of_map φ hφ (ggSporKRestPC_tab_map φ a b d.base) ?_⟩
    · simpa only [map_mul] using h4a
    · simpa only [map_mul, map_inv] using h4b
  have hgen' : ∀ t ∈ ggSporKRestPC_tab a b d.base,
      t ∈ Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d.base} := by
    intro t ht
    rw [ggSporKRestPC_tab] at ht
    obtain ⟨w, _hw, rfl⟩ := List.mem_map.mp ht
    exact sporKRestEval_mem (ggSporKRestPC_sg a b d.base) (sporKRestParse w)
      (Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d.base})
      (fun g hg => Subgroup.subset_closure hg)
  have hcard : Nat.card (Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d.base}) =
      p ^ (Nat.card K).factorization p := by
    rw [sporKRest_card_closure_of_table (ggSporKRestPC_sg a b d.base) (ggSporKRestPC_tab a b d.base)
      h1mem hcl' hgen' h2nd, h1']
    exact hord
  let S : Sylow p K :=
    Sylow.ofCard (Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d.base}) hcard
  have hS : (S : Subgroup K) = Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d.base} :=
    Sylow.coe_ofCard _ _
  have hT : ∀ x ∈ (S : Subgroup K), x ∈ ggSporKRestPC_tab a b d.base := by
    intro x hx
    rw [hS] at hx
    exact (sporKRest_mem_closure_iff_mem_table (ggSporKRestPC_sg a b d.base)
      (ggSporKRestPC_tab a b d.base) h1mem hcl' hgen' x).mp hx
  have hTS : ∀ t ∈ ggSporKRestPC_tab a b d.base, t ∈ (S : Subgroup K) := by
    intro t ht
    rw [hS]
    exact hgen' t ht
  have hent (c : PermCover.ClassData) (hc : c ∈ d.base.classes) :
      ∀ e ∈ ggSporKRestPC_ent a b d.base c,
        e.1 ∈ (S : Subgroup K) ∧ e.2.1⁻¹ * ggSporKRestPC_rep a b c * e.2.1 = e.1 ∧
          ∀ z ∈ e.2.2, z * e.1 = e.1 * z := by
    intro e he
    rw [ggSporKRestPC_ent] at he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    obtain ⟨hce, _hwa, _hwb⟩ := h5 c hc
    obtain ⟨hlt, hconj, hcent⟩ := hce e₀ he₀
    have hlt' : e₀.idx < (ggSporKRestPC_tab a b d.base).length := by
      rw [← ggSporKRestPC_permTab_length φ a b d.base]
      exact hlt
    refine ⟨?_, ?_, ?_⟩
    · rw [hS]
      apply hgen'
      rw [List.getD_eq_getElem (ggSporKRestPC_tab a b d.base) 1 hlt']
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
  have ha (c : PermCover.ClassData) (hc : c ∈ d.base.classes) :
      sporKRestEval (ggSporKRestPC_sg a b d.base ++
        (ggSporKRestPC_ent a b d.base c).flatMap (fun e => e.2.2)) (sporKRestParse c.wa) = a := by
    obtain ⟨_hce, hwa, _hwb⟩ := h5 c hc
    rw [ggSporKRestPC_ent_flatMap]
    exact ggSporKRestPC_eval_of_map φ hφ (ggSporKRestPC_letters_map φ a b d.base c) hwa
  have hb (c : PermCover.ClassData) (hc : c ∈ d.base.classes) :
      sporKRestEval (ggSporKRestPC_sg a b d.base ++
        (ggSporKRestPC_ent a b d.base c).flatMap (fun e => e.2.2)) (sporKRestParse c.wb) = b := by
    obtain ⟨_hce, _hwa, hwb⟩ := h5 c hc
    rw [ggSporKRestPC_ent_flatMap]
    exact ggSporKRestPC_eval_of_map φ hφ (ggSporKRestPC_letters_map φ a b d.base c) hwb
  have hreps : ∀ r ∈ d.base.classes.map (ggSporKRestPC_rep a b), ∀ x : K,
      IsConj r x → SporKRestGenerating p x := by
    intro r hr x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact sporKRest_generating_of_data hp a b hab S (ggSporKRestPC_sg a b d.base) hS
      (ggSporKRestPC_rep a b c) (ggSporKRestPC_ent a b d.base c) (hent c hc)
      (sporKRestParse c.wa) (sporKRestParse c.wb) (ha c hc) (hb c hc) hx
  have hmul : ∀ i j, i < (ggSporKRestPC_tab a b d.base).length →
      j < (ggSporKRestPC_tab a b d.base).length →
      sporKRestMulIdx (PermCover.parseMul d.mulS) i j < (ggSporKRestPC_tab a b d.base).length ∧
        (ggSporKRestPC_tab a b d.base).getD i 1 * (ggSporKRestPC_tab a b d.base).getD j 1 =
          (ggSporKRestPC_tab a b d.base).getD
            (sporKRestMulIdx (PermCover.parseMul d.mulS) i j) 1 := by
    intro i j hi hj
    have hi' : i < (PermCover.tab (φ a) (φ b) d.base).length := by
      rwa [ggSporKRestPC_permTab_length φ a b d.base]
    have hj' : j < (PermCover.tab (φ a) (φ b) d.base).length := by
      rwa [ggSporKRestPC_permTab_length φ a b d.base]
    obtain ⟨hm1, hm2⟩ := h7 i hi' j hj'
    refine ⟨?_, ?_⟩
    · rwa [ggSporKRestPC_permTab_length φ a b d.base] at hm1
    · apply hφ
      simp only [map_mul, ggSporKRestPC_map_getD_tab]
      exact hm2
  have hgood0 : (PermCover.goodOf d.base (ggSporKRestPC_tab a b d.base).length).getD 0 false =
      false := by
    simp only [PermCover.goodOf]
    rcases Nat.eq_zero_or_pos (ggSporKRestPC_tab a b d.base).length with hlen0 | hlenpos
    · simp [hlen0]
    · rw [List.getD_eq_getElem _ false (by simpa using hlenpos), List.getElem_map,
        List.getElem_range]
      apply List.any_eq_false.mpr
      intro e he h
      exact (h6 e he).2.2.1 (beq_iff_eq.mp h)
  have hgood : ∀ i, i < (ggSporKRestPC_tab a b d.base).length →
      (PermCover.goodOf d.base (ggSporKRestPC_tab a b d.base).length).getD i false = true →
      ∃ r ∈ d.base.classes.map (ggSporKRestPC_rep a b), ∃ g : K,
        g⁻¹ * r * g = (ggSporKRestPC_tab a b d.base).getD i 1 := by
    intro i hi hgt
    simp only [PermCover.goodOf] at hgt
    rw [List.getD_eq_getElem _ false (by simpa using hi), List.getElem_map, List.getElem_range]
      at hgt
    obtain ⟨e, he, het⟩ := List.any_eq_true.mp hgt
    have heti : e.t = i := beq_iff_eq.mp het
    obtain ⟨hcls, _ht, _hne, hconj⟩ := h6 e he
    refine ⟨ggSporKRestPC_rep a b (d.base.classes.getD e.cls ⟨"", [], "", ""⟩), ?_,
      sporKRestEval [a, b] (sporKRestParse e.g), ?_⟩
    · rw [List.mem_map]
      refine ⟨d.base.classes.getD e.cls ⟨"", [], "", ""⟩, ?_, rfl⟩
      rw [List.getD_eq_getElem d.base.classes ⟨"", [], "", ""⟩ hcls]
      exact List.getElem_mem hcls
    · apply hφ
      simp only [map_mul, map_inv, ggSporKRestPC_eval_map, ggSporKRestPC_rep_map,
        ggSporKRestPC_map_getD_tab]
      rw [heti] at hconj
      exact hconj
  have hcond : sporKRestECond (ggSporKRestPC_tab a b d.base).length p
      (PermCover.parseMul d.mulS) (PermCover.goodOf d.base (ggSporKRestPC_tab a b d.base).length) =
      true := by
    simpa only [ggSporKRestPC_permTab_length φ a b d.base] using h8
  exact sporKRest_cover_of_data_E hp S (ggSporKRestPC_tab a b d.base) h2nd h0K hT hTS
    (PermCover.parseMul d.mulS) hmul (d.base.classes.map (ggSporKRestPC_rep a b)) hreps
    (PermCover.goodOf d.base (ggSporKRestPC_tab a b d.base).length) hgood0 hgood hcond

end CFSG.StandardType.SporadicShape
