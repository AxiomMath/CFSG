module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckKey
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCover
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckClDefs

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv


private theorem ggSporKRestCl_eval_mem {n : ℕ} (a b : Perm (Fin n)) (H : Subgroup (Perm (Fin n)))
    (ha : a ∈ H) (hb : b ∈ H) (w : List ℤ) :
    sporKRestEval [a, b] w ∈ H := by
  apply sporKRestEval_mem
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ha
  · rw [List.mem_singleton] at hg
    rw [hg]
    exact hb

private theorem ggSporKRestCl_sg_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) :
    ∀ g ∈ sg a b d, g ∈ H := by
  intro g hg
  simp only [sg, List.mem_map] at hg
  obtain ⟨w, _, rfl⟩ := hg
  exact ggSporKRestCl_eval_mem a b H ha hb (sporKRestParse w)

private theorem ggSporKRestCl_tab_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) :
    ∀ t ∈ tab a b d, t ∈ H := by
  intro t ht
  simp only [tab, List.mem_map] at ht
  obtain ⟨w, _, rfl⟩ := ht
  exact sporKRestEval_mem (sg a b d) (sporKRestParse w) H (ggSporKRestCl_sg_mem a b d H ha hb)

private theorem ggSporKRestCl_tab_getD_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) (i : ℕ) :
    (tab a b d).getD i 1 ∈ H := by
  by_cases hi : i < (tab a b d).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact ggSporKRestCl_tab_mem a b d H ha hb _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact H.one_mem

private theorem ggSporKRestCl_rep_mem {n : ℕ} (a b : Perm (Fin n))
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) (c : ClassData) :
    rep a b c ∈ H :=
  ggSporKRestCl_eval_mem a b H ha hb (sporKRestParse c.x)

private theorem ggSporKRestCl_letters_mem {n : ℕ} (a b : Perm (Fin n)) (d : Data)
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) (c : ClassData) :
    ∀ g ∈ letters a b d c, g ∈ H := by
  intro g hg
  rw [letters, List.mem_append] at hg
  rcases hg with hg | hg
  · exact ggSporKRestCl_sg_mem a b d H ha hb g hg
  · rw [List.mem_flatMap] at hg
    obtain ⟨e, _, hg⟩ := hg
    rw [List.mem_map] at hg
    obtain ⟨w, _, rfl⟩ := hg
    exact ggSporKRestCl_eval_mem a b H ha hb (sporKRestParse w)

private theorem ggSporKRestCl_tabK {n : ℕ} (a b : Perm (Fin n)) (d : Data) :
    tabK (sg a b d) d = tab a b d := rfl

private theorem ggSporKRestCl_lettersK {n : ℕ} (a b : Perm (Fin n)) (d : Data) (c : ClassData) :
    lettersK (sg a b d) a b c = letters a b d c := by
  have h1 : lettersK (sg a b d) a b c = lettersMat a b d c := by
    simp only [lettersMat, lettersK, sgMat_eq]
  rw [h1, lettersMat_eq]

theorem checkClMatK_sound {n : ℕ} {B : List ℕ} {a b : Perm (Fin n)} {pOrder : ℕ} {d : Data}
    (hB : IsBase B (Subgroup.closure ({a, b} : Set (Perm (Fin n)))))
    (h : checkClMatK B a b pOrder d = true) : specCl a b pOrder d := by
  let H : Subgroup (Perm (Fin n)) := Subgroup.closure ({a, b} : Set (Perm (Fin n)))
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  unfold checkClMatK at h
  dsimp only at h
  simp only [mat_eq] at h
  rw [sgMat_eq, ggSporKRestCl_tabK] at h
  simp only [tableOkK, classesOkK, ggSporKRestCl_lettersK, repMat_eq, keyEq,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.contains_iff] at h
  obtain ⟨⟨⟨⟨⟨hlen, hnodup_keys⟩, _hkey0⟩, hmem1⟩, hcl⟩, hclasses⟩ := h
  unfold specCl
  refine ⟨hlen, List.Nodup.of_map (keyOf B) hnodup_keys, ?_, ?_, ?_⟩
  · obtain ⟨t, ht, hkey⟩ := List.mem_map.mp hmem1
    have ht1 : t = 1 := eq_of_keyOf_eq hB (ggSporKRestCl_tab_mem a b d H ha hb t ht) H.one_mem hkey
    rw [ht1] at ht
    exact ht
  · intro t ht g hg
    obtain ⟨h1, h2⟩ := hcl t ht g hg
    constructor
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h1
      have hmem : t * g ∈ H :=
        H.mul_mem (ggSporKRestCl_tab_mem a b d H ha hb t ht) (ggSporKRestCl_sg_mem a b d H ha hb g hg)
      have heq : t' = t * g :=
        eq_of_keyOf_eq hB (ggSporKRestCl_tab_mem a b d H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
    · obtain ⟨t', ht', hkey⟩ := List.mem_map.mp h2
      have hmem : t * g⁻¹ ∈ H :=
        H.mul_mem (ggSporKRestCl_tab_mem a b d H ha hb t ht)
          (H.inv_mem (ggSporKRestCl_sg_mem a b d H ha hb g hg))
      have heq : t' = t * g⁻¹ :=
        eq_of_keyOf_eq hB (ggSporKRestCl_tab_mem a b d H ha hb t' ht') hmem hkey
      rw [heq] at ht'
      exact ht'
  · intro c hc
    obtain ⟨⟨hent, hwa⟩, hwb⟩ := hclasses c hc
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨⟨hidx, hkey⟩, hzs⟩ := hent e he
      refine ⟨hidx, ?_, ?_⟩
      · have hL : (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c *
            sporKRestEval [a, b] (sporKRestParse e.h) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem (ggSporKRestCl_eval_mem a b H ha hb (sporKRestParse e.h)))
            (ggSporKRestCl_rep_mem a b H ha hb c))
            (ggSporKRestCl_eval_mem a b H ha hb (sporKRestParse e.h))
        exact eq_of_keyOf_eq hB hL (ggSporKRestCl_tab_getD_mem a b d H ha hb e.idx) hkey
      · intro zw hzw
        have hL : sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d).getD e.idx 1 ∈ H :=
          H.mul_mem (ggSporKRestCl_eval_mem a b H ha hb (sporKRestParse zw))
            (ggSporKRestCl_tab_getD_mem a b d H ha hb e.idx)
        exact eq_of_keyOf_eq hB hL (H.mul_mem (ggSporKRestCl_tab_getD_mem a b d H ha hb e.idx)
          (ggSporKRestCl_eval_mem a b H ha hb (sporKRestParse zw))) (hzs zw hzw)
    · have hL : sporKRestEval (letters a b d c) (sporKRestParse c.wa) ∈ H :=
        sporKRestEval_mem (letters a b d c) (sporKRestParse c.wa) H
          (ggSporKRestCl_letters_mem a b d H ha hb c)
      exact eq_of_keyOf_eq hB hL ha hwa
    · have hL : sporKRestEval (letters a b d c) (sporKRestParse c.wb) ∈ H :=
        sporKRestEval_mem (letters a b d c) (sporKRestParse c.wb) H
          (ggSporKRestCl_letters_mem a b d H ha hb c)
      exact eq_of_keyOf_eq hB hL hb hwb

end CFSG.StandardType.SporadicShape.PermCover

namespace CFSG.StandardType.SporadicShape

open Equiv

theorem sporKRest_cover_of_classCheckK {K : Type} [Group K] [Finite K] {n : ℕ}
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) (B : List ℕ)
    (hB : PermCover.IsBase B (Subgroup.closure ({φ a, φ b} : Set (Perm (Fin n)))))
    {p : ℕ} (hp : p.Prime) (m : ℕ) (d : PermCover.Data)
    (hcheck : PermCover.checkClMatK B (φ a) (φ b) (p ^ m) d = true)
    (hcomplete : ∀ s : K, orderOf s = p →
      ∃ c ∈ d.classes, IsConj (sporKRestEval [a, b] (sporKRestParse c.x)) s) :
    SporKRestCover p K := by
  have hspec := PermCover.checkClMatK_sound hB hcheck
  unfold PermCover.specCl at hspec
  obtain ⟨h1, h2, h3, h4, h5⟩ := hspec
  have h1' : (ggSporKRestPC_tab a b d).length = p ^ m := by
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
  have hcard : Nat.card (Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d}) = p ^ m := by
    rw [sporKRest_card_closure_of_table (ggSporKRestPC_sg a b d) (ggSporKRestPC_tab a b d)
      h1mem hcl' hgen' h2nd, h1']
  let S₀ : Subgroup K := Subgroup.closure {g | g ∈ ggSporKRestPC_sg a b d}
  have hS₀ : IsPGroup p S₀ := IsPGroup.of_card hcard
  have hent : ∀ c ∈ d.classes, ∀ e ∈ ggSporKRestPC_ent a b d c,
      e.1 ∈ S₀ ∧ e.2.1⁻¹ * ggSporKRestPC_rep a b c * e.2.1 = e.1 ∧
        ∀ z ∈ e.2.2, z * e.1 = e.1 * z := by
    intro c hc e he
    rw [ggSporKRestPC_ent] at he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    obtain ⟨hce, _hwa, _hwb⟩ := h5 c hc
    obtain ⟨hlt, hconj, hcent⟩ := hce e₀ he₀
    have hlt' : e₀.idx < (ggSporKRestPC_tab a b d).length := by
      rw [← ggSporKRestPC_permTab_length φ a b d]
      exact hlt
    refine ⟨?_, ?_, ?_⟩
    · apply hgen'
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
  have hgen : ∀ r ∈ d.classes.map (ggSporKRestPC_rep a b), ∀ x : K,
      IsConj r x → SporKRestGenerating p x := by
    intro r hr x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact sporKRest_generating_of_pgroup hp a b hab S₀ hS₀ (ggSporKRestPC_sg a b d) rfl
      (ggSporKRestPC_rep a b c) (ggSporKRestPC_ent a b d c) (hent c hc)
      (sporKRestParse c.wa) (sporKRestParse c.wb) (ha c hc) (hb c hc) hx
  refine sporKRest_cover_of_classes hp (d.classes.map (ggSporKRestPC_rep a b)) ?_ hgen
  intro s hs
  obtain ⟨c, hc, hconj⟩ := hcomplete s hs
  exact ⟨ggSporKRestPC_rep a b c, List.mem_map.mpr ⟨c, hc, rfl⟩, hconj⟩

end CFSG.StandardType.SporadicShape
