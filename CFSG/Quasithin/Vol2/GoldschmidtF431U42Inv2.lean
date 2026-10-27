module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Inv

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem chkInv_spec :
    invDat.length = 64 ∧ ∀ i < 64, comp (Tl.getD i []) (Tl.getD i []) = idL →
      Tl.getD i [] ≠ idL →
      comp (comp (evalW (invDat.getD i (0, [])).2) (Tl.getD i []))
          (evalW (invW (invDat.getD i (0, [])).2)) =
        (if (invDat.getD i (0, [])).1 = 0 then xL else t0L) := by
  have h := Certificates.certificate4161.2.2.2.2.1
  simp only [chkInv, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h
  refine ⟨h.1, fun i hi h1 h2 => ?_⟩
  rcases h.2 i hi with ⟨h3 | h3⟩ | h3
  · exact absurd h1 (by simpa using h3)
  · exact absurd h2 (by simpa using h3)
  · simpa using h3

theorem not_isConj_x_t : ¬ IsConj xY tY := by
  intro h
  rw [isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  have hc' : ((c : Y) : P45) * x45 * ((c : Y) : P45)⁻¹ = t45 := congrArg Subtype.val hc
  have himg : (Finset.univ.filter fun p : Fin 45 => t45 p = p) =
      (Finset.univ.filter fun p : Fin 45 => x45 p = p).map ((c : Y) : P45).toEmbedding := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hp
      refine ⟨((c : Y) : P45)⁻¹ p, ?_, by simp⟩
      have := congrArg (fun f : P45 => f p) hc'
      simp only [Equiv.Perm.mul_apply] at this
      have h2 : ((c : Y) : P45) (x45 (((c : Y) : P45)⁻¹ p)) =
          ((c : Y) : P45) (((c : Y) : P45)⁻¹ p) := by
        rw [this, hp]; simp
      exact ((c : Y) : P45).injective h2
    · rintro ⟨q, hq, rfl⟩
      have := congrArg (fun f : P45 => f (((c : Y) : P45) q)) hc'
      have e : ((c : Y) : P45)⁻¹ (((c : Y) : P45) q) = q := by simp
      simp only [Equiv.Perm.mul_apply, e] at this
      rw [← this, hq]
  have hcard := congrArg Finset.card himg
  rw [Finset.card_map, card_fix_x, card_fix_t] at hcard
  omega

theorem exists_conj_mem_T
    {g : Y} (hg : IsPGroup 2 (Subgroup.zpowers g)) : ∃ t ∈ T, ∃ k : Y, g = k * t * k⁻¹ := by
  have hS := isSylow_T
  obtain ⟨Q, hQ⟩ := hg.exists_le_sylow
  have hidx : ¬ 2 ∣ T.index := by
    have h := hS.2.2
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rwa [e] at h
  let T' : Sylow 2 Y := hS.2.1.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq Y T' Q
  have hk' : MulAut.conj k • T = (Q : Subgroup Y) := by
    have h1 := congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hgQ : g ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers g)
  rw [← hk', Subgroup.mem_smul_pointwise_iff_exists] at hgQ
  obtain ⟨t, ht, hte⟩ := hgQ
  refine ⟨t, ht, k, ?_⟩
  rw [← hte]
  simp [MulAut.conj_apply]

theorem orderOf_conj_eq (k t : Y) : orderOf (k * t * k⁻¹) = orderOf t := by
  simpa [MulAut.conj_apply] using (MulAut.conj k).orderOf_eq t

theorem classes {g : Y}
    (hg : orderOf g = 2) : IsConj xY g ∨ IsConj tY g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨t, htT, k, hgk⟩ := exists_conj_mem_T hp
  have hto : orderOf t = 2 := by rw [← hg, hgk, orderOf_conj_eq]
  obtain ⟨i, hi, hrep⟩ := (mem_T_iff t).1 htT
  have hsq : t * t = 1 := by rw [← pow_two]; exact hto ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at hto; omega
  have hl1 : comp (Tl.getD i []) (Tl.getD i []) = idL := by
    have : RepL (comp (Tl.getD i []) (Tl.getD i [])) (((t * t : Y)) : P45) := repL_mul hrep hrep
    rw [hsq] at this
    exact repL_unique this (repL_one 45)
  have hl2 : Tl.getD i [] ≠ idL := by
    intro h
    apply ht1
    apply Subtype.ext
    exact eq_of_repL hrep (by rw [h]; exact repL_one 45)
  have hspec := chkInv_spec.2 i hi hl1 hl2
  set w := (invDat.getD i (0, [])).2 with hw
  set h : Y := ⟨wordP w, wordP_mem _⟩ with hh
  have hrepc : RepL (comp (comp (evalW w) (Tl.getD i [])) (evalW (invW w)))
      (((h * t * h⁻¹ : Y)) : P45) := by
    refine repL_mul (repL_mul (repL_wordP w) hrep) ?_
    have : (((h : Y) : P45))⁻¹ = wordP (invW w) := by rw [wordP_invW]
    show RepL (evalW (invW w)) (((h : Y) : P45))⁻¹
    rw [this]
    exact repL_wordP _
  have hconj : IsConj (if (invDat.getD i (0, [])).1 = 0 then xY else tY) t := by
    rw [isConj_iff]
    refine ⟨h⁻¹, ?_⟩
    by_cases h0 : (invDat.getD i (0, [])).1 = 0
    · simp only [h0, ↓reduceIte] at hspec ⊢
      have : h * t * h⁻¹ = xY := Subtype.ext (eq_of_repL hrepc (by rw [hspec]; exact repL_x))
      calc h⁻¹ * xY * h⁻¹⁻¹ = h⁻¹ * (h * t * h⁻¹) * h := by rw [this]; simp
        _ = t := by simp [mul_assoc]
    · simp only [h0, ↓reduceIte] at hspec ⊢
      have : h * t * h⁻¹ = tY := Subtype.ext (eq_of_repL hrepc (by rw [hspec]; exact repL_t45))
      calc h⁻¹ * tY * h⁻¹⁻¹ = h⁻¹ * (h * t * h⁻¹) * h := by rw [this]; simp
        _ = t := by simp [mul_assoc]
  have hg' : IsConj t g := by
    rw [isConj_iff]
    exact ⟨k, hgk.symm⟩
  by_cases h0 : (invDat.getD i (0, [])).1 = 0
  · left
    simp only [h0, ↓reduceIte] at hconj
    exact hconj.trans hg'
  · right
    simp only [h0, ↓reduceIte] at hconj
    exact hconj.trans hg'

end CFSG.Quasithin.H13.F431.U42
