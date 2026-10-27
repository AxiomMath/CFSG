module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

local notation "V₄" => Fin 2 ⊕ Fin 2

section Union

variable {K : Type} [Field K]

theorem le_or_le_of_subset_union {P A B : Submodule K (V₄ → K)} (h : ∀ x ∈ P, x ∈ A ∨ x ∈ B) :
    P ≤ A ∨ P ≤ B := by
  by_contra hcon
  rw [not_or, IsConcreteLE.not_le_iff_exists, IsConcreteLE.not_le_iff_exists] at hcon
  obtain ⟨⟨x, hxP, hxA⟩, ⟨y, hyP, hyB⟩⟩ := hcon
  have hxB : x ∈ B := (h x hxP).resolve_left hxA
  have hyA : y ∈ A := (h y hyP).resolve_right hyB
  rcases h (x + y) (P.add_mem hxP hyP) with hs | hs
  · exact hxA (by simpa using A.sub_mem hs hyA)
  · exact hyB (by simpa using B.sub_mem hs hxB)

theorem exists_mem_apply_ne_zero {P : Submodule K (V₄ → K)} (f g : (V₄ → K) →ₗ[K] K)
    (hf : ∃ x ∈ P, f x ≠ 0) (hg : ∃ x ∈ P, g x ≠ 0) : ∃ z ∈ P, f z ≠ 0 ∧ g z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h : ∀ x ∈ P, x ∈ LinearMap.ker f ∨ x ∈ LinearMap.ker g := fun x hx => by
    by_cases hfx : f x = 0
    · exact Or.inl hfx
    · exact Or.inr (hcon x hx hfx)
  rcases le_or_le_of_subset_union h with hl | hl
  · obtain ⟨x, hx, hfx⟩ := hf
    exact hfx (LinearMap.mem_ker.mp (hl hx))
  · obtain ⟨x, hx, hgx⟩ := hg
    exact hgx (LinearMap.mem_ker.mp (hl hx))

end Union

section Orthogonal

variable {K : Type} [Field K]

theorem spForm_swap (x y : V₄ → K) : spForm 2 K y x = - spForm 2 K x y := by
  rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt]

theorem spForm_eq_zero_comm {x y : V₄ → K} (h : spForm 2 K x y = 0) : spForm 2 K y x = 0 := by
  rw [spForm_swap, h, neg_zero]

theorem spForm_ne_zero_comm {x y : V₄ → K} (h : spForm 2 K x y ≠ 0) : spForm 2 K y x ≠ 0 := by
  rw [spForm_swap, neg_ne_zero]
  exact h

theorem translate_orth {g : GL V₄ K} (hg : g ∈ StatedSp 2 K) (U : Submodule K (V₄ → K)) :
    translate g (orth U) = orth (translate g U) := by
  ext v
  rw [mem_translate, mem_orth]
  constructor
  · rintro ⟨u, hu, rfl⟩ w hw
    obtain ⟨u', hu', rfl⟩ := mem_translate.mp hw
    rw [spForm_mulVec hg]
    exact mem_orth.mp hu u' hu'
  · intro hv
    refine ⟨((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v, mem_orth.mpr fun u' hu' => ?_,
      gl_mulVec_inv_mulVec g v⟩
    rw [← spForm_mulVec hg, gl_mulVec_inv_mulVec]
    exact hv _ (mulVec_mem_translate hu')

theorem mem_orth_span_pair {a b v : V₄ → K} :
    v ∈ orth (Submodule.span K {a, b}) ↔ spForm 2 K a v = 0 ∧ spForm 2 K b v = 0 := by
  rw [mem_orth]
  constructor
  · intro h
    exact ⟨h a (Submodule.subset_span (by simp)), h b (Submodule.subset_span (by simp))⟩
  · rintro ⟨ha, hb⟩ u hu
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
    simp [ha, hb]

theorem span_pair_inf_orth {a b : V₄ → K} (hab : spForm 2 K a b ≠ 0) :
    Submodule.span K {a, b} ⊓ orth (Submodule.span K {a, b}) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv, hv'⟩
  rw [SetLike.mem_coe, mem_orth_span_pair] at hv'
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp only [map_add, map_smul, smul_eq_mul, spForm_self, mul_zero, zero_add, add_zero] at hv'
  have hba : spForm 2 K b a ≠ 0 := spForm_ne_zero_comm hab
  have hβ : β = 0 := (mul_eq_zero.mp hv'.1).resolve_right hab
  have hα : α = 0 := (mul_eq_zero.mp hv'.2).resolve_right hba
  simp [hα, hβ]

theorem finrank_span_pair {a b : V₄ → K} (hab : spForm 2 K a b ≠ 0) :
    Module.finrank K (Submodule.span K {a, b}) = 2 := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  have hb : b ∉ Submodule.span K {a} := by
    intro hb
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hb
    simp [spForm_self] at hab
  rw [show ({a, b} : Set (V₄ → K)) = insert a {b} from rfl, Submodule.span_insert]
  have hdisj : Disjoint (K ∙ a) (K ∙ b) := by
    rw [Submodule.disjoint_def]
    intro x hxa hxb
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hxa
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hxb
    by_contra hx
    have hl : l ≠ 0 := by
      rintro rfl
      exact hx (zero_smul _ _)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hm
      exact hx hm.symm
    apply hb
    rw [Submodule.mem_span_singleton]
    exact ⟨m⁻¹ * l, by rw [mul_smul, ← hm, smul_smul, inv_mul_cancel₀ hm0, one_smul]⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (Submodule.zero_mem _)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a) (K ∙ b)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero, finrank_span_singleton ha,
    finrank_span_singleton hb0] at h
  exact h

end Orthogonal

variable {K : Type} [Field K]

@[expose] def transCenters (G : Subgroup (GL V₄ K)) : Set (V₄ → K) :=
  {a | ∀ c, spTrans a c ∈ G}

variable {G : Subgroup (GL V₄ K)}

theorem mem_transCenters_of_spTrans_mem (hK : ∀ c : K, ∃ k : ℕ, (k : K) = c) {a : V₄ → K}
    {c₀ : K} (hc₀ : c₀ ≠ 0) (h : spTrans a c₀ ∈ G) : a ∈ transCenters G := by
  intro c
  obtain ⟨k, hk⟩ := hK (c / c₀)
  have hc : c = (k : K) * c₀ := by
    rw [hk, div_mul_cancel₀ _ hc₀]
  rw [hc, ← spTrans_npow]
  exact G.pow_mem h _

theorem zero_mem_transCenters : (0 : V₄ → K) ∈ transCenters G := fun c => by
  rw [spTrans_zero_vec]
  exact G.one_mem

theorem smul_mem_transCenters {a : V₄ → K} (ha : a ∈ transCenters G) (l : K) :
    l • a ∈ transCenters G := fun c => by
  rw [spTrans_smul]
  exact ha _

theorem mulVec_mem_transCenters (hGS : G ≤ StatedSp 2 K) {g : GL V₄ K}
    (hg : g ∈ G) {a : V₄ → K} (ha : a ∈ transCenters G) :
    (g : Matrix V₄ V₄ K) *ᵥ a ∈ transCenters G := fun c => by
  rw [← conj_spTrans (hGS hg)]
  exact G.mul_mem (G.mul_mem hg (ha c)) (G.inv_mem hg)

theorem add_smul_mem_transCenters (hGS : G ≤ StatedSp 2 K) {a b : V₄ → K}
    (ha : a ∈ transCenters G) (hb : b ∈ transCenters G) (hab : spForm 2 K a b ≠ 0)
    (s : K) : a + s • b ∈ transCenters G := by
  have h := mulVec_mem_transCenters hGS (hb (s / spForm 2 K a b)) ha
  rwa [spTrans_mulVec, div_mul_cancel₀ _ hab] at h

theorem lincomb_mem_transCenters (hGS : G ≤ StatedSp 2 K) {a b : V₄ → K}
    (ha : a ∈ transCenters G) (hb : b ∈ transCenters G) (hab : spForm 2 K a b ≠ 0)
    (α β : K) : α • a + β • b ∈ transCenters G := by
  by_cases hα : α = 0
  · rw [hα, zero_smul, zero_add]
    exact smul_mem_transCenters hb β
  · have h := smul_mem_transCenters (add_smul_mem_transCenters hGS ha hb hab (β / α)) α
    rwa [smul_add, smul_smul, show α * (β / α) = β by field_simp] at h

theorem spTrans_two_mul_eq {K : Type} [Field K] {a w : V₄ → K} (haw : spForm 2 K a w = 0)
    (d : K) :
    spTrans w (2 * d) = spTrans a (-(2 * d)) * spTrans (a + w) d * spTrans (a - w) d := by
  have hwa : spForm 2 K w a = 0 := spForm_eq_zero_comm haw
  apply gl_ext_mulVec
  intro x
  simp only [gl_mulVec_mul, spTrans_mulVec, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, spForm_self, haw, hwa]
  module

theorem mem_transCenters_of_isotropic (h2' : (2 : K) ≠ 0) {a w : V₄ → K}
    (haw : spForm 2 K a w = 0) (ha : a ∈ transCenters G)
    (h1 : a + w ∈ transCenters G) (h2 : a - w ∈ transCenters G) : w ∈ transCenters G := by
  intro c
  have hc : c = 2 * (c / 2) := by field_simp
  rw [hc, spTrans_two_mul_eq haw]
  exact G.mul_mem (G.mul_mem (ha _) (h1 _)) (h2 _)

theorem isInvariant_span_transCenters (hGS : G ≤ StatedSp 2 K) :
    IsInvariant G (Submodule.span K (transCenters G)) := by
  intro g hg v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (mulVec_mem_transCenters hGS hg hx)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul l x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ l hx

theorem eq_zero_of_forall_mem_spForm {S : Set (V₄ → K)}
    (hS : Submodule.span K S = ⊤) {v : V₄ → K}
    (hv : ∀ s ∈ S, spForm 2 K s v = 0) : v = 0 := by
  have hle : Submodule.span K S ≤ LinearMap.ker ((spForm 2 K).flip v) :=
    Submodule.span_le.mpr fun s hs => by
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      exact hv s hs
  rw [hS] at hle
  refine spForm_separatingLeft v fun x => ?_
  apply spForm_eq_zero_comm
  have := hle (Submodule.mem_top (x := x))
  simpa using this

theorem exists_mem_orth_spForm_ne_zero {w v : V₄ → K}
    (hv : spForm 2 K w v ≠ 0) :
    ∃ x ∈ orth (K ∙ w), spForm 2 K x v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hmem : v ∈ orth (orth (K ∙ w)) := mem_orth.mpr hcon
  rw [orth_orth] at hmem
  obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  apply hv
  rw [map_smul, smul_eq_mul, spForm_self, mul_zero]

theorem mem_transCenters_of_orth_subset (h2 : (2 : K) ≠ 0) (hGS : G ≤ StatedSp 2 K)
    {w E : V₄ → K} (hπ : ∀ u, spForm 2 K w u = 0 → u ∈ transCenters G)
    (hE : E ∈ transCenters G) (hwE : spForm 2 K w E ≠ 0) (v : V₄ → K) :
    v ∈ transCenters G := by
  by_cases hv : spForm 2 K w v = 0
  · exact hπ v hv
  set α := spForm 2 K w v / spForm 2 K w E with hα
  set u := v - α • E with hu
  have hwu : spForm 2 K w u = 0 := by
    simp only [u, map_sub, map_smul, smul_eq_mul, α]
    field_simp
    ring
  have horth : ∀ x ∈ orth (K ∙ w), spForm 2 K w x = 0 := fun x hx =>
    mem_orth.mp hx w (Submodule.mem_span_singleton_self w)
  have hmem_orth : ∀ x, spForm 2 K w x = 0 → x ∈ orth (K ∙ w) := fun x hx => by
    rw [mem_orth]
    intro y hy
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  obtain ⟨x₁, hx₁, hx₁E⟩ := exists_mem_orth_spForm_ne_zero hwE
  obtain ⟨x₂, hx₂, hx₂v⟩ := exists_mem_orth_spForm_ne_zero hv
  obtain ⟨z, hz, hzE, hzv⟩ := exists_mem_apply_ne_zero (P := orth (K ∙ w))
    ((spForm 2 K).flip E) ((spForm 2 K).flip v) ⟨x₁, hx₁, hx₁E⟩ ⟨x₂, hx₂, hx₂v⟩
  change spForm 2 K z E ≠ 0 at hzE
  change spForm 2 K z v ≠ 0 at hzv
  have hEz : spForm 2 K E z ≠ 0 := spForm_ne_zero_comm hzE
  have hwz : spForm 2 K w z = 0 := horth z hz
  obtain ⟨s, hs0, hs⟩ : ∃ s : K, s ≠ 0 ∧
      α * spForm 2 K E u + s * spForm 2 K z v ≠ 0 := by
    by_cases h1 : α * spForm 2 K E u + 1 * spForm 2 K z v = 0
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, fun hneg => ?_⟩
      have : (2 : K) * spForm 2 K z v = 0 := by linear_combination h1 - hneg
      exact hzv ((mul_eq_zero.mp this).resolve_left h2)
    · exact ⟨1, one_ne_zero, h1⟩
  have hy₁ : α • E + (1 : K) • (s • z) ∈ transCenters G :=
    lincomb_mem_transCenters hGS hE (hπ _ (by rw [map_smul, hwz, smul_zero]))
      (by rw [map_smul, smul_eq_mul]; exact mul_ne_zero hs0 hEz) α 1
  have hy₂ : u - s • z ∈ transCenters G :=
    hπ _ (by rw [map_sub, map_smul, hwu, hwz, smul_zero, sub_zero])
  have hB : spForm 2 K (α • E + (1 : K) • (s • z)) (u - s • z) ≠ 0 := by
    have hzE' : spForm 2 K z E = - spForm 2 K E z := spForm_swap E z
    have hzu : spForm 2 K z u = spForm 2 K z v - α * spForm 2 K z E := by
      simp only [u, map_sub, map_smul, smul_eq_mul]
    convert hs using 1
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, spForm_self, hzu, hzE']
    ring
  have := lincomb_mem_transCenters hGS hy₁ hy₂ hB 1 1
  convert this using 1
  simp only [u, one_smul]
  abel

theorem mem_span_of_orth_of_isotropic {K : Type} [Field K] {H : Submodule K (V₄ → K)}
    (hHinf : H ⊓ orth H = ⊥) (hOrank : Module.finrank K (orth H) = 2) {w y : V₄ → K}
    (hw : w ∈ orth H) (hw0 : w ≠ 0) (hy : y ∈ orth H) (hwy : spForm 2 K w y = 0) :
    ∃ l : K, l • w = y := by
  set P := orth H ⊓ orth (K ∙ w)
  have hwP : w ∈ P := ⟨hw, mem_orth.mpr fun u hu => by
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, LinearMap.smul_apply, spForm_self, smul_zero]⟩
  have hyP : y ∈ P := ⟨hy, mem_orth.mpr fun u hu => by
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, LinearMap.smul_apply, hwy, smul_zero]⟩
  have hlt : P < orth H := by
    refine lt_of_le_of_ne inf_le_left fun hP => hw0 ?_
    have hwH : w ∈ orth (orth H) := mem_orth.mpr fun x hx => by
      have hx' : x ∈ P := hP ▸ hx
      exact spForm_eq_zero_comm (mem_orth.mp hx'.2 w (Submodule.mem_span_singleton_self w))
    rw [orth_orth] at hwH
    have : w ∈ H ⊓ orth H := ⟨hwH, hw⟩
    rw [hHinf] at this
    exact this
  have hrank : Module.finrank K P ≤ Module.finrank K (K ∙ w) := by
    rw [finrank_span_singleton hw0]
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hPw : K ∙ w = P :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hwP) hrank
  rw [← hPw] at hyP
  exact Submodule.mem_span_singleton.mp hyP

theorem false_of_centers_subset (hGS : G ≤ StatedSp 2 K) (hirr : IsIrreducibleOn G)
    [Group.IsPerfect G] {H : Submodule K (V₄ → K)}
    (hH : ∀ v ∈ H, v ∈ transCenters G) (hHinf : H ⊓ orth H = ⊥)
    (hHrank : Module.finrank K H = 2)
    (hcon : ∀ e ∈ transCenters G, e ∉ H → e ∈ orth H) : False := by
  have hOrank : Module.finrank K (orth H) = 2 := by
    rw [finrank_orth, hHrank]
  have hHbot : H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hHrank
    exact absurd hHrank (by norm_num)
  have hsplit : ∀ g ∈ G, translate g H = H ∨ translate g H = orth H := by
    intro g hg
    have hsub : ∀ x ∈ translate g H, x ∈ H ∨ x ∈ orth H := fun x hx => by
      obtain ⟨u, hu, rfl⟩ := mem_translate.mp hx
      by_cases hxH : (g : Matrix V₄ V₄ K) *ᵥ u ∈ H
      · exact Or.inl hxH
      · exact Or.inr (hcon _ (mulVec_mem_transCenters hGS hg (hH u hu)) hxH)
    rcases le_or_le_of_subset_union hsub with hle | hle
    · exact Or.inl (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_translate]))
    · exact Or.inr (Submodule.eq_of_le_of_finrank_eq hle
        (by rw [finrank_translate, hHrank, hOrank]))
  have hne : orth H ≠ H := by
    intro h
    apply hHbot
    rw [← hHinf, h, inf_idem]
  let S : Subgroup G :=
    { carrier := {g | translate (g : GL V₄ K) H = H}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, translate_mul] at hx hy ⊢
        rw [hy, hx]
      one_mem' := by simp [translate_one]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at hx ⊢
        conv_lhs => rw [← hx]
        exact translate_inv_translate _ _ }
  have hP : ∀ x y : G, (translate ((x * y : G) : GL V₄ K) H = H) ↔
      ((translate (x : GL V₄ K) H = H) ↔ (translate (y : GL V₄ K) H = H)) := by
    intro x y
    rw [Subgroup.coe_mul, translate_mul]
    rcases hsplit y y.2 with hy | hy
    · rw [hy]
      simp
    · rw [hy, translate_orth (hGS x.2)]
      rcases hsplit x x.2 with hx | hx
      · rw [hx]
        simp
      · rw [hx, orth_orth]
        simp [hne]
  have hinv : ∀ z : G, (translate ((z⁻¹ : G) : GL V₄ K) H = H) ↔
      (translate (z : GL V₄ K) H = H) := by
    intro z
    have h := hP z z⁻¹
    rw [mul_inv_cancel, OneMemClass.coe_one, translate_one] at h
    simp only [true_iff] at h
    exact h.symm
  have hcomm : ∀ x y : G, ⁅x, y⁆ ∈ S := by
    intro x y
    show translate ((⁅x, y⁆ : G) : GL V₄ K) H = H
    rw [commutatorElement_def, hP, hP, hP, hinv, hinv]
    tauto
  have hall : ∀ g : G, g ∈ S := by
    intro g
    have hle : commutator G ≤ S := by
      rw [commutator_def, Subgroup.commutator_le]
      exact fun x _ y _ => hcomm x y
    rw [Group.IsPerfect.commutator_eq_top] at hle
    exact hle (Subgroup.mem_top g)
  have hinvH : ∀ g ∈ G, ∀ w ∈ H, (g : Matrix V₄ V₄ K) *ᵥ w ∈ H := fun g hg w hw => by
    have h : translate g H = H := hall ⟨g, hg⟩
    rw [← h]
    exact mulVec_mem_translate hw
  rcases hirr H hinvH with h | h
  · exact hHbot h
  · rw [h, finrank_top, Module.finrank_fintype_fun_eq_card] at hHrank
    simp at hHrank

theorem eq_statedSp_of_spTrans_mem' (h2 : (2 : K) ≠ 0) (hK : ∀ c : K, ∃ k : ℕ, (k : K) = c)
    (hGS : G ≤ StatedSp 2 K)
    (hirr : IsIrreducibleOn G) [Group.IsPerfect G] {a : V₄ → K} (ha : a ≠ 0)
    {c : K} (hc : c ≠ 0) (hT : spTrans a c ∈ G) : G = StatedSp 2 K := by
  have haΩ : a ∈ transCenters G := mem_transCenters_of_spTrans_mem hK hc hT
  have hspan : Submodule.span K (transCenters G) = ⊤ := by
    rcases hirr _ (isInvariant_span_transCenters hGS) with h | h
    · exact absurd ((Submodule.span_eq_bot.mp h) a haΩ) ha
    · exact h
  obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ :
      ∃ a₁ ∈ transCenters G, ∃ b₁ ∈ transCenters G, spForm 2 K a₁ b₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (eq_zero_of_forall_mem_spForm hspan fun s hs => hcon s hs a haΩ)
  set H := Submodule.span K {a₁, b₁} with hHdef
  have hH : ∀ v ∈ H, v ∈ transCenters G := fun v hv => by
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
    exact lincomb_mem_transCenters hGS ha₁ hb₁ hab α β
  have hHinf : H ⊓ orth H = ⊥ := span_pair_inf_orth hab
  have hHrank : Module.finrank K H = 2 := finrank_span_pair hab
  have hOrank : Module.finrank K (orth H) = 2 := by
    rw [finrank_orth, hHrank]
  obtain ⟨e, heΩ, heH, heO⟩ : ∃ e ∈ transCenters G, e ∉ H ∧ e ∉ orth H := by
    by_contra hcon
    push Not at hcon
    exact false_of_centers_subset hGS hirr hH hHinf hHrank hcon
  obtain ⟨h, hh, w, hw, rfl⟩ :=
    Submodule.mem_sup.mp ((sup_orth_eq_top hHinf).symm ▸ Submodule.mem_top (x := e))
  have hwH : ∀ u ∈ H, spForm 2 K u w = 0 := fun u hu => mem_orth.mp hw u hu
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [zero_add] at heO
    exact heO hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [add_zero] at heH
    exact heH hh
  have hstep2 : ∀ η ∈ H, spForm 2 K η h ≠ 0 → ∀ l : K, η + l • w ∈ transCenters G := by
    intro η hη hηh l
    have hy : η - l • h ∈ transCenters G := hH _ (H.sub_mem hη (H.smul_mem l hh))
    have hyc : spForm 2 K (η - l • h) (h + w) ≠ 0 := by
      simp only [map_add, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, spForm_self, hwH η hη, hwH h hh, mul_zero, sub_zero, add_zero]
      exact hηh
    have := add_smul_mem_transCenters hGS hy heΩ hyc l
    convert this using 1
    rw [smul_add]
    abel
  have hnonorth : ∀ x ∈ H, x ≠ 0 → ∃ y ∈ H, spForm 2 K y x ≠ 0 := by
    intro x hx hx0
    by_contra hcon
    push Not at hcon
    have : x ∈ H ⊓ orth H := ⟨hx, mem_orth.mpr hcon⟩
    rw [hHinf] at this
    exact hx0 this
  have hstep3 : ∀ η ∈ H, ∀ l : K, η + l • w ∈ transCenters G := by
    intro η hη l
    by_cases hη0 : η = 0
    · rw [hη0, zero_add]
      by_cases hl : l = 0
      · rw [hl, zero_smul]
        exact zero_mem_transCenters
      have ha₁0 : a₁ ≠ 0 := by
        rintro rfl
        simp at hab
      have ha₁H : a₁ ∈ H := Submodule.subset_span (by simp)
      have hpos : ∀ m : K, a₁ + m • w ∈ transCenters G := fun m => by
        by_cases hm : spForm 2 K a₁ h = 0
        · obtain ⟨η₁, hη₁, h1, h2⟩ := exists_mem_apply_ne_zero (P := H)
            ((spForm 2 K).flip h) ((spForm 2 K).flip a₁)
            (hnonorth h hh hh0) (hnonorth a₁ ha₁H ha₁0)
          change spForm 2 K η₁ h ≠ 0 at h1
          change spForm 2 K η₁ a₁ ≠ 0 at h2
          have hu₂ : (a₁ + η₁) + m • w ∈ transCenters G := hstep2 _ (H.add_mem ha₁H hη₁)
            (by rw [map_add, LinearMap.add_apply, hm, zero_add]; exact h1) m
          have hB : spForm 2 K η₁ ((a₁ + η₁) + m • w) ≠ 0 := by
            simp only [map_add, map_smul, smul_eq_mul, spForm_self, add_zero,
              hwH η₁ hη₁, mul_zero]
            exact h2
          have := lincomb_mem_transCenters hGS (hH η₁ hη₁) hu₂ hB (-1) 1
          convert this using 1
          rw [neg_one_smul, one_smul]
          abel
        · exact hstep2 a₁ ha₁H hm m
      have hwΩ : w ∈ transCenters G := by
        refine mem_transCenters_of_isotropic h2 (hwH a₁ ha₁H) (hH a₁ ha₁H) ?_ ?_
        · simpa using hpos 1
        · have h' := hpos (-1)
          rwa [neg_one_smul, ← sub_eq_add_neg] at h'
      exact smul_mem_transCenters hwΩ l
    by_cases hηh : spForm 2 K η h = 0
    · obtain ⟨η₁, hη₁, h1, h2⟩ := exists_mem_apply_ne_zero (P := H)
        ((spForm 2 K).flip h) ((spForm 2 K).flip η)
        (hnonorth h hh hh0) (hnonorth η hη hη0)
      change spForm 2 K η₁ h ≠ 0 at h1
      change spForm 2 K η₁ η ≠ 0 at h2
      have hu₂ : (η + η₁) + l • w ∈ transCenters G := hstep2 _ (H.add_mem hη hη₁)
        (by rw [map_add, LinearMap.add_apply, hηh, zero_add]; exact h1) l
      have hB : spForm 2 K η₁ ((η + η₁) + l • w) ≠ 0 := by
        simp only [map_add, map_smul, smul_eq_mul, spForm_self, add_zero, hwH η₁ hη₁,
          mul_zero]
        exact h2
      have := lincomb_mem_transCenters hGS (hH η₁ hη₁) hu₂ hB (-1) 1
      convert this using 1
      rw [neg_one_smul, one_smul]
      abel
    · exact hstep2 η hη hηh l
  have hπ : ∀ u, spForm 2 K w u = 0 → u ∈ transCenters G := by
    intro u hu
    obtain ⟨η, hη, y, hy, rfl⟩ := Submodule.mem_sup.mp
      ((sup_orth_eq_top hHinf).symm ▸ Submodule.mem_top (x := u))
    have hyw : spForm 2 K w y = 0 := by
      have := hu
      rw [map_add, spForm_eq_zero_comm (hwH η hη), zero_add] at this
      exact this
    obtain ⟨l, rfl⟩ := mem_span_of_orth_of_isotropic hHinf hOrank hw hw0 hy hyw
    exact hstep3 η hη l
  obtain ⟨E, hE, hwE⟩ : ∃ E ∈ transCenters G, spForm 2 K w E ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (eq_zero_of_forall_mem_spForm hspan fun s hs =>
      spForm_eq_zero_comm (hcon s hs))
  have hall : ∀ v, v ∈ transCenters G := mem_transCenters_of_orth_subset h2 hGS hπ hE hwE
  refine le_antisymm hGS ?_
  rw [statedSp_eq_closure_spTrans, Subgroup.closure_le]
  rintro _ ⟨v, d, rfl⟩
  exact hall v d

theorem eq_statedSp_of_spTrans_mem {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p)) (hirr : IsIrreducibleOn G)
    [Group.IsPerfect G] {a : V₄ → ZMod p} (ha : a ≠ 0) {c : ZMod p} (hc : c ≠ 0)
    (hT : spTrans a c ∈ G) : G = StatedSp 2 (ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  exact eq_statedSp_of_spTrans_mem' h2 (fun c => ⟨c.val, ZMod.natCast_zmod_val c⟩) hGS hirr ha
    hc hT

end CFSG.RankThree.SubgroupLists
