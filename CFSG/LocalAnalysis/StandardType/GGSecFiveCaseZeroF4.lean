module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCore

public section

namespace CFSG.StandardType

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}

section

variable {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}

private noncomputable def ggCZBLin (φ : Fin 4 → Module.Dual (ZMod p) V) (a : V) :
    Module.Dual (ZMod p) V := ∑ k : Fin 4, φ k a • φ k

private lemma ggCZBLin_apply {φ : Fin 4 → Module.Dual (ZMod p) V} {a v : V} :
    ggCZBLin φ a v = ggCZForm φ v a := by
  simp [ggCZBLin, ggCZForm, mul_comm]

private lemma phi_e (hd : GGCZDual e φ) (i j : Fin 4) :
    φ i (e j) = if i = j then 1 else 0 := hd i j

private lemma B_RD (hd : GGCZDual e φ) {i j : Fin 4} {ε : ZMod p} (v : V) :
    ggCZForm φ v (e i - ε • e j) = φ i v - ε * φ j v := by
  rw [ggCZForm_sub_right, ggCZForm_smul_right, ggCZForm_apply_e hd, ggCZForm_apply_e hd]

private lemma B_self_RD (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) : ggCZForm φ (e i - ε • e j) (e i - ε • e j) = 2 := by
  rw [B_RD hd]
  simp only [map_sub, map_smul, phi_e hd, smul_eq_mul]
  simp only [if_neg hij, if_neg (Ne.symm hij)]
  rcases hε with rfl | rfl <;> norm_num

private lemma B_S (hd : GGCZDual e φ) {i : Fin 4} (v : V) :
    ggCZForm φ v (e i) = φ i v := ggCZForm_apply_e hd v i

private lemma B_self_S (hd : GGCZDual e φ) (i : Fin 4) :
    ggCZForm φ (e i) (e i) = 1 := by
  rw [B_S hd, phi_e hd, if_pos rfl]

private noncomputable def ggCZHvec (e : Fin 4 → V) (w : Fin 4 → ZMod p) : V :=
  ∑ k, w k • e k

private noncomputable def ggCZHform (φ : Fin 4 → Module.Dual (ZMod p) V) (w : Fin 4 → ZMod p) :
    Module.Dual (ZMod p) V := (2 : ZMod p)⁻¹ • ∑ k, w k • φ k

private lemma B_H (hd : GGCZDual e φ) {w : Fin 4 → ZMod p} (v : V) :
    ggCZForm φ v (ggCZHvec e w) = ∑ k, w k * φ k v := by
  simp only [ggCZHvec, ggCZForm, map_sum, map_smul, phi_e hd, Finset.mul_sum, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ k) h

private lemma two_inv_mul_four (hp2 : p ≠ 2) : (2 : ZMod p)⁻¹ * 4 = 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  field_simp
  ring

private lemma B_self_H (hd : GGCZDual e φ) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) :
    ggCZForm φ (ggCZHvec e w) (ggCZHvec e w) = 4 := by
  have hφ : ∀ l, φ l (ggCZHvec e w) = ∑ m, w m * φ l (e m) := by
    intro l
    simp [ggCZHvec]
  rw [B_H hd]
  have h1 : ∀ k, w k * φ k (ggCZHvec e w) = 1 := by
    intro k
    rw [hφ k, Finset.mul_sum]
    have h2 : ∀ i, w k * (w i * φ k (e i)) = if i = k then w k * w k else 0 := by
      intro i
      rw [phi_e hd]
      by_cases h : i = k
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h]; simp
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    rw [Finset.sum_eq_single k]
    · have hk1 : w k * w k = 1 := by
        rcases hw k with hk | hk <;> rw [hk] <;> ring
      simp [hk1]
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [Finset.sum_congr rfl fun k _ => h1 k]
  simp

private noncomputable def ggCZRefl (φ : Fin 4 → Module.Dual (ZMod p) V) (a : V) (c : ZMod p)
    (h : (c • ggCZBLin φ a) a = 2) : V ≃ₗ[ZMod p] V :=
  Module.reflection h

private lemma ggCZRefl_apply {φ : Fin 4 → Module.Dual (ZMod p) V} {a : V} {c : ZMod p}
    (h : (c • ggCZBLin φ a) a = 2) (v : V) :
    ggCZRefl φ a c h v = v - (c * ggCZForm φ v a) • a := by
  rw [ggCZRefl, Module.reflection_apply, LinearMap.smul_apply, smul_eq_mul, ggCZBLin_apply]

private lemma ggCZRefl_isom {x : V} {c : ZMod p}
    (h : (c • ggCZBLin φ x) x = 2) (hc : c * ggCZForm φ x x = 2) :
    ∀ v w, ggCZForm φ (ggCZRefl φ x c h v) (ggCZRefl φ x c h w) = ggCZForm φ v w := by
  intro v w
  rw [ggCZRefl_apply, ggCZRefl_apply, ggCZForm_sub_left, ggCZForm_sub_right, ggCZForm_smul_right,
    ggCZForm_smul_left, ggCZForm_sub_right, ggCZForm_smul_right, ggCZForm_comm (φ := φ) x w]
  have h2 : c * ggCZForm φ v x * (c * ggCZForm φ w x * ggCZForm φ x x)
      = c * ggCZForm φ v x * ggCZForm φ w x * 2 := by
    rw [← hc]
    ring
  rw [mul_sub, h2]
  ring

private lemma ggCZRefl_aux_RD (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) :
    ((1 : ZMod p) • ggCZBLin φ (e i - ε • e j)) (e i - ε • e j) = 2 := by
  rw [one_smul, ggCZBLin_apply]
  exact B_self_RD hd hij hε

private lemma ggCZRefl_aux_S (hd : GGCZDual e φ) (i : Fin 4) :
    ((2 : ZMod p) • ggCZBLin φ (e i)) (e i) = 2 := by
  rw [LinearMap.smul_apply, smul_eq_mul, ggCZBLin_apply, B_self_S hd]
  norm_num

private lemma ggCZRefl_aux_H (hd : GGCZDual e φ) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) (hp2 : p ≠ 2) :
    ((2 : ZMod p)⁻¹ • ggCZBLin φ (ggCZHvec e w)) (ggCZHvec e w) = 2 := by
  rw [LinearMap.smul_apply, smul_eq_mul, ggCZBLin_apply, B_self_H hd hw, two_inv_mul_four hp2]

private noncomputable def ggCZRDrefl (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) : V ≃ₗ[ZMod p] V :=
  ggCZRefl φ (e i - ε • e j) 1 (ggCZRefl_aux_RD hd hij hε)

private lemma ggCZRDrefl_apply (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (v : V) :
    ggCZRDrefl hd hij hε v = v - (φ i v - ε * φ j v) • (e i - ε • e j) := by
  rw [ggCZRDrefl, ggCZRefl_apply, B_RD hd, one_mul]

private noncomputable def ggCZSrefl (hd : GGCZDual e φ) (i : Fin 4) : V ≃ₗ[ZMod p] V :=
  ggCZRefl φ (e i) 2 (ggCZRefl_aux_S hd i)

private lemma ggCZSrefl_apply (hd : GGCZDual e φ) (i : Fin 4) (v : V) :
    ggCZSrefl hd i v = v - (2 * φ i v) • e i := by
  rw [ggCZSrefl, ggCZRefl_apply, B_S hd]

private noncomputable def ggCZHrefl (hd : GGCZDual e φ) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) (hp2 : p ≠ 2) : V ≃ₗ[ZMod p] V :=
  ggCZRefl φ (ggCZHvec e w) ((2 : ZMod p)⁻¹) (ggCZRefl_aux_H hd hw hp2)

private lemma ggCZHrefl_apply (hd : GGCZDual e φ) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) (hp2 : p ≠ 2) (v : V) :
    ggCZHrefl hd hw hp2 v =
      v - ((2 : ZMod p)⁻¹ * ∑ k, w k * φ k v) • ggCZHvec e w := by
  rw [ggCZHrefl, ggCZRefl_apply, B_H hd]

private def ggCZLong (e : Fin 4 → V) : Set V :=
  {b | ∃ i j : Fin 4, i ≠ j ∧ ∃ c d : ZMod p, (c = 1 ∨ c = -1) ∧ (d = 1 ∨ d = -1) ∧
    b = c • e i + d • e j}

private lemma ggCZLong_sub (i j : Fin 4) (hij : i ≠ j) (ε : ZMod p)
    (hε : ε = 1 ∨ ε = -1) : e i - ε • e j ∈ ggCZLong (p := p) e := by
  refine ⟨i, j, hij, 1, -ε, Or.inl rfl, ?_, ?_⟩
  · rcases hε with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (by norm_num)
  · rw [one_smul, neg_smul, sub_eq_add_neg]

private lemma ggCZLong_neg {b : V} (hb : b ∈ ggCZLong (p := p) e) : -b ∈ ggCZLong (p := p) e := by
  obtain ⟨i, j, hij, c, d, hc, hd, rfl⟩ := hb
  refine ⟨i, j, hij, -c, -d, ?_, ?_, ?_⟩
  · rcases hc with rfl | rfl <;> norm_num
  · rcases hd with rfl | rfl <;> norm_num
  · rw [neg_add, neg_smul, neg_smul]

private lemma exists_RD_repr {b : V} (hb : b ∈ ggCZLong (p := p) e) :
    ∃ (i j : Fin 4) (_hij : i ≠ j) (ε q : ZMod p), (ε = 1 ∨ ε = -1) ∧ (q = 1 ∨ q = -1) ∧
      b = q • (e i - ε • e j) := by
  obtain ⟨i, j, hij, c, d, hc, hd, rfl⟩ := hb
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact ⟨i, j, hij, -1, 1, Or.inr rfl, Or.inl rfl, by simp [sub_eq_add_neg]⟩
  · exact ⟨i, j, hij, 1, 1, Or.inl rfl, Or.inl rfl, by simp [sub_eq_add_neg]⟩
  · exact ⟨i, j, hij, 1, -1, Or.inl rfl, Or.inr rfl, by simp [sub_eq_add_neg]⟩
  · exact ⟨i, j, hij, -1, -1, Or.inr rfl, Or.inr rfl, by simp [sub_eq_add_neg]⟩

private lemma smul_B_eq (hd : GGCZDual e φ) {b : V} {q : ZMod p} (hq : q = 1 ∨ q = -1)
    {i j : Fin 4} {ε : ZMod p} (hb : b = q • (e i - ε • e j)) (v : V) :
    ggCZForm φ v b • b = (φ i v - ε * φ j v) • (e i - ε • e j) := by
  rw [hb, ggCZForm_smul_right, B_RD hd, smul_smul]
  rw [show (q * (φ i v - ε * φ j v)) * q = φ i v - ε * φ j v by
    rcases hq with rfl | rfl <;> ring]

private lemma mem_RD_of_form (hd : GGCZDual e φ) {r : V ≃ₗ[ZMod p] V} {b : V}
    (hb : b ∈ ggCZLong (p := p) e) (hr : ∀ v, r v = v - ggCZForm φ v b • b) : r ∈ ggCZRD e φ := by
  obtain ⟨i, j, _hij, ε, q, hε, hq, rfl⟩ := exists_RD_repr hb
  exact ⟨i, j, _hij, ε, hε, fun v => by rw [hr v, smul_B_eq hd hq rfl]⟩

private lemma conj_form_B_smul {g : V ≃ₗ[ZMod p] V} {a : V} {c : ZMod p}
    {r : V ≃ₗ[ZMod p] V} (hiso : ∀ v w, ggCZForm φ (g v) (g w) = ggCZForm φ v w)
    (hr : ∀ v, r v = v - (c * ggCZForm φ v a) • a) (v : V) :
    (g * r * g⁻¹) v = v - (c * ggCZForm φ v (g a)) • g a := by
  have h1 : (g * r * g⁻¹) v = g (r (g⁻¹ v)) := rfl
  rw [h1, hr]
  simp only [map_sub, map_smul, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  rw [← hiso (g.symm v) a, LinearEquiv.apply_symm_apply]

private lemma conj_eq_refl {g r r' : V ≃ₗ[ZMod p] V} {b b' : V} {c c' q : ZMod p}
    (hiso : ∀ v w, ggCZForm φ (g v) (g w) = ggCZForm φ v w)
    (hcq : c * q * q = c') (himg : g b = q • b')
    (hr : ∀ v, r v = v - (c * ggCZForm φ v b) • b)
    (hr' : ∀ v, r' v = v - (c' * ggCZForm φ v b') • b') :
    g * r * g⁻¹ = r' := by
  refine LinearEquiv.ext fun v => ?_
  rw [conj_form_B_smul hiso hr v, himg, ggCZForm_smul_right, smul_smul,
    show (c * (q * ggCZForm φ v b')) * q = c' * ggCZForm φ v b' by
      rw [← hcq]; ring, hr' v]

private noncomputable def gen0 (hd : GGCZDual e φ) : V ≃ₗ[ZMod p] V :=
  ggCZRDrefl hd (i := 1) (j := 2) (by decide) (ε := 1) (Or.inl rfl)

private noncomputable def gen1 (hd : GGCZDual e φ) : V ≃ₗ[ZMod p] V :=
  ggCZRDrefl hd (i := 2) (j := 3) (by decide) (ε := 1) (Or.inl rfl)

private noncomputable def gen2 (hd : GGCZDual e φ) : V ≃ₗ[ZMod p] V :=
  ggCZSrefl hd 3

private lemma B_h (hd : GGCZDual e φ) (v : V) :
    ggCZForm φ v (e 0 - e 1 - e 2 - e 3) = φ 0 v - φ 1 v - φ 2 v - φ 3 v := by
  rw [ggCZForm_sub_right, ggCZForm_sub_right, ggCZForm_sub_right, B_S hd, B_S hd, B_S hd, B_S hd]

private lemma B_h_self (hd : GGCZDual e φ) :
    ggCZForm φ (e 0 - e 1 - e 2 - e 3) (e 0 - e 1 - e 2 - e 3) = 4 := by
  rw [B_h hd]
  simp only [map_sub, phi_e hd]
  norm_num

private noncomputable def gen3 (hd : GGCZDual e φ) (hp2 : p ≠ 2) : V ≃ₗ[ZMod p] V :=
  ggCZRefl φ (e 0 - e 1 - e 2 - e 3) ((2 : ZMod p)⁻¹) (by
    rw [LinearMap.smul_apply, smul_eq_mul, ggCZBLin_apply, B_h_self hd, two_inv_mul_four hp2])

private lemma gen0_apply (hd : GGCZDual e φ) (v : V) :
    gen0 hd v = v - (φ 1 v - φ 2 v) • (e 1 - e 2) := by
  rw [gen0, ggCZRDrefl_apply]
  simp

private lemma gen1_apply (hd : GGCZDual e φ) (v : V) :
    gen1 hd v = v - (φ 2 v - φ 3 v) • (e 2 - e 3) := by
  rw [gen1, ggCZRDrefl_apply]
  simp

private lemma gen2_apply (hd : GGCZDual e φ) (v : V) :
    gen2 hd v = v - (2 * φ 3 v) • e 3 :=
  ggCZSrefl_apply hd 3 v

private lemma gen3_apply (hd : GGCZDual e φ) (hp2 : p ≠ 2) (v : V) :
    gen3 hd hp2 v = v - ((2 : ZMod p)⁻¹ * (φ 0 v - φ 1 v - φ 2 v - φ 3 v)) •
      (e 0 - e 1 - e 2 - e 3) := by
  rw [gen3, ggCZRefl_apply, B_h hd]

private lemma gen0_mem (hd : GGCZDual e φ) : gen0 hd ∈ ggCZWF4 p e φ := by
  refine Subgroup.subset_closure ⟨0, ?_⟩
  simp only [GGCZGensF4]
  exact gen0_apply hd

private lemma gen1_mem (hd : GGCZDual e φ) : gen1 hd ∈ ggCZWF4 p e φ := by
  refine Subgroup.subset_closure ⟨1, ?_⟩
  simp only [GGCZGensF4]
  exact gen1_apply hd

private lemma gen2_mem (hd : GGCZDual e φ) : gen2 hd ∈ ggCZWF4 p e φ := by
  refine Subgroup.subset_closure ⟨2, ?_⟩
  simp only [GGCZGensF4]
  exact gen2_apply hd

private lemma gen3_mem (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 ∈ ggCZWF4 p e φ := by
  refine Subgroup.subset_closure ⟨3, ?_⟩
  simp only [GGCZGensF4]
  exact gen3_apply hd hp2

private lemma gen0_isom (hd : GGCZDual e φ) :
    ∀ v w, ggCZForm φ (gen0 hd v) (gen0 hd w) = ggCZForm φ v w :=
  ggCZRefl_isom (ggCZRefl_aux_RD hd (i := 1) (j := 2) (by decide) (ε := 1) (Or.inl rfl))
    (by rw [one_mul]; exact B_self_RD hd (by decide) (Or.inl rfl))

private lemma gen1_isom (hd : GGCZDual e φ) :
    ∀ v w, ggCZForm φ (gen1 hd v) (gen1 hd w) = ggCZForm φ v w :=
  ggCZRefl_isom (ggCZRefl_aux_RD hd (i := 2) (j := 3) (by decide) (ε := 1) (Or.inl rfl))
    (by rw [one_mul]; exact B_self_RD hd (by decide) (Or.inl rfl))

private lemma gen2_isom (hd : GGCZDual e φ) :
    ∀ v w, ggCZForm φ (gen2 hd v) (gen2 hd w) = ggCZForm φ v w :=
  ggCZRefl_isom (ggCZRefl_aux_S hd 3) (by rw [B_self_S hd]; norm_num)

private lemma gen3_isom (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    ∀ v w, ggCZForm φ (gen3 hd hp2 v) (gen3 hd hp2 w) = ggCZForm φ v w :=
  ggCZRefl_isom (x := e 0 - e 1 - e 2 - e 3) (c := (2 : ZMod p)⁻¹)
    (by rw [LinearMap.smul_apply, smul_eq_mul, ggCZBLin_apply, B_h_self hd,
      two_inv_mul_four hp2])
    (by rw [B_h_self hd, two_inv_mul_four hp2])

private lemma gen0_e0 (hd : GGCZDual e φ) : gen0 hd (e 0) = e 0 := by
  rw [gen0_apply]
  simp [phi_e hd]

private lemma gen0_e1 (hd : GGCZDual e φ) : gen0 hd (e 1) = e 2 := by
  rw [gen0_apply]
  simp [phi_e hd]

private lemma gen0_e2 (hd : GGCZDual e φ) : gen0 hd (e 2) = e 1 := by
  rw [gen0_apply]
  simp [phi_e hd]

private lemma gen0_e3 (hd : GGCZDual e φ) : gen0 hd (e 3) = e 3 := by
  rw [gen0_apply]
  simp [phi_e hd]

private lemma gen1_e0 (hd : GGCZDual e φ) : gen1 hd (e 0) = e 0 := by
  rw [gen1_apply]
  simp [phi_e hd]

private lemma gen1_e1 (hd : GGCZDual e φ) : gen1 hd (e 1) = e 1 := by
  rw [gen1_apply]
  simp [phi_e hd]

private lemma gen1_e2 (hd : GGCZDual e φ) : gen1 hd (e 2) = e 3 := by
  rw [gen1_apply]
  simp [phi_e hd]

private lemma gen1_e3 (hd : GGCZDual e φ) : gen1 hd (e 3) = e 2 := by
  rw [gen1_apply]
  simp [phi_e hd]

private lemma gen2_e0 (hd : GGCZDual e φ) : gen2 hd (e 0) = e 0 := by
  rw [gen2_apply]
  simp [phi_e hd]

private lemma gen2_e1 (hd : GGCZDual e φ) : gen2 hd (e 1) = e 1 := by
  rw [gen2_apply]
  simp [phi_e hd]

private lemma gen2_e2 (hd : GGCZDual e φ) : gen2 hd (e 2) = e 2 := by
  rw [gen2_apply]
  simp [phi_e hd]

private lemma gen2_e3 (hd : GGCZDual e φ) : gen2 hd (e 3) = -e 3 := by
  rw [gen2_apply]
  simp [phi_e hd]
  module

private noncomputable def ggCZR (e : Fin 4 → V) (k : Fin 4) : V :=
  match k with
  | 0 => e 0 + e 1 + e 2 + e 3
  | 1 => e 0 + e 1 - e 2 - e 3
  | 2 => e 0 - e 1 + e 2 - e 3
  | 3 => e 0 - e 1 - e 2 + e 3

private lemma gen3_two_smul (hd : GGCZDual e φ) (hp2 : p ≠ 2) (v : V) :
    (2 : ZMod p) • gen3 hd hp2 v =
      (2 : ZMod p) • v - ggCZForm φ v (e 0 - e 1 - e 2 - e 3) • (e 0 - e 1 - e 2 - e 3) := by
  rw [gen3_apply, smul_sub, smul_smul,
    show (2 : ZMod p) * (2⁻¹ * (φ 0 v - φ 1 v - φ 2 v - φ 3 v)) =
      φ 0 v - φ 1 v - φ 2 v - φ 3 v from by
    rw [← mul_assoc, mul_inv_cancel₀ (zmod_two_ne_zero hp2), one_mul],
    ← B_h hd]

private lemma gen3_two_e0 (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (2 : ZMod p) • gen3 hd hp2 (e 0) = ggCZR e 0 := by
  rw [gen3_two_smul hd hp2, B_h hd]
  simp only [phi_e hd]
  norm_num
  simp [ggCZR]
  module

private lemma gen3_two_e1 (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (2 : ZMod p) • gen3 hd hp2 (e 1) = ggCZR e 1 := by
  rw [gen3_two_smul hd hp2, B_h hd]
  simp only [phi_e hd]
  norm_num
  simp [ggCZR]
  module

private lemma gen3_two_e2 (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (2 : ZMod p) • gen3 hd hp2 (e 2) = ggCZR e 2 := by
  rw [gen3_two_smul hd hp2, B_h hd]
  simp only [phi_e hd]
  norm_num
  simp [ggCZR]
  module

private lemma gen3_two_e3 (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (2 : ZMod p) • gen3 hd hp2 (e 3) = ggCZR e 3 := by
  rw [gen3_two_smul hd hp2, B_h hd]
  simp only [phi_e hd]
  norm_num
  simp [ggCZR]
  module

private def MapsLong (e : Fin 4 → V) (g : V ≃ₗ[ZMod p] V) : Prop :=
  ∀ b ∈ ggCZLong (p := p) e, g b ∈ ggCZLong (p := p) e

private lemma inv_two_mul_two (hp2 : p ≠ 2) : (2 : ZMod p)⁻¹ * 2 = 1 :=
  inv_mul_cancel₀ (zmod_two_ne_zero hp2)

private lemma gen3_img_01_p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 0 + e 1) = e 0 + e 1 := by
  rw [gen3_apply]
  simp only [map_add, phi_e hd]
  norm_num

private lemma gen3_img_01_m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 0 - e 1) = e 2 + e 3 := by
  rw [gen3_apply]
  simp only [map_sub, phi_e hd]
  norm_num
  rw [inv_two_mul_two (p := p) hp2, one_smul]
  module

private lemma gen3_img_02_p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 0 + e 2) = e 0 + e 2 := by
  rw [gen3_apply]
  simp only [map_add, phi_e hd]
  norm_num

private lemma gen3_img_02_m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 0 - e 2) = e 1 + e 3 := by
  rw [gen3_apply]
  simp only [map_sub, phi_e hd]
  norm_num
  rw [inv_two_mul_two (p := p) hp2, one_smul]
  module

private lemma gen3_img_03_p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 0 + e 3) = e 0 + e 3 := by
  rw [gen3_apply]
  simp only [map_add, phi_e hd]
  norm_num

private lemma gen3_img_03_m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 0 - e 3) = e 1 + e 2 := by
  rw [gen3_apply]
  simp only [map_sub, phi_e hd]
  norm_num
  rw [inv_two_mul_two (p := p) hp2, one_smul]
  module

private lemma gen3_img_12_p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 1 + e 2) = e 0 - e 3 := by
  rw [gen3_apply]
  simp only [map_add, phi_e hd]
  norm_num
  rw [inv_two_mul_two (p := p) hp2, one_smul]
  module

private lemma gen3_img_12_m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 1 - e 2) = e 1 - e 2 := by
  rw [gen3_apply]
  simp only [map_sub, phi_e hd]
  norm_num

private lemma gen3_img_13_p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 1 + e 3) = e 0 - e 2 := by
  rw [gen3_apply]
  simp only [map_add, phi_e hd]
  norm_num
  rw [inv_two_mul_two (p := p) hp2, one_smul]
  module

private lemma gen3_img_13_m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 1 - e 3) = e 1 - e 3 := by
  rw [gen3_apply]
  simp only [map_sub, phi_e hd]
  norm_num

private lemma gen3_img_23_p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 2 + e 3) = e 0 - e 1 := by
  rw [gen3_apply]
  simp only [map_add, phi_e hd]
  norm_num
  rw [inv_two_mul_two (p := p) hp2, one_smul]
  module

private lemma gen3_img_23_m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (e 2 - e 3) = e 2 - e 3 := by
  rw [gen3_apply]
  simp only [map_sub, phi_e hd]
  norm_num

private lemma gen3_long_01 (hd : GGCZDual e φ) (hp2 : p ≠ 2) {c d : ZMod p}
    (hc : c = 1 ∨ c = -1) (hd' : d = 1 ∨ d = -1) :
    gen3 hd hp2 (c • e 0 + d • e 1) ∈ ggCZLong (p := p) e := by
  rcases hc with rfl | rfl <;> rcases hd' with rfl | rfl
  · have hv : (1 : ZMod p) • e 0 + (1 : ZMod p) • e 1 = e 0 + e 1 := by module
    rw [hv, gen3_img_01_p]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 0 1 (by decide) (-1) (Or.inr rfl))
  · have hv : (1 : ZMod p) • e 0 + (-1 : ZMod p) • e 1 = e 0 - e 1 := by module
    rw [hv, gen3_img_01_m]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 2 3 (by decide) (-1) (Or.inr rfl))
  · have hv : (-1 : ZMod p) • e 0 + (1 : ZMod p) • e 1 = -(e 0 - e 1) := by module
    rw [hv, map_neg, gen3_img_01_m]
    have hmem := ggCZLong_sub (p := p) (e := e) 2 3 (by decide) (-1) (Or.inr rfl)
    exact ggCZLong_neg (by simpa using hmem)
  · have hv : (-1 : ZMod p) • e 0 + (-1 : ZMod p) • e 1 = -(e 0 + e 1) := by module
    rw [hv, map_neg, gen3_img_01_p]
    have hmem := ggCZLong_sub (p := p) (e := e) 0 1 (by decide) (-1) (Or.inr rfl)
    exact ggCZLong_neg (by simpa using hmem)

private lemma gen3_long_02 (hd : GGCZDual e φ) (hp2 : p ≠ 2) {c d : ZMod p}
    (hc : c = 1 ∨ c = -1) (hd' : d = 1 ∨ d = -1) :
    gen3 hd hp2 (c • e 0 + d • e 2) ∈ ggCZLong (p := p) e := by
  rcases hc with rfl | rfl <;> rcases hd' with rfl | rfl
  · have hv : (1 : ZMod p) • e 0 + (1 : ZMod p) • e 2 = e 0 + e 2 := by module
    rw [hv, gen3_img_02_p]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 0 2 (by decide) (-1) (Or.inr rfl))
  · have hv : (1 : ZMod p) • e 0 + (-1 : ZMod p) • e 2 = e 0 - e 2 := by module
    rw [hv, gen3_img_02_m]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 1 3 (by decide) (-1) (Or.inr rfl))
  · have hv : (-1 : ZMod p) • e 0 + (1 : ZMod p) • e 2 = -(e 0 - e 2) := by module
    rw [hv, map_neg, gen3_img_02_m]
    have hmem := ggCZLong_sub (p := p) (e := e) 1 3 (by decide) (-1) (Or.inr rfl)
    exact ggCZLong_neg (by simpa using hmem)
  · have hv : (-1 : ZMod p) • e 0 + (-1 : ZMod p) • e 2 = -(e 0 + e 2) := by module
    rw [hv, map_neg, gen3_img_02_p]
    have hmem := ggCZLong_sub (p := p) (e := e) 0 2 (by decide) (-1) (Or.inr rfl)
    exact ggCZLong_neg (by simpa using hmem)

private lemma gen3_long_03 (hd : GGCZDual e φ) (hp2 : p ≠ 2) {c d : ZMod p}
    (hc : c = 1 ∨ c = -1) (hd' : d = 1 ∨ d = -1) :
    gen3 hd hp2 (c • e 0 + d • e 3) ∈ ggCZLong (p := p) e := by
  rcases hc with rfl | rfl <;> rcases hd' with rfl | rfl
  · have hv : (1 : ZMod p) • e 0 + (1 : ZMod p) • e 3 = e 0 + e 3 := by module
    rw [hv, gen3_img_03_p]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 0 3 (by decide) (-1) (Or.inr rfl))
  · have hv : (1 : ZMod p) • e 0 + (-1 : ZMod p) • e 3 = e 0 - e 3 := by module
    rw [hv, gen3_img_03_m]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 1 2 (by decide) (-1) (Or.inr rfl))
  · have hv : (-1 : ZMod p) • e 0 + (1 : ZMod p) • e 3 = -(e 0 - e 3) := by module
    rw [hv, map_neg, gen3_img_03_m]
    have hmem := ggCZLong_sub (p := p) (e := e) 1 2 (by decide) (-1) (Or.inr rfl)
    exact ggCZLong_neg (by simpa using hmem)
  · have hv : (-1 : ZMod p) • e 0 + (-1 : ZMod p) • e 3 = -(e 0 + e 3) := by module
    rw [hv, map_neg, gen3_img_03_p]
    have hmem := ggCZLong_sub (p := p) (e := e) 0 3 (by decide) (-1) (Or.inr rfl)
    exact ggCZLong_neg (by simpa using hmem)

private lemma gen3_long_12 (hd : GGCZDual e φ) (hp2 : p ≠ 2) {c d : ZMod p}
    (hc : c = 1 ∨ c = -1) (hd' : d = 1 ∨ d = -1) :
    gen3 hd hp2 (c • e 1 + d • e 2) ∈ ggCZLong (p := p) e := by
  rcases hc with rfl | rfl <;> rcases hd' with rfl | rfl
  · have hv : (1 : ZMod p) • e 1 + (1 : ZMod p) • e 2 = e 1 + e 2 := by module
    rw [hv, gen3_img_12_p]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 0 3 (by decide) 1 (Or.inl rfl))
  · have hv : (1 : ZMod p) • e 1 + (-1 : ZMod p) • e 2 = e 1 - e 2 := by module
    rw [hv, gen3_img_12_m]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 1 2 (by decide) 1 (Or.inl rfl))
  · have hv : (-1 : ZMod p) • e 1 + (1 : ZMod p) • e 2 = -(e 1 - e 2) := by module
    rw [hv, map_neg, gen3_img_12_m]
    have hmem := ggCZLong_sub (p := p) (e := e) 1 2 (by decide) 1 (Or.inl rfl)
    exact ggCZLong_neg (by simpa using hmem)
  · have hv : (-1 : ZMod p) • e 1 + (-1 : ZMod p) • e 2 = -(e 1 + e 2) := by module
    rw [hv, map_neg, gen3_img_12_p]
    have hmem := ggCZLong_sub (p := p) (e := e) 0 3 (by decide) 1 (Or.inl rfl)
    exact ggCZLong_neg (by simpa using hmem)

private lemma gen3_long_13 (hd : GGCZDual e φ) (hp2 : p ≠ 2) {c d : ZMod p}
    (hc : c = 1 ∨ c = -1) (hd' : d = 1 ∨ d = -1) :
    gen3 hd hp2 (c • e 1 + d • e 3) ∈ ggCZLong (p := p) e := by
  rcases hc with rfl | rfl <;> rcases hd' with rfl | rfl
  · have hv : (1 : ZMod p) • e 1 + (1 : ZMod p) • e 3 = e 1 + e 3 := by module
    rw [hv, gen3_img_13_p]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 0 2 (by decide) 1 (Or.inl rfl))
  · have hv : (1 : ZMod p) • e 1 + (-1 : ZMod p) • e 3 = e 1 - e 3 := by module
    rw [hv, gen3_img_13_m]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 1 3 (by decide) 1 (Or.inl rfl))
  · have hv : (-1 : ZMod p) • e 1 + (1 : ZMod p) • e 3 = -(e 1 - e 3) := by module
    rw [hv, map_neg, gen3_img_13_m]
    have hmem := ggCZLong_sub (p := p) (e := e) 1 3 (by decide) 1 (Or.inl rfl)
    exact ggCZLong_neg (by simpa using hmem)
  · have hv : (-1 : ZMod p) • e 1 + (-1 : ZMod p) • e 3 = -(e 1 + e 3) := by module
    rw [hv, map_neg, gen3_img_13_p]
    have hmem := ggCZLong_sub (p := p) (e := e) 0 2 (by decide) 1 (Or.inl rfl)
    exact ggCZLong_neg (by simpa using hmem)

private lemma gen3_long_23 (hd : GGCZDual e φ) (hp2 : p ≠ 2) {c d : ZMod p}
    (hc : c = 1 ∨ c = -1) (hd' : d = 1 ∨ d = -1) :
    gen3 hd hp2 (c • e 2 + d • e 3) ∈ ggCZLong (p := p) e := by
  rcases hc with rfl | rfl <;> rcases hd' with rfl | rfl
  · have hv : (1 : ZMod p) • e 2 + (1 : ZMod p) • e 3 = e 2 + e 3 := by module
    rw [hv, gen3_img_23_p]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 0 1 (by decide) 1 (Or.inl rfl))
  · have hv : (1 : ZMod p) • e 2 + (-1 : ZMod p) • e 3 = e 2 - e 3 := by module
    rw [hv, gen3_img_23_m]
    exact (by simpa using ggCZLong_sub (p := p) (e := e) 2 3 (by decide) 1 (Or.inl rfl))
  · have hv : (-1 : ZMod p) • e 2 + (1 : ZMod p) • e 3 = -(e 2 - e 3) := by module
    rw [hv, map_neg, gen3_img_23_m]
    have hmem := ggCZLong_sub (p := p) (e := e) 2 3 (by decide) 1 (Or.inl rfl)
    exact ggCZLong_neg (by simpa using hmem)
  · have hv : (-1 : ZMod p) • e 2 + (-1 : ZMod p) • e 3 = -(e 2 + e 3) := by module
    rw [hv, map_neg, gen3_img_23_p]
    have hmem := ggCZLong_sub (p := p) (e := e) 0 1 (by decide) 1 (Or.inl rfl)
    exact ggCZLong_neg (by simpa using hmem)

private lemma mapsLong_gen3 (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    MapsLong e (gen3 hd hp2) := by
  rintro b ⟨i, j, hij, c, d, hc, hd', rfl⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact gen3_long_01 hd hp2 hc hd'
  · exact gen3_long_02 hd hp2 hc hd'
  · exact gen3_long_03 hd hp2 hc hd'
  · simpa [add_comm] using gen3_long_01 hd hp2 hd' hc
  · exact absurd rfl hij
  · exact gen3_long_12 hd hp2 hc hd'
  · exact gen3_long_13 hd hp2 hc hd'
  · simpa [add_comm] using gen3_long_02 hd hp2 hd' hc
  · simpa [add_comm] using gen3_long_12 hd hp2 hd' hc
  · exact absurd rfl hij
  · exact gen3_long_23 hd hp2 hc hd'
  · simpa [add_comm] using gen3_long_03 hd hp2 hd' hc
  · simpa [add_comm] using gen3_long_13 hd hp2 hd' hc
  · simpa [add_comm] using gen3_long_23 hd hp2 hd' hc
  · exact absurd rfl hij

private def IsomB (φ : Fin 4 → Module.Dual (ZMod p) V) (g : V ≃ₗ[ZMod p] V) : Prop :=
  ∀ v w, ggCZForm φ (g v) (g w) = ggCZForm φ v w

private lemma IsomB.mul {g h : V ≃ₗ[ZMod p] V} (hg : IsomB φ g) (hh : IsomB φ h) :
    IsomB φ (g * h) := by
  intro v w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, hh]

private lemma mapsLong_of_smul_perm (g : V ≃ₗ[ZMod p] V) (σ : Fin 4 ≃ Fin 4)
    {c : Fin 4 → ZMod p} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (himg : ∀ i, g (e i) = c i • e (σ i)) : MapsLong e g := by
  rintro b ⟨i, j, hij, c0, d0, hc0, hd0, rfl⟩
  refine ⟨σ i, σ j, fun h => hij (σ.injective h), c0 * c i, d0 * c j, ?_, ?_, ?_⟩
  · rcases hc0 with rfl | rfl <;> rcases hc i with h | h <;> rw [h] <;> norm_num
  · rcases hd0 with rfl | rfl <;> rcases hc j with h | h <;> rw [h] <;> norm_num
  · rw [map_add, map_smul, map_smul, himg i, himg j, smul_smul, smul_smul]

private def swap12 : Fin 4 ≃ Fin 4 := Equiv.swap 1 2

private def swap23 : Fin 4 ≃ Fin 4 := Equiv.swap 2 3

private lemma mapsLong_gen0 (hd : GGCZDual e φ) : MapsLong e (gen0 hd) := by
  refine mapsLong_of_smul_perm (g := gen0 hd) (σ := swap12) (c := fun _ => 1)
    (fun _ => Or.inl rfl) fun i => ?_
  fin_cases i
  · change gen0 hd (e 0) = 1 • e (swap12 0)
    rw [gen0_e0, show swap12 0 = 0 from by decide, one_smul]
  · change gen0 hd (e 1) = 1 • e (swap12 1)
    rw [gen0_e1, show swap12 1 = 2 from by decide, one_smul]
  · change gen0 hd (e 2) = 1 • e (swap12 2)
    rw [gen0_e2, show swap12 2 = 1 from by decide, one_smul]
  · change gen0 hd (e 3) = 1 • e (swap12 3)
    rw [gen0_e3, show swap12 3 = 3 from by decide, one_smul]

private lemma mapsLong_gen1 (hd : GGCZDual e φ) : MapsLong e (gen1 hd) := by
  refine mapsLong_of_smul_perm (g := gen1 hd) (σ := swap23) (c := fun _ => 1)
    (fun _ => Or.inl rfl) fun i => ?_
  fin_cases i
  · change gen1 hd (e 0) = 1 • e (swap23 0)
    rw [gen1_e0, show swap23 0 = 0 from by decide, one_smul]
  · change gen1 hd (e 1) = 1 • e (swap23 1)
    rw [gen1_e1, show swap23 1 = 1 from by decide, one_smul]
  · change gen1 hd (e 2) = 1 • e (swap23 2)
    rw [gen1_e2, show swap23 2 = 3 from by decide, one_smul]
  · change gen1 hd (e 3) = 1 • e (swap23 3)
    rw [gen1_e3, show swap23 3 = 2 from by decide, one_smul]

private lemma mapsLong_gen2 (hd : GGCZDual e φ) : MapsLong e (gen2 hd) := by
  refine mapsLong_of_smul_perm (g := gen2 hd) (σ := Equiv.refl (Fin 4))
    (c := fun i => if i = 3 then -1 else 1) (fun i => ?_) fun i => ?_
  · fin_cases i <;> simp
  · fin_cases i
    · change gen2 hd (e 0) = (if (0 : Fin 4) = 3 then -1 else 1) • e 0
      rw [gen2_e0]; simp
    · change gen2 hd (e 1) = (if (1 : Fin 4) = 3 then -1 else 1) • e 1
      rw [gen2_e1]; simp
    · change gen2 hd (e 2) = (if (2 : Fin 4) = 3 then -1 else 1) • e 2
      rw [gen2_e2]; simp
    · change gen2 hd (e 3) = (if (3 : Fin 4) = 3 then -1 else 1) • e 3
      rw [gen2_e3]; simp

private lemma gen0_mul_self (hd : GGCZDual e φ) : gen0 hd * gen0 hd = 1 := by
  ext v
  rw [LinearEquiv.mul_apply]
  simp only [gen0, ggCZRDrefl]
  exact Module.involutive_reflection _ v

private lemma gen1_mul_self (hd : GGCZDual e φ) : gen1 hd * gen1 hd = 1 := by
  ext v
  rw [LinearEquiv.mul_apply]
  simp only [gen1, ggCZRDrefl]
  exact Module.involutive_reflection _ v

private lemma gen2_mul_self (hd : GGCZDual e φ) : gen2 hd * gen2 hd = 1 := by
  ext v
  rw [LinearEquiv.mul_apply]
  simp only [gen2, ggCZSrefl, ggCZRefl]
  exact Module.involutive_reflection _ v

private lemma gen3_mul_self (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 * gen3 hd hp2 = 1 := by
  ext v
  rw [LinearEquiv.mul_apply]
  simp only [gen3, ggCZRefl]
  exact Module.involutive_reflection _ v

private def ggCZGood (φ : Fin 4 → Module.Dual (ZMod p) V) (e : Fin 4 → V) :
    Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {g | IsomB φ g ∧ IsomB φ g⁻¹ ∧ MapsLong e g ∧ MapsLong e g⁻¹}
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v w; rfl
    · intro v w; rfl
    · intro b hb; exact hb
    · intro b hb; exact hb
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hg1.mul hh1
    · rw [mul_inv_rev]
      exact hh2.mul hg2
    · intro b hb; exact hg3 (h b) (hh3 b hb)
    · rw [mul_inv_rev]
      intro b hb
      exact hh4 (g⁻¹ b) (hg4 b hb)
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨hg2, hg1, hg4, hg3⟩

private lemma ggCZWF4_le_good (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    ggCZWF4 p e φ ≤ ggCZGood φ e := by
  rw [ggCZWF4, Subgroup.closure_le]
  rintro r ⟨i, hi⟩
  have hrt : ∀ (g g' : V ≃ₗ[ZMod p] V), g = g' → g ∈ ggCZGood φ e → g' ∈ ggCZGood φ e :=
    fun g g' h => h ▸ id
  fin_cases i
  · have hr : r = gen0 hd := by
      refine LinearEquiv.ext fun v => ?_
      rw [gen0_apply]
      exact hi v
    subst hr
    refine ⟨gen0_isom hd, ?_, mapsLong_gen0 hd, ?_⟩
    · rw [inv_eq_of_mul_eq_one_right (gen0_mul_self hd)]
      exact gen0_isom hd
    · rw [inv_eq_of_mul_eq_one_right (gen0_mul_self hd)]
      exact mapsLong_gen0 hd
  · have hr : r = gen1 hd := by
      refine LinearEquiv.ext fun v => ?_
      rw [gen1_apply]
      exact hi v
    subst hr
    refine ⟨gen1_isom hd, ?_, mapsLong_gen1 hd, ?_⟩
    · rw [inv_eq_of_mul_eq_one_right (gen1_mul_self hd)]
      exact gen1_isom hd
    · rw [inv_eq_of_mul_eq_one_right (gen1_mul_self hd)]
      exact mapsLong_gen1 hd
  · have hr : r = gen2 hd := by
      refine LinearEquiv.ext fun v => ?_
      rw [gen2_apply]
      exact hi v
    subst hr
    refine ⟨gen2_isom hd, ?_, mapsLong_gen2 hd, ?_⟩
    · rw [inv_eq_of_mul_eq_one_right (gen2_mul_self hd)]
      exact gen2_isom hd
    · rw [inv_eq_of_mul_eq_one_right (gen2_mul_self hd)]
      exact mapsLong_gen2 hd
  · have hr : r = gen3 hd hp2 := by
      refine LinearEquiv.ext fun v => ?_
      rw [gen3_apply]
      exact hi v
    subst hr
    refine ⟨gen3_isom hd hp2, ?_, mapsLong_gen3 hd hp2, ?_⟩
    · rw [inv_eq_of_mul_eq_one_right (gen3_mul_self hd hp2)]
      exact gen3_isom hd hp2
    · rw [inv_eq_of_mul_eq_one_right (gen3_mul_self hd hp2)]
      exact mapsLong_gen3 hd hp2

private noncomputable def wS2 (hd : GGCZDual e φ) : V ≃ₗ[ZMod p] V :=
  gen1 hd * gen2 hd * (gen1 hd)⁻¹

private noncomputable def wS1 (hd : GGCZDual e φ) : V ≃ₗ[ZMod p] V :=
  gen0 hd * wS2 hd * (gen0 hd)⁻¹

private lemma wS2_mem (hd : GGCZDual e φ) : wS2 hd ∈ ggCZWF4 p e φ :=
  (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen2_mem hd))
    ((ggCZWF4 p e φ).inv_mem (gen1_mem hd))

private lemma wS1_mem (hd : GGCZDual e φ) : wS1 hd ∈ ggCZWF4 p e φ :=
  (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem (gen0_mem hd) (wS2_mem hd))
    ((ggCZWF4 p e φ).inv_mem (gen0_mem hd))

private lemma wS2_eq (hd : GGCZDual e φ) : wS2 hd = ggCZSrefl hd 2 := by
  refine conj_eq_refl (g := gen1 hd) (b := e 3) (b' := e 2) (c := 2) (c' := 2) (q := 1)
    (gen1_isom hd) (by norm_num) ?_ ?_ ?_
  · rw [gen1_e3, one_smul]
  · intro v
    rw [gen2_apply, ← B_S hd]
  · intro v
    rw [ggCZSrefl_apply, ← B_S hd]

private lemma wS2_apply (hd : GGCZDual e φ) (v : V) :
    wS2 hd v = v - (2 * φ 2 v) • e 2 := by
  rw [wS2_eq hd, ggCZSrefl_apply]

private lemma wS1_eq (hd : GGCZDual e φ) : wS1 hd = ggCZSrefl hd 1 := by
  refine conj_eq_refl (g := gen0 hd) (b := e 2) (b' := e 1) (c := 2) (c' := 2) (q := 1)
    (gen0_isom hd) (by norm_num) ?_ ?_ ?_
  · rw [gen0_e2, one_smul]
  · intro v
    rw [wS2_apply hd, ← B_S hd]
  · intro v
    rw [ggCZSrefl_apply, ← B_S hd]

private lemma wS1_apply (hd : GGCZDual e φ) (v : V) :
    wS1 hd v = v - (2 * φ 1 v) • e 1 := by
  rw [wS1_eq hd, ggCZSrefl_apply]

private lemma IsomB_of_mem (hd : GGCZDual e φ) (hp2 : p ≠ 2) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWF4 p e φ) : IsomB φ g :=
  (ggCZWF4_le_good hd hp2 hg).1

private lemma MapsLong_of_mem (hd : GGCZDual e φ) (hp2 : p ≠ 2) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWF4 p e φ) : MapsLong e g :=
  (ggCZWF4_le_good hd hp2 hg).2.2.1

private lemma ggCZRDrefl_form (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (v : V) :
    ggCZRDrefl hd hij hε v = v - (1 * ggCZForm φ v (e i - ε • e j)) • (e i - ε • e j) := by
  rw [ggCZRDrefl_apply, B_RD hd, one_mul]

private lemma gen0_form (hd : GGCZDual e φ) (v : V) :
    gen0 hd v = v - (1 * ggCZForm φ v (e 1 - (1 : ZMod p) • e 2)) •
      (e 1 - (1 : ZMod p) • e 2) := by
  rw [gen0_apply, B_RD hd]
  simp

private lemma ggCZRDrefl_comm (hd : GGCZDual e φ) {i j : Fin 4} (hij : i ≠ j) (hji : j ≠ i)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ggCZRDrefl hd hji hε = ggCZRDrefl hd hij hε := by
  refine LinearEquiv.ext fun v => ?_
  rw [ggCZRDrefl_apply, ggCZRDrefl_apply]
  have h1 : φ j v - ε * φ i v = -ε * (φ i v - ε * φ j v) := by
    rcases hε with rfl | rfl <;> ring
  have h2 : e j - ε • e i = (-ε) • (e i - ε • e j) := by
    rcases hε with rfl | rfl
    · simp
    · simp; abel
  rw [h1, h2, smul_smul]
  rcases hε with rfl | rfl <;> simp

private lemma gen0_add_e2_e3 (hd : GGCZDual e φ) : gen0 hd (e 2 + e 3) = e 1 + e 3 := by
  rw [map_add, gen0_e2, gen0_e3]

private lemma gen0_sub_e2_e3 (hd : GGCZDual e φ) : gen0 hd (e 2 - e 3) = e 1 - e 3 := by
  rw [map_sub, gen0_e2, gen0_e3]

private lemma gen1_sub_e1_e3 (hd : GGCZDual e φ) : gen1 hd (e 1 - e 3) = e 1 - e 2 := by
  rw [map_sub, gen1_e1, gen1_e3]

private lemma gen2_add_e1_e3 (hd : GGCZDual e φ) : gen2 hd (e 1 + e 3) = e 1 - e 3 := by
  rw [map_add, gen2_e1, gen2_e3]
  abel

private lemma gen2_add_e2_e3 (hd : GGCZDual e φ) : gen2 hd (e 2 + e 3) = e 2 - e 3 := by
  rw [map_add, gen2_e2, gen2_e3]
  abel

private lemma gen2_add_e0_e3 (hd : GGCZDual e φ) : gen2 hd (e 0 + e 3) = e 0 - e 3 := by
  rw [map_add, gen2_e0, gen2_e3]
  abel

private lemma wS2_add_e1_e2 (hd : GGCZDual e φ) :
    wS2 hd (e 1 + e 2) = e 1 - e 2 := by
  rw [wS2_apply hd, map_add]
  simp only [phi_e hd]
  norm_num
  module

private lemma wS2_add_e0_e2 (hd : GGCZDual e φ) :
    wS2 hd (e 0 + e 2) = e 0 - e 2 := by
  rw [wS2_apply hd, map_add]
  simp only [phi_e hd]
  norm_num
  module

private lemma wS1_add_e0_e1 (hd : GGCZDual e φ) :
    wS1 hd (e 0 + e 1) = e 0 - e 1 := by
  rw [wS1_apply hd, map_add]
  simp only [phi_e hd]
  norm_num
  module

private lemma can_img_01p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (gen1 hd * gen2 hd * gen0 hd * gen3 hd hp2) (e 0 - e 1) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [gen3_img_01_m hd]
  rw [gen0_add_e2_e3 hd]
  rw [gen2_add_e1_e3 hd]
  rw [gen1_sub_e1_e3 hd]
  module

private lemma can_img_01m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (gen1 hd * gen2 hd * gen0 hd * gen3 hd hp2 * wS1 hd) (e 0 + e 1) = e 1 - (1 : ZMod p) • e 2 :=
      by
  simp only [LinearEquiv.mul_apply]
  rw [wS1_add_e0_e1 hd]
  rw [gen3_img_01_m hd]
  rw [gen0_add_e2_e3 hd]
  rw [gen2_add_e1_e3 hd]
  rw [gen1_sub_e1_e3 hd]
  module

private lemma can_img_02p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (gen1 hd * gen2 hd * gen3 hd hp2) (e 0 - e 2) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [gen3_img_02_m hd]
  rw [gen2_add_e1_e3 hd]
  rw [gen1_sub_e1_e3 hd]
  module

private lemma can_img_02m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (gen1 hd * gen2 hd * gen3 hd hp2 * wS2 hd) (e 0 + e 2) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [wS2_add_e0_e2 hd]
  rw [gen3_img_02_m hd]
  rw [gen2_add_e1_e3 hd]
  rw [gen1_sub_e1_e3 hd]
  module

private lemma can_img_03p (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (wS2 hd * gen3 hd hp2) (e 0 - e 3) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [gen3_img_03_m hd]
  rw [wS2_add_e1_e2 hd]
  module

private lemma can_img_03m (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    (wS2 hd * gen3 hd hp2 * gen2 hd) (e 0 + e 3) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [gen2_add_e0_e3 hd]
  rw [gen3_img_03_m hd]
  rw [wS2_add_e1_e2 hd]
  module

private lemma can_img_12m (hd : GGCZDual e φ) (_hp2 : p ≠ 2) :
    (wS2 hd) (e 1 + e 2) = e 1 - (1 : ZMod p) • e 2 := by
  rw [wS2_add_e1_e2 hd]
  module

private lemma can_img_13p (hd : GGCZDual e φ) (_hp2 : p ≠ 2) :
    (gen1 hd) (e 1 - e 3) = e 1 - (1 : ZMod p) • e 2 := by
  rw [gen1_sub_e1_e3 hd]
  module

private lemma can_img_13m (hd : GGCZDual e φ) (_hp2 : p ≠ 2) :
    (gen1 hd * gen2 hd) (e 1 + e 3) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [gen2_add_e1_e3 hd]
  rw [gen1_sub_e1_e3 hd]
  module

private lemma can_img_23p (hd : GGCZDual e φ) (_hp2 : p ≠ 2) :
    (gen1 hd * gen0 hd) (e 2 - e 3) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [gen0_sub_e2_e3 hd]
  rw [gen1_sub_e1_e3 hd]
  module

private lemma can_img_23m (hd : GGCZDual e φ) (_hp2 : p ≠ 2) :
    (gen1 hd * gen0 hd * gen2 hd) (e 2 + e 3) = e 1 - (1 : ZMod p) • e 2 := by
  simp only [LinearEquiv.mul_apply]
  rw [gen2_add_e2_e3 hd]
  rw [gen0_sub_e2_e3 hd]
  rw [gen1_sub_e1_e3 hd]
  module

private lemma canon_RD_lt_of_img (hd : GGCZDual e φ) (hp2 : p ≠ 2) {i j : Fin 4}
    (hij : i < j) {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWF4 p e φ)
    (himg : g (e i - ε • e j) = (1 : ZMod p) • (e 1 - (1 : ZMod p) • e 2)) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt hij) hε * g⁻¹ = gen0 hd := by
  exact ⟨g, hg, conj_eq_refl (IsomB_of_mem hd hp2 hg) (b := e i - ε • e j)
    (b' := e 1 - (1 : ZMod p) • e 2) (c := 1) (c' := 1) (q := 1) (by norm_num) himg
    (ggCZRDrefl_form hd (ne_of_lt hij) hε) (gen0_form hd)⟩

private lemma canon_RD_lt_01 (hd : GGCZDual e φ) (hp2 : p ≠ 2) (h01 : (0 : Fin 4) < 1)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt h01) hε * g⁻¹ = gen0 hd := by
  rcases hε with rfl | rfl
  · have hg : gen1 hd * gen2 hd * gen0 hd * gen3 hd hp2 ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem
        ((ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen2_mem hd)) (gen0_mem hd)) (gen3_mem hd hp2)
    exact canon_RD_lt_of_img hd hp2 h01 (Or.inl rfl) hg (by simpa using can_img_01p hd hp2)
  · have hg : gen1 hd * gen2 hd * gen0 hd * gen3 hd hp2 * wS1 hd ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem
        ((ggCZWF4 p e φ).mul_mem
          ((ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen2_mem hd)) (gen0_mem hd))
        (gen3_mem hd hp2)) (wS1_mem hd)
    exact canon_RD_lt_of_img hd hp2 h01 (Or.inr rfl) hg (by simpa using can_img_01m hd hp2)

private lemma canon_RD_lt_02 (hd : GGCZDual e φ) (hp2 : p ≠ 2) (h02 : (0 : Fin 4) < 2)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt h02) hε * g⁻¹ = gen0 hd := by
  rcases hε with rfl | rfl
  · have hg : gen1 hd * gen2 hd * gen3 hd hp2 ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen2_mem hd))
        (gen3_mem hd hp2)
    exact canon_RD_lt_of_img hd hp2 h02 (Or.inl rfl) hg (by simpa using can_img_02p hd hp2)
  · have hg : gen1 hd * gen2 hd * gen3 hd hp2 * wS2 hd ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem
        ((ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen2_mem hd)) (gen3_mem hd hp2)) (wS2_mem hd)
    exact canon_RD_lt_of_img hd hp2 h02 (Or.inr rfl) hg (by simpa using can_img_02m hd hp2)

private lemma canon_RD_lt_03 (hd : GGCZDual e φ) (hp2 : p ≠ 2) (h03 : (0 : Fin 4) < 3)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt h03) hε * g⁻¹ = gen0 hd := by
  rcases hε with rfl | rfl
  · have hg : wS2 hd * gen3 hd hp2 ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem (wS2_mem hd) (gen3_mem hd hp2)
    exact canon_RD_lt_of_img hd hp2 h03 (Or.inl rfl) hg (by simpa using can_img_03p hd hp2)
  · have hg : wS2 hd * gen3 hd hp2 * gen2 hd ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem (wS2_mem hd) (gen3_mem hd hp2))
        (gen2_mem hd)
    exact canon_RD_lt_of_img hd hp2 h03 (Or.inr rfl) hg (by simpa using can_img_03m hd hp2)

private lemma canon_RD_lt_12 (hd : GGCZDual e φ) (hp2 : p ≠ 2) (h12 : (1 : Fin 4) < 2)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt h12) hε * g⁻¹ = gen0 hd := by
  rcases hε with rfl | rfl
  · have hg : (1 : V ≃ₗ[ZMod p] V) ∈ ggCZWF4 p e φ := (ggCZWF4 p e φ).one_mem
    exact canon_RD_lt_of_img hd hp2 h12 (Or.inl rfl) hg (by simp)
  · have hg : wS2 hd ∈ ggCZWF4 p e φ := wS2_mem hd
    exact canon_RD_lt_of_img hd hp2 h12 (Or.inr rfl) hg (by simpa using can_img_12m hd hp2)

private lemma canon_RD_lt_13 (hd : GGCZDual e φ) (hp2 : p ≠ 2) (h13 : (1 : Fin 4) < 3)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt h13) hε * g⁻¹ = gen0 hd := by
  rcases hε with rfl | rfl
  · have hg : gen1 hd ∈ ggCZWF4 p e φ := gen1_mem hd
    exact canon_RD_lt_of_img hd hp2 h13 (Or.inl rfl) hg (by simpa using can_img_13p hd hp2)
  · have hg : gen1 hd * gen2 hd ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen2_mem hd)
    exact canon_RD_lt_of_img hd hp2 h13 (Or.inr rfl) hg (by simpa using can_img_13m hd hp2)

private lemma canon_RD_lt_23 (hd : GGCZDual e φ) (hp2 : p ≠ 2) (h23 : (2 : Fin 4) < 3)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt h23) hε * g⁻¹ = gen0 hd := by
  rcases hε with rfl | rfl
  · have hg : gen1 hd * gen0 hd ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen0_mem hd)
    exact canon_RD_lt_of_img hd hp2 h23 (Or.inl rfl) hg (by simpa using can_img_23p hd hp2)
  · have hg : gen1 hd * gen0 hd * gen2 hd ∈ ggCZWF4 p e φ :=
      (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem (gen1_mem hd) (gen0_mem hd))
        (gen2_mem hd)
    exact canon_RD_lt_of_img hd hp2 h23 (Or.inr rfl) hg (by simpa using can_img_23m hd hp2)

private lemma canon_RD_lt (hd : GGCZDual e φ) (hp2 : p ≠ 2) {i j : Fin 4} (hij : i < j)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd (ne_of_lt hij) hε * g⁻¹ = gen0 hd := by
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact canon_RD_lt_01 hd hp2 hij hε
  · exact canon_RD_lt_02 hd hp2 hij hε
  · exact canon_RD_lt_03 hd hp2 hij hε
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact canon_RD_lt_12 hd hp2 hij hε
  · exact canon_RD_lt_13 hd hp2 hij hε
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact canon_RD_lt_23 hd hp2 hij hε
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

private lemma canon_RD (hd : GGCZDual e φ) (hp2 : p ≠ 2) {i j : Fin 4} (hij : i ≠ j)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZRDrefl hd hij hε * g⁻¹ = gen0 hd := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact canon_RD_lt hd hp2 h hε
  · rw [← ggCZRDrefl_comm hd hij (ne_of_lt h) hε]
    exact canon_RD_lt hd hp2 h hε

private lemma mem_RD_refl (hd : GGCZDual e φ) (hp2 : p ≠ 2) {i j : Fin 4} (hij : i ≠ j)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) : ggCZRDrefl hd hij hε ∈ ggCZWF4 p e φ := by
  obtain ⟨g, hg, hconj⟩ := canon_RD hd hp2 hij hε
  have heq : ggCZRDrefl hd hij hε = g⁻¹ * gen0 hd * g := by
    rw [← hconj]; group
  rw [heq]
  exact (ggCZWF4 p e φ).mul_mem
    ((ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).inv_mem hg) (gen0_mem hd)) hg

private lemma ggCZSrefl_form (hd : GGCZDual e φ) (i : Fin 4) (v : V) :
    ggCZSrefl hd i v = v - (2 * ggCZForm φ v (e i)) • e i := by
  rw [ggCZSrefl_apply, B_S hd]

private lemma ggCZRDrefl_e0_e3_apply (hd : GGCZDual e φ) :
    ggCZRDrefl hd (i := 0) (j := 3) (by decide) (ε := 1) (Or.inl rfl) (e 3) = e 0 := by
  rw [ggCZRDrefl_apply]
  simp only [phi_e hd]
  norm_num

private lemma ggCZRDrefl_e1_e0_apply (hd : GGCZDual e φ) :
    ggCZRDrefl hd (i := 1) (j := 0) (by decide) (ε := 1) (Or.inl rfl) (e 0) = e 1 := by
  rw [ggCZRDrefl_apply]
  simp only [phi_e hd]
  norm_num

private lemma ggCZRDrefl_e1_e3_apply (hd : GGCZDual e φ) :
    ggCZRDrefl hd (i := 1) (j := 3) (by decide) (ε := 1) (Or.inl rfl) (e 3) = e 1 := by
  rw [ggCZRDrefl_apply]
  simp only [phi_e hd]
  norm_num

private lemma mem_S_refl (hd : GGCZDual e φ) (hp2 : p ≠ 2) (i : Fin 4) :
    ggCZSrefl hd i ∈ ggCZWF4 p e φ := by
  fin_cases i
  · change ggCZSrefl hd 0 ∈ ggCZWF4 p e φ
    have hw : ggCZRDrefl hd (i := 0) (j := 3) (by decide) (ε := 1) (Or.inl rfl) ∈
        ggCZWF4 p e φ := mem_RD_refl hd hp2 (by decide) (Or.inl rfl)
    have hconj : ggCZRDrefl hd (i := 0) (j := 3) (by decide) (ε := 1) (Or.inl rfl) *
        ggCZSrefl hd 3 * (ggCZRDrefl hd (i := 0) (j := 3) (by decide) (ε := 1) (Or.inl rfl))⁻¹
        = ggCZSrefl hd 0 := by
      refine conj_eq_refl (IsomB_of_mem hd hp2 hw) (b := e 3) (b' := e 0) (c := 2) (c' := 2)
        (q := 1) (by norm_num) ?_ (ggCZSrefl_form hd 3) (ggCZSrefl_form hd 0)
      rw [ggCZRDrefl_e0_e3_apply]; simp
    rw [← hconj]
    exact (ggCZWF4 p e φ).mul_mem
      ((ggCZWF4 p e φ).mul_mem hw (gen2_mem hd)) ((ggCZWF4 p e φ).inv_mem hw)
  · change ggCZSrefl hd 1 ∈ ggCZWF4 p e φ
    rw [← wS1_eq hd]
    exact wS1_mem hd
  · change ggCZSrefl hd 2 ∈ ggCZWF4 p e φ
    rw [← wS2_eq hd]
    exact wS2_mem hd
  · change ggCZSrefl hd 3 ∈ ggCZWF4 p e φ
    exact gen2_mem hd

private lemma canon_S (hd : GGCZDual e φ) (hp2 : p ≠ 2) (i : Fin 4) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZSrefl hd i * g⁻¹ = ggCZSrefl hd 1 := by
  fin_cases i
  · refine ⟨ggCZRDrefl hd (i := 1) (j := 0) (by decide) (ε := 1) (Or.inl rfl),
      mem_RD_refl hd hp2 (by decide) (Or.inl rfl), ?_⟩
    have himg : ggCZRDrefl hd (i := 1) (j := 0) (by decide) (ε := 1) (Or.inl rfl) (e 0) =
        (1 : ZMod p) • e 1 := by
      rw [ggCZRDrefl_e1_e0_apply]; simp
    exact conj_eq_refl (IsomB_of_mem hd hp2 (mem_RD_refl hd hp2 (by decide) (Or.inl rfl)))
      (b := e 0) (b' := e 1) (c := 2) (c' := 2) (q := 1) (by norm_num) himg
      (ggCZSrefl_form hd 0) (ggCZSrefl_form hd 1)
  · refine ⟨1, (ggCZWF4 p e φ).one_mem, ?_⟩
    have himg : (1 : V ≃ₗ[ZMod p] V) (e 1) = (1 : ZMod p) • e 1 := by simp
    exact conj_eq_refl (fun v w => rfl) (b := e 1) (b' := e 1) (c := 2) (c' := 2)
      (q := 1) (by norm_num) himg (ggCZSrefl_form hd 1) (ggCZSrefl_form hd 1)
  · refine ⟨gen0 hd, gen0_mem hd, ?_⟩
    have himg : gen0 hd (e 2) = (1 : ZMod p) • e 1 := by
      rw [gen0_e2]; simp
    exact conj_eq_refl (IsomB_of_mem hd hp2 (gen0_mem hd)) (b := e 2) (b' := e 1) (c := 2)
      (c' := 2) (q := 1) (by norm_num) himg (ggCZSrefl_form hd 2)
      (ggCZSrefl_form hd 1)
  · refine ⟨ggCZRDrefl hd (i := 1) (j := 3) (by decide) (ε := 1) (Or.inl rfl),
      mem_RD_refl hd hp2 (by decide) (Or.inl rfl), ?_⟩
    have himg : ggCZRDrefl hd (i := 1) (j := 3) (by decide) (ε := 1) (Or.inl rfl) (e 3) =
        (1 : ZMod p) • e 1 := by
      rw [ggCZRDrefl_e1_e3_apply]; simp
    exact conj_eq_refl (IsomB_of_mem hd hp2 (mem_RD_refl hd hp2 (by decide) (Or.inl rfl)))
      (b := e 3) (b' := e 1) (c := 2) (c' := 2) (q := 1) (by norm_num) himg
      (ggCZSrefl_form hd 3) (ggCZSrefl_form hd 1)

private lemma phi_ggCZHvec (hd : GGCZDual e φ) (k : Fin 4) (x : Fin 4 → ZMod p) :
    φ k (ggCZHvec e x) = x k := by
  rw [ggCZHvec]
  simp only [map_sum, map_smul, phi_e hd, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ k) h

private lemma ggCZHvec_sub_two_smul (x : Fin 4 → ZMod p) (a : Fin 4) :
    ggCZHvec e x - (2 * x a) • e a = ggCZHvec e (fun l => if l = a then -x l else x l) := by
  fin_cases a <;> simp [ggCZHvec, Fin.sum_univ_four] <;> module

private lemma ggCZSrefl_ggCZHvec (hd : GGCZDual e φ) (k : Fin 4) (x : Fin 4 → ZMod p) :
    ggCZSrefl hd k (ggCZHvec e x) = ggCZHvec e (fun l => if l = k then -x l else x l) := by
  rw [ggCZSrefl_apply, phi_ggCZHvec hd]
  exact ggCZHvec_sub_two_smul x k

private noncomputable def signFlipList (hd : GGCZDual e φ) : List (Fin 4) → V ≃ₗ[ZMod p] V
  | [] => 1
  | a :: t => ggCZSrefl hd a * signFlipList hd t

private lemma signFlipList_mem (hd : GGCZDual e φ) (hp2 : p ≠ 2) {w : Fin 4 → ZMod p}
    (l : List (Fin 4)) (h : ∀ k ∈ l, w k = -1) :
    signFlipList hd l ∈ ggCZWF4 p e φ := by
  induction l with
  | nil => exact (ggCZWF4 p e φ).one_mem
  | cons a t ih =>
    rw [signFlipList]
    exact (ggCZWF4 p e φ).mul_mem (mem_S_refl hd hp2 a)
      (ih fun k hk => h k (List.mem_cons_of_mem a hk))

private lemma signFlipList_apply (hd : GGCZDual e φ) (hp2 : p ≠ 2) (w : Fin 4 → ZMod p) :
    ∀ (l : List (Fin 4)), l.Nodup → (∀ k ∈ l, w k = -1) →
      signFlipList hd l (ggCZHvec e w) = ggCZHvec e (fun j => if j ∈ l then 1 else w j)
  | [], _, _ => by simp [signFlipList]
  | a :: t, hnd, h => by
      rw [signFlipList]
      obtain ⟨hat, hnd'⟩ := List.nodup_cons.mp hnd
      have ht : ∀ k ∈ t, w k = -1 := fun k hk => h k (List.mem_cons_of_mem a hk)
      have ha : w a = -1 := h a List.mem_cons_self
      rw [LinearEquiv.mul_apply, signFlipList_apply hd hp2 w t hnd' ht, ggCZSrefl_ggCZHvec hd a]
      congr 1
      funext j
      by_cases hj : j = a
      · subst hj; simp [ha, hat]
      · by_cases hjt : j ∈ t
        · simp [hj, hjt, List.mem_cons]
        · simp [hj, hjt, List.mem_cons]

private lemma two_smul_injective (hp2 : p ≠ 2) : Function.Injective (fun x : V => (2 : ZMod p) •
  x) := by
  intro x y h
  have h' : (2 : ZMod p) • x = (2 : ZMod p) • y := h
  have h2 : (2 : ZMod p) • (x - y) = 0 := by
    rw [smul_sub, h', sub_self]
  have h3 : x - y = 0 := by
    rcases smul_eq_zero.mp h2 with h' | h'
    · exact absurd h' (zmod_two_ne_zero hp2)
    · exact h'
  exact sub_eq_zero.mp h3

private lemma gen3_ggCZHvec_one (hd : GGCZDual e φ) (hp2 : p ≠ 2) :
    gen3 hd hp2 (ggCZHvec e (fun _ => (1 : ZMod p))) = (2 : ZMod p) • e 0 := by
  have h : ggCZHvec e (fun _ : Fin 4 => (1 : ZMod p)) = e 0 + e 1 + e 2 + e 3 := by
    simp [ggCZHvec, Fin.sum_univ_four]
  rw [h]
  have h2 : (2 : ZMod p) • gen3 hd hp2 (e 0 + e 1 + e 2 + e 3) =
      (2 : ZMod p) • ((2 : ZMod p) • e 0) := by
    rw [map_add, map_add, map_add, smul_add, smul_add, smul_add, gen3_two_e0 hd hp2,
      gen3_two_e1 hd hp2, gen3_two_e2 hd hp2, gen3_two_e3 hd hp2]
    simp only [ggCZR]
    module
  exact two_smul_injective (p := p) (V := V) hp2 h2

private lemma ggCZHrefl_form (hd : GGCZDual e φ) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) (hp2 : p ≠ 2) (v : V) :
    ggCZHrefl hd hw hp2 v =
      v - ((2 : ZMod p)⁻¹ * ggCZForm φ v (ggCZHvec e w)) • ggCZHvec e w := by
  rw [ggCZHrefl_apply, B_H hd]

private lemma canon_H (hd : GGCZDual e φ) (hp2 : p ≠ 2) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) :
    ∃ g ∈ ggCZWF4 p e φ, g * ggCZHrefl hd hw hp2 * g⁻¹ = ggCZSrefl hd 1 := by
  set T : Finset (Fin 4) := Finset.univ.filter (fun k => w k = -1) with hT
  have hTneg : ∀ k ∈ T, w k = -1 := by
    intro k hk
    rw [hT] at hk
    exact (Finset.mem_filter.mp hk).2
  have hTpos : ∀ k, k ∉ T → w k = 1 := by
    intro k hk
    rcases hw k with h | h
    · exact h
    · exact absurd (by rw [hT]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩) hk
  have hTneg' : ∀ k ∈ (List.finRange 4).filter (fun k => w k = -1), w k = -1 :=
    fun k hk => by simpa using (List.mem_filter.mp hk).2
  have hσmem : signFlipList hd ((List.finRange 4).filter (fun k => w k = -1)) ∈
      ggCZWF4 p e φ := signFlipList_mem hd hp2 _ hTneg'
  have hσact : signFlipList hd ((List.finRange 4).filter (fun k => w k = -1)) (ggCZHvec e w) =
      ggCZHvec e (fun _ => (1 : ZMod p)) := by
    rw [signFlipList_apply hd hp2 w _ (List.Nodup.filter _ (List.nodup_finRange 4)) hTneg']
    congr 1
    funext j
    by_cases hj : j ∈ (List.finRange 4).filter (fun k => w k = -1)
    · simp [hj]
    · have h1 : w j ≠ -1 := by
        intro h
        exact hj (List.mem_filter.mpr ⟨by simp, by simpa using h⟩)
      rcases hw j with h | h
      · simp [hj, h]
      · exact absurd h h1
  have hw1 : ggCZRDrefl hd (i := 1) (j := 0) (by decide) (ε := 1) (Or.inl rfl) ∈
      ggCZWF4 p e φ := mem_RD_refl hd hp2 (by decide) (Or.inl rfl)
  refine ⟨ggCZRDrefl hd (i := 1) (j := 0) (by decide) (ε := 1) (Or.inl rfl) *
      gen3 hd hp2 * signFlipList hd ((List.finRange 4).filter (fun k => w k = -1)), ?_, ?_⟩
  · exact (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).mul_mem hw1 (gen3_mem hd hp2)) hσmem
  · have himg : (ggCZRDrefl hd (i := 1) (j := 0) (by decide) (ε := 1) (Or.inl rfl) *
        gen3 hd hp2 * signFlipList hd ((List.finRange 4).filter (fun k => w k = -1))) (ggCZHvec e
          w) = (2 : ZMod p) • e 1 := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hσact, gen3_ggCZHvec_one hd hp2,
        map_smul, ggCZRDrefl_e1_e0_apply]
    refine conj_eq_refl (IsomB_of_mem hd hp2 ((ggCZWF4 p e φ).mul_mem
      ((ggCZWF4 p e φ).mul_mem hw1 (gen3_mem hd hp2)) hσmem)) (b := ggCZHvec e w) (b' := e 1)
      (c := (2 : ZMod p)⁻¹) (c' := 2) (q := 2) ?_ himg
      (ggCZHrefl_form hd hw hp2) (ggCZSrefl_form hd 1)
    rw [inv_two_mul_two hp2]
    norm_num

private lemma mem_H_refl (hd : GGCZDual e φ) (hp2 : p ≠ 2) {w : Fin 4 → ZMod p}
    (hw : ∀ k, w k = 1 ∨ w k = -1) : ggCZHrefl hd hw hp2 ∈ ggCZWF4 p e φ := by
  obtain ⟨g, hg, hconj⟩ := canon_H hd hp2 hw
  have heq : ggCZHrefl hd hw hp2 = g⁻¹ * ggCZSrefl hd 1 * g := by
    rw [← hconj]; group
  rw [heq]
  exact (ggCZWF4 p e φ).mul_mem
    ((ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).inv_mem hg) (mem_S_refl hd hp2 1)) hg

private lemma conj_via_canon {r r' c : V ≃ₗ[ZMod p] V}
    (h1 : ∃ g ∈ ggCZWF4 p e φ, g * r * g⁻¹ = c)
    (h2 : ∃ g ∈ ggCZWF4 p e φ, g * r' * g⁻¹ = c) :
    ∃ g ∈ ggCZWF4 p e φ, g * r * g⁻¹ = r' := by
  obtain ⟨g1, hg1, hc1⟩ := h1
  obtain ⟨g2, hg2, hc2⟩ := h2
  refine ⟨g2⁻¹ * g1, (ggCZWF4 p e φ).mul_mem ((ggCZWF4 p e φ).inv_mem hg2) hg1, ?_⟩
  calc (g2⁻¹ * g1) * r * (g2⁻¹ * g1)⁻¹ = g2⁻¹ * (g1 * r * g1⁻¹) * g2 := by group
    _ = g2⁻¹ * c * g2 := by rw [hc1]
    _ = r' := by rw [← hc2]; group

end

theorem ggCZ_subset_ggCZWF4 (hp2 : p ≠ 2) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) : ggCZRD e φ ∪ ggCZS e φ ∪ ggCZH e φ ⊆ ggCZWF4 p e φ := by
  rintro r ((hR | hS) | hH)
  · obtain ⟨i, j, hij, ε, hε, hr⟩ := hR
    have heq : r = ggCZRDrefl hd hij hε := by
      refine LinearEquiv.ext fun v => ?_
      rw [ggCZRDrefl_apply]
      exact hr v
    rw [heq]
    exact mem_RD_refl hd hp2 hij hε
  · obtain ⟨i, hr⟩ := hS
    have heq : r = ggCZSrefl hd i := by
      refine LinearEquiv.ext fun v => ?_
      rw [ggCZSrefl_apply]
      exact hr v
    rw [heq]
    exact mem_S_refl hd hp2 i
  · obtain ⟨w, hw, hr⟩ := hH
    have heq : r = ggCZHrefl hd hw hp2 := by
      refine LinearEquiv.ext fun v => ?_
      rw [ggCZHrefl_apply]
      exact hr v
    rw [heq]
    exact mem_H_refl hd hp2 hw

theorem ggCZWF4_refl [Finite V] (hp2 : p ≠ 2) {e : Fin 4 → V}
    {φ : Fin 4 → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWF4 p e φ) (hr : GGLinRefl g) : g ∈ ggCZRD e φ ∪ ggCZS e φ ∪ ggCZH e φ := by
  have hiso : IsomB φ g := IsomB_of_mem hd hp2 hg
  have hlong : MapsLong e g := MapsLong_of_mem hd hp2 hg
  have hC : ∀ v, (∀ k, φ k v = 0) → g v = v := fun v hv => ggCZWF4_fix hg hv
  have hN : ∀ r ∈ ggCZRD e φ, g * r * g⁻¹ ∈ ggCZRD e φ := by
    intro r hrrd
    obtain ⟨i, j, hij, ε, hε, hrv⟩ := hrrd
    have heq : r = ggCZRDrefl hd hij hε := by
      refine LinearEquiv.ext fun v => ?_
      rw [ggCZRDrefl_apply]
      exact hrv v
    have ha : e i - ε • e j ∈ ggCZLong (p := p) e := ggCZLong_sub i j hij ε hε
    have hga : g (e i - ε • e j) ∈ ggCZLong (p := p) e := hlong _ ha
    have hform : ∀ v, (g * ggCZRDrefl hd hij hε * g⁻¹) v =
        v - ggCZForm φ v (g (e i - ε • e j)) • g (e i - ε • e j) := by
      intro v
      rw [conj_form_B_smul hiso (fun v => by rw [ggCZRDrefl_apply, B_RD hd, one_mul]) v,
        one_mul]
    rw [heq]
    exact mem_RD_of_form hd hga hform
  have hcore := ggCZ_core hp2 (by norm_num : 3 ≤ 4) hd hr hC hN
  rcases hcore with h | h | ⟨-, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem ggCZWF4_conj_RD (hp2 : p ≠ 2) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r r' : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZRD e φ) (hr' : r' ∈ ggCZRD e φ) :
    ∃ g ∈ ggCZWF4 p e φ, g * r * g⁻¹ = r' := by
  obtain ⟨i, j, hij, ε, hε, hrv⟩ := hr
  obtain ⟨i', j', hij', ε', hε', hr'v⟩ := hr'
  have heq : r = ggCZRDrefl hd hij hε := by
    refine LinearEquiv.ext fun v => ?_
    rw [ggCZRDrefl_apply]
    exact hrv v
  have heq' : r' = ggCZRDrefl hd hij' hε' := by
    refine LinearEquiv.ext fun v => ?_
    rw [ggCZRDrefl_apply]
    exact hr'v v
  subst heq
  subst heq'
  exact conj_via_canon (canon_RD hd hp2 hij hε) (canon_RD hd hp2 hij' hε')

theorem ggCZWF4_conj_short (hp2 : p ≠ 2) {e : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r r' : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZS e φ ∪ ggCZH e φ)
    (hr' : r' ∈ ggCZS e φ ∪ ggCZH e φ) : ∃ g ∈ ggCZWF4 p e φ, g * r * g⁻¹ = r' := by
  have h1 : ∃ g ∈ ggCZWF4 p e φ, g * r * g⁻¹ = ggCZSrefl hd 1 := by
    rcases hr with hS | hH
    · obtain ⟨i, hrv⟩ := hS
      have heq : r = ggCZSrefl hd i := by
        refine LinearEquiv.ext fun v => ?_
        rw [ggCZSrefl_apply]
        exact hrv v
      rw [heq]
      exact canon_S hd hp2 i
    · obtain ⟨w, hw, hrv⟩ := hH
      have heq : r = ggCZHrefl hd hw hp2 := by
        refine LinearEquiv.ext fun v => ?_
        rw [ggCZHrefl_apply]
        exact hrv v
      rw [heq]
      exact canon_H hd hp2 hw
  have h2 : ∃ g ∈ ggCZWF4 p e φ, g * r' * g⁻¹ = ggCZSrefl hd 1 := by
    rcases hr' with hS | hH
    · obtain ⟨i, hrv⟩ := hS
      have heq : r' = ggCZSrefl hd i := by
        refine LinearEquiv.ext fun v => ?_
        rw [ggCZSrefl_apply]
        exact hrv v
      rw [heq]
      exact canon_S hd hp2 i
    · obtain ⟨w, hw, hrv⟩ := hH
      have heq : r' = ggCZHrefl hd hw hp2 := by
        refine LinearEquiv.ext fun v => ?_
        rw [ggCZHrefl_apply]
        exact hrv v
      rw [heq]
      exact canon_H hd hp2 hw
  exact conj_via_canon h1 h2

end

end CFSG.StandardType

end
