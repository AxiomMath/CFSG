module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SPair
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SArc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem dihedral_eq {a b c c' : D} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (h1 : b * (a * b * a⁻¹) * b⁻¹ * (a * b * a⁻¹)⁻¹ = c)
    (h2 : a * (b * a * b⁻¹) * a⁻¹ * (b * a * b⁻¹)⁻¹ = c') : c' = c := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e1 : c = (b * a) * (b * a) * (b * a) * (b * a) := by
    rw [← h1]
    simp only [mul_inv_rev, ha', hb']
    group
  have e2 : c' = (a * b) * (a * b) * (a * b) * (a * b) := by
    rw [← h2]
    simp only [mul_inv_rev, ha', hb']
    group
  have e3 : a * b = (b * a)⁻¹ := by rw [mul_inv_rev, ha', hb']
  calc c' = ((b * a) * (b * a) * (b * a) * (b * a))⁻¹ := by rw [e2, e3]; group
    _ = c⁻¹ := by rw [← e1]
    _ = c := inv_eq_of_mul_eq_one_right hc

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_nbr_ne [Finite D] (u v : CosetGeom (A ⊔ B) A B) :
    ∃ w, (graph (A ⊔ B) A B).Adj u w ∧ w ≠ v := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Set.ncard_eq_three.mp (h.ncard_nbrs u)
  have ha : (graph (A ⊔ B) A B).Adj u a := by
    have : a ∈ nbrs u := by rw [hset]; simp
    exact this
  have hb : (graph (A ⊔ B) A B).Adj u b := by
    have : b ∈ nbrs u := by rw [hset]; simp
    exact this
  by_cases hva : v = a
  · exact ⟨b, hb, by rw [hva]; exact hab.symm⟩
  · exact ⟨a, ha, fun e => hva e.symm⟩

theorem pair_apply [Finite D] {c α s₀ s₁ s₂ s₃ s₄ α' c' : CosetGeom (A ⊔ B) A B}
    (hP : Pair A B z V s₀ s₁ s₂ s₃ s₄)
    (hc : vtype c = true) (h1 : (graph (A ⊔ B) A B).Adj c α) (h2 : (graph (A ⊔ B) A B).Adj α s₀)
    (h3 : (graph (A ⊔ B) A B).Adj s₀ s₁) (n02 : c ≠ s₀) (n13 : α ≠ s₁)
    (hc' : vtype c' = true) (h1' : (graph (A ⊔ B) A B).Adj c' α')
    (h2' : (graph (A ⊔ B) A B).Adj α' s₄) (h3' : (graph (A ⊔ B) A B).Adj s₄ s₃) (n02' : c' ≠ s₄)
    (n13' : α' ≠ s₃) {x y : D} (hx : x ∈ Zv z c) (hy : y ∈ Zv z c') (ex : x ≠ 1) (ey : y ≠ 1) :
    x * y * x⁻¹ * y⁻¹ ∈ Zv z s₂ ∧ x * y * x⁻¹ * y⁻¹ ≠ 1 := by
  obtain ⟨hx0, hx1⟩ := h.far_label hc h1 h2 h3 n02 n13 hx ex
  obtain ⟨hy0, hy1⟩ := h.far_label hc' h1' h2' h3' n02' n13' hy ey
  exact hP x hx0 hx1 y hy0 hy1

theorem not_fixes_of_comm [Finite D] {w α c m : CosetGeom (A ⊔ B) A B} {a y : D} (ha : a ∈ A ⊔ B)
    (hw : vtype w = true) (hα : (graph (A ⊔ B) A B).Adj w α)
    (hc : (graph (A ⊔ B) A B).Adj α c) (hcw : c ≠ w) (hm : vtype m = true)
    (hwfix : (⟨a, ha⟩ : ↥(A ⊔ B)) • w = w) (hy : y ∈ Zv z c) (ey : y ≠ 1)
    (hcomm : a * y * a⁻¹ * y⁻¹ ∈ Zv z m) (hne : a * y * a⁻¹ * y⁻¹ ≠ 1)
    (hmw : Zv z m ≠ Zv z w) : (⟨a, ha⟩ : ↥(A ⊔ B)) • α ≠ α := by
  intro hαfix
  set g : ↥(A ⊔ B) := ⟨a, ha⟩ with hg
  have hαt : vtype α = false := vtype_eq_false_of_adj hα hw
  have hct : vtype c = true := vtype_eq_true_of_adj hc hαt
  have hgc : (graph (A ⊔ B) A B).Adj α (g • c) := by
    have := (smul_adj g).mpr hc
    rwa [hαfix] at this
  have hgcw : g • c ≠ w := fun e => hcw (smul_left_cancel g (e.trans hwfix.symm))
  have hmem : a * y * a⁻¹ ∈ Zv z (g • c) := by
    rw [Zv_smul h.normalizes_zpowers]
    exact mul_mem_conjSub hy
  have hne1 : a * y * a⁻¹ ≠ 1 := by
    intro e1
    apply ey
    have e2 : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    rw [e2, e1]
    group
  by_cases hcc : g • c = c
  ·
    rw [hcc] at hmem
    have hyy : a * y * a⁻¹ = y := h.eq_of_mem_Zv hct hmem hy hne1 ey
    apply hne
    rw [hyy]
    group
  ·
    have hsq := h.mul_self_eq_one_of_mem_Zv hct hy
    have hprod : (a * y * a⁻¹) * y ∈ Zv z w :=
      h.mul_mem_Zv_third hαt hgc hc hα.symm hcc hgcw hcw hmem hy hne1 ey
    have e3 : a * y * a⁻¹ * y⁻¹ = (a * y * a⁻¹) * y := by
      rw [inv_eq_of_mul_eq_one_right hsq]
    have hmw' : Zv z m = Zv z w := h.Zv_eq_of_mem hm hw hcomm (e3 ▸ hprod) hne
    exact hmw hmw'

theorem false_of_walk [Finite D] (hb : critDist (A ⊔ B) A B V = 5)
    (hP : ∀ s₀ s₁ s₂ s₃ s₄ : CosetGeom (A ⊔ B) A B, Walk4 A B s₀ s₁ s₂ s₃ s₄ →
      Pair A B z V s₀ s₁ s₂ s₃ s₄)
    (q : ℕ → CosetGeom (A ⊔ B) A B)
    (hadj : ∀ i, i < 10 → (graph (A ⊔ B) A B).Adj (q i) (q (i + 1)))
    (hnb : ∀ i, i + 2 ≤ 10 → q i ≠ q (i + 2)) (h0 : vtype (q 0) = true) : False := by
  have a0 : (graph (A ⊔ B) A B).Adj (q 0) (q 1) := hadj 0 (by omega)
  have a1 : (graph (A ⊔ B) A B).Adj (q 1) (q 2) := hadj 1 (by omega)
  have a2 : (graph (A ⊔ B) A B).Adj (q 2) (q 3) := hadj 2 (by omega)
  have a3 : (graph (A ⊔ B) A B).Adj (q 3) (q 4) := hadj 3 (by omega)
  have a4 : (graph (A ⊔ B) A B).Adj (q 4) (q 5) := hadj 4 (by omega)
  have a5 : (graph (A ⊔ B) A B).Adj (q 5) (q 6) := hadj 5 (by omega)
  have a6 : (graph (A ⊔ B) A B).Adj (q 6) (q 7) := hadj 6 (by omega)
  have a7 : (graph (A ⊔ B) A B).Adj (q 7) (q 8) := hadj 7 (by omega)
  have a8 : (graph (A ⊔ B) A B).Adj (q 8) (q 9) := hadj 8 (by omega)
  have a9 : (graph (A ⊔ B) A B).Adj (q 9) (q 10) := hadj 9 (by omega)
  have n0 : q 0 ≠ q 2 := hnb 0 (by omega)
  have n1 : q 1 ≠ q 3 := hnb 1 (by omega)
  have n2 : q 2 ≠ q 4 := hnb 2 (by omega)
  have n3 : q 3 ≠ q 5 := hnb 3 (by omega)
  have n4 : q 4 ≠ q 6 := hnb 4 (by omega)
  have n5 : q 5 ≠ q 7 := hnb 5 (by omega)
  have n6 : q 6 ≠ q 8 := hnb 6 (by omega)
  have n7 : q 7 ≠ q 9 := hnb 7 (by omega)
  have n8 : q 8 ≠ q 10 := hnb 8 (by omega)
  have t1 : vtype (q 1) = false := vtype_eq_false_of_adj a0 h0
  have t2 : vtype (q 2) = true := vtype_eq_true_of_adj a1 t1
  have t3 : vtype (q 3) = false := vtype_eq_false_of_adj a2 t2
  have t4 : vtype (q 4) = true := vtype_eq_true_of_adj a3 t3
  have t5 : vtype (q 5) = false := vtype_eq_false_of_adj a4 t4
  have t6 : vtype (q 6) = true := vtype_eq_true_of_adj a5 t5
  have t7 : vtype (q 7) = false := vtype_eq_false_of_adj a6 t6
  have t8 : vtype (q 8) = true := vtype_eq_true_of_adj a7 t7
  have t9 : vtype (q 9) = false := vtype_eq_false_of_adj a8 t8
  have t10 : vtype (q 10) = true := vtype_eq_true_of_adj a9 t9
  have hdist : ∀ i k, i + k ≤ 10 → CosetGeom.dist (q i) (q (i + k)) ≤ k := by
    intro i k
    induction k with
    | zero => intro _; simp [CosetGeom.dist_self]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : CosetGeom.dist (q (i + k)) (q (i + k + 1)) = 1 :=
        dist_eq_one_iff_adj.mpr (hadj (i + k) (by omega))
      have h3 := CosetGeom.dist_triangle rfl (q i) (q (i + k)) (q (i + k + 1))
      rw [show i + (k + 1) = i + k + 1 by omega]
      omega
  obtain ⟨a, ha, ea⟩ := h.exists_ne_one_mem_Zv h0
  obtain ⟨b, hbz, eb⟩ := h.exists_ne_one_mem_Zv t10
  have haG : a ∈ A ⊔ B := h.mem_sup_of_mem_Zv h0 ha
  have hbG : b ∈ A ⊔ B := h.mem_sup_of_mem_Zv t10 hbz
  have haa : a * a = 1 := h.mul_self_eq_one_of_mem_Zv h0 ha
  have hbb : b * b = 1 := h.mul_self_eq_one_of_mem_Zv t10 hbz
  have hfa : (⟨a, haG⟩ : ↥(A ⊔ B)) • q 6 = q 6 := by
    apply smul_eq_of_mem_stab
    have hd : CosetGeom.dist (q 1) (q 6) ≤ 5 := hdist 1 5 (by omega)
    exact h.Vv_le_stab_A hb t1 hd (h.Zv_le_Vv a0.symm t1 ha)
  have hfb : (⟨b, hbG⟩ : ↥(A ⊔ B)) • q 4 = q 4 := by
    apply smul_eq_of_mem_stab
    have hd : CosetGeom.dist (q 9) (q 4) ≤ 5 := by
      rw [CosetGeom.dist_comm]
      exact hdist 4 5 (by omega)
    exact h.Vv_le_stab_A hb t9 hd (h.Zv_le_Vv a9 t9 hbz)
  obtain ⟨y₈, hy₈, ey₈⟩ := h.exists_ne_one_mem_Zv t8
  obtain ⟨y₂, hy₂, ey₂⟩ := h.exists_ne_one_mem_Zv t2
  have hne46 : Zv z (q 4) ≠ Zv z (q 6) := h.Zv_ne_two a4 a5 t5 n4
  have hswa : (⟨a, haG⟩ : ↥(A ⊔ B)) • q 7 ≠ q 7 := by
    have hw : Walk4 A B (q 2) (q 3) (q 4) (q 5) (q 6) := ⟨t2, a2, a3, a4, a5, n2, n3, n4⟩
    have hpa := h.pair_apply (hP _ _ _ _ _ hw) h0 a0 a1 a2 n0 n1 t8 a7.symm a6.symm a5.symm
      n6.symm n5.symm ha hy₈ ea ey₈
    exact h.not_fixes_of_comm haG t6 a6 a7 n6.symm t4 hfa hy₈ ey₈ hpa.1 hpa.2 hne46
  have hswb : (⟨b, hbG⟩ : ↥(A ⊔ B)) • q 3 ≠ q 3 := by
    have hw : Walk4 A B (q 8) (q 7) (q 6) (q 5) (q 4) :=
      ⟨t8, a7.symm, a6.symm, a5.symm, a4.symm, n6.symm, n5.symm, n4.symm⟩
    have hpb := h.pair_apply (hP _ _ _ _ _ hw) t10 a9.symm a8.symm a7.symm n8.symm n7.symm
      t2 a2 a3 a4 n2 n3 hbz hy₂ eb ey₂
    exact h.not_fixes_of_comm hbG t4 a3.symm a2.symm n2 t6 hfb hy₂ ey₂ hpb.1 hpb.2
      (Ne.symm hne46)
  set ag : ↥(A ⊔ B) := ⟨a, haG⟩ with hag
  set bg : ↥(A ⊔ B) := ⟨b, hbG⟩ with hbg
  have hP₃ : b * (a * b * a⁻¹) * b⁻¹ * (a * b * a⁻¹)⁻¹ ∈ Zv z (q 6) ∧
      b * (a * b * a⁻¹) * b⁻¹ * (a * b * a⁻¹)⁻¹ ≠ 1 := by
    have hw : Walk4 A B (q 8) (q 7) (q 6) (ag • q 7) (ag • q 8) :=
      ⟨t8, a7.symm, a6.symm, by
          have := (smul_adj ag).mpr a6
          rwa [hfa] at this,
        (smul_adj ag).mpr a7, n6.symm, hswa.symm,
        fun e => n6 (smul_left_cancel ag (hfa.trans e))⟩
    have hbl : a * b * a⁻¹ ∈ Zv z (ag • q 10) := by
      rw [Zv_smul h.normalizes_zpowers]
      exact mul_mem_conjSub hbz
    have hbl1 : a * b * a⁻¹ ≠ 1 := fun e1 => eb (by
      have e2 : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [e2, e1]
      group)
    exact h.pair_apply (hP _ _ _ _ _ hw) t10 a9.symm a8.symm a7.symm n8.symm n7.symm
      (by rw [vtype_smul]; exact t10) ((smul_adj ag).mpr a9.symm) ((smul_adj ag).mpr a8.symm)
      ((smul_adj ag).mpr a7.symm) (fun e => n8 (smul_left_cancel ag e).symm)
      (fun e => n7 (smul_left_cancel ag e).symm) hbz hbl eb hbl1
  have hP₄ : a * (b * a * b⁻¹) * a⁻¹ * (b * a * b⁻¹)⁻¹ ∈ Zv z (q 4) ∧
      a * (b * a * b⁻¹) * a⁻¹ * (b * a * b⁻¹)⁻¹ ≠ 1 := by
    have hw : Walk4 A B (q 2) (q 3) (q 4) (bg • q 3) (bg • q 2) :=
      ⟨t2, a2, a3, by
          have := (smul_adj bg).mpr a3.symm
          rwa [hfb] at this,
        (smul_adj bg).mpr a2.symm, n2, hswb.symm,
        fun e => n2 (smul_left_cancel bg (hfb.trans e)).symm⟩
    have hal : b * a * b⁻¹ ∈ Zv z (bg • q 0) := by
      rw [Zv_smul h.normalizes_zpowers]
      exact mul_mem_conjSub ha
    have hal1 : b * a * b⁻¹ ≠ 1 := fun e1 => ea (by
      have e2 : a = b⁻¹ * (b * a * b⁻¹) * b := by group
      rw [e2, e1]
      group)
    exact h.pair_apply (hP _ _ _ _ _ hw) h0 a0 a1 a2 n0 n1
      (by rw [vtype_smul]; exact h0) ((smul_adj bg).mpr a0) ((smul_adj bg).mpr a1)
      ((smul_adj bg).mpr a2) (fun e => n0 (smul_left_cancel bg e))
      (fun e => n1 (smul_left_cancel bg e)) ha hal ea hal1
  have hcc : (b * (a * b * a⁻¹) * b⁻¹ * (a * b * a⁻¹)⁻¹) * (b * (a * b * a⁻¹) * b⁻¹ *
      (a * b * a⁻¹)⁻¹) = 1 := h.mul_self_eq_one_of_mem_Zv t6 hP₃.1
  have heq := dihedral_eq haa hbb hcc rfl rfl
  have hmem6 : a * (b * a * b⁻¹) * a⁻¹ * (b * a * b⁻¹)⁻¹ ∈ Zv z (q 6) := heq ▸ hP₃.1
  exact hne46 (h.Zv_eq_of_mem t4 t6 hP₄.1 hmem6 hP₄.2)

theorem false_of_pair_walk4 [Finite D] (hb : critDist (A ⊔ B) A B V = 5)
    (hP : ∀ s₀ s₁ s₂ s₃ s₄ : CosetGeom (A ⊔ B) A B, Walk4 A B s₀ s₁ s₂ s₃ s₄ →
      Pair A B z V s₀ s₁ s₂ s₃ s₄) : False := by
  obtain ⟨p, hp0⟩ := GoldAmL3T.exists_arc (Γ := graph (A ⊔ B) A B)
    (fun u v _ => h.exists_nbr_ne u v) (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm 10
  exact h.false_of_walk hb hP p.vert (fun i hi => p.adj i hi) (fun i hi => p.nb i hi)
    (by rw [hp0]; exact vtype_γ₁)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
