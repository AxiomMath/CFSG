module

public import CFSG.Quasithin.Vol2.Ch10SecQ2Tr
public import CFSG.Quasithin.Vol2.Ch10SecEE3Gen

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE.C10P02

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

section Aux

variable {M : Type*} [Group M]

theorem conj_eq_of_sq {q v : M} (hq : q ^ 2 = 1) (hv : v ^ 2 = 1) (h : (q * v) ^ 2 = 1) :
    q * v * q⁻¹ = v := by
  have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hq)
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv)
  rw [pow_two, ← mul_assoc] at h
  rw [hq', eq_inv_of_mul_eq_one_left h, hv']

theorem conj_mul_eq_of_commute {q₁ q₂ v v₂ : M} (h₁ : q₁ ^ 2 = 1) (h₂ : q₂ ^ 2 = 1)
    (hc : q₁ * q₂ = q₂ * q₁) (h : q₁ * v * (q₂ * v₂) = q₂ * v₂ * (q₁ * v)) :
    q₂ * v * q₂⁻¹ * v₂ = q₁ * v₂ * q₁⁻¹ * v := by
  have h₁' : q₁ * q₁ = 1 := by rw [← pow_two]; exact h₁
  have h₂' : q₂ * q₂ = 1 := by rw [← pow_two]; exact h₂
  have hi₁ : q₁⁻¹ = q₁ := inv_eq_of_mul_eq_one_right h₁'
  have hi₂ : q₂⁻¹ = q₂ := inv_eq_of_mul_eq_one_right h₂'
  have e1 : q₂ * v * q₂⁻¹ * v₂ = q₂ * q₁ * (q₁ * v * (q₂ * v₂)) := by
    rw [hi₂]
    simp only [mul_assoc]
    rw [← mul_assoc q₁ q₁, h₁', one_mul]
  have e2 : q₁ * v₂ * q₁⁻¹ * v = q₂ * q₁ * (q₂ * v₂ * (q₁ * v)) := by
    rw [hi₁]
    simp only [mul_assoc]
    rw [← mul_assoc q₁ q₂, hc, mul_assoc, ← mul_assoc q₂ q₂, h₂', one_mul]
  rw [e1, e2, h]

theorem mul_inv_eq_of_mul_eq {C : Type*} [CommGroup C] {a b c d : C} (h : a * b = c * d) :
    a * d⁻¹ = c * b⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, mul_right_comm, h, mul_inv_cancel_right]

end Aux

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : Case2Data hyp t)

@[expose] noncomputable def gam (B : Subgroup G) : Finset (Fin 4) :=
  D.phi (autI (SecA.isElemAbelian_fsuVM hyp) B)

theorem mem_gam {B : Subgroup G} {i : Fin 4} :
    i ∈ gam D B ↔ D.tau i ∈ autI (SecA.isElemAbelian_fsuVM hyp) B :=
  D.mem_phi

theorem autI_baum : autI (SecA.isElemAbelian_fsuVM hyp) (baum T) = D.P₁ ⊔ D.P₂ := by
  rw [D.baum_eq, D.thompsonJ_eq]

theorem mem_fixV_Yg {γ : Finset (Fin 4)} {w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)}
    (h : ∀ i ∈ γ, D.tau i w = w) : w ∈ fixV (D.Yg γ) := by
  have hle : D.Yg γ ≤ MulAction.stabilizer
      (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))) w :=
    D.Yg_le_of fun i hi => MulAction.mem_stabilizer_iff.mpr (h i hi)
  exact fun φ hφ => MulAction.mem_stabilizer_iff.mp (hle hφ)

theorem cls (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {q : Fin 4 → Subgroup.normalizer (fsuVM T L I : Set G)} (hqT : ∀ i, (q i : G) ∈ T)
    (hq2 : ∀ i, (q i : G) ^ 2 = 1) (hqc : ∀ i j, (q i : G) * q j = q j * q i)
    (hqτ : ∀ i, convI (SecA.isElemAbelian_fsuVM hyp) (q i) = D.tau i)
    {B : Subgroup G} (hBS : B ≤ baum T) (hB : IsElemAbelian 2 B)
    (hcard : Nat.card B = Nat.card (fsuVM T L I)) :
    autI (SecA.isElemAbelian_fsuVM hyp) B = D.Yg (gam D B) ∧
      B ⊓ Subgroup.centralizer (fsuVM T L I : Set G) =
        fsuVM T L I ⊓ Subgroup.centralizer (B : Set G) ∧
      ∀ i ∈ gam D B, (q i : G) ∈ B := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hBT : B ≤ T := hBS.trans inf_le_left
  have hBN : B ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    hBT.trans (SecA.le_normalizer_fsuVM T L I)
  have hBP : autI hV B ≤ D.P₁ ⊔ D.P₂ := autI_baum D ▸ autI_mono hV hBS
  have h1 := card_autI_mul_card_inf hV hBN
  have h3 := card_fixV_autI hV hBN
  have hab := hB.1
  have hle : B ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤
      fsuVM T L I ⊓ Subgroup.centralizer (B : Set G) := fun x hx =>
    ⟨hCV ⟨hBT hx.1, hx.2⟩, Subgroup.mem_centralizer_iff.mpr fun b hb => setLike_mul_comm hb hx.1⟩
  have h5 := D.prodSetting.card_mul_card_fixV_le D.bound₁ D.bound₂ hBP
  have hW : Nat.card (IntMod (fsuVM T L I) hV) = Nat.card (fsuVM T L I) := rfl
  rw [D.commV_sup_eq_top hC0, inf_top_eq, Subgroup.card_top, hW, h3] at h5
  have hpos : 0 < Nat.card (autI hV B) := Nat.card_pos
  have hc : Nat.card ↥(B ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) =
      Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (B : Set G)) := by
    refine le_antisymm (Subgroup.card_le_of_le hle) (Nat.le_of_mul_le_mul_left ?_ hpos)
    rw [h1, hcard]
    exact h5
  have hinf := Subgroup.eq_of_le_of_card_ge hle hc.ge
  have hexact : Nat.card (autI hV B) *
      Nat.card ↥(fixV (autI hV B) ⊓ (commV D.K₁ ⊔ commV D.K₂)) =
        Nat.card ↥(commV D.K₁ ⊔ commV D.K₂) := by
    rw [D.commV_sup_eq_top hC0, inf_top_eq, Subgroup.card_top, hW, h3, ← hc, h1, hcard]
  have hY : autI hV B = D.Yg (gam D B) := D.eq_Yg_of_exact hBP hexact
  refine ⟨hY, hinf, fun i hi => ?_⟩
  have hmemB : ∀ v ∈ fsuVM T L I, v ∈ Subgroup.centralizer (B : Set G) → v ∈ B := by
    intro v hv hvc
    have h6 : v ∈ B ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := hinf ▸ ⟨hv, hvc⟩
    exact h6.1
  have hlift : ∀ j ∈ gam D B, ∃ b : Subgroup.normalizer (fsuVM T L I : Set G), (b : G) ∈ B ∧
      convI hV b = D.tau j := fun j hj => (mem_autI hV).mp ((mem_gam D).mp hj)
  have hpart : ∀ (j : Fin 4) (b : Subgroup.normalizer (fsuVM T L I : Set G)), (b : G) ∈ B →
      convI hV b = D.tau j → (q j : G)⁻¹ * b ∈ fsuVM T L I := by
    intro j b hb hbτ
    refine hCV ⟨T.mul_mem (T.inv_mem (hqT j)) (hBT hb), ?_⟩
    have h7 : convI hV ((q j)⁻¹ * b) = 1 := by rw [map_mul, map_inv, hqτ, hbτ, inv_mul_cancel]
    exact (convI_eq_one_iff hV _).mp h7
  obtain ⟨b, hbB, hbτ⟩ := hlift i hi
  have hvV := hpart i b hbB hbτ
  set v := (q i : G)⁻¹ * b with hv
  have hbv : (b : G) = q i * v := by rw [hv, mul_inv_cancel_left]
  have hfix : ∀ j ∈ gam D B, D.tau j (IntMod.mk hV ⟨v, hvV⟩) = IntMod.mk hV ⟨v, hvV⟩ := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      rw [← hqτ j]
      apply IntMod.val_injective
      rw [convI_apply_val]
      exact conj_eq_of_sq (hq2 j) (hV.2 v hvV) (hbv ▸ hB.2 b hbB)
    · obtain ⟨b', hb'B, hb'τ⟩ := hlift j hj
      have hv'V := hpart j b' hb'B hb'τ
      set v' := (q j : G)⁻¹ * b' with hv'
      have hb'v : (b' : G) = q j * v' := by rw [hv', mul_inv_cancel_left]
      have hcomm : (b : G) * b' = b' * b := setLike_mul_comm hbB hb'B
      rw [hbv, hb'v] at hcomm
      have key := conj_mul_eq_of_commute (hq2 i) (hq2 j) (hqc i j) hcomm
      have hW' : D.tau j (IntMod.mk hV ⟨v, hvV⟩) * IntMod.mk hV ⟨v', hv'V⟩ =
          D.tau i (IntMod.mk hV ⟨v', hv'V⟩) * IntMod.mk hV ⟨v, hvV⟩ := by
        apply IntMod.val_injective
        rw [IntMod.val_mul, IntMod.val_mul, ← hqτ j, ← hqτ i, convI_apply_val, convI_apply_val]
        exact key
      exact mul_inv_eq_one.mp (tau_comm_eq_one D hC0 hji (mul_inv_eq_of_mul_eq hW'))
  have hvC : v ∈ Subgroup.centralizer (B : Set G) := by
    have h8 : IntMod.mk hV ⟨v, hvV⟩ ∈ fixV (autI hV B) := by
      rw [hY]
      exact mem_fixV_Yg D hfix
    exact (mem_fixV_autI hV hBN (IntMod.mk hV ⟨v, hvV⟩)).mp h8
  have hvB := hmemB v hvV hvC
  have hqi : (q i : G) = b * v⁻¹ := by rw [hbv, mul_inv_cancel_right]
  rw [hqi]
  exact B.mul_mem hbB (B.inv_mem hvB)

end CFSG.Quasithin.Vol2.Ch10.SecE.C10P02
