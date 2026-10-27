module

public import CFSG.Quasithin.Vol2.Ch11SecOE3I
public import CFSG.Quasithin.Background.B69Cnt
public import CFSG.Quasithin.Vol2.Ch11SecOE3G

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique.Setup
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T K I : Subgroup G} {r : ℕ} (h : Setting G T K I r) [IsMulCommutative ↥(fsuV T I)]
include h

theorem I_mem_irrPlus :
    I.subgroupOf (fsuV T I) ∈ IrrPlus (autOn K (fsuV T I)) (⊤ : Subgroup ↥(fsuV T I)) := by
  have h1 := h.fsu.irrPlus.2.2.2.2.1
  have h2 := h.fsu.irrPlus.2.2.2.2.2.1
  rw [show conjClosure K T = K from h.fsuL0_eq] at h1 h2
  exact mem_irrPlus_autOn h.le_normalizer_V (I_le_V T I) h.le_normalizer_I h.commutator_I h1 h2

theorem apply_eq_of_mem_I {b : MulAut ↥(fsuV T I)}
    (hb : b ∈ Subgroup.centralizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I))))
    (hb2 : b * b = 1) {v : ↥(fsuV T I)} (hv : v ∈ I.subgroupOf (fsuV T I)) : b v = v := by
  have hW := h.I_mem_irrPlus
  obtain ⟨hinv, -, -, hirr⟩ := mem_irrPlus_top_iff.1 hW
  set W := I.subgroupOf (fsuV T I) with hWdef
  set U := W ⊓ fixV (autOn K (fsuV T I)) with hUdef
  have hbW : ∀ w ∈ W, b w ∈ W := fun w hw => h.map_mem_I hb hw
  have hbU : ∀ u ∈ U, b u ∈ U := fun u hu => ⟨hbW u hu.1, (apply_mem_fixV_iff hb u).2 hu.2⟩
  have hbb : ∀ w, b (b w) = w := fun w => by rw [← MulAut.mul_apply, hb2, MulAut.one_apply]
  set J := Subgroup.closure {s | ∃ w ∈ W, b w * w⁻¹ = s} ⊔ U with hJdef
  have hJinv : ∀ x ∈ autOn K (fsuV T I), ∀ w ∈ J, x w ∈ J := by
    intro x hx
    have hle : J ≤ J.comap x.toMonoidHom := by
      refine sup_le ?_ fun u hu => ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨w, hw, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x w, hinv x hx w hw, ?_⟩)
        rw [MulEquiv.coe_toMonoidHom, map_mul, map_inv, ← MulAut.mul_apply _ x b,
          Subgroup.mem_centralizer_iff.mp hb x hx, MulAut.mul_apply]
      · refine Subgroup.mem_sup_right ?_
        rw [MulEquiv.coe_toMonoidHom, hu.2 x hx]
        exact hu
    exact fun w hw => hle hw
  have hJW : J ≤ W := by
    refine sup_le ?_ inf_le_left
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact W.mul_mem (hbW w hw) (W.inv_mem hw)
  have hsec : ∀ w ∈ W, b w * w⁻¹ ∈ fixV (autOn K (fsuV T I)) := by
    rcases hirr J hJinv le_sup_right hJW with hJ | hJ
    · intro w hw
      have hmem : b w * w⁻¹ ∈ J := Subgroup.mem_sup_left (Subgroup.subset_closure ⟨w, hw, rfl⟩)
      rw [hJ] at hmem
      exact hmem.2
    · let F : Subgroup ↥(fsuV T I) :=
        { carrier := {v | b v * v⁻¹ ∈ U}
          one_mem' := by
            simp only [Set.mem_ofPred_eq, map_one, inv_one, mul_one]
            exact U.one_mem
          mul_mem' := by
            intro v₁ v₂ h₁ h₂
            simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
            rw [map_mul, mul_inv, mul_mul_mul_comm]
            exact U.mul_mem h₁ h₂
          inv_mem' := by
            intro v h₁
            simp only [Set.mem_ofPred_eq] at h₁ ⊢
            rw [map_inv, ← mul_inv]
            exact U.inv_mem h₁ }
      have hJF : J ≤ F := by
        refine sup_le ?_ fun u hu => U.mul_mem (hbU u hu) (U.inv_mem hu)
        rw [Subgroup.closure_le]
        rintro _ ⟨w, hw, rfl⟩
        show b (b w * w⁻¹) * (b w * w⁻¹)⁻¹ ∈ U
        rw [map_mul, map_inv, hbb, mul_inv_rev, inv_inv, h.mul_self_eq_one]
        exact U.one_mem
      intro w hw
      rw [← hJ] at hw
      exact (hJF hw).2
  exact B69.sec_triv_imp_triv (A := Subgroup.centralizer (autOn K (fsuV T I) : Set _))
    (open_isQuasisimple h.shape_autOn.1)
    (fun a ha l hl => by
      rw [← Subgroup.mem_centralizer_iff.mp ha l hl, mul_inv_cancel_right]
      exact hl)
    hW (fun a ha w hw => h.map_mem_I ha hw) hb hsec v hv

theorem eq_one_of_mem_centralizer {b : MulAut ↥(fsuV T I)}
    (hb : b ∈ Subgroup.centralizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I))))
    (hb2 : b * b = 1) : b = 1 := by
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have key : ∀ t ∈ T, ∀ i ∈ I, ∀ hv : t * i * t⁻¹ ∈ fsuV T I,
      b ⟨t * i * t⁻¹, hv⟩ = ⟨t * i * t⁻¹, hv⟩ := by
    intro t ht i hi hv
    set τ := conjAct (fsuV T I) ⟨t, hTV ht⟩ with hτ
    have hτL : ∀ x ∈ autOn K (fsuV T I), τ * x * τ⁻¹ ∈ autOn K (fsuV T I) := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := Ch10.SecA.mem_autOn_iff'.mp hx
      refine Ch10.SecA.mem_autOn_iff'.mpr ⟨⟨t, hTV ht⟩ * g * ⟨t, hTV ht⟩⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (h.normal ht) g).mp hg
      · rw [hτ, map_mul, map_mul, map_inv]
    have hb' : τ⁻¹ * b * τ ∈
        Subgroup.centralizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 : τ * x * τ⁻¹ * b = b * (τ * x * τ⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hb _ (hτL x hx)
      calc x * (τ⁻¹ * b * τ) = τ⁻¹ * ((τ * x * τ⁻¹) * b) * τ := by group
        _ = τ⁻¹ * (b * (τ * x * τ⁻¹)) * τ := by rw [h1]
        _ = τ⁻¹ * b * τ * x := by group
    have hb'2 : τ⁻¹ * b * τ * (τ⁻¹ * b * τ) = 1 := by
      rw [show τ⁻¹ * b * τ * (τ⁻¹ * b * τ) = τ⁻¹ * (b * b) * τ by group, hb2]
      group
    have h2 := h.apply_eq_of_mem_I hb' hb'2 (v := ⟨i, I_le_V T I hi⟩) hi
    rw [MulAut.mul_apply, MulAut.mul_apply] at h2
    have h3 := congrArg (fun y => τ y) h2
    simp only [MulAut.apply_inv_self] at h3
    have e : (⟨t * i * t⁻¹, hv⟩ : ↥(fsuV T I)) = τ ⟨i, I_le_V T I hi⟩ :=
      Subtype.ext (Ch10.SecA.coe_conjAct_apply' ⟨t, hTV ht⟩ ⟨i, I_le_V T I hi⟩).symm
    rw [e]
    exact h3
  let Fx : Subgroup ↥(fsuV T I) :=
    { carrier := {v | b v = v}
      one_mem' := map_one b
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_mul] at hx hy ⊢
        rw [hx, hy]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq, map_inv] at hx ⊢
        rw [hx] }
  have hV : fsuV T I ≤ Fx.map (fsuV T I).subtype :=
    conjClosure_le fun t ht i hi => ⟨⟨t * i * t⁻¹, mem_conjClosure ht hi⟩,
      key t ht i hi (mem_conjClosure ht hi), rfl⟩
  refine MulEquiv.ext fun v => ?_
  obtain ⟨w, hw, hwv⟩ := hV v.2
  rw [MulAut.one_apply, ← Subtype.ext hwv]
  exact hw

theorem false_of_comm_eq_bot {A : Subgroup (MulAut ↥(fsuV T I))}
    (hA : Family.IsBestOffender
      (Subgroup.normalizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I)))) A)
    (hc : ⁅autOn K (fsuV T I), A⁆ = ⊥) : False := by
  obtain ⟨-, hA1, hAel, -, -⟩ := hA
  have hAC := Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
  apply hA1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  exact h.eq_one_of_mem_centralizer (hAC ha) (by rw [← pow_two]; exact hAel.2 a ha)

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE3
