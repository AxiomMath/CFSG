module

public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofFactors
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5J2

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

section SimpleProduct

variable {Γ : Type} [Group Γ] {r : ℕ} {S : Fin r → Subgroup Γ}

theorem exists_map_mulAut_eq_of_isSimpleProduct (h : IsSimpleProduct (⊤ : Subgroup Γ) S)
    (α : MulAut Γ) (i : Fin r) : ∃ j, (S i).map α.toMonoidHom = S j := by
  refine h.exists_eq_of_normal le_top ?_ ?_
  · rintro v - _ ⟨s, hs, rfl⟩
    refine ⟨α.symm v * s * (α.symm v)⁻¹, h.normal i _ (Subgroup.mem_top _) s hs, ?_⟩
    simp
  · have := h.simple i
    exact ((S i).equivMapOfInjective _ α.injective).symm.isSimpleGroup

noncomputable def mulAutIdx (h : IsSimpleProduct (⊤ : Subgroup Γ) S) (α : MulAut Γ)
    (i : Fin r) : Fin r :=
  (exists_map_mulAut_eq_of_isSimpleProduct h α i).choose

theorem map_mulAut_eq_mulAutIdx (h : IsSimpleProduct (⊤ : Subgroup Γ) S) (α : MulAut Γ)
    (i : Fin r) : (S i).map α.toMonoidHom = S (mulAutIdx h α i) :=
  (exists_map_mulAut_eq_of_isSimpleProduct h α i).choose_spec

theorem mulAutIdx_one (h : IsSimpleProduct (⊤ : Subgroup Γ) S) (i : Fin r) :
    mulAutIdx h 1 i = i := by
  apply h.injective
  rw [← map_mulAut_eq_mulAutIdx h 1 i]
  exact Subgroup.map_id _

theorem mulAutIdx_mul (h : IsSimpleProduct (⊤ : Subgroup Γ) S) (α β : MulAut Γ) (i : Fin r) :
    mulAutIdx h (α * β) i = mulAutIdx h α (mulAutIdx h β i) := by
  apply h.injective
  rw [← map_mulAut_eq_mulAutIdx h, ← map_mulAut_eq_mulAutIdx h, ← map_mulAut_eq_mulAutIdx h,
    Subgroup.map_map]
  rfl

@[instance_reducible] noncomputable def mulActionMulAutIdx
    (h : IsSimpleProduct (⊤ : Subgroup Γ) S) : MulAction (MulAut Γ) (Fin r) where
  smul α i := mulAutIdx h α i
  one_smul i := mulAutIdx_one h i
  mul_smul α β i := mulAutIdx_mul h α β i

noncomputable def mulAutPerm (h : IsSimpleProduct (⊤ : Subgroup Γ) S) :
    MulAut Γ →* Equiv.Perm (Fin r) :=
  @MulAction.toPermHom (MulAut Γ) (Fin r) _ (mulActionMulAutIdx h)

theorem map_eq_of_mem_ker_mulAutPerm (h : IsSimpleProduct (⊤ : Subgroup Γ) S) {α : MulAut Γ}
    (hα : α ∈ (mulAutPerm h).ker) (i : Fin r) : (S i).map α.toMonoidHom = S i := by
  rw [map_mulAut_eq_mulAutIdx h α i]
  congr 1
  exact congrArg (fun σ : Equiv.Perm (Fin r) => σ i) (MonoidHom.mem_ker.mp hα)

noncomputable def restrictMulAut {K : Subgroup Γ} (α : MulAut Γ) (hK : K.map α.toMonoidHom = K) :
    MulAut K :=
  (K.equivMapOfInjective α.toMonoidHom α.injective).trans (MulEquiv.subgroupCongr hK)

noncomputable def kerRestrict (h : IsSimpleProduct (⊤ : Subgroup Γ) S) :
    (mulAutPerm h).ker →* ((i : Fin r) → MulAut (S i)) where
  toFun α i := restrictMulAut (α : MulAut Γ) (map_eq_of_mem_ker_mulAutPerm h α.2 i)
  map_one' := by
    funext i
    exact MulEquiv.ext fun x => Subtype.ext rfl
  map_mul' α β := by
    funext i
    exact MulEquiv.ext fun x => Subtype.ext rfl

theorem kerRestrict_injective (h : IsSimpleProduct (⊤ : Subgroup Γ) S) :
    Function.Injective (kerRestrict h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hfix : ∀ i, ∀ x ∈ S i, (α : MulAut Γ) x = x := fun i x hx =>
    congrArg (fun φ : (i : Fin r) → MulAut (S i) => ((φ i ⟨x, hx⟩ : S i) : Γ)) hα
  have hle : (⊤ : Subgroup Γ) ≤
      MonoidHom.eqLocus (α : MulAut Γ).toMonoidHom (MonoidHom.id Γ) := by
    rw [← h.iSup_eq]
    exact iSup_le fun i x hx => hfix i x hx
  exact MulEquiv.ext fun x => hle (Subgroup.mem_top x)

theorem card_mulAut_dvd_of_isSimpleProduct [Finite Γ] (h : IsSimpleProduct (⊤ : Subgroup Γ) S) :
    Nat.card (MulAut Γ) ∣ r.factorial * ∏ i, Nat.card (MulAut (S i)) := by
  classical
  haveI : Finite (MulAut Γ) :=
    Finite.of_injective (fun α : MulAut Γ => (α : Γ → Γ)) DFunLike.coe_injective
  haveI : ∀ i, Finite (MulAut (S i)) := fun i =>
    Finite.of_injective (fun α : MulAut (S i) => (α : S i → S i)) DFunLike.coe_injective
  have hcard := Subgroup.card_ker_mul_card_range (mulAutPerm h)
  have hk : Nat.card (mulAutPerm h).ker ∣ ∏ i, Nat.card (MulAut (S i)) := by
    have h1 : Nat.card (mulAutPerm h).ker = Nat.card (kerRestrict h).range :=
      Nat.card_congr (Equiv.ofInjective _ (kerRestrict_injective h))
    rw [h1, ← Nat.card_pi]
    exact Subgroup.card_subgroup_dvd_card _
  have hr : Nat.card (mulAutPerm h).range ∣ r.factorial := by
    have h1 := Subgroup.card_subgroup_dvd_card (mulAutPerm h).range
    rwa [Nat.card_perm, Nat.card_fin] at h1
  rw [← hcard, mul_comm]
  exact mul_dvd_mul hr hk

end SimpleProduct

section Three

variable (A B C : Type) [Group A] [Group B] [Group C]

@[expose] def prodThreeFactors : Fin 3 → Subgroup (A × (B × C)) :=
  ![(MonoidHom.inl A (B × C)).range, ((MonoidHom.inr A (B × C)).comp (MonoidHom.inl B C)).range,
    ((MonoidHom.inr A (B × C)).comp (MonoidHom.inr B C)).range]

variable {A B C}

theorem injective_inl_three : Function.Injective (MonoidHom.inl A (B × C)) :=
  fun _ _ h => congrArg Prod.fst h

theorem injective_inr_inl_three :
    Function.Injective ((MonoidHom.inr A (B × C)).comp (MonoidHom.inl B C)) :=
  fun _ _ h => congrArg (fun x : A × (B × C) => x.2.1) h

theorem injective_inr_inr_three :
    Function.Injective ((MonoidHom.inr A (B × C)).comp (MonoidHom.inr B C)) :=
  fun _ _ h => congrArg (fun x : A × (B × C) => x.2.2) h

theorem exists_not_commute_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ a b : X, a * b ≠ b * a) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem eq_one_of_forall_commute_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) {x : X} (hx : ∀ y : X, x * y = y * x) : x = 1 := by
  apply CFSG.RankThree.PartTwo.Sec14.Wales1411W.HJProd.conj_injective_of_simple hX
  rw [map_one]
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.conj_apply, MulAut.one_apply, hx y, mul_inv_cancel_right]

variable [IsSimpleGroup A] [IsSimpleGroup B] [IsSimpleGroup C]

theorem isSimpleProduct_prodThreeFactors (hA : ∃ a b : A, a * b ≠ b * a)
    (hB : ∃ a b : B, a * b ≠ b * a) (hC : ∃ a b : C, a * b ≠ b * a) :
    IsSimpleProduct (⊤ : Subgroup (A × (B × C))) (prodThreeFactors A B C) := by
  have e0 := MonoidHom.ofInjective (injective_inl_three (A := A) (B := B) (C := C))
  have e1 := MonoidHom.ofInjective (injective_inr_inl_three (A := A) (B := B) (C := C))
  have e2 := MonoidHom.ofInjective (injective_inr_inr_three (A := A) (B := B) (C := C))
  refine ⟨fun _ => le_top, fun i => ?_, fun i => ?_, fun i v _ s hs => ?_,
    fun i j hij s hs t ht => ?_, ?_, fun z _ hz => ?_⟩
  · fin_cases i
    · exact e0.symm.isSimpleGroup
    · exact e1.symm.isSimpleGroup
    · exact e2.symm.isSimpleGroup
  · fin_cases i
    · exact exists_not_commute_of_mulEquiv e0 hA
    · exact exists_not_commute_of_mulEquiv e1 hB
    · exact exists_not_commute_of_mulEquiv e2 hC
  · fin_cases i
    · obtain ⟨a, rfl⟩ := hs
      exact ⟨v.1 * a * v.1⁻¹, by ext <;> simp⟩
    · obtain ⟨b, rfl⟩ := hs
      exact ⟨v.2.1 * b * v.2.1⁻¹, by ext <;> simp⟩
    · obtain ⟨c, rfl⟩ := hs
      exact ⟨v.2.2 * c * v.2.2⁻¹, by ext <;> simp⟩
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | (obtain ⟨a, rfl⟩ := hs
         obtain ⟨b, rfl⟩ := ht
         ext <;> simp)
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = (x.1, 1) * ((1, (x.2.1, 1)) * (1, (1, x.2.2))) := by
      ext <;> simp
    rw [hx]
    refine mul_mem (Subgroup.mem_iSup_of_mem 0 ⟨x.1, rfl⟩)
      (mul_mem (Subgroup.mem_iSup_of_mem 1 ⟨x.2.1, rfl⟩) (Subgroup.mem_iSup_of_mem 2 ⟨x.2.2, rfl⟩))
  · have h0 : z.1 = 1 := eq_one_of_forall_commute_of_simple hA fun a =>
      congrArg Prod.fst (hz 0 (a, 1) ⟨a, rfl⟩)
    have h1 : z.2.1 = 1 := eq_one_of_forall_commute_of_simple hB fun b =>
      congrArg (fun x : A × (B × C) => x.2.1) (hz 1 (1, (b, 1)) ⟨b, rfl⟩)
    have h2 : z.2.2 = 1 := eq_one_of_forall_commute_of_simple hC fun c =>
      congrArg (fun x : A × (B × C) => x.2.2) (hz 2 (1, (1, c)) ⟨c, rfl⟩)
    ext
    · exact h0
    · exact h1
    · exact h2

theorem card_mulAut_prod_three_dvd [Finite A] [Finite B] [Finite C]
    (hA : ∃ a b : A, a * b ≠ b * a) (hB : ∃ a b : B, a * b ≠ b * a)
    (hC : ∃ a b : C, a * b ≠ b * a) :
    Nat.card (MulAut (A × (B × C))) ∣
      6 * (Nat.card (MulAut A) * Nat.card (MulAut B) * Nat.card (MulAut C)) := by
  have h := card_mulAut_dvd_of_isSimpleProduct (isSimpleProduct_prodThreeFactors hA hB hC)
  rw [Fin.prod_univ_three] at h
  have c0 : Nat.card (MulAut (prodThreeFactors A B C 0)) = Nat.card (MulAut A) :=
    Nat.card_congr (MulAut.congr (MonoidHom.ofInjective injective_inl_three).symm).toEquiv
  have c1 : Nat.card (MulAut (prodThreeFactors A B C 1)) = Nat.card (MulAut B) :=
    Nat.card_congr (MulAut.congr (MonoidHom.ofInjective injective_inr_inl_three).symm).toEquiv
  have c2 : Nat.card (MulAut (prodThreeFactors A B C 2)) = Nat.card (MulAut C) :=
    Nat.card_congr (MulAut.congr (MonoidHom.ofInjective injective_inr_inr_three).symm).toEquiv
  rwa [c0, c1, c2, show (3 : ℕ).factorial = 6 from rfl] at h

end Three

end CFSG.RankThree.GF2n.Smith81.Insp
