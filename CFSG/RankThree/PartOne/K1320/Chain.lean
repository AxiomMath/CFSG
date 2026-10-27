module

public import CFSG.RankThree.PartOne.S12.Sec1320
public import CFSG.RankThree.PartOne.S12.Sec1322Reflect

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem kfKt_of_kfAt {p : ℕ} {E : Subgroup G} {f : ℕ} {t : MulAut E} (h : KFAt p E f t) :
    KFKt p E f t (kZero p E t) := by
  obtain ⟨hne, hmod, hcent, hmoved, hlift⟩ := h
  have hIs : IsKt p E t (kZero p E t) := ⟨fun f' hf' => absurd ⟨f', hf'⟩ hne, fun _ => rfl⟩
  exact ⟨hIs, fun K' hK' => hK'.2 hne, hmod, hcent, hmoved, hlift⟩

theorem chain_conj_into_L {p : ℕ} (hp : p.Prime) {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E}
    (hch : Chain3 p E L t₁ t₂ t₃) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ∈ reflectionSet p E ∧
      conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ∈ torusImage E L ∧
      conjAut E w hw * t₂ * (conjAut E w hw)⁻¹ ∈ reflectionSet p E ∧
      conjAut E w hw * t₂ * (conjAut E w hw)⁻¹ ∈ torusImage E L ∧
      orderOf (conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ *
        (conjAut E w hw * t₂ * (conjAut E w hw)⁻¹)) = 4 := by
  obtain ⟨w, hw, h1, h2⟩ := hch.inL
  refine ⟨w, hw, conj_mem_reflectionSet hp hch.mem₁ hw, h1, conj_mem_reflectionSet hp hch.mem₂ hw,
    h2, ?_⟩
  have hprod : conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ *
      (conjAut E w hw * t₂ * (conjAut E w hw)⁻¹) =
      conjAut E w hw * (t₁ * t₂) * (conjAut E w hw)⁻¹ := by group
  rw [hprod, ← hch.ord₁₂]
  exact (MulEquiv.orderOf_eq (MulAut.conj (conjAut E w hw)) (t₁ * t₂))

omit [Finite G] in
theorem chain_conj_eq {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E}
    (hch : Chain3 p E L t₁ t₂ t₃) : (t₂ * t₃)⁻¹ * t₃ * (t₂ * t₃) = t₂ := by
  have h2 : t₂ * t₂ = 1 := RefFacts.mul_self_eq_one hch.mem₂.1
  have h3 : t₃ * t₃ = 1 := RefFacts.mul_self_eq_one hch.mem₃.1
  have hm3 : (t₂ * t₃) ^ 3 = 1 := by rw [← hch.ord₂₃]; exact pow_orderOf_eq_one _
  have h6 : t₂ * t₃ * t₂ * t₃ * t₂ * t₃ = 1 := by
    simpa [pow_succ, mul_assoc] using hm3
  have hinv : (t₂ * t₃)⁻¹ = t₃ * t₂ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h3, inv_eq_of_mul_eq_one_right h2]
  rw [hinv]
  calc t₃ * t₂ * t₃ * (t₂ * t₃) = (t₂ * t₂) * t₃ * t₂ * t₃ * t₂ * t₃ := by
        rw [h2, one_mul]; simp only [mul_assoc]
    _ = t₂ * (t₂ * t₃ * t₂ * t₃ * t₂ * t₃) := by simp only [mul_assoc]
    _ = t₂ := by rw [h6, mul_one]

omit [Finite G] in
theorem chain_t₃_eq {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E}
    (hch : Chain3 p E L t₁ t₂ t₃) : t₃ = (t₂ * t₃) * t₂ * (t₂ * t₃)⁻¹ := by
  calc t₃ = (t₂ * t₃) * ((t₂ * t₃)⁻¹ * t₃ * (t₂ * t₃)) * (t₂ * t₃)⁻¹ := by group
    _ = (t₂ * t₃) * t₂ * (t₂ * t₃)⁻¹ := by rw [chain_conj_eq hch]

omit [Finite G] in
theorem chain_t₃_conj {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E}
    (hch : Chain3 p E L t₁ t₂ t₃) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      t₃ = conjAut E w hw * t₂ * (conjAut E w hw)⁻¹ := by
  have hX2 : t₂ ∈ reflectionGroup p E := Subgroup.subset_closure hch.mem₂
  have hX3 : t₃ ∈ reflectionGroup p E := Subgroup.subset_closure hch.mem₃
  have hm : t₂ * t₃ ∈ torusWeyl E :=
    (torusWeyl E).mul_mem (Sec1322.reflectionGroup_le E hX2) (Sec1322.reflectionGroup_le E hX3)
  obtain ⟨w, hw, hwm⟩ := Sec1322.exists_lift hm
  exact ⟨w, hw, by rw [hwm]; exact chain_t₃_eq hch⟩

omit [Finite G] in
theorem chain_not_conj_one_three {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E}
    (hch : Chain3 p E L t₁ t₂ t₃)
    (hnc : ∀ s ∈ reflectionGroup p E, ∀ t ∈ reflectionGroup p E, s * s = 1 → t * t = 1 →
      (∃ x ∈ reflectionGroup p E, x * s * x⁻¹ = t) → (s * t) ^ 4 = 1 → (s * t) ^ 2 ≠ 1 → False)
    {x : MulAut E} (hx : x ∈ reflectionGroup p E) : x * t₁ * x⁻¹ ≠ t₃ := by
  intro hxt
  have hX1 : t₁ ∈ reflectionGroup p E := Subgroup.subset_closure hch.mem₁
  have hX2 : t₂ ∈ reflectionGroup p E := Subgroup.subset_closure hch.mem₂
  have hX3 : t₃ ∈ reflectionGroup p E := Subgroup.subset_closure hch.mem₃
  have hm : t₂ * t₃ ∈ reflectionGroup p E := (reflectionGroup p E).mul_mem hX2 hX3
  have h1 : t₁ * t₁ = 1 := RefFacts.mul_self_eq_one hch.mem₁.1
  have h2 : t₂ * t₂ = 1 := RefFacts.mul_self_eq_one hch.mem₂.1
  refine hnc t₁ hX1 t₂ hX2 h1 h2 ⟨(t₂ * t₃)⁻¹ * x, ?_, ?_⟩ ?_ ?_
  · exact (reflectionGroup p E).mul_mem ((reflectionGroup p E).inv_mem hm) hx
  · calc (t₂ * t₃)⁻¹ * x * t₁ * ((t₂ * t₃)⁻¹ * x)⁻¹ = (t₂ * t₃)⁻¹ * (x * t₁ * x⁻¹) * (t₂ * t₃) := by
          group
      _ = (t₂ * t₃)⁻¹ * t₃ * (t₂ * t₃) := by rw [hxt]
      _ = t₂ := chain_conj_eq hch
  · rw [← hch.ord₁₂]; exact pow_orderOf_eq_one _
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hch.ord₁₂] at this
    omega

omit [Finite G] in
theorem conjBy_sup (w : G) (H K : Subgroup G) : conjBy w (H ⊔ K) = conjBy w H ⊔ conjBy w K := by
  unfold conjBy
  exact Subgroup.map_sup _ _ _

omit [Finite G] in
theorem conjBy_inf (w : G) (H K : Subgroup G) : conjBy w (H ⊓ K) = conjBy w H ⊓ conjBy w K := by
  unfold conjBy
  exact Subgroup.map_inf _ _ _ (MulAut.conj w).injective

omit [Finite G] in
theorem conjBy_le_conjBy_iff (w : G) {H K : Subgroup G} : conjBy w H ≤ conjBy w K ↔ H ≤ K := by
  unfold conjBy
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj w).injective

omit [Finite G] in
theorem conjBy_bot (w : G) : conjBy w (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

omit [Finite G] in
theorem commClause_of_conj {p : ℕ} {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {s t : MulAut E}
    (h : kZero p E (conjAut E w hw * s * (conjAut E w hw)⁻¹) ≤
        Subgroup.centralizer (kZero p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) : Set G) ∧
      kZero p E (conjAut E w hw * s * (conjAut E w hw)⁻¹) ⊓
        kZero p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) = ⊥) :
    kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧ kZero p E s ⊓ kZero p E t = ⊥ := by
  obtain ⟨h1, h2⟩ := h
  rw [kZero_conj p s hw, kZero_conj p t hw,
    Equivariance.centralizer_conjBy] at h1
  rw [kZero_conj p s hw, kZero_conj p t hw, ← conjBy_inf] at h2
  refine ⟨(conjBy_le_conjBy_iff w).1 h1, le_antisymm ?_ bot_le⟩
  refine (conjBy_le_conjBy_iff w).1 ?_
  rw [h2, conjBy_bot]

end CFSG.RankThree.PartOne.K1320
