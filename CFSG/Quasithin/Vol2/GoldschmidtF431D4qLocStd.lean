module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCenter
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYam
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocRep
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructSyl

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.Yam

set_option linter.unusedSectionVars false


section Elementary

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem zC_mem_Ust : zC σ ∈ Ust σ := by
  refine Subgroup.mem_subgroupOf.mpr ?_
  show d4x₆ K 1 ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom
  rw [d4x₆_eq_d4v σ]
  exact d4v_mem_graphFixedPosUnipotent σ hσ (map_zero σ) (map_zero σ) (map_one σ)

include hσ in
theorem tC_mem_Ust : tC σ hσ ∈ Ust σ := by
  refine Subgroup.mem_subgroupOf.mpr ?_
  show d4x₄ K σ 1 ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom
  rw [d4x₄_eq_d4v σ]
  exact d4v_mem_graphFixedPosUnipotent σ hσ (map_zero σ) (map_zero σ) (map_zero σ)

theorem orderOf_zC : orderOf (zC σ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact zC_mul_self σ) (zC_ne_one σ)

theorem orderOf_tC : orderOf (tC σ hσ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact tC_mul_self σ hσ) (tC_ne_one σ hσ)

include hσ in
theorem cls_d4 : ∀ x : Cm σ, orderOf x = 2 → IsConj (zC σ) x ∨ IsConj (tC σ hσ) x := by
  intro x hx
  have hx2 : x * x = 1 := by
    rw [← sq, ← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  obtain ⟨y, hy, hyx⟩ := d4_classesCover σ hσ (z := zC σ) (t := tC σ hσ) rfl rfl x hx2 hx1
  rcases List.mem_cons.mp hy with rfl | hy'
  · exact Or.inl hyx
  · rw [List.mem_singleton.mp hy'] at hyx
    exact Or.inr hyx

include hσ in
theorem center_d4 {w : Cm σ} (hw : w ∈ Ust σ) (hc : ∀ y ∈ Ust σ, y * w = w * y) (hne : w ≠ 1) :
    ∃ h ∈ Pst0 σ ⊓ Pst1 σ, h * zC σ * h⁻¹ = w := by
  obtain ⟨f, hf, hw'⟩ := centre_Ust σ hσ hw (fun v hv => (hc v hv).symm)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne (Subtype.ext (by rw [hw', d4x₆_zero]; rfl))
  obtain ⟨h, hP0, hP1, hh⟩ := exists_torus_zC σ hσ hf hf0
  exact ⟨h, Subgroup.mem_inf.mpr ⟨hP0, hP1⟩, Subtype.ext (hh.trans hw'.symm)⟩

include hσ in
theorem cent_zC : Subgroup.centralizer ({zC σ} : Set (Cm σ)) ≤ Pst0 σ := fun _ hg =>
  centralizer_zC_le_Pst0 σ hσ (Subgroup.mem_centralizer_singleton_iff.mp hg)

include hσ in
theorem cent_tC : Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) ≤ Pst1 σ := fun _ hg =>
  centralizer_tC_le_Pst1 σ hσ (Subgroup.mem_centralizer_singleton_iff.mp hg)

end Elementary

theorem mem_of_mem_normalizer_of_isCoatom {C : Type*} [Group C] [IsSimpleGroup C]
    {P : Subgroup C} (hP : IsCoatom P) (hP0 : P ≠ ⊥) {g : C}
    (hg : g ∈ Subgroup.normalizer (P : Set C)) : g ∈ P := by
  by_contra hgP
  have hlt : P < Subgroup.normalizer (P : Set C) :=
    lt_of_le_of_ne Subgroup.le_normalizer (fun h => hgP (h ▸ hg))
  have htop : Subgroup.normalizer (P : Set C) = ⊤ := hP.2 _ hlt
  have hn : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact hP0 h
  · exact hP.1 h

theorem mem_normalizer_of_conj_mem_autStab {C : Type} [Group C] {P : Subgroup C} {g : C}
    (hg : MulAut.conj g ∈ autStab P) : g ∈ Subgroup.normalizer (P : Set C) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simpa [MulAut.conj_apply] using hg x

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
  (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσq in
theorem mem_Pst0_of_conj_mem_autStab {g : Cm σ} (hg : MulAut.conj g ∈ autStab (Pst0 σ)) :
    g ∈ Pst0 σ := by
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσq
  have := CFSG.Quasithin.H13.F431.D4q.Hex.d4_fixed_isSimpleGroup σ hf hK hσq
  obtain ⟨R, hR1, -, hR⟩ := hS.twoLoc₀
  have hRP : R ≤ Pst0 σ := by
    have : R ≤ Subgroup.normalizer (R : Set (Cm σ)) := Subgroup.le_normalizer
    rwa [← hR] at this
  have hne : Pst0 σ ≠ ⊥ := fun h => hR1 (le_bot_iff.mp (h ▸ hRP))
  exact mem_of_mem_normalizer_of_isCoatom hS.coatom₀ hne (mem_normalizer_of_conj_mem_autStab hg)

include hf hK hσq in
theorem mem_Pst1_of_conj_mem_autStab {g : Cm σ} (hg : MulAut.conj g ∈ autStab (Pst1 σ)) :
    g ∈ Pst1 σ := by
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσq
  have := CFSG.Quasithin.H13.F431.D4q.Hex.d4_fixed_isSimpleGroup σ hf hK hσq
  obtain ⟨R, hR1, -, hR⟩ := hS.twoLoc₁
  have hRP : R ≤ Pst1 σ := by
    have : R ≤ Subgroup.normalizer (R : Set (Cm σ)) := Subgroup.le_normalizer
    rwa [← hR] at this
  have hne : Pst1 σ ≠ ⊥ := fun h => hR1 (le_bot_iff.mp (h ▸ hRP))
  exact mem_of_mem_normalizer_of_isCoatom hS.coatom₁ hne (mem_normalizer_of_conj_mem_autStab hg)

include hf hK hσq in
theorem exists_conj_fieldActor_of_stab {φ : MulAut (Cm σ)} (h0 : φ ∈ autStab (Pst0 σ))
    (h1 : φ ∈ autStab (Pst1 σ)) :
    ∃ g ∈ Pst0 σ ⊓ Pst1 σ, ∃ δ : K ≃+* K, φ = MulAut.conj g * fieldActor σ δ := by
  obtain ⟨-, -, hex, -⟩ := exists_theta σ hf hK hσq
  obtain ⟨g, δ, hφ⟩ := hex φ
  have hconj : MulAut.conj g = φ * (fieldActor σ δ)⁻¹ := by
    rw [hφ]
    group
  have hg0 : MulAut.conj g ∈ autStab (Pst0 σ) :=
    hconj ▸ mul_mem h0 (inv_mem (fieldActor_mem_autStab_Pst0 σ hf hK hσq δ))
  have hg1 : MulAut.conj g ∈ autStab (Pst1 σ) :=
    hconj ▸ mul_mem h1 (inv_mem (fieldActor_mem_autStab_Pst1 σ hf hK hσq δ))
  exact ⟨g, Subgroup.mem_inf.mpr ⟨mem_Pst0_of_conj_mem_autStab σ hf hK hσq hg0,
    mem_Pst1_of_conj_mem_autStab σ hf hK hσq hg1⟩, δ, hφ⟩

include hf hK hσq in
theorem aut_zC {φ : MulAut (Cm σ)} (h0 : φ ∈ autStab (Pst0 σ)) (h1 : φ ∈ autStab (Pst1 σ)) :
    ∃ b ∈ Pst0 σ ⊓ Pst1 σ, φ (zC σ) = b * zC σ * b⁻¹ := by
  obtain ⟨g, hg, δ, rfl⟩ := exists_conj_fieldActor_of_stab σ hf hK hσq h0 h1
  exact ⟨g, hg, by rw [MulAut.mul_apply, fieldActor_zC, MulAut.conj_apply]⟩

include hσ hf hK hσq in
theorem aut_tC {φ : MulAut (Cm σ)} (h0 : φ ∈ autStab (Pst0 σ)) (h1 : φ ∈ autStab (Pst1 σ)) :
    ∃ b ∈ Pst0 σ ⊓ Pst1 σ, φ (tC σ hσ) = b * tC σ hσ * b⁻¹ := by
  obtain ⟨g, hg, δ, rfl⟩ := exists_conj_fieldActor_of_stab σ hf hK hσq h0 h1
  exact ⟨g, hg, by rw [MulAut.mul_apply, fieldActor_tC σ hσ, MulAut.conj_apply]⟩

end Aut

end CFSG.Quasithin.H13.F431.D4q.Loc
