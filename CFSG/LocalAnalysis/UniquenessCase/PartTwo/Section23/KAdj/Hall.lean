module

public import Mathlib.GroupTheory.PGroup
import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

private theorem disjoint_of_pGroup_A03 {B : Type*} [Group B] {p : ℕ} [Fact p.Prime]
    {E T : Subgroup B} [Finite T] (hE : IsPGroup p E) (hT : ¬ p ∣ Nat.card T) :
    Disjoint E T := by
  rw [Subgroup.disjoint_def]
  rintro x hxE hxT
  by_contra hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hE) ⟨x, hxE⟩
  have hxk : orderOf x = p ^ k := by simpa only [Subgroup.orderOf_mk] using hk
  have hdiv : orderOf x ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T hxT
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hxk
    exact hx (orderOf_eq_one_iff.1 hxk)
  exact hT (dvd_trans (dvd_pow_self p hk0) (hxk ▸ hdiv))

private theorem disjoint_zpowers_of_pGroup_A03 {B : Type*} [Group B] {p : ℕ} [Fact p.Prime]
    {E : Subgroup B} (hE : IsPGroup p E) {t : B} (hto : ¬ p ∣ orderOf t) :
    Disjoint E (Subgroup.zpowers t) := by
  rw [Subgroup.disjoint_def]
  rintro x hxE hxt
  by_contra hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hE) ⟨x, hxE⟩
  have hxk : orderOf x = p ^ k := by simpa only [Subgroup.orderOf_mk] using hk
  have hdiv : orderOf x ∣ orderOf t := orderOf_dvd_of_mem_zpowers hxt
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hxk
    exact hx (orderOf_eq_one_iff.1 hxk)
  exact hto (dvd_trans (dvd_pow_self p hk0) (hxk ▸ hdiv))

private theorem exists_conj_of_top_A03 {B : Type*} [Group B] [Finite B] {p : ℕ} [Fact p.Prime]
    (E T : Subgroup B) [E.Normal] (hE : IsPGroup p E) (hT : ¬ p ∣ Nat.card T)
    (hsup : E ⊔ T = ⊤) (t : B) (hto : ¬ p ∣ orderOf t) :
    ∃ e ∈ E, e * t * e⁻¹ ∈ T := by
  have ht' : t ∈ (↑(E ⊔ T) : Set B) := by rw [hsup]; trivial
  rw [Subgroup.normal_mul] at ht'
  obtain ⟨e₀, he₀, τ, hτT, hmul⟩ := Set.mem_mul.1 ht'
  set Y : Subgroup B := Subgroup.zpowers t with hY
  set Z : Subgroup B := (E ⊔ Y) ⊓ T with hZ
  have hτt : τ = e₀⁻¹ * t := by rw [← hmul]; group
  have hτsup : τ ∈ E ⊔ Y := by
    rw [hτt]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left he₀))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hτZ : τ ∈ Z := by
    rw [hZ]
    exact Subgroup.mem_inf.mpr ⟨hτsup, hτT⟩
  have hZT : Z ≤ T := by rw [hZ]; exact inf_le_right
  have hZY : Z ≤ E ⊔ Y := by rw [hZ]; exact inf_le_left
  have hYZ : E ⊔ Y = E ⊔ Z := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [hY, Subgroup.zpowers_le, ← hmul]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he₀) (Subgroup.mem_sup_right hτZ)
    · exact sup_le le_sup_left hZY
  have hZp : ¬ p ∣ Nat.card Z := fun h =>
    hT (dvd_trans h (Subgroup.card_dvd_of_le hZT))
  have hEZ : Disjoint E Z := Disjoint.mono_right hZT (disjoint_of_pGroup_A03 hE hT)
  have hEY : Disjoint E Y := by
    rw [hY]
    exact disjoint_zpowers_of_pGroup_A03 hE hto
  obtain ⟨e, he, hconj⟩ :=
    CFSG.GH74.BNPair.exists_conj_of_complements hE hZp hEZ hEY hYZ
  refine ⟨e, he, ?_⟩
  have hmem : e * t * e⁻¹ ∈ Y.map (MulAut.conj e).toMonoidHom := by
    rw [Subgroup.mem_map]
    exact ⟨t, Subgroup.mem_zpowers t, by simp [MulAut.conj_apply]⟩
  rw [hconj] at hmem
  rw [hZ] at hmem
  exact hmem.2

theorem exists_conj_mem_of_mem_sup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E T : Subgroup G} (hET : T ≤ Subgroup.normalizer (E : Set G)) (hE : IsPGroup p E)
    (hT : ¬ p ∣ Nat.card T) {t : G} (ht : t ∈ E ⊔ T) (hto : ¬ p ∣ orderOf t) :
    ∃ e ∈ E, e * t * e⁻¹ ∈ T := by
  set B : Subgroup G := E ⊔ T with hB
  have hEB : E ≤ B := by rw [hB]; exact le_sup_left
  have hTB : T ≤ B := by rw [hB]; exact le_sup_right
  have hBN : B ≤ Subgroup.normalizer (E : Set G) := by
    rw [hB]
    exact sup_le Subgroup.le_normalizer hET
  haveI hEnorm : (E.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEB).2 hBN
  have hEBp : IsPGroup p (E.subgroupOf B) :=
    hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEB).symm
  have hTp : ¬ p ∣ Nat.card (T.subgroupOf B) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv]
    exact hT
  have hsup : E.subgroupOf B ⊔ T.subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hEB hTB]
    apply top_unique
    intro x _
    exact Subgroup.mem_subgroupOf.mpr (hB ▸ x.2)
  have htB : t ∈ B := by rw [hB]; exact ht
  have hord : ¬ p ∣ orderOf (⟨t, htB⟩ : B) := by rwa [Subgroup.orderOf_mk]
  obtain ⟨e', he', hmem⟩ :=
    exists_conj_of_top_A03 (E.subgroupOf B) (T.subgroupOf B) hEBp hTp hsup (⟨t, htB⟩ : B) hord
  refine ⟨((e' : B) : G), Subgroup.mem_subgroupOf.mp he', ?_⟩
  simpa using Subgroup.mem_subgroupOf.mp hmem

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
