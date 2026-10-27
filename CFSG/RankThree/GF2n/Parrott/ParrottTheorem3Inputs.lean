module

public import CFSG.RankThree.GF2n.Parrott.PSU6ElemAbelianNine
public import CFSG.RankThree.GF2n.Parrott.CaseIIIndex
public import CFSG.RankThree.GF2n.Parrott.Section1
public import CFSG.GroupTheory.SylowOfFusionTrivialCenter
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {w : K}
omit [Finite K] in
private theorem H_commute_w {y : K} (hy : y ∈ H w) : y * w = w * y :=
  Subgroup.mem_centralizer_singleton_iff.mp hy

omit [Finite K] in
private theorem mem_conjugate_iff_aux {S : Subgroup K} {g x : K} :
    x ∈ CFSG.conjugate S g ↔ g * x * g⁻¹ ∈ S := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ S
    rw [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
    exact hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group⟩

omit [Finite K] in
private theorem exists_isSylowOf_ge_aux {p : ℕ} {L P : Subgroup K} (hPL : P ≤ L)
    (hP : IsPGroup p P) : ∃ R : Subgroup K, IsSylowOf p R L ∧ P ≤ R := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := L)).exists_le_sylow
  exact ⟨(Q : Subgroup L).map L.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩⟩

section F2


theorem parrott_F2_of_hT3 (h : Tim79a.ParrottHypA w)
    (D : QuotientData (z := w) (J_subgroupOf_normal w))
    (hIII : ¬ ∃ σ₂ : ↥(H w), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hT3 : ∃ K₁ : Subgroup K, K₁.index = 2 ∧ K₁ ⊓ H w ≤ ⁅H w, H w⁆) :
    ∀ g : K, g * w * g⁻¹ ∈ H w → g * w * g⁻¹ ∈ ⁅H w, H w⁆ := by
  obtain ⟨K₁, hK₁i, hK₁H⟩ := hT3
  have hK₁n : K₁.Normal := Subgroup.normal_of_index_eq_two hK₁i
  have hJH := J_le_commutator_of_not_equalityBranch_A h D hIII
  have hH2 := relIndex_commutator_of_not_equalityBranch_A h D hIII
  have hH'H : ⁅H w, H w⁆ ≤ H w := Subgroup.commutator_le_self (H w)
  have hdvd : K₁.relIndex (H w) ∣ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal (H := K₁) (K := H w)
    rwa [hK₁i] at this
  have hr2 : K₁.relIndex (H w) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exfalso
      have hHK : H w ≤ K₁ := Subgroup.relIndex_eq_one.mp h1
      have : H w ≤ ⁅H w, H w⁆ := fun x hx => hK₁H ⟨hHK hx, hx⟩
      have h3 : ⁅H w, H w⁆.relIndex (H w) = 1 := Subgroup.relIndex_eq_one.mpr this
      omega
    · exact h1
  have hr2' : (K₁ ⊓ H w).relIndex (H w) = 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact hr2
  have h1 := Subgroup.relIndex_mul_relIndex (K₁ ⊓ H w) ⁅H w, H w⁆ (H w) hK₁H hH'H
  rw [hr2', hH2] at h1
  have h2 : (K₁ ⊓ H w).relIndex ⁅H w, H w⁆ = 1 := by omega
  have hH'K : ⁅H w, H w⁆ ≤ K₁ ⊓ H w := by
    have := Subgroup.relIndex_eq_one.mp h2
    exact this
  have hwK : w ∈ K₁ := (Subgroup.mem_inf.mp (hH'K (hJH (z_mem_J_A h)))).1
  intro g hg
  exact hK₁H ⟨hK₁n.conj_mem w hwK g, hg⟩

end F2

theorem exists_isConj_mem_parrottE
    (hne : ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤)) (hw : orderOf w = 2)
    (hJ : ∀ j ∈ J w, j ∉ Subgroup.zpowers w → ¬ IsConj w j)
    (hF2 : ∀ g : K, g * w * g⁻¹ ∈ H w → g * w * g⁻¹ ∈ ⁅H w, H w⁆)
    {E : Subgroup K}
    (hmeet : ∀ y ∈ H w, y * y = 1 → y ∉ J w → y ∈ ⁅H w, H w⁆ →
      ∃ x ∈ H w, x * y * x⁻¹ ∈ E) :
    ∃ y ∈ E, y ≠ w ∧ IsConj w y := by
  obtain ⟨y₀, ⟨g, hg⟩, hy₂, hyC, hyz⟩ := prop2_conj_centralizer hw hne
  have hyH : y₀ ∈ H w := hyC
  have hyy : y₀ * y₀ = 1 := by
    have := pow_orderOf_eq_one y₀
    rwa [hy₂, pow_two] at this
  have hyJ : y₀ ∉ J w := fun hyJ => hJ y₀ hyJ hyz (isConj_iff.mpr ⟨g, hg⟩)
  have hyH' : y₀ ∈ ⁅H w, H w⁆ := by
    have := hF2 g (hg ▸ hyH)
    rwa [hg] at this
  obtain ⟨x, hxH, hx⟩ := hmeet y₀ hyH hyy hyJ hyH'
  refine ⟨x * y₀ * x⁻¹, hx, ?_, isConj_iff.mpr ⟨x * g, ?_⟩⟩
  · intro h1
    apply hyz
    have : y₀ = w := by
      calc y₀ = x⁻¹ * (x * y₀ * x⁻¹) * x := by group
        _ = x⁻¹ * w * x := by rw [h1]
        _ = w := by
          have h2 : w * x = x * w := (H_commute_w hxH).symm
          calc x⁻¹ * w * x = x⁻¹ * (x * w) := by rw [mul_assoc, h2]
            _ = w := by group
    rw [this]
    exact Subgroup.mem_zpowers w
  · rw [← hg]
    group

theorem isSylowOf_top_of_isSylowOf_H_A (h : Tim79a.ParrottHypA w) {T : Subgroup K}
    (hT : IsSylowOf 2 T (H w)) : IsSylowOf 2 T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : J w ≤ T := by
    obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
    have hJQ : (J w).subgroupOf (H w) ≤ (Q : Subgroup ↥(H w)) := by
      rw [J_subgroupOf_eq_pCore]
      exact IsPGroup.le_sylow_of_normal pCore_isPGroup Q
    intro a ha
    have ha' : (⟨a, J_le_H ha⟩ : ↥(H w)) ∈ (Q : Subgroup ↥(H w)) :=
      hJQ (Subgroup.mem_subgroupOf.mpr ha)
    rw [hQ] at ha'
    exact Subgroup.mem_subgroupOf.mp ha'
  have hzT : w ∈ T := hJT (z_mem_J_A h)
  refine CFSG.GroupTheory.isSylowOf_of_fusion_trivial_center (p := 2) (z := w) (M := ⊤) (Y := T)
    ?_ ?_ ?_
  · simpa [H_eq_centralizer] using hT
  · refine Subgroup.mem_inf.mpr ⟨hzT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_iff.mp (z_centralizes_H_A (z := w)) t (hT.le ht)
  · intro g hg
    have haT : g * w * g⁻¹ ∈ T := (Subgroup.mem_inf.mp hg).1
    have haC : g * w * g⁻¹ ∈ Subgroup.centralizer (T : Set K) := (Subgroup.mem_inf.mp hg).2
    have haH : g * w * g⁻¹ ∈ H w := hT.le haT
    have haJ : g * w * g⁻¹ ∈ Subgroup.centralizer (J w : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_iff.mp haC j (hJT hj)
    have haZ : g * w * g⁻¹ ∈ centerIn (J w) := by
      rw [← centralizer_J_eq_centerIn_A h]
      exact Subgroup.mem_inf.mpr ⟨haH, haJ⟩
    rw [centerIn_J_eq_zpowers_A h] at haZ
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)).mp haZ with h1 | h1
    · exfalso
      have hz1 : w = 1 := by
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      have hzord := orderOf_z_A h
      rw [hz1, orderOf_one] at hzord
      norm_num at hzord
    · exact h1

theorem isElemAbelian_parrottE_of_hT3 (h : Tim79a.ParrottHypA w) {E : Subgroup K}
    (hM3 : ∀ E' : Subgroup K, E' ≤ H w → IsElemAbelian 2 E' → Nat.card E' = 2 ^ 9 →
      ∃ x ∈ H w, E' = CFSG.conjugate E x)
    (hT3 : ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
      (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
        Nonempty (↥K₁ ≃* X)) ∧ K₁ ⊓ H w ≤ ⁅H w, H w⁆) :
    IsElemAbelian 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₁, -, -, ⟨X, _, hX, ⟨e⟩⟩, -⟩ := hT3
  haveI : Finite X := Finite.of_equiv _ e.toEquiv
  obtain ⟨A, hA, hAcard⟩ := exists_isElemAbelian_card_two_pow_nine_of_lieModel_psu_six hX
  set A₂ : Subgroup K := (A.map e.symm.toMonoidHom).map K₁.subtype with hA₂
  have hA₂ab : IsElemAbelian 2 A₂ := (hA.map e.symm.toMonoidHom).map K₁.subtype
  have hA₂card : Nat.card A₂ = 2 ^ 9 := by
    rw [hA₂, Subgroup.card_map_of_injective K₁.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hAcard]
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H w)
  have hTtop := isSylowOf_top_of_isSylowOf_H_A h hT
  obtain ⟨R, hR, hA₂R⟩ := exists_isSylowOf_ge_aux (le_top : A₂ ≤ ⊤) hA₂ab.isPGroup
  obtain ⟨k, -, hk⟩ := hR.exists_mem_conj hTtop
  set A₃ : Subgroup K := A₂.map (MulAut.conj k).toMonoidHom with hA₃
  have hA₃ab : IsElemAbelian 2 A₃ := hA₂ab.map _
  have hA₃card : Nat.card A₃ = 2 ^ 9 := by
    rw [hA₃, Subgroup.card_map_of_injective (MulAut.conj k).injective, hA₂card]
  have hA₃T : A₃ ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    have : (MulAut.conj k).toMonoidHom a = k * a * k⁻¹ := rfl
    rw [this]
    refine (hk _).mpr ?_
    have h1 : k⁻¹ * (k * a * k⁻¹) * k = a := by group
    rw [h1]
    exact hA₂R ha
  obtain ⟨x, hxH, hx⟩ := hM3 A₃ (hA₃T.trans hT.le) hA₃ab hA₃card
  have hmem : ∀ a ∈ E, x⁻¹ * a * x ∈ A₃ := by
    intro a ha
    rw [hx, mem_conjugate_iff_aux]
    rw [show x * (x⁻¹ * a * x) * x⁻¹ = a by group]
    exact ha
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    have h1 := hA₃ab.comm (hmem a a.2) (hmem b b.2)
    show (a : K) * b = b * a
    calc (a : K) * b = x * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x) * (x⁻¹ * a * x)) * x⁻¹ := by rw [h1]
      _ = b * a := by group
  · have h1 := hA₃ab.mul_self_eq_one (hmem a ha)
    rw [pow_two]
    calc a * a = x * ((x⁻¹ * a * x) * (x⁻¹ * a * x)) * x⁻¹ := by group
      _ = 1 := by rw [h1]; group

end CFSG.RankThree.GF2n.Parrott
