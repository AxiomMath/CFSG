module

public import CFSG.RankThree.GF2n.Tim79a34Lemma12

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open
open scoped commutatorElement

theorem qe_derived_center {G : Type} [Group G] [Finite G] {P Q V A : Subgroup G}
    (hPQ : P ≤ Q) (hrel : P.relIndex Q = 2)
    (hA2 : Nat.card A = 2) (hAP : ⁅P, P⁆ = A) (hAn : ∀ q ∈ Q, ∀ x ∈ A, q * x * q⁻¹ ∈ A)
    (hPQA : ∀ x ∈ Q, ∀ p ∈ P, ⁅p, x⁆ ∈ A)
    (hAV : A ≤ V) (hVP : V ≤ P) (hV4 : Nat.card V = 4)
    (hCV : ∀ q ∈ Q, (∀ v ∈ V, q * v = v * q) → q ∈ P)
    (hCP : ∀ q ∈ Q, (∀ p ∈ P, q * p = p * q) → q ∈ V) :
    ⁅Q, Q⁆ = A ∧ (Subgroup.center ↥Q).map Q.subtype = A := by
  have hAP_le : A ≤ P := by
    rw [← hAP]
    refine Subgroup.commutator_le.mpr ?_
    intro x hx y hy
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  have hAQ : A ≤ Q := hAP_le.trans hPQ
  have hVQ : V ≤ Q := hVP.trans hPQ
  have hAcen : ∀ q ∈ Q, ∀ t ∈ A, q * t = t * q := by
    intro q hq t ht
    by_cases h1 : t = 1
    · subst h1
      simp
    · have hconj : q * t * q⁻¹ ∈ A := hAn q hq t ht
      have hne : q * t * q⁻¹ ≠ 1 := by
        intro h
        apply h1
        calc t = q⁻¹ * (q * t * q⁻¹) * q := by group
          _ = 1 := by rw [h]; group
      have heq : q * t * q⁻¹ = t := (l12_two_elt hA2 ht h1 _ hconj).resolve_left hne
      calc q * t = q * t * q⁻¹ * q := by group
        _ = t * q := by rw [heq]
  have hcomm_le : ⁅Q, Q⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    by_cases hxP : x ∈ P
    · exact hPQA y hy x hxP
    by_cases hyP : y ∈ P
    · have h := hPQA x hx y hyP
      have e : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact A.inv_mem h
    have hxy : x⁻¹ * y ∈ P := by
      have hx' : (⟨x, hx⟩ : ↥Q) ∉ P.subgroupOf Q := fun h => hxP (Subgroup.mem_subgroupOf.mp h)
      have hy' : (⟨y, hy⟩ : ↥Q) ∉ P.subgroupOf Q := fun h => hyP (Subgroup.mem_subgroupOf.mp h)
      have h : (⟨x, hx⟩ : ↥Q)⁻¹ * ⟨y, hy⟩ ∈ P.subgroupOf Q :=
        (Subgroup.mul_mem_iff_of_index_two hrel).mpr
          (iff_of_false (fun h => hx' ((P.subgroupOf Q).inv_mem_iff.mp h)) hy')
      exact Subgroup.mem_subgroupOf.mp h
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ P, y = x * p := ⟨x⁻¹ * y, hxy, by group⟩
    have ht : ⁅p, x⁆⁻¹ ∈ A := A.inv_mem (hPQA x hx p hp)
    have hc := hAn x hx _ ht
    have e2 : ⁅x, x * p⁆ = x * ⁅p, x⁆⁻¹ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact hc
  have hQP : ∃ c ∈ Q, c ∉ P := by
    by_contra hcon
    push Not at hcon
    have hPQeq : P = Q := le_antisymm hPQ hcon
    have h1 : P.relIndex Q = 1 := by
      rw [hPQeq]
      exact Subgroup.relIndex_self (H := Q)
    omega
  obtain ⟨c, hcQ, hcP⟩ := hQP
  have hvex : ∃ v ∈ V, c * v ≠ v * c := by
    by_contra hcon
    push Not at hcon
    exact hcP (hCV c hcQ hcon)
  obtain ⟨v, hvV, hcv⟩ := hvex
  have hvP : v ∈ P := hVP hvV
  have hvQ : v ∈ Q := hPQ hvP
  have ht_mem : ⁅v, c⁆ ∈ A := hPQA c hcQ v hvP
  have ht_ne : ⁅v, c⁆ ≠ 1 := by
    intro h
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact hcv h.symm
  have hA_le_comm : A ≤ ⁅Q, Q⁆ := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact Subgroup.one_mem _
    · have hav : a = ⁅v, c⁆ := (l12_two_elt hA2 ht_mem ht_ne a ha).resolve_left ha1
      rw [hav]
      exact Subgroup.commutator_mem_commutator hvQ hcQ
  have hpart1 : ⁅Q, Q⁆ = A := le_antisymm hcomm_le hA_le_comm
  have hpart2 : (Subgroup.center ↥Q).map Q.subtype = A := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      show (w : G) ∈ A
      have hzc : ∀ q ∈ Q, q * (w : G) = (w : G) * q := by
        intro q hq
        have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨q, hq⟩)
        simpa using h
      have hzV : (w : G) ∈ V := hCP (w : G) w.2 (fun p hp => (hzc p (hPQ hp)).symm)
      by_contra hzA
      have hvA : v ∉ A := fun h => hcv (hAcen c hcQ v h)
      have hidx : (A.subgroupOf V).index = 2 := by
        have h1 : Nat.card (A.subgroupOf V) = 2 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAV).toEquiv, hA2]
        have h2 := Subgroup.card_mul_index (H := A.subgroupOf V)
        rw [h1, hV4] at h2
        omega
      have hcos : (w : G)⁻¹ * v ∈ A := by
        have hx' : (⟨(w : G), hzV⟩ : ↥V) ∉ A.subgroupOf V :=
          fun h => hzA (Subgroup.mem_subgroupOf.mp h)
        have hy' : (⟨v, hvV⟩ : ↥V) ∉ A.subgroupOf V :=
          fun h => hvA (Subgroup.mem_subgroupOf.mp h)
        have h : (⟨(w : G), hzV⟩ : ↥V)⁻¹ * ⟨v, hvV⟩ ∈ A.subgroupOf V :=
          (Subgroup.mul_mem_iff_of_index_two hidx).mpr
            (iff_of_false (fun h => hx' ((A.subgroupOf V).inv_mem_iff.mp h)) hy')
        exact Subgroup.mem_subgroupOf.mp h
      apply hcv
      calc c * v = c * ((w : G) * ((w : G)⁻¹ * v)) := by group
        _ = (c * (w : G)) * ((w : G)⁻¹ * v) := by group
        _ = ((w : G) * c) * ((w : G)⁻¹ * v) := by rw [hzc c hcQ]
        _ = (w : G) * (c * ((w : G)⁻¹ * v)) := by group
        _ = (w : G) * (((w : G)⁻¹ * v) * c) := by rw [hAcen c hcQ _ hcos]
        _ = v * c := by group
    · intro a ha
      refine Subgroup.mem_map.mpr ⟨⟨a, hAQ ha⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hAcen g.1 g.2 a ha
  exact ⟨hpart1, hpart2⟩

theorem le_pCore_of_normal_inf {G : Type} [Group G] [Finite G] {M G₀ R : Subgroup G}
    [G₀.Normal] (hR : R ≤ M ⊓ G₀) (hRn : ∀ m ∈ M ⊓ G₀, ∀ r ∈ R, m * r * m⁻¹ ∈ R)
    (hR2 : IsPGroup 2 R) : R ≤ inSubgroup (pCore 2) M := by
  set M₀ : Subgroup G := M ⊓ G₀ with hM₀
  set D : Subgroup G := inSubgroup (pCore 2) M₀ with hD
  obtain ⟨hD2, hDM₀, hM₀D⟩ := inSubgroup_pCore_two M₀
  have hRN : M₀ ≤ Subgroup.normalizer (R : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hRn m hm x hx
    · intro hx
      have h := hRn m⁻¹ (M₀.inv_mem hm) _ hx
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h
  have hRD : R ≤ D := Tim78.le_inSubgroup_pCore hR hRN hR2
  have hMM₀ : ∀ m ∈ M, ∀ y ∈ M₀, m * y * m⁻¹ ∈ M₀ := by
    intro m hm y hy
    exact Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hm (Subgroup.mem_inf.mp hy).1)
      (M.inv_mem hm), (inferInstance : G₀.Normal).conj_mem y (Subgroup.mem_inf.mp hy).2 m⟩
  have hMD : ∀ m ∈ M, ∀ x ∈ D, m * x * m⁻¹ ∈ D := by
    intro m hm x hx
    set D' : Subgroup G := D.map (MulAut.conj m).toMonoidHom with hD'
    have hD'M₀ : D' ≤ M₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact hMM₀ m hm y (hDM₀ hy)
    have hD'n : M₀ ≤ Subgroup.normalizer (D' : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have key : ∀ y ∈ M₀, ∀ z ∈ D', y * z * y⁻¹ ∈ D' := by
        intro y hy z hz
        obtain ⟨z', hz', rfl⟩ := hz
        have hy' : m⁻¹ * y * m ∈ M₀ := by
          have := hMM₀ m⁻¹ (M.inv_mem hm) y hy
          simpa using this
        refine ⟨(m⁻¹ * y * m) * z' * (m⁻¹ * y * m)⁻¹, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hM₀D hy') z').mp hz'
        · show m * ((m⁻¹ * y * m) * z' * (m⁻¹ * y * m)⁻¹) * m⁻¹ = y * (m * z' * m⁻¹) * y⁻¹
          group
      constructor
      · exact fun hz => key y hy z hz
      · intro hz
        have h := key y⁻¹ (M₀.inv_mem hy) _ hz
        rwa [show y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z by group] at h
    have hD'2 : IsPGroup 2 D' :=
      hD2.of_equiv (Subgroup.equivMapOfInjective D (MulAut.conj m).toMonoidHom
        (MulAut.conj m).injective)
    have hD'D : D' ≤ D := Tim78.le_inSubgroup_pCore hD'M₀ hD'n hD'2
    exact hD'D ⟨x, hx, rfl⟩
  have hMDn : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hMD m hm x hx
    · intro hx
      have h := hMD m⁻¹ (M.inv_mem hm) _ hx
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h
  have hDM : D ≤ M := hDM₀.trans inf_le_left
  exact hRD.trans (Tim78.le_inSubgroup_pCore hDM hMDn hD2)

end CFSG.RankThree.GF2n.Tim79a
