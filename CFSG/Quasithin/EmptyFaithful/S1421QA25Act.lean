module

public import CFSG.Quasithin.EmptyFaithful.S1421QA25Defs
public import CFSG.Quasithin.Vol2.Ch1Quotient
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

namespace QA25

section Act

theorem conj_injective_of_center_eq_bot {M : Type*} [Group M] (h : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  intro a b hab
  have h1 : ∀ y : M, a * y * a⁻¹ = b * y * b⁻¹ := fun y => by
    simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut M => φ y) hab
  have hz : a⁻¹ * b ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro y
    calc y * (a⁻¹ * b) = a⁻¹ * (a * y * a⁻¹) * b := by group
      _ = a⁻¹ * (b * y * b⁻¹) * b := by rw [h1 y]
      _ = a⁻¹ * b * y := by group
  rw [h, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.mp hz)

theorem conj_bijective_of_isSporadic_M23
    {Y : Type} [Group Y] (h : IsSporadic .M23 Y) :
    Function.Bijective (MulAut.conj : Y →* MulAut Y) := by
  obtain ⟨e0⟩ := h
  let e : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := e0
  have hc : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M23 = ⊥ :=
    CFSG.Sporadic.Schreier.m23_center_eq_bot'
  have hinj := conj_injective_of_center_eq_bot hc
  have key : ∀ (c : Y) (z : ↥CFSG.Blueprint.NativeSporadic.M23),
      (MulAut.conj (e c) : MulAut _) z = e ((MulAut.conj c : MulAut Y) (e.symm z)) := by
    intro c z
    simp [MulAut.conj_apply]
  refine ⟨fun a b hab => ?_, fun α => ?_⟩
  · refine e.injective (hinj (MulEquiv.ext fun z => ?_))
    rw [key, key, hab]
  · obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Ch1.m23_all_inner (e.symm.trans (α.trans e))
    refine ⟨e.symm g, MulEquiv.ext fun y => e.injective ?_⟩
    have h1 : (MulAut.conj g : MulAut ↥CFSG.Blueprint.NativeSporadic.M23) (e y) =
        (e.symm.trans (α.trans e)) (e y) := by rw [hg]
    have h2 : g * e y * g⁻¹ = e (α y) := by simpa [MulAut.conj_apply] using h1
    have h3 : e ((MulAut.conj (e.symm g) : MulAut Y) y) = g * e y * g⁻¹ := by
      simp [MulAut.conj_apply]
    rw [h3, h2]

theorem eq_of_le_of_odd_index {Y : Type*} [Group Y] [Finite Y] {S₀ S : Subgroup Y}
    (hle : S₀ ≤ S) (hS : IsPGroup 2 ↥S) (hodd : ¬ 2 ∣ S₀.index) : S₀ = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have h1 : (S₀.subgroupOf S).index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : S₀.relIndex S ∣ S₀.index := Subgroup.relIndex_dvd_index_of_le hle
  have hm0 : m = 0 := by
    by_contra hm0
    apply hodd
    refine dvd_trans ?_ h2
    show 2 ∣ (S₀.subgroupOf S).index
    rw [hm]
    exact dvd_pow_self 2 hm0
  have h3 : S₀.relIndex S = 1 := by
    show (S₀.subgroupOf S).index = 1
    rw [hm, hm0, pow_zero]
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h3)

theorem exists_stable_of_m23
    (hM : M23L34Diagram) {X : Type} [Group X] [Finite X] {Tb M A : Subgroup X}
    (hTb : IsPGroup 2 ↥Tb) (hSM : IsSylowTwoOf (Tb ⊓ M) M) (hM23 : IsSporadic .M23 ↥M)
    (hA : IsPSL 3 2 2 ↥A) (hAM : A ≤ M) (hTM : Tb ≤ Subgroup.normalizer (M : Set X))
    (hTA : Tb ≤ Subgroup.normalizer (A : Set X)) :
    ∃ P : Subgroup X, P ≤ A ∧ P ≠ A ∧ (∀ Q : Subgroup X, Q ≤ A → P ≤ Q → Q = P ∨ Q = A) ∧
      A ⊓ Subgroup.normalizer ((Tb ⊓ A : Subgroup X) : Set X) ≤ P ∧
      Tb ≤ Subgroup.normalizer (P : Set X) := by
  obtain ⟨hinj, hsurj⟩ := conj_bijective_of_isSporadic_M23 hM23
  let ρ : ↥Tb →* MulAut ↥M := M.normalizerMonoidHom.comp (Subgroup.inclusion hTM)
  have hρ : ∀ (t : ↥Tb) (y : ↥M), ((ρ t y : ↥M) : X) = (t : X) * (y : X) * (t : X)⁻¹ :=
    fun t y => rfl
  let e : ↥M ≃* MulAut ↥M := MulEquiv.ofBijective MulAut.conj ⟨hinj, hsurj⟩
  let φ : ↥Tb →* ↥M := e.symm.toMonoidHom.comp ρ
  have hφ : ∀ t : ↥Tb, MulAut.conj (φ t) = ρ t := fun t => e.apply_symm_apply (ρ t)
  have hact : ∀ (t : ↥Tb) (y : ↥M),
      (((φ t) * y * (φ t)⁻¹ : ↥M) : X) = (t : X) * (y : X) * (t : X)⁻¹ := by
    intro t y
    have h1 := congrArg (fun α : MulAut ↥M => ((α y : ↥M) : X)) (hφ t)
    simpa [MulAut.conj_apply, hρ] using h1
  set S₀ : Subgroup ↥M := (Tb ⊓ M).subgroupOf M with hS₀def
  have hS₀ : IsSylowTwoOf S₀ ⊤ := isSylowTwoOf_top_subgroupOf hSM
  have hφS₀ : ∀ s : ↥M, s ∈ S₀ → ∀ hsT : (s : X) ∈ Tb, φ ⟨s, hsT⟩ = s := by
    intro s hs hsT
    apply hinj
    rw [hφ]
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [hρ]
    simp [MulAut.conj_apply]
  have hle : S₀ ≤ φ.range := by
    intro s hs
    have hsT : (s : X) ∈ Tb := ((Subgroup.mem_subgroupOf.mp hs).1)
    exact ⟨⟨s, hsT⟩, hφS₀ s hs hsT⟩
  have hφ2 : IsPGroup 2 ↥φ.range := hTb.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hodd : ¬ 2 ∣ S₀.index := by
    intro hd
    apply hS₀.2.2
    have h1 : (S₀.subgroupOf ⊤).index = S₀.index := Subgroup.relIndex_top_right S₀
    rw [h1]
    exact hd
  have hrange : S₀ = φ.range := eq_of_le_of_odd_index hle hφ2 hodd
  set A' : Subgroup ↥M := A.subgroupOf M with hA'def
  have hA' : IsPSL 3 2 2 ↥A' :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAM) hA
  have hS₀N : S₀ ≤ Subgroup.normalizer (A' : Set ↥M) := by
    intro s hs
    have hsT : (s : X) ∈ Tb := (Subgroup.mem_subgroupOf.mp hs).1
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    show (y : X) ∈ A ↔ ((s * y * s⁻¹ : ↥M) : X) ∈ A
    have := Subgroup.mem_normalizer_iff.mp (hTA hsT) (y : X)
    simpa using this
  have hnd := hM ↥M hM23 A' S₀ hA' hS₀ hS₀N
  obtain ⟨PM, hPM, hBM, hSPM⟩ : ∃ PM : Subgroup ↥M, IsMaxParabolic2 A' PM ∧
      A' ⊓ Subgroup.normalizer ((S₀ ⊓ A' : Subgroup ↥M) : Set ↥M) ≤ PM ∧
      S₀ ≤ Subgroup.normalizer (PM : Set ↥M) := by
    by_contra hcon
    exact hnd fun P hP hB hN => hcon ⟨P, hP, hB, hN⟩
  have hPMA : PM ≤ A' := hPM.1.1
  have hmapA : A'.map M.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAM]
  refine ⟨PM.map M.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmapA]
    exact Subgroup.map_mono hPMA
  · intro h
    exact hPM.2.1 (Subgroup.map_injective M.subtype_injective (h.trans hmapA.symm))
  · intro Q hQA hPQ
    have hQ'A : Q.subgroupOf M ≤ A' := fun x hx => hQA hx
    have hPQ' : PM ≤ Q.subgroupOf M := fun x hx => hPQ ⟨x, hx, rfl⟩
    have hpar : IsParabolic2 A' (Q.subgroupOf M) := by
      obtain ⟨-, S', hS', hS'B⟩ := hPM.1
      exact ⟨hQ'A, S', hS', hS'B.trans hPQ'⟩
    by_cases hQA' : Q.subgroupOf M = A'
    · right
      refine le_antisymm hQA fun a ha => ?_
      have h1 : (⟨a, hAM ha⟩ : ↥M) ∈ A' := ha
      rw [← hQA'] at h1
      exact h1
    · left
      have h2 := hPM.2.2 _ hpar hQA' hPQ'
      refine le_antisymm (fun q hq => ?_) hPQ
      have hqM : q ∈ M := hAM (hQA hq)
      have h1 : (⟨q, hqM⟩ : ↥M) ∈ Q.subgroupOf M := hq
      rw [h2] at h1
      exact ⟨⟨q, hqM⟩, h1, rfl⟩
  · rintro x ⟨hxA, hxN⟩
    have hxA' : x ∈ A := hxA
    have hxN' : x ∈ Subgroup.normalizer ((Tb ⊓ A : Subgroup X) : Set X) := hxN
    have hxmA : (⟨x, hAM hxA'⟩ : ↥M) ∈ A' := hxA'
    have key : ∀ z : ↥M, z ∈ S₀ ⊓ A' ↔ (z : X) ∈ Tb ⊓ A := by
      intro z
      simp only [Subgroup.mem_inf, hS₀def, Subgroup.mem_subgroupOf, hA'def]
      constructor
      · rintro ⟨⟨hT, -⟩, hAz⟩
        exact ⟨hT, hAz⟩
      · rintro ⟨hT, hAz⟩
        exact ⟨⟨hT, z.2⟩, hAz⟩
    have hxmN : (⟨x, hAM hxA'⟩ : ↥M) ∈ Subgroup.normalizer ((S₀ ⊓ A' : Subgroup ↥M) : Set ↥M) := by
      refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
      rw [key, key]
      have := Subgroup.mem_normalizer_iff.mp hxN' (y : X)
      simpa using this
    exact ⟨_, hBM ⟨hxmA, hxmN⟩, rfl⟩
  · intro t ht
    have hT' : ∀ t ∈ Tb, ∀ g ∈ PM.map M.subtype, t * g * t⁻¹ ∈ PM.map M.subtype := by
      intro t ht g hg
      obtain ⟨y, hy, rfl⟩ := hg
      have h1 : φ ⟨t, ht⟩ ∈ S₀ := by
        rw [hrange]
        exact ⟨⟨t, ht⟩, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp (hSPM h1) y).mp hy
      exact ⟨_, h2, hact ⟨t, ht⟩ y⟩
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨hT' t ht g, fun hg => ?_⟩
    have := hT' t⁻¹ (Tb.inv_mem ht) _ hg
    simpa [mul_assoc] using this

end Act

end QA25

end CFSG.Quasithin
