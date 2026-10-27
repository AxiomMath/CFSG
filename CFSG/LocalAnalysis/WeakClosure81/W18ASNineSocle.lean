module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {Y : Type*} [Group Y]

structure SimpleSocleMod (Kk F : Subgroup Y) : Prop where
  normal_left : Kk.Normal
  normal_right : F.Normal
  le : Kk ≤ F
  eq_or_eq : ∀ T : Subgroup Y, Kk ≤ T → T ≤ F → (T.subgroupOf F).Normal → T = Kk ∨ T = F
  not_abelian : ∃ f₁ ∈ F, ∃ f₂ ∈ F, ⁅f₁, f₂⁆ ∉ Kk
  centralizer_le : ∀ y : Y, (∀ f ∈ F, ⁅y, f⁆ ∈ Kk) → y ∈ Kk

namespace SimpleSocleMod

variable {Kk F : Subgroup Y}

theorem le_sup_of_not_le (h : SimpleSocleMod Kk F) {N N₁ : Subgroup Y} (hN : N.Normal)
    (hN₁N : N₁ ≤ N) (hN₁ : (N₁.subgroupOf N).Normal) (hnot : ¬ N₁ ≤ Kk) :
    F ≤ N₁ ⊔ Kk := by
  haveI := h.normal_left
  haveI := h.normal_right
  haveI := hN
  have hFN : F ≤ N ⊔ Kk := by
    have hKT : Kk ≤ F ⊓ (N ⊔ Kk) := le_inf h.le le_sup_right
    have hTnorm : ((F ⊓ (N ⊔ Kk)).subgroupOf F).Normal :=
      Subgroup.Normal.subgroupOf inferInstance F
    rcases h.eq_or_eq _ hKT inf_le_left hTnorm with hT | hT
    · exfalso
      apply hnot
      have hNK : N ≤ Kk := by
        refine fun n hn => h.centralizer_le n fun f hf => ?_
        have h1 : ⁅n, f⁆ ∈ N := by
          have : ⁅n, f⁆ = n * (f * n⁻¹ * f⁻¹) := by simp only [commutatorElement_def, mul_assoc]
          rw [this]
          exact N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) f)
        have h2 : ⁅n, f⁆ ∈ F := by
          rw [commutatorElement_def]
          exact F.mul_mem (h.normal_right.conj_mem f hf n) (F.inv_mem hf)
        have h3 : ⁅n, f⁆ ∈ F ⊓ (N ⊔ Kk) := ⟨h2, Subgroup.mem_sup_left h1⟩
        rw [hT] at h3
        exact h3
      exact hN₁N.trans hNK
    · exact inf_eq_left.mp hT
  have hcl : ∀ m ∈ N, ∀ p ∈ N₁ ⊔ Kk, m * p * m⁻¹ ∈ N₁ ⊔ Kk := by
    intro m hm p hp
    have hle : N₁ ⊔ Kk ≤ (N₁ ⊔ Kk).comap (MulAut.conj m).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun k hk => ?_)
      · rw [Subgroup.mem_comap]
        have := hN₁.conj_mem ⟨x, hN₁N hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
        exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 this)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right (h.normal_left.conj_mem k hk m)
    exact hle hp
  have hnormN : N ≤ Subgroup.normalizer ((N₁ ⊔ Kk : Subgroup Y) : Set Y) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · exact hcl m hm p
    · intro hp
      have := hcl m⁻¹ (N.inv_mem hm) _ hp
      simpa [mul_assoc] using this
  have hFnorm : F ≤ Subgroup.normalizer ((N₁ ⊔ Kk : Subgroup Y) : Set Y) :=
    hFN.trans (sup_le hnormN (le_sup_right.trans Subgroup.le_normalizer))
  have hKT₁ : Kk ≤ F ⊓ (N₁ ⊔ Kk) := le_inf h.le le_sup_right
  have hT₁norm : ((F ⊓ (N₁ ⊔ Kk)).subgroupOf F).Normal := by
    refine ⟨fun t ht f => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at ht ⊢
    refine ⟨(f * t * f⁻¹).2, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hFnorm f.2) (t : Y)).mp ht.2
  rcases h.eq_or_eq _ hKT₁ inf_le_left hT₁norm with hT | hT
  · exfalso
    apply hnot
    intro n₁ hn₁
    refine h.centralizer_le n₁ fun f hf => ?_
    have h1 : ⁅f, n₁⁆ ∈ F ⊓ (N₁ ⊔ Kk) := by
      refine ⟨?_, ?_⟩
      · have : ⁅f, n₁⁆ = f * (n₁ * f⁻¹ * n₁⁻¹) := by simp only [commutatorElement_def, mul_assoc]
        rw [this]
        exact F.mul_mem hf (h.normal_right.conj_mem f⁻¹ (F.inv_mem hf) n₁)
      · rw [commutatorElement_def]
        exact (N₁ ⊔ Kk).mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hFnorm hf) n₁).mp (Subgroup.mem_sup_left hn₁))
          ((N₁ ⊔ Kk).inv_mem (Subgroup.mem_sup_left hn₁))
    rw [hT] at h1
    have h2 := Kk.inv_mem h1
    rwa [commutatorElement_inv] at h2
  · exact inf_eq_left.mp hT

theorem exists_not_commute (h : SimpleSocleMod Kk F) {N N₁ N₂ : Subgroup Y} (hN : N.Normal)
    (hN₁N : N₁ ≤ N) (hN₁ : (N₁.subgroupOf N).Normal) (hN₂N : N₂ ≤ N)
    (hN₂ : (N₂.subgroupOf N).Normal) (h₁ : ¬ N₁ ≤ Kk) (h₂ : ¬ N₂ ≤ Kk) :
    ∃ x ∈ N₁, ∃ y ∈ N₂, x * y ≠ y * x := by
  by_contra hcomm
  have hcomm' : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x := fun x hx y hy =>
    by_contra fun hne => hcomm ⟨x, hx, y, hy, hne⟩
  haveI := h.normal_left
  have h1 := h.le_sup_of_not_le hN hN₁N hN₁ h₁
  have h2 := h.le_sup_of_not_le hN hN₂N hN₂ h₂
  obtain ⟨f₁, hf₁, f₂, hf₂, hnk⟩ := h.not_abelian
  obtain ⟨x₁, hx₁, k₁, hk₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h1 hf₁)
  obtain ⟨x₂, hx₂, k₂, hk₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h2 hf₂)
  apply hnk
  have e₁ : (QuotientGroup.mk' Kk) k₁ = 1 := (QuotientGroup.eq_one_iff k₁).mpr hk₁
  have e₂ : (QuotientGroup.mk' Kk) k₂ = 1 := (QuotientGroup.eq_one_iff k₂).mpr hk₂
  have hq : (QuotientGroup.mk' Kk) ⁅x₁ * k₁, x₂ * k₂⁆ = 1 := by
    rw [map_commutatorElement, map_mul, map_mul, e₁, e₂, mul_one, mul_one,
      ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr
        (hcomm' x₁ hx₁ x₂ hx₂), map_one]
  exact (QuotientGroup.eq_one_iff _).mp hq

theorem exists_conj_normalClosure (h : SimpleSocleMod Kk F) {a : Y} (ha : a ∉ Kk)
    (hc : ∀ c d : Y, IsConj a c → IsConj a d →
      c * d = d * c ∨ ∃ z ∈ Subgroup.closure ({c, d} : Set Y), d = z * c * z⁻¹) :
    ∀ y : Y, ∃ n ∈ Subgroup.normalClosure ({a} : Set Y), y * a * y⁻¹ = n * a * n⁻¹ := by
  intro y
  by_contra hne
  obtain ⟨b, hb⟩ : ∃ b : Y, b = y * a * y⁻¹ := ⟨_, rfl⟩
  have hne' : ∀ n ∈ Subgroup.normalClosure ({a} : Set Y), b ≠ n * a * n⁻¹ :=
    fun n hn hEq => hne ⟨n, hn, hb ▸ hEq⟩
  set N : Subgroup Y := Subgroup.normalClosure ({a} : Set Y) with hNdef
  haveI hN : N.Normal := Subgroup.normalClosure_normal
  have haN : a ∈ N := Subgroup.subset_normalClosure rfl
  have hbN : b ∈ N := by rw [hb]; exact hN.conj_mem a haN y
  have hstable : ∀ (S : Set Y), (∀ m ∈ N, ∀ s ∈ S, m * s * m⁻¹ ∈ S) →
      ∀ m ∈ N, ∀ p ∈ Subgroup.closure S, m * p * m⁻¹ ∈ Subgroup.closure S := by
    intro S hS m hm p hp
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact Subgroup.subset_closure (hS m hm s hs)
    exact hle hp
  set S₁ : Set Y := {x | ∃ n ∈ N, x = n * a * n⁻¹} with hS₁def
  set S₂ : Set Y := {x | ∃ n ∈ N, x = n * b * n⁻¹} with hS₂def
  have hS₁stable : ∀ m ∈ N, ∀ s ∈ S₁, m * s * m⁻¹ ∈ S₁ := by
    rintro m hm _ ⟨n, hn, rfl⟩
    exact ⟨m * n, N.mul_mem hm hn, by simp [mul_assoc]⟩
  have hS₂stable : ∀ m ∈ N, ∀ s ∈ S₂, m * s * m⁻¹ ∈ S₂ := by
    rintro m hm _ ⟨n, hn, rfl⟩
    exact ⟨m * n, N.mul_mem hm hn, by simp [mul_assoc]⟩
  have hS₁N : S₁ ⊆ N := by
    rintro _ ⟨n, hn, rfl⟩
    exact hN.conj_mem a haN n
  have hS₂N : S₂ ⊆ N := by
    rintro _ ⟨n, hn, rfl⟩
    exact hN.conj_mem b hbN n
  have hN₁N : Subgroup.closure S₁ ≤ N := (Subgroup.closure_le N).mpr hS₁N
  have hN₂N : Subgroup.closure S₂ ≤ N := (Subgroup.closure_le N).mpr hS₂N
  have hN₁norm : ((Subgroup.closure S₁).subgroupOf N).Normal :=
    ⟨fun x hx g => hstable S₁ hS₁stable g g.2 x hx⟩
  have hN₂norm : ((Subgroup.closure S₂).subgroupOf N).Normal :=
    ⟨fun x hx g => hstable S₂ hS₂stable g g.2 x hx⟩
  have hnot₁ : ¬ Subgroup.closure S₁ ≤ Kk := fun hle =>
    ha (hle (Subgroup.subset_closure ⟨1, N.one_mem, by simp⟩))
  have hnot₂ : ¬ Subgroup.closure S₂ ≤ Kk := fun hle => by
    have hbK : b ∈ Kk := hle (Subgroup.subset_closure ⟨1, N.one_mem, by simp⟩)
    apply ha
    have := h.normal_left.conj_mem b hbK y⁻¹
    simpa [hb, mul_assoc] using this
  have hgen : ∀ c ∈ S₁, ∀ d ∈ S₂, c * d = d * c := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
    have hc1 : IsConj a (n * a * n⁻¹) := isConj_iff.2 ⟨n, rfl⟩
    have hc2 : IsConj a (m * b * m⁻¹) := isConj_iff.2 ⟨m * y, by rw [hb]; simp [mul_assoc]⟩
    rcases hc _ _ hc1 hc2 with hcomm | ⟨z, hz, hzeq⟩
    · exact hcomm
    · exfalso
      have hzN : z ∈ N := by
        refine (Subgroup.closure_le N).mpr ?_ hz
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact hN.conj_mem a haN n
        · exact hN.conj_mem b hbN m
      apply hne' (m⁻¹ * z * n) (N.mul_mem (N.mul_mem (N.inv_mem hm) hzN) hn)
      calc b = m⁻¹ * (m * b * m⁻¹) * m := by simp [mul_assoc]
        _ = m⁻¹ * (z * (n * a * n⁻¹) * z⁻¹) * m := by rw [hzeq]
        _ = (m⁻¹ * z * n) * a * (m⁻¹ * z * n)⁻¹ := by simp [mul_assoc]
  have hstep1 : ∀ c ∈ S₁, ∀ y' ∈ Subgroup.closure S₂, c * y' = y' * c := by
    intro c hc y' hy'
    have hle : Subgroup.closure S₂ ≤ Subgroup.centralizer ({c} : Set Y) := by
      rw [Subgroup.closure_le]
      intro d hd
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hgen _ hc d hd
    have := hle hy'
    rw [Subgroup.mem_centralizer_iff] at this
    exact this c (Set.mem_singleton c)
  have hcomm_closure : ∀ x ∈ Subgroup.closure S₁, ∀ y' ∈ Subgroup.closure S₂, x * y' = y' * x := by
    intro x hx y' hy'
    have hle : Subgroup.closure S₁ ≤ Subgroup.centralizer ({y'} : Set Y) := by
      rw [Subgroup.closure_le]
      intro c hc
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (hstep1 c hc w hy').symm
    have := hle hx
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this y' (Set.mem_singleton y')).symm
  obtain ⟨x, hx, y', hy', hne2⟩ :=
    h.exists_not_commute hN hN₁N hN₁norm hN₂N hN₂norm hnot₁ hnot₂
  exact hne2 (hcomm_closure x hx y' hy')

theorem map {Y' : Type*} [Group Y'] (h : SimpleSocleMod Kk F) (π : Y →* Y')
    (hπ : Function.Surjective π) (hker : π.ker ≤ Kk) :
    SimpleSocleMod (Kk.map π) (F.map π) := by
  have hmem : ∀ x : Y, π x ∈ Kk.map π ↔ x ∈ Kk := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
      have hmem' : k⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
      have h2 := Kk.mul_mem hk (hker hmem')
      simpa using h2
    · intro hx
      exact Subgroup.mem_map_of_mem π hx
  refine
    { normal_left := h.normal_left.map π hπ
      normal_right := h.normal_right.map π hπ
      le := Subgroup.map_mono h.le
      eq_or_eq := ?_
      not_abelian := ?_
      centralizer_le := ?_ }
  · intro T' hKT' hT'F hT'norm
    have hKT : Kk ≤ T'.comap π ⊓ F := fun k hk =>
      ⟨hKT' (Subgroup.mem_map_of_mem π hk), h.le hk⟩
    have hTnorm : ((T'.comap π ⊓ F).subgroupOf F).Normal := by
      refine ⟨fun t ht f => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap] at ht ⊢
      refine ⟨?_, (f * t * f⁻¹).2⟩
      have := hT'norm.conj_mem ⟨π (t : Y), Subgroup.mem_map_of_mem π t.2⟩ ht.1
        ⟨π (f : Y), Subgroup.mem_map_of_mem π f.2⟩
      have key : π (((f * t * f⁻¹ : ↥F)) : Y) =
          (((⟨π (f : Y), Subgroup.mem_map_of_mem π f.2⟩ : ↥(F.map π)) *
            ⟨π (t : Y), Subgroup.mem_map_of_mem π t.2⟩ *
            (⟨π (f : Y), Subgroup.mem_map_of_mem π f.2⟩ : ↥(F.map π))⁻¹ : ↥(F.map π)) : Y') := by
        simp
      rw [key]
      exact this
    rcases h.eq_or_eq _ hKT inf_le_right hTnorm with hT | hT
    · left
      refine le_antisymm ?_ hKT'
      intro y' hy'
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp (hT'F hy')
      have : f ∈ T'.comap π ⊓ F := ⟨hy', hf⟩
      rw [hT] at this
      exact Subgroup.mem_map_of_mem π this
    · right
      refine le_antisymm hT'F ?_
      intro y' hy'
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hy'
      have : f ∈ T'.comap π ⊓ F := by rw [hT]; exact hf
      exact this.1
  · obtain ⟨f₁, hf₁, f₂, hf₂, hnk⟩ := h.not_abelian
    refine ⟨π f₁, Subgroup.mem_map_of_mem π hf₁, π f₂, Subgroup.mem_map_of_mem π hf₂, ?_⟩
    rw [← map_commutatorElement, hmem]
    exact hnk
  · intro y' hy'
    obtain ⟨y, rfl⟩ := hπ y'
    refine (hmem y).2 (h.centralizer_le y fun f hf => (hmem _).1 ?_)
    rw [map_commutatorElement]
    exact hy' (π f) (Subgroup.mem_map_of_mem π hf)

end SimpleSocleMod

theorem exists_hom_subgroupOf_of_le_sup {Kk F N : Subgroup Y} (hN : N.Normal) (hKF : Kk ≤ F)
    (hFN : F ≤ N ⊔ Kk) {S : Type*} [Group S] {φ : ↥F →* S} (hφ : Function.Surjective φ)
    (hker : ∀ k : ↥F, φ k = 1 ↔ (k : Y) ∈ Kk) :
    ∃ ψ : ↥(F.subgroupOf N) →* S, Function.Surjective ψ ∧
      ∀ k : ↥(F.subgroupOf N), ψ k = 1 ↔ ((k : ↥N) : Y) ∈ Kk := by
  haveI := hN
  let ι : ↥(F.subgroupOf N) →* ↥F :=
    ((N.subtype).comp (F.subgroupOf N).subtype).codRestrict F (fun k => k.2)
  refine ⟨φ.comp ι, ?_, fun k => hker (ι k)⟩
  intro s
  obtain ⟨f, rfl⟩ := hφ s
  obtain ⟨n, hn, κ, hκ, hnκ⟩ := Subgroup.mem_sup_of_normal_left.mp (hFN f.2)
  have hκF : κ⁻¹ ∈ F := F.inv_mem (hKF hκ)
  have hn' : n = (f : Y) * κ⁻¹ := by rw [← hnκ]; simp
  have hnF : n ∈ F := by
    rw [hn']
    exact F.mul_mem f.2 hκF
  refine ⟨⟨⟨n, hn⟩, hnF⟩, ?_⟩
  have h1 : (⟨n, hnF⟩ : ↥F) = f * ⟨κ⁻¹, hκF⟩ := Subtype.ext hn'
  show φ ⟨n, hnF⟩ = φ f
  rw [h1, map_mul, (hker ⟨κ⁻¹, hκF⟩).2 (Kk.inv_mem hκ), mul_one]

theorem exists_hom_map_of_ker_le {Y' : Type*} [Group Y'] {Kk F : Subgroup Y} (π : Y →* Y')
    (hker : π.ker ≤ Kk) (hKF : Kk ≤ F) {S : Type*} [Group S] {φ : ↥F →* S}
    (hφ : Function.Surjective φ) (hker' : ∀ k : ↥F, φ k = 1 ↔ (k : Y) ∈ Kk) :
    ∃ ψ : ↥(F.map π) →* S, Function.Surjective ψ ∧
      ∀ k : ↥(F.map π), ψ k = 1 ↔ (k : Y') ∈ Kk.map π := by
  have hπF : Function.Surjective (π.subgroupMap F) := π.subgroupMap_surjective F
  have hle : (π.subgroupMap F).ker ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [hker']
    apply hker
    rw [MonoidHom.mem_ker]
    have := congrArg Subtype.val hk
    simpa using this
  set ψ := (π.subgroupMap F).liftOfSurjective hπF ⟨φ, hle⟩ with hψ
  have hψapp : ∀ k : ↥F, ψ (π.subgroupMap F k) = φ k := fun k => by
    simp [ψ]
  refine ⟨ψ, ?_, ?_⟩
  · intro s
    obtain ⟨k, rfl⟩ := hφ s
    exact ⟨π.subgroupMap F k, hψapp k⟩
  · intro r
    obtain ⟨k, rfl⟩ := hπF r
    rw [hψapp, hker']
    have hcoe : ((π.subgroupMap F k : ↥(F.map π)) : Y') = π (k : Y) := rfl
    rw [hcoe]
    constructor
    · intro hk
      exact Subgroup.mem_map_of_mem π hk
    · intro hk
      obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp hk
      have hmem : (k' : Y)⁻¹ * (k : Y) ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkk', inv_mul_cancel]
      have h2 := Kk.mul_mem hk' (hker hmem)
      simpa using h2

end CFSG.LocalAnalysis.WeakClosure81

end
