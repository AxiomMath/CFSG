module

public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Defs
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.OddCentralQuot
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.SzTriple
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.SzSqRoot
public import CFSG.Quasithin.Background.F7TwoInvBenderInner

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

theorem exists_mem_closure_mk_eq {X : Type} [Group X] (N : Subgroup X) [N.Normal]
    {a b c : X} {γ : X ⧸ N}
    (hγ : γ ∈ Subgroup.closure ({(a : X ⧸ N), (b : X ⧸ N), (c : X ⧸ N)} : Set (X ⧸ N))) :
    ∃ g ∈ Subgroup.closure ({a, b, c} : Set X), (g : X ⧸ N) = γ := by
  have hle : Subgroup.closure ({(a : X ⧸ N), (b : X ⧸ N), (c : X ⧸ N)} : Set (X ⧸ N)) ≤
      (Subgroup.closure ({a, b, c} : Set X)).map (QuotientGroup.mk' N) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
  obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.mp (hle hγ)
  exact ⟨g, hg, by simpa using hgγ⟩

variable {X : Type} [Group X]

private theorem mk_conj {t c : X} {c' : X ⧸ fusionZStar X}
    (hc : (c : X ⧸ fusionZStar X) = c') :
    ((c⁻¹ * t * c : X) : X ⧸ fusionZStar X) = c'⁻¹ * (t : X ⧸ fusionZStar X) * c' := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc]

private theorem conj_mul_self_eq_one {Y : Type} [Group Y] {s c : Y} (hs : s * s = 1) :
    (c⁻¹ * s * c) * (c⁻¹ * s * c) = 1 := by
  calc (c⁻¹ * s * c) * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c := by group
    _ = 1 := by rw [hs]; group

private theorem conj_ne_one {Y : Type} [Group Y] {s c : Y} (hs : s ≠ 1) :
    c⁻¹ * s * c ≠ 1 := by
  intro h
  apply hs
  have hconj : c * (c⁻¹ * s * c) * c⁻¹ = s := by group
  rw [h] at hconj
  simpa using hconj.symm

private theorem fusionZStar_setup [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    (hodd : fusionOddCore X ≤ Subgroup.center X) {t : X} (ht : t * t = 1) (ht1 : t ≠ 1) :
    fusionZStar X ≤ Subgroup.center X ∧ Odd (Nat.card (fusionZStar X)) ∧
      (t : X ⧸ fusionZStar X) * (t : X ⧸ fusionZStar X) = 1 ∧
      (t : X ⧸ fusionZStar X) ≠ 1 := by
  have hZc := fusionZStar_le_center hO2 hodd
  have hZodd := odd_card_fusionZStar hO2 hodd
  have hs : (t : X ⧸ fusionZStar X) * (t : X ⧸ fusionZStar X) = 1 := by
    rw [← QuotientGroup.mk_mul, ht, QuotientGroup.mk_one]
  have hs1 : (t : X ⧸ fusionZStar X) ≠ 1 := by
    intro h1
    exact not_mem_of_mul_self hZodd ht ht1 ((QuotientGroup.eq_one_iff t).mp h1)
  exact ⟨hZc, hZodd, hs, hs1⟩

private theorem exists_sqroot_mem_closure_of_benderType [Finite X]
    (hO2 : CFSG.pCore 2 X = ⊥)
    (hodd : fusionOddCore X ≤ Subgroup.center X) {n : ℕ}
    (hS : BenderType (X ⧸ fusionZStar X) n 2 1) {t : X} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ c₂' c₃' γ : X ⧸ fusionZStar X,
      γ * γ = (t : X ⧸ fusionZStar X) ∧
      γ ∈ Subgroup.closure ({(t : X ⧸ fusionZStar X),
          c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂',
          c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃'} : Set (X ⧸ fusionZStar X)) ∧
      (t : X ⧸ fusionZStar X) * (c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂') =
        c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂' * (t : X ⧸ fusionZStar X) ∧
      c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂' ≠ (t : X ⧸ fusionZStar X) ∧
      (t : X ⧸ fusionZStar X) * (c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃') ≠
        c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃' * (t : X ⧸ fusionZStar X) ∧
      c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂' * (c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃') ≠
        c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃' *
          (c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂') := by
  obtain ⟨-, -, hs, hs1⟩ := fusionZStar_setup hO2 hodd ht ht1
  obtain ⟨c₂', c₃', hcomm', hne', hnc₁₃', hnc₂₃'⟩ :=
    exists_szTriple (S := X ⧸ fusionZStar X) hS hs hs1
  have h₂ := conj_mul_self_eq_one (c := c₂') hs
  have h₃ := conj_mul_self_eq_one (c := c₃') hs
  have h₂' := conj_ne_one (c := c₂') hs1
  obtain ⟨γ, hγmem, hγsq⟩ :=
    exists_mul_self_eq_of_mem_closure (S := X ⧸ fusionZStar X) hS hs hs1 h₂ h₂' hcomm' hne' h₃
      hnc₁₃'
  exact ⟨c₂', c₃', γ, hγsq, hγmem, hcomm', hne', hnc₁₃', hnc₂₃'⟩

private theorem conj_relations_of_mk (hZc : fusionZStar X ≤ Subgroup.center X)
    (hZodd : Odd (Nat.card (fusionZStar X))) {t c₂ c₃ : X} (ht : t * t = 1)
    {c₂' c₃' : X ⧸ fusionZStar X} (hc₂ : (c₂ : X ⧸ fusionZStar X) = c₂')
    (hc₃ : (c₃ : X ⧸ fusionZStar X) = c₃')
    (hcomm' : (t : X ⧸ fusionZStar X) * (c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂') =
      c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂' * (t : X ⧸ fusionZStar X))
    (hne' : c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂' ≠ (t : X ⧸ fusionZStar X))
    (hnc₁₃' : (t : X ⧸ fusionZStar X) * (c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃') ≠
      c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃' * (t : X ⧸ fusionZStar X))
    (hnc₂₃' : c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂' *
        (c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃') ≠
      c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃' * (c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂')) :
    t * (c₂⁻¹ * t * c₂) = (c₂⁻¹ * t * c₂) * t ∧ c₂⁻¹ * t * c₂ ≠ t ∧
      t * (c₃⁻¹ * t * c₃) ≠ (c₃⁻¹ * t * c₃) * t ∧
      (c₂⁻¹ * t * c₂) * (c₃⁻¹ * t * c₃) ≠ (c₃⁻¹ * t * c₃) * (c₂⁻¹ * t * c₂) := by
  have ht₂coe := mk_conj (t := t) hc₂
  have ht₃coe := mk_conj (t := t) hc₃
  have ht₂sq : (c₂⁻¹ * t * c₂) * (c₂⁻¹ * t * c₂) = 1 := conj_mul_self_eq_one ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine commute_of_mk_commute hZc hZodd ht ht₂sq ?_
    rw [ht₂coe]
    exact hcomm'
  · intro h1
    apply hne'
    rw [← ht₂coe, h1]
  · intro h1
    apply hnc₁₃'
    have h2 : (t : X ⧸ fusionZStar X) * ↑(c₃⁻¹ * t * c₃) =
        ↑(c₃⁻¹ * t * c₃) * (t : X ⧸ fusionZStar X) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
    rwa [ht₃coe] at h2
  · intro h1
    apply hnc₂₃'
    have h2 : ((c₂⁻¹ * t * c₂ : X) : X ⧸ fusionZStar X) *
          ((c₃⁻¹ * t * c₃ : X) : X ⧸ fusionZStar X) =
        ((c₃⁻¹ * t * c₃ : X) : X ⧸ fusionZStar X) *
          ((c₂⁻¹ * t * c₂ : X) : X ⧸ fusionZStar X) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
    rwa [ht₂coe, ht₃coe] at h2

private theorem not_isPGroup_closure_of_mk [Finite X] {n : ℕ}
    {t c₃ : X} (hS : BenderType (X ⧸ fusionZStar X) n 2 1) (ht : t * t = 1)
    {c₃' : X ⧸ fusionZStar X} (hc₃ : (c₃ : X ⧸ fusionZStar X) = c₃')
    (hnc : (t : X ⧸ fusionZStar X) * (c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃') ≠
      c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃' * (t : X ⧸ fusionZStar X)) :
    ¬ IsPGroup 2 ↥(Subgroup.closure ({(t : X), (c₃⁻¹ * t * c₃ : X)} : Set X)) := by
  have hs : (t : X ⧸ fusionZStar X) * (t : X ⧸ fusionZStar X) = 1 := by
    rw [← QuotientGroup.mk_mul, ht, QuotientGroup.mk_one]
  have ht₃coe := mk_conj (t := t) hc₃
  have h₃ : (c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃') *
      (c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃') = 1 := conj_mul_self_eq_one hs
  have hset : (QuotientGroup.mk' (fusionZStar X)) '' ({(t : X), (c₃⁻¹ * t * c₃ : X)} : Set X) =
      ({(t : X ⧸ fusionZStar X), ((c₃⁻¹ * t * c₃ : X) : X ⧸ fusionZStar X)} :
        Set (X ⧸ fusionZStar X)) := by
    rw [Set.image_insert_eq, Set.image_singleton]
    simp only [QuotientGroup.mk'_apply]
  intro hP
  have hmap : IsPGroup 2 ↥((Subgroup.closure ({(t : X), (c₃⁻¹ * t * c₃ : X)} : Set X)).map
      (QuotientGroup.mk' (fusionZStar X))) := hP.map (QuotientGroup.mk' (fusionZStar X))
  rw [MonoidHom.map_closure, hset, ht₃coe] at hmap
  exact hnc (CFSG.Quasithin.F7Two.commute_of_isPGroup_closure_involutions hS hs h₃ hmap)

private theorem exists_preimage_sqRoot {t c₂ c₃ : X} {c₂' c₃' γ : X ⧸ fusionZStar X}
    (hc₂ : (c₂ : X ⧸ fusionZStar X) = c₂') (hc₃ : (c₃ : X ⧸ fusionZStar X) = c₃')
    (hγmem : γ ∈ Subgroup.closure ({(t : X ⧸ fusionZStar X),
        c₂'⁻¹ * (t : X ⧸ fusionZStar X) * c₂',
        c₃'⁻¹ * (t : X ⧸ fusionZStar X) * c₃'} : Set (X ⧸ fusionZStar X)))
    (hγsq : γ * γ = (t : X ⧸ fusionZStar X)) :
    ∃ g₀ ∈ Subgroup.closure ({t, c₂⁻¹ * t * c₂, c₃⁻¹ * t * c₃} : Set X),
      (g₀ : X ⧸ fusionZStar X) = γ ∧ t⁻¹ * (g₀ * g₀) ∈ fusionZStar X := by
  have ht₂coe := mk_conj (t := t) hc₂
  have ht₃coe := mk_conj (t := t) hc₃
  have hγmem' : γ ∈ Subgroup.closure ({(t : X ⧸ fusionZStar X),
      ((c₂⁻¹ * t * c₂ : X) : X ⧸ fusionZStar X),
      ((c₃⁻¹ * t * c₃ : X) : X ⧸ fusionZStar X)} : Set (X ⧸ fusionZStar X)) := by
    rw [ht₂coe, ht₃coe]
    exact hγmem
  obtain ⟨g₀, hg₀mem, hg₀γ⟩ := exists_mem_closure_mk_eq (fusionZStar X) hγmem'
  have hg₀sq : ((g₀ * g₀ : X) : X ⧸ fusionZStar X) = (t : X ⧸ fusionZStar X) := by
    rw [QuotientGroup.mk_mul, hg₀γ, hγsq]
  exact ⟨g₀, hg₀mem, hg₀γ, (QuotientGroup.eq).mp hg₀sq.symm⟩

theorem exists_szBarTriple
    {X : Type} [Group X] [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    (hodd : fusionOddCore X ≤ Subgroup.center X) {n : ℕ}
    (hS : BenderType (X ⧸ fusionZStar X) n 2 1) {t : X} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ c₂ c₃ g : X, SzBarTriple t c₂ c₃ g := by
  classical
  obtain ⟨hZc, hZodd, -, -⟩ := fusionZStar_setup hO2 hodd ht ht1
  obtain ⟨c₂', c₃', γ, hγsq, hγmem, hcomm', hne', hnc₁₃', hnc₂₃'⟩ :=
    exists_sqroot_mem_closure_of_benderType hO2 hodd hS ht ht1
  obtain ⟨c₂, hc₂⟩ := QuotientGroup.mk_surjective c₂'
  obtain ⟨c₃, hc₃⟩ := QuotientGroup.mk_surjective c₃'
  obtain ⟨g₀, hg₀mem, -, hmemZ⟩ := exists_preimage_sqRoot hc₂ hc₃ hγmem hγsq
  obtain ⟨hcommX, hne₁₂, hnc₁₃, hnc₂₃⟩ :=
    conj_relations_of_mk hZc hZodd ht hc₂ hc₃ hcomm' hne' hnc₁₃' hnc₂₃'
  refine ⟨c₂, c₃, g₀ ^ Nat.card (fusionZStar X), ht, ht1, hcommX, hne₁₂, hnc₁₃, hnc₂₃,
    not_isPGroup_closure_of_mk hS ht hc₃ hnc₁₃', Subgroup.pow_mem _ hg₀mem _,
    pow_card_mul_self_eq hZc hZodd ht hmemZ⟩

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
