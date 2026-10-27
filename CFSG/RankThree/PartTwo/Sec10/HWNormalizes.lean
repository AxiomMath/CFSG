module

public import CFSG.RankThree.PartTwo.Sec10.Item108
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.KFacts.K73Lines

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_singleton_eq_of_zpowers_eq {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  have key : ∀ {u v : G}, u ∈ Subgroup.zpowers v → ∀ g : G,
      g ∈ Subgroup.centralizer ({v} : Set G) → g ∈ Subgroup.centralizer ({u} : Set G) := by
    intro u v hu g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact Commute.zpow_right hg k
  have hy : y ∈ Subgroup.zpowers x := by
    rw [h]
    exact Subgroup.mem_zpowers y
  have hx : x ∈ Subgroup.zpowers y := by
    rw [← h]
    exact Subgroup.mem_zpowers x
  ext g
  exact ⟨key hy g, key hx g⟩

omit [Finite G] in
theorem card_closure_pair_le {c a : G} (hca : c * a = a * c) (hc3 : c ^ 3 = 1) (ha3 : a ^ 3 = 1) :
    Nat.card (Subgroup.closure ({c, a} : Set G)) ≤ 9 := by
  set C := Subgroup.closure ({c, a} : Set G)
  have hc : c ∈ C := Subgroup.subset_closure (by simp)
  have ha : a ∈ C := Subgroup.subset_closure (by simp)
  have hf : Function.Surjective (fun ij : Fin 3 × Fin 3 =>
      (⟨c ^ (ij.1 : ℕ) * a ^ (ij.2 : ℕ), C.mul_mem (C.pow_mem hc _) (C.pow_mem ha _)⟩ : C)) := by
    rintro ⟨z, hz⟩
    obtain ⟨i, j, hi, hj, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hz
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hf
  simpa using h1

theorem commutator_mem_theta_of_ne {c : G} {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ thetaComponentsAt 3 c) (h₂ : L₂ ∈ thetaComponentsAt 3 c) (hne : L₁ ≠ L₂)
    {x y : G} (hx : x ∈ L₁) (hy : y ∈ L₂) :
    x * y * x⁻¹ * y⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  set H := Subgroup.centralizer ({c} : Set G)
  obtain ⟨hL₁H, hM₁⟩ := mem_thetaComponentsIn_iff.mp h₁
  obtain ⟨hL₂H, hM₂⟩ := mem_thetaComponentsIn_iff.mp h₂
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H)
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hK₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three hM₁
  have hK₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three hM₂
  have hMne : L₁.subgroupOf H ≠ L₂.subgroupOf H := fun h => hne (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hL₁H, ← Subgroup.map_subgroupOf_eq_of_le hL₂H, h])
  have hKne : (L₁.subgroupOf H).map π ≠ (L₂.subgroupOf H).map π :=
    fun h => hMne (hbij.injOn hM₁ hM₂ h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  have hx' : (⟨x, hL₁H hx⟩ : H) ∈ L₁.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hy' : (⟨y, hL₂H hy⟩ : H) ∈ L₂.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hy
  have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π hx')
    (Subgroup.mem_map_of_mem π hy')
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem le_normalizer_of_mem_inf {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    (h : Sec8.Hyp81 G A c L a) (hAN : A ≤ Subgroup.normalizer (L : Set G)) {d : G}
    (hdA : d ∈ A) (hdL : d ∈ L) (hdc : d ∉ Subgroup.zpowers c) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  rintro g ⟨hgH, hgW⟩
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  by_contra hne
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hne' : L' ≠ L := hne
  have hzc : Subgroup.zpowers ((MulAut.conj g) c) = Subgroup.zpowers c := by
    have h1 : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgH
    rw [MonoidHom.map_zpowers] at h1
    exact h1
  have hL'c : L' ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj g) h.mem_thetaComponentsAt
    rw [thetaComponentsAt_eq_thetaComponentsIn, centralizer_singleton_eq_of_zpowers_eq hzc] at h1
    exact h1
  set d' := g * d * g⁻¹ with hd'
  have hd'A : d' ∈ A := (Subgroup.mem_normalizer_iff.mp hgW d).mp hdA
  have hd'L' : d' ∈ L' := ⟨d, hdL, rfl⟩
  have hd'sc : d' ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨hd'A, fun x hx => ?_⟩
    have h1 := commutator_mem_theta_of_ne hL'c h.mem_thetaComponentsAt hne' hd'L' hx
    have h2 : d' * x * d'⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN hd'A) x).mp hx) (L.inv_mem hx)
    have h3 : d' * x * d'⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt h.mem_thetaComponentsAt]
      exact ⟨h2, h1⟩
    exact h3
  rw [h.sectionCentralizer_eq] at hd'sc
  apply hdc
  have h1 : g⁻¹ * d' * g⁻¹⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgH) d').mp hd'sc
  have e : g⁻¹ * d' * g⁻¹⁻¹ = d := by
    rw [hd']
    group
  rwa [e] at h1

end Core

theorem hwNormalizesL_of (h97 : Sec9.Item97) : HWNormalizesL := by
  intro G _ _ A c L a R h
  obtain ⟨d, hdL, -, hA⟩ := exists_inf_eq_zpowers h97 h
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · exact hcN
    · exact h.a_mem_normalizer
    · exact Subgroup.le_normalizer hdAL.2
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc
    have hle : A ≤ Subgroup.closure ({c, a} : Set G) := by
      rw [hA, Subgroup.closure_le]
      have hc : c ∈ Subgroup.closure ({c, a} : Set G) := Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact hc
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.zpowers_le.mpr hc hdc
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_closure_pair_le (hcomm c h.mem_A a h.a_mem) (hAe.2 c h.mem_A)
      (hAe.2 a h.a_mem)
    rw [h.card_eq] at h1
    omega
  exact le_normalizer_of_mem_inf h.toHyp81 hAN hdAL.1 hdAL.2 hdc

theorem item108_of_item97 (h107 : Item107) (h103 : Item103) (h97 : Sec9.Item97) : Item108 :=
  item108_of h107 h103 (hwNormalizesL_of h97)

end CFSG.RankThree.PartTwo.Sec10
