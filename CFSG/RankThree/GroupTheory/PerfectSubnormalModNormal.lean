module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup

universe u

theorem le_of_perfect_of_eq_mul_solvable {G : Type*} [Group G] {S M R : Subgroup G}
    (hS : Group.IsPerfect S) (hMS : M ≤ S) (hMn : S ≤ normalizer (M : Set G))
    (hsol : Group.IsSolvable (S ⊓ R : Subgroup G))
    (hS' : ∀ s ∈ S, ∃ m ∈ M, ∃ r ∈ S ⊓ R, m * r = s) : S ≤ M := by
  set M' : Subgroup S := M.subgroupOf S with hM'
  have hn : M'.Normal := (normal_subgroupOf_iff_le_normalizer hMS).mpr hMn
  have hperf : Group.IsPerfect (S ⧸ M') :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective M')
  let f : (S ⊓ R : Subgroup G) →* S ⧸ M' :=
    (QuotientGroup.mk' M').comp (Subgroup.inclusion (inf_le_left : S ⊓ R ≤ S))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨s, hs⟩, rfl⟩ := QuotientGroup.mk'_surjective M' q
    obtain ⟨m, hm, r, hr, hmr⟩ := hS' s hs
    refine ⟨⟨r, hr⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have hrS : r ∈ S := hr.1
    have hmS : m ∈ S := hMS hm
    have h1 : (⟨m, hmS⟩ : S) ∈ M' := by rw [hM', mem_subgroupOf]; exact hm
    have h2 := hn.conj_mem _ h1 (⟨r, hrS⟩ : S)⁻¹
    convert h2 using 1
    apply Subtype.ext
    simp only [coe_mul, coe_inv, Subgroup.coe_inclusion, InvMemClass.coe_inv, inv_inv]
    rw [← hmr]
    group
  have hsolQ : Group.IsSolvable (S ⧸ M') := Group.isSolvable_of_surjective hf
  have hsub : Subsingleton (S ⧸ M') := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable _ hsolQ
  intro x hx
  have h1 : (QuotientGroup.mk' M' ⟨x, hx⟩ : S ⧸ M') = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact mem_subgroupOf.mp h1

theorem le_of_perfect_of_sup_eq_of_solvable_inf {G : Type*} [Group G] {S₁ S₂ R : Subgroup G}
    [R.Normal] (h₁ : Group.IsPerfect S₁) (hR₁ : R ≤ normalizer (S₁ : Set G))
    (hR₂ : R ≤ normalizer (S₂ : Set G)) (hsup : S₁ ⊔ R = S₂ ⊔ R)
    (hsol₁ : Group.IsSolvable (S₁ ⊓ R : Subgroup G)) : S₁ ≤ S₂ := by
  have hS₁N₂ : S₁ ≤ normalizer (S₂ : Set G) :=
    (hsup ▸ (le_sup_left : S₁ ≤ S₁ ⊔ R) : S₁ ≤ S₂ ⊔ R).trans (sup_le le_normalizer hR₂)
  have hS₂N₁ : S₂ ≤ normalizer (S₁ : Set G) :=
    (hsup.symm ▸ (le_sup_left : S₂ ≤ S₂ ⊔ R) : S₂ ≤ S₁ ⊔ R).trans (sup_le le_normalizer hR₁)
  set M : Subgroup G := S₁ ⊓ S₂ with hM
  have hcomm : ⁅S₁, S₂⁆ ≤ M := by
    rw [commutator_le]
    intro x hx y hy
    refine ⟨?_, ?_⟩
    ·
      rw [commutatorElement_def]
      have h1 : y⁻¹ * x * y⁻¹⁻¹ ∈ S₁ := ((mem_normalizer_iff.mp (hS₂N₁ (S₂.inv_mem hy)) x).mp hx)
      have h2 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      have h3 : y * x⁻¹ * y⁻¹ ∈ S₁ := ((mem_normalizer_iff.mp (hS₂N₁ hy) x⁻¹).mp (S₁.inv_mem hx))
      rw [h2]
      exact S₁.mul_mem hx h3
    · rw [commutatorElement_def]
      have h3 : x * y * x⁻¹ ∈ S₂ := ((mem_normalizer_iff.mp (hS₁N₂ hx) y).mp hy)
      exact S₂.mul_mem h3 (S₂.inv_mem hy)
  let π := QuotientGroup.mk' R
  have hker : π.ker = R := QuotientGroup.ker_mk' R
  have hπeq : S₁.map π = S₂.map π := by
    have h1 : (S₁ ⊔ R).map π = S₁.map π := by
      rw [Subgroup.map_sup, (QuotientGroup.map_mk'_self R), sup_bot_eq]
    have h2 : (S₂ ⊔ R).map π = S₂.map π := by
      rw [Subgroup.map_sup, (QuotientGroup.map_mk'_self R), sup_bot_eq]
    rw [← h1, ← h2, hsup]
  have hperf : ⁅S₁.map π, S₁.map π⁆ = S₁.map π := by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp h₁]
  have hle : S₁.map π ≤ M.map π := by
    calc S₁.map π = ⁅S₁.map π, S₁.map π⁆ := hperf.symm
      _ = ⁅S₁.map π, S₂.map π⁆ := by rw [← hπeq]
      _ = (⁅S₁, S₂⁆).map π := (Subgroup.map_commutator _ _ _).symm
      _ ≤ M.map π := Subgroup.map_mono hcomm
  have hS₁M : S₁ ≤ M ⊔ R := by
    intro x hx
    have : x ∈ (M.map π).comap π := hle ⟨x, hx, rfl⟩
    rwa [Subgroup.comap_map_eq, hker] at this
  have hS' : ∀ s ∈ S₁, ∃ m ∈ M, ∃ r ∈ S₁ ⊓ R, m * r = s := by
    intro s hs
    obtain ⟨m, hm, r, hr, hmr⟩ := mem_sup_of_normal_right.mp (hS₁M hs)
    refine ⟨m, hm, r, ⟨?_, hr⟩, hmr⟩
    have : m⁻¹ * s = r := by rw [← hmr]; group
    rw [← this]
    exact S₁.mul_mem (S₁.inv_mem hm.1) hs
  have hMn : S₁ ≤ normalizer (M : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hx, hS₁N₂ hx⟩
  exact (le_of_perfect_of_eq_mul_solvable h₁ inf_le_left hMn hsol₁ hS').trans inf_le_right

theorem eq_of_perfect_of_sup_eq_of_solvable_inf {G : Type*} [Group G] {S₁ S₂ R : Subgroup G}
    [R.Normal] (h₁ : Group.IsPerfect S₁) (h₂ : Group.IsPerfect S₂)
    (hR₁ : R ≤ normalizer (S₁ : Set G)) (hR₂ : R ≤ normalizer (S₂ : Set G))
    (hsup : S₁ ⊔ R = S₂ ⊔ R) (hsol₁ : Group.IsSolvable (S₁ ⊓ R : Subgroup G))
    (hsol₂ : Group.IsSolvable (S₂ ⊓ R : Subgroup G)) : S₁ = S₂ :=
  le_antisymm (le_of_perfect_of_sup_eq_of_solvable_inf h₁ hR₁ hR₂ hsup hsol₁)
    (le_of_perfect_of_sup_eq_of_solvable_inf h₂ hR₂ hR₁ hsup.symm hsol₂)

theorem mem_normalizer_of_mem_normalizer_subgroupOf {G : Type*} [Group G] {S H : Subgroup G}
    (hSH : S ≤ H) {h : H}
    (hh : h ∈ normalizer ((S.subgroupOf H : Subgroup H) : Set H)) :
    (h : G) ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff] at hh ⊢
  intro x
  constructor
  · intro hx
    have := (hh ⟨x, hSH hx⟩).mp hx
    exact this
  · intro hx
    have hxH : x ∈ H := by
      have h1 : (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * (h : G) ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem h.2) (hSH hx)) h.2
      simpa [mul_assoc] using h1
    have := (hh ⟨x, hxH⟩).mpr hx
    exact this

theorem le_normalizer_of_perfect_isSubnormal_of_solvable_inf_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → ∀ {S N : Subgroup G} [N.Normal],
      Group.IsPerfect S → S.IsSubnormal → Group.IsSolvable (S ⊓ N : Subgroup G) →
        N ≤ normalizer (S : Set G) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hcard S N _ hS hsn hsol
  rcases hsn.lt_normal with hStop | ⟨H, hHn, hSH, hHlt⟩
  · rw [hStop]
    intro x _
    rw [mem_normalizer_iff]
    intro y
    simp
  have hHcard : Nat.card H < n := by
    rw [← hcard, ← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt hHlt
  have hS' : Group.IsPerfect (S.subgroupOf H) := by
    have : Group.IsPerfect S := hS
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hSH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hSH).symm.surjective
  have hsol' : Group.IsSolvable (S.subgroupOf H ⊓ N.subgroupOf H : Subgroup H) := by
    let f : (S.subgroupOf H ⊓ N.subgroupOf H : Subgroup H) →* (S ⊓ N : Subgroup G) :=
      { toFun := fun x => ⟨((x : H) : G), ⟨x.2.1, x.2.2⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x y hxy
      have : ((x : H) : G) = ((y : H) : G) :=
        congrArg (fun z : (S ⊓ N : Subgroup G) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext this)
    exact Group.isSolvable_of_isSolvable_injective hf
  have hIH := ih _ hHcard H rfl (S := S.subgroupOf H) (N := N.subgroupOf H) hS' hsn.subgroupOf hsol'
  have hR₁ : N ⊓ H ≤ normalizer (S : Set G) := by
    intro r hr
    exact mem_normalizer_of_mem_normalizer_subgroupOf hSH
      (h := ⟨r, hr.2⟩) (hIH (show (⟨r, hr.2⟩ : H) ∈ N.subgroupOf H from hr.1))
  have hc1 : ∀ q' ∈ N, ∀ s ∈ S, s⁻¹ * (q' * s * q'⁻¹) ∈ N ⊓ H := by
    intro q' hq' s hs
    refine ⟨?_, ?_⟩
    · have h1 : s⁻¹ * q' * s⁻¹⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem q' hq' s⁻¹
      have e : s⁻¹ * (q' * s * q'⁻¹) = (s⁻¹ * q' * s⁻¹⁻¹) * q'⁻¹ := by group
      rw [e]
      exact N.mul_mem h1 (N.inv_mem hq')
    · have h1 : q' * s * q'⁻¹ ∈ H := hHn.conj_mem s (hSH hs) q'
      exact H.mul_mem (H.inv_mem (hSH hs)) h1
  have hc2 : ∀ q' ∈ N, ∀ s ∈ S, (q' * s * q'⁻¹)⁻¹ * s ∈ N ⊓ H := by
    intro q' hq' s hs
    refine ⟨?_, ?_⟩
    · have h1 : s⁻¹ * q'⁻¹ * s⁻¹⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem q'⁻¹ (N.inv_mem hq') s⁻¹
      have e : (q' * s * q'⁻¹)⁻¹ * s = q' * (s⁻¹ * q'⁻¹ * s⁻¹⁻¹) := by group
      rw [e]
      exact N.mul_mem hq' h1
    · have h1 : q' * s * q'⁻¹ ∈ H := hHn.conj_mem s (hSH hs) q'
      exact H.mul_mem (H.inv_mem h1) (hSH hs)
  have key : ∀ q' ∈ N, ∀ s ∈ S, q'⁻¹ * s * q' ∈ S := by
    intro q' hq'
    let Sq : Subgroup G := S.comap (MulAut.conj q'⁻¹).toMonoidHom
    have hmemSq : ∀ x, x ∈ Sq ↔ q'⁻¹ * x * q' ∈ S := by
      intro x; simp [Sq]
    have hRN : ∀ r ∈ N ⊓ H, q'⁻¹ * r * q' ∈ N ⊓ H := by
      intro r hr
      refine ⟨?_, ?_⟩
      · simpa using (inferInstance : N.Normal).conj_mem r hr.1 q'⁻¹
      · simpa using hHn.conj_mem r hr.2 q'⁻¹
    have hR₂ : N ⊓ H ≤ normalizer (Sq : Set G) := by
      intro r hr
      rw [mem_normalizer_iff]
      intro x
      have hr' := hR₁ (hRN r hr)
      rw [mem_normalizer_iff] at hr'
      simp only [SetLike.mem_coe, hmemSq]
      have := hr' (q'⁻¹ * x * q')
      have e : (q'⁻¹ * r * q') * (q'⁻¹ * x * q') * (q'⁻¹ * r * q')⁻¹ =
          q'⁻¹ * (r * x * r⁻¹) * q' := by group
      rw [e] at this
      simpa only [SetLike.mem_coe] using this
    have hsup : S ⊔ (N ⊓ H) = Sq ⊔ (N ⊓ H) := by
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        intro s' hs'
        have hy : q' * s' * q'⁻¹ ∈ Sq := by
          rw [hmemSq]
          have e : q'⁻¹ * (q' * s' * q'⁻¹) * q' = s' := by group
          rw [e]; exact hs'
        have : s' = (q' * s' * q'⁻¹) * ((q' * s' * q'⁻¹)⁻¹ * s') := by group
        rw [this]
        exact mul_mem_sup hy (hc2 q' hq' s' hs')
      · refine sup_le ?_ le_sup_right
        intro y hy
        have hs0 : q'⁻¹ * y * q' ∈ S := (hmemSq y).mp hy
        have e : y = (q'⁻¹ * y * q') * ((q'⁻¹ * y * q')⁻¹ * y) := by group
        have hmem : (q'⁻¹ * y * q')⁻¹ * y ∈ N ⊓ H := by
          have h3 := hc1 q' hq' (q'⁻¹ * y * q') hs0
          have e3 : q' * (q'⁻¹ * y * q') * q'⁻¹ = y := by group
          rw [e3] at h3
          exact h3
        rw [e]
        exact mul_mem_sup hs0 hmem
    have hsol₁ : Group.IsSolvable (S ⊓ (N ⊓ H) : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (show S ⊓ (N ⊓ H) ≤ S ⊓ N from inf_le_inf_left _ inf_le_left))
        (Subgroup.inclusion_injective _)
    have hle : S ≤ Sq := le_of_perfect_of_sup_eq_of_solvable_inf hS hR₁ hR₂ hsup hsol₁
    intro s hs
    exact (hmemSq s).mp (hle hs)
  intro q hq
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    simpa using key q⁻¹ (N.inv_mem hq) x hx
  · intro hx
    have h1 := key q hq _ hx
    have e : q⁻¹ * (q * x * q⁻¹) * q = x := by group
    rwa [e] at h1

open scoped commutatorElement

theorem le_normalizer_of_perfect_isSubnormal_of_solvable_inf {G : Type u} [Group G] [Finite G]
    {S N : Subgroup G} [N.Normal] (hS : Group.IsPerfect S) (hsn : S.IsSubnormal)
    (hsol : Group.IsSolvable (S ⊓ N : Subgroup G)) : N ≤ normalizer (S : Set G) :=
  le_normalizer_of_perfect_isSubnormal_of_solvable_inf_aux _ G rfl hS hsn hsol

theorem eq_of_perfect_isSubnormal_of_sup_eq_of_solvable_inf {G : Type u} [Group G] [Finite G]
    {S₁ S₂ N : Subgroup G} [N.Normal] (h₁ : Group.IsPerfect S₁) (h₂ : Group.IsPerfect S₂)
    (hs₁ : S₁.IsSubnormal) (hs₂ : S₂.IsSubnormal)
    (hsol₁ : Group.IsSolvable (S₁ ⊓ N : Subgroup G)) (hsol₂ : Group.IsSolvable (S₂ ⊓ N : Subgroup G))
    (hsup : S₁ ⊔ N = S₂ ⊔ N) : S₁ = S₂ :=
  eq_of_perfect_of_sup_eq_of_solvable_inf h₁ h₂
    (le_normalizer_of_perfect_isSubnormal_of_solvable_inf h₁ hs₁ hsol₁)
    (le_normalizer_of_perfect_isSubnormal_of_solvable_inf h₂ hs₂ hsol₂) hsup hsol₁ hsol₂

end CFSG.RankThree.GroupTheory
