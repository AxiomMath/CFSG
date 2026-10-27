module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf)

variable {G G' : Type} [Group G] [Group G']

private def shape54pbPre {L : Subgroup G} {L' : Subgroup G'} (ψ : ↥L →* ↥L')
    (X' : Subgroup G') : Subgroup G :=
  ((X'.subgroupOf L').comap ψ).map L.subtype

private theorem shape54pb_mem_pre {L : Subgroup G} {L' : Subgroup G'} {ψ : ↥L →* ↥L'}
    {X' : Subgroup G'} (l : ↥L) :
    (l : G) ∈ shape54pbPre ψ X' ↔ ((ψ l : ↥L') : G') ∈ X' := by
  constructor
  · rintro ⟨y, hy, hyl⟩
    obtain rfl : y = l := Subtype.ext hyl
    exact hy
  · intro hl
    exact ⟨l, hl, rfl⟩

private theorem shape54pb_pre_le {L : Subgroup G} {L' : Subgroup G'} (ψ : ↥L →* ↥L')
    (X' : Subgroup G') : shape54pbPre ψ X' ≤ L := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

private theorem shape54pb_le_pre {L N : Subgroup G} {L' : Subgroup G'} (hNL : N ≤ L)
    {ψ : ↥L →* ↥L'} (hker : ∀ l : ↥L, ψ l = 1 ↔ (l : G) ∈ N) (X' : Subgroup G') :
    N ≤ shape54pbPre ψ X' := by
  intro n hn
  have h1 : ψ ⟨n, hNL hn⟩ = 1 := (hker ⟨n, hNL hn⟩).mpr hn
  refine (shape54pb_mem_pre (ψ := ψ) ⟨n, hNL hn⟩).mpr ?_
  rw [h1, OneMemClass.coe_one]
  exact X'.one_mem

private theorem shape54pb_relIndex_pre {L : Subgroup G} {L' : Subgroup G'} {ψ : ↥L →* ↥L'}
    (hψ : Function.Surjective ψ) (X' : Subgroup G') :
    (shape54pbPre ψ X').relIndex L = X'.relIndex L' := by
  have h : (shape54pbPre ψ X').subgroupOf L = (X'.subgroupOf L').comap ψ := by
    ext l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact shape54pb_mem_pre l
  rw [Subgroup.relIndex, Subgroup.relIndex, h, Subgroup.index_comap_of_surjective _ hψ]

private theorem shape54pb_isMaxParabolicMod {L N : Subgroup G} {L' N' : Subgroup G'}
    (hNL : N ≤ L) (ψ : ↥L →* ↥L') (hψ : Function.Surjective ψ)
    (hker : ∀ l : ↥L, ψ l = 1 ↔ (l : G) ∈ N) (hN' : ∀ l : ↥L', (l : G') ∈ N' → l = 1)
    {P' : Subgroup G'} (h : IsMaxParabolicMod N' L' P') :
    IsMaxParabolicMod N L (shape54pbPre ψ P') := by
  obtain ⟨-, hP'L', hmax, S', -, hS'L', hS'pow, hS'odd, hS'norm⟩ := h
  have hP'le : P' ≤ L' := hP'L'.le
  have hPL : shape54pbPre ψ P' ≤ L := shape54pb_pre_le ψ P'
  have hNP : N ≤ shape54pbPre ψ P' := shape54pb_le_pre hNL hker P'
  refine ⟨hNP, lt_of_le_of_ne hPL ?_, ?_, ?_⟩
  ·
    intro heq
    refine hP'L'.not_ge fun x hx => ?_
    obtain ⟨l, hl⟩ := hψ ⟨x, hx⟩
    have hlP : (l : G) ∈ shape54pbPre ψ P' := by
      rw [heq]
      exact l.2
    have h1 := (shape54pb_mem_pre l).mp hlP
    rw [hl] at h1
    exact h1
  ·
    intro Y hPY hYL
    let Y' : Subgroup G' := ((Y.subgroupOf L).map ψ).map L'.subtype
    have memY' : ∀ y : ↥L, (y : G) ∈ Y → ((ψ y : ↥L') : G') ∈ Y' := fun y hy =>
      ⟨ψ y, ⟨y, hy, rfl⟩, rfl⟩
    have hY'L' : Y' ≤ L' := by
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    have hP'Y' : P' ≤ Y' := by
      intro x hx
      obtain ⟨l, hl⟩ := hψ ⟨x, hP'le hx⟩
      have hlP : (l : G) ∈ shape54pbPre ψ P' := (shape54pb_mem_pre l).mpr (by rw [hl]; exact hx)
      have h1 := memY' l (hPY.le hlP)
      rw [hl] at h1
      exact h1
    have hP'Y'ne : P' ≠ Y' := by
      intro heq
      refine hPY.not_ge fun y hy => ?_
      have h1 := memY' ⟨y, hYL hy⟩ hy
      rw [← heq] at h1
      exact (shape54pb_mem_pre ⟨y, hYL hy⟩).mpr h1
    have hY'eq : Y' = L' := hmax Y' (lt_of_le_of_ne hP'Y' hP'Y'ne) hY'L'
    refine le_antisymm hYL fun l hl => ?_
    have h1 : ((ψ ⟨l, hl⟩ : ↥L') : G') ∈ Y' := by
      rw [hY'eq]
      exact (ψ ⟨l, hl⟩).2
    obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := h1
    have hz' : ψ y = ψ ⟨l, hl⟩ := Subtype.ext hz
    have h2 : ψ (y⁻¹ * ⟨l, hl⟩) = 1 := by
      rw [map_mul, map_inv, ← hz', inv_mul_cancel]
    have h3 : ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ Y := hPY.le (hNP ((hker _).mp h2))
    have h4 : l = (y : G) * ((y⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [h4]
    exact Y.mul_mem (Subgroup.mem_subgroupOf.mp hy) h3
  ·
    refine ⟨shape54pbPre ψ S', shape54pb_le_pre hNL hker S', shape54pb_pre_le ψ S', ?_, ?_, ?_⟩
    · intro s hs
      have hsL : s ∈ L := shape54pb_pre_le ψ S' hs
      obtain ⟨k, hk⟩ := hS'pow _ ((shape54pb_mem_pre ⟨s, hsL⟩).mp hs)
      refine ⟨k, ?_⟩
      have h2 : ψ (⟨s, hsL⟩ ^ 2 ^ k) = 1 := by
        apply hN'
        rw [map_pow, Subgroup.coe_pow]
        exact hk
      have h3 := (hker _).mp h2
      rwa [Subgroup.coe_pow] at h3
    · rw [shape54pb_relIndex_pre hψ S']
      exact hS'odd
    · intro l hl
      obtain ⟨hlL, hlN⟩ := Subgroup.mem_inf.mp hl
      refine (shape54pb_mem_pre ⟨l, hlL⟩).mpr (hS'norm (Subgroup.mem_inf.mpr
        ⟨(ψ ⟨l, hlL⟩).2, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩))
      constructor
      · intro hx
        obtain ⟨y, hy⟩ := hψ ⟨x, hS'L' hx⟩
        have hyS : (y : G) ∈ shape54pbPre ψ S' :=
          (shape54pb_mem_pre y).mpr (by rw [hy]; exact hx)
        have h1 : ((⟨l, hlL⟩ * y * (⟨l, hlL⟩ : ↥L)⁻¹ : ↥L) : G) ∈ shape54pbPre ψ S' :=
          (Subgroup.mem_normalizer_iff.mp hlN y).mp hyS
        have h2 := (shape54pb_mem_pre _).mp h1
        rw [map_mul, map_mul, map_inv, hy] at h2
        simpa using h2
      · intro hx
        have hlL' : ((ψ ⟨l, hlL⟩ : ↥L') : G') ∈ L' := (ψ ⟨l, hlL⟩).2
        have hxL : x ∈ L' := by
          have h1 : (ψ ⟨l, hlL⟩ : G')⁻¹ * ((ψ ⟨l, hlL⟩ : G') * x * (ψ ⟨l, hlL⟩ : G')⁻¹) *
              (ψ ⟨l, hlL⟩ : G') = x := by group
          rw [← h1]
          exact L'.mul_mem (L'.mul_mem (L'.inv_mem hlL') (hS'L' hx)) hlL'
        obtain ⟨y, hy⟩ := hψ ⟨x, hxL⟩
        have h1 : ((ψ (⟨l, hlL⟩ * y * (⟨l, hlL⟩ : ↥L)⁻¹) : ↥L') : G') ∈ S' := by
          rw [map_mul, map_mul, map_inv, hy]
          simpa using hx
        have h2 : ((⟨l, hlL⟩ * y * (⟨l, hlL⟩ : ↥L)⁻¹ : ↥L) : G) ∈ shape54pbPre ψ S' :=
          (shape54pb_mem_pre _).mpr h1
        have h3 : (y : G) ∈ shape54pbPre ψ S' := (Subgroup.mem_normalizer_iff.mp hlN y).mpr h2
        have h4 := (shape54pb_mem_pre y).mp h3
        rw [hy] at h4
        exact h4

theorem hasQuotShape_of_surjective {L N : Subgroup G} {L' N' : Subgroup G'}
    (ψ : ↥L →* ↥L') (hψ : Function.Surjective ψ) (hker : ∀ l : ↥L, ψ l = 1 ↔ (l : G) ∈ N)
    (hN' : ∀ l : ↥L', (l : G') ∈ N' → l = 1) {P : ∀ (X : Type) [Group X], Prop}
    (h : HasQuotShape L' (N' : Set G') P) : HasQuotShape L (N : Set G) P := by
  obtain ⟨X, hX, φ, hφ, hkerφ, hP⟩ := h
  refine ⟨X, hX, φ.comp ψ, hφ.comp hψ, fun l => ?_, hP⟩
  rw [MonoidHom.comp_apply, hkerφ, SetLike.mem_coe, SetLike.mem_coe, ← hker]
  constructor
  · exact hN' _
  · intro h1
    rw [h1, OneMemClass.coe_one]
    exact N'.one_mem

theorem actsOnDynkinMod_of_surjective {L N : Subgroup G} {L' N' : Subgroup G'} (hNL : N ≤ L)
    (ψ : ↥L →* ↥L') (hψ : Function.Surjective ψ) (hker : ∀ l : ↥L, ψ l = 1 ↔ (l : G) ∈ N)
    (hN' : ∀ l : ↥L', (l : G') ∈ N' → l = 1) {t : G} {t' : G'}
    (ht : t ∈ normalizer (L : Set G))
    (hcomp : ∀ l l₂ : ↥L, (l₂ : G) = t * l * t⁻¹ →
      ((ψ l₂ : ↥L') : G') = t' * (ψ l : G') * t'⁻¹)
    (h : ActsOnDynkinMod N' L' t') : ActsOnDynkinMod N L t := by
  obtain ⟨ht', P', hP', hconj⟩ := h
  have hP'le : P' ≤ L' := hP'.2.1.le
  refine ⟨ht, shape54pbPre ψ P', shape54pb_isMaxParabolicMod hNL ψ hψ hker hN' hP', ?_⟩
  intro l hl heq
  set l' : G' := ((ψ ⟨l, hl⟩ : ↥L') : G') with hl'
  refine hconj l' (ψ ⟨l, hl⟩).2 ?_
  rw [conjSubgroup_eq_iff_mem_normalizer] at heq ⊢
  have hg : t⁻¹ * l ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem ht) (le_normalizer hl)
  have hg' : t'⁻¹ * l' ∈ normalizer (L' : Set G') :=
    (normalizer (L' : Set G')).mul_mem ((normalizer (L' : Set G')).inv_mem ht')
      (le_normalizer (ψ ⟨l, hl⟩).2)
  have hgcomp : ∀ y y₂ : ↥L, (y₂ : G) = (t⁻¹ * l) * y * (t⁻¹ * l)⁻¹ →
      ((ψ y₂ : ↥L') : G') = (t'⁻¹ * l') * (ψ y : G') * (t'⁻¹ * l')⁻¹ := by
    intro y y₂ hy₂
    have h1 := hcomp y₂ (⟨l, hl⟩ * y * (⟨l, hl⟩ : ↥L)⁻¹) (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hy₂]
      group)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [← hl'] at h1
    have h2 : ((ψ y₂ : ↥L') : G') = t'⁻¹ * (t' * (ψ y₂ : G') * t'⁻¹) * t' := by group
    rw [h2, ← h1]
    group
  rw [Subgroup.mem_normalizer_iff] at heq ⊢
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hψ ⟨x, hP'le hx⟩
    have hyP : (y : G) ∈ shape54pbPre ψ P' := (shape54pb_mem_pre y).mpr (by rw [hy]; exact hx)
    have hy₂L : (t⁻¹ * l) * y * (t⁻¹ * l)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg y).mp y.2
    have h2 := (shape54pb_mem_pre (ψ := ψ) (X' := P') ⟨_, hy₂L⟩).mp ((heq y).mp hyP)
    rw [hgcomp y ⟨_, hy₂L⟩ rfl, hy] at h2
    exact h2
  · intro hx
    have hxL : x ∈ L' := (Subgroup.mem_normalizer_iff.mp hg' x).mpr (hP'le hx)
    obtain ⟨y, hy⟩ := hψ ⟨x, hxL⟩
    have hy₂L : (t⁻¹ * l) * y * (t⁻¹ * l)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg y).mp y.2
    have h2 : ((ψ ⟨_, hy₂L⟩ : ↥L') : G') ∈ P' := by
      rw [hgcomp y ⟨_, hy₂L⟩ rfl, hy]
      exact hx
    have h3 : (y : G) ∈ shape54pbPre ψ P' := (heq y).mpr ((shape54pb_mem_pre ⟨_, hy₂L⟩).mpr h2)
    have h4 := (shape54pb_mem_pre y).mp h3
    rw [hy] at h4
    exact h4

theorem shape54_of_surjective [Finite G] [Finite G'] {H T L : Subgroup G}
    {H' T' L' : Subgroup G'} (hNL : OInf H ≤ L) (ψ : ↥L →* ↥L') (hψ : Function.Surjective ψ)
    (hker : ∀ l : ↥L, ψ l = 1 ↔ (l : G) ∈ OInf H)
    (hN' : ∀ l : ↥L', (l : G') ∈ OInf H' → l = 1)
    (hT : ∀ t' ∈ T', t' ∈ normalizer (L' : Set G') → ∃ t ∈ T, t ∈ normalizer (L : Set G) ∧
      ∀ l l₂ : ↥L, (l₂ : G) = t * l * t⁻¹ → ((ψ l₂ : ↥L') : G') = t' * (ψ l : G') * t'⁻¹)
    (h : Shape54 H' T' L') : Shape54 H T L := by
  have key : ∀ P : ∀ (X : Type) [Group X], Prop,
      HasQuotShape L' (OInf H' : Set G') P → HasQuotShape L (OInf H : Set G) P :=
    fun _ h => hasQuotShape_of_surjective ψ hψ hker hN' h
  unfold Shape54 at h ⊢
  rcases h with h | h | ⟨h, t', ht'T, ht'⟩ | ⟨p, e, hp, hp2, hpe, h⟩ |
    ⟨p, hp, hp2, ⟨h4, h⟩ | ⟨h4, h⟩⟩ | ⟨p, hp, hp2, h⟩
  · exact Or.inl (key _ h)
  · exact Or.inr (Or.inl (key _ h))
  · obtain ⟨t, htT, htn, hcomp⟩ := hT t' ht'T ht'.1
    exact Or.inr (Or.inr (Or.inl ⟨key _ h, t, htT,
      actsOnDynkinMod_of_surjective hNL ψ hψ hker hN' htn hcomp ht'⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp2, hpe, key _ h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inl ⟨h4, key _ h⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inr ⟨h4, key _ h⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, key _ h⟩))))

end CFSG.LocalAnalysis.WeakClosure81

end
