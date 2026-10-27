module

public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec4

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75

section WeaklyClosed

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

private theorem utri_le_centralizer {A : Subgroup SL(2, F)} (hA : A ≤ utri F) :
    utri F ≤ Subgroup.centralizer (A : Set SL(2, F)) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨s, rfl⟩ := mem_utri_iff.1 (hA ha)
  obtain ⟨t, rfl⟩ := mem_utri_iff.1 hu
  rw [← utriElt_add, ← utriElt_add, add_comm]

private theorem mem_normalizer_conj {G : Type*} [Group G] {A T : Subgroup G} {x z : G}
    (hA : A = conjSubgroup x T) (hz : z ∈ Subgroup.normalizer (A : Set G)) :
    x⁻¹ * z * x ∈ Subgroup.normalizer (T : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hzA : conjSubgroup z A = A := mem_normalizer_iff_conjSubgroup_eq.1 hz
  have h1 : conjSubgroup x⁻¹ (conjSubgroup z (conjSubgroup x T)) =
      conjSubgroup (x⁻¹ * z * x) T := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  rw [← h1, ← hA, hzA, hA, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

private theorem weaklyClosedInNormalizer_conj {G : Type*} [Group G] {T : Subgroup G}
    (hwc : ∀ g : G, conjSubgroup g T ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T = T) (x : G) :
    ∀ g : G, conjSubgroup g (conjSubgroup x T) ≤
      Subgroup.normalizer (conjSubgroup x T : Set G) →
      conjSubgroup g (conjSubgroup x T) = conjSubgroup x T := by
  intro g hg
  set A : Subgroup G := conjSubgroup x T with hA
  have hkey : conjSubgroup (x⁻¹ * g * x) T ≤ Subgroup.normalizer (T : Set G) := by
    rintro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    have hz : g * (x * t * x⁻¹) * g⁻¹ ∈ conjSubgroup g A :=
      conj_mem_conjSubgroup g (by rw [hA]; exact conj_mem_conjSubgroup x ht)
    have hzN : g * (x * t * x⁻¹) * g⁻¹ ∈ Subgroup.normalizer (A : Set G) := hg hz
    have hyz : (MulAut.conj (x⁻¹ * g * x)) t =
        x⁻¹ * (g * (x * t * x⁻¹) * g⁻¹) * x := by
      rw [MulAut.conj_apply]
      group
    change (MulAut.conj (x⁻¹ * g * x)) t ∈ Subgroup.normalizer (T : Set G)
    rw [hyz]
    exact mem_normalizer_conj hA hzN
  calc conjSubgroup g A
      = conjSubgroup g (conjSubgroup x T) := by rw [hA]
    _ = conjSubgroup (g * x) T := conjSubgroup_conjSubgroup g x T
    _ = conjSubgroup (x * (x⁻¹ * g * x)) T := by
          rw [show x * (x⁻¹ * g * x) = g * x by group]
    _ = conjSubgroup x (conjSubgroup (x⁻¹ * g * x) T) :=
          (conjSubgroup_conjSubgroup x (x⁻¹ * g * x) T).symm
    _ = A := by rw [hwc (x⁻¹ * g * x) hkey, hA]

private theorem eq_utri_of_le_of_weaklyClosed {A : Subgroup SL(2, F)} (hA : A ≤ utri F)
    (hA1 : A ≠ ⊥) (hwc : ∀ g : SL(2, F),
      conjSubgroup g A ≤ Subgroup.normalizer (A : Set SL(2, F)) → conjSubgroup g A = A) :
    A = utri F := by
  refine le_antisymm hA ?_
  have hN : utri F ≤ Subgroup.normalizer (A : Set SL(2, F)) :=
    (utri_le_centralizer hA).trans (Subgroup.centralizer_le_normalizer (A : Set SL(2, F)))
  intro g hg
  obtain ⟨s, rfl⟩ := mem_utri_iff.1 hg
  by_cases hs : s = 0
  · rw [hs, utriElt_zero]
    exact A.one_mem
  · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    have ha1' : (a : SL(2, F)) ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨s₀, hs₀⟩ := mem_utri_iff.1 (hA a.2)
    have hs₀0 : s₀ ≠ 0 := by
      rintro rfl
      rw [utriElt_zero] at hs₀
      exact ha1' hs₀
    obtain ⟨c, hc⟩ := exists_torusElt_conj_utriElt hs₀0 hs
    have hstep : conjSubgroup (torusElt c) A = A := by
      refine hwc (torusElt c) ?_
      rintro y ⟨b, hb, rfl⟩
      exact hN (conj_mem_utri_of_mem_borel (torusElt_mem_borel c) (hA hb))
    have hmem : torusElt c * (a : SL(2, F)) * (torusElt c)⁻¹ ∈ A := by
      have h1 : torusElt c * (a : SL(2, F)) * (torusElt c)⁻¹ ∈
          conjSubgroup (torusElt c) A := conj_mem_conjSubgroup _ a.2
      rwa [hstep] at h1
    rw [hs₀, hc] at hmem
    exact hmem

end WeaklyClosed

theorem card_eq_of_weaklyClosed {F : Type} [Field F] [Fintype F] [CharP F 2]
    {T : Subgroup SL(2, F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hwc : ∀ g : SL(2, F), conjSubgroup g T ≤ Subgroup.normalizer (T : Set SL(2, F)) →
      conjSubgroup g T = T) :
    Nat.card T = Fintype.card F ∧ ∀ t ∈ T, t * t = 1 := by
  classical
  haveI : Finite F := Finite.of_fintype F
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  obtain ⟨x, hxP⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  have hTx : T ≤ conjSubgroup x (utri F) := by rw [hxP]; exact hTP
  set A : Subgroup SL(2, F) := conjSubgroup x⁻¹ T with hA
  have hA_le : A ≤ utri F := by
    rw [hA]
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hTx
    change conjSubgroup x⁻¹ T ≤ conjSubgroup x⁻¹ (conjSubgroup x (utri F)) at h
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
  have hA_ne : A ≠ ⊥ := by
    intro hbot
    apply hT1
    have h := congrArg (conjSubgroup x) hbot
    rw [hA, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one,
      conjSubgroup_bot] at h
    exact h
  have hwcA : ∀ g : SL(2, F), conjSubgroup g A ≤
      Subgroup.normalizer (A : Set SL(2, F)) → conjSubgroup g A = A :=
    weaklyClosedInNormalizer_conj hwc x⁻¹
  have hA_eq : A = utri F := eq_utri_of_le_of_weaklyClosed hA_le hA_ne hwcA
  have hTA : T = conjSubgroup x A := by
    rw [hA, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hT_eq : T = conjSubgroup x (utri F) := by rw [hTA, hA_eq]
  refine ⟨?_, ?_⟩
  · rw [hT_eq, card_conjSubgroup, card_utri, Nat.card_eq_fintype_card]
  · intro t ht
    rw [hT_eq] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have huu : u * u = 1 := by
      simpa [pow_two] using (isElemAbelian_utri (F := F)).2 u hu
    change (MulAut.conj x) u * (MulAut.conj x) u = 1
    rw [MulAut.conj_apply]
    calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [huu]; group

end CFSG.RankThree.GF2n.Tim81.Sec4
