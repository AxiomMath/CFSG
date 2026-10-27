module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZStar
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem commutator_mem_of_mem_sup {G : Type*} [Group G] {L : Subgroup G} {t : G}
    (ht : t * t = 1) (htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L) {h : G}
    (hh : h ∈ L ⊔ Subgroup.zpowers t) : h * t * h⁻¹ * t⁻¹ ∈ L := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have key : ∀ x ∈ Subgroup.closure ((L : Set G) ∪ {t}),
      (∀ l ∈ L, x * l * x⁻¹ ∈ L) ∧ (∀ l ∈ L, x⁻¹ * l * x ∈ L) ∧
        x * t * x⁻¹ * t⁻¹ ∈ L := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with hxL | rfl
      · refine ⟨fun l hl => L.mul_mem (L.mul_mem hxL hl) (L.inv_mem hxL),
          fun l hl => L.mul_mem (L.mul_mem (L.inv_mem hxL) hl) hxL, ?_⟩
        have h2 : (x * t * x⁻¹ * t⁻¹)⁻¹ ∈ L := by
          rw [show (x * t * x⁻¹ * t⁻¹)⁻¹ = t * x * t⁻¹ * x⁻¹ by group]
          exact L.mul_mem (htL x hxL) (L.inv_mem hxL)
        simpa using L.inv_mem h2
      · refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
        · simpa [htinv] using htL l hl
        · simpa [htinv] using htL l hl
        · simp [ht, htinv]
    | one =>
      exact ⟨fun l hl => by simpa using hl, fun l hl => by simpa using hl, by simp⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨?_, ?_, ?_⟩
      · intro l hl
        have h1 : x * y * l * (x * y)⁻¹ = x * (y * l * y⁻¹) * x⁻¹ := by group
        rw [h1]
        exact ihx.1 _ (ihy.1 l hl)
      · intro l hl
        have h1 : (x * y)⁻¹ * l * (x * y) = y⁻¹ * (x⁻¹ * l * x) * y := by group
        rw [h1]
        exact ihy.2.1 _ (ihx.2.1 l hl)
      · have h1 : x * y * t * (x * y)⁻¹ * t⁻¹ =
            x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ * (x * t * x⁻¹ * t⁻¹) := by group
        rw [h1]
        exact L.mul_mem (ihx.1 _ ihy.2.2) ihx.2.2
    | inv x hx ihx =>
      refine ⟨?_, ?_, ?_⟩
      · intro l hl
        simpa using ihx.2.1 l hl
      · intro l hl
        simpa using ihx.1 l hl
      · have h1 : x⁻¹ * t * (x⁻¹)⁻¹ * t⁻¹ = x⁻¹ * (x * t * x⁻¹ * t⁻¹)⁻¹ * x := by
          group
        rw [h1]
        exact ihx.2.1 _ (L.inv_mem ihx.2.2)
  exact (key h (by
    rwa [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure])).2.2

private theorem exists_conj_ne_commute_mul_mem_aux {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsQuasisimple ↥L) (heven : Even (Nat.card ↥L)) {t : G}
    (ht : t * t = 1) (htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hnc : ∃ l ∈ L, t * l ≠ l * t) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹) ∧
      g * t * g⁻¹ * t ∈ L := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let H : Subgroup G := L ⊔ Subgroup.zpowers t
  have hH : H = L ⊔ Subgroup.zpowers t := rfl
  have hLH : L ≤ H := by rw [hH]; exact le_sup_left
  have htH : t ∈ H := by
    rw [hH]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hcommL : ∀ h ∈ H, h * t * h⁻¹ * t⁻¹ ∈ L := fun h hh =>
    commutator_mem_of_mem_sup ht htL (hH ▸ hh)
  have ht1 : t ≠ 1 := by
    obtain ⟨l, hl, hne⟩ := hnc
    intro h1
    exact hne (by rw [h1, one_mul, mul_one])
  by_contra hno
  have hiso : ∀ h ∈ H, (h * t * h⁻¹) * t = t * (h * t * h⁻¹) → h * t * h⁻¹ = t := by
    intro h hh hc
    by_contra hne
    exact hno ⟨h, hne, hc, by simpa [htinv] using hcommL h hh⟩
  have hZ := CFSG.OddStandard.SmallF3.Omega.sec10_zStar (H := H) (t := t) htH ht1 ht hiso
  let M : Subgroup ↥L := (CFSG.OddStandard.SmallF3.Omega.oddCoreIn H).subgroupOf L
  have hM : M = (CFSG.OddStandard.SmallF3.Omega.oddCoreIn H).subgroupOf L := rfl
  have hHnorm : H ≤ Subgroup.normalizer
      ((CFSG.OddStandard.SmallF3.Omega.oddCoreIn H) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.OddStandard.SmallF3.Omega.oddCoreIn_normal H).1).mp
      (CFSG.OddStandard.SmallF3.Omega.oddCoreIn_normal H).2
  have hMn : M.Normal := by
    rw [hM]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (hLH.trans hHnorm)
  have hModd : Odd (Nat.card M) := by
    have hle : M.map L.subtype ≤ CFSG.OddStandard.SmallF3.Omega.oddCoreIn H := by
      rintro x ⟨m, hm, rfl⟩
      rw [hM] at hm
      exact Subgroup.mem_subgroupOf.mp hm
    have hcard : Nat.card M = Nat.card (M.map L.subtype) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
    rw [hcard]
    exact (CFSG.OddStandard.SmallF3.Omega.odd_card_oddCoreIn H).of_dvd_nat
      (Subgroup.card_dvd_of_le hle)
  have hMle : M ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hMn with htop | hle
    · exfalso
      have hcardL : Nat.card ↥L = Nat.card M := by
        rw [htop, Subgroup.card_top]
      have hoddL : Odd (Nat.card ↥L) := by
        rw [hcardL]
        exact hModd
      exact (Nat.not_even_iff_odd.mpr hoddL) heven
    · exact hle
  have hcentral : ∀ l ∈ L,
      t * l * t⁻¹ * l⁻¹ ∈ (Subgroup.center ↥L).map L.subtype := by
    intro l hl
    have hxL : l * t * l⁻¹ * t⁻¹ ∈ L :=
      commutator_mem_of_mem_sup ht htL (hH ▸ hLH hl)
    have hxO : l * t * l⁻¹ * t⁻¹ ∈ CFSG.OddStandard.SmallF3.Omega.oddCoreIn H :=
      hZ l (hLH hl)
    have hxM : (⟨l * t * l⁻¹ * t⁻¹, hxL⟩ : ↥L) ∈ M := by
      rw [hM]
      exact Subgroup.mem_subgroupOf.mpr hxO
    have hxZ : (⟨l * t * l⁻¹ * t⁻¹, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := hMle hxM
    refine ⟨(⟨l * t * l⁻¹ * t⁻¹, hxL⟩ : ↥L)⁻¹, (Subgroup.center ↥L).inv_mem hxZ, ?_⟩
    change (((⟨l * t * l⁻¹ * t⁻¹, hxL⟩ : ↥L)⁻¹ : ↥L) : G) = t * l * t⁻¹ * l⁻¹
    rw [Subgroup.coe_inv, Subtype.coe_mk]
    group
  have htN : t ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact fun hb => htL b hb
    · intro hb
      have h2 : t * (t * b * t⁻¹) * t⁻¹ ∈ L := htL _ hb
      have he : t * (t * b * t⁻¹) * t⁻¹ = b := by
        rw [show t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t⁻¹ * t⁻¹) by group,
          ht, htinv, ht]
        simp
      rwa [he] at h2
  have hLperf : commutator ↥L = ⊤ := hL.1.commutator_eq_top
  have hcen : ∀ l ∈ L, t * l * t⁻¹ = l :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2214_comm_eq_one_of_central hLperf htN hcentral
  obtain ⟨l, hl, hne⟩ := hnc
  refine hne ?_
  have h1 : t * l * t = l := by
    have h := hcen l hl
    rwa [htinv] at h
  calc t * l = t * l * (t * t) := by rw [ht, mul_one]
    _ = (t * l * t) * t := by group
    _ = l * t := by rw [h1]

theorem exists_conj_ne_commute_mul_mem_of_quasisimple {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsQuasisimple ↥L) (heven : Even (Nat.card ↥L)) {t : G}
    (ht : t * t = 1) (htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hnc : ∃ l ∈ L, t * l ≠ l * t) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹) ∧
      g * t * g⁻¹ * t ∈ L := by
  classical
  let e : G ≃* Shrink.{0} G := Shrink.mulEquiv.symm
  let L' : Subgroup (Shrink.{0} G) := L.map e.toMonoidHom
  have hL'def : L' = L.map e.toMonoidHom := rfl
  let t' : Shrink.{0} G := e t
  have hL' : IsQuasisimple ↥L' := by
    rw [hL'def]
    exact (IsQuasisimple.congr (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective)).mp hL
  have hcardL : Nat.card ↥L' = Nat.card ↥L := by
    rw [hL'def]
    exact Subgroup.card_map_of_injective e.injective
  have heven' : Even (Nat.card ↥L') := hcardL.symm ▸ heven
  have ht' : t' * t' = 1 := by
    simpa [t', map_mul] using congrArg e ht
  have htL' : ∀ l ∈ L', t' * l * t'⁻¹ ∈ L' := by
    intro l hl
    rw [hL'def] at hl
    rw [hL'def, Subgroup.mem_map_equiv]
    simpa [t', map_mul, map_inv] using htL (e.symm l) (Subgroup.mem_map_equiv.mp hl)
  have hnc' : ∃ l ∈ L', t' * l ≠ l * t' := by
    obtain ⟨l, hl, hne⟩ := hnc
    refine ⟨e l, ?_, ?_⟩
    · rw [hL'def]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hl
    · intro h
      exact hne (by simpa [t', map_mul] using congrArg e.symm h)
  obtain ⟨g', hne', hcomm', hmem'⟩ :=
    exists_conj_ne_commute_mul_mem_aux hL' heven' ht' htL' hnc'
  refine ⟨e.symm g', ?_, ?_, ?_⟩
  · intro h
    exact hne' (by simpa [t', map_mul, map_inv] using congrArg e h)
  · simpa [t', map_mul, map_inv] using congrArg e.symm hcomm'
  · rw [hL'def, Subgroup.mem_map_equiv] at hmem'
    simpa [t', map_mul, map_inv] using hmem'

end CFSG.LocalAnalysis.WeakClosure81
