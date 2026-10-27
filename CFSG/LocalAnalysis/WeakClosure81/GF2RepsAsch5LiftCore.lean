module

public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.A1b Subgroup

theorem exists_subgroup_stabilizer_family {G : Type} [Group G] {T L M : Subgroup G}
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hcomm : ∀ g : G, conjSub g L = L ∨ ∀ x ∈ L, ∀ y ∈ conjSub g L, x * y = y * x)
    (hML : M ≤ L) (hne : M ≠ ⊥) (hlt : M ≠ L)
    (hn : ∀ t ∈ T, conjSub t L = L → conjSub t M = M) :
    ∃ D : Subgroup G, T ≤ D ∧ M ≤ D ∧ ¬ L ≤ D := by
  classical
  let Φ : Set (Subgroup G) := {Y | ∃ s ∈ T, Y = conjSub s M}
  let D : Subgroup G :=
    { carrier := {g : G | (fun Y : Subgroup G => conjSub g Y) '' Φ = Φ}
      one_mem' := by
        change (fun Y : Subgroup G => conjSub (1 : G) Y) '' Φ = Φ
        rw [show (fun Y : Subgroup G => conjSub (1 : G) Y) = id from
          funext fun Y => conjSub_one Y, Set.image_id]
      mul_mem' := by
        intro a b ha hb
        change (fun Y : Subgroup G => conjSub (a * b) Y) '' Φ = Φ
        rw [show (fun Y : Subgroup G => conjSub (a * b) Y) =
              (fun Z : Subgroup G => conjSub a Z) ∘ (fun Y : Subgroup G => conjSub b Y)
            from funext fun Y => conjSub_mul a b Y, Set.image_comp, hb, ha]
      inv_mem' := by
        intro g hg
        change (fun Y : Subgroup G => conjSub g⁻¹ Y) '' Φ = Φ
        have h1 : (fun Y : Subgroup G => conjSub g⁻¹ Y) '' Φ =
            (fun Y : Subgroup G => conjSub g⁻¹ Y) ''
              ((fun Y : Subgroup G => conjSub g Y) '' Φ) := by rw [hg]
        rw [h1, ← Set.image_comp]
        have h2 : (fun Z : Subgroup G => conjSub g⁻¹ Z) ∘
              (fun Y : Subgroup G => conjSub g Y) =
            (fun Y : Subgroup G => conjSub (1 : G) Y) := by
          funext Y
          rw [Function.comp_apply, ← conjSub_mul, inv_mul_cancel]
        rw [h2, show (fun Y : Subgroup G => conjSub (1 : G) Y) = id from
          funext fun Y => conjSub_one Y, Set.image_id] }
  have hTD : T ≤ D := by
    intro t ht
    change (fun Y : Subgroup G => conjSub t Y) '' Φ = Φ
    apply le_antisymm
    · rintro Z ⟨Y, hY, rfl⟩
      obtain ⟨s, hsT, rfl⟩ := hY
      exact ⟨t * s, T.mul_mem ht hsT, by rw [conjSub_mul]⟩
    · rintro Z ⟨s, hsT, rfl⟩
      refine ⟨conjSub (t⁻¹ * s) M, ⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hsT, rfl⟩, ?_⟩
      show conjSub t (conjSub (t⁻¹ * s) M) = conjSub s M
      rw [← conjSub_mul, mul_inv_cancel_left]
  have hMD : M ≤ D := by
    intro m hm
    have hmL : m ∈ L := hML hm
    change (fun Y : Subgroup G => conjSub m Y) '' Φ = Φ
    have hfix : ∀ Y ∈ Φ, conjSub m Y = Y := by
      rintro Y ⟨s, hsT, rfl⟩
      by_cases hLs : conjSub s L = L
      · rw [hn s hsT hLs]
        exact conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hm)
      · have hc := (hcomm s).resolve_left hLs
        apply le_antisymm
        · intro x hx
          rw [mem_conjSub_iff] at hx
          have hxL : m⁻¹ * x * m ∈ conjSub s L := conjSub_mono s hML hx
          have hcz := hc m hmL (m⁻¹ * x * m) hxL
          have hx' : x = m⁻¹ * x * m := by
            calc x = m * (m⁻¹ * x * m) * m⁻¹ := by group
              _ = (m⁻¹ * x * m) * m * m⁻¹ := by rw [hcz]
              _ = m⁻¹ * x * m := by group
          rw [hx']
          exact hx
        · intro x hx
          rw [mem_conjSub_iff]
          have hxL : x ∈ conjSub s L := conjSub_mono s hML hx
          have hcx := hc m hmL x hxL
          have hx' : m⁻¹ * x * m = x := by
            calc m⁻¹ * x * m = m⁻¹ * (x * m) := by group
              _ = m⁻¹ * (m * x) := by rw [hcx]
              _ = x := by group
          rw [hx']
          exact hx
    have himg : (fun Y : Subgroup G => conjSub m Y) '' Φ = id '' Φ :=
      Set.image_congr hfix
    rw [himg, Set.image_id]
  refine ⟨D, hTD, hMD, ?_⟩
  intro hLD
  have hnorm : ∀ l ∈ L, conjSub l M = M := by
    intro l hl
    have hlD : (fun Y : Subgroup G => conjSub l Y) '' Φ = Φ := hLD hl
    have hMemΦ : conjSub l M ∈ Φ := by
      have : conjSub l M ∈ (fun Y : Subgroup G => conjSub l Y) '' Φ :=
        ⟨M, ⟨1, T.one_mem, (conjSub_one M).symm⟩, rfl⟩
      rwa [hlD] at this
    obtain ⟨s, hsT, hsM⟩ := hMemΦ
    have hsL : conjSub s L = L := by
      by_contra hLs
      have hc := (hcomm s).resolve_left hLs
      have hbot : conjSub s M = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hyL' : y ∈ L := by
          have hyM : y ∈ conjSub l M := by rw [hsM]; exact hy
          have hyLl : y ∈ conjSub l L := conjSub_mono l hML hyM
          have hlL : conjSub l L = L :=
            conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hl)
          rwa [hlL] at hyLl
        have hcy : ∀ x ∈ L, x * y = y * x :=
          fun x hx => hc x hx y (conjSub_mono s hML hy)
        have hy1 : y = 1 := by
          have hcenter : (⟨y, hyL'⟩ : ↥L) ∈ Subgroup.center ↥L := by
            rw [Subgroup.mem_center_iff]
            intro g
            exact Subtype.ext (by simpa using hcy g g.2)
          rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hb | ht
          · have h1 : (⟨y, hyL'⟩ : ↥L) = 1 := Subgroup.mem_bot.mp (hb ▸ hcenter)
            simpa using congrArg Subtype.val h1
          · exfalso
            obtain ⟨a, b, hab⟩ := hnab
            have hb' : b ∈ Subgroup.center ↥L := ht ▸ Subgroup.mem_top b
            exact hab (Subgroup.mem_center_iff.mp hb' a)
        rw [hy1]
        exact Subgroup.one_mem ⊥
      have hbot' : conjSub s (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _
      exact hne ((conjSub_inj s).mp (hbot.trans hbot'.symm))
    rw [hsM, hn s hsT hsL]
  have hN : (M.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hML).mpr
      (fun l hl => conjSub_eq_iff_mem_normalizer.mp (hnorm l hl))
  haveI := hN
  rcases hs.eq_bot_or_eq_top_of_normal (M.subgroupOf L) with h | h
  · exact hne (by
      have hdisj : M ⊓ L = ⊥ := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
      rwa [inf_of_le_left hML] at hdisj)
  · exact hlt (le_antisymm hML (Subgroup.subgroupOf_eq_top.mp h))

theorem exists_proper_overgroups {G : Type} [Group G] {T L M₁ M₂ : Subgroup G}
    (hLT : L ⊔ T = ⊤) (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hcomm : ∀ g : G, conjSub g L = L ∨ ∀ x ∈ L, ∀ y ∈ conjSub g L, x * y = y * x)
    (h₁ : M₁ ≤ L) (h₂ : M₂ ≤ L) (hne₁ : M₁ ≠ ⊥) (hne₂ : M₂ ≠ ⊥) (hlt₁ : M₁ ≠ L)
    (hlt₂ : M₂ ≠ L) (hsup : M₁ ⊔ M₂ = L)
    (hn₁ : ∀ t ∈ T, conjSub t L = L → conjSub t M₁ = M₁)
    (hn₂ : ∀ t ∈ T, conjSub t L = L → conjSub t M₂ = M₂) :
    ∃ D₁ D₂ : Subgroup G, T ≤ D₁ ∧ T ≤ D₂ ∧ D₁ < ⊤ ∧ D₂ < ⊤ ∧ D₁ ⊔ D₂ = ⊤ := by
  obtain ⟨D₁, hTD₁, hMD₁, hLD₁⟩ := exists_subgroup_stabilizer_family hs hnab hcomm h₁ hne₁ hlt₁ hn₁
  obtain ⟨D₂, hTD₂, hMD₂, hLD₂⟩ := exists_subgroup_stabilizer_family hs hnab hcomm h₂ hne₂ hlt₂ hn₂
  refine ⟨D₁, D₂, hTD₁, hTD₂, ?_, ?_, ?_⟩
  · refine lt_top_iff_ne_top.mpr fun h => hLD₁ ?_
    rw [h]
    exact le_top
  · refine lt_top_iff_ne_top.mpr fun h => hLD₂ ?_
    rw [h]
    exact le_top
  · rw [eq_top_iff, ← hLT, ← hsup]
    exact sup_le (sup_le (hMD₁.trans le_sup_left) (hMD₂.trans le_sup_right))
      (hTD₁.trans le_sup_left)

end CFSG.LocalAnalysis.WeakClosure81
