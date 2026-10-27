module

public import CFSG.Monster.Schur.GmatStructureAssembly
public import CFSG.Monster.Schur.Restriction

public section

namespace CFSG.Monster.Schur

open Subgroup

variable {G : Type*} [Group G]

theorem exists_not_mem_four {Z : Subgroup G} [Finite Z] (h : 4 < Nat.card Z) (a b c d : G) :
    ∃ u ∈ Z, u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (Z : Set G) ⊆ (({a, b, c, d} : Finset G) : Set G) := by
    intro u hu
    by_cases h1 : u = a
    · simp [h1]
    by_cases h2 : u = b
    · simp [h2]
    by_cases h3 : u = c
    · simp [h3]
    have := hcon u hu h1 h2 h3
    simp [this]
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : Nat.card Z = (Z : Set G).ncard := Nat.card_coe_set_eq _
  have h3 : ({a, b, c, d} : Finset G).card ≤ 4 := Finset.card_le_four
  omega

theorem exists_centralKernel_of_card_ker_eq_two {E : Type*} [Group E] (π : E →* G)
    (h : Nat.card π.ker = 2) : ∃ n : E, CentralKernel π n := by
  obtain ⟨n, hn1, hn, hn2, hker⟩ := exists_central_involution_of_card_ker_eq_two π h
  exact ⟨n, hn, hn2, hn1, hker⟩

structure SchurSetting (Gm : Subgroup G) (τ x : G) (Qx Cx : Subgroup G) : Prop where
  finite : Finite Gm
  τ_mem : τ ∈ Gm
  Qx_le : Qx ≤ Gm
  Cx_le : Cx ≤ Gm
  Qx_le_Cx : Qx ≤ Cx
  ext : IsExtraspecialAmbient Qx x
  norm_Qx : ∀ g ∈ Cx, ∀ a ∈ Qx, g * a * g⁻¹ ∈ Qx
  cent : ∀ g ∈ Gm, g * x = x * g → g ∈ Cx
  y_mem : τ * x * τ⁻¹ ∈ Qx
  x_mem : τ⁻¹ * x * τ ∈ Qx
  xy_ne : x ≠ τ * x * τ⁻¹
  Z_low : 2 * Nat.card Qx ≤
    Nat.card ↥(Qx ⊓ conjSub τ Qx) * Nat.card ↥(Qx ⊓ conjSub τ Qx)
  Z_big : 4 < Nat.card ↥(Qx ⊓ conjSub τ Qx)
  W3 : ∀ r ∈ conjSub τ Qx ⊓ Cx,
    (∀ g ∈ Cx ⊓ conjSub τ Cx, r⁻¹ * (g * r * g⁻¹) ∈ Qx) → r ∈ Qx
  split : ∃ (A : Type) (_ : Group A), Group.IsPerfect A ∧ NoPerfectDoubleCover A ∧
    ∃ ψ : ↥(Qx ⊔ (Cx ⊓ conjSub τ Cx)) →* A, Function.Surjective ψ ∧
      ψ.ker = (Qx ⊔ (conjSub τ Qx ⊓ Cx)).subgroupOf (Qx ⊔ (Cx ⊓ conjSub τ Cx))
  odd : Odd ((Qx ⊔ (Cx ⊓ conjSub τ Cx)).relIndex Gm)

@[expose] def LemmaAConclusion (Gm : Subgroup G) (Qx Cx : Subgroup G) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G) (n : E), CentralKernel π n → π.range = Gm →
    ∃ Sx : Subgroup E, IsLiftComplement π n Qx Sx ∧
      ∀ c ∈ Cx.comap π, ∀ s ∈ Sx, c * s * c⁻¹ ∈ Sx

theorem mem_conjSub_of_mem {g : G} {S : Subgroup G} {Gm : Subgroup G} (hg : g ∈ Gm)
    (hS : S ≤ Gm) : conjSub g S ≤ Gm := by
  intro h hh
  rw [mem_conjSub] at hh
  have := Gm.mul_mem (Gm.mul_mem hg (hS hh)) (Gm.inv_mem hg)
  simpa [mul_assoc] using this

theorem conjSub_normalizes {g : G} {C S : Subgroup G} (hn : ∀ c ∈ C, ∀ a ∈ S, c * a * c⁻¹ ∈ S) :
    ∀ c ∈ conjSub g C, ∀ a ∈ conjSub g S, c * a * c⁻¹ ∈ conjSub g S := by
  intro c hc a ha
  rw [mem_conjSub] at hc ha ⊢
  have := hn _ hc _ ha
  convert this using 1
  group

variable {Gm : Subgroup G} {τ x : G} {Qx Cx : Subgroup G}

theorem noPerfectDoubleCover_of_setting (S : SchurSetting Gm τ x Qx Cx)
    (hA : LemmaAConclusion Gm Qx Cx) : NoPerfectDoubleCover ↥Gm := by
  have hfin := S.finite
  refine noPerfectDoubleCover_of_odd_index_complement ?_
  intro E _ π0 hπ0 hE h2
  set π : E →* G := Gm.subtype.comp π0 with hπdef
  have hker : π.ker = π0.ker := by
    ext e
    simp [hπdef, MonoidHom.mem_ker]
  have hrange : π.range = Gm := by
    ext g
    refine ⟨fun ⟨e, he⟩ => he ▸ (π0 e).2, fun hg => ?_⟩
    obtain ⟨e, he⟩ := hπ0 ⟨g, hg⟩
    exact ⟨e, congrArg Subtype.val he⟩
  obtain ⟨n, hπ⟩ := exists_centralKernel_of_card_ker_eq_two (π := π) (hker ▸ h2)
  have hEfin : Finite E := finite_of_card_ker_ne_zero π0 (by rw [h2]; norm_num)
  obtain ⟨Sx, hSx, hnx⟩ := hA E π n hπ hrange
  obtain ⟨t, ht⟩ : τ ∈ π.range := hrange ▸ S.τ_mem
  set y : G := τ * x * τ⁻¹ with hy
  set Qy : Subgroup G := conjSub τ Qx with hQy
  set Cy : Subgroup G := conjSub τ Cx with hCy
  have hSy : IsLiftComplement π n Qy (conjSub t Sx) := by
    have := hSx.conj hπ t
    rwa [ht] at this
  have hny : ∀ c ∈ Cy.comap π, ∀ s ∈ conjSub t Sx, c * s * c⁻¹ ∈ conjSub t Sx := by
    have := conj_normalizes hnx t
    rwa [ht] at this
  have hQyGm : Qy ≤ Gm := mem_conjSub_of_mem S.τ_mem S.Qx_le
  have hCyGm : Cy ≤ Gm := mem_conjSub_of_mem S.τ_mem S.Cx_le
  have hQx : Qx ≤ π.range := hrange ▸ S.Qx_le
  have hQy' : Qy ≤ π.range := hrange ▸ hQyGm
  have hCV : Cx ⊓ Cy ≤ π.range := hrange ▸ inf_le_left.trans S.Cx_le
  have hnQy : ∀ g ∈ Cy, ∀ a ∈ Qy, g * a * g⁻¹ ∈ Qy := conjSub_normalizes S.norm_Qx
  have hQyCy : Qy ≤ Cy := conjSub_mono τ S.Qx_le_Cx
  have hQyext : IsExtraspecialAmbient Qy y := S.ext.conj τ
  have hfinQx : Finite Qx := Finite.of_injective (Subgroup.inclusion S.Qx_le)
    (Subgroup.inclusion_injective _)
  have hfinQy : Finite Qy := Finite.of_injective (Subgroup.inclusion hQyGm)
    (Subgroup.inclusion_injective _)
  have hxQy : x ∈ Qy := by
    rw [hQy, mem_conjSub]
    exact S.x_mem
  have hyQx : y ∈ Qx := S.y_mem
  have hxy : x ≠ y := S.xy_ne
  have hyQy : y ∈ Qy := hQyext.mem
  have hxQx : x ∈ Qx := S.ext.mem
  have hy1 : y ≠ 1 := hQyext.ne_one
  have hx1 : x ≠ 1 := S.ext.ne_one
  have hZab : ∀ a ∈ Qx ⊓ Qy, ∀ b ∈ Qx ⊓ Qy, a * b = b * a := by
    intro a ha b hb
    rcases S.ext.comm a ha.1 b hb.1 with h | h
    · exact h
    · rcases hQyext.comm a ha.2 b hb.2 with h' | h'
      · exact h'
      · exact absurd (mul_right_cancel (h.symm.trans h')) hxy
  have hxy_comm : x * y = y * x := hZab x ⟨hxQx, hxQy⟩ y ⟨hyQx, hyQy⟩
  have hZfin : Finite ↥(Qx ⊓ Qy) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  obtain ⟨u, huZ, hu1, hux, huy, huxy⟩ := exists_not_mem_four S.Z_big 1 x y (x * y)
  have hcentY : ∀ g ∈ Gm, g * y = y * g → g ∈ Cy := by
    intro g hg hgy
    rw [hCy, mem_conjSub]
    refine S.cent _ (Gm.mul_mem (Gm.mul_mem (Gm.inv_mem S.τ_mem) hg) S.τ_mem) ?_
    have h1 : g * (τ * x * τ⁻¹) = (τ * x * τ⁻¹) * g := hgy
    calc τ⁻¹ * g * τ * x = τ⁻¹ * (g * (τ * x * τ⁻¹)) * τ := by group
      _ = τ⁻¹ * ((τ * x * τ⁻¹) * g) * τ := by rw [h1]
      _ = x * (τ⁻¹ * g * τ) := by group
  obtain ⟨ζy, hζySy, hζyπ⟩ := hSy.exists_lift hπ hyQy (hQy' hyQy)
  have hζySx : ζy ∈ Sx := by
    obtain ⟨v, hvQy, hvx, hvu⟩ := hQyext.exists_comm_not_comm hxQy hx1 hxy huZ.2 hu1 hux huy huxy
    have huv : u * v * u⁻¹ * v⁻¹ = y := by
      rcases hQyext.comm v hvQy u huZ.2 with h | h
      · exact absurd h hvu
      · have hyy := hQyext.mul_self
        calc u * v * u⁻¹ * v⁻¹ = (y * y) * (u * v) * u⁻¹ * v⁻¹ := by rw [hyy, one_mul]
          _ = y * (y * (u * v)) * u⁻¹ * v⁻¹ := by group
          _ = y * (v * u) * u⁻¹ * v⁻¹ := by rw [← h]
          _ = y := by group
    exact lemmaB hπ hSx hSy hQx hQy' hnx huZ ⟨hvQy, S.cent v (hQyGm hvQy) hvx⟩ huv hζySy hζyπ
  obtain ⟨ζx, hζxSx, hζxπ⟩ := hSx.exists_lift hπ hxQx (hQx hxQx)
  have hζxSy : ζx ∈ conjSub t Sx := by
    have huyx : u ≠ y * x := hxy_comm ▸ huxy
    obtain ⟨v, hvQx, hvy, hvu⟩ := S.ext.exists_comm_not_comm hyQx hy1 hxy.symm huZ.1 hu1 huy hux
      huyx
    have huv : u * v * u⁻¹ * v⁻¹ = x := by
      rcases S.ext.comm v hvQx u huZ.1 with h | h
      · exact absurd h hvu
      · have hxx := S.ext.mul_self
        calc u * v * u⁻¹ * v⁻¹ = (x * x) * (u * v) * u⁻¹ * v⁻¹ := by rw [hxx, one_mul]
          _ = x * (x * (u * v)) * u⁻¹ * v⁻¹ := by group
          _ = x * (v * u) * u⁻¹ * v⁻¹ := by rw [← h]
          _ = x := by group
    exact lemmaB hπ hSy hSx hQy' hQx hny (u := u) (v := v) (y := x) ⟨huZ.2, huZ.1⟩
      ⟨hvQx, hcentY v (S.Qx_le hvQx) hvy⟩ huv hζxSx hζxπ
  have hC : ∀ s ∈ Sx, π s ∈ Qy → s ∈ conjSub t Sx := by
    refine lemmaC hπ hSx hSy hQx hQy' hCV hnx hny (fun g hg a ha => S.norm_Qx g hg a ha) hnQy
      hQyext hZab ?_ ⟨ζx, ⟨hζxSx, hζxSy⟩, hζxπ⟩ ⟨ζy, ⟨hζySx, hζySy⟩, hζyπ⟩
      (fun g hg h => S.cent g (hQyGm hg) h) S.W3
    have := S.Z_low
    rwa [← natCard_conjSub τ Qx] at this
  obtain ⟨A, _, hAp, hND, ψ, hψ, hψker⟩ := S.split
  have hP : Qx ⊔ (Cx ⊓ Cy) ≤ π.range :=
    hrange ▸ sup_le S.Qx_le (inf_le_left.trans S.Cx_le)
  obtain ⟨D, -, hDinf, hDsup⟩ := exists_complement_over hπ hSx hSy hQx hQy' hCV hnx hny
    (fun g hg a ha => S.norm_Qx g hg a ha) hnQy hQyCy hC rfl rfl hAp hND ψ hψ hψker hP
  refine ⟨(Qx ⊔ (Cx ⊓ Cy)).comap π, D, ?_, ?_, ?_⟩
  · rw [Subgroup.index_comap, hrange]
    exact S.odd
  · rw [← hker, hπ.ker]
    exact hDinf
  · rw [← hker, hπ.ker]
    exact hDsup

end CFSG.Monster.Schur
