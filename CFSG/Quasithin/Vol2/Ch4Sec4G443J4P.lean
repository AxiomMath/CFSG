module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4R

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin

namespace Lay

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem exists_mul_of_mem_sup {S E : Subgroup Y} (hSE : S ≤ Subgroup.centralizer (E : Set Y))
    {x : Y} (hx : x ∈ S ⊔ E) : ∃ s ∈ S, ∃ e ∈ E, s * e = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S E
    (hSE.trans (Subgroup.centralizer_le_normalizer _))] at hx
  exact hx

theorem exists_proj_hom (hY : CFSG.solvableRadical Y = ⊥) {S : Subgroup Y}
    (hS : CFSG.IsComponent S) :
    ∃ φ : ↥(CFSG.layer Y) →* Y, φ.range ≤ S ∧
      ∀ x, φ x = 1 → (x : Y) ∈ Subgroup.centralizer (S : Set Y) := by
  set E' : Subgroup Y := sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} with hE'
  obtain ⟨hE'C, hlayer⟩ := layer_eq_sup_others hS
  have hSL : S ≤ CFSG.layer Y := CFSG.LocalCores.component_le_layer hS
  have hE'L : E' ≤ CFSG.layer Y := hlayer ▸ le_sup_right
  have hSE : S ≤ Subgroup.centralizer (E' : Set Y) := Subgroup.le_centralizer_iff.mp hE'C
  have hLN : CFSG.layer Y ≤ Subgroup.normalizer (E' : Set Y) := by
    rw [hlayer]
    exact sup_le (hSE.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hN : (E'.subgroupOf (CFSG.layer Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE'L).mpr hLN
  set q := QuotientGroup.mk' (E'.subgroupOf (CFSG.layer Y)) with hq
  set ψ : ↥S →* ↥(CFSG.layer Y) ⧸ E'.subgroupOf (CFSG.layer Y) :=
    q.comp (Subgroup.inclusion hSL) with hψ
  have hSE1 : S ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxc : (⟨x, hx.1⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hE'C hx.2) s s.2)
    rw [center_component_eq_bot hY hS, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    rw [hψ, MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hs
    have h1 : (s : Y) ∈ S ⊓ E' := ⟨s.2, hs⟩
    rw [hSE1, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hx : (x : Y) ∈ S ⊔ E' := by
      rw [← hlayer]
      exact x.2
    obtain ⟨s, hs, e, he, hse⟩ := exists_mul_of_mem_sup hSE hx
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (s : Y)⁻¹ * x ∈ E'
    rw [← hse]
    simpa using he
  set eS := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩ with heS
  refine ⟨S.subtype.comp (eS.symm.toMonoidHom.comp q), ?_, fun x hx => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (eS.symm (q x)).2
  · rw [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.comp_apply,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, OneMemClass.coe_eq_one,
      MulEquiv.map_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hx
    exact hE'C hx

theorem le_of_commute_others (hY : CFSG.solvableRadical Y = ⊥) {S B : Subgroup Y}
    (hS : CFSG.IsComponent S) (hBE : B ≤ CFSG.layer Y)
    (hB : ∀ T : Subgroup Y, CFSG.IsComponent T → T ≠ S → ⁅T, B⁆ = ⊥) : B ≤ S := by
  obtain ⟨hφ, hφS, hφk⟩ := exists_proj_hom hY hS
  set E' : Subgroup Y := sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} with hE'
  obtain ⟨hE'C, hlayer⟩ := layer_eq_sup_others hS
  have hSE : S ≤ Subgroup.centralizer (E' : Set Y) := Subgroup.le_centralizer_iff.mp hE'C
  have hBC : B ≤ Subgroup.centralizer (E' : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun T hT =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hB T hT.1 hT.2)
  intro b hb
  have hb' : b ∈ S ⊔ E' := by
    rw [← hlayer]
    exact hBE hb
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup hSE hb'
  have he1 : e = 1 := by
    have heZ : e ∈ (Subgroup.center (CFSG.layer Y)).map (CFSG.layer Y).subtype := by
      have hE'L : E' ≤ CFSG.layer Y := hlayer ▸ le_sup_right
      refine (CFSG.LocalCores.mem_map_center_iff _).mpr ⟨hE'L he, ?_⟩
      rw [hlayer, Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨s', hs', e', he', rfl⟩ := exists_mul_of_mem_sup hSE hy
      have h1 : s' * e = e * s' := (Subgroup.mem_centralizer_iff.mp (hE'C he) s' hs')
      have h2 : e' * e = e * e' := by
        have hb2 := Subgroup.mem_centralizer_iff.mp (hBC hb) e' he'
        have hs2 := Subgroup.mem_centralizer_iff.mp (hSE hs) e' he'
        calc e' * e = s⁻¹ * (e' * (s * e)) := by
              rw [show e' * (s * e) = s * e' * e by rw [← mul_assoc, ← hs2]]
              group
          _ = s⁻¹ * ((s * e) * e') := by rw [hb2]
          _ = e * e' := by group
      calc s' * e' * e = s' * (e' * e) := by group
        _ = s' * (e * e') := by rw [h2]
        _ = (s' * e) * e' := by group
        _ = (e * s') * e' := by rw [h1]
        _ = e * (s' * e') := by group
    rw [center_layer_eq_bot hY, Subgroup.mem_bot] at heZ
    exact heZ
  rw [he1, mul_one]
  exact hs

end Lay

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_or_le_ker {B N : Subgroup X} (hBp : ⁅B, B⁆ = B) {S : Type} [Group S]
    [IsSimpleGroup S] (g : ↥B →* S) (hg : Function.Surjective g)
    (hgk : Group.IsSolvable ↥g.ker) (hNB : N ≤ B) (hNn : B ≤ Subgroup.normalizer (N : Set X)) :
    N = B ∨ ∀ b : ↥B, (b : X) ∈ N → g b = 1 := by
  have hN'n : (N.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr hNn
  have hgn : ((N.subgroupOf B).map g).Normal := Subgroup.Normal.map hN'n g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf B).map g) with h | h
  · right
    intro b hb
    have : g b ∈ (N.subgroupOf B).map g := ⟨b, hb, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  · left
    set W := g.ker.map B.subtype with hW
    have hWs : Group.IsSolvable ↥W := Group.isSolvable_of_surjective
      (f := (g.ker.equivMapOfInjective B.subtype B.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
    have hBNW : B = N ⊔ W := by
      refine le_antisymm (fun b hb => ?_) (sup_le hNB (Subgroup.map_le_iff_le_comap.mpr
        fun x _ => x.2))
      have hgb : g ⟨b, hb⟩ ∈ (N.subgroupOf B).map g := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnb⟩ := hgb
      have hk : n⁻¹ * ⟨b, hb⟩ ∈ g.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hnb,
        inv_mul_cancel]
      have e : b = (n : X) * ((n⁻¹ * ⟨b, hb⟩ : ↥B) : X) := by simp
      rw [e]
      exact Subgroup.mul_mem_sup hn ⟨_, hk, rfl⟩
    have h1 := perfectCore_le_of_sup_solvable hNB hN'n hBNW hWs
    rw [perfectCore_eq_self_of_perfect hBp] at h1
    exact le_antisymm hNB h1

end CFSG.Quasithin.H13.Ch4.G443J4
