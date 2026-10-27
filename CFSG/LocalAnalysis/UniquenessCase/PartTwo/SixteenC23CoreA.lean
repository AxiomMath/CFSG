module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_card_wTil_conj {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hx : x ∈ stabTil V₀ V) (L : Subgroup G) :
    Nat.card (wTil V₀ V hV (conjSubgroup L x)) = Nat.card (wTil V₀ V hV L) := by
  rw [s15_Infra_wTil_conjSubgroup V₀ V L hV hx]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem c23_fix_wTil_of_nBar {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {g : G} (hg : g ∈ D.M) (hgn : g ∉ nBar D.M V₀ V hV L) :
    ∀ a ∈ barSub V₀ V hV (conjSubgroup L g), ∀ y ∈ wTil V₀ V hV L,
      (a : MulAut (Vtil V₀ V hV)) y = y := by
  intro a ha y hy
  have hc := (h.commute g hg hgn).2
  rw [commSub_eq_bot_iff] at hc
  exact mem_fixV.1 (hc hy) a ha

theorem c23_fix_wTil_conj {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {x : G} (hx : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L) :
    ∀ a ∈ barSub V₀ V hV L, ∀ y ∈ wTil V₀ V hV (conjSubgroup L x),
      (a : MulAut (Vtil V₀ V hV)) y = y := by
  intro a ha y hy
  have hxs : x ∈ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hx
  have hxinv : x⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem hxs
  have hxm : x⁻¹ ∈ D.M := D.M.inv_mem hx
  have hxmn : x⁻¹ ∉ nBar D.M V₀ V hV L := fun hc =>
    hxn (by simpa using (nBar D.M V₀ V hV L).inv_mem hc)
  have hfix := c23_fix_wTil_of_nBar h hV hxm hxmn
  rw [s15_Infra_wTil_conjSubgroup V₀ V L hV hxs] at hy
  obtain ⟨y', hy', hyeq⟩ := Subgroup.mem_map.1 hy
  have hact : (actTil V₀ V hV ⟨x⁻¹, hxinv⟩)⁻¹ = actTil V₀ V hV ⟨x, hxs⟩ := by
    rw [show (⟨x⁻¹, hxinv⟩ : stabTil V₀ V) = (⟨x, hxs⟩ : stabTil V₀ V)⁻¹
      from Subtype.ext rfl, map_inv, inv_inv]
  have ha' : MulAut.conj (actTil V₀ V hV ⟨x, hxs⟩) a ∈
      barSub V₀ V hV (conjSubgroup L x⁻¹) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hxinv L]
    exact Subgroup.mem_map.2 ⟨a, ha, by
      simp only [MulEquiv.coe_toMonoidHom]; rw [hact]⟩
  have h1 : actTil V₀ V hV ⟨x, hxs⟩ (a y) =
      (MulAut.conj (actTil V₀ V hV ⟨x, hxs⟩) a) y' := by
    rw [← hyeq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply]
  calc a y = (actTil V₀ V hV ⟨x, hxs⟩)⁻¹ (actTil V₀ V hV ⟨x, hxs⟩ (a y)) :=
        (MulAut.inv_apply_self (Vtil V₀ V hV) (actTil V₀ V hV ⟨x, hxs⟩) (a y)).symm
    _ = (actTil V₀ V hV ⟨x, hxs⟩)⁻¹
          ((MulAut.conj (actTil V₀ V hV ⟨x, hxs⟩) a) y') := congrArg _ h1
    _ = (actTil V₀ V hV ⟨x, hxs⟩)⁻¹ y' :=
          congrArg _ (hfix (MulAut.conj (actTil V₀ V hV ⟨x, hxs⟩) a) ha' y' hy')
    _ = y := hyeq

theorem c23_exists_trans_conj {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hx : x ∈ stabTil V₀ V)
    (htr : ∀ u ∈ wTil V₀ V hV L, u ≠ 1 → ∀ u' ∈ wTil V₀ V hV L, u' ≠ 1 →
      ∃ φ ∈ barSub V₀ V hV L, (φ : MulAut (Vtil V₀ V hV)) u = u') :
    ∀ y ∈ wTil V₀ V hV (conjSubgroup L x), y ≠ 1 → ∀ y' ∈ wTil V₀ V hV (conjSubgroup L x),
      y' ≠ 1 → ∃ a ∈ barSub V₀ V hV (conjSubgroup L x), (a : MulAut (Vtil V₀ V hV)) y = y' := by
  intro y hy hy1 y' hy' hy'1
  rw [s15_Infra_wTil_conjSubgroup V₀ V L hV hx] at hy
  rw [s15_Infra_wTil_conjSubgroup V₀ V L hV hx] at hy'
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.1 hy
  obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.1 hy'
  have hu1 : u ≠ 1 := fun hc => hy1 (by rw [← hueq, hc, map_one])
  have hu'1 : u' ≠ 1 := fun hc => hy'1 (by rw [← hu'eq, hc, map_one])
  obtain ⟨φ, hφ, hφu⟩ := htr u hu hu1 u' hu' hu'1
  have hueq' : (actTil V₀ V hV ⟨x, hx⟩)⁻¹ u = y := by
    simpa only [MulEquiv.coe_toMonoidHom] using hueq
  refine ⟨MulAut.conj (actTil V₀ V hV ⟨x, hx⟩)⁻¹ φ, ?_, ?_⟩
  · rw [s15_Infra_barSub_conjSubgroup V₀ V hV hx L]
    exact Subgroup.mem_map.2 ⟨φ, hφ, rfl⟩
  · calc (MulAut.conj (actTil V₀ V hV ⟨x, hx⟩)⁻¹ φ) y
        = (MulAut.conj (actTil V₀ V hV ⟨x, hx⟩)⁻¹ φ)
            ((actTil V₀ V hV ⟨x, hx⟩)⁻¹ u) := by rw [hueq']
      _ = (actTil V₀ V hV ⟨x, hx⟩)⁻¹ (φ u) := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
              inv_inv, MulAut.apply_inv_self]
      _ = (actTil V₀ V hV ⟨x, hx⟩)⁻¹ u' := by rw [hφu]
      _ = y' := hu'eq

theorem c23_perm_wTil {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2) (hL : barSub V₀ V hV L ≠ ⊥) {x : G}
    (hx : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L) :
    ∀ φ ∈ Mbar D.M V₀ V hV,
      ((wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV L ∧
        (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom = wTil V₀ V hV (conjSubgroup L x)) ∨
      ((wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV (conjSubgroup L x) ∧
        (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom = wTil V₀ V hV L) := by
  intro φ hφ
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hxs : x ∈ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hx
  have hYne : wTil V₀ V hV L ≠ wTil V₀ V hV (conjSubgroup L x) := by
    intro heq
    have hiff := s15_Core_wTil_conj_eq_iff h hL (m := 1) (m' := x) D.M.one_mem hx
    rw [conjSubgroup_one] at hiff
    exact hxn ((s15_Infra_mem_nBar_iff h.hyp125 hV hx).2 (hiff.mp heq).symm)
  have hgm : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem g.2
  have hm1 : (g : G)⁻¹ ∈ D.M := D.M.inv_mem hgM
  have hm2 : x * (g : G)⁻¹ ∈ D.M := D.M.mul_mem hx (D.M.inv_mem hgM)
  have hm2s : x * (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).mul_mem hxs hgm
  have hmap1 : (wTil V₀ V hV L).map φ.toMonoidHom =
      wTil V₀ V hV (conjSubgroup L (g : G)⁻¹) := by
    rw [← hgφ, s15_Infra_wTil_conjSubgroup V₀ V L hV hgm]
    congr 1
    rw [show (⟨(g : G)⁻¹, hgm⟩ : stabTil V₀ V) = g⁻¹ from Subtype.ext rfl,
      map_inv, inv_inv]
  have hmap2 : (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom =
      wTil V₀ V hV (conjSubgroup L (x * (g : G)⁻¹)) := by
    rw [← hgφ, s15_Infra_wTil_conjSubgroup V₀ V L hV hxs, Subgroup.map_map,
      s15_Infra_wTil_conjSubgroup V₀ V L hV hm2s]
    congr 1
    rw [show (⟨x * (g : G)⁻¹, hm2s⟩ : stabTil V₀ V) = ⟨x, hxs⟩ * g⁻¹
        from Subtype.ext rfl,
      map_mul, map_inv, mul_inv_rev, inv_inv]
    ext w
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
  have hiffA := s15_Core_wTil_conj_eq_iff h hL (m := (g : G)⁻¹) (m' := 1) hm1 D.M.one_mem
  rw [conjSubgroup_one] at hiffA
  have hiffB := s15_Core_wTil_conj_eq_iff h hL (m := (g : G)⁻¹) (m' := x) hm1 hx
  have hiffC := s15_Core_wTil_conj_eq_iff h hL (m := x * (g : G)⁻¹) (m' := 1) hm2 D.M.one_mem
  rw [conjSubgroup_one] at hiffC
  have hiffD := s15_Core_wTil_conj_eq_iff h hL (m := x * (g : G)⁻¹) (m' := x) hm2 hx
  rcases c23_barSub_conj_cases D h hV hs hx hxn hm1 with hc1 | hc1
  · have hY1 : (wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV L := by
      rw [hmap1]
      exact hiffA.mpr hc1
    rcases c23_barSub_conj_cases D h hV hs hx hxn hm2 with hc2 | hc2
    · have hY2 : (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom =
          wTil V₀ V hV L := by
        rw [hmap2]
        exact hiffC.mpr hc2
      exfalso
      have heqmap : (wTil V₀ V hV L).map φ.toMonoidHom =
          (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom := by rw [hY1, hY2]
      exact hYne ((Subgroup.map_injective (MulEquiv.injective φ)) heqmap)
    · exact Or.inl ⟨hY1, by rw [hmap2]; exact hiffD.mpr hc2⟩
  · have hY1 : (wTil V₀ V hV L).map φ.toMonoidHom =
        wTil V₀ V hV (conjSubgroup L x) := by
      rw [hmap1]
      exact hiffB.mpr hc1
    rcases c23_barSub_conj_cases D h hV hs hx hxn hm2 with hc2 | hc2
    · exact Or.inr ⟨hY1, by rw [hmap2]; exact hiffC.mpr hc2⟩
    · have hY2 : (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom =
          wTil V₀ V hV (conjSubgroup L x) := by
        rw [hmap2]
        exact hiffD.mpr hc2
      exfalso
      have heqmap : (wTil V₀ V hV L).map φ.toMonoidHom =
          (wTil V₀ V hV (conjSubgroup L x)).map φ.toMonoidHom := by rw [hY1, hY2]
      exact hYne ((Subgroup.map_injective (MulEquiv.injective φ)) heqmap)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
