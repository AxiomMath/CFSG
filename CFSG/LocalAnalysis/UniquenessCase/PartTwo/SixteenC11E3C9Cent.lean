module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Prod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9CentA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_case9_E_fixed {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L)
    {x : MulAut (Vtil V₀ V hV)}
    (hxE : x ∈ (commutator ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype)
    (hx7 : x ^ 7 = 1) {v : Vtil V₀ V hV} (hv1 : v ≠ 1)
    (hvT : v ∈ fixV (barSub V₀ V hV D.T)) (hxv : x v = v) : x = 1 := by
  classical
  obtain ⟨g, hgT, hcomm, hinf, hEeq, hfixB, hfixA, hWinf, hWsup, -⟩ :=
    s1611e3_case9_prod h hc h9
  set Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hLb
  set Lp : Subgroup (MulAut (Vtil V₀ V hV)) := Lb.map (MulAut.conj g).toMonoidHom with hLp
  set Wt : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hWt
  set Wp : Subgroup (Vtil V₀ V hV) := Wt.map g.toMonoidHom with hWp
  have hL3 : IsL3 ↥Lb 1 := h9.2.1
  have hs15 : s15 D.M V₀ V hV L = 2 := h9.2.2.1
  have hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) Lb Wt ⊥ 3 := h9.2.2.2.1
  have hPSL : IsPSL 3 2 1 ↥Lb := s16c167_isPSL_of_isL3 hL3
  have hNat : NatSum3 Lb Wt := s16c167_natSum3_of_sumOfNat hsum
  have hWp_eq : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lp = Wp :=
    s16c167_commSub_top_conj g Lb
  have hxE' : x ∈ Lb ⊔ Lp := hEeq ▸ hxE
  obtain ⟨a, haL, b, hbL, hab⟩ := s1611e3_exists_mul_of_mem_sup_of_commute hcomm hxE'
  have hcommab : a * b = b * a := hcomm a haL b hbL
  have hpow : a ^ 7 * b ^ 7 = 1 := by
    rw [← Commute.mul_pow hcommab]
    rw [hab]
    exact hx7
  have ha7 : a ^ 7 = 1 := by
    have hmem : a ^ 7 ∈ Lb ⊓ Lp := by
      refine ⟨Lb.pow_mem haL 7, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact Lp.inv_mem (Subgroup.pow_mem _ hbL 7)
    rwa [hinf, Subgroup.mem_bot] at hmem
  have hb7 : b ^ 7 = 1 := by
    rw [ha7, one_mul] at hpow
    exact hpow
  obtain ⟨Q, hQ⟩ := D.sylowM
  have hTM : D.T ≤ D.M := by
    rw [← hQ]
    exact Subgroup.map_subtype_le (Q : Subgroup ↥D.M)
  have hgM : g ∈ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hTM hgT
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = Lb.map (MulAut.conj φ).toMonoidHom} = 2 := by
    simpa [s15, lBar, hLb] using hs15
  have hLb_ne_Lp : Lb ≠ Lp := by
    intro heq
    have hcard : Nat.card ↥Lb = 168 := card_eq_168_of_isPSL_three_two hPSL
    have hbot : Lb = ⊥ := by
      rw [← hinf, ← heq, inf_idem]
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hS_eq : {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = Lb.map (MulAut.conj φ).toMonoidHom} = {Lb, Lp} := by
    have hsub : ({Lb, Lp} : Set (Subgroup (MulAut (Vtil V₀ V hV)))) ⊆
        {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
          ∃ φ ∈ Mbar D.M V₀ V hV, Y = Lb.map (MulAut.conj φ).toMonoidHom} := by
      intro Y hY
      rcases hY with rfl | rfl
      · refine ⟨1, (Mbar D.M V₀ V hV).one_mem, ?_⟩
        change Lb = Lb.map (MonoidHom.id (MulAut (Vtil V₀ V hV)))
        exact (Subgroup.map_id Lb).symm
      · exact ⟨g, hgM, rfl⟩
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcls, Set.ncard_pair hLb_ne_Lp])).symm
  have hg2M : g ^ 2 ∈ Mbar D.M V₀ V hV := Subgroup.pow_mem _ hgM 2
  have hLb_g2 : Lb.map (MulAut.conj (g ^ 2)).toMonoidHom = Lb ∨
      Lb.map (MulAut.conj (g ^ 2)).toMonoidHom = Lp := by
    have hmem : Lb.map (MulAut.conj (g ^ 2)).toMonoidHom ∈
        {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
          ∃ φ ∈ Mbar D.M V₀ V hV, Y = Lb.map (MulAut.conj φ).toMonoidHom} :=
      ⟨g ^ 2, hg2M, rfl⟩
    rw [hS_eq] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hconj2 : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g ^ 2)).toMonoidHom := by
    have h1 : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g * MulAut.conj g).toMonoidHom := by
      ext y; rfl
    rw [h1, map_pow (MulAut.conj) g 2, pow_two]
  have hLb_g2' : Lb.map (MulAut.conj (g ^ 2)).toMonoidHom = Lb := by
    rcases hLb_g2 with h | h
    · exact h
    · exfalso
      have hLp_g : (Lb.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom =
          Lb.map (MulAut.conj (g ^ 2)).toMonoidHom := by
        rw [Subgroup.map_map, hconj2]
      have hLp_g_eq : (Lb.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom =
          Lb.map (MulAut.conj g).toMonoidHom := by
        rw [hLp_g, h]
      exact hLb_ne_Lp (Subgroup.map_injective (MulAut.conj g).injective hLp_g_eq.symm)
  have hWtgg : Wt.map (g ^ 2).toMonoidHom = Wt := by
    have h1 : commSub (⊤ : Subgroup (Vtil V₀ V hV))
        (Lb.map (MulAut.conj (g ^ 2)).toMonoidHom) =
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb).map (g ^ 2).toMonoidHom :=
      s16c167_commSub_top_conj (g ^ 2) Lb
    rw [hLb_g2'] at h1
    exact h1.symm
  have hgWp : Wp.map g.toMonoidHom = Wt := by
    have hgg2 : g.toMonoidHom.comp g.toMonoidHom = (g ^ 2).toMonoidHom := by
      ext y; rfl
    rw [hWp, Subgroup.map_map, hgg2, hWtgg]
  obtain ⟨w, hwWt, w', hwWp, hwv⟩ :=
    Subgroup.mem_sup.1 (by rw [hWsup]; exact Subgroup.mem_top v)
  have hgv : g v = v := mem_fixV.mp hvT g hgT
  have hgw_mem : g w ∈ Wp := Subgroup.mem_map_of_mem g.toMonoidHom hwWt
  have hgw'_mem : g w' ∈ Wt := by
    have h : g w' ∈ Wp.map g.toMonoidHom := Subgroup.mem_map_of_mem g.toMonoidHom hwWp
    rwa [hgWp] at h
  have hmul_g : g w * g w' = w * w' := by
    have h : g (w * w') = w * w' := by rw [hwv]; exact hgv
    rwa [map_mul] at h
  have hgswap : g w = w' ∧ g w' = w :=
    s1611e3_eq_of_mul_eq_mul_of_inf_bot (by rw [inf_comm]; exact hWinf)
      hgw_mem hgw'_mem hwWp hwWt (by rw [hmul_g, mul_comm])
  have hw1 : w ≠ 1 := by
    intro hw
    have hw'1 : w' = 1 := by rw [← hgswap.1, hw, map_one]
    exact hv1 (by rw [← hwv, hw, hw'1, mul_one])
  have hw'1 : w' ≠ 1 := by
    intro hw'
    have hw1' : w = 1 := by rw [← hgswap.2, hw', map_one]
    exact hv1 (by rw [← hwv, hw1', hw', mul_one])
  have hpres_Wt : ∀ a' ∈ Lb, ∀ u ∈ Wt, a' u ∈ Wt := by
    intro a' ha' u hu
    have hmap : Lb.map (MulAut.conj a').toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha')
    have h := s16c167_commSub_top_conj a' Lb
    rw [hmap] at h
    have hmem : a' u ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb).map a'.toMonoidHom := by
      show a' u ∈ Wt.map a'.toMonoidHom
      exact Subgroup.mem_map_of_mem a'.toMonoidHom hu
    rw [← h] at hmem
    exact hmem
  have hpres_Wp : ∀ b' ∈ Lp, ∀ u ∈ Wp, b' u ∈ Wp := by
    intro b' hb' u hu
    have hmap : Lp.map (MulAut.conj b').toMonoidHom = Lp :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hb')
    have h := s16c167_commSub_top_conj b' Lp
    rw [hmap] at h
    have hmem : b' u ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lp).map b'.toMonoidHom := by
      rw [hWp_eq]
      exact Subgroup.mem_map_of_mem b'.toMonoidHom hu
    rw [← h] at hmem
    rwa [← hWp_eq]
  have hxab : (a * b) v = v := by rw [hab]; exact hxv
  have hmulA : a w * b w' = w * w' := by
    have h := hxab
    rw [← hwv] at h
    simp only [MulAut.mul_apply, map_mul] at h
    rw [hfixB b hbL w hwWt, hfixA a haL (b w') (hpres_Wp b hbL w' hwWp)] at h
    exact h
  have hmainA : a w = w :=
    (s1611e3_eq_of_mul_eq_mul_of_inf_bot hWinf (hpres_Wt a haL w hwWt)
      (hpres_Wp b hbL w' hwWp) hwWt hwWp hmulA).1
  have hmainB : b w' = w' :=
    (s1611e3_eq_of_mul_eq_mul_of_inf_bot hWinf (hpres_Wt a haL w hwWt)
      (hpres_Wp b hbL w' hwWp) hwWt hwWp hmulA).2
  have ha1 : a = 1 :=
    s1611e3_seven_eq_one_of_fix_natSum3 hPSL hNat haL ha7 hwWt hw1 hmainA
  have hb1 : b = 1 := by
    obtain ⟨a', ha'L, ha'b⟩ := Subgroup.mem_map.mp hbL
    have ha'b' : MulAut.conj g a' = b := ha'b
    have ha'7 : a' ^ 7 = 1 := by
      have h1 : MulAut.conj g (a' ^ 7) = 1 := by
        rw [map_pow, ha'b']
        exact hb7
      exact (MulAut.conj g).injective (by rw [h1, map_one])
    obtain ⟨u, huWt, hu'⟩ := Subgroup.mem_map.mp hwWp
    have hu'' : g u = w' := hu'
    have ha'u : a' u = u := by
      have h : MulAut.conj g a' (g u) = g u := by
        rw [ha'b', hu'']
        exact hmainB
      simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h
      exact g.injective h
    have hu1 : u ≠ 1 := by
      intro hu
      exact hw'1 (by rw [← hu', hu, map_one])
    have ha'1 : a' = 1 :=
      s1611e3_seven_eq_one_of_fix_natSum3 hPSL hNat ha'L ha'7 huWt hu1 ha'u
    rw [← ha'b', ha'1, map_one]
  rw [← hab, ha1, hb1, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
