module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A1111Def
public import CFSG.LocalAnalysis.StandardType.PhanELocalSel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K]

private lemma plh_inf_sup_span_singleton_eq_bot {V : Type*} [AddCommGroup V] [Module K V]
    {M T : Submodule K V} {v : V} (hMT : M ⊓ T = ⊥) (hv : v ∉ M ⊔ T) :
    (M ⊔ K ∙ v) ⊓ T = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_inf] at hw
  obtain ⟨hwMv, hwT⟩ := hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hwMv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  by_cases hc : c = 0
  · rw [hc, zero_smul, add_zero] at hwT ⊢
    exact (Submodule.eq_bot_iff _).mp hMT a (Submodule.mem_inf.mpr ⟨ha, hwT⟩)
  · exfalso
    apply hv
    have hmem : c • v ∈ M ⊔ T := by
      have h' : c • v = (a + c • v) + (-a) := by abel
      rw [h']
      exact Submodule.add_mem _ (Submodule.mem_sup_right hwT)
        (Submodule.neg_mem _ (Submodule.mem_sup_left ha))
    have hv_eq : v = c⁻¹ • (c • v) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hv_eq]
    exact Submodule.smul_mem _ _ hmem

private lemma plh_inf_Vsub2_le_inf_Vsub3 (p : Submodule K (Fin 4 → K)) :
    p ⊓ Vsub 4 2 ≤ p ⊓ Vsub 4 3 := by
  intro v hv
  rw [Submodule.mem_inf] at hv ⊢
  exact ⟨hv.1, Vsub_mono (K := K) (n := 4) (by norm_num : (2 : ℕ) ≤ 3) hv.2⟩

private lemma plh_inf_Vsub1_le_inf_Vsub2 (p : Submodule K (Fin 4 → K)) :
    p ⊓ Vsub 4 1 ≤ p ⊓ Vsub 4 2 := by
  intro v hv
  rw [Submodule.mem_inf] at hv ⊢
  exact ⟨hv.1, Vsub_mono (K := K) (n := 4) (by norm_num : (1 : ℕ) ≤ 2) hv.2⟩

private lemma plh_card_insert_four {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, c, d} : Finset α)
  have h2 := Finset.card_insert_le b ({c, d} : Finset α)
  have h3 := Finset.card_insert_le c ({d} : Finset α)
  have h4 : ({d} : Finset α).card ≤ 1 := by simp
  omega

private lemma plh_card_insert_seven {α : Type*} [DecidableEq α] (a b c d e f g : α) :
    ({a, b, c, d, e, f, g} : Finset α).card ≤ 7 := by
  have h1 := Finset.card_insert_le a ({b, c, d, e, f, g} : Finset α)
  have h2 := Finset.card_insert_le b ({c, d, e, f, g} : Finset α)
  have h3 := Finset.card_insert_le c ({d, e, f, g} : Finset α)
  have h4 := Finset.card_insert_le d ({e, f, g} : Finset α)
  have h5 := Finset.card_insert_le e ({f, g} : Finset α)
  have h6 := Finset.card_insert_le f ({g} : Finset α)
  have h7 : ({g} : Finset α).card ≤ 1 := by simp
  omega

private lemma plh_triple (x y t : Submodule K (Fin 4 → K))
    (hx1 : finrank K x = 1) (hy1 : finrank K y = 1) (ht1 : finrank K t = 1)
    (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t)
    (hxV3 : x ⊓ Vsub 4 3 = ⊥) (hyV3 : y ⊓ Vsub 4 3 = ⊥) (htV3 : t ⊓ Vsub 4 3 = ⊥)
    (hxyV2 : (x ⊔ y) ⊓ Vsub 4 2 = ⊥)
    (hxtV2 : (x ⊔ t) ⊓ Vsub 4 2 = ⊥) (hytV2 : (y ⊔ t) ⊓ Vsub 4 2 = ⊥)
    (hxytV1 : (x ⊔ y ⊔ t) ⊓ Vsub 4 1 = ⊥)
    (hxyt3 : finrank K ↥(x ⊔ y ⊔ t) = 3)
    (hxy2 : finrank K ↥(x ⊔ y) = 2) (hxt2 : finrank K ↥(x ⊔ t) = 2)
    (hyt2 : finrank K ↥(y ⊔ t) = 2) :
    AdmAdj (Adm1111 (K := K)) x t ∧ AdmAdj (Adm1111 (K := K)) y t ∧
      AdmPlanar (Adm1111 (K := K)) x y t := by
  have hxyH : x ⊔ y ≤ x ⊔ y ⊔ t := le_sup_left
  have hxtH : x ⊔ t ≤ x ⊔ y ⊔ t := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hytH : y ⊔ t ≤ x ⊔ y ⊔ t := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hxLxt : x ≤ x ⊔ t := le_sup_left
  have htLxt : t ≤ x ⊔ t := le_sup_right
  have hyLyt : y ≤ y ⊔ t := le_sup_left
  have htLyt : t ≤ y ⊔ t := le_sup_right
  have hxLxy : x ≤ x ⊔ y := le_sup_left
  have hyLxy : y ≤ x ⊔ y := le_sup_right
  have hH3 : finrank K ↥(x ⊔ y ⊔ t) = 3 := hxyt3
  refine ⟨⟨hxt, x ⊔ t, x ⊔ y ⊔ t,
      ⟨⟨hx1, hxt2, hH3, hxLxt, hxtH⟩, hxV3, hxtV2, hxytV1⟩,
      ⟨⟨ht1, hxt2, hH3, htLxt, hxtH⟩, htV3, hxtV2, hxytV1⟩⟩,
    ⟨hyt, y ⊔ t, x ⊔ y ⊔ t,
      ⟨⟨hy1, hyt2, hH3, hyLyt, hytH⟩, hyV3, hytV2, hxytV1⟩,
      ⟨⟨ht1, hyt2, hH3, htLyt, hytH⟩, htV3, hytV2, hxytV1⟩⟩,
    x ⊔ y ⊔ t, x ⊔ y, y ⊔ t, x ⊔ t,
    ⟨⟨hx1, hxy2, hH3, hxLxy, hxyH⟩, hxV3, hxyV2, hxytV1⟩,
    ⟨⟨hy1, hxy2, hH3, hyLxy, hxyH⟩, hyV3, hxyV2, hxytV1⟩,
    ⟨⟨hy1, hyt2, hH3, hyLyt, hytH⟩, hyV3, hytV2, hxytV1⟩,
    ⟨⟨ht1, hyt2, hH3, htLyt, hytH⟩, htV3, hytV2, hxytV1⟩,
    ⟨⟨ht1, hxt2, hH3, htLxt, hxtH⟩, htV3, hxtV2, hxytV1⟩,
    ⟨⟨hx1, hxt2, hH3, hxLxt, hxtH⟩, hxV3, hxtV2, hxytV1⟩⟩

private lemma plh_coneTri_of_le (x y z : Submodule K (Fin 4 → K))
    (hxy : AdmAdj (Adm1111 (K := K)) x y)
    (hyz : AdmAdj (Adm1111 (K := K)) y z)
    (hzx : AdmAdj (Adm1111 (K := K)) z x)
    (hz : z ≤ x ⊔ y) (hQ : 16 ≤ Nat.card K) :
    ∃ t, AdmAdj (Adm1111 (K := K)) x t ∧ AdmAdj (Adm1111 (K := K)) y t ∧
      AdmAdj (Adm1111 (K := K)) z t ∧ AdmPlanar (Adm1111 (K := K)) x y t ∧
      AdmPlanar (Adm1111 (K := K)) y z t ∧ AdmPlanar (Adm1111 (K := K)) z x t := by
  obtain ⟨hxy_ne, Lxy, Hxy, hxLxy, hyLxy⟩ := hxy
  obtain ⟨hyz_ne, Lyz, Hyz, hyLyz, hzLyz⟩ := hyz
  obtain ⟨hzx_ne, Lzx, Hzx, hzLzx, hxLzx⟩ := hzx
  have hx1 : finrank K x = 1 := hxLxy.1.p1
  have hy1 : finrank K y = 1 := hyLxy.1.p1
  have hz1 : finrank K z = 1 := hzLyz.1.p1
  have hxV3 : x ⊓ Vsub 4 3 = ⊥ := hxLxy.2.1
  have hyV3 : y ⊓ Vsub 4 3 = ⊥ := hyLxy.2.1
  have hzV3 : z ⊓ Vsub 4 3 = ⊥ := hzLyz.2.1
  have hxy2 : finrank K ↥(x ⊔ y) = 2 := finrank_sup_of_ne_pts hx1 hy1 hxy_ne
  have hLxy_eq : Lxy = x ⊔ y := (Submodule.eq_of_le_of_finrank_eq
    (sup_le hxLxy.1.pL hyLxy.1.pL) (by rw [hxy2, hxLxy.1.L2])).symm
  have hxyV2 : (x ⊔ y) ⊓ Vsub 4 2 = ⊥ := by
    rw [← hLxy_eq]; exact hxLxy.2.2.1
  have hxyH : x ⊔ y ≤ Hxy := by
    rw [← hLxy_eq]; exact hxLxy.1.LH
  have hHxy3 : finrank K Hxy = 3 := hxLxy.1.H3
  have hHxyV1 : Hxy ⊓ Vsub 4 1 = ⊥ := hxLxy.2.2.2
  have hcomap_ne : ∀ W : Submodule K (Fin 4 → K), W ≤ x ⊔ y → W ≠ x ⊔ y →
      W.comap (x ⊔ y).subtype ≠ ⊤ := by
    intro W hWL hWne htop
    apply hWne
    apply le_antisymm hWL
    intro v hv
    have hmem : (⟨v, hv⟩ : ↥(x ⊔ y)) ∈ W.comap (x ⊔ y).subtype := by
      rw [htop]; trivial
    have hmem' : (x ⊔ y).subtype (⟨v, hv⟩ : ↥(x ⊔ y)) ∈ W := Submodule.mem_comap.mp hmem
    simpa using hmem'
  have hx_ne : x ≠ x ⊔ y := by
    intro h
    have hfin := congrArg (fun s : Submodule K (Fin 4 → K) => finrank K ↥s) h
    rw [hx1, hxy2] at hfin
    omega
  have hy_ne : y ≠ x ⊔ y := by
    intro h
    have hfin := congrArg (fun s : Submodule K (Fin 4 → K) => finrank K ↥s) h
    rw [hy1, hxy2] at hfin
    omega
  have hz_ne : z ≠ x ⊔ y := by
    intro h
    have hfin := congrArg (fun s : Submodule K (Fin 4 → K) => finrank K ↥s) h
    rw [hz1, hxy2] at hfin
    omega
  have hxyV3_ne : (x ⊔ y) ⊓ Vsub 4 3 ≠ x ⊔ y := by
    intro h
    have hle : x ⊔ y ≤ Vsub 4 3 := by rw [← h]; exact inf_le_right
    have hsup : (x ⊔ y) ⊔ Vsub 4 2 ≤ Vsub 4 3 :=
      sup_le hle (Vsub_mono (K := K) (n := 4) (by norm_num : (2 : ℕ) ≤ 3))
    have hfin : finrank K ↥((x ⊔ y) ⊔ Vsub 4 2) = 4 := by
      rw [finrank_sup_of_disjoint (disjoint_iff.mpr hxyV2), hxy2,
        finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)]
    have hmono := Submodule.finrank_mono hsup
    rw [hfin, finrank_Vsub (K := K) (n := 4) (c := 3) (by norm_num)] at hmono
    omega
  let S : Finset (Submodule K ↥(x ⊔ y)) :=
    {x.comap (x ⊔ y).subtype, y.comap (x ⊔ y).subtype, z.comap (x ⊔ y).subtype,
      ((x ⊔ y) ⊓ Vsub 4 3).comap (x ⊔ y).subtype}
  have hS : ∀ T ∈ S, T ≠ ⊤ := by
    intro T hT
    dsimp only [S] at hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact hcomap_ne x le_sup_left hx_ne
    · exact hcomap_ne y le_sup_right hy_ne
    · exact hcomap_ne z hz hz_ne
    · exact hcomap_ne ((x ⊔ y) ⊓ Vsub 4 3) inf_le_left hxyV3_ne
  have hScard : S.card < Nat.card K := by
    have h4 : S.card ≤ 4 := by
      dsimp only [S]
      exact plh_card_insert_four _ _ _ _
    omega
  obtain ⟨v, hv⟩ := exists_notMem_of_card_lt S hS hScard
  let w : Fin 4 → K := (v : Fin 4 → K)
  have hvx : w ∉ x := by
    intro hxmem
    exact hv (x.comap (x ⊔ y).subtype) (by simp [S])
      (by rw [Submodule.mem_comap]; exact hxmem)
  have hvy : w ∉ y := by
    intro hymem
    exact hv (y.comap (x ⊔ y).subtype) (by simp [S])
      (by rw [Submodule.mem_comap]; exact hymem)
  have hvz : w ∉ z := by
    intro hzmem
    exact hv (z.comap (x ⊔ y).subtype) (by simp [S])
      (by rw [Submodule.mem_comap]; exact hzmem)
  have hvV3 : w ∉ Vsub 4 3 := by
    intro hv3
    have h := hv (((x ⊔ y) ⊓ Vsub 4 3).comap (x ⊔ y).subtype) (by simp [S])
    apply h
    rw [Submodule.mem_comap]
    exact Submodule.mem_inf.mpr ⟨v.2, hv3⟩
  have hv0 : w ≠ 0 := by
    intro h0
    apply hvV3
    rw [h0]
    exact Submodule.zero_mem _
  have ht1 : finrank K (K ∙ w) = 1 := finrank_span_singleton hv0
  have htxy : K ∙ w ≤ x ⊔ y := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact v.2
  have htV3 : (K ∙ w) ⊓ Vsub 4 3 = ⊥ := by
    rw [← disjoint_iff]
    exact (Submodule.disjoint_span_singleton_of_notMem hvV3).symm
  have hxL' : AdmCh (Adm1111 (K := K)) x (x ⊔ y) Hxy :=
    ⟨⟨hx1, hxy2, hHxy3, le_sup_left, hxyH⟩, hxV3, hxyV2, hHxyV1⟩
  have hyL' : AdmCh (Adm1111 (K := K)) y (x ⊔ y) Hxy :=
    ⟨⟨hy1, hxy2, hHxy3, le_sup_right, hxyH⟩, hyV3, hxyV2, hHxyV1⟩
  have hzL' : AdmCh (Adm1111 (K := K)) z (x ⊔ y) Hxy :=
    ⟨⟨hz1, hxy2, hHxy3, hz, hxyH⟩, hzV3, hxyV2, hHxyV1⟩
  have htL' : AdmCh (Adm1111 (K := K)) (K ∙ w) (x ⊔ y) Hxy :=
    ⟨⟨ht1, hxy2, hHxy3, htxy, hxyH⟩, htV3, hxyV2, hHxyV1⟩
  have hxt_ne : x ≠ K ∙ w := by
    intro h
    exact hvx (by rw [h]; exact Submodule.mem_span_singleton_self w)
  have hyt_ne : y ≠ K ∙ w := by
    intro h
    exact hvy (by rw [h]; exact Submodule.mem_span_singleton_self w)
  have hzt_ne : z ≠ K ∙ w := by
    intro h
    exact hvz (by rw [h]; exact Submodule.mem_span_singleton_self w)
  refine ⟨K ∙ w,
    ⟨hxt_ne, x ⊔ y, Hxy, hxL', htL'⟩,
    ⟨hyt_ne, x ⊔ y, Hxy, hyL', htL'⟩,
    ⟨hzt_ne, x ⊔ y, Hxy, hzL', htL'⟩,
    ⟨Hxy, x ⊔ y, x ⊔ y, x ⊔ y, hxL', hyL', hyL', htL', htL', hxL'⟩,
    ⟨Hxy, x ⊔ y, x ⊔ y, x ⊔ y, hyL', hzL', hzL', htL', htL', hyL'⟩,
    ⟨Hxy, x ⊔ y, x ⊔ y, x ⊔ y, hzL', hxL', hxL', htL', htL', hzL'⟩⟩

private lemma plh_coneTri_of_not_le (x y z : Submodule K (Fin 4 → K))
    (hxy : AdmAdj (Adm1111 (K := K)) x y)
    (hyz : AdmAdj (Adm1111 (K := K)) y z)
    (hzx : AdmAdj (Adm1111 (K := K)) z x)
    (hz : ¬ z ≤ x ⊔ y) (hQ : 16 ≤ Nat.card K) :
    ∃ t, AdmAdj (Adm1111 (K := K)) x t ∧ AdmAdj (Adm1111 (K := K)) y t ∧
      AdmAdj (Adm1111 (K := K)) z t ∧ AdmPlanar (Adm1111 (K := K)) x y t ∧
      AdmPlanar (Adm1111 (K := K)) y z t ∧ AdmPlanar (Adm1111 (K := K)) z x t := by
  obtain ⟨hxy_ne, Lxy, Hxy, hxLxy, hyLxy⟩ := hxy
  obtain ⟨hyz_ne, Lyz, Hyz, hyLyz, hzLyz⟩ := hyz
  obtain ⟨hzx_ne, Lzx, Hzx, hzLzx, hxLzx⟩ := hzx
  have hx1 : finrank K x = 1 := hxLxy.1.p1
  have hy1 : finrank K y = 1 := hyLxy.1.p1
  have hz1 : finrank K z = 1 := hzLyz.1.p1
  have hxV3 : x ⊓ Vsub 4 3 = ⊥ := hxLxy.2.1
  have hyV3 : y ⊓ Vsub 4 3 = ⊥ := hyLxy.2.1
  have hzV3 : z ⊓ Vsub 4 3 = ⊥ := hzLyz.2.1
  have hxy2 : finrank K ↥(x ⊔ y) = 2 := finrank_sup_of_ne_pts hx1 hy1 hxy_ne
  have hyz2 : finrank K ↥(y ⊔ z) = 2 := finrank_sup_of_ne_pts hy1 hz1 hyz_ne
  have hzx2 : finrank K ↥(z ⊔ x) = 2 := finrank_sup_of_ne_pts hz1 hx1 hzx_ne
  have hLxy_eq : Lxy = x ⊔ y := (Submodule.eq_of_le_of_finrank_eq
    (sup_le hxLxy.1.pL hyLxy.1.pL) (by rw [hxy2, hxLxy.1.L2])).symm
  have hLyz_eq : Lyz = y ⊔ z := (Submodule.eq_of_le_of_finrank_eq
    (sup_le hyLyz.1.pL hzLyz.1.pL) (by rw [hyz2, hyLyz.1.L2])).symm
  have hLzx_eq : Lzx = z ⊔ x := (Submodule.eq_of_le_of_finrank_eq
    (sup_le hzLzx.1.pL hxLzx.1.pL) (by rw [hzx2, hzLzx.1.L2])).symm
  have hxyV2 : (x ⊔ y) ⊓ Vsub 4 2 = ⊥ := by
    rw [← hLxy_eq]; exact hxLxy.2.2.1
  have hyzV2 : (y ⊔ z) ⊓ Vsub 4 2 = ⊥ := by
    rw [← hLyz_eq]; exact hyLyz.2.2.1
  have hzxV2 : (z ⊔ x) ⊓ Vsub 4 2 = ⊥ := by
    rw [← hLzx_eq]; exact hzLzx.2.2.1
  have hxyV1 : (x ⊔ y) ⊓ Vsub 4 1 = ⊥ :=
    le_bot_iff.mp ((plh_inf_Vsub1_le_inf_Vsub2 (x ⊔ y)).trans (le_of_eq hxyV2))
  have hyzV1 : (y ⊔ z) ⊓ Vsub 4 1 = ⊥ :=
    le_bot_iff.mp ((plh_inf_Vsub1_le_inf_Vsub2 (y ⊔ z)).trans (le_of_eq hyzV2))
  have hzxV1 : (z ⊔ x) ⊓ Vsub 4 1 = ⊥ :=
    le_bot_iff.mp ((plh_inf_Vsub1_le_inf_Vsub2 (z ⊔ x)).trans (le_of_eq hzxV2))
  have hxV2 : x ⊓ Vsub 4 2 = ⊥ :=
    le_bot_iff.mp ((plh_inf_Vsub2_le_inf_Vsub3 x).trans (le_of_eq hxV3))
  have hyV2 : y ⊓ Vsub 4 2 = ⊥ :=
    le_bot_iff.mp ((plh_inf_Vsub2_le_inf_Vsub3 y).trans (le_of_eq hyV3))
  have hzV2 : z ⊓ Vsub 4 2 = ⊥ :=
    le_bot_iff.mp ((plh_inf_Vsub2_le_inf_Vsub3 z).trans (le_of_eq hzV3))
  obtain ⟨ux, hux0, hux_eq⟩ := exists_eq_span_of_finrank_eq_one hx1
  obtain ⟨uy, huy0, huy_eq⟩ := exists_eq_span_of_finrank_eq_one hy1
  obtain ⟨uz, huz0, huz_eq⟩ := exists_eq_span_of_finrank_eq_one hz1
  have hzy : (x ⊔ y) ⊓ z = ⊥ := by
    rw [inf_comm]
    by_contra h
    have hpos : finrank K ↥(z ⊓ (x ⊔ y)) ≠ 0 :=
      fun h0 => h (Submodule.finrank_eq_zero.mp h0)
    have hle1 : finrank K ↥(z ⊓ (x ⊔ y)) ≤ 1 := by
      have hmono := Submodule.finrank_mono (inf_le_left : z ⊓ (x ⊔ y) ≤ z)
      rwa [hz1] at hmono
    have h1 : finrank K ↥(z ⊓ (x ⊔ y)) = 1 := by omega
    have heq : z ⊓ (x ⊔ y) = z :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hz1])
    exact hz (heq ▸ inf_le_right)
  have hH0_3 : finrank K ↥(x ⊔ y ⊔ z) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (x ⊔ y) z
    rw [hzy, finrank_bot, add_zero, hxy2, hz1] at h
    omega
  have hH0_ne : x ⊔ y ⊔ z ≠ ⊤ := by
    intro htop
    have hfin : finrank K ↥(x ⊔ y ⊔ z) = 4 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    rw [hH0_3] at hfin
    omega
  obtain ⟨e, heH0⟩ := exists_notMem_of_card_lt
    ({(x ⊔ y ⊔ z)} : Finset (Submodule K (Fin 4 → K)))
    (by intro T hT; rw [Finset.mem_singleton] at hT; rw [hT]; exact hH0_ne)
    (by rw [Finset.card_singleton]; omega)
  have heH0' : e ∉ x ⊔ y ⊔ z := heH0 _ (by simp)
  have he0 : e ≠ 0 := by
    intro h0
    apply heH0'
    rw [h0]
    exact Submodule.zero_mem _
  have hH0e : x ⊔ y ⊔ z ⊔ K ∙ e = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_sup_of_disjoint (Submodule.disjoint_span_singleton_of_notMem heH0'),
      hH0_3, finrank_span_singleton he0, Module.finrank_fin_fun]
  have hspan_le : ∀ T : Submodule K (Fin 4 → K),
      ux ∈ T → uy ∈ T → uz ∈ T → e ∈ T → (x ⊔ y ⊔ z) ⊔ K ∙ e ≤ T := by
    intro T huxT huyT huzT heT
    have hxT : x ≤ T := by
      rw [hux_eq]; exact (Submodule.span_singleton_le_iff_mem _ _).mpr huxT
    have hyT : y ≤ T := by
      rw [huy_eq]; exact (Submodule.span_singleton_le_iff_mem _ _).mpr huyT
    have hzT : z ≤ T := by
      rw [huz_eq]; exact (Submodule.span_singleton_le_iff_mem _ _).mpr huzT
    have hKeT : K ∙ e ≤ T := (Submodule.span_singleton_le_iff_mem _ _).mpr heT
    exact sup_le (sup_le (sup_le hxT hyT) hzT) hKeT
  let Sbig : Finset (Submodule K (Fin 4 → K)) :=
    {Vsub 4 3, x ⊔ Vsub 4 2, y ⊔ Vsub 4 2, z ⊔ Vsub 4 2,
      x ⊔ y ⊔ Vsub 4 1, y ⊔ z ⊔ Vsub 4 1, z ⊔ x ⊔ Vsub 4 1}
  have hfinV3 : finrank K (Vsub 4 3) = 3 :=
    finrank_Vsub (K := K) (n := 4) (c := 3) (by norm_num)
  have hfinxV2 : finrank K ↥(x ⊔ Vsub 4 2) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hxV2), hx1,
      finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)]
  have hfinyV2 : finrank K ↥(y ⊔ Vsub 4 2) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hyV2), hy1,
      finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)]
  have hfinzV2 : finrank K ↥(z ⊔ Vsub 4 2) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hzV2), hz1,
      finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)]
  have hfinxyV1 : finrank K ↥(x ⊔ y ⊔ Vsub 4 1) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hxyV1), hxy2,
      finrank_Vsub (K := K) (n := 4) (c := 1) (by norm_num)]
  have hfinyzV1 : finrank K ↥(y ⊔ z ⊔ Vsub 4 1) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hyzV1), hyz2,
      finrank_Vsub (K := K) (n := 4) (c := 1) (by norm_num)]
  have hfinzxV1 : finrank K ↥(z ⊔ x ⊔ Vsub 4 1) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr hzxV1), hzx2,
      finrank_Vsub (K := K) (n := 4) (c := 1) (by norm_num)]
  have hTne : ∀ T ∈ Sbig, T ≠ ⊤ := by
    intro T hT htop
    have h4 : finrank K T = 4 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    dsimp only [Sbig] at hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hfinV3] at h4; omega
    · rw [hfinxV2] at h4; omega
    · rw [hfinyV2] at h4; omega
    · rw [hfinzV2] at h4; omega
    · rw [hfinxyV1] at h4; omega
    · rw [hfinyzV1] at h4; omega
    · rw [hfinzxV1] at h4; omega
  have hSbig : ∀ T ∈ Sbig, ¬ (ux ∈ T ∧ uy ∈ T ∧ uz ∈ T ∧ e ∈ T) := by
    intro T hT hcon
    obtain ⟨huxT, huyT, huzT, heT⟩ := hcon
    exact hTne T hT (top_le_iff.mp (hH0e ▸ hspan_le T huxT huyT huzT heT))
  have hSbigcard : Sbig.card < Nat.card K := by
    have h7 : Sbig.card ≤ 7 := by
      dsimp only [Sbig]
      exact plh_card_insert_seven _ _ _ _ _ _ _
    omega
  obtain ⟨a, b, c, -, -, -, hvSbig⟩ := exists_cone_vector ux uy uz e ∅ ∅ ∅ Sbig hSbig
    (by simpa using hSbigcard) (by simpa using hSbigcard) (by simpa using hSbigcard)
  let w : Fin 4 → K := a • ux + b • uy + c • uz + e
  have hvSbig' : ∀ T ∈ Sbig, w ∉ T := hvSbig
  have hvV3 : w ∉ Vsub 4 3 := hvSbig' _ (by simp [Sbig])
  have hvxV2 : w ∉ x ⊔ Vsub 4 2 := hvSbig' _ (by simp [Sbig])
  have hvyV2 : w ∉ y ⊔ Vsub 4 2 := hvSbig' _ (by simp [Sbig])
  have hvzV2 : w ∉ z ⊔ Vsub 4 2 := hvSbig' _ (by simp [Sbig])
  have hvxyV1 : w ∉ x ⊔ y ⊔ Vsub 4 1 := hvSbig' _ (by simp [Sbig])
  have hvyzV1 : w ∉ y ⊔ z ⊔ Vsub 4 1 := hvSbig' _ (by simp [Sbig])
  have hvzxV1 : w ∉ z ⊔ x ⊔ Vsub 4 1 := hvSbig' _ (by simp [Sbig])
  have hvxy : w ∉ x ⊔ y := fun h => hvxyV1 (Submodule.mem_sup_left h)
  have hvyz : w ∉ y ⊔ z := fun h => hvyzV1 (Submodule.mem_sup_left h)
  have hvzx : w ∉ z ⊔ x := fun h => hvzxV1 (Submodule.mem_sup_left h)
  have hv0 : w ≠ 0 := by
    intro h0
    apply hvV3
    rw [h0]
    exact Submodule.zero_mem _
  have ht1 : finrank K (K ∙ w) = 1 := finrank_span_singleton hv0
  have hxt_ne : x ≠ K ∙ w := by
    intro h
    exact hvxy (Submodule.mem_sup_left (by rw [h]; exact Submodule.mem_span_singleton_self _))
  have hyt_ne : y ≠ K ∙ w := by
    intro h
    exact hvxy (Submodule.mem_sup_right (by rw [h]; exact Submodule.mem_span_singleton_self _))
  have hzt_ne : z ≠ K ∙ w := by
    intro h
    exact hvyz (Submodule.mem_sup_right (by rw [h]; exact Submodule.mem_span_singleton_self _))
  have hxt2 : finrank K ↥(x ⊔ K ∙ w) = 2 := finrank_sup_of_ne_pts hx1 ht1 hxt_ne
  have hyt2 : finrank K ↥(y ⊔ K ∙ w) = 2 := finrank_sup_of_ne_pts hy1 ht1 hyt_ne
  have hzt2 : finrank K ↥(z ⊔ K ∙ w) = 2 := finrank_sup_of_ne_pts hz1 ht1 hzt_ne
  have htxy : (x ⊔ y) ⊓ K ∙ w = ⊥ := by
    rw [← disjoint_iff]
    exact Submodule.disjoint_span_singleton_of_notMem hvxy
  have htyz : (y ⊔ z) ⊓ K ∙ w = ⊥ := by
    rw [← disjoint_iff]
    exact Submodule.disjoint_span_singleton_of_notMem hvyz
  have htzx : (z ⊔ x) ⊓ K ∙ w = ⊥ := by
    rw [← disjoint_iff]
    exact Submodule.disjoint_span_singleton_of_notMem hvzx
  have hxyt3 : finrank K ↥(x ⊔ y ⊔ K ∙ w) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr htxy), hxy2, ht1]
  have hyzt3 : finrank K ↥(y ⊔ z ⊔ K ∙ w) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr htyz), hyz2, ht1]
  have hzxt3 : finrank K ↥(z ⊔ x ⊔ K ∙ w) = 3 := by
    rw [finrank_sup_of_disjoint (disjoint_iff.mpr htzx), hzx2, ht1]
  have htV3 : (K ∙ w) ⊓ Vsub 4 3 = ⊥ := by
    rw [← disjoint_iff]
    exact (Submodule.disjoint_span_singleton_of_notMem hvV3).symm
  have hxtV2 : (x ⊔ K ∙ w) ⊓ Vsub 4 2 = ⊥ :=
    plh_inf_sup_span_singleton_eq_bot (M := x) (T := Vsub 4 2) (v := w) hxV2 hvxV2
  have hytV2 : (y ⊔ K ∙ w) ⊓ Vsub 4 2 = ⊥ :=
    plh_inf_sup_span_singleton_eq_bot (M := y) (T := Vsub 4 2) (v := w) hyV2 hvyV2
  have hztV2 : (z ⊔ K ∙ w) ⊓ Vsub 4 2 = ⊥ :=
    plh_inf_sup_span_singleton_eq_bot (M := z) (T := Vsub 4 2) (v := w) hzV2 hvzV2
  have hxytV1 : (x ⊔ y ⊔ K ∙ w) ⊓ Vsub 4 1 = ⊥ :=
    plh_inf_sup_span_singleton_eq_bot (M := x ⊔ y) (T := Vsub 4 1) (v := w) hxyV1 hvxyV1
  have hyztV1 : (y ⊔ z ⊔ K ∙ w) ⊓ Vsub 4 1 = ⊥ :=
    plh_inf_sup_span_singleton_eq_bot (M := y ⊔ z) (T := Vsub 4 1) (v := w) hyzV1 hvyzV1
  have hzxtV1 : (z ⊔ x ⊔ K ∙ w) ⊓ Vsub 4 1 = ⊥ :=
    plh_inf_sup_span_singleton_eq_bot (M := z ⊔ x) (T := Vsub 4 1) (v := w) hzxV1 hvzxV1
  have htri1 := plh_triple x y (K ∙ w) hx1 hy1 ht1 hxy_ne hxt_ne hyt_ne
    hxV3 hyV3 htV3 hxyV2 hxtV2 hytV2 hxytV1 hxyt3 hxy2 hxt2 hyt2
  have htri2 := plh_triple y z (K ∙ w) hy1 hz1 ht1 hyz_ne hyt_ne hzt_ne
    hyV3 hzV3 htV3 hyzV2 hytV2 hztV2 hyztV1 hyzt3 hyz2 hyt2 hzt2
  have htri3 := plh_triple z x (K ∙ w) hz1 hx1 ht1 hzx_ne hzt_ne hxt_ne
    hzV3 hxV3 htV3 hzxV2 hztV2 hxtV2 hzxtV1 hzxt3 hzx2 hzt2 hxt2
  exact ⟨K ∙ w, htri1.1, htri1.2.1, htri2.2.1, htri1.2.2, htri2.2.2, htri3.2.2⟩

theorem adm1111_coneTri (hQ : 16 ≤ Nat.card K) : AdmConeTri (Adm1111 (K := K)) := by
  intro x y z hxy hyz hzx
  by_cases hz : z ≤ x ⊔ y
  · exact plh_coneTri_of_le x y z hxy hyz hzx hz hQ
  · exact plh_coneTri_of_not_le x y z hxy hyz hzx hz hQ

end CFSG.ClassicalInvolution.Phan.PhanE

end
