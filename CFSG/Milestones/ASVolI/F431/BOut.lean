module

public import CFSG.Milestones.ASVolI.F431.BTransfer
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSOutMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutGenB
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2FourG

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Blueprint

universe u v

section TwoG

variable {Mb : Type u} [Group Mb] [Finite Mb] {G : Type v} [Group G] [Finite G]
  {T Sb N N' : Subgroup Mb} {I : Finset Mb} {f z : Mb} {b : ↥N →* G} {b' : ↥N' →* G}
  {M : Subgroup G}

theorem burnsideF4m_TwoGSetup_out_false (hres : oTwoRes (⊤ : Subgroup G) = ⊤)
    (S : TwoGSetup N N' b b' M) (O : F431TwoOut T Sb f N N' z I) : False := by
  have hb := S.comp.inj₁
  have hfT := O.f_mem
  have hfN : f ∈ N := O.T_le hfT
  have hzN : z ∈ N := O.T_le O.z_mem
  have hbz : Subgroup.centralizer ({b ⟨z, hzN⟩} : Set G) ≤ b.range := by
    rw [S.range]
    exact S.cent _ (map_mem_centerOf_perfectCore hb S.range hzN O.z_ZN)
      ((orderOf_img hb hzN).trans O.z_two)
  have hSyl : IsSylowTwoOf (subImg b T) ⊤ :=
    lemma_F433_aux b hb O.sylow O.T_le O.z_mem O.z_two O.center_T hbz
  have hTfN : spTf T f ≤ N := inf_le_left.trans O.T_le
  have hTfSyl : IsSylowTwoOf (subImg b (spTf T f)) (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) :=
    sylow_Tf_of_center_le hb S.range S.cent O.T_le hfT O.Sylow_Tf O.Z_sq O.Z_S O.W_le O.W_ne
  have hSN : Sb ≤ N := O.S_le.trans O.T_le
  obtain ⟨t₀, ht₀⟩ := O.cyc
  have ht₀T : t₀ ∈ T := by
    rw [ht₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have ht₀N : t₀ ∈ N := O.T_le ht₀T
  have hcyc : subImg b T = subImg b Sb ⊔ Subgroup.zpowers (b ⟨t₀, ht₀N⟩) := by
    conv_lhs => rw [ht₀]
    rw [subImg_sup hSN (Subgroup.zpowers_le.mpr ht₀N), subImg_zpowers ht₀N]
  refine CFSG.QuasithinUnique.Lin2.burnsideF4m_transfer_contradiction_cyclic_oTwoRes hres hSyl
    (subImg_mono b O.S_le) (subImg_le_normalizer b O.S_norm) hcyc
    (mem_subImg_of_mem b hfN hfT)
    (fun h => O.f_not ((mem_subImg_iff_of_injective hb hfN).mp h))
    ((sq_eq_one_iff_of_injective hb hfN).mpr O.f_sq) ?_
  intro g hg
  obtain ⟨s, hsN, hsS, hs⟩ := mem_subImg.mp hg
  have hf1 : f ≠ 1 := fun h => O.f_not (h ▸ Sb.one_mem)
  have hfg2 : b ⟨f, hfN⟩ ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hfN).mpr O.f_sq
  have hs2 : s ^ 2 = 1 := by
    refine (sq_eq_one_iff_of_injective hb hsN).mp ?_
    rw [hs]
    calc (g⁻¹ * b ⟨f, hfN⟩ * g) ^ 2 = g⁻¹ * b ⟨f, hfN⟩ ^ 2 * g := by rw [sq, sq]; group
      _ = 1 := by rw [hfg2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h1 : b ⟨1, hsN⟩ = 1 := map_one b
    rw [h1] at hs
    have : b ⟨f, hfN⟩ = 1 := by
      calc b ⟨f, hfN⟩ = g * (g⁻¹ * b ⟨f, hfN⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [← hs]; group
    exact hf1 (congrArg Subtype.val (hb (this.trans (map_one b).symm)))
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨i, hiI, hiN, hsN', hic⟩ := O.exists_conj S.comp hsS hso
  obtain ⟨c, hc⟩ := isConj_iff.mp hic
  set u : G := b ⟨i, hiN⟩ with hu
  have hs' : b ⟨s, hsN'⟩ = g⁻¹ * b ⟨f, hfN⟩ * g := hs
  have hfu : (g * c) * u * (g * c)⁻¹ = b ⟨f, hfN⟩ := by
    calc (g * c) * u * (g * c)⁻¹ = g * (c * u * c⁻¹) * g⁻¹ := by group
      _ = g * b ⟨s, hsN'⟩ * g⁻¹ := by rw [hc]
      _ = g * (g⁻¹ * b ⟨f, hfN⟩ * g) * g⁻¹ := by rw [hs']
      _ = b ⟨f, hfN⟩ := by group
  have hTg_le : subImg b (T ⊓ Subgroup.centralizer ({i} : Set Mb)) ≤
      Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨t, htN, ⟨htT, htC⟩, rfl⟩ := mem_subImg.mp hy
    show b ⟨t, htN⟩ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_of_injective hb hiN htN).mpr (Subgroup.mem_centralizer_singleton_iff.mp htC)
  have hp : IsPGroup 2 (subImg b (T ⊓ Subgroup.centralizer ({i} : Set Mb))) :=
    hSyl.2.1.to_le (subImg_mono b inf_le_left)
  have h1 := card_le_twoPart hTg_le hp
  have h2 : twoPart (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) =
      twoPart (Subgroup.centralizer ({u} : Set G)) := by
    unfold twoPart
    rw [card_centralizer_eq_of_conj hfu]
  have h3 : Nat.card (subImg b (spTf T f)) =
      twoPart (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) := hTfSyl.card_eq
  have h4 := O.Tf_lt i hiI
  rw [card_subImg hb (inf_le_left.trans O.T_le)] at h1
  rw [card_subImg hb hTfN] at h3
  omega

end TwoG

section Sp

variable {Mb : Type u} [Group Mb] [Finite Mb] {G : Type v} [Group G] [Finite G]
  {T Sb N1 N2 : Subgroup Mb} {I : Finset Mb} {f : Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G}
  {M1 M2 : Subgroup G}

theorem burnsideF4m_SpGSetup_out_false (hres : oTwoRes (⊤ : Subgroup G) = ⊤)
    (S : SpGSetup N1 N2 b1 b2 M1 M2) (O : F431SpOut T Sb f N1 N2 I) : False := by
  have hfT := O.f_mem
  have hfN1 : f ∈ N1 := O.T_le₁ hfT
  have hfN2 : f ∈ N2 := O.T_le₂ hfT
  have hSyl := S.sylow_out O
  have hnf := S.not_conj_out O
  have hTf1 : spTf T f ≤ N1 := inf_le_left.trans O.T_le₁
  have hTf2 : spTf T f ≤ N2 := inf_le_left.trans O.T_le₂
  have hwc1 : ∀ (x y : Mb) (hx : x ∈ N1) (hy : y ∈ N1), x ∈ Sb → y ∈ Sb → orderOf x = 2 →
      orderOf y = 2 → IsConj (b1 ⟨x, hx⟩) (b1 ⟨y, hy⟩) → IsConj x y := by
    intro x y hx hy hxS hyS hxo hyo h
    refine (O.lemma_F435 S.comp hnf hxS hyS hxo hyo).mpr ?_
    rw [amalgamMap_of_mem₁ b1 b2 hx, amalgamMap_of_mem₁ b1 b2 hy]
    exact h
  have hwc2 : ∀ (x y : Mb) (hx : x ∈ N2) (hy : y ∈ N2), x ∈ Sb → y ∈ Sb → orderOf x = 2 →
      orderOf y = 2 → IsConj (b2 ⟨x, hx⟩) (b2 ⟨y, hy⟩) → IsConj x y := by
    intro x y hx hy hxS hyS hxo hyo h
    refine (O.lemma_F435 S.comp hnf hxS hyS hxo hyo).mpr ?_
    rw [amalgamMap_of_mem₂ b1 b2 S.comp.agree hx, amalgamMap_of_mem₂ b1 b2 S.comp.agree hy]
    exact h
  obtain ⟨j, x₀, hx₀W, hx₀Z, hx₀1⟩ := O.W_ne
  have hTfSyl : IsSylowTwoOf (subImg b1 (spTf T f))
      (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := by
    fin_cases j
    · exact sylow_Tf_of_weakly_closed S.comp.inj₁ S.range1 S.cent1 O.T_le₁ hfT (O.Sylow_Tf 0)
        (O.Z_sq 0) (O.Z_cls 0) O.W_le ⟨x₀, hx₀W, hx₀Z, hx₀1⟩ hwc1
    · have h := sylow_Tf_of_weakly_closed S.comp.inj₂ S.range2 S.cent2 O.T_le₂ hfT (O.Sylow_Tf 1)
        (O.Z_sq 1) (O.Z_cls 1) O.W_le ⟨x₀, hx₀W, hx₀Z, hx₀1⟩ hwc2
      have e : subImg b2 (spTf T f) = subImg b1 (spTf T f) :=
        (subImg_eq_of_agree S.comp.agree hTf1 hTf2).symm
      have e' : b2 ⟨f, hfN2⟩ = b1 ⟨f, hfN1⟩ := (S.comp.agree f hfN1 hfN2).symm
      rw [e, e'] at h
      exact h
  have hb := S.comp.inj₁
  have hSN1 : Sb ≤ N1 := O.S_le.trans O.T_le₁
  obtain ⟨t₀, ht₀⟩ := O.cyc
  have ht₀T : t₀ ∈ T := by
    rw [ht₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have ht₀N : t₀ ∈ N1 := O.T_le₁ ht₀T
  have hcyc : subImg b1 T = subImg b1 Sb ⊔ Subgroup.zpowers (b1 ⟨t₀, ht₀N⟩) := by
    conv_lhs => rw [ht₀]
    rw [subImg_sup hSN1 (Subgroup.zpowers_le.mpr ht₀N), subImg_zpowers ht₀N]
  refine CFSG.QuasithinUnique.Lin2.burnsideF4m_transfer_contradiction_cyclic_oTwoRes hres hSyl
    (subImg_mono b1 O.S_le) (subImg_le_normalizer b1 O.S_norm) hcyc
    (mem_subImg_of_mem b1 hfN1 hfT)
    (fun h => O.f_not ((mem_subImg_iff_of_injective hb hfN1).mp h))
    ((sq_eq_one_iff_of_injective hb hfN1).mpr O.f_sq) ?_
  intro g hg
  obtain ⟨s, hsN, hsS, hs⟩ := mem_subImg.mp hg
  have hf1 : f ≠ 1 := fun h => O.f_not (h ▸ Sb.one_mem)
  have hfg2 : b1 ⟨f, hfN1⟩ ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hfN1).mpr O.f_sq
  have hs2 : s ^ 2 = 1 := by
    refine (sq_eq_one_iff_of_injective hb hsN).mp ?_
    rw [hs]
    calc (g⁻¹ * b1 ⟨f, hfN1⟩ * g) ^ 2 = g⁻¹ * b1 ⟨f, hfN1⟩ ^ 2 * g := by rw [sq, sq]; group
      _ = 1 := by rw [hfg2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h1 : b1 ⟨1, hsN⟩ = 1 := map_one b1
    rw [h1] at hs
    have : b1 ⟨f, hfN1⟩ = 1 := by
      calc b1 ⟨f, hfN1⟩ = g * (g⁻¹ * b1 ⟨f, hfN1⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [← hs]; group
    exact hf1 (congrArg Subtype.val (hb (this.trans (map_one b1).symm)))
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨i, hiI, -, hiφ⟩ := O.exists_conj S.comp hsS hso
  have hiT : i ∈ T := (mem_centerOf_iff.mp (O.I_center i hiI)).1
  have hiN : i ∈ N1 := O.T_le₁ hiT
  rw [amalgamMap_of_mem₁ b1 b2 hiN, amalgamMap_of_mem₁ b1 b2 hsN] at hiφ
  obtain ⟨c, hc⟩ := isConj_iff.mp hiφ
  set u : G := b1 ⟨i, hiN⟩ with hu
  have hfu : (g * c)⁻¹ * b1 ⟨f, hfN1⟩ * (g * c)⁻¹⁻¹ = u := by
    have h1 : c * u * c⁻¹ = g⁻¹ * b1 ⟨f, hfN1⟩ * g := hc.trans hs
    calc (g * c)⁻¹ * b1 ⟨f, hfN1⟩ * (g * c)⁻¹⁻¹ = c⁻¹ * (g⁻¹ * b1 ⟨f, hfN1⟩ * g) * c := by group
      _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [h1]
      _ = u := by group
  have hTg_le : subImg b1 T ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨t, htN, htT, rfl⟩ := mem_subImg.mp hy
    show b1 ⟨t, htN⟩ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_of_injective hb hiN htN).mpr
      ((mem_centerOf_iff.mp (O.I_center i hiI)).2 t htT)
  have h1 : Nat.card (subImg b1 T) ≤ twoPart (Subgroup.centralizer ({u} : Set G)) :=
    card_le_twoPart hTg_le hSyl.2.1
  have h2 : twoPart (Subgroup.centralizer ({u} : Set G)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := by
    unfold twoPart
    rw [card_centralizer_eq_of_conj hfu]
  have h3 : Nat.card (subImg b1 (spTf T f)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := hTfSyl.card_eq
  have h4 : Nat.card (spTf T f) < Nat.card T := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => O.f_not_central ?_)
    rw [mem_centerOf_iff]
    refine ⟨hfT, fun t ht => ?_⟩
    have : t ∈ spTf T f := by
      rw [h]
      exact ht
    exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  rw [card_subImg hb O.T_le₁] at h1
  rw [card_subImg hb hTf1] at h3
  omega

end Sp

section SpFour

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {T Sb N1 N2 : Subgroup Mb}
  {I : Finset Mb} {f : Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G} {M1 M2 : Subgroup G}

theorem burnsideF4m_SpGSetup_out_false4 [Finite Mb] [Finite G] {i0 i1 : Mb}
    (hres : oTwoRes (⊤ : Subgroup G) = ⊤)
    (S : SpGSetup N1 N2 b1 b2 M1 M2) (O : F431SpOut4 T Sb f N1 N2 I i0 i1) : False := by
  have hC := O.core
  have hfT := hC.f_mem
  have hfN1 : f ∈ N1 := hC.T_le₁ hfT
  have hSyl := S.sylow_outC hC
  have hTf1 : spTf T f ≤ N1 := inf_le_left.trans hC.T_le₁
  have hTfSyl : IsSylowTwoOf (subImg b1 (spTf T f))
      (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := S.sylow_Tf_four O
  have hb := S.comp.inj₁
  have hSN1 : Sb ≤ N1 := hC.S_le.trans hC.T_le₁
  obtain ⟨t₀, ht₀⟩ := hC.cyc
  have ht₀T : t₀ ∈ T := by
    rw [ht₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have ht₀N : t₀ ∈ N1 := hC.T_le₁ ht₀T
  have hcyc : subImg b1 T = subImg b1 Sb ⊔ Subgroup.zpowers (b1 ⟨t₀, ht₀N⟩) := by
    conv_lhs => rw [ht₀]
    rw [subImg_sup hSN1 (Subgroup.zpowers_le.mpr ht₀N), subImg_zpowers ht₀N]
  refine CFSG.QuasithinUnique.Lin2.burnsideF4m_transfer_contradiction_cyclic_oTwoRes hres hSyl
    (subImg_mono b1 hC.S_le) (subImg_le_normalizer b1 hC.S_norm) hcyc
    (mem_subImg_of_mem b1 hfN1 hfT)
    (fun h => hC.f_not ((mem_subImg_iff_of_injective hb hfN1).mp h))
    ((sq_eq_one_iff_of_injective hb hfN1).mpr hC.f_sq) ?_
  intro g hg
  obtain ⟨s, hsN, hsS, hs⟩ := mem_subImg.mp hg
  have hf1 : f ≠ 1 := fun h => hC.f_not (h ▸ Sb.one_mem)
  have hfg2 : b1 ⟨f, hfN1⟩ ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hfN1).mpr hC.f_sq
  have hs2 : s ^ 2 = 1 := by
    refine (sq_eq_one_iff_of_injective hb hsN).mp ?_
    rw [hs]
    calc (g⁻¹ * b1 ⟨f, hfN1⟩ * g) ^ 2 = g⁻¹ * b1 ⟨f, hfN1⟩ ^ 2 * g := by rw [sq, sq]; group
      _ = 1 := by rw [hfg2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h1 : b1 ⟨1, hsN⟩ = 1 := map_one b1
    rw [h1] at hs
    have : b1 ⟨f, hfN1⟩ = 1 := by
      calc b1 ⟨f, hfN1⟩ = g * (g⁻¹ * b1 ⟨f, hfN1⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [← hs]; group
    exact hf1 (congrArg Subtype.val (hb (this.trans (map_one b1).symm)))
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨i, hiI, -, hiφ⟩ := hC.exists_conj S.comp hsS hso
  have hiT : i ∈ T := (mem_centerOf_iff.mp (hC.I_center i hiI)).1
  have hiN : i ∈ N1 := hC.T_le₁ hiT
  rw [amalgamMap_of_mem₁ b1 b2 hiN, amalgamMap_of_mem₁ b1 b2 hsN] at hiφ
  obtain ⟨c, hc⟩ := isConj_iff.mp hiφ
  set u : G := b1 ⟨i, hiN⟩ with hu
  have hfu : (g * c)⁻¹ * b1 ⟨f, hfN1⟩ * (g * c)⁻¹⁻¹ = u := by
    have h1 : c * u * c⁻¹ = g⁻¹ * b1 ⟨f, hfN1⟩ * g := hc.trans hs
    calc (g * c)⁻¹ * b1 ⟨f, hfN1⟩ * (g * c)⁻¹⁻¹ = c⁻¹ * (g⁻¹ * b1 ⟨f, hfN1⟩ * g) * c := by group
      _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [h1]
      _ = u := by group
  have hTg_le : subImg b1 T ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨t, htN, htT, rfl⟩ := mem_subImg.mp hy
    show b1 ⟨t, htN⟩ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_of_injective hb hiN htN).mpr
      ((mem_centerOf_iff.mp (hC.I_center i hiI)).2 t htT)
  have h1 : Nat.card (subImg b1 T) ≤ twoPart (Subgroup.centralizer ({u} : Set G)) :=
    card_le_twoPart hTg_le hSyl.2.1
  have h2 : twoPart (Subgroup.centralizer ({u} : Set G)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := by
    unfold twoPart
    rw [card_centralizer_eq_of_conj hfu]
  have h3 : Nat.card (subImg b1 (spTf T f)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := hTfSyl.card_eq
  have h4 : Nat.card (spTf T f) < Nat.card T := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hC.f_not_central ?_)
    rw [mem_centerOf_iff]
    refine ⟨hfT, fun t ht => ?_⟩
    have : t ∈ spTf T f := by
      rw [h]
      exact ht
    exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  rw [card_subImg hb hC.T_le₁] at h1
  rw [card_subImg hb hTf1] at h3
  omega

end SpFour

end CFSG.Quasithin.H13.F431

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431

universe u v

section Main

variable {Mb : Type u} [Group Mb] [Finite Mb] {G : Type v} [Group G] [Finite G]
  {T Sb N N' V : Subgroup Mb} {f z t : Mb} {b : ↥N →* G} {b' : ↥N' →* G} {M M' : Subgroup G}

theorem burnsideF4m_UnGSetup_out_false (hres : oTwoRes (⊤ : Subgroup G) = ⊤)
    (S : UnGSetup N N' b b' M M') (O : F431UnOut T Sb f N N' z t V) : False := by
  have hb := S.comp.inj₁
  have hfT := O.f_mem
  have hfN : f ∈ N := O.T_le hfT
  have hSyl : IsSylowTwoOf (subImg b T) ⊤ := S.sylow_img O
  have hTfN : spTf T f ≤ N := inf_le_left.trans O.T_le
  have hTfSyl : IsSylowTwoOf (subImg b (spTf T f))
      (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) := S.sylow_Tf O
  have hSN : Sb ≤ N := O.S_le.trans O.T_le
  obtain ⟨t₀, ht₀⟩ := O.cyc
  have ht₀T : t₀ ∈ T := by
    rw [ht₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have ht₀N : t₀ ∈ N := O.T_le ht₀T
  have hcyc : subImg b T = subImg b Sb ⊔ Subgroup.zpowers (b ⟨t₀, ht₀N⟩) := by
    conv_lhs => rw [ht₀]
    rw [subImg_sup hSN (Subgroup.zpowers_le.mpr ht₀N), subImg_zpowers ht₀N]
  refine CFSG.QuasithinUnique.Lin2.burnsideF4m_transfer_contradiction_cyclic_oTwoRes hres hSyl
    (subImg_mono b O.S_le) (subImg_le_normalizer b O.S_norm) hcyc
    (mem_subImg_of_mem b hfN hfT)
    (fun h => O.f_not ((mem_subImg_iff_of_injective hb hfN).mp h))
    ((sq_eq_one_iff_of_injective hb hfN).mpr O.f_sq) ?_
  intro g hg
  obtain ⟨s, hsN, hsS, hs⟩ := mem_subImg.mp hg
  have hf1 : f ≠ 1 := fun h => O.f_not (h ▸ Sb.one_mem)
  have hfg2 : b ⟨f, hfN⟩ ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hfN).mpr O.f_sq
  have hs2 : s ^ 2 = 1 := by
    refine (sq_eq_one_iff_of_injective hb hsN).mp ?_
    rw [hs]
    calc (g⁻¹ * b ⟨f, hfN⟩ * g) ^ 2 = g⁻¹ * b ⟨f, hfN⟩ ^ 2 * g := by rw [sq, sq]; group
      _ = 1 := by rw [hfg2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h1 : b ⟨1, hsN⟩ = 1 := map_one b
    rw [h1] at hs
    have : b ⟨f, hfN⟩ = 1 := by
      calc b ⟨f, hfN⟩ = g * (g⁻¹ * b ⟨f, hfN⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [← hs]; group
    exact hf1 (congrArg Subtype.val (hb (this.trans (map_one b).symm)))
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨i, hi, -, hic⟩ := O.exists_rep S.comp hsS hso
  have hiN : i ∈ N := O.T_le (O.S_le (O.rep_mem hi))
  rw [amalgamMap_of_mem₁ b b' hsN, amalgamMap_of_mem₁ b b' hiN] at hic
  obtain ⟨c, hc⟩ := isConj_iff.mp hic.symm
  set u : G := b ⟨i, hiN⟩ with hu
  have hfu : (g * c) * u * (g * c)⁻¹ = b ⟨f, hfN⟩ := by
    calc (g * c) * u * (g * c)⁻¹ = g * (c * u * c⁻¹) * g⁻¹ := by group
      _ = g * b ⟨s, hsN⟩ * g⁻¹ := by rw [hc]
      _ = g * (g⁻¹ * b ⟨f, hfN⟩ * g) * g⁻¹ := by rw [hs]
      _ = b ⟨f, hfN⟩ := by group
  have hTg_le : subImg b (T ⊓ Subgroup.centralizer ({i} : Set Mb)) ≤
      Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨t, htN, ⟨htT, htC⟩, rfl⟩ := mem_subImg.mp hy
    show b ⟨t, htN⟩ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_of_injective hb hiN htN).mpr (Subgroup.mem_centralizer_singleton_iff.mp htC)
  have hp : IsPGroup 2 (subImg b (T ⊓ Subgroup.centralizer ({i} : Set Mb))) :=
    hSyl.2.1.to_le (subImg_mono b inf_le_left)
  have h1 := card_le_twoPart hTg_le hp
  have h2 : twoPart (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) =
      twoPart (Subgroup.centralizer ({u} : Set G)) := by
    unfold twoPart
    rw [card_centralizer_eq_of_conj hfu]
  have h3 : Nat.card (subImg b (spTf T f)) =
      twoPart (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) := hTfSyl.card_eq
  have h4 : Nat.card (spTf T f) < Nat.card ↥(T ⊓ Subgroup.centralizer ({i} : Set Mb)) := by
    rcases hi with h | h
    · rw [h]
      exact O.Tf_lt_z
    · rw [h]
      exact O.Tf_lt_t
  rw [card_subImg hb (inf_le_left.trans O.T_le)] at h1
  rw [card_subImg hb hTfN] at h3
  omega

end Main

end CFSG.Quasithin.H13.F431.Un
