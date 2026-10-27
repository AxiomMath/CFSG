module

public import CFSG.Quasithin.H13.U3C137
public import CFSG.Quasithin.H13.U3P33
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C1PackS15212A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_ne_one_mem_center_of_normal {T Z : Subgroup G} (hT2 : IsPGroup 2 T)
    (hZT : Z ≤ T) (hZ1 : Z ≠ ⊥) (hTZ : T ≤ normalizer (Z : Set G)) [Finite G] :
    ∃ w ∈ Z, w ≠ 1 ∧ w ∈ centralizer (T : Set G) := by
  have hTnil : Group.IsNilpotent T := hT2.isNilpotent
  have hWn : (Z.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hZT).mpr hTZ
  have hWT' : Z.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hZ1
    rw [← map_subgroupOf_eq_of_le hZT, hbot, Subgroup.map_bot]
  obtain ⟨⟨w, hw⟩, hw1⟩ := (ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hWT')
  refine ⟨(w : G), mem_subgroupOf.mp (mem_inf.mp hw).1,
    fun h => hw1 (Subtype.ext (Subtype.ext h)), mem_centralizer_iff.2 fun t ht => ?_⟩
  have := mem_center_iff.mp (mem_inf.mp hw).2 ⟨t, ht⟩
  simpa using congrArg Subtype.val this

@[expose] noncomputable def fix15 : Subgroup (GL (Fin 6) (ZMod 2)) where
  carrier := {k | glLin k (vecOf 15) = vecOf 15}
  mul_mem' := by
    intro a b ha hb
    change glLin a (vecOf 15) = vecOf 15 at ha
    change glLin b (vecOf 15) = vecOf 15 at hb
    change glLin (a * b) (vecOf 15) = vecOf 15
    rw [map_mul, LinearEquiv.mul_apply, hb, ha]
  one_mem' := by
    change glLin 1 (vecOf 15) = vecOf 15
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    change glLin a (vecOf 15) = vecOf 15 at ha
    change glLin a⁻¹ (vecOf 15) = vecOf 15
    have h1 : glLin a⁻¹ (glLin a (vecOf 15)) = vecOf 15 := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [ha] at h1

theorem fix15_codes : ∀ i ∈ ([0, 1, 2, 3] : List (Fin 5)), vapp (u6c i) 15 = 15 := by
  decide +kernel

theorem u33A_le_fix15 :
    u33Data.A ≤ fix15.comap rho6 := by
  have hgen : ∀ i ∈ ([0, 1, 2, 3] : List (Fin 5)), u6GL i ∈ fix15 := fun i hi => by
    show glLin (u6GL i) (vecOf 15) = vecOf 15
    rw [glLin_vecOf rfl, fix15_codes i hi]
  obtain ⟨ha, hb, hs, hx, -⟩ := rho6_abs
  refine (closure_le _).2 ?_
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · show rho6 u33Data.a ∈ fix15
    rw [ha]
    exact hgen 0 (by simp)
  · show rho6 u33Data.b ∈ fix15
    rw [hb]
    exact hgen 1 (by simp)
  · show rho6 u33Data.s ∈ fix15
    rw [hs]
    exact hgen 2 (by simp)
  · show rho6 u33Data.x ∈ fix15
    rw [hx]
    exact hgen 3 (by simp)

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem isSylowTwoOf_inf
    (S : HullSetting G T L V z) : IsSylowTwoOf (T ⊓ L) L := by
  have hloc := S.hH.faithful.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  exact A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer S.hTL)

theorem inf_normalizer_V₁_le
    (S : HullSetting G T L V z) : L ⊓ normalizer (S.V₁ : Set G) ≤ L₁Of L S.V₁ ⊔ T := by
  have hTN : T ⊓ L ≤ L ⊓ normalizer (S.V₁ : Set G) := fun t ht => ⟨ht.2, S.T_le_N_V₁ ht.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ normalizer (S.V₁ : Set G)) :=
    C1GN.isSylowTwoOf_of_le S.isSylowTwoOf_inf hTN inf_le_left
  have h := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  rw [← h, ← oTwoRes_eq_oTwoUpper]
  exact sup_le_sup le_rfl inf_le_left

theorem L₁T_lt
    (S : HullSetting G T L V z) : L₁Of L S.V₁ ⊔ T < L ⊔ T := by
  refine lt_of_le_of_ne (sup_le_sup ((oTwoRes_le _).trans inf_le_left) le_rfl) fun h => ?_
  have hLH : L ≤ S.H := (le_sup_left.trans h.symm.le).trans S.L₁T_le_H
  rw [S.H_eq] at hLH
  have hz : z ∈ V ⊓ centralizer (L : Set G) :=
    ⟨S.hzV, mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hLH hl)⟩
  rw [inf_centralizer_L_eq_bot S.hF, mem_bot] at hz
  exact S.hz1 hz

theorem L₁T_max
    (S : HullSetting G T L V z) (H : Subgroup G) (hPH : L₁Of L S.V₁ ⊔ T ≤ H)
    (hHX : H ≤ L ⊔ T) : H = L₁Of L S.V₁ ⊔ T ∨ H = L ⊔ T := by
  set K : Subgroup U33G := (((H ⊓ L).subgroupOf (normalizer (V : Set G))).map S.rho).comap rho6
    with hK
  have hTH : T ≤ H := le_sup_right.trans hPH
  have hmemK : ∀ {h : G} (hhH : h ∈ H) (hhL : h ∈ L) {g : U33G},
      rho6 g = S.rho ⟨h, S.hLV hhL⟩ → g ∈ K := fun hhH hhL g hg =>
    mem_comap.2 (hg ▸ mem_map_of_mem _ (mem_subgroupOf.2 ⟨hhH, hhL⟩))
  obtain ⟨ha, hb, hs, hx, -⟩ := rho6_abs
  have hgen : ∀ (i : Fin 5) (g : U33G), i ∈ ([0, 1, 2] : List (Fin 5)) → rho6 g = u6GL i →
      g ∈ K := by
    intro i g hi hg
    obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho (u6GL_mem_rhoT hi)
    exact hmemK (hTH htTL.1) htTL.2 (by rw [hg, ← hrho])
  have hxK : u33Data.x ∈ K := by
    have hl₁N : S.l₁ ∈ L ⊓ normalizer (S.V₁ : Set G) := by
      rw [S.normalizer_V₁]
      exact ⟨S.l₁_mem, S.l₁_H⟩
    refine hmemK (hPH (S.inf_normalizer_V₁_le hl₁N)) S.l₁_mem ?_
    rw [hx, ← xGL_eq_u6GL]
    exact (S.rho_eq_of_spec S.l₁_N S.l₁_spec).symm
  have hAK : u33Data.A ≤ K := by
    refine (closure_le _).2 ?_
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hgen 0 _ (by simp) ha
    · exact hgen 1 _ (by simp) hb
    · exact hgen 2 _ (by simp) hs
    · exact hxK
  rcases u33Data.lattice K (u33Data.T_le_A.trans hAK) with h | h | h | h
  · exact absurd (le_antisymm u33Data.T_le_A (h ▸ hAK)) u33Data.T_ne_A
  ·
    left
    refine le_antisymm (fun g hg => ?_) hPH
    obtain ⟨l, hl, t, ht, rfl⟩ : ∃ l ∈ L, ∃ t ∈ T, g = l * t := by
      have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
        coe_mul_of_right_le_normalizer_left L T S.hTL
      have hx' : g ∈ (L : Set G) * (T : Set G) := by
        rw [← hmul]
        exact hHX hg
      obtain ⟨l, hl, t', ht', rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨l, hl, t', ht', rfl⟩
    have hlH : l ∈ H := by
      have := mul_mem hg (inv_mem (hTH ht))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨g', hg'J⟩ : S.rho ⟨l, S.hLV hl⟩ ∈ J6 := S.rho_L_mem hl
    have hg'K : g' ∈ K := hmemK hlH hl hg'J
    rw [h] at hg'K
    have hfix : glLin (S.rho ⟨l, S.hLV hl⟩) (vecOf 15) = vecOf 15 := by
      have := u33A_le_fix15 hg'K
      rw [mem_comap, hg'J] at this
      exact this
    have hlN : l ∈ normalizer (S.V₁ : Set G) := by
      rw [S.normalizer_V₁]
      exact (S.mem_H_iff (S.hLV hl) (S.rho_spec ⟨l, S.hLV hl⟩)).2 hfix
    exact mul_mem (S.inf_normalizer_V₁_le ⟨hl, hlN⟩) (mem_sup_right ht)
  ·
    exfalso
    have hAB : u33Data.A ≤ u33Data.A ⊓ u33Data.B := le_inf le_rfl (h ▸ hAK)
    rw [u33Data.inf_AB] at hAB
    exact u33Data.T_ne_A (le_antisymm u33Data.T_le_A hAB)
  ·
    right
    refine le_antisymm hHX (sup_le (fun l hl => ?_) hTH)
    obtain ⟨g', hg'J⟩ : S.rho ⟨l, S.hLV hl⟩ ∈ J6 := S.rho_L_mem hl
    have hg'K : g' ∈ K := h ▸ mem_top g'
    obtain ⟨⟨h', hh'N⟩, hh', hh'ρ⟩ := mem_map.1 (mem_comap.1 hg'K)
    have hh'HL : h' ∈ H ⊓ L := mem_subgroupOf.1 hh'
    have h1 : S.rho ((⟨h', hh'N⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV hl⟩) = 1 := by
      rw [map_mul, map_inv, hh'ρ, hg'J, inv_mul_cancel]
    have h2 : (((⟨h', hh'N⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV hl⟩ :
        normalizer (V : Set G)) : G) ∈ centralizer (V : Set G) :=
      (mem_centralizer_V_iff _ (S.rho_spec _)).2 h1
    have h3 : h'⁻¹ * l ∈ L ⊓ centralizer (V : Set G) :=
      mem_inf.2 ⟨mul_mem (inv_mem hh'HL.2) hl, h2⟩
    have h4 : h'⁻¹ * l ∈ H := hTH (S.pCoreOf_L_le (S.inf_centralizer_le h3)).1
    have := mul_mem hh'HL.1 h4
    rwa [mul_inv_cancel_left] at this

theorem not_line
    (S : HullSetting G T L V z) {l : Subgroup G} (hlV : l ≤ V) (hl4 : Nat.card ↥l = 4)
    (hN : L₁Of L S.V₁ ⊔ T ≤ normalizer (l : Set G)) : False := by
  classical
  have hl1 : l ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hl4
    omega
  obtain ⟨w, hwl, hw1, hwT⟩ := exists_ne_one_mem_center_of_normal S.hH.sylow.1
    (hlV.trans S.hVT) hl1 (le_sup_right.trans hN)
  have hwz : w ∈ zpowers z := by
    rw [← S.hVz]
    exact ⟨hlV hwl, hwT⟩
  have hzl : z ∈ l := by
    rw [mem_zpowers_iff_mem_range_orderOf, S.hz2, Finset.mem_image] at hwz
    obtain ⟨k, hk, hkw⟩ := hwz
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at hkw
      exact absurd hkw.symm hw1
    · rw [pow_one] at hkw
      exact hkw ▸ hwl
  have hV2 : A6.IsV2 T V l := by
    refine ⟨?_, hlV, le_sup_right.trans hN, hl4⟩
    rw [S.fsuV1_eq_V₁, S.V₁_eq, zpowers_le]
    exact hzl
  have hle : l = S.V₂ := (S.V2_eq hV2).trans S.V₂_eq_pullSub.symm
  have h3 : conjClosure S.V₂ (L₁Of L S.V₁) ≤ S.V₂ := conjClosure_le fun h hh v hv => by
    rw [← hle] at hv ⊢
    exact (mem_normalizer_iff.1 (hN (mem_sup_left hh)) v).1 hv
  rw [S.gen3] at h3
  have h4 := Subgroup.card_le_of_le h3
  rw [S.card_V₃, S.card_V₂] at h4
  omega

theorem c137
    (S : HullSetting G T L V z) (hC137 : C137Statement) :
    CharNormal (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T))) (L ⊔ T) ∨ H13.IsG2Block L := by
  have hcharL : CharTwo L := A5.charTwo_of_faithful S.hH.qtke.2.1 S.hH.sylow S.hH.faithful
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
    intro x hx
    have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
      coe_mul_of_right_le_normalizer_left L T S.hTL
    have hx' : x ∈ (L : Set G) * (T : Set G) := by
      rw [← hmul]
      exact hx
    obtain ⟨l, hl, t', ht', rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨l, hl, t', ht', rfl⟩
  have hirr := u3_isIrrPlusIn S.h1332 S.hH S.hU3 S.hF
  have hVL : ⁅V, L⁆ ≠ ⊥ := by
    rw [hirr.2.2.2.1]
    exact hirr.2.1
  have hcU : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := card_of_lieModel_PSU_three_three S.hU3
  have hL32 : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := fun h => by
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h
    have := Nat.card_congr e.toEquiv
    rw [hcU, HSType.card_SL_three_two] at this
    omega
  rcases hC137 G (L ⊔ T) T V L (L₁Of L S.V₁ ⊔ T) (L₁Of L S.V₁ ⊔ T)
      (charTwo_sup_of_normalizes S.hH.sylow.1 S.hTL hcharL)
      (A5.isSylowTwoOf_of_le S.hH.sylow le_sup_right) hLT S.hH.faithful.1.2.1 hcharL
      (Or.inr (Or.inr (Or.inr S.hU3))) (Or.inl S.hU3) le_sup_right le_rfl S.L₁T_lt
      S.L₁T_max (Or.inl rfl) S.isTwoReducedIn hVL (fun h => absurd h hL32) with
    h | h | ⟨-, l, -, hlV, hl4, hN⟩ | h
  · exact Or.inl h
  · exact Or.inr (h.2.2.2 S.hU3)
  · rw [inf_centralizer_L_eq_bot S.hF, card_bot, mul_one] at hl4
    exact (S.not_line hlV hl4 hN).elim
  · exfalso
    rcases h with he | h
    · obtain ⟨e⟩ := he
      have := Nat.card_congr e.toEquiv
      rw [hcU, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      norm_num [Nat.factorial] at this
    · exact not_isHatA6_of_psu S.hU3 h

end HullSetting

theorem stmt13_3_10_U33
    (h1332 : Stmt13_3_2) (hC137 : C137Statement) [Finite G] {T L V : Subgroup G}
    (hH : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    CharNormal (baum (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) (L ⊔ T) ∨ H13.IsG2Block L := by
  obtain ⟨z, hF⟩ := u3_frame_of_irrPlus h1332 hH hU3 hV
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  let S : HullSetting G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  rw [S.fsuV1_eq_V₁]
  exact S.c137 hC137

end CFSG.Quasithin.H13.U3
