module

public import CFSG.Quasithin.Vol2.Ch12Sec6L11a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

@[expose] def duads : Finset (Fin 8 → ZMod 2) :=
  ((six ×ˢ six).filter fun p => p.1 < p.2).image fun p => B5FinS8.pv p.1 p.2

@[expose] def vSix : Fin 8 → ZMod 2 := B5FinS8.pv 2 3 + B5FinS8.pv 4 5 + B5FinS8.pv 6 7

@[expose] def quads : Finset (Fin 8 → ZMod 2) := duads.image fun x => x + vSix

theorem card_duads_nbhd : ∀ x ∈ duads, (duads.filter fun y => x + y ∈ duads).card = 8 := by
  decide +kernel

theorem card_quads_nbhd : ∀ x ∈ quads, (quads.filter fun y => x + y ∈ quads).card = 6 := by
  decide +kernel

theorem classify_core : ∀ x : Fin 8 → ZMod 2, x 0 = 0 → x 1 = 0 → ∑ i, x i = 0 →
    x = 0 ∨ x ∈ duads ∨ x ∈ quads ∨ x = vSix := by
  decide +kernel

theorem mem_duads_iff : ∀ x : Fin 8 → ZMod 2, x ∈ duads ↔
    ∃ i j : Fin 8, i ∈ six ∧ j ∈ six ∧ i ≠ j ∧ x = B5FinS8.pv i j := by
  decide +kernel

theorem vSix_apply : ∀ i : Fin 8, vSix i = if i ∈ six then 1 else 0 := by
  decide +kernel

theorem pv_mem_duads {i j : Fin 8} (hi : i ∈ six) (hj : j ∈ six) (hij : i ≠ j) :
    B5FinS8.pv i j ∈ duads :=
  (mem_duads_iff _).2 ⟨i, j, hi, hj, hij, rfl⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem beta_mem_of_mem_Vv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {u : G} (hu : u ∈ V)
    (huv : u ∈ Vv L V v) : ∃ c ∈ core01, F.β ⟨u, hu⟩ = QuotientGroup.mk c := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have key : ∀ x (hx : x ∈ V), ∀ l ∈ Lv L v, ∃ hy : l * x⁻¹ * l⁻¹ ∈ V,
      F.β (⟨x, hx⟩ * ⟨_, hy⟩) ∈ core01.map (QuotientGroup.mk' (natKer 8)) := by
    intro x hx l hl
    have hlL : l ∈ L := Lv_le_L L v hl
    have hσ : psiP F hH ⟨l, hlL⟩ ∈ A6s := psiP_mem_A6s h1222 F hH hv hβ
      (show (⟨l, hlL⟩ : ↥L) ∈ (Lv L v).subgroupOf L from hl)
    obtain ⟨hσ0, hσ1, -⟩ := mem_A6s.1 hσ
    have hy : l * x⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hlL) _).1 (V.inv_mem hx)
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (F.β ⟨x, hx⟩)
    have hact := actsAs_psiP F hH ⟨l, hlL⟩ ⟨x, hx⟩⁻¹ ⟨_, hy⟩ rfl
    have h2 : F.β (⟨x, hx⟩ * ⟨_, hy⟩) =
        QuotientGroup.mk (c * coreAct 8 (psiP F hH ⟨l, hlL⟩) c⁻¹) := by
      rw [map_mul, hact, map_inv, ← hc, ← QuotientGroup.mk_inv, dAct_mk, ← QuotientGroup.mk_mul]
    refine ⟨hy, c * coreAct 8 (psiP F hH ⟨l, hlL⟩) c⁻¹, mem_core01.2 ⟨coord_mul_coreAct_inv _ _
      (by rw [Equiv.Perm.inv_eq_iff_eq, hσ0]), coord_mul_coreAct_inv _ _
      (by rw [Equiv.Perm.inv_eq_iff_eq, hσ1])⟩, ?_⟩
    rw [QuotientGroup.mk'_apply]
    exact h2.symm
  have hle : Vv L V v ≤
      ((core01.map (QuotientGroup.mk' (natKer 8))).comap F.β).map V.subtype := by
    rw [Vv, Subgroup.commutator_le]
    intro x hx l hl
    obtain ⟨hy, hmem⟩ := key x hx l hl
    refine ⟨⟨x, hx⟩ * ⟨_, hy⟩, hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, commutatorElement_def]
    group
  obtain ⟨w, hw, hwu⟩ := hle huv
  have hwu' : w = ⟨u, hu⟩ := Subtype.ext hwu
  rw [hwu'] at hw
  obtain ⟨c, hc, hcw⟩ := hw
  exact ⟨c, hc, hcw.symm⟩

omit [IsMulCommutative ↥V] in
theorem Vv_le_V (hH : Hyp126 G T L V) (v : G) : Vv L V v ≤ V := by
  rw [Vv, Subgroup.commutator_le]
  intro x hx l hl
  have hl' : l ∈ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1 (Lv_le_L L v hl)
  have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem hx ((Subgroup.mem_normalizer_iff.1 hl' _).1 (V.inv_mem hx))

noncomputable def coordV (F : Frame126 T L V) (y : G) : Fin 8 → ZMod 2 := by
  classical
  exact if h : ∃ hy : y ∈ V, ∃ c : ↥(coreMod 8), c ∈ core01 ∧ F.β ⟨y, hy⟩ = QuotientGroup.mk c
    then Multiplicative.toAdd ((h.choose_spec.choose : ↥(coreMod 8)) : PermMod 8) else 0

omit [Finite G] in
theorem coordV_eq {F : Frame126 T L V} {y : G} (hy : y ∈ V) {c : ↥(coreMod 8)} (hc : c ∈ core01)
    (hβy : F.β ⟨y, hy⟩ = QuotientGroup.mk c) :
    coordV F y = Multiplicative.toAdd (c : PermMod 8) := by
  have h : ∃ hy : y ∈ V, ∃ c : ↥(coreMod 8), c ∈ core01 ∧
      F.β ⟨y, hy⟩ = QuotientGroup.mk c := ⟨hy, c, hc, hβy⟩
  rw [coordV, dite_eq_left h]
  have h1 := h.choose_spec.choose_spec
  have heq : h.choose_spec.choose = c :=
    eq_of_mk_eq (mem_core01.1 h1.1).1 (mem_core01.1 hc).1 (h1.2.symm.trans hβy)
  rw [heq]

theorem coordV_spec (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {y : G} (hy : y ∈ V)
    (hyv : y ∈ Vv L V v) : ∃ c ∈ core01, Multiplicative.toAdd (c : PermMod 8) = coordV F y ∧
      F.β ⟨y, hy⟩ = QuotientGroup.mk c := by
  obtain ⟨c, hc, hβc⟩ := beta_mem_of_mem_Vv h1222 F hH hv hβ hy hyv
  exact ⟨c, hc, (coordV_eq hy hc hβc).symm, hβc⟩

theorem coordV_injOn (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {y y' : G} (hyv : y ∈ Vv L V v)
    (hyv' : y' ∈ Vv L V v) (h : coordV F y = coordV F y') : y = y' := by
  have hy := Vv_le_V hH v hyv
  have hy' := Vv_le_V hH v hyv'
  obtain ⟨c, hc, hcy, hβc⟩ := coordV_spec h1222 hH hv hβ hy hyv
  obtain ⟨c', hc', hcy', hβc'⟩ := coordV_spec h1222 hH hv hβ hy' hyv'
  have hcc : c = c' := Subtype.ext (Multiplicative.toAdd.injective (hcy.trans (h.trans hcy'.symm)))
  exact eq_of_beta_eq_of_mem_Vv h1222 hH hv hβ hy hy' hyv hyv' (by rw [hβc, hβc', hcc])

theorem coordV_mul (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {y y' : G} (hyv : y ∈ Vv L V v)
    (hyv' : y' ∈ Vv L V v) : coordV F (y * y') = coordV F y + coordV F y' := by
  have hy := Vv_le_V hH v hyv
  have hy' := Vv_le_V hH v hyv'
  obtain ⟨c, hc, hcy, hβc⟩ := coordV_spec h1222 hH hv hβ hy hyv
  obtain ⟨c', hc', hcy', hβc'⟩ := coordV_spec h1222 hH hv hβ hy' hyv'
  have hmul : F.β ⟨y * y', V.mul_mem hy hy'⟩ = QuotientGroup.mk (c * c') := by
    rw [show (⟨y * y', V.mul_mem hy hy'⟩ : ↥V) = ⟨y, hy⟩ * ⟨y', hy'⟩ from rfl, map_mul, hβc, hβc',
      QuotientGroup.mk_mul]
  rw [coordV_eq _ (core01.mul_mem hc hc') hmul, ← hcy, ← hcy']
  rfl

theorem coordV_conj (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {l : ↥L} (hl : (l : G) ∈ Lv L v)
    {y : G} (hyv : y ∈ Vv L V v) :
    coordV F ((l : G) * y * (l : G)⁻¹) = fun i => coordV F y ((psiP F hH l)⁻¹ i) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hy := Vv_le_V hH v hyv
  obtain ⟨c, hc, hcy, hβc⟩ := coordV_spec h1222 hH hv hβ hy hyv
  have hσ : psiP F hH l ∈ A6s := psiP_mem_A6s h1222 F hH hv hβ
    (show l ∈ (Lv L v).subgroupOf L from hl)
  obtain ⟨hσ0, hσ1, -⟩ := mem_A6s.1 hσ
  have hwV : (l : G) * y * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV l.2) y).1 hy
  have hact := actsAs_psiP F hH l ⟨y, hy⟩ ⟨_, hwV⟩ rfl
  have hc' : coreAct 8 (psiP F hH l) c ∈ core01 := by
    rw [mem_core01, coreAct_coe, permAct_apply, permAct_apply]
    have h0 : (psiP F hH l)⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, hσ0]
    have h1 : (psiP F hH l)⁻¹ 1 = 1 := by rw [Equiv.Perm.inv_eq_iff_eq, hσ1]
    rw [h0, h1]
    exact mem_core01.1 hc
  rw [coordV_eq hwV hc' (by rw [hact, hβc, dAct_mk]), ← hcy]
  funext i
  rw [coreAct_coe, permAct_apply]

theorem mem_Delta_iff (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {u : G} :
    u ∈ Delta F v ↔ u ∈ Vv L V v ∧ coordV F u ∈ duads := by
  constructor
  · rintro ⟨huV, huv, i, j, hi, hj, hij, hβu⟩
    refine ⟨huv, ?_⟩
    obtain ⟨c, hc, hcu, hβc⟩ := coordV_spec h1222 hH hv hβ huV huv
    have hceq : c = pe i j := eq_of_mk_eq (mem_core01.1 hc).1
      (by rw [S126L20a.toAdd_pe]; exact (pv_zero_of_two_le i j hi hj).1) (hβc.symm.trans hβu)
    rw [← hcu, hceq, S126L20a.toAdd_pe]
    exact pv_mem_duads (mem_six_of_two_le i hi) (mem_six_of_two_le j hj) hij
  · rintro ⟨huv, hD⟩
    have huV := Vv_le_V hH v huv
    obtain ⟨i, j, hi, hj, hij, hx⟩ := (mem_duads_iff _).1 hD
    obtain ⟨c, hc, hcu, hβc⟩ := coordV_spec h1222 hH hv hβ huV huv
    have hceq : c = pe i j := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [hcu, hx, S126L20a.toAdd_pe]
    refine ⟨huV, huv, i, j, two_le_of_mem_six i hi, two_le_of_mem_six j hj, hij, ?_⟩
    rw [hβc, hceq]

theorem coordV_cases (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {y : G} (hyv : y ∈ Vv L V v) :
    coordV F y = 0 ∨ coordV F y ∈ duads ∨ coordV F y ∈ quads ∨ coordV F y = vSix := by
  obtain ⟨c, hc, hcy, -⟩ := coordV_spec h1222 hH hv hβ (Vv_le_V hH v hyv) hyv
  obtain ⟨h0, h1⟩ := mem_core01.1 hc
  have hs : ∑ i, Multiplicative.toAdd (c : PermMod 8) i = 0 := mem_coreMod.1 c.2
  rw [← hcy]
  exact classify_core _ h0 h1 hs

theorem coordV_one (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) : coordV F (1 : G) = 0 := by
  have h1 := coordV_mul h1222 hH hv hβ ((Vv L V v).one_mem) ((Vv L V v).one_mem)
  rw [mul_one] at h1
  have : coordV F (1 : G) + coordV F 1 = coordV F 1 + 0 := by rw [add_zero, ← h1]
  exact add_left_cancel this

end S126T2

end CFSG.Quasithin.H13
