module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2J

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_conj_Lv (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {u : G} (hu : u ∈ V)
    {a b : Fin 8} (hab : a ≠ b) (hβu : F.β ⟨u, hu⟩ = QuotientGroup.mk (pe a b)) :
    ∃ g : ↥L, Lv L u = (Lv L v).map (MulAut.conj (g : G)).toMonoidHom ∧
      ((psiP F hH g 0 = a ∧ psiP F hH g 1 = b) ∨ (psiP F hH g 0 = b ∧ psiP F hH g 1 = a)) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hnv : IsNonsing (F.β ⟨v, hv⟩) := hβ ▸ ⟨pe 0 1, rfl, S126L20a.wt_pe (by decide)⟩
  have hnu : IsNonsing (F.β ⟨u, hu⟩) := hβu ▸ ⟨pe a b, rfl, S126L20a.wt_pe hab⟩
  obtain ⟨l, hlL, hl, hlβ⟩ := (part1 F ⟨v, hv⟩ ⟨u, hu⟩ (ne_one_of_nonsing hnv)
    (ne_one_of_nonsing hnu)).2 (iff_of_true hnv hnu)
  obtain ⟨w, hw⟩ : ∃ w : G, w = l * v * l⁻¹ := ⟨_, rfl⟩
  have hwV : w ∈ V := hw ▸ (Subgroup.mem_normalizer_iff.1 hl v).1 hv
  have hβw : F.β ⟨w, hwV⟩ = F.β ⟨u, hu⟩ := by
    rw [← hlβ]
    congr 1
    exact Subtype.ext hw
  obtain ⟨z, hzdef⟩ : ∃ z : G, z = w * u⁻¹ := ⟨_, rfl⟩
  have hwz : w = z * u := by rw [hzdef]; group
  have hz : z ∈ Subgroup.centralizer (L : Set G) := by
    have h1 : F.β (⟨w, hwV⟩ * (⟨u, hu⟩ : ↥V)⁻¹) = 1 := by
      rw [map_mul, map_inv, hβw, mul_inv_cancel]
    rw [hzdef]
    exact (F.β_ker _).1 h1
  have hGu : ∀ x ∈ L, x ∈ Gv u ↔ x ∈ Gv w := by
    intro x hx
    have hxz : x * z = z * x := Subgroup.mem_centralizer_iff.1 hz x hx
    rw [Gv, Gv, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      hwz]
    constructor
    · intro h
      calc x * (z * u) = z * (x * u) := by rw [← mul_assoc, hxz, mul_assoc]
        _ = z * (u * x) := by rw [h]
        _ = z * u * x := by group
    · intro h
      have h2 : z * (x * u) = z * (u * x) := by
        calc z * (x * u) = x * (z * u) := by rw [← mul_assoc, ← hxz, mul_assoc]
          _ = z * u * x := h
          _ = z * (u * x) := by group
      exact mul_left_cancel h2
  have hmap : L ⊓ Gv u = (L ⊓ Gv v).map (MulAut.conj l).toMonoidHom := by
    ext x
    constructor
    · rintro ⟨hxL, hxu⟩
      have hxw := (hGu x hxL).1 hxu
      refine ⟨l⁻¹ * x * l, ⟨L.mul_mem (L.mul_mem (L.inv_mem hlL) hxL) hlL, ?_⟩, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
      show l⁻¹ * x * l ∈ Gv v
      rw [Gv, Subgroup.mem_centralizer_singleton_iff] at hxw ⊢
      rw [hw] at hxw
      calc l⁻¹ * x * l * v = l⁻¹ * (x * (l * v * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * v * l⁻¹) * x) * l := by rw [hxw]
        _ = v * (l⁻¹ * x * l) := by group
    · rintro ⟨y, ⟨hyL, hyv⟩, rfl⟩
      have hyL' : l * y * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hlL hyL) (L.inv_mem hlL)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine ⟨hyL', (hGu _ hyL').2 ?_⟩
      have hyv' : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.1 hyv
      rw [Gv, Subgroup.mem_centralizer_singleton_iff, hw]
      calc l * y * l⁻¹ * (l * v * l⁻¹) = l * (y * v) * l⁻¹ := by group
        _ = l * (v * y) * l⁻¹ := by rw [hyv']
        _ = l * v * l⁻¹ * (l * y * l⁻¹) := by group
  refine ⟨⟨l, hlL⟩, ?_, ?_⟩
  · rw [Lv, hmap, ← map_perfectCore]
    rfl
  · have hact := S126T2.actsAs_psiP F hH ⟨l, hlL⟩ ⟨v, hv⟩ ⟨w, hwV⟩ hw
    rw [hβw, hβu, hβ, S126L20a.dAct_pe] at hact
    rcases mk_pe_eq_mk_pe hab hact with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2⟩

theorem exists_Lu (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {u : G} (hu : u ∈ V)
    {a b : Fin 8} (hab : a ≠ b) (hβu : F.β ⟨u, hu⟩ = QuotientGroup.mk (pe a b))
    {c : Equiv.Perm (Fin 8)} (hc : c ∈ alternatingGroup (Fin 8)) (hca : c a = a)
    (hcb : c b = b) : ∃ y : ↥L, (y : G) ∈ Lv L u ∧ psiP F hH y = c := by
  obtain ⟨g, hg, hg01⟩ := exists_conj_Lv F hH hv hβ hu hab hβu
  set π := psiP F hH g with hπ
  have hc' : π⁻¹ * c * π ∈ A6s := by
    have hfix : ∀ x : Fin 8, (x = a ∨ x = b) → (π⁻¹ * c * π) (π⁻¹ x) = π⁻¹ x := by
      intro x hx
      simp only [Equiv.Perm.mul_apply, S126Ex.perm_apply_inv]
      rcases hx with rfl | rfl
      · rw [hca]
      · rw [hcb]
    have hπA : π ∈ alternatingGroup (Fin 8) := psiP_mem F hH g
    refine mem_A6s.2 ⟨?_, ?_, (alternatingGroup (Fin 8)).mul_mem ((alternatingGroup (Fin 8)).mul_mem
      ((alternatingGroup (Fin 8)).inv_mem hπA) hc) hπA⟩
    · rcases hg01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have := hfix a (Or.inl rfl)
        rwa [show π⁻¹ a = 0 by rw [Equiv.Perm.inv_eq_iff_eq, h0]] at this
      · have := hfix b (Or.inr rfl)
        rwa [show π⁻¹ b = 0 by rw [Equiv.Perm.inv_eq_iff_eq, h0]] at this
    · rcases hg01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have := hfix b (Or.inr rfl)
        rwa [show π⁻¹ b = 1 by rw [Equiv.Perm.inv_eq_iff_eq, h1]] at this
      · have := hfix a (Or.inl rfl)
        rwa [show π⁻¹ a = 1 by rw [Equiv.Perm.inv_eq_iff_eq, h1]] at this
  obtain ⟨y, hy, hyc⟩ := exists_Lv_of_A6s h1222 F hH hv hβ _ hc'
  refine ⟨g * y * g⁻¹, ?_, ?_⟩
  · rw [hg]
    exact ⟨y, hy, by simp⟩
  · rw [map_mul, map_mul, map_inv, hyc, ← hπ]
    group

theorem two_le_of_mem_six : ∀ a : Fin 8, a ∈ six → 2 ≤ a.val := by
  decide

theorem exists_mem_Delta (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {a b : Fin 8}
    (ha : a ∈ six) (hb : b ∈ six) (hab : a ≠ b) :
    ∃ u ∈ Delta F v, ∃ hu : u ∈ V, F.β ⟨u, hu⟩ = QuotientGroup.mk (pe a b) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨i, hi, c, hc, hia, hib, hca, hcb, hic⟩ : ∃ i ∈ six, ∃ c ∈ six, i ≠ a ∧ i ≠ b ∧
      c ≠ a ∧ c ≠ b ∧ i ≠ c := by
    revert a b
    decide
  have hσ : cy b a c ∈ A6s := cy_mem (Ne.symm hab) (Ne.symm hcb) hb ha hc
  have hσa : cy b a c a = b := by
    rw [cy, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hca),
      Equiv.swap_apply_right]
  have hσi : cy b a c i = i := by
    rw [cy, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hib hic,
      Equiv.swap_apply_of_ne_of_ne hib hia]
  obtain ⟨l, hl, hlσ⟩ := exists_Lv_of_A6s h1222 F hH hv hβ _ hσ
  obtain ⟨w, hw⟩ := F.β_surj (QuotientGroup.mk (pe i a))
  have hlN := hLV l.2
  have hw' : (l : G) * (w : G)⁻¹ * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hlN _).1 (V.inv_mem w.2)
  have huV : (w : G) * l * (w : G)⁻¹ * (l : G)⁻¹ ∈ V := by
    rw [show (w : G) * l * (w : G)⁻¹ * (l : G)⁻¹ = w * ((l : G) * (w : G)⁻¹ * (l : G)⁻¹) by
      group]
    exact V.mul_mem w.2 hw'
  have hact := S126T2.actsAs_psiP F hH l (w⁻¹) ⟨_, hw'⟩ (by simp)
  have hβu : F.β ⟨_, huV⟩ = QuotientGroup.mk (pe a b) := by
    have e : (⟨_, huV⟩ : ↥V) = w * ⟨_, hw'⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul]
      group)
    rw [e, map_mul, hact, hlσ, map_inv, hw, map_inv, S126L20a.dAct_pe, hσi, hσa,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    rw [show (pe i b)⁻¹ = pe b i by
      rw [inv_eq_of_mul_eq_one_right (by rw [S126L23c.pe_mul_pe, S126L23c.pe_self] :
        pe i b * pe b i = 1)], mul_comm, S126L23c.pe_mul_pe, S126L20a.pe_comm]
  refine ⟨_, ⟨huV, ?_, a, b, ?_, ?_, hab, hβu⟩, huV, hβu⟩
  · have := Subgroup.commutator_mem_commutator w.2 hl
    rwa [commutatorElement_def] at this
  · exact two_le_of_mem_six a ha
  · exact two_le_of_mem_six b hb

omit [Finite G] in
theorem mem_normalizer_biSup {ι : Type*} {s : Set ι} {H : ι → Subgroup G} {g : G}
    (h : ∀ u ∈ s, g ∈ Subgroup.normalizer (H u : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ u ∈ s, H u : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  refine iSup_congr fun u => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hu => (Subgroup.mem_normalizer_iff_map_conj_eq).1 (h u hu)

theorem exists_fix_two {c : Equiv.Perm (Fin 8)} (hc : c.IsThreeCycle) :
    ∃ a ∈ six, ∃ b ∈ six, a ≠ b ∧ c a = a ∧ c b = b := by
  classical
  have h3 := hc.card_support
  have h6 : six.card = 6 := rfl
  have h1 : 1 < (six \ c.support).card := by
    have := Finset.le_card_sdiff c.support six
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1
  rw [Finset.mem_sdiff] at ha hb
  exact ⟨a, ha.1, b, hb.1, hab, Equiv.Perm.notMem_support.1 ha.2,
    Equiv.Perm.notMem_support.1 hb.2⟩

end S126T2

theorem lemma12_6_10_of (h1222 : Stmt12_2_2) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
      (F : Frame126 T L V) (v : G) (Kv S : Subgroup G), Ctx1262 F v Kv S →
        (⨆ u ∈ Delta F v, Lv L u) = L := by
  intro G _ _ T L V _ F v Kv S hC
  classical
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  set K := ⨆ u ∈ Delta F v, Lv L u with hK
  have hKL : K ≤ L := iSup₂_le fun u _ => Lv_le_L L u
  have hA8 : alternatingGroup (Fin 8) ≤ (K.subgroupOf L).map (psiP F hH) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro c hc
    obtain ⟨a, ha, b, hb, hab, hca, hcb⟩ := exists_fix_two hc
    obtain ⟨u, huΔ, hu, hβu⟩ := exists_mem_Delta h1222 F hH hv hβ ha hb hab
    obtain ⟨y, hy, hyc⟩ := exists_Lu h1222 F hH hv hβ hu hab hβu hc.mem_alternatingGroup hca hcb
    exact ⟨y, (le_iSup₂_of_le u huΔ le_rfl : Lv L u ≤ K) hy, hyc⟩
  have hCN : L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    refine mem_normalizer_biSup fun u huΔ => ?_
    obtain ⟨hu, -⟩ := huΔ
    have hxu : x ∈ L ⊓ Gv u := ⟨hx.1, by
      show x ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx.2 u hu).symm⟩
    exact normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hxu)
  have hdec : ∀ x ∈ L, x ∈ K ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := hA8 (psiP_mem F hH ⟨x, hx⟩)
    have hk' : (k : G) ∈ K := hk
    have hq : S126L19a.psi F hH (k⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact Subtype.ext hkx
    have hqC := (S126L19a.psi_eq_one_iff F hH _).1 hq
    have e : x = (k : G) * ((k : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hk' ⟨L.mul_mem (L.inv_mem k.2) hx, hqC⟩
  have hLN : L ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    (sup_le Subgroup.le_normalizer hCN) (hdec x hx)
  have hnorm : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLN
  exact hH.hyp.faithful.2.1 K hKL hnorm fun x hx =>
    two_pow_mem_of_mem_sup (isPGroup_CL h1222 hH) hCN (hdec x hx)

end CFSG.Quasithin.H13
