module

public import CFSG.Quasithin.Vol2.Ch10SecD12A
public import CFSG.Quasithin.Vol2.Ch10SecD12B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace L3

open CFSG.Quasithin.L3

theorem P0_not_comm : ∃ x ∈ P0, ∃ y ∈ P0, x * y ≠ y * x :=
  ⟨⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩, ⟨by decide, by decide, by decide⟩, by decide⟩

theorem card_le_four {P : Subgroup Γ} (hP : IsPGroup 2 P)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Nat.card P ≤ 4 := by
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).mp hP
  have hdvd : 2 ^ e ∣ 168 := by
    rw [← he, ← card_Γ]
    exact Subgroup.card_subgroup_dvd_card P
  have he3 : e ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 hlt).trans hdvd
    norm_num at this
  rcases (by omega : e ≤ 2 ∨ e = 3) with h2 | rfl
  · rw [he]
    calc 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 4 := by norm_num
  · exfalso
    obtain ⟨g, hg⟩ := exists_conj_eq_P0 (by rw [he]; norm_num : Nat.card P = 8)
    obtain ⟨x, hx, y, hy, hxy⟩ := P0_not_comm
    have hx' : (MulAut.conj g) x ∈ P := hg ▸ Subgroup.mem_map_of_mem _ hx
    have hy' : (MulAut.conj g) y ∈ P := hg ▸ Subgroup.mem_map_of_mem _ hy
    apply hxy
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul]
    exact hc _ hx' _ hy'

end L3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem exists_fix_not_mem {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {y : MulAut W} (hy : y ^ 2 = 1) {Z : Subgroup W} (hZ : Nat.card Z * Nat.card Z < Nat.card W) :
    ∃ w : W, y w = w ∧ w ∉ Z := by
  have h1 := card_commV_mul_card_fixV hW y
  have h2 := Subgroup.card_le_of_le (commV_zpowers_le_fixV_b4 hW hy)
  by_contra hcon
  push Not at hcon
  have hle : fixV (Subgroup.zpowers y) ≤ Z := fun w hw =>
    hcon w ((mem_fixV_zpowers_iff).mp hw)
  have h3 := Subgroup.card_le_of_le hle
  have : Nat.card W ≤ Nat.card Z * Nat.card Z := by
    calc Nat.card W = Nat.card (commV (Subgroup.zpowers y)) *
          Nat.card (fixV (Subgroup.zpowers y)) := h1.symm
      _ ≤ Nat.card (fixV (Subgroup.zpowers y)) * Nat.card (fixV (Subgroup.zpowers y)) :=
          Nat.mul_le_mul_right _ h2
      _ ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul h3 h3
  omega

theorem mem_normalizer_L (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {g : G}
    (hg : g ∈ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  rcases SecA.conjugate_eq_or h37 h38 h ht htn hg.1 with hL | hL
  · exact SecA.conjugate_eq_self_iff.mp hL
  · exfalso
    apply V1_ne_V2 h37 h38 h ht htn
    rw [← hL, ← SecA.conjugate_commutator_fsuVM hg.1, SecA.conjugate_eq_self_iff.mpr hg.2]

omit [Finite G] in
theorem conj_mem_autOn_iff {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgV : g ∈ Subgroup.normalizer (fsuUL T L I : Set G)) (σ : MulAut ↥(fsuUL T L I)) :
    σ ∈ autOn L (fsuUL T L I) ↔
      conjAct (fsuUL T L I) ⟨g, hgV⟩ * σ * (conjAct (fsuUL T L I) ⟨g, hgV⟩)⁻¹ ∈
        autOn L (fsuUL T L I) := by
  have hnorm : ∀ (g' : G) (hgL' : g' ∈ Subgroup.normalizer (L : Set G))
      (hgV' : g' ∈ Subgroup.normalizer (fsuUL T L I : Set G)),
      ∀ σ ∈ autOn L (fsuUL T L I), conjAct (fsuUL T L I) ⟨g', hgV'⟩ * σ *
        (conjAct (fsuUL T L I) ⟨g', hgV'⟩)⁻¹ ∈ autOn L (fsuUL T L I) := by
    rintro g' hgL' hgV' _ ⟨⟨l, hlN⟩, hl, rfl⟩
    refine ⟨⟨g', hgV'⟩ * ⟨l, hlN⟩ * (⟨g', hgV'⟩)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hgL' l).mp (Subgroup.mem_subgroupOf.mp hl)
    · rw [map_mul, map_mul, map_inv]
  have hgV' : g⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    (Subgroup.normalizer _).inv_mem hgV
  have hxinv : conjAct (fsuUL T L I) ⟨g⁻¹, hgV'⟩ = (conjAct (fsuUL T L I) ⟨g, hgV⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  refine ⟨hnorm g hgL hgV σ, fun hσ => ?_⟩
  have h1 := hnorm g⁻¹ ((Subgroup.normalizer _).inv_mem hgL) hgV' _ hσ
  rw [hxinv, inv_inv] at h1
  have e1 : (conjAct (fsuUL T L I) ⟨g, hgV⟩)⁻¹ * (conjAct (fsuUL T L I) ⟨g, hgV⟩ * σ *
      (conjAct (fsuUL T L I) ⟨g, hgV⟩)⁻¹) * conjAct (fsuUL T L I) ⟨g, hgV⟩ = σ := by group
  rwa [e1] at h1

theorem mem_autOn_of_mem (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) {g : G}
    (hg : g ∈ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) :
    conjAct (fsuUL T L I) ⟨g, hg.2⟩ ∈ autOn L (fsuUL T L I) := by
  obtain ⟨-, hcomm, hnat⟩ := h3
  rw [← fixV_autOn_V1 h37 h38 h] at hnat
  obtain ⟨D⟩ := hnat.toL3Coord
  exact mem_of_normalizes D (SecC.commV_autOn_fsuUL h)
    (conj_mem_autOn_iff (mem_normalizer_L h37 h38 h hg) hg.2)

theorem rank_le_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (E : Subgroup G)
    (hE : E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) (hEa : IsElemAbelian 2 E) :
    mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) ≤ 2 := by
  have hEN : E ≤ Subgroup.normalizer (fsuUL T L I : Set G) := hE.trans inf_le_right
  have hsub : autOn E (fsuUL T L I) ≤ autOn L (fsuUL T L I) := by
    rintro _ ⟨⟨x, hxN⟩, hxE, rfl⟩
    exact mem_autOn_of_mem h37 h38 h h3 (hE (Subgroup.mem_subgroupOf.mp hxE))
  obtain ⟨-, hcomm, hnat⟩ := h3
  rw [← fixV_autOn_V1 h37 h38 h] at hnat
  obtain ⟨D⟩ := hnat.toL3Coord
  set P := (autOn E (fsuUL T L I)).comap D.rho with hP
  have hrange : autOn E (fsuUL T L I) ≤ D.rho.range := fun σ hσ => by
    obtain ⟨γ, hγ⟩ := D.exists_rho (hsub hσ)
    exact ⟨γ, hγ⟩
  have hPc : Nat.card P = Nat.card (autOn E (fsuUL T L I)) := by
    rw [← Subgroup.map_comap_eq_self hrange, Subgroup.card_map_of_injective D.rho_injective]
  have hcardE : Nat.card (autOn E (fsuUL T L I)) =
      2 ^ mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) := by
    rw [card_autOn_eq_relIndex hEN]
    exact relIndex_eq_two_pow (B2F.isPGroup_of_isElemAbelian hEa) _
  have hP2 : IsPGroup 2 P := by
    rw [IsPGroup.iff_card]
    exact ⟨_, hPc.trans hcardE⟩
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    apply D.rho_injective
    rw [map_mul, map_mul]
    obtain ⟨⟨x, hxN⟩, hxE, hx⟩ := (Subgroup.mem_comap.mp ha)
    obtain ⟨⟨y, hyN⟩, hyE, hy⟩ := (Subgroup.mem_comap.mp hb)
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact B2F.isElemAbelian_comm hEa (Subgroup.mem_subgroupOf.mp hxE)
      (Subgroup.mem_subgroupOf.mp hyE)
  have h4 := L3.card_le_four hP2 hPcomm
  rw [hPc, hcardE] at h4
  by_contra hlt
  push Not at hlt
  have : 2 ^ 3 ≤ 2 ^ mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) :=
    Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem card_cV1_le_two (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) :
    Nat.card ↥(cV1 T L I) ≤ 2 := by
  obtain ⟨-, hcomm, hnat⟩ := h3
  have hfix := fixV_autOn_V1 h37 h38 h
  have hc := (hI16 (↥(fsuUL T L I)) (SecC.sq_eq_one_fsuUL h) (autOn L (fsuUL T L I)) 1).1
    (SecC.commV_autOn_fsuUL h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, by rw [hfix]; exact hnat⟩))))))
  rw [hfix, pow_one] at hc
  exact hc

omit [Finite G] in
theorem card_V1_eq_eight_mul (h3 : Case10_1_1Three T L I) :
    Nat.card ↥(fsuUL T L I) =
      8 * Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
  obtain ⟨-, hcomm, hnat⟩ := h3
  obtain ⟨D⟩ := hnat.toL3Coord
  have hU := D.card_U
  rw [Subgroup.card_top] at hU
  rw [hU, cV1, card_subgroupOf_eq, inf_comm]

theorem data_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) :
    Data10212 T L I 3 2 2 := by
  have h8 := card_V1_eq_eight_mul h3
  have hcV : Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) ≤ 2 := by
    have := card_cV1_le_two h37 h38 hI16 h h3
    rwa [cV1, card_subgroupOf_eq, inf_comm] at this
  have hm : mQuot (fsuUL T L I) (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) = 3 := by
    have h1 := card_eq_two_pow_mul (V := fsuUL T L I)
      ((SecA.isPGroup_fsuVM h).to_le V1_le_V) (inf_le_left :
        fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≤ fsuUL T L I)
    have hpos : 0 < Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) :=
      Nat.card_pos
    rw [h8] at h1
    have h2 : 2 ^ mQuot (fsuUL T L I)
        (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) = 2 ^ 3 :=
      (Nat.eq_of_mul_eq_mul_right hpos h1).symm
    exact Nat.pow_right_injective (le_refl 2) h2
  have hr := rank_le_three h37 h38 h h3
  exact ⟨hm.ge, hr, a_le_of_rank_le hr, fix_of_card h (hm.ge) (by omega), by norm_num⟩

end CFSG.Quasithin.Vol2.Ch10.SecD
