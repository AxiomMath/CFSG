module

public import CFSG.Quasithin.Vol2.Ch10SecD12C

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mQuot_le_one_of_card_le {A B : Subgroup G} (hA : IsPGroup 2 A) (hBA : B ≤ A)
    (hc : Nat.card A ≤ 2 * Nat.card B) : mQuot A B ≤ 1 := by
  have h := card_eq_two_pow_mul hA hBA
  have hB : 0 < Nat.card B := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h4 : 2 ^ 2 ≤ 2 ^ mQuot A B := Nat.pow_le_pow_right (by norm_num) hlt
  have : 4 * Nat.card B ≤ Nat.card A := by rw [h]; exact Nat.mul_le_mul_right _ h4
  omega

omit [Finite G] in
theorem le_V_of_eq {t : G} (ht : t ∈ T) {X : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) : X ≤ fsuVM T L I := by
  rcases hX with rfl | rfl
  · exact V1_le_V
  · exact commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))

omit [Finite G] in
theorem mQuot_V12 {t : G} (ht : t ∈ T) {X : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆) :
    mQuot X (X ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) =
      mQuot (fsuUL T L I) (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
  rcases hX with rfl | rfl
  · rfl
  · have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
    have hC : conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) t =
        Subgroup.centralizer (fsuL0 T L : Set G) := by
      rw [conjSubgroup_centralizer, conjSubgroup_eq_iff_mem_normalizer.2 htM]
    rw [V2_eq_conjugate ht]
    show mQuot (conjSubgroup (fsuUL T L I) t)
      (conjSubgroup (fsuUL T L I) t ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) = _
    conv_lhs => rw [← hC]
    rw [← conjSubgroup_inf, mQuot_conjSubgroup]

theorem acts_and_le {m a0 r0 : ℕ} (hD : Data10212 T L I m a0 r0)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3)
    (h1029 : Stmt10_2_9) (h10210 : Stmt10_2_10) (h : Hyp10 G T L I)
    (hgf : 0 < E3.wParam T (fsuVM T L I) ∨ GenFaithful T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∉ fsuM T L)
    (hnc : ⁅fsuVM T L I, conjSubgroup (fsuVM T L I) g⁆ ≠ ⊥) {X : Subgroup G}
    (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hAC : ¬ conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.centralizer (fsuUL T L I : Set G))
    (hk : mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) + 2 ≤ m) :
    conjSubgroup X g ⊓ fsuM T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) ∧
      (∀ b ∈ conjSubgroup X g ⊓ fsuM T L,
        b ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g →
        fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.centralizer ((conjSubgroup X g ⊓ fsuM T L : Subgroup G) : Set G)) ∧
      m ≤ mQuot (conjSubgroup X g) (conjSubgroup X g ⊓ fsuM T L) + a0 := by
  set W := conjSubgroup X g with hW
  set A := W ⊓ fsuM T L with hA
  set k := mQuot W A with hk_def
  have hV := SecA.isElemAbelian_fsuVM h
  have hXV := le_V_of_eq ht hX
  have hWV : W ≤ conjSubgroup (fsuVM T L I) g := conjSubgroup_mono_left g hXV
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_mono hWV (isElemAbelian_conjSubgroup hV g)
  have hW2 : IsPGroup 2 W := B2F.isPGroup_of_isElemAbelian hWel
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono inf_le_left hWel
  have hAM : A ≤ fsuM T L := inf_le_right
  have hmW : m ≤ mQuot W (W ⊓ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g) := by
    rw [hW, ← conjSubgroup_inf, mQuot_conjSubgroup, mQuot_V12 ht hX]
    exact hD.rank_quot
  have hex : ∀ B : Subgroup G, B ≤ W → mQuot W B < m →
      ∃ b ∈ B, b ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g := by
    intro B hBW hBm
    by_contra hcon
    push Not at hcon
    have hle : B ≤ W ⊓ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g :=
      le_inf hBW hcon
    have := mQuot_mono (V := W) hle
    omega
  have hkey : ∀ b ∈ A ⊓ Subgroup.normalizer (fsuUL T L I : Set G),
      b ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g →
      fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.centralizer (A : Set G) := fun b hb hbL =>
    inf_centralizer_le_of_mem h37 h38 h1013 h1029 h10210 h hgf ht htn hg hnc hX hb.1.1 hb.1.2
      hb.2 hbL
  have hAB : mQuot A (A ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) ≤ 1 :=
    mQuot_le_one_of_card_le (hW2.to_le inf_le_left) inf_le_left
      (card_le_two_mul_card_inf_normalizer_V1 h37 h38 h hAM)
  have hWB : mQuot W (A ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) ≤ k + 1 := by
    rw [mQuot_add (inf_le_left : A ⊓ Subgroup.normalizer (fsuUL T L I : Set G) ≤ A)
      (inf_le_left : A ≤ W)]
    omega
  obtain ⟨b0, hb0, hb0L⟩ := hex (A ⊓ Subgroup.normalizer (fsuUL T L I : Set G))
    (inf_le_left.trans inf_le_left) (by omega)
  have hb02 : b0 ^ 2 = 1 := hWel.2 b0 hb0.1.1
  obtain ⟨v, hv, hvL, hvb⟩ := hD.fix b0 hb0.2 hb02
  have hvA : v ∈ Subgroup.centralizer (A : Set G) :=
    hkey b0 hb0 hb0L ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr hvb.symm⟩
  have hAN : A ≤ Subgroup.normalizer (fsuUL T L I : Set G) := by
    intro a ha
    rcases mem_normalizer_V12_or h37 h38 h ht htn (hAM ha) with h1 | h1
    · exact h1.1
    · exfalso
      apply hvL
      have hav : a * v * a⁻¹ = v := by
        have := (Subgroup.mem_centralizer_iff.mp hvA) a ha
        rw [this]
        group
      have hv2 : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
        rw [← h1.1, SecA.mem_conjugate_iff, hav]
        exact hv
      exact V1_inf_V2_le h37 h38 h ht htn ⟨hv, hv2⟩
  have hkeyA : ∀ b ∈ A, b ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g →
      fsuUL T L I ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (A : Set G) :=
    fun b hb hbL => hkey b ⟨hb, hAN hb⟩ hbL
  refine ⟨hAN, hkeyA, ?_⟩
  have hq := hD.a_le A (le_inf hAM hAN) hAel hAC (m - k) fun B hBA hBk => by
    have hWB' : mQuot W B < m := by
      rw [mQuot_add hBA (inf_le_left : A ≤ W)]
      omega
    obtain ⟨b, hb, hbL⟩ := hex B (hBA.trans inf_le_left) hWB'
    refine le_antisymm (fun x hx => ⟨hx.1, ?_⟩) (inf_le_inf_left _ (Subgroup.centralizer_le hBA))
    refine hkeyA b (hBA hb) hbL ⟨hx.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hx.2) b hb).symm
  omega

end CFSG.Quasithin.Vol2.Ch10.SecD
