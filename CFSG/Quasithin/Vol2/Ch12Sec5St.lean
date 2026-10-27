module

public import CFSG.Quasithin.Vol2.Ch12Sec5W
public import CFSG.Quasithin.Vol2.Ch12Sec5Ex

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125ZV S125Aut S125W Matrix

namespace S125St

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem autOn_T_le (F : Frame125 T L V) : autOn T V ≤ autOn L V := by
  intro a ha
  obtain ⟨t, ht, htT, rfl⟩ := mem_autOn_iff_exists.mp ha
  obtain ⟨u, -, hact⟩ := F.borel t htT
  have h : conjAct V ⟨t, ht⟩ = ((F.γ.symm u : ↥(autOn L V)) : MulAut ↥V) := by
    refine MulEquiv.ext fun v => F.e.injective ?_
    rw [F.wedge, MulEquiv.apply_symm_apply]
    exact hact v _ rfl
  rw [h]
  exact (F.γ.symm u).2

omit [Finite G] in
theorem autOn_sup_eq (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) : autOn (L ⊔ T) V = autOn L V := by
  rw [autOn_sup_eq_sup_autOn hLV hTV, sup_eq_left.2 (autOn_T_le F)]

theorem mem_normalizer_of_conj_le {W : Subgroup G} {g : G}
    (h : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : g ∈ Subgroup.normalizer (W : Set G) := by
  have hpow : ∀ n : ℕ, ∀ w ∈ W, g ^ n * w * (g ^ n)⁻¹ ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      have e : g ^ (n + 1) * w * (g ^ (n + 1))⁻¹ = g ^ n * (g * w * g⁻¹) * (g ^ n)⁻¹ := by
        rw [pow_succ, _root_.mul_inv_rev]
        group
      rw [e]
      exact ih _ (h w hw)
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h w, fun hw => ?_⟩
  have hN : g ^ (Nat.card G - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one']
  have hinv : g⁻¹ = g ^ (Nat.card G - 1) := (eq_inv_of_mul_eq_one_left hN).symm
  have := hpow (Nat.card G - 1) _ hw
  rw [← hinv, inv_inv] at this
  simpa [mul_assoc] using this

theorem mem_autOn_mi_iff {W : Subgroup G} (hWV : W ≤ V) (h : ↥(autOn L V)) :
    (h : MulAut ↥V) ∈ autOn (mi T L W) V ↔
      ∀ v : ↥V, (v : G) ∈ W → (((h : MulAut ↥V) v : ↥V) : G) ∈ W := by
  constructor
  · intro hm v hv
    obtain ⟨x, hx, ⟨-, hxW⟩, hxh⟩ := mem_autOn_iff_exists.mp hm
    rw [← hxh]
    exact (Subgroup.mem_normalizer_iff.1 hxW v).1 hv
  · intro hW
    obtain ⟨l, hl, hlL, hlh⟩ := mem_autOn_iff_exists.mp h.2
    have hlW : l ∈ Subgroup.normalizer (W : Set G) := by
      apply mem_normalizer_of_conj_le
      intro w hw
      have := hW ⟨w, hWV hw⟩ hw
      rw [← hlh] at this
      exact this
    exact mem_autOn_iff_exists.mpr ⟨l, hl, ⟨Subgroup.mem_sup_left hlL, hlW⟩, hlh⟩

omit [Finite G] in
theorem autOn_mi_le (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (W : Subgroup G) :
    autOn (mi T L W) V ≤ autOn L V := by
  rw [← autOn_sup_eq F hLV hTV]
  exact A4.autOn_mono inf_le_left

omit [Finite G] in
theorem mem_sub_iff (F : Frame125 T L V) (S : Finset (Fin 10)) (v : ↥V) :
    (v : G) ∈ F.sub S ↔ ∀ k ∉ S, Multiplicative.toAdd (F.e v) k = 0 := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hwv' : w = v := Subtype.ext hwv
    rw [← hwv']
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [Finite G] in
theorem sub_le (F : Frame125 T L V) (S : Finset (Fin 10)) : F.sub S ≤ V := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

omit [Finite G] in
theorem mapsTo_sub_iff (F : Frame125 T L V) (S : Finset (Fin 10)) (h : ↥(autOn L V)) :
    (∀ v : ↥V, (v : G) ∈ F.sub S → (((h : MulAut ↥V) v : ↥V) : G) ∈ F.sub S) ↔
      CoordFix S (JonesParshall.wedgeMat (F.γ h : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
  rw [coordFix_iff_mulVec]
  constructor
  · intro hmap x hx
    have h1 := hmap (F.e.symm (Multiplicative.ofAdd x)) ((mem_sub_iff F S _).2 (by
      rw [MulEquiv.apply_symm_apply]
      exact hx))
    rw [mem_sub_iff, F.wedge, MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_ofAdd,
      wedgeRep_apply] at h1
    exact h1
  · intro hfix v hv
    rw [mem_sub_iff] at hv ⊢
    rw [F.wedge, toAdd_ofAdd, wedgeRep_apply]
    exact hfix _ hv

theorem mem_autOn_mi_sub_iff (F : Frame125 T L V) (S : Finset (Fin 10)) (h : ↥(autOn L V)) :
    (h : MulAut ↥V) ∈ autOn (mi T L (F.sub S)) V ↔
      CoordFix S (JonesParshall.wedgeMat (F.γ h : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
  rw [mem_autOn_mi_iff (sub_le F S), mapsTo_sub_iff]

theorem isStab_of (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (S : Finset (Fin 10)) (k : ℕ)
    (hS : ∀ g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
      CoordFix S (JonesParshall.wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) ↔ StabGam k g) :
    F.IsStab (mi T L (F.sub S)) k :=
  ⟨autOn_mi_le F hLV hTV _, fun h => (mem_autOn_mi_sub_iff F S h).trans (hS _)⟩

theorem isStab_V1 (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) : F.IsStab (mi T L F.V1) 2 :=
  isStab_of F hLV hTV _ 2 coordFix_V1_iff

theorem isStab_V3 (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) : F.IsStab (mi T L F.V3) 3 :=
  isStab_of F hLV hTV _ 3 coordFix_V3_iff

theorem isStab_V4 (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) : F.IsStab (mi T L F.V4) 1 :=
  isStab_of F hLV hTV _ 1 coordFix_V4_iff

theorem isStab_V6 (F : Frame125 T L V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) : F.IsStab (mi T L F.V6) 4 :=
  isStab_of F hLV hTV _ 4 coordFix_V6_iff

end S125St

end CFSG.Quasithin.H13
