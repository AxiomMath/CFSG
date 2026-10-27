module

public import CFSG.Quasithin.Vol2.Ch10SecENat
public import CFSG.Quasithin.Vol2.Ch10SecEL0
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixBaum

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

theorem two_pow_mul_ne_120 (m : ℕ) : 2 ^ m * (4 ^ m - 1) ≠ 120 := by
  rcases Nat.lt_or_ge m 4 with h | h
  · interval_cases m <;> decide
  · have h1 : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 4 ^ 4 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) h
    have h3 : 16 * 255 ≤ 2 ^ m * (4 ^ m - 1) := Nat.mul_le_mul h1 (by omega)
    omega

variable {G : Type} [Group G]

theorem val_mem_commutator_of_mem_commV {V : Subgroup G} (hV : IsElemAbelian 2 V) {X : Subgroup G}
    {w : IntMod V hV} (hw : w ∈ commV (autI hV X)) : w.val ∈ ⁅V, X⁆ := by
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨φ, hφ, v, rfl⟩ := hy
    obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).mp hφ
    rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
    have h : (g : G) * v.val * (g : G)⁻¹ * (v.val)⁻¹ = ⁅v.val, (g : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator v.val_mem hgX)
  | one => exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    rw [IntMod.val_mul]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [IntMod.val_inv]
    exact Subgroup.inv_mem _ ha

theorem convI_fix_iff {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (g : Subgroup.normalizer (V : Set G)) (w : IntMod V hV) :
    convI hV g w = w ↔ (g : G) * w.val * (g : G)⁻¹ = w.val := by
  rw [← convI_apply_val hV g w]
  exact ⟨fun h => by rw [h], fun h => IntMod.val_injective h⟩

variable [Finite G] {T L I : Subgroup G}

theorem false_of_fix_case1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n)
    {k : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hk : k ∈ autI (SecA.isElemAbelian_fsuVM hyp) L) (hkk : k * k ≠ 1)
    {w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)}
    (hw : w ∈ commV (autI (SecA.isElemAbelian_fsuVM hyp) L)) (hkw : k w = w)
    {d : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hd : d ∈ autI (SecA.isElemAbelian_fsuVM hyp) L) (hdw : d w ≠ w) : False := by
  obtain ⟨x, hxL, rfl⟩ := (mem_autI _).mp hk
  obtain ⟨y, hyL, rfl⟩ := (mem_autI _).mp hd
  have hwU : w.val ∈ fsuUL T L I := val_mem_commutator_of_mem_commV _ hw
  have hxw : (x : G) * w.val * (x : G)⁻¹ = w.val := (convI_fix_iff _ x w).mp hkw
  have hyw : (y : G) * w.val * (y : G)⁻¹ ≠ w.val := fun h => hdw ((convI_fix_iff _ y w).mpr h)
  obtain ⟨hn, -, hcU, hBN⟩ := h1
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) Subgroup.le_normalizer
  set x' : Subgroup.normalizer (fsuUL T L I : Set G) := ⟨x, hLU hxL⟩
  have hx'A : conjAct (fsuUL T L I) x' ∈ autOn L (fsuUL T L I) :=
    SecA.mem_autOn_iff'.mpr ⟨x', hxL, rfl⟩
  set u : ↥(fsuUL T L I) := ⟨w.val, hwU⟩
  have hxu : conjAct (fsuUL T L I) x' u = u :=
    Subtype.ext (by rw [SecA.coe_conjAct_apply']; exact hxw)
  have huC : u ∉ Ch10.cV1 T L I := by
    intro hu
    rw [Subgroup.mem_subgroupOf] at hu
    apply hyw
    have h2 := Subgroup.mem_centralizer_iff.mp hu y (SecA.le_fsuL0 T L hyL)
    calc (y : G) * w.val * (y : G)⁻¹ = w.val * y * (y : G)⁻¹ := by rw [← h2]
      _ = w.val := by group
  have hsq := mul_self_eq_one_of_binaryNaturalSL (by omega) hBN hx'A huC hxu
  have hxU : ∀ v ∈ fsuUL T L I, (x : G) * x * v = v * (x * x) := by
    intro v hv
    have h2 := congrArg (fun φ : MulAut ↥(fsuUL T L I) => ((φ ⟨v, hv⟩ : ↥(fsuUL T L I)) : G)) hsq
    simp only [MulAut.mul_apply, MulAut.one_apply, SecA.coe_conjAct_apply'] at h2
    calc (x : G) * x * v = ((x : G) * ((x : G) * v * (x : G)⁻¹) * (x : G)⁻¹) * (x * x) := by
          group
      _ = v * (x * x) := by rw [h2]
  have hV2 := SecA.commutator_conjugate_le_centralizer h37 h38 hyp ht htn
  have hxx : ((x * x : Subgroup.normalizer (fsuVM T L I : Set G)) : G) ∈
      Subgroup.centralizer (fsuVM T L I : Set G) := by
    have hle : ⁅fsuVM T L I, L⁆ ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤
        Subgroup.centralizer ({(x : G) * x} : Set G) := by
      refine sup_le (fun v hv => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hxU v hv).symm
      · have h2 := Subgroup.mem_centralizer_iff.mp (hV2 hv) x hxL
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc v * ((x : G) * x) = (v * x) * x := by group
          _ = x * (x * v) := by rw [← h2, mul_assoc, h2]
          _ = (x : G) * x * v := by group
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hv' : v ∈ ⁅fsuVM T L I, L⁆ ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
      (SecA.fsuVM_eq_sup h37 h38 hyp ht htn) ▸ hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv')
  apply hkk
  rw [← map_mul]
  exact (convI_eq_one_iff _ _).mpr hxx

theorem isL2Natural_of_case1
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n)
    {I' : Finset (Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))))}
    (hKJ : twoResidual (fsuL0 T L ⊔ T) ≤ thompsonJ (fsuL0 T L ⊔ T))
    (hcard : I'.card = 1 ∨ I'.card = 2)
    (hJeq : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = ⨆ K ∈ I', K)
    (hcomm : ∀ K ∈ I', ∀ K' ∈ I', K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hind : ∀ K ∈ I', K ⊓ ⨆ K' ∈ I', ⨆ (_ : K' ≠ K), K' = ⊥)
    (htrans : ∀ K ∈ I', ∀ K' ∈ I',
      ∃ s ∈ autI (SecA.isElemAbelian_fsuVM hyp) T, B1.conjAut s K = K')
    (htype : ∀ K ∈ I', (∃ m, E2.IsL2Natural K (fixV (autI (SecA.isElemAbelian_fsuVM hyp)
      (twoResidual (fsuL0 T L ⊔ T)))) m) ∨ E2.IsA5Module K) :
    ∀ K ∈ I', ∃ m, E2.IsL2Natural K (fixV (autI (SecA.isElemAbelian_fsuVM hyp)
      (twoResidual (fsuL0 T L ⊔ T)))) m := by
  intro K₀ hK₀
  rcases htype K₀ hK₀ with h | h5
  · exact h
  exfalso
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hall : ∀ K ∈ I', E2.IsA5Module K := by
    intro K hK
    rcases htype K hK with ⟨m, hm⟩ | h5'
    · obtain ⟨s, -, hs⟩ := htrans K₀ hK₀ K hK
      have hc := SecA.card_of_isL2Natural hm
      rw [← hs, SecA.card_conjAut, SecA.card_of_isA5Module h5] at hc
      exact absurd hc.symm (two_pow_mul_ne_120 m)
    · exact h5'
  obtain ⟨-, a, b, hab⟩ := SecA.isSimpleGroup_autOn h37 h38 h322 hyp
  obtain ⟨-, hBn⟩ := isSimpleGroup_autI_conjugate h37 h38 h322 hyp ht
  have hAn : ∃ x ∈ autI (SecA.isElemAbelian_fsuVM hyp) L,
      ∃ y ∈ autI (SecA.isElemAbelian_fsuVM hyp) L, x * y ≠ y * x :=
    ⟨a.1, a.2, b.1, b.2, fun h => hab (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h))⟩
  rcases ident_L0T h37 h38 h322 hyp ht htn hKJ hcard hJeq hcomm hind htrans with
    ⟨K, hK, -, -, hO⟩ | ⟨K₁, hK₁, K₂, -, -, -, -, hO₁, -, -, -⟩
  · exact false_of_isSimpleGroup (isSimpleGroup_oTwoUpper_of_isA5Module (hall K hK)) hAn hBn
      (autI_commute h37 h322 hyp ht htn) hO.ge hO.le
  · obtain ⟨k, hk, hkk, w, hw, hkw, d, hd, hdw⟩ := exists_fix_of_isA5Module (hall K₁ hK₁)
    rw [hO₁] at hk hw hd
    exact false_of_fix_case1 h37 h38 hyp ht htn h1 hk hkk hw hkw hd hdw

end CFSG.Quasithin.Vol2.Ch10.SecE
