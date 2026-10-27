module

public import CFSG.Quasithin.Vol2.Ch10SecC8FF
public import CFSG.Quasithin.Vol2.Ch10SecCCard

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_omegaOneCenterOf' (R : Subgroup G) :
    IsElemAbelian 2 (omegaOneCenterOf R) :=
  ⟨⟨⟨fun x y => Subtype.ext (A4.mul_comm_of_mem_omegaOneCenterOf x.2 y.2)⟩⟩,
    fun _ hx => A4.sq_eq_one_of_mem_omegaOneCenterOf hx⟩

theorem fsuVM_le_omegaOneCenterOf (hyp : Hyp10 G T L I) :
    fsuVM T L I ≤ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  intro v hv
  exact Subgroup.subset_closure ⟨⟨fsuVM_le_Q hyp hv, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    (Subgroup.mem_centralizer_iff.mp hq.2 v hv).symm⟩, (SecA.isElemAbelian_fsuVM hyp).2 v hv⟩

omit [Finite G] in
theorem Q_le_centralizer_omegaOne (T V : Subgroup G) :
    T ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.centralizer (omegaOneCenterOf (T ⊓ Subgroup.centralizer (V : Set G)) : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (A4.omegaOneCenterOf_le_centerOf _ hz).2 q hq).symm

theorem fsuVM_comm (hyp : Hyp10 G T L I) {a b : G} (ha : a ∈ fsuVM T L I)
    (hb : b ∈ fsuVM T L I) : a * b = b * a :=
  congrArg Subtype.val ((SecA.isElemAbelian_fsuVM hyp).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem le_normalizer_of_le_fsuVM (hyp : Hyp10 G T L I) {X Y : Subgroup G}
    (hX : X ≤ fsuVM T L I) (hY : Y ≤ fsuVM T L I) : X ≤ Subgroup.normalizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [fsuVM_comm hyp (hX hx) (hY hy), mul_inv_cancel_right]
    exact hy
  · intro hy
    have hyV : y ∈ fsuVM T L I := by
      have h1 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [← h1]
      exact (fsuVM T L I).mul_mem ((fsuVM T L I).mul_mem ((fsuVM T L I).inv_mem (hX hx))
        (hY hy)) (hX hx)
    rw [fsuVM_comm hyp (hX hx) hyV, mul_inv_cancel_right] at hy
    exact hy

theorem card_decomp_bound (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {A : Subgroup G}
    (h1 : Nat.card ↥(fsuUL T L I) = 16)
    (h2 : Nat.card ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆) = 16) :
    256 * Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card ↥(fsuVM T L I) *
        Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) :
            Set G) : Subgroup G) : Set G)) *
        Nat.card ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊓ Subgroup.centralizer (A : Set G)) := by
  set V := fsuVM T L I with hVdef
  set V1 := fsuUL T L I with hV1def
  set V2 := ⁅fsuVM T L I, CFSG.conjugate L t⁆ with hV2def
  set A1 := A ⊓ Subgroup.centralizer (V2 : Set G) with hA1
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, -, -, -⟩ := hdec t ht htn
  have hV1V : V1 ≤ V := commutator_le_left_of_le_normalizer
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV2V : V2 ≤ V := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV2A1 : V2 ≤ Subgroup.centralizer (A1 : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm
  set C1 := V ⊓ Subgroup.centralizer (A1 : Set G) with hC1
  have hC1eq : C1 = (V1 ⊓ Subgroup.centralizer (A1 : Set G)) ⊔ V2 := by
    apply le_antisymm
    · rintro v ⟨hv, hvA⟩
      have hv' : v ∈ (↑(V1 ⊔ V2) : Set G) := by rw [← hVeq]; exact hv
      rw [Subgroup.coe_mul_of_left_le_normalizer_right V1 V2
        (le_normalizer_of_le_fsuVM hyp hV1V hV2V)] at hv'
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := hv'
      have hv1A : v1 ∈ Subgroup.centralizer (A1 : Set G) := by
        have : v1 = v1 * v2 * v2⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ hvA (Subgroup.inv_mem _ (hV2A1 hv2))
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hv1, hv1A⟩) (Subgroup.mem_sup_right hv2)
    · exact sup_le (inf_le_inf_right _ hV1V) (le_inf hV2V hV2A1)
  have e1 := card_sup_mul_card_inf (H := V1 ⊓ Subgroup.centralizer (A1 : Set G)) (K := V2)
    (le_normalizer_of_le_fsuVM hyp hV2V (inf_le_left.trans hV1V))
  have hinf1 : (V1 ⊓ Subgroup.centralizer (A1 : Set G)) ⊓ V2 = V1 ⊓ V2 := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · rintro v ⟨hv1, hv2⟩
      exact ⟨⟨hv1, hV2A1 hv2⟩, hv2⟩
  rw [← hC1eq, hinf1, h2] at e1
  have e2 := card_sup_mul_card_inf (H := V1) (K := V2) (le_normalizer_of_le_fsuVM hyp hV2V hV1V)
  rw [← hVeq, h1, h2] at e2
  set C := V ⊓ Subgroup.centralizer (A : Set G) with hC
  have hCC1 : V2 ⊔ C ≤ C1 := sup_le (le_inf hV2V hV2A1)
    (inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left))
  have e3 := card_sup_mul_card_inf (H := V2) (K := C)
    (le_normalizer_of_le_fsuVM hyp inf_le_left hV2V)
  have hinf2 : V2 ⊓ C = V2 ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hV2V) inf_le_right)
  rw [hinf2, h2] at e3
  have hle := Subgroup.card_le_of_le hCC1
  have e2' : Nat.card V * Nat.card ↥(V1 ⊓ V2) = 256 := e2
  have k1 : 16 * Nat.card C1 = Nat.card ↥(V1 ⊓ Subgroup.centralizer (A1 : Set G)) *
      Nat.card V := by
    have h256 : 16 * (16 * Nat.card C1) =
        16 * (Nat.card ↥(V1 ⊓ Subgroup.centralizer (A1 : Set G)) * Nat.card V) := by
      calc 16 * (16 * Nat.card C1) = Nat.card C1 * (Nat.card V * Nat.card ↥(V1 ⊓ V2)) := by
            rw [e2']; ring
        _ = Nat.card V * (Nat.card C1 * Nat.card ↥(V1 ⊓ V2)) := by ring
        _ = Nat.card V * (Nat.card ↥(V1 ⊓ Subgroup.centralizer (A1 : Set G)) * 16) := by
            rw [e1]
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h256
  calc 256 * Nat.card C = 16 * (Nat.card ↥(V2 ⊔ C) *
        Nat.card ↥(V2 ⊓ Subgroup.centralizer (A : Set G))) := by rw [e3]; ring
    _ ≤ 16 * (Nat.card C1 * Nat.card ↥(V2 ⊓ Subgroup.centralizer (A : Set G))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hle)
    _ = (16 * Nat.card C1) * Nat.card ↥(V2 ⊓ Subgroup.centralizer (A : Set G)) := by ring
    _ = _ := by rw [k1]; ring

omit [Finite G] in
theorem card_V2_eq {t : G} (ht : t ∈ T) :
    Nat.card ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆) = Nat.card ↥(fsuUL T L I) := by
  rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht), SecA.conjugate_eq_map]
  exact Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective

theorem le_of_offender_bounds {a a0 a1 r1 r2 x1 x2 c v x c' s : ℕ} (ha0 : 0 < a0) (hc : 0 < c)
    (hr2 : r2 * a1 = a) (hr1 : r1 * a0 = a1) (hb2 : r2 * x2 ≤ 16) (hb1 : r1 * x1 ≤ 16)
    (hb3 : 256 * c ≤ v * x1 * x2) (ha : x * a0 ≤ a * c') (hs : s * c = v * c') : x ≤ s := by
  subst hr2 hr1
  have h1 : 256 * (r2 * (r1 * a0) * c) ≤ 256 * (a0 * v) := by
    calc 256 * (r2 * (r1 * a0) * c) = r2 * r1 * a0 * (256 * c) := by ring
      _ ≤ r2 * r1 * a0 * (v * x1 * x2) := Nat.mul_le_mul_left _ hb3
      _ = (r2 * x2) * (r1 * x1) * (a0 * v) := by ring
      _ ≤ 16 * 16 * (a0 * v) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hb2 hb1)
      _ = 256 * (a0 * v) := by ring
  have h2 : r2 * (r1 * a0) * c ≤ a0 * v := Nat.le_of_mul_le_mul_left h1 (by norm_num)
  have h3 : a0 * (x * c) ≤ a0 * (s * c) := by
    calc a0 * (x * c) = (x * a0) * c := by ring
      _ ≤ (r2 * (r1 * a0) * c') * c := Nat.mul_le_mul_right _ ha
      _ = (r2 * (r1 * a0) * c) * c' := by ring
      _ ≤ (a0 * v) * c' := Nat.mul_le_mul_right _ h2
      _ = a0 * (s * c) := by rw [hs]; ring
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_left h3 ha0) hc

theorem le_sup_inf_centralizer (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I)
    (hne : cV1 T L I ≠ ⊥) {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ≤
      fsuVM T L I ⊔ (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (A : Set G)) := by
  have hXel := isElemAbelian_omegaOneCenterOf' (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G))
  have hXT : omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ≤ T :=
    (A4.omegaOneCenterOf_le _).trans inf_le_left
  have hVX := fsuVM_le_omegaOneCenterOf hyp
  have hQX := Q_le_centralizer_omegaOne T (fsuVM T L I)
  by_cases hAV : A ≤ Subgroup.centralizer (fsuVM T L I : Set G)
  ·
    intro x hx
    refine Subgroup.mem_sup_right ⟨hx, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hQX ⟨hA.1 ha, hAV ha⟩) x hx).symm
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hAT1 : A ≤ T1 T L := (B6.le_thompsonJ hA).trans (h1012 G T L I hyp).2.1
  obtain ⟨hc, hnat⟩ := h3.2
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 := (card_fsuUL h37 h38 hyp h1011 h484 D hnat hne).1
  have h16' : Nat.card ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆) = 16 := by
    rw [card_V2_eq ht, h16]
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, -, -, -⟩ := hdec t ht htn
  have ha := card_mul_le_of_isMaxElemAbelian hA hXel hXT
  have hCAX : A ⊓ Subgroup.centralizer
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) : Set G) =
      A ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le hVX)
    · intro a ha
      refine ⟨ha.1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      exact Subgroup.mem_centralizer_iff.mp (hQX ⟨hA.1 ha.1, ha.2⟩) x hx
  rw [hCAX] at ha
  have hb2 := offender_bound_V2 h37 h38 hyp h1011 h484 h3 hne ht htn hAT1 hA.2.1
  have hr2 := Subgroup.relIndex_mul_card
    (Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G)) A
  rw [inf_comm] at hr2
  have hA1el : IsElemAbelian 2 (A ⊓ Subgroup.centralizer
      ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G)) :=
    ⟨⟨⟨fun x y => Subtype.ext (congrArg (Subtype.val : ↥A → G) (hA.2.1.1.is_comm.comm
      (⟨(x : G), x.2.1⟩ : ↥A) ⟨(y : G), y.2.1⟩))⟩⟩, fun x hx => hA.2.1.2 x hx.1⟩
  have hb1 := offender_bound_fsuUL h37 h38 hyp h1011 h484 h3 hne (inf_le_left.trans hAT1) hA1el
  have hr1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (fsuUL T L I : Set G))
    (A ⊓ Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G))
  have hCV : Subgroup.centralizer (fsuUL T L I : Set G) ⊓ (A ⊓ Subgroup.centralizer
      ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G)) =
      A ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
    conv_rhs => rw [hVeq]
    ext a
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, mem_centralizer_sup h1 h3⟩
    · rintro ⟨h2, h4⟩
      exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) h4, h2,
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) h4⟩
  rw [hCV] at hr1
  have hb3 := card_decomp_bound hyp h1011 ht htn (A := A) h16 h16'
  have hXV : omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ≤
      Subgroup.centralizer (fsuVM T L I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hQX (fsuVM_le_Q hyp hv)) x hx).symm
  have hs := card_sup_mul_card_inf (H := fsuVM T L I)
    (K := omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
      Subgroup.centralizer (A : Set G))
    ((inf_le_left.trans hXV).trans (Subgroup.centralizer_le_normalizer _))
  have hVY : fsuVM T L I ⊓ (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
      Subgroup.centralizer (A : Set G)) = fsuVM T L I ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hVX) inf_le_right)
  rw [hVY] at hs
  have hle := le_of_offender_bounds Nat.card_pos Nat.card_pos hr2 hr1 hb2 hb1 hb3 ha hs
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hVX inf_le_left) hle).ge

end CFSG.Quasithin.Vol2.Ch10.SecC
