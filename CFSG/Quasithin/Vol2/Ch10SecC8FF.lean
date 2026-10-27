module

public import CFSG.Quasithin.Background.AutOnElemAb
public import CFSG.Quasithin.Background.AutOnFixV
public import CFSG.Quasithin.Vol2.Ch10SecC8Inner

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem card_autOn_eq {A W : Subgroup G} (hA : A ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card (autOn A W) = (Subgroup.centralizer (W : Set G)).relIndex A :=
  CFSG.Quasithin.AutOn.card_autOn_eq_relIndex_centralizer hA

theorem card_fixV_autOn_eq {A W : Subgroup G} [IsMulCommutative ↥W]
    (hA : A ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card (fixV (autOn A W)) = Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) :=
  CFSG.Quasithin.AutOn.card_fixV_autOn_eq hA

theorem isElemAbelian2_autOn {A W : Subgroup G} [IsMulCommutative ↥W] (hA : IsElemAbelian 2 A) :
    IsElemAbelian2 (autOn A W) :=
  CFSG.Quasithin.AutOn.isElemAbelian2_autOn hA

theorem autOn_le_of_acts {A L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (h : ∀ a ∈ A, ∃ x ∈ L, ∀ w ∈ W, a * w * a⁻¹ = x * w * x⁻¹) : autOn A W ≤ autOn L W := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hxL, hx⟩ := h y hy
  refine ⟨⟨x, hLW hxL⟩, hxL, ?_⟩
  ext w
  change x * (w : G) * x⁻¹ = y * w * (y : G)⁻¹
  exact (hx w w.2).symm

variable [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem T1_le_normalizer_fsuUL (T L I : Subgroup G) :
    T1 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  SecA.le_normalizer_commutator
    (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)) inf_le_right

theorem offender_bound_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥)
    {A : Subgroup G} (hAT : A ≤ T1 T L) (hA : IsElemAbelian 2 A) :
    (Subgroup.centralizer (fsuUL T L I : Set G)).relIndex A *
      Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (A : Set G)) ≤ 16 := by
  obtain ⟨hc, hnat⟩ := h3.2
  obtain ⟨D⟩ := hnat.toL3Coord
  have H := offHyp_fsuUL h37 h38 hyp h1011 h484 D hnat hne
  have h16 := (card_fsuUL h37 h38 hyp h1011 h484 D hnat hne).1
  have hAN : A ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    hAT.trans (T1_le_normalizer_fsuUL T L I)
  have hle : autOn A (fsuUL T L I) ≤ autOn L (fsuUL T L I) :=
    autOn_le_of_acts (le_normalizer_fsuUL T L I) fun a ha => by
      obtain ⟨x₀, hx₀, -, hv⟩ := acts_as_inner_fsuUL hyp h1011 h3 (hAT ha)
      exact ⟨x₀, hx₀, hv⟩
  have hel := isElemAbelian2_autOn (W := fsuUL T L I) hA
  rw [← card_autOn_eq hAN, ← card_fixV_autOn_eq hAN]
  by_cases hbot : autOn A (fsuUL T L I) = ⊥
  · rw [hbot, B1.card_bot_mul_card_fixV, h16]
  · obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    have hb1' : (b : MulAut ↥(fsuUL T L I)) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have h1 := H.E4 _ hle hel
    have h2 := H.card_fixV_le hle hel b.2 hb1'
    calc Nat.card ↥(autOn A (fsuUL T L I)) * Nat.card ↥(fixV (autOn A (fsuUL T L I))) ≤ 4 * 4 :=
          Nat.mul_le_mul h1 h2
      _ = 16 := by norm_num

theorem T1_le_normalizer_conjugate (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    T1 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  intro s hs
  rw [← SecA.conjugate_eq_self_iff]
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn
      ((fsuM T L).mul_mem (SecA.le_fsuM T L ht) (SecA.le_fsuM T L hs.1)) with h | h
  · exfalso
    apply htn
    rw [← SecA.conjugate_eq_self_iff]
    have h1 := congrArg (fun X => CFSG.conjugate X s⁻¹) h
    simp only [SecA.conjugate_conjugate, mul_inv_cancel_right] at h1
    rw [h1]
    exact SecA.conjugate_eq_self_iff.mpr (Subgroup.inv_mem _ hs.2)
  · rw [SecA.conjugate_conjugate]
    exact h

theorem map_conj_le_T1 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {A : Subgroup G} (hA : A ≤ T1 T L) :
    A.map (MulAut.conj t).toMonoidHom ≤ T1 T L := by
  rintro _ ⟨a, ha, rfl⟩
  have haT := (hA ha).1
  refine ⟨T.mul_mem (T.mul_mem ht haT) (T.inv_mem ht), ?_⟩
  change t * a * t⁻¹ ∈ Subgroup.normalizer (L : Set G)
  rw [← SecA.conjugate_eq_self_iff]
  have h1 : CFSG.conjugate L (t * a * t⁻¹) =
      CFSG.conjugate (CFSG.conjugate (CFSG.conjugate L t) a) t⁻¹ := by
    rw [SecA.conjugate_conjugate, SecA.conjugate_conjugate, mul_assoc]
  rw [h1, SecA.conjugate_eq_self_iff.mpr (T1_le_normalizer_conjugate h37 h38 hyp ht htn (hA ha)),
    SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one]

omit [Finite G] in
theorem map_conj_V2 {t : G} (ht : t ∈ T) :
    (⁅fsuVM T L I, CFSG.conjugate L t⁆).map (MulAut.conj t).toMonoidHom = fsuUL T L I := by
  rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
  have h : (CFSG.conjugate ⁅fsuVM T L I, L⁆ t).map (MulAut.conj t).toMonoidHom =
      CFSG.conjugate (CFSG.conjugate ⁅fsuVM T L I, L⁆ t) t⁻¹ := by
    rw [SecA.conjugate_eq_map _ t⁻¹, inv_inv]
  rw [h, SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one]

theorem offender_bound_V2 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {A : Subgroup G} (hAT : A ≤ T1 T L) (hA : IsElemAbelian 2 A) :
    (Subgroup.centralizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G)).relIndex A *
      Nat.card ↥(⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊓ Subgroup.centralizer (A : Set G)) ≤ 16 := by
  set e := MulAut.conj t
  have hb := offender_bound_fsuUL h37 h38 hyp h1011 h484 h3 hne
    (map_conj_le_T1 h37 h38 hyp ht htn hAT) ((isElemAbelian_map_mulEquiv e).mpr hA)
  rw [← map_conj_V2 (I := I) ht, ← centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ e.injective, ← centralizer_map_mulEquiv,
    ← Subgroup.map_inf_eq _ _ _ e.injective, card_map_mulEquiv] at hb
  exact hb

end CFSG.Quasithin.Vol2.Ch10.SecC
