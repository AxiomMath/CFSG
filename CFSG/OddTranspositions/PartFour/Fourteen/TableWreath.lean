module

public import CFSG.OddTranspositions.WreathQuotient
public import CFSG.Timmesfeld.Bridge.Asc72WAct
public import CFSG.OddTranspositions.ClassificationStatement
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge.Asc72

section Wreath

variable {L : Type} [Group L] {n : ℕ}

theorem wreath_mul_inl_mul_inv (w : (Fin n → L) ⋊[permAct (Fin n) L] Equiv.Perm (Fin n))
    (x : Fin n → L) :
    w * SemidirectProduct.inl x * w⁻¹ = SemidirectProduct.inl (WreathAct.act L n w x) := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right w]
  rw [WreathAct.act_apply, map_mul, map_mul, SemidirectProduct.inl_aut]
  simp only [map_inv]
  group

theorem eq_one_of_forall_commute_wreath_base [Nontrivial L]
    (hZ : ∀ z : L, (∀ y, z * y = y * z) → z = 1)
    {w : (Fin n → L) ⋊[permAct (Fin n) L] Equiv.Perm (Fin n)}
    (hw : ∀ x : Fin n → L, SemidirectProduct.inl x * w = w * SemidirectProduct.inl x) :
    w = 1 := by
  have h1 : WreathAct.act L n w = 1 := MulEquiv.ext fun x => by
    have h2 : SemidirectProduct.inl (WreathAct.act L n w x) =
        (SemidirectProduct.inl x :
          (Fin n → L) ⋊[permAct (Fin n) L] Equiv.Perm (Fin n)) := by
      rw [← wreath_mul_inl_mul_inv, ← hw x, mul_inv_cancel_right]
    exact SemidirectProduct.inl_injective h2
  exact WreathAct.act_injective hZ (h1.trans (map_one _).symm)

end Wreath

theorem l2Wreath_layer_le_base_of_two_le {f n : ℕ} (hf : 2 ≤ f) :
    layer (L2Wreath f n) ≤
      (⊤ : Subgroup (Fin n → CFSG.Theory.Comparator.PSL2Model f)).map
        (SemidirectProduct.inl (φ := permAct (Fin n) (CFSG.Theory.Comparator.PSL2Model f))) := by
  classical
  let L := CFSG.Theory.Comparator.PSL2Model f
  let φ : Equiv.Perm (Fin n) →* MulAut (Fin n → L) := permAct (Fin n) L
  let B : Subgroup (L2Wreath f n) := (⊤ : Subgroup (Fin n → L)).map SemidirectProduct.inl
  change layer (L2Wreath f n) ≤ B
  have : Finite L := inferInstance
  have : Finite (L2Wreath f n) := WreathAct.finite_wreath
  have hZ : ∀ z : L, (∀ y, z * y = y * z) → z = 1 := fun z hz => by
    have hzc : z ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun y => (hz y).symm
    rwa [PartThree.center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hzc
  have : Nontrivial L := by
    have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      rw [GaloisField.card 2 f (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact IsSimpleGroup.toNontrivial
  have hBker : B = (SemidirectProduct.rightHom (φ := φ)).ker := by
    show (⊤ : Subgroup (Fin n → L)).map SemidirectProduct.inl = _
    rw [Subgroup.map_top]
    exact SemidirectProduct.range_inl_eq_ker_rightHom
  have hBnormal : B.Normal := hBker.symm ▸ MonoidHom.normal_ker _
  change sSup {K : Subgroup (L2Wreath f n) | CFSG.IsComponent K} ≤ B
  refine sSup_le fun K hK => ?_
  rcases CFSG.LocalCores.component_normal_subgroup hK hBnormal with h | h
  · exact h
  · exfalso
    have hKC : K ≤ Subgroup.centralizer (B : Set (L2Wreath f n)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hK1 : ∀ k : K, k = 1 := fun k => Subtype.ext
      (eq_one_of_forall_commute_wreath_base hZ fun x =>
        Subgroup.mem_centralizer_iff.mp (hKC k.2) _ ⟨x, trivial, rfl⟩)
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [hK1 a', hK1 b']

theorem l2Wreath_not_isPGroup_quotient_layer_of_three_le {f n : ℕ} (hf : 2 ≤ f) (hn : 3 ≤ n) :
    ¬ IsPGroup 2 (L2Wreath f n ⧸ layer (L2Wreath f n)) := by
  classical
  let L := CFSG.Theory.Comparator.PSL2Model f
  let φ : Equiv.Perm (Fin n) →* MulAut (Fin n → L) := permAct (Fin n) L
  let G := (Fin n → L) ⋊[φ] Equiv.Perm (Fin n)
  let B : Subgroup G := (⊤ : Subgroup (Fin n → L)).map SemidirectProduct.inl
  have hEB : layer (L2Wreath f n) = B :=
    le_antisymm (l2Wreath_layer_le_base_of_two_le hf) (l2Wreath_base_le_layer hf)
  have hBker : B = (SemidirectProduct.rightHom (φ := φ)).ker := by
    show (⊤ : Subgroup (Fin n → L)).map SemidirectProduct.inl = _
    rw [Subgroup.map_top]
    exact SemidirectProduct.range_inl_eq_ker_rightHom
  have : B.Normal := hBker.symm ▸ MonoidHom.normal_ker _
  have hquot : (L2Wreath f n) ⧸ layer (L2Wreath f n) ≃* Equiv.Perm (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq (hEB.trans hBker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (φ := SemidirectProduct.rightHom) SemidirectProduct.rightHom_surjective)
  intro hP
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (hP.of_equiv hquot)
  have h3 : 3 ∣ Nat.card (Equiv.Perm (Fin n)) := by
    rw [Nat.card_perm, Nat.card_fin]
    exact Nat.dvd_factorial (by norm_num) hn
  rw [hk] at h3
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
    ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h3))
  omega

theorem not_isPGroup_quotient_layer_of_l2Wreath {G : Type} [Group G] [Finite G]
    {f n : ℕ} (hf : 2 ≤ f) (hn : 3 ≤ n) (e : G ≃* L2Wreath f n) :
    ¬ IsPGroup 2 (G ⧸ CFSG.layer G) := by
  intro hP
  have hmap : (CFSG.layer G).map e.toMonoidHom = CFSG.layer (L2Wreath f n) :=
    CFSG.WholeGroup.layer_map_mulEquiv e
  exact l2Wreath_not_isPGroup_quotient_layer_of_three_le hf hn
    (hP.of_equiv (QuotientGroup.congr _ _ e hmap))

end CFSG.OddTranspositions.PartFour
