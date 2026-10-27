module

public import CFSG.Walter.W67.Lemma21
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.PSL2ProjectiveLine
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonBorelMatrices

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.Glauberman.Dickson

namespace Borel5

section PSL2

variable (F : Type) [Field F]

@[expose] noncomputable def torusHom : Fˣ →* PSL(2, F) :=
  (psl2QuotientMap F).comp (splitTorusSLHom F)

@[expose] noncomputable def torus : Subgroup PSL(2, F) := (torusHom F).range

abbrev unip : Subgroup PSL(2, F) := psl2UpperUnipotentSubgroup F

variable {F}

theorem splitTorusSLHom_mem_sl2Borel (a : Fˣ) : splitTorusSLHom F a ∈ sl2Borel F := by
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
  simp

theorem torus_le_borel : torus F ≤ psl2Borel F := by
  rintro _ ⟨a, rfl⟩
  rw [psl2Borel_eq_map]
  exact ⟨splitTorusSLHom F a, splitTorusSLHom_mem_sl2Borel a, rfl⟩

theorem torusHom_conj (a : Fˣ) (x : F) :
    torusHom F a * psl2QuotientMap F (sl2UpperUnipotent x) * (torusHom F a)⁻¹ =
      psl2QuotientMap F (sl2UpperUnipotent ((a : F) ^ 2 * x)) := by
  have h := sl2Borel_conj_upperUnipotent (splitTorusSLHom_mem_sl2Borel a) x
  have h00 : (splitTorusSLHom F a).val 0 0 = (a : F) := by simp
  rw [h00] at h
  change psl2QuotientMap F (splitTorusSLHom F a) * psl2QuotientMap F (sl2UpperUnipotent x) *
    (psl2QuotientMap F (splitTorusSLHom F a))⁻¹ = _
  rw [← map_mul, ← map_inv, ← map_mul, h]

theorem torusHom_conj_coordinate (a : Fˣ) (x : F) :
    (psl2UpperUnipotentEquiv F (Multiplicative.ofAdd ((a : F) ^ 2 * x)) :
        PSL(2, F)) =
      torusHom F a * (psl2UpperUnipotentEquiv F (Multiplicative.ofAdd x) :
        PSL(2, F)) * (torusHom F a)⁻¹ := by
  rw [psl2UpperUnipotentEquiv_apply, psl2UpperUnipotentEquiv_apply]
  simpa [psl2UpperUnipotentHom, sl2UpperUnipotentHom] using
    (torusHom_conj (F := F) a x).symm

theorem exists_sylow_scalar_coordinate
    {T : Sylow 2 (PSL(2, F))} {g : PSL(2, F)} (a : Fˣ)
    (hT : (T : Subgroup (PSL(2, F))) =
      (psl2UpperUnipotentSubgroup F).map (MulAut.conj g).toMonoidHom) :
    ∃ eT : Multiplicative F ≃* T,
      ∀ x : F,
        (eT (Multiplicative.ofAdd ((a : F) ^ 2 * x)) : PSL(2, F)) =
          MulAut.conj g (torusHom F a) *
            (eT (Multiplicative.ofAdd x) : PSL(2, F)) *
            (MulAut.conj g (torusHom F a))⁻¹ := by
  classical
  let eU : Multiplicative F ≃* psl2UpperUnipotentSubgroup F :=
    psl2UpperUnipotentEquiv F
  let cg : PSL(2, F) →* PSL(2, F) := (MulAut.conj g).toMonoidHom
  let eUT : psl2UpperUnipotentSubgroup F ≃*
      (psl2UpperUnipotentSubgroup F).map cg :=
    Subgroup.equivMapOfInjective (psl2UpperUnipotentSubgroup F) cg
      (MulAut.conj g).injective
  let eUTT : psl2UpperUnipotentSubgroup F ≃* T :=
    eUT.trans (MulEquiv.subgroupCongr hT.symm)
  let eT : Multiplicative F ≃* T := eU.trans eUTT
  have heUT_coe : ∀ u : psl2UpperUnipotentSubgroup F,
      ((eUT u : (psl2UpperUnipotentSubgroup F).map cg) : PSL(2, F)) =
        cg (u : PSL(2, F)) := by
    intro u
    exact Subgroup.coe_equivMapOfInjective_apply
      (psl2UpperUnipotentSubgroup F) cg (MulAut.conj g).injective u
  have heUTT_coe : ∀ u : psl2UpperUnipotentSubgroup F,
      ((eUTT u : T) : PSL(2, F)) = cg (u : PSL(2, F)) := by
    intro u
    change ((MulEquiv.subgroupCongr hT.symm (eUT u) : T) : PSL(2, F)) =
      cg (u : PSL(2, F))
    rw [MulEquiv.subgroupCongr_apply]
    exact heUT_coe u
  have heT_coe : ∀ x : Multiplicative F,
      ((eT x : T) : PSL(2, F)) = cg (eU x : PSL(2, F)) := by
    intro x
    change ((eUTT (eU x) : T) : PSL(2, F)) = cg (eU x : PSL(2, F))
    exact heUTT_coe (eU x)
  refine ⟨eT, ?_⟩
  intro x
  calc
    ((eT (Multiplicative.ofAdd ((a : F) ^ 2 * x)) : T) : PSL(2, F))
        = cg (eU (Multiplicative.ofAdd ((a : F) ^ 2 * x)) : PSL(2, F)) :=
          heT_coe _
    _ = cg ((torusHom F a) * eU (Multiplicative.ofAdd x) *
          (torusHom F a)⁻¹ : PSL(2, F)) := by
            simpa only [eU] using congrArg cg (torusHom_conj_coordinate (F := F) a x)
    _ = cg (torusHom F a) * cg (eU (Multiplicative.ofAdd x) : PSL(2, F)) *
          cg (torusHom F a)⁻¹ := by simp [cg]
    _ = MulAut.conj g (torusHom F a) *
          (eT (Multiplicative.ofAdd x) : PSL(2, F)) *
          (MulAut.conj g (torusHom F a))⁻¹ := by
        rw [← heT_coe]
        simp [cg, mul_assoc]

theorem torus_le_normalizer_unip : torus F ≤ Subgroup.normalizer (unip F : Set PSL(2, F)) :=
  torus_le_borel.trans (psl2UpperUnipotent_normalizer_eq_borel F).ge

theorem borel_le_unip_sup_torus : psl2Borel F ≤ unip F ⊔ torus F := by
  intro g hg
  rw [psl2Borel_eq_map] at hg
  obtain ⟨A, hA, rfl⟩ := hg
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).mp hA
  obtain ⟨a, ha⟩ := eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero A h10
  have hU : unipotentSLAddChar F (A 0 1 * A 0 0) = sl2UpperUnipotent (A 0 1 * A 0 0) := rfl
  rw [ha, map_mul, hU]
  exact mul_mem (Subgroup.mem_sup_left ((mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩))
    (Subgroup.mem_sup_right ⟨a, rfl⟩)

theorem normalizer_unip : Subgroup.normalizer (unip F : Set PSL(2, F)) = unip F ⊔ torus F := by
  rw [psl2UpperUnipotent_normalizer_eq_borel]
  exact le_antisymm borel_le_unip_sup_torus
    (sup_le psl2UpperUnipotent_le_borel torus_le_borel)

theorem eq_zero_of_unip_eq_one {y : F} (hy : psl2QuotientMap F (sl2UpperUnipotent y) = 1) :
    y = 0 := by
  have hc : sl2UpperUnipotent y ∈ Subgroup.center SL(2, F) := (QuotientGroup.eq_one_iff _).mp hy
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have := congrFun (congrFun hr 0) 1
  simpa [sl2UpperUnipotent, Matrix.scalar_apply] using this.symm

theorem unip_inf_centralizer_torus {t : PSL(2, F)} (ht : t ∈ torus F)
    (ht1 : t ≠ 1) : unip F ⊓ Subgroup.centralizer ({t} : Set PSL(2, F)) = ⊥ := by
  obtain ⟨a, rfl⟩ := ht
  rw [eq_bot_iff]
  intro u hu'
  obtain ⟨hu, hut⟩ := Subgroup.mem_inf.mp hu'
  obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
  rw [Subgroup.mem_centralizer_singleton_iff] at hut
  have h1 : torusHom F a * psl2QuotientMap F (sl2UpperUnipotent x) * (torusHom F a)⁻¹ =
      psl2QuotientMap F (sl2UpperUnipotent x) := by
    rw [← hut, mul_inv_cancel_right]
  rw [torusHom_conj] at h1
  have h2 : psl2QuotientMap F (sl2UpperUnipotent (((a : F) ^ 2 - 1) * x)) = 1 := by
    rw [show ((a : F) ^ 2 - 1) * x = (a : F) ^ 2 * x + -x by ring, ← sl2UpperUnipotent_mul,
      map_mul, h1, ← sl2UpperUnipotent_inv, map_inv, mul_inv_cancel]
  have h3 := eq_zero_of_unip_eq_one h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exfalso
    apply ht1
    have ha2 : (a : F) ^ 2 = 1 := sub_eq_zero.mp h4
    have hainv : (a : F) = (a : F)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_two, ha2])
    change ((splitTorusSLHom F a : SL(2, F)) : PSL(2, F)) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Matrix.SpecialLinearGroup.mem_center_iff.mpr
      ⟨(a : F), by simpa using ha2, splitTorusSLHom_eq_scalar_of_val_eq_inv a hainv⟩
  · rw [h4, sl2UpperUnipotent_zero, map_one, Subgroup.mem_bot]

theorem torusHom_eq_one_iff (a : Fˣ) : torusHom F a = 1 ↔ (a : F) ^ 2 = 1 := by
  constructor
  · intro h
    have hc : splitTorusSLHom F a ∈ Subgroup.center SL(2, F) := (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have h00 := congrFun (congrFun hr 0) 0
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, splitTorusSLHom_coe] at h00
    have h00' : r = (a : F) := by simpa using h00
    rw [← h00']
    simpa using hr2
  · intro ha2
    have hainv : (a : F) = (a : F)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_two, ha2])
    change ((splitTorusSLHom F a : SL(2, F)) : PSL(2, F)) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Matrix.SpecialLinearGroup.mem_center_iff.mpr
      ⟨(a : F), by simpa using ha2, splitTorusSLHom_eq_scalar_of_val_eq_inv a hainv⟩

theorem card_ker_torusHom (hF : ringChar F ≠ 2) : Nat.card (torusHom F).ker = 2 := by
  have hset : ((torusHom F).ker : Set Fˣ) = {1, -1} := by
    ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff,
      torusHom_eq_one_iff, pow_two, mul_self_eq_one_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Units.ext h)
      · exact Or.inr (Units.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hne : (1 : Fˣ) ≠ -1 := by
    intro h
    exact Ring.neg_one_ne_one_of_char_ne_two hF (congrArg Units.val h).symm
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_pair hne]

theorem card_torus [Finite F] (hF : ringChar F ≠ 2) : 2 * Nat.card (torus F) = Nat.card F - 1 := by
  rw [← Nat.card_units, ← Subgroup.card_ker_mul_card_range (torusHom F), card_ker_torusHom hF]
  rfl

theorem isCyclic_torus [Finite F] : IsCyclic (torus F) :=
  isCyclic_of_surjective (torusHom F).rangeRestrict (torusHom F).rangeRestrict_surjective

theorem fieldAut_quotientMap (σ : F ≃+* F) (A : SL(2, F)) :
    psl2FieldAut F σ (psl2QuotientMap F A) =
      psl2QuotientMap F (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  rw [psl2FieldAut_apply]
  exact psl2RingEquiv_mk σ A

theorem fieldAut_mem_unip (σ : F ≃+* F) {y : PSL(2, F)} (hy : y ∈ unip F) :
    psl2FieldAut F σ y ∈ unip F := by
  obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff y).mp hy
  rw [fieldAut_quotientMap]
  refine (mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨σ x, ?_⟩
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent]

theorem fieldAut_mem_torus (σ : F ≃+* F) {y : PSL(2, F)} (hy : y ∈ torus F) :
    psl2FieldAut F σ y ∈ torus F := by
  obtain ⟨a, rfl⟩ := hy
  change psl2FieldAut F σ (psl2QuotientMap F (splitTorusSLHom F a)) ∈ torus F
  rw [fieldAut_quotientMap]
  refine ⟨Units.map σ.toRingHom.toMonoidHom a, ?_⟩
  change psl2QuotientMap F _ = _
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

end PSL2

end Borel5

variable {G : Type} [Group G] [Finite G]

open Borel5 in
theorem Frame5.nonempty
    (s : Std G) : Nonempty (Frame5 s) := by
  obtain ⟨e', P₀, hT⟩ := s.fr.exists_coords
  set F := GaloisField s.p s.f
  set ι := psl2Emb e'
  have hι : Function.Injective ι := PSL2Sub.emb_injective e'
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F s.p]
    exact s.p_ne_two
  have hcardF : Nat.card F = s.q := GaloisField.card s.p s.f s.f_pos.ne'
  have hE : ∀ g ∈ s.fr.E, ∃ σ : F ≃+* F, ∀ y, g * ι y * g⁻¹ = ι (psl2FieldAut F σ y) :=
    fun g hg => s.fr.conj_eq_fieldAut hT hg
  have hnorm : ∀ H : Subgroup PSL(2, F), (∀ σ : F ≃+* F, ∀ y ∈ H, psl2FieldAut F σ y ∈ H) →
      s.fr.E ≤ Subgroup.normalizer ((H.map ι : Subgroup G) : Set G) := by
    intro H hH g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨σ, hσ⟩ := hE g hg
      exact ⟨_, hH σ y hy, (hσ y).symm⟩
    · rintro ⟨y, hy, hyz⟩
      obtain ⟨σ, hσ⟩ := hE g⁻¹ (s.fr.E.inv_mem hg)
      have hz : z = g⁻¹ * ι y * g⁻¹⁻¹ := by
        change ι y = g * z * g⁻¹ at hyz
        rw [hyz]
        group
      rw [hz, hσ y]
      exact ⟨_, hH σ y hy, rfl⟩
  have hmapN : ∀ H : Subgroup PSL(2, F), H ≤ Subgroup.normalizer (unip F : Set PSL(2, F)) →
      H.map ι ≤ Subgroup.normalizer (((unip F).map ι : Subgroup G) : Set G) := by
    intro H hH
    have h1 := JT.map_normalizer_of_injective ι hι (unip F)
    exact (Subgroup.map_mono hH).trans (h1.le.trans inf_le_right)
  have hEN : s.fr.E ≤ Subgroup.normalizer (((unip F).map ι : Subgroup G) : Set G) :=
    hnorm _ fun σ _ hy => fieldAut_mem_unip σ hy
  refine ⟨{
    B := (torus F).map ι
    B_le := PSL2Sub.map_le e' _
    B_cyclic := ?_
    card_B := ?_
    E_le_normalizer_B := hnorm _ fun σ _ hy => fieldAut_mem_torus σ hy
    P₁ := (unip F).map ι
    P₁_le := PSL2Sub.map_le e' _
    card_P₁ := ?_
    B_le_normalizer := sup_le (hmapN _ torus_le_normalizer_unip) hEN
    fixedPointFree := ?_
    normalizer_eq := ?_ }⟩
  · have := isCyclic_torus (F := F)
    exact isCyclic_of_surjective ((torus F).equivMapOfInjective ι hι)
      ((torus F).equivMapOfInjective ι hι).surjective
  · rw [Subgroup.card_map_of_injective hι, card_torus hF2, hcardF]
  · rw [Subgroup.card_map_of_injective hι, psl2UpperUnipotentSubgroup_card, hcardF]
  · rintro _ ⟨t, ht, rfl⟩ ht1
    have ht1' : t ≠ 1 := by
      rintro rfl
      exact ht1 (map_one ι)
    have h0 := unip_inf_centralizer_torus ht ht1'
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨u, hu, rfl⟩, hzc⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hzc
    have hut : u ∈ unip F ⊓ Subgroup.centralizer ({t} : Set PSL(2, F)) :=
      ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr (hι hzc)⟩
    rw [h0, Subgroup.mem_bot] at hut
    rw [hut, map_one, Subgroup.mem_bot]
  · apply le_antisymm
    · rintro x ⟨hxN, hxKE⟩
      obtain ⟨k, hk, e, he, rfl⟩ :=
        (mem_sup_iff_of_le_normalizer s.fr.E_le_normalizer_K).mp hxKE
      have hkN : k ∈ Subgroup.normalizer (((unip F).map ι : Subgroup G) : Set G) := by
        have := mul_mem hxN (hEN (s.fr.E.inv_mem he))
        rwa [mul_inv_cancel_right] at this
      obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq e' hk
      have hyN : ι y ∈ (Subgroup.normalizer (unip F : Set PSL(2, F))).map ι := by
        rw [JT.map_normalizer_of_injective ι hι]
        exact ⟨⟨y, rfl⟩, hkN⟩
      rw [Subgroup.mem_map_iff_mem hι, normalizer_unip] at hyN
      have hk' : ι y ∈ (unip F).map ι ⊔ (torus F).map ι := by
        rw [← Subgroup.map_sup]
        exact Subgroup.mem_map_of_mem ι hyN
      exact mul_mem (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right he)
    · refine le_inf (sup_le (sup_le Subgroup.le_normalizer
        (hmapN _ torus_le_normalizer_unip)) hEN) (sup_le (sup_le ?_ ?_) le_sup_right)
      · exact (PSL2Sub.map_le e' _).trans le_sup_left
      · exact (PSL2Sub.map_le e' _).trans le_sup_left

end CFSG.Walter.W67
