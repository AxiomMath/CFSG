module

public import CFSG.Quasithin.Vol2.Ch10SecB3EndSix
public import CFSG.Quasithin.Vol2.Ch10SecB3Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem thompsonJ_le_centralizer_fsuVM_of_not_FF (hyp : Hyp10 G T L I)
    (hnot : ∀ _ : IsMulCommutative ↥(fsuVM T L I),
      ¬ IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I))) :
    thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have hel : IsElemAbelian 2 (fsuVM T L I) := SecA.isElemAbelian_fsuVM hyp
  have := hel.1
  have hVH : fsuVM T L I ≤ fsuL0 T L ⊔ T := (SecA.fsuVM_le_T hyp).trans le_sup_right
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (SecA.fsuL0_le_normalizer_fsuVM T L I) (SecA.le_normalizer_fsuVM T L I)
  have hTH : IsSylowTwoOf T (fsuL0 T L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  refine iSup₂_le fun A hA => ?_
  by_contra hAV
  have hoff : IsFFStarOffender (autI hel (fsuL0 T L ⊔ T)) (autI hel A) :=
    offenderImages_isFFStarOffender hel hVH hHN
      ⟨A, ⟨isMaxElemAbelian_of_isSylowTwoOf hTH hA, hAV⟩, rfl⟩
  exact hnot hel.1 (((B1_4_5 (fun v => IntMod.sq_eq_one v) _).out 2 1).1
    (⟨_, hoff⟩ : {B | IsFFStarOffender (autI hel (fsuL0 T L ⊔ T)) B}.Nonempty))

theorem thompsonJ_le_centralizer_six (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4)
    (hyp : Hyp10 G T L I) (h6 : Case10_1_1Six T L I) :
    thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨⟨e⟩, hab, hds, h5⟩ := h6
  have he : Nonempty (↥(autOn L (fsuVM T L I)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    ⟨(SecA.autOnEquivQuot h37 h38 h322 hyp).trans e⟩
  exact thompsonJ_le_centralizer_fsuVM_of_not_FF hyp fun _ =>
    SecA.not_isFFModule_of_case_six h37 h38 h322 h154 hyp he hds h5

theorem commutator_center_eq_bot_six
    (h1022 : Stmt10_2_2) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4)
    (hyp : Hyp10 G T L I) (h6 : Case10_1_1Six T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hZH
  obtain ⟨⟨hL0, -⟩, -⟩ := h1022 G T L I hyp H hH hZH
  have hJ := thompsonJ_le_centralizer_six h37 h38 h322 h154 hyp h6
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hc : ⁅fsuL0 T L, thompsonJ T⁆ ≤ pCoreOf 2 (fsuL0 T L) := by
    rw [Subgroup.commutator_le]
    intro l hl j hj
    refine SecA.fsuL0_inf_centralizer_le h37 h38 hyp ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 : j * l⁻¹ * j⁻¹ ∈ fsuL0 T L :=
        (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L (hJT hj)) l⁻¹).mp
          (Subgroup.inv_mem _ hl)
      have := Subgroup.mul_mem _ hl h1
      simpa [mul_assoc] using this
    · rw [commutatorElement_def]
      have hlN : l ∈ Subgroup.normalizer
          ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
        SecA.le_normalizer_centralizer (SecA.fsuL0_le_normalizer_fsuVM T L I) hl
      have h1 := (Subgroup.mem_normalizer_iff.mp hlN j).mp (hJ hj)
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hJ hj))
  have hLp : IsPGroup 2 L := by
    have hle : L ≤ pCoreOf 2 (fsuL0 T L) := (SecA.le_fsuL0 T L).trans (hL0.le.trans hc)
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L)).to_le hle
  obtain ⟨⟨e⟩, -⟩ := h6
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hLp
  have hd : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ Nat.card L := Subgroup.card_quotient_dvd_card _
  rw [Nat.card_congr e.toEquiv, Vol2Native.A312L.Seven.card_slThree, hk] at hd
  have h3 : 3 ∣ 2 ^ k := (by norm_num : 3 ∣ 168).trans hd
  exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)

omit [Finite G] in
theorem fsuVM_inf_centralizer_le_centralizer (hVT : fsuVM T L I ≤ T)
    (hV2 : ∀ v ∈ fsuVM T L I, v ^ 2 = 1) {H : Subgroup G}
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) {A : Subgroup G} (hAH : A ≤ H) :
    fsuVM T L I ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (A : Set G) := by
  intro c hc
  have hcZ : c ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hVT hc.1, hc.2⟩, hV2 c hc.1⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH) hcZ
  exact Subgroup.mem_centralizer_iff.mp h a (hAH ha)

theorem not_fsuVM_inf_centralizer_le (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) :
    ¬ fsuVM T L I ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (L : Set G) := by
  intro hle
  obtain ⟨c, hcV, hc1, hcT⟩ := exists_ne_one_fsuVM_centralizer_T hyp
  have hel := SecA.isElemAbelian_fsuVM hyp
  have hc2 : c ^ 2 = 1 := hel.2 c hcV
  have hcp : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1, pow_one])
  obtain ⟨M', hM'⟩ := exists_inM_centralizer hcp hc1
  have hcL := hle ⟨hcV, hcT⟩
  have hLC : L ⊔ T ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (Subgroup.mem_centralizer_iff.mp hcL l hl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (Subgroup.mem_centralizer_iff.mp hcT t ht).symm
  have hM : M' = fsuM T L := (isUniqueM_L0T h331 hyp).2 M'
    ⟨hM'.1, (sup_le (fsuL0_le_sup T L) le_sup_right).trans (hLC.trans hM'.2)⟩
  have hcZ : c ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨SecA.fsuVM_le_T hyp hcV, hcT⟩, hc2⟩
  have hcH := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH) hcZ
  apply hH.2.1
  intro h hh
  rw [← hM]
  apply hM'.2
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (Subgroup.mem_centralizer_iff.mp hcH h hh).symm

theorem trivOnV_of_six
    (hF : FactCommGL4) (h1022 : Stmt10_2_2) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) (h6 : Case10_1_1Six T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : TrivOnV T L I H := by
  intro p hp hp2 hpL A hA hAH hAp
  have hZH := commutator_center_eq_bot_six h1022 h37 h38 h322 h154 hyp h6 hH
  have hel := SecA.isElemAbelian_fsuVM hyp
  exact commutator_fsuVM_eq_bot_six hF h37 h38 hyp h6 hp hp2 hpL hA hAp
    (fsuVM_inf_centralizer_le_centralizer (SecA.fsuVM_le_T hyp) hel.2 hZH hAH)
    (not_fsuVM_inf_centralizer_le h331 hyp hH hZH)

end CFSG.Quasithin.Vol2.Ch10.SecB
