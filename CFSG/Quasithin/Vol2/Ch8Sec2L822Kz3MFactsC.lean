module

public import CFSG.Quasithin.Background.HCocCode22
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Facts
public import CFSG.Quasithin.Background.HMathieuFacts22Base
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Code22
  CFSG.Monster.B.TwoA

private theorem mem_centSub_zpowers_kzc {V : Type} [CommGroup V] {g : MulAut V} {z : V} :
    g ∈ centSub (Subgroup.zpowers z) ↔ g z = z := by
  refine ⟨fun h => h z (Subgroup.mem_zpowers z), fun h u hu => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  rw [map_zpow, h]

private theorem kzFix_kz3_eq_centSub {V : Type} [CommGroup V] (z : V) :
    kzFix_kz3 z = centSub (Subgroup.zpowers z) :=
  Subgroup.ext fun g => mem_centSub_zpowers_kzc.symm

private theorem natCard_congr_kzc {G : Type*} [Group G] {H K : Subgroup G} (h : H = K) :
    Nat.card ↥H = Nat.card ↥K := by
  subst h
  rfl

private def kzcHexMasks : List ℕ := 1 :: orbTree.map Prod.fst

private def kzcMogBInvArr : Array ℕ :=
  #[0, 1, 18, 10, 15, 7, 3, 23, 21, 22, 16, 11, 12, 5, 20, 2, 6, 9, 4, 17, 14, 8, 19, 13]

private theorem kzcHexMasks_length : kzcHexMasks.length = 77 := by
  decide +kernel

private theorem hasArr_mogA_inv_kzc : HasArr mogA⁻¹ mogAArr := by
  unfold HasArr
  decide +kernel

private theorem hasArr_mogB_inv_kzc : HasArr mogB⁻¹ kzcMogBInvArr := by
  unfold HasArr
  decide +kernel

private theorem kzcHexMasks_closed :
    ∀ m ∈ kzcHexMasks, actC10 mogAArr m ∈ kzcHexMasks ∧ actC10 mogBArr m ∈ kzcHexMasks ∧
      actC10 kzcMogBInvArr m ∈ kzcHexMasks := by
  decide +kernel

private def kzcHexStab : Subgroup (MulAut W10) where
  carrier := {g | (∀ m ∈ kzcHexMasks, ∃ m' ∈ kzcHexMasks, g (toW 10 m) = toW 10 m') ∧
    (∀ m ∈ kzcHexMasks, ∃ m' ∈ kzcHexMasks, g⁻¹ (toW 10 m) = toW 10 m')}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · obtain ⟨m', hm', hhm⟩ := hh1 m hm
      obtain ⟨m'', hm'', hgm⟩ := hg1 m' hm'
      exact ⟨m'', hm'', by rw [MulAut.mul_apply, hhm, hgm]⟩
    · obtain ⟨m', hm', hgm⟩ := hg2 m hm
      obtain ⟨m'', hm'', hhm⟩ := hh2 m' hm'
      exact ⟨m'', hm'', by rw [mul_inv_rev, MulAut.mul_apply, hgm, hhm]⟩
  one_mem' := by
    refine ⟨fun m hm => ⟨m, hm, ?_⟩, fun m hm => ⟨m, hm, ?_⟩⟩
    · rw [MulAut.one_apply]
    · rw [inv_one, MulAut.one_apply]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    exact ⟨hg2, by simpa only [inv_inv] using hg1⟩

private theorem cRhoA_mem_kzcHexStab : cRhoA ∈ kzcHexStab := by
  refine ⟨fun m hm => ⟨actC10 mogAArr m, (kzcHexMasks_closed m hm).1, ?_⟩,
    fun m hm => ⟨actC10 mogAArr m, (kzcHexMasks_closed m hm).1, ?_⟩⟩
  · exact rhoC10_toW mog22 mog22_le_mog22plus ⟨mogA, mogA_mem22⟩ hasArr_mogA m
  · have h := rhoC10_toW mog22 mog22_le_mog22plus (⟨mogA, mogA_mem22⟩ : ↥mog22)⁻¹
      hasArr_mogA_inv_kzc m
    rwa [map_inv] at h

private theorem cRhoB_mem_kzcHexStab : cRhoB ∈ kzcHexStab := by
  refine ⟨fun m hm => ⟨actC10 mogBArr m, (kzcHexMasks_closed m hm).2.1, ?_⟩,
    fun m hm => ⟨actC10 kzcMogBInvArr m, (kzcHexMasks_closed m hm).2.2, ?_⟩⟩
  · exact rhoC10_toW mog22 mog22_le_mog22plus ⟨mogB, mogB_mem22⟩ hasArr_mogB m
  · have h := rhoC10_toW mog22 mog22_le_mog22plus (⟨mogB, mogB_mem22⟩ : ↥mog22)⁻¹
      hasArr_mogB_inv_kzc m
    rwa [map_inv] at h

private theorem apply_z0_mem_kzcHexMasks
    {g : MulAut W10} (hg : g ∈ imgC mog22) :
    ∃ m ∈ kzcHexMasks, g z0 = toW 10 m := by
  have hle : Subgroup.closure ({cRhoA, cRhoB} : Set (MulAut W10)) ≤ kzcHexStab := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact cRhoA_mem_kzcHexStab
    · exact cRhoB_mem_kzcHexStab
  exact (hle (imgC_le_closure hg)).1 1 List.mem_cons_self

private theorem ncard_orbit_le_kzc :
    (MulAction.orbit ↥(imgC mog22) z0).ncard ≤ 77 := by
  classical
  have hsub : MulAction.orbit ↥(imgC mog22) z0 ⊆
      ((kzcHexMasks.map (toW 10)).toFinset : Set W10) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨m, hm, hgm⟩ := apply_z0_mem_kzcHexMasks g.2
    simp only [List.coe_toFinset, List.mem_map, Set.mem_ofPred_eq]
    exact ⟨m, hm, hgm.symm⟩
  calc (MulAction.orbit ↥(imgC mog22) z0).ncard
      ≤ ((kzcHexMasks.map (toW 10)).toFinset : Set W10).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (kzcHexMasks.map (toW 10)).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (kzcHexMasks.map (toW 10)).length := List.toFinset_card_le _
    _ = 77 := by rw [List.length_map, kzcHexMasks_length]

theorem card_inf_centSub_z0_kz3 :
    Nat.card ↥(imgC mog22 ⊓ centSub (Subgroup.zpowers z0)) = 5760 := by
  have e : ↥(imgC mog22 ⊓ centSub (Subgroup.zpowers z0)) ≃
      ↥(MulAction.stabilizer ↥(imgC mog22) z0) :=
    { toFun := fun y => ⟨⟨y, y.2.1⟩, mem_centSub_zpowers_kzc.1 y.2.2⟩
      invFun := fun y => ⟨y.1, y.1.2, mem_centSub_zpowers_kzc.2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥(imgC mog22) z0)
  rw [MulAction.index_stabilizer, card_imgC_mog22, ← Nat.card_congr e] at h1
  have h2 : (MulAction.orbit ↥(imgC mog22) z0).ncard = 77 :=
    le_antisymm ncard_orbit_le_kzc le_card_orbit
  rw [h2] at h1
  omega

theorem card_inf_kzFix_kz3
    {V : Type} [CommGroup V] {A : Subgroup (MulAut V)} (hA : MathieuCode22 A ⊤ ⊥)
    {S : Subgroup (MulAut V)} (hSA : S ≤ A) (hS : Nat.card ↥S = 128) {z : V} (hz1 : z ≠ 1)
    (hzS : ∀ s ∈ S, s z = z) : Nat.card ↥(A ⊓ kzFix_kz3 z) = 5760 := by
  obtain ⟨e₀, he₀⟩ := code22_std hA
  haveI : Finite V := Finite.of_equiv W10 e₀.symm.toEquiv
  have hcardA : Nat.card ↥A = 443520 :=
    (card_map_congrHom e₀ A).symm.trans
      ((natCard_congr_kzc (he₀.trans range_rhoC10_eq_imgC)).trans card_imgC_mog22)
  have hS2 : Nat.card ↥S = 2 ^ (Nat.card ↥A).factorization 2 := by
    rw [hS, hcardA, show (443520 : ℕ) = 2 ^ 7 * 3465 by norm_num,
      factorization_eq Nat.prime_two (by norm_num)]
    norm_num
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 hA hz1 hSA hS2 hzS
  have h1 : (A ⊓ centSub (Subgroup.zpowers z)).map (congrHom e) =
      imgC mog22 ⊓ centSub (Subgroup.zpowers z0) :=
    (CFSG.Quasithin.H.ZTrans.inf_centSub_map_congrHom e A z).trans
      (congrArg₂ (· ⊓ ·) he (congrArg (fun w => centSub (Subgroup.zpowers w)) hez))
  have h2 : Nat.card ↥(A ⊓ centSub (Subgroup.zpowers z)) = 5760 :=
    (card_map_congrHom e _).symm.trans ((natCard_congr_kzc h1).trans card_inf_centSub_z0_kz3)
  rw [kzFix_kz3_eq_centSub]
  exact h2

theorem kzCodeHexad5760_kz3_proved :
    KzCodeHexad5760_kz3 :=
  fun _ _ A hA R _ _ _ hRA _ hz1 hzR =>
    card_inf_kzFix_kz3 hA (S := R ⊓ A) inf_le_right hRA hz1 fun s hs => hzR s hs.1

end CFSG.Quasithin.H13
