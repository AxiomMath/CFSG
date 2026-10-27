module

public import CFSG.LieType.Ree.LargeReeFixedGroupSchreier
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLargeReeTits
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.F134

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem card_commutator_congr {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    Nat.card (commutator G) = Nat.card (commutator G') := by
  have hmap : (commutator G).map e.toMonoidHom = commutator G' := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← hmap]
  exact Nat.card_congr ((commutator G).equivMapOfInjective _ e.injective).toEquiv

theorem three_dvd_card_commutator_of_sup {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) (h3 : 3 ∣ Nat.card (A ⊔ B : Subgroup G)) :
    3 ∣ Nat.card (commutator G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : G →* Abelianization G := Abelianization.of
  have hAB : IsPGroup 2 ((A ⊔ B).map φ) := by
    rw [Subgroup.map_sup]
    exact (hA.map φ).to_sup_of_normal_right (hB.map φ)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hAB
  let ψ := φ.comp (A ⊔ B).subtype
  have hrange : Nat.card ψ.range = 2 ^ k := by
    rw [← hk, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange] at hcard
  have hker : 3 ∣ Nat.card ψ.ker := by
    rw [hcard] at h3
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_right _ (by norm_num)) h3)
  refine hker.trans ?_
  have hle : ψ.ker.map (A ⊔ B).subtype ≤ commutator G := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← Abelianization.ker_of]
    exact hx
  calc Nat.card ψ.ker = Nat.card (ψ.ker.map (A ⊔ B).subtype) :=
        Nat.card_congr (ψ.ker.equivMapOfInjective _ (A ⊔ B).subtype_injective).toEquiv
    _ ∣ Nat.card (commutator G) := Subgroup.card_dvd_of_le hle

theorem three_dvd_card_commutator_reeGamma
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2) : 3 ∣ Nat.card (commutator (F4.reeGamma K 0)) := by
  have : Finite (ModGL F4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact F4.prime.Prime := ⟨Nat.prime_two⟩
  set j : Fin F4.fixedOrbitCount := ⟨0, by decide⟩
  set R := F4.reeGamma K 0
  set Xs := F4.reeFixedOrbitUnipotent K 0 j
  set Ys := F4.reeFixedOrbitNegUnipotent K 0 j
  set M := F4.reeLocalBlock K 0 j
  have hXcard : Nat.card Xs = 2 :=
    (card_reeFixedOrbitUnipotent_zero (a := 0) (by rw [hK]; norm_num)).trans hK
  have hX2 : IsPGroup 2 Xs := isPGroup_reeFixedOrbitUnipotent j
  obtain ⟨w, hwM, hw⟩ := exists_mem_reeLocalBlock_mk_eq (t := F4) (K := K) (a := 0) j
  have hY : Ys = Xs.map (MulAut.conj w).toMonoidHom :=
    (reeFixedOrbitNegUnipotent_eq_map_conj hwM hw).1
  have hY2 : IsPGroup 2 Ys := by
    rw [hY]
    exact hX2.map _
  have h3M : 3 ∣ Nat.card M := by
    set ω₀ : ModGL F4.tag K ⧸ F4.reeFixedBorel K 0 :=
      ((1 : ModGL F4.tag K) : ModGL F4.tag K ⧸ F4.reeFixedBorel K 0)
    have horb : MulAction.orbit M ω₀ = F4.reeLocalCosets K 0 j := by
      ext ω
      constructor
      · rintro ⟨m, rfl⟩
        exact smul_mem_reeLocalCosets m.2 (one_mem_reeLocalCosets j)
      · intro hω
        obtain ⟨m, hm, rfl⟩ := exists_mem_reeLocalBlock_smul_one_eq hω
        exact ⟨⟨m, hm⟩, rfl⟩
    have hidx := MulAction.index_stabilizer M ω₀
    rw [horb, ncard_reeLocalCosets j, hXcard] at hidx
    rw [← show 2 + 1 = 3 from rfl, ← hidx]
    exact Subgroup.index_dvd_card _
  have hXR : Xs ≤ R := inf_le_right
  have hYR : Ys ≤ R := inf_le_right
  have hsup : M.subgroupOf R = Xs.subgroupOf R ⊔ Ys.subgroupOf R :=
    Subgroup.subgroupOf_sup hXR hYR
  refine three_dvd_card_commutator_of_sup (A := Xs.subgroupOf R) (B := Ys.subgroupOf R) ?_ ?_ ?_
  · exact hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXR).symm
  · exact hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYR).symm
  · rw [← hsup, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (reeLocalBlock_le_reeGamma j)).toEquiv]
    exact h3M

theorem three_dvd_card_of_tits
    {X : Type} [Group X] (h : ReeTitsModel X .Tits 2 1) :
    3 ∣ Nat.card X := by
  obtain ⟨-, a, hf, hmodel⟩ := h
  have ha : a = 0 := by omega
  subst ha
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K F4.prime := hc
  let ψ := (MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed F4 K 0)).trans
    ((reeFixed F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm
  let e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _ ψ)
  let e'' := e'.trans ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK2)).trans
      QuotientGroup.quotientBot)
  rw [Nat.card_congr e''.toEquiv]
  have hR : F4.reeGamma K 0 = (reeFixed F4 K 0).map (adjointGroup F4.tag K).subtype :=
    reeGamma_eq_reeFixedGroup.trans (reeFixedGroup_eq_map_reeFixed F4 K 0)
  let χ := (MulEquiv.subgroupCongr hR).trans
    ((reeFixed F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm
  rw [← card_commutator_congr χ]
  exact three_dvd_card_commutator_reeGamma hK2

end CFSG.Quasithin.F134
