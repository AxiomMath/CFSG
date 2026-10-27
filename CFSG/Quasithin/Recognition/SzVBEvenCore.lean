module

public import CFSG.Quasithin.Recognition.SzVBOdd

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem wSide_card [Finite G] {P S V : Subgroup G} {z : G} (hK : KleinData P V z)
    (hB : BenderLocalFacts P S V) (hW : IsElemAbelian 2 (conjClosure V P)) :
    ∀ y : ↥P, y * y = 1 → y ∉ kerAct P V →
      ∃ ψ : ↥(conjClosure V P) →* ↥(conjClosure V P),
        (∀ a : ↥(conjClosure V P), ((ψ a : ↥(conjClosure V P)) : G) =
          y * a * (y : G)⁻¹ * (a : G)⁻¹) ∧ 2 ^ 4 ≤ Nat.card ψ.range := by
  obtain ⟨t, ht⟩ := exists_tDataG hK
  have hquad : ⁅⁅conjClosure V P, conjSub (1 : G) (conjClosure V P)⁆,
      conjSub (1 : G) (conjClosure V P)⁆ = ⊥ := by
    rw [conjSub_one, Subgroup.commutator_self_eq_bot_iff.mpr hW.1, Subgroup.commutator_bot_left]
  exact (OddAux.wSide (g := 1) hB hW (le_normalizer_conjClosure V P) ht hquad).2

private theorem index_le_four_of_tData [Finite G] {P S V W : Subgroup G} {z : G}
    {t : ConjSet P V → G} (hB : BenderLocalFacts P S V) (hW : IsElemAbelian 2 W)
    (hPN : P ≤ Subgroup.normalizer (W : Set G)) (ht : TDataG P W t z) {A₀ : Subgroup G}
    (hquad : ⁅⁅W, A₀⁆, A₀⁆ = ⊥) :
    ∀ E : Subgroup ↥P, (∀ e ∈ E, (e : G) ∈ A₀) → (kerAct P V).relIndex E ≤ 4 := by
  classical
  have : Fintype (ConjSet P V) := Fintype.ofFinite _
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  have hmul : ∀ a b : ↥W, ((a * b : ↥W) : G) = (a : G) * (b : G) := fun a b => rfl
  have hinvW : ∀ a : ↥W, ((a⁻¹ : ↥W) : G) = (a : G)⁻¹ := fun a => rfl
  have honeW : ((1 : ↥W) : G) = 1 := rfl
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥P →* MulAut ↥W,
      ∀ (x : ↥P) (a : ↥W), ((ρ x a : ↥W) : G) = x * a * (x : G)⁻¹ :=
    ⟨(conjAct W).comp (Subgroup.inclusion hPN),
      fun x a => OddAux.conjAct_coe W (Subgroup.inclusion hPN x) a⟩
  obtain ⟨tW, htW⟩ : ∃ tW : ConjSet P V → ↥W, ∀ a, ((tW a : ↥W) : G) = t a :=
    ⟨fun a => ⟨t a, ht.t_mem a⟩, fun a => rfl⟩
  obtain ⟨zW, hzW⟩ : ∃ zW : ↥W, (zW : G) = z := ⟨⟨z, ht.z_mem⟩, rfl⟩
  have hT : TData ρ tW zW := by
    refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, fun h => ht.z_ne_one ?_,
      fun x => Subtype.ext ?_, fun x a => ?_, fun a b hab => ?_⟩
    · rw [hmul, htW, honeW]
      exact ht.t_sq a
    · rw [hmul, hzW, honeW]
      exact ht.z_sq
    · rw [← hzW, h, honeW]
    · rw [hρ, hzW]
      calc (x : G) * z * (x : G)⁻¹ = z * x * (x : G)⁻¹ := by rw [ht.z_cent x x.2]
        _ = z := mul_inv_cancel_right _ _
    · rcases ht.act x a with h | h
      · refine Or.inl (Subtype.ext ?_)
        rw [hρ, htW, htW]
        exact h
      · refine Or.inr (Subtype.ext ?_)
        rw [hρ, hmul, htW, htW, hzW]
        exact h
    · refine ⟨fun h => (ht.distinct a b hab).1 ?_, fun h => (ht.distinct a b hab).2 ?_⟩
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, honeW] at this
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, hzW] at this
  have hΩodd : Odd (Fintype.card (ConjSet P V)) := by
    rw [← Nat.card_eq_fintype_card]
    exact hB.card_odd
  have hΩ5 : 5 ≤ Fintype.card (ConjSet P V) := by
    rw [← Nat.card_eq_fintype_card]
    exact hB.five_le
  have hker : KerProp tW zW := by
    refine kerProp_of_tData hT (OddAux.conjSet_isPretransitive P V) (S.subgroupOf P)
      (hB.S_pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hB.S_le).symm) (ConjSet.base P V)
      ?_ ?_ hΩodd
    · intro r hr
      exact Subtype.ext
        (OddAux.conjSub_eq_of_mem_normalizer'
          (hB.S_le_normalizer (Subgroup.mem_subgroupOf.mp hr)))
    · intro a b ha hb
      obtain ⟨s, hs, h⟩ := hB.S_transitive a b ha hb
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, h⟩
  have hcomm_coe : ∀ (s : ↥P) (a : ↥W), ((commMap ρ s a : ↥W) : G) =
      (s : G) * a * (s : G)⁻¹ * (a : G)⁻¹ := by
    intro s a
    rw [commMap_apply, hmul, hinvW, hρ]
  intro E hE
  refine hB.orbit_le_four E fun e he e' he' U => ?_
  refine orbit_le_two_of_quadratic hT hker hΩ5 e e' U (Or.inl ?_)
  have h1 : ((e : G) * t U * (e : G)⁻¹ * (t U)⁻¹) ∈ ⁅W, A₀⁆ := by
    rw [Subgroup.commutator_comm W A₀]
    exact Subgroup.commutator_mem_commutator (hE e he) (ht.t_mem U)
  have h2 : ((e' : G) * ((e : G) * t U * (e : G)⁻¹ * (t U)⁻¹) * (e' : G)⁻¹ *
      ((e : G) * t U * (e : G)⁻¹ * (t U)⁻¹)⁻¹) ∈ (⊥ : Subgroup G) := by
    rw [← hquad, Subgroup.commutator_comm ⁅W, A₀⁆ A₀]
    exact Subgroup.commutator_mem_commutator (hE e' he') h1
  apply Subtype.ext
  rw [hcomm_coe, hcomm_coe, htW, honeW]
  exact Subgroup.mem_bot.mp h2

theorem wSide_index [Finite G] {P S V : Subgroup G} {z : G} (hK : KleinData P V z)
    (hB : BenderLocalFacts P S V) (hW : IsElemAbelian 2 (conjClosure V P)) {A₀ : Subgroup G}
    (hquad : ⁅⁅conjClosure V P, A₀⁆, A₀⁆ = ⊥) :
    ∀ E : Subgroup ↥P, (∀ e ∈ E, (e : G) ∈ A₀) → (kerAct P V).relIndex E ≤ 4 := by
  obtain ⟨t, ht⟩ := exists_tDataG hK
  exact index_le_four_of_tData hB hW (le_normalizer_conjClosure V P) ht hquad

private theorem exists_index_le_eight {A P' : Subgroup G} (K : Subgroup ↥P')
    (h2 : P'.relIndex A ≤ 2)
    (h4 : ∀ E : Subgroup ↥P', (∀ e ∈ E, (e : G) ∈ A) → K.relIndex E ≤ 4) :
    ∃ F₀ : Subgroup ↥A, F₀.index ≤ 8 ∧
      ∀ f ∈ F₀, ∃ hf : (f : G) ∈ P', (⟨f, hf⟩ : ↥P') ∈ K := by
  let ι : ↥(P'.subgroupOf A) →* ↥P' :=
    { toFun := fun b => ⟨((b : ↥A) : G), Subgroup.mem_subgroupOf.mp b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨(K.comap ι).map (P'.subgroupOf A).subtype, ?_, ?_⟩
  · have hle : (K.comap ι).map (P'.subgroupOf A).subtype ≤ P'.subgroupOf A :=
      Subgroup.map_subtype_le _
    have hsub : ((K.comap ι).map (P'.subgroupOf A).subtype).subgroupOf (P'.subgroupOf A) =
        K.comap ι :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    have h4' : K.relIndex ι.range ≤ 4 := h4 _ (by rintro _ ⟨b, rfl⟩; exact (b : ↥A).2)
    have h2' : (P'.subgroupOf A).index ≤ 2 := h2
    rw [← Subgroup.relIndex_mul_index hle, Subgroup.relIndex, hsub, Subgroup.index_comap]
    calc K.relIndex ι.range * (P'.subgroupOf A).index ≤ 4 * 2 := Nat.mul_le_mul h4' h2'
      _ = 8 := by norm_num
  · rintro f ⟨b, hb, rfl⟩
    exact ⟨Subgroup.mem_subgroupOf.mp b.2, hb⟩

theorem even_case_false [Finite G] {P S V P' S' V' : Subgroup G} {z z' : G}
    (hK : KleinData P V z) (hB : BenderLocalFacts P S V)
    (hK' : KleinData P' V' z') (hB' : BenderLocalFacts P' S' V')
    (hA : IsElemAbelian 2 (conjClosure V P)) (hW' : IsElemAbelian 2 (conjClosure V' P'))
    (hW'P : conjClosure V' P' ≤ P)
    (hW'N : conjClosure V' P' ≤ Subgroup.normalizer (conjClosure V P : Set G))
    (hnontriv : ∃ w ∈ conjClosure V' P', ∃ hw : w ∈ P, (⟨w, hw⟩ : ↥P) ∉ kerAct P V)
    (h2 : P'.relIndex (conjClosure V P) ≤ 2) (h3 : z' ∉ conjClosure V P) : False := by
  have _ := hW'P
  obtain ⟨w, hw', hw, hwnot⟩ := hnontriv
  have hwsq : w * w = 1 := by
    have := F7.isElemAbelian_pow_eq_one hW' hw'
    rwa [pow_two] at this
  obtain ⟨ψ, hψ, hcard⟩ := wSide_card hK hB hA ⟨w, hw⟩ (Subtype.ext hwsq) hwnot
  have hquad : ⁅⁅conjClosure V' P', conjClosure V P⁆, conjClosure V P⁆ = ⊥ :=
    le_bot_iff.mp
      ((Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_right.mp hW'N)
        le_rfl).trans (Subgroup.commutator_self_eq_bot_iff.mpr hA.1).le)
  obtain ⟨F₀, hF₀idx, hF₀⟩ :=
    exists_index_le_eight (kerAct P' V') h2 (wSide_index hK' hB' hW' hquad)
  have hψ1 : ∀ f ∈ F₀, ψ f ∈ (⊥ : Subgroup ↥(conjClosure V P)) := by
    intro f hf
    obtain ⟨hfP, hfk⟩ := hF₀ f hf
    have hcomm := commutator_mem_of_fixes hK' hfP (OddAux.mem_kerAct.mp hfk) hw'
    have hwf : w * (f : G) * w⁻¹ * (f : G)⁻¹ ∈ conjClosure V P :=
      (conjClosure V P).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hW'N hw') (f : G)).mp f.2)
        ((conjClosure V P).inv_mem f.2)
    have e : w * (f : G) * w⁻¹ * (f : G)⁻¹ = ((f : G) * w * (f : G)⁻¹ * w⁻¹)⁻¹ := by group
    have hone : (f : G) * w * (f : G)⁻¹ * w⁻¹ = 1 := by
      rcases hcomm with h | h
      · exact h
      · exfalso
        apply h3
        rw [← h]
        have hinv := (conjClosure V P).inv_mem hwf
        rwa [e, inv_inv] at hinv
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [hψ]
    show w * (f : G) * w⁻¹ * (f : G)⁻¹ = 1
    rw [e, hone, inv_one]
  have hcard' := card_range_le_index_mul ψ F₀ ⊥ hψ1
  rw [Subgroup.card_bot, mul_one] at hcard'
  exact absurd (hcard.trans (hcard'.trans hF₀idx)) (by norm_num)

end CFSG.Quasithin.SzVB
