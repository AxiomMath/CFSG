
module

public import CFSG.Monster.B.TwoA.Base.Space34ABase
public import CFSG.Monster.B.TwoA.Base.SevenPairCBase
public import CFSG.Monster.B.TwoA.Base.ElemAut

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem dotProduct_Zsub {a : Fin 24 → ZMod 2} (ha : a ∈ Ceq) {v : Fin 24 → ZMod 2}
    (hv : v ∈ Zsub) : a ⬝ᵥ v = 0 := by
  rcases (mem_Zsub_iff v).1 hv with h | h
  · exact dotProduct_eq_zero (mem_Ceq.1 ha).1 h
  · have h1 := dotProduct_eq_zero (mem_Ceq.1 ha).1 h
    rw [dotProduct_add] at h1
    have h2 : a ⬝ᵥ e01 = 0 := by
      rw [e01, ePair, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one,
        (mem_Ceq.1 ha).2]
      exact (by decide : ∀ t : ZMod 2, t + t = 0) _
    rw [h2, add_zero] at h1
    exact h1

theorem dotProduct_ePair (a : Fin 24 → ZMod 2) (x y : Fin 24) : a ⬝ᵥ ePair x y = a x + a y := by
  rw [ePair, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem dotProduct_vb3 (a : Fin 24 → ZMod 2) (i : Fin 3) :
    a ⬝ᵥ vb3 i = a (bpA3 i) + a (bpB3 i) := by
  fin_cases i <;> exact dotProduct_ePair a _ _

theorem eval_lab3 {a : Fin 24 → ZMod 2} (ha : a ∈ Ceq) (ℓ : Fin 8) (hℓ : ℓ ≠ 0) :
    a (labA ℓ) + a (labB ℓ) = ∑ i : Fin 3, digit ℓ i * (a (bpA3 i) + a (bpB3 i)) := by
  have h := dotProduct_Zsub ha (lab3_rel ℓ hℓ)
  rw [dotProduct_sub, dotProduct_ePair, dotProduct_sum, sub_eq_zero] at h
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_vb3] at h
  exact h

theorem labA_lab7 : ∀ i : Fin 7, labA ⟨i + 1, by omega⟩ = pa7 i := by decide

theorem labB_lab7 : ∀ i : Fin 7, labB ⟨i + 1, by omega⟩ = pb7 i := by decide

theorem eval_pair7 {a : Fin 24 → ZMod 2} (ha : a ∈ Ceq) (i : Fin 7) :
    a (pa7 i) + a (pb7 i) = ∑ j : Fin 3, digit (i + 1) j * (a (bpA3 j) + a (bpB3 j)) := by
  have h := eval_lab3 ha ⟨i + 1, by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this)
  rwa [labA_lab7, labB_lab7] at h

theorem mem_DofA3_iff
    {a : Fin 24 → ZMod 2} :
    a ∈ DofA A3 ↔ a ∈ Ceq ∧ ∀ j : Fin 3, a (bpA3 j) = a (bpB3 j) := by
  rw [mem_DofA]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun j => ?_⟩
    obtain ⟨hj, hA⟩ := bp3_mem j
    exact h _ hA _ (by rw [duad_val]; exact Finset.mem_insert_self _ _) _
      (by rw [duad_val]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun D hD x hx y hy => ?_⟩
    obtain ⟨i, rfl⟩ := A3_eq_duad7 D hD
    have hxy : a (pa7 i) = a (pb7 i) := by
      have e := eval_pair7 ha i
      have hz : ∀ j : Fin 3, a (bpA3 j) + a (bpB3 j) = 0 := fun j => by
        rw [h j]; exact (by decide : ∀ t : ZMod 2, t + t = 0) _
      simp only [hz, mul_zero, Finset.sum_const_zero] at e
      exact (by decide : ∀ s t : ZMod 2, s + t = 0 → s = t) _ _ e
    rw [duad_val, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl

theorem mem_DofA2_iff
    {a : Fin 24 → ZMod 2} :
    a ∈ DofA A2 ↔ a ∈ Ceq ∧ ∀ j : Fin 2, a (bpA2 j) = a (bpB2 j) := by
  rw [mem_DofA]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun j => ?_⟩
    obtain ⟨hj, hA⟩ := bp2_mem j
    exact h _ hA _ (by rw [duad_val]; exact Finset.mem_insert_self _ _) _
      (by rw [duad_val]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun D hD x hx y hy => ?_⟩
    obtain ⟨i, hi, rfl⟩ := A2_eq_duad7 D hD
    have hxy : a (pa7 i) = a (pb7 i) := by
      have e := eval_pair7 ha i
      have h0 : a (bpA3 0) + a (bpB3 0) = 0 := by
        rw [show bpA3 0 = bpA2 0 from rfl, show bpB3 0 = bpB2 0 from rfl, h 0]
        exact (by decide : ∀ t : ZMod 2, t + t = 0) _
      have h1 : a (bpA3 1) + a (bpB3 1) = 0 := by
        rw [show bpA3 1 = bpA2 1 from rfl, show bpB3 1 = bpB2 1 from rfl, h 1]
        exact (by decide : ∀ t : ZMod 2, t + t = 0) _
      have hd2 : digit ((i : ℕ) + 1) 2 = 0 := by
        have : ∀ i : Fin 7, (i : ℕ) < 3 → digit ((i : ℕ) + 1) 2 = 0 := by decide
        exact this i hi
      rw [Fin.sum_univ_three, h0, h1] at e
      simp only [Fin.val_two, hd2, mul_zero, zero_mul, add_zero] at e
      exact (by decide : ∀ s t : ZMod 2, s + t = 0 → s = t) _ _ e
    rw [duad_val, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl

theorem DofA3_eq :
    DofA A3 = (LinearMap.ker evalMap3).map Ceq.subtype := by
  ext a
  rw [mem_DofA3_iff, Submodule.mem_map]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker, evalMap3_apply]
    funext j
    show a (bpA3 j) + a (bpB3 j) = 0
    rw [h j]
    exact (by decide : ∀ t : ZMod 2, t + t = 0) _
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun j => ?_⟩
    rw [LinearMap.mem_ker, evalMap3_apply] at hc
    exact (by decide : ∀ s t : ZMod 2, s + t = 0 → s = t) _ _ (congrFun hc j)

theorem DofA2_eq :
    DofA A2 = (LinearMap.ker evalMap2).map Ceq.subtype := by
  ext a
  rw [mem_DofA2_iff, Submodule.mem_map]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker, evalMap2_apply]
    funext j
    show a (bpA2 j) + a (bpB2 j) = 0
    rw [h j]
    exact (by decide : ∀ t : ZMod 2, t + t = 0) _
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun j => ?_⟩
    rw [LinearMap.mem_ker, evalMap2_apply] at hc
    exact (by decide : ∀ s t : ZMod 2, s + t = 0 → s = t) _ _ (congrFun hc j)

theorem finrank_ker_eval {n : ℕ} (f : Ceq →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hf : Function.Surjective f) :
    Module.finrank (ZMod 2) ((LinearMap.ker f).map Ceq.subtype) = 11 - n := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hf, finrank_top, Module.finrank_fin_fun, finrank_Ceq] at h
  rw [(Submodule.equivMapOfInjective _ Ceq.injective_subtype _).finrank_eq.symm]
  omega

theorem natCard_DofA3_quot :
    Nat.card (DofA A3 ⧸ ΩIn (DofA A3)) = 2 ^ 7 := by
  rw [natCard_quot_ΩIn (dofAKofAHyp A3), DofA3_eq, finrank_ker_eval _ evalMap3_surjective]

theorem natCard_DofA2_quot :
    Nat.card (DofA A2 ⧸ ΩIn (DofA A2)) = 2 ^ 8 := by
  rw [natCard_quot_ΩIn (dofAKofAHyp A2), DofA2_eq, finrank_ker_eval _ evalMap2_surjective]

theorem digits_inj : ∀ ℓ ℓ' : Fin 8, (∀ i : Fin 3, digit ℓ i = digit ℓ' i) → ℓ = ℓ' := by
  decide

theorem eq_of_zPair_eq_A3 {x y x' y' : Fin 24} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h : duad x y hxy ∈ A3) (h' : duad x' y' hxy' ∈ A3) (he : zPair x y = zPair x' y') :
    duad x y hxy = duad x' y' hxy' := by
  obtain ⟨ℓ, hℓ, hD⟩ := A3_cases _ h
  obtain ⟨ℓ', hℓ', hD'⟩ := A3_cases _ h'
  rw [zPair_eq_of_duad_eq hxy _ hD, zPair_eq_of_duad_eq hxy' _ hD', zPair_lab3 ℓ hℓ,
    zPair_lab3 ℓ' hℓ'] at he
  have hc := Fintype.linearIndependent_iff.1 linearIndependent_zb3
    (fun i => digit ℓ i - digit ℓ' i) (by
      simp only [sub_smul, Finset.sum_sub_distrib, he, sub_self])
  have hl : ℓ = ℓ' := digits_inj ℓ ℓ' fun i => sub_eq_zero.1 (hc i)
  rw [hD, hD']
  exact duad_congr _ _ (by rw [hl]) (by rw [hl])

theorem digits_inj2 : ∀ ℓ ℓ' : Fin 4, (∀ i : Fin 2, digit ℓ i = digit ℓ' i) → ℓ = ℓ' := by
  decide

theorem eq_of_zPair_eq_A2 {x y x' y' : Fin 24} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h : duad x y hxy ∈ A2) (h' : duad x' y' hxy' ∈ A2) (he : zPair x y = zPair x' y') :
    duad x y hxy = duad x' y' hxy' := by
  obtain ⟨ℓ, hℓ, hD⟩ := A2_cases _ h
  obtain ⟨ℓ', hℓ', hD'⟩ := A2_cases _ h'
  rw [zPair_eq_of_duad_eq hxy _ hD, zPair_eq_of_duad_eq hxy' _ hD', zPair_lab2 ℓ hℓ,
    zPair_lab2 ℓ' hℓ'] at he
  have hc := Fintype.linearIndependent_iff.1 linearIndependent_zb2
    (fun i => digit ℓ i - digit ℓ' i) (by
      simp only [sub_smul, Finset.sum_sub_distrib, he, sub_self])
  have hl : ℓ = ℓ' := digits_inj2 ℓ ℓ' fun i => sub_eq_zero.1 (hc i)
  rw [hD, hD']
  exact duad_congr _ _ (by rw [hl]) (by rw [hl])

theorem bp3_label : ∀ j : Fin 3, labelOf (bpA3 j) (bpB3 j) = 2 ^ (j : ℕ) := by decide

theorem bp2_label : ∀ j : Fin 2, labelOf (bpA2 j) (bpB2 j) = 2 ^ (j : ℕ) := by decide

theorem linEnd3_eq_one_iff (p : FA3) : glHom3 p = 1 ↔ linEnd3 p = 1 := by
  rw [glHom3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

theorem linEnd2_eq_one_iff (p : FA2) : glHom2 p = 1 ↔ linEnd2 p = 1 := by
  rw [glHom2, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

theorem mem_KofA3_iff
    (p : AutPerm) : p ∈ KofA A3 ↔ ∃ h : p ∈ FA3, glHom3 ⟨p, h⟩ = 1 := by
  rw [mem_KofA]
  constructor
  · rintro ⟨hp, hfix⟩
    have hF : p ∈ FA3 := ⟨hp, smul_eq_of_subset fun D hD => (hfix D hD).symm ▸ hD⟩
    refine ⟨hF, Units.ext ?_⟩
    rw [glHom3_apply, Units.val_one]
    have hl : ∀ j : Fin 3, labelOf ((p : Equiv.Perm (Fin 24)) (bpA3 j))
        ((p : Equiv.Perm (Fin 24)) (bpB3 j)) = labelOf (bpA3 j) (bpB3 j) := by
      intro j
      obtain ⟨hj, hA⟩ := bp3_mem j
      have h1 := hfix _ hA
      rw [autPerm_smul_duad] at h1
      exact labelOf_duad _ _ h1
    simp only [hl, bp3_label]
    decide
  · rintro ⟨hF, h1⟩
    refine ⟨hF.1, fun D hD => ?_⟩
    obtain ⟨x, y, hxy, rfl⟩ : ∃ x y : Fin 24, ∃ h : x ≠ y, D = duad x y h := by
      obtain ⟨ℓ, -, hD'⟩ := A3_cases D hD
      exact ⟨_, _, _, hD'⟩
    have hL := (linEnd3_eq_one_iff ⟨p, hF⟩).1 h1
    have hz := congrArg (fun f : Module.End (ZMod 2) Z3 => ((f ⟨zPair x y, zPair_mem_Z3 hxy hD⟩ :
      Z3) : Zcoc)) hL
    change zAct ⟨p, FA3_le_Ppair hF⟩ (zPair x y) = zPair x y at hz
    rw [zAct_zPair] at hz
    rw [autPerm_smul_duad]
    exact eq_of_zPair_eq_A3 _ hxy (duad_smul_mem_A3 hF hxy hD) hD hz

theorem mem_KofA2_iff
    (p : AutPerm) : p ∈ KofA A2 ↔ ∃ h : p ∈ FA2, glHom2 ⟨p, h⟩ = 1 := by
  rw [mem_KofA]
  constructor
  · rintro ⟨hp, hfix⟩
    have hF : p ∈ FA2 := ⟨hp, smul_eq_of_subset fun D hD => (hfix D hD).symm ▸ hD⟩
    refine ⟨hF, Units.ext ?_⟩
    rw [glHom2_apply, Units.val_one]
    have hl : ∀ j : Fin 2, labelOf ((p : Equiv.Perm (Fin 24)) (bpA2 j))
        ((p : Equiv.Perm (Fin 24)) (bpB2 j)) = labelOf (bpA2 j) (bpB2 j) := by
      intro j
      obtain ⟨hj, hA⟩ := bp2_mem j
      have h1 := hfix _ hA
      rw [autPerm_smul_duad] at h1
      exact labelOf_duad _ _ h1
    simp only [hl, bp2_label]
    decide
  · rintro ⟨hF, h1⟩
    refine ⟨hF.1, fun D hD => ?_⟩
    obtain ⟨x, y, hxy, rfl⟩ : ∃ x y : Fin 24, ∃ h : x ≠ y, D = duad x y h := by
      obtain ⟨ℓ, -, hD'⟩ := A2_cases D hD
      exact ⟨_, _, _, hD'⟩
    have hL := (linEnd2_eq_one_iff ⟨p, hF⟩).1 h1
    have hz := congrArg (fun f : Module.End (ZMod 2) Z2 => ((f ⟨zPair x y, zPair_mem_Z2 hxy hD⟩ :
      Z2) : Zcoc)) hL
    change zAct ⟨p, FA2_le_Ppair hF⟩ (zPair x y) = zPair x y at hz
    rw [zAct_zPair] at hz
    rw [autPerm_smul_duad]
    exact eq_of_zPair_eq_A2 _ hxy (duad_smul_mem_A2 hF hxy hD) hD hz

theorem KofA3_eq :
    KofA A3 = glHom3.ker.map FA3.subtype := by
  ext p
  rw [mem_KofA3_iff]
  constructor
  · rintro ⟨hF, h1⟩
    exact ⟨⟨p, hF⟩, h1, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩

theorem KofA2_eq :
    KofA A2 = glHom2.ker.map FA2.subtype := by
  ext p
  rw [mem_KofA2_iff]
  constructor
  · rintro ⟨hF, h1⟩
    exact ⟨⟨p, hF⟩, h1, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩

theorem natCard_ker_of_surj {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) : Nat.card f.ker * Nat.card H = Nat.card G := by
  rw [← natCard_range_mul_ker f, MonoidHom.range_eq_top.2 hf, Subgroup.card_top, mul_comm]

theorem map_wFix_eq
    {U : Submodule (ZMod 2) (Wv v0)} {A : Finset (Set.powersetCard (Fin 24) 2)}
    (hU : PairSpace U A) :
    (wFix (U : Set (Wv v0))).map (Kstab v0).subtype = monoSub (dofAKofAHyp A) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_wFix_iff hU k).1 hk
  · intro hx
    exact ⟨⟨x, monoSub_dofAKofA_le_Kstab hx⟩, (mem_wFix_iff hU _).2 hx, rfl⟩

theorem map_wSetStab_inf_Mfr_eq
    {U : Submodule (ZMod 2) (Wv v0)}
    {A : Finset (Set.powersetCard (Fin 24) 2)} (hU : PairSpace U A) :
    (wSetStab U ⊓ Mfr).map (Kstab v0).subtype = monoSub (ceqFofAHyp A) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_wSetStab_inf_Mfr_iff hU k).1 hk
  · intro hx
    exact ⟨⟨x, monoSub_ceqFofA_le_Kstab hx⟩, (mem_wSetStab_inf_Mfr_iff hU _).2 hx, rfl⟩

theorem natCard_of_map
    {H : Subgroup (Kstab v0)} {S : Subgroup OLq}
    (h : H.map (Kstab v0).subtype = S) : Nat.card H = Nat.card S := by
  rw [← h]
  exact Nat.card_congr (H.equivMapOfInjective _ Subtype.coe_injective).toEquiv

end CFSG.Monster.B.TwoA
