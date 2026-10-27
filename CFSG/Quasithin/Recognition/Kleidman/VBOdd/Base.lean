module

public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Ctx
public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Perm
public import CFSG.Quasithin.Recognition.SzVBOddL24Orbit

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SzVB

section Base

variable {G : Type} [Group G] [Finite G] {P T V : Subgroup G} {z : G}

omit [Finite G] in
theorem Prim.odd_card (hP : Prim P T V z) : Odd (Nat.card (ConjSet P V)) := by
  rw [hP.l24.card_five]; decide

omit [Finite G] in
theorem Prim.two_fixed (hP : Prim P T V z) : ∀ e ∈ P, e * e = 1 → e ∈ Subgroup.normalizer (V : Set G) →
    ∀ k ∈ P, conjSub k V ≠ V → e ∈ Subgroup.normalizer (conjSub k V : Set G) →
      e ∈ pCoreOf 2 P := by
  intro e heP he2 heV k hk hkV hek
  by_contra hne
  have hxk : (⟨e, heP⟩ : ↥P) ∉ kerAct P V := fun h => hne (hP.ker_le _ h)
  obtain ⟨ω, -, hu⟩ := hP.inv_one_fixed ⟨e, heP⟩ (Subtype.ext he2) hxk
  have h1 : (⟨e, heP⟩ : ↥P) • ConjSet.base P V = ConjSet.base P V :=
    Subtype.ext (F7.conjSub_eq_of_mem_normalizer heV)
  have h2 : (⟨e, heP⟩ : ↥P) • ConjSet.mk P V ⟨k, hk⟩ = ConjSet.mk P V ⟨k, hk⟩ :=
    Subtype.ext (F7.conjSub_eq_of_mem_normalizer hek)
  have h3 := (hu _ h1).trans (hu _ h2).symm
  exact hkV (congrArg Subtype.val h3).symm


theorem Prim.quad_pair (hP : Prim P T V z) : ∀ e ∈ P, ∀ e' ∈ P, e * e = 1 → e' * e' = 1 →
    e * e' = e' * e → (∀ a ∈ conjClosure V P, e' * (e * a * e⁻¹ * a⁻¹) * e'⁻¹ = e * a * e⁻¹ * a⁻¹) →
    e ∈ pCoreOf 2 P ∨ e' ∈ pCoreOf 2 P ∨ e * e' ∈ pCoreOf 2 P := by
  intro e he e' he' he2 he'2 hcomm hq
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  set x : ↥P := ⟨e, he⟩ with hxdef
  set x' : ↥P := ⟨e', he'⟩ with hx'def
  have hxx : x * x = 1 := Subtype.ext he2
  have hx'x' : x' * x' = 1 := Subtype.ext he'2
  have hxx' : x * x' = x' * x := Subtype.ext hcomm
  have hx : x ∉ kerAct P V := fun h => h1 (hP.ker_le x h)
  have hx' : x' ∉ kerAct P V := fun h => h2 (hP.ker_le x' h)
  obtain ⟨ω, hω, hu⟩ := hP.inv_one_fixed x hxx hx
  obtain ⟨ω', hω', hu'⟩ := hP.inv_one_fixed x' hx'x' hx'
  set ρ := MulAction.toPermHom ↥P (ConjSet P V) with hρ
  have hne : ρ x ≠ ρ x' := by
    intro hxx'ρ
    apply h3
    apply hP.ker_le (x * x')
    show ρ (x * x') = 1
    rw [map_mul, ← hxx'ρ, ← map_mul, hxx, map_one]
  obtain ⟨U, hU1, hU2, hU3⟩ := perm_pair_of_one_fixed hP.l24.card_five (ρ x) (ρ x')
    (by rw [← map_mul, hxx, map_one]) (by rw [← map_mul, hx'x', map_one])
    ⟨ω, hω, fun U hU => hu U hU⟩ ⟨ω', hω', fun U hU => hu' U hU⟩ hne
    (by rw [← map_mul, ← map_mul, hxx'])
  have key := orbit_of_comm hP.klein hP.abel hP.l24.S_le hP.l24.S_pGroup hP.l24.S_le_normalizer
    hP.l24.S_transitive hP.odd_card (by rw [hP.l24.card_five]) (e := x) (e' := x')
    (fun w hw => hq w hw) U
  rcases key with h | h | h
  · exact hU1 h
  · exact hU2 h
  · exact hU3 h


theorem Prim.exists_comm_hom (hP : Prim P T V z) {y : ↥P} (R : Finset (ConjSet P V))
    (hR : ∀ x ∈ R, y • x ≠ x ∧ y • x ∉ R) :
    ∃ ψ : ↥(conjClosure V P) →* ↥(conjClosure V P),
      (∀ a : ↥(conjClosure V P),
        ((ψ a : ↥(conjClosure V P)) : G) = y * a * (y : G)⁻¹ * (a : G)⁻¹) ∧
        2 ^ R.card ≤ Nat.card ψ.range := by
  classical
  obtain ⟨t, ht⟩ := exists_tDataG hP.klein
  have hPN := le_normalizer_conjClosure V P
  have hW := hP.abel
  generalize conjClosure V P = W at hW ht hPN ⊢
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
    exact hP.odd_card
  have hker : KerProp tW zW := by
    refine kerProp_of_tData hT (OddAux.conjSet_isPretransitive P V) (T.subgroupOf P)
      (hP.l24.S_pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.l24.S_le).symm)
      (ConjSet.base P V) ?_ ?_ hΩodd
    · intro r hr
      exact Subtype.ext
        (OddAux.conjSub_eq_of_mem_normalizer'
          (hP.l24.S_le_normalizer (Subgroup.mem_subgroupOf.mp hr)))
    · intro a b ha hb
      obtain ⟨s, hs, h⟩ := hP.l24.S_transitive a b ha hb
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, h⟩
  have hcomm_coe : ∀ (s : ↥P) (a : ↥W), ((commMap ρ s a : ↥W) : G) =
      (s : G) * a * (s : G)⁻¹ * (a : G)⁻¹ := by
    intro s a
    rw [commMap_apply, hmul, hinvW, hρ]
  refine ⟨commMap ρ y, hcomm_coe y, ?_⟩
  have hψ : ∀ x : ConjSet P V, commMap ρ y (tW x) = tW (y • x) * tW x ∨
      commMap ρ y (tW x) = tW (y • x) * tW x * zW := by
    intro x
    have hinv : (tW x)⁻¹ = tW x := inv_eq_of_mul_eq_one_right (hT.t_sq x)
    rw [commMap_apply, hinv]
    rcases hT.act y x with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h]; exact mul_right_comm _ _ _)
  exact card_range_ge_of_indep hker hΩodd hT.t_sq hT.z_sq (commMap ρ y) (fun x => y • x)
    (MulAction.injective y) R hR hψ

theorem Prim.comm_big (hP : Prim P T V z) : ∀ w ∈ P, w * w = 1 → w ∉ pCoreOf 2 P → ∀ c : G,
    ∃ a ∈ conjClosure V P, w * a * w⁻¹ * a⁻¹ ≠ 1 ∧ w * a * w⁻¹ * a⁻¹ ≠ c := by
  classical
  intro w hw hw2 hwO c
  set y : ↥P := ⟨w, hw⟩ with hydef
  have hyy : y * y = 1 := Subtype.ext hw2
  have hy : y ∉ kerAct P V := fun h => hwO (hP.ker_le y h)
  obtain ⟨ω, hω, hu⟩ := hP.inv_one_fixed y hyy hy
  obtain ⟨a, b, ha, hb, hba, hbma⟩ := perm_two_cycles_of_one_fixed hP.l24.card_five
    (MulAction.toPermHom ↥P (ConjSet P V) y)
    (by rw [← map_mul, hyy, map_one]) ⟨ω, hω, fun U hU => hu U hU⟩
  have hya : y • a ≠ a := ha
  have hyb : y • b ≠ b := hb
  have hbya : b ≠ y • a := hbma
  have hyyb : y • y • b = b := by rw [← mul_smul, hyy, one_smul]
  let R : Finset (ConjSet P V) := {a, b}
  have hR : ∀ x ∈ R, y • x ≠ x ∧ y • x ∉ R := by
    intro x hx
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · refine ⟨hya, ?_⟩
      rintro (h | h)
      · exact hya h
      · exact hbya h.symm
    · refine ⟨hyb, ?_⟩
      rintro (h | h)
      · exact hbya (hyyb.symm.trans (congrArg (fun u => y • u) h))
      · exact hyb h
  obtain ⟨ψ, hψ, hcard⟩ := hP.exists_comm_hom R hR
  have hRcard : R.card = 2 := Finset.card_pair (Ne.symm hba)
  by_contra hcon
  push Not at hcon
  have : Fintype ψ.range := Fintype.ofFinite _
  have hsub : ∀ r : ψ.range, (((r : ↥(conjClosure V P)) : ↥(conjClosure V P)) : G) ∈
      ({1, c} : Finset G) := by
    rintro ⟨_, ⟨a, rfl⟩⟩
    show ((ψ a : ↥(conjClosure V P)) : G) ∈ ({1, c} : Finset G)
    rw [hψ a]
    by_cases h : w * (a : G) * w⁻¹ * (a : G)⁻¹ = 1
    · simp [hydef, h]
    · have := hcon a a.2 h
      simp [hydef, this]
  have hinj : Function.Injective
      (fun r : ψ.range => (((r : ↥(conjClosure V P)) : ↥(conjClosure V P)) : G)) :=
    fun r r' h => Subtype.ext (Subtype.ext h)
  have hle : Nat.card ψ.range ≤ 2 := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact (Finset.card_le_card_of_injOn _ (fun r _ => hsub r) hinj.injOn).trans
      Finset.card_le_two
  rw [hRcard] at hcard
  omega

end Base

end CFSG.Quasithin.Kleidman.VBOdd
