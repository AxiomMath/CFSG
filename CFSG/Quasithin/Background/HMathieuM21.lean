module

public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.M22
public import Certificates.Data.CFSGNative.Mathieu.Check
public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.Quasithin.Background.A3ComponentsBasic
public meta import Certificates.Data.CFSGNative.Mathieu.Check
public meta import CFSG.Quasithin.Background.HMathieuCent
public meta import CFSG.Monster.Code.Basis
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import CFSG.Quasithin.Background.HMathieuM21Inputs
public import Certificates.Certificate7064

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped commutatorElement

theorem m21_check : check 21 m21Data = true :=
  Certificates.certificate7064.1

abbrev m21gA : Equiv.Perm (Fin 21) :=
  List.formPerm [0, 4] * List.formPerm [1, 2] * List.formPerm [5, 17] * List.formPerm [6, 13] *
    List.formPerm [7, 12] * List.formPerm [9, 18] * List.formPerm [10, 14] *
    List.formPerm [16, 19]

abbrev m21gB : Equiv.Perm (Fin 21) :=
  List.formPerm [0, 14, 11, 1, 20] * List.formPerm [2, 12, 9, 8, 3] *
    List.formPerm [4, 6, 10, 19, 15] * List.formPerm [7, 17, 13, 18, 16]

@[expose] def M21nat : Subgroup (Equiv.Perm (Fin 21)) := Subgroup.closure {m21gA, m21gB}

abbrev m21a : M21nat := ⟨m21gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m21b : M21nat := ⟨m21gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem rep_m21a : Rep 21 m21Data.tA m21a := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m21b : Rep 21 m21Data.tB m21b := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem m21_hyp : Hyp M21nat m21Data m21a m21b :=
  ⟨by norm_num, closure_pair_eq_top rfl _ _, rep_m21a, rep_m21b, m21_check⟩

theorem card_M21nat : Nat.card M21nat = 20160 := by
  rw [card_eq m21_hyp]
  rfl

theorem isSimpleGroup_M21nat : IsSimpleGroup M21nat :=
  isSimpleGroup_of_check m21_hyp (by decide) (by norm_num) (by norm_num [m21Data])
    (by norm_num [m21Data]) (by norm_num [m21Data]) (by decide) (by decide)

@[expose] def split21 : Fin 24 ≃ Fin 3 ⊕ Fin 21 where
  toFun i := if h : (i : ℕ) < 3 then .inl ⟨i, h⟩ else .inr ⟨i - 3, by omega⟩
  invFun s := match s with
    | .inl i => ⟨i, by have := i.2; omega⟩
    | .inr j => ⟨j + 3, by have := j.2; omega⟩
  left_inv := by decide
  right_inv := by decide

@[expose] def psi21 : Equiv.Perm (Fin 21) →* Equiv.Perm (Fin 24) where
  toFun g := (split21.trans (Equiv.sumCongr (Equiv.refl _) g)).trans split21.symm
  map_one' := Equiv.ext fun x => by
    simp only [Equiv.trans_apply, Equiv.Perm.one_apply]
    rcases h : split21 x with i | i <;> simp [← h]
  map_mul' g h := Equiv.ext fun x => by
    simp only [Equiv.trans_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
    rcases split21 x with i | i <;> rfl

theorem psi21_injective : Function.Injective psi21 := by
  intro g h hgh
  refine Equiv.ext fun i => ?_
  have := congrArg (fun σ : Equiv.Perm (Fin 24) => split21 (σ (split21.symm (.inr i)))) hgh
  simpa [psi21] using this

theorem psi21_apply_lt (g : Equiv.Perm (Fin 21)) (i : Fin 24) (hi : (i : ℕ) < 3) :
    psi21 g i = i := by
  change split21.symm (Equiv.sumCongr (Equiv.refl _) g (split21 i)) = i
  have h : split21 i = .inl ⟨i, hi⟩ := by simp [split21, hi]
  rw [h]
  rfl

theorem psi21_apply_ge (g : Equiv.Perm (Fin 21)) (i : Fin 24) (hi : 3 ≤ (i : ℕ)) :
    (psi21 g i : ℕ) = (g ⟨i - 3, by omega⟩ : ℕ) + 3 := by
  change (split21.symm (Equiv.sumCongr (Equiv.refl _) g (split21 i)) : ℕ) = _
  have h : split21 i = .inr ⟨i - 3, by omega⟩ := by simp [split21, show ¬ (i : ℕ) < 3 by omega]
  rw [h]
  rfl

theorem hasArr_psi21 {g : Equiv.Perm (Fin 21)} {a : Array ℕ} (h0 : a[0]! = 0) (h1 : a[1]! = 1)
    (h2 : a[2]! = 2) (h : ∀ j : Fin 21, (g j : ℕ) + 3 = a[(j : ℕ) + 3]!) : HasArr (psi21 g) a := by
  intro i
  by_cases hi : (i : ℕ) < 3
  · rw [psi21_apply_lt g i hi]
    interval_cases hv : (i : ℕ)
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
  · rw [psi21_apply_ge g i (by omega)]
    have := h ⟨i - 3, by omega⟩
    rw [show (i : ℕ) - 3 + 3 = i by omega] at this
    exact this

theorem psi21_a_arr : HasArr (psi21 m21gA) m21AArr :=
  hasArr_psi21 rfl rfl rfl (by decide)

theorem psi21_b_arr : HasArr (psi21 m21gB) m21BArr :=
  hasArr_psi21 rfl rfl rfl (by decide)

theorem m21_arrs_ok :
    inAutOK m21AArr = true ∧ inAutOK m21BArr = true :=
  Certificates.certificate7064.2

abbrev mog21 : Subgroup (Equiv.Perm (Fin 24)) := mog22 ⊓ stab 2

theorem mog21_le_mog22 : mog21 ≤ mog22 := inf_le_left

theorem mog21_le_mog22plus : mog21 ≤ mog22plus := mog21_le_mog22.trans mog22_le_mog22plus

theorem mem_mog21_of_hasArr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (h : inAutOK a = true) (h0 : a[0]! = 0) (h1 : a[1]! = 1) (h2 : a[2]! = 2) : σ ∈ mog21 :=
  ⟨mem_mog22_of_arr (mem_autPerm_of_hasArr hσ h) hσ h0 h1,
    (mem_stab_iff 2 σ).2 (hσ.apply_eq 2 h2)⟩

theorem card_mog22 :
    Nat.card mog22 = 443520 := by
  rw [Nat.card_congr mog22EquivM22.toEquiv, CFSG.Sporadic.Mathieu.card_M22]

theorem card_mog21 :
    Nat.card mog21 = 20160 := by
  have horb : MulAction.orbit ↥mog22 (2 : Fin 24) = {k | k ≠ 0 ∧ k ≠ 1} := by
    ext k
    constructor
    · rintro ⟨σ, rfl⟩
      have h0 : (σ : Equiv.Perm (Fin 24)) 0 = 0 := (mem_stab_iff 0 _).1 σ.2.1.2
      have h1 : (σ : Equiv.Perm (Fin 24)) 1 = 1 := (mem_stab_iff 1 _).1 σ.2.2
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h' : (σ : Equiv.Perm (Fin 24)) 2 = (σ : Equiv.Perm (Fin 24)) 0 := by
          rw [h0]
          exact h
        exact absurd ((σ : Equiv.Perm (Fin 24)).injective h') (by decide)
      · have h' : (σ : Equiv.Perm (Fin 24)) 2 = (σ : Equiv.Perm (Fin 24)) 1 := by
          rw [h1]
          exact h
        exact absurd ((σ : Equiv.Perm (Fin 24)).injective h') (by decide)
    · rintro ⟨hk0, hk1⟩
      obtain ⟨z, hz0, hz1, hzk⟩ : ∃ z : Fin 24, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ k := by
        by_cases hk : k = 2
        · exact ⟨3, by decide, by decide, by rw [hk]; decide⟩
        · exact ⟨2, by decide, by decide, fun h => hk h.symm⟩
      obtain ⟨τ, hτ, h0, h1, h2, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_four 0 1 k z
        (by decide) (Ne.symm hk0) (Ne.symm hz0) (Ne.symm hk1) (Ne.symm hz1) (Ne.symm hzk)
      exact ⟨⟨τ, ⟨⟨hτ, (mem_stab_iff 0 τ).2 h0⟩, (mem_stab_iff 1 τ).2 h1⟩⟩, h2⟩
  have hcard : (MulAction.orbit ↥mog22 (2 : Fin 24)).ncard = 22 := by
    rw [horb, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    rfl
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥mog22 (2 : Fin 24))
  rw [MulAction.index_stabilizer, hcard, card_mog22] at h1
  have h2 : mog21 = (MulAction.stabilizer ↥mog22 (2 : Fin 24)).map mog22.subtype := by
    ext σ
    constructor
    · rintro ⟨hσ, h2⟩
      exact ⟨⟨σ, hσ⟩, (mem_stab_iff 2 σ).1 h2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, (mem_stab_iff 2 _).2 hp⟩
  rw [h2, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  omega

theorem map_psi21_M21nat :
    M21nat.map psi21 = mog21 := by
  have hle : M21nat.map psi21 ≤ mog21 := by
    rw [M21nat, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with rfl | rfl
    · exact mem_mog21_of_hasArr psi21_a_arr m21_arrs_ok.1 rfl rfl rfl
    · exact mem_mog21_of_hasArr psi21_b_arr m21_arrs_ok.2 rfl rfl rfl
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_mog21, Subgroup.card_map_of_injective psi21_injective, card_M21nat]

@[expose] noncomputable def mog21EquivM21nat :
    ↥mog21 ≃* M21nat :=
  (MulEquiv.subgroupCongr map_psi21_M21nat.symm).trans
    (M21nat.equivMapOfInjective _ psi21_injective).symm

theorem commutator_eq_self_of_isSimpleGroup {G : Type*} [Group G] {H : Subgroup G}
    [IsSimpleGroup H] (hp : ¬ (Nat.card H).Prime) : (⁅H, H⁆ : Subgroup G) = H := by
  have hc : commutator ↥H = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥H) with h | h
    · exfalso
      have hcomm : ∀ a b : ↥H, a * b = b * a := fun a b => by
        have h1 : ⁅a, b⁆ ∈ commutator ↥H :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.1 h1
      let _ : CommGroup ↥H := { (inferInstance : Group ↥H) with mul_comm := hcomm }
      exact hp IsSimpleGroup.prime_card
    · exact h
  have h1 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← h1, hc, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

instance : IsSimpleGroup M21nat := isSimpleGroup_M21nat

theorem isSimpleGroup_mog21 :
    IsSimpleGroup ↥mog21 := mog21EquivM21nat.isSimpleGroup

theorem commutator_mog21 :
    ⁅mog21, mog21⁆ = mog21 := by
  have := isSimpleGroup_mog21
  refine commutator_eq_self_of_isSimpleGroup ?_
  rw [card_mog21]
  norm_num

instance :
    IsSimpleGroup NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2

theorem isSimpleGroup_mog22 :
    IsSimpleGroup ↥mog22 := mog22EquivM22.isSimpleGroup

theorem commutator_mog22 :
    ⁅mog22, mog22⁆ = mog22 := by
  have := isSimpleGroup_mog22
  refine commutator_eq_self_of_isSimpleGroup ?_
  rw [card_mog22]
  norm_num

theorem commutator_mem_stab_of_stabPair01 {σ τ : Equiv.Perm (Fin 24)} (hσ : σ ∈ stabPair01)
    (hτ : τ ∈ stabPair01) : ⁅σ, τ⁆ 0 = 0 ∧ ⁅σ, τ⁆ 1 = 1 := by
  have key : ∀ ρ ∈ stabPair01, (ρ 0 = 0 ∧ ρ 1 = 1 ∧ ρ⁻¹ 0 = 0 ∧ ρ⁻¹ 1 = 1) ∨
      (ρ 0 = 1 ∧ ρ 1 = 0 ∧ ρ⁻¹ 0 = 1 ∧ ρ⁻¹ 1 = 0) := by
    intro ρ hρ
    rcases hρ with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨h0, h1, by rw [Equiv.Perm.inv_eq_iff_eq, h0],
        by rw [Equiv.Perm.inv_eq_iff_eq, h1]⟩
    · exact Or.inr ⟨h0, h1, by rw [Equiv.Perm.inv_eq_iff_eq, h1],
        by rw [Equiv.Perm.inv_eq_iff_eq, h0]⟩
  simp only [commutatorElement_def, Equiv.Perm.mul_apply]
  rcases key σ hσ with ⟨a0, a1, c0, c1⟩ | ⟨a0, a1, c0, c1⟩ <;>
    rcases key τ hτ with ⟨b0, b1, d0, d1⟩ | ⟨b0, b1, d0, d1⟩ <;>
    simp only [a0, a1, b0, b1, c0, c1, d0, d1] <;> exact ⟨trivial, trivial⟩

theorem commutator_mog22plus_le : ⁅mog22plus, mog22plus⁆ ≤ mog22 := by
  rw [Subgroup.commutator_le]
  intro σ hσ τ hτ
  obtain ⟨h0, h1⟩ := commutator_mem_stab_of_stabPair01 hσ.2 hτ.2
  refine ⟨⟨?_, (mem_stab_iff 0 _).2 h0⟩, (mem_stab_iff 1 _).2 h1⟩
  rw [commutatorElement_def]
  exact AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.mul_mem hσ.1 hτ.1) (AutPerm.inv_mem hσ.1))
    (AutPerm.inv_mem hτ.1)

theorem perfectCore_mog22plus :
    perfectCore mog22plus = mog22 := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect mog22_le_mog22plus commutator_mog22)
  calc perfectCore mog22plus ≤ derivedSeriesOf mog22plus 1 := perfectCore_le_derivedSeriesOf _ 1
    _ = ⁅mog22plus, mog22plus⁆ := rfl
    _ ≤ mog22 := commutator_mog22plus_le

end CFSG.Quasithin.H.Mathieu
