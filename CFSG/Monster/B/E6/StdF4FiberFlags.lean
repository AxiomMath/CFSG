module

public import CFSG.Monster.B.E6.StdF4FiberCount

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Matrix Module
open CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def flagSub
    (k : Fin 3) (p : nativeParabolic firstJ) : Submodule K (Fin 6 → K) :=
  (residueFlag (QuotientGroup.mk p)).sub k

abbrev parSU
    (p : nativeParabolic firstJ) : SU6 := suOf (leviProj two_mem_firstJ p)

theorem flagSub_mul
    (k : Fin 3) (p q : nativeParabolic firstJ) :
    flagSub k (p * q) = (flagSub k q).map (suLin (parSU p) : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) := by
  have h := residueFlag_smul p (psiA_suOf (leviProj two_mem_firstJ p)) (QuotientGroup.mk q)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h
  rw [flagSub, flagSub, h, smul_sub]

theorem flagSub_one
    (k : Fin 3) : flagSub k 1 = baseFlag.sub k := by
  rw [flagSub, residueFlag_one]

theorem flagSub_mul_of_eq
    {k : Fin 3} (p q : nativeParabolic firstJ)
    (hq : flagSub k q = baseFlag.sub k) : flagSub k (p * q) = flagSub k p := by
  rw [flagSub_mul, hq, ← flagSub_one k, ← flagSub_mul, mul_one]

theorem flagSub_of_mem_stdBorel
    (k : Fin 3) {p : nativeParabolic firstJ}
    (hp : (p : ModGL Tag.E6 K) ∈ stdBorel) : flagSub k p = baseFlag.sub k := by
  have e : (QuotientGroup.mk p : ParabolicCosets firstJ) = QuotientGroup.mk 1 :=
    QuotientGroup.eq.2 (by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one,
        mul_one]
      exact inv_mem hp)
  rw [flagSub, e, residueFlag_one]

theorem flagSub_mul_left_of_mem_stdRadical
    (k : Fin 3) {u : nativeParabolic firstJ}
    (hu : (u : ModGL Tag.E6 K) ∈ stdRadical firstJ) (p : nativeParabolic firstJ) :
    flagSub k (u * p) = flagSub k p := by
  have h := (smul_eq_self_iff u).2 hu (QuotientGroup.mk p)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h
  rw [flagSub, flagSub, h]

@[expose] def flagStabP
    (k : Fin 3) : Subgroup (nativeParabolic firstJ) where
  carrier := {p | flagSub k p = baseFlag.sub k}
  mul_mem' {p q} hp hq := by
    change flagSub k (p * q) = _
    rw [flagSub_mul_of_eq p q hq]
    exact hp
  one_mem' := flagSub_one k
  inv_mem' {p} hp := by
    change flagSub k p⁻¹ = _
    have hinj : Function.Injective (Submodule.map
        (suLin (parSU p) : (Fin 6 → K) →ₗ[K] (Fin 6 → K))) :=
      Submodule.map_injective_of_injective (suLin (parSU p)).injective
    have h1 := flagSub_mul k p p⁻¹
    have h2 := flagSub_mul k p 1
    rw [mul_inv_cancel, flagSub_one] at h1
    rw [mul_one, flagSub_one] at h2
    have hp' : flagSub k p = baseFlag.sub k := hp
    exact hinj (h1.symm.trans (hp'.symm.trans h2))

theorem mem_flagStabP
    {k : Fin 3} {p : nativeParabolic firstJ} :
    p ∈ flagStabP k ↔ flagSub k p = baseFlag.sub k :=
  Iff.rfl

@[expose] def flagStab
    (k : Fin 3) : Subgroup (ModGL Tag.E6 K) :=
  (flagStabP k).map (nativeParabolic firstJ).subtype

theorem mem_flagStab
    {k : Fin 3} {g : ModGL Tag.E6 K} :
    g ∈ flagStab k ↔ ∃ hg : g ∈ nativeParabolic firstJ, flagSub k ⟨g, hg⟩ = baseFlag.sub k := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem stdBorel_le_flagStab
    (k : Fin 3) : stdBorel ≤ flagStab k := fun _ hb =>
  mem_flagStab.2 ⟨stdBorel_le_nativeParabolic firstJ hb, flagSub_of_mem_stdBorel k hb⟩

theorem flagStab_le_stdGroup
    (k : Fin 3) : flagStab k ≤ stdGroup := by
  rintro _ ⟨p, -, rfl⟩
  exact nativeParabolic_le_stdGroup firstJ p.2

theorem nativeRep_not_mem_stdBorel
    (i : Fin 4) : nativeRep i ∉ stdBorel := by
  intro h
  have h' := stdBorel_le_nativeParabolic ∅ h
  rw [nativeRep_mem_nativeParabolic_iff] at h'
  exact h'

theorem nativeRep_mem_singleton
    (i : Fin 4) : nativeRep i ∈ nativeParabolic {i} :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl, rfl⟩)

theorem nativeRep_mem_flagStab_iff
    (k : Fin 3) (i : Fin 4) :
    nativeRep i ∈ flagStab k ↔ i ∈ firstJ ∧ typeDim i ≠ k := by
  constructor
  · intro h
    obtain ⟨hP, hk⟩ := mem_flagStab.1 h
    have hi : i ∈ firstJ := (nativeRep_mem_nativeParabolic_iff firstJ i).1 hP
    refine ⟨hi, fun hik => ?_⟩
    have hagree := (mem_nativeParabolic_singleton_iff hi 1 ⟨nativeRep i, hP⟩).1 (by
      rw [inv_one, one_mul]
      exact nativeRep_mem_singleton i)
    have hF : residueFlag (QuotientGroup.mk (1 : nativeParabolic firstJ)) =
        residueFlag (QuotientGroup.mk ⟨nativeRep i, hP⟩) := by
      refine IsoFlag6.ext (funext fun k' => ?_)
      by_cases hk' : k' = typeDim i
      · rw [hk', hik, residueFlag_one]
        exact hk.symm
      · exact hagree k' hk'
    have e := QuotientGroup.eq.1 (residueFlag.injective hF)
    rw [Subgroup.mem_subgroupOf, inv_one, one_mul] at e
    exact nativeRep_not_mem_stdBorel i e
  · rintro ⟨hi, hik⟩
    have hP : nativeRep i ∈ nativeParabolic firstJ :=
      (nativeRep_mem_nativeParabolic_iff firstJ i).2 hi
    have hagree := (mem_nativeParabolic_singleton_iff hi 1 ⟨nativeRep i, hP⟩).1 (by
      rw [inv_one, one_mul]
      exact nativeRep_mem_singleton i)
    refine mem_flagStab.2 ⟨hP, ?_⟩
    rw [flagSub, ← hagree k (Ne.symm hik), residueFlag_one]

theorem flagStab_eq
    (k : Fin 3) :
    flagStab k = nativeParabolic {i | i ∈ firstJ ∧ typeDim i ≠ k} := by
  obtain ⟨I, hI⟩ := exists_eq_nativeParabolic (stdBorel_le_flagStab k) (flagStab_le_stdGroup k)
  have hI' : I = {i | i ∈ firstJ ∧ typeDim i ≠ k} := by
    ext i
    rw [← nativeRep_mem_nativeParabolic_iff, ← hI, nativeRep_mem_flagStab_iff]
    rfl
  rw [hI, hI']

@[expose] def fibKd : Fin 5 → Fin 3 := ![2, 2, 0, 2, 2]

@[expose] def IsMid (d : Fin 5) : Prop := d = 1 ∨ d = 2 ∨ d = 3

theorem flagStab_fibKd
    {d : Fin 5} (hd : IsMid d) :
    flagStab (fibKd d) = nativeParabolic (fibIF d : Set (Fin 4)) := by
  rw [flagStab_eq]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, firstJ, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rcases hd with rfl | rfl | rfl <;> fin_cases i <;> decide

theorem flagSub_eq_flagSub_iff
    {k : Fin 3} (p p' : nativeParabolic firstJ) :
    flagSub k p = flagSub k p' ↔ p⁻¹ * p' ∈ flagStabP k := by
  rw [mem_flagStabP]
  constructor
  · intro h
    rw [flagSub_mul, ← h, ← flagSub_mul, inv_mul_cancel, flagSub_one]
  · intro h
    rw [← flagSub_mul_of_eq p (p⁻¹ * p') h, mul_inv_cancel_left]

theorem mem_flagStabP_iff_mem
    {k : Fin 3} {I : Set (Fin 4)} (hk : flagStab k = nativeParabolic I)
    (p : nativeParabolic firstJ) :
    p ∈ flagStabP k ↔ (p : ModGL Tag.E6 K) ∈ nativeParabolic I := by
  rw [← hk]
  exact ⟨fun h => ⟨p, h, rfl⟩, fun ⟨q, hq, e⟩ => (Subtype.ext e : q = p) ▸ hq⟩

theorem flagSub_eq_iff_mem
    {k : Fin 3} {I : Set (Fin 4)} (hk : flagStab k = nativeParabolic I)
    (p p' : nativeParabolic firstJ) :
    flagSub k p = flagSub k p' ↔ ((p⁻¹ * p' : nativeParabolic firstJ) : ModGL Tag.E6 K) ∈
      nativeParabolic I := by
  rw [flagSub_eq_flagSub_iff, mem_flagStabP_iff_mem hk]

@[expose] def isoSubs (k : Fin 3) : Set (Submodule K (Fin 6 → K)) :=
  {S | finrank K S = k + 1 ∧ ∀ v ∈ S, ∀ w ∈ S, herm6 v w = 0}

theorem sub_mem_isoSubs (F : IsoFlag6) (k : Fin 3) : F.sub k ∈ isoSubs k := by
  refine ⟨F.finrank_sub k, fun v hv w hw => ?_⟩
  have hk : k ≤ 2 := Fin.le_iff_val_le_val.2 (by omega)
  exact F.isotropic v (F.mono hk hv) w (F.mono hk hw)

theorem flagSub_mem_isoSubs
    (k : Fin 3) (p : nativeParabolic firstJ) : flagSub k p ∈ isoSubs k :=
  sub_mem_isoSubs _ k

theorem exists_SU6_map_eq {U U' : Submodule K (Fin 6 → K)}
    (hU : ∀ v ∈ U, ∀ w ∈ U, herm6 v w = 0) (hU' : ∀ v ∈ U', ∀ w ∈ U', herm6 v w = 0)
    (h : finrank K U = finrank K U') :
    ∃ g : SU6, U.map (suLin g : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) = U' := by
  obtain ⟨g, hg, hgU⟩ := (isotropic_flag_extension unitaryFieldData_K form6_isSymm
    form6_separatingLeft (Module.finrank_fin_fun K)).2.2 U U'
    (fun x hx y hy => by rw [← herm6_eq_form6]; exact hU y hy x hx)
    (fun x hx y hy => by rw [← herm6_eq_form6]; exact hU' y hy x hx) h
  set M := Matrix.GeneralLinearGroup.toLin.symm g with hM
  have hgM : g = Matrix.GeneralLinearGroup.toLin M := by rw [hM, MulEquiv.apply_symm_apply]
  rw [hgM, toLin_mem_sesqSpecialUnitaryGroup_iff, mem_gramSU, coe_unitaryFieldData_K_bar] at hg
  let hSL : SpecialLinearGroup (Fin 6) K := ⟨M, hg.2⟩
  have hSU : hSL ∈ SU6 := (mem_SU6_iff hSL).mpr hg.1
  refine ⟨⟨hSL, hSU⟩, ?_⟩
  rw [← hgU, hgM]
  rfl

theorem exists_flagSub_eq
    {k : Fin 3} {S : Submodule K (Fin 6 → K)} (hS : S ∈ isoSubs k) :
    ∃ p : nativeParabolic firstJ, flagSub k p = S := by
  obtain ⟨g, hg⟩ := exists_SU6_map_eq (sub_mem_isoSubs baseFlag k).2 hS.2
    ((baseFlag.finrank_sub k).trans hS.1.symm)
  obtain ⟨x, hx⟩ := residueFlag.surjective (g • baseFlag)
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨p, by rw [flagSub, hx, smul_sub, hg]⟩

theorem range_flagSub
    (k : Fin 3) : Set.range (flagSub k) = isoSubs k :=
  Set.ext fun _ => ⟨fun ⟨p, hp⟩ => hp ▸ flagSub_mem_isoSubs k p, exists_flagSub_eq⟩

@[expose] def flagSubQ
    (k : Fin 3) : nativeParabolic firstJ ⧸ flagStabP k →
    Submodule K (Fin 6 → K) :=
  Quotient.lift (flagSub k) fun a b hab =>
    (flagSub_eq_flagSub_iff a b).2 (QuotientGroup.leftRel_apply.1 hab)

theorem flagSubQ_injective
    (k : Fin 3) : Function.Injective (flagSubQ k) := by
  intro x y h
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  exact QuotientGroup.eq.2 ((flagSub_eq_flagSub_iff a b).1 h)

theorem range_flagSubQ
    (k : Fin 3) : Set.range (flagSubQ k) = isoSubs k := by
  rw [← range_flagSub]
  exact Set.ext fun S => ⟨fun ⟨x, hx⟩ => by
    induction x using QuotientGroup.induction_on with | H a => exact ⟨a, hx⟩,
    fun ⟨a, ha⟩ => ⟨QuotientGroup.mk a, ha⟩⟩

theorem ncard_isoSubs_eq
    {k : Fin 3} {I : Set (Fin 4)} (hk : flagStab k = nativeParabolic I) :
    (isoSubs k).ncard * Nat.card (nativeParabolic I) = 3 * 2 ^ 36 * 93555 := by
  have h1 : (isoSubs k).ncard = (flagStabP k).index := by
    rw [← range_flagSubQ, Set.ncard_range_of_injective (flagSubQ_injective k)]
    rfl
  have h2 : Nat.card (flagStabP k) = Nat.card (nativeParabolic I) := by
    rw [← hk, flagStab, Nat.card_congr ((flagStabP k).equivMapOfInjective
      (nativeParabolic firstJ).subtype (nativeParabolic firstJ).subtype_injective).toEquiv]
  rw [h1, ← h2, mul_comm, Subgroup.card_mul_index, card_nativeParabolic_firstJ]

theorem ncard_isoSubs_two :
    (isoSubs 2).ncard = 891 := by
  have h : (isoSubs 2).ncard * Nat.card (nativeParabolic (fibIF 1 : Set (Fin 4))) = _ :=
    ncard_isoSubs_eq (flagStab_fibKd (d := 1) (Or.inl rfl))
  have h23 : ∑ᶠ w ∈ (ncs.parabolic (fibIF 1 : Set (Fin 4)) : Set NW),
      weylWeight ncs E6Folded.letterWeight w = 105 := finsum_parabolic_23
  rw [card_nativeParabolic, h23] at h
  have e : (3 * 2 ^ 36 * 93555 : ℕ) = 891 * (3 * 2 ^ 36 * 105) := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem ncard_isoSubs_zero :
    (isoSubs 0).ncard = 693 := by
  have h : (isoSubs 0).ncard * Nat.card (nativeParabolic (fibIF 2 : Set (Fin 4))) = _ :=
    ncard_isoSubs_eq (flagStab_fibKd (d := 2) (Or.inr (Or.inl rfl)))
  have h12 : ∑ᶠ w ∈ (ncs.parabolic (fibIF 2 : Set (Fin 4)) : Set NW),
      weylWeight ncs E6Folded.letterWeight w = 135 := finsum_parabolic_12
  rw [card_nativeParabolic, h12] at h
  have e : (3 * 2 ^ 36 * 93555 : ℕ) = 693 * (3 * 2 ^ 36 * 135) := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end CFSG.Monster.B.E6.StdF4
