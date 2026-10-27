module

public import CFSG.Monster.VisQuot.Image
public import CFSG.Monster.VisQuot.Words

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisCert
open scoped commutatorElement

abbrev EH : Subgroup Hvis := Evis.subgroupOf Hvis

abbrev JH : Subgroup Hvis := Subgroup.normalClosure (EH : Set Hvis)

theorem mem_JH_of_mem_Evis
    {x : Hvis} (hx : (x : GLV) ∈ Evis) : x ∈ JH :=
  Subgroup.subset_normalClosure hx

theorem conj_mem_JH (x : Hvis) {y : Hvis} (hy : y ∈ JH) : x * y * x⁻¹ ∈ JH :=
  Subgroup.normalClosure_normal.conj_mem y hy x

theorem kGenH_mem_JH_of_three_le {j : Fin 15} (hj : 3 ≤ (j : ℕ)) :
    (⟨kGen j, kGen_mem_Hvis j⟩ : Hvis) ∈ JH :=
  mem_JH_of_mem_Evis (Subgroup.subset_closure ⟨j, hj, rfl⟩)

@[expose] def xiH : Hvis := ⟨kGen 0, kGen_mem_Hvis 0⟩

theorem xiH_mem_JH : xiH ∈ JH := by
  have e3 : (⟨kGen 3, kGen_mem_Hvis 3⟩ : Hvis) ∈ JH := kGenH_mem_JH_of_three_le (by decide)
  have h : xiH = xiH⁻¹ * ⟨kGen 3, kGen_mem_Hvis 3⟩ * xiH⁻¹⁻¹ * ⟨kGen 3, kGen_mem_Hvis 3⟩ := by
    rw [inv_inv]
    exact Subtype.ext kGen_zero_eq
  rw [h]
  exact JH.mul_mem (conj_mem_JH _ e3) e3

@[expose] def permHomH : AutPerm →* Hvis :=
  permHom.codRestrict Hvis fun p => modTwoUnit_mem_Hvis (PO_mem_PvisLat p)

theorem coe_permHomH (p : AutPerm) : (permHomH p : GLV) = permHom p := rfl

theorem permHomH_betaAut_mem_JH : permHomH betaAut ∈ JH := by
  have e9 : (⟨kGen 9, kGen_mem_Hvis 9⟩ : Hvis) ∈ JH := kGenH_mem_JH_of_three_le (by decide)
  have h : permHomH betaAut = xiH * ⟨kGen 9, kGen_mem_Hvis 9⟩ * xiH⁻¹ :=
    Subtype.ext conj_kGen_nine.symm
  rw [h]
  exact conj_mem_JH _ e9

theorem permHomH_mem_JH (p : AutPerm) : permHomH p ∈ JH := by
  have hN : (JH.comap permHomH).Normal := Subgroup.Normal.comap inferInstance _
  rcases AutPerm_isSimpleGroup.eq_bot_or_eq_top_of_normal (JH.comap permHomH) with h | h
  · have hb : betaAut ∈ JH.comap permHomH := permHomH_betaAut_mem_JH
    rw [h] at hb
    exact absurd (Subgroup.mem_bot.1 hb) betaAut_ne_one
  · have hp : p ∈ JH.comap permHomH := by
      rw [h]
      exact Subgroup.mem_top p
    exact hp

theorem kGenH_mem_JH
    (j : Fin 15) : (⟨kGen j, kGen_mem_Hvis j⟩ : Hvis) ∈ JH := by
  rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ 3 ≤ (j : ℕ) by omega) with h | h | h | h
  · obtain rfl : j = 0 := Fin.ext h
    exact xiH_mem_JH
  · obtain rfl : j = 1 := Fin.ext h
    have e : (⟨kGen 1, kGen_mem_Hvis 1⟩ : Hvis) = permHomH pAAut := Subtype.ext kGen_one
    rw [e]
    exact permHomH_mem_JH _
  · obtain rfl : j = 2 := Fin.ext h
    have e : (⟨kGen 2, kGen_mem_Hvis 2⟩ : Hvis) = permHomH pBAut := Subtype.ext kGen_two
    rw [e]
    exact permHomH_mem_JH _
  · exact kGenH_mem_JH_of_three_le h

theorem JH_eq_top : JH = ⊤ := by
  have hK : Kvis ≤ JH.map Hvis.subtype := by
    show Subgroup.closure (Set.range kGen) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨_, kGenH_mem_JH j, rfl⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hK (Hvis_eq_Kvis.le x.2)
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

theorem closure_conj_Evis :
    Subgroup.closure {u : GLV | ∃ h ∈ Hvis, ∃ e ∈ Evis, u = h * e * h⁻¹} = Hvis := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨h, hh, e, he, rfl⟩
    exact Hvis.mul_mem (Hvis.mul_mem hh (Evis_le_Hvis he)) (Hvis.inv_mem hh)
  · intro x hx
    have h1 : (⟨x, hx⟩ : Hvis) ∈ Subgroup.closure (Group.conjugatesOfSet (EH : Set Hvis)) := by
      have : (⟨x, hx⟩ : Hvis) ∈ JH := JH_eq_top ▸ Subgroup.mem_top _
      exact this
    have h2 := Subgroup.mem_map_of_mem Hvis.subtype h1
    rw [MonoidHom.map_closure] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hay
    exact ⟨c, c.2, a, ha, rfl⟩

@[expose] def signH (a : C) : Hvis := ⟨modTwoUnit (gO a), modTwoUnit_mem_Hvis (gO_mem_PvisLat a)⟩

theorem signH_add (a b : C) : signH (a + b) = signH b * signH a :=
  Subtype.ext (by
    show modTwoUnit (gO (a + b)) = modTwoUnit (gO b) * modTwoUnit (gO a)
    rw [gO_add, modTwoUnit_mul])

theorem signH_zero : signH 0 = 1 := Subtype.ext (by
  show modTwoUnit (gO 0) = 1
  rw [gO_zero, modTwoUnit_one])

theorem signH_ΩC : signH ΩC = 1 := Subtype.ext (by
  show modTwoUnit (gO ΩC) = 1
  rw [gO_ΩC]
  exact (modTwoUnit_eq_one_iff _).2 (.inr rfl))

theorem commutatorElement_signH (d : C) (p : AutPerm) :
    ⁅signH d, permHomH p⁆ = signH (d + permC p d) :=
  Subtype.ext (commutatorElement_gO_permHom d p)

theorem commutatorElement_mem (x y : Hvis) : ⁅x, y⁆ ∈ commutator Hvis := by
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

theorem signH_congr {a b : C} (h : (a : Fin 24 → ZMod 2) = b) : signH a = signH b :=
  congrArg signH (Subtype.ext h)

theorem signH_mk_add {x y : Fin 24 → ZMod 2} (hx : x ∈ C) (hy : y ∈ C) (h : x + y ∈ C) :
    signH ⟨x + y, h⟩ = signH ⟨y, hy⟩ * signH ⟨x, hx⟩ :=
  signH_add ⟨x, hx⟩ ⟨y, hy⟩

theorem signH_mem_commutator_of_span {x : Fin 24 → ZMod 2}
    (hx : x ∈ Submodule.span (ZMod 2) bridgeDiffSet) :
    signH ⟨x, Submodule.span_le.2 bridgeDiffSet_subset_C hx⟩ ∈ commutator Hvis := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, j, rfl⟩ := hx
    obtain ⟨q, hq⟩ : ∃ q : AutPerm, (q : Equiv.Perm (Fin 24)) = p := by
      rcases hp with rfl | rfl
      · exact ⟨pAAut, pA_eq_bridgePA⟩
      · exact ⟨pBAut, pB_eq_bridgePB⟩
    convert commutatorElement_mem (signH (bC j)) (permHomH q) using 1
    rw [commutatorElement_signH]
    exact signH_congr (by
      show B j + permWord p (B j) = B j + permWord (q : Equiv.Perm (Fin 24)) (B j)
      rw [hq])
  | zero =>
    convert Subgroup.one_mem (commutator Hvis) using 1
    exact signH_zero
  | add x y hx hy ihx ihy =>
    convert Subgroup.mul_mem _ ihy ihx using 1
    exact signH_mk_add _ _ _
  | smul c x hx ihx =>
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · convert Subgroup.one_mem (commutator Hvis) using 1
      exact (signH_congr (zero_smul _ _)).trans signH_zero
    · convert ihx using 1
      exact signH_congr (one_smul _ _)

theorem signH_mem_commutator (a : C) : signH a ∈ commutator Hvis := by
  have ha : (a : Fin 24 → ZMod 2) ∈
      Submodule.span (ZMod 2) bridgeDiffSet ⊔ Submodule.span (ZMod 2) {Ω} :=
    span_bridgeDiffSet_sup.ge a.2
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ha
  have hzC : z ∈ C := Submodule.span_le.2 (Set.singleton_subset_iff.2 Ω_mem_C) hz
  have hz' : (⟨z, hzC⟩ : C) = 0 ∨ (⟨z, hzC⟩ : C) = ΩC := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · exact .inl (Subtype.ext (zero_smul _ _))
    · exact .inr (Subtype.ext (one_smul _ _))
  have e : a = ⟨y, Submodule.span_le.2 bridgeDiffSet_subset_C hy⟩ + ⟨z, hzC⟩ :=
    Subtype.ext hyz.symm
  have hz1 : signH ⟨z, hzC⟩ = 1 := by
    rcases hz' with h | h <;> rw [h]
    · exact signH_zero
    · exact signH_ΩC
  rw [e, signH_add, hz1, one_mul]
  exact signH_mem_commutator_of_span hy

theorem EH_le_commutator : EH ≤ commutator Hvis := fun x hx => by
  have hx' : (x : GLV) ∈ Esign := Evis_eq_Esign ▸ hx
  obtain ⟨a, ha⟩ := mem_Esign.1 hx'
  have e : x = signH a := Subtype.ext ha.symm
  rw [e]
  exact signH_mem_commutator a

theorem commutator_Hvis_eq_top :
    commutator Hvis = ⊤ :=
  eq_top_iff.2 (JH_eq_top.symm.le.trans (Subgroup.normalClosure_le_normal EH_le_commutator))

theorem commutator_Hvis :
    ⁅Hvis, Hvis⁆ = Hvis := by
  rw [← Subgroup.map_subtype_commutator, commutator_Hvis_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem visible_code_sign_normal_generation :
    Subgroup.normalClosure ((Evis.subgroupOf Hvis : Subgroup Hvis) : Set Hvis) = ⊤ ∧
    Subgroup.closure {u : GLV | ∃ h ∈ Hvis, ∃ e ∈ Evis, u = h * e * h⁻¹} = Hvis ∧
    commutator Hvis = ⊤ ∧ ⁅Hvis, Hvis⁆ = Hvis ∧
    kGen 0 ^ 3 = 1 ∧ kGen 0 = (kGen 0)⁻¹ * kGen 3 * kGen 0 * kGen 3 ∧
    kGen 0 * kGen 9 * (kGen 0)⁻¹ = permHom betaAut ∧ betaAut ≠ 1 ∧
    (∀ (d : C) (p : AutPerm), ⁅modTwoUnit (gO d), permHom p⁆ = modTwoUnit (gO (d + permC p d))) ∧
    Evis.subgroupOf Hvis ≤ commutator Hvis :=
  ⟨JH_eq_top, closure_conj_Evis, commutator_Hvis_eq_top, commutator_Hvis, kGen_zero_pow_three,
    kGen_zero_eq, conj_kGen_nine, betaAut_ne_one, commutatorElement_gO_permHom, EH_le_commutator⟩

end CFSG.Monster.VisQuot
