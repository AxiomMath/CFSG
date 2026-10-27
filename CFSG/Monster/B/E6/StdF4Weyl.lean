module

public import CFSG.LieType.Chevalley.C2E6NativeF4Coxeter
public import CFSG.Monster.B.Classical.E6Folded
public import CFSG.Monster.B.Geometry.Census

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.Monster.B.Classical CFSG.Monster.B.Geometry

abbrev NW :
    Type := relWeylTwist TwistTag.E6

abbrev ncs :
    CoxeterSystem CoxeterMatrix.F₄ NW := nativeCoxeterSystem

abbrev Lat : Type := Fin TwistTag.E6.tag.rank → ℤ

@[expose] def toLat (v : Fin 6 → ℤ) : Lat := v

@[expose] def wsmul
    (w : NW) (v : Fin 6 → ℤ) : Fin 6 → ℤ :=
  (w : WeylGroup TwistTag.E6.tag) • toLat v

theorem wsmul_mul
    (w w' : NW) (v : Fin 6 → ℤ) : wsmul (w * w') v = wsmul w (wsmul w' v) := by
  unfold wsmul
  rw [Subgroup.coe_mul, mul_smul]
  rfl

theorem wsmul_one
    (v : Fin 6 → ℤ) : wsmul 1 v = v := by
  unfold wsmul
  rw [OneMemClass.coe_one, one_smul]
  rfl

theorem fin4_cases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide

theorem wsmul_simple
    (i : Fin 4) (v : Fin 6 → ℤ) : wsmul (ncs.simple i) v = E6Folded.r i v := by
  unfold wsmul
  rw [nativeCoxeterSystem_simple, coe_nativeSimple, TwistTag.orbitReflection, wordProd_smul]
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · exact (E6Folded.s_eq_reflect 1 v).symm
  · exact (E6Folded.s_eq_reflect 3 v).symm
  · exact ((E6Folded.s_eq_reflect 2 (E6Folded.s 4 v)).trans
      (congrArg (reflect Tag.E6 (2 : Fin 6)) (E6Folded.s_eq_reflect 4 v))).symm
  · exact ((E6Folded.s_eq_reflect 0 (E6Folded.s 5 v)).trans
      (congrArg (reflect Tag.E6 (0 : Fin 6)) (E6Folded.s_eq_reflect 5 v))).symm

theorem wsmul_wordProd
    (ω : List (Fin 4)) (v : Fin 6 → ℤ) :
    wsmul (ncs.wordProd ω) v = ω.foldr E6Folded.r v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, wsmul_one, List.foldr_nil]
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, wsmul_mul, ih, wsmul_simple, List.foldr_cons]

theorem inOrbit_foldr (ω : List (Fin 4)) {v : Fin 6 → ℤ} (hv : E6Folded.InOrbit v) :
    E6Folded.InOrbit (ω.foldr E6Folded.r v) := by
  induction ω with
  | nil => exact hv
  | cons i ω ih => exact .step i ih

theorem inOrbit_wsmul
    (w : NW) {v : Fin 6 → ℤ} (hv : E6Folded.InOrbit v) :
    E6Folded.InOrbit (wsmul w v) := by
  obtain ⟨ω, rfl⟩ := ncs.wordProd_surjective w
  rw [wsmul_wordProd]
  exact inOrbit_foldr ω hv

@[expose] def weylPermFun
    (w : NW) (v : E6Folded.Λ) : E6Folded.Λ :=
  ⟨wsmul w v.1, inOrbit_wsmul w v.2⟩

theorem weylPermFun_mul
    (w w' : NW) (v : E6Folded.Λ) :
    weylPermFun (w * w') v = weylPermFun w (weylPermFun w' v) :=
  Subtype.ext (wsmul_mul w w' v.1)

theorem weylPermFun_one
    (v : E6Folded.Λ) : weylPermFun 1 v = v :=
  Subtype.ext (wsmul_one v.1)

@[expose] def weylPerm :
    NW →* Equiv.Perm E6Folded.Λ where
  toFun w :=
    { toFun := weylPermFun w
      invFun := weylPermFun w⁻¹
      left_inv := fun v => by rw [← weylPermFun_mul, inv_mul_cancel, weylPermFun_one]
      right_inv := fun v => by rw [← weylPermFun_mul, mul_inv_cancel, weylPermFun_one] }
  map_one' := Equiv.ext weylPermFun_one
  map_mul' w w' := Equiv.ext fun v => weylPermFun_mul w w' v

theorem coe_weylPerm_apply
    (w : NW) (v : E6Folded.Λ) : (weylPerm w v).1 = wsmul w v.1 :=
  rfl

theorem weylPerm_simple
    (i : Fin 4) : weylPerm (ncs.simple i) = E6Folded.gen i :=
  Equiv.ext fun v => Subtype.ext (wsmul_simple i v.1)

theorem weylPerm_wordProd
    (ω : List (Fin 4)) :
    weylPerm (ncs.wordProd ω) = E6Folded.wordProd ω := by
  induction ω with
  | nil => simp
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, map_mul, ih, weylPerm_simple,
      E6Folded.wordProd_cons]

theorem range_weylPerm :
    weylPerm.range = E6Folded.W := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    obtain ⟨ω, rfl⟩ := ncs.wordProd_surjective w
    rw [weylPerm_wordProd]
    exact E6Folded.wordProd_mem_W ω
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨ncs.simple i, weylPerm_simple i⟩

theorem mem_W_weylPerm
    (w : NW) : weylPerm w ∈ E6Folded.W :=
  range_weylPerm ▸ ⟨w, rfl⟩

theorem weylPerm_injective :
    Function.Injective weylPerm := by
  have hsurj : Function.Surjective (weylPerm.rangeRestrict) := MonoidHom.rangeRestrict_surjective _
  have hcard : Nat.card NW = Nat.card weylPerm.range := by
    rw [card_relWeylTwist_E6, range_weylPerm, E6Folded.card_W]
  have hbij := (Nat.bijective_iff_surjective_and_card _).2 ⟨hsurj, hcard⟩
  intro w w' h
  exact hbij.1 (Subtype.ext h)

theorem weylPerm_wordProd_eq_iff
    (ω : List (Fin 4)) (w : NW) :
    E6Folded.wordProd ω = weylPerm w ↔ ncs.wordProd ω = w := by
  rw [← weylPerm_wordProd]
  exact weylPerm_injective.eq_iff

theorem wordLength_weylPerm
    (w : NW) : E6Folded.wordLength (weylPerm w) = ncs.length w := by
  obtain ⟨ω, hred, hω⟩ := ncs.exists_isReduced w
  have hlen : ω.length = ncs.length w := by rw [hω]; exact hred.symm
  refine le_antisymm ?_ ?_
  · rw [← hlen]
    exact E6Folded.wordLength_le ((weylPerm_wordProd_eq_iff ω w).2 hω.symm)
  · have hne : {n | ∃ l : List (Fin 4), E6Folded.wordProd l = weylPerm w ∧ l.length = n}.Nonempty :=
      ⟨_, ω, (weylPerm_wordProd_eq_iff ω w).2 hω.symm, rfl⟩
    obtain ⟨l, hl, hlen'⟩ := Nat.sInf_mem hne
    have hl' := (weylPerm_wordProd_eq_iff l w).1 hl
    have := ncs.length_wordProd_le l
    rw [hl'] at this
    unfold E6Folded.wordLength
    omega

theorem isReducedWord_weylPerm_iff
    (w : NW) (ω : List (Fin 4)) :
    E6Folded.IsReducedWord (weylPerm w) ω ↔ ncs.IsReduced ω ∧ ncs.wordProd ω = w := by
  rw [E6Folded.IsReducedWord, weylPerm_wordProd_eq_iff, wordLength_weylPerm]
  constructor
  · rintro ⟨h, hlen⟩
    refine ⟨?_, h⟩
    rw [CoxeterSystem.IsReduced, h, hlen]
  · rintro ⟨hred, h⟩
    refine ⟨h, ?_⟩
    rw [← h]
    exact hred.symm

theorem weylWeight_eq_qWeight
    (w : NW) :
    weylWeight ncs E6Folded.letterWeight w = E6Folded.qWeight (weylPerm w) := by
  obtain ⟨hred, hω⟩ := (ncs.exists_isReduced w).choose_spec
  have hr : E6Folded.IsReducedWord (weylPerm w) (ncs.exists_isReduced w).choose :=
    (isReducedWord_weylPerm_iff w _).2 ⟨hred, hω.symm⟩
  rw [E6Folded.qWeight_eq_of_isReducedWord hr]
  rfl

theorem map_parabolic
    (S : Set (Fin 4)) :
    (ncs.parabolic S).map weylPerm = Subgroup.closure (E6Folded.gen '' S) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, CoxeterSystem.parabolic_le_iff]
    intro i hi
    rw [Subgroup.mem_comap, weylPerm_simple]
    exact Subgroup.subset_closure ⟨i, hi, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨ncs.simple i, ncs.simple_mem_parabolic hi, weylPerm_simple i⟩

theorem mem_parabolic_iff_weylPerm
    (S : Set (Fin 4)) (w : NW) :
    w ∈ ncs.parabolic S ↔ weylPerm w ∈ Subgroup.closure (E6Folded.gen '' S) := by
  rw [← map_parabolic]
  exact (Subgroup.mem_map_iff_mem weylPerm_injective).symm

theorem mem_parabolic_J_iff'
    (w : NW) : w ∈ ncs.parabolic E6Folded.J ↔ weylPerm w ∈ E6Folded.WJ :=
  mem_parabolic_iff_weylPerm E6Folded.J w

theorem mem_parabolic_K_iff'
    (w : NW) :
    w ∈ ncs.parabolic E6Folded.K ↔ weylPerm w ∈ E6Folded.WK :=
  mem_parabolic_iff_weylPerm E6Folded.K w

theorem mem_parabolic_J_iff
    (w : NW) :
    w ∈ ncs.parabolic E6Folded.J ↔ wsmul w E6Folded.θ = E6Folded.θ := by
  rw [mem_parabolic_J_iff', E6Folded.mem_WJ_iff_stabilizer]
  refine ⟨fun h => congrArg Subtype.val h.2, fun h => ⟨mem_W_weylPerm w, Subtype.ext h⟩⟩

@[expose] def level
    (w : NW) : ℤ :=
  E6Folded.form E6Folded.θ (wsmul w E6Folded.θ)

theorem level_eq
    (w : NW) : level w = E6Folded.form E6Folded.θ (weylPerm w E6Folded.θΛ).1 :=
  rfl

theorem level_mul_mul
    {u v : NW} (hu : u ∈ ncs.parabolic E6Folded.J)
    (hv : v ∈ ncs.parabolic E6Folded.J) (w : NW) : level (u * w * v) = level w := by
  rw [level_eq, level_eq, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  have hv' : weylPerm v E6Folded.θΛ = E6Folded.θΛ :=
    E6Folded.apply_θΛ_of_mem_WJ ((mem_parabolic_J_iff' v).1 hv)
  rw [hv']
  exact E6Folded.level_apply_of_mem_WJ ((mem_parabolic_J_iff' u).1 hu) _

theorem exists_mul_mul_of_level_eq
    {w w' : NW} (h : level w' = level w) :
    ∃ u ∈ ncs.parabolic E6Folded.J, ∃ v ∈ ncs.parabolic E6Folded.J, w' = u * w * v := by
  have hmem : weylPerm w' E6Folded.θΛ ∈ MulAction.orbit E6Folded.WJ (weylPerm w E6Folded.θΛ) := by
    rw [E6Folded.orbit_WJ]
    exact h
  obtain ⟨⟨x, hx⟩, hxw⟩ := hmem
  obtain ⟨u, rfl⟩ : ∃ u : NW, weylPerm u = x := by
    have : x ∈ weylPerm.range := range_weylPerm ▸ E6Folded.WJ_le_W hx
    exact this
  have hu : u ∈ ncs.parabolic E6Folded.J := (mem_parabolic_J_iff' u).2 hx
  refine ⟨u, hu, (u * w)⁻¹ * w', ?_, by rw [mul_inv_cancel_left]⟩
  rw [mem_parabolic_J_iff', E6Folded.mem_WJ_iff_stabilizer]
  refine ⟨mem_W_weylPerm _, ?_⟩
  rw [map_mul, map_inv, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq,
    Equiv.Perm.mul_apply]
  exact hxw.symm

theorem level_cases
    (w : NW) :
    level w = 2 ∨ level w = 1 ∨ level w = 0 ∨ level w = -1 ∨ level w = -2 := by
  have h : level w ∈ Set.range (fun α : E6Folded.Λ => E6Folded.form E6Folded.θ α.1) :=
    ⟨_, (level_eq w).symm⟩
  rw [E6Folded.range_level] at h
  simpa using h

theorem finsum_level_weylWeight
    (d : ℤ) :
    ∑ᶠ w ∈ {w : NW | level w = d}, weylWeight ncs E6Folded.letterWeight w =
      ∑ᶠ x ∈ {x : Equiv.Perm E6Folded.Λ | x ∈ E6Folded.W ∧
        E6Folded.form E6Folded.θ (x E6Folded.θΛ).1 = d}, E6Folded.qWeight x := by
  have himage : {x : Equiv.Perm E6Folded.Λ | x ∈ E6Folded.W ∧
      E6Folded.form E6Folded.θ (x E6Folded.θΛ).1 = d} = weylPerm '' {w : NW | level w = d} := by
    ext x
    constructor
    · rintro ⟨hx, hd⟩
      obtain ⟨w, rfl⟩ : ∃ w : NW, weylPerm w = x := (range_weylPerm ▸ hx : x ∈ weylPerm.range)
      exact ⟨w, hd, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨mem_W_weylPerm w, hw⟩
  rw [himage, finsum_mem_image weylPerm_injective.injOn]
  exact finsum_mem_congr rfl fun w _ => weylWeight_eq_qWeight w

theorem finsum_parabolic_J_weylWeight :
    ∑ᶠ w ∈ (ncs.parabolic E6Folded.J : Set NW), weylWeight ncs E6Folded.letterWeight w = 93555 := by
  have himage : (E6Folded.WJ : Set (Equiv.Perm E6Folded.Λ)) =
      weylPerm '' (ncs.parabolic E6Folded.J : Set NW) := by
    rw [← Subgroup.coe_map, map_parabolic]
    rfl
  rw [← E6Folded.finsum_qWeight_WJ, himage, finsum_mem_image weylPerm_injective.injOn]
  exact finsum_mem_congr rfl fun w _ => weylWeight_eq_qWeight w

theorem mem_double_coset_K_iff
    (w : NW) :
    (∃ a ∈ ncs.parabolic E6Folded.J, ∃ b ∈ ncs.parabolic E6Folded.K,
      ∃ c ∈ ncs.parabolic E6Folded.J, w = a * b * c) ↔
      level w = 2 ∨ level w = 1 ∨ level w = 0 := by
  have h := congrArg (fun S : Set (Equiv.Perm E6Folded.Λ) => weylPerm w ∈ S)
    E6Folded.double_coset_eq
  simp only [Set.mem_ofPred_eq, eq_iff_iff] at h
  rw [← level_eq] at h
  refine ⟨fun ⟨a, ha, b, hb, c, hc, hw⟩ => (h.1 ⟨weylPerm a, (mem_parabolic_J_iff' a).1 ha,
    weylPerm b, (mem_parabolic_K_iff' b).1 hb, weylPerm c, (mem_parabolic_J_iff' c).1 hc,
    by rw [hw, map_mul, map_mul]⟩).2, fun hl => ?_⟩
  obtain ⟨a, ha, b, hb, c, hc, hw⟩ := h.2 ⟨mem_W_weylPerm w, hl⟩
  obtain ⟨a', rfl⟩ : ∃ a' : NW, weylPerm a' = a :=
    (range_weylPerm ▸ E6Folded.WJ_le_W ha : a ∈ weylPerm.range)
  obtain ⟨b', rfl⟩ : ∃ b' : NW, weylPerm b' = b :=
    (range_weylPerm ▸ E6Folded.WK_le_W hb : b ∈ weylPerm.range)
  obtain ⟨c', rfl⟩ : ∃ c' : NW, weylPerm c' = c :=
    (range_weylPerm ▸ E6Folded.WJ_le_W hc : c ∈ weylPerm.range)
  refine ⟨a', (mem_parabolic_J_iff' a').2 ha, b', (mem_parabolic_K_iff' b').2 hb, c',
    (mem_parabolic_J_iff' c').2 hc, weylPerm_injective ?_⟩
  rw [hw, map_mul, map_mul]

end CFSG.Monster.B.E6.StdF4
