module

public import CFSG.Sporadic.Schreier.Co1WeightChar
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Schreier.Co1SplitLocal

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix CFSG.Blueprint CFSG.Sporadic.Mathieu

theorem MS.pow_phase {g : Mat24} {c : Fin 12 → ZMod 3} (h : MS g id c 1) (k : ℕ) :
    MS (g ^ k) id (fun j => (k : ZMod 3) * c j) 1 := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact MS.one.congr rfl (funext fun j => by simp) rfl
  | succ k ih =>
    rw [pow_succ]
    refine (ih.mul h).congr rfl (funext fun j => ?_) (funext fun j => by simp)
    simp only [id, Pi.one_apply, one_mul, Nat.cast_succ]
    ring

theorem MS.list_prod {ι : Type*} (l : List ι) (f : ι → GL24) (c : ι → Fin 12 → ZMod 3)
    (h : ∀ i, MS ((f i : GL24) : Mat24) id (c i) 1) :
    MS (((l.map f).prod : GL24) : Mat24) id (fun j => (l.map fun i => c i j).sum) 1 := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Units.val_one]
    exact MS.one.congr rfl (funext fun j => by simp) rfl
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul]
    exact ((h i).mul ih).congr rfl (funext fun j => by simp) (funext fun j => by simp)

theorem a_MS
    (i : Fin 6) : MS ((a i : GL24) : Mat24) id (fun j => γ j i) 1 := by
  have h := (msData_spec (isMS_a i).1).2
  rw [(msData_a i).1, (msData_a i).2] at h
  refine h.congr rfl (funext fun j => ?_) rfl
  have h1 := h j 0
  rw [ZMod.val_zero, pow_zero, one_mulVec, mul_zero, add_zero] at h1
  have h2 := a_mulVec_q i j
  rw [h1] at h2
  exact (zq_inj h2).2

theorem eProd_MS
    (b : Fin 6 → ZMod 3) :
    MS ((eProd b : GL24) : Mat24) id (fun j => ∑ i, b i * γ j i) 1 := by
  unfold eProd
  refine (MS.list_prod (List.finRange 6) (fun i => a i ^ (b i).val)
    (fun i j => ((b i).val : ZMod 3) * γ j i) fun i => ?_).congr rfl (funext fun j => ?_) rfl
  · rw [Units.val_pow_eq_pow_val]
    exact (a_MS i).pow_phase _
  · rw [Fin.sum_univ_def]
    simp only [ZMod.natCast_zmod_val]

theorem E_MS
    (x : E) : MS ((x : GL24) : Mat24) id (fun j => γ j ⬝ᵥ eExp x) 1 := by
  have h := eProd_MS (eExp x)
  rw [eProd_eExp] at h
  refine h.congr rfl (funext fun j => ?_) rfl
  rw [dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem conj_phase
    {c x y : GL24} {p : Fin 12 → Fin 12} {u ε β β' : Fin 12 → ZMod 3}
    (hc : MS (c : Mat24) p u ε) (hε : ∀ j, ε j * ε j = 1) (hx : MS (x : Mat24) id β 1)
    (hy : MS (y : Mat24) id β' 1) (hxy : c * y = x * c) : ∀ j, β' j = ε j * β (p j) := by
  have h1 := hc.mul hy
  have h2 := hx.mul hc
  rw [← Units.val_mul, hxy] at h1
  rw [← Units.val_mul] at h2
  have := (h1.unique h2).2.1
  intro j
  have hj := congrFun this j
  simp only [id, Pi.one_apply, one_mul] at hj
  linear_combination (ε j) * hj - (β' j) * hε j

theorem C_conj_mem
    {c e : GL24} (hc : c ∈ C) (he : e ∈ E) : c⁻¹ * e * c ∈ E := by
  have h := (Subgroup.mem_normalizer_iff.mp (A_le_normalizer (C_le_A (C.inv_mem hc))) e).mp he
  rwa [inv_inv] at h

@[expose] noncomputable def wStab :
    Subgroup GL24 where
  carrier := {c | c ∈ C ∧ ∀ e ∈ E, charV (γ 0) (c⁻¹ * e * c) = charV (γ 0) e}
  mul_mem' := by
    rintro c c' ⟨hc, h⟩ ⟨hc', h'⟩
    refine ⟨C.mul_mem hc hc', fun e he => ?_⟩
    have : (c * c')⁻¹ * e * (c * c') = c'⁻¹ * (c⁻¹ * e * c) * c' := by group
    rw [this, h' _ (C_conj_mem hc he), h e he]
  one_mem' := ⟨C.one_mem, fun e _ => by rw [inv_one, one_mul, mul_one]⟩
  inv_mem' := by
    rintro c ⟨hc, h⟩
    refine ⟨C.inv_mem hc, fun e he => ?_⟩
    have he' : c * e * c⁻¹ ∈ E := by
      have := C_conj_mem (C.inv_mem hc) he
      rwa [inv_inv] at this
    have := h _ he'
    have e1 : c⁻¹ * (c * e * c⁻¹) * c = e := by group
    rw [e1] at this
    rw [inv_inv, this]

theorem wStab_le_C :
    wStab ≤ C := fun _ h => h.1

theorem sign_sq {ε : ZMod 3} (h : ε ≠ 0) : ε * ε = 1 := by
  revert ε
  decide

theorem charV_E
    (x : E) : charV (γ 0) x = ω ^ (γ 0 ⬝ᵥ eExp x).val := by
  rw [charV_of_mem _ x.2]
  rfl

theorem mem_wStab_iff
    {c : GL24} (hc : c ∈ C) :
    c ∈ wStab ↔ (msData (c : Mat24)).1 0 = 0 ∧ (msData (c : Mat24)).2.2 0 = 1 := by
  obtain ⟨hs, hcMS⟩ := msData_spec (A_isMS c (C_le_A hc))
  set p := (msData (c : Mat24)).1
  set ε := (msData (c : Mat24)).2.2
  have hε : ∀ j, ε j * ε j = 1 := fun j => sign_sq (hs j)
  have key : ∀ e (he : e ∈ E), γ 0 ⬝ᵥ eExp ⟨c⁻¹ * e * c, C_conj_mem hc he⟩ =
      ε 0 * (γ (p 0) ⬝ᵥ eExp ⟨e, he⟩) := by
    intro e he
    have hy := E_MS ⟨c⁻¹ * e * c, C_conj_mem hc he⟩
    have hx := E_MS ⟨e, he⟩
    have hxy : c * (c⁻¹ * e * c) = e * c := by group
    exact conj_phase hcMS hε hx hy hxy 0
  have hiff : c ∈ wStab ↔ ∀ b : Fin 6 → ZMod 3, ε 0 * (γ (p 0) ⬝ᵥ b) = γ 0 ⬝ᵥ b := by
    constructor
    · rintro ⟨-, h⟩ b
      have h1 := h _ (eProd_mem b)
      rw [charV_E ⟨_, C_conj_mem hc (eProd_mem b)⟩, charV_E ⟨_, eProd_mem b⟩] at h1
      have h2 := ω_pow_val_inj h1
      rw [key _ (eProd_mem b), eExp_eProd] at h2
      exact h2
    · intro h
      refine ⟨hc, fun e he => ?_⟩
      rw [charV_E ⟨_, C_conj_mem hc he⟩, charV_E ⟨_, he⟩, key e he, h]
  rw [hiff]
  constructor
  · intro h
    have h0 := h (Pi.single 0 1)
    simp only [dotProduct_single, mul_one] at h0
    rw [γ_zero, γ_zero, mul_one] at h0
    refine ⟨?_, h0⟩
    apply γ_injective
    funext i
    have := h (Pi.single i 1)
    simp only [dotProduct_single, mul_one, h0, one_mul] at this
    exact this
  · rintro ⟨h1, h2⟩ b
    rw [h1, h2, one_mul]

theorem signedMatrix_pattern {p : Fin 12 → Fin 12} {ε : Fin 12 → ZMod 3} (hε : ∀ j, ε j ≠ 0)
    (i j : Fin 12) : signedMatrix p ε i j ≠ 0 ↔ i = p j := by
  simp only [signedMatrix, Matrix.of_apply]
  by_cases h : i = p j
  · simp only [h, ↓reduceIte, iff_true, ne_eq]
    exact hε j
  · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false]

theorem lineMap_signedMatrix
    {p : Fin 12 → Fin 12} {ε : Fin 12 → ZMod 3} (hε : ∀ j, ε j ≠ 0)
    (j : Fin 12) : lineMap (signedMatrix p ε) j = p j :=
  lineMap_eq fun i => signedMatrix_pattern hε i j

theorem signedMatrix_inj
    {p p' : Fin 12 → Fin 12} {ε ε' : Fin 12 → ZMod 3}
    (hε : ∀ j, ε j ≠ 0) (hε' : ∀ j, ε' j ≠ 0) (h : signedMatrix p ε = signedMatrix p' ε') :
    p = p' ∧ ε = ε' := by
  have hp : p = p' := funext fun j => by
    rw [← lineMap_signedMatrix (p := p) hε j, ← lineMap_signedMatrix (p := p') hε' j, h]
  subst hp
  refine ⟨rfl, funext fun j => ?_⟩
  have := congrFun (congrFun h (p j)) j
  simpa only [signedMatrix, Matrix.of_apply, ↓reduceIte] using this

theorem cEquiv_val
    (c : C) : ((cEquiv c : GL12) : Mat12) =
    signedMatrix (msData ((c : GL24) : Mat24)).1 (msData ((c : GL24) : Mat24)).2.2 := by
  rw [cEquiv_apply c (C_le_A c.2), proj_val]

theorem cPerm_apply
    (c : C) (j : Fin 12) : cPerm c j = (msData ((c : GL24) : Mat24)).1 j := by
  change qPerm (cEquiv c) j = _
  rw [qPerm_apply, cEquiv_val,
    lineMap_signedMatrix (msData_spec (A_isMS _ (C_le_A c.2))).1]

@[expose] noncomputable def wPerm :
    wStab →* Equiv.Perm (Fin 12) :=
  cPerm.comp (Subgroup.inclusion wStab_le_C)

theorem wPerm_apply
    (x : wStab) (j : Fin 12) :
    wPerm x j = (msData ((x : GL24) : Mat24)).1 j :=
  cPerm_apply _ j

theorem wPerm_injective :
    Function.Injective wPerm := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxC : (Subgroup.inclusion wStab_le_C x) ∈ cPerm.ker := hx
  rw [cPerm_ker_iff] at hxC
  have hx0 := (mem_wStab_iff (wStab_le_C x.2)).mp x.2
  rw [Subgroup.mem_bot]
  rcases hxC with h | h
  · have : Subgroup.inclusion wStab_le_C x = 1 :=
      cEquiv.injective (by rw [map_one]; exact Subtype.ext h)
    exact Subtype.ext (show (x : GL24) = 1 from congrArg Subtype.val this)
  · exfalso
    have hm := cEquiv_val (Subgroup.inclusion wStab_le_C x)
    rw [h, neg_one_val] at hm
    have := congrFun (congrFun hm 0) 0
    change (-1 : Mat12) 0 0 = signedMatrix (msData ((x : GL24) : Mat24)).1
      (msData ((x : GL24) : Mat24)).2.2 0 0 at this
    simp only [signedMatrix, Matrix.of_apply, hx0.1, ↓reduceIte, hx0.2] at this
    revert this
    decide

theorem cPerm_range' :
    cPerm.range = m12Conj := cPerm_range

@[expose] noncomputable def m12ConjStab : Subgroup (Equiv.Perm (Fin 12)) :=
  m12Conj ⊓ MulAction.stabilizer (Equiv.Perm (Fin 12)) (0 : Fin 12)

@[expose] noncomputable def zC :
    C := cEquiv.symm ⟨-1, neg_one_mem_Q⟩

theorem cEquiv_zC :
    cEquiv zC = ⟨-1, neg_one_mem_Q⟩ := MulEquiv.apply_symm_apply _ _

theorem cPerm_eq
    (c : C) : cPerm c = qPerm (cEquiv c) := rfl

theorem wPerm_range :
    wPerm.range = m12ConjStab := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← cPerm_range']
      exact ⟨_, rfl⟩
    · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, wPerm_apply]
      exact ((mem_wStab_iff (wStab_le_C x.2)).mp x.2).1
  · intro m hm
    obtain ⟨hm, hm0⟩ := Subgroup.mem_inf.mp hm
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hm0
    rw [← cPerm_range'] at hm
    obtain ⟨c, rfl⟩ := hm
    have hs := (msData_spec (A_isMS _ (C_le_A c.2))).1
    have hp0 : (msData ((c : GL24) : Mat24)).1 0 = 0 := by rw [← cPerm_apply]; exact hm0
    by_cases h1 : (msData ((c : GL24) : Mat24)).2.2 0 = 1
    · exact ⟨⟨c, (mem_wStab_iff c.2).mpr ⟨hp0, h1⟩⟩, rfl⟩
    ·
      have hc' : ((c * zC : C) : GL24) ∈ wStab := by
        rw [mem_wStab_iff (c * zC).2]
        have hs' := (msData_spec (A_isMS _ (C_le_A (c * zC).2))).1
        have hm' := cEquiv_val (c * zC)
        rw [map_mul, cEquiv_zC, Subgroup.coe_mul, Units.val_mul, cEquiv_val,
          show (((⟨-1, neg_one_mem_Q⟩ : Q) : GL12) : Mat12) = signedMatrix id (fun _ => 2) from
            (neg_one_val.trans signedMatrix_two.symm), signedMatrix_mul] at hm'
        obtain ⟨hp, hε⟩ := signedMatrix_inj hs'
          (fun j => mul_ne_zero (hs j) (by decide)) hm'.symm
        refine ⟨by rw [hp]; exact hp0, ?_⟩
        rw [hε]
        have h2 : (msData ((c : GL24) : Mat24)).2.2 0 = 2 := by
          have := hs 0
          generalize (msData ((c : GL24) : Mat24)).2.2 0 = s at this h1 ⊢
          revert s
          decide
        change (msData ((c : GL24) : Mat24)).2.2 (id 0) * 2 = 1
        rw [id, h2]
        decide
      refine ⟨⟨_, hc'⟩, ?_⟩
      change cPerm (c * zC) = cPerm c
      rw [map_mul, cPerm_eq zC, cEquiv_zC, qPerm_neg_one, mul_one]

@[expose] def m11Relabel : Equiv.Perm (Fin 11) where
  toFun i := Fin.ofNat 11 ([7, 5, 4, 0, 8, 1, 9, 3, 10, 2, 6].getD i.val 0)
  invFun i := Fin.ofNat 11 ([3, 5, 9, 7, 2, 1, 10, 0, 4, 6, 8].getD i.val 0)
  left_inv := by decide
  right_inv := by decide

@[expose] def m11Points : Fin 11 ≃ {x : Fin 12 // x ≠ 0} := m11Relabel.trans (finSuccAboveEquiv 0)

@[expose] def m11Hom : Equiv.Perm (Fin 11) →* Equiv.Perm (Fin 12) :=
  Equiv.Perm.extendDomainHom m11Points

@[expose] def m12Word (w : List ℕ) : Equiv.Perm (Fin 12) :=
  (w.map fun l => if l = 1 then m12gA else m12gB).prod

theorem m11Hom_gens : m11Hom m11gA = m12Word [2, 1, 2, 2] ∧
    m11Hom m11gB = m12Word [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2,
      1, 2, 1, 2, 2] := by
  constructor <;> decide +kernel

theorem m12Word_mem (w : List ℕ) : m12Word w ∈ NativeSporadic.M12 := by
  unfold m12Word
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
  rw [m12_eq]
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem m11Hom_injective : Function.Injective m11Hom := Equiv.Perm.extendDomainHom_injective _

theorem m11Hom_fix (m : Equiv.Perm (Fin 11)) : m11Hom m 0 = 0 :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ (not_not.mpr rfl)

@[expose] noncomputable def m12Stab : Subgroup (Equiv.Perm (Fin 12)) :=
  NativeSporadic.M12 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 12)) (0 : Fin 12)

theorem m12Stab_eq_map :
    m12Stab = (MulAction.stabilizer NativeSporadic.M12 (0 : Fin 12)).map
      NativeSporadic.M12.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxM, hx0⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.mk_smul]
    exact hx0
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def] at hy
    exact Subgroup.mem_inf.mpr ⟨y.2, hy⟩

theorem card_m12Stab : Nat.card m12Stab = 7920 := by
  have h2 := isMultiplyPretransitive_two m12_hyp (by decide) (by norm_num)
  have : MulAction.IsPretransitive NativeSporadic.M12 (Fin 12) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rw [m12Stab_eq_map, Subgroup.card_map_of_injective NativeSporadic.M12.subtype_injective,
    card_stabilizer_eq (0 : Fin 12) (by simp), card_M12, Nat.card_fin]

theorem map_m11Hom :
    NativeSporadic.M11.map m11Hom = m12Stab := by
  have hle : NativeSporadic.M11.map m11Hom ≤ m12Stab := by
    rw [m11_eq, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [m11Hom_gens.1]; exact m12Word_mem _
      · rw [MulAction.mem_stabilizer_iff]; exact m11Hom_fix _
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [m11Hom_gens.2]; exact m12Word_mem _
      · rw [MulAction.mem_stabilizer_iff]; exact m11Hom_fix _
  have : Finite m12Stab := Nat.finite_of_card_ne_zero (by rw [card_m12Stab]; norm_num)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_m12Stab, Subgroup.card_map_of_injective m11Hom_injective, card_M11]

theorem coordBij_zero : coordBij 0 = 0 := Fin.ext (coordBij_apply 0)

theorem m12ConjStab_eq : m12ConjStab = m12Stab.map (MulAut.conj coordBij).toMonoidHom := by
  have hinv : coordBij⁻¹ 0 = 0 := by
    rw [Equiv.Perm.inv_eq_iff_eq, coordBij_zero]
  ext m
  constructor
  · intro hm
    obtain ⟨hmC, hm0⟩ := Subgroup.mem_inf.mp hm
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hmC
    refine ⟨n, Subgroup.mem_inf.mpr ⟨hn, ?_⟩, rfl⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hm0 ⊢
    change (coordBij * n * coordBij⁻¹) 0 = 0 at hm0
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv] at hm0
    rw [← coordBij_zero] at hm0
    exact coordBij.injective hm0
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨hnM, hn0⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ hnM, ?_⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hn0 ⊢
    change (coordBij * n * coordBij⁻¹) 0 = 0
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hn0, coordBij_zero]

theorem card_m12ConjStab : Nat.card m12ConjStab = 7920 := by
  rw [m12ConjStab_eq, Subgroup.card_map_of_injective (MulAut.conj coordBij).injective,
    card_m12Stab]

theorem m11_commutator_eq_top :
    commutator NativeSporadic.M11 = ⊤ := by
  have := fam_m11_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator NativeSporadic.M11) with h | h
  · exfalso
    have hc := (commutator_eq_bot_iff _).mp h
    have h1 := congrArg Subtype.val (hc.is_comm.comm m11a m11b)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
    revert h1
    decide +kernel
  · exact h

theorem m12ConjStab_commutator :
    ⁅m12ConjStab, m12ConjStab⁆ = m12ConjStab := by
  rw [m12ConjStab_eq, ← map_m11Hom, Subgroup.map_map, ← Subgroup.map_commutator,
    ← Subgroup.map_subtype_commutator, m11_commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem card_wStab :
    Nat.card wStab = 7920 := by
  rw [← card_m12ConjStab, ← wPerm_range]
  refine Nat.card_eq_of_bijective (fun x => (⟨wPerm x, x, rfl⟩ : wPerm.range)) ⟨?_, ?_⟩
  · intro x y h
    exact wPerm_injective (congrArg Subtype.val h)
  · rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩

theorem commutator_wStab :
    commutator wStab = ⊤ := by
  apply Subgroup.map_injective wPerm_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, wPerm_range,
    m12ConjStab_commutator]

theorem wStab_hom_eq_one
    {K : Type*} [Field K] (φ : wStab →* Kˣ) : φ = 1 := by
  have h := Abelianization.commutator_subset_ker φ
  rw [commutator_wStab] at h
  ext x
  have := h (Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at this
  rw [this]
  rfl

end CFSG.Sporadic.Co1Schreier
