module

public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.Fischer.F4
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Fischer
  CFSG.LieType.RootSystem CFSG.LieType.Universal.Unitary.SUExtras Matrix

theorem natCard_F4 : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card]
  norm_num

noncomputable abbrev su6σ : F4 ≃+* F4 := unitaryInvolution F4 2 1

theorem su6σ_apply (c : F4) : su6σ c = c * c := by
  rw [unitaryInvolution_apply, pow_one, sq]

theorem su6σ_su6σ (c : F4) : su6σ (su6σ c) = c := unitaryInvolution_involutive natCard_F4 c

abbrev SU6 : Type := SU su6σ 6

noncomputable abbrev su6D : UniversalRootDatum SU6 := rootDatum natCard_F4 6

theorem su6D_rootGroup (γ : Fin (6 / 2) → ℤ) :
    su6D.rootGroup γ = rootGroup su6σ su6σ_su6σ 6 γ := rfl

@[expose] def su6Fund : Fin 18 → Fin (6 / 2) → ℤ := ![![1, 2, 1], ![1, 1, 1], ![1, 1, 0],
  ![1, 0, 0], ![0, 1, 1], ![0, 1, 0], ![-1, -2, -1], ![-1, -1, -1], ![-1, -1, 0], ![-1, 0, 0],
  ![0, -1, -1], ![0, -1, 0], ![2, 2, 1], ![0, 2, 1], ![0, 0, 1], ![-2, -2, -1], ![0, -2, -1],
  ![0, 0, -1]]

@[expose] def su6Eps : Fin 18 → Fin (6 / 2) → ℤ := ![![1, 1, 0], ![1, 0, 1], ![1, 0, -1],
  ![1, -1, 0], ![0, 1, 1], ![0, 1, -1], ![-1, -1, 0], ![-1, 0, -1], ![-1, 0, 1], ![-1, 1, 0],
  ![0, -1, -1], ![0, -1, 1], ![2, 0, 0], ![0, 2, 0], ![0, 0, 2], ![-2, 0, 0], ![0, -2, 0],
  ![0, 0, -2]]

@[expose] def su6Pos : Fin 18 → Fin 6 × Fin 6 := ![(0, 4), (0, 3), (0, 2), (0, 1), (1, 3),
  (1, 2), (5, 1), (5, 2), (5, 3), (5, 4), (4, 2), (4, 3), (0, 5), (1, 4), (2, 3), (5, 0), (4, 1),
  (3, 2)]

@[expose] def su6Wt (i : Fin 6) : Fin (6 / 2) → ℤ := ![if i = 0 then 1 else if i = 5 then -1 else 0,
  if i = 1 then 1 else if i = 4 then -1 else 0, if i = 2 then 1 else if i = 3 then -1 else 0]

theorem toStd_six (v : Fin (6 / 2) → ℤ) : toStd 6 v = ![v 0, v 1 - v 0, 2 * v 2 - v 1] := by
  funext a
  have he : Even 6 := ⟨3, rfl⟩
  fin_cases a <;> simp [toStd, he, Symplectic.toStd]

theorem toStd_su6Fund (r : Fin 18) : toStd 6 (su6Fund r) = su6Eps r := by
  rw [toStd_six]
  fin_cases r <;> decide

theorem toStd_six_injective : Function.Injective (toStd 6) := by
  intro v w h
  rw [toStd_six, toStd_six] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp at h0 h1 h2
  funext a
  fin_cases a <;> simp <;> omega

theorem weight_six (i : Fin 6) : weight 6 i = su6Wt i := by
  funext a
  fin_cases i <;> fin_cases a <;> simp [weight, su6Wt]

theorem su6Wt_short : ∀ r : Fin 18, r.val < 12 →
    su6Wt (su6Pos r).1 - su6Wt (su6Pos r).2 = su6Eps r := by
  decide

theorem su6Wt_long : ∀ r : Fin 18, 12 ≤ r.val → 2 • su6Wt (su6Pos r).1 = su6Eps r := by
  decide

theorem su6Pos_ne : ∀ r : Fin 18, (su6Pos r).1 ≠ (su6Pos r).2 := by decide

theorem su6Pos_fst_ne_rev : ∀ r : Fin 18, (su6Pos r).1 ≠ Fin.rev (su6Pos r).1 := by decide

theorem su6Pos_snd_ne_rev : ∀ r : Fin 18, (su6Pos r).2 ≠ Fin.rev (su6Pos r).2 := by decide

theorem su6Pos_short_ne : ∀ r : Fin 18, r.val < 12 → (su6Pos r).2 ≠ Fin.rev (su6Pos r).1 := by
  decide

theorem su6Pos_long : ∀ r : Fin 18, 12 ≤ r.val → (su6Pos r).2 = Fin.rev (su6Pos r).1 := by
  decide

theorem su6Wt_roots :
    (∀ i j : Fin 6, i ≠ j → i ≠ Fin.rev i → j ≠ Fin.rev j → j ≠ Fin.rev i →
      ∃ r : Fin 18, r.val < 12 ∧ su6Wt i - su6Wt j = su6Eps r) ∧
    ∀ i : Fin 6, ∃ r : Fin 18, 12 ≤ r.val ∧ 2 • su6Wt i = su6Eps r := by
  decide

theorem mem_su6D_roots_iff (γ : Fin (6 / 2) → ℤ) :
    γ ∈ su6D.roots ↔ ∃ r, γ = su6Fund r := by
  change γ ∈ roots (isFiniteType_cartan 6) (divisible 6) ↔ _
  rw [roots_eq]
  simp only [Set.mem_ofPred_eq]
  have key : ∀ r : Fin 18, toStd 6 γ = su6Eps r → γ = su6Fund r := fun r h =>
    toStd_six_injective (h.trans (toStd_su6Fund r).symm)
  constructor
  · rintro (⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, -, h⟩ | ⟨he, -⟩)
    · obtain ⟨r, -, hr⟩ := su6Wt_roots.1 i j hij hi hj hji
      rw [weight_six, weight_six, hr] at h
      exact ⟨r, key r h⟩
    · obtain ⟨r, -, hr⟩ := su6Wt_roots.2 i
      rw [weight_six, hr] at h
      exact ⟨r, key r h⟩
    · exact absurd ⟨3, rfl⟩ he
  · rintro ⟨r, rfl⟩
    rw [toStd_su6Fund]
    by_cases hr : r.val < 12
    · refine Or.inl ⟨(su6Pos r).1, (su6Pos r).2, su6Pos_ne r, su6Pos_fst_ne_rev r,
        su6Pos_snd_ne_rev r, su6Pos_short_ne r hr, ?_⟩
      rw [weight_six, weight_six, su6Wt_short r hr]
    · refine Or.inr (Or.inl ⟨(su6Pos r).1, su6Pos_fst_ne_rev r, ?_⟩)
      rw [weight_six, su6Wt_long r (by omega)]

theorem su6Fund_injective : Function.Injective su6Fund := by decide

theorem su6Fund_mem_roots (r : Fin 18) : su6Fund r ∈ su6D.roots :=
  (mem_su6D_roots_iff _).2 ⟨r, rfl⟩

theorem F4.eq_iff_code (x y : F4) : x = y ↔ x.code = y.code := by
  cases x
  cases y
  simp

@[expose, instance_reducible] def f4DecEq : DecidableEq F4 := fun x y =>
  decidable_of_iff _ (F4.eq_iff_code x y).symm

attribute [local instance high] f4DecEq

theorem one_mem_traceZero_su6σ : (1 : F4) ∈ traceZero su6σ := by
  rw [mem_traceZero, su6σ_apply]
  decide

theorem mem_traceZero_su6σ_iff (c : F4) : c ∈ traceZero su6σ ↔ c = 0 ∨ c = 1 := by
  rw [mem_traceZero, su6σ_apply]
  revert c
  decide

@[expose] noncomputable def su6Elt (r : Fin 18) (c : F4) : SU6 :=
  if r.val < 12 then
    rootHom su6σ su6σ_su6σ (su6Pos_ne r) (su6Pos_fst_ne_rev r) (su6Pos_snd_ne_rev r)
      (Multiplicative.ofAdd c)
  else if c = 0 then 1
  else longRootHom su6σ (su6Pos_fst_ne_rev r) (Multiplicative.ofAdd ⟨1, one_mem_traceZero_su6σ⟩)

@[expose] noncomputable def su6Entry (r : Fin 18) (x : SU6) : F4 :=
  mat su6σ 6 x (su6Pos r).1 (su6Pos r).2

theorem su6Wt_not_long : ∀ (i : Fin 6) (r : Fin 18), r.val < 12 → 2 • su6Wt i ≠ su6Eps r := by
  decide

theorem su6Wt_not_short : ∀ (i j : Fin 6) (r : Fin 18), 12 ≤ r.val → j ≠ Fin.rev i →
    su6Wt i - su6Wt j ≠ su6Eps r := by
  decide

theorem su6Wt_long_eq : ∀ (i : Fin 6) (r : Fin 18), 12 ≤ r.val → 2 • su6Wt i = su6Eps r →
    i = (su6Pos r).1 := by
  decide

theorem fin6_rev_ne : ∀ k : Fin 6, Fin.rev k ≠ k := by decide

theorem rootMatrix_rev_rev {i j : Fin 6} (c : F4) :
    rootMatrix su6σ (Fin.rev j) (Fin.rev i) c = rootMatrix su6σ i j (-su6σ c) := by
  rw [rootMatrix, rootMatrix, Fin.rev_rev, Fin.rev_rev, map_neg, su6σ_su6σ,
    ← Matrix.single_neg, ← Matrix.single_neg]
  abel

theorem rootGroup_le_range_short {r : Fin 18} (hr : r.val < 12) :
    su6D.rootGroup (su6Fund r) ≤ (rootHom su6σ su6σ_su6σ (su6Pos_ne r) (su6Pos_fst_ne_rev r)
      (su6Pos_snd_ne_rev r)).range := by
  rw [su6D_rootGroup]
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
    rw [toStd_su6Fund, ← su6Wt_short r hr, ← weight_six, ← weight_six] at hw
    rcases eq_of_weight_sub_eq_sub (su6Pos_ne r) (su6Pos_fst_ne_rev r) (su6Pos_snd_ne_rev r)
      (su6Pos_short_ne r hr) hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_rfl
    · rintro _ ⟨c, rfl⟩
      refine ⟨Multiplicative.ofAdd (-su6σ (Multiplicative.toAdd c)), Subtype.ext (Units.ext ?_)⟩
      rw [coe_rootHom, coe_rootHom, rootMatrix_rev_rev]
      rfl
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rw [toStd_su6Fund, weight_six] at hw
    exact absurd hw (su6Wt_not_long i r hr)
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exact absurd hk (fin6_rev_ne k)

theorem rootGroup_le_range_long {r : Fin 18} (hr : 12 ≤ r.val) :
    su6D.rootGroup (su6Fund r) ≤ (longRootHom su6σ (su6Pos_fst_ne_rev r)).range := by
  rw [su6D_rootGroup]
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
    rw [toStd_su6Fund, weight_six, weight_six] at hw
    exact absurd hw (su6Wt_not_short i j r hr hji)
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rw [toStd_su6Fund, weight_six] at hw
    obtain rfl := su6Wt_long_eq i r hr hw
    exact le_rfl
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exact absurd hk (fin6_rev_ne k)

theorem rootMatrix_apply_pos (r : Fin 18) (hr : r.val < 12) (c : F4) :
    rootMatrix su6σ (su6Pos r).1 (su6Pos r).2 c (su6Pos r).1 (su6Pos r).2 = c := by
  have h1 := su6Pos_ne r
  have h2 : ¬(Fin.rev (su6Pos r).2 = (su6Pos r).1 ∧ Fin.rev (su6Pos r).1 = (su6Pos r).2) :=
    fun h => su6Pos_short_ne r hr h.2.symm
  simp [rootMatrix, one_apply_ne h1, h2]

theorem longRootMatrix_apply_pos (r : Fin 18) (c : F4) :
    longRootMatrix (su6Pos r).1 c (su6Pos r).1 (Fin.rev (su6Pos r).1) = c := by
  simp [longRootMatrix, one_apply_ne (su6Pos_fst_ne_rev r)]

theorem eq_su6Elt_entry {r : Fin 18} {x : SU6} (hx : x ∈ su6D.rootGroup (su6Fund r)) :
    x = su6Elt r (su6Entry r x) := by
  by_cases hr : r.val < 12
  · obtain ⟨c, rfl⟩ := rootGroup_le_range_short hr hx
    rw [su6Elt, ite_eq_left_of_eq_true _ _ (eq_true hr), su6Entry, mat_apply, coe_rootHom,
      rootMatrix_apply_pos r hr]
    rfl
  · obtain ⟨c, rfl⟩ := rootGroup_le_range_long (by omega : 12 ≤ r.val) hx
    have hpos := su6Pos_long r (by omega)
    rw [su6Elt, ite_eq_right_of_eq_false _ _ (eq_false hr), su6Entry, mat_apply, coe_longRootHom,
      hpos, longRootMatrix_apply_pos r]
    rcases (mem_traceZero_su6σ_iff _).1 (Multiplicative.toAdd c).2 with h | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      have : c = 1 := by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext h
      rw [this, map_one]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [h]; exact one_ne_zero))]
      congr 1
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h

theorem su6Elt_mem (r : Fin 18) (c : F4) : su6Elt r c ∈ su6D.rootGroup (su6Fund r) := by
  rw [su6D_rootGroup]
  unfold su6Elt
  split_ifs with hr hc
  · exact rootHom_mem su6σ_su6σ (su6Pos_ne r) (su6Pos_fst_ne_rev r) (su6Pos_snd_ne_rev r)
      (su6Pos_short_ne r hr) (by rw [toStd_su6Fund, weight_six, weight_six, su6Wt_short r hr]) _
  · exact Subgroup.one_mem _
  · exact longRootHom_mem su6σ_su6σ (su6Pos_fst_ne_rev r)
      (by rw [toStd_su6Fund, weight_six, su6Wt_long r (by omega)]) _

end CFSG.Sporadic.Co2Smith
