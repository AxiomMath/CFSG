module

public import CFSG.Sporadic.Schreier.TitsLocal
public import CFSG.Sporadic.Schreier.TitsActionCheck
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped Pointwise

section Induced

variable {G X ι : Type*} [Group G] [MulAction G X] [Finite ι] {f : ι → X}

@[expose] def MapsRange (f : ι → X) (g : G) : Prop := ∀ i, ∃ j, f j = g • f i

theorem MapsRange.inv (hf : Function.Injective f) {g : G} (hg : MapsRange f g) :
    MapsRange f g⁻¹ := by
  choose φ hφ using hg
  have hinj : Function.Injective φ := fun i i' h => by
    apply hf
    have e : g • f i = g • f i' := by rw [← hφ i, ← hφ i', h]
    exact smul_left_cancel g e
  intro i
  obtain ⟨i', hi'⟩ := Finite.injective_iff_surjective.1 hinj i
  exact ⟨i', by rw [← hi', hφ i', inv_smul_smul]⟩

theorem mapsRange_closure (hf : Function.Injective f) {T : Set G}
    (hT : ∀ t ∈ T, MapsRange f t) : ∀ g ∈ Subgroup.closure T, MapsRange f g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht => exact hT t ht
  | one => exact fun i => ⟨i, by rw [one_smul]⟩
  | mul g h _ _ hg hh =>
    intro i
    obtain ⟨j, hj⟩ := hh i
    obtain ⟨k, hk⟩ := hg j
    exact ⟨k, by rw [hk, hj, mul_smul]⟩
  | inv g _ hg => exact hg.inv hf

@[expose] def indPerm (hf : Function.Injective f) {g : G} (hg : MapsRange f g) :
    Equiv.Perm ι :=
  Equiv.ofBijective (fun i => Classical.choose (hg i))
    (Finite.injective_iff_bijective.1 fun i i' h => by
      apply hf
      have e : g • f i = g • f i' := by
        rw [← Classical.choose_spec (hg i), ← Classical.choose_spec (hg i')]
        exact congrArg f h
      exact smul_left_cancel g e)

theorem f_indPerm (hf : Function.Injective f) {g : G} (hg : MapsRange f g) (i : ι) :
    f (indPerm hf hg i) = g • f i :=
  Classical.choose_spec (hg i)

@[expose] def indFun (H : Subgroup G) (hf : Function.Injective f)
    (hH : ∀ g ∈ H, MapsRange f g) (g : H) : Equiv.Perm ι :=
  indPerm hf (hH g g.2)

theorem f_indFun {H : Subgroup G} (hf : Function.Injective f) (hH : ∀ g ∈ H, MapsRange f g)
    (g : H) (i : ι) : f (indFun H hf hH g i) = (g : G) • f i :=
  f_indPerm hf _ i

@[expose] def indHom (H : Subgroup G) (hf : Function.Injective f)
    (hH : ∀ g ∈ H, MapsRange f g) : H →* Equiv.Perm ι where
  toFun := indFun H hf hH
  map_one' := Equiv.ext fun i => hf (by
    rw [f_indFun hf hH, Subgroup.coe_one, one_smul, Equiv.Perm.one_apply])
  map_mul' g h := Equiv.ext fun i => hf (by
    rw [Equiv.Perm.mul_apply, f_indFun hf hH, f_indFun hf hH, f_indFun hf hH, Subgroup.coe_mul,
      mul_smul])

theorem f_indHom {H : Subgroup G} (hf : Function.Injective f) (hH : ∀ g ∈ H, MapsRange f g)
    (g : H) (i : ι) : f (indHom H hf hH g i) = (g : G) • f i :=
  f_indFun hf hH g i

theorem indHom_eq_of {H : Subgroup G} (hf : Function.Injective f)
    (hH : ∀ g ∈ H, MapsRange f g) {g : H} {π : Equiv.Perm ι}
    (h : ∀ i, f (π i) = (g : G) • f i) : indHom H hf hH g = π :=
  Equiv.ext fun i => hf ((f_indHom hf hH g i).trans (h i).symm)

end Induced

theorem titsP_rep
    {i : ℕ} (hi : i < 4) : Rep 8775 titsFlagArrs[i]! (titsP i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsLocalData_check.1]; exact hi)

theorem titsAStar_rep
    {i : ℕ} (hi : i < 4) : Rep 2925 titsAStarArrs[i]! (titsAStar i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsLocalData_check.2.1]; exact hi)

theorem titsBetaArr_lt
    {j : ℕ} (hj : j < 8775) : titsBetaArr[j]! < 1755 :=
  of_decide_eq_true
    (allLt_spec titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hj)

theorem titsKappaArr_lt
    {j : ℕ} (hj : j < 8775) : titsKappaArr[j]! < 2925 :=
  of_decide_eq_true
    (allLt_spec titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hj)

theorem titsBeta_val
    (j : Fin 8775) : (titsBeta j : ℕ) = titsBetaArr[(j : ℕ)]! :=
  finPt_val (titsBetaArr_lt j.2)

theorem titsKappa_val
    (j : Fin 8775) : (titsKappa j : ℕ) = titsKappaArr[(j : ℕ)]! :=
  finPt_val (titsKappaArr_lt j.2)

theorem titsBeta_titsP
    {i : ℕ} (hi : i < 4) (j : Fin 8775) :
    titsBeta (titsP i j) = titsGen i (titsBeta j) := by
  apply Fin.ext
  rw [titsBeta_val, ← titsP_rep hi j, titsLines_check.1 i hi j j.2, ← titsBeta_val,
    titsGen_rep hi]

theorem titsKappa_titsP
    {i : ℕ} (hi : i < 4) (j : Fin 8775) :
    titsKappa (titsP i j) = titsAStar i (titsKappa j) := by
  apply Fin.ext
  rw [titsKappa_val, ← titsP_rep hi j, titsLines_check.2.1 i hi j j.2, ← titsKappa_val,
    titsAStar_rep hi]

@[expose] def titsLine (v : Fin 2925) : Finset (Fin 1755) :=
  (Finset.univ.filter fun j : Fin 8775 => titsKappa j = v).image titsBeta

@[expose] def titsLinePt (v : Fin 2925) (k : ℕ) : Fin 1755 :=
  finPt 1755 titsLinePtArr[3 * (v : ℕ) + k]!

theorem titsLinePt_val (v : Fin 2925) {k : ℕ} (hk : k < 3) :
    (titsLinePt v k : ℕ) = titsLinePtArr[3 * (v : ℕ) + k]! := by
  have h := titsLines_check.2.2.2.1 v v.2
  apply finPt_val
  interval_cases k <;> first | omega | (rw [Nat.add_zero]; omega)

@[expose] def titsLineFlag (v : Fin 2925) (k : ℕ) : Fin 8775 :=
  finPt 8775 titsLineFlagArr[3 * (v : ℕ) + k]!

theorem titsLineFlag_spec
    (v : Fin 2925) {k : ℕ} (hk : k < 3) :
    titsKappa (titsLineFlag v k) = v ∧ titsBeta (titsLineFlag v k) = titsLinePt v k := by
  obtain ⟨hlt, hκ, hβ⟩ := titsLines_check.2.2.1 v v.2 k hk
  have hval : (titsLineFlag v k : ℕ) = titsLineFlagArr[3 * (v : ℕ) + k]! := finPt_val hlt
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · rw [titsKappa_val, hval, hκ]
  · rw [titsBeta_val, hval, hβ, titsLinePt_val v hk]

theorem titsLineFlag_pos
    (j : Fin 8775) :
    ∃ k < 3, titsLineFlag (titsKappa j) k = j ∧ titsLinePt (titsKappa j) k = titsBeta j := by
  obtain ⟨hk, hj⟩ := titsLines_check.2.2.2.2.1 j j.2
  have hflag : titsLineFlag (titsKappa j)
      (titsLinePos titsKappaArr[(j : ℕ)]! titsBetaArr[(j : ℕ)]!) = j := by
    apply Fin.ext
    rw [titsLineFlag, titsKappa_val, finPt_val (by rw [hj]; exact j.2), hj]
  refine ⟨_, hk, hflag, ?_⟩
  rw [← (titsLineFlag_spec (titsKappa j) hk).2, hflag]

theorem titsLine_eq (v : Fin 2925) :
    titsLine v = {titsLinePt v 0, titsLinePt v 1, titsLinePt v 2} := by
  ext x
  simp only [titsLine, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨k, hk, -, hpt⟩ := titsLineFlag_pos j
    rw [hj] at hpt
    rw [← hpt]
    interval_cases k <;> simp
  · intro hx
    have key : ∀ k < 3, x = titsLinePt v k → ∃ j, titsKappa j = v ∧ titsBeta j = x :=
      fun k hk e => ⟨titsLineFlag v k, (titsLineFlag_spec v hk).1,
        e ▸ (titsLineFlag_spec v hk).2⟩
    rcases hx with h | h | h
    · exact key 0 (by norm_num) h
    · exact key 1 (by norm_num) h
    · exact key 2 (by norm_num) h

theorem titsLinePt_lt (v : Fin 2925) :
    titsLinePt v 0 < titsLinePt v 1 ∧ titsLinePt v 1 < titsLinePt v 2 := by
  obtain ⟨h1, h2, -⟩ := titsLines_check.2.2.2.1 v v.2
  rw [Fin.lt_def, Fin.lt_def, titsLinePt_val v (by norm_num), titsLinePt_val v (by norm_num),
    titsLinePt_val v (by norm_num)]
  exact ⟨by simpa using h1, h2⟩

theorem triple_eq_of_eq {n : ℕ} {a b c a' b' c' : Fin n} (h₁ : a < b) (h₂ : b < c)
    (h₁' : a' < b') (h₂' : b' < c') (h : ({a, b, c} : Finset (Fin n)) = {a', b', c'}) :
    a = a' ∧ b = b' ∧ c = c' := by
  have mem : ∀ x, x ∈ ({a, b, c} : Finset (Fin n)) ↔ x ∈ ({a', b', c'} : Finset (Fin n)) := by
    intro x; rw [h]
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  have ha := (mem a).1 (by simp)
  have hb := (mem b).1 (by simp)
  have hc := (mem c).1 (by simp)
  have ha' := (mem a').2 (by simp)
  have hb' := (mem b').2 (by simp)
  have hc' := (mem c').2 (by simp)
  rw [Fin.lt_def] at h₁ h₂ h₁' h₂'
  simp only [Fin.ext_iff] at ha hb hc ha' hb' hc' ⊢
  omega

theorem titsLineKey_eq (v : Fin 2925) :
    titsLineKey v = ((titsLinePt v 0 : ℕ) * 1755 + (titsLinePt v 1 : ℕ)) * 1755 +
      (titsLinePt v 2 : ℕ) := by
  rw [titsLineKey, titsLinePt_val v (by norm_num), titsLinePt_val v (by norm_num),
    titsLinePt_val v (by norm_num)]
  simp

theorem titsLine_injective :
    Function.Injective titsLine := by
  intro v w h
  rw [titsLine_eq, titsLine_eq] at h
  obtain ⟨hv1, hv2⟩ := titsLinePt_lt v
  obtain ⟨hw1, hw2⟩ := titsLinePt_lt w
  obtain ⟨e0, e1, e2⟩ := triple_eq_of_eq hv1 hv2 hw1 hw2 h
  have hkey : titsLineKey v = titsLineKey w := by rw [titsLineKey_eq, titsLineKey_eq, e0, e1, e2]
  have hnd : ((List.range 2925).map titsLineKey).Nodup := by
    have hp := List.mergeSort_perm ((List.range 2925).map titsLineKey)
      (fun a b => decide (a ≤ b))
    exact hp.nodup_iff.1 (titsLines_check.2.2.2.2.2.imp ne_of_lt)
  exact Fin.ext (List.inj_on_of_nodup_map hnd (List.mem_range.2 v.2) (List.mem_range.2 w.2) hkey)

theorem titsGen_smul_titsLine
    {i : ℕ} (hi : i < 4) (v : Fin 2925) :
    titsGen i • titsLine v = titsLine (titsAStar i v) := by
  rw [Finset.smul_finset_def, titsLine, titsLine, Finset.image_image]
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
    Equiv.Perm.smul_def]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨titsP i j, by rw [titsKappa_titsP hi, hj], titsBeta_titsP hi j⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(titsP i)⁻¹ j, ?_, ?_⟩
    · apply (titsAStar i).injective
      rw [← titsKappa_titsP hi, perm_apply_inv, hj]
    · rw [← titsBeta_titsP hi, perm_apply_inv]

theorem titsLine_mapsRange :
    ∀ g ∈ titsA, MapsRange titsLine g :=
  mapsRange_closure titsLine_injective (by
    rintro _ ⟨i, rfl⟩ v
    exact ⟨_, (titsGen_smul_titsLine i.2 v).symm⟩)

@[expose] def titsLineHom :
    titsA →* Equiv.Perm (Fin 2925) :=
  indHom titsA titsLine_injective titsLine_mapsRange

theorem titsLine_lineHom
    (g : titsA) (v : Fin 2925) :
    titsLine (titsLineHom g v) = (g : Equiv.Perm (Fin 1755)) • titsLine v :=
  f_indHom _ _ g v

theorem titsLineHom_gen
    {i : ℕ} (hi : i < 4) :
    titsLineHom ⟨titsGen i, titsGen_mem_titsA hi⟩ = titsAStar i :=
  indHom_eq_of _ _ fun v => (titsGen_smul_titsLine hi v).symm

@[expose] def titsFlagPair (j : Fin 8775) : Fin 1755 × Finset (Fin 1755) :=
  (titsBeta j, titsLine (titsKappa j))

theorem titsFlagPair_injective :
    Function.Injective titsFlagPair := by
  intro j j' h
  simp only [titsFlagPair, Prod.mk.injEq] at h
  obtain ⟨hβ, hL⟩ := h
  have hκ := titsLine_injective hL
  obtain ⟨k, hk, hj, hpt⟩ := titsLineFlag_pos j
  obtain ⟨k', hk', hj', hpt'⟩ := titsLineFlag_pos j'
  rw [hκ] at hj hpt
  have hkk : k = k' := by
    have e : titsLinePt (titsKappa j') k = titsLinePt (titsKappa j') k' := by
      rw [hpt, hpt', hβ]
    obtain ⟨h1, h2⟩ := titsLinePt_lt (titsKappa j')
    rw [Fin.lt_def] at h1 h2
    have e' := congrArg Fin.val e
    interval_cases k <;> interval_cases k' <;> first | rfl | (exfalso; omega)
  calc j = titsLineFlag (titsKappa j') k := hj.symm
    _ = titsLineFlag (titsKappa j') k' := by rw [hkk]
    _ = j' := hj'

theorem titsGen_smul_titsFlagPair
    {i : ℕ} (hi : i < 4) (j : Fin 8775) :
    titsGen i • titsFlagPair j = titsFlagPair (titsP i j) := by
  simp only [titsFlagPair, Prod.smul_mk, Equiv.Perm.smul_def, titsGen_smul_titsLine hi,
    titsKappa_titsP hi, titsBeta_titsP hi]

theorem titsFlagPair_mapsRange :
    ∀ g ∈ titsA, MapsRange titsFlagPair g :=
  mapsRange_closure titsFlagPair_injective (by
    rintro _ ⟨i, rfl⟩ j
    exact ⟨_, (titsGen_smul_titsFlagPair i.2 j).symm⟩)

@[expose] def titsFlagHom :
    titsA →* Equiv.Perm (Fin 8775) :=
  indHom titsA titsFlagPair_injective titsFlagPair_mapsRange

theorem titsFlagHom_gen
    {i : ℕ} (hi : i < 4) :
    titsFlagHom ⟨titsGen i, titsGen_mem_titsA hi⟩ = titsP i :=
  indHom_eq_of _ _ fun j => (titsGen_smul_titsFlagPair hi j).symm

theorem titsBeta_flag
    (g : titsA) (j : Fin 8775) :
    titsBeta (titsFlagHom g j) = (g : Equiv.Perm (Fin 1755)) (titsBeta j) :=
  congrArg Prod.fst (f_indHom titsFlagPair_injective titsFlagPair_mapsRange g j)

theorem titsKappa_flag
    (g : titsA) (j : Fin 8775) :
    titsKappa (titsFlagHom g j) = titsLineHom g (titsKappa j) := by
  apply titsLine_injective
  rw [titsLine_lineHom]
  exact congrArg Prod.snd (f_indHom titsFlagPair_injective titsFlagPair_mapsRange g j)

end CFSG.Sporadic.Schreier.Tits
