module

public import CFSG.Sporadic.Fi23.Tr.Points

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def trSet
    (k : ℕ) : Set D23 := dsetP trc.orb.sets[k]!

theorem trOrb_ok :
    trOrbitOK orb.alpha orb.beta zB tB trc.orb 3 = true :=
  tr_parts.2.2.2.2.2.2.2.2.2.1

theorem trSet_zero :
    trSet 0 = trRoot := by
  rw [trRoot_eq]
  exact dsetP_eq_of_pBit (trOrbitOK_spec trOrb_ok).2.2.2.2.2.1

theorem pKey_congr (z : PBits) {A B : PBits} (h : ∀ x < 31671, pBit A x = pBit B x) :
    pKey z A = pKey z B := by
  unfold pKey
  congr 1
  funext x hx C
  rw [h x hx]

theorem trFind_congr (o : TrOrb) (z : PBits) {A B : PBits}
    (h : ∀ x < 31671, pBit A x = pBit B x) : trFind o z A = trFind o z B := by
  unfold trFind
  rw [pKey_congr z h]

theorem trSet_inj
    {k m : ℕ} (hk : k < 137632) (hm : m < 137632) (h : trSet k = trSet m) :
    k = m := by
  have hkey := (trOrbitOK_spec trOrb_ok).2.2.2.2.2.2.2.2
  rw [← hkey k hk, ← hkey m hm]
  exact trFind_congr _ _ fun x hx => pBit_eq_of_dsetP_eq h hx

@[expose, instance_reducible] noncomputable def setAct :
    MulAction J (Set D23) where
  smul g S := ⇑(Pair.conjPerm pair_J g) '' S
  one_smul S := by
    show ⇑(Pair.conjPerm pair_J 1) '' S = S
    rw [map_one, Equiv.Perm.coe_one, Set.image_id]
  mul_smul g h S := by
    show ⇑(Pair.conjPerm pair_J (g * h)) '' S =
      ⇑(Pair.conjPerm pair_J g) '' (⇑(Pair.conjPerm pair_J h) '' S)
    rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp]

attribute [local instance] setAct

theorem setAct_smul
    (g : J) (S : Set D23) : g • S = ⇑(Pair.conjPerm pair_J g) '' S := rfl

theorem trHyps :
    (∀ i < 137632, ap trc.orb.pa i < 137632 ∧ a • trSet i = trSet (ap trc.orb.pa i)) ∧
    (∀ i < 137632, ap trc.orb.pb i < 137632 ∧ b • trSet i = trSet (ap trc.orb.pb i)) := by
  obtain ⟨-, -, -, -, -, -, hgen, -, -⟩ := trOrbitOK_spec trOrb_ok
  refine ⟨fun i hi => ⟨(hgen i hi).1, ?_⟩, fun i hi => ⟨(hgen i hi).2.1, ?_⟩⟩
  · rw [setAct_smul]
    exact conjPerm_image_dsetP rep_alpha (hgen i hi).2.2.1
  · rw [setAct_smul]
    exact conjPerm_image_dsetP rep_beta (hgen i hi).2.2.2

theorem trTreeHyp :
    ∀ i < 137632, 0 < i → ap trc.orb.par i < i ∧
    ((ap trc.orb.lab i = 1 ∧ ap trc.orb.pa (ap trc.orb.par i) = i) ∨
      (ap trc.orb.lab i = 2 ∧ ap trc.orb.pb (ap trc.orb.par i) = i)) :=
  fun i hi hi0 => (trOrbitOK_spec trOrb_ok).2.2.2.2.2.2.2.1 i hi0 hi

theorem orbit_trSet :
    MulAction.orbit J trRoot = trSet '' Set.Iio 137632 := by
  rw [← trSet_zero]
  exact orbit_eq_image closure_ab (by norm_num) trSet trHyps.1 trHyps.2 _ _ trTreeHyp

@[expose] noncomputable def trEquiv :
    Fin 137632 ≃ MulAction.orbit J trRoot :=
  (orbitEquiv closure_ab (n := 137632) (by norm_num) trSet (fun i hi j hj h => trSet_inj hi hj h)
    trHyps.1 trHyps.2 (fun k => ap trc.orb.par k) (fun k => ap trc.orb.lab k) trTreeHyp).trans
    (Equiv.subtypeEquivRight fun _ => by rw [trSet_zero])

theorem trEquiv_val
    (k : Fin 137632) : (trEquiv k : Set D23) = trSet k.val := rfl

noncomputable instance trIdx :
    MulAction J (Fin 137632) := trEquiv.mulAction J

theorem tr_smul_def
    (g : J) (k : Fin 137632) : g • k = trEquiv.symm (g • trEquiv k) := rfl

theorem trEquiv_smul
    (g : J) (k : Fin 137632) : trEquiv (g • k) = g • trEquiv k := by
  rw [tr_smul_def, Equiv.apply_symm_apply]

theorem conjPerm_image_trSet
    (g : J) {m : ℕ} (hm : m < 137632) :
    ⇑(Pair.conjPerm pair_J g) '' trSet m = trSet (idx 137632 g m) := by
  have h := congrArg Subtype.val (trEquiv_smul g ⟨m, hm⟩)
  rw [trEquiv_val] at h
  rw [idx_of_lt g hm, h]
  rfl

theorem idx_eq_of_trSet
    {g : J} {m m' : ℕ} (hm : m < 137632) (hm' : m' < 137632)
    (h : ⇑(Pair.conjPerm pair_J g) '' trSet m = trSet m') : idx 137632 g m = m' := by
  rw [conjPerm_image_trSet g hm] at h
  exact trSet_inj (idx_lt g hm) hm' h

theorem rep_pa :
    Rep 137632 trc.orb.pa a := by
  intro i hi
  obtain ⟨h1, h2⟩ := trHyps.1 i hi
  rw [setAct_smul] at h2
  exact (idx_eq_of_trSet hi h1 h2).symm

theorem rep_pb :
    Rep 137632 trc.orb.pb b := by
  intro i hi
  obtain ⟨h1, h2⟩ := trHyps.2 i hi
  rw [setAct_smul] at h2
  exact (idx_eq_of_trSet hi h1 h2).symm

theorem b_mul_b : b * b = b⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  apply mat_injective
  rw [mat_mul, mat_mul, mat_b, mat_one, mul_assoc]
  exact matrixFacts.B_inv

theorem rep_tbi :
    Rep 137632 tbi b⁻¹ := by
  rw [tbi_eq, ← b_mul_b]
  exact Rep.compT rep_pb rep_pb

theorem rep_trLetter (x : ℕ) :
    Rep 137632 (if x = 0 then trc.orb.pa else trc.orb.pb) (if x = 0 then a else b) := by
  split_ifs
  · exact rep_pa
  · exact rep_pb

theorem rep_trWordTab (w : List ℕ) :
    Rep 137632 (w.foldr (fun x T => compT 137632 (if x = 0 then trc.orb.pa else trc.orb.pb) T)
      (idT 137632)) (wordJ w) := by
  induction w with
  | nil => simpa [wordJ] using Rep.idT (G := J) (n := 137632) (by norm_num)
  | cons x w ih =>
    have e : wordJ (x :: w) = (if x = 0 then a else b) * wordJ w := by
      simp only [wordJ, List.map_cons, List.prod_cons]
    rw [List.foldr_cons, e]
    exact (rep_trLetter x).compT ih

theorem rep_tdd :
    Rep 137632 tdd d := by
  rw [tdd_eq]
  exact Rep.powT (by norm_num) (rep_trWordTab dWord) 7

theorem trAct_spec :
    ∀ k, ∀ m < 137632, trAct orb trc.orb tdd tbi k m = idx 137632 (conjPt k) m :=
  treeAct_spec rep_pa rep_pb rep_tbi rep_tdd a_inv conjPt conjPt_eq

theorem trAct_lt
    {k m : ℕ} (hm : m < 137632) : trAct orb trc.orb tdd tbi k m < 137632 := by
  rw [trAct_spec k m hm]
  exact idx_lt _ hm

theorem conjPerm_image_trSet_conjPt
    (k : ℕ) {m : ℕ} (hm : m < 137632) :
    ⇑(Pair.conjPerm pair_J (conjPt k)) '' trSet m = trSet (trAct orb trc.orb tdd tbi k m) := by
  rw [trAct_spec k m hm]
  exact conjPerm_image_trSet _ hm

theorem tv_image_trSet
    (h : Fin 31671) {m : ℕ} (hm : m < 137632) :
    (pairModel pair_J).tv (ptD23 h) '' trSet m = trSet (trAct orb trc.orb tdd tbi h.val m) := by
  rw [tv_eq_conjPerm, ptD23_val']
  exact conjPerm_image_trSet_conjPt _ hm

theorem conjPerm_image_trRoot
    (g : J) :
    ⇑(Pair.conjPerm pair_J g) '' trRoot ∈ trSet '' Set.Iio 137632 := by
  rw [← orbit_trSet]
  exact ⟨g, rfl⟩

theorem mem_trOrbit_iff
    {T : Set D23} : T ∈ trOrbit ↔ ∃ k < 137632, T = trSet k := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨k, hk, hke⟩ := conjPerm_image_trRoot g
    exact ⟨k, hk, hke.symm⟩
  · rintro ⟨k, hk, rfl⟩
    have hmem : trSet k ∈ MulAction.orbit J trRoot := by
      rw [orbit_trSet]
      exact ⟨k, hk, rfl⟩
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, hg.symm⟩

theorem trSet_mem_trOrbit
    {k : ℕ} (hk : k < 137632) : trSet k ∈ trOrbit :=
  mem_trOrbit_iff.2 ⟨k, hk, rfl⟩

theorem trOrbit_eq_image :
    trOrbit = trSet '' Set.Iio 137632 := by
  ext T
  rw [mem_trOrbit_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

theorem ncard_trOrbit :
    trOrbit.ncard = 137632 := by
  have hinj : Set.InjOn trSet (Set.Iio 137632) := fun k hk m hm h => trSet_inj hk hm h
  rw [trOrbit_eq_image, hinj.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset,
    Finset.card_range]

theorem conjPerm_mem_trOrbit
    {T : Set D23} (hT : T ∈ trOrbit) (g : J) :
    ⇑(Pair.conjPerm pair_J g) '' T ∈ trOrbit := by
  obtain ⟨h, rfl⟩ := hT
  refine ⟨g * h, ?_⟩
  rw [Set.image_image, map_mul]
  rfl

end CFSG.Sporadic.Fi23
