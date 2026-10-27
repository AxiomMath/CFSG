module

public import CFSG.Sporadic.Schreier.Co3Second
public import CFSG.Sporadic.Schreier.Co3FirstCheck
public import CFSG.Sporadic.Schreier.Co3Sp6
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.ComponentInitial.PerfectCentralQuotientOuter

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms

theorem co3IzNat_lt : ∀ x ∈ co3IzNat, x < 276 := by decide

theorem co3Iz_nodup : co3Iz.Nodup :=
  co3FinList_nodup (by decide) co3IzNat_lt pointList_co3IzNat.sorted.nodup

theorem mem_co3Iz
    (p : Fin 276) : p ∈ co3Iz ↔ co3Z p = p := by
  rw [co3Iz, mem_co3FinList _ co3IzNat_lt, co3Iz_spec]

theorem co3Iz_length : co3Iz.length = 36 := rfl

theorem co3M_preserves :
    ∀ h ∈ co3M, ∀ p ∈ co3Iz, h p ∈ co3Iz := by
  intro h hh p hp
  rw [mem_co3Iz] at hp ⊢
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (co3M_le_centralizer hh)
  rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hp]

@[expose] def co3Kappa :
    co3M →* Equiv.Perm (Fin 36) :=
  (MulAut.conj co3Csp).toMonoidHom.comp ((finCongr co3Iz_length).permCongrHom.toMonoidHom.comp
    (restrictHom co3Iz co3M co3M_preserves co3Iz_nodup))

@[expose] def co3IzLab (k : Fin 36) : Fin 276 :=
  co3Iz.get ((finCongr co3Iz_length).symm (co3Csp⁻¹ k))

theorem co3IzLab_kappa
    (m : co3M) (k : Fin 36) :
    co3IzLab (co3Kappa m k) = (m : Equiv.Perm (Fin 276)) (co3IzLab k) := by
  have generic {n r : ℕ} (I : List (Fin n)) (H : Subgroup (Equiv.Perm (Fin n)))
      (hH : ∀ h ∈ H, ∀ p ∈ I, h p ∈ I) (hI : I.Nodup)
      (e : Fin I.length ≃ Fin r) (c : Equiv.Perm (Fin r))
      (L : Fin r → Fin n) (ρ : H →* Equiv.Perm (Fin r))
      (hL : L = fun j => I.get (e.symm (c⁻¹ j)))
      (hρ : ρ = (MulAut.conj c).toMonoidHom.comp
        (e.permCongrHom.toMonoidHom.comp (restrictHom I H hH hI)))
      (h : H) (j : Fin r) : L (ρ h j) = (h : Equiv.Perm (Fin n)) (L j) := by
    subst L ρ
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Equiv.Perm.mul_apply]
    rw [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, co3_permCongrHom_apply,
      Equiv.symm_apply_apply, get_restrictHom]
  exact generic co3Iz co3M co3M_preserves co3Iz_nodup
    (finCongr co3Iz_length) co3Csp co3IzLab co3Kappa rfl rfl m k

theorem co3Csp_inv :
    isInvA 36 co3CspArr (invCand 36 co3CspArr) = true :=
  isInvA_co3Field36 (f := 2) (k := 0) (by norm_num) (by rw [co3Field36_size]; decide)

theorem rep_co3Csp :
    Rep 36 co3CspArr co3Csp := (rep_permOfArr co3Csp_inv).1

theorem co3IzArr_size : co3IzArr.size = co3Iz.length := rfl

theorem co3Iz_getElem {j : ℕ} (hj : j < co3Iz.length) :
    (co3Iz[j] : ℕ) = co3IzNat[j]'(by simpa [co3Iz, co3FinList] using hj) :=
  co3FinList_getElem (by decide) co3IzNat_lt hj

theorem co3IzArr_get (i : Fin co3Iz.length) : co3IzArr[(i : ℕ)]! = (co3Iz.get i : ℕ) := by
  have hi : (i : ℕ) < co3IzNat.length := i.2
  rw [List.get_eq_getElem, co3Iz_getElem, co3IzArr, getElem!_pos _ _ (by simpa using hi),
    List.getElem_toArray]

theorem co3IzArr_nodup :
    co3IzArr.toList.Nodup := pointList_co3IzNat.sorted.nodup

theorem rep_kappa
    {a : Array ℕ} {m : co3M} (ha : Rep 276 a (m : Equiv.Perm (Fin 276))) :
    Rep 36 (renameA 36 co3CspArr (restrictA co3IzArr a)) (co3Kappa m) := by
  have h1 := rep_restrictA co3IzArr_size co3IzArr_get co3IzArr_nodup co3M_preserves co3Iz_nodup ha
  have h2 : Rep 36 (restrictA co3IzArr a) ((finCongr co3Iz_length).permCongrHom
      (restrictHom co3Iz co3M co3M_preserves co3Iz_nodup m)) := by
    intro x
    exact h1 ((finCongr co3Iz_length).symm x)
  exact rep_renameA rep_co3Csp co3Csp_inv h2

@[expose] def co3MGenElt (k : Fin 7) : co3M :=
  ⟨permOfArr 276 co3MArrs[(k : ℕ)]!, by rw [co3M_eq]; exact Subgroup.subset_closure ⟨k, rfl⟩⟩

theorem co3M_top : (⊤ : Subgroup co3M) = Subgroup.closure (Set.range co3MGenElt) := by
  symm
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  have hg' : g ∈ Subgroup.closure (Set.range fun k : Fin 7 => permOfArr 276 co3MArrs[(k : ℕ)]!) :=
    co3M_eq ▸ hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨k, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    exact Subgroup.mul_mem _ (ihx (co3M_eq ▸ hx)) (ihy (co3M_eq ▸ hy))
  | inv x hx ihx => exact Subgroup.inv_mem _ (ihx (co3M_eq ▸ hx))

theorem co3M36Arrs_size : co3M36Arrs.size = 16 := co3Field36_size' 1 rfl

theorem co3M36Arrs_inv : ∀ j < co3M36Arrs.size,
    isInvA 36 co3M36Arrs[j]! (rawInvs 36 co3M36Arrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field36 (f := 1) (by norm_num) hj

theorem co3M36Arrays :
    ChainArrays co3M36Chain (co3M36Arrs.extract 0 co3M36GenCount)
    co3M36Arrs co3M36BaseArr (wordsArr co3M36GenCount co3M36StrongCount co3M36Derivations) :=
  chainArrays_ofArrays co3M36Arrs_inv

theorem co3M36Extract_get {j : ℕ} (hj : j < 6) :
    (co3M36Arrs.extract 0 6)[j]! = co3M36Arrs[j]! := by
  rw [getElem!_pos _ j (by simp [co3M36Arrs_size]; omega),
    getElem!_pos _ j (by rw [co3M36Arrs_size]; omega), Array.getElem_extract]
  simp

theorem co3M36Extract_size : (co3M36Arrs.extract 0 6).size = 6 := by
  simp [co3M36Arrs_size]

theorem co3XM_eq : co3XM = Subgroup.closure
    {g | ∃ j < (co3M36Arrs.extract 0 6).size, permOfArr 36 (co3M36Arrs.extract 0 6)[j]! = g} := by
  rw [co3XM, co3M36Chain, ofArrays_originalSubgroup]
  congr 1
  ext g
  rw [Set.mem_range, Set.mem_ofPred_eq, co3M36Extract_size]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, by rw [co3M36Extract_get i.2]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by rw [co3M36Extract_get hi]⟩

theorem card_co3XM :
    Nat.card co3XM = 1451520 := by
  rw [co3XM, card_originalSubgroup_of_chainOK co3M36Arrays (by norm_num) co3M36Chain_check.1,
    co3M36Chain_check.2]
  rfl

theorem co3KappaGens_size : co3KappaGens.size = 7 := by simp [co3KappaGens]

theorem rep_co3KappaGens :
    ∀ k < co3KappaGens.size,
    Rep 36 co3KappaGens[k]! (if h : k < 7 then co3Kappa (co3MGenElt ⟨k, h⟩) else 1) := by
  intro k hk
  rw [co3KappaGens_size] at hk
  rw [dite_eq_left hk, co3KappaGens, co3_getElem!_ofFn _ hk]
  exact rep_kappa (rep_co3MArr (by show k < 14; omega))

theorem rep_co3M36Gens : ∀ j < (co3M36Arrs.extract 0 6).size,
    Rep 36 (co3M36Arrs.extract 0 6)[j]! (permOfArr 36 (co3M36Arrs.extract 0 6)[j]!) := by
  intro j hj
  have hj' : j < 6 := by rwa [co3M36Extract_size] at hj
  rw [co3M36Extract_get hj']
  exact (rep_permOfArr (co3M36Arrs_inv j (by rw [co3M36Arrs_size]; omega))).1

theorem co3Kappa_range_XM :
    co3Kappa.range = co3XM := by
  rw [MonoidHom.range_eq_map, co3M_top, MonoidHom.map_closure, co3XM_eq,
    ← closure_eq_of_coversOK rep_co3KappaGens rep_co3M36Gens co3First_check.2.1]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq, co3KappaGens_size]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, k.2, by rw [dite_eq_left k.2]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨⟨k, hk⟩, rfl⟩, by rw [dite_eq_left hk]⟩

theorem mem_co3X36_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 36)} (hG : Rep 36 g G)
    (h : siftA 36 co3Sp36Levels co3Sp36BaseArr 0 g = true) : G ∈ co3X36 :=
  (siftA_iff_mem_originalSubgroup co3Sp36Arrays (by norm_num) co3Sp36_check.1 hG).1 h

theorem co3XM_eq_X36 :
    co3XM = co3X36 := by
  have hle : co3XM ≤ co3X36 := by
    rw [co3XM_eq, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j < 6 := by rwa [co3M36Extract_size] at hj
    refine mem_co3X36_of_sift (rep_co3M36Gens j hj) ?_
    rw [co3M36Extract_get hj']
    exact co3First_check.2.2 j hj'
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_co3XM, card_co3X36])

theorem co3Kappa_range :
    co3Kappa.range = co3X36 := by
  rw [co3Kappa_range_XM, co3XM_eq_X36]

theorem co3Z_mem_M :
    co3Z ∈ co3M := by
  rw [co3M_eq_centralizer]
  exact Subgroup.mem_inf.2 ⟨co3Z_mem_P, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def co3ZM :
    co3M := ⟨co3Z, co3Z_mem_M⟩

theorem co3Kappa_z :
    co3Kappa co3ZM = 1 := by
  have h : restrictHom co3Iz co3M co3M_preserves co3Iz_nodup co3ZM = 1 :=
    restrictHom_eq_one _ _ _ _ _ fun p hp => by
      rw [co3ZM, Subgroup.coe_mk]; exact (mem_co3Iz p).1 hp
  unfold co3Kappa
  simp only [MonoidHom.coe_comp, Function.comp_apply, h, map_one]

theorem orderOf_co3ZM :
    orderOf co3ZM = 2 := by
  rw [co3ZM, Subgroup.orderOf_mk, orderOf_co3Z]

theorem card_ker_co3Kappa :
    Nat.card co3Kappa.ker = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup co3Kappa.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange co3Kappa).toEquiv, co3Kappa_range,
    card_co3X36, card_co3M] at h1
  omega

theorem co3Kappa_ker :
    co3Kappa.ker = Subgroup.zpowers co3ZM := by
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 co3Kappa_z) ?_).symm
  rw [card_ker_co3Kappa, Nat.card_zpowers, orderOf_co3ZM]

theorem co3M_center :
    Subgroup.center co3M = Subgroup.zpowers co3ZM := by
  apply le_antisymm
  · intro x hx
    rw [← co3Kappa_ker, MonoidHom.mem_ker]
    have hmem : co3Kappa x ∈ co3X36 := by rw [← co3Kappa_range]; exact ⟨x, rfl⟩
    have hc : (⟨co3Kappa x, hmem⟩ : co3X36) ∈ Subgroup.center co3X36 := by
      refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
      obtain ⟨y, hy⟩ : (g : Equiv.Perm (Fin 36)) ∈ co3Kappa.range := by
        rw [co3Kappa_range]; exact g.2
      simp only [Subgroup.coe_mul]
      rw [← hy, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    rw [co3X36_center, Subgroup.mem_bot] at hc
    have h := congrArg Subtype.val hc
    exact h
  · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (co3M_le_centralizer g.2)

theorem card_co3M_center :
    Nat.card (Subgroup.center co3M) = 2 := by
  rw [co3M_center, Nat.card_zpowers, orderOf_co3ZM]

theorem co3M_center_eq_ker :
    Subgroup.center co3M = co3Kappa.ker := by
  rw [co3M_center, co3Kappa_ker]

@[expose] def co3MQuotEquiv :
    co3M ⧸ Subgroup.center co3M ≃* co3X36 :=
  (QuotientGroup.quotientMulEquivOfEq co3M_center_eq_ker).trans
    ((QuotientGroup.quotientKerEquivRange co3Kappa).trans (MulEquiv.subgroupCongr co3Kappa_range))

theorem co3MCommArrs_size : co3MCommArrs.size = 8 := co3Field276_size' 8 rfl

theorem co3MCommArrs_inv : ∀ j < co3MCommArrs.size,
    isInvA 276 co3MCommArrs[j]! (rawInvs 276 co3MCommArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field276 (f := 8) (by norm_num) hj

theorem co3MCommArrays :
    ChainArrays co3MCommChain (co3MCommArrs.extract 0 co3MCommGenCount)
    co3MCommArrs co3MCommBaseArr
    (wordsArr co3MCommGenCount co3MCommStrongCount co3MCommDerivations) :=
  chainArrays_ofArrays co3MCommArrs_inv

theorem card_co3DM :
    Nat.card co3DM = 2903040 := by
  rw [co3DM, card_originalSubgroup_of_chainOK co3MCommArrays (by norm_num) co3MCommChain_check.1,
    co3MCommChain_check.2]
  rfl

theorem co3DM_le_commutator :
    co3DM ≤ ⁅co3M, co3M⁆ := by
  rw [co3DM, co3MCommChain, ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨⟨k, hk4⟩, rfl⟩
  change k < 4 at hk4
  change permOfArr 276 co3MCommArrs[k]! ∈ ⁅co3M, co3M⁆
  have hpairs : ∀ k < 4, (co3MCommPairs.getD k (0, 0)).1 - 1 < 7 ∧
      (co3MCommPairs.getD k (0, 0)).2 - 1 < 7 := by decide
  have hp := hpairs k hk4
  have hinv : ∀ k < co3MArrs.size, isInvA 276 co3MArrs[k]! (invCand 276 co3MArrs[k]!) = true :=
    fun k hk => isInvA_co3Field276 (f := 6) (by norm_num) hk
  have hrep := rep_commA (G := fun k => permOfArr 276 co3MArrs[k]!)
    (fun k hk => rep_co3MArr (by rw [co3MArrs_size] at hk; exact hk)) hinv
    (i := (co3MCommPairs.getD k (0, 0)).1 - 1) (j := (co3MCommPairs.getD k (0, 0)).2 - 1)
    (by rw [co3MArrs_size]; omega) (by rw [co3MArrs_size]; omega)
  have hmem : ∀ k < 7, permOfArr 276 co3MArrs[k]! ∈ co3M := fun k hk => by
    rw [co3M_eq]; exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩
  have he := eq_of_eqA (rep_permOfArr (co3MCommArrs_inv k (by rw [co3MCommArrs_size]; omega))).1
    hrep (co3First_check.1 k hk4)
  rw [he]
  exact Subgroup.commutator_mem_commutator (hmem _ hp.2) (hmem _ hp.1)

theorem co3M_commutator_le : ⁅co3M, co3M⁆ ≤ co3M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact co3M.mul_mem (co3M.mul_mem (co3M.mul_mem ha hb) (co3M.inv_mem ha)) (co3M.inv_mem hb)

theorem co3M_commutator :
    ⁅co3M, co3M⁆ = co3M := by
  have hle : ⁅co3M, co3M⁆ ≤ co3M := co3M_commutator_le
  apply le_antisymm hle
  have h1 : co3DM ≤ co3M := co3DM_le_commutator.trans hle
  have h2 : co3DM = co3M := Subgroup.eq_of_le_of_card_ge h1 (by rw [card_co3M, card_co3DM])
  exact h2.symm.le.trans co3DM_le_commutator

instance co3M_isPerfect :
    Group.IsPerfect co3M := Subgroup.isPerfect_iff.2 co3M_commutator

theorem co3MQuot_classicalModel :
    StatedClassicalModel (co3M ⧸ Subgroup.center co3M) .PSp 3 2 1 := by
  obtain ⟨hadm, K, hK, hfin, hcard, ⟨e⟩⟩ := co3X36_classicalModel
  exact ⟨hadm, K, hK, hfin, hcard, ⟨co3MQuotEquiv.trans e⟩⟩

theorem co3M_outer_solvable :
    Group.IsSolvable (Outer co3M) :=
  (CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_Schreier co3M).2.2
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.classical_model_schreier le_rfl
      co3MQuot_classicalModel).2

theorem AT_Co3_first_centralizer_Schreier :
    Group.IsPerfect co3M ∧ ⁅co3M, co3M⁆ = co3M ∧
    Subgroup.center co3M = Subgroup.zpowers co3ZM ∧ Nat.card (Subgroup.center co3M) = 2 ∧
    (∀ (m : co3M) (k : Fin 36),
      co3IzLab (co3Kappa m k) = (m : Equiv.Perm (Fin 276)) (co3IzLab k)) ∧
    co3Kappa.range = co3X36 ∧ co3Kappa.ker = Subgroup.zpowers co3ZM ∧
    StatedClassicalModel (co3M ⧸ Subgroup.center co3M) .PSp 3 2 1 ∧
    Group.IsSolvable (Outer co3M) :=
  ⟨co3M_isPerfect, co3M_commutator, co3M_center, card_co3M_center, co3IzLab_kappa,
    co3Kappa_range, co3Kappa_ker, co3MQuot_classicalModel, co3M_outer_solvable⟩

end CFSG.Sporadic.Schreier.Co3
