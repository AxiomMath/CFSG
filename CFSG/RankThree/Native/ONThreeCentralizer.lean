module

public import CFSG.RankThree.Native.ONSevenRestrict
public import Certificates.Certificate8139
public import Certificates.Certificate9702

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native Subgroup

theorem onThree_t_check :
    (onSevenArr [6])[0]! = 0 ∧ (onSevenGood (onSevenArr [6]) []).length = 90 ∧
    onSevenCount (onSevenArr [6]) = 36 ∧
    peq N (pcomp N (onSevenArr [6]) (pcomp N (onSevenArr [6]) (onSevenArr [6]))) (pid N) = true ∧
    peq N (onSevenArr [6]) (pid N) = false :=
  Certificates.certificate8139

theorem onThree_checks :
    onThreeCommOK (onSevenArr [6]) = true ∧
    onThreeTreeOK onThreeYArrs onThreeTreePts onThreeTreePar onThreeTreeGen = true ∧
    onThreeCovers (onSevenArr [6]) onThreeTreePts = true :=
  Certificates.certificate9702

theorem le_card_of_orbit_supset {G α : Type*} [Group G] [MulAction G α] [Finite G]
    (K : Subgroup G) (b : α) (L : List α) (hnd : L.Nodup) (hL : ∀ c ∈ L, ∃ g ∈ K, g • b = c) :
    L.length * Nat.card (K ⊓ MulAction.stabilizer G b : Subgroup G) ≤ Nat.card K := by
  classical
  have h1 := (MulAction.stabilizer K b).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have horb : L.length ≤ (MulAction.orbit K b).ncard := by
    have hsub : (L.toFinset : Set α) ⊆ MulAction.orbit K b := by
      intro c hc
      rw [Finset.mem_coe, List.mem_toFinset] at hc
      obtain ⟨g, hg, rfl⟩ := hL c hc
      exact ⟨⟨g, hg⟩, rfl⟩
    calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = (L.toFinset : Set α).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit K b).ncard := Set.ncard_le_ncard hsub (Set.finite_range _)
  have hstab : Nat.card (K ⊓ MulAction.stabilizer G b : Subgroup G) ≤
      Nat.card (MulAction.stabilizer K b) := by
    refine Nat.card_le_card_of_injective
      (fun s => ⟨⟨(s : G), (Subgroup.mem_inf.1 s.2).1⟩,
        MulAction.mem_stabilizer_iff.2 ?_⟩) ?_
    · exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 s.2).2
    · intro s t hst
      exact Subtype.ext (congrArg (fun y : MulAction.stabilizer K b => ((y : K) : G)) hst)
  calc L.length * Nat.card (K ⊓ MulAction.stabilizer G b : Subgroup G)
      ≤ (MulAction.orbit K b).ncard * Nat.card (MulAction.stabilizer K b) :=
        Nat.mul_le_mul horb hstab
    _ = Nat.card K := by rw [mul_comm]; exact h1

theorem onSevenGood_nodup (x : Array ℕ) (bad : List ℕ) : (onSevenGood x bad).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem onThree_t_letters : plettersOK 7 [6] = true := by decide

theorem onThreeY_letters {j : ℕ} (hj : j < onThreeY.size) : plettersOK 7 onThreeY[j]! = true := by
  have h2 : onThreeY.size = 2 := rfl
  rw [h2] at hj
  interval_cases j <;> decide

section Orbit


abbrev onThreeT : Equiv.Perm (Fin N) := evalS [6]

theorem prep_onThreeT : PRep N (onSevenArr [6]) onThreeT := prep_onSevenArr onThree_t_letters

theorem prep_onThreeY {j : ℕ} (hj : j < onThreeY.size) :
    PRep N onThreeYArrs[j]! (evalS onThreeY[j]!) := by
  rw [onThreeYArrs, getElem!_map_onSeven onSevenArr onThreeY hj]
  exact prep_onSevenArr (onThreeY_letters hj)

abbrev onThreeK : Subgroup (Equiv.Perm (Fin N)) := centralizer {onThreeT} ⊓ Pv


theorem onThreeY_mem {j : ℕ} (hj : j < onThreeY.size) : evalS onThreeY[j]! ∈ onThreeK := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, evalS_mem _⟩
  have h := allBelowN_spec onThree_checks.1 (by simpa [onThreeYArrs] using hj)
  exact eq_of_peq (prep_pcomp (prep_onThreeY hj) prep_onThreeT)
    (prep_pcomp prep_onThreeT (prep_onThreeY hj)) h

theorem onThree_reach :
    ∀ k < onThreeTreePts.size, ∃ g ∈ onThreeK, ((g x0 : Fin N) : ℕ) = onThreeTreePts[k]! := by
  have hOK := onThree_checks.2.1
  simp only [onThreeTreeOK, Bool.and_eq_true, beq_iff_eq] at hOK
  obtain ⟨⟨⟨hsz1, hsz2⟩, h0⟩, hall⟩ := hOK
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk' := allBelowN_spec hall hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hk'
    obtain ⟨hlt, hk0 | ⟨⟨hpar, hgen⟩, himg⟩⟩ := hk'
    · subst hk0
      exact ⟨1, one_mem _, by simpa using h0.symm⟩
    · obtain ⟨g, hg, hgx⟩ := ih onThreeTreePar[k]! hpar (lt_trans hpar hk)
      have hpar_lt : onThreeTreePar[k]! < onThreeTreePts.size := lt_trans hpar hk
      have hlt' := allBelowN_spec hall hpar_lt
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt'
      have hgy : onThreeTreeGen[k]! < onThreeY.size := by simpa [onThreeYArrs] using hgen
      have hpt : onThreeTreePts[onThreeTreePar[k]!]! < N := hlt'.1
      refine ⟨evalS onThreeY[onThreeTreeGen[k]!]! * g, mul_mem (onThreeY_mem hgy) hg, ?_⟩
      have hg' : g x0 = ⟨onThreeTreePts[onThreeTreePar[k]!]!, hpt⟩ := Fin.ext hgx
      rw [Equiv.Perm.mul_apply, hg', ← (prep_onThreeY hgy ⟨_, hpt⟩)]
      exact himg

theorem onThree_orbit {q : ℕ} (hq : q ∈ onSevenGood (onSevenArr [6]) []) :
    ∃ g ∈ onThreeK, ((g x0 : Fin N) : ℕ) = q := by
  have hc := List.all_eq_true.1 (onThree_checks.2.2) q hq
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hc
  obtain ⟨k, hk, hkq⟩ := hc
  obtain ⟨g, hg, hgx⟩ := onThree_reach k hk
  exact ⟨g, hg, by rw [hgx, getElem!_pos onThreeTreePts k hk, hkq]⟩

end Orbit

section Main


theorem onThree_t_x0 : onThreeT x0 = x0 := by
  apply Fin.ext
  rw [← prep_onThreeT x0]
  exact onThree_t_check.1

theorem onThree_t_cube : onThreeT ^ 3 = 1 := by
  have h := eq_of_peq (prep_pcomp prep_onThreeT (prep_pcomp prep_onThreeT prep_onThreeT))
    prep_pid onThree_t_check.2.2.2.1
  rw [pow_succ, pow_succ, pow_one, mul_assoc]
  exact h

theorem onThree_t_ne_one : onThreeT ≠ 1 := by
  intro h
  have := (peq_iff prep_onThreeT prep_pid).2 h
  rw [onThree_t_check.2.2.2.2] at this
  exact Bool.false_ne_true this

theorem orderOf_onThreeT : orderOf onThreeT = 3 :=
  orderOf_eq_prime onThree_t_cube onThree_t_ne_one

theorem card_centralizer_onThreeT : Nat.card onThreeK = 3240 := by
  have hup : Nat.card onThreeK ≤ _ :=
    card_centralizer_le_of_good prep_onThreeT (evalS_mem _) onThree_t_x0 (bad := [])
      (fun q hq => by simp at hq)
  rw [onThree_t_check.2.1, onThree_t_check.2.2.1] at hup
  have hnd : ((onSevenGood (onSevenArr [6]) []).map onSevenPt).Nodup := by
    refine List.Nodup.map_on ?_ (onSevenGood_nodup _ _)
    intro a ha b hb hab
    have ha' : a < N := List.mem_range.1 (List.mem_filter.1 ha).1
    have hb' : b < N := List.mem_range.1 (List.mem_filter.1 hb).1
    have := congrArg Fin.val hab
    simpa [onSevenPt, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using this
  have hlow := le_card_of_orbit_supset onThreeK x0
    ((onSevenGood (onSevenArr [6]) []).map onSevenPt) hnd (by
      intro c hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
      obtain ⟨g, hg, hgq⟩ := onThree_orbit hq
      refine ⟨g, hg, Fin.ext ?_⟩
      have hqN : q < N := List.mem_range.1 (List.mem_filter.1 hq).1
      rw [Equiv.Perm.smul_def, hgq]
      simp [onSevenPt, Nat.mod_eq_of_lt hqN])
  have hstab : (onThreeK ⊓ MulAction.stabilizer (Equiv.Perm (Fin N)) x0 :
      Subgroup (Equiv.Perm (Fin N))) =
      centralizer {onThreeT} ⊓ (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0}) := by
    rw [stabilizer_x0_eq, inf_assoc]
  rw [hstab, card_centralizer_P0 prep_onThreeT (evalS_mem _), List.length_map,
    onThree_t_check.2.1, onThree_t_check.2.2.1] at hlow
  omega

end Main

theorem card_centralizer_eq_inf_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    {P : Subgroup G'} (e : G ≃* P) (x : G) :
    Nat.card (centralizer {x}) = Nat.card (centralizer {(e x : G')} ⊓ P : Subgroup G') := by
  have hι : Function.Injective (P.subtype.comp e.toMonoidHom) :=
    Subtype.val_injective.comp e.injective
  have hmap : (centralizer {x}).map (P.subtype.comp e.toMonoidHom) =
      centralizer {(e x : G')} ⊓ P := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z * x = x * z := mem_centralizer_singleton_iff.mp hz
      refine mem_inf.2 ⟨?_, (e z).2⟩
      rw [mem_centralizer_singleton_iff]
      change ((e z : P) : G') * (e x : P) = (e x : P) * (e z : P)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hz']
    · intro hw
      obtain ⟨hwc, hwP⟩ := mem_inf.1 hw
      rw [mem_centralizer_singleton_iff] at hwc
      refine ⟨e.symm ⟨w, hwP⟩, mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · apply e.injective
        apply Subtype.ext
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul]
        exact hwc
      · change ((e (e.symm ⟨w, hwP⟩) : P) : G') = w
        rw [MulEquiv.apply_symm_apply]
  rw [← hmap, Subgroup.card_map_of_injective hι]

theorem card_centralizer_conj_eq {X : Type*} [Group X] (a h : X) :
    Nat.card (centralizer {h⁻¹ * a * h}) = Nat.card (centralizer {a}) := by
  have e : (centralizer {h⁻¹ * a * h} : Subgroup X) = (centralizer {a}).map
      (MulAut.conj h⁻¹).toMonoidHom := by
    ext g
    simp only [mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    constructor
    · intro hg
      refine ⟨h * g * h⁻¹, ?_, by group⟩
      calc h * g * h⁻¹ * a = h * (g * (h⁻¹ * a * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * a * h) * g) * h⁻¹ := by rw [hg]
        _ = a * (h * g * h⁻¹) := by group
    · rintro ⟨y, hy, rfl⟩
      calc h⁻¹ * y * h * (h⁻¹ * a * h) = h⁻¹ * (y * a) * h := by group
        _ = h⁻¹ * (a * y) * h := by rw [hy]
        _ = h⁻¹ * a * h * (h⁻¹ * y * h) := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]

section Elt


abbrev onThreeP : Pv := ⟨onThreeT, evalS_mem _⟩

def onThreeElt : Blueprint.NativeSporadic.ON := onEquivPv.symm onThreeP

theorem orderOf_onThreeElt : orderOf onThreeElt = 3 := by
  rw [onThreeElt, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact orderOf_onThreeT

theorem card_centralizer_onThreeElt :
    Nat.card (centralizer {onThreeElt}) = 3240 := by
  have h := card_centralizer_eq_inf_of_mulEquiv (G := Blueprint.NativeSporadic.ON)
    (G' := Equiv.Perm (Fin N)) (P := Pv) (by exact onEquivPv) onThreeElt
  have he : ((onEquivPv onThreeElt : Pv) : Equiv.Perm (Fin N)) = onThreeT :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply onEquivPv onThreeP)
  exact h.trans ((congrArg (fun y => Nat.card (centralizer {y} ⊓ Pv : Subgroup _)) he).trans
    card_centralizer_onThreeT)

end Elt

end CFSG.RankThree.Native
