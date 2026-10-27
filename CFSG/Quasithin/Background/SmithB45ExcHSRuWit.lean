module

public import CFSG.Quasithin.Background.SmithB45ExcHSRuPIT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr

public section

namespace CFSG.Quasithin.B45Exc.Tab

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

variable {n : ℕ}

@[expose] def parseInts (s : String) : List ℤ := (s.splitOn " ").filterMap String.toInt?

@[expose] def fixCountA (n : ℕ) (a : Array ℕ) : ℕ := (List.range n).countP fun p => a[p]! == p

@[expose] def fixFinset (g : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun p => g p = p

theorem fixCountA_eq {a : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n a g) :
    fixCountA n a = (fixFinset g).card := by
  classical
  have e1 : fixCountA n a = ((Finset.range n).filter fun i => a[i]! = i).card := by
    rw [fixCountA, List.countP_eq_length_filter]
    simp only [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    congr 1
  rw [e1]
  refine Finset.card_bij (fun i hi => ⟨i, Finset.mem_range.1 (Finset.mem_filter.1 hi).1⟩)
    (fun i hi => ?_) (fun i _ j _ hij => ?_) (fun p hp => ⟨p.val, ?_, rfl⟩)
  · obtain ⟨hir, hia⟩ := Finset.mem_filter.1 hi
    simp only [fixFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    have := h.apply (Finset.mem_range.1 hir)
    rw [hia] at this
    exact this.symm
  · exact congrArg Fin.val hij
  · simp only [fixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 p.2, ?_⟩
    rw [h.apply p.2]
    exact congrArg Fin.val hp

theorem card_fix_conj (g h : Equiv.Perm (Fin n)) :
    (fixFinset (h * g * h⁻¹)).card = (fixFinset g).card := by
  refine Finset.card_bij (fun p _ => h⁻¹ p) (fun p hp => ?_) (fun p _ q _ hpq => ?_)
    (fun q hq => ⟨h q, ?_, by simp⟩)
  · simp only [fixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have := congrArg (fun x => h⁻¹ x) hp
    simpa [Equiv.Perm.mul_apply] using this
  · exact h⁻¹.injective hpq
  · simp only [fixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    simp [Equiv.Perm.mul_apply, hq]

@[expose] def pPow (n : ℕ) (x : PArr) : ℕ → PArr
  | 0 => pId n
  | k + 1 => pMul n x (pPow n x k)

theorem pRep_pow {x : PArr} {g : Equiv.Perm (Fin n)} (hx : PRep n x g) :
    ∀ k : ℕ, PRep n (pPow n x k) (g ^ k)
  | 0 => by simpa [pPow] using (pRep_id (n := n))
  | k + 1 => by
    rw [pPow, pow_succ']
    exact hx.mul (pRep_pow hx k)

@[expose] def orderCheck (n p : ℕ) (x : PArr) : Bool :=
  eqA n (pPow n x p).1 (idA n) && !eqA n x.1 (idA n)

theorem orderCheck_spec {p : ℕ} {x : PArr} {g : Equiv.Perm (Fin n)} (hx : PRep n x g)
    (h : orderCheck n p x = true) : g ^ p = 1 ∧ g ≠ 1 := by
  simp only [orderCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨(eqA_iff (pRep_pow hx p).1 rep_idA).1 h.1, fun h1 => ?_⟩
  have := (eqA_iff hx.1 rep_idA).2 h1
  rw [h.2] at this
  exact absurd this (by decide)

@[expose] def pComm (n : ℕ) (x y : PArr) : PArr :=
  pMul n (pMul n (pMul n x y) (pInv x)) (pInv y)

theorem pRep_comm {x y : PArr} {g h : Equiv.Perm (Fin n)} (hx : PRep n x g) (hy : PRep n y h) :
    PRep n (pComm n x y) ⁅g, h⁆ := by
  rw [commutatorElement_def]
  exact ((hx.mul hy).mul hx.inv).mul hy.inv

@[expose] def cfgCheck (n p : ℕ) (z x y : PArr) : Bool :=
  eqA n z.1 (pComm n x y).1 && eqA n (pPow n x p).1 (idA n) &&
    eqA n (pMul n z x).1 (pMul n x z).1 && eqA n (pMul n z y).1 (pMul n y z).1 &&
    !eqA n z.1 (idA n)

theorem cfgCheck_spec {p : ℕ} {z x y : PArr} {c g h : Equiv.Perm (Fin n)} (hz : PRep n z c)
    (hx : PRep n x g) (hy : PRep n y h) (hc : cfgCheck n p z x y = true) :
    c = ⁅g, h⁆ ∧ g ^ p = 1 ∧ Commute ⁅g, h⁆ g ∧ Commute ⁅g, h⁆ h ∧ ⁅g, h⁆ ≠ 1 := by
  simp only [cfgCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have hc1 : c = ⁅g, h⁆ := (eqA_iff hz.1 (pRep_comm hx hy).1).1 h1
  subst hc1
  refine ⟨rfl, (eqA_iff (pRep_pow hx p).1 rep_idA).1 h2, ?_, ?_, fun he => ?_⟩
  · exact (eqA_iff (hz.mul hx).1 (hx.mul hz).1).1 h3
  · exact (eqA_iff (hz.mul hy).1 (hy.mul hz).1).1 h4
  · have := (eqA_iff hz.1 rep_idA).2 he
    rw [h5] at this
    exact absurd this (by decide)

structure GenWit where
  basis : List ℕ
  g : List ℤ
  ws : List (List ℤ)

@[expose] def genRegs (gens : List PArr) (T : InvTab n) (w : GenWit) : List PArr :=
  (w.basis.map fun i => (T.elt i, T.elt i)) ++
    (w.basis.map fun i => pConj n (pWord n gens w.g) (T.elt i, T.elt i))

@[expose] def genWitOK (gens : List PArr) (T : InvTab n) (targets : List (Array ℕ))
    (w : GenWit) : Bool :=
  w.basis.all (· < T.m) && w.ws.length == targets.length &&
    (List.zip w.ws targets).all fun p => eqA n (pWord n (genRegs gens T w) p.1).1 p.2

theorem pRep_elt {T : InvTab n} {c : ℕ} (hc : 0 < c) (hT : T.check c = true) {i : ℕ}
    (hi : i < T.m) : PRep n (T.elt i, T.elt i) (T.perm i) :=
  PRep.of_sq (InvTab.rep_elt hc hT) (InvTab.perm_mul_self hc hT hi)

@[expose] def regSet (T : InvTab n) (B : List ℕ) (G : Equiv.Perm (Fin n)) :
    Set (Equiv.Perm (Fin n)) :=
  {x | ∃ i ∈ B, x = T.perm i} ∪ {x | ∃ i ∈ B, x = G * T.perm i * G⁻¹}

theorem genWitOK_spec {T : InvTab n} {c : ℕ} (hc : 0 < c) (hT : T.check c = true)
    {gens : List PArr} {K : Subgroup (Equiv.Perm (Fin n))} (hK : RegIn n K gens)
    {targets : List (Array ℕ)} {w : GenWit} (h : genWitOK gens T targets w = true) :
    ∃ G ∈ K, ∀ A ∈ targets, ∀ a : Equiv.Perm (Fin n), Rep n A a →
      a ∈ Subgroup.closure (regSet T w.basis G) := by
  simp only [genWitOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
    at h
  obtain ⟨⟨hB, hlen⟩, hw⟩ := h
  obtain ⟨G, hGK, hGrep⟩ := hK.word w.g
  refine ⟨G, hGK, fun A hA a ha => ?_⟩
  have hreg : RegIn n (Subgroup.closure (regSet T w.basis G)) (genRegs gens T w) := by
    intro r hr
    simp only [genRegs, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact ⟨T.perm i, Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩),
        pRep_elt hc hT (hB i hi)⟩
    · exact ⟨G * T.perm i * G⁻¹, Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩),
        (hGrep.mul (pRep_elt hc hT (hB i hi))).mul hGrep.inv⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hA
  have hkw : k < w.ws.length := by omega
  have hzip : (w.ws[k], targets[k]) ∈ List.zip w.ws targets := by
    have : (List.zip w.ws targets)[k]'(by simp; omega) = (w.ws[k], targets[k]) :=
      List.getElem_zip
    rw [← this]
    exact List.getElem_mem _
  have hA' := hw _ hzip
  obtain ⟨b, hb, hbrep⟩ := hreg.word w.ws[k]
  have : b = a := (eqA_iff hbrep.1 ha).1 hA'
  rw [← this]
  exact hb

theorem sylVerify_mem {N : ℕ} {gens : List PArr} {par lab tab : List ℕ} {Al : Array (Array ℕ)}
    {r : ℕ} (hv : sylVerify n N gens par lab tab Al r = true) (gp : ℕ → Equiv.Perm (Fin n))
    (hgp : ∀ j < gens.length, PRep n (gens.getD j (pId n)) (gp j)) :
    ∀ x ∈ Subgroup.closure {g | ∃ j < gens.length, g = gp j}, ∃ k < N, Rep n Al[k]! x := by
  classical
  simp only [sylVerify, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hN0⟩, h0⟩, hpar⟩, htab⟩, hinv⟩, -⟩, -⟩ := hv
  set E : ℕ → Equiv.Perm (Fin n) := fun k => permOfArr n Al[k]! with hE
  have hrep : ∀ k < N, Rep n Al[k]! (E k) := fun k hk => (rep_permOfArr (hinv k hk)).1
  have hE0 : E 0 = 1 := (eqA_iff (hrep 0 hN0) rep_idA).1 h0
  have hstep : ∀ k < N, k ≠ 0 → par.getD k 0 < k ∧ lab.getD k 0 < gens.length ∧
      E k = E (par.getD k 0) * gp (lab.getD k 0) := by
    intro k hk hk0
    have h := hpar k hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨hp, hl⟩, he⟩
    · exact absurd h hk0
    · refine ⟨hp, hl, ?_⟩
      have hr2 : Rep n (compA n Al[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1)
          (E (par.getD k 0) * gp (lab.getD k 0)) :=
        rep_compA (hrep _ (hp.trans hk)) (hgp _ hl).1
      exact (eqA_iff (hrep k hk) hr2).1 he
  have htabE : ∀ i < N, ∀ j < gens.length, ∃ k < N, E i * gp j = E k := by
    intro i hi j hj
    obtain ⟨hk, he⟩ := htab i hi j hj
    refine ⟨tab.getD (i * gens.length + j) 0, hk, ?_⟩
    have hr2 : Rep n (compA n Al[i]! (gens.getD j (pId n)).1) (E i * gp j) :=
      rep_compA (hrep i hi) (hgp j hj).1
    exact ((eqA_iff hr2 (hrep _ hk)).1 he)
  set rg : List (Equiv.Perm (Fin n)) := (List.range gens.length).map gp with hrg
  have hEclos : ∀ k < N, E k ∈ Subgroup.closure {g | g ∈ rg} := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [hE0]
        exact Subgroup.one_mem _
      · obtain ⟨hp, hl, he⟩ := hstep k hk hk0
        rw [he]
        refine Subgroup.mul_mem _ (ih _ hp (hp.trans hk)) (Subgroup.subset_closure ?_)
        exact List.mem_map.2 ⟨_, List.mem_range.2 hl, rfl⟩
  have h1 : (1 : Equiv.Perm (Fin n)) ∈ (List.range N).map E :=
    List.mem_map.2 ⟨0, List.mem_range.2 hN0, hE0⟩
  have hgen : ∀ x ∈ (List.range N).map E, ∀ g ∈ rg, x * g ∈ (List.range N).map E := by
    intro x hx g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    obtain ⟨k, hk, hik⟩ := htabE i (List.mem_range.1 hi) j (List.mem_range.1 hj)
    exact List.mem_map.2 ⟨k, List.mem_range.2 hk, hik.symm⟩
  obtain ⟨R, hR⟩ := exists_subgroup_of_gens rg ((List.range N).map E) h1 hgen (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hEclos i (List.mem_range.1 hi))
  have hle : Subgroup.closure {g | ∃ j < gens.length, g = gp j} ≤ R := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    show gp j ∈ R
    rw [hR]
    have := hgen 1 h1 (gp j) (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    rwa [one_mul] at this
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ((hR x).1 (hle hx))
  exact ⟨k, List.mem_range.1 hk, hrep k (List.mem_range.1 hk)⟩

end CFSG.Quasithin.B45Exc.Tab
