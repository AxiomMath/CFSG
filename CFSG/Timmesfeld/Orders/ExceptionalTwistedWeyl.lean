module

public import CFSG.Timmesfeld.Orders.ExceptionalWeylCert
public import CFSG.LieType.Chevalley.FoldedWeylData

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

variable {t : TwistTag}

theorem weylTwist_mem_parabolic {J : Set (Fin t.tag.rank)} (hJ : ∀ i ∈ J, t.perm i ∈ J)
    {w : WeylGroup t.tag} (hw : w ∈ (coxeterSystem t.tag).parabolic J) :
    weylTwist t w ∈ (coxeterSystem t.tag).parabolic J := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem t.tag).mem_parabolic_iff_exists_wordProd_eq.1 hw
  rw [weylTwist_wordProd]
  refine (coxeterSystem t.tag).wordProd_mem_parabolic fun i hi => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  exact hJ j (hω j hj)

theorem weylTwist_isMinimalCosetRep {J' : Set (Fin t.tag.rank)}
    (hJ' : ∀ i ∈ J', t.perm.symm i ∈ J') {u : WeylGroup t.tag}
    (hu : (coxeterSystem t.tag).IsMinimalCosetRep J' u) :
    (coxeterSystem t.tag).IsMinimalCosetRep J' (weylTwist t u) := by
  rw [isMinimalCosetRep_iff] at hu ⊢
  intro i hi hdesc
  apply hu (t.perm.symm i) (hJ' i hi)
  have e : weylTwist t u * simple t.tag i =
      weylTwist t (u * simple t.tag (t.perm.symm i)) := by
    rw [map_mul, weylTwist_simple, Equiv.apply_symm_apply]
  change (coxeterSystem t.tag).length (weylTwist t u * simple t.tag i) <
    (coxeterSystem t.tag).length (weylTwist t u) at hdesc
  rw [e, length_weylTwist, length_weylTwist] at hdesc
  exact hdesc

section Sums

variable (t) [Fintype (WeylGroup t.tag)]

open Classical in
@[expose] def twistedParabolicSum (J : Set (Fin t.tag.rank)) (q : ℕ) : ℕ :=
  ∑ w ∈ Finset.univ.filter (fun w => w ∈ (coxeterSystem t.tag).parabolic J ∧
    w ∈ relWeylTwist t), q ^ (coxeterSystem t.tag).length w

open Classical in
@[expose] def twistedCosetSum (J J' : Set (Fin t.tag.rank)) (q : ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => (u ∈ (coxeterSystem t.tag).parabolic J ∧
    (coxeterSystem t.tag).IsMinimalCosetRep J' u) ∧ u ∈ relWeylTwist t),
    q ^ (coxeterSystem t.tag).length u

variable {t}

theorem twistedParabolicSum_eq_mul {J J' : Set (Fin t.tag.rank)} (hJ : J' ⊆ J)
    (hρ : ∀ i ∈ J', t.perm i ∈ J') (hρ' : ∀ i ∈ J', t.perm.symm i ∈ J') (q : ℕ) :
    twistedParabolicSum t J q = twistedCosetSum t J J' q * twistedParabolicSum t J' q := by
  classical
  set cs := coxeterSystem t.tag
  rw [twistedParabolicSum, twistedCosetSum, twistedParabolicSum, Finset.sum_mul_sum,
    ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨mul_mem h.1.1.1 (cs.parabolic_mono hJ h.2.1), mul_mem h.1.2 h.2.2⟩
  · rintro ⟨u, v⟩ h ⟨u', v'⟩ h' huv
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h h'
    obtain ⟨_, -, huniq⟩ := cs.existsUnique_isMinimalCosetRep_mul J' (u * v)
    exact (huniq (u, v) ⟨h.1.1.2, h.2.1, rfl⟩).trans
      (huniq (u', v') ⟨h'.1.1.2, h'.2.1, huv⟩).symm
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨⟨u, v⟩, ⟨hu, hv, rfl⟩, huniq⟩ := cs.existsUnique_isMinimalCosetRep_mul J' w
    have hfix := huniq (weylTwist t u, weylTwist t v)
      ⟨weylTwist_isMinimalCosetRep hρ' hu, weylTwist_mem_parabolic hρ hv, by
        rw [← map_mul, (mem_relWeylTwist t).1 hw.2]⟩
    simp only [Prod.mk.injEq] at hfix
    refine ⟨(u, v), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨⟨?_, hu⟩, (mem_relWeylTwist t).2 hfix.1⟩, hv, (mem_relWeylTwist t).2 hfix.2⟩
    have := mul_mem hw.1 (inv_mem (cs.parabolic_mono hJ hv))
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [cs.length_mul_of_isMinimalCosetRep h.1.1.2 h.2.1, pow_add]

theorem twistedParabolicSum_empty (q : ℕ) : twistedParabolicSum t ∅ q = 1 := by
  classical
  rw [twistedParabolicSum, (coxeterSystem t.tag).parabolic_empty]
  have : Finset.univ.filter (fun w => w ∈ (⊥ : Subgroup (WeylGroup t.tag)) ∧
      w ∈ relWeylTwist t) = {1} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_bot,
      Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ one_mem _⟩⟩
  rw [this, Finset.sum_singleton, (coxeterSystem t.tag).length_one, pow_zero]

open Classical in
theorem twistedParabolicSum_univ (q : ℕ) :
    twistedParabolicSum t Set.univ q =
      ∑ w ∈ Finset.univ.filter (· ∈ relWeylTwist t), q ^ (coxeterSystem t.tag).length w := by
  classical
  rw [twistedParabolicSum, (coxeterSystem t.tag).parabolic_univ]
  congr 1
  ext w
  simp

end Sums

theorem label_permLattice (v : Fin t.tag.rank → ℤ) (i : Fin t.tag.rank) :
    label t.tag (permLattice t.perm v) (t.perm i) = label t.tag v i := by
  simp only [label, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp t.perm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [t.cartan_perm, Equiv.symm_apply_apply]

@[expose] def IsPermInvariant (t : TwistTag) (c : Fin t.tag.rank → ℤ) : Prop :=
  ∀ i, c (t.perm i) = c i

instance (c : Fin t.tag.rank → ℤ) : Decidable (IsPermInvariant t c) :=
  inferInstanceAs (Decidable (∀ i, c (t.perm i) = c i))

theorem label_permLattice_eq {v : Fin t.tag.rank → ℤ} (hv : IsPermInvariant t (label t.tag v)) :
    label t.tag (permLattice t.perm v) = label t.tag v := by
  funext j
  obtain ⟨i, rfl⟩ := t.perm.surjective j
  rw [label_permLattice, hv i]

namespace IsOrbitList

variable {J J' : Finset (Fin t.tag.rank)} {lam : Fin t.tag.rank → ℤ}
  {L : List (Fin t.tag.rank → ℤ)} (hL : IsOrbitList t.tag J J' lam L)
include hL

theorem twistedCosetSum_eq_sum [Fintype (WeylGroup t.tag)] (hJ : ∀ i ∈ J, t.perm i ∈ J)
    (hJ' : ∀ i ∈ J', t.perm.symm i ∈ J') (hlam : permLattice t.perm lam = lam) (q : ℕ) :
    twistedCosetSum t J J' q =
      ((L.filter fun c => decide (IsPermInvariant t c)).map fun c =>
        q ^ negCount t.tag J c).sum := by
  classical
  rw [twistedCosetSum, ← List.sum_toFinset _ (hL.nodup.filter _)]
  refine Finset.sum_bij (fun u _ => label t.tag (u • lam)) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine List.mem_toFinset.2 (List.mem_filter.2 ⟨hL.label_smul_mem hu.1.1, ?_⟩)
    refine decide_eq_true fun i => ?_
    have h := (mem_relWeylTwist_iff_smul t).1 hu.2 lam
    rw [hlam] at h
    conv_lhs => rw [h]
    exact label_permLattice _ i
  · intro u hu u' hu' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
    exact hL.eq_of_label_eq hu.1.1 hu.1.2 hu'.1.1 hu'.1.2 h
  · intro c hc
    obtain ⟨hcL, hcinv⟩ := List.mem_filter.1 (List.mem_toFinset.1 hc)
    obtain ⟨u, hu, hmin, rfl⟩ := hL.exists_eq_label hcL
    have hδ : weylTwist t u = u := by
      refine hL.eq_of_label_eq (weylTwist_mem_parabolic (fun i hi => by
          simpa using hJ i (by simpa using hi)) hu)
        (weylTwist_isMinimalCosetRep (fun i hi => by simpa using hJ' i (by simpa using hi)) hmin)
        hu hmin ?_
      conv_lhs => rw [← hlam, weylTwist_smul_permLattice]
      exact label_permLattice_eq (of_decide_eq_true hcinv)
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨hu, hmin⟩, (mem_relWeylTwist t).2 hδ⟩
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [hL.length_eq hu.1.1 hu.1.2]

end IsOrbitList

@[expose] def isPermInvB (t : TwistTag) (c : Fin t.tag.rank → ℤ) : Bool :=
  (List.finRange t.tag.rank).all fun i => c (t.perm i) == c i

theorem isPermInvB_eq_decide (c : Fin t.tag.rank → ℤ) :
    isPermInvB t c = decide (IsPermInvariant t c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp [isPermInvB, IsPermInvariant]

structure TwistedStep (t : TwistTag) where
  mask : ℕ
  prev : ℕ
  cert : OrbitCert t.tag
  factors : List (ℕ × ℕ)

namespace TwistedStep

@[expose] def rhoLens (s : TwistedStep t) : List ℕ :=
  ((s.cert.pts.zip s.cert.lens).filter fun p => isPermInvB t (decodeVec p.1)).map Prod.snd

@[expose] def check (s : TwistedStep t) : Bool :=
  s.cert.check s.mask s.prev &&
    ((List.finRange t.tag.rank).all fun k => !s.prev.testBit k || s.mask.testBit k) &&
    ((List.finRange t.tag.rank).all fun k => !s.mask.testBit k || s.mask.testBit (t.perm k)) &&
    ((List.finRange t.tag.rank).all fun k => !s.prev.testBit k || s.prev.testBit (t.perm k)) &&
    ((List.finRange t.tag.rank).all fun k =>
      !s.prev.testBit k || s.prev.testBit (t.perm.symm k)) &&
    (List.ofFn (permLattice t.perm (decodeVec (τ := t.tag) s.cert.lam)) ==
      List.ofFn (decodeVec (τ := t.tag) s.cert.lam)) &&
    decide (s.rhoLens.Perm (prodExps s.factors))

@[expose] def value (s : TwistedStep t) (q : ℕ) : ℕ :=
  (s.factors.map fun f => geomSum f.1 f.2 q).prod

end TwistedStep

@[expose] def twistedChainCheck : List (TwistedStep t) → ℕ → Bool
  | [], m => m == 0
  | s :: ss, m => s.mask == m && s.check && twistedChainCheck ss s.prev

theorem map_snd_filter_zip_map {α β : Type*} (P : α → Bool) (g : α → β) :
    ∀ l : List α, ((l.zip (l.map g)).filter fun p => P p.1).map Prod.snd = (l.filter P).map g
  | [] => rfl
  | a :: l => by
    by_cases h : P a = true
    · simp [h, map_snd_filter_zip_map P g l]
    · simp [h, map_snd_filter_zip_map P g l]

theorem mem_maskSet_of_testBit {m : ℕ} (hm : ∀ k : Fin t.tag.rank, !m.testBit k || m.testBit
    (t.perm k)) : ∀ i ∈ (maskSet t.tag m : Set (Fin t.tag.rank)), t.perm i ∈ maskSet t.tag m :=
  fun i hi => by
    have := hm i
    rw [Finset.mem_coe, mem_maskSet] at hi
    rw [hi] at this
    exact mem_maskSet.2 (by simpa using this)

theorem twistedParabolicSum_eq_of_chainCheck [Fintype (WeylGroup t.tag)] (q : ℕ) :
    ∀ (ss : List (TwistedStep t)) (m : ℕ), twistedChainCheck ss m = true →
      twistedParabolicSum t (maskSet t.tag m) q = (ss.map fun s => s.value q).prod
  | [], m, h => by
    simp only [twistedChainCheck, beq_iff_eq] at h
    subst h
    rw [maskSet_zero, Finset.coe_empty, twistedParabolicSum_empty, List.map_nil, List.prod_nil]
  | s :: ss, m, h => by
    simp only [twistedChainCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hs⟩, hss⟩ := h
    simp only [TwistedStep.check, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨hcert, hsub⟩, hρJ⟩, hρJ'⟩, hρJ''⟩, hlam⟩, hperm⟩ := hs
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hsub hρJ hρJ' hρJ''
    have hJ : maskSet t.tag s.prev ⊆ maskSet t.tag s.mask := fun k hk => by
      have := hsub k
      rw [mem_maskSet.1 hk] at this
      exact mem_maskSet.2 (by simpa using this)
    have hJρ := mem_maskSet_of_testBit hρJ
    have hJ'ρ := mem_maskSet_of_testBit hρJ'
    have hJ'ρ' : ∀ i ∈ (maskSet t.tag s.prev : Set (Fin t.tag.rank)),
        t.perm.symm i ∈ maskSet t.tag s.prev := fun i hi => by
      have := hρJ'' i
      rw [Finset.mem_coe, mem_maskSet] at hi
      rw [hi] at this
      exact mem_maskSet.2 (by simpa using this)
    obtain ⟨hL, hlens⟩ := s.cert.isOrbitList hJ hcert
    have hlamρ : permLattice t.perm (decodeVec (τ := t.tag) s.cert.lam) =
        decodeVec s.cert.lam := OrbitCert.eq_of_ofFn_beq hlam
    rw [twistedParabolicSum_eq_mul (Finset.coe_subset.2 hJ) hJ'ρ hJ'ρ',
      hL.twistedCosetSum_eq_sum hJρ hJ'ρ' hlamρ,
      twistedParabolicSum_eq_of_chainCheck q ss s.prev hss, List.map_cons, List.prod_cons]
    congr 1
    rw [TwistedStep.value, ← sum_map_pow_prodExps, ← (hperm.map _).sum_eq, TwistedStep.rhoLens,
      hlens, map_snd_filter_zip_map (fun a => isPermInvB t (decodeVec a)), List.filter_map,
      List.map_map, List.map_map]
    simp only [isPermInvB_eq_decide]
    rfl

end CFSG.Timmesfeld.ExceptionalOrders
