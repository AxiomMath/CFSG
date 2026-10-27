module

public import CFSG.Monster.VisCert.FrameRows
public import CFSG.Monster.VisCert.Delta
public import Mathlib.GroupTheory.GroupAction.Primitive

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible

@[expose] def lettersIn (lo hi : ℕ) (w : List ℕ) : Bool := w.all fun g => decide (lo ≤ g ∧ g < hi)

@[expose] def ambientOK : Bool :=
  allTo (fun j => lettersIn 0 15 ambientWords[j]! &&
    actWord frameMatrices ambientWords[j]! frameSeedVec == fusionOrbitReps[j + 1]!) 5

@[expose] def witnessOK (j : ℕ) (e : FusionWitness) : Bool :=
  decide (e.src < 6) && decide (e.dst < 6) && lettersIn 1 15 e.srcWord &&
    lettersIn 1 15 e.dstWord && actWord frameMatrices e.srcWord fusionOrbitReps[e.src]! == e.v &&
    actWord frameMatrices e.dstWord fusionOrbitReps[e.dst]! == e.w &&
    actWord frameMatrices ambientWords[j]! e.v == e.w

@[expose] def fusionEdges (j : ℕ) : List (ℕ × ℕ) :=
  (fusionWitnesses[j]!).toList.map fun e => (e.src, e.dst)

@[expose] def reachStep (E : List (ℕ × ℕ)) (S : List ℕ) : List ℕ :=
  S ++ E.filterMap fun e => if e.1 ∈ S then some e.2 else if e.2 ∈ S then some e.1 else none

@[expose] def reachFrom (E : List (ℕ × ℕ)) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => reachStep E (reachFrom E n)

@[expose] def fusionOK : Bool :=
  allTo (fun j => (fusionWitnesses[j]!).toList.all (witnessOK j) &&
    allTo (fun k => decide (k ∈ reachFrom (fusionEdges j) 6)) 6) 5

theorem ambientOK_eq_true : ambientOK = true := by decide +kernel

theorem fusionOK_eq_true : fusionOK = true := by decide +kernel

theorem mem_reachFrom {E : List (ℕ × ℕ)} {P : ℕ → Prop} (h0 : P 0)
    (hE : ∀ e ∈ E, (P e.1 ↔ P e.2)) : ∀ n, ∀ k ∈ reachFrom E n, P k
  | 0, k, hk => by
    simp only [reachFrom, List.mem_singleton] at hk
    subst hk
    exact h0
  | n + 1, k, hk => by
    simp only [reachFrom, reachStep, List.mem_append, List.mem_filterMap] at hk
    rcases hk with hk | ⟨e, he, hek⟩
    · exact mem_reachFrom h0 hE n k hk
    · by_cases h1 : e.1 ∈ reachFrom E n
      · rw [ite_eq_left h1, Option.some.injEq] at hek
        subst hek
        exact (hE e he).1 (mem_reachFrom h0 hE n _ h1)
      · rw [ite_eq_right h1] at hek
        by_cases h2 : e.2 ∈ reachFrom E n
        · rw [ite_eq_left h2, Option.some.injEq] at hek
          subst hek
          exact (hE e he).2 (mem_reachFrom h0 hE n _ h2)
        · rw [ite_eq_right h2] at hek
          exact absurd hek (by simp)

theorem lettersIn_spec {lo hi : ℕ} {w : List ℕ} (h : lettersIn lo hi w = true) :
    ∀ g ∈ w, lo ≤ g ∧ g < hi := by
  intro g hg
  have := List.all_eq_true.1 h g hg
  simpa using this

@[expose] def tAmb (j : Fin 5) : GLV := wordGL ambientWords[(j : ℕ)]!

theorem ambient_spec (j : Fin 5) :
    (∀ g ∈ ambientWords[(j : ℕ)]!, g < 15) ∧
      actWord frameMatrices ambientWords[(j : ℕ)]! frameSeedVec =
        fusionOrbitReps[(j : ℕ) + 1]! := by
  have h := allTo_spec ambientOK_eq_true j.2
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨fun g hg => (lettersIn_spec h.1 g hg).2, h.2⟩

theorem tAmb_smul (j : Fin 5) : tAmb j • twoΩCls = frameRep j.succ := by
  rw [tAmb, ← dec_seed, wordGL_smul_dec _ (ambient_spec j).1, frameRep]
  exact congrArg dec (ambient_spec j).2

theorem tAmb_mem_Kvis (j : Fin 5) : tAmb j ∈ Kvis := wordGL_mem_Kvis _ (ambient_spec j).1

theorem tAmb_mem_Hvis (j : Fin 5) : tAmb j ∈ Hvis := Kvis_le_Hvis (tAmb_mem_Kvis j)

@[expose] def fusionGroup (j : Fin 5) : Subgroup GLV := Nvis ⊔ Subgroup.zpowers (tAmb j)

theorem fusionGroup_le_Hvis (j : Fin 5) : fusionGroup j ≤ Hvis :=
  sup_le Nvis_le_Hvis ((Subgroup.zpowers_le).2 (tAmb_mem_Hvis j))

theorem Nvis_le_fusionGroup (j : Fin 5) : Nvis ≤ fusionGroup j := le_sup_left

theorem tAmb_mem_fusionGroup (j : Fin 5) : tAmb j ∈ fusionGroup j :=
  le_sup_right (a := Nvis) (Subgroup.mem_zpowers _)

theorem witness_spec (j : Fin 5) {e : FusionWitness} (he : e ∈ fusionWitnesses[(j : ℕ)]!) :
    e.src < 6 ∧ e.dst < 6 ∧ (∀ g ∈ e.srcWord, 1 ≤ g ∧ g < 15) ∧
      (∀ g ∈ e.dstWord, 1 ≤ g ∧ g < 15) ∧
      actWord frameMatrices e.srcWord fusionOrbitReps[e.src]! = e.v ∧
      actWord frameMatrices e.dstWord fusionOrbitReps[e.dst]! = e.w ∧
      actWord frameMatrices ambientWords[(j : ℕ)]! e.v = e.w := by
  have h := allTo_spec fusionOK_eq_true j.2
  rw [Bool.and_eq_true] at h
  have hw := List.all_eq_true.1 h.1 e (Array.mem_toList_iff.2 he)
  simp only [witnessOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨hs, hd⟩, hsw⟩, hdw⟩, hv⟩, hwv⟩, ht⟩ := hw
  exact ⟨hs, hd, lettersIn_spec hsw, lettersIn_spec hdw, hv, hwv, ht⟩

theorem witness_edge (j : Fin 5) {e : FusionWitness} (he : e ∈ fusionWitnesses[(j : ℕ)]!) :
    dec fusionOrbitReps[e.dst]! ∈
      MulAction.orbit (fusionGroup j) (dec fusionOrbitReps[e.src]!) := by
  obtain ⟨-, -, hsw, hdw, hv, hwv, ht⟩ := witness_spec j he
  have hnA := wordGL_mem_Nvis _ hsw
  have hnB := wordGL_mem_Nvis _ hdw
  have hA : dec e.v = wordGL e.srcWord • dec fusionOrbitReps[e.src]! := by
    rw [wordGL_smul_dec _ (fun g hg => (hsw g hg).2), hv]
  have hB : dec e.w = wordGL e.dstWord • dec fusionOrbitReps[e.dst]! := by
    rw [wordGL_smul_dec _ (fun g hg => (hdw g hg).2), hwv]
  have hT : dec e.w = tAmb j • dec e.v := by
    rw [tAmb, wordGL_smul_dec _ (ambient_spec j).1, ht]
  have hmem : (wordGL e.dstWord)⁻¹ * tAmb j * wordGL e.srcWord ∈ fusionGroup j :=
    (fusionGroup j).mul_mem ((fusionGroup j).mul_mem
      ((fusionGroup j).inv_mem (Nvis_le_fusionGroup j hnB)) (tAmb_mem_fusionGroup j))
      (Nvis_le_fusionGroup j hnA)
  refine ⟨⟨_, hmem⟩, ?_⟩
  change ((wordGL e.dstWord)⁻¹ * tAmb j * wordGL e.srcWord) • dec fusionOrbitReps[e.src]! = _
  rw [mul_smul, mul_smul, ← hA, ← hT, hB, inv_smul_smul]

section Fusion

variable (hΔ : frameDelta = ⋃ t : Fin 6, MulAction.orbit Nvis (frameRep t))
include hΔ

omit hΔ in
theorem orbit_fusionGroup_subset (j : Fin 5) :
    MulAction.orbit (fusionGroup j) twoΩCls ⊆ frameDelta := by
  rintro _ ⟨⟨u, hu⟩, rfl⟩
  exact (smul_mem_frameDelta_iff (fusionGroup_le_Hvis j hu)).2 twoΩCls_mem_frameDelta

omit hΔ in
theorem fusionGroup_mem_orbit_reps (j : Fin 5) :
    ∀ k < 6, dec fusionOrbitReps[k]! ∈ MulAction.orbit (fusionGroup j) twoΩCls := by
  intro k hk
  have hall := allTo_spec fusionOK_eq_true j.2
  rw [Bool.and_eq_true] at hall
  have hreach := of_decide_eq_true (allTo_spec hall.2 hk)
  refine mem_reachFrom (E := fusionEdges j)
    (P := fun k => dec fusionOrbitReps[k]! ∈ MulAction.orbit (fusionGroup j) twoΩCls)
    (by rw [← frameRep_zero]; exact MulAction.mem_orbit_self _) ?_ 6 k hreach
  intro p hp
  simp only [fusionEdges, List.mem_map, Array.mem_toList_iff] at hp
  obtain ⟨e, he, rfl⟩ := hp
  have hedge := witness_edge j he
  have horb := MulAction.orbit_eq_iff.2 hedge
  constructor
  · intro hsrc
    rw [← MulAction.orbit_eq_iff] at hsrc ⊢
    exact horb.trans hsrc
  · intro hdst
    rw [← MulAction.orbit_eq_iff] at hdst ⊢
    exact horb.symm.trans hdst

theorem orbit_fusionGroup (j : Fin 5) :
    MulAction.orbit (fusionGroup j) twoΩCls = frameDelta := by
  refine Set.Subset.antisymm (orbit_fusionGroup_subset j) ?_
  rw [hΔ]
  rintro x hx
  obtain ⟨t, ⟨⟨n, hn⟩, rfl⟩⟩ := Set.mem_iUnion.1 hx
  exact MulAction.mem_orbit_of_mem_orbit (⟨n, Nvis_le_fusionGroup j hn⟩ : fusionGroup j)
    (fusionGroup_mem_orbit_reps j t t.2)

variable (hstab : ∀ u ∈ Hvis, u • twoΩCls = twoΩCls ↔ u ∈ Nvis)
include hstab

theorem fusionGroup_eq_Hvis (j : Fin 5) : fusionGroup j = Hvis := by
  refine le_antisymm (fusionGroup_le_Hvis j) fun h hh => ?_
  have hx : h • twoΩCls ∈ MulAction.orbit (fusionGroup j) twoΩCls := by
    rw [orbit_fusionGroup hΔ j]
    exact (smul_mem_frameDelta_iff hh).2 twoΩCls_mem_frameDelta
  obtain ⟨⟨m, hm⟩, hmf⟩ := hx
  change m • twoΩCls = h • twoΩCls at hmf
  have hfix : (m⁻¹ * h) • twoΩCls = twoΩCls := by
    rw [mul_smul, ← hmf, inv_smul_smul]
  have hN := (hstab _ (Hvis.mul_mem (Hvis.inv_mem (fusionGroup_le_Hvis j hm)) hh)).1 hfix
  have := (fusionGroup j).mul_mem hm (Nvis_le_fusionGroup j hN)
  rwa [mul_inv_cancel_left] at this

end Fusion

@[expose] def deltaSub : SubMulAction Hvis L2 where
  carrier := frameDelta
  smul_mem' h _ hx := (smul_mem_frameDelta_iff h.2).2 hx

@[expose] def fDelta : deltaSub := ⟨twoΩCls, twoΩCls_mem_frameDelta⟩

theorem coe_smul_deltaSub (h : Hvis) (x : deltaSub) :
    ((h • x : deltaSub) : L2) = (h : GLV) • (x : L2) := rfl

theorem mem_stabilizer_fDelta (h : Hvis) :
    h ∈ MulAction.stabilizer Hvis fDelta ↔ (h : GLV) • twoΩCls = twoΩCls := by
  rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
  rfl

theorem frameRep_one_ne : frameRep 1 ≠ twoΩCls := by
  rw [← dec_seed, frameRep]
  intro h
  have := dec_injective (by decide) (by norm_num) h
  exact absurd this (by decide)

section Primitive

variable (hΔ : frameDelta = ⋃ t : Fin 6, MulAction.orbit Nvis (frameRep t))
include hΔ

theorem isPretransitive : MulAction.IsPretransitive Hvis deltaSub := by
  refine ⟨fun x y => ?_⟩
  have hx : (x : L2) ∈ MulAction.orbit (fusionGroup 0) twoΩCls := by
    rw [orbit_fusionGroup hΔ 0]
    exact x.2
  have hy : (y : L2) ∈ MulAction.orbit (fusionGroup 0) twoΩCls := by
    rw [orbit_fusionGroup hΔ 0]
    exact y.2
  obtain ⟨⟨a, ha⟩, hax⟩ := hx
  obtain ⟨⟨b, hb⟩, hby⟩ := hy
  change a • twoΩCls = (x : L2) at hax
  change b • twoΩCls = (y : L2) at hby
  refine ⟨⟨b * a⁻¹, Hvis.mul_mem (fusionGroup_le_Hvis 0 hb)
    (Hvis.inv_mem (fusionGroup_le_Hvis 0 ha))⟩, Subtype.ext ?_⟩
  rw [coe_smul_deltaSub]
  change (b * a⁻¹) • (x : L2) = y
  rw [← hax, ← hby, smul_smul, inv_mul_cancel_right]

omit hΔ in
theorem nontrivial_deltaSub : Nontrivial deltaSub := by
  refine ⟨⟨fDelta, ⟨frameRep 1, ?_⟩, fun h => frameRep_one_ne (congrArg Subtype.val h).symm⟩⟩
  have h1 : frameRep 1 = tAmb 0 • twoΩCls := (tAmb_smul 0).symm
  rw [h1]
  exact (smul_mem_frameDelta_iff (tAmb_mem_Hvis 0)).2 twoΩCls_mem_frameDelta

variable (hstab : ∀ u ∈ Hvis, u • twoΩCls = twoΩCls ↔ u ∈ Nvis)
include hstab

theorem isCoatom_stabilizer : IsCoatom (MulAction.stabilizer Hvis fDelta) := by
  refine ⟨fun htop => ?_, fun T hT => ?_⟩
  · have hmem : (⟨tAmb 0, tAmb_mem_Hvis 0⟩ : Hvis) ∈ MulAction.stabilizer Hvis fDelta :=
      htop ▸ Subgroup.mem_top _
    rw [mem_stabilizer_fDelta] at hmem
    exact frameRep_one_ne ((tAmb_smul 0).symm.trans hmem)
  · obtain ⟨g, hgT, hgS⟩ := IsConcreteLE.exists_of_lt hT
    rw [mem_stabilizer_fDelta] at hgS
    have hgf : (g : GLV) • twoΩCls ∈ frameDelta :=
      (smul_mem_frameDelta_iff g.2).2 twoΩCls_mem_frameDelta
    rw [hΔ] at hgf
    obtain ⟨k, ⟨⟨n, hn⟩, hnk⟩⟩ := Set.mem_iUnion.1 hgf
    change n • frameRep k = (g : GLV) • twoΩCls at hnk
    have hnf : n • twoΩCls = twoΩCls := (hstab n (Nvis_le_Hvis hn)).2 hn
    obtain ⟨j, rfl⟩ : ∃ j : Fin 5, k = j.succ := by
      rcases Fin.eq_zero_or_eq_succ k with h0 | hj
      · subst h0
        rw [frameRep_zero, hnf] at hnk
        exact absurd hnk.symm hgS
      · exact hj
    rw [← tAmb_smul j] at hnk
    have hs : ((tAmb j)⁻¹ * n⁻¹ * (g : GLV)) • twoΩCls = twoΩCls := by
      rw [mul_smul, mul_smul, ← hnk, smul_smul n⁻¹ n, inv_mul_cancel, one_smul, inv_smul_smul]
    have hsH : (tAmb j)⁻¹ * n⁻¹ * (g : GLV) ∈ Hvis :=
      Hvis.mul_mem (Hvis.mul_mem (Hvis.inv_mem (tAmb_mem_Hvis j))
        (Hvis.inv_mem (Nvis_le_Hvis hn))) g.2
    have hsN := (hstab _ hsH).1 hs
    set T' : Subgroup GLV := T.map Hvis.subtype with hT'
    have hNT : Nvis ≤ T' := fun x hx => by
      have hxS : (⟨x, Nvis_le_Hvis hx⟩ : Hvis) ∈ MulAction.stabilizer Hvis fDelta := by
        rw [mem_stabilizer_fDelta]
        exact (hstab x (Nvis_le_Hvis hx)).2 hx
      exact ⟨_, hT.le hxS, rfl⟩
    have hgT' : (g : GLV) ∈ T' := ⟨g, hgT, rfl⟩
    have htT : tAmb j ∈ T' := by
      have h1 : n⁻¹ * (g : GLV) * ((tAmb j)⁻¹ * n⁻¹ * (g : GLV))⁻¹ ∈ T' :=
        T'.mul_mem (T'.mul_mem (T'.inv_mem (hNT hn)) hgT') (T'.inv_mem (hNT hsN))
      have e : n⁻¹ * (g : GLV) * ((tAmb j)⁻¹ * n⁻¹ * (g : GLV))⁻¹ = tAmb j := by group
      rwa [e] at h1
    have hHT : Hvis ≤ T' := by
      rw [← fusionGroup_eq_Hvis hΔ hstab j]
      exact sup_le hNT ((Subgroup.zpowers_le).2 htT)
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := hHT x.2
    rwa [show y = x from Subtype.ext hxy] at hy

theorem isPreprimitive : MulAction.IsPreprimitive Hvis deltaSub := by
  have := isPretransitive hΔ
  have := nontrivial_deltaSub
  exact (MulAction.isCoatom_stabilizer_iff_preprimitive Hvis fDelta).1
    (isCoatom_stabilizer hΔ hstab)

end Primitive

end CFSG.Monster.VisCert
