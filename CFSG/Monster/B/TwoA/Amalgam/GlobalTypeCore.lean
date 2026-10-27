module

public import CFSG.Monster.B.TwoA.Amalgam.LocalLabel
public import CFSG.Monster.B.TwoA.Amalgam.TriangleCore
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTriple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

@[expose] def rootPairOrbit
    {v : CVert} (ρ : vStab v →* GStar) (w : CVert) (x : rootClass) :
    Set rootClass :=
  {x' | ∃ q : vStab v, (q : Shat) ∈ vStab w ∧
    (SemidirectProduct.inl (x' : stdGroup) : GStar) =
      (ρ q)⁻¹ * SemidirectProduct.inl (x : stdGroup) * ρ q}

@[expose] def nativeRoots
    {v : CVert} (ρ : vStab v →* GStar) (w : CVert) : Set rootClass :=
  {x | ∃ z ∈ cgraph.commonNeighbors v w, ∃ y : vStab v, ((y : Shat) : Dfull) = clabel z ∧
    ρ y = SemidirectProduct.inl (x : stdGroup)}

@[expose] def IsLocalLabel
    {v : CVert} (ρ : vStab v →* GStar)
    (iv : cgraph.neighborSet v ≃ rootClass) : Prop :=
  (∀ (g : vStab v) (z : cgraph.neighborSet v),
    SemidirectProduct.inl (iv (stabAct g z) : stdGroup) =
      (ρ g)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ g) ∧
  (∀ z z' : cgraph.neighborSet v, z ≠ z' →
    (cgraph.Adj z z' ↔ Commute (iv z : stdGroup) (iv z'))) ∧
  ∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
    ρ y = SemidirectProduct.inl (iv z : stdGroup)

@[expose] def IsAmbientRootOrbits
    {v : CVert} (ρ : vStab v →* GStar) (w : CVert) : Prop :=
  ∃ r : Fin 4 → rootClass,
    (∀ x : rootClass, ∃! k, x ∈ rootPairOrbit ρ w (r k)) ∧
    rootPairOrbit ρ w (r 0) = nativeRoots ρ w ∧
    (∀ k, (rootPairOrbit ρ w (r k)).ncard = ![3510, 142155, 694980, 3127410] k) ∧
    ∀ k, ∀ x ∈ rootPairOrbit ρ w (r k),
      {x' | x' ∈ nativeRoots ρ w ∧ x' ≠ x ∧ Commute (x' : stdGroup) x}.ncard =
        ![693, 22, 126, 22] k

@[expose] def AmbientRootOrbitsHyp :
    Prop :=
  ∀ v w : CVert, w ∈ sphereThree v → ∃ (ρ : vStab v →* GStar)
    (iv : cgraph.neighborSet v ≃ rootClass), IsLocalLabel ρ iv ∧ IsAmbientRootOrbits ρ w

@[expose] def outerOrbit
    (v w : CVert) (n : ℕ) : Set CVert :=
  {u | u ∈ cgraph.neighborSet w ∧ u ∉ cgraph.commonNeighbors v w ∧
    (pairStabOrbit v w u).ncard = n}

theorem pairStabOrbit_comm
    (a b c : CVert) : pairStabOrbit b a c = pairStabOrbit a b c := by
  ext c'
  exact exists_congr fun s => and_left_comm

theorem mem_pairStabOrbit_self
    (a b c : CVert) : c ∈ pairStabOrbit a b c :=
  ⟨1, cvMul_one a, cvMul_one b, cvMul_one c⟩

theorem pairStabOrbit_eq_of_mem
    {a b c c' : CVert} (h : c' ∈ pairStabOrbit a b c) :
    pairStabOrbit a b c' = pairStabOrbit a b c := by
  obtain ⟨s, ha, hb, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨t, hta, htb, rfl⟩
    exact ⟨s * t, by rw [cvMul_mul, ha, hta], by rw [cvMul_mul, hb, htb], cvMul_mul c s t⟩
  · rintro ⟨t, hta, htb, rfl⟩
    refine ⟨s⁻¹ * t, ?_, ?_, ?_⟩
    · rw [cvMul_mul, cvMul_inv_eq_of_cvMul_eq ha, hta]
    · rw [cvMul_mul, cvMul_inv_eq_of_cvMul_eq hb, htb]
    · rw [← cvMul_mul, mul_inv_cancel_left]

theorem pairStabOrbit_subset_neighborSet
    {a b c : CVert} (hc : c ∈ cgraph.neighborSet a) :
    pairStabOrbit a b c ⊆ cgraph.neighborSet a := by
  rintro _ ⟨s, ha, -, rfl⟩
  have h := (cgraph_adj_cvMul a c s).2 hc
  rwa [ha] at h

theorem inl_injective_rootClass
    {x y : rootClass}
    (h : (SemidirectProduct.inl (x : stdGroup) : GStar) = SemidirectProduct.inl (y : stdGroup)) :
    x = y :=
  Subtype.ext (SemidirectProduct.inl_injective h)

section Transport

variable {w : CVert} {ρ : vStab w →* GStar} {iv : cgraph.neighborSet w ≃ rootClass}
  (hL : IsLocalLabel ρ iv) (v : CVert)
include hL

theorem mem_rootPairOrbit_iff (z z' : cgraph.neighborSet w) :
    iv z' ∈ rootPairOrbit ρ v (iv z) ↔ (z' : CVert) ∈ pairStabOrbit w v z := by
  constructor
  · rintro ⟨q, hqv, hq⟩
    rw [← hL.1 q z] at hq
    have e : z' = stabAct q z := iv.injective (inl_injective_rootClass hq)
    exact ⟨q, mem_vStab.1 q.2, mem_vStab.1 hqv, by rw [e, coe_stabAct]⟩
  · rintro ⟨s, hsw, hsv, hz⟩
    have e : stabAct ⟨s, mem_vStab.2 hsw⟩ z = z' := Subtype.ext hz
    exact ⟨⟨s, mem_vStab.2 hsw⟩, mem_vStab.2 hsv, by rw [← hL.1, e]⟩

theorem pairStabOrbit_eq_image (z : cgraph.neighborSet w) :
    pairStabOrbit w v z = Subtype.val '' (iv.symm '' rootPairOrbit ρ v (iv z)) := by
  ext u
  constructor
  · intro hu
    have hu' : u ∈ cgraph.neighborSet w := pairStabOrbit_subset_neighborSet z.2 hu
    exact ⟨⟨u, hu'⟩, ⟨iv ⟨u, hu'⟩, (mem_rootPairOrbit_iff hL v z ⟨u, hu'⟩).2 hu,
      iv.symm_apply_apply _⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (mem_rootPairOrbit_iff hL v z (iv.symm x)).1 (by rwa [iv.apply_symm_apply])

theorem ncard_pairStabOrbit (z : cgraph.neighborSet w) :
    (pairStabOrbit w v z).ncard = (rootPairOrbit ρ v (iv z)).ncard := by
  rw [pairStabOrbit_eq_image hL v z, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_image_of_injective _ iv.symm.injective]

theorem mem_nativeRoots_iff (z : cgraph.neighborSet w) :
    iv z ∈ nativeRoots ρ v ↔ (z : CVert) ∈ cgraph.commonNeighbors w v := by
  constructor
  · rintro ⟨z', hz', y, hy, hρ⟩
    have h1 := hL.2.2 ⟨z', hz'.1⟩ y hy
    rw [hρ] at h1
    have e : z = ⟨z', hz'.1⟩ := iv.injective (inl_injective_rootClass h1)
    rw [e]
    exact hz'
  · intro hz
    obtain ⟨s, hs⟩ := cvMul_transitive cv0 w
    obtain ⟨y, hy⟩ := exists_vStab_eq_clabel hs z
    exact ⟨z, hz, y, hy, hL.2.2 z y hy⟩

theorem ncard_commuting_nativeRoots (u : cgraph.neighborSet w)
    (hu : (u : CVert) ∉ cgraph.commonNeighbors w v) :
    {x' | x' ∈ nativeRoots ρ v ∧ x' ≠ iv u ∧ Commute (x' : stdGroup) (iv u)}.ncard =
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors w v).ncard := by
  have e : {x' | x' ∈ nativeRoots ρ v ∧ x' ≠ iv u ∧ Commute (x' : stdGroup) (iv u)} =
      iv '' {z | (z : CVert) ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors w v} := by
    ext x
    obtain ⟨z, rfl⟩ := iv.surjective x
    rw [Set.mem_ofPred_eq, iv.injective.mem_set_image, Set.mem_ofPred_eq,
      mem_nativeRoots_iff hL v]
    constructor
    · rintro ⟨hz, hne, hc⟩
      have hne' : z ≠ u := fun e => hne (congrArg iv e)
      exact ⟨(cgraph.adj_comm _ _).1 ((hL.2.1 z u hne').2 hc), hz⟩
    · rintro ⟨hadj, hz⟩
      have hne' : z ≠ u := fun e => hu (by rw [← e]; exact hz)
      exact ⟨hz, fun e => hne' (iv.injective e),
        (hL.2.1 z u hne').1 ((cgraph.adj_comm _ _).1 hadj)⟩
  have e2 : (cgraph.neighborSet u ∩ cgraph.commonNeighbors w v).ncard =
      {z : cgraph.neighborSet w |
        (z : CVert) ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors w v}.ncard := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx.2.1⟩, hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  rw [e, Set.ncard_image_of_injective _ iv.injective, e2]

end Transport

theorem ambient_sizes_injective :
    ∀ j k : Fin 4, (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) j =
      ![3510, 142155, 694980, 3127410] k → j = k := by
  decide

theorem ambient_counts_pos : ∀ j : Fin 4, 0 < (![693, 22, 126, 22] : Fin 4 → ℕ) j := by
  decide

theorem type_three_neighborhood_global_distance_bound_of
    (hamb : AmbientRootOrbitsHyp)
    {v w : CVert} (hw : w ∈ sphereThree v) :
    cgraph.neighborSet w \ cgraph.commonNeighbors v w =
        outerOrbit v w 142155 ∪ outerOrbit v w 694980 ∪ outerOrbit v w 3127410 ∧
    {O | ∃ u ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w, O = pairStabOrbit v w u} =
        {outerOrbit v w 142155, outerOrbit v w 694980, outerOrbit v w 3127410} ∧
    (∀ n : ℕ, ∀ u ∈ outerOrbit v w n, pairStabOrbit v w u = outerOrbit v w n) ∧
    (outerOrbit v w 142155).ncard = 142155 ∧ (outerOrbit v w 694980).ncard = 694980 ∧
    (outerOrbit v w 3127410).ncard = 3127410 ∧
    (∀ u ∈ outerOrbit v w 142155,
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 22) ∧
    (∀ u ∈ outerOrbit v w 694980,
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 126) ∧
    (∀ u ∈ outerOrbit v w 3127410,
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 22) ∧
    (∀ u ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w, cgraph.dist v u = 2) ∧
    (∀ u ∈ cgraph.neighborSet w, u ∈ cgraph.neighborSet v ∨ cgraph.dist v u = 2) ∧
    ∀ u, cgraph.Adj w u → cgraph.dist v u ≠ 3 := by
  obtain ⟨ρ, iv, hL, r, hpart, h0, hsize, hcount⟩ := hamb w v (mem_sphereThree_comm.1 hw)
  have hMeq : cgraph.commonNeighbors v w = cgraph.commonNeighbors w v :=
    cgraph.commonNeighbors_symm v w
  set O : Fin 4 → Set CVert := fun k => pairStabOrbit w v (iv.symm (r k)) with hOdef
  have hmemO : ∀ (u : cgraph.neighborSet w) (k : Fin 4),
      (u : CVert) ∈ O k ↔ iv u ∈ rootPairOrbit ρ v (r k) := by
    intro u k
    have h := mem_rootPairOrbit_iff hL v (iv.symm (r k)) u
    rw [iv.apply_symm_apply] at h
    exact h.symm
  have hOsub : ∀ k, O k ⊆ cgraph.neighborSet w := fun k =>
    pairStabOrbit_subset_neighborSet (iv.symm (r k)).2
  have hpart' : ∀ u ∈ cgraph.neighborSet w, ∃! k, u ∈ O k := by
    intro u hu
    obtain ⟨k, hk, huniq⟩ := hpart (iv ⟨u, hu⟩)
    exact ⟨k, (hmemO ⟨u, hu⟩ k).2 hk, fun j hj => huniq j ((hmemO ⟨u, hu⟩ j).1 hj)⟩
  have hdisj : ∀ {u : CVert} {j k : Fin 4}, u ∈ O j → u ∈ O k → j = k := by
    intro u j k hj hk
    obtain ⟨i, -, huniq⟩ := hpart' u (hOsub j hj)
    rw [huniq j hj, huniq k hk]
  have hO0 : O 0 = cgraph.commonNeighbors v w := by
    ext u
    constructor
    · intro hu
      have hu' := hOsub 0 hu
      have h := (hmemO ⟨u, hu'⟩ 0).1 hu
      rw [h0, mem_nativeRoots_iff hL v] at h
      rw [hMeq]
      exact h
    · intro hu
      have hu' : u ∈ cgraph.neighborSet w := hu.2
      refine (hmemO ⟨u, hu'⟩ 0).2 ?_
      rw [h0, mem_nativeRoots_iff hL v, ← hMeq]
      exact hu
  have hOcard : ∀ k, (O k).ncard = (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k := by
    intro k
    have h := ncard_pairStabOrbit hL v (iv.symm (r k))
    rw [iv.apply_symm_apply] at h
    exact h.trans (hsize k)
  have hOorb : ∀ k, ∀ u ∈ O k, pairStabOrbit v w u = O k := fun k u hu => by
    rw [pairStabOrbit_comm w v u]
    exact pairStabOrbit_eq_of_mem hu
  have hOcnt : ∀ k, ∀ u ∈ O k, u ∉ cgraph.commonNeighbors v w →
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard =
        (![693, 22, 126, 22] : Fin 4 → ℕ) k := by
    intro k u hu hnot
    have hu' := hOsub k hu
    have h := hcount k (iv ⟨u, hu'⟩) ((hmemO ⟨u, hu'⟩ k).1 hu)
    rw [ncard_commuting_nativeRoots hL v ⟨u, hu'⟩ (by rwa [← hMeq])] at h
    rw [hMeq]
    exact h
  have hnotM : ∀ {k : Fin 4} {u : CVert}, k ≠ 0 → u ∈ O k → u ∉ cgraph.commonNeighbors v w :=
    fun hk hu hm => hk (hdisj hu (by rw [hO0]; exact hm))
  have hout : ∀ k : Fin 4, k ≠ 0 →
      outerOrbit v w ((![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k) = O k := by
    intro k hk
    ext u
    constructor
    · rintro ⟨hu1, hu2, hu3⟩
      obtain ⟨j, hj, -⟩ := hpart' u hu1
      have hjk : j = k := ambient_sizes_injective j k (by rw [← hOcard j, ← hOorb j u hj, hu3])
      rw [← hjk]
      exact hj
    · intro hu
      exact ⟨hOsub k hu, hnotM hk hu, by rw [hOorb k u hu, hOcard k]⟩
  have h1 : outerOrbit v w 142155 = O 1 := hout 1 (by decide)
  have h2 : outerOrbit v w 694980 = O 2 := hout 2 (by decide)
  have h3 : outerOrbit v w 3127410 = O 3 := hout 3 (by decide)
  have hcases : ∀ u ∈ cgraph.neighborSet w, u ∉ cgraph.commonNeighbors v w →
      ∃ k : Fin 4, k ≠ 0 ∧ u ∈ O k := by
    intro u hu1 hu2
    obtain ⟨j, hj, -⟩ := hpart' u hu1
    refine ⟨j, fun hj0 => hu2 ?_, hj⟩
    rw [← hO0, ← hj0]
    exact hj
  have hdist : ∀ u ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w, cgraph.dist v u = 2 := by
    rintro u ⟨hu1, hu2⟩
    obtain ⟨k, -, hk⟩ := hcases u hu1 hu2
    have hc := hOcnt k u hk hu2
    have hne : (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard ≠ 0 := by
      rw [hc]
      exact (ambient_counts_pos k).ne'
    obtain ⟨z, hzu, hzM⟩ := Set.nonempty_of_ncard_ne_zero hne
    have hvw := (cgraph_dist_eq_two_iff.1 hw.1).2.1
    refine cgraph_dist_eq_two_iff.2 ⟨fun e => hvw ?_, fun hvu => hu2 ⟨hvu, hu1⟩, z, hzM.1,
      cgraph.adj_symm hzu⟩
    rw [e]
    exact cgraph.adj_symm hu1
  have hnbr : ∀ u ∈ cgraph.neighborSet w, u ∈ cgraph.neighborSet v ∨ cgraph.dist v u = 2 := by
    intro u hu
    by_cases hM : u ∈ cgraph.commonNeighbors v w
    · exact Or.inl hM.1
    · exact Or.inr (hdist u ⟨hu, hM⟩)
  refine ⟨?_, ?_, ?_, by rw [h1, hOcard 1]; rfl, by rw [h2, hOcard 2]; rfl,
    by rw [h3, hOcard 3]; rfl, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, hdist, hnbr, ?_⟩
  · ext u
    constructor
    · rintro ⟨hu1, hu2⟩
      obtain ⟨k, hk, hku⟩ := hcases u hu1 hu2
      rw [h1, h2, h3]
      fin_cases k
      · exact absurd rfl hk
      · exact Or.inl (Or.inl hku)
      · exact Or.inl (Or.inr hku)
      · exact Or.inr hku
    · rintro ((h | h) | h) <;> exact ⟨h.1, h.2.1⟩
  · ext X
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      obtain ⟨k, hk, hku⟩ := hcases u hu1 hu2
      rw [hOorb k u hku, h1, h2, h3]
      fin_cases k
      · exact absurd rfl hk
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · have hrep : ∀ k : Fin 4, k ≠ 0 →
          ∃ u ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w, O k = pairStabOrbit v w u :=
        fun k hk => ⟨_, ⟨hOsub k (mem_pairStabOrbit_self _ _ _),
          hnotM hk (mem_pairStabOrbit_self _ _ _)⟩,
          (hOorb k _ (mem_pairStabOrbit_self _ _ _)).symm⟩
      rintro (rfl | rfl | rfl)
      · rw [h1]
        exact hrep 1 (by decide)
      · rw [h2]
        exact hrep 2 (by decide)
      · rw [h3]
        exact hrep 3 (by decide)
  · intro n u hu
    obtain ⟨k, hk, hku⟩ := hcases u hu.1 hu.2.1
    have hn : n = (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k := by
      rw [← hu.2.2, hOorb k u hku, hOcard k]
    rw [hn, hout k hk, hOorb k u hku]
  · have hu' := hu
    rw [h1] at hu'
    exact hOcnt 1 u hu' hu.2.1
  · have hu' := hu
    rw [h2] at hu'
    exact hOcnt 2 u hu' hu.2.1
  · have hu' := hu
    rw [h3] at hu'
    exact hOcnt 3 u hu' hu.2.1
  · intro u hu
    rcases hnbr u hu with h | h
    · rw [SimpleGraph.dist_eq_one_iff_adj.2 h]
      decide
    · rw [h]
      decide

end CFSG.Monster.B.TwoA.Amalgam
