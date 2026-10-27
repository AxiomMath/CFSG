module

public import CFSG.Sporadic.Fi22.LH.Tables
public import CFSG.Fischer.Uniq.LocalHyperoval

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def lhSet (i k : ℕ) : Set (Fin 3510) := bset lhc.orb[i]!.sets[k]!

@[expose] noncomputable def lhMem
    (i k : ℕ) : Set D := dset lhc.orb[i]!.sets[k]!

theorem lhMem_eq (i k : ℕ) : lhMem i k = ptD '' lhSet i k := rfl

theorem orbitOK_lhc {i : ℕ} (hi : i < 2) :
    orbitOK orb.alpha orb.beta lhc.B[i]! lhc.orb[i]! lhc.keys[i]! = true :=
  (lh_parts.2.2.2.2.2.2.2.2.2.1 i hi).2.2.2.2.2.2

theorem lhSet_zero
    {i : ℕ} (hi : i < 2) : lhSet i 0 = bset lhc.B[i]! := by
  ext x
  rw [lhSet, mem_bset, mem_bset, (orbitOK_spec (orbitOK_lhc hi)).2.2.2.2.2.1 x.val x.2]

theorem smul_idxSet_eq_image
    (g : J) (S : Set (Fin 3510)) : g • S = (fun x => g • x) '' S := rfl

theorem orbit_lhSet
    {i : ℕ} (hi : i < 2) :
    MulAction.orbit J (lhSet i 0) = lhSet i '' Set.Iio 14080 := by
  obtain ⟨-, -, -, -, -, -, hgen, htree, -⟩ := orbitOK_spec (orbitOK_lhc hi)
  refine orbit_eq_image closure_ab (n := 14080) (by norm_num) (lhSet i)
    (α := fun k => lhc.orb[i]!.pa[k]!) (β := fun k => lhc.orb[i]!.pb[k]!) ?_ ?_
    (fun k => lhc.orb[i]!.par[k]!) (fun k => lhc.orb[i]!.lab[k]!) ?_
  · intro k hk
    refine ⟨(hgen k hk).1, ?_⟩
    rw [smul_idxSet_eq_image]
    exact image_bset rep_alpha (hgen k hk).2.2.1
  · intro k hk
    refine ⟨(hgen k hk).2.1, ?_⟩
    rw [smul_idxSet_eq_image]
    exact image_bset rep_beta (hgen k hk).2.2.2
  · intro k hk hk0
    exact htree k hk0 hk

theorem canonKey_congr {A B : Bits} (h : ∀ x < 3510, bitAt A x = bitAt B x) :
    canonKey A = canonKey B := by
  unfold canonKey
  exact List.filter_congr fun x hx => h x (List.mem_range.1 hx)

theorem keyFind_congr (K : Std.HashMap (List ℕ) ℕ) {A B : Bits}
    (h : ∀ x < 3510, bitAt A x = bitAt B x) : keyFind K A = keyFind K B := by
  unfold keyFind
  rw [canonKey_congr h]

theorem bitAt_eq_of_bset_eq {A B : Bits} (h : bset A = bset B) {x : ℕ} (hx : x < 3510) :
    bitAt A x = bitAt B x := by
  have h' := congrArg (fun S => (⟨x, hx⟩ : Fin 3510) ∈ S) h
  simp only [mem_bset, eq_iff_iff] at h'
  cases hA : bitAt A x <;> cases hB : bitAt B x <;> simp_all

theorem lhSet_inj
    {i : ℕ} (hi : i < 2) {k m : ℕ} (hk : k < 14080) (hm : m < 14080)
    (h : lhSet i k = lhSet i m) : k = m := by
  have hkey := (orbitOK_spec (orbitOK_lhc hi)).2.2.2.2.2.2.2.2
  rw [← hkey k hk, ← hkey m hm]
  exact keyFind_congr _ fun x hx => bitAt_eq_of_bset_eq h hx

theorem lhMem_inj
    {i : ℕ} (hi : i < 2) {k m : ℕ} (hk : k < 14080) (hm : m < 14080)
    (h : lhMem i k = lhMem i m) : k = m :=
  lhSet_inj hi hk hm ((Set.image_injective.2 ptD.injective) h)

theorem mem_lhOrbit_iff
    {i : Fin 2} {T : Set D} :
    T ∈ lhOrbit i ↔ ∃ k < 14080, T = lhMem i.val k := by
  have horb := orbit_lhSet i.2
  rw [lhSet_zero i.2] at horb
  constructor
  · rintro ⟨g, rfl⟩
    have hmem : g • bset lhc.B[i.val]! ∈ MulAction.orbit J (bset lhc.B[i.val]!) := ⟨g, rfl⟩
    rw [horb] at hmem
    obtain ⟨k, hk, hke⟩ := hmem
    refine ⟨k, hk, ?_⟩
    rw [lhRoot_eq, dset, conjPerm_image_ptD, ← smul_idxSet_eq_image, ← hke, lhMem_eq]
  · rintro ⟨k, hk, rfl⟩
    have hmem : lhSet i.val k ∈ MulAction.orbit J (bset lhc.B[i.val]!) := by
      rw [horb]; exact ⟨k, hk, rfl⟩
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, ?_⟩
    rw [lhRoot_eq, dset, conjPerm_image_ptD, ← smul_idxSet_eq_image, lhMem_eq]
    exact congrArg _ hg.symm

theorem lhMem_mem_lhOrbit
    (i : Fin 2) {k : ℕ} (hk : k < 14080) : lhMem i.val k ∈ lhOrbit i :=
  mem_lhOrbit_iff.2 ⟨k, hk, rfl⟩

theorem lhOrbit_eq_image
    (i : Fin 2) : lhOrbit i = lhMem i.val '' Set.Iio 14080 := by
  ext T
  rw [mem_lhOrbit_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

theorem ncard_lhOrbit
    (i : Fin 2) : (lhOrbit i).ncard = 14080 := by
  have hinj : Set.InjOn (lhMem i.val) (Set.Iio 14080) := fun k hk m hm h => lhMem_inj i.2 hk hm h
  rw [lhOrbit_eq_image, hinj.ncard_image]
  rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

theorem lhRoot_eq_lhMem
    (i : Fin 2) : lhRoot i = lhMem i.val 0 := by
  rw [lhRoot_eq, dset, lhMem_eq, lhSet_zero i.2]

theorem conjPerm_mem_lhOrbit
    {i : Fin 2} {T : Set D} (hT : T ∈ lhOrbit i) (g : J) :
    ⇑(Pair.conjPerm pair_D g) '' T ∈ lhOrbit i := by
  obtain ⟨h, rfl⟩ := hT
  refine ⟨g * h, ?_⟩
  rw [Set.image_image, map_mul]
  rfl

theorem lhRoot_one_notMem :
    lhRoot 1 ∉ lhOrbit 0 := by
  intro h
  obtain ⟨k, hk, hke⟩ := mem_lhOrbit_iff.1 h
  have hkey := (orbitOK_spec (orbitOK_lhc (i := 0) (by norm_num))).2.2.2.2.2.2.2.2 k hk
  have hB : ∀ x < 3510, bitAt lhc.B[1]! x = bitAt lhc.orb[0]!.sets[k]! x := by
    intro x hx
    rw [lhRoot_eq, lhMem] at hke
    exact bitAt_eq_of_dset_eq hke hx
  have h1 := lh_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [keyFind_congr _ hB, hkey] at h1
  omega

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

theorem lhOrbit_disjoint
    (i j : Fin 2) (h : i ≠ j) : Disjoint (lhOrbit i) (lhOrbit j) := by
  have key : ∀ T, T ∈ lhOrbit 0 → T ∈ lhOrbit 1 → False := by
    rintro T ⟨g, rfl⟩ ⟨g', hg'⟩
    apply lhRoot_one_notMem
    refine ⟨g'⁻¹ * g, ?_⟩
    rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp, hg', ← Set.image_comp, ← Equiv.Perm.coe_mul,
      ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.coe_one, Set.image_id]
  rw [Set.disjoint_left]
  intro T hi hj
  rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
  · exact h rfl
  · exact key T hi hj
  · exact key T hj hi
  · exact h rfl

theorem tv_eq_conjPerm
    (p : D) : ⇑((pairModel pair_D).tv p) = ⇑(Pair.conjPerm pair_D (p : J)) := by
  funext y
  apply Subtype.ext
  rw [pairModel_tv, Pair.conjPerm_apply, Pair.inv_eq pair_D p.2]

theorem tv_image_mem_lhOrbit
    {i : Fin 2} {T : Set D} (hT : T ∈ lhOrbit i) (p : D) :
    (pairModel pair_D).tv p '' T ∈ lhOrbit i := by
  rw [tv_eq_conjPerm]
  exact conjPerm_mem_lhOrbit hT p

theorem conjPerm_mem_of_invariant {𝒮 : Set (Set D)}
    (h𝒮 : ∀ T ∈ 𝒮, ∀ p, (pairModel pair_D).tv p '' T ∈ 𝒮) (g : J) :
    ∀ T ∈ 𝒮, ⇑(Pair.conjPerm pair_D g) '' T ∈ 𝒮 := by
  have hg : g ∈ Subgroup.closure D := by rw [closure_D]; trivial
  induction hg using Subgroup.closure_induction_left with
  | one => intro T hT; rwa [map_one, Equiv.Perm.coe_one, Set.image_id]
  | mul_left x hx y _ ih =>
    intro T hT
    rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp]
    have := h𝒮 _ (ih T hT) ⟨x, hx⟩
    rwa [tv_eq_conjPerm] at this
  | inv_mul_cancel x hx y _ ih =>
    intro T hT
    rw [Pair.inv_eq pair_D hx, map_mul, Equiv.Perm.coe_mul, Set.image_comp]
    have := h𝒮 _ (ih T hT) ⟨x, hx⟩
    rwa [tv_eq_conjPerm] at this

theorem lhOrbit_subset_of_invariant (𝒮 : Set (Set D))
    (h𝒮 : ∀ T ∈ 𝒮, ∀ p, (pairModel pair_D).tv p '' T ∈ 𝒮) (i : Fin 2) {T : Set D}
    (hT𝒮 : T ∈ 𝒮) (hT : T ∈ lhOrbit i) : lhOrbit i ⊆ 𝒮 := by
  obtain ⟨g, rfl⟩ := hT
  rintro _ ⟨g', rfl⟩
  have := conjPerm_mem_of_invariant h𝒮 (g' * g⁻¹) _ hT𝒮
  have e : ⇑(Pair.conjPerm pair_D (g' * g⁻¹)) '' (⇑(Pair.conjPerm pair_D g) '' lhRoot i) =
      ⇑(Pair.conjPerm pair_D g') '' lhRoot i := by
    rw [← Set.image_comp, ← Equiv.Perm.coe_mul, ← map_mul, inv_mul_cancel_right]
  rwa [e] at this

theorem lhU_ptD
    (i : Fin 3510) : lhU (ptD i) = ptD (uOut i) := lhU_apply i

theorem ptD_symm_lhU
    (x : D) : ptD.symm (lhU x) = uOut (ptD.symm x) := by
  rw [← ptD.apply_symm_apply x, lhU_ptD, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem lhU_lhU
    (x : D) : lhU (lhU x) = x := by
  rw [← ptD.apply_symm_apply x, lhU_ptD, lhU_ptD, ← Equiv.Perm.mul_apply, uOut_mul_self,
    Equiv.Perm.one_apply]

theorem tauIdx_eq_self_iff (i j : Fin 3510) :
    tauIdx i j = j ↔ (ptD i : J) * ptD j = ptD j * ptD i := by
  rw [ptD_commute_iff, tauIdx_apply, ← Fin.val_inj, conjPt_smul_val i.2]

theorem lhU_commute (x y : D) :
    ((lhU x : D) : J) * lhU y = lhU y * lhU x ↔ (x : J) * y = y * x := by
  rw [← ptD.apply_symm_apply x, ← ptD.apply_symm_apply y, lhU_ptD, lhU_ptD,
    ← tauIdx_eq_self_iff, ← tauIdx_eq_self_iff, ← tauAut_apply uOut_mem_tauAut,
    uOut.injective.eq_iff]

theorem lhU_tv (x y : D) :
    lhU ((pairModel pair_D).tv x y) = (pairModel pair_D).tv (lhU x) (lhU y) := by
  have e : ∀ i j : Fin 3510, (pairModel pair_D).tv (ptD i) (ptD j) = ptD (tauIdx i j) := by
    intro i j
    rw [ptD_tauIdx]
    rfl
  rw [← ptD.apply_symm_apply x, ← ptD.apply_symm_apply y, e, lhU_ptD, lhU_ptD, lhU_ptD, e,
    tauAut_apply uOut_mem_tauAut]

theorem lhU_conjPerm
    (g : J) : ∃ g' : J, ∀ x : D,
    lhU (Pair.conjPerm pair_D g x) = Pair.conjPerm pair_D g' (lhU x) := by
  obtain ⟨g', hg'⟩ := conj_mem_range_idxPerm uOut_mem_tauAut g
  refine ⟨g', fun x => ?_⟩
  rw [← ptD.apply_symm_apply x, conjPerm_ptD, lhU_ptD, lhU_ptD, conjPerm_ptD]
  congr 1
  rw [← idxPerm_apply g', hg', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, uOut_inv,
    ← Equiv.Perm.mul_apply uOut uOut, uOut_mul_self, Equiv.Perm.one_apply, idxPerm_apply]

theorem uOut_image_bset {A B : Bits} (h : mapsOnto nfpU A B = true) :
    ⇑uOut '' bset A = bset B :=
  image_bset (G := Equiv.Perm (Fin 3510)) rep_uOut h

theorem lhU_image_dset
    {A B : Bits} (h : mapsOnto nfpU A B = true) :
    ⇑lhU '' dset A = dset B := by
  unfold dset
  rw [Set.image_image, ← uOut_image_bset h, Set.image_image]
  simp only [lhU_ptD]

theorem lh_swap :
    swapOK (lhUTab orb) lhc.B[0]! lhc.B[1]! lhc.orb[0]! lhc.orb[1]! lhc.uIdx = true :=
  lh_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lhU_image_lhRoot_zero :
    ⇑lhU '' lhRoot 0 ∈ lhOrbit 1 := by
  obtain ⟨h0, h1, -, -⟩ := swapOK_spec lh_swap
  have hU : lhUTab orb = nfpU := rfl
  rw [hU] at h1
  have e : lhRoot 0 = dset lhc.B[0]! := lhRoot_eq 0
  rw [e, lhU_image_dset h1]
  exact lhMem_mem_lhOrbit 1 h0

theorem lhU_image_lhRoot_one :
    ⇑lhU '' lhRoot 1 ∈ lhOrbit 0 := by
  obtain ⟨-, -, h2, h3⟩ := swapOK_spec lh_swap
  have hU : lhUTab orb = nfpU := rfl
  rw [hU] at h3
  have e : lhRoot 1 = dset lhc.B[1]! := lhRoot_eq 1
  rw [e, lhU_image_dset h3]
  exact lhMem_mem_lhOrbit 0 h2

theorem lhU_image_mem
    {i : Fin 2} {T : Set D} (hT : T ∈ lhOrbit i) :
    ⇑lhU '' T ∈ lhOrbit (i + 1) := by
  obtain ⟨g, rfl⟩ := hT
  obtain ⟨g', hg'⟩ := lhU_conjPerm g
  have himg : ⇑lhU '' (⇑(Pair.conjPerm pair_D g) '' lhRoot i) =
      ⇑(Pair.conjPerm pair_D g') '' (⇑lhU '' lhRoot i) := by
    rw [Set.image_image, Set.image_image]
    simp only [hg']
  rw [himg]
  apply conjPerm_mem_lhOrbit
  rcases fin_two_cases i with rfl | rfl
  · exact lhU_image_lhRoot_zero
  · exact lhU_image_lhRoot_one

theorem image_lhU_lhOrbit
    (i : Fin 2) : (fun T => ⇑lhU '' T) '' lhOrbit i = lhOrbit (i + 1) := by
  ext T
  constructor
  · rintro ⟨T', hT', rfl⟩
    exact lhU_image_mem hT'
  · intro hT
    refine ⟨⇑lhU '' T, ?_, ?_⟩
    · have := lhU_image_mem hT
      rwa [add_assoc, show (1 : Fin 2) + 1 = 0 by decide, add_zero] at this
    · simp only [Set.image_image, lhU_lhU, Set.image_id']

end CFSG.Sporadic.Fi22
