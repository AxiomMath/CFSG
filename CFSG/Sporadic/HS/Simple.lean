module

public import CFSG.Sporadic.HS.Chain

public section

namespace CFSG.Sporadic.SmallF2

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

variable {D : VecData} {c : ℕ} (hF : Facts D c)
include hF

theorem rep_pairG_all : ∀ l < (L D).size, Rep D.n (L D)[l]! (pairG (gs D) l) := by
  obtain ⟨h2, hinv, -⟩ := chainOK_parts hF.chain
  exact rep_pairG (rep_letters hF) h2 hinv

theorem subTreeFacts {j : ℕ} (hj : j < D.subReps.size) :
    TreeFacts D.n (S D)[j]! (lv D) (pairG (gs D)) D.subReps[j]! :=
  treeOK_facts (fun l hl => rep_pairG_all hF l (levelLetters_lt hl)) (hF.subTrees j hj)

omit hF in
theorem lettersGroup_lv : lettersGroup (lv D) (pairG (gs D)) = lvl D 1 := rfl

omit hF in
theorem orbit_conj {H : Subgroup (J D)} {x p q : Fin D.n} (hp : p ∈ MulAction.orbit H x)
    (hq : q ∈ MulAction.orbit H x) : ∃ g ∈ H, g • p = q := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  obtain ⟨⟨v, hv⟩, rfl⟩ := hq
  refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
  show (v * u⁻¹) • (u • x) = v • x
  rw [mul_smul, inv_smul_smul]

omit hF in
theorem orbit_smul_mem' {H : Subgroup (J D)} {x p : Fin D.n} {g : J D} (hg : g ∈ H)
    (hp : p ∈ MulAction.orbit H x) : g • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  refine ⟨⟨g * u, H.mul_mem hg hu⟩, ?_⟩
  show (g * u) • x = g • (u • x)
  exact mul_smul g u x

theorem mem_subTree_iff {j : ℕ} (hj : j < D.subReps.size) (p : Fin D.n) :
    (∃ t < (S D)[j]!.pts.size, ap (S D)[j]!.pts t = p.val) ↔
      p ∈ MulAction.orbit (lvl D 1) (⟨D.subReps[j]!, (subTreeFacts hF hj).r_lt⟩ : Fin D.n) :=
  ((subTreeFacts hF hj).mem_orbit_iff p).symm

theorem labs_iff {j : ℕ} (hj : j < D.subReps.size) (p : Fin D.n) :
    (labs D)[p.val]! = j ↔ ∃ t < (S D)[j]!.pts.size, ap (S D)[j]!.pts t = p.val := by
  constructor
  · intro h
    have hm := hF.labs_mem p.val p.isLt
    simp only [inTreeB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
    rw [h] at hm
    exact ⟨_, hm.1, hm.2⟩
  · rintro ⟨t, ht, hp⟩
    rw [← hp]
    exact hF.labs_pts j hj t ht

@[expose] noncomputable def subLab {k : ℕ} (hk : D.subReps.size = k + 1) (p : Fin D.n) :
    Fin (k + 1) :=
  ⟨(labs D)[p.val]!, by rw [← hk]; exact hF.labs_lt p.val p.isLt⟩

theorem subLab_orb {k : ℕ} (hk : D.subReps.size = k + 1) (p q : Fin D.n)
    (h : subLab hF hk p = subLab hF hk q) : ∃ g ∈ lvl D 1, g • p = q := by
  have hpq : (labs D)[p.val]! = (labs D)[q.val]! := congrArg Fin.val h
  have hjk : (labs D)[q.val]! < D.subReps.size := hF.labs_lt q.val q.isLt
  exact orbit_conj ((mem_subTree_iff hF hjk p).1 ((labs_iff hF hjk p).1 hpq))
    ((mem_subTree_iff hF hjk q).1 ((labs_iff hF hjk q).1 rfl))

theorem subLab_inv {k : ℕ} (hk : D.subReps.size = k + 1) :
    ∀ g ∈ lvl D 1, ∀ p : Fin D.n, subLab hF hk (g • p) = subLab hF hk p := by
  intro g hg p
  apply Fin.ext
  show (labs D)[(g • p).val]! = (labs D)[p.val]!
  have hjk : (labs D)[p.val]! < D.subReps.size := hF.labs_lt p.val p.isLt
  rw [labs_iff hF hjk, mem_subTree_iff hF hjk]
  exact orbit_smul_mem' hg ((mem_subTree_iff hF hjk p).1 ((labs_iff hF hjk p).1 rfl))

theorem card_subLab {k : ℕ} (hk : D.subReps.size = k + 1) (i : Fin (k + 1)) :
    (Finset.univ.filter (fun p : Fin D.n => subLab hF hk p = i)).card = D.subSizes[i.val]! := by
  classical
  have hik : i.val < D.subReps.size := by rw [hk]; exact i.isLt
  have hTF := subTreeFacts hF hik
  have hc := hTF.card_orbit
  have hset : MulAction.orbit (lettersGroup (lv D) (pairG (gs D)))
      (⟨D.subReps[i.val]!, hTF.r_lt⟩ : Fin D.n) =
      ↑(Finset.univ.filter (fun p : Fin D.n => subLab hF hk p = i)) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hTF.mem_orbit_iff p, ← labs_iff hF hik p]
    simp only [Finset.mem_univ, true_and]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  rw [hc]
  have h := congrArg (fun L : List ℕ => L[i.val]?) hF.subSizes
  have hi' : i.val < (S D).size := by rw [hF.S_size]; exact hik
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi',
    Option.map_some] at h
  rw [getElem!_pos (S D) i.val hi', getElem!_def, ← h]

theorem subLab_root {k : ℕ} (hk : D.subReps.size = k + 1) : subLab hF hk (root hF) = 0 := by
  apply Fin.ext
  show (labs D)[0]! = 0
  have hTF := subTreeFacts hF hF.k_pos
  have h := hF.labs_pts 0 hF.k_pos 0 hTF.size_pos
  rwa [hTF.root, hF.rep0] at h

theorem isPreprimitive (horb0 : D.orbSizes[0]! = D.n) {k : ℕ} (hk : D.subReps.size = k + 1)
    (hdiv : ∀ S : Finset (Fin (k + 1)), 0 ∈ S → (∑ i ∈ S, D.subSizes[i.val]!) ∣ D.n →
      S = {0} ∨ S = Finset.univ) :
    MulAction.IsPreprimitive (J D) (Fin D.n) := by
  have := isPretransitive hF horb0
  apply isPreprimitive_of_suborbit_labels (root hF) (lvl D 1) (fun g hg => lvl_one_fix hF hg)
    (subLab hF hk) (subLab_inv hF hk) (subLab_orb hF hk)
  intro S hS hdvd
  rw [subLab_root hF hk] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin D.n => subLab hF hk p = i)).card) =
      ∑ i ∈ S, D.subSizes[i.val]! := Finset.sum_congr rfl fun i _ => card_subLab hF hk i
  rw [hsum, Fintype.card_fin] at hdvd
  exact hdiv S hS hdvd

theorem tupleEq_basis_of_one {X : Table} (hX : Rep D.n X (1 : J D)) :
    tupleEq (apT X D.basis) D.basis = true := by
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq, apT_size, true_and]
  rw [allIn_eq_true]
  intro t _ ht
  rw [apT_get _ _ ht, hX _ (hF.basis_lt t ht), idx_one]
  simp

theorem eq_one_of_tupleEq {g : J D} {X : Table} (hX : Rep D.n X g)
    (h : tupleEq (apT X D.basis) D.basis = true) : g = 1 := by
  apply eq_one_of_fix_basis hF.toBaseFacts
  intro t ht
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq] at h
  have := (allIn_eq_true.1 h.2) t (Nat.zero_le _) ht
  simp only [beq_iff_eq] at this
  rw [apT_get _ _ ht, hX _ (hF.basis_lt t ht)] at this
  exact this

theorem orderOf_of_ordOK {g : J D} {X : Table} (hX : Rep D.n X g) {pe : ℕ × ℕ}
    (hp : pe.1.Prime) (h : ordOK D.n D.basis X pe = true) : orderOf g = pe.1 ^ pe.2 := by
  simp only [ordOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨he, h1⟩, h2⟩ := h
  have : Fact pe.1.Prime := ⟨hp⟩
  have hpow1 : g ^ pe.1 ^ (pe.2 - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel he]
    exact eq_one_of_tupleEq hF (Rep.powT (n_lt_two_pow hF) hX _) h1
  have hpow2 : ¬g ^ pe.1 ^ (pe.2 - 1) = 1 := by
    intro e
    have hR := Rep.powT (n_lt_two_pow hF) hX (pe.1 ^ (pe.2 - 1))
    rw [e] at hR
    rw [tupleEq_basis_of_one hF hR] at h2
    exact absurd h2 (by decide)
  have := orderOf_eq_prime_pow hpow2 hpow1
  rwa [Nat.sub_add_cancel he] at this

theorem orderOf_r0 (hp : D.ord0.1.Prime) : orderOf (r0 D) = D.ord0.1 ^ D.ord0.2 :=
  orderOf_of_ordOK hF (rep_R0_zero hF) hp hF.ord0

theorem orderOf_r1 (hp : D.ord1.1.Prime) : orderOf (r1 D) = D.ord1.1 ^ D.ord1.2 :=
  orderOf_of_ordOK hF (rep_R0_one hF) hp hF.ord1

theorem orderOf_r01 (hp : D.ord01.1.Prime) : orderOf (r0 D * r1 D) = D.ord01.1 ^ D.ord01.2 :=
  orderOf_of_ordOK hF (Rep.compT (rep_R0_zero hF) (rep_R0_one hF)) hp hF.ord01

theorem isSimpleGroup_J (horb0 : D.orbSizes[0]! = D.n) (hn2 : 2 ≤ D.n) {k : ℕ}
    (hk : D.subReps.size = k + 1)
    (hdiv : ∀ S : Finset (Fin (k + 1)), 0 ∈ S → (∑ i ∈ S, D.subSizes[i.val]!) ∣ D.n →
      S = {0} ∨ S = Finset.univ)
    (hp0 : D.ord0.1.Prime) (hp1 : D.ord1.1.Prime) (hp01 : D.ord01.1.Prime)
    (hcop : Nat.Coprime (D.ord0.1 ^ D.ord0.2) (D.ord1.1 ^ D.ord1.2))
    (hprod : Nat.Coprime (D.ord01.1 ^ D.ord01.2)
      (∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]!)) :
    IsSimpleGroup (J D) := by
  have := faithful hF.toBaseFacts
  have := isPreprimitive hF horb0 hk hdiv
  have : Finite (J D) := inferInstance
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin D.n) ?_ (r0 D) (r1 D) (closure_r hF)
    (root hF) ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn2
  · rw [orderOf_r0 hF hp0, orderOf_r1 hF hp1]; exact hcop
  · rw [orderOf_r01 hF hp01, card_stabilizer_root hF]; exact hprod

theorem isSimpleGroup_seedUnits (horb0 : D.orbSizes[0]! = D.n) (hn2 : 2 ≤ D.n) {k : ℕ}
    (hk : D.subReps.size = k + 1)
    (hdiv : ∀ S : Finset (Fin (k + 1)), 0 ∈ S → (∑ i ∈ S, D.subSizes[i.val]!) ∣ D.n →
      S = {0} ∨ S = Finset.univ)
    (hp0 : D.ord0.1.Prime) (hp1 : D.ord1.1.Prime) (hp01 : D.ord01.1.Prime)
    (hcop : Nat.Coprime (D.ord0.1 ^ D.ord0.2) (D.ord1.1 ^ D.ord1.2))
    (hprod : Nat.Coprime (D.ord01.1 ^ D.ord01.2)
      (∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]!)) :
    IsSimpleGroup (CFSG.Blueprint.NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ :=
  @MulEquiv.isSimpleGroup _ _ _ _
    (isSimpleGroup_J hF horb0 hn2 hk hdiv hp0 hp1 hp01 hcop hprod) (seedEquiv hF.toBaseFacts)

theorem card_seedUnits :
    Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ =
      ∏ l ∈ Finset.Ico 0 D.base.size, D.orbSizes[l]! := by
  rw [Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv, ← card_lvl hF (Nat.zero_le _),
    lvl_zero hF, Subgroup.card_top]

end CFSG.Sporadic.SmallF2
