module

public import CFSG.Sporadic.Recognition.McLASSpec

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem conj_mem_conjClass {M : Type*} [Group M] {P : Subgroup M} {g t w : M} (hg : g ∈ P)
    (hw : w ∈ conjClass P t) : g * w * g⁻¹ ∈ conjClass P t := by
  obtain ⟨h, hh, rfl⟩ := hw
  exact ⟨g * h, P.mul_mem hg hh, by group⟩

open Classical in
theorem card_filter_comm_conj {M : Type*} [Group M] [Fintype M] {P : Subgroup M}
    {z x y g : M} (hg : g ∈ P) (hy : y = g * x * g⁻¹) :
    ((conjClass P z).toFinset.filter fun w => y * w = w * y).card =
      ((conjClass P z).toFinset.filter fun w => x * w = w * x).card := by
  classical
  subst hy
  refine Finset.card_bij' (fun w _ => g⁻¹ * w * g) (fun w _ => g * w * g⁻¹) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Set.mem_toFinset] at hw ⊢
    refine ⟨by simpa using conj_mem_conjClass (P.inv_mem hg) hw.1, ?_⟩
    calc x * (g⁻¹ * w * g) = g⁻¹ * ((g * x * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * x * g⁻¹)) * g := by rw [hw.2]
      _ = g⁻¹ * w * g * x := by group
  · intro w hw
    simp only [Finset.mem_filter, Set.mem_toFinset] at hw ⊢
    refine ⟨conj_mem_conjClass hg hw.1, ?_⟩
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hw.2]
      _ = g * w * g⁻¹ * (g * x * g⁻¹) := by group
  · intro w _
    group
  · intro w _
    group

theorem ncard_conjClass_mul_ncard_comm {M : Type*} [Group M] [Finite M] (P : Subgroup M)
    (x z : M) :
    (conjClass P x).ncard * (conjClass P z ∩ {w | x * w = w * x}).ncard =
      (conjClass P z).ncard * (conjClass P x ∩ {y | z * y = y * z}).ncard := by
  classical
  have : Fintype M := Fintype.ofFinite M
  set X := (conjClass P x).toFinset with hX
  set Z := (conjClass P z).toFinset with hZ
  have e1 : (conjClass P z ∩ {w | x * w = w * x}).ncard = (Z.filter fun w => x * w = w * x).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp [hZ]
  have e2 : (conjClass P x ∩ {y | z * y = y * z}).ncard = (X.filter fun y => z * y = y * z).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp [hX]
  have hfib : ∀ y ∈ X, (Z.filter fun w => y * w = w * y).card =
      (Z.filter fun w => x * w = w * x).card := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Set.mem_toFinset.1 hy
    exact card_filter_comm_conj hg rfl
  have hfib' : ∀ w ∈ Z, (X.filter fun y => y * w = w * y).card =
      (X.filter fun y => z * y = y * z).card := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := Set.mem_toFinset.1 hw
    rw [← card_filter_comm_conj (P := P) (z := x) hg rfl]
    congr 1
    ext y
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := X) (t := Z) (r := fun y w => y * w = w * y)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
  rw [Finset.sum_congr rfl hfib, Finset.sum_congr rfl hfib', Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul] at hdc
  rw [e1, e2, Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card', ← hX, ← hZ]
  exact hdc

theorem exists_conj_mem_of_card_sylow {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {R S : Subgroup M} (hSR : S ≤ R) (hS : Nat.card S = p ^ (Nat.card R).factorization p)
    {t : M} (ht : t ∈ R) (htp : orderOf t = p) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  let S' : Sylow p R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have htR : IsPGroup p (zpowers (⟨t, ht⟩ : R)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, htp, pow_one]
  obtain ⟨T, hT⟩ := htR.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, ?_⟩
  have htT : (⟨t, ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

variable {n : ℕ}

theorem elemFacts_of_bounds {P : Subgroup (Equiv.Perm (Fin n))} {p NP : ℕ} {r : ElemRow}
    (hrep : Rep n r.rep (tp n r.rep)) (hord : orderOf (tp n r.rep) = p) (hmem : tp n r.rep ∈ P)
    (hcg : ∀ c ∈ r.centGens.toArray,
      tp n c ∈ P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n))))
    (hK : r.centOrder ≤ Nat.card ↥(closure (tp n '' {x | x ∈ r.centGens.toArray})))
    (hcls : r.classSize ≤ (conjClass P (tp n r.rep)).ncard) (hP : Nat.card P = NP)
    (hprod : r.classSize * r.centOrder = NP) : ElemFacts n P p r := by
  set t := tp n r.rep
  set K := closure (tp n '' {x | x ∈ r.centGens.toArray})
  set C := P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))
  have hKle : K ≤ C := by
    rw [closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact hcg c hc
  have hos : (conjClass P t).ncard * Nat.card C = Nat.card P := ncard_conjClass_mul_card P t
  rw [hP, ← hprod] at hos
  have hCle : Nat.card K ≤ Nat.card C := card_le_of_le hKle
  have hPpos : 0 < NP := hP ▸ Nat.card_pos
  have hpos1 : 0 < r.classSize := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hprod
    omega
  have hpos2 : 0 < r.centOrder := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hprod
    omega
  have hcent : Nat.card C = r.centOrder := by
    by_contra hne
    have hlt : r.centOrder < Nat.card C := by omega
    have : r.classSize * r.centOrder < (conjClass P t).ncard * Nat.card C :=
      Nat.mul_lt_mul_of_le_of_lt hcls hlt (hpos1.trans_le hcls)
    omega
  have hclsEq : (conjClass P t).ncard = r.classSize := by
    rw [hcent] at hos
    exact Nat.eq_of_mul_eq_mul_right hpos2 hos
  have hKeq : K = C := Subgroup.eq_of_le_of_card_ge hKle (by rw [hcent]; exact hK)
  exact ⟨hrep, hord, hmem, hKeq, hcent, hclsEq⟩

theorem le_card_closure_of_mulTree (hn : n < 2 ^ 32) {cg : Array Table}
    (hcg : ∀ c ∈ cg, Rep n c (tp n c)) {C : Array Table × Array ℕ × Array ℕ}
    (htree : mulTreeOK n cg C.1 C.2.1 C.2.2 = true) (hdist : hkeysDistinct n C.1.toList = true) :
    C.1.size ≤ Nat.card ↥(closure (tp n '' {x | x ∈ cg})) := by
  set K := closure (tp n '' {x | x ∈ cg})
  have hga : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧ tp n cg[l]! ∈ K := fun l hl =>
    ⟨hcg _ (getElem!_mem_array hl), subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hCK := mulTreeOK_spec hn K (gg := fun l => tp n cg[l]!) hga htree
  have hCrep : ∀ k < C.1.size, Rep n C.1[k]! (tablePerm n C.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hCrep) hdist
  have := length_le_card_of_nodup hnodup fun x hx => by
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
    obtain ⟨c, hc, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hc
  rwa [List.length_map, Array.length_toList] at this

theorem le_ncard_conjClass_of_conjTree {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)}
    (hgP : ∀ l < pg.size, Rep n pg[l]! (gg l) ∧ Rep n pgInv[l]! (gg l)⁻¹ ∧ gg l ∈ P)
    {x : Table} {t : Equiv.Perm (Fin n)} (hx : Rep n x t) {o : Closure}
    (horb : conjTreeOK n pg pgInv x o.1 o.2.1 o.2.2 = true)
    (hdist : hkeysDistinct n o.1.toList = true) : o.1.size ≤ (conjClass P t).ncard := by
  have horb' := conjTreeOK_spec P hgP hx horb
  have horep : ∀ k < o.1.size, Rep n o.1[k]! (tablePerm n o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb' k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hdist
  have := length_le_ncard_of_nodup honodup (S := conjClass P t) fun y hy => by
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hy
    obtain ⟨c, hc, hrep⟩ := horb' k hk
    rw [tablePerm_eq hrep]
    exact ⟨c, hc, rfl⟩
  rwa [List.length_map, Array.length_toList] at this

@[expose] noncomputable def fixedPtNum {n : ℕ} (g : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => g i = i).card

theorem fixedPtNum_conj {n : ℕ} (c g : Equiv.Perm (Fin n)) :
    fixedPtNum (c * g * c⁻¹) = fixedPtNum g := by
  unfold fixedPtNum
  symm
  refine Finset.card_equiv c fun i => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp

theorem mulClosure_cover (hn : n < 2 ^ 32) {gens : Array Table}
    (hg : ∀ c ∈ gens, permOK n c = true) {cap : ℕ}
    (htree : mulTreeOK n gens (mulClosureH n gens cap).1 (mulClosureH n gens cap).2.1
      (mulClosureH n gens cap).2.2 = true)
    (hdist : hkeysDistinct n (mulClosureH n gens cap).1.toList = true)
    (hsize : Nat.card ↥(closure (tp n '' {x | x ∈ gens})) ≤ (mulClosureH n gens cap).1.size) :
    ∀ y ∈ closure (tp n '' {x | x ∈ gens}),
      ∃ k < (mulClosureH n gens cap).1.size, Rep n (mulClosureH n gens cap).1[k]! y := by
  set E := (mulClosureH n gens cap).1 with hE
  set K := closure (tp n '' {x | x ∈ gens}) with hK
  have hga : ∀ l < gens.size, Rep n gens[l]! (tp n gens[l]!) ∧ tp n gens[l]! ∈ K := fun l hl =>
    ⟨rep_tp (hg _ (getElem!_mem_array hl)), subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hCK := mulTreeOK_spec hn K (gg := fun l => tp n gens[l]!) hga htree
  have hCrep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hCmem : ∀ k < E.size, tablePerm n E[k]! ∈ K := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hc
  have hCnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hCrep) hdist
  intro y hy
  have hmem := mem_of_nodup_of_card_le hCnodup (K := K)
    (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
      exact hCmem k hk)
    (by rw [List.length_map, Array.length_toList]; exact hsize) y hy
  obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hmem
  exact ⟨k, hk, hCrep k hk⟩

end CFSG.Sporadic.Recognition.McLAS

end
