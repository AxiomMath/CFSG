module

public import CFSG.Timmesfeld.Orders.ExceptionalTorus
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Chevalley.GraphFixedRankOneBruhat

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Conj

variable {τ : Tag} {K : Type} [Field K]

@[expose] def coordReflect (τ : Tag) (i : Fin τ.rank) (c : Fin τ.rank → Kˣ) : Fin τ.rank → Kˣ :=
  c * Pi.mulSingle i (∏ j, c j ^ (-τ.cartan j i))

theorem list_prod_map_torusElt (i : Fin τ.rank) (l : List Kˣ) :
    (l.map (torusElt τ K i)).prod = torusElt τ K i l.prod := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, List.prod_nil, torusElt_one]
  | cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, torusElt_mul]

theorem list_prod_conj {G : Type*} [Group G] (n : G) :
    ∀ l : List G, n * l.prod * n⁻¹ = (l.map fun x => n * x * n⁻¹).prod
  | [] => by simp
  | x :: l => by
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← list_prod_conj n l]
    group

theorem weylElt_conj_torusCoordHom (i : Fin τ.rank) (c : Fin τ.rank → Kˣ) :
    weylElt τ K i 1 * ((torusCoordHom τ K c : torusGroup τ K) :
        (Module.End K (RootModule τ K))ˣ) * (weylElt τ K i 1)⁻¹ =
      ((torusCoordHom τ K (coordReflect τ i c) : torusGroup τ K) :
        (Module.End K (RootModule τ K))ˣ) := by
  have h1 : ((torusCoordHom τ K (coordReflect τ i c) : torusGroup τ K) :
      (Module.End K (RootModule τ K))ˣ) =
      ((torusCoordHom τ K c : torusGroup τ K) : (Module.End K (RootModule τ K))ˣ) *
        torusElt τ K i (∏ j, c j ^ (-τ.cartan j i)) := by
    rw [coordReflect, map_mul, Subgroup.coe_mul, coe_torusCoordHom_mulSingle]
  have h3 : torusElt τ K i (∏ j, c j ^ (-τ.cartan j i)) =
      (List.ofFn fun j => torusElt τ K i (c j ^ (-τ.cartan j i))).prod := by
    rw [← List.prod_ofFn, ← list_prod_map_torusElt, List.map_ofFn]
    rfl
  rw [h1, h3, coe_torusCoordHom, list_prod_conj, List.map_ofFn,
    ← list_prod_ofFn_mul _ _ fun j j' => torusElt_mul_comm _ _ _ _]
  refine congrArg List.prod (List.ofFn_inj.2 (funext fun j => ?_))
  exact weylElt_one_mul_torusElt_mul_inv τ K i j (c j)

@[expose] def iterReflect (τ : Tag) (ω : List (Fin τ.rank)) (c : Fin τ.rank → Kˣ) :
    Fin τ.rank → Kˣ :=
  ω.foldr (fun i c => coordReflect τ i c) c

theorem list_prod_weylElt_conj_torusCoordHom (ω : List (Fin τ.rank)) (c : Fin τ.rank → Kˣ) :
    (ω.map fun i => weylElt τ K i 1).prod * ((torusCoordHom τ K c : torusGroup τ K) :
        (Module.End K (RootModule τ K))ˣ) * ((ω.map fun i => weylElt τ K i 1).prod)⁻¹ =
      ((torusCoordHom τ K (iterReflect τ ω c) : torusGroup τ K) :
        (Module.End K (RootModule τ K))ˣ) := by
  induction ω with
  | nil => simp [iterReflect]
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, iterReflect, List.foldr_cons, ← iterReflect,
      ← weylElt_conj_torusCoordHom, ← ih]
    group

theorem list_prod_map_mulSingle {ω : List (Fin τ.rank)} (hω : ω.Nodup)
    (y : Fin τ.rank → Kˣ) :
    (ω.map fun i => Pi.mulSingle i (y i)).prod = fun k => if k ∈ ω then y k else 1 := by
  classical
  rw [← List.prod_toFinset _ hω]
  funext k
  rw [Finset.prod_apply]
  simp only [Pi.mulSingle_apply]
  rw [Finset.prod_ite_eq]
  simp

theorem iterReflect_eq {ω : List (Fin τ.rank)} (hω : ω.Nodup)
    (horth : ∀ i ∈ ω, ∀ j ∈ ω, i ≠ j → τ.cartan i j = 0) (c : Fin τ.rank → Kˣ) :
    iterReflect τ ω c = c * (ω.map fun i => Pi.mulSingle i (∏ j, c j ^ (-τ.cartan j i))).prod := by
  induction ω with
  | nil => simp [iterReflect]
  | cons i ω ih =>
    obtain ⟨hi, hω'⟩ := List.nodup_cons.1 hω
    rw [iterReflect, List.foldr_cons, ← iterReflect, ih hω' fun a ha b hb hab =>
      horth a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab, coordReflect,
      List.map_cons, List.prod_cons]
    have hprod : ∏ j, ((c * (ω.map fun l => Pi.mulSingle l (∏ k, c k ^ (-τ.cartan k l))).prod)
        j) ^ (-τ.cartan j i) = ∏ j, c j ^ (-τ.cartan j i) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [list_prod_map_mulSingle hω', Pi.mul_apply, mul_zpow]
      by_cases hj : j ∈ ω
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        rw [horth j (List.mem_cons_of_mem _ hj) i List.mem_cons_self hji, neg_zero, zpow_zero,
          zpow_zero, mul_one]
      · simp [hj]
    rw [hprod]
    ac_rfl

end Conj

variable {t : TwistTag} {K : Type} [Field K] (σ : K →+* K)

@[expose] def compatSubgroup : Subgroup (Fin t.tag.rank → Kˣ) where
  carrier := {c | ∀ i, c (t.perm i) = Units.map σ.toMonoidHom (c i)}
  one_mem' := fun i => by simp
  mul_mem' := fun ha hb i => by simp [ha i, hb i]
  inv_mem' := fun ha i => by simp [ha i]

theorem mem_compatSubgroup {c : Fin t.tag.rank → Kˣ} :
    c ∈ compatSubgroup σ ↔ ∀ i, c (t.perm i) = Units.map σ.toMonoidHom (c i) :=
  Iff.rfl

@[expose] def compatTorus : Subgroup (ModGL t.tag K) :=
  (compatSubgroup σ).map ((torusGroup t.tag K).subtype.comp (torusCoordHom t.tag K))

theorem mem_compatTorus {h : ModGL t.tag K} :
    h ∈ compatTorus σ ↔ ∃ c ∈ compatSubgroup σ, (torusCoordHom t.tag K c : ModGL t.tag K) = h :=
  Subgroup.mem_map

theorem compatTorus_le_torusGroup : compatTorus σ ≤ torusGroup t.tag K := by
  rintro _ ⟨c, -, rfl⟩
  exact (torusCoordHom t.tag K c).2

theorem compatTorus_le_graphFixedRootTorus : compatTorus σ ≤ graphFixedRootTorus t K σ := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨s, rfl⟩ := exists_compatDiag_eq (σ := σ) hc
  have h := list_prod_orbitH (K := K) (σ := σ) s
  change (torusCoordHom t.tag K (compatDiag t σ s) : ModGL t.tag K) ∈ _
  rw [coe_torusCoordHom, List.ofFn_eq_map, ← h]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootTorus t σ a (s a)

theorem orthogonal_orbitWord (a : Fin t.foldedTag.rank) :
    ∀ i ∈ t.orbitWord a, ∀ j ∈ t.orbitWord a, i ≠ j → t.tag.cartan i j = 0 :=
  fun _ hi _ hj hij => t.cartan_eq_zero_of_mem_orbit ((t.mem_orbitWord).1 hi)
    ((t.mem_orbitWord).1 hj) hij

theorem list_prod_orbitWord_mulSingle (a : Fin t.foldedTag.rank) (y : Fin t.tag.rank → Kˣ) :
    ((t.orbitWord a).map fun i => Pi.mulSingle i (y i)).prod =
      fun k => if k ∈ t.orbit a then y k else 1 := by
  rw [list_prod_map_mulSingle (t.nodup_orbitWord a)]
  funext k
  simp only [t.mem_orbitWord]

theorem iterReflect_orbitWord_mem {a : Fin t.foldedTag.rank} {c : Fin t.tag.rank → Kˣ}
    (hc : c ∈ compatSubgroup σ) : iterReflect t.tag (t.orbitWord a) c ∈ compatSubgroup σ := by
  classical
  rw [iterReflect_eq (t.nodup_orbitWord a) (orthogonal_orbitWord a),
    list_prod_orbitWord_mulSingle]
  refine mul_mem hc fun k => ?_
  have hy : (∏ j, c j ^ (-t.tag.cartan j (t.perm k))) =
      Units.map σ.toMonoidHom (∏ j, c j ^ (-t.tag.cartan j k)) := by
    simp only [map_prod, map_zpow]
    rw [← Equiv.prod_comp t.perm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hc j, t.cartan_perm]
  have hmem : t.perm k ∈ t.orbit a ↔ k ∈ t.orbit a := by
    rw [t.mem_orbit_iff, t.mem_orbit_iff, t.orbitIndex_perm]
  by_cases hk : k ∈ t.orbit a
  · simp only [hk, hmem.2 hk, ↓reduceIte, hy]
  · simp only [hk, mt hmem.1 hk, ↓reduceIte, map_one]

theorem canonicalRep_orbitReflection_conj_mem_compatTorus (a : Fin t.foldedTag.rank)
    {h : ModGL t.tag K} (hh : h ∈ compatTorus σ) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * h *
      (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ ∈ compatTorus σ := by
  obtain ⟨c, hc, rfl⟩ := (mem_compatTorus σ).1 hh
  rw [canonicalRep_orbitReflection, list_prod_weylElt_conj_torusCoordHom]
  exact (mem_compatTorus σ).2 ⟨_, iterReflect_orbitWord_mem σ hc, rfl⟩

theorem list_prod_sq_of_commute {G : Type*} [Group G] {ι : Type*} (f : ι → G) :
    ∀ {ω : List ι}, ω.Nodup → (∀ i ∈ ω, ∀ j ∈ ω, i ≠ j → Commute (f i) (f j)) →
      (ω.map f).prod * (ω.map f).prod = (ω.map fun i => f i * f i).prod
  | [], _, _ => by simp
  | i :: ω, hω, hc => by
    obtain ⟨hi, hω'⟩ := List.nodup_cons.1 hω
    have hcomm : Commute (f i) (ω.map f).prod := Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hc i List.mem_cons_self j (List.mem_cons_of_mem _ hj) fun h => hi (h ▸ hj)
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      ← list_prod_sq_of_commute f hω' fun a ha b hb hab =>
        hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab,
      mul_assoc, ← mul_assoc (ω.map f).prod, ← hcomm.eq]
    group

theorem canonicalRep_orbitReflection_sq_mem_compatTorus (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ compatTorus σ := by
  rw [canonicalRep_orbitReflection, list_prod_sq_of_commute _ (t.nodup_orbitWord a)
    fun i hi j hj hij => commute_weylElt_weylElt K ((t.mem_orbitWord).1 hi)
      ((t.mem_orbitWord).1 hj) hij 1 1]
  simp only [weylElt_one_mul_self]
  refine (mem_compatTorus σ).2 ⟨((t.orbitWord a).map fun i => Pi.mulSingle i (-1 : Kˣ)).prod, ?_,
    ?_⟩
  · rw [list_prod_orbitWord_mulSingle a fun _ => -1]
    intro k
    have hmem : t.perm k ∈ t.orbit a ↔ k ∈ t.orbit a := by
      rw [t.mem_orbit_iff, t.mem_orbit_iff, t.orbitIndex_perm]
    by_cases hk : k ∈ t.orbit a
    · simp only [hk, hmem.2 hk, ↓reduceIte]
      exact Units.ext (by simp)
    · simp only [hk, mt hmem.1 hk, ↓reduceIte, map_one]
  · rw [map_list_prod, List.map_map, Subgroup.val_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    exact coe_torusCoordHom_mulSingle i (-1)

theorem canonicalRep_orbitReflection_inv_conj_mem_compatTorus (a : Fin t.foldedTag.rank)
    {h : ModGL t.tag K} (hh : h ∈ compatTorus σ) :
    (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ * h *
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ compatTorus σ := by
  set n := canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
  have hn2 := canonicalRep_orbitReflection_sq_mem_compatTorus σ a
  have e : n⁻¹ * h * n = (n * n)⁻¹ * (n * h * n⁻¹) * (n * n) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hn2) (canonicalRep_orbitReflection_conj_mem_compatTorus σ a hh))
    hn2

theorem compatTorus_le_graphFixedRootGroup : compatTorus σ ≤ graphFixedRootGroup t K σ :=
  (compatTorus_le_graphFixedRootTorus σ).trans (graphFixedRootTorus_le t K σ)

theorem card_compatTorus_mul [Finite K] :
    Nat.card (compatTorus (t := t) σ) *
        Nat.card ↥(compatSubgroup (t := t) σ ⊓ (zpowMatrix (G := Kˣ) t.tag.cartan).ker) =
      Nat.card (compatSubgroup (t := t) σ) := by
  set f : (Fin t.tag.rank → Kˣ) →* ModGL t.tag K :=
    (torusGroup t.tag K).subtype.comp (torusCoordHom t.tag K)
  have hker : f.ker = (zpowMatrix (G := Kˣ) t.tag.cartan).ker := by
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← torusCoordHom_eq_one_iff]
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  set g := f.domRestrict (compatSubgroup (t := t) σ)
  have hrange : g.range = compatTorus σ := MonoidHom.domRestrict_range _ f
  have hkerg : Nat.card g.ker =
      Nat.card ↥(compatSubgroup (t := t) σ ⊓ (zpowMatrix (G := Kˣ) t.tag.cartan).ker) := by
    rw [MonoidHom.ker_domRestrict, hker, inf_comm, ← Subgroup.subgroupOf_map_subtype]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv)
  rw [← hrange, ← hkerg, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

end CFSG.Timmesfeld.ExceptionalOrders
