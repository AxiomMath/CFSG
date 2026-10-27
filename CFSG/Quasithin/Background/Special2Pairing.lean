module

public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.KGFactC31EBasis

public section

namespace CFSG.Quasithin.Special2

open CFSG.Quasithin.KGC31
open scoped commutatorElement

section Comm

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_commute {y y' z : G} (h : ⁅y', z⁆ * y = y * ⁅y', z⁆) :
    ⁅y * y', z⁆ = ⁅y', z⁆ * ⁅y, z⁆ := by
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at *
  calc y * y' * z * (y * y')⁻¹ * z⁻¹ = y * (y' * z * y'⁻¹ * z⁻¹) * z * y⁻¹ * z⁻¹ := by group
    _ = (y' * z * y'⁻¹ * z⁻¹) * y * z * y⁻¹ * z⁻¹ := by rw [← h]
    _ = y' * z * y'⁻¹ * z⁻¹ * (y * z * y⁻¹ * z⁻¹) := by group

theorem commutatorElement_mul_right_of_commute {y z z' : G} (h : ⁅y, z'⁆ * z = z * ⁅y, z'⁆) :
    ⁅y, z * z'⁆ = ⁅y, z⁆ * ⁅y, z'⁆ := by
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at *
  calc y * (z * z') * y⁻¹ * (z * z')⁻¹
      = (y * z * y⁻¹ * z⁻¹) * (z * (y * z' * y⁻¹ * z'⁻¹)) * z⁻¹ := by group
    _ = (y * z * y⁻¹ * z⁻¹) * ((y * z' * y⁻¹ * z'⁻¹) * z) * z⁻¹ := by rw [← h]
    _ = y * z * y⁻¹ * z⁻¹ * (y * z' * y⁻¹ * z'⁻¹) := by group

end Comm

variable {G : Type} [Group G] {V : Subgroup G} {b : ℕ} {q : Fin b → G}

structure Table (V : Subgroup G) (q : Fin b → G) : Prop where
  abV : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v
  centV : ∀ v ∈ V, ∀ i, v * q i = q i * v
  comm : ∀ i j, ⁅q i, q j⁆ ∈ V
  sq : ∀ i, q i * q i ∈ V

@[expose] def tabGroup (V : Subgroup G) (q : Fin b → G) : Subgroup G :=
  Subgroup.closure (Set.range q) ⊔ V

theorem le_tabGroup : V ≤ tabGroup V q := le_sup_right

theorem mem_tabGroup (i : Fin b) : q i ∈ tabGroup V q :=
  le_sup_left (a := Subgroup.closure (Set.range q)) (Subgroup.subset_closure ⟨i, rfl⟩)

theorem tabGroup_eq_closure : tabGroup V q = Subgroup.closure (Set.range q ∪ (V : Set G)) := by
  rw [tabGroup, Subgroup.closure_union, Subgroup.closure_eq]

namespace Table

variable (h : Table V q)
include h

theorem central : ∀ v ∈ V, ∀ y ∈ tabGroup V q, v * y = y * v := by
  have hle : tabGroup V q ≤ Subgroup.centralizer (V : Set G) := by
    refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_iff.mpr fun v hv => h.centV v hv i
    · intro w hw
      exact Subgroup.mem_centralizer_iff.mpr fun v hv => h.abV v hv w hw
  intro v hv y hy
  exact Subgroup.mem_centralizer_iff.mp (hle hy) v hv

theorem commutatorElement_eq_one_of_mem_left {v y : G} (hv : v ∈ V) (hy : y ∈ tabGroup V q) :
    ⁅v, y⁆ = 1 := by
  rw [commutatorElement_def, h.central v hv y hy]
  group

theorem commutatorElement_eq_one_of_mem_right {v y : G} (hv : v ∈ V) (hy : y ∈ tabGroup V q) :
    ⁅y, v⁆ = 1 := by
  rw [commutatorElement_def, ← h.central v hv y hy]
  group

theorem comm_mem_left (j : Fin b) : ∀ y ∈ tabGroup V q, ⁅y, q j⁆ ∈ V := by
  intro y hy
  rw [tabGroup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | hx
    · exact h.comm i j
    · rw [h.commutatorElement_eq_one_of_mem_left hx (mem_tabGroup j)]
      exact V.one_mem
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
    rw [commutatorElement_mul_left_of_commute (h.central _ ihy x hxQ)]
    exact V.mul_mem ihy ihx
  | inv x hx ih =>
    have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
    have h1 := commutatorElement_mul_left_of_commute (y := x⁻¹) (y' := x) (z := q j)
      (h.central _ ih _ ((tabGroup V q).inv_mem hxQ))
    rw [inv_mul_cancel, commutatorElement_one_left] at h1
    rw [eq_inv_of_mul_eq_one_right h1.symm]
    exact V.inv_mem ih

theorem comm_mem {y : G} (hy : y ∈ tabGroup V q) : ∀ z ∈ tabGroup V q, ⁅y, z⁆ ∈ V := by
  intro z hz
  rw [tabGroup_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨j, rfl⟩ | hx
    · exact h.comm_mem_left j y hy
    · rw [h.commutatorElement_eq_one_of_mem_right hx hy]
      exact V.one_mem
  | one => simp
  | mul x x' hx hx' ihx ihx' =>
    have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
    rw [commutatorElement_mul_right_of_commute (h.central _ ihx' x hxQ)]
    exact V.mul_mem ihx ihx'
  | inv x hx ih =>
    have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
    have h1 := commutatorElement_mul_right_of_commute (y := y) (z := x⁻¹) (z' := x)
      (h.central _ ih _ ((tabGroup V q).inv_mem hxQ))
    rw [inv_mul_cancel, commutatorElement_one_right] at h1
    rw [eq_inv_of_mul_eq_one_left h1.symm]
    exact V.inv_mem ih

theorem sq_mem : ∀ y ∈ tabGroup V q, y * y ∈ V := by
  intro y hy
  rw [tabGroup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | hx
    · exact h.sq i
    · exact V.mul_mem hx hx
  | one => simp
  | mul x x' hx hx' ihx ihx' =>
    have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
    have hxQ' : x' ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx'
    have hc := h.comm_mem ((tabGroup V q).inv_mem hxQ) x' hxQ'
    have e : x * x' * (x * x') = x * x * ⁅x⁻¹, x'⁆ * (x' * x') := by
      rw [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem (V.mul_mem ihx hc) ihx'
  | inv x hx ih =>
    have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
    rw [← mul_inv_rev]
    exact V.inv_mem ih

end Table

section Quot

variable (h : Table V q)

abbrev tabV (V : Subgroup G) (q : Fin b → G) : Subgroup ↥(tabGroup V q) :=
  V.subgroupOf (tabGroup V q)

include h in
theorem tabV_normal : (tabV V q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ V := hn
  show (g : G) * n * (g : G)⁻¹ ∈ V
  rw [← h.central _ hn' g g.2]
  simpa using hn'

include h in
theorem quot_comm [(tabV V q).Normal] (a c : ↥(tabGroup V q) ⧸ tabV V q) : a * c = c * a := by
  induction a using QuotientGroup.induction_on with
  | H y =>
  induction c using QuotientGroup.induction_on with
  | H z =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  show ((y : G) * z)⁻¹ * ((z : G) * y) ∈ V
  have e : ((y : G) * z)⁻¹ * ((z : G) * y) = ⁅(z : G)⁻¹, (y : G)⁻¹⁆ := by
    rw [commutatorElement_def]; group
  rw [e]
  exact h.comm_mem ((tabGroup V q).inv_mem z.2) _ ((tabGroup V q).inv_mem y.2)

include h in
theorem quot_sq [(tabV V q).Normal] (a : ↥(tabGroup V q) ⧸ tabV V q) : a * a = 1 := by
  induction a using QuotientGroup.induction_on with
  | H y =>
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact h.sq_mem y y.2

@[expose] noncomputable def qbar (V : Subgroup G) (q : Fin b → G) [(tabV V q).Normal] (i : Fin b) :
    ↥(tabGroup V q) ⧸ tabV V q :=
  ((⟨q i, mem_tabGroup i⟩ : ↥(tabGroup V q)) : ↥(tabGroup V q) ⧸ tabV V q)

@[expose] noncomputable def qprod (V : Subgroup G) (q : Fin b → G) [(tabV V q).Normal]
    (a : Fin b → ZMod 2) : ↥(tabGroup V q) ⧸ tabV V q :=
  (List.ofFn fun i => qbar V q i ^ (a i).val).prod

include h in
theorem qbar_pow_add [(tabV V q).Normal] (x : ↥(tabGroup V q) ⧸ tabV V q) (a a' : ZMod 2) :
    x ^ (a + a').val = x ^ a.val * x ^ a'.val := by
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact quot_sq h x
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx2, pow_add]

include h in
theorem qprod_add [(tabV V q).Normal] (a a' : Fin b → ZMod 2) :
    qprod V q (a + a') = qprod V q a * qprod V q a' := by
  have hc : ∀ x y : ↥(tabGroup V q) ⧸ tabV V q, x * y = y * x := quot_comm h
  let _ : CommGroup (↥(tabGroup V q) ⧸ tabV V q) :=
    { (inferInstance : Group _) with mul_comm := hc }
  unfold qprod
  rw [List.prod_ofFn, List.prod_ofFn, List.prod_ofFn, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, qbar_pow_add h]

include h in
theorem qprod_single [(tabV V q).Normal] (i : Fin b) : qprod V q (Pi.single i 1) = qbar V q i := by
  have hc : ∀ x y : ↥(tabGroup V q) ⧸ tabV V q, x * y = y * x := quot_comm h
  let _ : CommGroup (↥(tabGroup V q) ⧸ tabV V q) :=
    { (inferInstance : Group _) with mul_comm := hc }
  unfold qprod
  rw [List.prod_ofFn, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
    exact pow_one _
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    exact pow_zero _
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem qprod_zero [(tabV V q).Normal] : qprod V q 0 = 1 := by
  simp [qprod]

include h in
theorem qprod_surjective [(tabV V q).Normal] : Function.Surjective (qprod V q) := by
  have key : ∀ y (hy' : y ∈ Subgroup.closure (Set.range q ∪ (V : Set G))) (hy : y ∈ tabGroup V q),
      ∃ a, qprod V q a = ((⟨y, hy⟩ : ↥(tabGroup V q)) : ↥(tabGroup V q) ⧸ tabV V q) := by
    intro y hy'
    induction hy' using Subgroup.closure_induction with
    | mem x hx =>
      intro hy
      rcases hx with ⟨i, rfl⟩ | hx
      · exact ⟨Pi.single i 1, qprod_single h i⟩
      · refine ⟨0, ?_⟩
        rw [qprod_zero]
        exact ((QuotientGroup.eq_one_iff (⟨x, hy⟩ : ↥(tabGroup V q))).mpr
          (show (⟨x, hy⟩ : ↥(tabGroup V q)) ∈ tabV V q from hx)).symm
    | one => intro _; exact ⟨0, by rw [qprod_zero]; rfl⟩
    | mul x x' hx hx' ihx ihx' =>
      intro hy
      have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
      have hxQ' : x' ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx'
      obtain ⟨a, ha⟩ := ihx hxQ
      obtain ⟨a', ha'⟩ := ihx' hxQ'
      refine ⟨a + a', ?_⟩
      rw [qprod_add h, ha, ha']
      rfl
    | inv x hx ih =>
      intro hy
      have hxQ : x ∈ tabGroup V q := tabGroup_eq_closure (V := V) (q := q) ▸ hx
      obtain ⟨a, ha⟩ := ih hxQ
      refine ⟨a, ?_⟩
      rw [ha]
      have hsq := quot_sq h ((⟨x, hxQ⟩ : ↥(tabGroup V q)) : ↥(tabGroup V q) ⧸ tabV V q)
      show _ = ((⟨x, hxQ⟩ : ↥(tabGroup V q))⁻¹ : ↥(tabGroup V q) ⧸ tabV V q)
      exact eq_inv_of_mul_eq_one_left hsq
  intro a
  induction a using QuotientGroup.induction_on with
  | H y =>
  obtain ⟨y, hy⟩ := y
  exact key y (tabGroup_eq_closure (V := V) (q := q) ▸ hy) hy

theorem card_tabV : Nat.card ↥(tabV V q) = Nat.card ↥V :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_tabGroup).toEquiv

include h in
theorem card_quot_le [(tabV V q).Normal] : Nat.card (↥(tabGroup V q) ⧸ tabV V q) ≤ 2 ^ b := by
  have := Nat.card_le_card_of_surjective _ (qprod_surjective h)
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at this

include h in
theorem card_le : Nat.card ↥(tabGroup V q) ≤ 2 ^ b * Nat.card ↥V := by
  have := tabV_normal h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (tabV V q), card_tabV]
  exact Nat.mul_le_mul_right _ (card_quot_le h)

end Quot

section Pairing

@[expose] noncomputable def commHom (h : Table V q) {z : G} (hz : z ∈ tabGroup V q) :
    ↥(tabGroup V q) →* ↥V where
  toFun y := ⟨⁅(y : G), z⁆, h.comm_mem y.2 z hz⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y y' := Subtype.ext (by
    show ⁅(y : G) * y', z⁆ = ⁅(y : G), z⁆ * ⁅(y' : G), z⁆
    rw [commutatorElement_mul_left_of_commute (h.central _ (h.comm_mem y'.2 z hz) y y.2)]
    exact h.abV _ (h.comm_mem y'.2 z hz) _ (h.comm_mem y.2 z hz))

structure Pairing (h : Table V q) (f : Fin b → ↥V →* Multiplicative (ZMod 2)) (js : Fin b → Fin b)
    (M : Fin b → Fin b → ZMod 2) : Prop where
  inv : ∀ k k', ∑ i, M k i * Multiplicative.toAdd (f k' ⟨⁅q i, q (js k')⁆, h.comm i (js k')⟩) =
    if k = k' then 1 else 0

@[expose] noncomputable def pairHom (h : Table V q) (f : Fin b → ↥V →* Multiplicative (ZMod 2))
    (js : Fin b → Fin b) : ↥(tabGroup V q) →* (Fin b → Multiplicative (ZMod 2)) :=
  MonoidHom.pi fun k => (f k).comp (commHom h (mem_tabGroup (js k)))

theorem pairHom_apply (h : Table V q) (f : Fin b → ↥V →* Multiplicative (ZMod 2))
    (js : Fin b → Fin b) (y : ↥(tabGroup V q)) (k : Fin b) :
    pairHom h f js y k = f k (commHom h (mem_tabGroup (js k)) y) := rfl

variable {h : Table V q} {f : Fin b → ↥V →* Multiplicative (ZMod 2)} {js : Fin b → Fin b}
  {M : Fin b → Fin b → ZMod 2}

theorem pairHom_surjective (hP : Pairing h f js M) : Function.Surjective (pairHom h f js) := by
  intro t
  set c : Fin b → ZMod 2 := fun i => ∑ k, Multiplicative.toAdd (t k) * M k i with hc
  set y : ↥(tabGroup V q) :=
    (List.ofFn fun i => (⟨q i, mem_tabGroup i⟩ : ↥(tabGroup V q)) ^ (c i).val).prod with hy
  refine ⟨y, funext fun k' => ?_⟩
  apply Multiplicative.toAdd.injective
  have hA : ∀ i, Multiplicative.toAdd (pairHom h f js ⟨q i, mem_tabGroup i⟩ k') =
      Multiplicative.toAdd (f k' ⟨⁅q i, q (js k')⁆, h.comm i (js k')⟩) := fun i => rfl
  rw [hy, map_list_prod, List.map_ofFn]
  have e1 : ∀ (L : List (Fin b → Multiplicative (ZMod 2))),
      Multiplicative.toAdd (L.prod k') = (L.map fun x => Multiplicative.toAdd (x k')).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons x L ih => simp only [List.prod_cons, List.map_cons, List.sum_cons, Pi.mul_apply,
        toAdd_mul, ih]
  rw [e1, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, map_pow, Pi.pow_apply, toAdd_pow, hA, nsmul_eq_mul,
    ZMod.natCast_zmod_val]
  calc ∑ i, c i * Multiplicative.toAdd (f k' ⟨⁅q i, q (js k')⁆, h.comm i (js k')⟩)
      = ∑ i, ∑ k, Multiplicative.toAdd (t k) * (M k i *
          Multiplicative.toAdd (f k' ⟨⁅q i, q (js k')⁆, h.comm i (js k')⟩)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
    _ = ∑ k, Multiplicative.toAdd (t k) * ∑ i, M k i *
          Multiplicative.toAdd (f k' ⟨⁅q i, q (js k')⁆, h.comm i (js k')⟩) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = Multiplicative.toAdd (t k') := by
        simp only [hP.inv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]

theorem le_ker_pairHom : V.subgroupOf (tabGroup V q) ≤ (pairHom h f js).ker := by
  intro v hv
  rw [MonoidHom.mem_ker]
  funext k
  rw [pairHom_apply]
  have : commHom h (mem_tabGroup (js k)) v = 1 := Subtype.ext
    (h.commutatorElement_eq_one_of_mem_left hv (mem_tabGroup (js k)))
  rw [this, map_one]
  rfl

theorem card_mul_ker (hP : Pairing h f js M) :
    Nat.card ↥(tabGroup V q) = 2 ^ b * Nat.card ↥(pairHom h f js).ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pairHom h f js).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (pairHom_surjective hP)).toEquiv] at h1
  rw [h1, Nat.card_fun, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)),
    Fintype.card_multiplicative, ZMod.card, Nat.card_eq_fintype_card, Fintype.card_fin]

variable [Finite G]

theorem ker_pairHom (hP : Pairing h f js M) :
    (pairHom h f js).ker = V.subgroupOf (tabGroup V q) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge le_ker_pairHom
  have h1 := card_mul_ker hP
  have h2 := card_le h
  have h3 : Nat.card ↥(V.subgroupOf (tabGroup V q)) = Nat.card ↥V := card_tabV
  rw [h3]
  rw [h1] at h2
  exact Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos b)

theorem card_eq (hP : Pairing h f js M) : Nat.card ↥(tabGroup V q) = 2 ^ b * Nat.card ↥V := by
  rw [card_mul_ker hP, ker_pairHom hP, card_tabV]

theorem mem_of_forall_commute (hP : Pairing h f js M) {y : G} (hy : y ∈ tabGroup V q)
    (hc : ∀ j, y * q j = q j * y) : y ∈ V := by
  have hk : (⟨y, hy⟩ : ↥(tabGroup V q)) ∈ (pairHom h f js).ker := by
    rw [MonoidHom.mem_ker]
    funext k
    rw [pairHom_apply]
    have : commHom h (mem_tabGroup (js k)) ⟨y, hy⟩ = 1 := Subtype.ext (by
      show ⁅y, q (js k)⁆ = 1
      rw [commutatorElement_def, hc (js k)]
      group)
    rw [this, map_one]
    rfl
  rw [ker_pairHom hP] at hk
  exact hk

theorem center_eq (hP : Pairing h f js M) :
    Subgroup.center ↥(tabGroup V q) = V.subgroupOf (tabGroup V q) := by
  ext ⟨y, hy⟩
  constructor
  · intro hz
    refine mem_of_forall_commute hP hy fun j => ?_
    have := Subgroup.mem_center_iff.mp hz ⟨q j, mem_tabGroup j⟩
    exact (congrArg Subtype.val this).symm
  · intro hv
    refine Subgroup.mem_center_iff.mpr fun z => Subtype.ext ?_
    exact (h.central y hv z z.2).symm

end Pairing

section Special

variable [Finite G]

theorem isE2_of_card' {X : Type*} [Group X] [Finite X] (hc : ∀ x y : X, x * y = y * x)
    (hsq : ∀ x : X, x * x = 1) {n : ℕ} (hcard : Nat.card X = 2 ^ n) :
    CFSG.Quasithin.IsElemAbelianOfRank 2 n X := by
  let _ : CommGroup X := { ‹Group X› with mul_comm := hc }
  have h2 : ∀ x : Additive X, (2 : ℕ) • x = 0 := by
    intro x
    have : (2 : ℕ) • Additive.ofMul (Additive.toMul x) = Additive.ofMul (Additive.toMul x ^ 2) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at this
    rw [this, pow_two, hsq]
    rfl
  let _ : Module (ZMod 2) (Additive X) := AddCommGroup.zmodModule h2
  have : Finite (Additive X) := inferInstanceAs (Finite X)
  have : Module.Finite (ZMod 2) (Additive X) := Module.Finite.of_finite
  let bas := Module.finBasis (ZMod 2) (Additive X)
  have hd : Module.finrank (ZMod 2) (Additive X) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
    have hcard' : Nat.card (Additive X) = 2 ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive X ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    bas.equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

variable {a : ℕ} {v : Fin a → G} (hv : EBasis v) {q : Fin b → G}
  {f : Fin b → ↥(eSub hv) →* Multiplicative (ZMod 2)} {js : Fin b → Fin b}
  {M : Fin b → Fin b → ZMod 2}

theorem isSpecial2Group (h : Table (eSub hv) q) (hP : Pairing h f js M)
    (hgen : ∀ k, ∃ i j, v k = ⁅q i, q j⁆) :
    IsSpecial2Group a b ↥(tabGroup (eSub hv) q) := by
  have hZ := center_eq hP
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ, card_tabV, card_eSub hv]
  · rw [hZ]
    apply le_antisymm
    · rw [commutator, Subgroup.commutator_le]
      rintro y - z -
      exact h.comm_mem y.2 z z.2
    · have hle : eSub hv ≤ Subgroup.closure (Set.range v) := (eSub_eq_closure hv).le
      intro y hy
      have hy' : (y : G) ∈ Subgroup.closure (Set.range v) := hle hy
      obtain ⟨y, hyQ⟩ := y
      have key : ∀ x (hx : x ∈ Subgroup.closure (Set.range v)), ∀ hxQ : x ∈ tabGroup (eSub hv) q,
          (⟨x, hxQ⟩ : ↥(tabGroup (eSub hv) q)) ∈ commutator ↥(tabGroup (eSub hv) q) := by
        intro x hx
        induction hx using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          intro hxQ
          obtain ⟨i, j, hij⟩ := hgen k
          have e : (⟨v k, hxQ⟩ : ↥(tabGroup (eSub hv) q)) =
              ⁅(⟨q i, mem_tabGroup i⟩ : ↥(tabGroup (eSub hv) q)), ⟨q j, mem_tabGroup j⟩⁆ :=
            Subtype.ext hij
          rw [e]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        | one => intro _; exact Subgroup.one_mem _
        | mul x x' hx hx' ihx ihx' =>
          intro hxQ
          have h1 : x ∈ tabGroup (eSub hv) q := le_tabGroup ((eSub_eq_closure hv).ge hx)
          have h2 : x' ∈ tabGroup (eSub hv) q := le_tabGroup ((eSub_eq_closure hv).ge hx')
          exact Subgroup.mul_mem _ (ihx h1) (ihx' h2)
        | inv x hx ih =>
          intro hxQ
          have h1 : x ∈ tabGroup (eSub hv) q := le_tabGroup ((eSub_eq_closure hv).ge hx)
          exact Subgroup.inv_mem _ (ih h1)
      exact key y hy' hyQ
  · have := tabV_normal h
    have e : ↥(tabGroup (eSub hv) q) ⧸ Subgroup.center ↥(tabGroup (eSub hv) q) ≃*
        ↥(tabGroup (eSub hv) q) ⧸ tabV (eSub hv) q := QuotientGroup.quotientMulEquivOfEq hZ
    have hcard : Nat.card (↥(tabGroup (eSub hv) q) ⧸ tabV (eSub hv) q) = 2 ^ b := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (tabV (eSub hv) q)
      rw [card_eq hP, card_tabV] at h1
      exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
    obtain ⟨e'⟩ := isE2_of_card' (quot_comm h) (quot_sq h) hcard
    exact ⟨e.trans e'⟩

end Special

end CFSG.Quasithin.Special2
