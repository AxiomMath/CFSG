module

public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement IsMulCommutative

namespace ExtraGen

section Eval

variable {A : Type*} [Group A] [IsMulCommutative A] {n : ℕ}

def evalProd (a : Fin n → A) (e : Fin n → ZMod 2) : A := ∏ i, a i ^ (e i).val

theorem evalProd_add (a : Fin n → A) (ha : ∀ i, a i * a i = 1) (e e' : Fin n → ZMod 2) :
    evalProd a (e + e') = evalProd a e * evalProd a e' := by
  unfold evalProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  have h2 : a i ^ 2 = 1 := by rw [pow_two]; exact ha i
  rw [Pi.add_apply, ZMod.val_add, pow_eq_pow_mod _ h2, pow_eq_pow_mod (_ + _) h2, Nat.mod_mod]

theorem evalProd_zero (a : Fin n → A) : evalProd a 0 = 1 := by
  simp [evalProd]

theorem evalProd_single (a : Fin n → A) (i : Fin n) : evalProd a (Pi.single i 1) = a i := by
  unfold evalProd
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem evalProd_surjective (a : Fin n → A) (ha : ∀ i, a i * a i = 1)
    (hgen : Subgroup.closure (Set.range a) = ⊤) : Function.Surjective (evalProd a) := by
  let f : Multiplicative (Fin n → ZMod 2) →* A :=
    { toFun := fun e => evalProd a (Multiplicative.toAdd e)
      map_one' := evalProd_zero a
      map_mul' := fun e e' => evalProd_add a ha _ _ }
  have h : Subgroup.closure (Set.range a) ≤ f.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd (Pi.single i 1), evalProd_single a i⟩
  rw [hgen] at h
  intro x
  obtain ⟨e, he⟩ := h (Subgroup.mem_top x)
  exact ⟨Multiplicative.toAdd e, he⟩

end Eval

section Central

variable {Q : Type*} [Group Q] {z : Q}

theorem zpow_val_add (hz2 : z * z = 1) (d d' : ZMod 2) :
    z ^ (d + d').val = z ^ d.val * z ^ d'.val := by
  have h2 : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  rw [← pow_add, ZMod.val_add, pow_eq_pow_mod _ h2, pow_eq_pow_mod (d.val + d'.val) h2,
    Nat.mod_mod]

theorem zpow_val_inj (hz1 : z ≠ 1) {d d' : ZMod 2} (h : z ^ d.val = z ^ d'.val) : d = d' := by
  have key : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rcases key d with rfl | rfl <;> rcases key d' with rfl | rfl
  · rfl
  · exfalso
    rw [ZMod.val_zero, h1, pow_zero, pow_one] at h
    exact hz1 h.symm
  · exfalso
    rw [ZMod.val_zero, h1, pow_zero, pow_one] at h
    exact hz1 h
  · rfl

theorem eq_one_or_eq_of_mem_zpowers (hz2 : z * z = 1) {u : Q} (hu : u ∈ Subgroup.zpowers z) :
    u = 1 ∨ u = z := by
  obtain ⟨k, rfl⟩ := hu
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    beta_reduce
    rw [zpow_mul, h2, one_zpow]
  · right
    beta_reduce
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem normal_zpowers_of_central (hcen : ∀ x : Q, z * x = x * z) :
    (Subgroup.zpowers z).Normal := by
  refine Subgroup.normal_of_le_center ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
  exact fun g => (hcen g).symm

theorem central_of_gens {n : ℕ} (q : Fin n → Q) (hgen : Subgroup.closure (Set.range q) = ⊤)
    (hzc : ∀ i, z * q i = q i * z) (x : Q) : z * x = x * z := by
  have h : Subgroup.closure (Set.range q) ≤ Subgroup.centralizer ({z} : Set Q) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro h rfl
    exact hzc i
  rw [hgen] at h
  exact (Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_top x))) z rfl

theorem mul_comm_of_mem_zpowers (hcen : ∀ x : Q, z * x = x * z) {u : Q}
    (hu : u ∈ Subgroup.zpowers z) (x : Q) : u * x = x * u := by
  obtain ⟨k, rfl⟩ := hu
  exact (Commute.zpow_left (hcen x : Commute z x) k).eq

theorem comm_sq_mem_zpowers {n : ℕ} (q : Fin n → Q) (hgen : Subgroup.closure (Set.range q) = ⊤)
    (hzc : ∀ i, z * q i = q i * z) (hsq : ∀ i, q i * q i = 1 ∨ q i * q i = z)
    (hcomm : ∀ i j, ∃ k : ℕ, q i * q j = q j * q i * z ^ k) :
    (∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers z) ∧ (∀ x : Q, x * x ∈ Subgroup.zpowers z) := by
  have hcen := central_of_gens q hgen hzc
  have : (Subgroup.zpowers z).Normal := normal_zpowers_of_central hcen
  let π : Q →* Q ⧸ Subgroup.zpowers z := QuotientGroup.mk' _
  have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).2 (Subgroup.mem_zpowers z)
  have ha_comm : ∀ i j, π (q i) * π (q j) = π (q j) * π (q i) := by
    intro i j
    obtain ⟨k, hk⟩ := hcomm i j
    rw [← map_mul, ← map_mul, hk, map_mul, map_pow, hπz, one_pow, mul_one]
  have ha_sq : ∀ i, π (q i) * π (q i) = 1 := by
    intro i
    rw [← map_mul]
    rcases hsq i with h | h
    · rw [h, map_one]
    · rw [h, hπz]
  have hagen : Subgroup.closure (Set.range fun i => π (q i)) = ⊤ := by
    have : Set.range (fun i => π (q i)) = π '' Set.range q := by
      rw [← Set.range_comp]; rfl
    rw [this, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)
  have hAcomm : ∀ x y : Q ⧸ Subgroup.zpowers z, x * y = y * x := by
    have hpair : (Set.range fun i => π (q i)).Pairwise Commute := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact ha_comm i j
    have h := Subgroup.isMulCommutative_closure hpair
    rw [hagen] at h
    intro x y
    exact congrArg Subtype.val (h.is_comm.comm (⟨x, trivial⟩ : (⊤ : Subgroup _)) ⟨y, trivial⟩)
  have hAsq : ∀ x : Q ⧸ Subgroup.zpowers z, x * x = 1 := by
    intro x
    have hx : x ∈ Subgroup.closure (Set.range fun i => π (q i)) := by rw [hagen]; trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ha_sq i
    | one => simp
    | mul y w _ _ hy hw =>
      calc y * w * (y * w) = y * (w * y) * w := by group
        _ = y * (y * w) * w := by rw [hAcomm w y]
        _ = (y * y) * (w * w) := by group
        _ = 1 := by rw [hy, hw, one_mul]
    | inv y _ hy =>
      rw [← mul_inv_rev, hy, inv_one]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h : π ⁅x, y⁆ = 1 :=
      (map_commutatorElement π x y).trans (commutatorElement_eq_one_iff_mul_comm.2 (hAcomm _ _))
    exact (QuotientGroup.eq_one_iff _).1 h
  · have h : π (x * x) = 1 := by rw [map_mul]; exact hAsq _
    exact (QuotientGroup.eq_one_iff _).1 h

end Central

section CommExp

variable {Q : Type*} [Group Q] {z : Q}

open scoped Classical in
noncomputable def commExp (x y : Q) : ZMod 2 := if ⁅x, y⁆ = 1 then 0 else 1

theorem commutator_eq_zpow_commExp (hz2 : z * z = 1) {x y : Q}
    (h : ⁅x, y⁆ ∈ Subgroup.zpowers z) : ⁅x, y⁆ = z ^ (commExp x y).val := by
  classical
  unfold commExp
  split_ifs with h1
  · rw [h1, ZMod.val_zero, pow_zero]
  · rcases eq_one_or_eq_of_mem_zpowers hz2 h with h2 | h2
    · exact absurd h2 h1
    · rw [h2, show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem commExp_eq_zero_iff (x y : Q) : commExp x y = 0 ↔ ⁅x, y⁆ = 1 := by
  classical
  unfold commExp
  split_ifs with h1
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

theorem commExp_mul_left (hz1 : z ≠ 1) (hz2 : z * z = 1) (hcen : ∀ x : Q, z * x = x * z)
    (hcom : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers z) (x x' y : Q) :
    commExp (x * x') y = commExp x y + commExp x' y := by
  refine zpow_val_inj hz1 ?_
  rw [zpow_val_add hz2, ← commutator_eq_zpow_commExp hz2 (hcom _ _),
    ← commutator_eq_zpow_commExp hz2 (hcom x y), ← commutator_eq_zpow_commExp hz2 (hcom x' y)]
  have e1 : x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ := by
    rw [← mul_comm_of_mem_zpowers hcen (hcom x' y) x, mul_inv_cancel_right]
  rw [commutatorElement_mul_left_eq_conj_mul, e1]
  exact mul_comm_of_mem_zpowers hcen (hcom x' y) _

theorem commutator_eq_of_mul_eq (hcen : ∀ x : Q, z * x = x * z) {x y : Q} {k : ℕ}
    (h : x * y = y * x * z ^ k) : ⁅x, y⁆ = z ^ k := by
  have hu : ∀ w : Q, w * z ^ k = z ^ k * w := fun w =>
    (mul_comm_of_mem_zpowers hcen (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) k) w).symm
  have e : y * x * z ^ k * x⁻¹ * y⁻¹ = y * x * z ^ k * (y * x)⁻¹ := by simp [mul_assoc]
  rw [commutatorElement_def, h, e]
  exact mul_inv_eq_iff_eq_mul.2 (hu (y * x))

noncomputable def commHom (hz1 : z ≠ 1) (hz2 : z * z = 1) (hcen : ∀ x : Q, z * x = x * z)
    (hcom : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers z) (w : Q) : Q →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (commExp x w)
  map_one' := by
    rw [(commExp_eq_zero_iff 1 w).2 (commutatorElement_one_left w), ofAdd_zero]
  map_mul' x x' := by
    rw [commExp_mul_left hz1 hz2 hcen hcom, ofAdd_add]

end CommExp

section Main

variable {Q : Type*} [Group Q]

theorem card_and_centralizer_of_closure_eq_top {n : ℕ} (q : Fin n → Q) (z : Q)
    (hgen : Subgroup.closure (Set.range q) = ⊤) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzc : ∀ i, z * q i = q i * z) (B : Fin n → Fin n → ZMod 2)
    (hsq : ∀ i, q i * q i = 1 ∨ q i * q i = z)
    (hcomm : ∀ i j, q i * q j = q j * q i * z ^ (B i j).val)
    (hnd : ∀ e : Fin n → ZMod 2, (∀ j, ∑ i, e i * B i j = 0) → e = 0) :
    Nat.card Q = 2 ^ (n + 1) ∧ ∀ x : Q, (∀ y, x * y = y * x) → x ∈ Subgroup.zpowers z := by
  obtain ⟨hcom, hsqZ⟩ := comm_sq_mem_zpowers q hgen hzc hsq (fun i j => ⟨_, hcomm i j⟩)
  have hcen := central_of_gens q hgen hzc
  have : (Subgroup.zpowers z).Normal := normal_zpowers_of_central hcen
  let π : Q →* Q ⧸ Subgroup.zpowers z := QuotientGroup.mk' _
  have hAcomm : ∀ x y : Q ⧸ Subgroup.zpowers z, x * y = y * x := by
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have h : π ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcom x y)
    rw [map_commutatorElement] at h
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  have : IsMulCommutative (Q ⧸ Subgroup.zpowers z) := ⟨⟨hAcomm⟩⟩
  let a : Fin n → Q ⧸ Subgroup.zpowers z := fun i => π (q i)
  have ha_sq : ∀ i, a i * a i = 1 := by
    intro i
    show π (q i) * π (q i) = 1
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).2 (hsqZ _)
  have hagen : Subgroup.closure (Set.range a) = ⊤ := by
    have : Set.range a = π '' Set.range q := by
      rw [← Set.range_comp]; rfl
    rw [this, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)
  have hsurj := evalProd_surjective a ha_sq hagen
  let cb : Fin n → (Q ⧸ Subgroup.zpowers z) →* Multiplicative (ZMod 2) := fun j =>
    QuotientGroup.lift (Subgroup.zpowers z) (commHom hz1 hz2 hcen hcom (q j)) (by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      show Multiplicative.ofAdd (commExp z (q j)) = 1
      rw [(commExp_eq_zero_iff z (q j)).2 (commutatorElement_eq_one_iff_mul_comm.2 (hcen _)),
        ofAdd_zero])
  have hcb : ∀ j x, cb j (π x) = Multiplicative.ofAdd (commExp x (q j)) := fun j x => rfl
  have hcb_a : ∀ i j, cb j (a i) = Multiplicative.ofAdd (B i j) := by
    intro i j
    rw [show a i = π (q i) from rfl, hcb]
    congr 1
    exact zpow_val_inj hz1 ((commutator_eq_zpow_commExp hz2 (hcom _ _)).symm.trans
      (commutator_eq_of_mul_eq hcen (hcomm i j)))
  have hcb_eval : ∀ j e, cb j (evalProd a e) = Multiplicative.ofAdd (∑ i, e i * B i j) := by
    intro j e
    unfold evalProd
    rw [map_prod, ofAdd_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, hcb_a, ← ofAdd_nsmul]
    congr 1
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hker : ∀ e : Fin n → ZMod 2, (∀ j, cb j (evalProd a e) = 1) → e = 0 := by
    intro e he
    refine hnd e fun j => ?_
    have h := he j
    rw [hcb_eval] at h
    exact ofAdd_eq_one.1 h
  have hinj : Function.Injective (evalProd a) := by
    intro e e' h
    have h0 : evalProd a (e + e') = 1 := by
      rw [evalProd_add a ha_sq, h, ← evalProd_add a ha_sq]
      have : e' + e' = 0 := by
        ext i
        have key : ∀ u : ZMod 2, u + u = 0 := by decide
        exact key _
      rw [this, evalProd_zero]
    have h1 := hker (e + e') (fun j => by rw [h0, map_one])
    funext i
    have key : ∀ u v : ZMod 2, u + v = 0 → u = v := by decide
    exact key _ _ (congrFun h1 i)
  have hcardA : Nat.card (Q ⧸ Subgroup.zpowers z) = 2 ^ n := by
    rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩), Nat.card_fun, Nat.card_zmod]
    simp
  have hZcard : Nat.card (Subgroup.zpowers z) = 2 := by
    have h2 : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime h2 hz1
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z), hcardA, hZcard,
      pow_succ]
  · obtain ⟨e, he⟩ := hsurj (π x)
    have h1 : ∀ j, cb j (evalProd a e) = 1 := by
      intro j
      rw [he, hcb, (commExp_eq_zero_iff x (q j)).2
        (commutatorElement_eq_one_iff_mul_comm.2 (hx _)), ofAdd_zero]
    have he0 := hker e h1
    rw [he0, evalProd_zero] at he
    exact (QuotientGroup.eq_one_iff x).1 he.symm

end Main

end ExtraGen

theorem card_and_extraspecial_of_gens {G : Type*} [Group G] [Finite G] {n : ℕ} (q : Fin n → G)
    (z : G) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzmem : z ∈ Subgroup.closure (Set.range q)) (hzc : ∀ i, z * q i = q i * z)
    (B : Fin n → Fin n → ZMod 2)
    (hsq : ∀ i, q i * q i = 1 ∨ q i * q i = z)
    (hcomm : ∀ i j, q i * q j = q j * q i * z ^ (B i j).val)
    (hnd : ∀ e : Fin n → ZMod 2, (∀ j, ∑ i, e i * B i j = 0) → e = 0) :
    Nat.card (Subgroup.closure (Set.range q)) = 2 ^ (n + 1) ∧
    CFSG.IsExtraspecialPGroup 2 (Subgroup.closure (Set.range q)) ∧
    ∀ x ∈ Subgroup.closure (Set.range q),
      (∀ y ∈ Subgroup.closure (Set.range q), x * y = y * x) → x ∈ Subgroup.zpowers z := by
  set S := Subgroup.closure (Set.range q)
  let q' : Fin n → S := fun i => ⟨q i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let z' : S := ⟨z, hzmem⟩
  have hgen : Subgroup.closure (Set.range q') = ⊤ := by
    have : Set.range q' = ((↑) : S → G) ⁻¹' (Set.range q) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    rw [this]
    exact Subgroup.closure_closure_coe_preimage
  have hz1' : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz2' : z' * z' = 1 := Subtype.ext hz2
  have hzc' : ∀ i, z' * q' i = q' i * z' := fun i => Subtype.ext (hzc i)
  have hsq' : ∀ i, q' i * q' i = 1 ∨ q' i * q' i = z' := fun i =>
    (hsq i).imp Subtype.ext Subtype.ext
  have hcomm' : ∀ i j, q' i * q' j = q' j * q' i * z' ^ (B i j).val := fun i j =>
    Subtype.ext (hcomm i j)
  obtain ⟨hcard, hcent⟩ :=
    ExtraGen.card_and_centralizer_of_closure_eq_top q' z' hgen hz1' hz2' hzc' B hsq' hcomm' hnd
  obtain ⟨hcom, hsqZ⟩ :=
    ExtraGen.comm_sq_mem_zpowers q' hgen hzc' hsq' (fun i j => ⟨_, hcomm' i j⟩)
  have hcen := ExtraGen.central_of_gens q' hgen hzc'
  have hZcard : Nat.card (Subgroup.zpowers z') = 2 := by
    have h2 : z' ^ 2 = 1 := by rw [pow_two]; exact hz2'
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime h2 hz1'
  have hnab : ∃ x : S, x ∉ Subgroup.zpowers z' := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.zpowers z' = ⊤ := (Subgroup.eq_top_iff' _).2 hall
    have h2 : Nat.card S = 2 := by rw [← Subgroup.card_top, ← htop, hZcard]
    have hn : n = 0 := by
      have h3 : 2 ^ (n + 1) = 2 ^ 1 := by rw [← hcard, h2, pow_one]
      have := Nat.pow_right_injective (le_refl 2) h3
      omega
    subst hn
    have h4 : z' ∈ (⊤ : Subgroup S) := trivial
    rw [← hgen, Set.range_eq_empty, Subgroup.closure_empty, Subgroup.mem_bot] at h4
    exact hz1' h4
  have hext : CFSG.IsExtraspecialPGroup 2 S :=
    CFSG.RankThree.PartOne.PlaneCommuting.isExtraspecialPGroup_of_pairing (IsPGroup.of_card hcard)
      hZcard (Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 fun g => (hcen g).symm)) hcom
      (fun x => by rw [pow_two]; exact hsqZ x) hcent hnab
  refine ⟨hcard, hext, fun x hx hxc => ?_⟩
  obtain ⟨k, hk⟩ := hcent ⟨x, hx⟩ (fun y => Subtype.ext (hxc y.1 y.2))
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.Quasithin.J4M2
