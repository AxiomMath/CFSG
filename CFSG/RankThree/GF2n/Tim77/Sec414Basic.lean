module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.Open

section Dihedral

variable {G : Type} [Group G]

theorem sec414_orderOf_mul_conj {c t : G} (hc : c * c = 1) (ht : t * t = 1) :
    orderOf (c * ((t * c)⁻¹ * c * (t * c))) = orderOf ((t * c) ^ 2) := by
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  congr 1
  rw [mul_inv_rev, hc', ht', pow_two]
  calc c * (c * t * c * (t * c)) = (c * c) * t * c * (t * c) := by simp only [mul_assoc]
    _ = t * c * (t * c) := by rw [hc, one_mul]

theorem sec414_dihedral_mul_pow {s r : G} (hs : s * s = 1) (hsr : s * r * s = r⁻¹) (k : ℕ) :
    s * r ^ k = (r ^ k)⁻¹ * s := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h : s * r ^ k * s⁻¹ = (r ^ k)⁻¹ := by
    rw [← conj_pow, hs', hsr, inv_pow]
  exact mul_inv_eq_iff_eq_mul.mp h

theorem sec414_dihedral_left_inv {x y : G} (hx : x * x = 1) (hy : y * y = 1) :
    x * (x * y) * x = (x * y)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy,
    ← mul_assoc, hx, one_mul]

theorem sec414_dihedral_right_inv {x y : G} (hx : x * x = 1) (hy : y * y = 1) :
    y * (x * y) * y = (x * y)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy,
    show y * (x * y) * y = y * x * (y * y) by simp only [mul_assoc], hy, mul_one]

theorem sec414_dihedral_pow_even {x y : G} (hx : x * x = 1) (hy : y * y = 1) (k : ℕ) :
    x * (x * y) ^ (2 * k) = ((x * y) ^ k)⁻¹ * x * (x * y) ^ k := by
  rw [two_mul, pow_add, ← mul_assoc, sec414_dihedral_mul_pow hx (sec414_dihedral_left_inv hx hy),
    mul_assoc]

theorem sec414_dihedral_pow_odd {x y : G} (hx : x * x = 1) (hy : y * y = 1) (k : ℕ) :
    x * (x * y) ^ (2 * k + 1) = ((x * y) ^ k)⁻¹ * y * (x * y) ^ k := by
  have hxy : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  rw [pow_succ', ← mul_assoc, hxy, two_mul, pow_add, ← mul_assoc,
    sec414_dihedral_mul_pow hy (sec414_dihedral_right_inv hx hy), mul_assoc]

theorem sec414_exists_conj_mul_pow {x y : G} (hx : x * x = 1) (hy : y * y = 1) (i : ℕ) :
    ∃ c ∈ Subgroup.closure ({x, y} : Set G),
      x * (x * y) ^ i = c * x * c⁻¹ ∨ x * (x * y) ^ i = c * y * c⁻¹ := by
  have hxy : x * y ∈ Subgroup.closure ({x, y} : Set G) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · refine ⟨((x * y) ^ k)⁻¹, inv_mem (pow_mem hxy k), Or.inl ?_⟩
    rw [inv_inv, sec414_dihedral_pow_even hx hy]
  · refine ⟨((x * y) ^ k)⁻¹, inv_mem (pow_mem hxy k), Or.inr ?_⟩
    rw [inv_inv, sec414_dihedral_pow_odd hx hy]

theorem sec414_exists_conj_order_four_of_ne_zero {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h0 : orderOf (x * y) ≠ 0) (h4 : 4 ∣ orderOf (x * y)) :
    ∃ c ∈ Subgroup.closure ({x, y} : Set G), ∃ w ∈ ({x, y} : Set G),
      orderOf (x * (c * w * c⁻¹)) = 4 := by
  obtain ⟨q, hq⟩ := h4
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using hq)
  have hdvd : q ∣ orderOf (x * y) := ⟨4, by rw [hq, mul_comm]⟩
  have hord : orderOf ((x * y) ^ q) = 4 := by
    rw [orderOf_pow_of_dvd hq0 hdvd, hq, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hq0)]
  have key : ∀ (c w : G), x * (x * y) ^ q = c * w * c⁻¹ → orderOf (x * (c * w * c⁻¹)) = 4 := by
    intro c w h
    rw [← h, ← mul_assoc, hx, one_mul, hord]
  obtain ⟨c, hc, h | h⟩ := sec414_exists_conj_mul_pow hx hy q
  · exact ⟨c, hc, x, by simp, key c x h⟩
  · exact ⟨c, hc, y, by simp, key c y h⟩

theorem sec414_exists_conj_order_four [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h4 : 4 ∣ orderOf (x * y)) :
    ∃ c ∈ Subgroup.closure ({x, y} : Set G), ∃ w ∈ ({x, y} : Set G),
      orderOf (x * (c * w * c⁻¹)) = 4 :=
  sec414_exists_conj_order_four_of_ne_zero hx hy (orderOf_pos _).ne' h4

theorem sec414_exists_conj_of_odd {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) :
    ∃ c ∈ Subgroup.closure ({x, y} : Set G), y = c * x * c⁻¹ := by
  have hxy : x * y ∈ Subgroup.closure ({x, y} : Set G) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  obtain ⟨m, hm⟩ := hodd
  refine ⟨((x * y) ^ (m + 1))⁻¹, inv_mem (pow_mem hxy _), ?_⟩
  have hr : (x * y) ^ (2 * (m + 1)) = x * y := by
    rw [show 2 * (m + 1) = orderOf (x * y) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have h := sec414_dihedral_pow_even hx hy (m + 1)
  rw [hr, ← mul_assoc, hx, one_mul] at h
  rw [inv_inv, ← h]

end Dihedral

section PGroup

variable {G : Type} [Group G]

theorem sec414_isPGroup_sup {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hQP : ∀ q ∈ Q, ∀ p ∈ P, q * p * q⁻¹ ∈ P) : IsPGroup 2 ↥(P ⊔ Q) := by
  refine hP.to_sup_of_normal_left' hQ fun q hq => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => hQP q hq p hp, fun h => ?_⟩
  have h' := hQP q⁻¹ (inv_mem hq) _ h
  rwa [show q⁻¹ * (q * p * q⁻¹) * q⁻¹⁻¹ = p by group] at h'

end PGroup

section Coprime

variable {G : Type} [Group G]

theorem sec414_norm_map {V : Type*} [CommGroup V] (hV : ∀ x : V, x * x = 1) (ν : V →* V) {m : ℕ}
    (hm : Odd m) (hν : ∀ x, ν^[m] x = x) :
    ∃ e : V →* V, (∀ x, ν (e x) = e x) ∧ (∀ x, e (ν x) = e x) ∧ (∀ x, ν x = x → e x = x) ∧
      ∀ S : Subgroup V, (∀ x ∈ S, ν x ∈ S) → ∀ x ∈ S, e x ∈ S := by
  have hshift : ∀ x : V,
      ∏ i ∈ Finset.range m, ν^[i + 1] x = ∏ i ∈ Finset.range m, ν^[i] x := by
    intro x
    have h1 := Finset.prod_range_succ (fun i => ν^[i] x) m
    have h2 := Finset.prod_range_succ' (fun i => ν^[i] x) m
    simp only [hν x, Function.iterate_zero, id] at h1 h2
    exact mul_right_cancel (h2.symm.trans h1)
  let e : V →* V := MonoidHom.mk' (fun x => ∏ i ∈ Finset.range m, ν^[i] x) fun a b => by
    simp only [iterate_map_mul, Finset.prod_mul_distrib]
  refine ⟨e, fun x => ?_, fun x => ?_, fun x hx => ?_, fun S hS x hx => ?_⟩
  · show ν (∏ i ∈ Finset.range m, ν^[i] x) = ∏ i ∈ Finset.range m, ν^[i] x
    calc ν (∏ i ∈ Finset.range m, ν^[i] x) = ∏ i ∈ Finset.range m, ν^[i + 1] x := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun i _ => (Function.iterate_succ_apply' ν i x).symm
      _ = ∏ i ∈ Finset.range m, ν^[i] x := hshift x
  · show ∏ i ∈ Finset.range m, ν^[i] (ν x) = ∏ i ∈ Finset.range m, ν^[i] x
    calc ∏ i ∈ Finset.range m, ν^[i] (ν x) = ∏ i ∈ Finset.range m, ν^[i + 1] x :=
          Finset.prod_congr rfl fun i _ => (Function.iterate_succ_apply ν i x).symm
      _ = ∏ i ∈ Finset.range m, ν^[i] x := hshift x
  · show ∏ i ∈ Finset.range m, ν^[i] x = x
    simp only [Function.iterate_fixed hx, Finset.prod_const, Finset.card_range]
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_succ, pow_mul, pow_two, hV x, one_pow, one_mul]
  · show ∏ i ∈ Finset.range m, ν^[i] x ∈ S
    have hit : ∀ i : ℕ, ν^[i] x ∈ S := by
      intro i
      induction i with
      | zero => simpa using hx
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact hS _ ih
    exact S.prod_mem fun i _ => hit i

theorem sec414_elemAbelian_decomp [Finite G] {P : Subgroup G} (hP : IsElemAbelian 2 P) {n : G}
    (hn : Odd (orderOf n)) (hnP : ∀ x ∈ P, n * x * n⁻¹ ∈ P) :
    ∃ C D : Subgroup G, C ≤ P ∧ D ≤ P ∧ (∀ x ∈ P, n * x * n⁻¹ = x ↔ x ∈ C) ∧
      (∀ x ∈ D, n * x * n⁻¹ ∈ D) ∧ (∀ x ∈ C, x ∈ D → x = 1) ∧
      (∀ d ∈ D, n * d * n⁻¹ = d → d = 1) ∧
      (∀ x ∈ P, ∃ c ∈ C, ∃ d ∈ D, x = c * d ∧
        ∀ L : Subgroup G, L ≤ P → (∀ y ∈ L, n * y * n⁻¹ ∈ L) → x ∈ L → c ∈ L ∧ d ∈ L) := by
  obtain ⟨hcomm, hexp⟩ := hP
  letI : CommGroup P := { (inferInstance : Group P) with mul_comm := fun a b => mul_comm' a b }
  have hV : ∀ x : P, x * x = 1 := fun x =>
    Subtype.ext (by simpa [pow_two] using hexp x x.2)
  let ν : P →* P :=
    { toFun := fun x => ⟨n * x * n⁻¹, hnP x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show n * (↑a * ↑b) * n⁻¹ = n * ↑a * n⁻¹ * (n * ↑b * n⁻¹)
        group) }
  have hνcoe : ∀ x : P, ((ν x : P) : G) = n * x * n⁻¹ := fun x => rfl
  have hit : ∀ (i : ℕ) (x : P), ((ν^[i] x : P) : G) = n ^ i * x * (n ^ i)⁻¹ := by
    intro i x
    induction i with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', hνcoe, ih]
      group
  have hνm : ∀ x : P, ν^[orderOf n] x = x := fun x =>
    Subtype.ext (by rw [hit, pow_orderOf_eq_one]; simp)
  obtain ⟨e, he1, he2, he3, he4⟩ := sec414_norm_map hV ν hn hνm
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, ∀ x, x ∈ C ↔ x ∈ P ∧ n * x * n⁻¹ = x :=
    ⟨P ⊓ Subgroup.centralizer {n}, fun x => by
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, mul_inv_eq_iff_eq_mul]
      simp only [Set.mem_singleton_iff, forall_eq]⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, ∀ x, x ∈ D ↔ ∃ y : P, e y = 1 ∧ (y : G) = x :=
    ⟨(MonoidHom.ker e).map P.subtype, fun x => by simp [Subgroup.mem_map]⟩
  have hDP : D ≤ P := fun x hx => by
    obtain ⟨y, -, rfl⟩ := (hD x).1 hx
    exact y.2
  have hCD : ∀ x ∈ C, x ∈ D → x = 1 := by
    intro x hxC hxD
    obtain ⟨y, hy, rfl⟩ := (hD x).1 hxD
    have hfix : ν y = y := Subtype.ext ((hC _).1 hxC).2
    have h1 : y = 1 := by rw [← he3 y hfix, hy]
    rw [h1]
    rfl
  refine ⟨C, D, fun x hx => ((hC x).1 hx).1, hDP,
    fun x hx => ⟨fun h => (hC x).2 ⟨hx, h⟩, fun h => ((hC x).1 h).2⟩, ?_, hCD,
    fun d hd h => hCD d ((hC d).2 ⟨hDP hd, h⟩) hd, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (hD x).1 hx
    exact (hD _).2 ⟨ν y, by rw [he2, hy], rfl⟩
  · intro x hx
    let y : P := ⟨x, hx⟩
    have hey : (e y : G) ∈ C := (hC _).2 ⟨(e y).2, congrArg (fun z : P => (z : G)) (he1 y)⟩
    have hdy : e (y * (e y)⁻¹) = 1 := by
      rw [map_mul, map_inv, he3 (e y) (he1 y), mul_inv_cancel]
    have hsplit : e y * (y * (e y)⁻¹) = y := by rw [mul_left_comm, mul_inv_cancel, mul_one]
    refine ⟨(e y : G), hey, ((y * (e y)⁻¹ : P) : G), (hD _).2 ⟨_, hdy, rfl⟩,
      congrArg (fun z : P => (z : G)) hsplit.symm, ?_⟩
    intro L _ hLn hxL
    have hyS : y ∈ L.comap P.subtype := hxL
    have hS : ∀ z ∈ L.comap P.subtype, ν z ∈ L.comap P.subtype := fun z hz => hLn z hz
    have hS' := he4 (L.comap P.subtype) hS y hyS
    exact ⟨hS', (L.comap P.subtype).mul_mem hyS ((L.comap P.subtype).inv_mem hS')⟩

end Coprime

end CFSG.RankThree.GF2n.Tim77
