module

public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.Quasithin.SteinbergBQ

theorem eq_one_of_perfect_of_isSolvable {B M : Type*} [Group B] [Group M] [Group.IsPerfect B]
    [Group.IsSolvable M] (f : B →* M) (b : B) : f b = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (Subsingleton.elim (⟨f b, ⟨b, rfl⟩⟩ : f.range) 1)

theorem cyclic_sylow_center_rank_two_core_centralizes_perfect_subgroups {H : Type*} [Group H]
    [Finite H] (T : Sylow 2 H) (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hZT : IsCyclic (Subgroup.center T))
    (hrank : ∀ E : Subgroup H, E ≤ T → IsElementaryAbelian 2 E → Nat.card E ≤ 4) {z : H}
    (hzT : z ∈ (T : Subgroup H)) (hzZ : z ∈ Subgroup.centralizer ((T : Subgroup H) : Set H))
    (hz2 : orderOf z = 2) (B : Subgroup H) (hB : ⁅B, B⁆ = B) :
    B ≤ Subgroup.centralizer ({z} : Set H) ∧
      B ≤ (CFSG.perfectResidual (Subgroup.centralizer ({z} : Set H))).map
        (Subgroup.centralizer ({z} : Set H)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : Q ≤ (T : Subgroup H) := hQ.le_sylow_of_normal T
  let E : Subgroup H :=
    { carrier := {x | x ∈ Q ∧ (∀ q ∈ Q, x * q = q * x) ∧ x ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, fun q hq => by
          rw [mul_assoc, hb.2.1 q hq, ← mul_assoc, ha.2.1 q hq, mul_assoc], by
          rw [(Commute.mul_pow (hb.2.1 a ha.1).symm 2), ha.2.2, hb.2.2, one_mul]⟩
      one_mem' := ⟨Q.one_mem, fun q _ => by rw [one_mul, mul_one], one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, fun q hq => by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha.2.1 q hq, mul_inv_cancel_right],
          by rw [inv_pow, ha.2.2, inv_one]⟩ }
  have hEn : E.Normal := ⟨fun x hx h => ⟨(inferInstance : Q.Normal).conj_mem x hx.1 h,
    fun q hq => by
      have hq' : h⁻¹ * q * h ∈ Q := by
        have := (inferInstance : Q.Normal).conj_mem q hq h⁻¹
        simpa using this
      have hc := hx.2.1 _ hq'
      calc h * x * h⁻¹ * q = h * (x * (h⁻¹ * q * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * q * h) * x) * h⁻¹ := by rw [hc]
        _ = q * (h * x * h⁻¹) := by group,
    by rw [conj_pow, hx.2.2, mul_one, mul_inv_cancel]⟩⟩
  have hEQ : E ≤ Q := fun x hx => hx.1
  have hET : E ≤ (T : Subgroup H) := hEQ.trans hQT
  have hEel : IsElementaryAbelian 2 E :=
    { is_comm := ⟨fun a b => Subtype.ext (a.2.2.1 b b.2.1)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using a.2.2.2) }
  have hE4 : Nat.card E ≤ 4 := hrank E hET hEel
  have hE1 : E ≠ ⊥ := by
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
    have hZQ : Nontrivial (Subgroup.center Q) := IsPGroup.center_nontrivial hQ
    obtain ⟨c, hcZ, hc1⟩ : ∃ c ∈ Subgroup.center Q, c ≠ 1 := by
      obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center Q)
      exact ⟨c, c.2, fun h => hc (Subtype.ext h)⟩
    obtain ⟨n, hn⟩ := hQ c
    have hc' : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.1 h)
    obtain ⟨m, hm⟩ : ∃ m, orderOf c = 2 ^ (m + 1) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
      rcases k with _ | m
      · exact absurd (by simpa using hk) hc'
      · exact ⟨m, hk⟩
    have hdvd : 2 ^ m ∣ orderOf c := hm ▸ pow_dvd_pow 2 (Nat.le_succ m)
    have hord : orderOf (c ^ 2 ^ m) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hm, pow_succ,
        Nat.mul_div_cancel_left _ (pow_pos two_pos m)]
    set y : Q := c ^ 2 ^ m with hy
    have hyZ : y ∈ Subgroup.center Q := Subgroup.pow_mem _ hcZ _
    have hy1 : y ≠ 1 := fun h => by
      rw [h, orderOf_one] at hord
      norm_num at hord
    have hy2 : y ^ 2 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    refine fun hbot => hy1 ?_
    have hyE : (y : H) ∈ E := ⟨y.2, fun q hq => by
        have := Subgroup.mem_center_iff.1 hyZ ⟨q, hq⟩
        exact (congrArg Subtype.val this).symm, by
      have := congrArg Subtype.val hy2
      simpa using this⟩
    rw [hbot, Subgroup.mem_bot] at hyE
    exact Subtype.ext hyE
  have hBE : B ≤ Subgroup.centralizer (E : Set H) := by
    have : Group.IsPerfect B := Subgroup.isPerfect_iff.2 hB
    have : Finite E := inferInstance
    have : Group.IsSolvable (Equiv.Perm E) := Equiv.Perm.isSolvable hE4
    let act : B →* Equiv.Perm E :=
      { toFun := fun b =>
          { toFun := fun x => ⟨b * x * b⁻¹, hEn.conj_mem x x.2 b⟩
            invFun := fun x => ⟨b⁻¹ * x * b, by simpa using hEn.conj_mem x x.2 b⁻¹⟩
            left_inv := fun x => Subtype.ext (by simp [mul_assoc])
            right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
        map_one' := Equiv.ext fun x => Subtype.ext (by simp)
        map_mul' := fun b c => Equiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun τ : Equiv.Perm E => ((τ ⟨x, hx⟩ : E) : H))
      (eq_one_of_perfect_of_isSolvable act ⟨b, hb⟩)
    have h2 : b * x * b⁻¹ = x := h1
    calc x * b = b * x * b⁻¹ * b := by rw [h2]
      _ = b * x := by group
  have hzE : z ∈ E := by
    have hET' : (E.subgroupOf (T : Subgroup H)).Normal := Subgroup.Normal.subgroupOf hEn _
    have hnil : Group.IsNilpotent (T : Subgroup H) := T.isPGroup'.isNilpotent
    have hne : E.subgroupOf (T : Subgroup H) ≠ ⊥ := by
      intro h
      apply hE1
      rw [← Subgroup.map_subgroupOf_eq_of_le hET, h, Subgroup.map_bot]
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    obtain ⟨heE, heZ⟩ := Subgroup.mem_inf.1 he
    have heE' : (e : H) ∈ E := heE
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    have : Fintype (Subgroup.center (T : Subgroup H)) := Fintype.ofFinite _
    let e' : Subgroup.center (T : Subgroup H) := ⟨e, heZ⟩
    let z' : Subgroup.center (T : Subgroup H) := ⟨⟨z, hzT⟩, Subgroup.mem_center_iff.2 fun t =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 hzZ t t.2))⟩
    have he2 : e' ^ 2 = 1 := Subtype.ext (Subtype.ext heE'.2.2)
    have hzz : z ^ 2 = 1 := by
      rw [← hz2]
      exact pow_orderOf_eq_one z
    have hz2' : z' ^ 2 = 1 := Subtype.ext (Subtype.ext hzz)
    have he'1 : e' ≠ 1 := fun h => he1' (congrArg Subtype.val h)
    have hz'1 : z' ≠ 1 := fun h => by
      have : z = 1 := congrArg (fun w : Subgroup.center (T : Subgroup H) => ((w : T) : H)) h
      rw [this, orderOf_one] at hz2
      norm_num at hz2
    by_contra hzE
    have hez : e' ≠ z' := fun h => hzE (by
      have := congrArg (fun w : Subgroup.center (T : Subgroup H) => ((w : T) : H)) h
      simp only [e', z'] at this
      rw [← this]
      exact heE')
    have hle := IsCyclic.card_pow_eq_one_le (α := Subgroup.center (T : Subgroup H))
      (n := 2) (by norm_num)
    have hsub : ({1, e', z'} : Finset (Subgroup.center (T : Subgroup H))) ⊆
        Finset.univ.filter fun a => a ^ 2 = 1 := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_filter]
      rcases ha with rfl | rfl | rfl
      · exact ⟨Finset.mem_univ _, one_pow 2⟩
      · exact ⟨Finset.mem_univ _, he2⟩
      · exact ⟨Finset.mem_univ _, hz2'⟩
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [he'1.symm, hz'1.symm]),
      Finset.card_pair hez] at h3
    omega
  have hBz : B ≤ Subgroup.centralizer ({z} : Set H) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (hBE hb) z hzE).symm)
  refine ⟨hBz, ?_⟩
  set C := Subgroup.centralizer ({z} : Set H)
  have hBC : Group.IsPerfect (B.subgroupOf C) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBz, hB]
  have h := (CFSG.perfect_residual_transport (G := C) (MonoidHom.id C)).2.2 _ hBC
  rw [← Subgroup.map_subgroupOf_eq_of_le hBz]
  exact Subgroup.map_mono h

end CFSG.Quasithin.SteinbergBQ
