module

public import CFSG.RankThree.GF2n.Parrott.CaseII
public import CFSG.GroupTheory.ConjOrderThree

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_J_A1 (h : Tim79a.ParrottHypA1 z) : Nat.card (J z) = 2 ^ 9 := h.card_J

theorem z_mem_J_A1 (h : Tim79a.ParrottHypA1 z) : z ∈ J z := by
  have hz : z ∈ ⁅J z, J z⁆ := by
    rw [h.commutator]
    exact Subgroup.mem_zpowers z
  exact Subgroup.commutator_le_self (J z) hz

theorem centerIn_J_eq_zpowers_A1 (h : Tim79a.ParrottHypA1 z) :
    centerIn (J z) = Subgroup.zpowers z := by
  rw [CFSG.centerIn_eq_map_center, ← h.extraspecial.2.1, h.commutator]

theorem orderOf_z_A1 (h : Tim79a.ParrottHypA1 z) : orderOf z = 2 := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [← h.commutator]
    exact h.extraspecial.2.2
  rwa [Nat.card_zpowers] at hcard

theorem centralizer_J_eq_centerIn_A1 (h : Tim79a.ParrottHypA1 z) :
    H z ⊓ Subgroup.centralizer (J z : Set G) = centerIn (J z) := by
  apply le_antisymm
  · intro x hx
    exact ⟨h.centralizer_le hx, hx.2⟩
  · intro x hx
    exact ⟨J_le_H hx.1, hx.2⟩

private theorem sigma1_ne_sigma2 : sigma1 ≠ sigma2 := by
  decide

section Coprime

variable {M Q : Type*} [Group M] [Finite M] [Group Q]

theorem exists_pow_lift_orderOf_eq (q : M →* Q) (hker : IsPGroup 2 q.ker) {c : M} {m : ℕ}
    (hm : Odd m) (hm1 : 1 < m) (hc : orderOf (q c) = m) :
    ∃ n : ℕ, q (c ^ n) = q c ∧ orderOf (c ^ n) = m := by
  obtain ⟨a, ha⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm1
  have hmem : c ^ m ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hc, pow_orderOf_eq_one]
  have hN : (c ^ m) ^ 2 ^ a = 1 := by
    have h := pow_card_eq_one' (G := q.ker) (x := ⟨c ^ m, hmem⟩)
    rw [ha] at h
    exact congrArg Subtype.val h
  have hqn : q (c ^ (2 ^ a * b)) = q c := by
    rw [map_pow, ← pow_mod_orderOf, hc, hb, pow_one]
  refine ⟨2 ^ a * b, hqn, ?_⟩
  have h1 : (c ^ (2 ^ a * b)) ^ m = 1 := by
    calc (c ^ (2 ^ a * b)) ^ m = ((c ^ m) ^ 2 ^ a) ^ b := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf
      _ = 1 := by rw [hN, one_pow]
  have h2 : orderOf (q (c ^ (2 ^ a * b))) ∣ orderOf (c ^ (2 ^ a * b)) := orderOf_map_dvd q _
  rw [hqn, hc] at h2
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h1) h2

omit [Finite M] in
theorem exists_commute_mem_fibre (q : M →* Q) {p : ℕ} [Fact p.Prime] {P S : Subgroup M}
    (hP : IsPGroup p P) (hPS : P ≤ S) (hker : ¬ p ∣ Nat.card ↥(q.ker ⊓ S)) {m₀ : M}
    (hm₀ : m₀ ∈ S) (hcomm : ∀ g ∈ P, q g * q m₀ = q m₀ * q g) :
    ∃ m ∈ S, q m = q m₀ ∧ ∀ g ∈ P, g * m = m * g := by
  classical
  let α := {m : M // m ∈ S ∧ q m = q m₀}
  have hconj : ∀ g : P, ∀ m : α, (g : M) * m * (g : M)⁻¹ ∈ S ∧
      q ((g : M) * m * (g : M)⁻¹) = q m₀ := by
    intro g m
    refine ⟨S.mul_mem (S.mul_mem (hPS g.2) m.2.1) (S.inv_mem (hPS g.2)), ?_⟩
    rw [map_mul, map_mul, map_inv, m.2.2, hcomm g g.2, mul_inv_cancel_right]
  let act : MulAction P α :=
    { smul := fun g m => ⟨(g : M) * m * (g : M)⁻¹, hconj g m⟩
      one_smul := fun m => Subtype.ext (by
        change ((1 : P) : M) * (m : M) * ((1 : P) : M)⁻¹ = m
        simp)
      mul_smul := fun g h m => Subtype.ext (by
        change (g : M) * (h : M) * m * ((g : M) * (h : M))⁻¹ =
          (g : M) * ((h : M) * m * (h : M)⁻¹) * (g : M)⁻¹
        group) }
  let e : α ≃ ↥(q.ker ⊓ S) :=
    { toFun := fun m => ⟨m₀⁻¹ * m, Subgroup.mem_inf.mpr
        ⟨MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, m.2.2, inv_mul_cancel]),
          S.mul_mem (S.inv_mem hm₀) m.2.1⟩⟩
      invFun := fun k => ⟨m₀ * k, S.mul_mem hm₀ (Subgroup.mem_inf.mp k.2).2, by
        rw [map_mul, MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp k.2).1, mul_one]⟩
      left_inv := fun m => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  have hα : ¬ p ∣ Nat.card α := by rwa [Nat.card_congr e]
  obtain ⟨m, hm⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α hα
  refine ⟨m.1, m.2.1, m.2.2, fun g hg => ?_⟩
  have h := congrArg Subtype.val (hm ⟨g, hg⟩)
  change g * m * g⁻¹ = m at h
  calc g * m = g * m * g⁻¹ * g := by group
    _ = m * g := by rw [h]

theorem exists_conj_mem_inf_of_order_three {J S : Subgroup M} [J.Normal] (hJ2 : IsPGroup 2 J)
    {x y : M} (hxS : x ∈ S) (hyS : y ∈ S) (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hcos : x⁻¹ * y ∈ J) : ∃ j ∈ J ⊓ S, j * y * j⁻¹ = x := by
  have hJS : (J.subgroupOf S).Normal := Subgroup.Normal.subgroupOf inferInstance S
  have hJS2 : IsPGroup 2 (J.subgroupOf S) := hJ2.comap_subtype
  obtain ⟨j, hj, hjx⟩ := CFSG.GroupTheory.exists_conj_of_order_three_of_mem_same_coset
    (M := ↥S) (J := J.subgroupOf S) hJS2 (x := ⟨x, hxS⟩) (y := ⟨y, hyS⟩)
    (by rw [Subgroup.orderOf_mk]; exact hx) (by rw [Subgroup.orderOf_mk]; exact hy)
    (by rw [Subgroup.mem_subgroupOf]; exact hcos)
  exact ⟨j, ⟨Subgroup.mem_subgroupOf.mp hj, j.2⟩, congrArg Subtype.val hjx⟩

end Coprime

section Map

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

@[expose] noncomputable def qHP : ↥(H z) →* QP45.originalSubgroup :=
  (QuotientDataPSp.toQP45 D).toMonoidHom.comp (QuotientGroup.mk' ((J z).subgroupOf (H z)))

omit [Finite G] in
theorem qHP_surjective : Function.Surjective (qHP D) :=
  (QuotientDataPSp.toQP45 D).surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem ker_qHP : (qHP D).ker = (J z).subgroupOf (H z) := by
  ext x
  rw [MonoidHom.mem_ker]
  change (QuotientDataPSp.toQP45 D) (QuotientGroup.mk' ((J z).subgroupOf (H z)) x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem isPGroup_ker_qHP : IsPGroup 2 (qHP D).ker := by
  rw [ker_qHP]
  exact isPGroup_J_subgroupOf (z := z)

@[expose] noncomputable def qHPA : ↥(H z) →* QA45.originalSubgroup :=
  (Subgroup.inclusion QP45_le_QA45).comp (qHP D)

omit [Finite G] in
theorem coe_qHPA (x : ↥(H z)) :
    ((qHPA D x : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) = (qHP D x : Equiv.Perm (Fin 45)) :=
  rfl

omit [Finite G] in
theorem ker_qHPA : (qHPA D).ker = (J z).subgroupOf (H z) := by
  ext x
  rw [← ker_qHP D, MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, Subtype.ext_iff,
    coe_qHPA]
  rfl

omit [Finite G] in
theorem range_qHPA :
    (qHPA D).range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subgroup.mem_subgroupOf, coe_qHPA]
    exact (qHP D y).2
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy⟩ := qHP_surjective D ⟨(x : Equiv.Perm (Fin 45)), hx⟩
    exact ⟨y, Subtype.ext (by rw [coe_qHPA, hy])⟩

omit [Finite G] in
theorem qHPA_eq_of_qHP_eq {x : ↥(H z)} {y : Equiv.Perm (Fin 45)} (hy : y ∈ QP45.originalSubgroup)
    (hx : qHP D x = ⟨y, hy⟩) : qHPA D x = ⟨y, QP45_le_QA45 hy⟩ :=
  Subtype.ext (by rw [coe_qHPA, hx])

omit [Finite G] in
theorem mem_J_iff_qHPA_eq_one {x : G} (hx : x ∈ H z) : x ∈ J z ↔ qHPA D ⟨x, hx⟩ = 1 := by
  rw [← MonoidHom.mem_ker, ker_qHPA, Subgroup.mem_subgroupOf]

noncomputable def liftP (x : QP45.originalSubgroup) : ↥(H z) :=
  Classical.choose (qHP_surjective D x)

omit [Finite G] in
@[simp] theorem qHP_liftP (x : QP45.originalSubgroup) : qHP D (liftP D x) = x :=
  Classical.choose_spec (qHP_surjective D x)

noncomputable abbrev a2HP : ↥(H z) := liftP D ⟨alpha2, alpha2_mem_Q⟩

noncomputable abbrev b2HP : ↥(H z) := liftP D ⟨beta2, beta2_mem_Q⟩

noncomputable abbrev betaHP : ↥(H z) := liftP D ⟨beta, beta_mem_Q⟩

omit [Finite G] in
theorem qHP_a2HP : qHP D (a2HP D) = ⟨alpha2, alpha2_mem_Q⟩ := qHP_liftP D _

omit [Finite G] in
theorem qHP_b2HP : qHP D (b2HP D) = ⟨beta2, beta2_mem_Q⟩ := qHP_liftP D _

omit [Finite G] in
theorem qHP_betaHP : qHP D (betaHP D) = ⟨beta, beta_mem_Q⟩ := qHP_liftP D _

theorem not_three_dvd_card_ker_inf (S : Subgroup ↥(H z)) :
    ¬ 3 ∣ Nat.card ↥((qHP D).ker ⊓ S) := by
  obtain ⟨a, ha⟩ := ((isPGroup_ker_qHP D).to_le inf_le_left).exists_card_eq
  rw [ha]
  intro h
  have h3 := (Nat.prime_three.dvd_of_dvd_pow h)
  norm_num at h3

theorem orderOf_sigma2Q : orderOf (⟨sigma2, sigma2_mem_Q⟩ : QP45.originalSubgroup) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime sigma2_cube sigma2_ne_one

theorem e9_mem_Q : e9 ∈ QP45.originalSubgroup := by
  have hnorm : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  have h2 := Subgroup.pow_index_mem (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    (⟨e9, e9_mem_A⟩ : QA45.originalSubgroup)
  rw [index_QP45] at h2
  have h10 : (⟨e9, e9_mem_A⟩ : QA45.originalSubgroup) =
      ((⟨e9, e9_mem_A⟩ : QA45.originalSubgroup) ^ 2) ^ 5 := by
    apply Subtype.ext
    change e9 = (e9 ^ 2) ^ 5
    rw [← pow_mul, show 2 * 5 = 9 + 1 from rfl, pow_succ, e9_pow_nine, one_mul]
  have h := Subgroup.pow_mem _ h2 5
  rw [← h10, Subgroup.mem_subgroupOf] at h
  exact h

theorem exists_order_nine_root_sigma1_P :
    ∃ y : ↥(H z), orderOf y = 9 ∧ orderOf (y ^ 3) = 3 ∧
      qHP D (y ^ 3) = ⟨sigma1, sigma1_mem_Q⟩ := by
  have hord : orderOf (qHP D (liftP D ⟨e9, e9_mem_Q⟩)) = 9 := by
    rw [qHP_liftP, Subgroup.orderOf_mk]
    exact orderOf_e9
  obtain ⟨n, hn, hn9⟩ := exists_pow_lift_orderOf_eq (qHP D) (isPGroup_ker_qHP D) (m := 9)
    ⟨4, rfl⟩ (by norm_num) hord
  refine ⟨liftP D ⟨e9, e9_mem_Q⟩ ^ n, hn9, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (by norm_num) (by rw [hn9]; norm_num), hn9]
  · rw [map_pow, hn, qHP_liftP]
    exact Subtype.ext e9_cube

noncomputable def nineRootHP : ↥(H z) := Classical.choose (exists_order_nine_root_sigma1_P D)

noncomputable def s1HP : ↥(H z) := nineRootHP D ^ 3

theorem orderOf_nineRootHP : orderOf (nineRootHP D) = 9 :=
  (Classical.choose_spec (exists_order_nine_root_sigma1_P D)).1

theorem orderOf_s1HP : orderOf (s1HP D) = 3 :=
  (Classical.choose_spec (exists_order_nine_root_sigma1_P D)).2.1

theorem qHP_s1HP : qHP D (s1HP D) = ⟨sigma1, sigma1_mem_Q⟩ :=
  (Classical.choose_spec (exists_order_nine_root_sigma1_P D)).2.2

theorem exists_lift_u_swap :
    ∃ x : ↥(H z), qHP D x = ⟨u, u_mem_Q⟩ ∧ Commute (s1HP D) (x * s1HP D * x⁻¹) ∧
      x * (x * s1HP D * x⁻¹) * x⁻¹ = s1HP D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ₁ := s1HP D with hσ₁
  have hσ₁3 : orderOf σ₁ = 3 := orderOf_s1HP D
  have hP : IsPGroup 3 (Subgroup.zpowers σ₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ₁3, pow_one])
  obtain ⟨c₀, -, hc₀, hc₀σ⟩ := exists_commute_mem_fibre (qHP D) (S := ⊤) hP le_top
    (not_three_dvd_card_ker_inf D ⊤) (m₀ := liftP D ⟨sigma2, sigma2_mem_Q⟩) (Subgroup.mem_top _)
    (by
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [qHP_liftP, map_zpow, qHP_s1HP]
      apply Commute.eq
      apply Commute.zpow_left
      exact Subtype.ext sigma1_commute_sigma2)
  rw [qHP_liftP] at hc₀
  obtain ⟨n, hn, hn3⟩ := exists_pow_lift_orderOf_eq (qHP D) (isPGroup_ker_qHP D) (c := c₀)
    (m := 3) ⟨1, rfl⟩ (by norm_num) (by rw [hc₀]; exact orderOf_sigma2Q)
  set σ₂ := c₀ ^ n with hσ₂
  have hσ₂q : qHP D σ₂ = ⟨sigma2, sigma2_mem_Q⟩ := by rw [hσ₂, hn, hc₀]
  have hcomm : σ₁ * σ₂ = σ₂ * σ₁ := by
    have h : Commute σ₁ c₀ := hc₀σ σ₁ (Subgroup.mem_zpowers σ₁)
    rw [hσ₂]
    exact (h.pow_right n).eq
  set x₁ := liftP D ⟨u, u_mem_Q⟩ with hx₁
  have hτ₀ : orderOf (x₁ * σ₁ * x₁⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hσ₁3]
  have hτ₀q : qHP D (x₁ * σ₁ * x₁⁻¹) = ⟨sigma2, sigma2_mem_Q⟩ := by
    rw [map_mul, map_mul, map_inv, hx₁, qHP_liftP, qHP_s1HP]
    exact Subtype.ext sigma1_conj_u
  obtain ⟨j, hj, hjτ⟩ := CFSG.GroupTheory.exists_conj_of_order_three_of_mem_same_coset
    (isPGroup_J_subgroupOf (z := z)) hn3 hτ₀ (by
      rw [← ker_qHP D, MonoidHom.mem_ker, map_mul, map_inv, hσ₂q, hτ₀q, inv_mul_cancel])
  set x₂ := j * x₁ with hx₂
  have hx₂σ : x₂ * σ₁ * x₂⁻¹ = σ₂ := by
    rw [hx₂, ← hjτ]
    group
  have hj1 : qHP D j = 1 := by
    rw [← MonoidHom.mem_ker, ker_qHP D]
    exact hj
  have hx₂q : qHP D x₂ = ⟨u, u_mem_Q⟩ := by
    rw [hx₂, map_mul, hj1, one_mul, hx₁, qHP_liftP]
  set τ := x₂⁻¹ * σ₁ * x₂ with hτ
  have hτ3 : orderOf τ = 3 := by
    rw [hτ, show x₂⁻¹ * σ₁ * x₂ = x₂⁻¹ * σ₁ * x₂⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hσ₁3]
  have hτq : qHP D τ = ⟨sigma2, sigma2_mem_Q⟩ := by
    rw [hτ, map_mul, map_mul, map_inv, hx₂q, qHP_s1HP]
    apply Subtype.ext
    change u⁻¹ * sigma1 * u = sigma2
    have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right u_sq
    calc u⁻¹ * sigma1 * u = u * sigma1 * u⁻¹ := by rw [hu]
      _ = sigma2 := sigma1_conj_u
  have hστ : σ₂ = x₂ * σ₁ * x₂⁻¹ := hx₂σ.symm
  have h1 : x₂⁻¹ * σ₂ * x₂ = σ₁ := by rw [hστ]; group
  have hτC : τ ∈ Subgroup.centralizer ({σ₁} : Set ↥(H z)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc τ * σ₁ = x₂⁻¹ * σ₁ * x₂ * (x₂⁻¹ * σ₂ * x₂) := by rw [h1]
      _ = x₂⁻¹ * (σ₁ * σ₂) * x₂ := by group
      _ = x₂⁻¹ * (σ₂ * σ₁) * x₂ := by rw [hcomm]
      _ = x₂⁻¹ * σ₂ * x₂ * (x₂⁻¹ * σ₁ * x₂) := by group
      _ = σ₁ * τ := by rw [h1]
  have hσ₂C : σ₂ ∈ Subgroup.centralizer ({σ₁} : Set ↥(H z)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  obtain ⟨c, ⟨hcJ, hcC⟩, hcτ⟩ := exists_conj_mem_inf_of_order_three
    (J := (J z).subgroupOf (H z)) (isPGroup_J_subgroupOf (z := z)) hτC hσ₂C hτ3 hn3 (by
      rw [← ker_qHP D, MonoidHom.mem_ker, map_mul, map_inv, hτq, hσ₂q, inv_mul_cancel])
  have hcσ : c * σ₁ = σ₁ * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hc1 : qHP D c = 1 := by
    rw [← MonoidHom.mem_ker, ker_qHP D]
    exact hcJ
  refine ⟨x₂ * c, ?_, ?_, ?_⟩
  · rw [map_mul, hx₂q, hc1, mul_one]
  · have h1 : x₂ * c * σ₁ * (x₂ * c)⁻¹ = σ₂ := by
      rw [← hx₂σ]
      calc x₂ * c * σ₁ * (x₂ * c)⁻¹ = x₂ * (c * σ₁) * c⁻¹ * x₂⁻¹ := by group
        _ = x₂ * σ₁ * x₂⁻¹ := by rw [hcσ]; group
    rw [h1]
    exact hcomm
  · have h1 : x₂ * c * σ₁ * (x₂ * c)⁻¹ = σ₂ := by
      rw [← hx₂σ]
      calc x₂ * c * σ₁ * (x₂ * c)⁻¹ = x₂ * (c * σ₁) * c⁻¹ * x₂⁻¹ := by group
        _ = x₂ * σ₁ * x₂⁻¹ := by rw [hcσ]; group
    rw [h1]
    calc x₂ * c * σ₂ * (x₂ * c)⁻¹ = x₂ * (c * σ₂ * c⁻¹) * x₂⁻¹ := by group
      _ = x₂ * τ * x₂⁻¹ := by rw [hcτ]
      _ = σ₁ := by rw [hτ]; group

noncomputable def uHP : ↥(H z) := Classical.choose (exists_lift_u_swap D)

noncomputable def s2HP : ↥(H z) := uHP D * s1HP D * (uHP D)⁻¹

noncomputable def sHP : ↥(H z) := s1HP D * (s2HP D)⁻¹

theorem qHP_uHP : qHP D (uHP D) = ⟨u, u_mem_Q⟩ :=
  (Classical.choose_spec (exists_lift_u_swap D)).1

theorem commute_s1HP_s2HP : Commute (s1HP D) (s2HP D) :=
  (Classical.choose_spec (exists_lift_u_swap D)).2.1

theorem uHP_conj_s2HP : uHP D * s2HP D * (uHP D)⁻¹ = s1HP D :=
  (Classical.choose_spec (exists_lift_u_swap D)).2.2

theorem qHP_s2HP : qHP D (s2HP D) = ⟨sigma2, sigma2_mem_Q⟩ := by
  rw [s2HP, map_mul, map_mul, map_inv, qHP_uHP, qHP_s1HP]
  exact Subtype.ext sigma1_conj_u

theorem orderOf_s2HP : orderOf (s2HP D) = 3 := by
  rw [s2HP, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_s1HP]

theorem qHP_sHP :
    qHP D (sHP D) = ⟨sigma1 * sigma2⁻¹,
      QP45.originalSubgroup.mul_mem sigma1_mem_Q (QP45.originalSubgroup.inv_mem sigma2_mem_Q)⟩ := by
  rw [sHP, map_mul, map_inv, qHP_s1HP, qHP_s2HP]
  rfl

theorem orderOf_sHP : orderOf (sHP D) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : s1HP D ^ 3 = 1 := by
    rw [← orderOf_s1HP D]
    exact pow_orderOf_eq_one _
  have h2 : s2HP D ^ 3 = 1 := by
    rw [← orderOf_s2HP D]
    exact pow_orderOf_eq_one _
  refine orderOf_eq_prime ?_ ?_
  · rw [sHP, ((commute_s1HP_s2HP D).inv_right).mul_pow, inv_pow, h1, h2, inv_one, one_mul]
  · intro h
    have h1 := congrArg (fun x => ((qHP D x : QP45.originalSubgroup) : Equiv.Perm (Fin 45))) h
    simp only [qHP_sHP, map_one, OneMemClass.coe_one] at h1
    exact sigma1_ne_sigma2 (mul_inv_eq_one.mp h1)

theorem uHP_conj_sHP : uHP D * sHP D * (uHP D)⁻¹ = (sHP D)⁻¹ := by
  have h1 : uHP D * s1HP D * (uHP D)⁻¹ = s2HP D := rfl
  have h2 := uHP_conj_s2HP D
  calc uHP D * sHP D * (uHP D)⁻¹ =
        (uHP D * s1HP D * (uHP D)⁻¹) * (uHP D * s2HP D * (uHP D)⁻¹)⁻¹ := by rw [sHP]; group
    _ = (sHP D)⁻¹ := by rw [h1, h2, sHP]; group

theorem exists_lift_t_commute :
    ∃ x : ↥(H z), qHP D x = ⟨t, t_mem_Q⟩ ∧ Commute x (s1HP D) ∧ Commute x (s2HP D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP1 : IsPGroup 3 (Subgroup.zpowers (s1HP D)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_s1HP, pow_one])
  have hP2 : IsPGroup 3 (Subgroup.zpowers (s2HP D)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_s2HP, pow_one])
  have htc : ∀ (σ : ↥(H z)) (y : Equiv.Perm (Fin 45)) (hy : y ∈ QP45.originalSubgroup),
      qHP D σ = ⟨y, hy⟩ → t * y = y * t → ∀ g ∈ Subgroup.zpowers σ,
      qHP D g * ⟨t, t_mem_Q⟩ = ⟨t, t_mem_Q⟩ * qHP D g := by
    intro σ y hy hσ hty g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [map_zpow, hσ]
    apply Commute.eq
    apply Commute.zpow_left
    exact Subtype.ext hty.symm
  obtain ⟨x₁, -, hx₁, hx₁σ⟩ := exists_commute_mem_fibre (qHP D) (S := ⊤) hP1 le_top
    (not_three_dvd_card_ker_inf D ⊤) (m₀ := liftP D ⟨t, t_mem_Q⟩) (Subgroup.mem_top _)
    (by rw [qHP_liftP]; exact htc _ _ _ (qHP_s1HP D) t_commute_sigma1)
  rw [qHP_liftP] at hx₁
  have hx₁C : x₁ ∈ Subgroup.centralizer ({s1HP D} : Set ↥(H z)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx₁σ (s1HP D) (Subgroup.mem_zpowers _)).symm
  have hP2C : Subgroup.zpowers (s2HP D) ≤ Subgroup.centralizer ({s1HP D} : Set ↥(H z)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_s1HP_s2HP D).eq.symm
  obtain ⟨x, hxC, hx, hxσ⟩ := exists_commute_mem_fibre (qHP D) hP2 hP2C
    (not_three_dvd_card_ker_inf D _) hx₁C
    (by rw [hx₁]; exact htc _ _ _ (qHP_s2HP D) t_commute_sigma2)
  refine ⟨x, hx.trans hx₁, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mp hxC
  · exact (hxσ (s2HP D) (Subgroup.mem_zpowers _)).symm

noncomputable def tHP : ↥(H z) := Classical.choose (exists_lift_t_commute D)

theorem qHP_tHP : qHP D (tHP D) = ⟨t, t_mem_Q⟩ :=
  (Classical.choose_spec (exists_lift_t_commute D)).1

theorem commute_tHP_s1HP : Commute (tHP D) (s1HP D) :=
  (Classical.choose_spec (exists_lift_t_commute D)).2.1

theorem commute_tHP_s2HP : Commute (tHP D) (s2HP D) :=
  (Classical.choose_spec (exists_lift_t_commute D)).2.2

theorem qHPA_s1HP : qHPA D (s1HP D) = ⟨sigma1, sigma1_mem_A⟩ :=
  qHPA_eq_of_qHP_eq D _ (qHP_s1HP D)

theorem qHPA_s2HP : qHPA D (s2HP D) = ⟨sigma2, sigma2_mem_A⟩ :=
  qHPA_eq_of_qHP_eq D _ (qHP_s2HP D)

end Map

end CFSG.RankThree.GF2n.Parrott
