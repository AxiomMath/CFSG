module

public import Mathlib.GroupTheory.PGroup

public section

open scoped commutatorElement

namespace CFSG.Quasithin.H13.L827X.LBGroupAbs

variable {H : Type*} [Group H]

@[expose] def Yof (N : Subgroup H) : Subgroup H := ⁅(⊤ : Subgroup H), ⊤⁆ ⊔ N

@[expose] def IsXiShape (p : ℕ) (N : Subgroup H) : Prop :=
  N.index = p ^ 2 ∨ (N.index = p ^ 3 ∧ ¬ ⁅(⊤ : Subgroup H), ⊤⁆ ≤ N)

section QuotientFacts

variable {Q : Type*} [Group Q]

private theorem exists_pow_eq_of_card_prime {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p) {g : G} (hg : g ≠ 1) (x : G) : ∃ j : ℕ, g ^ j = x := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.out.ne_zero)
  have hord : orderOf g = p := by
    have hd : orderOf g ∣ p := hG ▸ orderOf_dvd_natCard g
    rcases (Nat.dvd_prime hp.out).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg
    · exact h
  have hcard : Nat.card (Subgroup.zpowers g) = Nat.card G := by
    rw [Nat.card_zpowers, hord, hG]
  have htop : Subgroup.zpowers g = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  have hx : x ∈ Subgroup.zpowers g := by
    rw [htop]; exact Subgroup.mem_top x
  exact (Submonoid.mem_powers_iff x g).mp (mem_powers_iff_mem_zpowers.mpr hx)

private theorem pow_eq_one_of_card_eq {G : Type*} [Group G] {p : ℕ} (hG : Nat.card G = p)
    (x : G) : x ^ p = 1 := by
  rw [← hG]; exact pow_card_eq_one'

private theorem pow_eq_one_of_mem_center_card {p : ℕ} {x : Q}
    (hZ : Nat.card (Subgroup.center Q) = p) (hx : x ∈ Subgroup.center Q) : x ^ p = 1 := by
  have h := congrArg Subtype.val (pow_eq_one_of_card_eq hZ (⟨x, hx⟩ : Subgroup.center Q))
  simpa using h

private theorem comm_mul_central {u v : Q} (hu : ∀ g : Q, g * u = u * g)
    (hv : ∀ g : Q, g * v = v * g) (g h : Q) : ⁅u * g, v * h⁆ = ⁅g, h⁆ := by
  have key : ∀ x y : Q, ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := fun x y => by
    simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  have huv : ∀ x : Q, x * (u * v) = u * v * x := fun x => by
    calc x * (u * v) = x * u * v := (mul_assoc _ _ _).symm
      _ = u * x * v := by rw [hu x]
      _ = u * (x * v) := mul_assoc _ _ _
      _ = u * (v * x) := by rw [hv x]
      _ = u * v * x := (mul_assoc _ _ _).symm
  have e1 : u * g * (v * h) = u * v * (g * h) := by
    calc u * g * (v * h) = u * (g * v) * h := by simp only [mul_assoc]
      _ = u * (v * g) * h := by rw [hv g]
      _ = u * v * (g * h) := by simp only [mul_assoc]
  have e2 : v * h * (u * g) = u * v * (h * g) := by
    calc v * h * (u * g) = v * (h * u) * g := by simp only [mul_assoc]
      _ = v * (u * h) * g := by rw [hu h]
      _ = v * u * (h * g) := by simp only [mul_assoc]
      _ = u * v * (h * g) := by rw [hv u]
  rw [key (u * g) (v * h), key g h, e1, e2]
  calc u * v * (g * h) * (u * v * (h * g))⁻¹
      = (u * v) * ((g * h) * (h * g)⁻¹) * (u * v)⁻¹ := by group
    _ = ((g * h) * (h * g)⁻¹) * (u * v) * (u * v)⁻¹ := by
        rw [← huv ((g * h) * (h * g)⁻¹)]
    _ = (g * h) * (h * g)⁻¹ := mul_inv_cancel_right _ _

private theorem card_center_eq_of_card_cube {p : ℕ} [hp : Fact p.Prime] [Finite Q]
    (hQ : Nat.card Q = p ^ 3) (hnc : ∃ a b : Q, a * b ≠ b * a) :
    Nat.card (Subgroup.center Q) = p := by
  obtain ⟨a, b, hab⟩ := hnc
  have hpQ : IsPGroup p Q := IsPGroup.iff_card.mpr ⟨3, hQ⟩
  haveI : Nontrivial Q := ⟨⟨a, 1, fun h => hab (by rw [h, one_mul, mul_one])⟩⟩
  haveI := IsPGroup.center_nontrivial hpQ
  have hZ1 : 1 < Nat.card (Subgroup.center Q) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hdvd : Nat.card (Subgroup.center Q) ∣ p ^ 3 := by
    rw [← hQ]; exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · simp [hk] at hZ1
    · rw [hk, pow_one]
  · exfalso
    have hidx : (Subgroup.center Q).index * Nat.card (Subgroup.center Q) = Nat.card Q :=
      Subgroup.index_mul_card _
    have hdiv : (Subgroup.center Q).index ∣ p := by
      have h1 : (Subgroup.center Q).index * p ^ 2 ∣ (Subgroup.center Q).index * p ^ k :=
        mul_dvd_mul_left _ (pow_dvd_pow p hk2)
      rw [← hk, hidx, hQ] at h1
      have h2 : p ^ 3 = p * p ^ 2 := by ring
      rw [h2] at h1
      exact Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.out.pos 2) h1
    have hdiv' : Nat.card (Q ⧸ Subgroup.center Q) ∣ p := hdiv
    haveI : IsCyclic (Q ⧸ Subgroup.center Q) := isCyclic_of_card_dvd_prime hdiv'
    exact hab ((isMulCommutative_of_isCyclic_quotient_center_self Q).is_comm.comm a b)

private theorem commutator_le_center_of_card_quot {p : ℕ} [Fact p.Prime]
    (hZ : Nat.card (Q ⧸ Subgroup.center Q) = p ^ 2) :
    ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ Subgroup.center Q := by
  have hcomm : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hZ
  rw [Subgroup.commutator_le]
  intro g _ h _
  apply (QuotientGroup.eq_one_iff _).mp
  have e : ((⁅g, h⁆ : Q) : Q ⧸ Subgroup.center Q) =
      ⁅(g : Q ⧸ Subgroup.center Q), (h : Q ⧸ Subgroup.center Q)⁆ :=
    map_commutatorElement (QuotientGroup.mk' (Subgroup.center Q)) g h
  rw [e, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm.is_comm.comm _ _

private theorem commutator_eq_center_of_card_cube {p : ℕ} [Fact p.Prime] [Finite Q]
    (hQ : Nat.card Q = p ^ 3) (hnc : ∃ a b : Q, a * b ≠ b * a) :
    ⁅(⊤ : Subgroup Q), ⊤⁆ = Subgroup.center Q := by
  have hZ := card_center_eq_of_card_cube hQ hnc
  have hidx : (Subgroup.center Q).index * Nat.card (Subgroup.center Q) = Nat.card Q :=
    Subgroup.index_mul_card _
  have hZsq : Nat.card (Q ⧸ Subgroup.center Q) = p ^ 2 := by
    have h1 : (Subgroup.center Q).index * p = p ^ 2 * p := by
      rw [hZ, hQ] at hidx
      rw [hidx]; ring
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h1
  have hle := commutator_le_center_of_card_quot hZsq
  have hdvd : Nat.card ↥⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ∣ p := by
    rw [← hZ]; exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hmem : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    have hne : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hsub : Subsingleton ↥⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    have h3 := Subsingleton.elim (⟨⁅a, b⁆, hmem⟩ : ↥⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆) 1
    exact hne (congrArg Subtype.val h3)
  · exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hZ, h1]))

private theorem mulAut_apply_apply {G : Type*} [Group G] {β : MulAut G} (hβ : β ^ 2 = 1)
    (z : G) : β (β z) = z := by
  have h := congrArg (fun f : MulAut G => f z) hβ
  simpa [pow_two, MulAut.mul_apply] using h

end QuotientFacts

section Main

variable [Finite H] {p : ℕ} [Fact p.Prime] {N : Subgroup H} [N.Normal]

private theorem commute_mk_of_comm_mem {x y : H} (h : ⁅x, y⁆ ∈ N) :
    (x : H ⧸ N) * (y : H ⧸ N) = (y : H ⧸ N) * (x : H ⧸ N) := by
  have e : ((⁅x, y⁆ : H) : H ⧸ N) = ⁅(x : H ⧸ N), (y : H ⧸ N)⁆ :=
    map_commutatorElement (QuotientGroup.mk' N) x y
  have h1 : ((⁅x, y⁆ : H) : H ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr h
  rw [e, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

private theorem comm_mem_of_commute_mk {x y : H}
    (h : (x : H ⧸ N) * (y : H ⧸ N) = (y : H ⧸ N) * (x : H ⧸ N)) : ⁅x, y⁆ ∈ N := by
  apply (QuotientGroup.eq_one_iff _).mp
  have e : ((⁅x, y⁆ : H) : H ⧸ N) = ⁅(x : H ⧸ N), (y : H ⧸ N)⁆ :=
    map_commutatorElement (QuotientGroup.mk' N) x y
  rw [e, commutatorElement_eq_one_iff_mul_comm]
  exact h

private theorem conj_mem_normal {n : H} (hn : n ∈ N) (g : H) : g * n * g⁻¹ ∈ N :=
  Subgroup.Normal.conj_mem (H := N) inferInstance n hn g

private theorem le_Yof' : N ≤ Yof N := by
  unfold Yof; exact le_sup_right

private theorem commutator_le_of_index_sq (hN : N.index = p ^ 2) :
    ⁅(⊤ : Subgroup H), ⊤⁆ ≤ N := by
  have hcomm : IsMulCommutative (H ⧸ N) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (show Nat.card (H ⧸ N) = p ^ 2 from hN)
  rw [Subgroup.commutator_le]
  intro g _ h _
  exact comm_mem_of_commute_mk (hcomm.is_comm.comm _ _)

private theorem mem_of_mem_Yof_of_index_sq (hN : N.index = p ^ 2) {y : H} (hy : y ∈ Yof N) :
    y ∈ N := by
  unfold Yof at hy
  rwa [sup_eq_right.mpr (commutator_le_of_index_sq hN)] at hy

private theorem cube_structure (hN : N.index = p ^ 3) (hnc : ¬ ⁅(⊤ : Subgroup H), ⊤⁆ ≤ N) :
    Yof N = (Subgroup.center (H ⧸ N)).comap (QuotientGroup.mk' N) ∧
      Nat.card (Subgroup.center (H ⧸ N)) = p := by
  haveI : Finite (H ⧸ N) :=
    Finite.of_surjective (QuotientGroup.mk : H → H ⧸ N) QuotientGroup.mk_surjective
  have hQ : Nat.card (H ⧸ N) = p ^ 3 := hN
  have hnc' : ∃ a b : H ⧸ N, a * b ≠ b * a := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    exact hnc (Subgroup.commutator_le.mpr fun a _ b _ => comm_mem_of_commute_mk (hcon _ _))
  have hK := commutator_eq_center_of_card_cube hQ hnc'
  have hZ := card_center_eq_of_card_cube hQ hnc'
  have hmap : Subgroup.map (QuotientGroup.mk' N) (Yof N) = Subgroup.center (H ⧸ N) := by
    rw [← hK]
    unfold Yof
    rw [Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
      QuotientGroup.map_mk'_self, sup_bot_eq]
  have h := QuotientGroup.comap_map_mk' N (Yof N)
  rw [hmap, sup_eq_right.mpr le_Yof'] at h
  exact ⟨h.symm, hZ⟩

private theorem mk_mem_center_of_mem_Yof (hS : IsXiShape p N) {y : H} (hy : y ∈ Yof N) :
    (y : H ⧸ N) ∈ Subgroup.center (H ⧸ N) := by
  obtain h2 | ⟨h3, hnc⟩ := hS
  · have hyN : y ∈ N := mem_of_mem_Yof_of_index_sq h2 hy
    rw [(QuotientGroup.eq_one_iff y).mpr hyN]
    exact Subgroup.one_mem _
  · rw [(cube_structure h3 hnc).1] at hy
    exact hy

private theorem index_center_eq_sq (hN : N.index = p ^ 3)
    (hZ : Nat.card (Subgroup.center (H ⧸ N)) = p) :
    (Subgroup.center (H ⧸ N)).index = p ^ 2 := by
  haveI : Finite (H ⧸ N) :=
    Finite.of_surjective (QuotientGroup.mk : H → H ⧸ N) QuotientGroup.mk_surjective
  have h1 : (Subgroup.center (H ⧸ N)).index * Nat.card (Subgroup.center (H ⧸ N)) =
      Nat.card (H ⧸ N) := Subgroup.index_mul_card _
  rw [hZ] at h1
  have hQ : Nat.card (H ⧸ N) = p ^ 3 := hN
  rw [hQ] at h1
  apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
  rw [h1]; ring

theorem Yof_eq_of_index_sq (hN : N.index = p ^ 2) : Yof N = N := by
  unfold Yof
  exact sup_eq_right.mpr (commutator_le_of_index_sq hN)

theorem index_Yof_of_index_cube (hN : N.index = p ^ 3) (hnc : ¬ ⁅(⊤ : Subgroup H), ⊤⁆ ≤ N) :
    (Yof N).index = p ^ 2 ∧ N.relIndex (Yof N) = p := by
  obtain ⟨hYeq, hZ⟩ := cube_structure hN hnc
  have hidx := index_center_eq_sq hN hZ
  have hYidx : (Yof N).index = p ^ 2 := by
    rw [hYeq, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact hidx
  refine ⟨hYidx, ?_⟩
  have h2 : N.relIndex (Yof N) * (Yof N).index = N.index := Subgroup.relIndex_mul_index le_Yof'
  rw [hYidx, hN] at h2
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos 2)
  rw [h2]; ring

theorem comm_mem_of_mem_Yof (hS : IsXiShape p N) {y : H} (hy : y ∈ Yof N) (h : H) :
    ⁅y, h⁆ ∈ N := by
  apply comm_mem_of_commute_mk
  exact (Subgroup.mem_center_iff.mp (mk_mem_center_of_mem_Yof hS hy) (h : H ⧸ N)).symm

theorem pow_mem_of_mem_Yof (hS : IsXiShape p N) {y : H} (hy : y ∈ Yof N) : y ^ p ∈ N := by
  obtain h2 | ⟨h3, hnc⟩ := hS
  · exact N.pow_mem (mem_of_mem_Yof_of_index_sq h2 hy) p
  · obtain ⟨hYeq, hZ⟩ := cube_structure h3 hnc
    have hy' : (y : H ⧸ N) ∈ Subgroup.center (H ⧸ N) := by
      rw [hYeq] at hy; exact hy
    have h1 : (y : H ⧸ N) ^ p = 1 := pow_eq_one_of_mem_center_card hZ hy'
    have h4 : (QuotientGroup.mk' N) (y ^ p) = 1 := by
      rw [map_pow]; exact h1
    exact (QuotientGroup.eq_one_iff (y ^ p)).mp h4

theorem mem_Yof_of_forall_comm_mem (hN : N.index = p ^ 3) (hnc : ¬ ⁅(⊤ : Subgroup H), ⊤⁆ ≤ N)
    {y : H} (hy : ∀ b : H, ⁅y, b⁆ ∈ N) : y ∈ Yof N := by
  rw [(cube_structure hN hnc).1, Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro g
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N g
  exact (commute_mk_of_comm_mem (hy b)).symm

theorem exists_pow_mul_inv_mem (hN : N.index = p ^ 3) (hnc : ¬ ⁅(⊤ : Subgroup H), ⊤⁆ ≤ N)
    {z : H} (hz : z ∈ Yof N) (hzN : z ∉ N) {w : H} (hw : w ∈ Yof N) :
    ∃ j : ℕ, z ^ j * w⁻¹ ∈ N := by
  obtain ⟨hYeq, hZ⟩ := cube_structure hN hnc
  have hz' : (z : H ⧸ N) ∈ Subgroup.center (H ⧸ N) := by
    rw [hYeq] at hz; exact hz
  have hw' : (w : H ⧸ N) ∈ Subgroup.center (H ⧸ N) := by
    rw [hYeq] at hw; exact hw
  have hne : (⟨(z : H ⧸ N), hz'⟩ : ↥(Subgroup.center (H ⧸ N))) ≠ 1 := by
    intro h
    apply hzN
    apply (QuotientGroup.eq_one_iff z).mp
    exact congrArg Subtype.val h
  obtain ⟨j, hj⟩ := exists_pow_eq_of_card_prime hZ hne ⟨(w : H ⧸ N), hw'⟩
  have hj' : (z : H ⧸ N) ^ j = (w : H ⧸ N) := by
    have h := congrArg Subtype.val hj
    simpa using h
  refine ⟨j, ?_⟩
  apply (QuotientGroup.eq_one_iff _).mp
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hj', mul_inv_cancel]

theorem fix_mod_of_mem_Yof (hS : IsXiShape p N) {α : MulAut H} (hαN : ∀ x, α x ∈ N ↔ x ∈ N)
    (hα : ∀ x, α x * x⁻¹ ∈ Yof N) {y : H} (hy : y ∈ Yof N) : α y * y⁻¹ ∈ N := by
  let S : Subgroup H :=
    { carrier := {z : H | α z * z⁻¹ ∈ N}
      mul_mem' := by
        intro a b ha hb
        have ha' : α a * a⁻¹ ∈ N := ha
        have hb' : α b * b⁻¹ ∈ N := hb
        have e : α (a * b) * (a * b)⁻¹ = (α a * a⁻¹) * (a * (α b * b⁻¹) * a⁻¹) := by
          simp only [map_mul, mul_inv_rev]; group
        show α (a * b) * (a * b)⁻¹ ∈ N
        rw [e]
        exact N.mul_mem ha' (conj_mem_normal hb' a)
      one_mem' := by
        show α 1 * (1 : H)⁻¹ ∈ N
        simp
      inv_mem' := by
        intro a ha
        have ha' : α a * a⁻¹ ∈ N := ha
        have e : α a⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (α a * a⁻¹)⁻¹ * a⁻¹⁻¹ := by
          simp only [map_inv, mul_inv_rev, inv_inv]; group
        show α a⁻¹ * (a⁻¹)⁻¹ ∈ N
        rw [e]
        exact conj_mem_normal (N.inv_mem ha') a⁻¹ }
  have hNS : N ≤ S := fun n hn => by
    show α n * n⁻¹ ∈ N
    exact N.mul_mem ((hαN n).2 hn) (N.inv_mem hn)
  have hcomm : ∀ a b : H, ⁅a, b⁆ ∈ S := by
    intro a b
    show α ⁅a, b⁆ * ⁅a, b⁆⁻¹ ∈ N
    obtain ⟨ca, hca, hcaY⟩ : ∃ c : H, α a = c * a ∧ c ∈ Yof N :=
      ⟨α a * a⁻¹, by group, hα a⟩
    obtain ⟨cb, hcb, hcbY⟩ : ∃ c : H, α b = c * b ∧ c ∈ Yof N :=
      ⟨α b * b⁻¹, by group, hα b⟩
    have hu := Subgroup.mem_center_iff.mp (mk_mem_center_of_mem_Yof hS hcaY)
    have hv := Subgroup.mem_center_iff.mp (mk_mem_center_of_mem_Yof hS hcbY)
    have hmk : ∀ x y : H, ((⁅x, y⁆ : H) : H ⧸ N) = ⁅(x : H ⧸ N), (y : H ⧸ N)⁆ :=
      fun x y => map_commutatorElement (QuotientGroup.mk' N) x y
    have hφ : ((α ⁅a, b⁆ : H) : H ⧸ N) = ((⁅a, b⁆ : H) : H ⧸ N) := by
      rw [map_commutatorElement α a b, hca, hcb, hmk, hmk, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul]
      exact comm_mul_central hu hv _ _
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hφ, mul_inv_cancel]
  have hYS : Yof N ≤ S := by
    unfold Yof
    exact sup_le (Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b) hNS
  exact hYS hy

theorem pow_fix_mod (hS : IsXiShape p N) {α : MulAut H} (hαN : ∀ x, α x ∈ N ↔ x ∈ N)
    (hα : ∀ x, α x * x⁻¹ ∈ Yof N) (x : H) : (α ^ p) x * x⁻¹ ∈ N := by
  obtain ⟨c, hc, hcY⟩ : ∃ c : H, α x = c * x ∧ c ∈ Yof N := ⟨α x * x⁻¹, by group, hα x⟩
  have key : ∀ n : ℕ, ∃ m ∈ N, (α ^ n) x = c ^ n * x * m := by
    intro n
    induction n with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨m, hm, hmx⟩ := ih
      obtain ⟨n', hn'N, hn'⟩ : ∃ n' ∈ N, α (c ^ n) = n' * c ^ n :=
        ⟨α (c ^ n) * (c ^ n)⁻¹, fix_mod_of_mem_Yof hS hαN hα ((Yof N).pow_mem hcY n), by group⟩
      have ht : (c ^ (n + 1))⁻¹ * n' * (c ^ (n + 1))⁻¹⁻¹ ∈ N := conj_mem_normal hn'N _
      refine ⟨x⁻¹ * ((c ^ (n + 1))⁻¹ * n' * (c ^ (n + 1))⁻¹⁻¹) * x⁻¹⁻¹ * α m,
        N.mul_mem (conj_mem_normal ht x⁻¹) ((hαN m).2 hm), ?_⟩
      rw [pow_succ' α n, MulAut.mul_apply, hmx, map_mul, map_mul, hc, hn', pow_succ c n]
      generalize c ^ n = d
      group
  obtain ⟨m, hm, hmx⟩ := key p
  rw [hmx]
  have e : c ^ p * x * m * x⁻¹ = c ^ p * (x * m * x⁻¹) := by group
  rw [e]
  exact N.mul_mem (pow_mem_of_mem_Yof hS hcY) (conj_mem_normal hm x)

theorem invol_fix_mod (hS : IsXiShape p N) (hp2 : p ≠ 2) {α : MulAut H} (hα2 : α ^ 2 = 1)
    (hαN : ∀ x, α x ∈ N ↔ x ∈ N) (hα : ∀ x, α x * x⁻¹ ∈ Yof N) (x : H) : α x * x⁻¹ ∈ N := by
  have h2 := mulAut_apply_apply hα2
  obtain ⟨c, hc, hcY⟩ : ∃ c : H, α x = c * x ∧ c ∈ Yof N := ⟨α x * x⁻¹, by group, hα x⟩
  have hαc : α c = c⁻¹ := by
    have e : α c * c * x = 1 * x := by
      calc α c * c * x = α c * (c * x) := mul_assoc _ _ _
        _ = α c * α x := by rw [hc]
        _ = α (c * x) := (map_mul α c x).symm
        _ = α (α x) := by rw [hc]
        _ = x := h2 x
        _ = 1 * x := (one_mul x).symm
    exact eq_inv_of_mul_eq_one_left (mul_right_cancel e)
  have hcN : α c * c⁻¹ ∈ N := fix_mod_of_mem_Yof hS hαN hα hcY
  rw [hαc] at hcN
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hc2k : c ^ (2 * k) ∈ N := by
    have h1 : (c⁻¹ * c⁻¹) ^ k ∈ N := N.pow_mem hcN k
    have h3 : (c⁻¹ * c⁻¹) ^ k = (c ^ (2 * k))⁻¹ := by
      rw [← inv_pow, pow_mul, sq]
    rw [h3] at h1
    exact N.inv_mem_iff.mp h1
  have hcp : c ^ p ∈ N := pow_mem_of_mem_Yof hS hcY
  have hcID : c = c ^ p * (c ^ (2 * k))⁻¹ := by
    rw [hk, pow_succ', mul_inv_cancel_right]
  have hcmem : c ∈ N := by
    have h4 := N.mul_mem hcp (N.inv_mem hc2k)
    rwa [← hcID] at h4
  rw [hc, mul_inv_cancel_right]
  exact hcmem

theorem exists_inv_not_mem_Yof {α : MulAut H} (hα2 : α ^ 2 = 1) {x : H}
    (hx : α x * x⁻¹ ∉ Yof N) : ∃ y : H, y ∉ Yof N ∧ α y = y⁻¹ := by
  have h2 := mulAut_apply_apply hα2
  refine ⟨x * (α x)⁻¹, ?_, ?_⟩
  · intro hy
    apply hx
    have h3 := (Yof N).inv_mem hy
    rwa [mul_inv_rev, inv_inv] at h3
  · rw [map_mul, map_inv, h2, mul_inv_rev, inv_inv]

end Main

end CFSG.Quasithin.H13.L827X.LBGroupAbs
