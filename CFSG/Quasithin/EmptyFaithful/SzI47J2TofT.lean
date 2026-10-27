module

public import CFSG.Quasithin.EmptyFaithful.SzI47J2Steps

public section

namespace CFSG.Quasithin.SzI47J2T

open CFSG.QuasithinUnique CFSG.ShultStronglyClosedTI.InvolutionCounting
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem z_mul_z (F : J2Frame G z) : z * z = 1 := by
  rw [← pow_two]
  exact F.isTypeH2.sq

theorem eq_one_of_mem_M_of_mem_R {F : J2Frame G z} {hcount : involutionClassCount G = 2}
    {R : Subgroup G} (hR : IsKernelComplement F hcount R) {m : G} (hmM : m ∈ F.M hcount)
    (hmR : m ∈ R) : m = 1 := by
  have hW : m ∈ F.W := (F.mem_M_and_mem_T_iff hcount).mp ⟨hmM, hR.le_T hmR⟩
  have h : m ∈ R ⊓ F.W := ⟨hmR, hW⟩
  rw [hR.inf_W, Subgroup.mem_bot] at h
  exact h

theorem R_le_X {F : J2Frame G z} {hcount : involutionClassCount G = 2} {R : Subgroup G}
    (hR : IsKernelComplement F hcount R) : R ≤ F.X :=
  hR.le_T.trans F.T_le_X

theorem eq_of_mul_eq_of_mem_M_of_mem_R {F : J2Frame G z} {hcount : involutionClassCount G = 2}
    {R : Subgroup G} (hR : IsKernelComplement F hcount R) {m m' ρ ρ' : G}
    (hm : m ∈ F.M hcount) (hm' : m' ∈ F.M hcount) (hρ : ρ ∈ R) (hρ' : ρ' ∈ R)
    (h : m * ρ = m' * ρ') : m = m' ∧ ρ = ρ' := by
  have h1 : m'⁻¹ * m ∈ F.M hcount := (F.M hcount).mul_mem ((F.M hcount).inv_mem hm') hm
  have h2 : m'⁻¹ * m = ρ' * ρ⁻¹ := by
    calc m'⁻¹ * m = m'⁻¹ * (m * ρ) * ρ⁻¹ := by group
      _ = m'⁻¹ * (m' * ρ') * ρ⁻¹ := by rw [h]
      _ = ρ' * ρ⁻¹ := by group
  have h3 : m'⁻¹ * m ∈ R := by
    rw [h2]
    exact R.mul_mem hρ' (R.inv_mem hρ)
  have h4 := eq_one_of_mem_M_of_mem_R hR h1 h3
  have hmm : m = m' := by
    calc m = m' * (m'⁻¹ * m) := by group
      _ = m' := by rw [h4, mul_one]
  refine ⟨hmm, ?_⟩
  rw [hmm] at h
  exact mul_left_cancel h

theorem card_X {F : J2Frame G z} {hcount : involutionClassCount G = 2} {R : Subgroup G}
    (hR : IsKernelComplement F hcount R) :
    Nat.card ↥F.X = Nat.card ↥(F.M hcount) * 4 := by
  have h : Nat.card (↥(F.M hcount) × ↥R) = Nat.card ↥F.X := by
    refine Nat.card_eq_of_bijective
      (fun p => ⟨(p.1 : G) * (p.2 : G), F.X.mul_mem (F.M_le_X hcount p.1.2) (R_le_X hR p.2.2)⟩)
      ⟨?_, ?_⟩
    · rintro ⟨⟨m, hm⟩, ⟨ρ, hρ⟩⟩ ⟨⟨m', hm'⟩, ⟨ρ', hρ'⟩⟩ h
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_mem_M_of_mem_R hR hm hm' hρ hρ' (congrArg Subtype.val h)
      subst h1
      subst h2
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨m, hm, ρ, hρ, rfl⟩ := hR.X_eq g hg
      exact ⟨(⟨m, hm⟩, ⟨ρ, hρ⟩), rfl⟩
  rw [Nat.card_prod, hR.card] at h
  exact h.symm

theorem exists_mem_X_conj_mem_T (F : J2Frame G z) (hcount : involutionClassCount G = 2) {y : G}
    (hyX : y ∈ F.X) (hy2 : y * y = 1) : ∃ g ∈ F.X, g * y * g⁻¹ ∈ F.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hy1 : y = 1
  · exact ⟨1, F.X.one_mem, by rw [hy1]; simp⟩
  set P := F.sylowT hcount with hP
  have hyX1 : (⟨y, hyX⟩ : ↥F.X) ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
  have hsp : IsPGroup 2 (Subgroup.zpowers (⟨y, hyX⟩ : ↥F.X)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (Subtype.ext (by rw [pow_two]; exact hy2)) hyX1,
        pow_one])
  obtain ⟨P', hP'⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥F.X P' P
  have h1 : MulAut.conj g ⟨y, hyX⟩ ∈ MulAut.conj g • (P' : Subgroup ↥F.X) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hP' (Subgroup.mem_zpowers _))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  refine ⟨(g : G), g.2, ?_⟩
  have h2 : g * ⟨y, hyX⟩ * g⁻¹ ∈ (P : Subgroup ↥F.X) := by
    simpa [MulAut.conj_apply] using h1
  rw [hP, J2Frame.coe_sylowT, Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem isConj_z_iff (F : J2Frame G z) (hcount : involutionClassCount G = 2) {b : G}
    (hbX : b ∈ F.X) : IsConj z b ↔ b ∈ F.M hcount ∧ b * b = 1 ∧ b ≠ 1 := by
  constructor
  · intro h
    have hb2 : b * b = 1 := mul_self_eq_one_of_isConj (z_mul_z F) h
    have hb1 : b ≠ 1 := fun h1 => F.isTypeH2.ne_one (by
      rw [h1] at h
      exact isConj_one_left.mp h)
    refine ⟨?_, hb2, hb1⟩
    obtain ⟨g, hgX, hgT⟩ := exists_mem_X_conj_mem_T F hcount hbX hb2
    by_cases hW : g * b * g⁻¹ ∈ F.W
    · have hM : g * b * g⁻¹ ∈ F.M hcount := F.W_le_M hcount hW
      have h2 := F.conj_mem_M hcount hM (F.X.inv_mem hgX)
      have e : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
      rwa [e] at h2
    · exact absurd (h.trans (isConj_iff.mpr ⟨g, rfl⟩)) (F.not_isConj_of_mem_T hcount hgT hW)
  · rintro ⟨hbM, hb2, hb1⟩
    obtain ⟨m, -, hm⟩ := F.exists_mem_M_conj_eq_z hcount hbM hb2 hb1
    exact (isConj_iff.mpr ⟨m, hm⟩).symm

theorem isConj_t_iff (F : J2Frame G z) (hcount : involutionClassCount G = 2) {a : G}
    (haX : a ∈ F.X) : IsConj F.t a ↔ a * a = 1 ∧ a ≠ 1 ∧ a ∉ F.M hcount := by
  constructor
  · intro h
    have ha2 : a * a = 1 := mul_self_eq_one_of_isConj F.t_mul_t h
    have ha1 : a ≠ 1 := fun h1 => F.t_ne_one (by
      rw [h1] at h
      exact isConj_one_left.mp h)
    refine ⟨ha2, ha1, fun haM => F.not_isConj_t hcount ?_⟩
    exact ((isConj_z_iff F hcount haX).mpr ⟨haM, ha2, ha1⟩).trans h.symm
  · rintro ⟨ha2, ha1, haM⟩
    rcases F.isConj_z_or_t hcount ha2 ha1 with h | h
    · exact absurd ((isConj_z_iff F hcount haX).mp h).1 haM
    · exact h

theorem mem_X_of_mem_thompsonPairs (F : J2Frame G z) (hcount : involutionClassCount G = 2)
    {p : G × G} (hp : p ∈ thompsonPairs F.t z F.t) : p.1 ∈ F.X ∧ p.2 ∈ F.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime F.isTypeH2.sq F.isTypeH2.ne_one
  have ht2 : orderOf F.t = 2 := orderOf_eq_prime (by rw [pow_two]; exact F.t_mul_t) F.t_ne_one
  have hnc : ¬ IsConj F.t z := fun h => F.not_isConj_t hcount h.symm
  have hcl : ∀ x : G, orderOf x = 2 → IsConj F.t x ∨ IsConj z x := by
    intro x hx
    have hx2 : x * x = 1 := by
      rw [← pow_two, ← hx]
      exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      rintro rfl
      simp at hx
    exact (F.isConj_z_or_t hcount hx2 hx1).symm
  exact (CFSG.GH74.thompson_two_involution_class_order_formula ht2 hz2 hnc hcl).2 F.t
    (Or.inl rfl) p hp

omit [Finite G] in
theorem mul_t_mul_self (F : J2Frame G z) {a : G} (haX : a ∈ F.X) (ha2 : a * a = 1) :
    a * F.t * (a * F.t) = 1 := by
  have h := F.mem_X.mp haX
  calc a * F.t * (a * F.t) = a * (F.t * a) * F.t := by group
    _ = a * (a * F.t) * F.t := by rw [← h]
    _ = a * a * (F.t * F.t) := by group
    _ = 1 := by rw [ha2, F.t_mul_t, mul_one]

theorem data_of_mem_thompsonPairs {F : J2Frame G z} {hcount : involutionClassCount G = 2}
    {R : Subgroup G} (hR : IsKernelComplement F hcount R) {a b : G}
    (hab : (a, b) ∈ thompsonPairs F.t z F.t) :
    a * F.t ∈ F.M hcount ∧ b ∈ F.M hcount ∧ a * F.t * (a * F.t) = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧
      Odd (orderOf (a * F.t * b)) := by
  have hXX := mem_X_of_mem_thompsonPairs F hcount hab
  have haX : a ∈ F.X := hXX.1
  have hbX : b ∈ F.X := hXX.2
  obtain ⟨hta, hzb, ht⟩ := hab
  obtain ⟨hbM, hb2, hb1⟩ := (isConj_z_iff F hcount hbX).mp hzb
  obtain ⟨ha2, ha1, haM⟩ := (isConj_t_iff F hcount haX).mp hta
  obtain ⟨m, hm, ρ, hρ, hmρ⟩ := hR.X_eq a haX
  have hcomm : ∀ x ∈ F.M hcount, ρ * x = x * ρ := hR.comm_M ρ hρ
  have hρ2 : ρ * ρ = 1 := hR.mul_self ρ hρ
  have hcM : m * b ∈ F.M hcount := (F.M hcount).mul_mem hm hbM
  have hab' : a * b = m * b * ρ := by
    rw [hmρ]
    calc m * ρ * b = m * (ρ * b) := by group
      _ = m * (b * ρ) := by rw [hcomm b hbM]
      _ = m * b * ρ := by group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hk' : (m * b * ρ) ^ k = F.t := by
    rw [← hab']
    exact hk
  have hcρ : Commute (m * b) ρ := (hcomm _ hcM).symm
  rw [hcρ.mul_zpow] at hk'
  have hck : (m * b) ^ k ∈ F.M hcount := (F.M hcount).zpow_mem hcM k
  have hρk : ρ ^ k ∈ R := R.zpow_mem hρ k
  have hckR : (m * b) ^ k ∈ R := by
    have : (m * b) ^ k = F.t * (ρ ^ k)⁻¹ := eq_mul_inv_of_mul_eq hk'
    rw [this]
    exact R.mul_mem hR.t_mem (R.inv_mem hρk)
  have hck1 : (m * b) ^ k = 1 := eq_one_of_mem_M_of_mem_R hR hck hckR
  rw [hck1, one_mul] at hk'
  have hρ2' : ρ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hρ2
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · exfalso
    have h1 : ρ ^ k = 1 := by rw [hn, zpow_mul, hρ2', one_zpow]
    exact F.t_ne_one (hk'.symm.trans h1)
  · have h1 : ρ ^ k = ρ := by
      rw [hn, zpow_add, zpow_mul, hρ2', one_zpow, one_mul, zpow_one]
    have hρt : ρ = F.t := h1.symm.trans hk'
    have hat : a * F.t = m := by rw [hmρ, hρt, mul_assoc, F.t_mul_t, mul_one]
    have hod : Odd (orderOf (m * b)) := by
      have hd : (orderOf (m * b) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hck1
      exact Odd.of_dvd_nat (Int.natAbs_odd.mpr ⟨n, hn⟩) (Int.natCast_dvd.mp hd)
    have hm2 : m * m = 1 := by
      have := mul_t_mul_self F haX ha2
      rwa [hat] at this
    rw [hat]
    exact ⟨hm, hbM, hm2, hb2, hb1, hod⟩

theorem mem_thompsonPairs_of_data {F : J2Frame G z} {hcount : involutionClassCount G = 2}
    {R : Subgroup G} (hR : IsKernelComplement F hcount R) {m b : G} (hmM : m ∈ F.M hcount)
    (hbM : b ∈ F.M hcount) (hm2 : m * m = 1) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hodd : Odd (orderOf (m * b))) : (m * F.t, b) ∈ thompsonPairs F.t z F.t := by
  have htR : F.t ∈ R := hR.t_mem
  have hmt : F.t * m = m * F.t := hR.comm_M F.t htR m hmM
  have hbt : F.t * b = b * F.t := hR.comm_M F.t htR b hbM
  have hmX : m ∈ F.X := F.M_le_X hcount hmM
  have haX : m * F.t ∈ F.X := F.X.mul_mem hmX F.t_mem_X
  have ha2 : m * F.t * (m * F.t) = 1 := mul_t_mul_self F hmX hm2
  have htM : F.t ∉ F.M hcount := fun h => F.t_ne_one (eq_one_of_mem_M_of_mem_R hR h htR)
  have ha1 : m * F.t ≠ 1 := fun h => htM (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact (F.M hcount).inv_mem hmM)
  have haM : m * F.t ∉ F.M hcount := fun h => htM (by
    have := (F.M hcount).mul_mem ((F.M hcount).inv_mem hmM) h
    rwa [inv_mul_cancel_left] at this)
  refine ⟨(isConj_t_iff F hcount haX).mpr ⟨ha2, ha1, haM⟩,
    (isConj_z_iff F hcount (F.M_le_X hcount hbM)).mpr ⟨hbM, hb2, hb1⟩, ?_⟩
  show F.t ∈ Subgroup.zpowers (m * F.t * b)
  obtain ⟨r, hr⟩ := hodd
  have hcom : Commute (m * b) F.t :=
    Commute.mul_left (show Commute m F.t from hmt.symm) (show Commute b F.t from hbt.symm)
  have e : m * F.t * b = m * b * F.t := by
    calc m * F.t * b = m * (F.t * b) := by group
      _ = m * (b * F.t) := by rw [hbt]
      _ = m * b * F.t := by group
  have hpow : (m * F.t * b) ^ orderOf (m * b) = F.t := by
    rw [e, hcom.mul_pow, pow_orderOf_eq_one, one_mul, hr, pow_succ, pow_mul, pow_two, F.t_mul_t,
      one_pow, one_mul]
  have := Subgroup.npow_mem_zpowers (m * F.t * b) (orderOf (m * b))
  rwa [hpow] at this

@[expose] def oddPairs (M : Type*) [Group M] : Set (M × M) :=
  {q | q.1 * q.1 = 1 ∧ q.2 * q.2 = 1 ∧ q.2 ≠ 1 ∧ Odd (orderOf (q.1 * q.2))}

theorem thompsonPairs_eq_image {F : J2Frame G z} {hcount : involutionClassCount G = 2}
    {R : Subgroup G} (hR : IsKernelComplement F hcount R) :
    thompsonPairs F.t z F.t =
      (fun q : ↥(F.M hcount) × ↥(F.M hcount) => ((q.1 : G) * F.t, (q.2 : G))) ''
        oddPairs ↥(F.M hcount) := by
  ext ⟨a, b⟩
  constructor
  · intro hab
    obtain ⟨hmM, hbM, hm2, hb2, hb1, hodd⟩ := data_of_mem_thompsonPairs hR hab
    refine ⟨(⟨a * F.t, hmM⟩, ⟨b, hbM⟩), ⟨Subtype.ext hm2, Subtype.ext hb2,
      fun h => hb1 (congrArg Subtype.val h), ?_⟩, ?_⟩
    · have h := Subgroup.orderOf_coe (⟨a * F.t, hmM⟩ * ⟨b, hbM⟩ : ↥(F.M hcount))
      rw [← h]
      exact hodd
    · refine Prod.ext ?_ rfl
      show a * F.t * F.t = a
      rw [mul_assoc, F.t_mul_t, mul_one]
  · rintro ⟨⟨m, b'⟩, ⟨hm2, hb2, hb1, hodd⟩, h⟩
    have h1 : (m : G) * F.t = a := congrArg Prod.fst h
    have h2 : (b' : G) = b := congrArg Prod.snd h
    subst h1
    subst h2
    refine mem_thompsonPairs_of_data hR m.2 b'.2 (congrArg Subtype.val hm2)
      (congrArg Subtype.val hb2) (fun h => hb1 (Subtype.ext h)) ?_
    have h := Subgroup.orderOf_coe (m * b')
    rw [← h] at hodd
    exact hodd

theorem card_thompsonPairs {F : J2Frame G z} {hcount : involutionClassCount G = 2}
    {R : Subgroup G} (hR : IsKernelComplement F hcount R) :
    Nat.card ↥(thompsonPairs F.t z F.t) = Nat.card ↥(oddPairs ↥(F.M hcount)) := by
  rw [thompsonPairs_eq_image hR]
  refine Nat.card_image_of_injective ?_ _
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
  have h1 : (x1 : G) * F.t = y1 * F.t := congrArg Prod.fst h
  have h2 : (x2 : G) = y2 := congrArg Prod.snd h
  rw [Subtype.ext (mul_right_cancel h1), Subtype.ext h2]

theorem card_oddPairs_of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N) :
    Nat.card ↥(oddPairs M) = Nat.card ↥(oddPairs N) := by
  refine Nat.card_congr ((e.toEquiv.prodCongr e.toEquiv).subtypeEquiv fun q => ?_)
  have h1 : e q.1 * e q.1 = 1 ↔ q.1 * q.1 = 1 := by rw [← map_mul, e.map_eq_one_iff]
  have h2 : e q.2 * e q.2 = 1 ↔ q.2 * q.2 = 1 := by rw [← map_mul, e.map_eq_one_iff]
  have h3 : e q.2 ≠ 1 ↔ q.2 ≠ 1 := not_congr e.map_eq_one_iff
  have h4 : orderOf (e q.1 * e q.2) = orderOf (q.1 * q.2) := by rw [← map_mul, e.orderOf_eq]
  show (q.1 * q.1 = 1 ∧ q.2 * q.2 = 1 ∧ q.2 ≠ 1 ∧ Odd (orderOf (q.1 * q.2))) ↔
    (e q.1 * e q.1 = 1 ∧ e q.2 * e q.2 = 1 ∧ e q.2 ≠ 1 ∧ Odd (orderOf (e q.1 * e q.2)))
  rw [h1, h2, h3, h4]

theorem odd_orderOf_iff_pow_three {H : Type*} [Group H] (hH : Nat.card H = 12) (x : H) :
    Odd (orderOf x) ↔ x ^ 3 = 1 := by
  have hd : orderOf x ∣ 12 := hH ▸ orderOf_dvd_natCard x
  have key : ∀ n : ℕ, n < 13 → n ∣ 12 → (Odd n ↔ n ∣ 3) := by decide
  rw [key _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hd)) hd, orderOf_dvd_iff_pow_eq_one]

theorem card_oddPairs_alt4 : Nat.card ↥(oddPairs (alternatingGroup (Fin 4))) = 3 := by
  have h12 : Nat.card (alternatingGroup (Fin 4)) = 12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  have h : oddPairs (alternatingGroup (Fin 4)) = {q | q.1 * q.1 = 1 ∧ q.2 * q.2 = 1 ∧ q.2 ≠ 1 ∧
      (q.1 * q.2) ^ 3 = 1} := by
    ext q
    simp only [oddPairs, Set.mem_ofPred_eq, odd_orderOf_iff_pow_three h12]
  rw [h, Set.coe_ofPred, Nat.card_eq_fintype_card]
  decide +kernel

end CFSG.Quasithin.SzI47J2T

namespace CFSG.Quasithin

open CFSG.ShultStronglyClosedTI.InvolutionCounting

theorem j2PairCountT_holds : J2PairCountT := by
  intro G _ _ z hcount F R hR he
  obtain ⟨e⟩ := he
  have h12 : Nat.card ↥(F.M hcount) = 12 :=
    (Nat.card_congr e.toEquiv).trans (alternatingGroup.card_of_card_eq_four (by simp))
  refine ⟨?_, ?_⟩
  · show Nat.card ↥(thompsonPairs F.t z F.t) = 3
    rw [SzI47J2T.card_thompsonPairs hR, SzI47J2T.card_oddPairs_of_mulEquiv e,
      SzI47J2T.card_oddPairs_alt4]
  · have h := SzI47J2T.card_X hR
    rw [h12] at h
    exact h.trans (by norm_num)

end CFSG.Quasithin
