module

public import CFSG.Quasithin.Recognition.HSTypeZQ

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem prime_dvd_card_of_free {α : Type*} [DecidableEq α] (S : Finset α) (σ : α → α) {p : ℕ}
    (hp : p.Prime) (hσ : ∀ a ∈ S, σ^[p] a = a) (hS : ∀ a ∈ S, σ a ∈ S)
    (hfree : ∀ a ∈ S, σ a ≠ a) : p ∣ S.card := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let f : Function.End ↥S := fun a => ⟨σ a, hS a a.2⟩
  have hfk : ∀ (k : ℕ) (a : ↥S), ((f ^ k) a : α) = σ^[k] a := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [pow_succ', Function.iterate_succ_apply']
      show σ ((f ^ k) a : α) = _
      rw [ih]
  have hf : f ^ p ^ 1 = 1 := by
    funext a
    apply Subtype.ext
    rw [pow_one, hfk]
    exact hσ a a.2
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨a, ha⟩
    exact hfree a a.2 (congrArg Subtype.val ha)
  rw [hfix, Fintype.card_coe] at h
  exact Nat.modEq_zero_iff_dvd.mp h

abbrev hsK (z : G) : Subgroup G := hsH z ⊓ Subgroup.centralizer (hsZQ z : Set G)

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem ZQ_le_centralizer_of_odd_prime [Finite G] (h : HSSetting z V) {y : G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hyH : y ∈ hsH z) (hy : y ^ p = 1) :
    hsZQ z ≤ Subgroup.centralizer ({y} : Set G) := by
  have hmod := card_modEq_card_inf_centralizer_prime hp hy (h.H_le_normalizer_ZQ hyH)
  rw [h.card_ZQ] at hmod
  set C := hsZQ z ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hzC : Subgroup.zpowers z ≤ C := (Subgroup.zpowers_le).mpr
    ⟨h.z_mem_ZQ, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hyH).symm⟩
  have h2 : 2 ≤ Nat.card C := by
    have := Subgroup.card_le_of_le hzC
    rwa [Nat.card_zpowers, h.orderOf_z] at this
  have hdvd : Nat.card C ∣ 4 := h.card_ZQ ▸ Subgroup.card_dvd_of_le inf_le_left
  have h4 : Nat.card C = 4 := by
    have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card C
    · exfalso
      have h42 : p ∣ 4 - 2 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
      have := Nat.le_of_dvd (by norm_num) h42
      have := hp.two_le
      omega
    · simp at hdvd
    · rfl
  have hCZ : C = hsZQ z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, h.card_ZQ])
  rw [← hCZ]
  exact inf_le_right

theorem mem_K_of_odd_prime [Finite G] (h : HSSetting z V) {y : G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hyH : y ∈ hsH z) (hy : y ^ p = 1) : y ∈ hsK z :=
  ⟨hyH, Subgroup.mem_centralizer_iff.mpr fun _ hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      (h.ZQ_le_centralizer_of_odd_prime hp hp2 hyH hy hx))⟩

theorem Q_le_K (h : HSSetting z V) : hsQ z ≤ hsK z := fun q hq =>
  ⟨h.Q_le_H hq, Subgroup.mem_centralizer_iff.mpr fun _ hx =>
    (Subgroup.mem_centralizer_iff.mp hx.2 q hq).symm⟩

theorem centralizer_Q_eq_ZQ_of_five [Finite G] (h : HSSetting z V) {y : G} (hyH : y ∈ hsH z)
    (hy : orderOf y = 5) : hsQ z ⊓ Subgroup.centralizer ({y} : Set G) = hsZQ z := by
  have hp5 : Nat.Prime 5 := by norm_num
  have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hyQ : y ∈ Subgroup.normalizer (hsQ z : Set G) := le_normalizer_quasithinGenFitting _ hyH
  have hmod := card_modEq_card_inf_centralizer_prime hp5 hy5 hyQ
  rw [h.card_Q] at hmod
  set C := hsQ z ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hZC : hsZQ z ≤ C :=
    le_inf inf_le_left (h.ZQ_le_centralizer_of_odd_prime hp5 (by norm_num) hyH hy5)
  have h4 : 4 ≤ Nat.card C := h.card_ZQ ▸ Subgroup.card_le_of_le hZC
  have hdvd : Nat.card C ∣ 64 := h.card_Q ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne64 : Nat.card C ≠ 64 := by
    intro h64
    have hCQ : C = hsQ z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h64, h.card_Q])
    have hyQ' : y ∈ hsQ z := by
      refine centralizer_quasithinGenFitting_le (hsH z) ⟨hyH, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hCQ ▸ hq : q ∈ C).2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 (hsQ z) := IsPGroup.of_card (n := 6) (by rw [h.card_Q]; norm_num)
    obtain ⟨k, hk⟩ := hQp ⟨y, hyQ'⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have := orderOf_dvd_of_pow_eq_one hyk
    rw [hy] at this
    have h5 := Nat.Prime.dvd_of_dvd_pow hp5 this
    norm_num at h5
  have h4' : Nat.card C = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp
      (show Nat.card C ∣ 2 ^ 6 by simpa using hdvd)
    rw [hk] at h4 hmod hne64 ⊢
    have hk6 : k ≤ 6 := by
      by_contra hk6
      have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ k ≤ 64 := hk ▸ Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases k <;> simp_all [Nat.ModEq]
  exact (Subgroup.eq_of_le_of_card_ge hZC (by rw [h4', h.card_ZQ])).symm

theorem exists_conj_eq_of_mem_V [Finite G] (h : HSSetting z V) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) : ∃ m ∈ hsM V, m * z * m⁻¹ = v := by
  classical
  let : MulAction ↥(hsM V) G :=
    MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp (hsM V).subtype)
  have hsmul : ∀ (m : ↥(hsM V)) (g : G), m • g = (m : G) * g * (m : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer ↥(hsM V) z = (hsH z ⊓ hsM V).subgroupOf (hsM V) := by
    ext m
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hm
      refine ⟨?_, m.2⟩
      calc (m : G) * z = (m : G) * z * (m : G)⁻¹ * (m : G) := by group
        _ = z * (m : G) := by rw [hm]
    · rintro ⟨hm, -⟩
      rw [hm, mul_inv_cancel_right]
  have hcardstab : Nat.card (MulAction.stabilizer ↥(hsM V) z) = 512 * 3 := by
    rw [hstab, ← h.card_H_inf_M]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have horb : MulAction.orbit ↥(hsM V) z ⊆ (V : Set G) \ {1} := by
    rintro _ ⟨m, rfl⟩
    show m • z ∈ (V : Set G) \ {1}
    rw [hsmul]
    refine ⟨(Subgroup.mem_normalizer_iff.mp m.2 z).mp h.mem_V, ?_⟩
    rw [Set.mem_singleton_iff]
    intro h1
    apply h.z_ne_one
    have : z = (m : G)⁻¹ * ((m : G) * z * (m : G)⁻¹) * (m : G) := by group
    rw [this, h1]
    group
  have hV7 : ((V : Set G) \ {1}).ncard = 7 := by
    rw [Set.ncard_sdiff_singleton_of_mem (show (1 : G) ∈ (V : Set G) from V.one_mem),
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.card_V]
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(hsM V) z)
  rw [MulAction.index_stabilizer, hcardstab, h.card_M] at hmul
  have hk : (MulAction.orbit ↥(hsM V) z).ncard = 7 := by omega
  have heq : MulAction.orbit ↥(hsM V) z = (V : Set G) \ {1} :=
    Set.eq_of_subset_of_ncard_le horb (by rw [hk, hV7]) (Set.toFinite _)
  have hvo : v ∈ MulAction.orbit ↥(hsM V) z := heq ▸ ⟨hv, hv1⟩
  obtain ⟨m, hm⟩ := hvo
  exact ⟨m, m.2, (hsmul m z).symm.trans hm⟩

omit [Group G] in
theorem iterate_conj [Group G] (y w : G) (n : ℕ) :
    (fun w => y * w * y⁻¹)^[n] w = y ^ n * w * (y ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    group

theorem K_transitive [Finite G] (h : HSSetting z V) {x x' : G} (hx : x ∈ hsQ z)
    (hx2 : x * x = 1) (hxZ : x ∉ hsZQ z) (hx' : x' ∈ hsQ z) (hx'2 : x' * x' = 1)
    (hx'Z : x' ∉ hsZQ z) : ∃ k ∈ hsK z, k * x * k⁻¹ = x' := by
  classical
  have := Fintype.ofFinite G
  set I := Finset.univ.filter fun w : G => w ∈ hsQ z ∧ w * w = 1 ∧ w ∉ hsZQ z with hI
  have hIcard : I.card = 30 := by
    have h30 := card_noncentral_invol_of_isZ4Q8Q8 (P := ↥(hsQ z)) h.one.fstar
    rw [← h30]
    refine Finset.card_bij (fun w hw => ⟨w, (Finset.mem_filter.mp hw).2.1⟩) ?_ ?_ ?_
    · intro w hw
      obtain ⟨-, hwQ, hw2, hwZ⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hw2, fun hc => hwZ ?_⟩
      rw [← ZQ_subgroupOf_eq_center] at hc
      exact hc
    · intro a _ b _ hab
      exact congrArg Subtype.val hab
    · intro w hw
      obtain ⟨-, hw2, hwZ⟩ := Finset.mem_filter.mp hw
      refine ⟨w.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.2, congrArg Subtype.val hw2,
        fun hc => hwZ ?_⟩, rfl⟩
      rw [← ZQ_subgroupOf_eq_center]
      exact hc
  set O := Finset.univ.filter fun w : G => ∃ k ∈ hsK z, k * x * k⁻¹ = w with hO
  have hKH : hsK z ≤ hsH z := inf_le_left
  have hOI : O ⊆ I := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := (Finset.mem_filter.mp hw).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_quasithinGenFitting _ (hKH hk)) x).mp
        hx
    · calc k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
        _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
    · intro hz
      apply hxZ
      have := (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_ZQ (hKH hk)) x).mpr hz
      exact this
  have hxO : x ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, 1, (hsK z).one_mem, by simp⟩
  have hOmem : ∀ w ∈ O, ∀ g ∈ hsK z, g * w * g⁻¹ ∈ O := by
    intro w hw g hg
    obtain ⟨k, hk, rfl⟩ := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, g * k, (hsK z).mul_mem hg hk, by group⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite ↥(hsH z ⊓ hsM V)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥(hsH z ⊓ hsM V)) 3
    (by rw [← Nat.card_eq_fintype_card, h.card_H_inf_M]; norm_num)
  have hyo : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hy3 : (y : G) ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one _
  have hyK : (y : G) ∈ hsK z := h.mem_K_of_odd_prime Nat.prime_three (by norm_num) y.2.1 hy3
  have hCy := h.centralizer_Q_eq_ZQ_of_three y.2.1 y.2.2 hyo
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := Fintype.ofFinite ↥(hsH z)
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card (G := ↥(hsH z)) 5
    (by rw [← Nat.card_eq_fintype_card, h.card_H]; norm_num)
  have hfo : orderOf (f : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hf
  have hf5 : (f : G) ^ 5 = 1 := by rw [← hfo]; exact pow_orderOf_eq_one _
  have hfK : (f : G) ∈ hsK z := h.mem_K_of_odd_prime (by norm_num) (by norm_num) f.2 hf5
  have hCf := h.centralizer_Q_eq_ZQ_of_five f.2 hfo
  have hfree : ∀ g ∈ hsK z, hsQ z ⊓ Subgroup.centralizer ({g} : Set G) = hsZQ z →
      ∀ w ∈ O, g * w * g⁻¹ ≠ w := by
    intro g _ hC w hw hgw
    have hwI := hOI hw
    obtain ⟨-, hwQ, -, hwZ⟩ := Finset.mem_filter.mp hwI
    apply hwZ
    rw [← hC]
    refine ⟨hwQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc w * g = g * w * g⁻¹ * g := by rw [hgw]
      _ = g * w := by group
  have h3 : 3 ∣ O.card := prime_dvd_card_of_free O (fun w => (y : G) * w * (y : G)⁻¹)
    Nat.prime_three (fun w _ => by rw [iterate_conj, hy3]; group)
    (fun w hw => hOmem w hw _ hyK) (hfree _ hyK hCy)
  have h5 : 5 ∣ O.card := prime_dvd_card_of_free O (fun w => (f : G) * w * (f : G)⁻¹)
    (by norm_num) (fun w _ => by rw [iterate_conj, hf5]; group)
    (fun w hw => hOmem w hw _ hfK) (hfree _ hfK hCf)
  have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
  have h2 : 2 ∣ O.card := by
    refine prime_dvd_card_of_free O (fun w => w * z) Nat.prime_two
      (fun w _ => by simp [mul_assoc, hzz]) (fun w hw => ?_) (fun w _ hwz => ?_)
    · obtain ⟨-, hwQ, -, hwZ⟩ := Finset.mem_filter.mp (hOI hw)
      have hnc : ¬ ∀ q ∈ hsQ z, q * w = w * q := fun hall => hwZ
        ⟨hwQ, Subgroup.mem_centralizer_iff.mpr fun q hq => hall q hq⟩
      push Not at hnc
      obtain ⟨q, hq, hqw⟩ := hnc
      rcases h.mul_comm_or_mul_z hq hwQ with hc | hc
      · exact absurd hc hqw
      · have hqz : q * z = z * q := h.comm_z_of_mem_Q hq
        have : q * w * q⁻¹ = w * z := by
          rw [hc]
          calc w * q * z * q⁻¹ = w * (q * z * q⁻¹) := by group
            _ = w * z := by rw [hqz, mul_inv_cancel_right]
        rw [← this]
        exact hOmem w hw q (h.Q_le_K hq)
    · apply h.z_ne_one
      have := congrArg (w⁻¹ * ·) hwz
      simpa using this
  have h30 : 30 ∣ O.card := by
    have h6 : 6 ∣ O.card := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6 h5
  have hOpos : 0 < O.card := Finset.card_pos.mpr ⟨x, hxO⟩
  have hOle := Finset.card_le_card hOI
  have hOcard : O.card = 30 := by
    obtain ⟨c, hc⟩ := h30
    omega
  have hOeq : O = I := Finset.eq_of_subset_of_card_le hOI (by rw [hOcard, hIcard])
  have hx'O : x' ∈ O := hOeq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx', hx'2, hx'Z⟩
  exact (Finset.mem_filter.mp hx'O).2

theorem exists_mem_V_not_mem_zpowers [Finite G] (h : HSSetting z V) :
    ∃ v ∈ V, v ∉ Subgroup.zpowers z := by
  by_contra hne
  push Not at hne
  have hle : V ≤ Subgroup.zpowers z := fun v hv => hne v hv
  have := Subgroup.card_le_of_le hle
  rw [h.card_V, Nat.card_zpowers, h.orderOf_z] at this
  omega

theorem exists_conj_z_of_invol_Q [Finite G] (h : HSSetting z V) {x : G} (hx : x ∈ hsQ z)
    (hx2 : x * x = 1) (hxZ : x ∉ hsZQ z) : ∃ g : G, g * z * g⁻¹ = x := by
  obtain ⟨v, hvV, hvz⟩ := h.exists_mem_V_not_mem_zpowers
  have hv1 : v ≠ 1 := fun h1 => hvz (h1 ▸ (Subgroup.zpowers z).one_mem)
  have hv2 : v * v = 1 := by
    have := h.elem.2 v hvV
    rwa [sq] at this
  have hvZ : v ∉ hsZQ z := by
    intro hvZ
    apply hvz
    rw [h.eq_z_of_mem_ZQ hvZ hv2 hv1]
    exact Subgroup.mem_zpowers z
  obtain ⟨m, -, hm⟩ := h.exists_conj_eq_of_mem_V hvV hv1
  obtain ⟨k, -, hk⟩ := h.K_transitive (h.two.le hvV) hv2 hvZ hx hx2 hxZ
  exact ⟨k * m, by rw [← hk, ← hm]; group⟩

end HSSetting

end CFSG.Quasithin.HSType
