module

public import CFSG.Quasithin.Background.B1Blocks
public import CFSG.Quasithin.Background.B1Key

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

namespace B1

theorem tv_of_index_two [Finite V] {t : MulAut V} (ht : t ≠ 1)
    (h : Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers t))) :
    ∃ w, IsTransvectionWith t w := by
  obtain ⟨v₀, hv₀⟩ := exists_moved_of_ne_one ht
  have hv₀C : v₀ ∉ fixV (Subgroup.zpowers t) := fun hc => hv₀ (hc t (Subgroup.mem_zpowers t))
  have hpos : 0 < Nat.card (fixV (Subgroup.zpowers t)) := Nat.card_pos
  have hidx : (fixV (Subgroup.zpowers t)).index = 2 := by
    have h1 := card_eq_index_mul (Subgroup.zpowers t)
    have h2 : (fixV (Subgroup.zpowers t)).index ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have : 3 * Nat.card (fixV (Subgroup.zpowers t)) ≤ Nat.card V := by
        rw [h1]
        exact Nat.mul_le_mul_right _ hcon
      omega
    have h3 : (fixV (Subgroup.zpowers t)).index ≠ 1 := by
      intro h1'
      rw [Subgroup.index_eq_one] at h1'
      exact hv₀C (h1' ▸ Subgroup.mem_top v₀)
    have h4 : (fixV (Subgroup.zpowers t)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
  have hcoset : ∀ v : V, v ∉ fixV (Subgroup.zpowers t) →
      v * v₀⁻¹ ∈ fixV (Subgroup.zpowers t) := by
    intro v hv
    have h1 : v * a ∈ fixV (Subgroup.zpowers t) := by
      rcases ha v with h | h
      · exact h.1
      · exact absurd h.1 hv
    have h2 : v₀ * a ∈ fixV (Subgroup.zpowers t) := by
      rcases ha v₀ with h | h
      · exact h.1
      · exact absurd h.1 hv₀C
    have h3 := (fixV (Subgroup.zpowers t)).mul_mem h1 ((fixV (Subgroup.zpowers t)).inv_mem h2)
    have h4 : v * a * (v₀ * a)⁻¹ = v * v₀⁻¹ := by
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    rwa [h4] at h3
  set w : V := t v₀ * v₀⁻¹ with hw
  have hw1 : w ≠ 1 := fun h' => hv₀ (mul_inv_eq_one.1 h')
  refine ⟨w, hw1, fun v => ?_⟩
  by_cases hvC : v ∈ fixV (Subgroup.zpowers t)
  · left
    exact hvC t (Subgroup.mem_zpowers t)
  · right
    have hc := hcoset v hvC
    have htc : t (v * v₀⁻¹) = v * v₀⁻¹ := hc t (Subgroup.mem_zpowers t)
    have h1 : t v = t (v * v₀⁻¹) * t v₀ := by
      rw [← map_mul]
      congr 1
      group
    rw [h1, htc, hw]
    calc v * v₀⁻¹ * t v₀ = v * (v₀⁻¹ * t v₀) := mul_assoc _ _ _
      _ = v * (t v₀ * v₀⁻¹) := by rw [mul_comm v₀⁻¹ (t v₀)]

theorem card_mul_card_fixV_of_isFFStarOffender_ge [Finite V] {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
  have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
  rwa [card_bot_mul_card_fixV] at this

theorem exists_transvection_of_isFFStarMin [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A : Subgroup (MulAut V)} (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hA : IsFFStarMin X A) :
    ∃ t : MulAut V, t ∈ X ∧ IsTransvection t ∧ A = Subgroup.zpowers t := by
  have hcard : Nat.card A = 2 := key_card_two hV hsolv hO2 hA
  obtain ⟨⟨t, htA⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.1.2.1
  have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
  have hord : orderOf t = 2 := by
    have h1 : orderOf (⟨t, htA⟩ : ↥A) ∣ Nat.card A := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hcard] at h1
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ht1
    · exact h
  have hAt : A = Subgroup.zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 htA) ?_).symm
    rw [hcard, Nat.card_zpowers, hord]
  refine ⟨t, hA.1.1 htA, ⟨ht1, ?_⟩, hAt⟩
  have hge := card_mul_card_fixV_of_isFFStarOffender_ge hA.1
  rw [hcard, hAt] at hge
  exact tv_of_index_two ht1 hge

theorem card_mul_card_fixV_of_isFFStarMin [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A : Subgroup (MulAut V)} (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hA : IsFFStarMin X A) : Nat.card A * Nat.card (fixV A) = Nat.card V := by
  have hcard : Nat.card A = 2 := key_card_two hV hsolv hO2 hA
  have hge := card_mul_card_fixV_of_isFFStarOffender_ge hA.1
  have hne : fixV A ≠ ⊤ := fun h => hA.1.2.1 (eq_bot_of_fixV_eq_top h)
  have hidx : 2 ≤ (fixV A).index := by
    have h0 : (fixV A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (fixV A).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    omega
  have h2 := card_eq_index_mul A
  have h3 : 2 * Nat.card (fixV A) ≤ (fixV A).index * Nat.card (fixV A) :=
    Nat.mul_le_mul_right _ hidx
  rw [← h2] at h3
  rw [hcard] at hge ⊢
  omega

theorem card_mul_card_fixV_of_isFFStarOffender [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A : Subgroup (MulAut V)} (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hA : IsFFStarOffender X A) : Nat.card A * Nat.card (fixV A) = Nat.card V := by
  obtain ⟨A₀, hle, hmin⟩ := exists_isFFStarMin_le hA
  rw [← hle.2.2.2]
  exact card_mul_card_fixV_of_isFFStarMin hV hsolv hO2 hmin

theorem not_isStrongFFModule [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥) :
    ¬ IsStrongFFModule X := by
  intro h
  obtain ⟨A, hA, hr⟩ := (isStrongFFModule_iff hV).1 h
  obtain ⟨B, -, hB, hrB⟩ := B1_4_4_lt hV hA hr
  have h1 := (rAV_lt_one_iff hV hB.isA2).1 hrB
  have h2 := card_mul_card_fixV_of_isFFStarOffender hV hsolv hO2 hB
  omega

theorem closure_transvectionsIn_le (X : Subgroup (MulAut V)) :
    Subgroup.closure (transvectionsIn X) ≤ X :=
  (Subgroup.closure_le _).2 fun _ ht => ht.1

theorem closure_transvectionsIn_normal {X : Subgroup (MulAut V)} :
    ∀ b ∈ X, ∀ j ∈ Subgroup.closure (transvectionsIn X),
      b * j * b⁻¹ ∈ Subgroup.closure (transvectionsIn X) := by
  intro b hb j hj
  refine Subgroup.closure_induction
    (p := fun j _ => b * j * b⁻¹ ∈ Subgroup.closure (transvectionsIn X)) ?_ ?_ ?_ ?_ hj
  · rintro t ⟨htX, htr⟩
    exact Subgroup.subset_closure
      ⟨X.mul_mem (X.mul_mem hb htX) (X.inv_mem hb), isTransvection_conj htr b⟩
  · have : b * (1 : MulAut V) * b⁻¹ = 1 := by group
    rw [this]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    have : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem normal_two_subgroups_trivial_of_normal {G : Type*} [Group G] [Finite G]
    {X J : Subgroup G} (hJX : J ≤ X) (hJn : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hO2 : ∀ Q : Subgroup G, Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥) :
    ∀ Q : Subgroup G, Q ≤ J → (Q.subgroupOf J).Normal → IsPGroup 2 Q → Q = ⊥ := by
  intro Q hQJ hQn hQ2
  let K : Subgroup G := (CFSG.pCore 2 ↥J).map J.subtype
  have hKJ : K ≤ J := Subgroup.map_subtype_le _
  have hQK : Q ≤ K := by
    have hp : IsPGroup 2 (Q.subgroupOf J) :=
      hQ2.of_injective (Subgroup.subgroupOfEquivOfLe hQJ).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hQJ).injective
    have h1 : Q.subgroupOf J ≤ CFSG.pCore 2 ↥J := le_sSup ⟨hQn, hp⟩
    intro q hq
    exact ⟨⟨q, hQJ hq⟩, h1 (by simpa [Subgroup.mem_subgroupOf] using hq), rfl⟩
  have hKnorm : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    obtain ⟨k', hk', rfl⟩ := hk
    let φ : ↥J ≃* ↥J :=
      { toFun := fun j => ⟨x * j * x⁻¹, hJn x hx j j.2⟩
        invFun := fun j => ⟨x⁻¹ * j * x, by simpa using hJn x⁻¹ (X.inv_mem hx) j j.2⟩
        left_inv := fun j => Subtype.ext (by simp only; group)
        right_inv := fun j => Subtype.ext (by simp only; group)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hmap := CFSG.pCore_map_iso 2 φ
    have hφ : φ k' ∈ CFSG.pCore 2 ↥J := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hk'
    exact ⟨φ k', hφ, rfl⟩
  have hK2 : IsPGroup 2 K := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).map J.subtype
  have hKX : K ≤ X := hKJ.trans hJX
  have hKn : (K.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKX]
    intro h k hh hk
    exact hKnorm k hk h hh
  have hK0 := hO2 K hKX hKn hK2
  exact le_bot_iff.1 (hK0 ▸ hQK)


theorem isElemAbelian2_zpowers_tv (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} {w : V}
    (ht1 : t ≠ 1) (htw : IsTransvectionWith t w) : IsElemAbelian2 (Subgroup.zpowers t) := by
  have hsq : t * t = 1 := B1.tv_sq hV htw ht1
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.refl t).zpow_zpow m k).eq
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hsq
    simp [this]

theorem isElemAbelian2_of_shape (hV : ∀ v : V, v ^ 2 = 1) {H K : Subgroup (MulAut V)}
    (h : K = ⊥ ∨ ∃ t ∈ transvectionsIn H, K = Subgroup.zpowers t) : IsElemAbelian2 K := by
  rcases h with rfl | ⟨t, ⟨-, ht1, w, htw⟩, rfl⟩
  · refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    · rw [Subgroup.mem_bot] at ha
      rw [ha]
      group
  · exact isElemAbelian2_zpowers_tv hV ht1 htw

theorem card_eq_two_mul_fixV_of_tv [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} {w : V}
    (ht1 : t ≠ 1) (htw : IsTransvectionWith t w) :
    Nat.card V = 2 * Nat.card (fixV (Subgroup.zpowers t)) := by
  let δ : V →* V := MonoidHom.mk' (fun v => t v * v⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hker : δ.ker = fixV (Subgroup.zpowers t) := by
    ext v
    simp only [MonoidHom.mem_ker, δ, MonoidHom.mk'_apply, mul_inv_eq_one]
    constructor
    · intro hv y hy
      exact zpowers_fix hv y hy
    · intro hv
      exact hv t (Subgroup.mem_zpowers t)
  have hrange_le : δ.range ≤ Subgroup.zpowers w := by
    rintro _ ⟨v, rfl⟩
    rcases htw.2 v with h | h
    · have : δ v = 1 := by simp [δ, h]
      rw [this]
      exact Subgroup.one_mem _
    · have : δ v = w := by
        simp only [δ, MonoidHom.mk'_apply, h]
        rw [mul_comm v w, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.mem_zpowers w
  have hcardw : Nat.card (Subgroup.zpowers w) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hV w))
  have hle : Nat.card δ.range ≤ 2 := (Subgroup.card_le_of_le hrange_le).trans hcardw
  obtain ⟨v₀, hv₀⟩ := exists_moved_of_ne_one ht1
  have hne : δ.range ≠ ⊥ := by
    intro hbot
    have : δ v₀ ∈ δ.range := ⟨v₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hv₀ (mul_inv_eq_one.1 this)
  have hge : 1 < Nat.card δ.range := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hcard := Subgroup.card_ker_mul_card_range δ
  rw [hker] at hcard
  have h2 : Nat.card δ.range = 2 := by omega
  rw [h2] at hcard
  omega

theorem iSup₂_induction_finset {G : Type*} [Group G] {ι : Type*} (s : Finset ι)
    (S : ι → Subgroup G) {C : G → Prop} {x : G} (hx : x ∈ ⨆ i ∈ s, S i)
    (mem : ∀ i ∈ s, ∀ y ∈ S i, C y) (one : C 1) (mul : ∀ y z, C y → C z → C (y * z)) : C x := by
  refine Subgroup.iSup_induction (C := C) (fun i => ⨆ (_ : i ∈ s), S i) hx (fun i y hy => ?_) one mul
  exact Subgroup.iSup_induction (C := C) (fun _ : i ∈ s => S i) hy
    (fun hi z hz => mem i hi z hz) one mul

theorem isElemAbelian2_biSup {ι : Type*} (s : Finset ι) (S : ι → Subgroup (MulAut V))
    (hS : ∀ i ∈ s, IsElemAbelian2 (S i))
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x) :
    IsElemAbelian2 (⨆ i ∈ s, S i) := by
  have hcom : ∀ x ∈ ⨆ i ∈ s, S i, ∀ y ∈ ⨆ i ∈ s, S i, x * y = y * x := by
    intro x hx y hy
    refine iSup₂_induction_finset s S (C := fun x => ∀ y ∈ ⨆ i ∈ s, S i, x * y = y * x) hx
      ?_ ?_ ?_ y hy
    · intro i hi x hx y hy
      refine iSup₂_induction_finset s S (C := fun y => x * y = y * x) hy ?_ ?_ ?_
      · intro j hj y hy
        exact hcomm i hi j hj x hx y hy
      · simp
      · intro y z hy hz
        rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
    · intro y _
      simp
    · intro x₁ x₂ h₁ h₂ y hy
      rw [mul_assoc, h₂ y hy, ← mul_assoc, h₁ y hy, mul_assoc]
  refine ⟨hcom, fun x hx => ?_⟩
  have key : x ∈ ⨆ i ∈ s, S i ∧ x ^ 2 = 1 := by
    refine iSup₂_induction_finset s S (C := fun x => x ∈ ⨆ i ∈ s, S i ∧ x ^ 2 = 1) hx ?_ ?_ ?_
    · intro i hi y hy
      exact ⟨le_iSup₂ (f := fun (i : ι) (_ : i ∈ s) => S i) i hi hy, (hS i hi).2 y hy⟩
    · exact ⟨Subgroup.one_mem _, by simp⟩
    · rintro y z ⟨hy, hy2⟩ ⟨hz, hz2⟩
      refine ⟨Subgroup.mul_mem _ hy hz, ?_⟩
      have hyz : Commute y z := hcom y hy z hz
      rw [hyz.mul_pow, hy2, hz2, mul_one]
  exact key.2


end B1

namespace IsTransvectionBlocks

variable {J : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))} {H : Subgroup (MulAut V)}

theorem card_inf_fixV_tv [Finite V] (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) {t : MulAut V}
    (htr : t ∈ transvectionsIn H) :
    Nat.card ↥(commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t)) * 2 =
      Nat.card (commSub (⊤ : Subgroup V) H) := by
  obtain ⟨htH, ht1, w, htw⟩ := htr
  have hW4 : Nat.card (commSub (⊤ : Subgroup V) H) = 4 := hb.card_comm H hH
  have hwW : w ∈ commSub (⊤ : Subgroup V) H := tv_centre_mem_commSub htw ht1 htH
  have htwfix : t w = w := B1.tv_fix htw ht1
  have hwF : w ∈ fixV (Subgroup.zpowers t) := fun y hy => B1.zpowers_fix htwfix y hy
  have htW : ∃ u ∈ commSub (⊤ : Subgroup V) H, t u ≠ u := by
    by_contra hcon
    push Not at hcon
    have h1 : t ∈ H ⊓ centSub (commSub (⊤ : Subgroup V) H) := ⟨htH, fun u hu => hcon u hu⟩
    rw [hb.inf_centSub hH, Subgroup.mem_bot] at h1
    exact ht1 h1
  have hdvd : Nat.card ↥(commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t)) ∣ 4 := by
    rw [← hW4]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne4 : Nat.card ↥(commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t)) ≠ 4 := by
    intro h4
    have heq : commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t) = commSub (⊤ : Subgroup V) H :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hW4])
    obtain ⟨u, hu, hne⟩ := htW
    have hu' : u ∈ commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t) := by rw [heq]; exact hu
    exact hne (hu'.2 t (Subgroup.mem_zpowers t))
  have hne1 : Nat.card ↥(commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t)) ≠ 1 := by
    intro h1
    have hbot := Subgroup.card_eq_one.1 h1
    have : w ∈ commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t) := ⟨hwW, hwF⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact htw.1 this
  have hmem : Nat.card ↥(commSub (⊤ : Subgroup V) H ⊓ fixV (Subgroup.zpowers t)) ∈
      Nat.divisors 4 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have hd : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem peel_block [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (hH : H ∈ 𝓗) {t : MulAut V} (htr : t ∈ transvectionsIn H) {D : Subgroup (MulAut V)}
    (hD : D ≤ centSub (commSub (⊤ : Subgroup V) H)) (hcomm : ∀ d ∈ D, t * d = d * t) :
    Nat.card ↥(Subgroup.zpowers t ⊔ D) * Nat.card ↥(fixV (Subgroup.zpowers t ⊔ D)) =
      Nat.card D * Nat.card ↥(fixV D) := by
  obtain ⟨htH, ht1, w, htw⟩ := htr
  obtain ⟨C, hCinf, hCsup, hC⟩ := hb.exists_compl H hH
  have htD : t ∉ D := by
    intro h
    have h1 : t ∈ H ⊓ centSub (commSub (⊤ : Subgroup V) H) := ⟨htH, hD h⟩
    rw [hb.inf_centSub hH, Subgroup.mem_bot] at h1
    exact ht1 h1
  exact B1.peel (by rw [inf_comm]; exact hCinf) (by rw [sup_comm]; exact hCsup)
    (B1.tv_sq hV htw ht1) (hC t htH) (hb.card_inf_fixV_tv hH ⟨htH, ht1, w, htw⟩) hD hcomm htD

theorem offender_structure [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    {𝓗 : Finset (Subgroup (MulAut V))}
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗) :
    ∀ n : ℕ, ∀ B : Subgroup (MulAut V), IsFFStarOffender X B → Nat.card B ≤ n →
      ∃ a : Subgroup (MulAut V) → Subgroup (MulAut V),
        (∀ H ∈ 𝓗, a H ≤ H ∧
          (a H = ⊥ ∨ ∃ t ∈ transvectionsIn H, a H = Subgroup.zpowers t)) ∧
        B = ⨆ H ∈ 𝓗, a H := by
  classical
  have hnoStrong : ¬ IsStrongFFModule X := B1.not_isStrongFFModule hV hsolv hO2
  intro n
  induction n with
  | zero =>
    intro B hB hBn
    have : 0 < Nat.card B := Nat.card_pos
    omega
  | succ n ih =>
    intro B hB hBn
    obtain ⟨A₀, hA₀le, hA₀min⟩ := B1.exists_isFFStarMin_le hB
    obtain ⟨t, htX, ⟨ht1, w, htw⟩, hA₀t⟩ :=
      B1.exists_transvection_of_isFFStarMin hV hsolv hO2 hA₀min
    have htB : t ∈ B := hA₀le.2.2.1 (hA₀t ▸ Subgroup.mem_zpowers t)
    have htJ : t ∈ Subgroup.closure (transvectionsIn X) :=
      Subgroup.subset_closure ⟨htX, ht1, w, htw⟩
    obtain ⟨H, hH, htH⟩ := hb.cover t ⟨htJ, ht1, w, htw⟩
    have hBabel : IsElemAbelian2 B := hB.2.2.1
    have hBt : ∀ b ∈ B, b * t = t * b := fun b hb' => hBabel.1 b hb' t htB
    have hBJ : ∀ b ∈ B, ∀ j ∈ Subgroup.closure (transvectionsIn X),
        b * j * b⁻¹ ∈ Subgroup.closure (transvectionsIn X) :=
      fun b hb' j hj => B1.closure_transvectionsIn_normal b (hB.1 hb') j hj
    have hinv : ∀ b ∈ B, ∀ u ∈ commSub (⊤ : Subgroup V) H, b u ∈ commSub (⊤ : Subgroup V) H :=
      hb.invariant_of_centralizes hV hH hBJ htw ht1 htH hBt
    have hBst : B ≤ stabSub (commSub (⊤ : Subgroup V) H) := B1.le_stabSub_of_invariant hinv
    have htmov : ∃ u ∈ commSub (⊤ : Subgroup V) H, t u ≠ u := by
      by_contra hcon
      push Not at hcon
      have h1 : t ∈ H ⊓ centSub (commSub (⊤ : Subgroup V) H) := ⟨htH, fun u hu => hcon u hu⟩
      rw [hb.inf_centSub hH, Subgroup.mem_bot] at h1
      exact ht1 h1
    have hmov : ¬ commSub (⊤ : Subgroup V) H ≤ fixV B := by
      intro h
      obtain ⟨u, hu, hne⟩ := htmov
      exact hne (h hu t htB)
    have hautle : Nat.card (autSub B (commSub (⊤ : Subgroup V) H)) ≤ 2 :=
      hb.card_autSub_le_two hV hH hBabel hBst hmov
    have hautne : autSub B (commSub (⊤ : Subgroup V) H) ≠ ⊥ :=
      fun h => hmov ((B1.autSub_eq_bot_iff hBst).1 h)
    have haut2 : Nat.card (autSub B (commSub (⊤ : Subgroup V) H)) = 2 := by
      have : 1 < Nat.card (autSub B (commSub (⊤ : Subgroup V) H)) :=
        (Subgroup.one_lt_card_iff_ne_bot _).2 hautne
      omega
    have hcardB : Nat.card B = 2 * Nat.card ↥(B ⊓ centSub (commSub (⊤ : Subgroup V) H)) := by
      have := card_autSub_mul hBst
      rw [haut2] at this
      exact this.symm
    have htD : t ∉ B ⊓ centSub (commSub (⊤ : Subgroup V) H) := by
      intro h
      obtain ⟨u, hu, hne⟩ := htmov
      exact hne (h.2 u hu)
    have hDcomm : ∀ d ∈ B ⊓ centSub (commSub (⊤ : Subgroup V) H), t * d = d * t :=
      fun d hd => (hBt d hd.1).symm
    have hsq : t * t = 1 := B1.tv_sq hV htw ht1
    have hBeq : Subgroup.zpowers t ⊔ (B ⊓ centSub (commSub (⊤ : Subgroup V) H)) = B := by
      refine Subgroup.eq_of_le_of_card_ge
        (sup_le (Subgroup.zpowers_le.2 htB) inf_le_left) ?_
      rw [B1.card_sup_zpowers hsq hDcomm htD]
      exact hcardB.le
    have hpeel := hb.peel_block hV hH ⟨htH, ht1, w, htw⟩
      (inf_le_right : B ⊓ centSub (commSub (⊤ : Subgroup V) H) ≤ _) hDcomm
    rw [hBeq] at hpeel
    have hBr : Nat.card B * Nat.card (fixV B) = Nat.card V :=
      B1.card_mul_card_fixV_of_isFFStarOffender hV hsolv hO2 hB
    have hDr : Nat.card ↥(B ⊓ centSub (commSub (⊤ : Subgroup V) H)) *
        Nat.card (fixV (B ⊓ centSub (commSub (⊤ : Subgroup V) H))) = Nat.card V := by
      rw [← hpeel]
      exact hBr
    have hshape : ∀ (a' : Subgroup (MulAut V) → Subgroup (MulAut V)),
        (∀ H' ∈ 𝓗, a' H' ≤ H' ∧ (a' H' = ⊥ ∨ ∃ t ∈ transvectionsIn H', a' H' = Subgroup.zpowers t)) →
        ∀ H' ∈ 𝓗, (fun K => if K = H then Subgroup.zpowers t else a' K) H' ≤ H' ∧
          ((fun K => if K = H then Subgroup.zpowers t else a' K) H' = ⊥ ∨
            ∃ t' ∈ transvectionsIn H',
              (fun K => if K = H then Subgroup.zpowers t else a' K) H' = Subgroup.zpowers t') := by
      intro a' ha' H' hH'
      dsimp only
      split_ifs with h
      · rw [h]
        exact ⟨Subgroup.zpowers_le.2 htH, Or.inr ⟨t, ⟨htH, ht1, w, htw⟩, rfl⟩⟩
      · exact ha' H' hH'
    by_cases hDbot : B ⊓ centSub (commSub (⊤ : Subgroup V) H) = ⊥
    · refine ⟨fun K => if K = H then Subgroup.zpowers t else ⊥, ?_, ?_⟩
      · exact hshape (fun _ => ⊥) (fun H' _ => ⟨bot_le, Or.inl rfl⟩)
      · rw [← hBeq, hDbot, sup_bot_eq]
        apply le_antisymm
        · exact le_iSup₂_of_le H hH (by simp)
        · exact iSup₂_le fun H' _ => by dsimp only; split_ifs <;> simp
    · have hD2 : IsA2 X (B ⊓ centSub (commSub (⊤ : Subgroup V) H)) :=
        ⟨inf_le_left.trans hB.1, hDbot,
          ⟨fun a ha b hb' => hBabel.1 a ha.1 b hb'.1, fun a ha => hBabel.2 a ha.1⟩⟩
      have hrD : rAV (B ⊓ centSub (commSub (⊤ : Subgroup V) H)) = 1 :=
        (rAV_eq_one_iff hV hD2).2 hDr.symm
      have hDP : IsFFStarOffender X (B ⊓ centSub (commSub (⊤ : Subgroup V) H)) := by
        have h6 := B1_4_6 hV hnoStrong
        have hmem : (B ⊓ centSub (commSub (⊤ : Subgroup V) H)) ∈
            {A | IsA2 X A ∧ rAV A = 1} := ⟨hD2, hrD⟩
        rw [← h6] at hmem
        exact hmem
      have hDlt : Nat.card ↥(B ⊓ centSub (commSub (⊤ : Subgroup V) H)) ≤ n := by
        have : 0 < Nat.card ↥(B ⊓ centSub (commSub (⊤ : Subgroup V) H)) := Nat.card_pos
        omega
      obtain ⟨a', ha'shape, ha'eq⟩ := ih _ hDP hDlt
      have ha'le : ∀ H' ∈ 𝓗, a' H' ≤ B ⊓ centSub (commSub (⊤ : Subgroup V) H) := by
        intro H' hH'
        rw [ha'eq]
        exact le_iSup₂ (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => a' K) H' hH'
      have ha'H : a' H = ⊥ := by
        have h3 : a' H ≤ H ⊓ centSub (commSub (⊤ : Subgroup V) H) :=
          le_inf (ha'shape H hH).1 ((ha'le H hH).trans inf_le_right)
        rw [hb.inf_centSub hH] at h3
        exact le_bot_iff.1 h3
      refine ⟨fun K => if K = H then Subgroup.zpowers t else a' K, hshape a' ha'shape, ?_⟩
      rw [← hBeq]
      apply le_antisymm
      · refine sup_le (le_iSup₂_of_le H hH (by simp)) ?_
        rw [ha'eq]
        refine iSup₂_le fun H' hH' => le_iSup₂_of_le H' hH' ?_
        dsimp only
        split_ifs with h
        · rw [h, ha'H]
          exact bot_le
        · exact le_rfl
      · refine iSup₂_le fun H' hH' => ?_
        dsimp only
        split_ifs with h
        · exact le_sup_left
        · exact (ha'le H' hH').trans le_sup_right



end IsTransvectionBlocks

namespace IsTransvectionBlocks

variable {J : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))} {H : Subgroup (MulAut V)}

theorem prod_card_mul_card_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) (a : Subgroup (MulAut V) → Subgroup (MulAut V))
    (ha : ∀ H ∈ 𝓗, a H ≤ H ∧ (a H = ⊥ ∨ ∃ t ∈ transvectionsIn H, a H = Subgroup.zpowers t)) :
    ∀ S : Finset (Subgroup (MulAut V)), S ⊆ 𝓗 →
      Nat.card ↥(⨆ H ∈ S, a H) * Nat.card ↥(fixV (⨆ H ∈ S, a H)) = Nat.card V := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have : (⨆ H ∈ (∅ : Finset (Subgroup (MulAut V))), a H) = ⊥ := by simp
    rw [this]
    exact B1.card_bot_mul_card_fixV
  | insert H₀ S' hH₀ ih =>
    intro hS
    have hH₀𝓗 : H₀ ∈ 𝓗 := hS (Finset.mem_insert_self _ _)
    have hS' : S' ⊆ 𝓗 := fun x hx => hS (Finset.mem_insert_of_mem hx)
    have ih' := ih hS'
    rw [Finset.iSup_insert]
    rcases (ha H₀ hH₀𝓗).2 with h0 | ⟨t, htr, h0⟩
    · rw [h0, bot_sup_eq]
      exact ih'
    · rw [h0]
      have hD : (⨆ H ∈ S', a H) ≤ centSub (commSub (⊤ : Subgroup V) H₀) := by
        refine iSup₂_le fun H hH => ?_
        have hne : H ≠ H₀ := fun h => hH₀ (h ▸ hH)
        exact (ha H (hS' hH)).1.trans (hb.le_centSub (hS' hH) hH₀𝓗 hne)
      have hcomm : ∀ d ∈ ⨆ H ∈ S', a H, t * d = d * t := by
        have hle : (⨆ H ∈ S', a H) ≤ Subgroup.centralizer ({t} : Set (MulAut V)) := by
          refine iSup₂_le fun H hH d hd => ?_
          have hne : H₀ ≠ H := fun h => hH₀ (h ▸ hH)
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff] at hg
          rw [hg]
          exact hb.comm H₀ hH₀𝓗 H (hS' hH) hne t htr.1 d ((ha H (hS' hH)).1 hd)
        exact fun d hd => Subgroup.mem_centralizer_iff.1 (hle hd) t (Set.mem_singleton t)
      rw [hb.peel_block hV hH₀𝓗 htr hD hcomm]
      exact ih'



theorem offender_of_product [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    {𝓗 : Finset (Subgroup (MulAut V))}
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    (a : Subgroup (MulAut V) → Subgroup (MulAut V))
    (ha : ∀ H ∈ 𝓗, a H ≤ H ∧ (a H = ⊥ ∨ ∃ t ∈ transvectionsIn H, a H = Subgroup.zpowers t))
    (hne : ∃ H ∈ 𝓗, a H ≠ ⊥) : IsFFStarOffender X (⨆ H ∈ 𝓗, a H) := by
  have hnoStrong := B1.not_isStrongFFModule hV hsolv hO2
  have hA2 : IsA2 X (⨆ H ∈ 𝓗, a H) := by
    refine ⟨iSup₂_le fun H hH =>
      (ha H hH).1.trans ((hb.le_J hH).trans (B1.closure_transvectionsIn_le X)), ?_, ?_⟩
    · obtain ⟨H, hH, hne⟩ := hne
      intro hbot
      exact hne (le_bot_iff.1 (hbot ▸ le_iSup₂ (f := fun (K : Subgroup (MulAut V))
        (_ : K ∈ 𝓗) => a K) H hH))
    · refine B1.isElemAbelian2_biSup 𝓗 a
        (fun H hH => B1.isElemAbelian2_of_shape (H := H) hV (ha H hH).2) ?_
      intro H hH H' hH' x hx y hy
      by_cases h : H = H'
      · subst h
        exact (B1.isElemAbelian2_of_shape (H := H) hV (ha H hH).2).1 x hx y hy
      · exact hb.comm H hH H' hH' h x ((ha H hH).1 hx) y ((ha H' hH').1 hy)
  have hr : rAV (⨆ H ∈ 𝓗, a H) = 1 :=
    (rAV_eq_one_iff hV hA2).2 (hb.prod_card_mul_card_fixV hV a ha 𝓗 le_rfl).symm
  have h6 := B1_4_6 hV hnoStrong
  have hmem : (⨆ H ∈ 𝓗, a H) ∈ {A | IsA2 X A ∧ rAV A = 1} := ⟨hA2, hr⟩
  rw [← h6] at hmem
  exact hmem

end IsTransvectionBlocks

namespace B1

theorem isFFStarOffender_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    {t : MulAut V} (htX : t ∈ X) (htr : IsTransvection t) :
    IsFFStarOffender X (Subgroup.zpowers t) := by
  obtain ⟨ht1, w, htw⟩ := htr
  have hA2 : IsA2 X (Subgroup.zpowers t) :=
    ⟨Subgroup.zpowers_le.2 htX, fun h => ht1 (Subgroup.zpowers_eq_bot.1 h),
      isElemAbelian2_zpowers_tv hV ht1 htw⟩
  have hsq : t ^ 2 = 1 := by rw [pow_two]; exact tv_sq hV htw ht1
  have hord : orderOf t = 2 := orderOf_eq_prime hsq ht1
  have hr : rAV (Subgroup.zpowers t) = 1 := by
    refine (rAV_eq_one_iff hV hA2).2 ?_
    rw [Nat.card_zpowers, hord]
    exact card_eq_two_mul_fixV_of_tv hV ht1 htw
  have h6 := B1_4_6 hV (not_isStrongFFModule hV hsolv hO2)
  have hmem : Subgroup.zpowers t ∈ {A | IsA2 X A ∧ rAV A = 1} := ⟨hA2, hr⟩
  rw [← h6] at hmem
  exact hmem

end B1

namespace IsTransvectionBlocks

variable {J : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))} {H : Subgroup (MulAut V)}

theorem ffJ_eq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    {𝓗 : Finset (Subgroup (MulAut V))}
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗) :
    ffJ X = ⨆ H ∈ 𝓗, H := by
  unfold ffJ
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨a, ha, haeq⟩ := hb.offender_structure hV hsolv hO2 (Nat.card A) A hA le_rfl
    rw [haeq]
    exact iSup₂_le fun H hH =>
      (ha H hH).1.trans (le_iSup₂ (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) H hH)
  · refine iSup₂_le fun H hH => ?_
    rw [← hb.closure_eq H hH]
    refine (Subgroup.closure_le _).2 fun t ht => ?_
    have htX : t ∈ X := B1.closure_transvectionsIn_le X (hb.le_J hH ht.1)
    have hP : IsFFStarOffender X (Subgroup.zpowers t) :=
      B1.isFFStarOffender_zpowers hV hsolv hO2 htX ht.2
    exact le_iSup₂ (f := fun (A : Subgroup (MulAut V)) (_ : IsFFStarOffender X A) => A)
      (Subgroup.zpowers t) hP (Subgroup.mem_zpowers t)

theorem fixV_inf_commSub [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (hH : H ∈ 𝓗) : fixV H ⊓ commSub (⊤ : Subgroup V) H = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  by_contra hu1
  have hex : ∃ w' ∈ commSub (⊤ : Subgroup V) H, w' ≠ 1 ∧ w' ≠ u := by
    by_contra hcon
    push Not at hcon
    have hle : commSub (⊤ : Subgroup V) H ≤ Subgroup.zpowers u := by
      intro w hw
      by_cases hw1 : w = 1
      · rw [hw1]
        exact Subgroup.one_mem _
      · rw [hcon w hw hw1]
        exact Subgroup.mem_zpowers u
    have h1 := Subgroup.card_le_of_le hle
    rw [hb.card_comm H hH, Nat.card_zpowers] at h1
    have h2 : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hV u))
    omega
  obtain ⟨w', hw', hw'1, hw'u⟩ := hex
  obtain ⟨h, hhH, hh⟩ := hb.transitive hV hH hu.2 hw' hu1 hw'1
  exact hw'u (by rw [← hh, hu.1 h hhH])

theorem inf_biSup_ne_eq_bot (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) :
    H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H' = ⊥ := by
  have hle : (⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H') ≤ centSub (commSub (⊤ : Subgroup V) H) :=
    iSup₂_le fun H' hH' => iSup_le fun hne => hb.le_centSub hH' hH hne
  refine le_bot_iff.1 ?_
  calc H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H' ≤ H ⊓ centSub (commSub (⊤ : Subgroup V) H) :=
        inf_le_inf_left _ hle
    _ = ⊥ := hb.inf_centSub hH

theorem commSub_inf_biSup_ne_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) :
    commSub (⊤ : Subgroup V) H ⊓
      ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commSub (⊤ : Subgroup V) H' = ⊥ := by
  have hle : (⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commSub (⊤ : Subgroup V) H') ≤ fixV H :=
    iSup₂_le fun H' hH' => iSup_le fun hne u hu g hg =>
      hb.triv H hH H' hH' (Ne.symm hne) g hg u hu
  refine le_bot_iff.1 ?_
  calc commSub (⊤ : Subgroup V) H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commSub (⊤ : Subgroup V) H'
      ≤ commSub (⊤ : Subgroup V) H ⊓ fixV H := inf_le_inf_left _ hle
    _ = ⊥ := by rw [inf_comm]; exact hb.fixV_inf_commSub hV hH

end IsTransvectionBlocks

namespace B1

theorem commSub_biSup_le {ι : Type*} (s : Finset ι) (S : ι → Subgroup (MulAut V)) (M : Subgroup V)
    (h : ∀ i ∈ s, commSub (⊤ : Subgroup V) (S i) ≤ M) :
    commSub (⊤ : Subgroup V) (⨆ i ∈ s, S i) ≤ M := by
  let K : Subgroup (MulAut V) :=
    { carrier := {g | ∀ v : V, g v * v⁻¹ ∈ M}
      one_mem' := fun v => by simp
      mul_mem' := by
        intro g g' hg hg' v
        have h1 : (g * g') v * v⁻¹ = (g (g' v) * (g' v)⁻¹) * (g' v * v⁻¹) := by
          simp only [MulAut.mul_apply]
          group
        rw [h1]
        exact M.mul_mem (hg (g' v)) (hg' v)
      inv_mem' := by
        intro g hg v
        have h1 : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by
          have : g (g⁻¹ v) = v := by simp
          rw [this]
          group
        rw [h1]
        exact M.inv_mem (hg (g⁻¹ v)) }
  have hSK : ∀ i ∈ s, S i ≤ K := by
    intro i hi g hg v
    exact h i hi (Subgroup.subset_closure ⟨g, hg, v, Subgroup.mem_top v, rfl⟩)
  have hle : (⨆ i ∈ s, S i) ≤ K := iSup₂_le hSK
  refine (Subgroup.closure_le M).2 ?_
  rintro _ ⟨g, hg, v, -, rfl⟩
  exact hle hg v

end B1

end CFSG.Quasithin
