
module

public import CFSG.Quasithin.Vol2.KGFactC31Red
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Quasithin.Background.C31Insp

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native

@[expose] def NoOddAct (X : Type) [Group X] : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ y : X, (∃ k : ℕ, y ^ p ^ k = 1) → ∀ W : Subgroup X,
    IsElemAbelian 2 W → y ∈ Subgroup.normalizer (W : Set X) → ∀ t ∈ W, y * t * y⁻¹ = t

theorem noOddAct_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : NoOddAct Y) :
    NoOddAct X := by
  intro p hp hp5 y ⟨k, hk⟩ W hW hyW t ht
  apply e.injective
  have hW' : IsElemAbelian 2 (W.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := a
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul]
      congr 1
      have := hW.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      simpa using congrArg Subtype.val this
    · rintro _ ⟨a, ha, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hW.2 a ha, map_one]
  have hyW' : e y ∈ Subgroup.normalizer ((W.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff] at hyW ⊢
    intro z
    obtain ⟨z, rfl⟩ := e.surjective z
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨a, ha, hae⟩
      rw [e.injective hae] at ha
      exact ⟨y * z * y⁻¹, (hyW z).mp ha, by simp⟩
    · rintro ⟨a, ha, hae⟩
      refine ⟨z, ?_, rfl⟩
      have : a = y * z * y⁻¹ := e.injective (by rw [hae]; simp)
      rw [this] at ha
      exact (hyW z).mpr ha
  have := h p hp hp5 (e y) ⟨k, by rw [← map_pow, hk, map_one]⟩ _ hW' hyW' (e t)
    ⟨t, ht, rfl⟩
  simpa using this

theorem false_of_noOddAct {A : Type} [Group A] [Finite A] {S M₀ V : Subgroup A}
    (hS : NoOddAct ↥S) (hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀) (hVM₀ : V ≤ M₀)
    (hVne : V ≠ ⊥) (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V) : False := by
  have hN := le_normalizer_of_comm hcomm
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm hper hN (by rwa [hcomm])
  have hyS := hM₀S hy
  have htS := hM₀S (hVM₀ ht)
  set W : Subgroup S := V.subgroupOf S with hWdef
  have hW : IsElemAbelian 2 W := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have := hV.1.is_comm.comm ⟨(a : S), a.2⟩ ⟨(b : S), b.2⟩
      simpa using congrArg Subtype.val this
    · apply Subtype.ext
      simpa using hV.2 _ hx
  have hyW : (⟨y, hyS⟩ : S) ∈ Subgroup.normalizer (W : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [hWdef, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN hy) z)
  have := hS p hp hp5 ⟨y, hyS⟩ ⟨k, Subtype.ext (by simpa using hk)⟩ W hW hyW ⟨t, htS⟩
    (by rw [hWdef, Subgroup.mem_subgroupOf]; exact ht)
  exact hyt (by simpa using congrArg Subtype.val this)

theorem inspC31SporadicAt_of_noOddAct {s : TauCeti.SporadicName}
    (h : NoOddAct (CFSG.Blueprint.NativeSporadic.Carrier s)) :
    CFSG.Quasithin.InspC31SporadicAt s := by
  intro A _ _ S M₀ R M V _ hSs _ hM₀S hper _ _ _ _ _ _ _ hVM₀ hVne hV hcomm
  obtain ⟨e⟩ := hSs
  exact (false_of_noOddAct (noOddAct_of_mulEquiv e h) hM₀S hper hVM₀ hVne hV hcomm).elim

theorem wordG_mem_of {G : Type*} [Group G] (K : Subgroup G) {gens : ℤ → G}
    (h : ∀ l, gens l ∈ K) (w : List ℤ) : wordG gens w ∈ K := by
  unfold wordG
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    exact K.mul_mem (h l) ih

theorem eq_one_of_pow_of_not_dvd {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hcop : ¬ p ∣ Nat.card X) {y : X} (hy : ∃ k : ℕ, y ^ p ^ k = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk)
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero j)).trans (hj ▸ orderOf_dvd_natCard y)) hcop

theorem comm_of_qElement {X : Type*} [Group X] [Finite X] {V : Subgroup X} (hV8 : Nat.card V ∣ 8)
    {q : ℕ} [hq : Fact q.Prime] (hq5 : 5 ≤ q) (hq7 : q ≠ 7) {y : X} (hy : ∃ k : ℕ, y ^ q ^ k = 1)
    (hyV : y ∈ Subgroup.normalizer (V : Set X)) : ∀ v ∈ V, y * v * y⁻¹ = v := by
  have hY : IsPGroup q (Subgroup.zpowers y) := by
    obtain ⟨k, hk⟩ := hy
    intro ⟨z, hz⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, Subtype.ext ?_⟩
    show (y ^ i) ^ q ^ k = 1
    rw [← zpow_natCast (y ^ i), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hYN : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set X) := Subgroup.zpowers_le.mpr hyV
  have hconj : ∀ g : Subgroup.zpowers y, ∀ v : V, (g : X) * v * (g : X)⁻¹ ∈ V := fun g v =>
    (Subgroup.mem_normalizer_iff.mp (hYN g.2) v).mp v.2
  let act : MulAction (Subgroup.zpowers y) V :=
    { smul := fun g v => ⟨(g : X) * v * (g : X)⁻¹, hconj g v⟩
      one_smul := fun v => Subtype.ext (by show (1 : X) * v * 1⁻¹ = v; group)
      mul_smul := fun g h v => Subtype.ext (by
        show ((g * h : Subgroup.zpowers y) : X) * v * ((g * h : Subgroup.zpowers y) : X)⁻¹ =
          (g : X) * ((h : X) * v * (h : X)⁻¹) * (g : X)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hmod := hY.card_modEq_card_fixedPoints V
  let F : Subgroup V :=
    { carrier := {v | y * (v : X) * y⁻¹ = v}
      mul_mem' := fun {a b} ha hb => by
        show y * ((a : X) * b) * y⁻¹ = a * b
        calc y * ((a : X) * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
          _ = a * b := by
            rw [show y * (a : X) * y⁻¹ = a from ha, show y * (b : X) * y⁻¹ = b from hb]
      one_mem' := by show y * (1 : X) * y⁻¹ = 1; group
      inv_mem' := fun {a} ha => by
        show y * ((a : X)⁻¹) * y⁻¹ = (a : X)⁻¹
        have ha' : y * (a : X) * y⁻¹ = a := ha
        calc y * ((a : X)⁻¹) * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
          _ = (a : X)⁻¹ := by rw [ha'] }
  have hFfix : ∀ v : V, v ∈ MulAction.fixedPoints (Subgroup.zpowers y) V ↔ v ∈ F := by
    intro v
    constructor
    · intro h
      have := congrArg Subtype.val (h ⟨y, Subgroup.mem_zpowers y⟩)
      exact this
    · intro h g
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
      apply Subtype.ext
      show (g : X) * v * (g : X)⁻¹ = v
      rw [← hi]
      have hv : y * (v : X) * y⁻¹ = v := h
      have hc : Commute y (v : X) := by
        show y * v = v * y
        calc y * (v : X) = y * v * y⁻¹ * y := by group
          _ = v * y := by rw [hv]
      rw [(hc.zpow_left i).eq]
      group
  have hcardF : Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) V) = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight hFfix)
  rw [hcardF] at hmod
  have hFdvd : Nat.card F ∣ Nat.card V := F.card_subgroup_dvd_card
  have hFle : Nat.card F ≤ Nat.card V := Nat.le_of_dvd Nat.card_pos hFdvd
  have hdvd : q ∣ Nat.card V - Nat.card F := (Nat.modEq_iff_dvd' hFle).mp hmod.symm
  have hV : Nat.card V ∈ ({1, 2, 4, 8} : Finset ℕ) := by
    have := Nat.mem_divisors.mpr ⟨hV8, by norm_num⟩
    exact this
  have hFV : Nat.card F = Nat.card V := by
    have hFpos : 0 < Nat.card F := Nat.card_pos
    by_contra hne
    have hlt : Nat.card F < Nat.card V := lt_of_le_of_ne hFle hne
    have hd : Nat.card V - Nat.card F ≤ 7 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hV
      omega
    have hqd := Nat.le_of_dvd (by omega) hdvd
    have hq57 : q = 5 ∨ q = 6 ∨ q = 7 := by omega
    rcases hq57 with rfl | rfl | rfl
    ·
      simp only [Finset.mem_insert, Finset.mem_singleton] at hV
      rcases hV with h | h | h | h <;> rw [h] at hFdvd hdvd hlt <;>
        (have := Nat.le_of_dvd (by norm_num) hFdvd; interval_cases (Nat.card F) <;> simp_all)
    · exact absurd hq.out (by decide)
    · exact hq7 rfl
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F hFV
  intro v hv
  have : (⟨v, hv⟩ : V) ∈ F := htop ▸ Subgroup.mem_top _
  exact this

theorem false_of_twoSubgroups {A : Type} [Group A] [Finite A] {S M₀ V : Subgroup A}
    (hS2 : ∀ P : Subgroup A, P ≤ S → IsPGroup 2 P → IsMulCommutative P ∧ Nat.card P ∣ 8)
    (hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀) (hVM₀ : V ≤ M₀) (hVne : V ≠ ⊥)
    (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V) : False := by
  have hN := le_normalizer_of_comm hcomm
  obtain ⟨q, hq, hq3, hq7, y, hy, ⟨k, hk⟩, t, ht, hyt⟩ :=
    exists_qElement_not_comm Nat.prime_three (by norm_num : Nat.Prime 7) (by norm_num) hper hN
      (by rwa [hcomm])
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hV8 : Nat.card V ∣ 8 := (hS2 V (hVM₀.trans hM₀S) hV2).2
  have : Fact q.Prime := ⟨hq⟩
  by_cases hq2 : q = 2
  · subst hq2
    have hY : IsPGroup 2 (Subgroup.zpowers y) := by
      intro ⟨z, hz⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine ⟨k, Subtype.ext ?_⟩
      show (y ^ i) ^ 2 ^ k = 1
      rw [← zpow_natCast (y ^ i), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    have hP : IsPGroup 2 (Subgroup.zpowers y ⊔ V : Subgroup A) :=
      hY.to_sup_of_normal_right' hV2 (Subgroup.zpowers_le.mpr (hN hy))
    have hab := (hS2 _ (sup_le (Subgroup.zpowers_le.mpr (hM₀S hy)) (hVM₀.trans hM₀S)) hP).1
    have hc := hab.is_comm.comm ⟨y, le_sup_left (a := Subgroup.zpowers y)
      (Subgroup.mem_zpowers y)⟩ ⟨t, le_sup_right (b := V) ht⟩
    apply hyt
    have h1 : y * t = t * y := by simpa using congrArg Subtype.val hc
    rw [h1]
    group
  · have hq5 : 5 ≤ q := by
      have := hq.two_le
      by_contra h5
      interval_cases q
      · exact hq2 rfl
      · exact hq3 rfl
      · exact absurd hq (by decide)
    exact hyt (comm_of_qElement hV8 hq5 hq7 ⟨k, hk⟩ (hN hy) t ht)

variable {n : ℕ}

theorem badAct_eq_true (hn : n < 2 ^ 32) {x xi t : Table} {g h : Equiv.Perm (Fin n)}
    (hx : Rep n x g) (hxi : Rep n xi g⁻¹) (ht : Rep n t h) (m : ℕ) (hmove : g * h * g⁻¹ ≠ h)
    (hcomm : ∀ j < m, h * (g ^ j * h * g⁻¹ ^ j) = g ^ j * h * g⁻¹ ^ j * h) :
    badAct n m x xi t = true := by
  have hc : Rep n (conjTab n x xi t) (g * h * g⁻¹) := Rep.compT (Rep.compT hx ht) hxi
  unfold badAct
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [Bool.not_eq_true']
    by_contra h1
    rw [Bool.not_eq_false] at h1
    exact hmove (rep_unique (rep_of_tblEq ht h1) hc).symm
  · rw [List.mem_range] at hj
    have hcj : Rep n (conjTab n (powT n j x) (powT n j xi) t) (g ^ j * h * g⁻¹ ^ j) :=
      Rep.compT (Rep.compT (Rep.powT hn hx j) ht) (Rep.powT hn hxi j)
    have h1 := Rep.compT ht hcj
    have h2 := Rep.compT hcj ht
    rw [hcomm j hj] at h1
    rw [tblEq_iff]
    intro i hi
    rw [h1 i hi, h2 i hi]

theorem false_of_actCheck (hn : n < 2 ^ 32) {m : ℕ} {invs els : List Table}
    (h : actCheck n m invs els = true) {t e : Table} (ht : t ∈ invs) (he : e ∈ els)
    {g k : Equiv.Perm (Fin n)} (hg : Rep n e g) (hk : Rep n t k) (hmove : g * k * g⁻¹ ≠ k)
    (hcomm : ∀ j < m, k * (g ^ j * k * g⁻¹ ^ j) = g ^ j * k * g⁻¹ ^ j * k) : False := by
  unfold actCheck at h
  rw [List.all_eq_true] at h
  have h1 := h e he
  rw [Bool.and_eq_true, List.all_eq_true] at h1
  have hi : Rep n (invT n e) g⁻¹ := Rep.inv_of_invOK hg h1.1
  have h2 := h1.2 t ht
  rw [badAct_eq_true hn hg hi hk m hmove hcomm] at h2
  exact absurd h2 (by decide)

theorem exists_conj_mem_of_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsPGroup p P) (hPi : ¬ p ∣ P.index) {y : X}
    (hy : ∃ k : ℕ, y ^ p ^ k = 1) : ∃ g : X, g⁻¹ * y * g ∈ P := by
  have hQ : IsPGroup p (Subgroup.zpowers y) := by
    obtain ⟨k, hk⟩ := hy
    intro ⟨z, hz⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, Subtype.ext ?_⟩
    show (y ^ i) ^ p ^ k = 1
    rw [← zpow_natCast (y ^ i), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨Q, hQle⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q (hP.toSylow hPi)
  refine ⟨g⁻¹, ?_⟩
  have hyQ : y ∈ (Q : Subgroup X) := hQle (Subgroup.mem_zpowers y)
  have h1 : MulAut.conj g • y ∈ ((g • Q : Sylow p X) : Subgroup X) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hyQ
  rw [hg] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply] using h1

theorem pow_mod_of_pow_eq_one {X : Type*} [Monoid X] {x : X} {p : ℕ} (hx : x ^ p = 1) (n : ℕ) :
    x ^ (n % p) = x ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hx, one_pow, one_mul]

@[expose] def gridSubgroup {X : Type*} [Group X] {x y : X} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : Commute x y) : Subgroup X where
  carrier := {z | ∃ a < p, ∃ b < p, z = x ^ a * y ^ b}
  mul_mem' := by
    rintro _ _ ⟨a, -, b, -, rfl⟩ ⟨c, -, d, -, rfl⟩
    refine ⟨(a + c) % p, Nat.mod_lt _ hp, (b + d) % p, Nat.mod_lt _ hp, ?_⟩
    rw [pow_mod_of_pow_eq_one hx, pow_mod_of_pow_eq_one hy, pow_add, pow_add]
    calc x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ a * (y ^ b * x ^ c) * y ^ d := by group
      _ = x ^ a * (x ^ c * y ^ b) * y ^ d := by rw [(hxy.pow_pow c b).eq]
      _ = x ^ a * x ^ c * (y ^ b * y ^ d) := by group
  one_mem' := ⟨0, hp, 0, hp, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨(p - a) % p, Nat.mod_lt _ hp, (p - b) % p, Nat.mod_lt _ hp, ?_⟩
    rw [pow_mod_of_pow_eq_one hx, pow_mod_of_pow_eq_one hy]
    have h1 : (x ^ a)⁻¹ = x ^ (p - a) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' ha.le, hx]
    have h2 : (y ^ b)⁻¹ = y ^ (p - b) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hb.le, hy]
    rw [mul_inv_rev, h1, h2, (hxy.pow_pow (p - a) (p - b)).eq]

theorem mem_gridSubgroup {X : Type*} [Group X] {x y : X} {p : ℕ} {hp : 0 < p} {hx : x ^ p = 1}
    {hy : y ^ p = 1} {hxy : Commute x y} {z : X} :
    z ∈ gridSubgroup hp hx hy hxy ↔ ∃ a < p, ∃ b < p, z = x ^ a * y ^ b :=
  Iff.rfl

theorem card_gridSubgroup {X : Type*} [Group X] {x y : X} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hxy : Commute x y)
    (hinj : ∀ a < p, ∀ b < p, ∀ c < p, ∀ d < p, x ^ a * y ^ b = x ^ c * y ^ d → a = c ∧ b = d) :
    Nat.card (gridSubgroup hp hx hy hxy) = p ^ 2 := by
  let f : Fin p × Fin p → gridSubgroup hp hx hy hxy := fun ab =>
    ⟨x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ), ab.1, ab.1.2, ab.2, ab.2.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun ab cd h => ?_, fun z => ?_⟩
    · have h' := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := hinj _ ab.1.2 _ ab.2.2 _ cd.1.2 _ cd.2.2 h'
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · obtain ⟨a, ha, b, hb, hz⟩ := z.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hz.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin, sq]

theorem exists_mem_of_forall₂ {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | cons hr _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, hab⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem exists_orderTables (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {t : Equiv.Perm (Fin n)} (ht : t ∈ Q.originalSubgroup) (h2 : orderOf t = 2) :
    ∃ T ∈ orderTables Q 2, Rep n T t := by
  apply exists_mem_of_forall₂ (forall₂_orderTables hn Q (by norm_num))
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_iff]
  exact ⟨(mem_enumeration_iff Q hQ t).2 ht, h2⟩

theorem exists_powTabs (hn : n < 2 ^ 32) {H : Subgroup (Equiv.Perm (Fin n))} {T : Table}
    {x : H} (hT : Rep n T (x : Equiv.Perm (Fin n))) {z : H} (hz : z ∈ Subgroup.zpowers x) :
    ∃ e ∈ powTabs n T (orderOf x), Rep n e (z : Equiv.Perm (Fin n)) := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  refine ⟨powT n a T, ?_, ?_⟩
  · exact List.mem_map.2 ⟨a, List.mem_range.2 (Finset.mem_range.1 ha), rfl⟩
  · rw [Subgroup.coe_pow]
    exact Rep.powT hn hT a

theorem forall_act_of_sylow (hn : n < 2 ^ 32) {H : Subgroup (Equiv.Perm (Fin n))} {p m : ℕ}
    [Fact p.Prime] {P : Subgroup H} (hP : IsPGroup p P) (hPi : ¬ p ∣ P.index)
    {invs els : List Table} (hels : ∀ x ∈ P, ∃ e ∈ els, Rep n e (x : Equiv.Perm (Fin n)))
    (hinvs : ∀ t : H, orderOf t = 2 → ∃ T ∈ invs, Rep n T (t : Equiv.Perm (Fin n)))
    (hchk : actCheck n m invs els = true) {y : H} (hy : ∃ k : ℕ, y ^ p ^ k = 1)
    {W : Subgroup H} (hW : IsElemAbelian 2 W) (hyW : y ∈ Subgroup.normalizer (W : Set H))
    {t : H} (ht : t ∈ W) : y * t * y⁻¹ = t := by
  by_contra hne
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi hy
  have ht1 : t ≠ 1 := fun h => hne (by rw [h]; group)
  have ht2 : t ^ 2 = 1 := hW.2 t ht
  have hord : orderOf (g⁻¹ * t * g) = 2 := by
    apply orderOf_eq_prime
    · rw [show (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g by rw [sq, sq]; group, ht2]
      group
    · intro h
      apply ht1
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
  obtain ⟨T, hT, hTrep⟩ := hinvs _ hord
  obtain ⟨e, he, herep⟩ := hels _ hg
  have hconj : ∀ j : ℕ, (g⁻¹ * y * g) ^ j * (g⁻¹ * t * g) * (g⁻¹ * y * g)⁻¹ ^ j =
      g⁻¹ * (y ^ j * t * y⁻¹ ^ j) * g := by
    intro j
    have h1 : (g⁻¹ * y * g) ^ j = g⁻¹ * y ^ j * g := by
      simpa using (conj_pow (a := g⁻¹) (b := y) (i := j))
    have h2 : (g⁻¹ * y * g)⁻¹ ^ j = g⁻¹ * y⁻¹ ^ j * g := by
      rw [show (g⁻¹ * y * g)⁻¹ = g⁻¹ * y⁻¹ * g by group]
      simpa using (conj_pow (a := g⁻¹) (b := y⁻¹) (i := j))
    rw [h1, h2]
    group
  refine false_of_actCheck hn hchk hT he herep hTrep ?_ ?_
  · intro h
    apply hne
    have h1 : (g⁻¹ * y * g) * (g⁻¹ * t * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * t * g := by
      apply Subtype.ext
      simpa using h
    calc y * t * y⁻¹ = g * ((g⁻¹ * y * g) * (g⁻¹ * t * g) * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
      _ = t := by rw [h1]; group
  · intro j _
    have hc : y ^ j * t * y⁻¹ ^ j ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyW j) t).mp ht
      rwa [← inv_pow] at this
    have hcomm := hW.1.is_comm.comm ⟨t, ht⟩ ⟨_, hc⟩
    have hcomm' : t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := by
      simpa using congrArg Subtype.val hcomm
    have h1 : (g⁻¹ * t * g) * ((g⁻¹ * y * g) ^ j * (g⁻¹ * t * g) * (g⁻¹ * y * g)⁻¹ ^ j) =
        ((g⁻¹ * y * g) ^ j * (g⁻¹ * t * g) * (g⁻¹ * y * g)⁻¹ ^ j) * (g⁻¹ * t * g) := by
      rw [hconj j]
      calc g⁻¹ * t * g * (g⁻¹ * (y ^ j * t * y⁻¹ ^ j) * g) =
            g⁻¹ * (t * (y ^ j * t * y⁻¹ ^ j)) * g := by group
        _ = g⁻¹ * (y ^ j * t * y⁻¹ ^ j * t) * g := by rw [hcomm']
        _ = g⁻¹ * (y ^ j * t * y⁻¹ ^ j) * g * (g⁻¹ * t * g) := by group
    have := congrArg Subtype.val h1
    simpa [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] using this

end CFSG.Quasithin.KGC31

end
