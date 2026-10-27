module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

def KleinNorm {A : Type*} [Group A] (s : A) : Prop :=
  ∃ a b : A, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 ∧
    a * b = b * a ∧ s * a * s⁻¹ = b ∧ s * b * s⁻¹ = a * b

theorem kleinNorm_map {A : Type*} [Group A] (φ : A ≃* A) {s : A} (h : KleinNorm s) :
    KleinNorm (φ s) := by
  obtain ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨φ a, φ b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · exact fun e => h3 (φ.injective e)
  · exact fun e => h4 (φ.injective (e.trans (map_one φ).symm))
  · exact fun e => h5 (φ.injective (e.trans (map_one φ).symm))
  · rw [← map_mul, ← map_mul, h6]
  · rw [← map_inv, ← map_mul, ← map_mul, h7]
  · rw [← map_inv, ← map_mul, ← map_mul, h8, map_mul]

theorem cycleType_three_of_support {σ : Equiv.Perm (Fin 6)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) {k : ℕ}
    (hsupp : σ.support.card = 3 * (k + 1)) : σ.cycleType = Multiset.replicate (k + 1) 3 := by
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_three)
  rw [hord] at hm
  have h := Equiv.Perm.sum_cycleType σ
  rw [hm, Multiset.sum_replicate, smul_eq_mul, hsupp] at h
  rw [hm, show m = k by omega]

def c1A : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

def c2A : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * (Equiv.swap 3 4 * Equiv.swap 4 5),
    Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

theorem kleinNorm_c1A : KleinNorm c1A :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 0 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem kleinNorm_c2A : KleinNorm c2A :=
  ⟨⟨Equiv.swap 0 3 * Equiv.swap 1 4, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨Equiv.swap 1 4 * Equiv.swap 2 5, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem a6_three_klein :
    ∀ s : alternatingGroup (Fin 6), s ^ 3 = 1 → s ≠ 1 →
      ∃ a b : alternatingGroup (Fin 6), a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 ∧
        a * b = b * a ∧ s * a * s⁻¹ = b ∧ s * b * s⁻¹ = a * b := by
  intro s h3 h1
  have hs3 : (s : Equiv.Perm (Fin 6)) ^ 3 = 1 := by rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  have hs1 : (s : Equiv.Perm (Fin 6)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hord : orderOf (s : Equiv.Perm (Fin 6)) = 3 := orderOf_eq_prime hs3 hs1
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_three)
  rw [hord] at hk
  have hle : 3 * (k + 1) ≤ 6 := by
    have h := Equiv.Perm.sum_cycleType_le (s : Equiv.Perm (Fin 6))
    rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h
    omega
  have hc : ∃ c : alternatingGroup (Fin 6),
      (c : Equiv.Perm (Fin 6)).cycleType = Multiset.replicate (k + 1) 3 ∧ KleinNorm c := by
    rcases k with _ | _ | k
    · exact ⟨c1A, cycleType_three_of_support (by decide) (by decide) (by decide), kleinNorm_c1A⟩
    · exact ⟨c2A, cycleType_three_of_support (by decide) (by decide) (by decide), kleinNorm_c2A⟩
    · omega
  obtain ⟨c, hct, hK⟩ := hc
  obtain ⟨g, hg⟩ := isConj_iff.1 ((Equiv.Perm.isConj_iff_cycleType_eq).2 (hct.trans hk.symm))
  have hs : s = MulAut.conjNormal g c := Subtype.ext (by rw [MulAut.conjNormal_apply, hg])
  rw [hs]
  exact kleinNorm_map (MulAut.conjNormal g) hK

theorem involutions_comm_of_commutator_central {Q : Type} [Group Q] [Finite Q]
    (hZ : Nat.card (Subgroup.center Q) = 3) {g h : Q}
    (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hcen : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center Q) : g * h = h * g := by
  have hg' : g * g = 1 := by rw [← pow_two]; exact hg
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg'
  set c := g * h * g⁻¹ * h⁻¹ with hcdef
  have hcomm : ∀ x : Q, x * c = c * x := fun x => Subgroup.mem_center_iff.mp hcen x
  have h3 : c ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center Q) (x := ⟨c, hcen⟩)
    rw [hZ] at h
    simpa using congrArg Subtype.val h
  have hrel : g * h * g = c * h := by
    rw [hcdef, hginv]
    group
  have hL : g * (g * h * g) * g = h := by
    calc g * (g * h * g) * g = (g * g) * h * (g * g) := by group
      _ = h := by rw [hg']; simp
  have hR : g * (g * h * g) * g = c * c * h := by
    calc g * (g * h * g) * g = g * (c * h) * g := by rw [hrel]
      _ = (g * c) * h * g := by group
      _ = (c * g) * h * g := by rw [hcomm g]
      _ = c * (g * h * g) := by group
      _ = c * (c * h) := by rw [hrel]
      _ = c * c * h := by group
  have h2 : c ^ 2 = 1 := by
    rw [pow_two]
    apply mul_right_cancel (b := h)
    rw [one_mul]
    exact (hL.symm.trans hR).symm
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  calc g * h = g * h * g⁻¹ * h⁻¹ * (h * g) := by group
    _ = h * g := by rw [← hcdef, hc1, one_mul]

noncomputable def toA6 {Q : Type} [Group Q]
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) : Q →* alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))

theorem toA6_surjective {Q : Type} [Group Q]
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) :
    Function.Surjective (toA6 e) := by
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) (e.symm a)
  exact ⟨x, by simp only [toA6, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx,
    MulEquiv.apply_symm_apply]⟩

theorem toA6_eq_one_iff {Q : Type} [Group Q]
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) (x : Q) :
    toA6 e x = 1 ↔ x ∈ Subgroup.center Q := by
  simp only [toA6, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem pow_three_of_mem_center {Q : Type} [Group Q] [Finite Q]
    (hZ : Nat.card (Subgroup.center Q) = 3) {x : Q} (hx : x ∈ Subgroup.center Q) :
    x ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Subgroup.center Q) (x := ⟨x, hx⟩)
  rw [hZ] at h
  simpa using congrArg Subtype.val h

theorem exists_lift_involution {Q : Type} [Group Q] [Finite Q]
    (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6))
    {a : alternatingGroup (Fin 6)} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃ y : Q, y ^ 2 = 1 ∧ y ≠ 1 ∧ toA6 e y = a := by
  obtain ⟨x, hx⟩ := toA6_surjective e a
  have hx2 : x ^ 2 ∈ Subgroup.center Q := by
    rw [← toA6_eq_one_iff, map_pow, hx, ha]
  have h6 : (x ^ 2) ^ 3 = 1 := pow_three_of_mem_center hZ hx2
  have hsq : (x ^ 3) ^ 2 = 1 := by
    rw [← h6, ← pow_mul, ← pow_mul, mul_comm]
  have ha3 : a ^ 3 = a := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, ha, one_mul]
  have hy : toA6 e (x ^ 3) = a := by
    rw [map_pow, hx, ha3]
  refine ⟨x ^ 3, hsq, ?_, hy⟩
  intro h1
  apply ha1
  rw [← hy, h1, map_one]

def KleinZ {G : Type*} [Group G] (a b u : G) : Prop :=
  ∃ m n : ℤ, u = a ^ m * b ^ n

theorem kleinZ_one {G : Type*} [Group G] {a b : G} : KleinZ a b 1 :=
  ⟨0, 0, by simp⟩

theorem kleinZ_mul {G : Type*} [Group G] {a b : G} (hc : Commute a b) {u v : G}
    (hu : KleinZ a b u) (hv : KleinZ a b v) : KleinZ a b (u * v) := by
  obtain ⟨m, n, rfl⟩ := hu
  obtain ⟨p, q, rfl⟩ := hv
  refine ⟨m + p, n + q, ?_⟩
  have hcc : Commute (b ^ n) (a ^ p) := (hc.zpow_zpow p n).symm
  calc a ^ m * b ^ n * (a ^ p * b ^ q) = a ^ m * (b ^ n * a ^ p) * b ^ q := by
        simp only [mul_assoc]
    _ = a ^ m * (a ^ p * b ^ n) * b ^ q := by rw [hcc.eq]
    _ = a ^ (m + p) * b ^ (n + q) := by
        rw [zpow_add, zpow_add]; simp only [mul_assoc]

theorem kleinZ_inv {G : Type*} [Group G] {a b : G} (hc : Commute a b) {u : G}
    (hu : KleinZ a b u) : KleinZ a b u⁻¹ := by
  obtain ⟨m, n, rfl⟩ := hu
  refine ⟨-m, -n, ?_⟩
  have hcc : Commute (b ^ (-n)) (a ^ (-m)) := (hc.zpow_zpow (-m) (-n)).symm
  rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
  exact hcc.eq

theorem kleinZ_commute {G : Type*} [Group G] {a b : G} (hc : Commute a b) {u v : G}
    (hu : KleinZ a b u) (hv : KleinZ a b v) : Commute u v := by
  obtain ⟨m, n, rfl⟩ := hu
  obtain ⟨p, q, rfl⟩ := hv
  have h1 : Commute (a ^ m) (a ^ p) := (Commute.refl a).zpow_zpow m p
  have h2 : Commute (a ^ m) (b ^ q) := hc.zpow_zpow m q
  have h3 : Commute (b ^ n) (a ^ p) := (hc.zpow_zpow p n).symm
  have h4 : Commute (b ^ n) (b ^ q) := (Commute.refl b).zpow_zpow n q
  exact (h1.mul_right h2).mul_left (h3.mul_right h4)

theorem kleinZ_conj {G : Type*} [Group G] {a b s : G} (hc : Commute a b)
    (ha : s * a * s⁻¹ = b) (hb : s * b * s⁻¹ = a * b) {u : G} (hu : KleinZ a b u) :
    KleinZ a b (s * u * s⁻¹) := by
  obtain ⟨m, n, rfl⟩ := hu
  refine ⟨n, m + n, ?_⟩
  have e1 : s * (a ^ m * b ^ n) * s⁻¹ = (s * a * s⁻¹) ^ m * (s * b * s⁻¹) ^ n := by
    rw [conj_zpow, conj_zpow]
    group
  have hcc : Commute (b ^ m) (a ^ n) := (hc.zpow_zpow n m).symm
  rw [e1, ha, hb, Commute.mul_zpow hc n, zpow_add, ← mul_assoc, hcc.eq, mul_assoc]

theorem card_A6_local : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

def kleinPre {Q : Type} [Group Q] [Finite Q] (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) {a b : alternatingGroup (Fin 6)}
    (hc : Commute a b) : Subgroup Q where
  carrier := {g | KleinZ a b (toA6 e g) ∧ g ^ 2 = 1}
  one_mem' := by
    show KleinZ a b (toA6 e 1) ∧ (1 : Q) ^ 2 = 1
    rw [map_one]
    exact ⟨kleinZ_one, one_pow 2⟩
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ : KleinZ a b (toA6 e g) ∧ g ^ 2 = 1 := hg
    obtain ⟨hh1, hh2⟩ : KleinZ a b (toA6 e h) ∧ h ^ 2 = 1 := hh
    have hcomm : Commute (toA6 e g) (toA6 e h) := kleinZ_commute hc hg1 hh1
    have hcen : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center Q := by
      rw [← toA6_eq_one_iff e]
      simp only [map_mul, map_inv]
      rw [hcomm.eq]
      group
    have hgh : Commute g h := involutions_comm_of_commutator_central hZ hg2 hh2 hcen
    show KleinZ a b (toA6 e (g * h)) ∧ (g * h) ^ 2 = 1
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      exact kleinZ_mul hc hg1 hh1
    · rw [hgh.mul_pow, hg2, hh2, one_mul]
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2⟩ : KleinZ a b (toA6 e g) ∧ g ^ 2 = 1 := hg
    show KleinZ a b (toA6 e g⁻¹) ∧ (g⁻¹) ^ 2 = 1
    refine ⟨?_, ?_⟩
    · rw [map_inv]
      exact kleinZ_inv hc hg1
    · rw [inv_pow, hg2, inv_one]

theorem kleinPre_conj_mem {Q : Type} [Group Q] [Finite Q]
    (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) {a b : alternatingGroup (Fin 6)}
    (hc : Commute a b) {t : Q} (ha : toA6 e t * a * (toA6 e t)⁻¹ = b)
    (hb : toA6 e t * b * (toA6 e t)⁻¹ = a * b) {v : Q} (hv : v ∈ kleinPre hZ e hc) :
    MulAut.conj t v ∈ kleinPre hZ e hc := by
  obtain ⟨hv1, hv2⟩ : KleinZ a b (toA6 e v) ∧ v ^ 2 = 1 := hv
  show KleinZ a b (toA6 e (MulAut.conj t v)) ∧ (MulAut.conj t v) ^ 2 = 1
  rw [MulAut.conj_apply]
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact kleinZ_conj hc ha hb hv1
  · rw [conj_pow, hv2, mul_one, mul_inv_cancel]

theorem kleinPre_pow_conj_mem {Q : Type} [Group Q] [Finite Q]
    (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) {a b : alternatingGroup (Fin 6)}
    (hc : Commute a b) {t : Q} (ha : toA6 e t * a * (toA6 e t)⁻¹ = b)
    (hb : toA6 e t * b * (toA6 e t)⁻¹ = a * b) (n : ℕ) :
    ∀ v ∈ kleinPre hZ e hc, ((MulAut.conj t) ^ n) v ∈ kleinPre hZ e hc := by
  induction n with
  | zero =>
    intro v hv
    simpa using hv
  | succ n ih =>
    intro v hv
    rw [pow_succ, MulAut.mul_apply]
    exact ih _ (kleinPre_conj_mem hZ e hc ha hb hv)

theorem ker_conj_eq_center (Q : Type) [Group Q] :
    ((MulAut.conj : Q →* MulAut Q)).ker = Subgroup.center Q := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hx g
    have h1 : x * g * x⁻¹ = g := congrArg (fun φ : MulAut Q => φ g) hx
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro hx
    ext g
    show x * g * x⁻¹ = g
    rw [← hx g]
    group

theorem card_range_conj {Q : Type} [Group Q] [Finite Q]
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) :
    Nat.card (MulAut.conj : Q →* MulAut Q).range = 360 := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAut.conj : Q →* MulAut Q)).toEquiv,
    ker_conj_eq_center, Nat.card_congr e.toEquiv, card_A6_local]

theorem card_Q_eq {Q : Type} [Group Q] [Finite Q] (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) : Nat.card Q = 1080 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hZ,
    Nat.card_congr e.toEquiv, card_A6_local]

theorem exists_orderOf_prime_of_natCard {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : ∃ x : G, orderOf x = p := by
  haveI := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hdvd
  exact exists_prime_orderOf_dvd_card p hdvd

theorem exists_nat_pow_eq_zpow {G : Type} [Group G] {f : G} (hf : f ^ 3 = 1) (m : ℤ) :
    ∃ n : ℕ, f ^ m = f ^ n := by
  refine ⟨(m % 3).toNat, ?_⟩
  have hm : (((m % 3).toNat : ℕ) : ℤ) = m % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
  have h3 : f ^ (3 : ℤ) = 1 := by simpa using hf
  rw [← zpow_natCast, hm]
  have hdecomp : m = m % 3 + 3 * (m / 3) := by omega
  conv_lhs => rw [hdecomp]
  rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem exists_V_of_bot (Q : Type) [Group Q] [Finite Q] (hQ : Nat.card Q = 1080) :
    ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ f ∈ (⊥ : Subgroup (MulAut Q)), ∀ v ∈ V, f v ∈ V := by
  obtain ⟨y, hy⟩ := exists_orderOf_prime_of_natCard (G := Q) 2 (by norm_num [hQ])
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    norm_num at hy
  refine ⟨Subgroup.zpowers y, ?_, ?_, ?_⟩
  · intro hbot
    apply hy1
    have hmem : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · refine IsPGroup.iff_card.mpr ⟨1, ?_⟩
    rw [Nat.card_zpowers, hy] <;> norm_num
  · intro f hf v hv
    rw [Subgroup.mem_bot.mp hf, MulAut.one_apply]
    exact hv

theorem exists_V_of_order_three {Q : Type} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6))
    {f : MulAut Q} (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1) :
    ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ g ∈ Subgroup.zpowers f, ∀ v ∈ V, g v ∈ V := by
  obtain ⟨t, ht⟩ := CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof.exists_eq_conj_of_tripleCover
    e (σ := f) (k := 1) (by rw [pow_one]; exact hf3)
  have ht3 : t ^ 3 ∈ Subgroup.center Q := by
    have h1 : (MulAut.conj : Q →* MulAut Q) (t ^ 3) = 1 := by
      rw [map_pow, ← ht, hf3]
    rw [← ker_conj_eq_center]
    exact MonoidHom.mem_ker.mpr h1
  have hs3 : (toA6 e t) ^ 3 = 1 := by
    rw [← map_pow, (toA6_eq_one_iff e _).mpr ht3]
  have hs1 : toA6 e t ≠ 1 := by
    intro h1
    have htc : t ∈ Subgroup.center Q := (toA6_eq_one_iff e t).mp h1
    rw [← ker_conj_eq_center] at htc
    exact hf1 (ht.trans (MonoidHom.mem_ker.mp htc))
  obtain ⟨a, b, ha2, hb2, -, ha1, -, hab, hsa, hsb⟩ := a6_three_klein (toA6 e t) hs3 hs1
  have hc : Commute a b := hab
  obtain ⟨y, hy2, hy1, hya⟩ := exists_lift_involution hZ e ha2 ha1
  have hyP : y ∈ kleinPre hZ e hc := by
    show KleinZ a b (toA6 e y) ∧ y ^ 2 = 1
    exact ⟨by rw [hya]; exact ⟨1, 0, by simp⟩, hy2⟩
  refine ⟨kleinPre hZ e hc, ?_, ?_, ?_⟩
  · intro hbot
    apply hy1
    rw [hbot] at hyP
    exact Subgroup.mem_bot.mp hyP
  · refine fun g => ⟨1, Subtype.ext ?_⟩
    obtain ⟨_, hg2⟩ : KleinZ a b (toA6 e (g : Q)) ∧ (g : Q) ^ 2 = 1 := g.2
    simpa using hg2
  · intro g hg v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    obtain ⟨n, hn⟩ := exists_nat_pow_eq_zpow hf3 m
    rw [hn, ht]
    exact kleinPre_pow_conj_mem hZ e hc hsa hsb n v hv

theorem ks1012AutHyp_tripleCover (Q : Type) [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (h : Sec4.IsTripleCover Q (alternatingGroup (Fin 6)))
    (F : Subgroup (MulAut Q)) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧
      ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  haveI : Group.IsPerfect Q := hq.1
  obtain ⟨hZ, ⟨e⟩⟩ := h
  haveI : Finite (MulAut Q) := Finite.of_injective (fun φ : MulAut Q => φ.toEquiv)
    (fun φ ψ hφψ => MulEquiv.ext (fun x => congrArg (fun σ : Q ≃ Q => σ x) hφψ))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFexp : ∀ x ∈ F, x ^ 3 = 1 := hF.2
  have hQ : Nat.card Q = 1080 := card_Q_eq hZ e
  have hFle : F ≤ (MulAut.conj : Q →* MulAut Q).range := by
    intro f hf
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof.exists_eq_conj_of_tripleCover
      e (σ := f) (k := 1) (by rw [pow_one]; exact hFexp f hf)
    exact ⟨t, ht.symm⟩
  have hFp : IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hFexp g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hFp
  have hdvd : Nat.card F ∣ 360 := by
    have := Subgroup.card_dvd_of_le hFle
    rwa [card_range_conj e] at this
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have h27 : 3 ^ 3 ∣ 3 ^ n := Nat.pow_dvd_pow 3 (by omega)
    rw [← hn] at h27
    have h360 : 3 ^ 3 ∣ 360 := dvd_trans h27 hdvd
    norm_num at h360
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · obtain ⟨V, hV1, hV2, hV3⟩ := exists_V_of_bot Q hQ
    refine ⟨⊥, bot_le, ?_, V, hV1, hV2, hV3⟩
    rw [Subgroup.card_bot, hn] <;> norm_num
  · obtain ⟨V, hV1, hV2, hV3⟩ := exists_V_of_bot Q hQ
    refine ⟨⊥, bot_le, ?_, V, hV1, hV2, hV3⟩
    rw [Subgroup.card_bot, hn] <;> norm_num
  · have h3dvd : 3 ∣ Nat.card F := by rw [hn]; norm_num
    obtain ⟨g, hg⟩ := exists_orderOf_prime_of_natCard (G := ↥F) 3 h3dvd
    have hfF : (g : MulAut Q) ∈ F := g.2
    have hof : orderOf (g : MulAut Q) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hg
    have hf3 : (g : MulAut Q) ^ 3 = 1 := hFexp _ hfF
    have hf1 : (g : MulAut Q) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hof
      norm_num at hof
    obtain ⟨V, hV1, hV2, hV3⟩ := exists_V_of_order_three hZ e hf3 hf1
    refine ⟨Subgroup.zpowers (g : MulAut Q), ?_, ?_, V, hV1, hV2, hV3⟩
    · exact Subgroup.zpowers_le.mpr hfF
    · rw [hn, Nat.card_zpowers, hof] <;> norm_num

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
