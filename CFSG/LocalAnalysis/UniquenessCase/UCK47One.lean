module

public import CFSG.LocalAnalysis.UniquenessCase.UCK41
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.RankThree.FFModules (fixSub)
open scoped commutatorElement

private def conjSub {G : Type*} [Group G] (g : G) (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

private lemma mem_conjSub_iff {G : Type*} [Group G] {g : G} {A : Subgroup G} {x : G} :
    x ∈ conjSub g A ↔ g⁻¹ * x * g ∈ A := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hx⟩
    have hx' : g * a * g⁻¹ = x := by
      rw [← hx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hx']
    have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rwa [this]
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private lemma conjSub_zpowers {G : Type*} [Group G] (g x : G) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [conjSub, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

private lemma zmod_two_eq_zero_or_one (μ : ZMod 2) : μ = 0 ∨ μ = 1 := by
  revert μ; decide

private lemma apply_inv_apply {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : G) (x : V) : ρ g⁻¹ (ρ g x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private lemma apply_apply_inv {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : G) (x : V) : ρ g (ρ g⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private lemma fixSub_conjSub {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : G) (A : Subgroup G) :
    fixSub ρ (conjSub g A) = (fixSub ρ A).map (ρ g) := by
  ext w
  constructor
  · intro hw
    refine ⟨ρ g⁻¹ w, ?_, ?_⟩
    · intro a ha
      have hmem : g * a * g⁻¹ ∈ conjSub g A := by
        rw [mem_conjSub_iff]
        have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
        rwa [this]
      have h := hw (g * a * g⁻¹) hmem
      have h2 : ρ g (ρ a (ρ g⁻¹ w)) = w := by
        simpa only [map_mul, Module.End.mul_apply] using h
      calc ρ a (ρ g⁻¹ w) = ρ g⁻¹ (ρ g (ρ a (ρ g⁻¹ w))) :=
            (apply_inv_apply ρ g (ρ a (ρ g⁻¹ w))).symm
        _ = ρ g⁻¹ w := by rw [h2]
    · exact apply_apply_inv ρ g w
  · rintro ⟨u, hu, rfl⟩ y hy
    rw [mem_conjSub_iff] at hy
    have h1 : ρ g⁻¹ (ρ y (ρ g u)) = u := by
      have hya : ρ (g⁻¹ * y * g) u = u := hu (g⁻¹ * y * g) hy
      simpa only [map_mul, Module.End.mul_apply] using hya
    calc ρ y (ρ g u) = ρ g (ρ g⁻¹ (ρ y (ρ g u))) :=
          (apply_apply_inv ρ g (ρ y (ρ g u))).symm
      _ = ρ g u := by rw [h1]

private lemma isElemAbelian_zpowers {G : Type*} [Group G] {p : ℕ} {x : G} (hx : x ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) := by
  rw [Subgroup.zpowers_eq_closure]
  exact CFSG.Open.IsElemAbelian.closure_of_commute
    (by rintro a rfl b rfl; rfl) (by rintro a rfl; exact hx)

private lemma mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hz
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have hba : b * a' = a' * b := (hc a' ha' b hb).symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hba]
      _ = a * a' * (b * b') := by group
  | inv y _ hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have hba : b * a = a * b := (hc a ha b hb).symm
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hba]

private lemma conj_pow_mul_eq {G : Type*} [Group G] {d z c : G}
    (hcd : c * d * c⁻¹ = z * d) (hcZ : c * z = z * c) :
    ∀ n : ℕ, c ^ n * d * (c⁻¹) ^ n = z ^ n * d := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hcz : Commute c z := hcZ
    have hczn : c * z ^ n * c⁻¹ = z ^ n := by
      rw [(hcz.pow_right n).eq, mul_assoc, mul_inv_cancel, mul_one]
    calc c ^ (n + 1) * d * (c⁻¹) ^ (n + 1)
        = c * (c ^ n * d * (c⁻¹) ^ n) * c⁻¹ := by
          rw [pow_succ', pow_succ']; group
      _ = c * (z ^ n * d) * c⁻¹ := by rw [ih]
      _ = (c * z ^ n * c⁻¹) * (c * d * c⁻¹) := by group
      _ = z ^ n * (z * d) := by rw [hczn, hcd]
      _ = z ^ (n + 1) * d := by rw [pow_succ]; group

private lemma hyperplane_eq_zpowers_or_conj {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {d z c : G} (hd_pow : d ^ r = 1) (hzr : z ^ r = 1)
    (hd1 : d ≠ 1) (hz1 : z ≠ 1) (hdz : d * z = z * d) (hcZ : c * z = z * c)
    (hcd : c * d * c⁻¹ = z * d) (hdZ : d ∉ Subgroup.zpowers z)
    {B : Subgroup G} (hBX : B ≤ Subgroup.zpowers d ⊔ Subgroup.zpowers z)
    (hBidx : B.relIndex (Subgroup.zpowers d ⊔ Subgroup.zpowers z) = r) :
    B = Subgroup.zpowers z ∨
      ∃ i : ℕ, B = conjSub (c ^ i) (Subgroup.zpowers d) := by
  classical
  set D0 : Subgroup G := Subgroup.zpowers d with hD0
  set Z : Subgroup G := Subgroup.zpowers z with hZ
  set X : Subgroup G := D0 ⊔ Z with hX
  have hdzc : Commute d z := hdz
  have hD0card : Nat.card D0 = r := by
    have ho : orderOf d = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf d) (orderOf_dvd_of_pow_eq_one hd_pow) with h | h
      · exact absurd h (by rw [orderOf_eq_one_iff]; exact hd1)
      · exact h
    rw [hD0, Nat.card_zpowers, ho]
  have hZcard : Nat.card Z = r := by
    have ho : orderOf z = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf z) (orderOf_dvd_of_pow_eq_one hzr) with h | h
      · exact absurd h (by rw [orderOf_eq_one_iff]; exact hz1)
      · exact h
    rw [hZ, Nat.card_zpowers, ho]
  have hcross : ∀ x ∈ D0, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    rw [hD0] at hx
    rw [hZ] at hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hi, ← hj]
    exact (hdzc.zpow_zpow i j).eq
  have hXel : CFSG.Open.IsElemAbelian r X :=
    CFSG.Open.IsElemAbelian.sup_of_commute (isElemAbelian_zpowers hd_pow)
      (isElemAbelian_zpowers hzr) hcross
  have hinf : D0 ⊓ Z = ⊥ := by
    have hdvd : Nat.card (D0 ⊓ Z : Subgroup G) ∣ Nat.card Z := by
      have h := Subgroup.card_subgroup_dvd_card ((D0 ⊓ Z).subgroupOf Z)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h
    rw [hZcard] at hdvd
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr'
    · exact Subgroup.eq_bot_of_card_eq (D0 ⊓ Z) h1
    · exfalso
      have hZle' : Z ≤ D0 := by
        have hEq : D0 ⊓ Z = Z :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hZcard, hr'])
        rw [← hEq]; exact inf_le_left
      have hZeq : Z = D0 := Subgroup.eq_of_le_of_card_ge hZle' (by rw [hD0card, hZcard])
      exact hdZ (by rw [hZeq]; exact Subgroup.mem_zpowers d)
  have hXcard : Nat.card X = r ^ 2 := by
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D0 Z hcross).1
    rw [hinf, Subgroup.card_bot, mul_one, hD0card, hZcard] at hc
    rw [hX, hc, pow_two]
  rcases eq_or_ne B Z with rfl | hBZ
  · exact Or.inl rfl
  · refine Or.inr ?_
    have hBcard : Nat.card B = r := by
      have hidx : (B.subgroupOf X).index = r := hBidx
      have h := Subgroup.index_mul_card (B.subgroupOf X)
      have hcardB : Nat.card (B.subgroupOf X) = Nat.card B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
      rw [hidx, hcardB, hXcard] at h
      exact Nat.mul_left_cancel hr.pos (by rw [h, pow_two])
    have hBinf : B ⊓ Z = ⊥ := by
      have hdvd : Nat.card (B ⊓ Z : Subgroup G) ∣ Nat.card Z := by
        have h := Subgroup.card_subgroup_dvd_card ((B ⊓ Z).subgroupOf Z)
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h
      rw [hZcard] at hdvd
      rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr'
      · exact Subgroup.eq_bot_of_card_eq (B ⊓ Z) h1
      · exfalso
        have hZle' : Z ≤ B := by
          have hEq : B ⊓ Z = Z :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hZcard, hr'])
          rw [← hEq]; exact inf_le_left
        exact hBZ (Subgroup.eq_of_le_of_card_ge hZle' (by rw [hBcard, hZcard])).symm
    have hZle : Z ≤ X := le_sup_right
    have hBsup : B ⊔ Z = X := by
      have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B Z
        (fun x hx y hy => hXel.comm (hBX hx) (hZle hy))).1
      have hle : B ⊔ Z ≤ X := sup_le hBX hZle
      have hsupcard : Nat.card (B ⊔ Z : Subgroup G) = r ^ 2 := by
        rw [hBinf, Subgroup.card_bot, mul_one, hBcard, hZcard] at hc
        rw [hc, pow_two]
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hsupcard, hXcard])
    have hdX : d ∈ B ⊔ Z := by
      rw [hBsup]
      exact (le_sup_left : D0 ≤ D0 ⊔ Z) (Subgroup.mem_zpowers d)
    obtain ⟨b, hbB, z', hz'Z, hdb⟩ :=
      mem_sup_of_commute (A := B) (B := Z)
        (fun x hx y hy => hXel.comm (hBX hx) (hZle hy)) hdX
    rw [hZ] at hz'Z
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz'Z
    have hzeq : z' = z ^ m := hm.symm
    have hb_eq : b = d * z'⁻¹ := by rw [hdb]; group
    have hz_order : orderOf z = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf z) (orderOf_dvd_of_pow_eq_one hzr) with h | h
      · exact absurd h (by rw [orderOf_eq_one_iff]; exact hz1)
      · exact h
    set j : ℤ := (-m) % (r : ℤ) with hj
    have hj_eq : z ^ j = z'⁻¹ := by
      have h1 : z ^ ((-m) % (orderOf z : ℤ)) = z ^ (-m) := zpow_mod_orderOf z (-m)
      rw [hz_order] at h1
      rw [← hj] at h1
      have h2 : z'⁻¹ = z ^ (-m) := by rw [hzeq, ← zpow_neg]
      rw [h1, h2]
    have hj_nonneg : 0 ≤ j := Int.emod_nonneg (-m) (by exact_mod_cast hr.ne_zero)
    have hj_lt : j < r := by
      have := Int.emod_lt_of_pos (-m) (by exact_mod_cast hr.pos : (0 : ℤ) < (r : ℤ))
      rw [← hj] at this; exact_mod_cast this
    set j' : ℕ := j.toNat with hj'
    have hzjj : z ^ j = z ^ j' := by
      rw [← Int.toNat_of_nonneg hj_nonneg, zpow_natCast, ← hj']
    have hzval : z'⁻¹ = z ^ j' := by rw [← hj_eq, hzjj]
    have hb_eq' : b = d * z ^ j' := by rw [hb_eq, hzval]
    have hb_ne : b ≠ 1 := by
      intro hb1
      apply hdZ
      have hd_eq : d = (z ^ j')⁻¹ := by
        calc d = d * z ^ j' * (z ^ j')⁻¹ := by group
          _ = 1 * (z ^ j')⁻¹ := by rw [← hb_eq', hb1]
          _ = (z ^ j')⁻¹ := by rw [one_mul]
      rw [hd_eq, hZ]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers_iff.mpr ⟨(j' : ℤ), by rw [zpow_natCast]⟩)
    have hb_pow : b ^ r = 1 := by
      rw [hb_eq']
      have hcomm : Commute d (z ^ j') := by simpa using hdzc.zpow_right (j' : ℤ)
      rw [hcomm.mul_pow, hd_pow, one_mul, ← pow_mul, mul_comm j' r, pow_mul, hzr, one_pow]
    have hb_order : orderOf b = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf b) (orderOf_dvd_of_pow_eq_one hb_pow) with h | h
      · exact absurd h (by rw [orderOf_eq_one_iff]; exact hb_ne)
      · exact h
    have hBgen : B = Subgroup.zpowers b := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
      rw [Nat.card_zpowers, hb_order, hBcard]
    refine ⟨j', ?_⟩
    rw [hBgen, hb_eq', conjSub_zpowers, ← inv_pow, conj_pow_mul_eq hcd hcZ j']
    congr 1
    simpa using (hdzc.zpow_right (j' : ℤ)).eq

theorem k47_one {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (D : Subgroup G) (hD : Nat.card D = r) (hfix : Module.finrank (ZMod 2) (fixSub ρ D) ≤ 1)
    (R : Subgroup G) (hR : IsPGroup r R) (hDR : D ≤ R) (c : G) (hc : c ∈ R)
    (hcz : ∀ d ∈ D, c * d * c⁻¹ * d⁻¹ ∈ (Subgroup.center ↥R).map R.subtype) :
    ∀ d ∈ D, c * d = d * c := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  intro d hd
  by_contra hne
  have hd1 : d ≠ 1 := by rintro rfl; exact hne (by simp)
  set z : G := c * d * c⁻¹ * d⁻¹ with hzdef
  have hz_mem : z ∈ (Subgroup.center ↥R).map R.subtype := hcz d hd
  obtain ⟨zR, hzR_center, hzR_map⟩ := Subgroup.mem_map.mp hz_mem
  have hzR_val : (zR : G) = z := hzR_map
  have hz_comm_R : ∀ x ∈ R, z * x = x * z := by
    intro x hx
    have h := Subgroup.mem_center_iff.mp hzR_center (⟨x, hx⟩ : R)
    have h2 : (x : G) * zR = zR * (x : G) := congrArg Subtype.val h
    rw [hzR_val] at h2
    exact h2.symm
  have hczc : Commute c z := (hz_comm_R c hc).symm
  have hdzc : Commute d z := (hz_comm_R d (hDR hd)).symm
  have hcd : c * d * c⁻¹ = z * d := by rw [hzdef]; group
  have hz1 : z ≠ 1 := by
    intro hz_eq
    apply hne
    have hcz1 : c * d * c⁻¹ * d⁻¹ = 1 := by rw [← hzdef]; exact hz_eq
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
    exact hcz1
  have hd_order : orderOf d = r := by
    have hd_dvd : orderOf d ∣ r := by
      rw [← hD]; exact Subgroup.orderOf_dvd_natCard D hd
    rcases hr.eq_one_or_self_of_dvd (orderOf d) hd_dvd with h | h
    · exact absurd h (by rw [orderOf_eq_one_iff]; exact hd1)
    · exact h
  have hd_pow : d ^ r = 1 := by rw [← hd_order]; exact pow_orderOf_eq_one d
  have hzr : z ^ r = 1 := by
    have hzeq : ⁅c, d⁆ = z := by rw [commutatorElement_def, ← hzdef]
    have hcomm : Commute d ⁅c, d⁆ := by rw [hzeq]; exact hdzc
    rw [← hzeq, Commute.commutatorElement_pow_right hcomm, hd_pow, commutatorElement_one_right]
  have hz_order : orderOf z = r := by
    rcases hr.eq_one_or_self_of_dvd (orderOf z) (orderOf_dvd_of_pow_eq_one hzr) with h | h
    · exact absurd h (by rw [orderOf_eq_one_iff]; exact hz1)
    · exact h
  have hdZ : d ∉ Subgroup.zpowers z := by
    intro hdZ'
    have hDleZ : Subgroup.zpowers d ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hdZ'
    have hDZ : Subgroup.zpowers d = Subgroup.zpowers z := by
      apply Subgroup.eq_of_le_of_card_ge hDleZ
      rw [Nat.card_zpowers, Nat.card_zpowers, hd_order, hz_order]
    have hzD : z ∈ Subgroup.zpowers d := by
      rw [hDZ]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzD
    have hcz_conj : c * z * c⁻¹ = z := by rw [hczc.eq]; group
    have hconj_dk : c * d ^ k * c⁻¹ = d ^ k := by rw [hk, hcz_conj]
    have hconjpow : c * d ^ k * c⁻¹ = (c * d * c⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    have hdk : c * d ^ k * c⁻¹ = d ^ (k * (k + 1)) := by
      rw [hconjpow, hcd, ← hk, ← zpow_add_one, ← zpow_mul]
      congr 1
      ring
    have h3 : d ^ (k * k + k) = d ^ k := by
      have he : k * k + k = k * (k + 1) := by ring
      rw [he, ← hdk, hconj_dk]
    rw [zpow_add] at h3
    have hdkk : d ^ (k * k) = 1 := by
      have h4 := congrArg (fun x => x * (d ^ k)⁻¹) h3
      simpa [mul_assoc] using h4
    have hdvd : (r : ℤ) ∣ k * k := by
      have h5 : (orderOf d : ℤ) ∣ k * k := (orderOf_dvd_iff_zpow_eq_one (x := d)).mpr hdkk
      rwa [hd_order] at h5
    have hk0 : (k : ZMod r) = 0 := by
      have hcast : (k : ZMod r) * (k : ZMod r) = 0 := by
        rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hdvd
      exact mul_self_eq_zero.mp hcast
    have hk_dvd : (r : ℤ) ∣ k := (ZMod.intCast_zmod_eq_zero_iff_dvd k r).mp hk0
    have hz_eq1 : z = 1 := by
      rw [← hk]
      exact (orderOf_dvd_iff_zpow_eq_one (x := d)).mp (by rwa [hd_order])
    exact hz1 hz_eq1
  set D0 : Subgroup G := Subgroup.zpowers d with hD0
  set Z : Subgroup G := Subgroup.zpowers z with hZ
  have hD_eq : D = D0 := by
    rw [hD0]
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd)
    rw [Nat.card_zpowers, hd_order, hD]
  have hcross' : ∀ x ∈ D0, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    rw [hD0] at hx
    rw [hZ] at hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hi, ← hj]
    exact (hdzc.zpow_zpow i j).eq
  have hXel : CFSG.Open.IsElemAbelian r (D0 ⊔ Z) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (isElemAbelian_zpowers hd_pow)
      (isElemAbelian_zpowers hzr) hcross'
  have hXne : D0 ⊔ Z ≠ ⊥ := by
    intro hbot
    have hdX' : d ∈ D0 ⊔ Z :=
      (le_sup_left : D0 ≤ D0 ⊔ Z) (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    rw [hbot] at hdX'
    exact hd1 (by simpa using hdX')
  have hspan := iSup_fixSub_hyperplane_eq_top ρ hr hr2 hXel hXne
  have key : (⊤ : Submodule (ZMod 2) V) ≤
      fixSub ρ Z ⊔ ⨆ i : ℕ, fixSub ρ (conjSub (c ^ i) D0) := by
    rw [← hspan]
    refine iSup_le fun B => ?_
    rcases hyperplane_eq_zpowers_or_conj hr hd_pow hzr hd1 hz1 hdzc.eq hczc.eq hcd hdZ B.2.1 B.2.2 with
      hBZ | ⟨i, hi⟩
    · rw [hBZ]; exact le_sup_left
    · rw [hi]
      exact (le_iSup (fun i => fixSub ρ (conjSub (c ^ i) D0)) i).trans le_sup_right
  have harith : ¬ (∀ i : ℕ, fixSub ρ (conjSub (c ^ i) D0) ≤ fixSub ρ Z) := by
    intro hall
    have hUle : fixSub ρ Z ⊔ ⨆ i : ℕ, fixSub ρ (conjSub (c ^ i) D0) ≤ fixSub ρ Z :=
      sup_le le_rfl (iSup_le hall)
    have htop : (⊤ : Submodule (ZMod 2) V) ≤ fixSub ρ Z := key.trans hUle
    have hZtop : fixSub ρ Z = ⊤ := top_le_iff.mp htop
    have hz_id : ρ z = 1 := by
      apply LinearMap.ext
      intro w
      have : w ∈ fixSub ρ Z := by rw [hZtop]; exact Submodule.mem_top
      exact this z (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    exact hz1 (hρ (by rw [hz_id, map_one]))
  push Not at harith
  obtain ⟨i, hi⟩ := harith
  simp only [SetLike.le_def] at hi
  push Not at hi
  obtain ⟨w, hwB, hwZ⟩ := hi
  have hzw : ρ z w ≠ w := by
    intro h
    apply hwZ
    let S : Subgroup G :=
      { carrier := {a | ρ a w = w}
        mul_mem' := fun {a b} ha hb => by
          change ρ (a * b) w = w
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by change ρ 1 w = w; rw [map_one, Module.End.one_apply]
        inv_mem' := fun {a} ha => by
          change ρ a⁻¹ w = w
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hzS : z ∈ S := h
    intro a ha
    exact Subgroup.zpowers_le.mpr hzS (hZ ▸ ha)
  have hwB' : w ∈ (fixSub ρ D0).map (ρ (c ^ i)) := by
    rw [← fixSub_conjSub]
    exact hwB
  obtain ⟨v, hvD0, hvw⟩ := Submodule.mem_map.mp hwB'
  have hci_comm_z : z * c ^ i = c ^ i * z := (hczc.symm.pow_right i).eq
  have hzu : ρ z v ≠ v := by
    intro h
    apply hzw
    calc ρ z w = ρ z (ρ (c ^ i) v) := by rw [hvw]
      _ = ρ (z * c ^ i) v := by conv_rhs => rw [map_mul, Module.End.mul_apply]
      _ = ρ (c ^ i * z) v := by rw [hci_comm_z]
      _ = ρ (c ^ i) (ρ z v) := by conv_lhs => rw [map_mul, Module.End.mul_apply]
      _ = ρ (c ^ i) v := by rw [h]
      _ = w := hvw
  have hzv_mem : ρ z v ∈ fixSub ρ D0 := by
    intro a ha
    have ha' : a ∈ Subgroup.zpowers d := hD0 ▸ ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ha'
    have haz : a * z = z * a := by
      rw [← hj]
      exact (hdzc.zpow_left j).eq
    calc ρ a (ρ z v) = ρ (a * z) v := by conv_rhs => rw [map_mul, Module.End.mul_apply]
      _ = ρ (z * a) v := by rw [haz]
      _ = ρ z (ρ a v) := by conv_lhs => rw [map_mul, Module.End.mul_apply]
      _ = ρ z v := by rw [hvD0 a ha]
  have hfixS : Module.finrank (ZMod 2) (fixSub ρ D0) ≤ 1 := by rw [← hD_eq]; exact hfix
  have hv_ne : v ≠ 0 := by
    intro hv0
    apply hzu
    rw [hv0, map_zero]
  have hT_le : (ZMod 2) ∙ v ≤ fixSub ρ D0 := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hvD0
  have hTfin : Module.finrank (ZMod 2) ((ZMod 2) ∙ v) = 1 := finrank_span_singleton hv_ne
  have hSfin : Module.finrank (ZMod 2) (fixSub ρ D0) = 1 :=
    le_antisymm hfixS (by rw [← hTfin]; exact Submodule.finrank_mono hT_le)
  have hSeq : (ZMod 2) ∙ v = fixSub ρ D0 :=
    Submodule.eq_of_le_of_finrank_le hT_le (by rw [hSfin, hTfin])
  have hzv_span : ρ z v ∈ (ZMod 2) ∙ v := by rw [hSeq]; exact hzv_mem
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hzv_span
  have hμ_ne : μ ≠ 1 := by
    intro hμ1
    apply hzu
    rw [← hμ, hμ1, one_smul]
  have hμ0 : μ = 0 := by
    have h : μ = 0 ∨ μ = 1 := zmod_two_eq_zero_or_one μ
    tauto
  have hz0 : ρ z v = 0 := by rw [← hμ, hμ0, zero_smul]
  have hzinj : Function.Injective (ρ z) := by
    intro a b hab
    have h1 := congrArg (ρ z⁻¹) hab
    rw [apply_inv_apply ρ z a, apply_inv_apply ρ z b] at h1
    exact h1
  exact hv_ne (hzinj (hz0.trans (map_zero (ρ z)).symm))

end CFSG.LocalAnalysis.UniquenessCase.UCK
