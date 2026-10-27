module

public import CFSG.RankThree.PartOne.K1214.ActR
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.K1214

variable {G : Type*} [Group G]

section Act

variable {p : ℕ}

theorem act_subgroup [Fact p.Prime] (hp5 : 5 ≤ p) {r e : ℕ} (hr : r = 1 ∨ r = 2) (he1 : 1 ≤ e)
    (he : r = 1 ∨ 2 ≤ e) {R : Subgroup G}
    (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) {c : G}
    (hc : c ∈ Subgroup.normalizer (R : Set G)) (hcp : c ^ p = 1) :
    (∀ x ∈ R, (c * x * c⁻¹ * x⁻¹) ^ p = 1) ∧ (∀ x ∈ R, x ^ p = 1 → c * x * c⁻¹ = x) := by
  set σ : MulAut ↥R := R.normalizerMonoidHom ⟨c, hc⟩ with hσdef
  have hσ : σ ^ p = 1 := by
    rw [hσdef, ← map_pow]
    have : (⟨c, hc⟩ : ↥(Subgroup.normalizer (R : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hcp)
    rw [this, map_one]
  obtain ⟨h1, h2⟩ := act_lemma_mul hp5 hr he1 he φ σ hσ
  have hσx : ∀ x : ↥R, ((σ x : ↥R) : G) = c * x * c⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe R ⟨c, hc⟩ x
  refine ⟨fun x hx => ?_, fun x hx hxp => ?_⟩
  · have h3 := congrArg Subtype.val (h1 ⟨x, hx⟩)
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, hσx] at h3
    exact h3
  · have h3 := congrArg Subtype.val (h2 ⟨x, hx⟩ (Subtype.ext (by simpa using hxp)))
    rwa [hσx] at h3

theorem exists_equiv_fin_one [Fact p.Prime] [Finite G] {Z : Subgroup G} (hZp : IsPGroup p ↥Z)
    (hZc : IsCyclic ↥Z) :
    ∃ e : ℕ, Nonempty (↥Z ≃* (Fin 1 → Multiplicative (ZMod (p ^ e)))) := by
  obtain ⟨e, hcard⟩ := (IsPGroup.iff_card).1 hZp
  let φ2 : Multiplicative (ZMod (p ^ e)) ≃* ↥Z :=
    (((ZMod.ringEquivCongr hcard.symm).toAddEquiv).toMultiplicative).trans (zmodCyclicMulEquiv hZc)
  exact ⟨e, ⟨φ2.symm.trans
    (MulEquiv.piUnique (fun _ : Fin 1 => Multiplicative (ZMod (p ^ e)))).symm⟩⟩

end Act

section Class2

theorem mul_pow_of_comm_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g q δ : G}
    (hδ : g * q * g⁻¹ * q⁻¹ = δ) (hgδ : g * δ = δ * g) (hδq : δ * q = q * δ) (hδp : δ ^ p = 1) :
    (g * q) ^ p = q ^ p * g ^ p := by
  have hgq : g * q = δ * q * g := by
    rw [← hδ]
    group
  have hpow : ∀ m : ℕ, g ^ m * q = δ ^ m * q * g ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hcomm : g * δ ^ m = δ ^ m * g := (Commute.pow_right (hgδ : Commute g δ) m).eq
      calc g ^ (m + 1) * q = g * (g ^ m * q) := by rw [pow_succ']; group
        _ = g * (δ ^ m * q * g ^ m) := by rw [ih]
        _ = (g * δ ^ m) * q * g ^ m := by group
        _ = δ ^ m * g * q * g ^ m := by rw [hcomm]
        _ = δ ^ m * (g * q) * g ^ m := by group
        _ = δ ^ m * (δ * q * g) * g ^ m := by rw [hgq]
        _ = δ ^ (m + 1) * q * g ^ (m + 1) := by rw [pow_succ, pow_succ']; group
  have hqδ : Commute q δ := hδq.symm
  have hmain : ∀ n : ℕ, ∃ k : ℕ, (g * q) ^ n = δ ^ k * q ^ n * g ^ n ∧ 2 * k = n * (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨k, hk, h2k⟩ := ih
      refine ⟨k + (n + 1), ?_, by nlinarith⟩
      have hc : q ^ n * δ ^ (n + 1) = δ ^ (n + 1) * q ^ n := (Commute.pow_pow hqδ n (n + 1)).eq
      calc (g * q) ^ (n + 1) = (g * q) ^ n * (g * q) := pow_succ _ _
        _ = δ ^ k * q ^ n * g ^ n * (g * q) := by rw [hk]
        _ = δ ^ k * q ^ n * (g ^ (n + 1) * q) := by rw [pow_succ]; group
        _ = δ ^ k * q ^ n * (δ ^ (n + 1) * q * g ^ (n + 1)) := by rw [hpow (n + 1)]
        _ = δ ^ k * (q ^ n * δ ^ (n + 1)) * q * g ^ (n + 1) := by group
        _ = δ ^ k * (δ ^ (n + 1) * q ^ n) * q * g ^ (n + 1) := by rw [hc]
        _ = δ ^ (k + (n + 1)) * q ^ (n + 1) * g ^ (n + 1) := by rw [pow_add, pow_succ q n]; group
  obtain ⟨k, hk, h2k⟩ := hmain p
  have hpk : p ∣ k := by
    have h1 : p ∣ 2 * k := ⟨p + 1, by rw [h2k]⟩
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    · exact h
  obtain ⟨k', rfl⟩ := hpk
  rw [hk, pow_mul, hδp, one_pow, one_mul]

theorem pow_eq_of_comm_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g q δ : G}
    (hδ : g * q * g⁻¹ * q⁻¹ = δ) (hgδ : g * δ = δ * g) (hδq : δ * q = q * δ) (hδp : δ ^ p = 1)
    (hgp : g ^ p = 1) : (g * q) ^ p = q ^ p := by
  rw [mul_pow_of_comm_data hp hp2 hδ hgδ hδq hδp, hgp, mul_one]

end Class2

section Cyclic

variable [Finite G]

omit [Finite G] in
theorem isCyclic_quotient_of_sup {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQn : (Q.subgroupOf P).Normal) {f : G} (hfP : f ∈ P)
    (hPf : P = Q ⊔ Subgroup.zpowers f) : IsCyclic (↥P ⧸ Q.subgroupOf P) := by
  classical
  set Q' := Q.subgroupOf P with hQ'
  let φ : ↥P →* ↥P ⧸ Q' := QuotientGroup.mk' Q'
  have hall : ∀ y : ↥P, φ y ∈ Subgroup.zpowers (φ ⟨f, hfP⟩) := by
    intro y
    have hy : (y : G) ∈ Q ⊔ Subgroup.zpowers f := by
      rw [← hPf]
      exact y.2
    rw [Subgroup.sup_eq_closure] at hy
    have key : ∃ hyP : (y : G) ∈ P, φ ⟨y, hyP⟩ ∈ Subgroup.zpowers (φ ⟨f, hfP⟩) := by
      refine Subgroup.closure_induction
        (p := fun x _ => ∃ hxP : x ∈ P, φ ⟨x, hxP⟩ ∈ Subgroup.zpowers (φ ⟨f, hfP⟩)) ?_ ?_ ?_ ?_ hy
      · rintro x (hx | hx)
        · refine ⟨hQP hx, ?_⟩
          have : φ ⟨x, hQP hx⟩ = 1 :=
            (QuotientGroup.eq_one_iff (⟨x, hQP hx⟩ : ↥P)).2 (Subgroup.mem_subgroupOf.2 hx)
          rw [this]
          exact Subgroup.one_mem _
        · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          have hxP : f ^ k ∈ P := Subgroup.zpow_mem _ hfP k
          refine ⟨hxP, ⟨k, ?_⟩⟩
          have : (⟨f ^ k, hxP⟩ : ↥P) = (⟨f, hfP⟩ : ↥P) ^ k := by
            apply Subtype.ext
            simp
          rw [this, map_zpow]
      · exact ⟨P.one_mem, by
          have : φ ⟨1, P.one_mem⟩ = 1 := map_one φ
          rw [this]
          exact Subgroup.one_mem _⟩
      · rintro x y - - ⟨hxP, hx⟩ ⟨hyP, hy⟩
        refine ⟨P.mul_mem hxP hyP, ?_⟩
        have : φ ⟨x * y, P.mul_mem hxP hyP⟩ = φ ⟨x, hxP⟩ * φ ⟨y, hyP⟩ := by
          rw [← map_mul]
          rfl
        rw [this]
        exact Subgroup.mul_mem _ hx hy
      · rintro x - ⟨hxP, hx⟩
        refine ⟨P.inv_mem hxP, ?_⟩
        have : φ ⟨x⁻¹, P.inv_mem hxP⟩ = (φ ⟨x, hxP⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact Subgroup.inv_mem _ hx
    obtain ⟨hyP, hy'⟩ := key
    exact hy'
  show IsCyclic (↥P ⧸ Q')
  have hcyc : IsCyclic (↥P ⧸ Q') := by
    refine ⟨φ ⟨f, hfP⟩, fun y' => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
    exact hall y
  exact hcyc

theorem exists_c_pow_mul {p : ℕ} (hp : p.Prime) {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQn : (Q.subgroupOf P).Normal) {f c : G} (hfP : f ∈ P)
    (hPf : P = Q ⊔ Subgroup.zpowers f) (hcP : c ∈ P) (hcQ : c ∉ Q)
    (hcp : c ^ p = 1) {x : G} (hx : x ∈ P) (hxp : x ^ p = 1) :
    ∃ j : ℕ, ∃ q ∈ Q, x = c ^ j * q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Q' := Q.subgroupOf P with hQ'
  let φ : ↥P →* ↥P ⧸ Q' := QuotientGroup.mk' Q'
  have hcyc : IsCyclic (↥P ⧸ Q') := isCyclic_quotient_of_sup hQP hQn hfP hPf
  have hφc : φ ⟨c, hcP⟩ ≠ 1 := fun h =>
    hcQ (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))
  have hφcp : (φ ⟨c, hcP⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨c, hcP⟩ : ↥P) ^ p = 1 := Subtype.ext (by simpa using hcp)
    rw [this, map_one]
  have hordc : orderOf (φ ⟨c, hcP⟩) = p := orderOf_eq_prime hφcp hφc
  have hφxp : (φ ⟨x, hx⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥P) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [this, map_one]
  have hle : Subgroup.zpowers (φ ⟨x, hx⟩) ≤ Subgroup.zpowers (φ ⟨c, hcP⟩) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hordc]
    exact orderOf_dvd_of_pow_eq_one hφxp
  have hmem : φ ⟨x, hx⟩ ∈ Subgroup.zpowers (φ ⟨c, hcP⟩) := hle (Subgroup.mem_zpowers _)
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 hmem
  refine ⟨n, (c ^ n)⁻¹ * x, ?_, by group⟩
  have h1 : φ ((⟨c, hcP⟩ : ↥P) ^ n) = φ ⟨x, hx⟩ := by
    rw [map_pow]
    exact hn
  have h2 : ((⟨c, hcP⟩ : ↥P) ^ n)⁻¹ * ⟨x, hx⟩ ∈ Q' := QuotientGroup.eq.1 h1
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa using h3


theorem exists_pow_mul_of_not_mem {p : ℕ} (hp : p.Prime) {P Q : Subgroup G} (hP : IsPGroup p ↥P)
    (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) {f c : G} (hfP : f ∈ P)
    (hPf : P = Q ⊔ Subgroup.zpowers f) (hcP : c ∈ P) (hcQ : c ∉ Q) (hcp : c ^ p = 1) {x : G}
    (hx : x ∈ P) (hxQ : x ∉ Q) : ∃ k : ℕ, ∃ q ∈ Q, c = x ^ k * q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Q' := Q.subgroupOf P with hQ'
  let φ : ↥P →* ↥P ⧸ Q' := QuotientGroup.mk' Q'
  have hcyc : IsCyclic (↥P ⧸ Q') := isCyclic_quotient_of_sup hQP hQn hfP hPf
  have hφc : φ ⟨c, hcP⟩ ≠ 1 := fun h =>
    hcQ (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))
  have hφcp : (φ ⟨c, hcP⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨c, hcP⟩ : ↥P) ^ p = 1 := Subtype.ext (by simpa using hcp)
    rw [this, map_one]
  have hordc : orderOf (φ ⟨c, hcP⟩) = p := orderOf_eq_prime hφcp hφc
  have hφx : φ ⟨x, hx⟩ ≠ 1 := fun h =>
    hxQ (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h))
  have hqp : IsPGroup p (↥P ⧸ Q') := hP.to_quotient Q'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hqp) (φ ⟨x, hx⟩)
  have hk1 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, orderOf_eq_one_iff] at hk
    exact hφx hk
  have hle : Subgroup.zpowers (φ ⟨c, hcP⟩) ≤ Subgroup.zpowers (φ ⟨x, hx⟩) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hordc, hk]
    exact dvd_pow_self p hk1
  have hmem : φ ⟨c, hcP⟩ ∈ Subgroup.zpowers (φ ⟨x, hx⟩) := hle (Subgroup.mem_zpowers _)
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 hmem
  refine ⟨n, (x ^ n)⁻¹ * c, ?_, by group⟩
  have h1 : φ ((⟨x, hx⟩ : ↥P) ^ n) = φ ⟨c, hcP⟩ := by
    rw [map_pow]
    exact hn
  have h2 : ((⟨x, hx⟩ : ↥P) ^ n)⁻¹ * ⟨c, hcP⟩ ∈ Q' := QuotientGroup.eq.1 h1
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa using h3

end Cyclic

section Elem

theorem isElementaryAbelian_closure {p : ℕ} {S : Set G} (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hpow : ∀ x ∈ S, x ^ p = 1) : IsElementaryAbelian p ↥(Subgroup.closure S) := by
  have hcl : IsMulCommutative ↥(Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm x hx y hy)
  refine { toIsMulCommutative := hcl, exponent_dvd_p := ?_ }
  have := hcl
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure S := x.2
  exact
    Subgroup.closure_induction (k := S) (p := fun z _hz => z ^ p = 1) (x := (x : G))
      (fun y hy => hpow y hy) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          show y * z = z * y
          simpa using congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := Subgroup.closure S)).comm ⟨y, hy⟩ ⟨z, hz⟩)
        calc (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y _hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

end Elem

section Props

variable {p : ℕ}

theorem pow_c_pow_mul (hp : p.Prime) (hp2 : p ≠ 2) {c q d : G} (hd : c * q * c⁻¹ * q⁻¹ = d)
    (hcd : c * d = d * c) (hdp : d ^ p = 1) (hdq : d * q = q * d) (hcp : c ^ p = 1) (j : ℕ) :
    (c ^ j * q) ^ p = q ^ p := by
  have hcq : c * q = d * q * c := by
    rw [← hd]
    group
  have hpow : ∀ m : ℕ, c ^ m * q = d ^ m * q * c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hcomm : c * d ^ m = d ^ m * c := (Commute.pow_right (hcd : Commute c d) m).eq
      calc c ^ (m + 1) * q = c * (c ^ m * q) := by rw [pow_succ']; group
        _ = c * (d ^ m * q * c ^ m) := by rw [ih]
        _ = (c * d ^ m) * q * c ^ m := by group
        _ = d ^ m * c * q * c ^ m := by rw [hcomm]
        _ = d ^ m * (c * q) * c ^ m := by group
        _ = d ^ m * (d * q * c) * c ^ m := by rw [hcq]
        _ = d ^ (m + 1) * q * c ^ (m + 1) := by rw [pow_succ, pow_succ']; group
  have hδ : c ^ j * q * (c ^ j)⁻¹ * q⁻¹ = d ^ j := by
    rw [hpow j]
    group
  refine pow_eq_of_comm_data hp hp2 hδ ?_ ?_ ?_ ?_
  · exact ((Commute.pow_pow (hcd : Commute c d) j j).eq)
  · exact (Commute.pow_left (hdq : Commute d q) j).eq
  · rw [← pow_mul, mul_comm, pow_mul, hdp, one_pow]
  · rw [← pow_mul, mul_comm, pow_mul, hcp, one_pow]

theorem props_sup {R Z : Subgroup G} {c : G}
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r) (hbot : R ⊓ Z = ⊥)
    (hRc : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r) (hZc : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hcR : ∀ r ∈ R, c * r * c⁻¹ ∈ R) (hcZ : ∀ z ∈ Z, c * z * c⁻¹ ∈ Z)
    (hR1 : ∀ x ∈ R, (c * x * c⁻¹ * x⁻¹) ^ p = 1) (hR2 : ∀ x ∈ R, x ^ p = 1 → c * x * c⁻¹ = x)
    (hZ1 : ∀ x ∈ Z, (c * x * c⁻¹ * x⁻¹) ^ p = 1) (hZ2 : ∀ x ∈ Z, x ^ p = 1 → c * x * c⁻¹ = x) :
    (∀ a ∈ Z ⊔ R, ∀ b ∈ Z ⊔ R, a * b = b * a) ∧
      (∀ q ∈ Z ⊔ R, (c * q * c⁻¹ * q⁻¹) ^ p = 1) ∧
      (∀ q ∈ Z ⊔ R, q ^ p = 1 → c * q * c⁻¹ = q) := by
  have hZR : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z := fun z hz r hr => (hRZ r hr z hz).symm
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨z1, hz1, r1, hr1, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hZR ha
    obtain ⟨z2, hz2, r2, hr2, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hZR hb
    have h12 : Commute z1 z2 := hZc z1 hz1 z2 hz2
    have h34 : Commute r1 r2 := hRc r1 hr1 r2 hr2
    have h14 : Commute z1 r2 := hZR z1 hz1 r2 hr2
    have h32 : Commute r1 z2 := hRZ r1 hr1 z2 hz2
    exact Commute.mul_left (Commute.mul_right h12 h14) (Commute.mul_right h32 h34)
  · intro q hq
    obtain ⟨z, hz, r, hr, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hZR hq
    have hdz : c * z * c⁻¹ * z⁻¹ ∈ Z := Z.mul_mem (hcZ z hz) (Z.inv_mem hz)
    have hdr : c * r * c⁻¹ * r⁻¹ ∈ R := R.mul_mem (hcR r hr) (R.inv_mem hr)
    have hsplit : c * (z * r) * c⁻¹ * (z * r)⁻¹ =
        (c * z * c⁻¹ * z⁻¹) * (c * r * c⁻¹ * r⁻¹) := by
      have h1 : (c * r * c⁻¹ * r⁻¹) * z⁻¹ = z⁻¹ * (c * r * c⁻¹ * r⁻¹) :=
        hRZ _ hdr _ (Z.inv_mem hz)
      calc c * (z * r) * c⁻¹ * (z * r)⁻¹
          = (c * z * c⁻¹) * ((c * r * c⁻¹ * r⁻¹) * z⁻¹) := by group
        _ = (c * z * c⁻¹) * (z⁻¹ * (c * r * c⁻¹ * r⁻¹)) := by rw [h1]
        _ = (c * z * c⁻¹ * z⁻¹) * (c * r * c⁻¹ * r⁻¹) := by group
    rw [hsplit, Commute.mul_pow (hRZ _ hdr _ hdz).symm, hZ1 z hz, hR1 r hr, one_mul]
  · intro q hq hqp
    obtain ⟨z, hz, r, hr, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hZR hq
    have hcomm : Commute z r := hZR z hz r hr
    have h1 : z ^ p * r ^ p = 1 := by rw [← hcomm.mul_pow]; exact hqp
    have hrp : r ^ p ∈ R ⊓ Z := ⟨R.pow_mem hr p, by
      have : r ^ p = (z ^ p)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact Z.inv_mem (Z.pow_mem hz p)⟩
    rw [hbot, Subgroup.mem_bot] at hrp
    have hzp : z ^ p = 1 := by rw [hrp, mul_one] at h1; exact h1
    have e1 := hZ2 z hz hzp
    have e2 := hR2 r hr hrp
    calc c * (z * r) * c⁻¹ = (c * z * c⁻¹) * (c * r * c⁻¹) := by group
      _ = z * r := by rw [e1, e2]

end Props

end CFSG.RankThree.PartOne.K1214
