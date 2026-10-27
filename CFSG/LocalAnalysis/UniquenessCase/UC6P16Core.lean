module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

private def p16Prod {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) : Subgroup G where
  carrier := {u | ∃ h ∈ H, ∃ k ∈ K, u = h * k}
  mul_mem' := by
    rintro _ _ ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
    refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
    calc h1 * k1 * (h2 * k2) = h1 * (k1 * h2) * k2 := by simp only [mul_assoc]
      _ = h1 * (h2 * k1) * k2 := by rw [hc h2 hh2 k1 hk1]
      _ = h1 * h2 * (k1 * k2) := by simp only [mul_assoc]
  one_mem' := ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  inv_mem' := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    rw [mul_inv_rev]
    exact ((show Commute h k from hc h hh k hk).inv_inv).eq.symm

private theorem p16Prod_ge {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    H ⊔ K ≤ p16Prod hc :=
  sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, (mul_one h).symm⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, (one_mul k).symm⟩)

private theorem p16_sup_decomp {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {u : G}
    (hu : u ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, u = h * k :=
  p16Prod_ge hc hu

private theorem p16_sup_comm {H K : Subgroup G} (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    {u v : G} (hu : u ∈ H ⊔ K) (hv : v ∈ H ⊔ K) : u * v = v * u := by
  obtain ⟨h1, hh1, k1, hk1, rfl⟩ := p16_sup_decomp hc hu
  obtain ⟨h2, hh2, k2, hk2, rfl⟩ := p16_sup_decomp hc hv
  calc h1 * k1 * (h2 * k2) = h1 * (k1 * h2) * k2 := by simp only [mul_assoc]
    _ = h1 * (h2 * k1) * k2 := by rw [hc h2 hh2 k1 hk1]
    _ = h1 * h2 * (k1 * k2) := by simp only [mul_assoc]
    _ = h2 * h1 * (k2 * k1) := by rw [hH h1 hh1 h2 hh2, hK k1 hk1 k2 hk2]
    _ = h2 * (h1 * k2) * k1 := by simp only [mul_assoc]
    _ = h2 * (k2 * h1) * k1 := by rw [hc h1 hh1 k2 hk2]
    _ = h2 * k2 * (h1 * k1) := by simp only [mul_assoc]

private theorem p16_sup_pow {r : ℕ} {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (hH : ∀ x ∈ H, x ^ r = 1) (hK : ∀ x ∈ K, x ^ r = 1) {u : G} (hu : u ∈ H ⊔ K) :
    u ^ r = 1 := by
  obtain ⟨h, hh, k, hk, rfl⟩ := p16_sup_decomp hc hu
  rw [(show Commute h k from hc h hh k hk).mul_pow, hH h hh, hK k hk, one_mul]

private theorem p16_sup_isElemAbelian {r : ℕ} {H K : Subgroup G}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hHe : ∀ x ∈ H, x ^ r = 1)
    (hKe : ∀ x ∈ K, x ^ r = 1) : IsElemAbelian r (H ⊔ K) :=
  ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (p16_sup_comm hH hK hc a.2 b.2),
    fun _ hx => p16_sup_pow hc hHe hKe hx⟩

private theorem p16_zpow_exp {r : ℕ} {x : G} (hx : x ^ r = 1) (i : ℤ) : (x ^ i) ^ r = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private theorem p16_card_le {r : ℕ} (hr : r.Prime) {R B : Subgroup G}
    (hrank : Open.pRank r R ≤ 3) (hBR : B ≤ R) (hB : IsElemAbelian r B) :
    Nat.card B ≤ r ^ 3 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hpB : IsPGroup r B := by
    refine isPGroup_iff_pow_pow_eq_one.2 fun g => ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hB.2 g.1 g.2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpB
  have hnle : n ≤ Open.pRank r R := le_pRank_of_elemAbelian hr hBR hB hn
  rw [hn]
  exact Nat.pow_le_pow_right hr.pos (hnle.trans hrank)

private theorem p16_iter (E : Subgroup G) (y z0 : G) (a : ℤ) (e₁ : G) (he₁ : e₁ ∈ E)
    (hyE : ∀ f ∈ E, y * f * y⁻¹ = f) (hzc : ∀ f ∈ E, z0 * f = f * z0)
    (ha : y * z0 * y⁻¹ = z0 ^ a * e₁) (k : ℕ) :
    ∃ f ∈ E, y ^ k * z0 * (y ^ k)⁻¹ = z0 ^ (a ^ k) * f := by
  induction k with
  | zero => exact ⟨1, E.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨f, hf, hfk⟩ := ih
    refine ⟨e₁ ^ (a ^ k) * f, E.mul_mem (E.zpow_mem he₁ _) hf, ?_⟩
    have hce : Commute (z0 ^ a) e₁ := (show Commute z0 e₁ from hzc e₁ he₁).zpow_left a
    calc y ^ (k + 1) * z0 * (y ^ (k + 1))⁻¹ = y * (y ^ k * z0 * (y ^ k)⁻¹) * y⁻¹ := by group
      _ = y * (z0 ^ (a ^ k) * f) * y⁻¹ := by rw [hfk]
      _ = (y * z0 ^ (a ^ k) * y⁻¹) * (y * f * y⁻¹) := by group
      _ = (y * z0 * y⁻¹) ^ (a ^ k) * f := by rw [← conj_zpow, hyE f hf]
      _ = (z0 ^ a * e₁) ^ (a ^ k) * f := by rw [ha]
      _ = (z0 ^ a) ^ (a ^ k) * e₁ ^ (a ^ k) * f := by rw [hce.mul_zpow]
      _ = z0 ^ (a ^ (k + 1)) * (e₁ ^ (a ^ k) * f) := by rw [← zpow_mul, pow_succ', mul_assoc]

private theorem p16_conj_gen {r : ℕ} (hr : r.Prime) {E : Subgroup G} {z0 y : G}
    (hz0 : orderOf z0 = r) (hzE : ∀ m : ℤ, z0 ^ m ∈ E → (r : ℤ) ∣ m) {k : ℕ}
    (hyk : y ^ (r ^ k) = 1) (hyE : ∀ f ∈ E, y * f * y⁻¹ = f)
    (hzc : ∀ f ∈ E, z0 * f = f * z0) {a : ℤ} {e₁ : G} (he₁ : e₁ ∈ E)
    (ha : y * z0 * y⁻¹ = z0 ^ a * e₁) : y * z0 * y⁻¹ = z0 * e₁ := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨f, hf, hfk⟩ := p16_iter E y z0 a e₁ he₁ hyE hzc ha (r ^ k)
  simp only [hyk, inv_one, one_mul, mul_one] at hfk
  have hz1 : z0 ^ (a ^ (r ^ k) - 1) = f⁻¹ := by
    have hs : z0 ^ (a ^ (r ^ k)) = z0 * f⁻¹ := eq_mul_inv_of_mul_eq hfk.symm
    have hc' : z0 * f⁻¹ = f⁻¹ * z0 := (show Commute z0 f from hzc f hf).inv_right.eq
    rw [zpow_sub, zpow_one, hs, hc', mul_inv_cancel_right]
  have hdvd : (r : ℤ) ∣ a ^ (r ^ k) - 1 := hzE _ (by rw [hz1]; exact E.inv_mem hf)
  have hZM : (a : ZMod r) ^ (r ^ k) = 1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ (r ^ k) - 1) r).2 hdvd
    push_cast at h
    exact sub_eq_zero.1 h
  have hA1 : (a : ZMod r) = 1 := by
    have h := ZMod.pow_card_pow (n := k) (a : ZMod r)
    rw [hZM] at h
    exact h.symm
  have hdvd1 : (r : ℤ) ∣ a - 1 := by
    have h : ((a - 1 : ℤ) : ZMod r) = 0 := by
      push_cast
      rw [hA1, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
  have hdvd2 : ((orderOf z0 : ℕ) : ℤ) ∣ a - 1 := by
    rw [hz0]
    exact hdvd1
  have hza : z0 ^ a = z0 := by
    have h1 : z0 ^ (a - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hdvd2
    rw [show a = (a - 1) + 1 by ring, zpow_add, h1, one_mul, zpow_one]
  rw [ha, hza]

private theorem p16_fix {R E : Subgroup G} (hER : ∀ e ∈ E, ∀ x ∈ R, e * x = x * e) {x c : G}
    (hx : x ∈ R) (hc : c ∈ E) : x * c * x⁻¹ = c := by
  rw [← hER c hc x hx, mul_inv_cancel_right]

private theorem p16_fix' {R E : Subgroup G} (hER : ∀ e ∈ E, ∀ x ∈ R, e * x = x * e) {x c : G}
    (hx : x ∈ R) (hc : c ∈ E) : x⁻¹ * c * x = c := by
  have h := p16_fix hER (R.inv_mem hx) hc
  rwa [inv_inv] at h

private def p16Good (Z : Subgroup G) {R E : Subgroup G}
    (hER : ∀ e ∈ E, ∀ x ∈ R, e * x = x * e) : Subgroup G where
  carrier := {g | g ∈ R ∧ ∀ z ∈ Z, z * g * z⁻¹ * g⁻¹ ∈ E}
  mul_mem' := by
    rintro g h ⟨hgR, hg⟩ ⟨hhR, hh⟩
    refine ⟨R.mul_mem hgR hhR, fun z hz => ?_⟩
    have key : z * (g * h) * z⁻¹ * (g * h)⁻¹
        = (z * g * z⁻¹ * g⁻¹) * (g * (z * h * z⁻¹ * h⁻¹) * g⁻¹) := by group
    rw [key, p16_fix hER hgR (hh z hz)]
    exact E.mul_mem (hg z hz) (hh z hz)
  one_mem' := ⟨R.one_mem, fun z _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgR, hg⟩
    refine ⟨R.inv_mem hgR, fun z hz => ?_⟩
    have key : z * g⁻¹ * z⁻¹ * g⁻¹⁻¹ = g⁻¹ * (z * g * z⁻¹ * g⁻¹)⁻¹ * g := by group
    rw [key, p16_fix' hER hgR (E.inv_mem (hg z hz))]
    exact E.inv_mem (hg z hz)

private theorem p16Good_iff {Z R E : Subgroup G} (hER : ∀ e ∈ E, ∀ x ∈ R, e * x = x * e)
    (g : G) : g ∈ p16Good Z hER ↔ g ∈ R ∧ ∀ z ∈ Z, z * g * z⁻¹ * g⁻¹ ∈ E := Iff.rfl

theorem p16_core {r : ℕ} (hr : r.Prime) {R E Z : Subgroup G} (hR : IsPGroup r R)
    (hrank : Open.pRank r R ≤ 3)
    (hER : ∀ e ∈ E, ∀ x ∈ R, e * x = x * e) (hER' : E ≤ R)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hZR : Z ≤ R) (hZcard : Nat.card Z = r) (hZE : ¬ Z ≤ E)
    (h69 : ∀ P : Subgroup G, P ≤ R → Z ≤ P →
      (∀ z ∈ Z, ∀ p ∈ P, ∀ q ∈ P, (z * p * z⁻¹ * p⁻¹) * q = q * (z * p * z⁻¹ * p⁻¹)) →
      ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z) :
    (∀ a ∈ Z ⊔ E, ∀ x ∈ R, a * x = x * a) ∧ (∀ x ∈ R, x ^ r = 1 → x ∈ Z ⊔ E) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hAR : Z ⊔ E ≤ R := sup_le hZR hER'
  obtain ⟨z0, hz0Z, hz0⟩ : ∃ z0 ∈ Z, orderOf z0 = r := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r
      (show r ∣ Nat.card Z from ⟨1, by rw [hZcard, mul_one]⟩)
    exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  have hZgen : Z = Subgroup.zpowers z0 :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz0Z)
      (le_of_eq (by rw [Nat.card_zpowers, hz0, hZcard]))).symm
  have hZpow : ∀ z ∈ Z, ∃ i : ℤ, z0 ^ i = z := fun z hz => by
    rw [hZgen] at hz
    exact Subgroup.mem_zpowers_iff.1 hz
  have hz0r : z0 ^ r = 1 := by
    rw [← hz0]
    exact pow_orderOf_eq_one z0
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := hZpow x hx
    obtain ⟨j, rfl⟩ := hZpow y hy
    exact ((Commute.refl z0).zpow_zpow i j).eq
  have hZexp : ∀ x ∈ Z, x ^ r = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := hZpow x hx
    exact p16_zpow_exp hz0r i
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.1 hEel.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hZE_c : ∀ x ∈ Z, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    (hER y hy x (hZR hx)).symm
  have hEexp : ∀ x ∈ E, x ^ r = 1 := fun x hx => hEel.2 x hx
  have hAcomm : ∀ u ∈ Z ⊔ E, ∀ v ∈ Z ⊔ E, u * v = v * u :=
    fun u hu v hv => p16_sup_comm hZcomm hEcomm hZE_c hu hv
  have hAexp : ∀ u ∈ Z ⊔ E, u ^ r = 1 :=
    fun u hu => p16_sup_pow hZE_c hZexp hEexp hu
  have hZEbot : Z ⊓ E = ⊥ := by
    have hd : Nat.card (Z ⊓ E : Subgroup G) ∣ r := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : Z ⊓ E ≤ Z)
      rwa [hZcard] at h
    rcases (Nat.dvd_prime hr).1 hd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have hZ : Z ⊓ E = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hZcard, h1]))
      exact hZE (inf_eq_left.1 hZ)
  have hAcard : Nat.card (Z ⊔ E : Subgroup G) = r ^ 3 := by
    let f : (↥Z × ↥E) → ↥(Z ⊔ E : Subgroup G) := fun p =>
      ⟨p.1.1 * p.2.1, (Z ⊔ E).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
    have hinj : Function.Injective f := by
      rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ h
      have h' : p1 * p2 = q1 * q2 := congrArg Subtype.val h
      have hw : q1⁻¹ * p1 ∈ Z ⊓ E := by
        refine ⟨Z.mul_mem (Z.inv_mem hq1) hp1, ?_⟩
        have e : q1⁻¹ * p1 = q2 * p2⁻¹ := by
          calc q1⁻¹ * p1 = q1⁻¹ * (p1 * p2) * p2⁻¹ := by group
            _ = q1⁻¹ * (q1 * q2) * p2⁻¹ := by rw [h']
            _ = q2 * p2⁻¹ := by group
        rw [e]
        exact E.mul_mem hq2 (E.inv_mem hp2)
      rw [hZEbot, Subgroup.mem_bot] at hw
      have e1 : q1 = p1 := inv_mul_eq_one.1 hw
      subst e1
      have e2 : p2 = q2 := mul_left_cancel h'
      subst e2
      rfl
    have hsurj : Function.Surjective f := by
      rintro ⟨a, ha⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := p16_sup_decomp hZE_c ha
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
    rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩, Nat.card_prod, hZcard, hEcard]
    ring
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G,
      X = R ⊓ Subgroup.centralizer ((Z ⊔ E : Subgroup G) : Set G) := ⟨_, rfl⟩
  have hXmem : ∀ x, x ∈ X ↔ x ∈ R ∧ ∀ a ∈ Z ⊔ E, a * x = x * a := by
    intro x
    simp only [hXdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  have hXle : X ≤ R := by
    rw [hXdef]
    exact inf_le_left
  have hZX : Z ≤ X := fun z hz =>
    (hXmem z).2 ⟨hZR hz, fun c hc => hAcomm c hc z (Subgroup.mem_sup_left hz)⟩
  have hstep2 : ∀ x ∈ X, x ^ r = 1 → x ∈ Z ⊔ E := by
    intro x hxX hx1
    obtain ⟨hxR, hxc⟩ := (hXmem x).1 hxX
    have hxc' : ∀ a ∈ Z ⊔ E, ∀ y ∈ Subgroup.zpowers x, a * y = y * a := by
      intro a ha y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute a x from hxc a ha).zpow_right j).eq
    have hzc : ∀ y ∈ Subgroup.zpowers x, ∀ w ∈ Subgroup.zpowers x, y * w = w * y := by
      intro y hy w hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact ((Commute.refl x).zpow_zpow i j).eq
    have hxe : ∀ w ∈ Subgroup.zpowers x, w ^ r = 1 := by
      intro w hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact p16_zpow_exp hx1 i
    have hBR : (Z ⊔ E) ⊔ Subgroup.zpowers x ≤ R := sup_le hAR (Subgroup.zpowers_le.2 hxR)
    have hB : IsElemAbelian r ((Z ⊔ E) ⊔ Subgroup.zpowers x) :=
      p16_sup_isElemAbelian hAcomm hzc hxc' hAexp hxe
    have hbB := p16_card_le hr hrank hBR hB
    have hEq : Z ⊔ E = (Z ⊔ E) ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hAcard]; exact hbB)
    have hxB : x ∈ (Z ⊔ E) ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [← hEq] at hxB
    exact hxB
  have hXeqR : X = R := by
    by_contra hne
    have hlt : X < R := lt_of_le_of_ne hXle hne
    obtain ⟨-, y, hy, hyX⟩ := SetLike.lt_iff_le_and_exists.1
      (CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer
        r hr R X hR hlt)
    have hyR : y ∈ R := (Subgroup.mem_inf.1 hy).1
    have hyN : y ∈ Subgroup.normalizer (X : Set G) := (Subgroup.mem_inf.1 hy).2
    have hyN' : ∀ w, w ∈ X ↔ y * w * y⁻¹ ∈ X := fun w =>
      Subgroup.mem_set_normalizer_iff.1 hyN w
    have hyA : ∀ a ∈ Z ⊔ E, y * a * y⁻¹ ∈ Z ⊔ E := by
      intro a ha
      refine hstep2 _ ((hyN' a).1 ((hXmem a).2 ⟨hAR ha, fun c hc => hAcomm c hc a ha⟩)) ?_
      rw [conj_pow, hAexp a ha, mul_one, mul_inv_cancel]
    have hyz0A : y * z0 * y⁻¹ ∈ Z ⊔ E := hyA z0 (Subgroup.mem_sup_left hz0Z)
    obtain ⟨h0, hh0, e1, he1, hdec⟩ := p16_sup_decomp hZE_c hyz0A
    obtain ⟨a, rfl⟩ := hZpow h0 hh0
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.1 hR ⟨y, hyR⟩
    have hyk : y ^ (r ^ k) = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    have hzE : ∀ m : ℤ, z0 ^ m ∈ E → (r : ℤ) ∣ m := by
      intro m hm
      have hmZ : z0 ^ m ∈ Z ⊓ E := ⟨Z.zpow_mem hz0Z m, hm⟩
      rw [hZEbot, Subgroup.mem_bot] at hmZ
      have h := orderOf_dvd_iff_zpow_eq_one.2 hmZ
      rwa [hz0] at h
    have hyE : ∀ f ∈ E, y * f * y⁻¹ = f := fun f hf => by
      rw [← hER f hf y hyR, mul_inv_cancel_right]
    have hyz0 : y * z0 * y⁻¹ = z0 * e1 :=
      p16_conj_gen hr hz0 hzE hyk hyE (fun f hf => hZE_c z0 hz0Z f hf) he1 hdec
    have hyS : y ∈ p16Good Z hER := by
      rw [p16Good_iff]
      refine ⟨hyR, fun z hz => ?_⟩
      obtain ⟨i, rfl⟩ := hZpow z hz
      have hf : e1 ^ i ∈ E := E.zpow_mem he1 i
      have hCz : Commute z0 e1 := hZE_c z0 hz0Z e1 he1
      have hconj : y * z0 ^ i * y⁻¹ = z0 ^ i * e1 ^ i := by
        rw [← conj_zpow, hyz0]
        exact hCz.mul_zpow i
      have hC : Commute (z0 ^ i) (e1 ^ i)⁻¹ := (hCz.zpow_zpow i i).inv_right
      have key : z0 ^ i * y * (z0 ^ i)⁻¹ * y⁻¹ = (e1 ^ i)⁻¹ := by
        calc z0 ^ i * y * (z0 ^ i)⁻¹ * y⁻¹ = z0 ^ i * (y * z0 ^ i * y⁻¹)⁻¹ := by group
          _ = z0 ^ i * (z0 ^ i * e1 ^ i)⁻¹ := by rw [hconj]
          _ = z0 ^ i * ((e1 ^ i)⁻¹ * (z0 ^ i)⁻¹) := by rw [mul_inv_rev]
          _ = (z0 ^ i * (e1 ^ i)⁻¹) * (z0 ^ i)⁻¹ := by rw [mul_assoc]
          _ = ((e1 ^ i)⁻¹ * z0 ^ i) * (z0 ^ i)⁻¹ := by rw [hC.eq]
          _ = (e1 ^ i)⁻¹ := by group
      rw [key]
      exact E.inv_mem hf
    have hXS : ∀ x ∈ X, x ∈ p16Good Z hER := by
      intro x hx
      obtain ⟨hxR, hxc⟩ := (hXmem x).1 hx
      rw [p16Good_iff]
      refine ⟨hxR, fun z hz => ?_⟩
      have hzx : z * x = x * z := hxc z (Subgroup.mem_sup_left hz)
      have h1 : z * x * z⁻¹ * x⁻¹ = 1 := by
        rw [hzx]
        group
      rw [h1]
      exact E.one_mem
    have hPS : X ⊔ Subgroup.zpowers y ≤ p16Good Z hER :=
      sup_le hXS (Subgroup.zpowers_le.2 hyS)
    have hPR : X ⊔ Subgroup.zpowers y ≤ R := sup_le hXle (Subgroup.zpowers_le.2 hyR)
    have hZP : Z ≤ X ⊔ Subgroup.zpowers y := le_trans hZX le_sup_left
    have hcomm69 : ∀ z ∈ Z, ∀ p ∈ X ⊔ Subgroup.zpowers y, ∀ q ∈ X ⊔ Subgroup.zpowers y,
        (z * p * z⁻¹ * p⁻¹) * q = q * (z * p * z⁻¹ * p⁻¹) := by
      intro z hz p hp q hq
      have hpE : z * p * z⁻¹ * p⁻¹ ∈ E := ((p16Good_iff hER p).1 (hPS hp)).2 z hz
      exact hER _ hpE q (hPR hq)
    have hZy : ∀ z ∈ Z, z * y = y * z := fun z hz =>
      h69 (X ⊔ Subgroup.zpowers y) hPR hZP hcomm69 z hz y
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    have hyX' : y ∈ X := by
      refine (hXmem y).2 ⟨hyR, fun a ha => ?_⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := p16_sup_decomp hZE_c ha
      calc h * k * y = h * (k * y) := mul_assoc _ _ _
        _ = h * (y * k) := by rw [hER k hk y hyR]
        _ = h * y * k := (mul_assoc _ _ _).symm
        _ = y * h * k := by rw [hZy h hh]
        _ = y * (h * k) := mul_assoc _ _ _
    exact hyX hyX'
  have hXall : ∀ x ∈ R, x ∈ X := fun x hx => by
    rw [hXeqR]
    exact hx
  exact ⟨fun a ha x hx => ((hXmem x).1 (hXall x hx)).2 a ha,
    fun x hx hx1 => hstep2 x (hXall x hx) hx1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6
