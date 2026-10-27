module

public import CFSG.Quasithin.EmptyFaithful.S146zMFit
public import CFSG.Quasithin.EmptyFaithful.S146zLSgn
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.SectionRank
open scoped Pointwise

section Lift

variable {p : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X] [Finite X]

theorem exists_elemAbelian_lift (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {A : Subgroup (X ⧸ N)} (hA : IsElemAbelian p A) {k : ℕ} (hcard : Nat.card A = p ^ k) :
    ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  have hcop : ∀ {k : ℕ}, Nat.Coprime (p ^ k) (Nat.card N) := fun {k} =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  set P : Subgroup X := A.comap (QuotientGroup.mk' N)
  have hPcard : Nat.card P = Nat.card N * p ^ k := by
    rw [← hcard]
    exact QuotientGroup.card_preimage_mk N (A : Set (X ⧸ N))
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p P))
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* X := P.subtype.comp (S : Subgroup P).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  set φ : S →* A := ((QuotientGroup.mk' N).comp ι).codRestrict A fun s => s.1.2
  have hker : ∀ s : S, ι s ∈ N → s = 1 := by
    intro s hs
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup P).map P.subtype)
      (K := N) (by
        rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
        exact hcop)
    have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ N := ⟨⟨s, s.2, rfl⟩, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : (QuotientGroup.mk' N) (ι s) = 1 := congrArg Subtype.val hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Subgroup.mem_bot).2 (hker s h2)
  have hAc := hA.1
  obtain ⟨hcomm, hpow⟩ := comm_pow_of_injective (p := p) hφ (fun a b => mul_comm' _ _)
    (fun a => Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hA.2 _ (φ a).2))
  refine ⟨ι.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨u, hu⟩ := b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← hs, ← hu, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨s, rfl⟩ := hx
    rw [← map_pow, hpow, map_one]
  · rw [← hScard]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm

end Lift

section Sup

variable {p : ℕ} {G : Type*} [Group G]

theorem zmComm {A : Subgroup G} (hA : IsElemAbelian p A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a := CFSG.Open.IsElemAbelian.comm hA ha hb

theorem zmElemAbelian_zpowers {x : G} (hx : x ^ p = 1) : IsElemAbelian p (Subgroup.zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers hx

theorem zmElemAbelian_sup {A B : Subgroup G} (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : IsElemAbelian p (A ⊔ B) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hA hB hc

variable [Finite G]

theorem zmEq_of_orderOf_centralizes [hp : Fact p.Prime] (hr : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) {x : G} (hx : orderOf x = p)
    (hc : ∀ e ∈ E, e * x = x * e) : x ∈ E := by
  by_contra hxE
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hZ := zmElemAbelian_zpowers (p := p) hxp
  have hZc : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hinf : E ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers (x := x) (y := y)).mpr hy.2
    have hn' : x ^ n = y := hn
    have hpn : ¬ p ∣ n := fun hd => by
      obtain ⟨m, rfl⟩ := hd
      apply hy1
      rw [← hn', pow_mul, hxp, one_pow]
    have hcop : Nat.Coprime (orderOf x) n := by
      rw [hx]
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpn
    exact hxE (mem_of_pow_mem_of_coprime hcop (by rw [hn']; exact hy.1))
  have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := fun a ha b hb => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (hc a ha) m).eq)
  have hsup := zmElemAbelian_sup hE hZ hcomm
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (Subgroup.zpowers x) hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, hEc, hZc] at hcard
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank hp.out.one_lt le_top hsup (k := 3) (by rw [hcard]; ring)
  omega

end Sup

section Dec

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_elemAbelian_sq (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∃ E : Subgroup G, E ≤ H ∧ E ≤ oTwoUpper H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₁, hφ₁s, hker₁⟩ := h.exists_phi_gen
  obtain ⟨a₁, ha₁⟩ := hφ₁s (DihedralGroup.r 1)
  obtain ⟨φ₂, hφ₂s, hker₂⟩ := h.swap.exists_phi_gen
  obtain ⟨a₂, ha₂⟩ := hφ₂s (DihedralGroup.r 1)
  have ha₁H : (a₁ : G) ∈ H := h.le (h.le₁ a₁.2)
  have ha₂H : (a₂ : G) ∈ H := h.le (h.le₂ a₂.2)
  have hrot : ∀ {Hi : Subgroup G} (φ : ↥Hi →* DihedralGroup p)
      (hker : ∀ y : ↥Hi, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) (a : ↥Hi),
      φ a = DihedralGroup.r 1 → (a : G) ∉ pCoreOf 2 H ∧ (a : G) ^ p ∈ pCoreOf 2 H := by
    intro Hi φ hker a ha
    refine ⟨fun hQ => ?_, ?_⟩
    · have := (hker a).mpr hQ
      rw [ha] at this
      have h1 : (DihedralGroup.r (1 : ZMod p)) = DihedralGroup.r 0 := this
      exact one_ne_zero (DihedralGroup.r.inj h1)
    · have h1 : φ (a ^ p) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
      simpa using (hker _).mp h1
  obtain ⟨haQ₁, hap₁⟩ := hrot φ₁ hker₁ a₁ ha₁
  obtain ⟨haQ₂, hap₂⟩ := hrot φ₂ hker₂ a₂ ha₂
  set α₁ := piQ H ⟨(a₁ : G), ha₁H⟩ with hα₁
  set α₂ := piQ H ⟨(a₂ : G), ha₂H⟩ with hα₂
  have hα₁ne : α₁ ≠ 1 := fun e => haQ₁ ((piQ_eq_one_iff H _).mp e)
  have hα₂ne : α₂ ≠ 1 := fun e => haQ₂ ((piQ_eq_one_iff H _).mp e)
  have hα₁p : α₁ ^ p = 1 := by
    rw [hα₁, ← map_pow]
    exact (piQ_eq_one_iff H _).mpr (by simpa using hap₁)
  have hα₂p : α₂ ^ p = 1 := by
    rw [hα₂, ← map_pow]
    exact (piQ_eq_one_iff H _).mpr (by simpa using hap₂)
  have hα₁α₂ : α₁ * α₂ = α₂ * α₁ := by
    have h1 : (a₁ : G) * (a₂ : G) * (a₁ : G)⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H :=
      h.comm (Subgroup.commutator_mem_commutator a₁.2 a₂.2)
    exact mul_inv_eq_iff_eq_mul.mp ((cent_iff ha₁H ha₂H).mp h1)
  have hord₁ : orderOf α₁ = p := orderOf_eq_prime hα₁p hα₁ne
  have hord₂ : orderOf α₂ = p := orderOf_eq_prime hα₂p hα₂ne
  have hcomm : ∀ x ∈ Subgroup.zpowers α₁, ∀ y ∈ Subgroup.zpowers α₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute α₁ α₂ from hα₁α₂) m n).eq
  have hinf : Subgroup.zpowers α₁ ⊓ Subgroup.zpowers α₂ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers (x := α₁) (y := y)).mpr hy.1
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers (x := α₂) (y := y)).mpr hy.2
    have hm' : α₁ ^ m = y := hm
    have hn' : α₂ ^ n = y := hn
    have hmn : piQ H ⟨(a₁ : G) ^ m, H.pow_mem ha₁H m⟩ = piQ H ⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ := by
      have e1 : (⟨(a₁ : G) ^ m, H.pow_mem ha₁H m⟩ : ↥H) = ⟨(a₁ : G), ha₁H⟩ ^ m := rfl
      have e2 : (⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) = ⟨(a₂ : G), ha₂H⟩ ^ n := rfl
      rw [e1, e2, map_pow, map_pow, ← hα₁, ← hα₂, hm', hn']
    have hq : ((⟨(a₁ : G) ^ m, H.pow_mem ha₁H m⟩ : ↥H)⁻¹ * ⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) ∈
        (pCoreOf 2 H).subgroupOf H := QuotientGroup.eq.mp hmn
    have hqQ : ((a₁ : G) ^ m)⁻¹ * (a₂ : G) ^ n ∈ pCoreOf 2 H := hq
    have hv₂ : (a₂ : G) ^ n ∈ H₂ := H₂.pow_mem a₂.2 n
    have hv₁ : (a₂ : G) ^ n ∈ H₁ := by
      have e : (a₂ : G) ^ n = (a₁ : G) ^ m * (((a₁ : G) ^ m)⁻¹ * (a₂ : G) ^ n) := by group
      rw [e]
      exact H₁.mul_mem (H₁.pow_mem a₁.2 m) (h.Q₁ hqQ)
    have hvQ : (a₂ : G) ^ n ∈ pCoreOf 2 H := by
      have : (a₂ : G) ^ n ∈ H₁ ⊓ H₂ := ⟨hv₁, hv₂⟩
      rwa [h.inf] at this
    rw [← hn']
    have e3 : α₂ ^ n = piQ H ⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ := by
      have e2 : (⟨(a₂ : G) ^ n, H.pow_mem ha₂H n⟩ : ↥H) = ⟨(a₂ : G), ha₂H⟩ ^ n := rfl
      rw [e2, map_pow]
    rw [e3]
    exact (piQ_eq_one_iff H _).mpr hvQ
  set A := Subgroup.zpowers α₁ ⊔ Subgroup.zpowers α₂ with hA
  have hAel : IsElemAbelian p A :=
    zmElemAbelian_sup (zmElemAbelian_zpowers hα₁p) (zmElemAbelian_zpowers hα₂p) hcomm
  have hAcard : Nat.card A = p ^ 2 := by
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers α₁)
      (Subgroup.zpowers α₂) hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hord₁, hord₂] at hc
    rw [hA, hc]
    ring
  have hQcard : ¬ p ∣ Nat.card ((pCoreOf 2 H).subgroupOf H) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).toEquiv, hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨E₀, hE₀, hE₀c⟩ := exists_elemAbelian_lift ((pCoreOf 2 H).subgroupOf H) hQcard hAel hAcard
  refine ⟨E₀.map H.subtype, Subgroup.map_subtype_le E₀, fun x hx => ?_,
    isElemAbelian_map hE₀ H.subtype, ?_⟩
  · have hxH : x ∈ H := Subgroup.map_subtype_le E₀ hx
    refine mem_oTwoUpper_of_odd hxH ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' : y ^ p = 1 := hE₀.2 y hy
    have hdvd : orderOf (H.subtype y) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hy', map_one]
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) hdvd
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hE₀c]

end Dec

section Struct

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem IsRedCE.exists_pow_eq_one (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) {x : G}
    (hx : x ∈ H) : ∃ a b : ℕ, x ^ (2 ^ a * p ^ b) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTH : T ≤ H := hred.isHTM.1.1
  have hxPT : x ∈ PQ ⊔ T := by rw [← hred.eq]; exact hx
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 (hTH.trans hred.normal) hxPT
  obtain ⟨j, hj⟩ := hred.pSec _ hk
  have hQ2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H
  obtain ⟨i, hi⟩ := hQ2 ⟨_, hj⟩
  have hi' : ((x ^ 2 ^ k) ^ p ^ j) ^ 2 ^ i = 1 := congrArg Subtype.val hi
  refine ⟨k + i, j, ?_⟩
  rw [← hi', ← pow_mul, ← pow_mul, pow_add]
  congr 1
  ring

theorem IsRedCE.prime_dvd_card (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card H) : r = 2 ∨ r = p := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) r hd
  obtain ⟨a, b, hab⟩ := hred.exists_pow_eq_one S x.2
  have h1 : orderOf (x : G) ∣ 2 ^ a * p ^ b := orderOf_dvd_of_pow_eq_one hab
  rw [Subgroup.orderOf_coe, hx] at h1
  rcases (Nat.Prime.dvd_mul hr).1 h1 with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hred.prime).1 (hr.dvd_of_dvd_pow h))

theorem IsRedCE.isSolvable (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) :
    Group.IsSolvable ↥H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hred.prime⟩
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTH : T ≤ H := hred.isHTM.1.1
  set Q := pCoreOf 2 H with hQ
  have hQn : (Q.subgroupOf H).Normal := inferInstance
  let π : ↥H →* ↥H ⧸ Q.subgroupOf H := QuotientGroup.mk' (Q.subgroupOf H)
  have hQ2 : IsPGroup 2 ↥(Q.subgroupOf H) := by
    intro y
    obtain ⟨i, hi⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H) ⟨(y : G), y.2⟩
    have hi' : ((y : ↥H) : G) ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    exact ⟨i, Subtype.ext (Subtype.ext hi')⟩
  have hQs : Group.IsSolvable ↥(Q.subgroupOf H) := by
    have : Group.IsNilpotent ↥(Q.subgroupOf H) := hQ2.isNilpotent
    infer_instance
  set P' : Subgroup (↥H ⧸ Q.subgroupOf H) := (PQ.subgroupOf H).map π with hP'
  have hP'n : P'.Normal := Subgroup.Normal.map (Subgroup.normal_subgroupOf_iff_le_normalizer hred.le
    |>.mpr hred.normal) π (QuotientGroup.mk'_surjective _)
  have hP'p : IsPGroup p ↥P' := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨j, hj⟩ := hred.pSec (y : G) (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨j, Subtype.ext ?_⟩
    show (π y) ^ p ^ j = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hj))
  have hP's : Group.IsSolvable ↥P' := by
    have : Group.IsNilpotent ↥P' := hP'p.isNilpotent
    infer_instance
  have hq2 : IsPGroup 2 ((↥H ⧸ Q.subgroupOf H) ⧸ P') := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H z =>
      induction z using QuotientGroup.induction_on with
      | H y =>
        have hxPT : (y : G) ∈ PQ ⊔ T := by rw [← hred.eq]; exact y.2
        obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 (hTH.trans hred.normal) hxPT
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact ⟨y ^ 2 ^ k, Subgroup.mem_subgroupOf.mpr (by simpa using hk), rfl⟩
  have hq2s : Group.IsSolvable ((↥H ⧸ Q.subgroupOf H) ⧸ P') := by
    have : Group.IsNilpotent ((↥H ⧸ Q.subgroupOf H) ⧸ P') := hq2.isNilpotent
    infer_instance
  have hHs : Group.IsSolvable (↥H ⧸ Q.subgroupOf H) :=
    Group.isSolvable_of_ker_le_range P'.subtype (QuotientGroup.mk' P')
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact Group.isSolvable_of_ker_le_range (Q.subgroupOf H).subtype π
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Struct

end CFSG.Quasithin
