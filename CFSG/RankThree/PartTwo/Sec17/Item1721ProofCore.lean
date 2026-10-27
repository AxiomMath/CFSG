module

public import CFSG.RankThree.PartTwo.Sec17.Item1721ProofTools
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement

namespace TailProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutatorElement_central_mul {Q : Subgroup G} {z x w : G}
    (hz : z ∈ Subgroup.centralizer (Q : Set G)) (hx : x ∈ Q) (hw : w ∈ Q) :
    ⁅z * x, w⁆ = ⁅x, w⁆ := by
  have hxwx : x * w * x⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hx hw) (Q.inv_mem hx)
  have hc : x * w * x⁻¹ * z = z * (x * w * x⁻¹) := Subgroup.mem_centralizer_iff.mp hz _ hxwx
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * w * (z * x)⁻¹ * w⁻¹ = z * (x * w * x⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = x * w * x⁻¹ * z * z⁻¹ * w⁻¹ := by rw [← hc]
    _ = x * w * x⁻¹ * w⁻¹ := by group

omit [Finite G] in
theorem commutatorElement_mul_central {Q : Subgroup G} {z x y : G}
    (hz : z ∈ Subgroup.centralizer (Q : Set G)) (hx : x ∈ Q) (hy : y ∈ Q) :
    ⁅x, z * y⁆ = ⁅x, y⁆ := by
  have hxz : x * z = z * x := Subgroup.mem_centralizer_iff.mp hz x hx
  have hk : x * y * x⁻¹ * y⁻¹ ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx)) (Q.inv_mem hy)
  have hc : x * y * x⁻¹ * y⁻¹ * z = z * (x * y * x⁻¹ * y⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hz _ hk
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (z * y) * x⁻¹ * (z * y)⁻¹ = x * z * y * x⁻¹ * y⁻¹ * z⁻¹ := by group
    _ = z * x * y * x⁻¹ * y⁻¹ * z⁻¹ := by rw [hxz]
    _ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ * z * z⁻¹ := by rw [← hc]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem mem_centralizer_of_commutator_mem {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hZ : ⁅Q, Q⁆ = Q ⊓ Subgroup.centralizer (Q : Set G))
    {f : G} (hf3 : f ^ 3 = 1) (hfQ : f ∈ Subgroup.normalizer (Q : Set G))
    (h : ∀ k : ℤ, ∀ x ∈ Q,
      f ^ k * x * (f ^ k)⁻¹ * x⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G)) :
    f ∈ Subgroup.centralizer (Q : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Q ⊓ Subgroup.centralizer (Q : Set G) with hZdef
  have hCf : Subgroup.centralizer ((Subgroup.zpowers f : Subgroup G) : Set G) =
      Subgroup.centralizer ({f} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hfZ : Z ≤ Subgroup.centralizer ({f} : Set G) := by
    rw [← hZ, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := h 1 x hx
    have h2 := h 1 y hy
    rw [zpow_one] at h1 h2
    have hx' : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
    have hy' : f * y * f⁻¹ = (f * y * f⁻¹ * y⁻¹) * y := by group
    have hconj : f * ⁅x, y⁆ * f⁻¹ = ⁅x, y⁆ := by
      have e1 : f * ⁅x, y⁆ * f⁻¹ = ⁅f * x * f⁻¹, f * y * f⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1, hx', hy', commutatorElement_central_mul h1.2 hx (Q.mul_mem h2.1 hy),
        commutatorElement_mul_central h2.2 hx hy]
    calc ⁅x, y⁆ * f = f * ⁅x, y⁆ * f⁻¹ * f := by rw [hconj]
      _ = f * ⁅x, y⁆ := by group
  have hQf : ⁅Q, Subgroup.zpowers f⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hw := h k x⁻¹ (Q.inv_mem hx)
    set w := f ^ k * x⁻¹ * (f ^ k)⁻¹ * x⁻¹⁻¹ with hwdef
    have hxw : x * w = w * x := Subgroup.mem_centralizer_iff.mp hw.2 x hx
    have e : ⁅x, f ^ k⁆ = x * w * x⁻¹ := by
      rw [commutatorElement_def, hwdef]
      group
    rw [e, hxw, mul_inv_cancel_right]
    exact hw
  have hf3' : IsPGroup 3 (Subgroup.zpowers f) := fun g => ⟨1, Subtype.ext (by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hf3, one_zpow, Subgroup.coe_one])⟩
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    rw [hn] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hfN : Subgroup.zpowers f ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hfQ
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (Subgroup.zpowers f) Q hf3' hQ3 hfN
  have hZf : Z ≤ Subgroup.centralizer ((Subgroup.zpowers f : Subgroup G) : Set G) := by
    rw [hCf]
    exact hfZ
  have hbot : ⁅Q, Subgroup.zpowers f⁆ = ⊥ := by
    rw [← hidem, eq_bot_iff]
    calc ⁅⁅Q, Subgroup.zpowers f⁆, Subgroup.zpowers f⁆ ≤ ⁅Z, Subgroup.zpowers f⁆ :=
          Subgroup.commutator_mono hQf le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZf
      _ ≤ ⊥ := le_rfl
  have hQC : Q ≤ Subgroup.centralizer ({f} : Set G) := by
    rw [← hCf]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hQC hx)

omit [Finite G] in
theorem normalizer_le_normalizer_center (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_map_conj_eq' ?_
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, Sec14.map_conj_centralizer,
    Late.map_conj_eq_of_mem_normalizer hg]

theorem card_map_mk_mul_card {H : Type} [Group H] [Finite H] {Z K : Subgroup H} [Z.Normal]
    (hZK : Z ≤ K) : Nat.card (K.map (QuotientGroup.mk' Z)) * Nat.card Z = Nat.card K := by
  rw [← Subgroup.relIndex_ker K (QuotientGroup.mk' Z), QuotientGroup.ker_mk',
    ← Subgroup.relIndex_mul_card (H := Z) (K := K), inf_eq_left.mpr hZK]

theorem card_map_mk_of_coprime {H : Type} [Group H] [Finite H] {Z K : Subgroup H} [Z.Normal]
    (hcop : Nat.Coprime (Nat.card Z) (Nat.card K)) :
    Nat.card (K.map (QuotientGroup.mk' Z)) = Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card (H := Z) (K := K)
  have h2 : Nat.card (Z ⊓ K : Subgroup H) = 1 := by
    have hd1 : Nat.card (Z ⊓ K : Subgroup H) ∣ Nat.card Z := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card (Z ⊓ K : Subgroup H) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
    exact Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  rw [h2, mul_one] at h1
  rw [← Subgroup.relIndex_ker K (QuotientGroup.mk' Z), QuotientGroup.ker_mk', h1]

theorem le_centralizer_of_extraspecial {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    {Q F : Subgroup G} (hQ : IsPGroup p Q) (hQexp : ∀ x ∈ Q, x ^ p = 1)
    (hQcard : Nat.card Q = p ^ 3) (hZ : ⁅Q, Q⁆ = Q ⊓ Subgroup.centralizer (Q : Set G))
    (hZcard : Nat.card (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) = p)
    (hF3 : ∀ f ∈ F, f ^ 3 = 1) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hF9 : Nat.card F = 9)
    (hFQ : F ≤ Subgroup.normalizer (Q : Set G)) {c s t : G} (hc3 : c ^ 3 = 1)
    (hcF : ∀ f ∈ F, c * f = f * c) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hcC : c ∉ Subgroup.centralizer (Q : Set G))
    (hsQ : s ∈ Subgroup.normalizer (Q : Set G)) (hsc : s * c * s⁻¹ = c⁻¹)
    (hsF : ∀ f ∈ F, s * f * s⁻¹ ∈ F)
    (htQ : t ∈ Subgroup.normalizer (Q : Set G)) (htc : t * c * t⁻¹ = c)
    (htF : ∀ f ∈ F, t * f * t⁻¹ = f⁻¹) :
    F ≤ Subgroup.centralizer (Q : Set G) := by
  set N := Subgroup.normalizer (Q : Set G) with hN
  set Z := Q ⊓ Subgroup.centralizer (Q : Set G) with hZdef
  have hQN : Q ≤ N := Subgroup.le_normalizer
  have hZQ : Z ≤ Q := inf_le_left
  have hZN : Z ≤ N := hZQ.trans hQN
  set Zn := Z.subgroupOf N with hZn
  have : Zn.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).mpr (normalizer_le_normalizer_center Q)
  set π := QuotientGroup.mk' Zn with hπ
  set Qb := (Q.subgroupOf N).map π with hQb
  set Fb := (F.subgroupOf N).map π with hFb
  have hmk_eq_one : ∀ (g : G) (hg : g ∈ N), π ⟨g, hg⟩ = 1 → g ∈ Z := fun g hg h1 => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hmemQb : ∀ (x : G) (hx : x ∈ Q), π ⟨x, hQN hx⟩ ∈ Qb := fun x hx =>
    ⟨⟨x, hQN hx⟩, hx, rfl⟩
  have hQb_iff : ∀ q ∈ Qb, ∃ (x : G) (hx : x ∈ Q), π ⟨x, hQN hx⟩ = q := by
    rintro q ⟨⟨x, hxN⟩, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hFb_iff : ∀ q ∈ Fb, ∃ (f : G) (hf : f ∈ F), π ⟨f, hFQ hf⟩ = q := by
    rintro q ⟨⟨f, hfN⟩, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  have hconj : ∀ (g x : G) (hg : g ∈ N) (hx : x ∈ N),
      π ⟨g, hg⟩ * π ⟨x, hx⟩ * (π ⟨g, hg⟩)⁻¹ = π ⟨g * x * g⁻¹, mul_mem (mul_mem hg hx)
        (inv_mem hg)⟩ := fun g x hg hx => by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  have hbarN : ∀ (g : G) (hg : g ∈ N), π ⟨g, hg⟩ ∈ Subgroup.normalizer (Qb : Set _) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hQb_iff q hq
    rw [SetLike.mem_coe, hconj g x hg (hQN hx)]
    exact hmemQb _ ((Subgroup.mem_normalizer_iff.mp hg x).mp hx)
  have hcomm_of : ∀ (g : G) (hg : g ∈ N), π ⟨g, hg⟩ ∈ Subgroup.centralizer (Qb : Set _) →
      ∀ k : ℤ, ∀ x ∈ Q, g ^ k * x * (g ^ k)⁻¹ * x⁻¹ ∈ Z := by
    intro g hg hC k x hx
    have hgk : g ^ k ∈ N := zpow_mem hg k
    have hCk : π ⟨g ^ k, hgk⟩ ∈ Subgroup.centralizer (Qb : Set _) := by
      have e : (⟨g ^ k, hgk⟩ : ↥N) = (⟨g, hg⟩ : ↥N) ^ k := Subtype.ext (by simp)
      rw [e, map_zpow]
      exact zpow_mem hC k
    have hc := Subgroup.mem_centralizer_iff.mp hCk _ (hmemQb x hx)
    apply hmk_eq_one
    have e : (⟨g ^ k * x * (g ^ k)⁻¹ * x⁻¹, by
        exact mul_mem (mul_mem (mul_mem hgk (hQN hx)) (inv_mem hgk)) (inv_mem (hQN hx))⟩ : ↥N) =
        (⟨g ^ k, hgk⟩ : ↥N) * ⟨x, hQN hx⟩ * (⟨g ^ k, hgk⟩ : ↥N)⁻¹ * (⟨x, hQN hx⟩ : ↥N)⁻¹ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  have hQbe : CFSG.Assembly.IsElemAbelian p Qb := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun q hq => ?_⟩
    · obtain ⟨x, hx, hxa⟩ := hQb_iff a a.2
      obtain ⟨y, hy, hyb⟩ := hQb_iff b b.2
      change (a : ↥N ⧸ Zn) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hmem : ⁅y⁻¹, x⁻¹⁆ ∈ ⁅Q, Q⁆ :=
        Subgroup.commutator_mem_commutator (Q.inv_mem hy) (Q.inv_mem hx)
      rw [hZ] at hmem
      convert hmem using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    · obtain ⟨x, hx, rfl⟩ := hQb_iff q hq
      rw [← map_pow]
      have e : (⟨x, hQN hx⟩ : ↥N) ^ p = 1 := Subtype.ext (by simp [hQexp x hx])
      rw [e, map_one]
  have hQbcard : Nat.card Qb = p ^ 2 := by
    have hZnQ : Zn ≤ Q.subgroupOf N := fun z hz => Subgroup.mem_subgroupOf.mpr
      (hZQ (Subgroup.mem_subgroupOf.mp hz))
    have h1 := card_map_mk_mul_card hZnQ
    have hZn' : Nat.card Zn = p := by
      rw [hZn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, hZcard]
    have hQn' : Nat.card (Q.subgroupOf N) = p ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv, hQcard]
    rw [hZn', hQn', pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos h1
  have hFbcard : Nat.card Fb = 9 := by
    have hFn : Nat.card (F.subgroupOf N) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFQ).toEquiv, hF9]
    have hZn' : Nat.card Zn = p := by
      rw [hZn, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, hZcard]
    rw [hFb, card_map_mk_of_coprime (by
      rw [hZn', hFn, show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp.out Nat.prime_three).mpr hp3)), hFn]
  set cb := π ⟨c, hcQ⟩ with hcb
  set sb := π ⟨s, hsQ⟩ with hsb
  set tb := π ⟨t, htQ⟩ with htb
  have hbar_inv : ∀ (g : G) (hg : g ∈ N), (π ⟨g, hg⟩)⁻¹ = π ⟨g⁻¹, inv_mem hg⟩ := fun g hg => by
    rw [← map_inv]
    rfl
  have hFbN : Fb ≤ Subgroup.normalizer (Qb : Set _) := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := hFb_iff q hq
    exact hbarN f (hFQ hf)
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcb, ← map_pow]
    have e : (⟨c, hcQ⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simp [hc3])
    rw [e, map_one]
  have hcbF : ∀ q ∈ Fb, cb * q = q * cb := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := hFb_iff q hq
    rw [hcb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcF f hf)
  have hcbC : cb ∉ Subgroup.centralizer (Qb : Set _) := fun hC =>
    hcC (mem_centralizer_of_commutator_mem hp3 hQ hZ hc3 hcQ (hcomm_of c hcQ hC))
  have hsbc : sb * cb * sb⁻¹ = cb⁻¹ := by
    rw [hsb, hcb, hconj s c hsQ hcQ, hbar_inv]
    congr 1
    exact Subtype.ext hsc
  have hsbF : ∀ q ∈ Fb, sb * q * sb⁻¹ ∈ Fb := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := hFb_iff q hq
    rw [hsb, hconj s f hsQ (hFQ hf)]
    exact ⟨_, hsF f hf, rfl⟩
  have htbc : tb * cb * tb⁻¹ = cb := by
    rw [htb, hcb, hconj t c htQ hcQ]
    congr 1
    exact Subtype.ext htc
  have htbF : ∀ q ∈ Fb, tb * q * tb⁻¹ = q⁻¹ := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := hFb_iff q hq
    rw [htb, hconj t f htQ (hFQ hf), hbar_inv]
    congr 1
    exact Subtype.ext (htF f hf)
  have hFb3 : ∀ q ∈ Fb, q ^ 3 = 1 := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := hFb_iff q hq
    rw [← map_pow]
    have e : (⟨f, hFQ hf⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simp [hF3 f hf])
    rw [e, map_one]
  have hFbab : ∀ a ∈ Fb, ∀ b ∈ Fb, a * b = b * a := by
    intro a ha b hb
    obtain ⟨f, hf, rfl⟩ := hFb_iff a ha
    obtain ⟨g, hg, rfl⟩ := hFb_iff b hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hFab f hf g hg)
  have hFbC := le_centralizer_of_inverts_two hp3 hQbe hQbcard hFb3 hFbab hFbcard hFbN hcb3
    hcbF (hbarN c hcQ) hcbC (hbarN s hsQ) hsbc hsbF (hbarN t htQ) htbc htbF
  intro f hf
  exact mem_centralizer_of_commutator_mem hp3 hQ hZ (hF3 f hf) (hFQ hf)
    (hcomm_of f (hFQ hf) (hFbC ⟨⟨f, hFQ hf⟩, hf, rfl⟩))

omit [Finite G] in
theorem map_subtype_commutator (Q : Subgroup G) :
    (commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Finite G] in
theorem map_subtype_center (Q : Subgroup G) :
    (Subgroup.center ↥Q).map Q.subtype = Q ⊓ Subgroup.centralizer (Q : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)
  · rintro ⟨hxQ, hxC⟩
    refine ⟨⟨x, hxQ⟩, Subgroup.mem_center_iff.mpr fun z => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxC (z : G) z.2

theorem le_centralizer_of_inverts_pGroup {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {P F : Subgroup G} (hP : IsPGroup p P)
    (hrank : ∀ E : Subgroup G, E ≤ P → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ x ∈ E, x ^ p = 1) → Nat.card E ≤ p ^ 2)
    (hF3 : ∀ f ∈ F, f ^ 3 = 1) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hF9 : Nat.card F = 9)
    (hFP : F ≤ Subgroup.normalizer (P : Set G)) {c s t : G} (hc3 : c ^ 3 = 1)
    (hcF : ∀ f ∈ F, c * f = f * c) (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (hcC : c ∉ Subgroup.centralizer (P : Set G))
    (hsP : s ∈ Subgroup.normalizer (P : Set G)) (hsc : s * c * s⁻¹ = c⁻¹)
    (hsF : ∀ f ∈ F, s * f * s⁻¹ ∈ F)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (htc : t * c * t⁻¹ = c)
    (htF : ∀ f ∈ F, t * f * t⁻¹ = f⁻¹) :
    F ≤ Subgroup.centralizer (P : Set G) := by
  have hPnt : Nontrivial ↥P := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    exact hcC (Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [(Subgroup.mem_bot).mp hx, one_mul, mul_one])
  obtain ⟨D, hDchar, hD1, -, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 (P := ↥P) hP
  set Q := D.map P.subtype with hQdef
  have hQP : Q ≤ P := Subgroup.map_subtype_le D
  have hQp : IsPGroup p Q := hP.to_le hQP
  have hNQ : ∀ g ∈ Subgroup.normalizer (P : Set G), g ∈ Subgroup.normalizer (Q : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨d, hd, rfl⟩ := hx
    set σ := P.normalizerMonoidHom ⟨g, hg⟩ with hσ
    have hσD : D.map σ.toMonoidHom = D := Subgroup.characteristic_iff_map_eq.mp hDchar σ
    have hσd : σ d ∈ D := by
      rw [← hσD]
      exact ⟨d, hd, rfl⟩
    exact ⟨σ d, hσd, Subgroup.normalizerMonoidHom_apply_apply_coe P ⟨g, hg⟩ d⟩
  have hcrit : ∀ a ∈ Subgroup.normalizer (P : Set G), a ^ 3 = 1 →
      a ∈ Subgroup.centralizer (Q : Set G) → a ∈ Subgroup.centralizer (P : Set G) := by
    intro a ha ha3 haQ
    set σ := P.normalizerMonoidHom ⟨a, ha⟩ with hσdef
    have hσfix : σ ∈ fixingSubgroup (MulAut ↥P) (D : Set ↥P) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      rw [MulAut.smul_def, hσdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hda : (d : G) * a = a * d := Subgroup.mem_centralizer_iff.mp haQ (d : G) ⟨d, hd, rfl⟩
      rw [← hda, mul_inv_cancel_right]
    obtain ⟨k, hk⟩ := hDfix ⟨σ, hσfix⟩
    have hσk : σ ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσdef, ← map_pow]
      have e : (⟨a, ha⟩ : Subgroup.normalizer (P : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simp [ha3])
      rw [e, map_one]
    have hσ1 : σ = 1 := by
      have hcop : Nat.Coprime 3 (p ^ k) := Nat.Coprime.pow_right k
        ((Nat.coprime_primes Nat.prime_three hp.out).mpr (Ne.symm hp3))
      have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσ3) (orderOf_dvd_of_pow_eq_one hσk)
      rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
      exact h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥P => ((φ ⟨y, hy⟩ : ↥P) : G)) hσ1
    simp only [MulAut.one_apply] at h1
    rw [hσdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    calc y * a = (a * y * a⁻¹) * a := by rw [h1]
      _ = a * y := by group
  have hQexp : ∀ x ∈ Q, x ^ p = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hDexp d hd, Subgroup.coe_one]
  have hQ1 : Q ≠ ⊥ := by
    rw [hQdef, Ne, Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective]
    exact hD1
  have hFQ : F ≤ Subgroup.normalizer (Q : Set G) := fun f hf => hNQ f (hFP hf)
  have hcQ := hNQ c hcP
  have hsQ := hNQ s hsP
  have htQ := hNQ t htP
  have hcCQ : c ∉ Subgroup.centralizer (Q : Set G) := fun h => hcC (hcrit c hcP hc3 h)
  suffices hFQC : F ≤ Subgroup.centralizer (Q : Set G) from
    fun f hf => hcrit f (hFP hf) (hF3 f hf) (hFQC hf)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hk1 : 1 ≤ k := by
    by_contra h0
    push Not at h0
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hk
    exact hQ1 (Subgroup.card_eq_one.mp hk)
  by_cases hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  ·
    have hQe : CFSG.Assembly.IsElemAbelian p Q :=
      ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hQexp⟩
    have hle := hrank Q hQP hab hQexp
    rw [hk] at hle
    have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hle
    interval_cases k
    · exact le_centralizer_of_inverts_one hQe (by rw [hk, pow_one]) hF3 hFQ htQ htF
    · exact le_centralizer_of_inverts_two hp3 hQe hk hF3 hFab hF9 hFQ hc3 hcF hcQ hcCQ hsQ hsc
        hsF htQ htc htF
  ·
    have hexp' : ∀ x : ↥Q, x ^ p = 1 := fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, hQexp x x.2, Subgroup.coe_one])
    have hcard : p < Nat.card ↥Q := by
      by_contra hle
      push Not at hle
      have hk1' : k = 1 := by
        rw [hk] at hle
        have := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp (by rwa [pow_one] : p ^ k ≤ p ^ 1)
        omega
      rw [hk1', pow_one] at hk
      have : IsCyclic ↥Q := isCyclic_of_prime_card hk
      apply hab
      intro a ha b hb
      exact congrArg Subtype.val
        ((inferInstance : IsMulCommutative ↥Q).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hrk : CFSG.pRank p ↥Q = 2 := by
      refine le_antisymm (pRank_le_of_forall_isMulCommutative hp.out fun E hE => ?_)
        (two_le_pRank hQp hexp' hcard)
      have h := hrank (E.map Q.subtype) ((Subgroup.map_subtype_le E).trans hQP) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg (fun x : ↥Q => (x : G))
          (congrArg Subtype.val (hE.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)))
        (by
          rintro _ ⟨a, ha, rfl⟩
          rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hexp' a, Subgroup.coe_one])
      rwa [Subgroup.card_map_of_injective Q.subtype_injective] at h
    rcases (exponent_prime_rank_two_structure hQp hexp' hrk).1 with ⟨hel, -⟩ |
      ⟨hQ3, hZp, hcz, -⟩
    · exfalso
      apply hab
      intro a ha b hb
      exact congrArg Subtype.val (hel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · have hZ : ⁅Q, Q⁆ = Q ⊓ Subgroup.centralizer (Q : Set G) := by
        rw [← map_subtype_commutator, hcz, map_subtype_center]
      have hZcard : Nat.card (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) = p := by
        rw [← map_subtype_center, Subgroup.card_map_of_injective Q.subtype_injective, hZp]
      exact le_centralizer_of_extraspecial hp3 hQp hQexp hQ3 hZ hZcard hF3 hFab hF9 hFQ hc3 hcF
        hcQ hcCQ hsQ hsc hsF htQ htc htF

end TailProof

end CFSG.RankThree.PartTwo.Sec17
