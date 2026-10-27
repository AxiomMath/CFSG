module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Setup
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.AGLEmbeddingD2.E9TwoGroup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open CFSG.AGLEmbeddingD2.E9TwoGroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma inf_X_A_eq_bot {X A : Subgroup G} (hXA : XReg49 X A) : X ⊓ A = ⊥ := by
  by_contra hne
  have hcardX : Nat.card X = 3 := hXA.1
  have hle : X ≤ A := by
    have hdvd : Nat.card ↥(X ⊓ A) ∣ 3 := by
      rw [← hcardX]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
    · have heq : X ⊓ A = X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcardX])
      exact heq ▸ inf_le_right
  have hcomm : A ≤ Subgroup.centralizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (congrArg Subtype.val (hXA.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨x, hle hx⟩)).symm
  have hcard : Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set G)) = 27 := by
    rw [inf_eq_left.mpr hcomm, hXA.2.2.1]
  have h3 : Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set G)) = 3 := hXA.2.2.2.2
  omega

private lemma le_normalizer_Z49 {X A : Subgroup G} (hXA : XReg49 X A) :
    X ≤ Subgroup.normalizer (Z49 X A : Set G) := by
  have hXN : X ≤ Subgroup.normalizer (A : Set G) := hXA.2.2.2.1
  have hXC : X ≤ Subgroup.normalizer ((Subgroup.centralizer (X : Set G)) : Set G) :=
    ((Subgroup.le_centralizer_iff (H := X) (K := Subgroup.centralizer (X : Set G))).mpr
        le_rfl).trans (Subgroup.centralizer_le_normalizer
          ((Subgroup.centralizer (X : Set G)) : Set G))
  exact (le_inf hXN hXC).trans
    (Subgroup.inf_normalizer_le_normalizer_inf (H := A)
      (K := Subgroup.centralizer (X : Set G)))

private lemma inf_X_Z49_eq_bot {X A : Subgroup G} (hXA : XReg49 X A) :
    X ⊓ Z49 X A = ⊥ := by
  change X ⊓ (A ⊓ Subgroup.centralizer (X : Set G)) = ⊥
  rw [← inf_assoc, inf_X_A_eq_bot hXA, bot_inf_eq]

private lemma card_sup_eq_mul_of_inf_eq_bot {H K : Subgroup G}
    (hK : H ≤ Subgroup.normalizer (K : Set G)) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hcarrier : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H K hK
  have hbij : Function.Bijective (fun p : H × K =>
      (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem _
        (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
        (H ⊔ K : Subgroup G))) := by
    constructor
    · rintro ⟨h1, k1⟩ ⟨h2, k2⟩ heq
      have heq' : (h1 : G) * k1 = (h2 : G) * k2 := congrArg Subtype.val heq
      have hmem : (h2 : G)⁻¹ * h1 ∈ H ⊓ K := by
        refine ⟨H.mul_mem (H.inv_mem h2.2) h1.2, ?_⟩
        have h4 : (h2 : G)⁻¹ * h1 * k1 = k2 := by
          rw [mul_assoc, heq', inv_mul_cancel_left]
        have h3 : (h2 : G)⁻¹ * h1 = k2 * (↑k1)⁻¹ := by
          have h5 := congrArg (fun t : G => t * (↑k1)⁻¹) h4
          rw [mul_assoc, mul_inv_cancel, mul_one] at h5
          exact h5
        rw [h3]
        simpa using K.mul_mem k2.2 (K.inv_mem k1.2)
      rw [hinf] at hmem
      have hh : (h1 : G) = h2 := by
        exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem)).symm
      have hk : (k1 : G) = k2 := by
        rw [hh] at heq'
        exact mul_left_cancel heq'
      exact Prod.ext (Subtype.ext hh) (Subtype.ext hk)
    · intro t
      have ht : (t : G) ∈ (H : Set G) * (K : Set G) := by
        rw [← hcarrier]
        exact t.2
      obtain ⟨h, hh, k, hk, hkeq⟩ := Set.mem_mul.mp ht
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hkeq⟩
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

private lemma orderOf_eq_three_of_mem {H : Subgroup G} {x : G} (hcard : Nat.card H = 3)
    (hxH : x ∈ H) (hx1 : x ≠ 1) : orderOf x = 3 := by
  have hdvd : orderOf x ∣ 3 := by
    rw [← hcard]
    simpa [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨x, hxH⟩ : H)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h3

private lemma eq_zpowers_of_mem_of_card {H : Subgroup G} {x : G} (hcard : Nat.card H = 3)
    (hxH : x ∈ H) (hx3 : orderOf x = 3) : H = Subgroup.zpowers x := by
  refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers x) (K := H)
    (Subgroup.zpowers_le.mpr hxH) ?_).symm
  rw [Nat.card_zpowers, hx3, hcard]

private lemma isInvariant_Z49_subgroupOf {X A : Subgroup G} (hXA : XReg49 X A)
    [Fact (X ≤ Subgroup.normalizer (A : Set G))] :
    CFSG.IsInvariant ↥X ↥A ((Z49 X A).subgroupOf A) := by
  refine CFSG.SolvableHall.isInvariant_of_forall_smul_mem ?_
  intro y z hz
  rw [Subgroup.mem_subgroupOf] at hz ⊢
  rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_Z49 hXA y.2) (z : G)).mp hz

private lemma dvd_card_quotient_Z49_subgroupOf {X A : Subgroup G} (hXA : XReg49 X A) :
    3 ∣ Nat.card (↥A ⧸ (Z49 X A).subgroupOf A) := by
  set Z : Subgroup G := Z49 X A with hZdef
  have hZle : Z ≤ A := inf_le_left
  have hZcard : Nat.card Z = 3 := hXA.2.2.2.2
  have hri : Z.relIndex A * Nat.card ↥(Z ⊓ A) = Nat.card A :=
    Subgroup.relIndex_mul_card (H := Z) (K := A)
  rw [inf_eq_left.mpr hZle, hZcard, hXA.2.2.1] at hri
  have h9 : Z.relIndex A = 9 := by omega
  have : Nat.card (↥A ⧸ (Z49 X A).subgroupOf A) = Z.relIndex A := rfl
  rw [this, h9]
  norm_num

private lemma exists_fixed_coset {X A : Subgroup G} (hXA : XReg49 X A) (x : G) (hxX : x ∈ X) :
    ∃ a : ↥A, (a : G) ∉ Z49 X A ∧
      x * (a : G) * x⁻¹ * (a : G)⁻¹ ∈ Z49 X A := by
  classical
  set Z : Subgroup G := Z49 X A with hZdef
  haveI : Fact (X ≤ Subgroup.normalizer (A : Set G)) := ⟨hXA.2.2.2.1⟩
  let Z' : Subgroup ↥A := Z.subgroupOf A
  haveI hZ'n : Z'.Normal := by
    haveI : IsMulCommutative ↥A := hXA.2.1.1
    exact Subgroup.normal_of_isMulCommutative Z'
  have hZ'inv : CFSG.IsInvariant ↥X ↥A Z' := isInvariant_Z49_subgroupOf hXA
  letI : MulDistribMulAction ↥X (↥A ⧸ Z') :=
    quotientMulDistribMulAction (A := ↥X) (G := ↥A) Z' hZ'inv
  letI : MulAction.QuotientAction ↥X Z' :=
    CFSG.quotientAction_of_isInvariant (A := ↥X) Z' hZ'inv
  have hXp : IsPGroup 3 ↥X := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hXA.1)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card (↥A ⧸ Z') := dvd_card_quotient_Z49_subgroupOf hXA
  obtain ⟨q, hqfix, hqne⟩ := IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (p := 3) (G := ↥X) hXp (α := ↥A ⧸ Z') h3dvd (a := (1 : ↥A ⧸ Z'))
    (by intro y; rw [smul_one])
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have haZ : (a : G) ∉ Z := by
    intro hz
    exact hqne (by
      rw [eq_comm, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hz)
  refine ⟨a, haZ, ?_⟩
  have hfixx := hqfix ⟨x, hxX⟩
  rw [MulAction.Quotient.smul_coe] at hfixx
  have hdiv : ((⟨x, hxX⟩ : ↥X) • a / a : ↥A) ∈ Z' :=
    (QuotientGroup.eq_iff_div_mem).mp hfixx
  rw [div_eq_mul_inv, Subgroup.mem_subgroupOf] at hdiv
  simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using hdiv

private lemma exists_conj_eq_mul {X A : Subgroup G} (hXA : XReg49 X A) {x : G}
    (hxX : x ∈ X) (hx1 : x ≠ 1) :
    ∃ h ∈ A, ∃ z ∈ Z49 X A, z ≠ 1 ∧ h⁻¹ * x * h = x * z := by
  classical
  set Z : Subgroup G := Z49 X A with hZdef
  have hZle : Z ≤ A := inf_le_left
  have hx3 : orderOf x = 3 := orderOf_eq_three_of_mem hXA.1 hxX hx1
  have hXeq : X = Subgroup.zpowers x := eq_zpowers_of_mem_of_card hXA.1 hxX hx3
  obtain ⟨a, haZ, hcomm⟩ := exists_fixed_coset hXA x hxX
  set w : G := x * (a : G) * x⁻¹ * (a : G)⁻¹ with hwdef
  have hwZ : w ∈ Z := hcomm
  have hw1 : w ≠ 1 := by
    intro h1
    apply haZ
    have hconja : x * (a : G) * x⁻¹ = (a : G) := by
      have h2 := congrArg (fun t => t * (a : G)) h1
      rw [hwdef] at h2
      simpa [mul_assoc] using h2
    have hax : (a : G) * x = x * (a : G) := by
      have h2 := congrArg (fun t => t * x) hconja
      simpa [mul_assoc] using h2.symm
    have hmemC : (a : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [hXeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hax
    exact Subgroup.mem_inf.mpr ⟨a.2, hmemC⟩
  have hwa : w * (a : G) = (a : G) * w :=
    congrArg Subtype.val (hXA.2.1.1.is_comm.comm ⟨w, hZle hwZ⟩ ⟨(a : G), a.2⟩)
  have hwx : w * x = x * w :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwZ).2 x hxX).symm
  have hrel : x * (a : G) * x⁻¹ = w * (a : G) := by
    rw [hwdef]
    group
  have hxa : x * (a : G) = (a : G) * x * w := by
    calc x * (a : G) = (x * (a : G) * x⁻¹) * x := by group
      _ = (w * (a : G)) * x := by rw [hrel]
      _ = w * (a : G) * x := by group
      _ = (a : G) * w * x := by rw [hwa]
      _ = (a : G) * (w * x) := by group
      _ = (a : G) * (x * w) := by rw [hwx]
      _ = (a : G) * x * w := by group
  have hconj : (a : G)⁻¹ * x * (a : G) = x * w := by
    calc (a : G)⁻¹ * x * (a : G) = (a : G)⁻¹ * (x * (a : G)) := by group
      _ = (a : G)⁻¹ * ((a : G) * x * w) := by rw [hxa]
      _ = x * w := by group
  exact ⟨(a : G), a.2, w, hwZ, hw1, hconj⟩

private lemma card_inf_centralizer_diag {A X Q : Subgroup G} (hXA : XReg49 X A)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) {x w h : G} (hhA : h ∈ A) (hwA : w ∈ A)
    (hconj : h⁻¹ * x * h = x * w) (hw3 : orderOf w = 3) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({x * w} : Set G)) =
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x * w⁻¹} : Set G)) =
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have h1 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({x * w} : Set G)) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hg : (h⁻¹ : G) ∈ Subgroup.normalizer (Q : Set G) := Subgroup.inv_mem _ (hAQ hhA)
    have hc := card_inf_centralizer_conj Q (g := h⁻¹) hg x
    rw [inv_inv, hconj] at hc
    exact hc
  have hhw : Commute h w :=
    congrArg Subtype.val (hXA.2.1.1.is_comm.comm ⟨h, hhA⟩ ⟨w, hwA⟩)
  have hwh : h⁻¹ * w * h = w := hhw.inv_mul_cancel
  have hw2 : w * w = w⁻¹ := by
    have h3 : w ^ 3 = 1 := by simpa [hw3] using pow_orderOf_eq_one w
    have h4 : w ^ 2 * w = 1 := by rw [← pow_succ, h3]
    have h5 : w ^ 2 = w⁻¹ := eq_inv_of_mul_eq_one_left h4
    rwa [pow_two] at h5
  have h2rel : h⁻¹ * h⁻¹ * x * (h * h) = x * w⁻¹ := by
    calc h⁻¹ * h⁻¹ * x * (h * h)
        = h⁻¹ * (h⁻¹ * x * h) * h := by group
      _ = h⁻¹ * (x * w) * h := by rw [hconj]
      _ = (h⁻¹ * x * h) * (h⁻¹ * w * h) := by group
      _ = (x * w) * w := by rw [hconj, hwh]
      _ = x * (w * w) := by group
      _ = x * w⁻¹ := by rw [hw2]
  have h2 : Nat.card ↥(Q ⊓ Subgroup.centralizer ({x * w⁻¹} : Set G)) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have hg : (h⁻¹ * h⁻¹ : G) ∈ Subgroup.normalizer (Q : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAQ hhA)) (Subgroup.inv_mem _ (hAQ hhA))
    have hc := card_inf_centralizer_conj Q (g := h⁻¹ * h⁻¹) hg x
    rw [mul_inv_rev, inv_inv, h2rel] at hc
    exact hc
  exact ⟨h1, h2⟩

private lemma exists_order_three_gen_Z49 {X A : Subgroup G} (hXA : XReg49 X A) :
    ∃ x ∈ X, ∃ w ∈ Z49 X A, ∃ h ∈ A, x ≠ 1 ∧ orderOf x = 3 ∧ orderOf w = 3 ∧
      w ∉ Subgroup.zpowers x ∧ h⁻¹ * x * h = x * w := by
  classical
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    have hne : X ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card X = 1 := by rw [hbot, Subgroup.card_bot]
      exact absurd (hXA.1.symm.trans h1) (by norm_num)
    obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, hxX, fun h => hx1 (Subtype.ext h)⟩
  have hx3 : orderOf x = 3 := orderOf_eq_three_of_mem hXA.1 hxX hx1
  have hXeq : X = Subgroup.zpowers x := eq_zpowers_of_mem_of_card hXA.1 hxX hx3
  obtain ⟨h, hhA, w, hwZ, hw1, hconj⟩ := exists_conj_eq_mul hXA hxX hx1
  have hw3 : orderOf w = 3 :=
    orderOf_eq_three_of_mem (H := Z49 X A) hXA.2.2.2.2 hwZ hw1
  have hwnot : w ∉ Subgroup.zpowers x := by
    rw [← hXeq]
    intro hwX
    have hmem : w ∈ X ⊓ Z49 X A := Subgroup.mem_inf.mpr ⟨hwX, hwZ⟩
    rw [show X ⊓ Z49 X A = ⊥ from inf_X_Z49_eq_bot hXA] at hmem
    exact hw1 (Subgroup.mem_bot.mp hmem)
  exact ⟨x, hxX, w, hwZ, h, hhA, hx1, hx3, hw3, hwnot, hconj⟩

private lemma sup_Z49_card_nine {X A : Subgroup G} (hXA : XReg49 X A) :
    Nat.card ↥(X ⊔ Z49 X A) = 9 := by
  rw [card_sup_eq_mul_of_inf_eq_bot (le_normalizer_Z49 hXA) (inf_X_Z49_eq_bot hXA),
    hXA.1, hXA.2.2.2.2]

private lemma sup_Z49_le_normalizer {X A Q : Subgroup G}
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    X ⊔ Z49 X A ≤ Subgroup.normalizer (Q : Set G) :=
  sup_le hXQ fun z hz => hAQ (Subgroup.mem_inf.mp hz).1

private lemma coprime_card_three_of_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    Nat.Coprime (Nat.card Q) 3 := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_left n (by norm_num)

private lemma isSolvable_of_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    Group.IsSolvable Q := by
  have := hQ.isNilpotent
  infer_instance

theorem count49 {X A Q : Subgroup G} (hXA : XReg49 X A)
    (hQ : IsPGroup 2 Q) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    Nat.card Q * Nat.card ↥(Q ⊓ Subgroup.centralizer ((X ⊔ Z49 X A : Subgroup G) : Set G)) ^ 3 =
      Nat.card ↥(Q ⊓ Subgroup.centralizer (Z49 X A : Set G)) *
        Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) ^ 3 := by
  classical
  let Z : Subgroup G := Z49 X A
  let E : Subgroup G := X ⊔ Z
  change Nat.card Q * Nat.card ↥(Q ⊓ Subgroup.centralizer (E : Set G)) ^ 3 =
    Nat.card ↥(Q ⊓ Subgroup.centralizer (Z : Set G)) *
      Nat.card ↥(Q ⊓ Subgroup.centralizer (X : Set G)) ^ 3
  obtain ⟨x, hxX, w, hwZ, h, hhA, hx1, hx3, hw3, hwnot, hconj⟩ :=
    exists_order_three_gen_Z49 hXA
  have hxE : x ∈ E := by
    rw [show E = X ⊔ Z from rfl]
    exact Subgroup.mem_sup_left hxX
  have hwE : w ∈ E := by
    rw [show E = X ⊔ Z from rfl]
    exact Subgroup.mem_sup_right hwZ
  have hEcard : Nat.card E = 9 := by
    rw [show E = X ⊔ Z from rfl]
    exact sup_Z49_card_nine hXA
  have hcop : Nat.Coprime (Nat.card Q) 3 := coprime_card_three_of_isPGroup_two hQ
  have hsolv : Group.IsSolvable Q := isSolvable_of_isPGroup_two hQ
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := by
    rw [show E = X ⊔ Z from rfl]
    exact sup_Z49_le_normalizer hXQ hAQ
  have hid := card_mul_card_inf_centralizer_pow_three Q E hEQ hcop hsolv hEcard hxE hwE
    hx3 hw3 hwnot
  obtain ⟨h1, h2⟩ := card_inf_centralizer_diag hXA hAQ hhA
    (Subgroup.mem_inf.mp hwZ).1 hconj hw3
  rw [h1, h2] at hid
  have hcx : Subgroup.centralizer (X : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rw [eq_zpowers_of_mem_of_card hXA.1 hxX hx3, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  have hcz : Subgroup.centralizer (Z : Set G) = Subgroup.centralizer ({w} : Set G) := by
    rw [show Z = Subgroup.zpowers w from
        eq_zpowers_of_mem_of_card hXA.2.2.2.2 hwZ hw3,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcx, ← hcz] at hid
  rw [hid]
  ring

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
