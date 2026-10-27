module

public import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProof
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSwapW
import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSwap
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec11.Item118

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Statements

@[expose] def Step1119SymTypes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype →
      (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (A : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      r * a = a * r → s * a = a * s →
      ¬ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} →
      (∃ h ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
        h * c * h⁻¹ ∈ A ∧ h * c * h⁻¹ ∉ Subgroup.closure ({c, d} : Set G)) →
      ∃ f ∈ A, f ∉ Subgroup.closure ({a, d} : Set G) ∧
        Subgroup.closure ({f, d} : Set G) ≤ Y ∧
        Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {f, d} : Subgroup G) : Set G) ∧
        ∀ f' ∈ Subgroup.closure ({f, d} : Set G), f' ∉ Subgroup.zpowers d →
          ∀ Y' ∈ thetaComponentsAt 3 f', sec11K L f' ≤ Y' → KFacts.InducesStdKind Y' c .field

end Statements

namespace Item1117Res5Proof

section Group

variable {G : Type} [Group G]

theorem mem_of_pow_mem_of_pow_three_mem {M : Subgroup G} {x : G} {n : ℕ} (hn : ¬ 3 ∣ n)
    (hxn : x ^ n ∈ M) (hx3 : x ^ 3 ∈ M) : x ∈ M := by
  obtain ⟨q, hq | hq⟩ : ∃ q, n = 3 * q + 1 ∨ n = 3 * q + 2 := ⟨n / 3, by omega⟩
  · have e : x = ((x ^ 3) ^ q)⁻¹ * x ^ n := by
      rw [hq, pow_add, pow_mul, pow_one, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact M.mul_mem (M.inv_mem (M.pow_mem hx3 q)) hxn
  · have e : x = ((x ^ 3) ^ (2 * q + 1))⁻¹ * (x ^ n) ^ 2 := by
      rw [hq, ← pow_mul, ← pow_mul, show (3 * q + 2) * 2 = 3 * (2 * q + 1) + 1 by ring, pow_add,
        pow_one, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact M.mul_mem (M.inv_mem (M.pow_mem hx3 _)) (M.pow_mem hxn 2)

end Group

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem not_inducesOuterTheta_of_mem {x : G} {L : Subgroup G} (hx : x ∈ L) :
    ¬ Sec4.InducesOuterTheta x L := by
  rintro ⟨hxN, hout⟩
  apply hout
  have h1 := thetaQuotMulAut_compAction_of_mem L hx
  have h2 : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨x, Subgroup.le_normalizer hx⟩ := rfl
  rw [h2, h1]
  exact ⟨_, rfl⟩

theorem exists_mem_closure_ca (h : Sec11Data G A c L a R Y d x s r g) {f : G} (hf : f ∈ A) :
    ∃ k : ℤ, ∃ f₀ ∈ Subgroup.closure ({c, a} : Set G), f = d ^ k * f₀ := by
  have hdA := Item1117Proof.d_mem_A h
  have hdc : d * c = c * d := Item1117Proof.commute_of_mem_A h hdA h.mem_A
  have hda : d * a = a * d := Item1117Proof.commute_of_mem_A h hdA h.a_mem
  have hdN : d ∈ Subgroup.normalizer
      ((Subgroup.closure ({c, a} : Set G) : Subgroup G) : Set G) := by
    have hle : Subgroup.closure ({c, a} : Set G) ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hdc.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hda.symm
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, ← Subgroup.mem_centralizer_singleton_iff.mp (hle hz), mul_inv_cancel_right]
    exact hz
  have hle : A ≤ Subgroup.zpowers d ⊔ Subgroup.closure ({c, a} : Set G) := by
    rw [h.closure_eq, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  exact Item1119Proof.exists_zpow_mul_of_mem_sup hdN (hle hf)

theorem sec11K_eq_of_mem_closure (h : Sec11Data G A c L a R Y d x s r g) {f₀ : G}
    (hf₀ : f₀ ∈ Subgroup.closure ({c, a} : Set G))
    (hf₀cd : f₀ ∉ Subgroup.closure ({c, d} : Set G)) : sec11K L f₀ = sec11K L a := by
  have hca : c * a = a * c := Item1117Proof.commute_of_mem_A h h.mem_A h.a_mem
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hca hf₀
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hj : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨j', rfl⟩
    apply hf₀cd
    rw [zpow_mul, show a ^ (3 : ℤ) = a ^ (3 : ℕ) by norm_cast, ha3, one_zpow, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i
  have haj : a ∈ Subgroup.zpowers (a ^ j) :=
    Item1116Proof.mem_zpowers_zpow_of_not_dvd ⟨1, by rw [pow_one, ha3]⟩ hj
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have key : L ⊓ Subgroup.centralizer ({c ^ i * a ^ j} : Set G) =
      L ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hl, hlf⟩
      refine ⟨hl, ?_⟩
      have hlc : Commute l c := Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
      have hlf' : Commute l (c ^ i * a ^ j) := hlf
      have hlaj : Commute l (a ^ j) := by
        have e : a ^ j = (c ^ i)⁻¹ * (c ^ i * a ^ j) := by group
        rw [e]
        exact (hlc.zpow_right i).inv_right.mul_right hlf'
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp haj
      rw [← hm]
      exact (hlaj.zpow_right m).eq
    · rintro ⟨hl, hla⟩
      refine ⟨hl, ?_⟩
      have hlc : Commute l c := Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
      have hla' : Commute l a := hla
      exact ((hlc.zpow_right i).mul_right (hla'.zpow_right j)).eq
  unfold sec11K
  rw [key]

theorem x_pow_three_commute_of_mem_A (h : Sec11Data G A c L a R Y d x s r g) {v : G}
    (hv : v ∈ A) : x ^ 3 * v = v * x ^ 3 := by
  obtain ⟨z, hz, hxz⟩ := Item1117Proof.exists_conj_of_mem_A h hv
  have hzA : z ∈ A := Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_A h) hz
  have hvz : v * z = z * v := Item1117Proof.commute_of_mem_A h hv hzA
  have hxz' : x * z = z * x := (Item1117Proof.commute_x_of_mem_zpowers_d h hz).eq
  have hj : x * v * x⁻¹ = v * z ^ (1 : ℤ) := by rw [zpow_one, hxz]
  have h3 := conj_zpow_eq_of_conj_eq hvz hxz' hj 3
  have hz3 : z ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact h.mem_partTwoF.1.2 z hzA
  rw [show ((3 : ℕ) : ℤ) * 1 = 3 by norm_num, hz3, mul_one] at h3
  calc x ^ 3 * v = (x ^ 3 * v * (x ^ 3)⁻¹) * x ^ 3 := by group
    _ = v * x ^ 3 := by rw [h3]

theorem exists_mul_pow_mem_inf_of_not_commute (h45 : Sec4.Item4_5) (h113 : Item113)
    (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) (hge : g * e ≠ e * g) :
    ∃ n : ℕ, ¬ 3 ∣ n ∧ g * x ^ n ∈ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) := by
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hzd : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := Item1117StepsProof.conj_x_e_mem h he
  set z := x * e * x⁻¹ * e⁻¹ with hz
  have hz1 : z ≠ 1 := by
    intro h1
    apply Item1117StepsProof.not_commute_x_e h45 h he hecd
    calc x * e = z * (e * x) := by rw [hz]; group
      _ = e * x := by rw [h1, one_mul]
  have hz3 : orderOf z = 3 := by
    have h1 := orderOf_dvd_of_mem_zpowers hzd
    rw [Item1117Proof.orderOf_d h] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h1
  have hzz : Subgroup.zpowers z = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzd)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, Item1117Proof.orderOf_d h])
  have hzA : z ∈ A := Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_A h) hzd
  have hez : e * z = z * e := Item1117Proof.commute_of_mem_A h he hzA
  have hxz : x * z = z * x := (Item1117Proof.commute_x_of_mem_zpowers_d h hzd).eq
  have hxe : x * e * x⁻¹ = e * z ^ (1 : ℤ) := by rw [zpow_one, hez, hz]; group
  have hw := Item1117Proof.conj_g_mem_of_mem_A h117 h he
  rw [← hzz] at hw
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr hw
  have hk' : z ^ k = g * e * g⁻¹ * e⁻¹ := hk
  have hk3 : ¬ 3 ∣ k := by
    rintro ⟨k', rfl⟩
    apply hge
    have h1 : g * e * g⁻¹ * e⁻¹ = 1 := by
      rw [← hk', pow_mul, ← hz3, pow_orderOf_eq_one, one_pow]
    calc g * e = (g * e * g⁻¹ * e⁻¹) * (e * g) := by group
      _ = e * g := by rw [h1, one_mul]
  refine ⟨2 * k, fun h3 => hk3 ((Nat.Coprime.dvd_mul_left (by norm_num)).mp h3),
    Subgroup.mem_inf.mpr ⟨(sec11P R g).mul_mem hgP ((sec11P R g).pow_mem hxP _), ?_⟩⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := conj_zpow_eq_of_conj_eq hez hxz hxe (2 * k)
  rw [mul_one, zpow_natCast] at h1
  have hgz : g * z ^ (2 * k) * g⁻¹ = z ^ (2 * k) := by
    have hzk : z ^ (2 * k) ∈ Subgroup.zpowers d :=
      hzz ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers z) (2 * k)
    rw [Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hzk hgP, mul_inv_cancel_right]
  have hz3' : z ^ (3 * k) = 1 := by rw [pow_mul, ← hz3, pow_orderOf_eq_one, one_pow]
  have hconj : g * x ^ (2 * k) * e * (g * x ^ (2 * k))⁻¹ = e := by
    calc g * x ^ (2 * k) * e * (g * x ^ (2 * k))⁻¹
        = g * (x ^ (2 * k) * e * (x ^ (2 * k))⁻¹) * g⁻¹ := by group
      _ = (g * e * g⁻¹) * (g * z ^ (2 * k) * g⁻¹) := by rw [h1]; group
      _ = (g * e * g⁻¹ * e⁻¹) * e * z ^ (2 * k) := by rw [hgz]; group
      _ = z ^ k * e * z ^ (2 * k) := by rw [hk']
      _ = e * (z ^ k * z ^ (2 * k)) := by
        rw [((Commute.pow_left hez.symm k)).eq]; group
      _ = e := by rw [← pow_add, show k + 2 * k = 3 * k by ring, hz3', mul_one]
  calc g * x ^ (2 * k) * e = (g * x ^ (2 * k) * e * (g * x ^ (2 * k))⁻¹) * (g * x ^ (2 * k)) :=
        by group
    _ = e * (g * x ^ (2 * k)) := by rw [hconj]

theorem isSylowOf_of_swap (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) (h : Sec11Data G A c L a R Y d x s r g) {e : G}
    (heA : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'') {w : G}
    (hwT : w ∈ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) (hwc : w * c ≠ c * w) :
    IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G))
      (Subgroup.normalizer (Subgroup.zpowers e : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) with hT
  set CA := Subgroup.centralizer (A : Set G) with hCA
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hdA := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := hexp d hdA
  have hd3o : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hR'act := forall_commutator_mem_of_swap h45 h97 h113 h117 h119 h heA hecd hYe hKYe hstd
  have hR'W : R' ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_eq_closure (h113 G A e Ye c R' Y'' hstd).1
  have hR'N : R' ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := hstd.isSylowOf.le
  have hR'3 : IsPGroup 3 R' := hstd.isSylowOf.isPGroup
  have hR'el : ∀ w ∈ R', ∃ k : ℕ, w ^ 3 ^ k = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hR'3 ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hR'c : ∀ w ∈ R', w * c * w⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := fun w hw =>
    hR'act w hw c h.mem_A
  have hR'd : ∀ w ∈ R', w * d = d * w := fun w hw => by
    obtain ⟨k, hk⟩ := hR'el w hw
    exact Sec12.commute_of_conj_mem_zpowers hd3o ((Subgroup.mem_normalizer_iff.mp
      (Item1115Proof.W_le_normalizer_d h117 h (hR'W hw)) d).mp (Subgroup.mem_zpowers d)) hk
  have hR'e : ∀ w ∈ R', w * e = e * w := fun w hw => by
    obtain ⟨k, hk⟩ := hR'el w hw
    have he1 : e ≠ 1 := fun h1 => hecd (h1 ▸ Subgroup.one_mem _)
    exact Sec12.commute_of_conj_mem_zpowers (orderOf_eq_prime (hexp e heA) he1)
      ((Subgroup.mem_normalizer_iff.mp (hR'N hw) e).mp (Subgroup.mem_zpowers e)) hk
  have hcard1 := Item1117ResProof.card_le_three_mul_card_inf_centralizer hd3 hR'd hR'c
  have hA' : A = Subgroup.closure {c, e, d} :=
    h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  have hR'cA : R' ⊓ Subgroup.centralizer ({c} : Set G) ≤ CA := by
    intro w hw
    rw [hCA, Subgroup.mem_centralizer_iff, hA']
    intro z hz
    refine (Subgroup.closure_induction (p := fun z _ => z * w = w * z) ?_ ?_ ?_ ?_ hz)
    · rintro y (rfl | rfl | rfl)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm
      · exact (hR'e w hw.1).symm
      · exact (hR'd w hw.1).symm
    · simp
    · intro y z _ _ hy hz
      rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
    · intro y _ hy
      calc y⁻¹ * w = y⁻¹ * (w * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * w) * y⁻¹ := by rw [hy]
        _ = w * y⁻¹ := by group
  have hCAH : CA ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) := by
    intro z hz
    refine ⟨?_, Subgroup.centralizer_le_normalizer _ hz⟩
    have hzc : z ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hz c h.mem_A).symm)
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hzc
    exact Subgroup.centralizer_le_normalizer _ hzc
  have hNCA : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (CA : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hz ⊢
    intro y hy
    have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hn.2) y).mp hy
    rw [inv_inv] at hy'
    have h1 := hz _ hy'
    calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * y := by group
  have hS := h.isSylowOf_inf.inf_of_le_normalizer hCAH hNCA
  have hcard2 : Nat.card (R' ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) ≤
      Nat.card ((R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA : Subgroup G) :=
    Item1117ResProof.card_le_of_isSylowOf hR'cA (hR'3.to_le inf_le_left) hS
  have hCRT : (R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA ≤ T ⊓ CA := by
    refine le_inf ?_ inf_le_right
    intro z hz
    refine ⟨Item1119Proof.R_le_P R g hz.1.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 e heA).symm
  have hwCA : w ∉ T ⊓ CA := by
    intro hm
    exact hwc (Subgroup.mem_centralizer_iff.mp hm.2 c h.mem_A).symm
  have hcard3 : 3 * Nat.card (T ⊓ CA : Subgroup G) ≤ Nat.card T :=
    Item1117ResProof.three_mul_card_le_of_lt inf_le_left (h.isPGroup_sec11P.to_le inf_le_left) hwT
      hwCA
  have hcard4 : Nat.card ((R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA : Subgroup G) ≤
      Nat.card (T ⊓ CA : Subgroup G) := Subgroup.card_le_of_le hCRT
  have hgoal : Nat.card R' ≤ Nat.card T := by omega
  have hTN : T ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    refine inf_le_right.trans ?_
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  exact Item1117StepsProof.isSylowOf_of_card_le hTN (h.isPGroup_sec11P.to_le inf_le_left)
    hstd.isSylowOf hgoal

theorem sec11P_inf_centralizer_eq (h : Sec11Data G A c L a R Y d x s r g) {e : G}
    (hre : r * e = e * r) (hse : s * e = e * s) (hx3e : x ^ 3 * e = e * x ^ 3) {n : ℕ}
    (hn : ¬ 3 ∣ n) (hgx : g * x ^ n ∈ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) :
    sec11P (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) g = sec11P R g := by
  set T := sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) with hT
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  apply le_antisymm
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hgP)
  · have hTP : T ≤ sec11P T g := le_sup_left
    have hgP' : g ∈ sec11P T g := Item1119Proof.g_mem_P T g
    have hmemT : ∀ y ∈ R, y * e = e * y → y ∈ sec11P T g := fun y hy hye =>
      hTP ⟨Item1119Proof.R_le_P R g hy, Subgroup.mem_centralizer_singleton_iff.mpr hye⟩
    have hxn : x ^ n ∈ sec11P T g := by
      have e1 : x ^ n = g⁻¹ * (g * x ^ n) := by group
      rw [e1]
      exact (sec11P T g).mul_mem ((sec11P T g).inv_mem hgP') (hTP hgx)
    have hx : x ∈ sec11P T g :=
      mem_of_pow_mem_of_pow_three_mem hn hxn (hmemT _ (R.pow_mem hxR 3) hx3e)
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hgP')
    rw [h.R_eq, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hmemT _ hrR hre
    · exact hx
    · exact hmemT _ hsR hse

theorem pow_three_commutator_x_r_ne_one (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    (x * r * x⁻¹ * r⁻¹) ^ 3 ≠ 1 := by
  intro hu3
  obtain ⟨-, hRL⟩ := Item1116Proof.le_centralizer_and_normalizer h45 h
  obtain ⟨hrR, hxR, -⟩ := Item1116Proof.mem_R h
  have hRs : ∀ y ∈ R, y ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
    intro y hy
    rw [← h.inf_centralizer_eq]
    exact Item1116Proof.mem_normalizer_inf (Subgroup.le_normalizer hy)
      (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L (hRL hy))
  obtain ⟨i, j, hij⟩ := Item1116Proof.exists_zpow_mul_zpow_of_mem_closure (hRs r hrR)
    h.a_mem_closure
  have h3i : (3 : ℤ) ∣ i := by
    by_contra h3
    apply hrs
    have hri : r ^ i ∈ Subgroup.closure ({a, s} : Set G) := by
      have e : r ^ i = a * (s ^ j)⁻¹ := by
        rw [hij]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j))
    have hr : r ∈ Subgroup.closure ({a, s} : Set G) :=
      Subgroup.zpowers_le.mpr hri (Item1116Proof.mem_zpowers_zpow_of_not_dvd
        (Item1116Proof.exists_pow_eq_one_of_mem h hrR) h3)
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact hr
      · exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact h.a_mem_closure
      · exact Subgroup.subset_closure (by simp)
  obtain ⟨i', rfl⟩ := h3i
  set u := x * r * x⁻¹ * r⁻¹ with hu
  have hrx : r ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    Item1115Proof.mem_normalizer_zpowers_x h45 h hrR
  have hux : u ∈ Subgroup.zpowers x := by
    have h1 : r * x⁻¹ * r⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.mem_normalizer_iff.mp hrx (x⁻¹)).mp (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
    have e : u = x * (r * x⁻¹ * r⁻¹) := by rw [hu]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x) h1
  have hud : u ∈ Subgroup.zpowers d := Item1117Proof.mem_zpowers_of_pow_three_eq_one
    (Item1117Proof.d_mem_zpowers_x h) (Item1117Proof.orderOf_d h) hux hu3
  have hru : r * u = u * r :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hud (Item1119Proof.R_le_P R g hrR)
  have hxu : x * u = u * x := (Item1117Proof.commute_x_of_mem_zpowers_d h hud).eq
  have hrxr : r * x * r⁻¹ = x * u ^ (-1 : ℤ) := by
    have e1 : r * x * r⁻¹ = u⁻¹ * x := by rw [hu]; group
    rw [e1, zpow_neg_one, ← (Commute.inv_left (hxu.symm : Commute u x)).eq]
  have hr3 := conj_zpow_eq_of_conj_eq hxu hru hrxr 3
  have hu3' : u ^ ((3 : ℕ) * (-1 : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, show ((3 : ℕ) : ℤ) = 3 by norm_num, zpow_neg_one,
      show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, inv_pow, hu3, inv_one]
  rw [hu3', mul_one] at hr3
  have hr3C : r ^ (3 : ℤ) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [zpow_ofNat, Subgroup.mem_centralizer_singleton_iff]
    calc r ^ 3 * x = (r ^ 3 * x * (r ^ 3)⁻¹) * r ^ 3 := by group
      _ = x * r ^ 3 := by rw [hr3]
  have hsC : s ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.commute_s_x
  have haC : a ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [hij, zpow_mul]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hr3C i') (Subgroup.zpow_mem _ hsC j)
  apply (Item1119Proof.commutator_x_a_facts h45 h).2
  rw [← Subgroup.mem_centralizer_singleton_iff.mp haC, mul_inv_cancel_right, mul_inv_cancel]

end Data

end Item1117Res5Proof

section Main

open Item1117Res5Proof in
theorem step1119SymC_of_types (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h119 : Item119) (h1016 : Sec10.Item1016)
    (h1116 : Item1116) (h1117 : Item1117) (hT : Step1119SymTypes) : Step1119SymC := by
  intro G _ _ A c L a R Y d x s r g hbig hA2 hZR hNA hNd hra hsa hN hsc hrs hh
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, hfA, hfad, hfY, hNf, hfty⟩ :=
    hT G A c L a R Y d x s r g hbig hA2 hZR hNA hNd hra hsa hN hsc hrs hh
  have h := hbig.toSec11Data
  have h118 := item118_of h117 h45 h48
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hdA := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := hexp d hdA
  have hdd : d ∉ Subgroup.closure ({c, d} : Set G) → False := fun hn =>
    hn (Subgroup.subset_closure (by simp))
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hfd : f ∉ Subgroup.zpowers d := fun hm =>
    hfad (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hm)
  obtain ⟨k, f₀, hf₀ca, hff₀⟩ := exists_mem_closure_ca h hfA
  have hcaA : Subgroup.closure ({c, a} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [h.mem_A, h.a_mem]
  have hf₀A : f₀ ∈ A := hcaA hf₀ca
  have hf₀fd : f₀ ∈ Subgroup.closure ({f, d} : Set G) := by
    have e : f₀ = (d ^ k)⁻¹ * f := by rw [hff₀]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _
      (Subgroup.subset_closure (by simp)) k)) (Subgroup.subset_closure (by simp))
  have hf₀d : f₀ ∉ Subgroup.zpowers d := by
    intro hm
    apply hfd
    rw [hff₀]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) k) hm
  have hfdc : f * d = d * f := Item1117Proof.commute_of_mem_A h hfA hdA
  have hf₀eq : Subgroup.closure ({f₀, d} : Set G) = Subgroup.closure {f, d} :=
    Item1117Proof.closure_pair_eq_of_mem hfdc (hexp f hfA) hd3 hf₀fd hf₀d
  have hf₀cd : f₀ ∉ Subgroup.closure ({c, d} : Set G) := by
    intro hm
    apply hN
    have hcd : Subgroup.closure ({f₀, d} : Set G) = Subgroup.closure {c, d} :=
      Item1117Proof.closure_pair_eq_of_mem (Item1117Proof.commute_of_mem_A h h.mem_A hdA)
        (hexp c h.mem_A) hd3 hm hf₀d
    rw [← hcd, hf₀eq]
    exact hNf
  have hf₀ad : f₀ ∉ Subgroup.closure ({a, d} : Set G) := by
    intro hm
    apply hfad
    have had : Subgroup.closure ({f₀, d} : Set G) = Subgroup.closure {a, d} :=
      Item1117Proof.closure_pair_eq_of_mem (Item1117Proof.commute_of_mem_A h h.a_mem hdA)
        (hexp a h.a_mem) hd3 hm hf₀d
    rw [← had, hf₀eq]
    exact Subgroup.subset_closure (by simp)
  have haf₀d : a ∉ Subgroup.closure ({f₀, d} : Set G) := by
    intro hm
    apply hf₀ad
    have had : Subgroup.closure ({a, d} : Set G) = Subgroup.closure {f₀, d} :=
      Item1117Proof.closure_pair_eq_of_mem (Item1117Proof.commute_of_mem_A h hf₀A hdA)
        (hexp f₀ hf₀A) hd3 hm (fun ha => (h.toSec11Std.not_mem_facts h.inf_eq
          h.closure_eq).2.1 (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) ha))
    rw [had]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨Ye, hYe, hKYe⟩ :=
    exists_mem_thetaComponentsAt_sec11K_le h45 h48 h.toSec11Std h.inf_eq h.closure_eq hf₀A hf₀cd
  have hfield : KFacts.InducesStdKind Ye c .field := hfty f₀ hf₀fd hf₀d Ye hYe hKYe
  obtain ⟨R₁, Y₁, hstd₁⟩ :=
    Item1117Proof.exists_sec11Std_swap h45 h48 h97 h118 h1016 h hf₀A hf₀cd hYe hKYe hfield
  have hAYe := Item1117StepsProof.inf_eq_zpowers_d_swap h45 h97 h hf₀A hf₀cd hYe hKYe hstd₁
  have hA₂ : A = Subgroup.closure {f₀, c, d} := by
    rw [h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq hf₀A hf₀cd, Set.insert_comm]
  have hA₃ : A = Subgroup.closure {f₀, a, d} :=
    hstd₁.closure_eq_of_not_mem hAYe hA₂ h.a_mem haf₀d
  have hgP := Item1119Proof.g_mem_P R g
  have hgf₀ : g * f₀ ≠ f₀ * g := by
    intro hgf
    apply h.g_not_mem
    have hgA : ∀ y ∈ A, y * g = g * y := by
      intro y hy
      rw [hA₃] at hy
      refine forall_commute_of_closure ?_ y hy
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hgf.symm
      · exact (Item1117Proof.commute_g_a h).symm
      · exact (Item1119Proof.commute_d h113 h117 h hgP).symm
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [← hgA c h.mem_A, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  obtain ⟨n, hn3, hgxT⟩ :=
    exists_mul_pow_mem_inf_of_not_commute h45 h113 h117 h hf₀A hf₀cd hgf₀
  have hxc : x * c = c * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Item1117Proof.R_le_centralizer_c h hxR))
  have hwc : g * x ^ n * c ≠ c * (g * x ^ n) := by
    intro hgc
    apply h.g_not_mem
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    have e1 : g * c * g⁻¹ = (g * x ^ n) * c * (g * x ^ n)⁻¹ := by
      have := (Commute.pow_left (hxc : Commute x c) n).eq
      calc g * c * g⁻¹ = g * (x ^ n * c * (x ^ n)⁻¹) * g⁻¹ := by
            rw [this, mul_inv_cancel_right]
        _ = (g * x ^ n) * c * (g * x ^ n)⁻¹ := by group
    rw [e1, hgc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  have hQ := isSylowOf_of_swap h45 h97 h113 h117 h119 h hf₀A hf₀cd hYe hKYe hstd₁ hgxT hwc
  set T := sec11P R g ⊓ Subgroup.centralizer ({f₀} : Set G) with hTdef
  have hstd₂ := Item1117StepsProof.sec11Std_swap h45 h113 h hf₀A hf₀cd hYe hKYe hstd₁ hQ
  have hKeq := sec11K_eq_of_mem_closure h hf₀ca hf₀cd
  have hKp : Group.IsPerfect (sec11K L a) := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hdK : d ∈ sec11K L a := h.toSec11Std.d_mem_sec11K h.inf_eq
  have hd1 : d ≠ 1 := (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).2.2
  have hK1 : sec11K L a ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
  have hKa : sec11K L a ≤ Subgroup.centralizer ({a} : Set G) :=
    (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_right |>.trans' le_rfl
  have hKK : sec11K L a ≤ sec11K Ye a :=
    Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKp (le_inf (hKeq ▸ hKYe) hKa)
  obtain ⟨Ya, hYa, hKYa⟩ :=
    exists_mem_thetaComponentsAt_sec11K_le h45 h48 hstd₂ hAYe hA₂ h.a_mem haf₀d
  have hYaY : Ya = Y := Sec6.eq_of_mem_thetaComponentsIn_of_le hYa h.mem_thetaComponentsAt_Y
    hKp hK1 (hKK.trans hKYa) h.sec11K_le
  have hstd₃ : Sec11Std G A f₀ Ye a T Y :=
    hstd₂.change_a h45 hAYe hA₂ h.a_mem haf₀d h.mem_thetaComponentsAt_Y (hYaY ▸ hKYa)
  obtain ⟨x', hx'⟩ := hstd₃.exists_zpowers_eq_inf_L
  obtain ⟨s', hs'⟩ := RChoice.exists_zpowers_eq_of_isCyclic (h113 G A f₀ Ye a T Y hstd₃).2
  obtain ⟨r', hr'T, har'⟩ := hstd₃.exists_eq_closure h45 hAYe hA₃ hx' hs'
  have hδ := Item1117Proof.conj_g_mem_of_mem_A h117 h hf₀A
  set δ := g * f₀ * g⁻¹ * f₀⁻¹ with hδdef
  have hgδ : g * δ = δ * g := Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hδ hgP
  have hginv : g⁻¹ * f₀ * g = δ⁻¹ * f₀ := by
    have e1 : g * f₀ * g⁻¹ = δ * f₀ := by rw [hδdef]; group
    have hgδ' : g⁻¹ * δ * g = δ := by rw [mul_assoc, ← hgδ]; group
    calc g⁻¹ * f₀ * g = g⁻¹ * (δ⁻¹ * (δ * f₀)) * g := by group
      _ = g⁻¹ * (δ⁻¹ * (g * f₀ * g⁻¹)) * g := by rw [e1]
      _ = (g⁻¹ * δ * g)⁻¹ * f₀ := by group
      _ = δ⁻¹ * f₀ := by rw [hgδ']
  have hgT : g ∈ Subgroup.normalizer (T : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hz' : z ∈ T := hz
    have hzf : z * f₀ = f₀ * z := Subgroup.mem_centralizer_singleton_iff.mp hz'.2
    have hzδ : z * δ⁻¹ = δ⁻¹ * z :=
      ((Commute.inv_right (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hδ hz'.1 :
        Commute z δ))).eq
    have hmem : g * z * g⁻¹ ∈ T := by
      refine Subgroup.mem_inf.mpr ⟨(sec11P R g).mul_mem ((sec11P R g).mul_mem hgP hz'.1)
        ((sec11P R g).inv_mem hgP), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc g * z * g⁻¹ * f₀ = g * (z * (g⁻¹ * f₀ * g)) * g⁻¹ := by group
        _ = g * (z * (δ⁻¹ * f₀)) * g⁻¹ := by rw [hginv]
        _ = g * ((δ⁻¹ * f₀) * z) * g⁻¹ := by
            have e2 : z * (δ⁻¹ * f₀) = (δ⁻¹ * f₀) * z := by
              calc z * (δ⁻¹ * f₀) = (z * δ⁻¹) * f₀ := (mul_assoc _ _ _).symm
                _ = (δ⁻¹ * z) * f₀ := by rw [hzδ]
                _ = δ⁻¹ * (z * f₀) := mul_assoc _ _ _
                _ = δ⁻¹ * (f₀ * z) := by rw [hzf]
                _ = (δ⁻¹ * f₀) * z := (mul_assoc _ _ _).symm
            rw [e2]
        _ = f₀ * (g * z * g⁻¹) := by
            rw [← hginv]
            group
    exact hmem
  have hf₀3 : orderOf f₀ = 3 := orderOf_eq_prime (hexp f₀ hf₀A)
    (fun h1 => hf₀d (h1 ▸ Subgroup.one_mem _))
  have hgN : g ∉ Subgroup.normalizer (Subgroup.zpowers f₀ : Set G) := by
    intro hgN
    obtain ⟨m, hm⟩ := h.pow_eq_one
    exact hgf₀ (Sec12.commute_of_conj_mem_zpowers hf₀3
      ((Subgroup.mem_normalizer_iff.mp hgN f₀).mp (Subgroup.mem_zpowers f₀)) hm)
  have hgconj : g * f₀ * g⁻¹ ∈ Subgroup.closure ({f₀, d} : Set G) := by
    have e1 : g * f₀ * g⁻¹ = δ * f₀ := by rw [hδdef]; group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hδ)
      (Subgroup.subset_closure (by simp))
  have h₃ : Sec11Data G A f₀ Ye a T Y d x' s' r' g :=
    { toSec11Std := hstd₃
      inf_eq := hAYe
      closure_eq := hA₃
      inf_L_eq := hx'
      inf_centralizer_eq := hs'
      R_eq := hr'T
      a_mem_closure := har'
      pow_eq_one := h.pow_eq_one
      g_mem := h.g_mem
      g_mem_normalizer := hgT
      g_not_mem := hgN
      conj_mem := hgconj }
  have hrA : ∀ y ∈ A, r * y = y * r := by
    intro y hy
    rw [h.closure_eq] at hy
    refine (forall_commute_of_closure ?_ y hy).symm
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp
        (Item1117Proof.R_le_centralizer_c h hrR)).symm
    · exact hra.symm
    · exact (Item1119Proof.commute_d h113 h117 h (Item1119Proof.R_le_P R g hrR)).symm
  have hsA : s ∈ A := Subgroup.zpowers_le.mpr h.mem_A (hsc ▸ Subgroup.mem_zpowers s)
  have hP' : sec11P T g = sec11P R g :=
    sec11P_inf_centralizer_eq h (hrA f₀ hf₀A) (Item1117Proof.commute_of_mem_A h hsA hf₀A)
      (x_pow_three_commute_of_mem_A h hf₀A) hn3 hgxT
  have hx'9 : 9 < orderOf x' := by
    by_contra hle
    have hcase : Subgroup.zpowers s' = Subgroup.zpowers f₀ ∧
        Subgroup.closure ({r', s'} : Set G) = Subgroup.closure {a, s'} := by
      by_contra hc
      apply hle
      refine h1116 G A f₀ Ye a T Y d x' s' r' g h₃ ?_
      by_contra hc'
      push Not at hc'
      exact hc hc'
    obtain ⟨⟨a'', ha''A, -, hPP, -⟩, -⟩ := h1117 G A f₀ Ye a T Y d x' s' r' g h₃ hcase.1 hcase.2
    rw [hP'] at hPP
    have hcomm : x * r * x⁻¹ * r⁻¹ ∈ ⁅sec11P R g, sec11P R g⁆ := by
      have := Subgroup.commutator_mem_commutator (Item1119Proof.R_le_P R g hxR)
        (Item1119Proof.R_le_P R g hrR)
      rwa [commutatorElement_def] at this
    rw [hPP] at hcomm
    have hle' : Subgroup.closure ({a'', d} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      exacts [ha''A, hdA]
    exact Item1117Res5Proof.pow_three_commutator_x_r_ne_one h45 h113 h117 h hrs
      (hexp _ (hle' hcomm))
  have hbig' : Sec11Big G A f₀ Ye a T Y d x' s' r' g :=
    { toSec11Data := h₃
      orderOf_x_gt := hx'9
      isList := hbig.isList
      not_field := fun hf =>
        not_inducesOuterTheta_of_mem (hfY hf₀fd)
          (KFacts.InducesStdKind.inducesOuterTheta Y hf (by decide))
      orderOf_g := hbig.orderOf_g
      exists_inverts := by
        obtain ⟨t, ht, htg⟩ := hbig.exists_inverts
        exact ⟨t, ⟨hKK ht.1, ht.2⟩, htg⟩ }
  refine ⟨f₀, Ye, a, T, Y, x', s', r', g, hbig', ?_⟩
  rw [hP', hf₀eq]
  exact hNf

end Main

end CFSG.RankThree.PartTwo.Sec11
