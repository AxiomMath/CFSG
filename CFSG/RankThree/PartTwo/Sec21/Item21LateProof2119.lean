module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofIdent
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofGL33
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

structure Config2119 (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G)
    (L : Subgroup G) : Prop where
  pair : Sec21Pair G A E U c L
  lthree : ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n))
  typeC : Sec4.IsTypeCOn A L
  card : Nat.card A = 3 ^ 3
  star : Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))

@[expose] def Item2119Frame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2119 G A E U c L →
      ∃ d ∈ A ⊓ L, d ≠ 1 ∧ Sec4.InducesTypeOn L d 1 ∧
        (∃ w ∈ L ⊓ Subgroup.normalizer (A : Set G), w * d * w⁻¹ = d ∧
          (∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ Subgroup.zpowers d) ∧ ∃ a ∈ A, w * a * w⁻¹ ≠ a) ∧
        ∃ t ∈ L ⊓ Subgroup.normalizer (A : Set G), t * d * t⁻¹ = d⁻¹

@[expose] def Item2120 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2119 G A E U c L → ∀ d ∈ A ⊓ L, d ≠ 1 → Sec4.InducesTypeOn L d 1 →
      (∀ g ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d,
        g * x * g⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) →
      ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d

@[expose] def Item2121 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2119 G A E U c L → ∀ d ∈ A ⊓ L, d ≠ 1 → Sec4.InducesTypeOn L d 1 →
      (∃ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∉ Subgroup.zpowers d) →
      ∀ X : Subgroup G, X ≤ A → (∀ g ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X) →
        Nat.card X = 9 → d ∈ X → c ∉ X → False

@[expose] def Item2119End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2119 G A E U c L → ∀ d ∈ A ⊓ L, d ≠ 1 → Sec4.InducesTypeOn L d 1 →
      ¬ ∀ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∈ Subgroup.zpowers d

namespace Item21LateProof

variable {G : Type} [Group G]

theorem card_zpowers_sup_zpowers [Finite G] {c d : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hc1 : c ≠ 1) (hdc : d ∉ Subgroup.zpowers c) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow hcd i j)).eq
  obtain ⟨hcd', -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hZc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hZd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hinf : Nat.card (Subgroup.zpowers c ⊓ Subgroup.zpowers d : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers c ⊓ Subgroup.zpowers d : Subgroup G) ∣ 3 :=
      hZd ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.zpowers c ⊓ Subgroup.zpowers d = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hZd, h])
      have hmem : d ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers d := by
        rw [heq]
        exact Subgroup.mem_zpowers d
      exact hdc hmem.1
  rw [hinf, mul_one, hZc, hZd] at hcd'
  exact hcd'

theorem mem_of_conj_invariant [Finite G] {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1)
    (hA : Nat.card A = 27) {c d : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hdA : d ∈ A)
    (hdc : d ∉ Subgroup.zpowers c) {w t : G} (hwc : w * c * w⁻¹ = c) (hwd : w * d * w⁻¹ = d)
    (hwA : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ Subgroup.zpowers d)
    (hwmove : ∃ a ∈ A, w * a * w⁻¹ ≠ a) (htc : t * c * t⁻¹ = c) (htd : t * d * t⁻¹ = d⁻¹)
    (X : Subgroup G) (hXA : X ≤ A) (hXw : ∀ x ∈ X, w * x * w⁻¹ ∈ X)
    (hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hX1 : X ≠ ⊥) (hXc : X ≠ Subgroup.zpowers c) : d ∈ X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  have hZd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hZc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hgen : ∀ δ ∈ X, δ ∈ Subgroup.zpowers d → δ ≠ 1 → d ∈ X := by
    intro δ hδX hδd hδ1
    have hδ3 : δ ^ 3 = 1 := h3 δ (hXA hδX)
    have heq : Subgroup.zpowers δ = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hδd)
        (by rw [hZd, Nat.card_zpowers, orderOf_eq_prime hδ3 hδ1])
    have hd : d ∈ Subgroup.zpowers δ := heq ▸ Subgroup.mem_zpowers d
    exact (Subgroup.zpowers_le.mpr hδX) hd
  by_cases hmove : ∃ x ∈ X, w * x * w⁻¹ ≠ x
  · obtain ⟨x, hxX, hx⟩ := hmove
    refine hgen _ (X.mul_mem (X.inv_mem hxX) (hXw x hxX)) (hwA x (hXA hxX)) ?_
    intro h
    rw [inv_mul_eq_one] at h
    exact hx h.symm
  push Not at hmove
  set D := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hD
  have hcd : c * d = d * c := hcomm c hcA d hdA
  have hD9 := card_zpowers_sup_zpowers hcd hc3 hd3 hc1 hdc
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)
  have hwD : ∀ y ∈ D, w * y * w⁻¹ = y := by
    intro y hy
    have hDc : ∀ x ∈ Subgroup.zpowers c, ∀ z ∈ Subgroup.zpowers d, x * z = z * x := by
      intro x hx z hz
      exact hcomm x ((Subgroup.zpowers_le.mpr hcA) hx) z ((Subgroup.zpowers_le.mpr hdA) hz)
    have hy' : y ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := hy
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hDc).2] at hy'
    obtain ⟨x, hx, z, hz, rfl⟩ := hy'
    rw [show w * (x * z) * w⁻¹ = (w * x * w⁻¹) * (w * z * w⁻¹) by group,
      Item21LateProof.conj_eq_of_mem_zpowers hwc hx, Item21LateProof.conj_eq_of_mem_zpowers hwd hz]
  have hXD : X ≤ D := by
    intro x hxX
    by_contra hxD
    obtain ⟨a, haA, ha⟩ := hwmove
    apply ha
    obtain ⟨k, -, y, hyD, rfl⟩ :=
      Item21LateProof.exists_pow_mul_of_card hcomm h3 hDA (by rw [hA, hD9]) (hXA hxX) hxD a haA
    rw [show w * (x ^ k * y) * w⁻¹ = (w * x ^ k * w⁻¹) * (w * y * w⁻¹) by group,
      ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hmove x hxX, hwD y hyD]
  have hdvd : Nat.card X ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hD9]
    exact Subgroup.card_dvd_of_le hXD
  obtain ⟨k, hk2, hkX⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exact absurd (Subgroup.eq_bot_of_card_eq X (by rw [hkX, pow_zero])) hX1
  ·
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX1
    have hxD : (x : G) ∈ D := hXD x.2
    have hDc : ∀ x ∈ Subgroup.zpowers c, ∀ z ∈ Subgroup.zpowers d, x * z = z * x := by
      intro x hx z hz
      exact hcomm x ((Subgroup.zpowers_le.mpr hcA) hx) z ((Subgroup.zpowers_le.mpr hdA) hz)
    have hxD' : (x : G) ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := hxD
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hDc).2] at hxD'
    obtain ⟨u, hu, v, hv, huv⟩ := hxD'
    simp only at huv
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hv
    have htu : t * u * t⁻¹ = u := Item21LateProof.conj_eq_of_mem_zpowers htc hu
    have htv : t * v * t⁻¹ = v⁻¹ := by
      rw [← hj, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htd, inv_zpow]
    have hxt : (x : G)⁻¹ * (t * x * t⁻¹) = v⁻¹ * v⁻¹ := by
      rw [← huv, show t * (u * v) * t⁻¹ = (t * u * t⁻¹) * (t * v * t⁻¹) by group, htu, htv]
      have huv' : u * v = v * u := hDc u hu v hv
      calc (u * v)⁻¹ * (u * v⁻¹) = v⁻¹ * (u⁻¹ * u) * v⁻¹ := by group
        _ = v⁻¹ * v⁻¹ := by rw [inv_mul_cancel, mul_one]
    by_cases hv1 : v⁻¹ * v⁻¹ = 1
    ·
      exfalso
      have hv3 : v ^ 3 = 1 := h3 v ((Subgroup.zpowers_le.mpr hdA) hv)
      have hv1' : v = 1 := by
        have e1 : v = v ^ 3 * (v⁻¹ * v⁻¹) := by rw [pow_succ, pow_two]; group
        rw [e1, hv3, hv1, one_mul]
      apply hXc
      have hxc : (x : G) ∈ Subgroup.zpowers c := by rw [← huv, hv1', mul_one]; exact hu
      have hx3 : (x : G) ^ 3 = 1 := h3 x (hXA x.2)
      have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hXx : X = Subgroup.zpowers (x : G) := by
        refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_).symm
        rw [hkX, pow_one, Nat.card_zpowers, orderOf_eq_prime hx3 hx1']
      rw [hXx]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc)
        (by rw [hZc, Nat.card_zpowers, orderOf_eq_prime hx3 hx1'])
    · refine hgen _ ?_ ?_ hv1
      · rw [← hxt]
        exact X.mul_mem (X.inv_mem x.2) (hXt x x.2)
      · exact (Subgroup.zpowers d).mul_mem ((Subgroup.zpowers d).inv_mem hv)
          ((Subgroup.zpowers d).inv_mem hv)
  ·
    have hXeq : X = D := Subgroup.eq_of_le_of_card_ge hXD (by rw [hD9, hkX]; norm_num)
    rw [hXeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)

end Item21LateProof

open Item21LateProof

theorem item2119_of
    (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (hF : Item2119Frame) (h20 : Item2120) (h21 : Item2121) (hEnd : Item2119End) :
    Item2119 := by
  intro G _ _ A E U c L hpair ⟨n, ⟨eL⟩⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hn, he, hC, h27, hS3⟩ := case7_of_lBar_L3 h211 h2116 hpair eL
  have hcfg : Config2119 G A E U c L := ⟨hpair, ⟨n, hn, he, ⟨eL⟩⟩, hC, h27, hS3⟩
  obtain ⟨d, hdB, hd1, hdT, ⟨w, ⟨hwL, hwN⟩, hwd, hwA, hwmove⟩, t, ⟨htL, htN⟩, htd⟩ :=
    hF G A E U c L hcfg
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA27 : Nat.card A = 27 := by rw [h27]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hfixc : ∀ {y : G}, y ∈ L → y * c * y⁻¹ = c := fun hy => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hLC hy)), mul_inv_cancel_right]
  have hcL : c ∉ L := by
    intro hcL
    have := Item222Proof.isSimpleGroup_projSL_three (GaloisField 2 n)
    have hsimp : IsSimpleGroup (lBar L) := eL.isSimpleGroup
    have hZ : Subgroup.center (lBar L) = ⊥ :=
      Item21Early2Proof.center_eq_bot_of_isSimpleGroup_of_not_prime (by
        obtain ⟨r, hr, hcard⟩ := card_projSL3_eq n
        rw [Nat.card_congr eL.toEquiv, hcard]
        refine Item21Early2Proof.not_prime_of_four_dvd ?_
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) r)
    have hcZ : (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ : lBar L) ∈
        Subgroup.center (lBar L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ z
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLC y.2))
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcZ
    obtain ⟨-, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := L)
      Nat.prime_three
    have hc3 : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3 c hcA)
    have hc1' : (⟨c, hcL⟩ : L) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    have ho : orderOf (⟨⟨c, hcL⟩, hcZ⟩ : aschbacherSolvableCore 3 L) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1'
    apply hT3
    have h := orderOf_dvd_natCard (⟨⟨c, hcL⟩, hcZ⟩ : aschbacherSolvableCore 3 L)
    rwa [ho] at h
  have hdA : d ∈ A := hdB.1
  have hdc : d ∉ Subgroup.zpowers c := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hc3 : c ^ 3 = 1 := h3 c hcA
    have hd3 : d ^ 3 = 1 := h3 d hdA
    apply hcL
    have hZ : Subgroup.zpowers d = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hc3 hc1,
          orderOf_eq_prime hd3 hd1])
    have hcd : c ∈ Subgroup.zpowers d := hZ ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hdB.2) hcd
  have hNc : ¬ ∀ g ∈ Subgroup.normalizer (A : Set G), g * c * g⁻¹ ∈ Subgroup.zpowers c := by
    intro hno
    apply h2115 G A E U c L hpair
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact (Subgroup.zpowers c).zpow_mem (hno g hg) k
  intro X hX
  set X' := X.map A.subtype with hX'
  have hX'A : X' ≤ A := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hX'N : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ X', g * x * g⁻¹ ∈ X' := by
    rintro g hg _ ⟨x, hx, rfl⟩
    have h1 := hX (A.normalizerMonoidHom ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
    have h2 : A.normalizerMonoidHom ⟨g, hg⟩ x ∈ X := by
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    exact ⟨_, h2, rfl⟩
  have hX'eq : X = X'.subgroupOf A := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
  by_cases hX1 : X' = ⊥
  · left
    rw [hX'eq, hX1, Subgroup.bot_subgroupOf]
  by_cases hXt : X' = A
  · right
    rw [hX'eq, hXt, Subgroup.subgroupOf_self]
  exfalso
  have hXc : X' ≠ Subgroup.zpowers c := by
    intro h
    apply hNc
    intro g hg
    rw [← h]
    exact hX'N g hg c (h ▸ Subgroup.mem_zpowers c)
  have hdX : d ∈ X' := mem_of_conj_invariant hcomm h3 hA27 hcA hc1 hdA hdc (hfixc hwL) hwd hwA
    hwmove (hfixc htL) htd X' hX'A (hX'N w hwN) (hX'N t htN) hX1 hXc
  have hnd := hEnd G A E U c L hcfg d hdB hd1 hdT
  have hnd' : ∃ g ∈ Subgroup.normalizer (A : Set G), g * d * g⁻¹ ∉ Subgroup.zpowers d := by
    by_contra h
    push Not at h
    exact hnd h
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hD9 := card_zpowers_sup_zpowers (hcomm c hcA d hdA) hc3 hd3 hc1 hdc
  have hdvd : Nat.card X' ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_dvd_of_le hX'A
  obtain ⟨k, hk3, hkX⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exact hX1 (Subgroup.eq_bot_of_card_eq X' (by rw [hkX, pow_zero]))
  ·
    apply hnd
    have hd1' : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    have hXd : X' = Subgroup.zpowers d := (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr hdX) (by rw [hkX, pow_one, Nat.card_zpowers, hd1'])).symm
    intro g hg
    rw [← hXd]
    exact hX'N g hg d hdX
  ·
    by_cases hcX : c ∈ X'
    ·
      have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ X' :=
        sup_le (Subgroup.zpowers_le.mpr hcX) (Subgroup.zpowers_le.mpr hdX)
      have hXeq : Subgroup.zpowers c ⊔ Subgroup.zpowers d = X' :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hkX, hD9]; norm_num)
      apply hnd
      exact h20 G A E U c L hcfg d hdB hd1 hdT (hXeq ▸ hX'N)
    ·
      exact h21 G A E U c L hcfg d hdB hd1 hdT hnd' X' hX'A hX'N (by rw [hkX]; norm_num) hdX hcX
  · exact hXt (Subgroup.eq_of_le_of_card_ge hX'A (by rw [hkX, hA27]; norm_num))

end CFSG.RankThree.PartTwo.Sec21
