module

public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Statements

@[expose] def Gap1117SwapSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      g * x * g⁻¹ * x⁻¹ ∈ A → g * x * g⁻¹ * x⁻¹ ∉ Subgroup.closure {c, d} →
      (∀ a' ∈ Subgroup.closure ({g * x * g⁻¹ * x⁻¹, d} : Set G), a' ∉ Subgroup.zpowers d →
        ∀ Y' ∈ thetaComponentsAt 3 a', sec11K L a' ≤ Y' → KFacts.InducesStdKind Y' c .field) →
      ∀ (Ye R' Y'' : Subgroup G), Ye ∈ thetaComponentsAt 3 (g * x * g⁻¹ * x⁻¹) →
        sec11K L (g * x * g⁻¹ * x⁻¹) ≤ Ye →
        Sec11Std G A (g * x * g⁻¹ * x⁻¹) Ye c R' Y'' →
        9 < orderOf x → KFacts.InducesStdKind Y c .field →
        9 < Nat.card (R' ⊓ Ye : Subgroup G) →
          IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G))
            (Subgroup.normalizer (Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) : Set G))

@[expose] def Gap1117SwapOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      g * x * g⁻¹ * x⁻¹ ∈ A → g * x * g⁻¹ * x⁻¹ ∉ Subgroup.closure {c, d} →
      (∀ a' ∈ Subgroup.closure ({g * x * g⁻¹ * x⁻¹, d} : Set G), a' ∉ Subgroup.zpowers d →
        ∀ Y' ∈ thetaComponentsAt 3 a', sec11K L a' ≤ Y' → KFacts.InducesStdKind Y' c .field) →
      ∀ (Ye R' Y'' : Subgroup G), Ye ∈ thetaComponentsAt 3 (g * x * g⁻¹ * x⁻¹) →
        sec11K L (g * x * g⁻¹ * x⁻¹) ≤ Ye →
        Sec11Std G A (g * x * g⁻¹ * x⁻¹) Ye c R' Y'' →
        9 < orderOf x → KFacts.InducesStdKind Y c .field →
        IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G))
          (Subgroup.normalizer (Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) : Set G)) →
        9 < Nat.card ((sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G)) ⊓ Ye :
          Subgroup G) →
          ∀ y ∈ sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G),
            ∃ i : ℕ, c ^ i * y ∈ innerPreimage Ye

end Statements

namespace Item1117StepsProof

section Elementary

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_card_le {Q S K : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup 3 Q)
    (hS : IsSylowOf 3 S K) (hcard : Nat.card S ≤ Nat.card Q) : IsSylowOf 3 Q K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  have h1 : Nat.card Q ≤ Nat.card S := by
    rw [hS.card_eq, ← Sylow.card_eq_multiplicity T]
    calc Nat.card Q = Nat.card (Q.subgroupOf K) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv).symm
      _ ≤ Nat.card T := Subgroup.card_le_of_le hT
  exact CFSG.ABGLocalTools.isSylowOf_of_card hQK ((le_antisymm h1 hcard).trans hS.card_eq)

end Elementary

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sec11P_le_centralizer_d (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    sec11P R g ≤ Subgroup.centralizer ({d} : Set G) := by
  have hdA := Item1117Proof.d_mem_A h
  refine sup_le ?_ ?_
  · rw [Item1117Proof.R_eq_closure h hsc hrs, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Item1117Proof.commute_of_mem_A h h.a_mem hdA)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Item1117Proof.commute_d_x h).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Item1117Proof.commute_of_mem_A h h.mem_A hdA)
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    have h1 := Item1117Proof.conj_g_d h117 h
    calc g * d = (g * d * g⁻¹) * g := by group
      _ = d * g := by rw [h1]

theorem conj_x_e_mem (h : Sec11Data G A c L a R Y d x s r g) {e : G} (he : e ∈ A) :
    x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
  obtain ⟨z, hz, hxz⟩ := Item1117Proof.exists_conj_of_mem_A h he
  have hzA : z ∈ A := Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_A h) hz
  rw [hxz, Item1117Proof.commute_of_mem_A h he hzA, mul_inv_cancel_right]
  exact hz

theorem not_commute_x_e (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {e : G}
    (he : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) : x * e ≠ e * x := by
  intro hxe
  apply h.toSec11Std.mul_ne_mul h45 h.inf_eq h.closure_eq h.inf_L_eq
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq he hecd
  have hle : A ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hA', Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
        (Item1117Proof.R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxe.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Item1117Proof.commute_d_x h)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle h.a_mem)

theorem x_not_mem_normalizer_e (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {e : G} (he : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) :
    x ∉ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
  intro hxN
  have h1 : x * e * x⁻¹ = e :=
    conj_eq_self_of_threeElement (Item1117Proof.pow_three_of_mem_A h he)
      (Item1117Proof.x_pow_eq_one h)
      ((Subgroup.mem_normalizer_iff.mp hxN e).mp (Subgroup.mem_zpowers e))
  apply not_commute_x_e h45 h he hecd
  calc x * e = (x * e * x⁻¹) * x := by group
    _ = e * x := by rw [h1]

theorem x_mem_normalizer_inf (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (he : e ∈ A) :
    x ∈ Subgroup.normalizer
      ((sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) := by
  have hxP : x ∈ sec11P R g := le_sup_left (a := R) (Item1116Proof.mem_R h).2.1
  have hPd := sec11P_le_centralizer_d h117 h hsc hrs
  have hzd : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := conj_x_e_mem h he
  set z := x * e * x⁻¹ * e⁻¹ with hz
  have hxe : x * e * x⁻¹ = z * e := by rw [hz]; group
  have hzx : Commute x z := Item1117Proof.commute_x_of_mem_zpowers_d h hzd
  have hzq : ∀ q ∈ sec11P R g, Commute q z := by
    intro q hq
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzd
    rw [← hn]
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hPd hq)) n
  have hxe' : x⁻¹ * e * x = z⁻¹ * e := by
    have e1 : x⁻¹ * (z * e) * x = z * (x⁻¹ * e * x) := by
      have := hzx.inv_left.eq
      calc x⁻¹ * (z * e) * x = (x⁻¹ * z) * e * x := by group
        _ = (z * x⁻¹) * e * x := by rw [this]
        _ = z * (x⁻¹ * e * x) := by group
    have e2 : x⁻¹ * (z * e) * x = e := by rw [← hxe]; group
    calc x⁻¹ * e * x = z⁻¹ * (z * (x⁻¹ * e * x)) := by group
      _ = z⁻¹ * e := by rw [← e1, e2]
  refine Subgroup.mem_normalizer_fintype fun q hq => ?_
  rw [SetLike.mem_coe, Subgroup.mem_inf] at hq ⊢
  obtain ⟨hqP, hqe⟩ := hq
  refine ⟨(sec11P R g).mul_mem ((sec11P R g).mul_mem hxP hqP) ((sec11P R g).inv_mem hxP), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hqe ⊢
  have hqz := (hzq q hqP).inv_right.eq
  have hxz := hzx.inv_right.eq
  calc x * q * x⁻¹ * e = x * q * (x⁻¹ * e * x) * x⁻¹ := by group
    _ = x * q * (z⁻¹ * e) * x⁻¹ := by rw [hxe']
    _ = x * (q * z⁻¹) * e * x⁻¹ := by group
    _ = x * (z⁻¹ * q) * e * x⁻¹ := by rw [hqz]
    _ = x * z⁻¹ * (q * e) * x⁻¹ := by group
    _ = x * z⁻¹ * (e * q) * x⁻¹ := by rw [hqe]
    _ = (x * z⁻¹) * e * q * x⁻¹ := by group
    _ = (z⁻¹ * x) * e * q * x⁻¹ := by rw [hxz]
    _ = z⁻¹ * (x * e * x⁻¹) * (x * q * x⁻¹) := by group
    _ = z⁻¹ * (z * e) * (x * q * x⁻¹) := by rw [hxe]
    _ = e * (x * q * x⁻¹) := by group

theorem exists_mul_pow_mem_inf (h45 : Sec4.Item4_5) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ n : ℕ, g * x ^ n ∈ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) := by
  have hxP : x ∈ sec11P R g := le_sup_left (a := R) (Item1116Proof.mem_R h).2.1
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have hPd := sec11P_le_centralizer_d h117 h hsc hrs
  have hzd : x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := conj_x_e_mem h he
  set z := x * e * x⁻¹ * e⁻¹ with hz
  have hz1 : z ≠ 1 := by
    intro h1
    apply not_commute_x_e h45 h he hecd
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
  refine ⟨2 * k, Subgroup.mem_inf.mpr ⟨(sec11P R g).mul_mem hgP ((sec11P R g).pow_mem hxP _), ?_⟩⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := conj_zpow_eq_of_conj_eq hez hxz hxe (2 * k)
  rw [mul_one, zpow_natCast] at h1
  have hgz : g * z ^ (2 * k) * g⁻¹ = z ^ (2 * k) := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hPd hgP)).symm) : Subgroup.zpowers d ≤ _)
        (hzz ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers z) (2 * k)))
    calc g * z ^ (2 * k) * g⁻¹ = (z ^ (2 * k) * g) * g⁻¹ := by rw [this]
      _ = z ^ (2 * k) := by group
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

theorem inf_sup_zpowers_x (h45 : Sec4.Item4_5) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) :
    (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) ⊔ Subgroup.zpowers x = sec11P R g := by
  have hxP : x ∈ sec11P R g := le_sup_left (a := R) (Item1116Proof.mem_R h).2.1
  have hAP : A ≤ sec11P R g := (le_R_of_hyp91 h.toHyp91).trans le_sup_left
  apply le_antisymm
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxP)
  have hAQ : ∀ u ∈ A, u ∈ (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) ⊔
      Subgroup.zpowers x := fun u hu => Subgroup.mem_sup_left
    ⟨hAP hu, Subgroup.mem_centralizer_singleton_iff.mpr (Item1117Proof.commute_of_mem_A h hu he)⟩
  obtain ⟨n, hgx⟩ := exists_mul_pow_mem_inf h45 h117 h hsc hrs he hecd
  refine (le_of_eq (Item1117Proof.sec11P_eq_closure h hsc hrs)).trans ?_
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy | hy | hy <;> rw [hy, SetLike.mem_coe]
  · exact hAQ _ h.a_mem
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact hAQ _ h.mem_A
  · have hm := Subgroup.mul_mem _ (Subgroup.mem_sup_left hgx)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n)))
    rwa [mul_inv_cancel_right] at hm

theorem le_card_inf_centralizer (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) :
    81 ≤ Nat.card (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hgx⟩ := exists_mul_pow_mem_inf h45 h117 h hsc hrs he hecd
  set t := g * x ^ n with ht
  have hAP : A ≤ sec11P R g := (le_R_of_hyp91 h.toHyp91).trans le_sup_left
  have hAQ : A ≤ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) := fun u hu =>
    Subgroup.mem_inf.mpr ⟨hAP hu,
      Subgroup.mem_centralizer_singleton_iff.mpr (Item1117Proof.commute_of_mem_A h hu he)⟩
  have hle : Subgroup.zpowers t ⊔ A ≤ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hgx) hAQ
  have htA : Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr (h.sec11P_le_normalizer_A h113 (Subgroup.mem_inf.mp hgx).1)
  have hcard := Sec6.card_sup_mul_card_inf htA
  rw [h.card_eq] at hcard
  have hxR : x ∈ R := (Item1116Proof.mem_R h).2.1
  have htnA : t ∉ A := by
    intro htA'
    apply h.g_not_mem
    have hgR : g ∈ R := by
      have e1 : g = t * (x ^ n)⁻¹ := by rw [ht]; group
      rw [e1]
      exact R.mul_mem (le_R_of_hyp91 h.toHyp91 htA') (R.inv_mem (R.pow_mem hxR n))
    exact h.isSylowOf.le hgR
  have hP3 : IsPGroup 3 (sec11P R g) := h.isPGroup_sec11P
  have ht3 : IsPGroup 3 (Subgroup.zpowers t) := hP3.to_le (Subgroup.zpowers_le.mpr
    (Subgroup.mem_inf.mp hgx).1)
  set T := Subgroup.zpowers t ⊓ A with hT
  have hTt : T ≤ Subgroup.zpowers t := inf_le_left
  have hrel : Nat.card T * T.relIndex (Subgroup.zpowers t) = Nat.card (Subgroup.zpowers t) := by
    have h1 := Subgroup.relIndex_mul_card T (Subgroup.zpowers t)
    rw [inf_of_le_left hTt] at h1
    rw [mul_comm]
    exact h1
  have hrel1 : T.relIndex (Subgroup.zpowers t) ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact htnA (h1 (Subgroup.mem_zpowers t)).2
  have hrel3 : 3 ≤ T.relIndex (Subgroup.zpowers t) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp ht3
    have hdvd : T.relIndex (Subgroup.zpowers t) ∣ 3 ^ m := by
      rw [← hm, ← hrel]
      exact Dvd.intro_left _ rfl
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hj] at hrel1 ⊢
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd (pow_zero 3) hrel1
    · calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj0
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hsup : Nat.card (Subgroup.zpowers t ⊔ A : Subgroup G) =
      27 * T.relIndex (Subgroup.zpowers t) := by
    apply Nat.eq_of_mul_eq_mul_right hTpos
    rw [hcard, ← hrel]
    ring
  calc 81 = 27 * 3 := by norm_num
    _ ≤ Nat.card (Subgroup.zpowers t ⊔ A : Subgroup G) := by
      rw [hsup]
      exact Nat.mul_le_mul_left 27 hrel3
    _ ≤ Nat.card (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
      Subgroup.card_le_of_le hle

theorem sec11K_swap_le_L (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {e : G}
    (he : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'') : sec11K Ye c ≤ L := by
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq he hecd hYe hKYe
  have hdK : d ∈ sec11K L e := hstdE.d_mem_sec11K h.inf_eq
  have hd1 : d ≠ 1 := (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).2.2
  have hKp : Group.IsPerfect (sec11K L e) := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hK1 : sec11K L e ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
  have hKL : sec11K L e ≤ L := sec11K_le L e
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hKK : sec11K L e ≤ sec11K Ye c :=
    Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKp (le_inf hKYe (hKL.trans hLc))
  have hY'' : Y'' = L := Sec6.eq_of_mem_thetaComponentsIn_of_le hstd.mem_thetaComponentsAt_Y
    h.mem_thetaComponentsAt hKp hK1 (hKK.trans hstd.sec11K_le) hKL
  rw [← hY'']
  exact hstd.sec11K_le

theorem inf_eq_zpowers_d_swap (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h : Sec11Data G A c L a R Y d x s r g) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'') : A ⊓ Ye = Subgroup.zpowers d := by
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq he hecd hYe hKYe
  have hdYe : d ∈ Ye := hKYe (hstdE.d_mem_sec11K h.inf_eq)
  have h3 := (h97 G A e Ye c R' hstd.toHyp91).1
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact ⟨Item1117Proof.d_mem_A h, hdYe⟩
  · rw [h3, Nat.card_zpowers, Item1117Proof.orderOf_d h]

theorem sec11Std_swap (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : Sec11Data G A c L a R Y d x s r g) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'')
    (hQ : IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G))
      (Subgroup.normalizer (Subgroup.zpowers e : Set G))) :
    Sec11Std G A e Ye c (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) L := by
  have hQW : sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer (A : Set G) := inf_le_left.trans (h.sec11P_le_normalizer_A h113)
  have hQsylW : IsSylowOf 3
      ((sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) ⊓ Subgroup.normalizer (A : Set G))
      (Subgroup.normalizer (Subgroup.zpowers e : Set G) ⊓ Subgroup.normalizer (A : Set G)) := by
    rw [inf_of_le_left hQW]
    exact hQ.of_le (le_inf hQ.le hQW) inf_le_left
  exact
    { toHyp91 := { hstd.toHyp91 with isSylowOf := hQ, isSylowOf_inf := hQsylW }
      isList1016 := hstd.isList1016
      mem_thetaComponentsAt_Y := h.mem_thetaComponentsAt
      sec11K_le := sec11K_swap_le_L h45 h he hecd hYe hKYe hstd }

theorem exists_sec11Data_swap (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h113 : Item113)
    (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'')
    (hQ : IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G))
      (Subgroup.normalizer (Subgroup.zpowers e : Set G))) :
    ∃ x' s' r' : G, (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) ⊓ Ye = Subgroup.zpowers x' ∧
      (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) ⊓ Sec4.thetaQuotCentralizer Ye =
        Subgroup.zpowers s' ∧
      Sec11Data G A e Ye c (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) L d x' s' r' x := by
  have hPW := h.sec11P_le_normalizer_A h113
  have hstd' := sec11Std_swap h45 h113 h he hecd hYe hKYe hstd hQ
  have hAYe := inf_eq_zpowers_d_swap h45 h97 h he hecd hYe hKYe hstd
  have hA' : A = Subgroup.closure {e, c, d} := by
    rw [h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq he hecd, Set.insert_comm]
  obtain ⟨x', hx'⟩ := hstd'.exists_zpowers_eq_inf_L
  obtain ⟨s', hs'⟩ := RChoice.exists_zpowers_eq_of_isCyclic
    (h113 G A e Ye c (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) L hstd').2
  obtain ⟨r', hr'R, hr'c⟩ := hstd'.exists_eq_closure h45 hAYe hA' hx' hs'
  have hxL : x ∈ L := by
    have hx : x ∈ R ⊓ L := by
      rw [h.inf_L_eq]
      exact Subgroup.mem_zpowers x
    exact hx.2
  have hxP : x ∈ sec11P R g := le_sup_left (a := R) (Item1116Proof.mem_R h).2.1
  have hxe : x * e * x⁻¹ ∈ Subgroup.closure ({e, d} : Set G) := by
    have e1 : x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
    rw [e1]
    exact Subgroup.mul_mem _
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) (conj_x_e_mem h he))
      (Subgroup.subset_closure (by simp))
  exact ⟨x', s', r', hx', hs',
    { toSec11Std := hstd'
      inf_eq := hAYe
      closure_eq := hA'
      inf_L_eq := hx'
      inf_centralizer_eq := hs'
      R_eq := hr'R
      a_mem_closure := hr'c
      pow_eq_one := Item1117Proof.x_pow_eq_one h
      g_mem := ⟨hxL, hPW hxP⟩
      g_mem_normalizer := x_mem_normalizer_inf h117 h hsc hrs he
      g_not_mem := x_not_mem_normalizer_e h45 h he hecd
      conj_mem := hxe }⟩

theorem eq_closure_of_out {e : G} {Ye Y' : Subgroup G} {x' s' r' g' : G}
    (hd : Sec11Data G A e Ye c (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) Y' d x' s' r' g')
    (hout : ∀ y ∈ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G),
      ∃ i : ℕ, c ^ i * y ∈ innerPreimage Ye) :
    sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) = Subgroup.closure {c, x', s'} := by
  have hinner := hd.toSec11Std.inf_innerPreimage_eq hd.inf_L_eq hd.inf_centralizer_eq
  have hcQ : c ∈ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_R_of_hyp91 hd.toHyp91 hd.a_mem
  obtain ⟨-, hx'Q, hs'Q⟩ := Item1116Proof.mem_R hd
  apply le_antisymm
  · intro y hy
    obtain ⟨i, hi⟩ := hout y hy
    have h1 : c ^ i * y ∈ (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G)) ⊓
        innerPreimage Ye :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.pow_mem _ hcQ i) hy, hi⟩
    rw [hinner] at h1
    have h2 : Subgroup.closure ({s', x'} : Set G) ≤ Subgroup.closure {c, x', s'} := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz <;> rw [hz] <;> exact Subgroup.subset_closure (by simp)
    have e1 : y = (c ^ i)⁻¹ * (c ^ i * y) := by group
    rw [e1]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) i)) (h2 h1)
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz <;> rw [hz]
    · exact hcQ
    · exact hx'Q
    · exact hs'Q

theorem pow_eq_one_of_mem_inf_centralizer (h45 : Sec4.Item4_5)
    (h : Sec11Data G A c L a R Y d x s r g) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye) {n : ℕ}
    (hn : orderOf x = 3 ^ (n + 1)) {t : G}
    (ht : t ∈ L ⊓ Subgroup.centralizer ({e} : Set G)) (ht3 : ∃ k : ℕ, t ^ 3 ^ k = 1) :
    t ^ 3 ^ n = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq he hecd hYe hKYe
  obtain ⟨k, hk⟩ := ht3
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  by_contra hne
  have hmn : n + 1 ≤ m := by
    by_contra hlt
    apply hne
    rw [← orderOf_dvd_iff_pow_eq_one, hm]
    exact pow_dvd_pow 3 (by omega)
  have htL : Subgroup.zpowers t ≤ L := Subgroup.zpowers_le.mpr ht.1
  have ht3' : IsPGroup 3 (Subgroup.zpowers t) := Item1117Proof.isPGroup_zpowers hk
  have hSyl := h.toSec11Std.isSylowOf_inf_L
  have hcard : Nat.card (R ⊓ L : Subgroup G) ≤ Nat.card (Subgroup.zpowers t) := by
    rw [h.inf_L_eq, Nat.card_zpowers, Nat.card_zpowers, hn, hm]
    exact Nat.pow_le_pow_right (by norm_num) hmn
  have htSyl := isSylowOf_of_card_le htL ht3' hSyl hcard
  apply Item1116Proof.not_le_centralizer_of_isSylowOf hstdE htSyl
  rw [Subgroup.zpowers_le]
  exact ht.2

theorem orderOf_dvd_of_swap (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {e : G} (he : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'') {x'' : G} (hx'' : R' ⊓ Ye = Subgroup.zpowers x'') :
    orderOf x'' ∣ orderOf x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k₀, hk₀⟩ := Item1117Proof.x_pow_eq_one h
  obtain ⟨n₁, -, hn₁⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk₀)
  have h9 := Item1117Proof.nine_dvd_orderOf_x h
  obtain ⟨n, rfl⟩ : ∃ n, n₁ = n + 1 := by
    rcases n₁ with _ | n
    · rw [hn₁, pow_zero] at h9
      norm_num at h9
    · exact ⟨n, rfl⟩
  have hx''mem : x'' ∈ R' ⊓ Ye := hx'' ▸ Subgroup.mem_zpowers x''
  have hcR' : c ∈ R' := le_R_of_hyp91 hstd.toHyp91 h.mem_A
  obtain ⟨hcN, hc3, -, hQ⟩ := hstd.a_facts
  have hcN' : c ∈ Subgroup.normalizer ((R' ⊓ Ye : Subgroup G) : Set G) :=
    Item1116Proof.mem_normalizer_inf (Subgroup.le_normalizer hcR') hcN
  have hcx : c * x'' * c⁻¹ ∈ Subgroup.zpowers x'' := by
    rw [← hx'']
    exact (Subgroup.mem_normalizer_iff.mp hcN' x'').mp hx''mem
  obtain ⟨k, hk⟩ := hstd.isSylowOf.isPGroup ⟨x'', hx''mem.1⟩
  have hk' : x'' ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcx3 := Item1117Proof.conj_pow_three_eq_of_pow_three_eq_one hc3 ⟨k, hk'⟩ hcx
  have hx3C : x'' ^ 3 ∈ Ye ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine ⟨Ye.pow_mem hx''mem.2 3, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc x'' ^ 3 * c = (c * x'' ^ 3 * c⁻¹) * c := by rw [hcx3]
      _ = c * x'' ^ 3 := by group
  have hx3k : (x'' ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]
  have hx3K : x'' ^ 3 ∈ sec11K Ye c := mem_sec11K_of_pow_eq_one hcN hc3 hQ.1 hx3C hx3k
  have hx3L : x'' ^ 3 ∈ L := sec11K_swap_le_L h45 h he hecd hYe hKYe hstd hx3K
  have hYee : Ye ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYe
  have h1 := pow_eq_one_of_mem_inf_centralizer h45 h he hecd hYe hKYe hn₁
    ⟨hx3L, hYee hx3C.1⟩ ⟨k, hx3k⟩
  rw [hn₁]
  apply orderOf_dvd_of_pow_eq_one
  rw [pow_succ', pow_mul]
  exact h1

theorem card_R_le_of_orderOf_le (h1116 : Item1116) (h : Sec11Data G A c L a R Y d x s r g)
    (hx9 : orderOf x ≤ 9) : Nat.card R ≤ 81 := by
  have hsr : Subgroup.zpowers s = Subgroup.zpowers c ∧
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} := by
    by_contra hne
    rw [not_and_or] at hne
    have := h1116 G A c L a R Y d x s r g h hne
    omega
  obtain ⟨hsc, hrs⟩ := hsr
  have hRle : R ≤ A ⊔ Subgroup.zpowers x := by
    intro y hy
    obtain ⟨m, u, hu, rfl⟩ := Item1117Proof.exists_eq_zpow_mul h hsc hrs hy
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x m))
      (Subgroup.mem_sup_left hu)
  have hAx : A ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro u hu
    obtain ⟨z, hz, hzu⟩ := Item1117Proof.exists_conj_x_of_mem_A h hu
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [hzu]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x)
      (Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_zpowers_x h) hz)
  have hcard := Sec6.card_sup_mul_card_inf hAx
  rw [h.card_eq, Nat.card_zpowers] at hcard
  have h3 : 3 ≤ Nat.card (A ⊓ Subgroup.zpowers x : Subgroup G) := by
    have hle : Subgroup.zpowers d ≤ A ⊓ Subgroup.zpowers x :=
      Subgroup.zpowers_le.mpr ⟨Item1117Proof.d_mem_A h, Item1117Proof.d_mem_zpowers_x h⟩
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, Item1117Proof.orderOf_d h] at this
  have hsup : Nat.card (A ⊔ Subgroup.zpowers x : Subgroup G) ≤ 81 := by
    by_contra hlt
    push Not at hlt
    have h1 : 82 * 3 ≤ Nat.card (A ⊔ Subgroup.zpowers x : Subgroup G) *
        Nat.card (A ⊓ Subgroup.zpowers x : Subgroup G) := Nat.mul_le_mul hlt h3
    rw [hcard] at h1
    have h2 : 27 * orderOf x ≤ 27 * 9 := Nat.mul_le_mul_left 27 hx9
    omega
  exact (Subgroup.card_le_of_le hRle).trans hsup

theorem isSylowOf_inf_of_card_le (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) (h1116 : Item1116) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hstd : Sec11Std G A e Ye c R' Y'') (hsmall : Nat.card (R' ⊓ Ye : Subgroup G) ≤ 9) :
    IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G))
      (Subgroup.normalizer (Subgroup.zpowers e : Set G)) := by
  obtain ⟨a', Y', d', x'', s'', r'', g'', hd⟩ :=
    sec11DataExists_of h97 h45 h113 h117 h119 G A e Ye c R' Y'' hstd
  have hx'' : orderOf x'' ≤ 9 := by
    rw [← Nat.card_zpowers, ← hd.inf_L_eq]
    exact hsmall
  have hR' := card_R_le_of_orderOf_le h1116 hd hx''
  have hle : sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    refine inf_le_right.trans ?_
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  exact isSylowOf_of_card_le hle (h.isPGroup_sec11P.to_le inf_le_left) hstd.isSylowOf
    (hR'.trans (le_card_inf_centralizer h45 h113 h117 h hsc hrs he hecd))

end Data

end Item1117StepsProof

section Main

open Item1117StepsProof in
theorem false_of_exchange (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) (h1116 : Item1116) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (heA : g * x * g⁻¹ * x⁻¹ ∈ A) (hecd : g * x * g⁻¹ * x⁻¹ ∉ Subgroup.closure {c, d})
    {Ye R' Y'' : Subgroup G} (hYe : Ye ∈ thetaComponentsAt 3 (g * x * g⁻¹ * x⁻¹))
    (hKYe : sec11K L (g * x * g⁻¹ * x⁻¹) ≤ Ye)
    (hstd : Sec11Std G A (g * x * g⁻¹ * x⁻¹) Ye c R' Y'')
    (hS : 9 < Nat.card (R' ⊓ Ye : Subgroup G) →
      IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G))
        (Subgroup.normalizer (Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) : Set G)))
    (hO : IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G))
        (Subgroup.normalizer (Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) : Set G)) →
      9 < Nat.card ((sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G)) ⊓ Ye :
        Subgroup G) →
      ∀ y ∈ sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G),
        ∃ i : ℕ, c ^ i * y ∈ innerPreimage Ye) : False := by
  have hQ : IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G))
      (Subgroup.normalizer (Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) : Set G)) := by
    by_cases hsmall : Nat.card (R' ⊓ Ye : Subgroup G) ≤ 9
    · exact isSylowOf_inf_of_card_le h45 h97 h113 h117 h119 h1116 h hsc hrs heA hecd hstd hsmall
    · push Not at hsmall
      exact hS hsmall
  obtain ⟨x', s', r', hx', -, hdata⟩ :=
    exists_sec11Data_swap h45 h97 h113 h117 h hsc hrs heA hecd hYe hKYe hstd hQ
  have hP' : sec11P (sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G)) x =
      sec11P R g := inf_sup_zpowers_x h45 h117 h hsc hrs heA hecd
  have hPP := Item1117Proof.commutator_eq_closure h117 h hsc hrs heA
  have key : ∀ r₁ : G, Sec11Data G A (g * x * g⁻¹ * x⁻¹) Ye c
      (sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G)) L d x' s' r₁ x →
      Subgroup.closure ({r₁, s'} : Set G) = Subgroup.closure {c, s'} → False := by
    intro r₁ hd hrs₁
    refine false_of_commutator_le_closure_c_d h45 h113 h117 hd hrs₁ ?_ ?_
    · rw [hP', hPP]
    · rw [hP', ← hPP]
      exact Item1117Proof.normalizer_le_normalizer_commutator _
  by_cases hbig : 9 < orderOf x'
  · have hcard : 9 < Nat.card ((sec11P R g ⊓ Subgroup.centralizer ({g * x * g⁻¹ * x⁻¹} : Set G)) ⊓
        Ye : Subgroup G) := by
      rw [hx', Nat.card_zpowers]
      exact hbig
    exact key c { hdata with
      R_eq := eq_closure_of_out hdata (hO hQ hcard)
      a_mem_closure := Subgroup.subset_closure (by simp) } rfl
  · refine key r' hdata ?_
    by_contra hne
    exact hbig (h1116 G A _ Ye c _ L d x' s' r' x hdata (Or.inr hne))

open Item1117StepsProof in
theorem gap1117SymmetrySwap_of_exchange (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h119 : Item119) (h1116 : Item1116)
    (hND : KFact1117Cube) (hS : Gap1117SwapSylow) (hO : Gap1117SwapOut) :
    Gap1117SymmetrySwap := by
  intro G _ _ A c L a R Y d x s r g h hsc hrs heA hecd hsym Ye R' Y'' hYe hKYe hstd
  have hx9 : ∀ (R₁ Y₁ : Subgroup G), Sec11Std G A (g * x * g⁻¹ * x⁻¹) Ye c R₁ Y₁ →
      9 < Nat.card (R₁ ⊓ Ye : Subgroup G) → 9 < orderOf x := by
    intro R₁ Y₁ hstd₁ hbig
    obtain ⟨x₁, hx₁⟩ := hstd₁.exists_zpowers_eq_inf_L
    have h1 := Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x))
      (orderOf_dvd_of_swap h45 h heA hecd hYe hKYe hstd₁ hx₁)
    rw [hx₁, Nat.card_zpowers] at hbig
    omega
  have hf : 9 < orderOf x → KFacts.InducesStdKind Y c .field := by
    intro hx9'
    by_contra hnf
    exact Item1117Proof.false_of_not_field h119 hND h hsc hrs hnf hx9'
  refine false_of_exchange h45 h97 h113 h117 h119 h1116 h hsc hrs heA hecd hYe hKYe hstd
    (fun hbig => ?_) fun hQ hbig => ?_
  · have h9 := hx9 R' Y'' hstd hbig
    exact hS G A c L a R Y d x s r g h hsc hrs heA hecd hsym Ye R' Y'' hYe hKYe hstd h9 (hf h9)
      hbig
  · have h9 := hx9 _ L (sec11Std_swap h45 h113 h heA hecd hYe hKYe hstd hQ) hbig
    exact hO G A c L a R Y d x s r g h hsc hrs heA hecd hsym Ye R' Y'' hYe hKYe hstd h9 (hf h9)
      hQ hbig

end Main

end CFSG.RankThree.PartTwo.Sec11
