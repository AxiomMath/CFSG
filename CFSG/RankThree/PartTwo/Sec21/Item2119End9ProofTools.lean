module

import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofWeak
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ
import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofJ

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace Item2119End9Proof

variable {G : Type} [Group G] [Finite G]

theorem card_le_card_inf_mul_card_centralizer {X K : Subgroup G} {e : G} (heX : e ∈ X)
    (hcomm : ∀ x ∈ X, x * e * x⁻¹ * e⁻¹ ∈ K) :
    Nat.card X ≤ Nat.card (X ⊓ K : Subgroup G) *
      Nat.card (X ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
  classical
  set C : Subgroup X := (X ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf X with hCdef
  have hC : Nat.card C = Nat.card (X ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmem : ∀ x : X, (x : G) * e * (x : G)⁻¹ * e⁻¹ ∈ X ⊓ K := fun x =>
    ⟨X.mul_mem (X.mul_mem (X.mul_mem x.2 heX) (X.inv_mem x.2)) (X.inv_mem heX),
      hcomm x x.2⟩
  let f₀ : X → (X ⊓ K : Subgroup G) := fun x => ⟨(x : G) * e * (x : G)⁻¹ * e⁻¹, hmem x⟩
  have hkey : ∀ a b : X, a⁻¹ * b ∈ C ↔ f₀ a = f₀ b := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨-, hc⟩
      have hc' : ((a : G)⁻¹ * b) * e = e * ((a : G)⁻¹ * b) := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hc
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
      apply Subtype.ext
      change (a : G) * e * (a : G)⁻¹ * e⁻¹ = (b : G) * e * (b : G)⁻¹ * e⁻¹
      have hb : (b : G) = a * ((a : G)⁻¹ * b) := by group
      rw [hb]
      calc (a : G) * e * (a : G)⁻¹ * e⁻¹
          = (a : G) * (((a : G)⁻¹ * b) * e * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ * e⁻¹ := by
            rw [hc']; group
        _ = (a * ((a : G)⁻¹ * b)) * e * (a * ((a : G)⁻¹ * b))⁻¹ * e⁻¹ := by group
    · intro h
      have h' : (a : G) * e * (a : G)⁻¹ * e⁻¹ = (b : G) * e * (b : G)⁻¹ * e⁻¹ :=
        congrArg Subtype.val h
      refine ⟨(a⁻¹ * b).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h2 : (a : G) * e * (a : G)⁻¹ = (b : G) * e * (b : G)⁻¹ := mul_right_cancel h'
      calc ((a : G)⁻¹ * b) * e = (a : G)⁻¹ * ((b : G) * e * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * e * (a : G)⁻¹) * b := by rw [h2]
        _ = e * ((a : G)⁻¹ * b) := by group
  let f : X ⧸ C → (X ⊓ K : Subgroup G) :=
    Quotient.lift f₀ fun a b hab => (hkey a b).mp (QuotientGroup.leftRel_apply.mp hab)
  have hf : Function.Injective f := by
    intro p q
    induction p using Quotient.inductionOn with | h a => ?_
    induction q using Quotient.inductionOn with | h b => ?_
    intro h
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hkey a b).mpr h))
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have h2 : Nat.card (X ⧸ C) ≤ Nat.card (X ⊓ K : Subgroup G) :=
    Nat.card_le_card_of_injective f hf
  calc Nat.card X = Nat.card (X ⧸ C) * Nat.card C := h1
    _ ≤ Nat.card (X ⊓ K : Subgroup G) * Nat.card C := Nat.mul_le_mul_right _ h2
    _ = _ := by rw [hC]

theorem card_le_mul_81 {A : Subgroup G} {d : G} {F : G → Subgroup G}
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d)
    {X K : Subgroup G} (hX3 : IsPGroup 3 X) (heX : e ∈ X)
    (hcomm : ∀ x ∈ X, x * e * x⁻¹ * e⁻¹ ∈ K) :
    Nat.card X ≤ Nat.card (X ⊓ K : Subgroup G) * 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h81 : Nat.card (A ⊔ F e : Subgroup G) = 81 := (hQ.2.2.2.2 e he hed).1
  have hC : Nat.card (X ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ≤ 81 := by
    have h := Item2119End6Proof.card_le_three_pow_of_isPGroup
      (inf_le_right : X ⊓ Subgroup.centralizer ({e} : Set G) ≤ _) hX3.to_inf_left
    rwa [← (h27 e he hed).card_eq, h81] at h
  calc Nat.card X ≤ Nat.card (X ⊓ K : Subgroup G) *
        Nat.card (X ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
        card_le_card_inf_mul_card_centralizer heX hcomm
    _ ≤ Nat.card (X ⊓ K : Subgroup G) * 81 := Nat.mul_le_mul_left _ hC

theorem exists_ne_one_mem_comm {T R : Subgroup G} (hT : IsPGroup 3 T) (hRT : R ≤ T)
    (hRn : T ≤ Subgroup.normalizer (R : Set G)) (hR : R ≠ ⊥) :
    ∃ z ∈ R, z ≠ 1 ∧ ∀ t ∈ T, t * z = z * t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnorm : (R.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRT).mpr hRn
  have hne : R.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hR
    rw [eq_bot_iff]
    intro q hq
    have h1 : (⟨q, hRT hq⟩ : T) ∈ R.subgroupOf T := hq
    rw [hbot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)
  have hS := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨x, hxS⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS
  refine ⟨(x : G), hxS.1, fun h => hx1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  have h := (Subgroup.mem_center_iff.mp hxS.2) ⟨t, ht⟩
  exact congrArg Subtype.val h

omit [Finite G] in
theorem eq_one_of_sq_of_isPGroup {T : Subgroup G} (hT : IsPGroup 3 T) {w : G} (hw : w ∈ T)
    (hw2 : w * w = 1) : w = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨w, hw⟩
  rw [Subgroup.orderOf_mk] at hk
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  rw [hk] at h2
  have hk0 : k = 0 := by
    by_contra hne
    have h3 : 3 ∣ 3 ^ k := dvd_pow_self 3 hne
    have := Nat.le_of_dvd (by norm_num) (h3.trans h2)
    omega
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem eq_one_of_mem_centralizer_of_inv {D : Subgroup G} {e t : G}
    (he3 : IsPGroup 3 (Subgroup.zpowers e)) (heD : e ∈ Subgroup.normalizer (D : Set G))
    (het : e * t = t * e) (htD : ∀ x ∈ D, t * x * t⁻¹ = x⁻¹)
    (hD : ∀ R : Subgroup G, IsPGroup 3 R → R ≤ Subgroup.centralizer ({e} : Set G) →
      R ≤ Subgroup.centralizer (D : Set G) → R ≤ D)
    {z : G} (hzD : z ∈ Subgroup.centralizer (D : Set G))
    (hzt : z ∈ Subgroup.centralizer ({t} : Set G)) (hz3 : z ^ 3 = 1) : z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hz1
  set Z := Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hZdef
  have heZ : e ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hcD : y ∈ Subgroup.centralizer (D : Set G) ↔
        e * y * e⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
      simp only [Subgroup.mem_centralizer_iff]
      constructor
      · intro h x hx
        have hx' : e⁻¹ * x * e ∈ D := by
          have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heD) x).mp hx
          simpa only [inv_inv] using h1
        have h2 := h _ hx'
        calc x * (e * y * e⁻¹) = e * ((e⁻¹ * x * e) * y) * e⁻¹ := by group
          _ = e * (y * (e⁻¹ * x * e)) * e⁻¹ := by rw [h2]
          _ = e * y * e⁻¹ * x := by group
      · intro h x hx
        have hx' : e * x * e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp heD x).mp hx
        have h2 := h _ hx'
        calc x * y = e⁻¹ * ((e * x * e⁻¹) * (e * y * e⁻¹)) * e := by group
          _ = e⁻¹ * ((e * y * e⁻¹) * (e * x * e⁻¹)) * e := by rw [h2]
          _ = y * x := by group
    have het' : e * t * e⁻¹ = t := by rw [het]; group
    have hct : y ∈ Subgroup.centralizer ({t} : Set G) ↔
        e * y * e⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have het'' : e⁻¹ * t * e = t := by
          calc e⁻¹ * t * e = e⁻¹ * (e * t * e⁻¹) * e := by rw [het']
            _ = t := by group
        calc e * y * e⁻¹ * t = e * y * (e⁻¹ * t * e) * e⁻¹ := by group
          _ = e * (y * t) * e⁻¹ := by rw [het'']; group
          _ = e * (t * y) * e⁻¹ := by rw [h]
          _ = (e * t * e⁻¹) * (e * y * e⁻¹) := by group
          _ = t * (e * y * e⁻¹) := by rw [het']
      · intro h
        calc y * t = e⁻¹ * ((e * y * e⁻¹) * (e * t * e⁻¹)) * e := by group
          _ = e⁻¹ * ((e * y * e⁻¹) * t) * e := by rw [het']
          _ = e⁻¹ * (t * (e * y * e⁻¹)) * e := by rw [h]
          _ = e⁻¹ * ((e * t * e⁻¹) * (e * y * e⁻¹)) * e := by rw [het']
          _ = t * y := by group
    exact ⟨fun h => ⟨hcD.mp h.1, hct.mp h.2⟩, fun h => ⟨hcD.mpr h.1, hct.mpr h.2⟩⟩
  set K := Z ⊔ Subgroup.zpowers e with hKdef
  have hKN : K ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr heZ)
  obtain ⟨S, hS, heS⟩ := Item2119End5Proof.exists_isSylowOf_ge
    (le_sup_right : Subgroup.zpowers e ≤ K) he3
  have hSZ : IsSylowOf 3 (S ⊓ Z) Z := hS.inf_of_le_normalizer le_sup_left hKN
  have hS3 : IsPGroup 3 S := hS.isPGroup
  have hzZ : z ∈ Z := ⟨hzD, hzt⟩
  have hne : S ⊓ Z ≠ ⊥ := by
    intro hbot
    have hcard := hSZ.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hz : orderOf (⟨z, hzZ⟩ : Z) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hz3 hz1
    have hdvd : 3 ∣ Nat.card Z := hz ▸ orderOf_dvd_natCard (⟨z, hzZ⟩ : Z)
    have hpos : (Nat.card Z).factorization 3 ≠ 0 := by
      have hZpos : Nat.card Z ≠ 0 := Nat.card_pos.ne'
      exact (Nat.Prime.factorization_pos_of_dvd Nat.prime_three hZpos hdvd).ne'
    have : 3 ^ (Nat.card Z).factorization 3 ≠ 1 := by
      intro h
      exact hpos (Nat.pow_eq_one.mp h |>.resolve_left (by norm_num))
    exact this hcard.symm
  have hSN : S ≤ Subgroup.normalizer ((S ⊓ Z : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyS, hyZ⟩
      exact ⟨S.mul_mem (S.mul_mem hs hyS) (S.inv_mem hs),
        (Subgroup.mem_normalizer_iff.mp (hKN (hS.le hs)) y).mp hyZ⟩
    · rintro ⟨hyS, hyZ⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hKN (hS.le hs)) y).mpr hyZ⟩
      have : y = s⁻¹ * (s * y * s⁻¹) * s := by group
      rw [this]
      exact S.mul_mem (S.mul_mem (S.inv_mem hs) hyS) hs
  obtain ⟨w, ⟨hwS, hwZ⟩, hw1, hwc⟩ := exists_ne_one_mem_comm hS3 inf_le_left hSN hne
  have hwe : e * w = w * e := hwc e (heS (Subgroup.mem_zpowers e))
  have hwR : Subgroup.zpowers w ≤ D := by
    refine hD _ (hS3.to_le (Subgroup.zpowers_le.mpr hwS)) ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hwe.symm
    · rw [Subgroup.zpowers_le]
      exact hwZ.1
  have hwD : w ∈ D := hwR (Subgroup.mem_zpowers w)
  have h1 : t * w * t⁻¹ = w⁻¹ := htD w hwD
  have h2 : t * w * t⁻¹ = w := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hwZ.2).symm]
    group
  have hw2 : w * w = 1 := by
    have : w = w⁻¹ := h2.symm.trans h1
    calc w * w = w * w⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel w
  exact hw1 (eq_one_of_sq_of_isPGroup hS3 hwS hw2)

theorem F_eq_sup {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) {Lf F : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)))
    (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F)
    (h28 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) :
    F e = Subgroup.zpowers e ⊔ (F e ⊓ Lf e) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have he3 : e ^ 3 = 1 := hAe.2 e he
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  obtain ⟨hFe, hF27, -, -, -⟩ := hF e he hed
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have heF : e ∈ F e := Item2119End8Proof.mem_F hAe hA27 h27 hQ hF he hed
  have hH9 := (Item2119End8Proof.facts_H (hF e he hed) (hLf e he hed) h26 (h28 e he hed)).1
  obtain ⟨eL⟩ := h26
  obtain ⟨hLe, -, -, ⟨eLe⟩, -⟩ := hLf e he hed
  have hZ : Subgroup.center (lBar (Lf e)) = ⊥ :=
    Item2119End3Proof.center_eq_bot_of_mulEquiv' (eLe.trans eL)
      (Item21Early2Proof.center_projSL_three_eq_bot (by norm_num) (by decide))
  have heL : e ∉ Lf e := Item2119End3Proof.not_mem_of_mem_thetaComponentsAt hLe hZ he3 he1
  set H := F e ⊓ Lf e with hHdef
  have hcomm : ∀ x ∈ Subgroup.zpowers e, ∀ y ∈ H, x * y = y * x := by
    intro x hx y hy
    exact hFc x ((Subgroup.zpowers_le.mpr heF) hx) y hy.1
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hZe : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he3 he1]
  have hinf : Nat.card (Subgroup.zpowers e ⊓ H : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers e ⊓ H : Subgroup G) ∣ 3 :=
      hZe ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.zpowers e ⊓ H = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZe, h])
      have hmem : e ∈ Subgroup.zpowers e ⊓ H := by
        rw [heq]
        exact Subgroup.mem_zpowers e
      exact heL hmem.2.2
  rw [hinf, mul_one, hZe, hH9] at hcard
  have hle : Subgroup.zpowers e ⊔ H ≤ F e :=
    sup_le (Subgroup.zpowers_le.mpr heF) inf_le_left
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF27, hcard])).symm

theorem le_of_le_centralizer_of_le {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) {Lf F : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)))
    (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F)
    (h28 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hHD : F e ⊓ Lf e ≤ D)
    (heD : e ∉ Subgroup.centralizer (D : Set G)) {R : Subgroup G} (hR3 : IsPGroup 3 R)
    (hRe : R ≤ Subgroup.centralizer ({e} : Set G))
    (hRD : R ≤ Subgroup.centralizer (D : Set G)) : R ≤ F e ⊓ Lf e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have he3 : e ^ 3 = 1 := hAe.2 e he
  have hFeq := F_eq_sup hE hLf h26 hF h27 hQ h28 he hed
  set H := F e ⊓ Lf e with hHdef
  have hRF : R ≤ Subgroup.centralizer (F e : Set G) := by
    rw [hFeq]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    have hle : Subgroup.zpowers e ⊔ H ≤ Subgroup.centralizer ({r} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hRe hr)).symm
      · intro h hh
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hRD hr)) h (hHD hh))
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
  have hRFe : R ≤ F e :=
    Item2119End8Proof.le_F_of_le_centralizer hAe hA27 h27 hQ hF he hed hR3 hRF
  intro r hr
  have hrF : r ∈ ((Subgroup.zpowers e ⊔ H : Subgroup G) : Set G) := by
    rw [← hFeq]
    exact hRFe hr
  have hcomm : ∀ x ∈ Subgroup.zpowers e, ∀ y ∈ H, x * y = y * x := by
    obtain ⟨hFe, -⟩ := hF e he hed
    intro x hx y hy
    have heF : e ∈ F e := Item2119End8Proof.mem_F hAe hA27 h27 hQ hF he hed
    exact congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, (Subgroup.zpowers_le.mpr heF) hx⟩
      ⟨y, hy.1⟩)
  rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2] at hrF
  obtain ⟨x, hx, h, hh, rfl⟩ := hrF
  have hxD : x ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := (Subgroup.mem_centralizer_iff.mp (hRD hr)) y hy
    have h2 : h * y = y * h := hDc h (hHD hh) y hy
    have h3 : y * (x * h) = (x * h) * y := h1
    calc y * x = y * (x * h) * h⁻¹ := by group
      _ = (x * h) * y * h⁻¹ := by rw [h3]
      _ = x * (h * y) * h⁻¹ := by group
      _ = x * (y * h) * h⁻¹ := by rw [h2]
      _ = x * y := by group
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  by_cases hi : e ^ i = 1
  · simp only [hi, one_mul]
    exact hh
  · exfalso
    apply heD
    have heZ : e ∈ Subgroup.zpowers (e ^ i) :=
      Item21Late2Proof.mem_zpowers_of_mem he3 (Subgroup.zpow_mem_zpowers e i) hi
        (Subgroup.mem_zpowers e)
    exact (Subgroup.zpowers_le.mpr hxD) heZ

end Item2119End9Proof

end CFSG.RankThree.PartTwo.Sec21
