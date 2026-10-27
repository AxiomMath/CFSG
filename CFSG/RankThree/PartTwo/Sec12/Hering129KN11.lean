module

public import CFSG.RankThree.PartTwo.Sec12.Hering129Defs
public import CFSG.RankThree.PartTwo.Sec12.Hering129KN3
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KN11

section Theta

variable {G : Type} [Group G] [Finite G]

theorem theta_centralizer_le (c : G) :
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  set K := Subgroup.centralizer ({c} : Set G)
  set D := Subgroup.normalizer (Subgroup.zpowers c : Set G)
  have hKD : K ≤ D := Sec13.centralizer_le_normalizer_zpowers c
  have hsn : (K.subgroupOf D).IsSubnormal :=
    (Sec13.centralizer_normal_in_normalizer_zpowers c).isSubnormal
  have h1 := CFSG.RankThree.solvable_prime_complement_core_subnormal_intersection
    Nat.prime_three hsn
  have h2 := congrArg (Subgroup.map D.subtype) h1
  have e1 := Sec6.map_inSubgroup_theta_of_injective D.subtype D.subtype_injective (K.subgroupOf D)
  rw [Subgroup.map_subgroupOf_eq_of_le hKD] at e1
  rw [e1, Subgroup.map_inf_eq _ _ D.subtype D.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hKD] at h2
  rw [h2]
  exact inf_le_right

theorem lBar_commute {c : G} {K L : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hL : L ∈ thetaComponentsAt 3 c) (hne : K ≠ L) {x y} (hx : x ∈ lBar c K)
    (hy : y ∈ lBar c L) : x * y = y * x := by
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hy
  obtain ⟨t, ht, hte⟩ := Hering129KN11.theta_centralizer_le c
    (Sec10.commutator_mem_theta_of_ne hK hL hne
    (Subgroup.mem_subgroupOf.mp hk) (Subgroup.mem_subgroupOf.mp hl))
  have htk : t = k * l * k⁻¹ * l⁻¹ := Subtype.ext (by simpa using hte)
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))) (k * l * k⁻¹ * l⁻¹) = 1 := by
    rw [← htk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ht
  simp only [map_mul, map_inv] at h1
  have h2 := congrArg (fun z => z * (QuotientGroup.mk' _ l * QuotientGroup.mk' _ k)) h1
  simp only [one_mul] at h2
  rw [← h2]
  group

end Theta

theorem exists_slPi_model {X : Type} [Group X] {q : TauCeti.PrimePower}
    (hq : Sec4.IsSLThreePiAt X q.card) (hqm : ¬ PiModNine q.card) :
    ∃ (π : Bool) (K : Type) (_ : Field K), Sec4.PiField π q.p q.exponent K ∧
      Sec4.ModThree π (q.p ^ q.exponent) ∧ ¬ Sec4.ModNine π (q.p ^ q.exponent) ∧
      Nonempty (X ≃* Sec4.slPi π 3 (q.p ^ q.exponent) K) := by
  rw [TauCeti.PrimePower.card_def] at hq hqm
  obtain ⟨K, _, -, hcase⟩ := hq
  rcases hcase with ⟨hK, hq3, ⟨e⟩⟩ | ⟨hK, hq3, ⟨e⟩⟩
  · exact ⟨true, K, inferInstance, ⟨q.prime_p, q.exponent_pos, hK⟩, hq3,
      fun h => hqm (Or.inl h), ⟨e⟩⟩
  · exact ⟨false, K, inferInstance, ⟨q.prime_p, q.exponent_pos, hK⟩, hq3,
      fun h => hqm (Or.inr h), ⟨e⟩⟩

theorem card_center_eq_three {X : Type} [Group X] {U : Subgroup X} {π : Bool} {p f : ℕ}
    {K : Type} [Field K] (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (e : ↥U ≃* Sec4.slPi π 3 (p ^ f) K) : Nat.card (Subgroup.center U) = 3 := by
  rw [← KFacts.card_center_slPi hK hq, ← Subgroup.map_center_eq e,
    Subgroup.card_map_of_injective e.injective]

theorem endLocalX_of_slPi {X : Type} [Group X] [Finite X] {U₁ U₂ : Subgroup X} {a b z t : X}
    (hcomm : ∀ u ∈ U₁, ∀ v ∈ U₂, u * v = v * u)
    {π₁ : Bool} {p₁ f₁ : ℕ} {K₁ : Type} [Field K₁] (hK₁ : Sec4.PiField π₁ p₁ f₁ K₁)
    (hq₁ : Sec4.ModThree π₁ (p₁ ^ f₁)) (h9₁ : ¬ Sec4.ModNine π₁ (p₁ ^ f₁))
    (e₁ : ↥U₁ ≃* Sec4.slPi π₁ 3 (p₁ ^ f₁) K₁)
    {π₂ : Bool} {p₂ f₂ : ℕ} {K₂ : Type} [Field K₂] (hK₂ : Sec4.PiField π₂ p₂ f₂ K₂)
    (hq₂ : Sec4.ModThree π₂ (p₂ ^ f₂)) (h9₂ : ¬ Sec4.ModNine π₂ (p₂ ^ f₂))
    (e₂ : ↥U₂ ≃* Sec4.slPi π₂ 3 (p₂ ^ f₂) K₂)
    (ha : a ∈ U₁) (hb : b ∈ U₂) (hz₁ : z ∈ U₁) (hz₂ : z ∈ U₂) (hz1 : z ≠ 1)
    (hzc₁ : ∀ u ∈ U₁, u * z = z * u) (hzc₂ : ∀ u ∈ U₂, u * z = z * u)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (haz : a ∉ Subgroup.zpowers z) (hbz : b ∉ Subgroup.zpowers z)
    (htU₁ : ∀ u ∈ U₁, t * u * t⁻¹ ∈ U₁) (htU₂ : ∀ u ∈ U₂, t * u * t⁻¹ ∈ U₂)
    (hta : t * a * t⁻¹ = a) (htb : t * b * t⁻¹ = b) (htz : t * z * t⁻¹ = z⁻¹)
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) :
    EndLocalX (U₁ ⊔ U₂) (a * b) t z := by
  have h1 : SLFactor U₁ a z := slFactor_of_slPi hK₁ hq₁ h9₁ e₁ ha hz₁ hz1 hzc₁ ha3 haz
  have hzi : ∀ u ∈ U₂, u * z⁻¹ = z⁻¹ * u := fun u hu => by
    have h := hzc₂ u hu
    calc u * z⁻¹ = z⁻¹ * (z * u) * z⁻¹ := by group
      _ = z⁻¹ * (u * z) * z⁻¹ := by rw [h]
      _ = z⁻¹ * u := by group
  have h2 : SLFactor U₂ b z⁻¹ := slFactor_of_slPi hK₂ hq₂ h9₂ e₂ hb (inv_mem hz₂)
    (inv_ne_one.mpr hz1) hzi hb3 (by rwa [Subgroup.zpowers_inv])
  have hU : ∀ u, u ∈ U₁ → u ∈ U₂ → u ∈ Subgroup.zpowers z := by
    intro u hu₁ hu₂
    have hZ : Nat.card (Subgroup.center U₁) = 3 :=
      Hering129KN11.card_center_eq_three hK₁ hq₁ e₁
    let z' : U₁ := ⟨z, hz₁⟩
    have hz'Z : z' ∈ Subgroup.center U₁ :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc₁ g g.2)
    have hz'3 : z' ^ 3 = 1 := Subtype.ext (by simpa using h1.hz3)
    have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have heq : Subgroup.zpowers z' = Subgroup.center U₁ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz'Z)
        (by rw [hZ, Nat.card_zpowers, orderOf_eq_prime hz'3 hz'1])
    have hu : (⟨u, hu₁⟩ : U₁) ∈ Subgroup.center U₁ :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcomm g g.2 u hu₂)
    rw [← heq] at hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact endLocalX_of_factors hcomm hU h1 h2 htU₁ htU₂ hta htb htz ht2

end Hering129KN11

theorem endLocalX_lBar {G : Type} [Group G] [Finite G] {A : Subgroup G} {c a b t : G}
    {L J : Subgroup G} {q r : TauCeti.PrimePower}
    (hL : L ∈ thetaComponentsAt 3 c) (hJ : J ∈ thetaComponentsAt 3 c) (hLJ : L ≠ J)
    (hcL : c ∈ L) (hcJ : c ∈ J) (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A)
    (haA : a ∈ A) (hbA : b ∈ A) (hc1 : c ≠ 1) (haL : a ∈ L) (hbJ : b ∈ J)
    (hac : a ∉ Subgroup.zpowers c) (hbc : b ∉ Subgroup.zpowers c)
    (hq : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card) (hqm : ¬ PiModNine q.card)
    (hr : Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) r.card) (hrm : ¬ PiModNine r.card)
    (htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L) (htJ : ∀ j ∈ J, t * j * t⁻¹ ∈ J)
    (hta : t * a = a * t) (htb : t * b = b * t) (htc : t * c * t⁻¹ = c⁻¹)
    (ht2 : IsPGroup 2 (Subgroup.zpowers t))
    {xN tN cN : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))}
    (hxN : (xN : G) = a * b) (htN : (tN : G) = t) (hcN : (cN : G) = c) :
    EndLocalX (lBar c L ⊔ lBar c J)
      (QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) xN)
      (QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) tN)
      (QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) cN) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hc3 : c ^ 3 = 1 := hAel.2 c hcA
  have hLN := Sec13.le_normalizer_zpowers_of_mem hL
  have hJN := Sec13.le_normalizer_zpowers_of_mem hJ
  have hLC := Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hJC := Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  obtain ⟨aN, haN⟩ : ∃ aN : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G)),
      (aN : G) = a := ⟨⟨a, hLN haL⟩, rfl⟩
  obtain ⟨bN, hbN⟩ : ∃ bN : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G)),
      (bN : G) = b := ⟨⟨b, hJN hbJ⟩, rfl⟩
  have hxab : xN = aN * bN := Subtype.ext (by rw [hxN, Subgroup.coe_mul, haN, hbN])
  rw [hxab, map_mul]
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3
    (Subgroup.normalizer (Subgroup.zpowers c : Set G))) with hπ
  obtain ⟨π₁, K₁, _, hK₁, hq₁, h9₁, ⟨φ₁⟩⟩ := Hering129KN11.exists_slPi_model hq hqm
  obtain ⟨π₂, K₂, _, hK₂, hq₂, h9₂, ⟨φ₂⟩⟩ := Hering129KN11.exists_slPi_model hr hrm
  obtain ⟨η₁, -⟩ := Sec13.exists_lBarEquiv hL
  obtain ⟨η₂, -⟩ := Sec13.exists_lBarEquiv hJ
  have hA3 : IsPGroup 3 ↥(A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
    fun x => ⟨1, Subtype.ext (Subtype.ext (by simpa using hAel.2 _ x.2))⟩
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hA3
  have hnz : ∀ {y : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))} {g : G}, (y : G) = g →
      g ∈ A → g ∉ Subgroup.zpowers c → π y ∉ Subgroup.zpowers (π cN) := by
    intro y g hy hgA hgc h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← map_zpow] at hk
    have h1 : cN ^ k = y := hinj (Subgroup.mem_subgroupOf.mpr (by
      rw [Subgroup.coe_zpow, hcN]; exact zpow_mem hcA k))
      (Subgroup.mem_subgroupOf.mpr (by rw [hy]; exact hgA)) hk
    exact hgc (Subgroup.mem_zpowers_iff.mpr ⟨k, by
      rw [← hy, ← h1, Subgroup.coe_zpow, hcN]⟩)
  have hz1 : π cN ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have hord : orderOf cN = 3 := by
      rw [← Subgroup.orderOf_coe, hcN]
      exact orderOf_eq_prime hc3 hc1
    have hdvd := Subgroup.orderOf_dvd_natCard _ h
    rw [hord] at hdvd
    exact CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore hdvd
  have hmem : ∀ {M : Subgroup G} {y : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))}
      {g : G}, (y : G) = g → g ∈ M → π y ∈ lBar c M := fun hy hg =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hy ▸ hg))
  have hzc : ∀ {M : Subgroup G}, M ≤ Subgroup.centralizer ({c} : Set G) →
      ∀ u ∈ lBar c M, u * π cN = π cN * u := by
    rintro M hMC _ ⟨l, hl, rfl⟩
    have hlc := Subgroup.mem_centralizer_singleton_iff.mp (hMC (Subgroup.mem_subgroupOf.mp hl))
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hcN, hlc])
  have htU : ∀ {M : Subgroup G}, (∀ m ∈ M, t * m * t⁻¹ ∈ M) →
      ∀ u ∈ lBar c M, π tN * u * (π tN)⁻¹ ∈ lBar c M := by
    rintro M htM _ ⟨l, hl, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    refine hmem rfl ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, htN]
    exact htM _ (Subgroup.mem_subgroupOf.mp hl)
  have htg : ∀ {y : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))} {g : G}, (y : G) = g →
      t * g = g * t → π tN * π y * (π tN)⁻¹ = π y := by
    intro y g hy htg
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, htN, hy, htg,
        mul_inv_cancel_right])
  have htz : π tN * π cN * (π tN)⁻¹ = (π cN)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, htN, hcN, htc])
  have ht2' : IsPGroup 2 (Subgroup.zpowers (π tN)) := by
    obtain ⟨k, hk⟩ := ht2 ⟨t, Subgroup.mem_zpowers t⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have htk' : π tN ^ 2 ^ k = 1 := by
      have h1 : tN ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, htN, htk]; rfl)
      rw [← map_pow, h1, map_one]
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htk', one_zpow]
  have hpow3 : ∀ {y : ↥(Subgroup.normalizer (Subgroup.zpowers c : Set G))} {g : G}, (y : G) = g →
      g ^ 3 = 1 → π y ^ 3 = 1 := by
    intro y g hy hg3
    have h1 : y ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hy, hg3]; rfl)
    rw [← map_pow, h1, map_one]
  exact Hering129KN11.endLocalX_of_slPi
    (fun u hu v hv => Hering129KN11.lBar_commute hL hJ hLJ hu hv)
    hK₁ hq₁ h9₁ (η₁.symm.trans φ₁) hK₂ hq₂ h9₂ (η₂.symm.trans φ₂)
    (hmem haN haL) (hmem hbN hbJ) (hmem hcN hcL) (hmem hcN hcJ) hz1
    (hzc hLC) (hzc hJC) (hpow3 haN ha3) (hpow3 hbN hb3) (hnz haN haA hac) (hnz hbN hbA hbc)
    (htU htL) (htU htJ) (htg haN hta) (htg hbN htb) htz ht2'

end CFSG.RankThree.PartTwo.Sec12
