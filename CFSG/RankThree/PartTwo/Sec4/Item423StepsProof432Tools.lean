module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item432Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section WeakClosure

variable {G : Type} [Group G] [Finite G] {Z : Subgroup G}

theorem le_normalizer_of_isPGroup
    (hwc : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) →
      Z.map (MulAut.conj g).toMonoidHom = Z)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hZQ : Z ≤ Q) :
    Q ≤ Subgroup.normalizer (Z : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent Q := hQ.isNilpotent
  set P : Subgroup Q := (Subgroup.normalizer (Z : Set G)).subgroupOf Q with hP
  have hself : Subgroup.normalizer (P : Set Q) = P := by
    refine le_antisymm (fun y hy => ?_) Subgroup.le_normalizer
    rw [hP, Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff_map_conj_eq]
    apply hwc
    rintro _ ⟨a, ha, rfl⟩
    have haP : (⟨a, hZQ ha⟩ : Q) ∈ P :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.le_normalizer ha)
    have h1 := (Subgroup.mem_normalizer_iff.mp hy _).mp haP
    rw [hP, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := Q))) P hself
  intro x hx
  have hx' : (⟨x, hx⟩ : Q) ∈ P := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hx'

theorem map_conj_eq_of_le
    (hwc : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) →
      Z.map (MulAut.conj g).toMonoidHom = Z)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hZQ : Z ≤ Q) {g : G}
    (hgQ : Z.map (MulAut.conj g).toMonoidHom ≤ Q) : Z.map (MulAut.conj g).toMonoidHom = Z :=
  hwc g (hgQ.trans (le_normalizer_of_isPGroup hwc hQ hZQ))

theorem commute_of_mem_zpowers {z q : G} (hz : orderOf z = 3) (hq : ∃ k : ℕ, q ^ 3 ^ k = 1)
    (hqz : q * z * q⁻¹ ∈ Subgroup.zpowers z) : q * z = z * q := by
  classical
  obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hqz)
  rw [hz, Finset.mem_range] at hj
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  interval_cases j
  · exfalso
    have h1 : q * z * q⁻¹ = 1 := by rw [← hjz, pow_zero]
    have h2 : z = 1 := by
      have e : z = q⁻¹ * (q * z * q⁻¹) * q := by group
      rw [e, h1]
      group
    rw [h2, orderOf_one] at hz
    norm_num at hz
  · rw [pow_one] at hjz
    calc q * z = q * z * q⁻¹ * q := by group
      _ = z * q := by rw [← hjz]
  · have e1 : q * z * q⁻¹ = z⁻¹ := by
      rw [← hjz]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz3])
    have h2 : q ^ 2 * z = z * q ^ 2 := by
      have e2 : q ^ 2 * z * (q ^ 2)⁻¹ = q * (q * z * q⁻¹) * q⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      have e3 : q ^ 2 * z * (q ^ 2)⁻¹ = z := by
        rw [e2, e1, show q * z⁻¹ * q⁻¹ = (q * z * q⁻¹)⁻¹ by group, e1, inv_inv]
      calc q ^ 2 * z = q ^ 2 * z * (q ^ 2)⁻¹ * q ^ 2 := by group
        _ = z * q ^ 2 := by rw [e3]
    obtain ⟨k, hk⟩ := hq
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    have hcop : Nat.Coprime 2 (orderOf q) := by
      rw [hi]
      exact Nat.Coprime.pow_right i (by norm_num)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact ((Commute.pow_left h2 m).eq)

theorem le_centralizer_of_le_normalizer {z : G} (hz : orderOf z = 3) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q)
    (hQN : Q ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :
    Q ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  intro q hq
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  have hk' : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hqz : q * z * q⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.mp (hQN hq) z).mp (Subgroup.mem_zpowers z)
  exact commute_of_mem_zpowers hz ⟨k, hk'⟩ hqz

theorem le_centralizer_of_isPGroup {z : G} (hz : orderOf z = 3)
    (hwc : ∀ g : G, (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) →
      (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hzQ : z ∈ Q) :
    Q ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
  le_centralizer_of_le_normalizer hz hQ
    (le_normalizer_of_isPGroup hwc hQ (Subgroup.zpowers_le.mpr hzQ))

end WeakClosure

theorem not_three_dvd_card_of_isPerfect {X : Type*} [Group X] [Finite X]
    (hX : Group.IsPerfect X) (P : Sylow 3 X) (hP : (P : Subgroup X) ≤ Subgroup.center X) :
    ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  have htr : ∀ g : X, g ^ (Subgroup.center X).index = 1 := by
    intro g
    have hker := Abelianization.commutator_subset_ker (MonoidHom.transferCenterPow X)
    rw [Group.isPerfect_def.mp hX] at hker
    have hg := hker (Subgroup.mem_top g)
    rw [MonoidHom.mem_ker] at hg
    have := congrArg Subtype.val hg
    rwa [MonoidHom.transferCenterPow_apply] at this
  have hidx : ¬ 3 ∣ (Subgroup.center X).index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hP))
  have hPc : Nat.card (P : Subgroup X) = 3 ^ (Nat.card X).factorization 3 :=
    Sylow.card_eq_multiplicity P
  have hpos : 0 < (Nat.card X).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
  have hnt : Nontrivial (P : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPc]
    exact Nat.one_lt_pow hpos.ne' (by norm_num)
  obtain ⟨⟨g, hgP⟩, hg1⟩ := exists_ne (1 : (P : Subgroup X))
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hgP⟩
  have hgk : g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (3 ^ k) (Subgroup.center X).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx)
  have hg : g ^ Nat.gcd (3 ^ k) (Subgroup.center X).index = 1 :=
    pow_gcd_eq_one.mpr ⟨hgk, htr g⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
  exact hg1 (Subtype.ext hg)

section Components

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_isComponent (hO : CFSG.pPrimeCore 3 G = ⊥) {z : G}
    (hz : orderOf z = 3)
    (hwc : ∀ g : G, (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) →
      (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z)
    {L : Subgroup G} (hL : IsComponent L) : z ∈ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hzL
  set c : G ≃* G := MulAut.conj z with hc
  set L₁ := L.map c.toMonoidHom with hL₁def
  set L₂ := L₁.map c.toMonoidHom with hL₂def
  have hL₁ : IsComponent L₁ := LocalCores.isComponent_map_mulEquiv c hL
  have hL₂ : IsComponent L₂ := LocalCores.isComponent_map_mulEquiv c hL₁
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hL₃ : L₂.map c.toMonoidHom = L := by
    rw [hL₂def, hL₁def, Subgroup.map_map, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id L]
    congr 1
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hc,
      MulAut.conj_apply, MonoidHom.id_apply]
    have e : z * (z * (z * x * z⁻¹) * z⁻¹) * z⁻¹ = z ^ 3 * x * (z ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hz3]
    group
  have hne01 : L ≠ L₁ := fun h => hzL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hne12 : L₁ ≠ L₂ := fun h => hne01 (Subgroup.map_injective c.injective h)
  have hne02 : L ≠ L₂ := fun h => hne01 (by
    calc L = L₂.map c.toMonoidHom := hL₃.symm
      _ = L.map c.toMonoidHom := by rw [← h]
      _ = L₁ := rfl)
  have c01 := (LocalCores.distinct_components_commute hL₁ hL).resolve_left hne01.symm
  have c02 := (LocalCores.distinct_components_commute hL₂ hL).resolve_left hne02.symm
  have c12 := (LocalCores.distinct_components_commute hL₁ hL₂).resolve_left hne12
  have h1C : L₁ ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp c01
  have h2C : L₂ ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp c02
  set K := L ⊔ L₁ ⊔ L₂ with hK
  have hKL : K ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (h1C.trans (Subgroup.centralizer_le_normalizer _)))
      (h2C.trans (Subgroup.centralizer_le_normalizer _))
  have hzK : z ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change K.map c.toMonoidHom = K
    rw [hK, Subgroup.map_sup, Subgroup.map_sup, hL₃]
    change L₁ ⊔ L₂ ⊔ L = L ⊔ L₁ ⊔ L₂
    rw [sup_comm, ← sup_assoc]
  set Z := Subgroup.zpowers z with hZ
  set Y := K ⊔ Z with hY
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hzK)
  have hZ3 : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨S, hS, hZS⟩ := Sec13.Item134SylowBarProof.exists_isSylowOf_le
    (le_sup_right : Z ≤ Y) hZ3
  have hSK : IsSylowOf 3 (S ⊓ K) K := hS.inf_of_le_normalizer le_sup_left hYK
  have hLK : L ≤ K := le_sup_left.trans le_sup_left
  have hSL : IsSylowOf 3 (S ⊓ K ⊓ L) L := hSK.inf_of_le_normalizer hLK hKL
  have hSZ : S ≤ Subgroup.centralizer (Z : Set G) :=
    le_centralizer_of_isPGroup hz hwc hS.isPGroup (hZS (Subgroup.mem_zpowers z))
  have hT : ∀ t ∈ S ⊓ K ⊓ L, t ∈ L₁ := by
    intro t ht
    have htz : z * t = t * z := by
      have h := Subgroup.mem_centralizer_iff.mp (hSZ ht.1.1) z (Subgroup.mem_zpowers z)
      exact h
    have hmem : z * t * z⁻¹ ∈ L₁ := ⟨t, ht.2, rfl⟩
    rwa [htz, mul_inv_cancel_right] at hmem
  obtain ⟨P, hP⟩ := hSL.exists_sylow_eq_subgroupOf
  have hPc : (P : Subgroup L) ≤ Subgroup.center L := by
    rw [hP]
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have htL₁ := hT _ (Subgroup.mem_subgroupOf.mp ht)
    exact (Subgroup.mem_centralizer_iff.mp (h1C htL₁) g g.2)
  have h3 : ¬ 3 ∣ Nat.card L := not_three_dvd_card_of_isPerfect hL.1.1 P hPc
  have hLc := GH74.GLS.le_pPrimeCore_of_subnormal 3 hL.2
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  rw [hO] at hLc
  have := LocalCores.isQuasisimple_nontrivial hL.1
  obtain ⟨⟨x, hxL⟩, hx1⟩ := exists_ne (1 : L)
  exact hx1 (Subtype.ext (Subgroup.mem_bot.mp (hLc hxL)))

theorem isPGroup_center_of_isSubnormal (hO : CFSG.pPrimeCore 3 G = ⊥) {K : Subgroup G}
    (hK : K.IsSubnormal) : IsPGroup 3 (Subgroup.center K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨z, hz⟩
  have hn0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  set z0 : K := z ^ (3 ^ a) with hz0
  have hz0ord : orderOf z0 = m := by
    have := orderOf_pow_of_dvd (x := z) (n := 3 ^ a) (by positivity) (hn ▸ Dvd.intro _ rfl)
    rw [hz0, this, hn]
    simp [Nat.mul_div_cancel_left _ (by positivity : 0 < 3 ^ a)]
  have hz0central : z0 ∈ Subgroup.center K := Subgroup.pow_mem _ hz _
  let Z0 : Subgroup K := Subgroup.zpowers z0
  have hZ0le : Z0 ≤ Subgroup.center K := (Subgroup.zpowers_le).mpr hz0central
  have hZ0n : Z0.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := Subgroup.mem_center_iff.mp (hZ0le hn) g
    rw [this, mul_inv_cancel_right]
    exact hn
  set Z1 : Subgroup G := Z0.map K.subtype with hZ1
  have hZ1sub : Z1.IsSubnormal := by
    refine Subgroup.IsSubnormal.step Z1 K ?_ hK ?_
    · rintro _ ⟨k, -, rfl⟩
      exact k.2
    · have : Z1.subgroupOf K = Z0 :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective Z0
      rw [this]
      exact hZ0n
  have hcard : Nat.card Z1 = m := by
    rw [hZ1, Subgroup.card_map_of_injective K.subtype_injective, Nat.card_zpowers, hz0ord]
  have hcop : Nat.Coprime 3 (Nat.card Z1) := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm
  have hle := GH74.GLS.le_pPrimeCore_of_subnormal 3 hZ1sub hcop
  rw [hO, le_bot_iff] at hle
  have hZ0bot : Z0 = ⊥ :=
    Subgroup.map_injective K.subtype_injective (by rw [Subgroup.map_bot]; exact hle)
  have hz01 : z0 = 1 := by
    have : z0 ∈ Z0 := Subgroup.mem_zpowers z0
    rw [hZ0bot, Subgroup.mem_bot] at this
    exact this
  have hm1 : m = 1 := by rw [← hz0ord, hz01, orderOf_one]
  refine ⟨a, Subtype.ext ?_⟩
  have : z ^ (3 ^ a) = 1 := by
    have h1 : orderOf z = 3 ^ a := by rw [hn, hm1, mul_one]
    rw [← h1]
    exact pow_orderOf_eq_one z
  simpa using this

end Components

end CFSG.RankThree.PartTwo.Sec4.Item432Proof
