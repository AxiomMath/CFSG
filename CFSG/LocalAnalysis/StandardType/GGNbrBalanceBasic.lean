module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceNestedTransport
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceMinimalLifts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification

section Components

variable {G : Type*} [Group G]

theorem isSubnormal_le_of_assembly {A B : Subgroup G} (h : IsSubnormal A B) : A ≤ B :=
  LBalance.subnormal_le ((AssemblyBPredicates.isSubnormal_iff_open A B).1 h)

theorem isComponentOf_of_isSubnormal_of_isComponentOf {J A B : Subgroup G}
    (hJ : IsComponentOf J A) (hA : IsSubnormal A B) : IsComponentOf J B :=
  ⟨hJ.1.trans (isSubnormal_le_of_assembly hA),
    LocalAnalysis.ComponentInitial.assembly_isSubnormal_trans hJ.2.1 hA, hJ.2.2⟩

theorem isComponentOf_le_or_commutator_eq_bot [Finite G] {K N H : Subgroup G}
    (hK : IsComponentOf K H) (hN : IsSubnormal N H) : K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  have hNH : N ≤ H := isSubnormal_le_of_assembly hN
  have hK' :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hK.1).1 hK
  have hN' : (N.subgroupOf H).IsSubnormal := by
    rw [← AssemblyBPredicates.isSubnormal_top_iff_mathlib,
      AssemblyBPredicates.isSubnormal_iff_open, LBalance.subnormal_subgroupOf_iff hNH,
      ← AssemblyBPredicates.isSubnormal_iff_open]
    exact hN
  rcases CFSG.LocalCores.component_subnormal_subgroup hK' hN' with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hK.1 h)
  · right
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_eq_left.mpr hNH] at h1

theorem commutator_self_eq_of_isQuasisimple {K : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple K) :
    ⁅K, K⁆ = K := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  exact Subgroup.commutator_eq_self

theorem commutator_ne_bot_of_isQuasisimple {K : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple K) :
    ⁅K, K⁆ ≠ ⊥ := by
  rw [commutator_self_eq_of_isQuasisimple hK]
  intro hbot
  have : Nontrivial K := Quasisimple.nontrivial hK
  obtain ⟨a, b, hab⟩ := exists_pair_ne K
  apply hab
  have ha : (a : G) ∈ (⊥ : Subgroup G) := hbot ▸ a.2
  have hb : (b : G) ∈ (⊥ : Subgroup G) := hbot ▸ b.2
  rw [Subgroup.mem_bot] at ha hb
  exact Subtype.ext (ha.trans hb.symm)

end Components

section Vocabulary

variable {G : Type*} [Group G]

theorem largeEvenPComponent_iff_lBalance (p : ℕ) (X L : Subgroup G) :
    LargeEvenPComponent p X L ↔ L ≤ X ∧ CFSG.Open.lBalanceIsPComponent p X L := by
  constructor
  · rintro ⟨hLX, hs, hc, hmin⟩
    refine ⟨hLX, (LBalance.pComponent_iff_minimal_image p X L hLX).2
      ⟨(AssemblyBPredicates.isSubnormal_iff_open L X).1 hs,
        ⟨hc.1, (AssemblyBPredicates.isSubnormal_iff_open _ _).1 hc.2.1, hc.2.2⟩, ?_⟩⟩
    intro J hJL hJ heq
    by_contra hne
    exact hmin J (lt_of_le_of_ne hJL hne) ((AssemblyBPredicates.isSubnormal_iff_open J X).2 hJ)
      heq
  · rintro ⟨hLX, hL⟩
    obtain ⟨hs, hc, hmin⟩ := (LBalance.pComponent_iff_minimal_image p X L hLX).1 hL
    refine ⟨hLX, (AssemblyBPredicates.isSubnormal_iff_open L X).2 hs,
      ⟨hc.1, (AssemblyBPredicates.isSubnormal_iff_open _ _).2 hc.2.1, hc.2.2⟩, ?_⟩
    intro J hJL hJ heq
    exact hJL.ne (hmin J hJL.le ((AssemblyBPredicates.isSubnormal_iff_open J X).1 hJ) heq)

theorem largeEvenPLayer_eq_lBalancePLayer (p : ℕ) (X : Subgroup G) :
    LargeEvenPLayer p X = CFSG.Open.lBalancePLayer p X :=
  congrArg sSup (Set.ext fun L =>
    ⟨fun h => ((largeEvenPComponent_iff_lBalance p X L).1 h).2,
      fun h => (largeEvenPComponent_iff_lBalance p X L).2 ⟨LBalance.subnormal_le h.1, h⟩⟩)

end Vocabulary


section Images

variable {G : Type*} [Group G]

theorem le_lBalancePrimeCore_of_commutator_quotientImage {p : ℕ} {Y A : Subgroup G}
    (hAY : A ≤ Y) (hA : ⁅A, A⁆ = A)
    (hc : ⁅LBalance.quotientImage p Y A, LBalance.quotientImage p Y A⁆ = ⊥) :
    A ≤ CFSG.Open.lBalancePrimeCore p Y := by
  have hderived : (⁅A, A⁆).subgroupOf Y = ⁅A.subgroupOf Y, A.subgroupOf Y⁆ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self A).trans hAY),
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAY]
  have h1 : LBalance.quotientImage p Y ⁅A, A⁆ =
      ⁅LBalance.quotientImage p Y A, LBalance.quotientImage p Y A⁆ := by
    unfold LBalance.quotientImage
    rw [hderived, Subgroup.map_commutator]
  have h2 : LBalance.quotientImage p Y A = ⊥ := by
    rw [← hc, ← h1, hA]
  have h3 : A.subgroupOf Y ≤ CFSG.pPrimeCore p ↥Y := by
    have h4 := (Subgroup.map_eq_bot_iff _).mp h2
    rwa [QuotientGroup.ker_mk'] at h4
  rw [LBalance.primeCore_eq_map]
  intro a ha
  exact ⟨⟨a, hAY ha⟩, h3 (Subgroup.mem_subgroupOf.mpr ha), rfl⟩

theorem isSubnormal_quotientImage {p : ℕ} {Y A : Subgroup G} (hA : IsSubnormal A Y) :
    CFSG.Open.IsSubnormal (LBalance.quotientImage p Y A) ⊤ := by
  have hchain : CFSG.Open.IsSubnormal (A.subgroupOf Y) ⊤ :=
    (LBalance.subnormal_subgroupOf_iff (isSubnormal_le_of_assembly hA)).2
      ((AssemblyBPredicates.isSubnormal_iff_open A Y).1 hA)
  have h := Components.chain_map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥Y)) hchain
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h

theorem commutator_quotientImage_eq_bot {p : ℕ} {Y A : Subgroup G} (hA : ⁅A, A⁆ = ⊥) :
    ⁅LBalance.quotientImage p Y A, LBalance.quotientImage p Y A⁆ = ⊥ := by
  unfold LBalance.quotientImage
  rw [← Subgroup.map_commutator]
  have h : ⁅A.subgroupOf Y, A.subgroupOf Y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hab : (a : G) ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hA (Subgroup.mem_subgroupOf.mp ha)
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hab) b (Subgroup.mem_subgroupOf.mp hb))
  rw [h, Subgroup.map_bot]

theorem commutator_eq_bot_of_subgroupOf_le_center {A A' : Subgroup G}
    (h : A'.subgroupOf A ≤ Subgroup.center A) (hA'A : A' ≤ A) : ⁅A', A'⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hz := Subgroup.mem_center_iff.mp (h (show (⟨a, hA'A ha⟩ : A) ∈ A'.subgroupOf A from ha))
    ⟨b, hA'A hb⟩
  exact congrArg Subtype.val hz

theorem lBalanceIsPComponent_of_isComponentOf [Finite G] {p : ℕ} {Y J : Subgroup G}
    (hJ : IsComponentOf J Y) (hJO : ¬ J ≤ CFSG.Open.lBalancePrimeCore p Y) :
    CFSG.Open.lBalanceIsPComponent p Y J := by
  have hJY : J ≤ Y := hJ.1
  have hq : CFSG.Open.IsQuasisimple J := hJ.2.2
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJ.2.2
  rw [LBalance.pComponent_iff_minimal_image p Y J hJY]
  refine ⟨(AssemblyBPredicates.isSubnormal_iff_open J Y).1 hJ.2.1,
    ⟨le_top, isSubnormal_quotientImage hJ.2.1, ?_⟩, ?_⟩
  · let f : J →* ↥Y ⧸ CFSG.pPrimeCore p ↥Y :=
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥Y)).comp (Subgroup.inclusion hJY)
    have hker : f.ker ≠ ⊤ := by
      intro htop
      apply hJO
      rw [LBalance.primeCore_eq_map]
      intro j hj
      have hj1 : f ⟨j, hj⟩ = 1 := (MonoidHom.mem_ker).mp (htop ▸ Subgroup.mem_top _)
      have hj2 : (⟨j, hJY hj⟩ : Y) ∈ CFSG.pPrimeCore p ↥Y :=
        (QuotientGroup.eq_one_iff _).mp hj1
      exact ⟨⟨j, hJY hj⟩, hj2, rfl⟩
    have hrange : f.range = LBalance.quotientImage p Y J := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨j, hJY j.2⟩, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
    exact Components.quasisimple_of_equiv (MulEquiv.subgroupCongr hrange).symm
      (Quasisimple.range_quasisimple_of_ker_ne_top hq f hker)
  · intro J' hJ'J hJ' heq
    have hsub : CFSG.Open.IsSubnormal (J'.subgroupOf J) ⊤ := by
      have h := LBalance.subnormal_subgroupOf hJ' J
      rwa [(Subgroup.subgroupOf_eq_top).mpr hJY] at h
    rcases Quasisimple.subnormal_le_center_or_eq_top hq (J'.subgroupOf J) hsub with hc | htop
    · exfalso
      apply hJO
      refine le_lBalancePrimeCore_of_commutator_quotientImage hJY hJJ ?_
      rw [← heq]
      exact commutator_quotientImage_eq_bot (commutator_eq_bot_of_subgroupOf_le_center hc hJ'J)
    · exact le_antisymm hJ'J ((Subgroup.subgroupOf_eq_top).mp htop)

theorem lBalanceIsPComponent_eq_or_commute [Finite G] {p : ℕ} {X K K' : Subgroup G}
    (hK : IsComponentOf K X) (hKO : ¬ K ≤ CFSG.Open.lBalancePrimeCore p X)
    (hK' : CFSG.Open.lBalanceIsPComponent p X K') : K' = K ∨ ⁅K', K⁆ = ⊥ := by
  have hK'X : K' ≤ X := LBalance.subnormal_le hK'.1
  have hK'sn : IsSubnormal K' X := (AssemblyBPredicates.isSubnormal_iff_open K' X).2 hK'.1
  rcases isComponentOf_le_or_commutator_eq_bot hK hK'sn with hle | hc
  · left
    by_contra hne
    have hlt : K < K' := lt_of_le_of_ne hle (Ne.symm hne)
    apply hK'.2.2 K hlt ((AssemblyBPredicates.isSubnormal_iff_open K X).1 hK.2.1)
    rw [← LBalance.quotientImage_eq_iff p X hK.1 hK'X]
    have hC'q : CFSG.Open.IsQuasisimple (LBalance.quotientImage p X K') :=
      (LBalance.pComponent_image p X K' hK').2.2
    have hCC' : LBalance.quotientImage p X K ≤ LBalance.quotientImage p X K' :=
      Subgroup.map_mono fun z hz => hle hz
    have hsub : CFSG.Open.IsSubnormal
        ((LBalance.quotientImage p X K).subgroupOf (LBalance.quotientImage p X K')) ⊤ := by
      have h := LBalance.subnormal_subgroupOf (isSubnormal_quotientImage (p := p) hK.2.1)
        (LBalance.quotientImage p X K')
      rwa [Subgroup.top_subgroupOf] at h
    rcases Quasisimple.subnormal_le_center_or_eq_top hC'q _ hsub with hcen | htop
    · exfalso
      exact hKO (le_lBalancePrimeCore_of_commutator_quotientImage hK.1
        (commutator_self_eq_of_isQuasisimple hK.2.2)
        (commutator_eq_bot_of_subgroupOf_le_center hcen hCC'))
    · exact le_antisymm hCC' ((Subgroup.subgroupOf_eq_top).mp htop)
  · right
    rwa [Subgroup.commutator_comm]

theorem lBalancePLayer_le_sup_centralizer [Finite G] {p : ℕ} {X K : Subgroup G}
    (hK : IsComponentOf K X) (hKO : ¬ K ≤ CFSG.Open.lBalancePrimeCore p X) :
    CFSG.Open.lBalancePLayer p X ≤ K ⊔ Subgroup.centralizer (K : Set G) :=
  sSup_le fun K' hK' => by
    rcases lBalanceIsPComponent_eq_or_commute hK hKO hK' with h | h
    · rw [h]
      exact le_sup_left
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans le_sup_right

theorem not_le_lBalancePrimeCore_of_dvd [Finite G] {p : ℕ} [Fact p.Prime] {Y A : Subgroup G}
    (hA : p ∣ Nat.card A) : ¬ A ≤ CFSG.Open.lBalancePrimeCore p Y := fun h =>
  (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (LBalance.primeCore_coprime p Y)
    (hA.trans (Subgroup.card_dvd_of_le h))

end Images


section Central

open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutatorElement_mul_mul_of_commute {a b c d : G} (hac : Commute a c)
    (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ * ⁅c, d⁆ := by
  have h1 : a * c * (b * d) = a * b * (c * d) := by
    rw [mul_assoc a c, ← mul_assoc c b, ← hbc.eq, mul_assoc b c, ← mul_assoc a b]
  have h2 : b * d * (a * c) = b * a * (d * c) := by
    rw [mul_assoc b d, ← mul_assoc d a, ← had.eq, mul_assoc a d, ← mul_assoc b a]
  have hc : Commute c (b * a) := hbc.symm.mul_right hac.symm
  have hd : Commute d (b * a) := hbd.symm.mul_right had.symm
  have h3 : Commute (c * d * c⁻¹ * d⁻¹) (b * a) :=
    ((hc.mul_left hd).mul_left hc.inv_left).mul_left hd.inv_left
  calc ⁅a * c, b * d⁆ = a * c * (b * d) * (b * d * (a * c))⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = a * b * (c * d) * (b * a * (d * c))⁻¹ := by rw [h1, h2]
    _ = a * b * (c * d * c⁻¹ * d⁻¹) * (b * a)⁻¹ := by group
    _ = a * b * (b * a)⁻¹ * (c * d * c⁻¹ * d⁻¹) := by
        rw [mul_assoc (a * b), h3.inv_right.eq, ← mul_assoc]
    _ = ⁅a, b⁆ * ⁅c, d⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group

theorem commutatorElement_mem_of_mem {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem exists_mul_eq_of_mem_sup_centralizer {K : Subgroup G} {g : G}
    (hg : g ∈ K ⊔ Subgroup.centralizer (K : Set G)) :
    ∃ k ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set G), k * c = g := by
  have h : g ∈ ((K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K _ (Subgroup.centralizer_le_normalizer _)]
    at h
  obtain ⟨k, hk, c, hc, hkc⟩ := h
  exact ⟨k, hk, c, hc, hkc⟩

theorem commute_of_mem_centralizer {K : Subgroup G} {k c : G} (hk : k ∈ K)
    (hc : c ∈ Subgroup.centralizer (K : Set G)) : Commute k c :=
  Subgroup.mem_centralizer_iff.mp hc k hk

theorem exists_conj_eq_mul_center {K : Subgroup G} {x k c : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K)
    (hc : c ∈ Subgroup.centralizer (K : Set G)) (hj : x * (k * c) = k * c * x) :
    ∃ z ∈ K, z ∈ Subgroup.centralizer (K : Set G) ∧ x * k * x⁻¹ = k * z := by
  have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer K hxK
  have hk' : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxK k).mp hk
  have hc' : x * c * x⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hxC c).mp hc
  have heq : x * k * x⁻¹ * (x * c * x⁻¹) = k * c := by
    calc x * k * x⁻¹ * (x * c * x⁻¹) = x * (k * c) * x⁻¹ := by group
      _ = k * c * x * x⁻¹ := by rw [hj]
      _ = k * c := by group
  refine ⟨k⁻¹ * (x * k * x⁻¹), K.mul_mem (K.inv_mem hk) hk', ?_, by group⟩
  have hz : k⁻¹ * (x * k * x⁻¹) = c * (x * c * x⁻¹)⁻¹ := by
    calc k⁻¹ * (x * k * x⁻¹) = k⁻¹ * (x * k * x⁻¹ * (x * c * x⁻¹)) * (x * c * x⁻¹)⁻¹ := by
          group
      _ = c * (x * c * x⁻¹)⁻¹ := by rw [heq]; group
  rw [hz]
  exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc')

theorem le_centralizer_of_le_sup_centralizer {K J : Subgroup G} {x : G} (hJJ : ⁅J, J⁆ = J)
    (hJK : J ≤ K ⊔ Subgroup.centralizer (K : Set G))
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hJC : ⁅J, K ⊓ Subgroup.centralizer ({x} : Set G)⁆ = ⊥) :
    J ≤ Subgroup.centralizer (K : Set G) := by
  set C := Subgroup.centralizer (K : Set G) with hCdef
  set U := K ⊓ Subgroup.centralizer ({x} : Set G) with hUdef
  have hxj : ∀ j ∈ J, x * j = j * x := fun j hj =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hJx hj)).symm
  have hJU : J ≤ U ⊔ C := by
    rw [← hJJ, Subgroup.commutator_le]
    intro j₁ hj₁ j₂ hj₂
    obtain ⟨k₁, hk₁, c₁, hc₁, rfl⟩ := exists_mul_eq_of_mem_sup_centralizer (hJK hj₁)
    obtain ⟨k₂, hk₂, c₂, hc₂, rfl⟩ := exists_mul_eq_of_mem_sup_centralizer (hJK hj₂)
    rw [commutatorElement_mul_mul_of_commute (commute_of_mem_centralizer hk₁ hc₁)
      (commute_of_mem_centralizer hk₁ hc₂) (commute_of_mem_centralizer hk₂ hc₁)
      (commute_of_mem_centralizer hk₂ hc₂)]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
      (Subgroup.mem_sup_right (commutatorElement_mem_of_mem hc₁ hc₂))
    · exact commutatorElement_mem_of_mem hk₁ hk₂
    · obtain ⟨z₁, hz₁K, hz₁C, hz₁⟩ := exists_conj_eq_mul_center hxK hk₁ hc₁ (hxj _ hj₁)
      obtain ⟨z₂, hz₂K, hz₂C, hz₂⟩ := exists_conj_eq_mul_center hxK hk₂ hc₂ (hxj _ hj₂)
      have hconj : x * ⁅k₁, k₂⁆ * x⁻¹ = ⁅k₁, k₂⁆ := by
        have h := map_commutatorElement (MulAut.conj x) k₁ k₂
        simp only [MulAut.conj_apply] at h
        rw [h, hz₁, hz₂, commutatorElement_mul_mul_of_commute
          (commute_of_mem_centralizer hk₁ hz₁C) (commute_of_mem_centralizer hk₁ hz₂C)
          (commute_of_mem_centralizer hk₂ hz₁C) (commute_of_mem_centralizer hk₂ hz₂C),
          (commutatorElement_eq_one_iff_mul_comm).mpr
            (commute_of_mem_centralizer hz₁K hz₂C).eq, mul_one]
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ⁅k₁, k₂⁆ * x = x * ⁅k₁, k₂⁆ * x⁻¹ * x := by rw [hconj]
        _ = x * ⁅k₁, k₂⁆ := by group
  have hUC : C ≤ Subgroup.normalizer (U : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (show (U : Set G) ⊆ K from fun u hu => hu.1) hc)
  rw [← hJJ, Subgroup.commutator_le]
  intro j₁ hj₁ j₂ hj₂
  have hdec : ∀ j ∈ J, ∃ u ∈ U, ∃ c ∈ C, u * c = j := fun j hj => by
    have h : j ∈ ((U ⊔ C : Subgroup G) : Set G) := hJU hj
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U C hUC] at h
    obtain ⟨u, hu, c, hc, huc⟩ := h
    exact ⟨u, hu, c, hc, huc⟩
  obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := hdec j₁ hj₁
  obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := hdec j₂ hj₂
  rw [commutatorElement_mul_mul_of_commute (commute_of_mem_centralizer hu₁.1 hc₁)
    (commute_of_mem_centralizer hu₁.1 hc₂) (commute_of_mem_centralizer hu₂.1 hc₁)
    (commute_of_mem_centralizer hu₂.1 hc₂)]
  have hcomm : u₁ * u₂ = u₂ * u₁ := by
    have h1 : u₁ * c₁ ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJC hj₁
    have h2 : u₂ * (u₁ * c₁) = u₁ * c₁ * u₂ := Subgroup.mem_centralizer_iff.mp h1 u₂ hu₂
    have h3 : c₁ * u₂ = u₂ * c₁ := (commute_of_mem_centralizer hu₂.1 hc₁).eq.symm
    have h4 : u₂ * u₁ * c₁ = u₁ * u₂ * c₁ := by
      calc u₂ * u₁ * c₁ = u₁ * c₁ * u₂ := by rw [mul_assoc, h2]
        _ = u₁ * u₂ * c₁ := by rw [mul_assoc, h3, ← mul_assoc]
    exact (mul_right_cancel h4).symm
  rw [(commutatorElement_eq_one_iff_mul_comm).mpr hcomm, one_mul]
  exact commutatorElement_mem_of_mem hc₁ hc₂

end Central

end CFSG.StandardType

end
