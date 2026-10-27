module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518Canon
public import CFSG.Quasithin.Vol2.Ch5Sec1DSC
public import CFSG.Quasithin.Vol2.Ch5Sec1L34F112Four
public import CFSG.Quasithin.H13.NQCatF112G2
public import CFSG.Quasithin.H13.NQCatF112D4
public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DSSz
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Am

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def F112L2FourChiefD4FactC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
      (IsLieOverTwo .trialityD4 0 2) →
    IsL2Quot (3 * 2) (oTwoQuot ↥L1) →
    IsSpecialPow 2 (2 ^ 2) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) →
    IsL2Quot 2 (oTwoQuot ↥L2) → Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ 2) ^ 11 →
    ∀ Z₀ : Subgroup G, Z₀ ≠ ⊥ → Z₀ ≤ centerOf S → Z₀ ≤ Subgroup.centralizer (L2 : Set G) →
      ∀ n : ℕ, IsChiefSeriesFrom L2 (pCoreOf 2 L2) (pCoreOf 2 L2) n → n ≤ 2

theorem f112L2FourChiefG2FactC_holds :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
        (IsG2Over 2) →
      IsL2Quot 2 (oTwoQuot ↥L1) → IsL2Quot 2 (oTwoQuot ↥L2) →
      IsSpecialPow 2 (2 ^ 2) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) →
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ 2) ^ 5 →
      ∀ Li : Subgroup G, (Li = L1 ∨ Li = L2) →
        ∀ Z₀ : Subgroup G, Z₀ ≠ ⊥ → Z₀ ≤ centerOf S → Z₀ ≤ Subgroup.centralizer (Li : Set G) →
          ∀ n : ℕ, IsChiefSeriesFrom Li (pCoreOf 2 Li) (pCoreOf 2 Li) n → n ≤ 2 := by
  intro G _ _ L1 L2 S hH _ hL1 hL2 hsp hcard Li hLi _ _ _ _ n hn
  have hq : IsL2Quot 2 (oTwoQuot ↥Li) := by
    rcases hLi with rfl | rfl
    · exact hL1
    · exact hL2
  have hO : Nat.card (pCoreOf 2 Li) ≤ (2 ^ 2) ^ 5 := by
    rcases hLi with rfl | rfl
    · rw [show (2 ^ 2) ^ 5 = (2 ^ 2) ^ (1 + 2 * 2) by norm_num, ← hsp.2.1]
      exact Subgroup.card_le_of_le hH.pCoreOf_le_pCoreOf_vertex
    · rw [← hcard]
      have h2 := hH.symm.pCoreOf_le_pCoreOf_vertex
      rw [bigB_comm] at h2
      exact Subgroup.card_le_of_le h2
  have h16 := NQCat.F112G2.sixteen_pow_le_card
    (fun L N hs hnc => NQCat.F112G2.sixteen_le_relIndex hq hs hnc) hn
  by_contra hlt
  rw [not_le] at hlt
  have h3 : 16 ^ 3 ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
  have := h3.trans (h16.trans hO)
  norm_num at this

theorem f112L2FourChiefU4FactC_holds :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
      (IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
          (IsLieOverTwo .PSU 4 2) ∨
        IsU4ExtTwo 2 (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))) →
      IsL2Quot 2 (oTwoQuot ↥L1) →
      IsSpecialPow 2 (2 ^ 2) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) →
      IsBlock2 L2 L2 → IsL2Quot (2 * 2) (oTwoQuot ↥L2) → IsOmega4MinusType L2 2 →
      ∀ Z₀ : Subgroup G, Z₀ ≠ ⊥ → Z₀ ≤ centerOf S → Z₀ ≤ Subgroup.centralizer (L1 : Set G) →
        ∀ n : ℕ, IsChiefSeriesFrom L1 (pCoreOf 2 L1) (pCoreOf 2 L1) n → n ≤ 2 := by
  intro G _ _ L1 L2 S hH _ hL1 hsp _ _ _ _ _ _ _ n hn
  have hO : Nat.card (pCoreOf 2 L1) ≤ (2 ^ 2) ^ 5 :=
    (Subgroup.card_le_of_le hH.pCoreOf_le_pCoreOf_vertex).trans (hsp.2.1.le.trans (by norm_num))
  have h16 := NQCat.F112G2.sixteen_pow_le_card
    (fun L N hs hnc => NQCat.F112G2.sixteen_le_relIndex hL1 hs hnc) hn
  by_contra hlt
  rw [not_le] at hlt
  have h3 : 16 ^ 3 ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
  have := h3.trans (h16.trans hO)
  norm_num at this

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13.NQCat.F112D4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239.Lie

section Main

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

theorem f112L2FourChiefD4FactC_holds
    : F112L2FourChiefD4FactC := by
  intro G _ _ L1 L2 S hH hA _ _ hL2 _ Z₀ hZ₀ hZS hZC n hn
  exfalso
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ₀
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzS : z ∈ S := (hZS hz).1
  have hzL : ∀ l ∈ L2, l * z = z * l := Subgroup.mem_centralizer_iff.1 (hZC hz)
  set PB := L2 ⊔ bigB L1 L2 S with hPB
  have hzPB : z ∈ PB := Subgroup.mem_sup_right (Subgroup.mem_sup_right hzS)
  have hL2PB : L2 ≤ PB := le_sup_left
  have hPBN : PB ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer (sup_le (sup_le hH.h2.borel_le
      (inf_le_left.trans Subgroup.le_normalizer)) hH.h2.normalizes)
  have hL2n : (L2.subgroupOf PB).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL2PB).2 hPBN
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨ι⟩⟩ := hA
  have hYm : ChevalleyExceptionalModel Y .trialityD4 2 2 := by
    rcases hY with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · simp [classicalTags] at h
    · exact h
    · simp [reeTitsTags] at h
    · exact absurd h (by decide)
  obtain ⟨-, K₀, _, _, σ₀, -, -, ⟨e₀⟩⟩ := exists_mulEquiv_triality_model hYm
  have : Finite (ModGL TwistTag.D4.tag K₀) := finite_modGL
  have : Finite Y := Finite.of_equiv _ e₀.symm.toEquiv
  obtain ⟨K, _, _, σ, φ, hK, hσ, -, hres, -⟩ := even_rank_two_residual_triality hYm hpair.1
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK64 : Nat.card K = 2 ^ 6 := by rw [hK]; norm_num
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK64
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    have : Fintype K := Fintype.ofFinite K
    have hpow : c ^ 64 = c := by
      have := FiniteField.pow_card c
      rwa [← Nat.card_eq_fintype_card, hK64] at this
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    exact hpow
  have hBT := CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hYm
  have hPC : ∀ j : Fin 2, graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun j => graphFixedParabolic_le _ _ _ _
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
  have hne : ∀ j : Fin 2, ({d4Index j} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ :=
    fun j => by
      rcases hcases (d4Index j) with h | h <;> rw [h]
      · exact singleton_ne_univ_fa0
      · exact singleton_ne_univ_fa1
  have hQ : ∀ j : Fin 2,
      ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
          φ.symm.toMonoidHom ≠ ⊥ ∧
        IsPGroup 2 ↥(((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
          {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) ∧
        ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
            φ.symm.toMonoidHom ≤ Subgroup.normalizer ((((graphFixedParabolicRadical TwistTag.D4 K
              σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom :
                Subgroup Y) : Set Y) := by
    intro j
    obtain ⟨hQP, hPN, hQ2, -⟩ := library_facts σ (d4Index j) (hne j)
    have hQC := hQP.trans (hPC j)
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      have hna : ∃ x ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j},
          ∃ y ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j},
            x * y ≠ y * x := by
        rcases hcases (d4Index j) with h | h <;> rw [h]
        · exact nonabelian_a0 σ hσ3
        · exact nonabelian_a1 σ hσ3
      obtain ⟨x, hx, y, hy, hxy⟩ := hna
      have hx1 : φ.symm ⟨x, hQC hx⟩ = 1 := by
        have : φ.symm ⟨x, hQC hx⟩ ∈ ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
            {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom :=
          ⟨⟨x, hQC hx⟩, hx, rfl⟩
        rwa [h0, Subgroup.mem_bot] at this
      have hx' : x = 1 := by
        have := congrArg Subtype.val ((MulEquiv.map_eq_one_iff φ.symm).1 hx1)
        exact this
      exact hxy (by rw [hx', one_mul, mul_one])
    · exact (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm).map _
    · rintro _ ⟨p, hp, rfl⟩
      refine Subgroup.le_normalizer_map _ ⟨p, ?_, rfl⟩
      rw [← Subgroup.subgroupOf_normalizer_eq hQC]
      exact hPN hp
  obtain ⟨hM, hTM⟩ := (hpair.2.2 M₂).2 (Or.inr rfl)
  let ψ : ↥PB ≃* ↥M₂ := ι.φ2
  obtain ⟨j, g, hMj⟩ := G24Split.exists_eq_map_conj_of_isMaximalTwoLocal hpair.1 hres hBT
    (Q := fun j => ((graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) hQ hpair.1 hM hTM
  set P' := graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} with hP'
  let Θ : Y →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp
      (φ.toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom)
  let Φ : ↥PB →* ModGL TwistTag.D4.tag K := Θ.comp (M₂.subtype.comp ψ.toMonoidHom)
  have hΘ : ∀ y : Y, Θ y = ((φ (g⁻¹ * y * g) : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) := fun y => by
    show ((φ ((MulAut.conj g⁻¹) y) : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) = _
    rw [MulAut.conj_apply, inv_inv]
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h1 : ((φ (g⁻¹ * (ψ a : Y) * g) : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) = ((φ (g⁻¹ * (ψ b : Y) * g) :
          ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : ModGL TwistTag.D4.tag K) := by
      rw [← hΘ, ← hΘ]
      exact hab
    have h2 := φ.injective (Subtype.ext h1)
    exact ψ.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h2)))
  have hΦP : ∀ x : ↥PB, Φ x ∈ P' := by
    intro x
    have hx : ((ψ x : ↥M₂) : Y) ∈ (((graphFixedParabolic TwistTag.D4 K σ.toRingHom
        {d4Index j}).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
          φ.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [← hMj]
      exact (ψ x).2
    obtain ⟨p, ⟨q, hq, hqp⟩, hpx⟩ := hx
    have hp : p = g⁻¹ * (ψ x : Y) * g := by
      rw [← hpx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    show Θ (ψ x : Y) ∈ P'
    rw [hΘ, ← hp, ← hqp]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hq
  have hΦs : ∀ y ∈ P', ∃ x : ↥PB, Φ x = y := by
    intro y hy
    set p : Y := φ.symm ⟨y, hPC j hy⟩ with hp
    have hpM : g * p * g⁻¹ ∈ M₂ := by
      rw [hMj]
      exact ⟨p, ⟨⟨y, hPC j hy⟩, hy, rfl⟩, by simp [MulAut.conj_apply]⟩
    obtain ⟨x, hx⟩ := ψ.surjective ⟨_, hpM⟩
    refine ⟨x, ?_⟩
    show Θ (ψ x : Y) = y
    rw [hx, hΘ]
    simp only [hp, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    exact congrArg Subtype.val (φ.apply_symm_apply _)
  set N := (L2.subgroupOf PB).map Φ with hN
  have hNP : N ≤ P' := by
    rintro _ ⟨x, -, rfl⟩
    exact hΦP x
  have hPN : P' ≤ Subgroup.normalizer (N : Set (ModGL TwistTag.D4.tag K)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hΦs y hy
    refine Subgroup.le_normalizer_map Φ ⟨x, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top_iff.2 hL2n]
    exact Subgroup.mem_top x
  set z' : ModGL TwistTag.D4.tag K := Φ ⟨z, hzPB⟩ with hz'
  have hz'c : z' ∈ Subgroup.centralizer (N : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    rw [hz', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzL _ hl)
  have hz'1 : z' ≠ 1 := fun h => hz1' (congrArg Subtype.val (hΦinj (h.trans (map_one Φ).symm)))
  let eN : ↥N ≃* ↥L2 := ((L2.subgroupOf PB).equivMapOfInjective Φ hΦinj).symm.trans
    (Subgroup.subgroupOfEquivOfLe hL2PB)
  have hNq : IsL2Quot 2 (oTwoQuot ↥N) := H13.IsL2Quot.of_mulEquiv (oTwoQuotCongr eN.symm) hL2
  have hNs : ¬ Group.IsSolvable ↥N := fun hs => by
    have : Group.IsSolvable (oTwoQuot ↥N) := inferInstance
    exact not_isSolvable_of_isL2Quot_two hNq this
  have hcard : Nat.card (oTwoQuot ↥N) = 60 := by
    rw [IsL2Quot.card (by norm_num) hNq]
    norm_num
  rcases hcases (d4Index j) with ha | ha
  ·
    have hP0 : P' = P0 σ := by rw [hP', ha]
    rw [hP0] at hNP hPN
    have := card_le_card_oTwoQuot_a0 σ hσ3 (by rw [hK64]; norm_num) hNP hPN hNs
    rw [hcard, hK64] at this
    norm_num at this
  ·
    have hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom) := by
      have : Fintype K := Fintype.ofFinite K
      classical
      have : Fintype ↥(trialityFixedField K σ.toRingHom) := Fintype.ofFinite _
      obtain ⟨m, -, hm⟩ := FiniteField.card ↥(trialityFixedField K σ.toRingHom) 2
      have hu : 3 ∣ Fintype.card Kˣ := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK64]
        norm_num
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      obtain ⟨u, hu3⟩ := exists_prime_orderOf_dvd_card 3 hu
      have hω3 : (u : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← hu3, pow_orderOf_eq_one, Units.val_one]
      have hω1 : (u : K) ≠ 1 := fun h => by
        have : u = 1 := Units.ext h
        rw [this, orderOf_one] at hu3
        norm_num at hu3
      have hωk : (u : K) ∈ trialityFixedField K σ.toRingHom := by
        rw [mem_trialityFixedField]
        show σ (u : K) = u
        rw [hσ, show (2 : ℕ) ^ 2 = 3 + 1 by norm_num, pow_succ, hω3, one_mul]
      have h2 : 2 < Fintype.card ↥(trialityFixedField K σ.toRingHom) := by
        refine Fintype.two_lt_card_iff.2 ⟨0, 1, ⟨u, hωk⟩, zero_ne_one, fun h => ?_, fun h => ?_⟩
        · exact u.ne_zero (congrArg Subtype.val h).symm
        · exact hω1 (congrArg Subtype.val h).symm
      rw [Nat.card_eq_fintype_card, hm]
      rw [hm] at h2
      have hm2 : 2 ≤ (m : ℕ) := by
        by_contra hlt
        have : (m : ℕ) = 1 := by have := m.pos; omega
        rw [this] at h2
        norm_num at h2
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm2
    have hP1 : P' = P1 σ := by rw [hP', ha]
    rw [hP1] at hNP hPN hΦP
    have hC := perfectCore_le_of_parabolicFacts (parabolicFacts_a1 σ hσ3) hNP hPN hNs
    exact hz'1 (eq_one_of_mem_centralizer_perfectCore_a1 σ hσ3 hk4 (hΦP _)
      (Subgroup.centralizer_le hC hz'c))

end Main

end CFSG.Quasithin.H13.NQCat.F112D4

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem f112L2FourChiefFactC_of (hD4 : F112L2FourChiefD4FactC) : F112L2FourChiefFactC := by
  have hG2 := f112L2FourChiefG2FactC_holds
  have hU4 := f112L2FourChiefU4FactC_holds
  intro G _ _ L1 L2 S hH hA Li hLi hq Z₀ hZ₀ hZS hZC n hn
  unfold F112ListA at hA
  dsimp only at hA
  rcases hA with ⟨f, hf, -, hB1, -, hB2, -⟩ | ⟨f, hf, -, hB1, -, hB2, -⟩ |
    ⟨f, hf, hα, h1, h2, h3, h4⟩ | ⟨f, hf, hα, h1, h2, h3, h4⟩ | ⟨a, ha, -, ⟨e⟩, -, h2, -⟩ |
    ⟨f, hf, hα, h1, h2, h3, h4, h5⟩ | ⟨-, ⟨F, _, _, hF, ⟨e⟩⟩, -, h2, -⟩
  ·
    rcases hLi with rfl | rfl
    · exact (le_one_of_isShort2 hB1.1 hn).trans (by norm_num)
    · exact (le_one_of_isShort2 hB2.1 hn).trans (by norm_num)
  ·
    rcases hLi with rfl | rfl
    · exact (le_one_of_isShort2 hB1.1 hn).trans (by norm_num)
    · exact (le_one_of_isShort2 hB2.1 hn).trans (by norm_num)
  ·
    have hf2 : f = 2 := by
      rcases hLi with rfl | rfl
      · exact eq_of_isL2Quot (by omega) (by norm_num) h1 hq
      · exact eq_of_isL2Quot (by omega) (by norm_num) h2 hq
    subst hf2
    exact hG2 G L1 L2 S hH hα h1 h2 h3 h4 Li hLi Z₀ hZ₀ hZS hZC n hn
  ·
    rcases hLi with rfl | rfl
    · exact absurd (eq_of_isL2Quot (by omega) (by norm_num) h1 hq) (by omega)
    · have hf2 : f = 2 := eq_of_isL2Quot (by omega) (by norm_num) h3 hq
      subst hf2
      exact hD4 G _ _ S hH hα h1 h2 h3 h4 Z₀ hZ₀ hZS hZC n hn
  ·
    rcases hLi with rfl | rfl
    · have hc := hq.card (by norm_num)
      rw [Nat.card_congr e.toEquiv] at hc
      have := sixtyFour_le_card_sz ha
      norm_num at hc
      omega
    · exact absurd (eq_of_isL2Quot (by omega) (by norm_num) h2 hq) (by omega)
  ·
    rcases hLi with rfl | rfl
    · have hf2 : f = 2 := eq_of_isL2Quot (by omega) (by norm_num) h1 hq
      subst hf2
      exact hU4 G _ _ S hH hα h1 h2 h3 h4 h5 Z₀ hZ₀ hZS hZC n hn
    · exact absurd (eq_of_isL2Quot (by omega) (by norm_num) h4 hq) (by omega)
  ·
    rcases hLi with rfl | rfl
    · exact (not_mulEquiv_su34_of_isL2Quot (by norm_num) hq hF e).elim
    · exact absurd (eq_of_isL2Quot (by norm_num) (by norm_num) h2 hq) (by omega)

theorem f112L2FourChiefFactC_holds :
    F112L2FourChiefFactC :=
  f112L2FourChiefFactC_of NQCat.F112D4.f112L2FourChiefD4FactC_holds

end CFSG.Quasithin.H13
