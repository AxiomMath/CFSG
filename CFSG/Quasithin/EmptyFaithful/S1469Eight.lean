module

public import CFSG.Quasithin.EmptyFaithful.S1469Sev

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem exists_relIndex_eq_two_pow {U Y : Subgroup G} (hU : IsPGroup 2 U) :
    ∃ k : ℕ, Y.relIndex U = 2 ^ k := by
  obtain ⟨a, ha⟩ := hU.exists_card_eq
  have h := Subgroup.relIndex_mul_card (H := Y) (K := U)
  have hd : Y.relIndex U ∣ 2 ^ a := ⟨Nat.card ↥(Y ⊓ U), by rw [← ha, ← h]⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨k, hk⟩

theorem mIdx_le_of_lt_of_relIndex_le_two {U A Bp Bq : Subgroup G} (hU : IsPGroup 2 U)
    (hAB : A < Bp) (hBq : Bq ≤ Bp) (hpq : Bq.relIndex Bp ≤ 2) (hBU : Bp ≤ U) :
    mIdx U Bq ≤ mIdx U A := by
  have hA1 : A.relIndex Bp ≠ 1 := fun h => absurd (Subgroup.relIndex_eq_one.mp h) (not_le_of_gt hAB)
  have hA0 : A.relIndex Bp ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_mul_card (H := A) (K := Bp)
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne this
  have hA2 : 2 ≤ A.relIndex Bp := by omega
  have e1 : A.relIndex U = A.relIndex Bp * Bp.relIndex U :=
    (Subgroup.relIndex_mul_relIndex A Bp U hAB.le hBU).symm
  have e2 : Bq.relIndex U = Bq.relIndex Bp * Bp.relIndex U :=
    (Subgroup.relIndex_mul_relIndex Bq Bp U hBq hBU).symm
  have hle : Bq.relIndex U ≤ A.relIndex U := by
    rw [e1, e2]
    exact Nat.mul_le_mul_right _ (hpq.trans hA2)
  obtain ⟨j, hj⟩ := exists_relIndex_eq_two_pow (Y := Bq) hU
  obtain ⟨k, hk⟩ := exists_relIndex_eq_two_pow (Y := A) hU
  unfold mIdx
  rw [hj, hk, padicValNat.prime_pow, padicValNat.prime_pow]
  rw [hj, hk] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

theorem exists_isComponentIn_of_not_charTwo {I : Subgroup G} (hO : oddCoreIn I = ⊥)
    (h : ¬ CharTwo I) : ∃ K : Subgroup G, IsComponentIn K I := by
  by_contra hno
  push Not at hno
  have hlay : CFSG.layer ↥I = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall fun K hK =>
    hno (K.map I.subtype) ⟨Subgroup.map_subtype_le K, by
      have e : (K.map I.subtype).subgroupOf I = K :=
        Subgroup.comap_map_eq_self_of_injective I.subtype_injective K
      rw [e]; exact hK⟩
  have hodd : CFSG.oddCore ↥I = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxO : (x : G) ∈ oddCoreIn I := (mem_oddCoreIn_iff I x).mpr hx
    rw [hO, Subgroup.mem_bot] at hxO
    exact Subgroup.mem_bot.mpr (Subtype.ext hxO)
  have hP : CFSG.pPrimeCore 2 ↥I = ⊥ := by
    rw [← EscapingLocal.oddCore_eq_pPrimeCore]; exact hodd
  have hF : CFSG.fittingSubgroup ↥I = CFSG.pCore 2 ↥I := CFSG.Fitting_eq_pcore ↥I 2 hP
  have hchar : CFSG.IsCharacteristicP 2 ↥I :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥I 2).mpr
      (by rw [CFSG.generalizedFitting, hlay, sup_bot_eq, hF])
  apply h
  refine charTwo_iff_internal.mpr ?_
  have h2 : Subgroup.centralizer (CFSG.pCore 2 ↥I : Set ↥I) ≤ CFSG.pCore 2 ↥I := hchar
  assumption

theorem pCoreOf_le_centralizer_of_isComponentIn {I K : Subgroup G} (hK : IsComponentIn K I) :
    pCoreOf 2 I ≤ Subgroup.centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥I := CFSG.pCore 2 ↥I
  have : N.Normal := CFSG.pCore_normal
  have : Group.IsNilpotent N := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).isNilpotent
  have : Group.IsSolvable N := inferInstance
  have hsub : Open.IsSubnormal N ⊤ :=
    ComponentClassification.Components.chain_of_mathlib_subnormal
      (inferInstance : N.Normal).isSubnormal
  have hcomm := ComponentClassification.Layer.commutes_with_solvable_subnormal N hsub
  have hKlayer : K.subgroupOf I ≤ ComponentClassification.Layer.subgroup ↥I := by
    rw [← CFSG.layer_eq_componentClassification]
    exact le_sSup hK.2
  intro x hx
  obtain ⟨x', hx', rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : (⟨k, hK.1 hk⟩ : ↥I) ∈ K.subgroupOf I := hk
  have hx'N : x' ∈ N := by
    show x' ∈ CFSG.pCore 2 ↥I
    exact hx'
  have h1 := Subgroup.commutator_mem_commutator (hKlayer hk') hx'N
  rw [hcomm, Subgroup.mem_bot] at h1
  have h2 : (⟨k, hK.1 hk⟩ : ↥I) * x' = x' * ⟨k, hK.1 hk⟩ :=
    commutatorElement_eq_one_iff_mul_comm.mp h1
  exact congrArg Subtype.val h2

omit [Finite G] in
theorem ne_bot_of_isComponentIn {I K : Subgroup G} (hK : IsComponentIn K I) : K ≠ ⊥ := by
  intro h
  have hq : CFSG.IsQuasisimple (K.subgroupOf I) := hK.2.1
  have : Nontrivial (K.subgroupOf I) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨⟨x₀, hx₀⟩, hx⟩ := exists_ne (1 : K.subgroupOf I)
  have hb : K.subgroupOf I = ⊥ := by simp [h]
  rw [hb] at hx₀
  exact hx (Subtype.ext (Subgroup.mem_bot.mp hx₀))

theorem Setting146.not_mem_pCoreOf_of_isComponentIn (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    {K : Subgroup G} (hK : IsComponentIn K I) : z ∉ pCoreOf 2 I := by
  intro hzO
  have h115 := S.lemma115Hyp_of_isIStar hH hu hI hsyl hz hz1
  have hKz := (h115.lemma115.2.2 K hK).1
  have hcent : Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (pCoreOf_le_centralizer_of_isComponentIn hK hzO)
  have hbot : ⁅K, Subgroup.zpowers z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hcent)
  exact ne_bot_of_isComponentIn hK (hKz ▸ hbot)

theorem Setting146.lemma_14_6_8 (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {u : G} (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) (hchar : ¬ CharTwo I) :
    mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) ≤
      mIdx (conjClosure (VZ T M) H) (pCoreOf 2 I) := by
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hO := S.oddCoreIn_eq_bot hH hu hI hsyl hzZ hz1'
  obtain ⟨K, hK⟩ := exists_isComponentIn_of_not_charTwo hO hchar
  have hzO : z ∉ pCoreOf 2 I := S.not_mem_pCoreOf_of_isComponentIn hH hu hI hsyl hzZ hz1' hK
  set Q := pCoreOf 2 H with hQ
  set U := conjClosure (VZ T M) H with hU
  set O := pCoreOf 2 I with hOdef
  set P := Q ⊓ Subgroup.centralizer ({u} : Set G) with hP
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hUQ : U ≤ Q := S.conjClosure_le_pCoreOf hH
  have hQT : Q ≤ T := S.pCoreOf_le_T hH
  have hU2 : IsPGroup 2 U := hT2.to_le (hUQ.trans hQT)
  have hUab : IsElemAbelian 2 U := S.lemma_14_5_15_two hH
  have hcommU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUab.1.is_comm.comm (⟨a, ha⟩ : U) ⟨b, hb⟩)
  have huU : u ∈ U := hu.mem
  have hTuI : tU T u ≤ I := hI.1.1.1
  have hZU : quasithinOmegaOneCenter T ≤ U := Z_le_conjClosure_VZ T M H
  have hPI : P ≤ I := fun p hp => hTuI ((S146T.mem_tU_iff).mpr ⟨hQT hp.1,
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hp.2 u rfl).symm⟩)
  have hZeq : ∀ c ∈ quasithinOmegaOneCenter T, c = 1 ∨ c = z := fun c hc => by
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · exact Or.inr (S.Z_eq_of_iff hc hzZ ⟨fun h => absurd h hc1, fun h => absurd h hz1'⟩)
  have hAB : U ⊓ O ≤ U ⊓ Subgroup.centralizer (P : Set G) := by
    refine le_inf inf_le_left fun a ha => Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    have hc : ⁅p, a⁆ ∈ quasithinOmegaOneCenter T := S.comm_mem_Z hH ha.1 hp.1
    have hcO : ⁅p, a⁆ ∈ O := by
      have h1 : p * a * p⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I (hPI hp)) a).mp ha.2
      rw [commutatorElement_def]
      exact O.mul_mem h1 (O.inv_mem ha.2)
    rcases hZeq _ hc with h | h
    · exact commutatorElement_eq_one_iff_mul_comm.mp h
    · exact absurd (h ▸ hcO) hzO
  have hAlt : U ⊓ O < U ⊓ Subgroup.centralizer (P : Set G) := by
    refine lt_of_le_of_ne hAB fun heq => hzO ?_
    have hzB : z ∈ U ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hZU hzZ, Subgroup.mem_centralizer_iff.mpr fun p hp => S146T.comm_Z_T (hQT hp.1) hzZ⟩
    exact (heq ▸ hzB : z ∈ U ⊓ O).2
  have hBq : U ⊓ Subgroup.centralizer (Q : Set G) ≤ U ⊓ Subgroup.centralizer (P : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have hpq : (U ⊓ Subgroup.centralizer (Q : Set G)).relIndex
      (U ⊓ Subgroup.centralizer (P : Set G)) ≤ 2 := by
    obtain ⟨q₀, hq₀1, hq₀u⟩ := Setting146.exists_comm_ne_one hu
    have hq₀Q : q₀ ∈ Q := S.pCoreOf_mcOf_le_pCoreOf hH hq₀1
    have hZT := fun {x : G} (hx : x ∈ quasithinOmegaOneCenter T) => S146T.Z_le hx
    have hκ : ∀ q ∈ Q, ⁅q, u⁆ ∈ quasithinOmegaOneCenter T := fun q hq => S.comm_mem_Z hH huU hq
    have hκmul : ∀ q ∈ Q, ∀ q' ∈ Q, ⁅q * q', u⁆ = ⁅q, u⁆ * ⁅q', u⁆ := by
      intro q hq q' hq'
      rw [S146T.comm_mul_left q q' u]
      have h1 : q * ⁅q', u⁆ * q⁻¹ = ⁅q', u⁆ := by
        have := S146T.comm_Z_T (hQT hq) (hκ q' hq')
        calc q * ⁅q', u⁆ * q⁻¹ = (q * ⁅q', u⁆) * q⁻¹ := rfl
          _ = (⁅q', u⁆ * q) * q⁻¹ := by rw [this]
          _ = ⁅q', u⁆ := by group
      rw [h1]
      exact (S146T.comm_Z_T (hZT (hκ q hq)) (hκ q' hq')).symm
    have hcoset : ∀ q ∈ Q, q ∈ P ∨ q₀⁻¹ * q ∈ P := by
      intro q hq
      have hQinv : q₀⁻¹ ∈ Q := Q.inv_mem hq₀Q
      have hmem : ∀ x ∈ Q, ⁅x, u⁆ = 1 → x ∈ P := fun x hx h =>
        ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm⟩
      rcases hZeq _ (hκ q hq) with h | h
      · exact Or.inl (hmem q hq h)
      · right
        apply hmem _ (Q.mul_mem hQinv hq)
        have hq₀z : ⁅q₀, u⁆ = z := by
          rcases hZeq _ (hκ q₀ hq₀Q) with h' | h'
          · exact absurd h' hq₀u
          · exact h'
        have hinv : ⁅q₀⁻¹, u⁆ = z := by
          have h2 := hκmul q₀⁻¹ hQinv q₀ hq₀Q
          rw [inv_mul_cancel, hq₀z] at h2
          have h3 : ⁅(1 : G), u⁆ = 1 := by simp
          rw [h3] at h2
          have hz2 : z * z = 1 := by
            have := S146T.Z_sq hzZ
            rwa [pow_two] at this
          calc ⁅q₀⁻¹, u⁆ = ⁅q₀⁻¹, u⁆ * (z * z) := by rw [hz2, mul_one]
            _ = (⁅q₀⁻¹, u⁆ * z) * z := by rw [mul_assoc]
            _ = 1 * z := by rw [← h2]
            _ = z := one_mul z
        rw [hκmul q₀⁻¹ hQinv q hq, hinv, h]
        have := S146T.Z_sq hzZ
        rwa [pow_two] at this
    set Bp := U ⊓ Subgroup.centralizer (P : Set G) with hBp
    have hθmem : ∀ a ∈ Bp, ⁅q₀, a⁆ ∈ quasithinOmegaOneCenter T :=
      fun a ha => S.comm_mem_Z hH ha.1 hq₀Q
    have hUT : U ≤ T := hUQ.trans hQT
    let θ : Bp →* ↥(quasithinOmegaOneCenter T) :=
      { toFun := fun a => ⟨⁅q₀, (a : G)⁆, hθmem a a.2⟩
        map_one' := by
          apply Subtype.ext
          show ⁅q₀, ((1 : Bp) : G)⁆ = 1
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          show ⁅q₀, (a : G) * (b : G)⁆ = ⁅q₀, (a : G)⁆ * ⁅q₀, (b : G)⁆
          rw [S146T.comm_mul_right]
          have h1 := S146T.comm_Z_T (hUT a.2.1) (hθmem b b.2)
          congr 1
          calc (a : G) * ⁅q₀, (b : G)⁆ * (a : G)⁻¹ = (⁅q₀, (b : G)⁆ * (a : G)) * (a : G)⁻¹ := by
                rw [h1]
            _ = ⁅q₀, (b : G)⁆ := by group }
    have hker : θ.ker ≤ (U ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf Bp := by
      intro a ha
      have ha1 : ⁅q₀, (a : G)⁆ = 1 := congrArg Subtype.val ha
      have hq₀a : q₀ * (a : G) = (a : G) * q₀ := commutatorElement_eq_one_iff_mul_comm.mp ha1
      refine Subgroup.mem_subgroupOf.mpr ⟨a.2.1, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have haP : ∀ p ∈ P, p * (a : G) = (a : G) * p := fun p hp =>
        Subgroup.mem_centralizer_iff.mp a.2.2 p hp
      rcases hcoset q hq with h | h
      · exact haP q h
      · have h2 := haP _ h
        have e : q = q₀ * (q₀⁻¹ * q) := by group
        rw [e]
        calc q₀ * (q₀⁻¹ * q) * (a : G) = q₀ * ((q₀⁻¹ * q) * (a : G)) := by group
          _ = q₀ * ((a : G) * (q₀⁻¹ * q)) := by rw [h2]
          _ = (q₀ * (a : G)) * (q₀⁻¹ * q) := by group
          _ = ((a : G) * q₀) * (q₀⁻¹ * q) := by rw [hq₀a]
          _ = (a : G) * (q₀ * (q₀⁻¹ * q)) := by group
    have hdvd : ((U ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf Bp).index ∣ θ.ker.index :=
      Subgroup.index_dvd_of_le hker
    have hidx : θ.ker.index = Nat.card θ.range := Subgroup.index_ker θ
    have hrange : Nat.card θ.range ≤ 2 := by
      have := Subgroup.card_le_card_group θ.range
      rwa [S.card_Z] at this
    have hpos : 0 < Nat.card θ.range := Nat.card_pos
    exact (Nat.le_of_dvd (hidx ▸ hpos) hdvd).trans (hidx ▸ hrange)
  have hmain := mIdx_le_of_lt_of_relIndex_le_two hU2 hAlt hBq hpq inf_le_left
  unfold mIdx at hmain ⊢
  rwa [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left] at hmain

end CFSG.Quasithin
