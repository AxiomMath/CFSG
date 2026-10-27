module

public import CFSG.Milestones.ASVolI.B1
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.Quasithin.Background.S1549DGen
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Quasithin.Background.A4Bridge
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.Quasithin.Background.C124B2102

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section B2Vocab

variable {G : Type*} [Group G]

@[expose] def Aj (H : Subgroup G) (j : ℕ) : Set (Subgroup G) :=
  {A | j ≤ CFSG.pRank 2 ↥H ∧
    ∃ A' ∈ CFSG.higherElemThompsonFamily ↥H j, A = A'.map H.subtype}

@[expose] noncomputable def Jj (H : Subgroup G) (j : ℕ) : Subgroup G :=
  if j ≤ CFSG.pRank 2 ↥H then
    (CFSG.higherElemThompson ↥H j).map H.subtype else ⊥

theorem Jj_eq_higherElemThompson_of_le (H : Subgroup G) (j : ℕ)
    (bound : j ≤ CFSG.pRank 2 ↥H) :
    Jj H j = (CFSG.higherElemThompson ↥H j).map H.subtype := by
  simp only [Jj, if_pos bound]

theorem Aj_eq_empty_of_rank_lt (H : Subgroup G) (j : ℕ)
    (bound : CFSG.pRank 2 ↥H < j) : Aj H j = ∅ := by
  ext A
  simp only [Aj, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  exact iff_false_intro (fun member => (Nat.not_le_of_lt bound) member.1)

@[expose] def baumOf (H : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer (omegaOneCenterOf (Jj H 0) : Set G)

@[expose] def O2Phi (X : Subgroup G) : Subgroup G :=
  ((frattini (↥X ⧸ pCore 2 ↥X)).comap (QuotientGroup.mk' (pCore 2 ↥X))).map X.subtype

variable {V : Subgroup G}

@[expose] def starOffenders (hV : IsElemAbelian 2 V) (H : Subgroup G) :
    Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | ∃ A ∈ Aj H 0, autI hV A ≠ ⊥ ∧ B = autI hV A}

@[expose] def starOffendersR (hV : IsElemAbelian 2 V) (R : Subgroup G) :
    Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | ∃ A : Subgroup G, (∃ g : G, A.map (MulAut.conj g).toMonoidHom ∈ Aj R 0) ∧
    autI hV A ≠ ⊥ ∧ B = autI hV A}

@[expose] def IsFFOffenderRel (hV : IsElemAbelian 2 V) (H A : Subgroup G) : Prop :=
  A ∈ Aj H 0 ∧ autI hV A ≠ ⊥

@[expose] def IsStrongFFOffenderRel (hV : IsElemAbelian 2 V) (H A : Subgroup G) : Prop :=
  IsFFOffenderRel hV H A ∧ IsStrongFFStarOffender (autI hV H) (autI hV A)

@[expose] noncomputable def preimI (hV : IsElemAbelian 2 V) (Y : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  (Y.comap (convI hV)).map (Subgroup.normalizer (V : Set G)).subtype

end B2Vocab

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

@[expose] def B_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (i : ℕ),
    ((Jj H i).subgroupOf H).Characteristic ∧ (IsPGroup 2 H → ((baumOf H).subgroupOf H).Characteristic)

section BurnsideB2a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_pRank_eq {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.pRank 2 ↥H = CFSG.Open.pRank 2 H :=
  CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank 2 H

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_le_pRank_of_corank {G : Type} [Group G] [Finite G] {H A : Subgroup G}
    {j : ℕ} (hA : CFSG.Quasithin.IsElemAbelianCorank H j A) : j ≤ CFSG.pRank 2 ↥H := by
  rw [burnsideB2a_pRank_eq H]
  have h1 : 2 ^ j ≤ 2 ^ CFSG.Open.pRank 2 H := by
    rw [← hA.2.2]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_corank_map {G : Type} [Group G] [Finite G] (H : Subgroup G) (j : ℕ)
    (hj : j ≤ CFSG.pRank 2 ↥H) (A' : Subgroup ↥H)
    (hA' : A' ∈ CFSG.higherElemThompsonFamily ↥H j) :
    CFSG.Quasithin.IsElemAbelianCorank H j (A'.map H.subtype) := by
  obtain ⟨hE, hc⟩ := (CFSG.mem_higherElemThompsonFamily_iff j A').1 hA'
  refine ⟨BlueprintB2.map_subtype_le_self A', ?_, ?_⟩
  · exact (BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr
      (BlueprintB2.isElementaryAbelian_map hE H.subtype)
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hc, ← burnsideB2a_pRank_eq H,
      ← pow_add, Nat.sub_add_cancel hj]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_family_of_corank {G : Type} [Group G] [Finite G] {H A : Subgroup G}
    {j : ℕ}
    (hA : CFSG.Quasithin.IsElemAbelianCorank H j A) :
    A.subgroupOf H ∈ CFSG.higherElemThompsonFamily ↥H j := by
  have hj : j ≤ CFSG.pRank 2 ↥H := burnsideB2a_le_pRank_of_corank hA
  refine (CFSG.mem_higherElemThompsonFamily_iff j (A.subgroupOf H)).2 ⟨?_, ?_⟩
  · exact BlueprintB2.isElementaryAbelian_subgroupOf
      ((BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mp hA.2.1)
  · rw [BlueprintB2.card_subgroupOf_eq hA.1]
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0 : ℕ) < 2) j)
    rw [hA.2.2, ← pow_add, Nat.sub_add_cancel hj, burnsideB2a_pRank_eq H]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_mem_Aj_iff {G : Type} [Group G] [Finite G] (H A : Subgroup G) (j : ℕ) :
    A ∈ Aj H j ↔ CFSG.Quasithin.IsElemAbelianCorank H j A := by
  unfold Aj
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hj, A', hA', rfl⟩
    exact burnsideB2a_corank_map H j hj A' hA'
  · intro hA
    exact ⟨burnsideB2a_le_pRank_of_corank hA, A.subgroupOf H,
      burnsideB2a_family_of_corank hA, (Subgroup.map_subgroupOf_eq_of_le hA.1).symm⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_Jj_eq_thompsonJi {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (j : ℕ) :
    Jj H j = thompsonJi H j := by
  by_cases hj : j ≤ CFSG.pRank 2 ↥H
  · rw [Jj_eq_higherElemThompson_of_le H j hj]
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun A' hA' => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      unfold thompsonJi
      exact le_iSup₂_of_le (A'.map H.subtype) (burnsideB2a_corank_map H j hj A' hA') le_rfl
    · unfold thompsonJi
      refine iSup₂_le fun A hA => ?_
      rw [← Subgroup.map_subgroupOf_eq_of_le hA.1]
      exact Subgroup.map_mono (le_sSup (burnsideB2a_family_of_corank hA))
  · have hbot : thompsonJi H j = ⊥ := by
      refine le_bot_iff.mp ?_
      unfold thompsonJi
      exact iSup₂_le fun A hA => (hj (burnsideB2a_le_pRank_of_corank hA)).elim
    rw [hbot]
    unfold Jj
    rw [if_neg hj]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_Jj_zero {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    Jj H 0 = thompsonJ H := by
  rw [Jj_eq_higherElemThompson_of_le H 0 (Nat.zero_le _), CFSG.higherElemThompson_zero ↥H]
  exact elemThompson_map_subtype_eq_thompsonJ H

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_baumOf_eq_baum {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    baumOf H = baum H := by
  unfold baumOf baum
  rw [burnsideB2a_Jj_zero H]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2a_mem_Aj_zero_iff {G : Type} [Group G] [Finite G] (H A : Subgroup G) :
    A ∈ Aj H 0 ↔ CFSG.Quasithin.IsMaxElemAbelian H A := by
  rw [burnsideB2a_mem_Aj_iff, CFSG.Quasithin.isMaxElemAbelian_iff_corank_zero]

private theorem burnsideB2a_card_eq_two_pow {W : Type} [Group W] [Finite W] (h : ∀ w : W, w ^ 2
    = 1) :
    ∃ k : ℕ, Nat.card W = 2 ^ k := by
  have hp : IsPGroup 2 W := by
    intro w
    exact ⟨1, by simpa using h w⟩
  exact IsPGroup.iff_card.mp hp

private theorem burnsideB2a_rk_eq {W : Type} [Group W] {k : ℕ} (hk : Nat.card W = 2 ^ k) :
    CFSG.Quasithin.rk W = k := by
  unfold CFSG.Quasithin.rk
  rw [hk, padicValNat.prime_pow]

private theorem burnsideB2a_index_eq_pow_rkIdx {W : Type} [Group W] [Finite W] {k : ℕ}
    (hk : Nat.card W = 2 ^ k) (H : Subgroup W) :
    H.index = 2 ^ CFSG.Quasithin.rkIdx H := by
  have hd : H.index ∣ 2 ^ k := by
    rw [← hk]
    exact H.index_dvd_card
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  unfold CFSG.Quasithin.rkIdx
  rw [hi, padicValNat.prime_pow]

end BurnsideB2a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_2 : B_2_2 := by
  intro G _ _ H i
  refine ⟨?_, fun _ => ?_⟩
  · by_cases hi : i ≤ CFSG.pRank 2 ↥H
    · rw [Jj_eq_higherElemThompson_of_le H i hi,
        CFSG.Quasithin.BlueprintB2.subgroupOf_map_subtype_self]
      exact CFSG.Quasithin.SteinbergBK.higherElemThompson_characteristic i
    · have hbot : Jj H i = ⊥ := by
        unfold Jj
        rw [if_neg hi]
      rw [hbot, Subgroup.bot_subgroupOf]
      infer_instance
  · rw [burnsideB2a_baumOf_eq_baum H]
    exact CFSG.Quasithin.C1GN.characteristic_baum H

@[expose] def B_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), IsPGroup 2 S →
    ∀ i j : ℕ, i ≤ j → j < CFSG.Open.pRank 2 S →
      Jj S i ≤ Jj S j ∧
      (omegaOneCenterOf (Jj S j) ≤ omegaOneOf (S ⊓ Subgroup.centralizer (Jj S i : Set G)) ∧
        omegaOneOf (S ⊓ Subgroup.centralizer (Jj S i : Set G)) = omegaOneCenterOf (Jj S i)) ∧
      (∀ R : Subgroup G, Jj S i ≤ R → R ≤ S → Jj S i = Jj R i) ∧
      (∀ R : Subgroup G, baumOf S ≤ R → R ≤ S → baumOf S = baumOf R) ∧
      (∀ U : Subgroup G, U ≤ S → IsElemAbelian 2 U → Jj S 0 ≤ S ⊓ Subgroup.centralizer (U : Set G) →
        baumOf S = baumOf (S ⊓ Subgroup.centralizer (U : Set G))) ∧
      (∀ A ∈ Aj S 0, A = omegaOneOf (S ⊓ Subgroup.centralizer (A : Set G))) ∧
      (omegaOneOf (S ⊓ Subgroup.centralizer (Jj S 0 : Set G)) = omegaOneCenterOf (Jj S 0) ∧
        omegaOneCenterOf (Jj S 0) = ⨅ (A : Subgroup G) (_ : A ∈ Aj S 0), A)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_3 : B_2_3 := by
  intro G _ _ S _ i j hij hj
  have hJ : ∀ (H : Subgroup G) (k : ℕ), Jj H k = thompsonJi H k :=
    fun H k => burnsideB2a_Jj_eq_thompsonJi H k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ S i, hJ S j]
    exact thompsonJi_mono hij hj
  · rw [hJ S j, hJ S i]
    exact omegaOneCenterOf_thompsonJi_le hij hj
  · intro R hR hRS
    rw [hJ S i] at hR
    rw [hJ S i, hJ R i]
    exact thompsonJi_eq_of_le (lt_of_le_of_lt hij hj) hR hRS
  · intro R hR hRS
    simp only [burnsideB2a_baumOf_eq_baum] at hR ⊢
    exact baum_eq_of_le hR hRS
  · intro U hUS hU hJU
    rw [burnsideB2a_Jj_zero S] at hJU
    simp only [burnsideB2a_baumOf_eq_baum]
    exact baum_eq_baum_centralizer hU hUS hJU
  · intro A hA
    exact eq_omegaOneOf_centralizer ((burnsideB2a_mem_Aj_zero_iff S A).1 hA)
  · rw [burnsideB2a_Jj_zero S]
    refine ⟨(omegaOne_centralizer_thompsonJ S).1, (omegaOne_centralizer_thompsonJ S).2.trans ?_⟩
    exact le_antisymm
      (le_iInf₂ fun A hA => iInf₂_le A ((burnsideB2a_mem_Aj_zero_iff S A).1 hA))
      (le_iInf₂ fun A hA => iInf₂_le A ((burnsideB2a_mem_Aj_zero_iff S A).2 hA))

@[expose] def B_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (S : Subgroup G) (j : ℕ) (A : Subgroup G), IsPGroup 2 S → V ≤ S → A ∈ Aj S j →
      autI hV A ≠ ⊥ →
      (rkIdx (fixV (autI hV A)) ≤ rk (autI hV A) + j ∧
        (j = 0 → rAV (autI hV A) ≤ 1 ∧ IsFFModule (autI hV ⊤))) ∧
      (rkIdx (fixV (autI hV A)) = rk (autI hV A) + j →
        (((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0)) ∧
      (A ∈ Aj S 0 → rkIdx (fixV (autI hV A)) = rk (autI hV A) →
        ((((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0) ∧
          CFSG.Open.pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 S ∧
          Aj (S ⊓ Subgroup.centralizer (V : Set G)) 0 ⊆ Aj S 0 ∧
          V ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0) ∧
          omegaOneCenterOf (Jj S 0) ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0)))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_4 : B_2_4 := by
  intro G _ _ V hV _ S j A _ hVS hAS hA1
  have hcorank : CFSG.Quasithin.IsElemAbelianCorank S j A := (burnsideB2a_mem_Aj_iff S A j).1 hAS
  have hNtop : Subgroup.normalizer (V : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hNtop]
    exact le_top
  have hm : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have hmeq : (fixV (autI hV A)).index * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card V := by
    have h := Subgroup.card_mul_index (fixV (autI hV A))
    rw [card_fixV_autI hV hAN] at h
    rw [mul_comm]
    exact h
  have hbound := card_le_relIndex_mul_card_mul_two_pow hV hVS hcorank
  rw [← card_autI_eq hV hAN] at hbound
  have hsqA : ∀ w : ↥(autI hV A), w ^ 2 = 1 := fun w =>
    Subtype.ext ((isElemAbelian2_autI hV hcorank.2.1 hAN).2 w w.2)
  obtain ⟨ka, hka⟩ := burnsideB2a_card_eq_two_pow hsqA
  have hNa : Nat.card (autI hV A) = 2 ^ CFSG.Quasithin.rk (autI hV A) := by
    rw [burnsideB2a_rk_eq hka]
    exact hka
  obtain ⟨kW, hkW⟩ := burnsideB2a_card_eq_two_pow (W := IntMod V hV) (fun w => IntMod.sq_eq_one w)
  have hFindex : (fixV (autI hV A)).index = 2 ^ CFSG.Quasithin.rkIdx (fixV (autI hV A)) :=
    burnsideB2a_index_eq_pow_rkIdx hkW _
  have hle : CFSG.Quasithin.rkIdx (fixV (autI hV A)) ≤ CFSG.Quasithin.rk (autI hV A) + j := by
    have h1 : (fixV (autI hV A)).index ≤ Nat.card (autI hV A) * 2 ^ j := by
      refine Nat.le_of_mul_le_mul_right ?_ hm
      calc (fixV (autI hV A)).index * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))
          = Nat.card V := hmeq
        _ ≤ Nat.card (autI hV A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ j :=
            hbound
        _ = Nat.card (autI hV A) * 2 ^ j * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
            ring
    rw [hFindex, hNa, ← pow_add] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hj0part : j = 0 → CFSG.Quasithin.rAV (autI hV A) ≤ 1 ∧ IsFFModule (autI hV ⊤) := by
    intro hj0
    subst hj0
    refine ⟨?_, ?_⟩
    · unfold CFSG.Quasithin.rAV
      apply div_le_one_of_le₀
      · have h0 : CFSG.Quasithin.rkIdx (fixV (autI hV A)) ≤ CFSG.Quasithin.rk (autI hV A) := by
          simpa using hle
        exact_mod_cast h0
      · positivity
    · exact isFFModule_autOn hV hVS (le_of_eq hNtop.symm) le_top
        ((burnsideB2a_mem_Aj_zero_iff S A).1 hAS)
        (fun h => hA1 ((autI_eq_bot_iff hV hAN).2 h))
  have h2 : CFSG.Quasithin.rkIdx (fixV (autI hV A)) = CFSG.Quasithin.rk (autI hV A) + j →
      ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0 := by
    intro heq
    have hx : (fixV (autI hV A)).index = Nat.card (autI hV A) * 2 ^ j := by
      rw [hFindex, hNa, heq, pow_add]
    have heq' : Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * 2 ^ j := by
      rw [← card_autI_eq hV hAN, ← hmeq, hx]
      ring
    exact (burnsideB2a_mem_Aj_zero_iff S _).2 (isMaxElemAbelian_sup_of_eq hV hVS hcorank heq')
  have h3 : A ∈ Aj S 0 → CFSG.Quasithin.rkIdx (fixV (autI hV A)) = CFSG.Quasithin.rk (autI hV A) →
      (((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ∈ Aj S 0 ∧
        CFSG.Open.pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 S ∧
        Aj (S ⊓ Subgroup.centralizer (V : Set G)) 0 ⊆ Aj S 0 ∧
        V ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0) ∧
        omegaOneCenterOf (Jj S 0) ≤ omegaOneCenterOf (Jj (S ⊓ Subgroup.centralizer (V : Set G)) 0)) := by
    intro hA0 heq
    have hmax : CFSG.Quasithin.IsMaxElemAbelian S A := (burnsideB2a_mem_Aj_zero_iff S A).1 hA0
    have hx : (fixV (autI hV A)).index = Nat.card (autI hV A) := by
      rw [hFindex, hNa, heq]
    have heq' : Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
      rw [← card_autI_eq hV hAN, ← hmeq, hx]
    obtain ⟨hB, hpr, hsub, hV1, hV2⟩ := B24_three hV hVS hmax heq'
    refine ⟨(burnsideB2a_mem_Aj_zero_iff S _).2 hB, hpr, ?_, ?_, ?_⟩
    · intro A' hA'
      exact (burnsideB2a_mem_Aj_zero_iff S A').2
        (hsub A' ((burnsideB2a_mem_Aj_zero_iff _ A').1 hA'))
    · simp only [burnsideB2a_Jj_zero]
      exact hV1
    · simp only [burnsideB2a_Jj_zero]
      exact hV2
  exact ⟨⟨hle, hj0part⟩, h2, h3⟩

@[expose] def B_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal],
    (starOffenders hV ⊤ = ∅ ∨ IsStableFF (autI hV ⊤) (starOffenders hV ⊤)) ∧
      (∀ B ∈ starOffenders hV ⊤, IsFFStarOffender (autI hV ⊤) B) ∧
      (∀ B ∈ starOffenders hV ⊤, ∀ g ∈ autI hV ⊤,
        B.map (MulAut.conj g).toMonoidHom ∈ starOffenders hV ⊤) ∧
      (∀ A ∈ starOffenders hV ⊤, ∀ B : Subgroup (MulAut (IntMod V hV)),
        FFLe (autI hV ⊤) B A → B ∈ starOffenders hV ⊤)

section BurnsideB2b

private theorem burnsideB2b_top_le_normalizer {G : Type} [Group G] (V : Subgroup G) [V.Normal] :
    (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
  (Subgroup.normalizer_eq_top_iff.mpr inferInstance : Subgroup.normalizer (V : Set G) = ⊤).ge

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2b_mem_Aj_zero_iff {G : Type} [Group G] [Finite G] (H A : Subgroup G) :
    A ∈ Aj H 0 ↔ IsMaxElemAbelian H A := by
  constructor
  · rintro ⟨-, A', hA', rfl⟩
    have hA'e : A' ∈ CFSG.elemThompsonFamily ↥H 2 := by
      have h := (CFSG.mem_higherElemThompsonFamily_iff 0 A').1 hA'
      rw [Nat.sub_zero] at h
      exact h
    rw [BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily, BlueprintB2.subgroupOf_map_subtype_self]
    exact ⟨BlueprintB2.map_subtype_le_self A', hA'e⟩
  · intro hmax
    have h := BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily.1 hmax
    show 0 ≤ CFSG.pRank 2 ↥H ∧ ∃ A' ∈ CFSG.higherElemThompsonFamily ↥H 0, A = A'.map H.subtype
    refine ⟨Nat.zero_le _, A.subgroupOf H, ?_, (Subgroup.map_subgroupOf_eq_of_le h.1).symm⟩
    rw [CFSG.mem_higherElemThompsonFamily_iff, Nat.sub_zero]
    exact h.2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2b_Jj_zero_eq {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    Jj H 0 = CFSG.Quasithin.thompsonJ H := by
  unfold Jj
  rw [if_pos (Nat.zero_le _), CFSG.higherElemThompson_zero,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2b_isFFOffenderRel_iff {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (A : Subgroup G) :
    IsFFOffenderRel hV H A ↔ CFSG.Quasithin.IsFFOffender H V A := by
  constructor
  · rintro ⟨hA, hne⟩
    exact ⟨(burnsideB2b_mem_Aj_zero_iff H A).1 hA,
      fun h => hne (CFSG.Quasithin.autI_eq_bot_of_le_centralizer hV h)⟩
  · rintro ⟨hmax, hnot⟩
    exact ⟨(burnsideB2b_mem_Aj_zero_iff H A).2 hmax,
      fun h => hnot ((CFSG.Quasithin.autI_eq_bot_iff hV (hmax.1.trans hHN)).1 h)⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2b_starOffenders_eq {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hHN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) :
    starOffenders hV ⊤ = CFSG.Quasithin.offenderImages hV ⊤ := by
  ext B
  constructor
  · rintro ⟨A, hA, hne, rfl⟩
    exact ⟨A, (burnsideB2b_isFFOffenderRel_iff hV hHN A).1 ⟨hA, hne⟩, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨hA1, hA2⟩ := (burnsideB2b_isFFOffenderRel_iff hV hHN A).2 hA
    exact ⟨A, hA1, hA2, rfl⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2b_inf_preimI_eq {G : Type} [Group G] {V : Subgroup G} (hV :
    IsElemAbelian 2 V)
    {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (B : Subgroup (MulAut (IntMod V hV))) :
    A ⊓ preimI hV B = CFSG.Quasithin.preI hV A hA B := by
  ext g
  constructor
  · rintro ⟨hgA, hg⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    exact (CFSG.Quasithin.mem_preI hV).2 ⟨hgA, hx⟩
  · intro hg
    obtain ⟨hgA, hgB⟩ := (CFSG.Quasithin.mem_preI hV).1 hg
    refine ⟨hgA, ?_⟩
    exact Subgroup.mem_map.2 ⟨⟨g, hA hgA⟩, hgB, rfl⟩

open CFSG.Quasithin in
private theorem burnsideB2b_rk_add_eq_of_card {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hX : CFSG.Quasithin.IsElemAbelian2 X)
    (hcard : Nat.card W = Nat.card X * Nat.card (CFSG.Quasithin.fixV X)) :
    CFSG.Quasithin.rk X + CFSG.Quasithin.rk (CFSG.Quasithin.fixV X) = CFSG.Quasithin.rk W := by
  have h1 := (CFSG.Quasithin.B1.card_eq_iff hW hX).1 hcard
  have h2 := CFSG.Quasithin.rk_add_rkIdx (CFSG.Quasithin.fixV X)
  omega

open CFSG.Quasithin in
private theorem burnsideB2b_rkIdx_le_rk_of_rAV {W : Type} [CommGroup W] [Finite W]
    {Y X : Subgroup (MulAut W)} (hX : CFSG.Quasithin.IsA2 Y X)
    (hr : CFSG.Quasithin.rAV X ≤ 1) :
    CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV X) ≤ CFSG.Quasithin.rk X := by
  have hpos : (0 : ℚ) < (CFSG.Quasithin.rk X : ℚ) := by exact_mod_cast hX.rk_pos
  unfold CFSG.Quasithin.rAV at hr
  rw [div_le_one hpos] at hr
  exact_mod_cast hr

open CFSG.Quasithin in
private theorem burnsideB2b_rk_le_add_of_rAV {W : Type} [CommGroup W] [Finite W]
    {Y X : Subgroup (MulAut W)} (hX : CFSG.Quasithin.IsA2 Y X)
    (hr : CFSG.Quasithin.rAV X ≤ 1) :
    CFSG.Quasithin.rk W ≤ CFSG.Quasithin.rk X + CFSG.Quasithin.rk (CFSG.Quasithin.fixV X) := by
  have h1 := burnsideB2b_rkIdx_le_rk_of_rAV hX hr
  have h2 := CFSG.Quasithin.rk_add_rkIdx (CFSG.Quasithin.fixV X)
  omega

end BurnsideB2b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_5 : B_2_5 := by
  intro G _ _ V hV _
  have hHN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
    burnsideB2b_top_le_normalizer V
  rw [burnsideB2b_starOffenders_eq hV hHN]
  refine ⟨?_, fun B hB => CFSG.Quasithin.offenderImages_isFFStarOffender hV le_top hHN hB,
    fun B hB g hg => CFSG.Quasithin.offenderImages_conj hV hB hg, ?_⟩
  · by_cases hne : (CFSG.Quasithin.offenderImages hV ⊤).Nonempty
    · exact Or.inr (CFSG.Quasithin.B2_5 hV le_top hHN hne)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)
  · intro A hA B hB
    obtain ⟨A', hA', rfl⟩ := hA
    exact CFSG.Quasithin.offenderImages_ffLe hV le_top hHN hA' hB

theorem B_2_5_stable_of_nonempty (statement : B_2_5)
    (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (nonempty : ∃ A ∈ Aj ⊤ 0, autI hV A ≠ ⊥) :
    IsStableFF (autI hV ⊤) (starOffenders hV ⊤) := by
  rcases (statement G V hV).1 with empty | stable
  · obtain ⟨A, maximal, nontrivial⟩ := nonempty
    have member : autI hV A ∈ starOffenders hV ⊤ := ⟨A, maximal, nontrivial, rfl⟩
    have contradiction : False := by simpa [empty] using member
    exact contradiction.elim
  · exact stable

@[expose] def B_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (A : Subgroup G), IsFFOffenderRel hV ⊤ A → IsFFStarOffender (autI hV ⊤) (autI hV A)

theorem as_B_2_6 : B_2_6 := by
  intro G _ _ V hV _ A hA
  exact (as_B_2_5 G V hV).2.1 (CFSG.Quasithin.autI hV A) ⟨A, hA.1, hA.2, rfl⟩

@[expose] def B_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (T : Subgroup G), IsSylowTwoOf T ⊤ →
      ((Jj ⊤ 0 ≤ Subgroup.centralizer (V : Set G) ∧
          (Subgroup.normalizer (Jj T 0 : Set G) : Set G) *
            (Subgroup.centralizer (V : Set G) : Set G) = Set.univ) ∨
        (¬ Jj ⊤ 0 ≤ Subgroup.centralizer (V : Set G) ∧ IsFFModule (autI hV ⊤) ∧
          IsStableFF (autI hV ⊤) (starOffenders hV ⊤))) ∧
      autI hV (Jj ⊤ 0) = ffJP (starOffenders hV ⊤) (autI hV ⊤) ∧
      ffJP (starOffenders hV ⊤) (autI hV ⊤) ≤ ffJ (autI hV ⊤)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_7 : B_2_7 := by
  intro G _ _ V hV _ T hT
  have hHN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
    burnsideB2b_top_le_normalizer V
  rw [burnsideB2b_starOffenders_eq hV hHN]
  have hJtop : Jj (⊤ : Subgroup G) 0 = CFSG.Quasithin.thompsonJ ⊤ := burnsideB2b_Jj_zero_eq ⊤
  have hJT : Jj T 0 = CFSG.Quasithin.thompsonJ T := burnsideB2b_Jj_zero_eq T
  have hauto : CFSG.Quasithin.autI hV (Jj (⊤ : Subgroup G) 0) =
      CFSG.Quasithin.ffJP (CFSG.Quasithin.offenderImages hV ⊤) (CFSG.Quasithin.autI hV ⊤) := by
    rw [hJtop]
    exact CFSG.Quasithin.autI_thompsonJ hV hHN
  refine ⟨?_, hauto, ?_⟩
  · by_cases h : Jj (⊤ : Subgroup G) 0 ≤ Subgroup.centralizer (V : Set G)
    · left
      refine ⟨h, ?_⟩
      have htop : CFSG.Quasithin.thompsonJ ⊤ ≤ Subgroup.centralizer (V : Set G) := by
        rwa [hJtop] at h
      have hJ' : CFSG.Quasithin.thompsonJ T ≤ Subgroup.centralizer (V : Set G) :=
        (CFSG.Quasithin.thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans htop
      obtain ⟨-, hfac⟩ := CFSG.Quasithin.B2_7_of_le_factor hHN hT hJ'
      rw [hJT]
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn, c, hc, hx⟩ := hfac x (Subgroup.mem_top x)
      exact Set.mem_mul.2 ⟨n, hn.2, c, hc.2, hx.symm⟩
    · right
      have h' : ¬ CFSG.Quasithin.thompsonJ ⊤ ≤ Subgroup.centralizer (V : Set G) := by
        rwa [hJtop] at h
      obtain ⟨hmod, hstable, -, -⟩ := CFSG.Quasithin.B2_7_of_not_le hV le_top hHN h'
      exact ⟨h, hmod, hstable⟩
  · by_cases h : CFSG.Quasithin.thompsonJ ⊤ ≤ Subgroup.centralizer (V : Set G)
    · have hb : CFSG.Quasithin.ffJP (CFSG.Quasithin.offenderImages hV ⊤)
          (CFSG.Quasithin.autI hV ⊤) = ⊥ := by
        rw [← CFSG.Quasithin.autI_thompsonJ hV hHN,
          CFSG.Quasithin.autI_eq_bot_of_le_centralizer hV h]
      rw [hb]
      exact bot_le
    · exact (CFSG.Quasithin.B2_7_of_not_le hV le_top hHN h).2.2.2

@[expose] def B_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (A : Subgroup G), IsFFOffenderRel hV ⊤ A →
      (∀ B : Subgroup (MulAut (IntMod V hV)), FFLe (autI hV ⊤) B (autI hV A) →
        ∃ D ∈ Aj ⊤ 0, autI hV D = B ∧
          D = (A ⊓ preimI hV B) ⊔
            (V ⊓ Subgroup.centralizer ((A ⊓ preimI hV B) : Set G))) ∧
      (¬ IsStrongFFStarOffender (autI hV ⊤) (autI hV A) →
        rk (autI hV A) + rk (fixV (autI hV A)) = rk (IntMod V hV) ∧
        ∀ B : Subgroup (MulAut (IntMod V hV)), B ≠ ⊥ → B ≤ autI hV A → rAV B ≤ 1 →
          rk (IntMod V hV) ≤ rk B + rk (fixV B) ∧ FFLe (autI hV ⊤) B (autI hV A))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_8 : B_2_8 := by
  intro G _ _ V hV _ A hA
  have hHN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
    burnsideB2b_top_le_normalizer V
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := le_top.trans hHN
  have hbg : CFSG.Quasithin.IsFFOffender ⊤ V A :=
    (burnsideB2b_isFFOffenderRel_iff hV hHN A).1 hA
  refine ⟨?_, ?_⟩
  · intro B hB
    have hBA : B ≤ CFSG.Quasithin.autI hV A := hB.2.2.1
    obtain ⟨hD, hDB⟩ :=
      (CFSG.Quasithin.offender_core hV le_top hHN hbg.1 hBA).2 hB.2.2.2
    refine ⟨CFSG.Quasithin.preI hV A hAN B ⊔
        (V ⊓ Subgroup.centralizer ((CFSG.Quasithin.preI hV A hAN B : Subgroup G) : Set G)),
      (burnsideB2b_mem_Aj_zero_iff ⊤ _).2 hD, hDB, ?_⟩
    clear hD hDB hB hBA hbg hA
    have hkey : A ⊓ preimI hV B = CFSG.Quasithin.preI hV A hAN B :=
      burnsideB2b_inf_preimI_eq hV hAN B
    rw [← hkey] <;> rfl
  · intro hnot
    have hnot' : ¬ CFSG.Quasithin.IsStrongFFOffender hV ⊤ A := fun h => hnot h.2
    have hAs : CFSG.Quasithin.IsFFStarOffender (CFSG.Quasithin.autI hV ⊤)
        (CFSG.Quasithin.autI hV A) :=
      CFSG.Quasithin.offenderImages_isFFStarOffender hV le_top hHN ⟨A, hbg, rfl⟩
    have hcard := CFSG.Quasithin.B2_8_card_eq hV le_top hHN hbg hnot'
    refine ⟨burnsideB2b_rk_add_eq_of_card (fun w => IntMod.sq_eq_one w) hAs.isA2.2.2 hcard, ?_⟩
    intro B hB1 hBA hr
    have hff := CFSG.Quasithin.B2_8_ffLe hV le_top hHN hbg hnot' hB1 hBA hr
    exact ⟨burnsideB2b_rk_le_add_of_rAV hff.1 hr, hff⟩

@[expose] def B_2_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (A : Subgroup G), IsFFOffenderRel hV ⊤ A →
      ¬ IsStrongFFStarOffender (autI hV ⊤) (autI hV A) →
      (∀ B : Subgroup (MulAut (IntMod V hV)), IsFFStarOffender (autI hV ⊤) B → B ≤ autI hV A →
        ∃ D : Subgroup G, IsFFOffenderRel hV ⊤ D ∧ autI hV D = B) ∧
      (∀ B : Subgroup (MulAut (IntMod V hV)), B ≠ ⊥ → B ≤ autI hV A → rAV B ≤ 1 →
        ∃ D : Subgroup G, IsFFOffenderRel hV ⊤ D ∧ autI hV D = B)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_9 : B_2_9 := by
  intro G _ _ V hV _ A hA hnot
  have hHN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
    burnsideB2b_top_le_normalizer V
  have hbg : CFSG.Quasithin.IsFFOffender ⊤ V A :=
    (burnsideB2b_isFFOffenderRel_iff hV hHN A).1 hA
  have hnot' : ¬ CFSG.Quasithin.IsStrongFFOffender hV ⊤ A := fun h => hnot h.2
  refine ⟨?_, ?_⟩
  · intro B hB hBA
    obtain ⟨D, hD, hDB⟩ := CFSG.Quasithin.B2_9_1 hV le_top hHN hbg hnot' hB hBA
    exact ⟨D, (burnsideB2b_isFFOffenderRel_iff hV hHN D).2 hD, hDB⟩
  · intro B hB1 hBA hr
    obtain ⟨D, hD, hDB⟩ := CFSG.Quasithin.B2_9_2 hV le_top hHN hbg hnot' hB1 hBA hr
    exact ⟨D, (burnsideB2b_isFFOffenderRel_iff hV hHN D).2 hD, hDB⟩

@[expose] def B_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R T : Subgroup G), IsSylowTwoOf T ⊤ → pCoreOf 2 (⊤ : Subgroup G) ≤ R → R ≤ T →
      (pCoreOf 2 (⊤ : Subgroup G) = R ⊓ Subgroup.centralizer (V : Set G) →
        ((Jj R 0 = Jj (pCoreOf 2 (⊤ : Subgroup G)) 0 ∧
            baumOf R = baumOf (pCoreOf 2 (⊤ : Subgroup G)) ∧
            (Jj R 0).Normal ∧ (baumOf R).Normal) ∨
          (IsStableFF (autI hV ⊤) (starOffendersR hV R) ∧
            ffJP (starOffendersR hV R) (autI hV ⊤) ≤ ffJ (autI hV ⊤)))) ∧
      (pCoreOf 2 (autI hV ⊤) = ⊥ → ∀ L : Subgroup G,
        (L : Set G) * (T : Set G) = Set.univ → ¬ L ≤ Subgroup.centralizer (V : Set G) →
        ((quasithinIsCComponent L ⊤ ∧ CFSG.Open.IsQuasisimple (↥L ⧸ pCore 2 ↥L)) ∨
          Nonempty ((↥L ⧸ pCore 2 ↥L) ≃* Multiplicative (ZMod 3))) →
          IsSylowTwoOf (pCoreOf 2 (Subgroup.centralizer (V : Set G))) (Subgroup.centralizer (V : Set G)) ∧
          pCoreOf 2 (⊤ : Subgroup G) = R ⊓ Subgroup.centralizer (V : Set G) ∧
          autI hV L = quasithinGenFitting (autI hV ⊤) ∧
          (baumOf R = baumOf (pCoreOf 2 (⊤ : Subgroup G)) ∨
            autI hV L = quasithinGenFitting (ffJP (starOffendersR hV R) (autI hV ⊤))))

section BurnsideB2f

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2f_mem_Aj_zero_iff {G : Type} [Group G] [Finite G] (H A : Subgroup G) :
    A ∈ Aj H 0 ↔ IsMaxElemAbelian H A := by
  constructor
  · rintro ⟨-, A', hA', rfl⟩
    have hA'e : A' ∈ CFSG.elemThompsonFamily ↥H 2 := by
      have h := (CFSG.mem_higherElemThompsonFamily_iff 0 A').1 hA'
      rw [Nat.sub_zero] at h
      exact h
    rw [BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily,
      BlueprintB2.subgroupOf_map_subtype_self]
    exact ⟨BlueprintB2.map_subtype_le_self A', hA'e⟩
  · intro hmax
    have h := BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily.1 hmax
    show 0 ≤ CFSG.pRank 2 ↥H ∧ ∃ A' ∈ CFSG.higherElemThompsonFamily ↥H 0, A = A'.map H.subtype
    refine ⟨Nat.zero_le _, A.subgroupOf H, ?_, (Subgroup.map_subgroupOf_eq_of_le h.1).symm⟩
    rw [CFSG.mem_higherElemThompsonFamily_iff, Nat.sub_zero]
    exact h.2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2f_Jj_zero_eq {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    Jj H 0 = CFSG.Quasithin.thompsonJ H := by
  unfold Jj
  rw [if_pos (Nat.zero_le _), CFSG.higherElemThompson_zero,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2f_baumOf_eq {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    baumOf H = CFSG.Quasithin.baum H := by
  unfold baumOf CFSG.Quasithin.baum
  rw [burnsideB2f_Jj_zero_eq H]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2f_starOffendersR_eq_in {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (R : Subgroup G) :
    starOffendersR hV R = CFSG.Quasithin.C124.offenderImagesConjIn hV ⊤ R := by
  ext B
  constructor
  · rintro ⟨A, ⟨g, hg⟩, hne, rfl⟩
    refine ⟨hne, A, rfl, g⁻¹, Subgroup.mem_top _, ?_⟩
    have := (burnsideB2f_mem_Aj_zero_iff R _).1 hg
    rwa [← inv_inv g] at this
  · rintro ⟨hne, A, rfl, g, -, hg⟩
    exact ⟨A, ⟨g⁻¹, (burnsideB2f_mem_Aj_zero_iff R _).2 hg⟩, hne, rfl⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2f_starOffendersR_eq {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (R : Subgroup G) :
    starOffendersR hV R = CFSG.Quasithin.offenderImagesConj hV R := by
  ext B
  constructor
  · rintro ⟨A, ⟨g, hg⟩, hne, rfl⟩
    refine ⟨hne, A, rfl, g⁻¹, ?_⟩
    have := (burnsideB2f_mem_Aj_zero_iff R _).1 hg
    rwa [← inv_inv g] at this
  · rintro ⟨hne, A, rfl, g, hg⟩
    exact ⟨A, ⟨g⁻¹, (burnsideB2f_mem_Aj_zero_iff R _).2 hg⟩, hne, rfl⟩


open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB CFSG.LieType.BorelTits in
private theorem burnsideB2f_isTwoReducedIn {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) [V.Normal] (hO : pCoreOf 2 (autI hV ⊤) = ⊥) :
    CFSG.Quasithin.IsTwoReducedIn (⊤ : Subgroup G) V := by
  have hHN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer_eq_top_iff.mpr inferInstance : Subgroup.normalizer (V : Set G) = ⊤).ge
  refine ⟨le_top, hHN, hV, fun D _ hDN hDpow => ?_⟩
  have hDN' : D ≤ Subgroup.normalizer (V : Set G) := fun x _ => hHN (Subgroup.mem_top x)
  have hp : IsPGroup 2 (autI hV D) := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨k, hk⟩ := hDpow g hg
    refine ⟨k, Subtype.ext ?_⟩
    show convI hV g ^ 2 ^ k = 1
    rw [← map_pow]
    exact (convI_eq_one_iff hV _).2 (by simpa using hk)
  have hnorm : autI hV ⊤ ≤ Subgroup.normalizer (autI hV D : Set (MulAut (IntMod V hV))) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => C124.autI_conj_mem hV hDN y hy l hl, fun hl => ?_⟩
    have := C124.autI_conj_mem hV hDN y⁻¹ ((autI hV ⊤).inv_mem hy) _ hl
    simpa [mul_assoc] using this
  have hle : autI hV D ≤ pCoreOf 2 (autI hV ⊤) :=
    le_pCoreOf_of_le_normalizer 2 (autI_mono hV le_top) hnorm hp
  rw [hO] at hle
  exact (autI_eq_bot_iff hV hDN').1 (le_bot_iff.1 hle)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB CFSG.LieType.BorelTits in
private theorem burnsideB2f_core {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) [V.Normal] {R T L : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hOR : pCoreOf 2 (⊤ : Subgroup G) ≤ R) (hRT : R ≤ T)
    (hO : pCoreOf 2 (autI hV ⊤) = ⊥) (hn : L.Normal)
    (hLT : ∀ x : G, ∃ l ∈ L, ∃ t ∈ T, x = l * t)
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    IsSylowTwoOf (pCoreOf 2 (Subgroup.centralizer (V : Set G))) (Subgroup.centralizer (V : Set G)) ∧
      pCoreOf 2 (⊤ : Subgroup G) = R ⊓ Subgroup.centralizer (V : Set G) ∧
      autI hV L = quasithinGenFitting (autI hV ⊤) ∧
      (baumOf R = baumOf (pCoreOf 2 (⊤ : Subgroup G)) ∨
        autI hV L = quasithinGenFitting (ffJP (starOffendersR hV R) (autI hV ⊤))) := by
  have hred := burnsideB2f_isTwoReducedIn hV hO
  have hVL : (⁅V, L⁆ : Subgroup G) ≠ ⊥ := fun h => hLV (by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h)
  have hnorm : (⊤ : Subgroup G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer_eq_top_iff.mpr hn : Subgroup.normalizer (L : Set G) = ⊤).ge
  obtain ⟨⟨h1, h2⟩, -, h3, h4⟩ := C124.B2_10_2 (X := ⊤) hV hred hOR hRT hT le_top hnorm
    (fun x _ => hLT x) hVL hLq
  refine ⟨by simpa using h1, h2, h3.symm, ?_⟩
  rcases h4 with h | ⟨-, -, h⟩
  · left
    rw [burnsideB2f_baumOf_eq, burnsideB2f_baumOf_eq]
    exact h
  · right
    rw [burnsideB2f_starOffendersR_eq_in]
    exact h.symm


open CFSG.Quasithin in
private theorem burnsideB2f_normal_of_subnormal {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) {H K : Subgroup G} (hsub : CFSG.Open.IsSubnormal H K) :
    ∀ L : Subgroup G, ⁅L, L⁆ = L → L ≤ H → (L.subgroupOf H).Normal →
      (∀ k ∈ K, ∃ l ∈ L, ∃ t ∈ T, k = l * t) → (L.subgroupOf K).Normal := by
  induction hsub with
  | refl H =>
    intro L _ _ hLH _
    exact hLH
  | @step H M K hHM hHn hMK ih =>
    intro L hperf hLH hLHn hfact
    have hHK : H ≤ K := hHM.trans (A3.subnormal_le hMK)
    have hHdec : H = L ⊔ (T ⊓ H) := by
      refine B2F.eq_sup_of_forall_exists_mul hLH inf_le_right ?_
      intro x hx
      obtain ⟨l, hl, t, ht, rfl⟩ := hfact x (hHK hx)
      refine ⟨l, hl, t, ⟨ht, ?_⟩, rfl⟩
      have := H.mul_mem (H.inv_mem (hLH hl)) hx
      simpa using this
    have hsolv : Group.IsSolvable ↥(T ⊓ H) := by
      have hp : IsPGroup 2 ↥(T ⊓ H) := hT.to_le inf_le_left
      haveI := hp.isNilpotent
      infer_instance
    have hcore : perfectCore H ≤ L := perfectCore_le_of_sup_solvable hLH hLHn hHdec hsolv
    have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hHn
    have key : ∀ m ∈ M, ∀ x ∈ L, m * x * m⁻¹ ∈ L := by
      intro m hm x hx
      have hLle : L.map (MulAut.conj m).toMonoidHom ≤ H := by
        rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (hMH hm) y).1 (hLH hy)
      have hLperf : ⁅L.map (MulAut.conj m).toMonoidHom, L.map (MulAut.conj m).toMonoidHom⁆ =
          L.map (MulAut.conj m).toMonoidHom := by
        rw [← Subgroup.map_commutator, hperf]
      have := hcore (le_perfectCore_of_perfect hLle hLperf ⟨x, hx, rfl⟩)
      simpa using this
    have hLM : (L.subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hLH.trans hHM)]
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key m hm x, fun hx => ?_⟩
      have := key m⁻¹ (M.inv_mem hm) _ hx
      simpa [mul_assoc] using this
    exact ih L hperf (hLH.trans hHM) hLM hfact


private theorem burnsideB2f_relIndex_dvd_card {W : Type*} [Group W] [Finite W] {Y A P : Subgroup W}
    (hAY : A ≤ Y) (hPY : P ≤ Y) (h : ∀ y ∈ Y, ∃ a ∈ A, ∃ p ∈ P, y = a * p) :
    P.relIndex Y ∣ Nat.card A := by
  have hcardA : Nat.card (A.subgroupOf Y) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  rw [← hcardA]
  let x₀ : ↥Y ⧸ P.subgroupOf Y := ((1 : ↥Y) : ↥Y ⧸ P.subgroupOf Y)
  have horb : MulAction.orbit (A.subgroupOf Y) x₀ = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨a, ha, p, hp, hy⟩ := h y y.2
      refine ⟨⟨⟨a, hAY ha⟩, ha⟩, ?_⟩
      show (⟨a, hAY ha⟩ : ↥Y) • x₀ = (y : ↥Y ⧸ P.subgroupOf Y)
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [hy] using hp
  have h1 := MulAction.index_stabilizer (A.subgroupOf Y) x₀
  rw [horb, Set.ncard_univ] at h1
  have h2 := Subgroup.index_dvd_card (MulAction.stabilizer (A.subgroupOf Y) x₀)
  rw [h1] at h2
  exact h2

private theorem burnsideB2f_card_dvd_six {W : Type*} [Group W] [Finite W] {Y P : Subgroup W}
    (hPY : P ≤ Y) (hP : IsPGroup 2 P) (hidx : P.relIndex Y = 3) (hO : pCoreOf 2 Y = ⊥) :
    Nat.card Y ∣ 6 := by
  have hidx' : (P.subgroupOf Y).index = 3 := hidx
  haveI : (P.subgroupOf Y).FiniteIndex := ⟨by rw [hidx']; norm_num⟩
  have h := Subgroup.index_normalCore_dvd_factorial_index (P.subgroupOf Y)
  rw [hidx'] at h
  have hP' : IsPGroup 2 (P.subgroupOf Y) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
  have hcoreP : IsPGroup 2 (P.subgroupOf Y).normalCore := hP'.to_le (Subgroup.normalCore_le _)
  have hpc : CFSG.pCore 2 ↥Y = ⊥ := by
    have h0 := hO
    unfold pCoreOf at h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 h0
  have hnc : (P.subgroupOf Y).normalCore = ⊥ := by
    have h1 := CFSG.LieType.BorelTits.le_pCore 2 (Subgroup.normalCore_normal _) hcoreP
    rw [hpc] at h1
    exact le_bot_iff.1 h1
  rw [hnc, Subgroup.index_bot] at h
  simpa [Nat.factorial] using h

private theorem burnsideB2f_normalizer_of_dvd_six {W : Type*} [Group W] [Finite W] {Y A :
    Subgroup W}
    (hAY : A ≤ Y) (h6 : Nat.card Y ∣ 6) (h3 : 3 ∣ Nat.card A) :
    Y ≤ Subgroup.normalizer (A : Set W) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hAY]
  have hcard := (A.subgroupOf Y).index_mul_card
  have hcardA : Nat.card (A.subgroupOf Y) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  rw [hcardA] at hcard
  have hle : (A.subgroupOf Y).index * Nat.card A ≤ 6 := by
    rw [hcard]
    exact Nat.le_of_dvd (by norm_num) h6
  obtain ⟨a, ha⟩ := h3
  have hapos : 0 < a := by
    have := Nat.card_pos (α := A)
    rw [ha] at this
    omega
  have hidx_pos : 0 < (A.subgroupOf Y).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hi : (A.subgroupOf Y).index ≤ 2 := by
    rw [ha] at hle
    nlinarith
  interval_cases hix : (A.subgroupOf Y).index
  · exact Subgroup.normal_of_index_eq_one hix
  · exact Subgroup.normal_of_index_eq_two hix

open CFSG.Quasithin in
private theorem burnsideB2f_exists_phi {G : Type} [Group G] {V : Subgroup G} (hV :
    IsElemAbelian 2 V)
    [V.Normal] :
    ∃ φ : G →* MulAut (IntMod V hV), φ.ker = Subgroup.centralizer (V : Set G) ∧
      ∀ K : Subgroup G, K.map φ = autI hV K := by
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 ‹V.Normal›]
    exact Subgroup.mem_top g
  refine ⟨(convI hV).comp ((MonoidHom.id G).codRestrict (Subgroup.normalizer (V : Set G)) hN),
    ?_, ?_⟩
  · ext g
    rw [MonoidHom.mem_ker]
    exact convI_eq_one_iff hV ⟨g, hN g⟩
  · intro K
    ext ψ
    rw [Subgroup.mem_map, mem_autI]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hN g⟩, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩

private theorem burnsideB2f_card_pCoreOf {G : Type*} [Group G] (L : Subgroup G) :
    Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) :=
  Subgroup.card_map_of_injective L.subtype_injective

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits in
private theorem burnsideB2f_z3_struct {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) [V.Normal] {T L : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hO : pCoreOf 2 (autI hV ⊤) = ⊥) (hfact : ∀ x : G, ∃ l ∈ L, ∃ t ∈ T, x = l * t)
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    IsPGroup 2 (Subgroup.centralizer (V : Set G)) ∧
      autI hV ⊤ ≤ Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))) ∧
      Nat.card (autI hV L) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hker, hmap⟩ := burnsideB2f_exists_phi hV
  have hHN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 ‹V.Normal›]
    exact Subgroup.mem_top g
  have hLcard : Nat.card L = 3 * Nat.card (pCoreOf 2 L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), h3,
      burnsideB2f_card_pCoreOf]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (pCoreOf_isPGroup 2 L)
  have hTodd : ¬ 2 ∣ T.index := by
    have h0 : ¬ 2 ∣ T.relIndex ⊤ := hT.2.2
    rwa [Subgroup.relIndex_top_right] at h0
  have hTL : T.index ∣ Nat.card L := by
    have h0 := burnsideB2f_relIndex_dvd_card (le_top : L ≤ ⊤) (le_top : T ≤ ⊤)
      (fun y _ => hfact y)
    rwa [Subgroup.relIndex_top_right] at h0
  have hT3 : T.index ∣ 3 := by
    have hcop : Nat.Coprime T.index (2 ^ a) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hTodd).symm.pow_right a
    rw [hLcard, ha] at hTL
    exact hcop.dvd_of_dvd_mul_right hTL
  have hP2 : IsPGroup 2 (T.map φ) := hT.2.1.map φ
  have hrel : (T.map φ).relIndex ((⊤ : Subgroup G).map φ) = (T ⊔ φ.ker).index := by
    rw [Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  have hdvd : (T.map φ).relIndex ((⊤ : Subgroup G).map φ) ∣ T.index := by
    rw [hrel]
    exact Subgroup.index_dvd_of_le le_sup_left
  have hY' : pCoreOf 2 ((⊤ : Subgroup G).map φ) = ⊥ := by
    rw [hmap]
    exact hO
  have hAY : L.map φ ≤ (⊤ : Subgroup G).map φ := Subgroup.map_mono le_top
  have hPY : T.map φ ≤ (⊤ : Subgroup G).map φ := Subgroup.map_mono le_top
  have hfactY : ∀ y ∈ (⊤ : Subgroup G).map φ, ∃ a ∈ L.map φ, ∃ p ∈ T.map φ, y = a * p := by
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := hfact g
    exact ⟨φ l, ⟨l, hl, rfl⟩, φ t, ⟨t, ht, rfl⟩, map_mul φ l t⟩
  have hAne : L.map φ ≠ ⊥ := fun h => hLV (by
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff _).1 h)
  have hidx3 : (T.map φ).relIndex ((⊤ : Subgroup G).map φ) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (hdvd.trans hT3) with h1 | h1
    · exfalso
      have hYP : (⊤ : Subgroup G).map φ ≤ T.map φ := Subgroup.relIndex_eq_one.1 h1
      have hY2 : IsPGroup 2 ((⊤ : Subgroup G).map φ) := hP2.to_le hYP
      have hle := le_pCoreOf_of_le_normalizer 2 (le_refl _) Subgroup.le_normalizer hY2
      rw [hY'] at hle
      exact hAne (le_bot_iff.1 (hAY.trans hle))
    · exact h1
  have h6 := burnsideB2f_card_dvd_six hPY hP2 hidx3 hY'
  have h3A : 3 ∣ Nat.card (L.map φ) := by
    have h0 := burnsideB2f_relIndex_dvd_card hAY hPY hfactY
    rwa [hidx3] at h0
  have hYnorm := burnsideB2f_normalizer_of_dvd_six hAY h6 h3A
  have hT3' : T.index = 3 := by
    have h3d : 3 ∣ T.index := by
      have h0 := hdvd
      rwa [hidx3] at h0
    exact Nat.dvd_antisymm hT3 h3d
  have hCT : Subgroup.centralizer (V : Set G) ≤ T := by
    have h1 := Subgroup.relIndex_mul_index (le_sup_left : T ≤ T ⊔ φ.ker)
    rw [← hrel, hidx3, hT3'] at h1
    have h2 : T.relIndex (T ⊔ φ.ker) = 1 := by omega
    have h4 := Subgroup.relIndex_eq_one.1 h2
    rw [← hker]
    exact le_sup_right.trans h4
  refine ⟨hT.2.1.to_le hCT, ?_, ?_⟩
  · rw [← hmap, ← hmap]
    exact hYnorm
  ·
    have hNA : (pCoreOf 2 L).map φ ≤ L.map φ := Subgroup.map_mono (pCoreOf_le 2 L)
    have hANnorm : L.map φ ≤ Subgroup.normalizer
        (((pCoreOf 2 L).map φ : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) :=
      (Subgroup.map_mono (le_normalizer_pCoreOf 2 L)).trans (Subgroup.le_normalizer_map φ)
    have hN2 : IsPGroup 2 ((pCoreOf 2 L).map φ) := (pCoreOf_isPGroup 2 L).map φ
    have hNpA := le_pCoreOf_of_le_normalizer 2 hNA hANnorm hN2
    have hpA : pCoreOf 2 (L.map φ) ≤ pCoreOf 2 ((⊤ : Subgroup G).map φ) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hAY)
        (hYnorm.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    rw [hY'] at hpA
    have hN0 : (pCoreOf 2 L).map φ = ⊥ := le_bot_iff.1 (hNpA.trans hpA)
    have hOC : pCoreOf 2 L ≤ L ⊓ Subgroup.centralizer (V : Set G) := by
      refine le_inf (pCoreOf_le 2 L) ?_
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff _).1 hN0
    have hcardA := card_autI_mul_card_inf hV
      (fun x _ => hHN x : L ≤ Subgroup.normalizer (V : Set G))
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hOC
    rw [hk, hLcard] at hcardA
    have hpos : 0 < Nat.card (pCoreOf 2 L) := Nat.card_pos
    have h1 : Nat.card (autI hV L) * k = 3 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc Nat.card (pCoreOf 2 L) * (Nat.card (autI hV L) * k)
          = Nat.card (autI hV L) * (Nat.card (pCoreOf 2 L) * k) := by ring
        _ = 3 * Nat.card (pCoreOf 2 L) := hcardA
        _ = Nat.card (pCoreOf 2 L) * 3 := by ring
    rw [hmap L] at h3A
    exact Nat.dvd_antisymm (Dvd.intro k h1) h3A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits in
private theorem burnsideB2f_z3_normal {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) [V.Normal] {T L : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hO : pCoreOf 2 (autI hV ⊤) = ⊥) (hfact : ∀ x : G, ∃ l ∈ L, ∃ t ∈ T, x = l * t)
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) :
    ∃ L' : Subgroup G, L'.Normal ∧ autI hV L' = autI hV L ∧
      (∀ x : G, ∃ l ∈ L', ∃ t ∈ T, x = l * t) ∧ ¬ L' ≤ Subgroup.centralizer (V : Set G) ∧
      Nat.card (↥L' ⧸ CFSG.pCore 2 ↥L') = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hC2, hYnorm, hA3⟩ := burnsideB2f_z3_struct hV hT hO hfact hLV h3
  obtain ⟨φ, hker, hmap⟩ := burnsideB2f_exists_phi hV
  have hHN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 ‹V.Normal›]
    exact Subgroup.mem_top g
  have hAr : autI hV L ≤ φ.range := by
    rw [MonoidHom.range_eq_map, hmap]
    exact autI_mono hV le_top
  have hLL' : L ≤ (autI hV L).comap φ := fun l hl => by
    rw [Subgroup.mem_comap, ← hmap]
    exact ⟨l, hl, rfl⟩
  have hautI : autI hV ((autI hV L).comap φ) = autI hV L := by
    rw [← hmap, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hAr
  have hCL' : Subgroup.centralizer (V : Set G) ≤ (autI hV L).comap φ := fun c hc => by
    rw [Subgroup.mem_comap]
    have h1 : φ c = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hc
    rw [h1]
    exact (autI hV L).one_mem
  have hCnorm : (Subgroup.centralizer (V : Set G)).Normal := inferInstance
  refine ⟨(autI hV L).comap φ, ?_, hautI, fun x => ?_, fun h => hLV (hLL'.trans h), ?_⟩
  · refine ⟨fun x hx g => ?_⟩
    have hφg : φ g ∈ autI hV ⊤ := by
      rw [← hmap]
      exact ⟨g, trivial, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hYnorm hφg) (φ x)).1 hx
    simpa [Subgroup.mem_comap, map_mul, map_inv] using h1
  · obtain ⟨l, hl, t, ht, rfl⟩ := hfact x
    exact ⟨l, hLL' hl, t, ht, rfl⟩
  ·
    set L' := (autI hV L).comap φ with hL'
    have hL'N : L' ≤ Subgroup.normalizer (V : Set G) := fun x _ => hHN x
    have hcardL' := card_autI_mul_card_inf hV hL'N
    rw [hautI, hA3, inf_eq_right.2 hCL'] at hcardL'
    have hCO : Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L' := by
      refine le_pCoreOf_of_le_normalizer 2 hCL' ?_ hC2
      exact (Subgroup.normalizer_eq_top_iff.2 hCnorm : Subgroup.normalizer
        (Subgroup.centralizer (V : Set G) : Set G) = ⊤).ge.trans' le_top
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L') 2)
    have hdecomp := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L')
    obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hCO
    rw [burnsideB2f_card_pCoreOf] at hj
    have hCpos : 0 < Nat.card ↥(Subgroup.centralizer (V : Set G)) := Nat.card_pos
    have hij : Nat.card (↥L' ⧸ CFSG.pCore 2 ↥L') * j = 3 := by
      apply Nat.eq_of_mul_eq_mul_left hCpos
      rw [hdecomp, hj] at hcardL'
      linarith
    rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro j hij) with h1 | h1
    · exfalso
      rw [h1, one_mul, hn] at hdecomp
      have h2 : 3 ∣ 2 ^ n := by
        rw [← hdecomp, ← hcardL']
        exact Dvd.intro _ rfl
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
    · exact h1

end BurnsideB2f

open scoped Pointwise in
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_10 : B_2_10 := by
  intro G _ _ V hV _ R T hT hOR hRT
  refine ⟨fun hC => ?_, fun hO L hLT hLV hL => ?_⟩
  · rcases CFSG.Quasithin.B2_10_1 hV inferInstance hOR hC with ⟨⟨hJ, hB⟩, hJn, hBn⟩ | ⟨hst, hle⟩
    · left
      simp only [burnsideB2f_Jj_zero_eq, burnsideB2f_baumOf_eq]
      exact ⟨hJ, hB, hJn, hBn⟩
    · right
      rw [burnsideB2f_starOffendersR_eq]
      exact ⟨hst, hle⟩
  · have hfact : ∀ x : G, ∃ l ∈ L, ∃ t ∈ T, x = l * t := fun x => by
      have hx : x ∈ (L : Set G) * (T : Set G) := by rw [hLT]; trivial
      obtain ⟨l, hl, t, ht, h⟩ := Set.mem_mul.1 hx
      exact ⟨l, hl, t, ht, h.symm⟩
    rcases hL with ⟨⟨-, hLperf, hLsub, -⟩, hLq⟩ | hnon
    · have hLn : L.Normal := by
        have h := burnsideB2f_normal_of_subnormal hT.2.1 hLsub L hLperf le_rfl
          (by rw [Subgroup.subgroupOf_self]; infer_instance) (fun k _ => hfact k)
        exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1
          ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 h))
      exact burnsideB2f_core hV hT hOR hRT hO hLn hfact hLV
        (Or.inl (CFSG.Quasithin.B1Red.isQuasisimple_of_open hLq))
    · obtain ⟨e⟩ := hnon
      have h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
        rw [Nat.card_congr e.toEquiv]
        simp [Nat.card_eq_fintype_card]
      obtain ⟨L', hL'n, hautI, hfact', hLV', hL'3⟩ :=
        burnsideB2f_z3_normal hV hT hO hfact hLV h3
      have hcore := burnsideB2f_core hV hT hOR hRT hO hL'n hfact' hLV' (Or.inr hL'3)
      rw [hautI] at hcore
      exact hcore

@[expose] def B_2_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), V ∈ primeReducedFamily G 2 →
    pCoreOf 2 (⊤ : Subgroup G) ≤ Subgroup.centralizer (V : Set G) ∧
      V ≤ omegaOneCenterOf (pCoreOf 2 (⊤ : Subgroup G))

section BurnsideB2c

private theorem burnsideB2c_pCoreOf_top {G : Type*} [Group G] (p : ℕ) :
    CFSG.Open.pCoreOf p (⊤ : Subgroup G) = CFSG.pCore p G := by
  unfold CFSG.Open.pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv p (Subgroup.topEquiv (G := G)).symm,
    Subgroup.map_map]
  have hid : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom =
      MonoidHom.id G := by
    ext x
    rfl
  rw [hid, Subgroup.map_id]

private theorem burnsideB2c_mem_fam_zero_iff {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (A : Subgroup ↥H) :
    A ∈ CFSG.higherElemThompsonFamily ↥H 0 ↔ A ∈ CFSG.elemThompsonFamily ↥H 2 := by
  rw [CFSG.mem_higherElemThompsonFamily_iff, Nat.sub_zero]
  rfl

private theorem burnsideB2c_mem_Aj_zero_iff {G : Type*} [Group G] [Finite G] {H A : Subgroup G} :
    A ∈ CFSG.ASVolI.ChB.Aj H 0 ↔ CFSG.Quasithin.IsMaxElemAbelian H A := by
  simp only [CFSG.ASVolI.ChB.Aj, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, A', hA', rfl⟩
    refine CFSG.Quasithin.BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily.2
      ⟨CFSG.Quasithin.BlueprintB2.map_subtype_le_self A', ?_⟩
    rw [CFSG.Quasithin.BlueprintB2.subgroupOf_map_subtype_self]
    exact (burnsideB2c_mem_fam_zero_iff H A').1 hA'
  · intro hA
    obtain ⟨hAH, hfam⟩ :=
      CFSG.Quasithin.BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily.1 hA
    exact ⟨Nat.zero_le _, A.subgroupOf H,
      (burnsideB2c_mem_fam_zero_iff H (A.subgroupOf H)).2 hfam,
      (Subgroup.map_subgroupOf_eq_of_le hAH).symm⟩

private theorem burnsideB2c_Jj_zero {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.ASVolI.ChB.Jj H 0 = CFSG.Quasithin.thompsonJ H := by
  unfold CFSG.ASVolI.ChB.Jj
  rw [if_pos (Nat.zero_le (CFSG.pRank 2 ↥H)), CFSG.higherElemThompson_zero ↥H,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ H]

private theorem burnsideB2c_baumOf {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.ASVolI.ChB.baumOf H = CFSG.Quasithin.baum H := by
  unfold CFSG.ASVolI.ChB.baumOf CFSG.Quasithin.baum
  rw [burnsideB2c_Jj_zero]

private theorem burnsideB2c_isPGroup_of_isElemAbelian {G : Type*} [Group G] {V : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) : IsPGroup 2 V := by
  haveI : CFSG.IsElementaryAbelian 2 V :=
    (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).1 hV
  exact CFSG.IsElementaryAbelian.isPGroup 2 V

end BurnsideB2c

theorem as_B_2_11 : B_2_11 := by
  intro G _ _ V hV
  have hVp : CFSG.Quasithin.IsPrimeReduced 2 V := hV
  rw [burnsideB2c_pCoreOf_top, CFSG.Quasithin.BlueprintB2.omegaOneCenterOf_eq_centerTorsion]
  exact ⟨CFSG.Quasithin.pCore_le_centralizer_of_isPrimeReduced hVp,
    CFSG.Quasithin.isPrimeReduced_le_centerTorsion_pCore hVp⟩

@[expose] def B_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ V₁ ∈ primeReducedFamily G 2, ∀ V₂ ∈ primeReducedFamily G 2,
      V₁ ⊔ V₂ ∈ primeReducedFamily G 2) ∧
    primeReducedAggregate G 2 ∈ primeReducedFamily G 2 ∧
    (∀ V ∈ primeReducedFamily G 2, V ≤ primeReducedAggregate G 2)

theorem as_B_2_12 : B_2_12 := by
  intro G _ _
  refine ⟨fun V₁ h₁ V₂ h₂ => CFSG.Quasithin.isPrimeReduced_sup h₁ h₂,
    CFSG.Quasithin.isPrimeReduced_primeReducedAggregate 2,
    fun V hV => CFSG.Quasithin.le_primeReducedAggregate hV⟩

@[expose] def B_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSylowTwoOf T ⊤ →
    pCoreOf 2 (⊤ : Subgroup G) ≠ ⊥ → ∀ Z : Subgroup G, Z ≠ ⊥ →
      Z ≤ pCoreOf 2 (⊤ : Subgroup G) ⊓ omegaOneCenterOf T →
        Subgroup.normalClosure (Z : Set G) ∈ primeReducedFamily G 2 ∧
        ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ∈ primeReducedFamily G 2 ∧
        Subgroup.normalClosure (Z : Set G) =
          ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ⊔
            (Subgroup.normalClosure (Z : Set G) ⊓ Subgroup.center G)

section BurnsideB2d

private theorem burnsideB2d_pCoreOf_top (G : Type) [Group G] :
    pCoreOf 2 (⊤ : Subgroup G) = pCore 2 G := by
  unfold pCoreOf
  exact CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := G))

private theorem burnsideB2d_charTwo_top (G : Type) [Group G] [Finite G]
    (hF : CFSG.Open.genFittingFStar G = pCore 2 G) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : CFSG.generalizedFitting G = pCore 2 G :=
    (CFSG.Adapters.genFittingFStar_eq_foundations G).symm.trans hF
  have hchar : CFSG.IsCharacteristicP 2 G :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore G 2).mpr hgen
  unfold CFSG.QuasithinUnique.CharTwo
  rw [burnsideB2d_pCoreOf_top G]
  intro x hx
  exact hchar hx.2

private theorem burnsideB2d_conjClosure_top (G : Type) [Group G] (Z : Subgroup G) :
    CFSG.Quasithin.conjClosure Z ⊤ = Subgroup.normalClosure (Z : Set G) := by
  unfold CFSG.Quasithin.conjClosure Subgroup.normalClosure
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Group.mem_conjugatesOfSet_iff, Subgroup.mem_top, true_and,
    isConj_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨h, z, hz, rfl⟩
    exact ⟨z, hz, h, rfl⟩
  · rintro ⟨z, hz, h, rfl⟩
    exact ⟨h, z, hz, rfl⟩

open CFSG.ASVolI.ChB CFSG.Quasithin in
private theorem burnsideB2d_Jj_zero {G : Type} [Group G] [Finite G] (T : Subgroup G) :
    Jj T 0 = CFSG.Quasithin.thompsonJ T := by
  rw [Jj_eq_higherElemThompson_of_le T 0 (Nat.zero_le _), CFSG.higherElemThompson_zero,
    elemThompson_map_subtype_eq_thompsonJ]

open CFSG.Quasithin in
private theorem burnsideB2d_pCoreOf_autI_eq_bot {G : Type} [Group G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : IsTwoReducedIn (⊤ : Subgroup G) V) :
    pCoreOf 2 (autI hV (⊤ : Subgroup G)) = ⊥ :=
  CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot h

private theorem burnsideB2d_pow_mul_mem {G : Type*} [Group G] {K : Subgroup G} [K.Normal] {d k : G}
    (hk : k ∈ K) {n : ℕ} (hd : d ^ n ∈ K) : (d * k) ^ n ∈ K := by
  have key : ∀ m : ℕ, ∃ k' ∈ K, (d * k) ^ m = d ^ m * k' := by
    intro m
    induction m with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨k', hk', h⟩ := ih
      have hc : d⁻¹ * k' * d ∈ K := by
        have := Subgroup.Normal.conj_mem inferInstance k' hk' d⁻¹
        rwa [inv_inv] at this
      refine ⟨(d⁻¹ * k' * d) * k, K.mul_mem hc hk, ?_⟩
      rw [pow_succ, h, pow_succ]
      group
  obtain ⟨k', hk', h⟩ := key n
  rw [h]
  exact K.mul_mem hd hk'

private theorem burnsideB2d_sq_mem_centralizer {G : Type*} [Group G] {W : Subgroup G}
    (hexp : ∀ x ∈ ⁅W, (⊤ : Subgroup G)⁆, x ^ 2 = 1) {k : G}
    (hk : k ∈ Subgroup.centralizer ((⁅W, (⊤ : Subgroup G)⁆ : Subgroup G) : Set G)) {w : G}
    (hw : w ∈ W) : w * (k * k) = (k * k) * w := by
  have hcmem : w * k * w⁻¹ * k⁻¹ ∈ ⁅W, (⊤ : Subgroup G)⁆ := by
    have := Subgroup.commutator_mem_commutator hw (Subgroup.mem_top k)
    rwa [commutatorElement_def] at this
  obtain ⟨c, hc_def⟩ : ∃ c : G, c = w * k * w⁻¹ * k⁻¹ := ⟨_, rfl⟩
  rw [← hc_def] at hcmem
  have hc2 : c ^ 2 = 1 := hexp c hcmem
  have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hck : c * k = k * c := Subgroup.mem_centralizer_iff.mp hk c hcmem
  have hkw : k * w * k⁻¹ = c * w := by
    calc k * w * k⁻¹ = c⁻¹ * w := by rw [hc_def]; group
      _ = c * w := by rw [hcinv]
  have hkck : k * c * k⁻¹ = c := by rw [← hck, mul_inv_cancel_right]
  have key : k * k * w * (k * k)⁻¹ = w := by
    calc k * k * w * (k * k)⁻¹ = k * (k * w * k⁻¹) * k⁻¹ := by group
      _ = k * (c * w) * k⁻¹ := by rw [hkw]
      _ = (k * c * k⁻¹) * (k * w * k⁻¹) := by group
      _ = c * (c * w) := by rw [hkck, hkw]
      _ = w := by rw [← mul_assoc, hcc, one_mul]
  calc w * (k * k) = (k * k * w * (k * k)⁻¹) * (k * k) := by rw [key]
    _ = (k * k) * w := by group

open CFSG.Quasithin in
private theorem burnsideB2d_isPrimeReduced_of_top {G : Type*} [Group G] {V : Subgroup G}
    (h : IsTwoReducedIn (⊤ : Subgroup G) V) : IsPrimeReduced 2 V := by
  obtain ⟨-, hN, hel, hD⟩ := h
  have hnorm : V.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hN)
  refine (isPrimeReduced_iff_forall 2).mpr ⟨hnorm,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mpr hel, fun D hDn hDp =>
      hD D le_top (Subgroup.normalizer_eq_top_iff.mpr hDn).symm.le hDp⟩

open CFSG.Quasithin in
private theorem burnsideB2d_commutator_isPrimeReduced {G : Type*} [Group G] {W : Subgroup G}
    (hW : IsPrimeReduced 2 W) : IsPrimeReduced 2 ⁅W, (⊤ : Subgroup G)⁆ := by
  obtain ⟨hWn, hWe, hWf⟩ := (isPrimeReduced_iff_forall 2).mp hW
  haveI : W.Normal := hWn
  haveI := hWe
  have hle : ⁅W, (⊤ : Subgroup G)⁆ ≤ W := Subgroup.commutator_le_left W ⊤
  have hexp : ∀ x ∈ ⁅W, (⊤ : Subgroup G)⁆, x ^ 2 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian x (hle hx)
  have hUe : CFSG.IsElementaryAbelian 2 ↥⁅W, (⊤ : Subgroup G)⁆ :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_of_le hle hWe
  refine (isPrimeReduced_iff_forall 2).mpr ⟨inferInstance, hUe, ?_⟩
  intro D hD hDp
  haveI := hD
  have hsq : ∀ k ∈ Subgroup.centralizer ((⁅W, (⊤ : Subgroup G)⁆ : Subgroup G) : Set G),
      k * k ∈ Subgroup.centralizer (W : Set G) := fun k hk =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => burnsideB2d_sq_mem_centralizer hexp hk hw
  have hL_le_K : Subgroup.centralizer (W : Set G) ≤
      Subgroup.centralizer ((⁅W, (⊤ : Subgroup G)⁆ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)
  have hD' := hWf (D ⊔ Subgroup.centralizer ((⁅W, (⊤ : Subgroup G)⁆ : Subgroup G) : Set G))
    inferInstance ?_
  · exact (le_sup_left.trans hD').trans hL_le_K
  · intro m hm
    obtain ⟨d, hd, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hm
    obtain ⟨a, ha⟩ := hDp d hd
    refine ⟨a + 1, ?_⟩
    have h1 : (d * k) ^ (2 ^ a) ∈ Subgroup.centralizer ((⁅W, (⊤ : Subgroup G)⁆ : Subgroup G) : Set G) :=
      burnsideB2d_pow_mul_mem hk ha
    have h2 : (d * k) ^ 2 ^ (a + 1) = ((d * k) ^ 2 ^ a) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    rw [h2, pow_two]
    exact hsq _ h1


open scoped commutatorElement in
open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideB2d_le_sup_center {G : Type} [Group G] [Finite G] {T U Z : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hU : IsTwoReducedIn (⊤ : Subgroup G) U)
    (hZT : Z ≤ quasithinOmegaOneCenter T) (hZU : Z ≤ U) :
    Z ≤ ⁅U, (⊤ : Subgroup G)⁆ ⊔ (U ⊓ Subgroup.center G) := by
  have hel : IsElemAbelian 2 U := hU.2.2.1
  have hTN : T ≤ Subgroup.normalizer (U : Set G) := le_trans le_top hU.2.1
  have hS : IsSylowTwoOf (autI hel T) (autI hel (⊤ : Subgroup G)) :=
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hT hU.2.1
  have hfixsub := CFSG.Quasithin.S1549D.fixV_le_commV_sup_fixV (V := IntMod U hel)
    (fun x => IntMod.sq_eq_one x) hS
  obtain ⟨ι, hι⟩ : ∃ ι : IntMod U hel →* G, ∀ x, ι x = x.val :=
    ⟨{ toFun := IntMod.val, map_one' := IntMod.val_one,
       map_mul' := fun a b => IntMod.val_mul a b }, fun _ => rfl⟩
  have hcomm : commV (autI hel (⊤ : Subgroup G)) ≤
      (⁅U, (⊤ : Subgroup G)⁆ ⊔ (U ⊓ Subgroup.center G)).comap ι := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, y, rfl⟩
    obtain ⟨g, -, rfl⟩ := (mem_autI hel).1 hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, hι, IntMod.val_mul, IntMod.val_inv,
      convI_apply_val]
    apply Subgroup.mem_sup_left
    have hc := Subgroup.commutator_mem_commutator y.val_mem (Subgroup.mem_top (g : G))
    have e : (g : G) * y.val * (g : G)⁻¹ * y.val⁻¹ = (⁅y.val, (g : G)⁆)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact inv_mem hc
  have hfix : fixV (autI hel (⊤ : Subgroup G)) ≤
      (⁅U, (⊤ : Subgroup G)⁆ ⊔ (U ⊓ Subgroup.center G)).comap ι := by
    intro w hw
    rw [Subgroup.mem_comap, hι]
    apply Subgroup.mem_sup_right
    rw [Subgroup.mem_inf]
    refine ⟨w.val_mem, Subgroup.mem_center_iff.mpr fun g => ?_⟩
    have hcw := (mem_fixV_autI hel hU.2.1 w).mp hw
    exact Subgroup.mem_centralizer_iff.mp hcw g (Subgroup.mem_top g)
  intro z hz
  have hzU : z ∈ U := hZU hz
  have hvz : IntMod.mk hel (⟨z, hzU⟩ : U) ∈ fixV (autI hel T) := by
    rw [mem_fixV_autI hel hTN]
    exact (CFSG.Quasithin.B2F.omegaOneCenter_le_inf_centralizer T (hZT hz)).2
  have hmem := hfixsub hvz
  have hfin := (sup_le hcomm hfix) hmem
  rw [Subgroup.mem_comap, hι] at hfin
  exact hfin

open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideB2d_main {G : Type} [Group G] [Finite G] {T Z : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hZT : Z ≤ quasithinOmegaOneCenter T)
    (hZO : Z ≤ pCoreOf 2 (⊤ : Subgroup G)) :
    IsPrimeReduced 2 (CFSG.Quasithin.conjClosure Z ⊤) ∧
      IsPrimeReduced 2 ⁅CFSG.Quasithin.conjClosure Z ⊤, (⊤ : Subgroup G)⁆ ∧
      CFSG.Quasithin.conjClosure Z ⊤ = ⁅CFSG.Quasithin.conjClosure Z ⊤, (⊤ : Subgroup G)⁆ ⊔
        (CFSG.Quasithin.conjClosure Z ⊤ ⊓ Subgroup.center G) := by
  have hU : IsTwoReducedIn (⊤ : Subgroup G) (CFSG.Quasithin.conjClosure Z ⊤) :=
    B2_13_conjClosure hT hZT hZO
  have hP := burnsideB2d_isPrimeReduced_of_top hU
  have hC := burnsideB2d_commutator_isPrimeReduced hP
  have hUn : (CFSG.Quasithin.conjClosure Z ⊤).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hU.2.1)
  refine ⟨hP, hC, le_antisymm ?_ ?_⟩
  · refine CFSG.Quasithin.conjClosure_le fun h _ z hz => ?_
    have hzK := burnsideB2d_le_sup_center hT hU hZT (CFSG.Quasithin.le_conjClosure Z ⊤) hz
    exact Subgroup.Normal.conj_mem inferInstance z hzK h
  · exact sup_le (Subgroup.commutator_le_left _ _) inf_le_left

end BurnsideB2d

theorem as_B_2_13 : B_2_13 := by
  intro G _ _ T hT _ Z _ hZ
  have hZT : Z ≤ quasithinOmegaOneCenter T := hZ.trans inf_le_right
  have hZO : Z ≤ pCoreOf 2 (⊤ : Subgroup G) := hZ.trans inf_le_left
  obtain ⟨h1, h2, h3⟩ := burnsideB2d_main hT hZT hZO
  rw [← burnsideB2d_conjClosure_top G Z]
  exact ⟨h1, h2, h3⟩

@[expose] def B_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], genFittingFStar G = pCore 2 G →
    ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ Z : Subgroup G, Z ≠ ⊥ → Z ≤ omegaOneCenterOf T →
      (Subgroup.normalClosure (Z : Set G) ∈ primeReducedFamily G 2 ∧
        ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ∈ primeReducedFamily G 2 ∧
        Subgroup.normalClosure (Z : Set G) =
          ⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ⊔
            (Subgroup.normalClosure (Z : Set G) ⊓ Subgroup.center G)) ∧
      Subgroup.normalClosure (Z : Set G) ≤ omegaOneCenterOf (pCoreOf 2 (⊤ : Subgroup G)) ∧
      (pCore 2 (G ⧸ Subgroup.centralizer (Subgroup.normalClosure (Z : Set G) : Set G)) = ⊥ ∧
        pCore 2 (G ⧸ Subgroup.centralizer
          ((⁅Subgroup.normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ : Subgroup G) : Set G)) = ⊥)

theorem as_B_2_14 : B_2_14 := by
  intro G _ _ hF T hT Z _ hZ
  have hZT : Z ≤ quasithinOmegaOneCenter T := hZ
  have hZO : Z ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    hZT.trans (CFSG.Quasithin.omegaOneCenter_le_pCoreOf_of_charTwo hT
      (burnsideB2d_charTwo_top G hF))
  obtain ⟨h1, h2, h3⟩ := burnsideB2d_main hT hZT hZO
  rw [burnsideB2d_conjClosure_top] at h1 h2 h3
  refine ⟨⟨h1, h2, h3⟩, ?_, ?_, ?_⟩
  · rw [burnsideB2d_pCoreOf_top G, CFSG.Quasithin.BlueprintB2.omegaOneCenterOf_eq_centerTorsion]
    exact CFSG.Quasithin.isPrimeReduced_le_centerTorsion_pCore h1
  · obtain ⟨_, _, hc⟩ := h1
    exact hc
  · obtain ⟨_, _, hc⟩ := h2
    exact hc

@[expose] def B_2_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], genFittingFStar G = pCore 2 G →
    ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ Z : Subgroup G, Z = omegaOneCenterOf T →
      (¬ Jj T 0 ≤ Subgroup.centralizer (Subgroup.normalClosure (Z : Set G) : Set G) ∧
        (∃ hU : IsElemAbelian 2 (Subgroup.normalClosure (Z : Set G)),
          IsFFModule (autI hU ⊤) ∧ pCoreOf 2 (autI hU ⊤) = ⊥)) ∨
      (Jj T 0 ≤ Subgroup.centralizer (Subgroup.normalClosure (Z : Set G) : Set G) ∧
        (Subgroup.centralizer (Z : Set G) : Set G) * (Subgroup.normalizer (Jj T 0 : Set G) : Set G) =
          Set.univ)

open scoped Pointwise in
open CFSG.Quasithin in
theorem as_B_2_15 : B_2_15 := by
  intro G _ _ hF T hT Z hZ
  subst hZ
  rw [← burnsideB2d_conjClosure_top G (omegaOneCenterOf T), burnsideB2d_Jj_zero T]
  obtain ⟨hU, h⟩ := CFSG.Quasithin.B2_15 (burnsideB2d_charTwo_top G hF) hT
  rcases h with ⟨hnot, hFF, hred⟩ | ⟨hJ, hfac⟩
  · exact Or.inl ⟨hnot, hU, hFF, burnsideB2d_pCoreOf_autI_eq_bot hU hred⟩
  · refine Or.inr ⟨hJ, Set.eq_univ_of_forall fun g => ?_⟩
    obtain ⟨c, hc, n, hn, rfl⟩ := hfac g (Subgroup.mem_top g)
    exact Set.mem_mul.mpr ⟨c, hc.2, n, hn.2, rfl⟩

@[expose] def B_2_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → genFittingFStar G = pCore 2 G →
    ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ Z : Subgroup G, Z = omegaOneCenterOf T →
      ∀ V : Subgroup G, V = Subgroup.normalClosure (Z : Set G) →
        V ∈ primeReducedFamily G 2 ∧
        ((Jj T 0 ≤ Subgroup.centralizer (V : Set G) ∧
            (Subgroup.normalizer (Jj T 0 : Set G) : Set G) *
              (Subgroup.centralizer (omegaOneCenterOf T : Set G) : Set G) = Set.univ) ∨
          (¬ Jj T 0 ≤ Subgroup.centralizer (V : Set G) ∧ ∃ hV : IsElemAbelian 2 V,
            IsSylowTwoOf (autI hV (Jj T 0)) (autI hV (Jj ⊤ 0)) ∧
            ∃ (n : ℕ) (Ls : Fin n → Subgroup (MulAut (IntMod V hV))),
              IsIntDirProd (autI hV (Jj ⊤ 0)) Ls ∧
              IsIntDirSum (⊤ : Subgroup (IntMod V hV))
                (fun o : Option (Fin n) => o.elim (fixV (autI hV (Jj ⊤ 0))) (fun i => commV (Ls i))) ∧
              (∀ i, Nonempty (↥(Ls i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
                ActsAsNaturalL2 (Ls i) (commV (Ls i))) ∧
              (∀ g ∈ autI hV ⊤, ∀ i, ∃ j, (Ls i).map (MulAut.conj g).toMonoidHom = Ls j ∧
                (commV (Ls i)).map g.toMonoidHom = commV (Ls j)))) ∧
        CFSG.Open.pRank 2 (T ⊓ Subgroup.centralizer (V : Set G)) = CFSG.Open.pRank 2 T ∧
        Jj (T ⊓ Subgroup.centralizer (V : Set G)) 0 ≤ Jj T 0

section BurnsideB2e

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_Jj_zero {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ChB.Jj H 0 = CFSG.Quasithin.thompsonJ H := by
  rw [ChB.Jj, if_pos (Nat.zero_le _), CFSG.higherElemThompson_zero ↥H,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ H]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_baumOf {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ChB.baumOf H = CFSG.Quasithin.baum H := by
  unfold ChB.baumOf CFSG.Quasithin.baum
  rw [burnsideB2e_Jj_zero]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_twoResidual_top {G : Type} [Group G] [Finite G] :
    CFSG.Quasithin.twoResidual (⊤ : Subgroup G) = CFSG.Quasithin.pResidualOf 2 (⊤ : Subgroup G) := by
  rw [CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper, CFSG.Quasithin.oTwoUpper_eq_pResidualOf]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_starPre_eq {G : Type} [Group G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVN : V.Normal) (M : Subgroup G)
    (Y : Subgroup (MulAut (CFSG.Quasithin.IntMod V hV))) :
    CFSG.Quasithin.B2F.starPre hV hVN M Y = M ⊓ ChB.preimI hV Y := by
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) :=
    CFSG.Quasithin.B2F.mem_normalizer_of_normal hVN
  ext x
  simp only [CFSG.Quasithin.B2F.starPre, ChB.preimI, Subgroup.mem_inf, Subgroup.mem_comap,
    Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨hM, hY⟩
    exact ⟨hM, ⟨⟨x, hN x⟩, hY, rfl⟩⟩
  · rintro ⟨hM, ⟨y, hY, hyx⟩⟩
    have hy : y = ⟨x, hN x⟩ := Subtype.ext hyx
    rw [hy] at hY
    exact ⟨hM, hY⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_O2Phi {G : Type} [Group G] (L : Subgroup G) :
    ChB.O2Phi L = CFSG.Quasithin.oTwoPhi L := rfl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_noStrong {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (R : Subgroup G)
    (hc : ∀ B : Subgroup (MulAut (CFSG.Quasithin.IntMod V hV)),
      B ≤ CFSG.Quasithin.autI hV R → ¬ CFSG.Quasithin.IsStrongFFStarOffender
        (CFSG.Quasithin.autI hV ⊤) B) :
    ∀ B : Subgroup (MulAut (CFSG.Quasithin.IntMod V hV)),
      ¬ CFSG.Quasithin.IsStrongFFStarOffender (CFSG.Quasithin.autI hV R) B := by
  intro B hB
  exact hc B hB.1.1
    ⟨CFSG.Quasithin.isFFStarOffender_mono (CFSG.Quasithin.autI_mono hV le_top) hB.1, hB.2⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_offenders {G : Type} [Group G] [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (R L : Subgroup G) (n : ℕ)
    (Y : Fin n → Subgroup (MulAut (CFSG.Quasithin.IntMod V hV)))
    (hE : ∀ B : Subgroup (MulAut (CFSG.Quasithin.IntMod V hV)), B ≤ CFSG.Quasithin.autI hV R →
      CFSG.Quasithin.IsFFStarOffender (CFSG.Quasithin.autI hV ⊤) B →
        ∃ (r : ℕ) (Bs : Fin r → Subgroup (MulAut (CFSG.Quasithin.IntMod V hV))),
          B = ⨆ k, Bs k ∧
            ∀ k, CFSG.Quasithin.IsFFStarOffender (CFSG.Quasithin.autI hV ⊤) (Bs k) ∧
              ∃ (j : Fin n) (g : MulAut (CFSG.Quasithin.IntMod V hV)),
                g ∈ CFSG.Quasithin.autI hV L ∧
                Bs k ≤ (Y j).map (MulAut.conj g).toMonoidHom ∧
                (Y j).map (MulAut.conj g).toMonoidHom ≤ CFSG.Quasithin.autI hV R) :
    ∀ A : Subgroup (MulAut (CFSG.Quasithin.IntMod V hV)),
      CFSG.Quasithin.IsFFStarOffender (CFSG.Quasithin.autI hV R) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (CFSG.Quasithin.IntMod V hV))),
          A = ⨆ k, Ai k ∧
            ∀ k, CFSG.Quasithin.IsFFStarOffender (CFSG.Quasithin.autI hV R) (Ai k) ∧
              ∃ (j : Fin n) (g : MulAut (CFSG.Quasithin.IntMod V hV)),
                g ∈ CFSG.Quasithin.autI hV L ∧
                Ai k ≤ CFSG.Quasithin.B1.conjAut g (Y j) ∧
                CFSG.Quasithin.B1.conjAut g (Y j) ≤ CFSG.Quasithin.autI hV R := by
  intro A hA
  obtain ⟨r, Bs, hAeq, hBs⟩ := hE A hA.1
    (CFSG.Quasithin.isFFStarOffender_mono (CFSG.Quasithin.autI_mono hV le_top) hA)
  refine ⟨r, Bs, hAeq, fun k => ?_⟩
  obtain ⟨hk1, j, g, hg, hk2, hk3⟩ := hBs k
  refine ⟨⟨hk2.trans hk3, hk1.2.1, hk1.2.2.1, hk1.2.2.2⟩, j, g, hg, ?_, ?_⟩
  · rw [CFSG.Quasithin.conjAut_eq_map]
    exact hk2
  · rw [CFSG.Quasithin.conjAut_eq_map]
    exact hk3



open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_disjoint_sup {α : Type*} [CompleteLattice α] [IsModularLattice α]
    {C S F : α} (hCS : Disjoint C S) (hF : Disjoint F (C ⊔ S)) : Disjoint C (F ⊔ S) := by
  rw [disjoint_iff] at hCS hF ⊢
  have h1 : (S ⊔ F) ⊓ (C ⊔ S) = S := by
    rw [sup_inf_assoc_of_le F (le_sup_right : S ≤ C ⊔ S), hF, sup_bot_eq]
  have h2 : C ⊓ (F ⊔ S) ≤ S := by
    calc C ⊓ (F ⊔ S) ≤ (C ⊔ S) ⊓ (F ⊔ S) := inf_le_inf_right _ le_sup_left
      _ = (S ⊔ F) ⊓ (C ⊔ S) := by rw [sup_comm F S, inf_comm]
      _ = S := h1
  exact le_antisymm ((le_inf inf_le_left h2).trans hCS.le) bot_le

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_iSupIndep_finset {ι α : Type*} [CompleteLattice α]
    (I : Finset ι) (φ : ι → α)
    (hind : ∀ a ∈ I, Disjoint (φ a) (⨆ b ∈ I, ⨆ (_ : b ≠ a), φ b)) :
    iSupIndep (fun x : I => φ x.1) := by
  classical
  have h : I.SupIndep φ := by
    refine Finset.supIndep_iff_disjoint_erase.2 fun a ha => ?_
    have herase : (I.erase a).sup φ = ⨆ b ∈ I, ⨆ (_ : b ≠ a), φ b := by
      rw [Finset.sup_eq_iSup]
      apply le_antisymm
      · exact iSup₂_le fun b hb => le_iSup₂_of_le b (Finset.mem_of_mem_erase hb)
          (le_iSup_of_le (Finset.ne_of_mem_erase hb) le_rfl)
      · exact iSup₂_le fun b hb => iSup_le fun hne =>
          le_iSup₂_of_le b (Finset.mem_erase.2 ⟨hne, hb⟩) le_rfl
    rw [herase]
    exact hind a ha
  exact iSupIndep_comp_coe_iff_supIndep.2 h

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_iSup_fin {ι α : Type*} [CompleteLattice α] (I : Finset ι) (F : ι → α) :
    ⨆ i : Fin I.card, F (I.equivFin.symm i).1 = ⨆ L ∈ I, F L := by
  apply le_antisymm
  · exact iSup_le fun i => le_iSup₂_of_le (I.equivFin.symm i).1 (I.equivFin.symm i).2 le_rfl
  · exact iSup₂_le fun L hL => le_iSup_of_le (I.equivFin ⟨L, hL⟩) (by simp)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_iSupIndep_option {M : Type*} [CommGroup M] {n : ℕ}
    (F : Subgroup M) (U : Fin n → Subgroup M) (hU : iSupIndep U)
    (hF : Disjoint F (⨆ i, U i)) :
    iSupIndep (fun o : Option (Fin n) => o.elim F U) := by
  rw [iSupIndep_def]
  rintro (_ | k)
  · have hsup : (⨆ (j : Option (Fin n)) (_ : j ≠ none), j.elim F U) = ⨆ i, U i := by
      apply le_antisymm
      · refine iSup₂_le fun j hj => ?_
        cases j with
        | none => exact absurd rfl hj
        | some i => exact le_iSup U i
      · exact iSup_le fun i => le_iSup₂_of_le (some i) (by simp) le_rfl
    show Disjoint F (⨆ (j : Option (Fin n)) (_ : j ≠ none), j.elim F U)
    rw [hsup]
    exact hF
  · have hS : (⨆ (j : Option (Fin n)) (_ : j ≠ some k), j.elim F U) ≤
        F ⊔ ⨆ (i : Fin n) (_ : i ≠ k), U i := by
      refine iSup₂_le fun j hj => ?_
      cases j with
      | none => exact le_sup_left
      | some i =>
        have hik : i ≠ k := fun h => hj (by rw [h])
        exact le_sup_of_le_right (le_iSup₂_of_le i hik le_rfl)
    have hk : Disjoint (U k) (⨆ (i : Fin n) (_ : i ≠ k), U i) := iSupIndep_def.1 hU k
    have hle : U k ⊔ ⨆ (i : Fin n) (_ : i ≠ k), U i ≤ ⨆ i, U i :=
      sup_le (le_iSup U k) (iSup₂_le fun i _ => le_iSup U i)
    have hFk : Disjoint F (U k ⊔ ⨆ (i : Fin n) (_ : i ≠ k), U i) := Disjoint.mono_right hle hF
    show Disjoint (U k) (⨆ (j : Option (Fin n)) (_ : j ≠ some k), j.elim F U)
    exact Disjoint.mono_right hS (burnsideB2e_disjoint_sup hk hFk)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_charTwo_top {G : Type} [Group G] [Finite G]
    (hgen : CFSG.Open.genFittingFStar G = CFSG.pCore 2 G) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup G) := by
  unfold CFSG.QuasithinUnique.CharTwo
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2]
  intro x hx
  have hC : x ∈ Subgroup.centralizer (CFSG.Open.genFittingFStar G : Set G) := by
    rw [hgen]
    exact hx.2
  have hF := CFSG.Adapters.generalized_fitting_self_centralizing G hC
  rw [hgen] at hF
  exact hF

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_conjClosure_top {G : Type} [Group G] (Z : Subgroup G) :
    CFSG.Quasithin.conjClosure Z ⊤ = Subgroup.normalClosure (Z : Set G) := by
  unfold CFSG.Quasithin.conjClosure Subgroup.normalClosure
  congr 1
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq, Subgroup.mem_top, true_and, Group.mem_conjugatesOfSet_iff,
    isConj_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨h, z, hz, hx⟩
    exact ⟨z, hz, h, hx⟩
  · rintro ⟨z, hz, h, hx⟩
    exact ⟨h, z, hz, hx⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
private theorem burnsideB2e_isPrimeReduced_of_twoReduced {G : Type} [Group G] {V : Subgroup G}
    (h : CFSG.Quasithin.IsTwoReducedIn (⊤ : Subgroup G) V) :
    CFSG.Quasithin.IsPrimeReduced 2 V := by
  obtain ⟨-, hN, hEA, hD⟩ := h
  have hVN : V.Normal := Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hN)
  refine (CFSG.Quasithin.isPrimeReduced_iff_forall 2).2 ⟨hVN, ?_, fun D hDn hDp => ?_⟩
  · exact (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).1 hEA
  · exact hD D le_top (Subgroup.normalizer_eq_top_iff.2 hDn).ge hDp

end BurnsideB2e

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_16 : B_2_16 := by
  unfold B_2_16
  intro G _ _ hsol hgen T hT Z hZ V hV
  subst hZ
  subst hV
  have hcc : Subgroup.normalClosure ((omegaOneCenterOf T : Subgroup G) : Set G) =
      CFSG.Quasithin.conjClosure (CFSG.Open.quasithinOmegaOneCenter T) ⊤ := by
    rw [burnsideB2e_conjClosure_top]
    rfl
  obtain ⟨hU, hred, hcase, hrank, hJ⟩ := CFSG.Quasithin.B2_16 (H := ⊤) (T := T)
    inferInstance (burnsideB2e_charTwo_top hgen) hT hcc
  simp only [burnsideB2e_Jj_zero]
  refine ⟨burnsideB2e_isPrimeReduced_of_twoReduced hred, ?_, hrank, hJ⟩
  rcases hcase with ⟨hJC, hall⟩ | ⟨hJn, I, hSyl, hI_eq, hcomm, hind, hnat, hfix_sup, hfix_inf,
    hind_c, hconj⟩
  · left
    refine ⟨hJC, ?_⟩
    rw [CFSG.Quasithin.omegaOneCenterOf_eq]
    refine Set.eq_univ_iff_forall.2 fun x => ?_
    obtain ⟨n, hn, c, hc, hx⟩ := hall x (Subgroup.mem_top x)
    exact Set.mem_mul.2 ⟨n, hn.2, c, hc.2, hx.symm⟩
  · right
    have hUi : iSupIndep (fun i => CFSG.Quasithin.commV ((I.equivFin.symm i).1)) :=
      (burnsideB2e_iSupIndep_finset I (fun L => CFSG.Quasithin.commV L)
        (fun L hL => disjoint_iff.2 (hind_c L hL))).comp I.equivFin.symm.injective
    have hsupU : (⨆ i : Fin I.card, CFSG.Quasithin.commV ((I.equivFin.symm i).1)) =
        ⨆ L ∈ I, CFSG.Quasithin.commV L :=
      burnsideB2e_iSup_fin I (fun L => CFSG.Quasithin.commV L)
    have hFd : Disjoint (CFSG.Quasithin.fixV (CFSG.Quasithin.autI hU (CFSG.Quasithin.thompsonJ
        (⊤ : Subgroup G))))
        (⨆ i : Fin I.card, CFSG.Quasithin.commV ((I.equivFin.symm i).1)) := by
      rw [hsupU]
      exact disjoint_iff.2 hfix_inf
    have hIS := burnsideB2e_iSupIndep_option (CFSG.Quasithin.fixV
      (CFSG.Quasithin.autI hU (CFSG.Quasithin.thompsonJ (⊤ : Subgroup G))))
      (fun i => CFSG.Quasithin.commV ((I.equivFin.symm i).1)) hUi hFd
    refine ⟨hJn, hU, hSyl, I.card, fun i => (I.equivFin.symm i).1, ⟨?_, ?_, ?_⟩, ⟨hIS, ?_⟩, ?_, ?_⟩
    · refine fun i j hij a ha b hb => ?_
      have hne : (I.equivFin.symm i).1 ≠ (I.equivFin.symm j).1 := fun h =>
        hij (I.equivFin.symm.injective (Subtype.ext h))
      exact hcomm _ (I.equivFin.symm i).2 _ (I.equivFin.symm j).2 hne a ha b hb
    · exact (burnsideB2e_iSupIndep_finset I (fun L => L)
        (fun L hL => disjoint_iff.2 (hind L hL))).comp I.equivFin.symm.injective
    · rw [hI_eq]
      exact burnsideB2e_iSup_fin I (fun L => L)
    · show (⨆ o : Option (Fin I.card), o.elim (CFSG.Quasithin.fixV
          (CFSG.Quasithin.autI hU (CFSG.Quasithin.thompsonJ (⊤ : Subgroup G))))
          (fun i => CFSG.Quasithin.commV ((I.equivFin.symm i).1))) = ⊤
      rw [iSup_option]
      change CFSG.Quasithin.fixV (CFSG.Quasithin.autI hU (CFSG.Quasithin.thompsonJ
        (⊤ : Subgroup G))) ⊔ (⨆ i : Fin I.card, CFSG.Quasithin.commV ((I.equivFin.symm i).1)) = ⊤
      rw [hsupU]
      exact hfix_sup
    · intro i
      obtain ⟨e', _⟩ := hnat _ (I.equivFin.symm i).2
      exact ⟨⟨e'⟩, hnat _ (I.equivFin.symm i).2⟩
    · intro g hg i
      obtain ⟨hmem, hcm⟩ := hconj g hg (I.equivFin.symm i).1 (I.equivFin.symm i).2
      rw [CFSG.Quasithin.conjAut_eq_map] at hmem hcm
      refine ⟨I.equivFin ⟨_, hmem⟩, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]
      · simp only [Equiv.symm_apply_apply]
        exact hcm

@[expose] def B_2_17 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n : ℕ) (X : Fin n → Subgroup (MulAut V)) (L : Subgroup (MulAut V)),
      L ≤ ⨆ i, X i → ∑ i, rkIdx (fixV (X i)) ≤ rkIdx (fixV L) →
        fixV L = fixV (⨆ i, X i) ∧ rkIdx (fixV L) = ∑ i, rkIdx (fixV (X i))

theorem as_B_2_17 : B_2_17 := by
  intro V _ _ hV n X L hL h
  exact CFSG.Quasithin.B2_17_aut hV X hL h

@[expose] def B_2_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R : Subgroup G), IsPGroup 2 R → V ≤ R →
      pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ R ⊓ Subgroup.centralizer (V : Set G) →
      twoResidual (⊤ : Subgroup G) ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) →
      twoResidual (⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤ O2Phi (twoResidual (⊤ : Subgroup G)) →
      (∀ B : Subgroup (MulAut (IntMod V hV)), B ≤ autI hV R →
        ¬ IsStrongFFStarOffender (autI hV ⊤) B) →
      ∀ (n : ℕ) (X : Fin n → Subgroup G),
        (∀ i, (∃ l ∈ twoResidual (⊤ : Subgroup G), (X i).map (MulAut.conj l).toMonoidHom ≤ R) ∧
          Jj (X i) 0 = X i ∧ CFSG.Open.pRank 2 (X i) = CFSG.Open.pRank 2 R) →
        autI hV (twoResidual (⊤ : Subgroup G)) ≤ ⨆ i, autI hV (X i) →
        ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV (twoResidual (⊤ : Subgroup G)))) →
        Jj R 0 ≤ ⨆ i, X i →
          pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ baumOf R ∧
          omegaOneCenterOf (Jj R 0) =
            (omegaOneCenterOf (Jj R 0) ⊓ Subgroup.centralizer (twoResidual (⊤ : Subgroup G) : Set G)) ⊔
              (V ⊓ Subgroup.centralizer (Jj R 0 : Set G)) ∧
          (IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
              ((twoResidual (⊤ : Subgroup G) ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) →
            IsSylowTwoOf (baumOf R ⊓ Subgroup.centralizer (V : Set G))
              ((twoResidual (⊤ : Subgroup G) ⊔ baumOf R) ⊓ Subgroup.centralizer (V : Set G)) ∧
            (IsSylowTwoOf (autI hV (baumOf R)) (autI hV (twoResidual (⊤ : Subgroup G)) ⊔ autI hV (baumOf R)) →
              IsSylowTwoOf (baumOf R) (twoResidual (⊤ : Subgroup G) ⊔ baumOf R)))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_18 : B_2_18 := by
  unfold B_2_18
  intro G _ _ V hV hVN R hR hVR ha₁ ha₂ hb hc n X hd hLX hsum hJ
  have hde : ∃ (n : ℕ) (X : Fin n → Subgroup G),
      (∀ i, ∃ l ∈ CFSG.Quasithin.twoResidual (⊤ : Subgroup G),
        CFSG.Quasithin.cjSub l (X i) ≤ R) ∧
      (∀ i, X i = CFSG.Quasithin.thompsonJ (X i)) ∧
      (∀ i, CFSG.Open.pRank 2 (X i) = CFSG.Open.pRank 2 R) ∧
      CFSG.Quasithin.autI hV (CFSG.Quasithin.twoResidual (⊤ : Subgroup G)) ≤
        ⨆ i, CFSG.Quasithin.autI hV (X i) ∧
      ∑ i, CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (CFSG.Quasithin.autI hV (X i))) ≤
        CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV
          (CFSG.Quasithin.autI hV (CFSG.Quasithin.twoResidual (⊤ : Subgroup G)))) ∧
      CFSG.Quasithin.thompsonJ R ≤ ⨆ i, X i :=
    ⟨n, X, fun i => (hd i).1, fun i => by
        rw [← burnsideB2e_Jj_zero (X i)]
        exact (hd i).2.1.symm,
      fun i => (hd i).2.2, hLX, hsum, by
        rw [← burnsideB2e_Jj_zero R]
        exact hJ⟩
  have hbg := CFSG.Quasithin.B2_18 (L := CFSG.Quasithin.twoResidual (⊤ : Subgroup G)) hV hVN
    burnsideB2e_twoResidual_top hR hVR ha₁ ha₂ hb (burnsideB2e_noStrong hV R hc) hde
  rw [burnsideB2e_Jj_zero R, burnsideB2e_baumOf R]
  exact hbg

@[expose] def B_2_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R : Subgroup G), IsPGroup 2 R → V ≤ R →
      pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ R ⊓ Subgroup.centralizer (V : Set G) →
      IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
        ((twoResidual (⊤ : Subgroup G) ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) →
      twoResidual (⊤ : Subgroup G) ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) →
      twoResidual (⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤ O2Phi (twoResidual (⊤ : Subgroup G)) →
      (∀ B : Subgroup (MulAut (IntMod V hV)), B ≤ autI hV R →
        ¬ IsStrongFFStarOffender (autI hV ⊤) B) →
      ∀ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V hV))),
        (∀ i, (∃ l ∈ autI hV (twoResidual (⊤ : Subgroup G)), (Y i).map (MulAut.conj l).toMonoidHom ≤ autI hV R) ∧
          ∀ Ri : Subgroup G, IsSylowTwoOf Ri ((twoResidual (⊤ : Subgroup G) ⊔ R) ⊓ preimI hV (Y i)) →
            Y i = autI hV (Jj Ri 0) ∧ CFSG.Open.pRank 2 Ri = CFSG.Open.pRank 2 R) →
        autI hV (twoResidual (⊤ : Subgroup G)) ≤ ⨆ i, Y i →
        ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV (twoResidual (⊤ : Subgroup G)))) →
        (∀ B : Subgroup (MulAut (IntMod V hV)), B ≤ autI hV R → IsFFStarOffender (autI hV ⊤) B →
          ∃ (r : ℕ) (Bs : Fin r → Subgroup (MulAut (IntMod V hV))), B = ⨆ k, Bs k ∧
            ∀ k, IsFFStarOffender (autI hV ⊤) (Bs k) ∧
              ∃ (j : Fin n) (g : MulAut (IntMod V hV)), g ∈ autI hV (twoResidual (⊤ : Subgroup G)) ∧
                Bs k ≤ (Y j).map (MulAut.conj g).toMonoidHom ∧
                (Y j).map (MulAut.conj g).toMonoidHom ≤ autI hV R) →
          pCoreOf 2 (twoResidual (⊤ : Subgroup G)) ≤ baumOf R ∧
          omegaOneCenterOf (Jj R 0) =
            (omegaOneCenterOf (Jj R 0) ⊓ Subgroup.centralizer (twoResidual (⊤ : Subgroup G) : Set G)) ⊔
              (V ⊓ Subgroup.centralizer (Jj R 0 : Set G)) ∧
          IsSylowTwoOf (baumOf R ⊓ Subgroup.centralizer (V : Set G))
              ((baumOf R ⊔ twoResidual (⊤ : Subgroup G)) ⊓ Subgroup.centralizer (V : Set G)) ∧
          (IsSylowTwoOf (autI hV (baumOf R)) (autI hV (twoResidual (⊤ : Subgroup G)) ⊔ autI hV (baumOf R)) →
            IsSylowTwoOf (baumOf R) (twoResidual (⊤ : Subgroup G) ⊔ baumOf R))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
theorem as_B_2_19 : B_2_19 := by
  unfold B_2_19
  intro G _ _ V hV hVN R hR hVR hA₁ hA₂ hA₃ hB hC n Y hD hLY hsum hE
  have hbot : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.iff_card.2 ⟨0, by simp⟩
  have hex : ∀ i, ∃ S : Subgroup G, IsSylowTwoOf S
      (CFSG.Quasithin.B2F.starPre hV hVN (CFSG.Quasithin.twoResidual (⊤ : Subgroup G) ⊔ R)
        (Y i)) := fun i => by
    obtain ⟨S, hS, -⟩ := CFSG.Quasithin.B6.exists_isSylowTwoOf_ge hbot
      (bot_le : (⊥ : Subgroup G) ≤ CFSG.Quasithin.B2F.starPre hV hVN
        (CFSG.Quasithin.twoResidual (⊤ : Subgroup G) ⊔ R) (Y i))
    exact ⟨S, hS⟩
  choose Rs hRs using hex
  have hRs' : ∀ i, IsSylowTwoOf (Rs i)
      ((CFSG.Quasithin.twoResidual (⊤ : Subgroup G) ⊔ R) ⊓ ChB.preimI hV (Y i)) := fun i => by
    rw [← burnsideB2e_starPre_eq hV hVN]
    exact hRs i
  have hbg := CFSG.Quasithin.B2_19 (L := CFSG.Quasithin.twoResidual (⊤ : Subgroup G)) hV hVN
    burnsideB2e_twoResidual_top hR hVR hA₁ hA₂ hA₃ hB (burnsideB2e_noStrong hV R hC)
    ⟨n, Y, Rs, fun i => by
        obtain ⟨l, hl, hle⟩ := (hD i).1
        exact ⟨l, hl, by rw [CFSG.Quasithin.conjAut_eq_map]; exact hle⟩,
      hRs,
      fun i => by
        rw [← burnsideB2e_Jj_zero (Rs i)]
        exact ((hD i).2 (Rs i) (hRs' i)).1,
      fun i => ((hD i).2 (Rs i) (hRs' i)).2,
      hLY, hsum, burnsideB2e_offenders hV R (CFSG.Quasithin.twoResidual (⊤ : Subgroup G)) n Y hE⟩
  obtain ⟨b1, b2, b3, b4⟩ := hbg
  have e : CFSG.Quasithin.baum R ⊔ CFSG.Quasithin.twoResidual (⊤ : Subgroup G) =
      CFSG.Quasithin.twoResidual (⊤ : Subgroup G) ⊔ CFSG.Quasithin.baum R := sup_comm _ _
  rw [burnsideB2e_Jj_zero R, burnsideB2e_baumOf R, e]
  exact ⟨b1, b2, b3, b4⟩

@[expose] def B_2_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal]
    (R T : Subgroup G), IsSylowTwoOf T ⊤ → pCoreOf 2 (⊤ : Subgroup G) ≤ R → R ≤ T →
      ¬ Jj R 0 ≤ Subgroup.centralizer (V : Set G) →
      R ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (⊤ : Subgroup G) →
      ∀ Astar : Subgroup (MulAut (IntMod V hV)),
        IsFFStarOffender (autI hV R) Astar →
        (∀ B : Subgroup (MulAut (IntMod V hV)), IsFFStarOffender (autI hV R) B → B = Astar) →
        Astar = autI hV R ⊓ centSub (fixV Astar) →
          Astar = autI hV (Jj R 0) ∧ autI hV (Jj R 0) = autI hV (baumOf R)

theorem as_B_2_20 : B_2_20 := by
  intro G _ _ V hV _ R T _ hpc _ hJ _ Astar _ hu hAC
  have hVpc : V ≤ CFSG.pCore 2 G :=
    le_sSup ⟨inferInstance, burnsideB2c_isPGroup_of_isElemAbelian hV⟩
  rw [burnsideB2c_pCoreOf_top] at hpc
  have hVR : V ≤ R := hVpc.trans hpc
  have hRN : R ≤ Subgroup.normalizer (V : Set G) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm.le
  rw [burnsideB2c_Jj_zero R] at hJ
  have key := CFSG.Quasithin.B2_20 hV hVR hRN hJ hu hAC
  rw [burnsideB2c_Jj_zero R, burnsideB2c_baumOf R]
  exact key

@[expose] def B_2_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G) (hV : IsElemAbelian 2 V) [V.Normal],
    Subgroup.centralizer (V : Set G) = V →
      ∀ A ∈ Aj ⊤ 0, (∃ a ∈ A, V ⊓ Subgroup.centralizer (A : Set G) = V ⊓ Subgroup.centralizer ({a} : Set G)) →
        A ∈ Aj ⊤ 0 ∧ ∀ B ∈ Aj ⊤ 0, autI hV B = autI hV A → B = A

theorem as_B_2_21 : B_2_21 := by
  intro G _ _ V hV _ hC A hA hex
  obtain ⟨a, haA, ha⟩ := hex
  refine ⟨hA, fun B hB hAB => ?_⟩
  have hA' : CFSG.Quasithin.IsMaxElemAbelian ⊤ A := burnsideB2c_mem_Aj_zero_iff.1 hA
  have hB' : CFSG.Quasithin.IsMaxElemAbelian ⊤ B := burnsideB2c_mem_Aj_zero_iff.1 hB
  have hHN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm.le
  have hC' : (⊤ : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) = V := by
    rw [top_inf_eq]
    exact hC
  exact CFSG.Quasithin.B2_21 hV le_top hHN hC' hA' haA ha hB' hAB.symm

end CFSG.ASVolI
