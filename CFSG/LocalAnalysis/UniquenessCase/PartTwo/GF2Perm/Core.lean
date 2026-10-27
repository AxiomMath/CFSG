module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Witness
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.ClassicalInvolution.ModelFacts.ChevAutBasic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootQuotientClassesBasic
import CFSG.GroupTheory.CommuteOfSqEqOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def cubeCore (W : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ W ∧ x ^ 3 ∈ CFSG.Open.pCoreOf 2 W}

theorem cubeCore_map_mulAut {W : Subgroup G} (φ : MulAut G) (hW : W.map φ.toMonoidHom = W) :
    (cubeCore W).map φ.toMonoidHom = cubeCore W := by
  have hp : CFSG.Open.pCoreOf 2 W = (CFSG.Open.pCoreOf 2 W).map φ.toMonoidHom := by
    rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 φ W, hW]
  have hWsym : W.map φ.symm.toMonoidHom = W := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [Subgroup.map_map]
    rw [show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G from by ext z; simp,
      Subgroup.map_id, hW]
  have hpsym : (CFSG.Open.pCoreOf 2 W).map φ.symm.toMonoidHom = CFSG.Open.pCoreOf 2 W := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [Subgroup.map_map]
    rw [show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G from by ext z; simp,
      Subgroup.map_id]
    exact hp
  have hS : φ.toMonoidHom '' {x | x ∈ W ∧ x ^ 3 ∈ CFSG.Open.pCoreOf 2 W} =
      {x | x ∈ W ∧ x ^ 3 ∈ CFSG.Open.pCoreOf 2 W} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · exact hW ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hx.1
      · rw [← map_pow]
        exact hp ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hx.2
    · rintro ⟨hyW, hy3⟩
      refine ⟨φ.symm y, ⟨?_, ?_⟩, by simp⟩
      · rw [← hWsym]
        exact Subgroup.mem_map_of_mem φ.symm.toMonoidHom hyW
      · rw [← hpsym]
        change (φ.symm.toMonoidHom y) ^ 3 ∈
          Subgroup.map φ.symm.toMonoidHom (CFSG.Open.pCoreOf 2 W)
        simpa only [map_pow] using Subgroup.mem_map_of_mem φ.symm.toMonoidHom hy3
  rw [cubeCore, MonoidHom.map_closure, hS]

private theorem card_pCoreOf_three_of_card_six [Finite G] (L : Subgroup G)
    (h6 : Nat.card L = 6) : Nat.card (CFSG.Open.pCoreOf 3 L) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := L)
  have hPcard : Nat.card (P : Subgroup L) = 3 := by
    rw [Sylow.card_eq_multiplicity, h6]
    norm_num [Nat.factorization]
  have hidx : (P : Subgroup L).index = 2 := by
    have h := Subgroup.card_mul_index (P : Subgroup L)
    rw [hPcard, h6] at h
    omega
  have hPn : (P : Subgroup L).Normal := Subgroup.normal_of_index_eq_two hidx
  have hnorm : L ≤ Subgroup.normalizer ((P : Subgroup L).map L.subtype : Set G) := by
    have hpnorm : Subgroup.normalizer ((P : Subgroup L) : Set L) = ⊤ :=
      Subgroup.normalizer_eq_top (H := (P : Subgroup L))
    have h := Subgroup.le_normalizer_map (H := (P : Subgroup L)) (f := L.subtype)
    rw [hpnorm, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hPle : (P : Subgroup L).map L.subtype ≤ CFSG.Open.pCoreOf 3 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 (Subgroup.map_subtype_le _) hnorm
      (P.isPGroup'.map L.subtype)
  have h3le : 3 ≤ Nat.card (CFSG.Open.pCoreOf 3 L) := by
    calc 3 = Nat.card ((P : Subgroup L).map L.subtype) := by
          rw [Subgroup.card_map_of_injective L.subtype_injective, hPcard]
      _ ≤ Nat.card (CFSG.Open.pCoreOf 3 L) := Subgroup.card_le_of_le hPle
  have h6le : Nat.card (CFSG.Open.pCoreOf 3 L) ≤ 6 := by
    calc Nat.card (CFSG.Open.pCoreOf 3 L) ≤ Nat.card L :=
          Subgroup.card_le_of_le (CFSG.LieType.BorelTits.pCoreOf_le 3 L)
      _ = 6 := h6
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 L).exists_card_eq
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at hn
      omega
    · exact hpos
  have hnlt : n < 2 := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · exact hlt
    · exfalso
      have h9 : 9 ≤ 3 ^ n := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hge
      omega
  have hn1 : n = 1 := by omega
  rw [hn, hn1]
  norm_num

private theorem sq_mem_pCoreOf_three_of_card_six [Finite G] {L : Subgroup G}
    (h6 : Nat.card L = 6) : ∀ x ∈ L, x ^ 2 ∈ CFSG.Open.pCoreOf 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : Nat.card (CFSG.Open.pCoreOf 3 L) = 3 := card_pCoreOf_three_of_card_six L h6
  have hcard : Nat.card ((CFSG.Open.pCoreOf 3 L).subgroupOf L) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.LieType.BorelTits.pCoreOf_le 3 L)).toEquiv, hA3]
  have hidx : ((CFSG.Open.pCoreOf 3 L).subgroupOf L).index = 2 := by
    have h := Subgroup.card_mul_index ((CFSG.Open.pCoreOf 3 L).subgroupOf L)
    rw [hcard, h6] at h
    omega
  intro x hx
  have hx2 : (⟨x, hx⟩ : L) ^ 2 ∈ (CFSG.Open.pCoreOf 3 L).subgroupOf L :=
    Subgroup.sq_mem_of_index_two hidx ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp (by simpa using hx2)

private theorem le_normalizer_sup_of_normal_left {W V Q : Subgroup G} (hVW : V ≤ W)
    (hQW : Q ≤ W) (hWV : W ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) := hQW.trans hWV
  have hconj : ∀ w ∈ V, ∀ n ∈ (V ⊔ Q : Subgroup G), w * n * w⁻¹ ∈ V ⊔ Q := by
    intro w hw n hn
    have hn' : n ∈ ((V ⊔ Q : Subgroup G) : Set G) := hn
    rw [Subgroup.coe_mul_of_right_le_normalizer_left V Q hQV] at hn'
    obtain ⟨a, ha, b, hb, rfl⟩ := hn'
    change w * (a * b) * w⁻¹ ∈ ((V ⊔ Q : Subgroup G) : Set G)
    have hwa : w * a * w⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hWV (hVW hw)) a).mp ha
    have hwb : w * b * w⁻¹ ∈ (V ⊔ Q : Subgroup G) := by
      have hconjb : b * w⁻¹ * b⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hWV (hQW hb)) w⁻¹).mp (Subgroup.inv_mem _ hw)
      rw [show w * b * w⁻¹ = (w * (b * w⁻¹ * b⁻¹)) * b by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _ hw hconjb))
        (Subgroup.mem_sup_right hb)
    rw [show w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwa) hwb
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact hconj w hw n
  · intro hn
    have h := hconj w⁻¹ (Subgroup.inv_mem _ hw) (w * n * w⁻¹) hn
    rw [inv_inv] at h
    rwa [show w⁻¹ * (w * n * w⁻¹) * w = n by group] at h

private theorem mem_normalizer_closure_of_commutes {T Q : Subgroup G} {ι : Type*}
    {L A : ι → Subgroup G} (hQ : Q = Subgroup.closure ((T : Set G) ∪ ⋃ i, (A i : Set G)))
    (hTQ : T ≤ Q) (hAQ : ∀ i, A i ≤ Q)
    (hTL : ∀ i, ∀ x ∈ T, ∀ y ∈ L i, x * y = y * x)
    (hLL : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hAL : ∀ i, A i ≤ L i)
    (hAnorm : ∀ i, L i ≤ Subgroup.normalizer (A i : Set G))
    (j : ι) {l : G} (hl : l ∈ L j) : l ∈ Subgroup.normalizer (Q : Set G) := by
  have hconj : ∀ l ∈ L j, ∀ y ∈ Q, l * y * l⁻¹ ∈ Q := by
    intro l hl y hy
    rw [hQ] at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hxT | hxA
        · have hcomm : l * x = x * l := (hTL j x hxT l hl).symm
          rw [show l * x * l⁻¹ = x by rw [hcomm]; group]
          exact hTQ hxT
        · obtain ⟨k, hxA⟩ := Set.mem_iUnion.mp hxA
          by_cases hkj : k = j
          · subst hkj
            exact hAQ k ((Subgroup.mem_normalizer_iff.mp (hAnorm k hl) x).mp hxA)
          · have hcomm : x * l = l * x := hLL k j hkj x (hAL k hxA) l hl
            rw [show l * x * l⁻¹ = x by rw [← hcomm]; group]
            exact hAQ k hxA
    | one => simp
    | mul a b ha hb iha ihb =>
        rw [show l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) by group]
        exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
        rw [show l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ iha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hconj l hl y
  · intro hy
    have h := hconj l⁻¹ (Subgroup.inv_mem _ hl) (l * y * l⁻¹) hy
    rw [inv_inv] at h
    rwa [show l⁻¹ * (l * y * l⁻¹) * l = y by group] at h

private theorem le_normalizer_sup_of_generators {W V T Q : Subgroup G} {ι : Type*}
    {L : ι → Subgroup G} (hW : W = V ⊔ T ⊔ ⨆ i, L i)
    (hVW : V ≤ W) (hQW : Q ≤ W) (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hTQ : T ≤ Q) (hQc : IsMulCommutative Q)
    (hLQ : ∀ i, L i ≤ Subgroup.normalizer (Q : Set G)) :
    W ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
  have hLW : ∀ i, L i ≤ W := by
    intro i
    rw [hW]
    exact le_sup_of_le_right (le_iSup_of_le i le_rfl)
  have hVV : V ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) :=
    le_normalizer_sup_of_normal_left hVW hQW hWV
  have hQcen : Q ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : Q) ⟨y, hy⟩)).symm
  have hQQ : Q ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
    have h1 : Q ≤ Subgroup.normalizer (V : Set G) := hQW.trans hWV
    have h2 : Q ≤ Subgroup.normalizer (Q : Set G) :=
      hQcen.trans (Subgroup.centralizer_le_normalizer _)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup V Q ⟨h1 hx, h2 hx⟩
  have hLLQ : ∀ i, L i ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
    intro i
    have h1 : L i ≤ Subgroup.normalizer (V : Set G) := (hLW i).trans hWV
    have h2 : L i ≤ Subgroup.normalizer (Q : Set G) := hLQ i
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup V Q ⟨h1 hx, h2 hx⟩
  rw [hW]
  exact sup_le (sup_le hVV (hTQ.trans hQQ)) (iSup_le fun i => hLLQ i)

private theorem pairwise_commute_iUnion_of_commute {H : Type*} [Group H] {ι : Type*}
    {M : ι → Subgroup H} (hM2 : ∀ i, ∀ z ∈ M i, z ^ 2 = 1)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ M i, ∀ b ∈ M j, Commute a b) :
    (⋃ i, (M i : Set H)).Pairwise Commute := by
  rintro a ha b hb hab
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  by_cases hij : i = j
  · subst hij
    exact CFSG.commute_of_sq_eq_one (hM2 i a hi) (hM2 i b hj)
      (hM2 i (a * b) (Subgroup.mul_mem _ hi hj))
  · exact hcomm i j hij a hi b hj

private theorem commute_of_mem_iUnion_of_pairwise {H : Type*} [Group H] {ι : Type*}
    {M : ι → Subgroup H} (hScomm : (⋃ i, (M i : Set H)).Pairwise Commute)
    {i j : ι} {a b : H} (ha : a ∈ M i) (hb : b ∈ M j) : Commute a b := by
  by_cases hab : a = b
  · subst hab
    exact Commute.refl a
  · exact hScomm (Set.mem_iUnion.mpr ⟨i, ha⟩) (Set.mem_iUnion.mpr ⟨j, hb⟩) hab

private theorem pow_two_mem_sup_of_sq_mem [Finite G] {W V T Q : Subgroup G} {ι : Type*}
    [Finite ι] {L : ι → Subgroup G} (hW : W = V ⊔ T ⊔ ⨆ i, L i)
    (hVW : V ≤ W) (hQW : Q ≤ W) (hTQ : T ≤ Q)
    (hNnorm : W ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G))
    (hLsq : ∀ i, ∀ x ∈ L i, x ^ 2 ∈ Q)
    (hLcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) :
    ∀ x ∈ W, x ^ 2 ∈ V ⊔ Q := by
  have hLW : ∀ i, L i ≤ W := by
    intro i
    rw [hW]
    exact le_sup_of_le_right (le_iSup_of_le i le_rfl)
  have hNle : V ⊔ Q ≤ W := sup_le hVW hQW
  let N' : Subgroup W := (V ⊔ Q).subgroupOf W
  have hN'normal : N'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hNnorm
  let π : W →* W ⧸ N' := QuotientGroup.mk' N'
  let Lw : ι → Subgroup W := fun i => (L i).subgroupOf W
  let M : ι → Subgroup (W ⧸ N') := fun i => (Lw i).map π
  have hWN : W = (V ⊔ Q) ⊔ ⨆ i, L i := by
    apply le_antisymm
    · rw [hW]
      exact sup_le (sup_le (le_sup_of_le_left le_sup_left)
        (hTQ.trans (le_sup_of_le_left le_sup_right))) le_sup_right
    · exact sup_le hNle (iSup_le fun i => hLW i)
  have hWw : (⊤ : Subgroup W) = N' ⊔ ⨆ i, Lw i := by
    have h1 : W.subgroupOf W = ((V ⊔ Q) ⊔ ⨆ i, L i).subgroupOf W := by rw [hWN]
    rw [← Subgroup.subgroupOf_self W, h1, Subgroup.subgroupOf_sup hNle (iSup_le hLW),
      CFSG.subgroupOf_iSup L hLW]
  have htop : (⊤ : Subgroup (W ⧸ N')) = ⨆ i, M i := by
    have h := congrArg (Subgroup.map π) hWw
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N'),
      Subgroup.map_sup, Subgroup.map_iSup, QuotientGroup.map_mk'_self, bot_sup_eq] at h
  have hM2 : ∀ i, ∀ z ∈ M i, z ^ 2 = 1 := by
    intro i z hz
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
    have hsq : (l : G) ^ 2 ∈ V ⊔ Q :=
      Subgroup.mem_sup_right (hLsq i (l : G) (Subgroup.mem_subgroupOf.mp hl))
    have hmem : (l : W) ^ 2 ∈ N' := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hsq
    have hπ : π (l ^ 2) = 1 := (QuotientGroup.eq_one_iff (l ^ 2)).mpr hmem
    rw [map_pow] at hπ
    exact hπ
  have hScomm : (⋃ i, (M i : Set (W ⧸ N'))).Pairwise Commute := by
    refine pairwise_commute_iUnion_of_commute hM2 ?_
    rintro i j hij x hx y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hy
    have hlL : (l : G) ∈ L i := Subgroup.mem_subgroupOf.mp hl
    have hl'L : (l' : G) ∈ L j := Subgroup.mem_subgroupOf.mp hl'
    have hll : (l : W) * l' = l' * l := by
      apply Subtype.ext
      exact hLcomm i j hij (l : G) hlL (l' : G) hl'L
    show π l * π l' = π l' * π l
    rw [← map_mul, ← map_mul, hll]
  have hquot2 : ∀ g : W ⧸ N', g ^ 2 = 1 := fun g =>
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.pow_eq_one_of_mem_iSup
      (fun i j a ha b hb => commute_of_mem_iUnion_of_pairwise hScomm ha hb) hM2 g
      (by rw [← htop]; exact Subgroup.mem_top g)
  intro x hx
  have h2 : (π ⟨x, hx⟩) ^ 2 = 1 := hquot2 _
  have hmem : (⟨x, hx⟩ : W) ^ 2 ∈ N' := (QuotientGroup.eq_one_iff _).mp h2
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa using this

private theorem cubeCore_le_pCoreOf_sup [Finite G] {W V T Q : Subgroup G} {ι : Type*}
    [Finite ι] {L : ι → Subgroup G} (hW : W = V ⊔ T ⊔ ⨆ i, L i)
    (hVW : V ≤ W) (hQW : Q ≤ W) (hTQ : T ≤ Q)
    (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hNnorm : W ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G))
    (hV2 : IsPGroup 2 V)
    (hLsq : ∀ i, ∀ x ∈ L i, x ^ 2 ∈ Q)
    (hLcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) :
    cubeCore W ≤ CFSG.Open.pCoreOf 2 W ⊔ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := pow_two_mem_sup_of_sq_mem hW hVW hQW hTQ hNnorm hLsq hLcomm
  have hVle : V ≤ CFSG.Open.pCoreOf 2 W :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVW hWV hV2
  have hNle : V ⊔ Q ≤ CFSG.Open.pCoreOf 2 W ⊔ Q :=
    sup_le (hVle.trans le_sup_left) le_sup_right
  refine (Subgroup.closure_le (CFSG.Open.pCoreOf 2 W ⊔ Q)).mpr ?_
  rintro x ⟨hxW, hx3⟩
  have hx2 : x ^ 2 ∈ V ⊔ Q := hsq x hxW
  have hx : x = (x ^ 3)⁻¹ * (x ^ 2) ^ 2 := by group
  rw [hx]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hx3))
    (hNle (Subgroup.pow_mem _ hx2 2))

private theorem pCoreOf_two_le_of_sylow_of_le [Finite G] {U W : Subgroup G} (hUW : U ≤ W)
    (hU2 : IsPGroup 2 U) (hUodd : ¬ 2 ∣ (U.subgroupOf W).index) :
    CFSG.Open.pCoreOf 2 W ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2' : IsPGroup 2 (U.subgroupOf W) :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUW).symm
  let P : Sylow 2 W := hU2'.toSylow hUodd
  have hPcoe : (P : Subgroup W) = U.subgroupOf W := IsPGroup.toSylow_coe hU2' hUodd
  have hnormal : (CFSG.Open.pCore 2 W).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hp : IsPGroup 2 (CFSG.Open.pCore 2 W) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hle : CFSG.Open.pCore 2 W ≤ (P : Subgroup W) := IsPGroup.le_sylow_of_normal hp P
  have hm : CFSG.Open.pCoreOf 2 W ≤ (P : Subgroup W).map W.subtype :=
    Subgroup.map_mono hle
  rw [hPcoe, Subgroup.map_subgroupOf_eq_of_le hUW] at hm
  exact hm

private theorem pow_three_mem_of_le_sup [Finite G] {W R Q X : Subgroup G} (hRW : R ≤ W)
    (hQW : Q ≤ W) (hWnorm : W ≤ Subgroup.normalizer (R : Set G))
    (hQ3 : ∀ x ∈ Q, x ^ 3 = 1) (hXW : X ≤ W) (hX : X ≤ R ⊔ Q) :
    ∀ x ∈ X, x ^ 3 ∈ R := by
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) := hQW.trans hWnorm
  let R' : Subgroup W := R.subgroupOf W
  have hR'normal : R'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRW).mpr hWnorm
  let π : W →* W ⧸ R' := QuotientGroup.mk' R'
  intro x hx
  have hxW : x ∈ W := hXW hx
  have hxRQ : x ∈ ((R ⊔ Q : Subgroup G) : Set G) := hX hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R Q hQR] at hxRQ
  obtain ⟨r, hr, q, hq, hxrq⟩ := hxRQ
  have hr1 : π ⟨r, hRW hr⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hr)
  have hxq : π ⟨x, hxW⟩ = π ⟨q, hQW hq⟩ := by
    rw [show (⟨x, hxW⟩ : W) = ⟨r, hRW hr⟩ * ⟨q, hQW hq⟩ from Subtype.ext hxrq.symm,
      map_mul, hr1, one_mul]
  have hq3 : (⟨q, hQW hq⟩ : W) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hQ3 q hq
  have hmem : (⟨x, hxW⟩ : W) ^ 3 ∈ R' := by
    rw [← QuotientGroup.eq_one_iff]
    change π ((⟨x, hxW⟩ : W) ^ 3) = 1
    rw [map_pow, hxq, ← map_pow, hq3, map_one]
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa using this

private theorem commutator_mem_pCoreOf_of_le_sup [Finite G] {W R Q X : Subgroup G} (hRW : R ≤ W)
    (hQW : Q ≤ W) (hWnorm : W ≤ Subgroup.normalizer (R : Set G))
    (hQc : IsMulCommutative Q) (hXW : X ≤ W) (hX : X ≤ R ⊔ Q) :
    ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ R := by
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) := hQW.trans hWnorm
  let R' : Subgroup W := R.subgroupOf W
  have hR'normal : R'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRW).mpr hWnorm
  let π : W →* W ⧸ R' := QuotientGroup.mk' R'
  have hcoe : ∀ z ∈ X, ∃ r ∈ R, ∃ q ∈ Q, r * q = z := by
    intro z hz
    have hzRQ : z ∈ ((R ⊔ Q : Subgroup G) : Set G) := hX hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R Q hQR] at hzRQ
    exact hzRQ
  intro x hx y hy
  have hxW : x ∈ W := hXW hx
  have hyW : y ∈ W := hXW hy
  obtain ⟨r, hr, q, hq, hxrq⟩ := hcoe x hx
  obtain ⟨r', hr', q', hq', hyrq⟩ := hcoe y hy
  have hr1 : π ⟨r, hRW hr⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hr)
  have hr'1 : π ⟨r', hRW hr'⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hr')
  have hxq : π ⟨x, hxW⟩ = π ⟨q, hQW hq⟩ := by
    rw [show (⟨x, hxW⟩ : W) = ⟨r, hRW hr⟩ * ⟨q, hQW hq⟩ from Subtype.ext hxrq.symm,
      map_mul, hr1, one_mul]
  have hyq : π ⟨y, hyW⟩ = π ⟨q', hQW hq'⟩ := by
    rw [show (⟨y, hyW⟩ : W) = ⟨r', hRW hr'⟩ * ⟨q', hQW hq'⟩ from Subtype.ext hyrq.symm,
      map_mul, hr'1, one_mul]
  have hqq'_G : q * q' = q' * q :=
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨q, hq⟩ : Q) ⟨q', hq'⟩)
  have hqq' : π ⟨q, hQW hq⟩ * π ⟨q', hQW hq'⟩ = π ⟨q', hQW hq'⟩ * π ⟨q, hQW hq⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hqq'_G)
  have hmem : (⟨x, hxW⟩ * ⟨y, hyW⟩ * ⟨x, hxW⟩⁻¹ * ⟨y, hyW⟩⁻¹) ∈ R' := by
    rw [← QuotientGroup.eq_one_iff]
    change π (⟨x, hxW⟩ * ⟨y, hyW⟩ * ⟨x, hxW⟩⁻¹ * ⟨y, hyW⟩⁻¹) = 1
    simp only [map_mul, map_inv, hxq, hyq, hqq']
    group
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa using this

private theorem nine_mul_card_le_of_sup_le [Finite G] {E R X : Subgroup G}
    (hR2 : IsPGroup 2 R) (hE9 : Nat.card E = 9)
    (hER : E ≤ Subgroup.normalizer (R : Set G)) (hEX : E ≤ X) (hRX : R ≤ X) :
    9 * Nat.card R ≤ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hR2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card E) (Nat.card R) := by
    rw [hE9, hn]
    exact Nat.Coprime.pow (k := 3) (l := 2) 2 n (by norm_num)
  have hdisj : E ⊓ R = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hcard := CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses.card_sup_mul_card_inf
    (A := E) (B := R) hER
  rw [hdisj, Subgroup.card_bot, hE9, mul_one] at hcard
  have hle : E ⊔ R ≤ X := sup_le hEX hRX
  have := Subgroup.card_le_of_le hle
  omega

private theorem pairwise_commute_torus_pCoreOf [Finite G] {T : Subgroup G} {ι : Type*}
    {L : ι → Subgroup G} (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hL6 : ∀ i, Nat.card (L i) = 6)
    (hLL : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hTL : ∀ i, ∀ x ∈ T, ∀ y ∈ L i, x * y = y * x) :
    ((T : Set G) ∪ ⋃ i, ((CFSG.Open.pCoreOf 3 (L i) : Subgroup G) : Set G)).Pairwise
      Commute := by
  rintro x (hxT | hxA) y (hyT | hyA) hxy
  · exact hTc x hxT y hyT
  · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hyA
    exact hTL j x hxT y (CFSG.LieType.BorelTits.pCoreOf_le 3 (L j) hxj)
  · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxA
    exact (hTL j y hyT x (CFSG.LieType.BorelTits.pCoreOf_le 3 (L j) hxj)).symm
  · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxA
    obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hyA
    by_cases hjk : j = k
    · subst hjk
      have hcard : Nat.card (CFSG.Open.pCoreOf 3 (L j)) = 3 :=
        card_pCoreOf_three_of_card_six (L j) (hL6 j)
      have : IsMulCommutative (CFSG.Open.pCoreOf 3 (L j)) :=
        (isCyclic_of_prime_card (α := CFSG.Open.pCoreOf 3 (L j)) (p := 3)
          hcard).isMulCommutative
      exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨x, hxj⟩ : CFSG.Open.pCoreOf 3 (L j)) ⟨y, hyk⟩)
    · exact hLL j k hjk x (CFSG.LieType.BorelTits.pCoreOf_le 3 (L j) hxj) y
        (CFSG.LieType.BorelTits.pCoreOf_le 3 (L k) hyk)

private theorem pow_three_mem_closure_torus_pCoreOf [Finite G] {T : Subgroup G} {ι : Type*}
    {L : ι → Subgroup G} (hT3 : ∀ x ∈ T, x ^ 3 = 1) (hL6 : ∀ i, Nat.card (L i) = 6)
    (hcomm : ((T : Set G) ∪ ⋃ i,
      ((CFSG.Open.pCoreOf 3 (L i) : Subgroup G) : Set G)).Pairwise Commute) :
    ∀ x ∈ Subgroup.closure ((T : Set G) ∪
      ⋃ i, ((CFSG.Open.pCoreOf 3 (L i) : Subgroup G) : Set G)), x ^ 3 = 1 := by
  intro x hx
  refine CFSG.AGLEmbeddingD2.AltFiveRankTools.pow_eq_one_of_mem_closure_of_pairwise_commute
    hcomm ?_ hx
  rintro x (hxT | hxU)
  · exact hT3 x hxT
  · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
    have hcard : Nat.card (CFSG.Open.pCoreOf 3 (L j)) = 3 :=
      card_pCoreOf_three_of_card_six (L j) (hL6 j)
    exact (orderOf_dvd_iff_pow_eq_one).mp (by
      have h := Subgroup.orderOf_dvd_natCard (CFSG.Open.pCoreOf 3 (L j)) hxj
      rwa [hcard] at h)

private theorem exists_Q_setup [Finite G] {W V T : Subgroup G} {ι : Type*}
    {L : ι → Subgroup G} (hW : W = V ⊔ T ⊔ ⨆ i, L i)
    (hVW : V ≤ W) (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT3 : ∀ x ∈ T, x ^ 3 = 1)
    (hL6 : ∀ i, Nat.card (L i) = 6)
    (hLL : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hTL : ∀ i, ∀ x ∈ T, ∀ y ∈ L i, x * y = y * x) :
    ∃ Q : Subgroup G, T ≤ Q ∧ Q ≤ W ∧ IsMulCommutative Q ∧ (∀ x ∈ Q, x ^ 3 = 1) ∧
      (∀ i, L i ≤ Subgroup.normalizer (Q : Set G)) ∧
      (∀ i, ∀ x ∈ L i, x ^ 2 ∈ Q) ∧
      W ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
  let A : ι → Subgroup G := fun i => CFSG.Open.pCoreOf 3 (L i)
  let Q : Subgroup G := Subgroup.closure ((T : Set G) ∪ ⋃ i, (A i : Set G))
  have hQdef : Q = Subgroup.closure ((T : Set G) ∪ ⋃ i, (A i : Set G)) := rfl
  have hAL : ∀ i, A i ≤ L i := fun i => CFSG.LieType.BorelTits.pCoreOf_le 3 (L i)
  have hcomm : ((T : Set G) ∪ ⋃ i, (A i : Set G)).Pairwise Commute :=
    pairwise_commute_torus_pCoreOf hTc hL6 hLL hTL
  have hQc : IsMulCommutative Q := Subgroup.isMulCommutative_closure hcomm
  have hQ3 : ∀ x ∈ Q, x ^ 3 = 1 := pow_three_mem_closure_torus_pCoreOf hT3 hL6 hcomm
  have hLW : ∀ i, L i ≤ W := by
    intro i
    rw [hW]
    exact le_sup_of_le_right (le_iSup_of_le i le_rfl)
  have hTQ : T ≤ Q := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hA_le_Q : ∀ i, A i ≤ Q := fun i x hx =>
    Subgroup.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
  have hQ_le_W : Q ≤ W := by
    rw [Subgroup.closure_le]
    rintro x (hxT | hxU)
    · rw [hW]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hxT)
    · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
      exact hLW j (hAL j hxj)
  have hLQ : ∀ i, L i ≤ Subgroup.normalizer (Q : Set G) := fun i l hl =>
    mem_normalizer_closure_of_commutes hQdef hTQ hA_le_Q hTL hLL hAL
      (fun i => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 (L i)) i hl
  have hNnorm : W ≤ Subgroup.normalizer ((V ⊔ Q : Subgroup G) : Set G) :=
    le_normalizer_sup_of_generators hW hVW hQ_le_W hWV hTQ hQc hLQ
  have hLsq : ∀ i, ∀ x ∈ L i, x ^ 2 ∈ Q := fun i x hx =>
    hA_le_Q i (sq_mem_pCoreOf_three_of_card_six (hL6 i) x hx)
  exact ⟨Q, hTQ, hQ_le_W, hQc, hQ3, hLQ, hLsq, hNnorm⟩

theorem permWitnessAt_of_generators [Finite G] {ι : Type*} [Finite ι] (U : Sylow 2 G)
    {W V T : Subgroup G} {J : Set ι} {L : ι → Subgroup G} (hUW : (U : Subgroup G) ≤ W)
    (hfix : ∀ φ : MulAut G, (U : Subgroup G).map φ.toMonoidHom = U → W.map φ.toMonoidHom = W)
    (hW : W = V ⊔ T ⊔ ⨆ j ∈ J, L j) (hV2 : IsPGroup 2 V)
    (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hT3 : ∀ x ∈ T, x ^ 3 = 1)
    (hL6 : ∀ j ∈ J, Nat.card (L j) = 6)
    (hLL : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x ∈ L j, ∀ y ∈ L k, x * y = y * x)
    (hTL : ∀ j ∈ J, ∀ x ∈ T, ∀ y ∈ L j, x * y = y * x)
    {E : Subgroup G} (hEW : E ≤ W) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9) :
    PermWitnessAt G U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let J' := {j : ι // j ∈ J}
  let L' : J' → Subgroup G := fun j => L j.1
  have hW' : W = V ⊔ T ⊔ ⨆ j : J', L' j := by
    simpa [L', J', iSup_subtype] using hW
  have hL6' : ∀ j : J', Nat.card (L' j) = 6 := fun j => hL6 j.1 j.2
  have hLL' : ∀ j k : J', j ≠ k → ∀ x ∈ L' j, ∀ y ∈ L' k, x * y = y * x := by
    intro j k hjk x hx y hy
    exact hLL j.1 j.2 k.1 k.2 (fun h => hjk (Subtype.ext h)) x hx y hy
  have hTL' : ∀ j : J', ∀ x ∈ T, ∀ y ∈ L' j, x * y = y * x := fun j => hTL j.1 j.2
  have hVW : V ≤ W := by
    rw [hW']
    exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  obtain ⟨Q, hTQ, hQ_le_W, hQc, hQ3, _, hLsq, hNnorm⟩ :=
    exists_Q_setup hW' hVW hWV hTc hT3 hL6' hLL' hTL'
  let R : Subgroup G := CFSG.Open.pCoreOf 2 W
  have hRW : R ≤ W := CFSG.LieType.BorelTits.pCoreOf_le 2 W
  have hRnorm : W ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 W
  have hXW : cubeCore W ≤ W := by
    rw [cubeCore, Subgroup.closure_le]
    rintro x ⟨hxW, -⟩
    exact hxW
  have hX_le : cubeCore W ≤ R ⊔ Q := by
    simpa [R] using cubeCore_le_pCoreOf_sup hW' hVW hQ_le_W hTQ hWV hNnorm hV2 hLsq hLL'
  have hRU : R ≤ U := by
    refine pCoreOf_two_le_of_sylow_of_le hUW U.isPGroup' ?_
    intro h2
    exact U.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le hUW))
  have hRX : R ≤ cubeCore W := by
    intro r hr
    exact Subgroup.subset_closure ⟨hRW hr, Subgroup.pow_mem R hr 3⟩
  have hXR : cubeCore W ≤ Subgroup.normalizer (R : Set G) := hXW.trans hRnorm
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W
  have hcube : ∀ x ∈ cubeCore W, x ^ 3 ∈ R :=
    pow_three_mem_of_le_sup hRW hQ_le_W hRnorm hQ3 hXW hX_le
  have hcomm : ∀ x ∈ cubeCore W, ∀ y ∈ cubeCore W, x * y * x⁻¹ * y⁻¹ ∈ R :=
    commutator_mem_pCoreOf_of_le_sup hRW hQ_le_W hRnorm hQc hXW hX_le
  have hE_le_X : E ≤ cubeCore W := by
    intro e he
    exact Subgroup.subset_closure ⟨hEW he, by rw [hE3 e he]; exact Subgroup.one_mem R⟩
  have hcard : 9 * Nat.card R ≤ Nat.card (cubeCore W) :=
    nine_mul_card_le_of_sup_le hR2 hE9 (hEW.trans hRnorm) hE_le_X hRX
  refine ⟨cubeCore W, R, ?_, hRU, hRX, hXR, hR2, hcube, hcomm, hcard⟩
  intro φ hφ
  exact cubeCore_map_mulAut φ (hfix φ hφ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
