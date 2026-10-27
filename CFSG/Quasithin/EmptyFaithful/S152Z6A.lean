module

public import CFSG.Quasithin.EmptyFaithful.S152FinChief
public import CFSG.Quasithin.EmptyFaithful.S152FinRank
public import CFSG.Quasithin.EmptyFaithful.S152NBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S152Z6

variable {G : Type} [Group G] [Finite G] {H T V A : Subgroup G}

theorem isMinOffender_cjSub' (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V) {h : G} (hh : h ∈ H)
    (hAT : IsMaxElemAbelian T (cjSub h A)) : IsMinOffender T H V (cjSub h A) := by
  have hQT := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hAδ := S152N.cjSub_mem_deltaSet hh hA
  refine ⟨hAT, fun hmax => hAδ.2.1 hmax.1, fun A'' hA'' hA''n => ?_, hAδ.2.2.2⟩
  have hA''nle : ¬ A'' ≤ pCoreOf 2 H := fun hle =>
    hA''n ⟨hle, hA''.2.1, fun B hBQ hB => hA''.2.2 B (hBQ.trans hQT) hB⟩
  exact hAδ.2.2.1 A'' (isMaxElemAbelian_of_isSylowTwoOf hT hA'') hA''nle

theorem exists_conj_isMinOffender' (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V) :
    ∃ h ∈ H, IsMinOffender T H V (cjSub h A) := by
  obtain ⟨h, hh, hAT⟩ := exists_conj_isMaxElemAbelian hT hA.1
  exact ⟨h, hh, isMinOffender_cjSub' hT hA hh hAT⟩

theorem delta_fixed_eq' {M : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hc : Concl319 T M V H True) :
    conjClosure V H ⊓ Subgroup.centralizer (A : Set G) =
      conjClosure V H ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
  obtain ⟨h, hh, hmin⟩ := exists_conj_isMinOffender' hT hA
  have key : conjClosure V H ⊓ Subgroup.centralizer (cjSub h A : Set G) =
      conjClosure V H ⊓ Subgroup.centralizer ((cjSub h A ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
    hc.fixed_eq _ hmin
  have h1 := congrArg (cjSub h⁻¹) key
  rw [B2F.cjSub_inf, B2F.cjSub_inf, B2F.cjSub_centralizer, B2F.cjSub_centralizer,
    S152N.cjSub_conjClosure (H.inv_mem hh), cjSub_inv_cjSub, B2F.cjSub_inf, cjSub_inv_cjSub,
    S152N.cjSub_pCoreOf (H.inv_mem hh)] at h1
  exact h1

theorem delta_count_one' {M : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hc : Concl319 T M V H True) :
    Nat.card A ^ 2 * Nat.card ↥(conjClosure V H ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 * Nat.card (conjClosure V H) := by
  obtain ⟨h, hh, hmin⟩ := exists_conj_isMinOffender' hT hA
  have key := hc.count_one _ hmin
  have e1 : conjClosure V H ⊓ Subgroup.centralizer (cjSub h A : Set G) =
      cjSub h (conjClosure V H ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [B2F.cjSub_inf, B2F.cjSub_centralizer, S152N.cjSub_conjClosure hh]
  have e2 : cjSub h A ⊓ pCoreOf 2 H = cjSub h (A ⊓ pCoreOf 2 H) := by
    rw [B2F.cjSub_inf, S152N.cjSub_pCoreOf hh]
  rw [e1, e2, card_cjSub, card_cjSub, card_cjSub] at key
  exact key

theorem delta_count_two' {M : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hc : Concl319 T M V H True) :
    Nat.card (conjClosure V H) *
        Nat.card ↥(A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G)) ^ 2 =
      Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 *
        Nat.card ↥(conjClosure V H ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨h, hh, hmin⟩ := exists_conj_isMinOffender' hT hA
  have key := hc.count_two _ hmin
  have e1 : cjSub h A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G) =
      cjSub h (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G)) := by
    rw [B2F.cjSub_inf, B2F.cjSub_inf, S152N.cjSub_pCoreOf hh, B2F.cjSub_centralizer,
      S152N.cjSub_conjClosure hh]
  have e2 : cjSub h A ⊓ pCoreOf 2 H = cjSub h (A ⊓ pCoreOf 2 H) := by
    rw [B2F.cjSub_inf, S152N.cjSub_pCoreOf hh]
  have e3 : conjClosure V H ⊓ Subgroup.centralizer (cjSub h A : Set G) =
      cjSub h (conjClosure V H ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [B2F.cjSub_inf, B2F.cjSub_centralizer, S152N.cjSub_conjClosure hh]
  rw [e1, e2, e3, card_cjSub, card_cjSub, card_cjSub] at key
  exact key

theorem delta_count_three' {M : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hc : Concl319 T M V H True) {h : G} (hh : h ∈ H)
    (hne : ⁅A ⊓ pCoreOf 2 H, conjSubgroup V h⁆ ≠ ⊥) :
    Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 *
        Nat.card ↥(conjSubgroup V h ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) =
      Nat.card ↥(A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) ^ 2 *
        Nat.card (conjSubgroup V h) := by
  obtain ⟨g, hg, hmin⟩ := exists_conj_isMinOffender' hT hA
  have hk : h * g⁻¹ ∈ H := H.mul_mem hh (H.inv_mem hg)
  have hV : ∀ k : G, conjSubgroup V k = cjSub k⁻¹ V := fun k => rfl
  have hVk : conjSubgroup V (h * g⁻¹) = cjSub g (conjSubgroup V h) := by
    rw [hV, hV, ← B2F.cjSub_mul]
    congr 1
    group
  have hB : cjSub g A ⊓ pCoreOf 2 H = cjSub g (A ⊓ pCoreOf 2 H) := by
    rw [B2F.cjSub_inf, S152N.cjSub_pCoreOf hg]
  have hne' : ⁅cjSub g A ⊓ pCoreOf 2 H, conjSubgroup V (h * g⁻¹)⁆ ≠ ⊥ := by
    rw [hB, hVk, ← S152N.cjSub_commutator]
    intro hbot
    exact hne ((S152N.cjSub_eq_bot_iff g).mp hbot)
  have key : Nat.card ↥(cjSub g A ⊓ pCoreOf 2 H) ^ 2 *
        Nat.card ↥(conjSubgroup V (h * g⁻¹) ⊓
          Subgroup.centralizer ((cjSub g A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) =
      Nat.card ↥(cjSub g A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V (h * g⁻¹) : Set G)) ^ 2 *
        Nat.card ↥(conjSubgroup V (h * g⁻¹)) :=
    hc.count_three _ hmin (h * g⁻¹) hk hne'
  have e1 : conjSubgroup V (h * g⁻¹) ⊓
        Subgroup.centralizer ((cjSub g A ⊓ pCoreOf 2 H : Subgroup G) : Set G) =
      cjSub g (conjSubgroup V h ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) := by
    rw [hB, hVk, B2F.cjSub_inf g (conjSubgroup V h), B2F.cjSub_centralizer g]
  have e2 : cjSub g A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V (h * g⁻¹) : Set G) =
      cjSub g (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) := by
    rw [hB, hVk, B2F.cjSub_inf g (A ⊓ pCoreOf 2 H), B2F.cjSub_centralizer g]
  rw [e1, e2, hB, hVk, card_cjSub, card_cjSub, card_cjSub, card_cjSub] at key
  exact key

theorem delta_cA_le' {M : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ∈ deltaSet H V)
    (hc : Concl319 T M V H True) :
    A ⊓ Subgroup.centralizer (conjClosure V H : Set G) ≤ pCoreOf 2 H := by
  obtain ⟨g, hg, hmin⟩ := exists_conj_isMinOffender' hT hA
  obtain ⟨L, N, hstep, hnc, hNU⟩ := S152Fin.exists_noncentral_of_series hc.chief (n := 2) (by norm_num)
  have h4 := (hc.count_four _ hmin L N hstep hnc).1
  intro x hx
  have hy : g * x * g⁻¹ ∈ cjSub g A := by
    rw [mem_cjSub]
    simpa [mul_assoc] using hx.1
  have hyC : g * x * g⁻¹ ∈ Subgroup.centralizer (conjClosure V H : Set G) := by
    have : g * x * g⁻¹ ∈ cjSub g (Subgroup.centralizer (conjClosure V H : Set G)) := by
      rw [mem_cjSub]
      simpa [mul_assoc] using hx.2
    rwa [B2F.cjSub_centralizer, S152N.cjSub_conjClosure hg] at this
  have hyc : g * x * g⁻¹ ∈ cSecIn (cjSub g A) L N := by
    refine Subgroup.subset_closure ⟨hy, fun z hz => ?_⟩
    have hzU : z ∈ conjClosure V H := hstep.1.1 hz
    have h1 : g * x * g⁻¹ * z * (g * x * g⁻¹)⁻¹ * z⁻¹ = 1 := by
      rw [(Subgroup.mem_centralizer_iff.1 hyC z hzU).symm]
      group
    rw [h1]
    exact L.one_mem
  rw [h4] at hyc
  have hyQ : g * x * g⁻¹ ∈ pCoreOf 2 H := hyc.2
  have hxQ : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (H.inv_mem hg)) _).1 hyQ
  simpa [mul_assoc] using hxQ

theorem relIndex_delta_two_or_four (hφ : Nonempty (OTwoQuot H ≃* S152N.W3)) (hA : A ∈ deltaSet H V) :
    (A ⊓ pCoreOf 2 H).relIndex A = 2 ∨ (A ⊓ pCoreOf 2 H).relIndex A = 4 := by
  have hle : (pCoreOf 2 H).relIndex A ≤ 4 :=
    S152Fin.relIndex_pCoreOf_le_four hφ hA.1.1 hA.1.2.1
  have h1 : (pCoreOf 2 H).relIndex A = (A ⊓ pCoreOf 2 H).relIndex A := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [h1] at hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (B2F.isPGroup_of_isElemAbelian hA.1.2.1).index ((A ⊓ pCoreOf 2 H).subgroupOf A)
  have hn' : (A ⊓ pCoreOf 2 H).relIndex A = 2 ^ n := hn
  have hne : (A ⊓ pCoreOf 2 H).relIndex A ≠ 1 := fun h =>
    hA.2.1 (le_inf_iff.1 (Subgroup.relIndex_eq_one.1 h)).2
  have hn2 : n ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases n
  · exact absurd hn' (by simpa using hne)
  · left; simpa using hn'
  · right; simpa using hn'

theorem inf_centralizer_eq_inf' {U A : Subgroup G} (hA : IsMaxElemAbelian H A)
    (hU : IsElemAbelian 2 U) (hUH : U ≤ H) :
    U ⊓ Subgroup.centralizer (A : Set G) = A ⊓ U := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    exact ⟨inf_centralizer_le_of_isMaxElemAbelian hU hUH hA hx, hx.1⟩
  · intro hx
    exact ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha =>
      B2F.isElemAbelian_comm hA.2.1 ha hx.1⟩

structure Data4 (V H A : Subgroup G) : Prop where
  rel : (A ⊓ pCoreOf 2 H).relIndex A = 4
  maxA : IsMaxElemAbelian H A
  uElem : IsElemAbelian 2 (conjClosure V H)
  uLe : conjClosure V H ≤ H
  quad : ⁅⁅conjClosure V H, A⁆, A⁆ = ⊥
  fix : conjClosure V H ⊓ Subgroup.centralizer (A : Set G) =
    conjClosure V H ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)
  cA : A ⊓ Subgroup.centralizer (conjClosure V H : Set G) ≤ pCoreOf 2 H
  idxU : Nat.card (conjClosure V H) =
    16 * Nat.card ↥(conjClosure V H ⊓ Subgroup.centralizer (A : Set G))
  idxB : Nat.card ↥(A ⊓ pCoreOf 2 H) =
    4 * Nat.card ↥(A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure V H : Set G))
  AU : conjClosure V H ⊓ Subgroup.centralizer (A : Set G) = A ⊓ conjClosure V H
  count_three : ∀ h ∈ H, ⁅A ⊓ pCoreOf 2 H, conjSubgroup V h⁆ ≠ ⊥ →
    Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 *
        Nat.card ↥(conjSubgroup V h ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) =
      Nat.card ↥(A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) ^ 2 *
        Nat.card (conjSubgroup V h)

theorem data4_of_delta {Mc M : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hc : Concl319 T M (V154 T Mc M) H True) (hA : A ∈ deltaSet H (V154 T Mc M))
    (h4 : (A ⊓ pCoreOf 2 H).relIndex A = 4) : Data4 (V154 T Mc M) H A := by
  have hT := S152N.isSylowTwoOf_hStar hs hH
  have hVH : V154 T Mc M ≤ H := (S152N.V154_le_T hs).trans hH.1.1
  have hUH : conjClosure (V154 T Mc M) H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hVH hz)) (H.inv_mem hh)
  have hAB : Nat.card A = 4 * Nat.card ↥(A ⊓ pCoreOf 2 H) := by
    have := Subgroup.relIndex_mul_card (A ⊓ pCoreOf 2 H) A
    rw [h4, inf_eq_left.2 inf_le_left] at this
    exact this.symm
  have hBpos : 0 < Nat.card ↥(A ⊓ pCoreOf 2 H) := Nat.card_pos
  have hCpos : 0 < Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (A : Set G)) :=
    Nat.card_pos
  have h1 := delta_count_one' hT hA hc
  have idxU : Nat.card (conjClosure (V154 T Mc M) H) =
      16 * Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [hAB] at h1
    refine Nat.eq_of_mul_eq_mul_left (pow_pos hBpos 2) ?_
    calc Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 * Nat.card (conjClosure (V154 T Mc M) H)
        = (4 * Nat.card ↥(A ⊓ pCoreOf 2 H)) ^ 2 *
            Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (A : Set G)) := h1.symm
      _ = _ := by ring
  have h2 := delta_count_two' hT hA hc
  have idxB : Nat.card ↥(A ⊓ pCoreOf 2 H) =
      4 * Nat.card ↥(A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G)) := by
    rw [idxU] at h2
    have h3 : Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 =
        (4 * Nat.card ↥(A ⊓ pCoreOf 2 H ⊓
          Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G))) ^ 2 := by
      refine Nat.eq_of_mul_eq_mul_right hCpos ?_
      calc Nat.card ↥(A ⊓ pCoreOf 2 H) ^ 2 *
            Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (A : Set G))
          = 16 * Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (A : Set G)) *
              Nat.card ↥(A ⊓ pCoreOf 2 H ⊓
                Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G)) ^ 2 := h2.symm
        _ = _ := by ring
    exact Nat.pow_left_injective (by norm_num) h3
  exact
    { rel := h4
      maxA := hA.1
      uElem := hc.elemAbelian
      uLe := hUH
      quad := S152N.delta_quadratic hA
      fix := delta_fixed_eq' hT hA hc
      cA := delta_cA_le' hT hA hc
      idxU := idxU
      idxB := idxB
      AU := inf_centralizer_eq_inf' hA.1 hc.elemAbelian hUH
      count_three := fun h hh hne => delta_count_three' hT hA hc hh hne }

end S152Z6

end CFSG.Quasithin
