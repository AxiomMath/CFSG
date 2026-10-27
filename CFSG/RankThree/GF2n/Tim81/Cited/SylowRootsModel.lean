module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
public import CFSG.Timmesfeld.Transvection.ModelSULowSpan
import CFSG.RankThree.GF2n.Tim81.Cited.SUImageBasic
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount
import CFSG.Timmesfeld.Transvection.ModelSULowRadGen
import CFSG.GroupTheory.OddKernelImage
import CFSG.Timmesfeld.ARS.CaseMSU
import CFSG.Timmesfeld.ARS.ConjSubComp
import CFSG.LocalAnalysis.StandardType.SUCenterOdd

public section

namespace CFSG.RankThree.GF2n.Tim81.SUTrans

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.RankThree.GF2n CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection
open CFSG.Timmesfeld.Transvection.ModelRank
open scoped MatrixGroups commutatorElement Pointwise

private theorem sylowRoots_le_map_lowRad {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {N : ℕ} (hN : 2 ≤ N) {K : Type} [Group K]
    {X₀ : Subgroup K} {Δ : Set (Subgroup K)} {Φ : SU σ N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ N)) (hrange : Φ.range = X₀)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x).map Φ)
    (S : Sylow 2 ↥X₀)
    (hS : (lowRad σ N).map Φ ≤ (S : Subgroup ↥X₀).map X₀.subtype) :
    sylowRoots X₀ Δ S ≤ (lowRad σ N).map Φ := by
  haveI : Finite (SU σ N) :=
    Finite.of_injective (SUExtras.mat σ N) (SUExtras.mat_injective (σ := σ) (n := N))
  have hodd : Odd (Nat.card Φ.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU σ hker
  have hSleRange : (S : Subgroup ↥X₀).map X₀.subtype ≤ Φ.range := by
    rw [hrange]
    exact Subgroup.map_subtype_le _
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAΔ, hAS⟩ := hA
  obtain ⟨v, T, hv0, hvv, hT, rfl⟩ := exists_eq_map_of_mem hσ hN hΔ hAΔ
  obtain ⟨P, hP2, hPmap, -⟩ :=
    CFSG.GroupTheory.exists_isPGroup_map_eq_of_odd (Φ := Φ) hodd hSleRange
      (S.isPGroup'.map X₀.subtype)
  have hQbarP : (lowRad σ N).map Φ ≤ P.map Φ := by rw [hPmap]; exact hS
  have hRP : lowRad σ N ≤ P :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd hker hodd (isPGroup_lowRad (σ := σ) (m := N)) hQbarP
  have hT2 : IsPGroup 2 T :=
    (isPGroup_uRad (σ := σ) v).of_injective
      (Subgroup.inclusion (le_uRad_of_isUTransGroup hvv hT))
      (Subgroup.inclusion_injective _)
  have hTP : T ≤ P :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd hker hodd hT2 (by rw [hPmap]; exact hAS)
  have hvlow : v ∈ lowSpan F N :=
    mem_lowSpan_of_isPGroup_of_lowRad_le hσ hP2 hRP hvv hT hTP
  exact Subgroup.map_mono (le_lowRad_of_isUTransGroup hvlow hT)

private theorem map_lowRad_le_sylowRoots {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {N : ℕ} (hN : 2 ≤ N)
    {K : Type} [Group K] {X₀ : Subgroup K} {Δ : Set (Subgroup K)} {Φ : SU σ N →* K}
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x).map Φ)
    (S : Sylow 2 ↥X₀)
    (hS : (lowRad σ N).map Φ ≤ (S : Subgroup ↥X₀).map X₀.subtype) :
    (lowRad σ N).map Φ ≤ sylowRoots X₀ Δ S := by
  rw [Subgroup.map_le_iff_le_comap]
  refine lowRad_le_of_forall hσ fun v T hv hv0 hT => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hvv : uForm σ v v = 0 := uForm_eq_zero_of_mem_lowSpan hv hv
  have hTlow : T ≤ lowRad σ N := le_lowRad_of_isUTransGroup hv hT
  refine le_iSup₂_of_le (T.map Φ)
    ⟨map_mem hσ htr hN hΔ hv0 hvv hT, (Subgroup.map_mono hTlow).trans hS⟩ le_rfl

theorem sylowRoots_eq_map_lowRad {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {N : ℕ} (hN : 2 ≤ N)
    {K : Type} [Group K] {X₀ : Subgroup K} {Δ : Set (Subgroup K)} {Φ : SU σ N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ N)) (hrange : Φ.range = X₀)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x).map Φ)
    (S : Sylow 2 ↥X₀)
    (hS : (lowRad σ N).map Φ ≤ (S : Subgroup ↥X₀).map X₀.subtype) :
    sylowRoots X₀ Δ S = (lowRad σ N).map Φ :=
  le_antisymm (sylowRoots_le_map_lowRad hσ hN hker hrange hΔ S hS)
    (map_lowRad_le_sylowRoots hσ htr hN hΔ S hS)

theorem exists_map_comp_conj_lowRad_le {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    {N : ℕ} {K : Type} [Group K] [Finite K] {X₀ : Subgroup K} {Φ : SU σ N →* K}
    (hrange : Φ.range = X₀) (S : Sylow 2 ↥X₀) :
    ∃ x : SU σ N, (lowRad σ N).map (Φ.comp (MulAut.conj x).toMonoidHom) ≤
      (S : Subgroup ↥X₀).map X₀.subtype := by
  let Qbar : Subgroup K := (lowRad σ N).map Φ
  have hQbar_le_X : Qbar ≤ X₀ := (Subgroup.map_le_range Φ (lowRad σ N)).trans_eq hrange
  let Q' : Subgroup ↥X₀ := Qbar.subgroupOf X₀
  have hQ'2 : IsPGroup 2 Q' :=
    (isPGroup_lowRad (σ := σ) (m := N)).map Φ |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe hQbar_le_X).symm
  obtain ⟨S₀, hQ'S₀⟩ := hQ'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X₀ S₀ S
  have hSbar₀ : Qbar ≤ (S₀ : Subgroup ↥X₀).map X₀.subtype := by
    calc Qbar = Q'.map X₀.subtype := (Subgroup.map_subgroupOf_eq_of_le hQbar_le_X).symm
      _ ≤ (S₀ : Subgroup ↥X₀).map X₀.subtype := Subgroup.map_mono hQ'S₀
  have hSbar : (S : Subgroup ↥X₀).map X₀.subtype =
      conjSubgroup (X₀.subtype g) ((S₀ : Subgroup ↥X₀).map X₀.subtype) := by
    calc (S : Subgroup ↥X₀).map X₀.subtype
        = ((g • S₀ : Sylow 2 ↥X₀) : Subgroup ↥X₀).map X₀.subtype := by rw [← hg]
      _ = (MulAut.conj g • (S₀ : Subgroup ↥X₀)).map X₀.subtype := by
            rw [Sylow.coe_subgroup_smul]
      _ = ((S₀ : Subgroup ↥X₀).map (MulAut.conj g).toMonoidHom).map X₀.subtype := by
            rw [Subgroup.pointwise_smul_def]
            rfl
      _ = conjSubgroup (X₀.subtype g) ((S₀ : Subgroup ↥X₀).map X₀.subtype) :=
            map_conjSubgroup X₀.subtype g (S₀ : Subgroup ↥X₀)
  have hmem : X₀.subtype g ∈ Φ.range := by
    rw [hrange]
    exact g.2
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  calc (lowRad σ N).map (Φ.comp (MulAut.conj x).toMonoidHom)
      = ((lowRad σ N).map (MulAut.conj x).toMonoidHom).map Φ := by
          rw [Subgroup.map_map]
    _ = (conjSubgroup x (lowRad σ N)).map Φ := rfl
    _ = conjSubgroup (Φ x) Qbar := map_conjSubgroup Φ x (lowRad σ N)
    _ = conjSubgroup (X₀.subtype g) Qbar := by rw [hx]
    _ ≤ conjSubgroup (X₀.subtype g) ((S₀ : Subgroup ↥X₀).map X₀.subtype) :=
          Subgroup.map_mono hSbar₀
    _ = (S : Subgroup ↥X₀).map X₀.subtype := hSbar.symm

theorem exists_sylowRoots_eq_map_lowRad {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (htr : ∀ a, σ a = a → ∃ c, c + σ c = a)
    {N : ℕ} (hN : 2 ≤ N) {K : Type} [Group K] [Finite K] {X₀ : Subgroup K}
    {Δ : Set (Subgroup K)} {Φ : SU σ N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ N)) (hrange : Φ.range = X₀)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x).map Φ)
    (S : Sylow 2 ↥X₀) :
    ∃ Φ' : SU σ N →* K, Φ'.ker ≤ Subgroup.center (SU σ N) ∧ Φ'.range = X₀ ∧
      (∀ U : Subgroup K, U ∈ Δ ↔
        ∃ x, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x).map Φ') ∧
      sylowRoots X₀ Δ S = (lowRad σ N).map Φ' := by
  obtain ⟨x, hx⟩ := exists_map_comp_conj_lowRad_le hrange S
  let Φ' : SU σ N →* K := Φ.comp (MulAut.conj x).toMonoidHom
  have hker' : Φ'.ker ≤ Subgroup.center (SU σ N) :=
    CFSG.Timmesfeld.ARS.CaseMSU.ker_comp_conj_le_center hker x
  have hrange' : Φ'.range = X₀ := (range_comp_conj Φ x).trans hrange
  have hΔ' : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ y, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) y).map Φ' := by
    intro U
    refine (hΔ U).trans ?_
    exact (exists_eq_map_conjSub_comp_conj_iff Φ
      (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x U).symm
  refine ⟨Φ', hker', hrange', hΔ', ?_⟩
  exact sylowRoots_eq_map_lowRad hσ htr hN hker' hrange' hΔ' S hx

theorem commute_of_mem_map_lowRad {F : Type} [Field F] {σ : F ≃+* F} {N : ℕ}
    {K : Type} [Group K] {Φ : SU σ N →* K} {x y : K}
    (hx : x ∈ (lowRad σ N).map Φ) (hy : y ∈ (lowRad σ N).map Φ) : x * y = y * x := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hy
  rw [← map_mul, ← map_mul, commute_of_mem_lowRad hg hh]

theorem mul_self_eq_one_of_mem_map_lowRad {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    {N : ℕ} {K : Type} [Group K] {Φ : SU σ N →* K} {x : K}
    (hx : x ∈ (lowRad σ N).map Φ) : x * x = 1 := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  rw [← map_mul, mul_self_eq_one_of_mem_lowRad hg, map_one]

theorem inSubgroup_pCore_le_normalizer_map_lowRad {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (htr : ∀ a, σ a = a → ∃ c, c + σ c = a)
    {N : ℕ} (hN : 2 ≤ N) {K : Type} [Group K] [Finite K] {X₀ : Subgroup K}
    {Δ : Set (Subgroup K)} {Φ : SU σ N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ N)) (hrange : Φ.range = X₀)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x).map Φ)
    {T : Subgroup K} (hT : T ≤ (lowRad σ N).map Φ) :
    inSubgroup (pCore 2) (X₀ ⊓ Subgroup.normalizer (T : Set K)) ≤
      Subgroup.normalizer (((lowRad σ N).map Φ : Subgroup K) : Set K) := by
  let Qbar : Subgroup K := (lowRad σ N).map Φ
  let L : Subgroup K := X₀ ⊓ Subgroup.normalizer (T : Set K)
  let R : Subgroup K := inSubgroup (pCore 2) L
  have hQbar_le_X : Qbar ≤ X₀ := (Subgroup.map_le_range Φ (lowRad σ N)).trans_eq hrange
  have hQbar_le_NT : Qbar ≤ Subgroup.normalizer (T : Set K) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq t ht
    rw [commute_of_mem_map_lowRad hq (hT ht), mul_assoc, mul_inv_cancel, mul_one]
    exact ht
  have hQbar_le_L : Qbar ≤ L := le_inf hQbar_le_X hQbar_le_NT
  haveI : (CFSG.pCore 2 L).Normal :=
    CFSG.LieType.BorelTits.pCore_normal (G := L) (r := 2)
  have hRnorm : L ≤ Subgroup.normalizer (R : Set K) := by
    have h := Subgroup.le_normalizer_map (H := CFSG.pCore 2 L) L.subtype
    rw [Subgroup.normalizer_eq_top] at h
    have htop : (⊤ : Subgroup L).map L.subtype = L := by
      ext x
      simp
    rwa [htop] at h
  have hR2 : IsPGroup 2 R :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := L) (r := 2)).map L.subtype
  have hQ2 : IsPGroup 2 Qbar := isPGroup_lowRad.map Φ
  have hRQ2 : IsPGroup 2 (R ⊔ Qbar : Subgroup K) :=
    IsPGroup.to_sup_of_normal_left' hR2 hQ2 (hQbar_le_L.trans hRnorm)
  have hR_le_X : R ≤ X₀ := (Subgroup.map_subtype_le (CFSG.pCore 2 L)).trans inf_le_left
  have hRQ_le_X : R ⊔ Qbar ≤ X₀ := sup_le hR_le_X hQbar_le_X
  let P : Subgroup ↥X₀ := (R ⊔ Qbar).subgroupOf X₀
  have hP2 : IsPGroup 2 P :=
    hRQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hRQ_le_X).symm
  obtain ⟨S', hPS'⟩ := hP2.exists_le_sylow
  have hPmap : P.map X₀.subtype = R ⊔ Qbar :=
    Subgroup.map_subgroupOf_eq_of_le hRQ_le_X
  have hQbar_le_S' : Qbar ≤ (S' : Subgroup ↥X₀).map X₀.subtype := by
    refine (show Qbar ≤ P.map X₀.subtype from ?_).trans (Subgroup.map_mono hPS')
    rw [hPmap]
    exact le_sup_right
  have hR_le_S' : R ≤ (S' : Subgroup ↥X₀).map X₀.subtype := by
    refine (show R ≤ P.map X₀.subtype from ?_).trans (Subgroup.map_mono hPS')
    rw [hPmap]
    exact le_sup_left
  have hS'eq : sylowRoots X₀ Δ S' = Qbar :=
    sylowRoots_eq_map_lowRad hσ htr hN hker hrange hΔ S' hQbar_le_S'
  have hΔconj : ∀ A ∈ Δ, ∀ x ∈ X₀, conjSubgroup x A ∈ Δ := by
    intro A hA x hx
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    exact conjSubgroup_mem_of_mem hσ hN hΔ hA y
  have hmap := map_sylow_le_normalizer_sylowRoots hΔconj S'
  rw [hS'eq] at hmap
  exact hR_le_S'.trans hmap

theorem le_map_lowRad_of_le_centralizer {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {N : ℕ} (hN : 2 ≤ N) {K : Type} [Group K]
    {X₀ : Subgroup K} {Δ : Set (Subgroup K)} {Φ : SU σ N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ N))
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ N (unitaryLongRoot N hN)) x).map Φ)
    {A : Subgroup K} (hA : A ∈ Δ)
    (hAc : A ≤ Subgroup.centralizer (((lowRad σ N).map Φ : Subgroup K) : Set K)) :
    A ≤ (lowRad σ N).map Φ := by
  obtain ⟨v, T, hv0, hvv, hT, rfl⟩ := exists_eq_map_of_mem hσ hN hΔ hA
  have hmem : ∀ a : Fin (N / 2),
      uForm σ v (Pi.single (lowIdx a) 1 : Fin N → F) = 0 := by
    intro a
    have hee : uForm σ (Pi.single (lowIdx a) 1 : Fin N → F) (Pi.single (lowIdx a) 1) = 0 :=
      uForm_single_self (lowIdx_ne_rev a a)
    obtain ⟨Ta, hTa⟩ := exists_isUTransGroup hσ hee
    have hTaQ : Ta ≤ lowRad σ N :=
      le_lowRad_of_isUTransGroup (single_lowIdx_mem_lowSpan a) hTa
    have hTcomm : ⁅T.map Φ, Ta.map Φ⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (hAc hx)) y (Subgroup.map_mono hTaQ hy)
    exact (commutator_map_eq_bot_iff hσ hker hT hTa hv0 hvv hee).1 hTcomm
  have hvlow : v ∈ lowSpan F N := mem_lowSpan_of_forall_uForm_single_eq_zero hvv hmem
  exact Subgroup.map_mono (le_lowRad_of_isUTransGroup hvlow hT)

theorem natCard_map_lowRad {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {N : ℕ} {K : Type} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) N)) :
    Nat.card ↥((lowRad (unitaryInvolution F 2 f) N).map Φ) = (2 ^ f) ^ ((N / 2) ^ 2) := by
  haveI : Finite (SU (unitaryInvolution F 2 f) N) :=
    Finite.of_injective (SUExtras.mat (unitaryInvolution F 2 f) N)
      (SUExtras.mat_injective (σ := unitaryInvolution F 2 f) (n := N))
  have hodd : Odd (Nat.card Φ.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU (unitaryInvolution F 2 f) hker
  rw [CFSG.GroupTheory.natCard_map_of_isPGroup_of_odd (Φ := Φ) hodd
      (isPGroup_lowRad (σ := unitaryInvolution F 2 f) (m := N)),
    natCard_lowRad hF hf N]

end CFSG.RankThree.GF2n.Tim81.SUTrans
