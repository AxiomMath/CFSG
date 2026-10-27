module

public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance

public section

namespace CFSG.StandardType.GGDichotomy

open CFSG CFSG.ComponentClassification Subgroup

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_primeCore_of_ne {p : ℕ} [Fact p.Prime] {Y K L : Subgroup G}
    (hK : CFSG.Open.lBalanceIsPComponent p Y K) (hL : CFSG.Open.lBalanceIsPComponent p Y L)
    (hne : K ≠ L) : ⁅K, L⁆ ≤ CFSG.Open.lBalancePrimeCore p Y := by
  have hKY : K ≤ Y := LBalance.subnormal_le hK.1
  have hLY : L ≤ Y := LBalance.subnormal_le hL.1
  have hK' : IsPComponent p (K.subgroupOf Y) :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y K hKY).mpr hK
  have hL' : IsPComponent p (L.subgroupOf Y) :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y L hLY).mpr hL
  have hne' : K.subgroupOf Y ≠ L.subgroupOf Y := fun h =>
    hne (by rw [← map_subgroupOf_eq_of_le hKY, h, map_subgroupOf_eq_of_le hLY])
  have h := (CatalogueBPrimeJoin.mutual_normalization_core_commutation p _ _ hK' hL' hne').2.2
  have h2 : ⁅K.subgroupOf Y, L.subgroupOf Y⁆ ≤ pPrimeCore p ↥Y :=
    (h.trans inf_le_left).trans (GGPumpup.map_pPrimeCore_le hK')
  have h3 := Subgroup.map_mono (f := Y.subtype) h2
  rwa [Subgroup.map_commutator, map_subgroupOf_eq_of_le hKY, map_subgroupOf_eq_of_le hLY,
    ← LBalance.primeCore_eq_map] at h3

theorem eq_of_le_of_pComponent {p : ℕ} [Fact p.Prime] {Y J X X' : Subgroup G}
    (hX : CFSG.Open.lBalanceIsPComponent p Y X) (hX' : CFSG.Open.lBalanceIsPComponent p Y X')
    (hJX : J ≤ X) (hJX' : J ≤ X') (hJ : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J) : X' = X := by
  by_contra hne
  have h := commutator_le_primeCore_of_ne hX' hX hne
  refine not_le_lBalancePrimeCore_of_dvd (Y := Y) hpJ ?_
  calc J = ⁅J, J⁆ := hJ.symm
    _ ≤ ⁅X', X⁆ := Subgroup.commutator_mono hJX' hJX
    _ ≤ CFSG.Open.lBalancePrimeCore p Y := h

theorem eq_one_of_mem_of_coprime {p : ℕ} {O : Subgroup G} (hO : p.Coprime (Nat.card O)) {c : G}
    (hc : c ∈ O) (hcp : c ^ p = 1) : c = 1 := by
  have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have h2 : orderOf c ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk c hc]
    exact orderOf_dvd_natCard _
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hO) h2)

theorem commutator_iSup_le_primeCore {p : ℕ} {Y X : Subgroup G} (A : ℕ → Subgroup G) (n : ℕ)
    (hX : X ≤ Y) (hA : ∀ i, i < n → A i ≤ Y)
    (h : ∀ i, i < n → ⁅A i, X⁆ ≤ CFSG.Open.lBalancePrimeCore p Y) :
    ⁅⨆ (i : ℕ) (_ : i < n), A i, X⁆ ≤ CFSG.Open.lBalancePrimeCore p Y := by
  rw [Subgroup.commutator_le]
  intro g hg b hb
  obtain ⟨W, hW1, hW2⟩ := exists_le_iff_commutator_le_lBalancePrimeCore p (hX hb)
  have hAW : (⨆ (i : ℕ) (_ : i < n), A i) ≤ W := iSup₂_le fun i hi =>
    hW1 (A i) (hA i hi) ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hb)).trans
      (h i hi))
  exact hW2 _ hAW (Subgroup.commutator_mem_commutator hg (Subgroup.mem_zpowers b))

theorem exists_pComponent_orbit (hL : GGLBalanceInput) {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hYK : CFSG.Open.lBalanceIsKGroup ↥Y) {e : G} (heY : e ∈ Y) (hep : e ^ p = 1)
    {T : Subgroup G}
    (hT : CFSG.Open.lBalanceIsPComponent p (Y ⊓ centralizer ({e} : Set G)) T) :
    ∃ A : Subgroup G, CFSG.Open.lBalanceIsPComponent p Y A ∧ T ≤ GGPumpup.orbitJoinLT A e p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hTle : T ≤ Y ⊓ centralizer ({e} : Set G) := LBalance.subnormal_le hT.1
  have hTW' : T ≤ CFSG.Open.lBalancePLayer p (Y ⊓ centralizer ({e} : Set G)) := le_sSup hT
  have hTW : T ≤ CFSG.Open.lBalancePLayer p Y :=
    hTW'.trans (lBalancePLayer_inf_centralizer_le_of_input hL hp hYK heY hep)
  set e' : ↥Y := ⟨e, heY⟩ with he'def
  have he'p : e' ^ p = 1 := Subtype.ext (by simp [e', hep])
  obtain ⟨hTC, hT'⟩ := GGPumpup.isPComponent_subgroupOf_centralizer heY hT
  have hTE : T.subgroupOf Y ≤ pLayer ↥Y p := by
    intro z hz
    have hz' : (z : G) ∈ (pLayer ↥Y p).map Y.subtype := by
      rw [← LBalance.Asm.lBalancePLayer_eq_map]
      exact hTW (mem_subgroupOf.mp hz)
    exact (mem_map_iff_mem Y.subtype_injective).mp hz'
  obtain ⟨A', hA', hKA'⟩ := GGPumpup.exists_pComponent_closureIn_eq he'p hTC hT' hTE
  have hAY : A'.map Y.subtype ≤ Y := map_subtype_le A'
  have hAlB : CFSG.Open.lBalanceIsPComponent p Y (A'.map Y.subtype) := by
    refine (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y _ hAY).mp ?_
    change IsPComponent p ((A'.map Y.subtype).comap Y.subtype)
    rwa [comap_map_eq_self_of_injective Y.subtype_injective A']
  refine ⟨A'.map Y.subtype, hAlB, ?_⟩
  have hTK : T.subgroupOf Y ≤ GGPumpup.orbitJoinLT A' e' p := by
    rw [← hKA']
    exact GGPumpup.le_closureIn _ _
  have h := Subgroup.map_mono (f := Y.subtype) hTK
  rw [map_subgroupOf_eq_of_le (hTle.trans inf_le_left), GGPumpup.map_orbitJoinLT] at h
  exact h

theorem pComponent_le_or_commutator_le (hL : GGLBalanceInput) {p : ℕ} (hp : p.Prime)
    {Y X : Subgroup G} (hYK : CFSG.Open.lBalanceIsKGroup ↥Y)
    (hX : CFSG.Open.lBalanceIsPComponent p Y X) (S : Finset G) (hSY : ∀ e ∈ S, e ∈ Y)
    (hSp : ∀ e ∈ S, e ^ p = 1) (hSX : ∀ e ∈ S, e ∈ normalizer (X : Set G))
    (hSc : ∀ e ∈ S, ∀ f ∈ S, e * f = f * e) :
    ∀ T : Subgroup G, CFSG.Open.lBalanceIsPComponent p (Y ⊓ centralizer (S : Set G)) T →
      T ≤ X ∨ ⁅T, X⁆ ≤ CFSG.Open.lBalancePrimeCore p Y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hXY : X ≤ Y := LBalance.subnormal_le hX.1
  have hOn : Y ≤ normalizer (CFSG.Open.lBalancePrimeCore p Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (LBalance.primeCore_le p Y)).mp
      (LBalance.primeCore_normal p Y)
  induction S using Finset.induction_on with
  | empty =>
    intro T hT
    have hc : Y ⊓ centralizer (((∅ : Finset G)) : Set G) = Y := by
      ext g
      simp [mem_inf, mem_centralizer_iff]
    rw [hc] at hT
    by_cases hTX : T = X
    · exact Or.inl hTX.le
    · exact Or.inr (commutator_le_primeCore_of_ne hT hX hTX)
  | insert e S heS ih =>
    intro T hT
    have heY : e ∈ Y := hSY e (Finset.mem_insert_self e S)
    have hep : e ^ p = 1 := hSp e (Finset.mem_insert_self e S)
    have heX : e ∈ normalizer (X : Set G) := hSX e (Finset.mem_insert_self e S)
    have hSY' : ∀ f ∈ S, f ∈ Y := fun f hf => hSY f (Finset.mem_insert_of_mem hf)
    have hSp' : ∀ f ∈ S, f ^ p = 1 := fun f hf => hSp f (Finset.mem_insert_of_mem hf)
    have hSX' : ∀ f ∈ S, f ∈ normalizer (X : Set G) :=
      fun f hf => hSX f (Finset.mem_insert_of_mem hf)
    have hSc' : ∀ f ∈ S, ∀ f' ∈ S, f * f' = f' * f :=
      fun f hf f' hf' => hSc f (Finset.mem_insert_of_mem hf) f' (Finset.mem_insert_of_mem hf')
    have heC : e ∈ centralizer (S : Set G) := by
      rw [mem_centralizer_iff]
      intro f hf
      exact hSc f (Finset.mem_insert_of_mem hf) e (Finset.mem_insert_self e S)
    have hY'K : CFSG.Open.lBalanceIsKGroup ↥(Y ⊓ centralizer (S : Set G)) :=
      GGPumpup.lBalanceIsKGroup_of_le hYK inf_le_left
    have hcent : Y ⊓ centralizer (((insert e S : Finset G)) : Set G) =
        (Y ⊓ centralizer (S : Set G)) ⊓ centralizer ({e} : Set G) := by
      ext g
      simp only [mem_inf, mem_centralizer_iff, Finset.coe_insert, Set.mem_insert_iff,
        Finset.mem_coe, forall_eq_or_imp, Set.mem_singleton_iff, forall_eq]
      tauto
    rw [hcent] at hT
    obtain ⟨A₀, hA₀, hTA⟩ := exists_pComponent_orbit hL hp hY'K (mem_inf.mpr ⟨heY, heC⟩) hep hT
    rcases ih hSY' hSp' hSX' hSc' A₀ hA₀ with hAX | hAX
    · left
      refine hTA.trans (GGPumpup.orbitJoinLT_le fun i _ => ?_)
      exact ((GGPumpup.conjugate_le_conjugate_iff (e ^ i)).mpr hAX).trans
        (GGPumpup.conjugate_eq_of_mem_normalizer (Subgroup.pow_mem _ heX i)).le
    · right
      have hA₀Y : A₀ ≤ Y := (LBalance.subnormal_le hA₀.1).trans inf_le_left
      refine (Subgroup.commutator_mono hTA le_rfl).trans ?_
      refine commutator_iSup_le_primeCore (fun i => CFSG.conjugate A₀ (e ^ i)) p hXY
        (fun i _ => ?_) (fun i _ => ?_)
      · exact ((GGPumpup.conjugate_le_conjugate_iff (e ^ i)).mpr hA₀Y).trans
          (GGPumpup.conjugate_eq_of_mem_normalizer
            (Subgroup.le_normalizer (Subgroup.pow_mem _ heY i))).le
      · have hXi : CFSG.conjugate X (e ^ i) = X :=
          GGPumpup.conjugate_eq_of_mem_normalizer (Subgroup.pow_mem _ heX i)
        have hOi : CFSG.conjugate (CFSG.Open.lBalancePrimeCore p Y) (e ^ i) =
            CFSG.Open.lBalancePrimeCore p Y :=
          GGPumpup.conjugate_eq_of_mem_normalizer
            (Subgroup.pow_mem _ (hOn heY) i)
        calc ⁅CFSG.conjugate A₀ (e ^ i), X⁆
            = ⁅CFSG.conjugate A₀ (e ^ i), CFSG.conjugate X (e ^ i)⁆ := by rw [hXi]
          _ = CFSG.conjugate ⁅A₀, X⁆ (e ^ i) := by
              unfold CFSG.conjugate
              rw [Subgroup.map_commutator]
          _ ≤ CFSG.conjugate (CFSG.Open.lBalancePrimeCore p Y) (e ^ i) :=
              (GGPumpup.conjugate_le_conjugate_iff (e ^ i)).mpr hAX
          _ = CFSG.Open.lBalancePrimeCore p Y := hOi

end CFSG.StandardType.GGDichotomy

end
