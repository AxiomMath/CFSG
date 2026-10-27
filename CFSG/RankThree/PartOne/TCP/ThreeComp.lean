module

public import CFSG.RankThree.PartOne.TCP.SurvStruct
public import CFSG.RankThree.PartOne.TCP.FixedRank
public import CFSG.RankThree.PartOne.S11d.LowRank

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.TCP
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)
open scoped commutatorElement

theorem exists_isotropic_of_normalizes {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {x : StatedSp n K} {S : Subgroup (StatedSp n K)} (hS2 : IsPGroup 2 ↥S) (hS1 : S ≠ ⊥)
    (hx : x ∈ Subgroup.normalizer (S : Set (StatedSp n K))) :
    ∃ W : Submodule K (Fin n ⊕ Fin n → K), W ≠ ⊥ ∧
      (∀ u ∈ W, ∀ v ∈ W, CFSG.RankThree.Classical.spForm n K u v = 0) ∧
      ∀ w ∈ W, CFSG.RankThree.Classical.spEnd x w ∈ W := by
  obtain ⟨W, hW0, hWiso, hWE⟩ := KFU.exists_invariant_isotropic
    (CFSG.LieType.BorelTits.spForm n K) (CFSG.LieType.BorelTits.natRep (StatedSp n K))
    (CFSG.LieType.BorelTits.isIsometric_natRep_statedSp n K)
    (CFSG.LieType.BorelTits.natRep_injective _) (E := Subgroup.zpowers x) hS2 hS1
    ((Subgroup.zpowers_le).mpr hx)
  refine ⟨W, hW0, fun u hu v hv => ?_, fun w hw => ?_⟩
  · have h := hWiso hv u hu
    rw [CFSG.RankThree.Classical.spForm_apply]
    exact h
  · exact hWE x (Subgroup.mem_zpowers x) w hw

theorem normalizer_map_of_mulEquiv {T P : Type*} [Group T] [Group P] (e : T ≃* P) {x : T}
    {S : Subgroup T} (hx : x ∈ Subgroup.normalizer (S : Set T)) :
    e x ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup P) : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨s, rfl⟩ := e.surjective y
  have h1 : e s ∈ (S.map e.toMonoidHom : Subgroup P) ↔ s ∈ S := by
    constructor
    · rintro ⟨t, ht, hts⟩
      have : t = s := e.injective hts
      exact this ▸ ht
    · intro hs
      exact ⟨s, hs, rfl⟩
  have h2 : e x * e s * (e x)⁻¹ = e (x * s * x⁻¹) := by simp [map_mul, map_inv]
  have h3 : e (x * s * x⁻¹) ∈ (S.map e.toMonoidHom : Subgroup P) ↔ x * s * x⁻¹ ∈ S := by
    constructor
    · rintro ⟨t, ht, hts⟩
      have : t = x * s * x⁻¹ := e.injective hts
      exact this ▸ ht
    · intro hs
      exact ⟨_, hs, rfl⟩
  rw [h2, h1, h3]
  exact (Subgroup.mem_normalizer_iff.mp hx s)

theorem component_of_commutator_data {T P : Type} [Group T] [Group P] (e : T ≃* P) {x : T}
    (α : MulAut T) (hαx : α x = x) {D : Subgroup P} (hDq : CFSG.IsQuasisimple ↥D)
    (hDC : D ≤ Subgroup.centralizer ({e x} : Set P))
    (hDn : ∀ g ∈ Subgroup.centralizer ({e x} : Set P), ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hDc : ∀ g ∈ Subgroup.centralizer ({e x} : Set P),
      ∀ h ∈ Subgroup.centralizer ({e x} : Set P), ⁅g, h⁆ ∈ D)
    (hD2 : ∀ g ∈ Subgroup.centralizer ({e x} : Set P), (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ D) :
    ∃ D' : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D' ∧
      (∀ g ∈ D', α g ∈ D') ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) →
        g ∈ D' := by
  set C : Subgroup T := Subgroup.centralizer ({x} : Set T) with hC
  set D' : Subgroup T := D.map e.symm.toMonoidHom with hD'
  have hmemC : ∀ g : T, g ∈ C ↔ e g ∈ Subgroup.centralizer ({e x} : Set P) := fun g => by
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, e.injective.eq_iff]
  have hmemD : ∀ g : T, g ∈ D' ↔ e g ∈ D := fun g => by
    constructor
    · rintro ⟨d, hd, rfl⟩
      simpa using hd
    · intro hg
      exact ⟨e g, hg, by simp⟩
  have hD'C : D' ≤ C := fun g hg => (hmemC g).mpr (hDC ((hmemD g).mp hg))
  have hD'n : ∀ g ∈ C, ∀ d ∈ D', g * d * g⁻¹ ∈ D' := by
    intro g hg d hd
    rw [hmemD, map_mul, map_mul, map_inv]
    exact hDn _ ((hmemC g).mp hg) _ ((hmemD d).mp hd)
  have hD'c : ∀ g ∈ C, ∀ h ∈ C, ⁅g, h⁆ ∈ D' := by
    intro g hg h hh
    rw [hmemD, map_commutatorElement]
    exact hDc _ ((hmemC g).mp hg) _ ((hmemC h).mp hh)
  have hD'q : CFSG.IsQuasisimple ↥D' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective D e.symm.toMonoidHom e.symm.injective) hDq
  have hnormal : (D'.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : T) ∈ D' := hn
    show (g : T) * (n : T) * (g : T)⁻¹ ∈ D'
    exact hD'n g g.2 n hn'
  refine ⟨D', ⟨hD'C, hD'q, hnormal.isSubnormal⟩, ?_, ?_⟩
  · intro g hg
    have hαC : ∀ y ∈ C, α y ∈ C := fun y hy => by
      rw [hC, Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← hαx, ← map_mul, ← map_mul, hy]
    have hperf : ⁅D', D'⁆ = D' := KCUnitary.commutator_eq_of_isPerfect hD'q.1
    have hg' : g ∈ ⁅D', D'⁆ := hperf.symm ▸ hg
    have hmap : ⁅D', D'⁆.map α.toMonoidHom = ⁅D'.map α.toMonoidHom, D'.map α.toMonoidHom⁆ :=
      Subgroup.map_commutator _ _ _
    have hle : D'.map α.toMonoidHom ≤ C := by
      rintro _ ⟨d, hd, rfl⟩
      exact hαC d (hD'C hd)
    have hCC : ⁅C, C⁆ ≤ D' := Subgroup.commutator_le.mpr fun a ha b hb => hD'c a ha b hb
    have : α g ∈ ⁅D'.map α.toMonoidHom, D'.map α.toMonoidHom⁆ := by
      rw [← hmap]
      exact ⟨g, hg', rfl⟩
    exact hCC (Subgroup.commutator_mono hle hle this)
  · intro g hg _ hk
    obtain ⟨k, hk⟩ := hk
    rw [hmemD]
    refine hD2 _ ((hmemC g).mp hg) ⟨k, ?_⟩
    rw [MulEquiv.orderOf_eq, hk]

theorem ker_proj_two_eq_bot {K : Type} [Field K] [Finite K] (hK : 2 ∣ Nat.card K) {r : ℕ}
    (hr : 1 ≤ r) : (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K).ker = ⊥ := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj, ← Subgroup.card_eq_one,
    CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K hr]
  have : 1 < Nat.card K := Finite.one_lt_card
  have h2 : ¬ 2 ∣ Nat.card K - 1 := by omega
  exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)

theorem threeCompBL_PSp : ThreeCompBL .PSp := by
  intro T _ _ p hp hp5 hrank h2 n f₀ hf₀ hM hLow α hαp hαinn hLR hFix x hxp hx1 hαx S hS1 hS2 hSα
    hSx
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, k₀, _, _, hn2, hK, hk₀, ⟨eT⟩, ⟨eF⟩⟩ :=
    psp_concrete hp hp5 hrank hf₀ hM hαp hαinn hLR hFix
  have hp2 : p ≠ 2 := by omega
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
  have : CharP k₀ 2 := K128.charP_two_of_card_eq_two_pow hk₀
  have hpK : ¬ p ∣ Nat.card K := not_dvd_card_of_charTwo hp hp2
  have hpk : ¬ p ∣ Nat.card k₀ := not_dvd_card_of_charTwo hp hp2
  have hQ : Nat.card K = Nat.card k₀ ^ p := by rw [hK, hk₀, ← pow_mul, mul_comm]
  have hord : orderOf (Nat.card K : ZMod p) = orderOf (Nat.card k₀ : ZMod p) :=
    orderOf_natCast_pow_prime hp hQ
  have hrk : 2 ≤ CFSG.pRank p ↥(StatedSp n K) := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT]
    exact h2
  have hbd := blockDim_le_of_two_le_pRank hp hp2 hpK hrk
  rw [hord] at hbd
  by_cases hcond : Even (orderOf (Nat.card k₀ : ZMod p)) → orderOf (Nat.card k₀ : ZMod p) < n
  ·
    exfalso
    obtain ⟨R, hRe, hRc, hU⟩ := exists_psp_config hp hpk hbd
    obtain ⟨U, hU1, hU2, hUN⟩ := hU hcond
    let ψ : StatedSp n k₀ →* T := (fixRes α).subtype.comp eF.symm.toMonoidHom
    have hψ : Function.Injective ψ := (fixRes α).subtype_injective.comp eF.symm.injective
    have hfix : ∀ y, α (ψ y) = ψ y := fun y =>
      mem_fixSub.mp (fixRes_le_fixSub α (eF.symm y).2)
    exact false_of_rank_two_in_fixSub hαp hαinn hLR ψ hψ hfix hRe hRc hU1 hU2 hUN
  ·
    have hcond' : Even (orderOf (Nat.card k₀ : ZMod p)) ∧
        n ≤ orderOf (Nat.card k₀ : ZMod p) := by
      by_contra hc
      exact hcond fun hev => by
        by_contra hge
        exact hc ⟨hev, by omega⟩
    obtain ⟨hev, hne⟩ := hcond'
    have hbde : blockDim (orderOf (Nat.card k₀ : ZMod p)) = orderOf (Nat.card k₀ : ZMod p) :=
      ite_eq_left_iff.mpr fun h => absurd hev h
    rw [hbde] at hbd
    have hn3 : n ≤ 3 := hLow
    have hne' : orderOf (Nat.card k₀ : ZMod p) = n := le_antisymm hbd hne
    have hn2' : n = 2 := by
      obtain ⟨m, hm⟩ := hev
      omega
    subst hn2'
    have he2 : orderOf (Nat.card K : ZMod p) = 2 := by rw [hord, hne']
    have hf1 : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
    have hq4 : 3 < 2 ^ (p * f₀) := by
      calc 3 < 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hxo : orderOf (eT x) = p := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hxp hx1
    have hD : CFSG.RankThree.PartOne.KCSpComm.SpData 2 (p * f₀) 2 p K (eT x) :=
      ⟨Nat.prime_two, hf1, hK, hq4, le_rfl, hp, by omega, by omega, hxo⟩
    have hker := ker_proj_two_eq_bot (K := K) (hK ▸ dvd_pow_self 2 (by omega)) (r := 2)
      (by norm_num)
    have hinj : Function.Injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have hxop : orderOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K (eT x)) =
        p := by
      rw [orderOf_injective _ hinj (eT x), hxo]
    have blocks := ((CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
      Nat.prime_two hf1 hK hp hp2 hp2 (by norm_num) _ hxop).2) (eT x) rfl hxo
    set S' : Subgroup (StatedSp 2 K) := S.map eT.toMonoidHom with hS'
    have hS'1 : S' ≠ ⊥ := fun h =>
      hS1 ((Subgroup.map_eq_bot_iff_of_injective S eT.injective).mp h)
    have hS'2 : IsPGroup 2 ↥S' := hS2.map eT.toMonoidHom
    obtain ⟨W, hW0, hWiso, hWx⟩ := exists_isotropic_of_normalizes hS'2 hS'1
      (normalizer_map_of_mulEquiv eT hSx)
    obtain ⟨D, hDq, hDC, hDn, hDc, hD2⟩ :=
      sp4_survivor_component hD he2 blocks hW0 hWiso hWx
    exact component_of_commutator_data eT α hαx hDq hDC hDn hDc hD2

theorem fixedRankTL_PSp : FixedRankTL .PSp := fixedRankT_PSp.toL

end CFSG.RankThree.PartOne.TCX
