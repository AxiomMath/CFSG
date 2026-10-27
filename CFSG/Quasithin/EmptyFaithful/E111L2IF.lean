module

public import CFSG.Quasithin.EmptyFaithful.E111L2IE
public import CFSG.Quasithin.EmptyFaithful.E111L2IA

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

variable {G : Type} [Group G]

theorem conj_mem_pCoreOf (K : Subgroup G) :
    ∀ k ∈ K, ∀ n ∈ pCoreOf 2 K, k * n * k⁻¹ ∈ pCoreOf 2 K := by
  intro k hk n hn
  obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.1 hn
  have hnorm := CFSG.LieType.BorelTits.pCore_normal (G := ↥K) 2
  exact Subgroup.mem_map.2 ⟨⟨k, hk⟩ * n' * ⟨k, hk⟩⁻¹, hnorm.conj_mem n' hn' ⟨k, hk⟩, by simp⟩

section Diag

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C] [Finite G]
  {L₀ P V' : Subgroup G}
  (hd : S4Data (diagSub S C h.diagComm) T (T ⊓ Subgroup.centralizer (A : Set G)) L₀ P V')
include h hd

theorem K_le_normalizer_M :
    sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
        (T ⊓ Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer ((sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) V') :
        Subgroup G) : Set G) :=
  sup_le (sSup_le_normalizer h hd.L_le (S4Data.V_le_D h hd) (fun k hk hD => (hd.inv k hk hD).1)
    hd.V_norm) (le_normalizer_conjFam _ _)

theorem M_le_pCoreOf :
    sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) V') ≤
      pCoreOf 2 (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
        (T ⊓ Subgroup.centralizer (A : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ (K_le_normalizer_M h hd)
    (h.isPGroup_T.to_le (sSup_le_T hd.V_T))
  refine (sSup_le fun Z hZ => ?_).trans le_sup_left
  obtain ⟨k, rfl⟩ := hZ
  exact (A1b.conjSub_mono _ (hd.V_le.trans hd.P_le)).trans (le_sSup (conj_mem_conjFam k.2))

omit hd in
theorem diagE_le_sup {D' : Subgroup G} (hD' : D' ∈ diagFam T A S C h.diagComm) :
    diagE T A S C h.diagComm ≤ D' ⊔ Subgroup.centralizer (D' : Set G) := by
  refine sSup_le fun D'' hD'' => ?_
  by_cases heq : D'' = D'
  · exact heq ▸ le_sup_left
  · refine le_sup_of_le_right fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h.semiFam.comm D'' hD'' D' hD' heq x hx y hy).symm

theorem mul_self_of_mem_centralizer
    (hcent : Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm = V')
    (hV' : IsKleinFour ↥V') {y : G} (hyY : y ∈ diagE T A S C h.diagComm)
    (hyM : y ∈ Subgroup.centralizer
      ((sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) V') : Subgroup G) : Set G)) :
    y * y = 1 := by
  have hcen : ∀ D' ∈ diagFam T A S C h.diagComm,
      y * y ∈ Subgroup.centralizer (D' : Set G) := by
    rintro _ ⟨k, rfl⟩
    set D' := A1b.conjSub (k : G) (diagSub S C h.diagComm) with hD'
    have hD'mem : D' ∈ diagFam T A S C h.diagComm := ⟨k, rfl⟩
    have hN : Subgroup.centralizer (D' : Set G) ≤ Subgroup.normalizer (D' : Set G) :=
      Subgroup.centralizer_le_normalizer _
    obtain ⟨d, hd', c, hc, rfl⟩ := exists_mul_of_mem_sup hN (diagE_le_sup h hD'mem hyY)
    have hdV : d ∈ A1b.conjSub (k : G) V' := by
      rw [A1b.mem_conjSub_iff]
      have hdD : (k : G)⁻¹ * d * k ∈ diagSub S C h.diagComm := by
        rw [hD', A1b.mem_conjSub_iff] at hd'
        exact hd'
      rw [← hcent]
      refine Subgroup.mem_inf.mpr ⟨?_, hdD⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : (k : G) * v * (k : G)⁻¹ ∈ D' :=
        A1b.mem_conjSub_of_mem (S4Data.V_le_D h hd hv)
      have hvM : (k : G) * v * (k : G)⁻¹ ∈
          sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) V') :=
        le_sSup (conj_mem_conjFam k.2) (A1b.mem_conjSub_of_mem hv)
      have e1 := Subgroup.mem_centralizer_iff.mp hyM _ hvM
      have e2 := Subgroup.mem_centralizer_iff.mp hc _ hv'
      set w := (k : G) * v * (k : G)⁻¹ with hw
      have e3 : w * d = d * w := by
        calc w * d = (w * (d * c)) * c⁻¹ := by group
          _ = (d * c * w) * c⁻¹ := by rw [e1]
          _ = d * (c * w) * c⁻¹ := by group
          _ = d * (w * c) * c⁻¹ := by rw [e2]
          _ = d * w := by group
      calc v * ((k : G)⁻¹ * d * k) = (k : G)⁻¹ * (w * d) * k := by rw [hw]; group
        _ = (k : G)⁻¹ * (d * w) * k := by rw [e3]
        _ = (k : G)⁻¹ * d * k * v := by rw [hw]; group
    have hdd : d * d = 1 := by
      rw [A1b.mem_conjSub_iff] at hdV
      have h1 := congrArg Subtype.val (hV'.mul_self ⟨_, hdV⟩)
      have h2 : (k : G)⁻¹ * (d * d) * k = 1 := by
        simp only [Subgroup.coe_mul, OneMemClass.coe_one] at h1
        rw [← h1]
        group
      calc d * d = k * ((k : G)⁻¹ * (d * d) * k) * (k : G)⁻¹ := by group
        _ = 1 := by rw [h2]; group
    have hcd : c * d = d * c := (Subgroup.mem_centralizer_iff.mp hc d hd').symm
    have : d * c * (d * c) = c * c := by
      calc d * c * (d * c) = d * (c * d) * c := by group
        _ = d * (d * c) * c := by rw [hcd]
        _ = (d * d) * (c * c) := by group
        _ = c * c := by rw [hdd, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ hc hc
  have hY : y * y ∈ Subgroup.centralizer ((diagE T A S C h.diagComm : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : diagE T A S C h.diagComm ≤ Subgroup.centralizer ({y * y} : Set G) :=
      sSup_le fun D' hD' x hx => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hcen D' hD') x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have h1 : y * y ∈ diagE T A S C h.diagComm ⊓
      Subgroup.centralizer ((diagE T A S C h.diagComm : Subgroup G) : Set G) :=
    ⟨Subgroup.mul_mem _ hyY hyY, hY⟩
  rw [diagE, inf_centralizer_eq_bot h.semiFam, Subgroup.mem_bot] at h1
  exact h1

theorem inf_centralizer_le_pCoreOf
    (hcent : Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm = V')
    (hV' : IsKleinFour ↥V') :
    (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
        (T ⊓ Subgroup.centralizer (A : Set G))) ⊓
      Subgroup.centralizer
        ((sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) V') : Subgroup G) : Set G) ≤
      pCoreOf 2 (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
        (T ⊓ Subgroup.centralizer (A : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := T ⊓ Subgroup.centralizer (A : Set G) with hR
  set K := sSup (conjFam R L₀) ⊔ R with hK
  set M := sSup (conjFam R V') with hM
  have hKD : K ≤ diagK T A S C h.diagComm := by
    refine sup_le (sSup_le fun Z hZ => ?_) h.le_diagK
    obtain ⟨k, rfl⟩ := hZ
    have hmem : A1b.conjSub (k : G) (diagSub S C h.diagComm) ∈ diagFam T A S C h.diagComm :=
      ⟨k, rfl⟩
    exact (A1b.conjSub_mono _ hd.L_le).trans ((le_sSup hmem).trans h.diagE_le_diagK)
  have hB : IsPGroup 2 ↥(R.subgroupOf (diagK T A S C h.diagComm)) :=
    (h.isPGroup_T.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe h.le_diagK).symm
  have h2 : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (M : Set G)) := by
    rintro ⟨x, hxK, hxM⟩
    obtain ⟨m, hm⟩ := pow_mem_of_sup h.normal_diagE h.sup_subgroupOf_eq_top hB ⟨x, hKD hxK⟩
    have hxY : x ^ 2 ^ m ∈ diagE T A S C h.diagComm := by
      simpa using Subgroup.mem_subgroupOf.mp hm
    have hxx := mul_self_of_mem_centralizer h hd hcent hV' hxY (Subgroup.pow_mem _ hxM _)
    refine ⟨m + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_succ, pow_mul, pow_two, hxx]
  have hN : K ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (M : Set G) : Subgroup G) : Set G) := by
    intro k hk
    have hkC := normalizer_le_normalizer_centralizer M (K_le_normalizer_M h hd hk)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp hkC x)]
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨K.mul_mem (K.mul_mem hk hx1) (K.inv_mem hk), hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, hx2⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hx1) hk
      simpa [mul_assoc] using this
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN h2

end Diag

end CFSG.Quasithin.E2.E22N.E111L.KMI
