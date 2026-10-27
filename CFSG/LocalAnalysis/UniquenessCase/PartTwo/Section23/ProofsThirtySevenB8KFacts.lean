module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsThirtySevenB8
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.Quasithin.Recognition.St84.L2Group
public import CFSG.Walter.PSL2Facts.TwoGroupBorel
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.Mathlib.FieldTheory.Finite.FixedUnits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.GorensteinWalter CFSG.Walter CFSG.Quasithin.St84
open CFSG.ASVolI CFSG.SeitzReduction.LinearPilot
open scoped MatrixGroups

private theorem one_le_of_isL2 {X : Type} [Group X] {k : ℕ} (h : IsL2 X k) : 1 ≤ k :=
  h.admissible.2.1

private theorem two_le_of_isL2 {X : Type} [Group X] {k : ℕ} (h : IsL2 X k) : 2 ≤ k := by
  have h1 : 1 ≤ k := one_le_of_isL2 h
  have hne : k ≠ 1 := by
    rintro rfl
    exact h.admissible.2.2.2.1 (by norm_num)
  omega

theorem kL2BorelCard_holds : KL2BorelCard := by
  intro X _ _ k hX S
  have hk1 : 1 ≤ k := one_le_of_isL2 hX
  have hk2 : 2 ≤ k := two_le_of_isL2 hX
  obtain ⟨e⟩ := CFSG.Quasithin.H13.nonempty_equiv_psl_of_lieModel hk1 hX
  let U : Sylow 2 (PSL2 (GaloisField 2 k)) :=
    Sylow.mapSurjective (f := (e : X →* PSL2 (GaloisField 2 k))) e.surjective S
  have hUcoe : (U : Subgroup (PSL2 (GaloisField 2 k))) =
      (S : Subgroup X).map (e : X →* PSL2 (GaloisField 2 k)) :=
    Sylow.coe_mapSurjective (f := (e : X →* PSL2 (GaloisField 2 k))) e.surjective S
  have hUcoe' : (U : Subgroup (PSL2 (GaloisField 2 k))) =
      (S : Subgroup X).map e.toMonoidHom := by simpa using hUcoe
  constructor
  · calc
      Nat.card (S : Subgroup X) =
          Nat.card ((S : Subgroup X).map (e : X →* PSL2 (GaloisField 2 k))) :=
        (Subgroup.card_map_of_injective e.injective).symm
      _ = Nat.card (U : Subgroup (PSL2 (GaloisField 2 k))) := by rw [← hUcoe]
      _ = 2 ^ k := psl2_sylow_two_card hk1 U
  · have hmap : (Subgroup.normalizer ((S : Subgroup X) : Set X)).map e.toMonoidHom =
        Subgroup.normalizer (((S : Subgroup X).map e.toMonoidHom : Subgroup
          (PSL2 (GaloisField 2 k))) : Set (PSL2 (GaloisField 2 k))) :=
      Subgroup.map_equiv_normalizer_eq (S : Subgroup X) e
    calc
      Nat.card (Subgroup.normalizer ((S : Subgroup X) : Set X)) =
          Nat.card ((Subgroup.normalizer ((S : Subgroup X) : Set X)).map
            e.toMonoidHom) :=
        (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
      _ = Nat.card (Subgroup.normalizer
            (((S : Subgroup X).map e.toMonoidHom : Subgroup
              (PSL2 (GaloisField 2 k))) : Set (PSL2 (GaloisField 2 k)))) := by
        rw [hmap]
      _ = Nat.card (Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
            Set (PSL2 (GaloisField 2 k)))) := by rw [← hUcoe']
      _ = 2 ^ k * (2 ^ k - 1) :=
        psl2_even_card_normalizer_sylow_two (f := k) (by omega) U

theorem kL2BorelComm_holds : KL2BorelComm := by
  intro X _ _ k hX S x hx y hy
  have hk1 : 1 ≤ k := one_le_of_isL2 hX
  have hk2 : 2 ≤ k := two_le_of_isL2 hX
  obtain ⟨e⟩ := CFSG.Quasithin.H13.nonempty_equiv_psl_of_lieModel hk1 hX
  let U : Sylow 2 (PSL2 (GaloisField 2 k)) :=
    Sylow.mapSurjective (f := (e : X →* PSL2 (GaloisField 2 k))) e.surjective S
  have hUcoe : (U : Subgroup (PSL2 (GaloisField 2 k))) =
      (S : Subgroup X).map (e : X →* PSL2 (GaloisField 2 k)) :=
    Sylow.coe_mapSurjective (f := (e : X →* PSL2 (GaloisField 2 k))) e.surjective S
  have hUcoe' : (U : Subgroup (PSL2 (GaloisField 2 k))) =
      (S : Subgroup X).map e.toMonoidHom := by simpa using hUcoe
  let N : Subgroup (PSL2 (GaloisField 2 k)) :=
    Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
      Set (PSL2 (GaloisField 2 k)))
  have hxN : e x ∈ N := by
    change e x ∈ Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
      Set (PSL2 (GaloisField 2 k)))
    rw [hUcoe']
    exact Subgroup.le_normalizer_map e.toMonoidHom
      (Subgroup.mem_map_of_mem e.toMonoidHom hx)
  have hyN : e y ∈ N := by
    change e y ∈ Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
      Set (PSL2 (GaloisField 2 k)))
    rw [hUcoe']
    exact Subgroup.le_normalizer_map e.toMonoidHom
      (Subgroup.mem_map_of_mem e.toMonoidHom hy)
  haveI : (U.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  haveI hQcyc : IsCyclic (N ⧸ U.subgroupOf N) :=
    psl2_normalizer_quotient_cyclic hk2 U
  let π : N →* N ⧸ U.subgroupOf N := QuotientGroup.mk' _
  have hπ : π (⟨e x, hxN⟩ * ⟨e y, hyN⟩ * ⟨e x, hxN⟩⁻¹ * ⟨e y, hyN⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    letI : CommGroup (N ⧸ U.subgroupOf N) := IsCyclic.commGroup
    rw [mul_comm (π ⟨e x, hxN⟩) (π ⟨e y, hyN⟩)]
    group
  have hmemN : (⟨e x, hxN⟩ * ⟨e y, hyN⟩ * ⟨e x, hxN⟩⁻¹ * ⟨e y, hyN⟩⁻¹ : N) ∈
      U.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff]
    exact hπ
  have hmemU : e (x * y * x⁻¹ * y⁻¹) ∈ (U : Subgroup (PSL2 (GaloisField 2 k))) := by
    have hcoe : ((⟨e x, hxN⟩ * ⟨e y, hyN⟩ * ⟨e x, hxN⟩⁻¹ * ⟨e y, hyN⟩⁻¹ : N) :
        PSL2 (GaloisField 2 k)) ∈ U := Subgroup.mem_subgroupOf.mp hmemN
    have hval : ((⟨e x, hxN⟩ * ⟨e y, hyN⟩ * ⟨e x, hxN⟩⁻¹ * ⟨e y, hyN⟩⁻¹ : N) :
        PSL2 (GaloisField 2 k)) = e (x * y * x⁻¹ * y⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rwa [hval] at hcoe
  rw [hUcoe'] at hmemU
  have hmemS : e.symm (e (x * y * x⁻¹ * y⁻¹)) ∈ (S : Subgroup X) :=
    (Subgroup.mem_map_equiv (f := e) (K := (S : Subgroup X))
      (x := e (x * y * x⁻¹ * y⁻¹))).1 hmemU
  simpa using hmemS

theorem kL2TorusSelfCent_holds :
    ∀ (X : Type) [Group X] [Finite X] (k : ℕ), IsL2 X k → ∀ (S : Sylow 2 X)
      (H : Subgroup X), H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) →
        Nat.card H = 2 ^ k - 1 → IsCyclic H ∧ Subgroup.centralizer (H : Set X) ≤ H := by
  intro X _ _ k hX S H hH hHcard
  have hk1 : 1 ≤ k := one_le_of_isL2 hX
  have hk2 : 2 ≤ k := two_le_of_isL2 hX
  obtain ⟨e⟩ := CFSG.Quasithin.H13.nonempty_equiv_psl_of_lieModel hk1 hX
  let U : Sylow 2 (PSL2 (GaloisField 2 k)) :=
    Sylow.mapSurjective (f := (e : X →* PSL2 (GaloisField 2 k))) e.surjective S
  have hUcoe : (U : Subgroup (PSL2 (GaloisField 2 k))) =
      (S : Subgroup X).map (e : X →* PSL2 (GaloisField 2 k)) :=
    Sylow.coe_mapSurjective (f := (e : X →* PSL2 (GaloisField 2 k))) e.surjective S
  let H' : Subgroup (PSL2 (GaloisField 2 k)) :=
    H.map (e : X →* PSL2 (GaloisField 2 k))
  have hH'card : Nat.card H' = 2 ^ k - 1 := by
    rw [show Nat.card H' = Nat.card H from
      Subgroup.card_map_of_injective (f := (e : X →* PSL2 (GaloisField 2 k))) e.injective,
      hHcard]
  have hH'N : H' ≤ Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
      Set (PSL2 (GaloisField 2 k))) := by
    have h1 : H' ≤ (Subgroup.normalizer ((S : Subgroup X) : Set X)).map
        (e : X →* PSL2 (GaloisField 2 k)) := Subgroup.map_mono hH
    have h2 : (Subgroup.normalizer ((S : Subgroup X) : Set X)).map
        (e : X →* PSL2 (GaloisField 2 k)) ≤ Subgroup.normalizer
          (((S : Subgroup X).map (e : X →* PSL2 (GaloisField 2 k))) :
            Set (PSL2 (GaloisField 2 k))) := Subgroup.le_normalizer_map _
    rw [← hUcoe] at h2
    exact h1.trans h2
  have hUcard : Nat.card (U : Subgroup (PSL2 (GaloisField 2 k))) = 2 ^ k :=
    psl2_sylow_two_card hk1 U
  have hH'odd : Odd (Nat.card H') := by
    rw [hH'card]
    exact Nat.Even.sub_odd (Nat.two_pow_pos k)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hH'odd' : Odd (2 ^ k - 1) := by
    rw [← hH'card]
    exact hH'odd
  have hHU : H' ⊓ (U : Subgroup (PSL2 (GaloisField 2 k))) = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by
      rw [hH'card, hUcard]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hH'odd'))
  have hNcard : Nat.card (Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
      Set (PSL2 (GaloisField 2 k)))) = 2 ^ k * (2 ^ k - 1) :=
    psl2_even_card_normalizer_sylow_two (f := k) (by omega) U
  have hsupcard : Nat.card ↥(H' ⊔ (U : Subgroup (PSL2 (GaloisField 2 k)))) =
      Nat.card (Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
        Set (PSL2 (GaloisField 2 k)))) := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := H') (K := (U : Subgroup (PSL2 (GaloisField 2 k)))) hH'N
    rw [hHU, Subgroup.card_bot, mul_one] at h
    rw [h, hH'card, hUcard, hNcard]
    ring
  have hsup : H' ⊔ (U : Subgroup (PSL2 (GaloisField 2 k))) =
      Subgroup.normalizer ((U : Subgroup (PSL2 (GaloisField 2 k))) :
        Set (PSL2 (GaloisField 2 k))) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hH'N Subgroup.le_normalizer) ?_
    rw [hsupcard]
  have hcyc' : IsCyclic H' := psl2_torus_cyclic hk1 hHU hsup
  have hcent' : Subgroup.centralizer (H' : Set (PSL2 (GaloisField 2 k))) = H' :=
    psl2_torus_centralizer hk2 hHU hsup
  constructor
  · exact (Subgroup.equivMapOfInjective H (e : X →* PSL2 (GaloisField 2 k))
      e.injective).isCyclic.mpr hcyc'
  · intro c hc
    have hce : e c ∈ Subgroup.centralizer (H' : Set (PSL2 (GaloisField 2 k))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
      have hch : h * c = c * h := (Subgroup.mem_centralizer_iff.mp hc) h hh
      calc
        e h * e c = e (h * c) := by rw [map_mul]
        _ = e (c * h) := by rw [hch]
        _ = e c * e h := by rw [map_mul]
    rw [hcent'] at hce
    obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp hce
    have hch : h = c := e.injective heq
    rwa [← hch]

private theorem psl2_fieldAut_diag_eq_of_mem_borel_mod_upper
    {K : Type} [Field K] [Finite K] {k : ℕ} (hK : Nat.card K = 2 ^ k) (hk1 : 1 ≤ k)
    {θ : MulAut (PSL2 K)} {u₀ d₀ : PSL2 K} {σ : K ≃+* K}
    (hu₀ : u₀ ∈ psl2UpperUnipotentSubgroup K)
    (hd₀ : d₀ ∈ burnsideAut_psl2Diag K)
    (hfac : θ = MulAut.conj u₀ * (MulAut.conj d₀ * psl2FieldAut K σ))
    {u d : PSL2 K} (hu : u ∈ psl2UpperUnipotentSubgroup K)
    (hd : d ∈ burnsideAut_psl2Diag K)
    (hcent : θ (u * d) * (u * d)⁻¹ ∈ psl2UpperUnipotentSubgroup K) :
    psl2FieldAut K σ d = d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card K Nat.prime_two hK
  let U := psl2UpperUnipotentSubgroup K
  let D := burnsideAut_psl2Diag K
  have hU2 : IsPGroup 2 U := by
    change IsPGroup 2 (psl2UpperUnipotentSubgroup K)
    refine IsPGroup.of_card (n := k) ?_
    rw [psl2UpperUnipotentSubgroup_card, hK]
  have hDodd : Odd (Nat.card D) := by
    change Odd (Nat.card (burnsideAut_psl2Diag K))
    exact burnsideAut_card_psl2Diag_odd hk1 hK
  have hUD : U ⊓ D = ⊥ := by
    change psl2UpperUnipotentSubgroup K ⊓ burnsideAut_psl2Diag K = ⊥
    exact CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hU2 hDodd
  have hdN : d ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    change d ∈ Subgroup.normalizer ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K))
    rw [psl2UpperUnipotent_normalizer_eq_borel]
    exact burnsideAut_psl2Diag_le_borel hd
  have hd₀N : d₀ ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    change d₀ ∈ Subgroup.normalizer ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K))
    rw [psl2UpperUnipotent_normalizer_eq_borel]
    exact burnsideAut_psl2Diag_le_borel hd₀
  have hσu : psl2FieldAut K σ u ∈ U := by
    change psl2FieldAut K σ u ∈ psl2UpperUnipotentSubgroup K
    rw [← burnsideAut_map_psl2FieldAut_upper σ]
    exact Subgroup.mem_map_of_mem _ hu
  have hσdD : psl2FieldAut K σ d ∈ D := by
    change psl2FieldAut K σ d ∈ burnsideAut_psl2Diag K
    rw [← burnsideAut_map_psl2FieldAut_diag σ]
    exact Subgroup.mem_map_of_mem _ hd
  have hσdN : psl2FieldAut K σ d ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    change psl2FieldAut K σ d ∈ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K))
    rw [psl2UpperUnipotent_normalizer_eq_borel]
    exact burnsideAut_psl2Diag_le_borel hσdD
  have hcomm : d₀ * psl2FieldAut K σ d * d₀⁻¹ = psl2FieldAut K σ d := by
    rw [burnsideAut_psl2Diag_comm hd₀ hσdD]
    group
  let A : PSL2 K := u₀ * (d₀ * psl2FieldAut K σ u * d₀⁻¹) * u₀⁻¹
  let C : PSL2 K := u₀ * (psl2FieldAut K σ d * u₀⁻¹ * (psl2FieldAut K σ d)⁻¹)
  have hA : A ∈ U := by
    change u₀ * (d₀ * psl2FieldAut K σ u * d₀⁻¹) * u₀⁻¹ ∈ U
    refine Subgroup.mul_mem (H := U) (Subgroup.mul_mem (H := U) hu₀ ?_)
      (Subgroup.inv_mem (H := U) hu₀)
    exact (Subgroup.mem_normalizer_iff.mp hd₀N (psl2FieldAut K σ u)).1 hσu
  have hC : C ∈ U := by
    change u₀ * (psl2FieldAut K σ d * u₀⁻¹ * (psl2FieldAut K σ d)⁻¹) ∈ U
    exact Subgroup.mul_mem (H := U) hu₀
      ((Subgroup.mem_normalizer_iff.mp hσdN u₀⁻¹).1 (Subgroup.inv_mem (H := U) hu₀))
  have hθ : θ (u * d) = (A * C) * psl2FieldAut K σ d := by
    rw [hfac]
    simp only [MulAut.mul_apply]
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul]
    rw [show u₀ * (d₀ * (psl2FieldAut K σ u * psl2FieldAut K σ d) * d₀⁻¹) * u₀⁻¹ =
          u₀ * (d₀ * psl2FieldAut K σ u * d₀⁻¹) *
            (d₀ * psl2FieldAut K σ d * d₀⁻¹) * u₀⁻¹ by group]
    rw [hcomm]
    dsimp only [A, C]
    group
  have hE : psl2FieldAut K σ d * d⁻¹ ∈ D :=
    Subgroup.mul_mem (H := D) hσdD (Subgroup.inv_mem (H := D) hd)
  have hEN : psl2FieldAut K σ d * d⁻¹ ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    change psl2FieldAut K σ d * d⁻¹ ∈ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K))
    rw [psl2UpperUnipotent_normalizer_eq_borel]
    exact burnsideAut_psl2Diag_le_borel hE
  have hEupper : psl2FieldAut K σ d * d⁻¹ ∈ U := by
    let E : PSL2 K := psl2FieldAut K σ d * d⁻¹
    have hC2 : E * u⁻¹ * E⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hEN u⁻¹).1 (Subgroup.inv_mem _ hu)
    have htotal : (A * C) * E * u⁻¹ ∈ U := by
      have h := hcent
      rw [hθ] at h
      convert h using 1
      dsimp only [E]
      group
    have hcoef : (A * C) * (E * u⁻¹ * E⁻¹) ∈ U :=
      Subgroup.mul_mem (H := U) (Subgroup.mul_mem (H := U) hA hC) hC2
    have hEeq : E = ((A * C) * (E * u⁻¹ * E⁻¹))⁻¹ * ((A * C) * E * u⁻¹) := by
      group
    change E ∈ U
    rw [hEeq]
    exact Subgroup.mul_mem (H := U) (Subgroup.inv_mem (H := U) hcoef) htotal
  have hE1 : psl2FieldAut K σ d * d⁻¹ = 1 := by
    have hmem : psl2FieldAut K σ d * d⁻¹ ∈ U ⊓ D := ⟨hEupper, hE⟩
    rw [hUD] at hmem
    simpa using hmem
  exact mul_inv_eq_one.mp hE1

private theorem psl2_odd_aut_inner_of_fixed_torus
    {K : Type} [Field K] [Finite K] {k e m : ℕ} (hK : Nat.card K = 2 ^ k)
    (hk2 : 2 ≤ k) (hkm : k = 2 ^ e * m)
    {θ : MulAut (PSL2 K)} (hodd : Odd (orderOf θ))
    (S : Sylow 2 (PSL2 K))
    (hS : ∀ x ∈ (S : Subgroup (PSL2 K)), θ x ∈ (S : Subgroup (PSL2 K)))
    (H : Subgroup (PSL2 K))
    (hH : H ≤ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K)))
    (hHcard : Nat.card H = 2 ^ m - 1)
    (hfix : ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup (PSL2 K))) :
    θ ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range := by
  have hk1 : 1 ≤ k := by omega
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, mul_zero] at hkm
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card K Nat.prime_two hK
  let U := psl2UpperUnipotentSubgroup K
  let D := burnsideAut_psl2Diag K
  have hUcard : Nat.card U = 2 ^ k := by
    change Nat.card (psl2UpperUnipotentSubgroup K) = 2 ^ k
    rw [psl2UpperUnipotentSubgroup_card, hK]
  have hU2 : IsPGroup 2 U := by
    change IsPGroup 2 (psl2UpperUnipotentSubgroup K)
    refine IsPGroup.of_card (n := k) ?_
    rw [psl2UpperUnipotentSubgroup_card, hK]
  have hDodd : Odd (Nat.card D) := by
    change Odd (Nat.card (burnsideAut_psl2Diag K))
    exact burnsideAut_card_psl2Diag_odd hk1 hK
  have hUD : U ⊓ D = ⊥ := by
    change psl2UpperUnipotentSubgroup K ⊓ burnsideAut_psl2Diag K = ⊥
    exact CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hU2 hDodd
  obtain ⟨h₀, hhU⟩ := exists_conj_upper_of_sylow hK S
  let θ₁ : MulAut (PSL2 K) := (MulAut.conj h₀)⁻¹ * θ * MulAut.conj h₀
  have hθ₁eq : θ₁ = MulAut.conj (MulAut.conj h₀)⁻¹ θ := by
    rw [MulAut.conj_apply, inv_inv]
  have hθ₁U : U.map θ₁.toMonoidHom = U := by
    rw [hθ₁eq]
    exact conj_theta_maps_upper hhU hS
  have hθ₁odd : Odd (orderOf θ₁) := by
    rw [hθ₁eq, MulEquiv.orderOf_eq]
    exact hodd
  obtain ⟨u₀, d₀, σ, hu₀, hd₀, hfac⟩ := exists_factorization_of_normalizes_upper hK hθ₁U
  have hσθ₁ : psl2FieldPart K θ₁ = σ := by
    rw [hfac, map_mul, map_mul, psl2FieldPart_conj, psl2FieldPart_conj,
      psl2FieldPart_psl2FieldAut, one_mul, one_mul]
  have hσodd : Odd (orderOf σ) := by
    rw [← hσθ₁]
    exact Odd.of_dvd_nat hθ₁odd (orderOf_map_dvd (psl2FieldPart K) θ₁)
  have hSinv : (S : Subgroup (PSL2 K)).map (MulAut.conj h₀).symm.toMonoidHom = U :=
    (Subgroup.map_symm_eq_iff_map_eq (K := U) (H := (S : Subgroup (PSL2 K)))
      (e := MulAut.conj h₀)).2 hhU
  let H₁ : Subgroup (PSL2 K) := H.map (MulAut.conj h₀).symm.toMonoidHom
  have hH₁card : Nat.card H₁ = 2 ^ m - 1 := by
    rw [show Nat.card H₁ = Nat.card H from
      Subgroup.card_map_of_injective (f := (MulAut.conj h₀).symm.toMonoidHom)
        (MulAut.conj h₀).symm.injective, hHcard]
  have hH₁N : H₁ ≤ Subgroup.normalizer (U : Set (PSL2 K)) := by
    have h1 : H₁ ≤ (Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))).map
        (MulAut.conj h₀).symm.toMonoidHom := Subgroup.map_mono hH
    have h2 : (Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))).map
        (MulAut.conj h₀).symm.toMonoidHom ≤
        Subgroup.normalizer (((S : Subgroup (PSL2 K)).map
          (MulAut.conj h₀).symm.toMonoidHom) : Set (PSL2 K)) :=
      Subgroup.le_normalizer_map _
    rw [hSinv] at h2
    exact h1.trans h2
  have hH₁B : H₁ ≤ psl2Borel K := by
    rw [← psl2UpperUnipotent_normalizer_eq_borel]
    exact hH₁N
  have hH₁odd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd (Nat.two_pow_pos m)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hH₁U : H₁ ⊓ U = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by
      rw [hH₁card, hUcard]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hH₁odd))
  have hfix₁ : ∀ h ∈ H₁, θ₁ h * h⁻¹ ∈ U := by
    intro h hh
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
    have hmem : (MulAut.conj h₀)⁻¹ (θ h' * h'⁻¹) ∈ U := by
      rw [← hSinv]
      exact Subgroup.mem_map_of_mem _ (hfix h' hh')
    have hcalc : θ₁ ((MulAut.conj h₀)⁻¹ h') *
        ((MulAut.conj h₀)⁻¹ h')⁻¹ = (MulAut.conj h₀)⁻¹ (θ h' * h'⁻¹) := by
      simp only [θ₁, MulAut.mul_apply]
      rw [MulAut.apply_inv_self, map_mul, map_inv]
    change θ₁ ((MulAut.conj h₀)⁻¹ h') * ((MulAut.conj h₀)⁻¹ h')⁻¹ ∈ U
    rw [hcalc]
    exact hmem
  choose u d hu hd hud using fun h : H₁ =>
    exists_mul_mem_upper_diag_of_mem_borel (hH₁B h.2)
  choose lam hlam using fun h : H₁ => MonoidHom.mem_range.mp (hd h)
  have hσd : ∀ h : H₁, psl2FieldAut K σ (d h) = d h := by
    intro h
    refine psl2_fieldAut_diag_eq_of_mem_borel_mod_upper hK hk1 hu₀ hd₀ hfac
      (hu h) (hd h) ?_
    simpa [hud h] using hfix₁ (h : PSL2 K) h.2
  have hinj : Function.Injective
      ((psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K)) :=
    (psl2QuotientMap_injective_of_charTwo (K := K)).comp (burnsideAut_sl2DiagHom_injective K)
  have hσlam : ∀ h : H₁, Units.map (σ : K →* K) (lam h) = lam h := by
    intro h
    have hσd' := hσd h
    rw [← hlam h] at hσd'
    apply hinj
    show psl2QuotientMap K (burnsideAut_sl2DiagHom K
      (Units.map (σ : K →* K) (lam h))) =
        psl2QuotientMap K (burnsideAut_sl2DiagHom K (lam h))
    rw [← CFSG.ASVolI.burnsideAut_psl2FieldAut_diag σ (lam h)]
    exact hσd'
  obtain ⟨s, hsdvd, hsdiv, y, hyord, -, hygen⟩ :=
    CFSG.exists_zpowers_eq_fixed_units (p := 2) (a := k) hK σ
  let Dy : Subgroup (PSL2 K) :=
    (Subgroup.zpowers y).map ((psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K))
  have hDycard : Nat.card Dy = 2 ^ s - 1 := by
    rw [show Nat.card Dy = Nat.card (Subgroup.zpowers y) from
      Subgroup.card_map_of_injective (f := (psl2QuotientMap K).comp
        (burnsideAut_sl2DiagHom K)) hinj, Nat.card_zpowers, hyord]
  have hlam_mem : ∀ h : H₁, lam h ∈ Subgroup.zpowers y := fun h =>
    hygen (lam h) (congrArg Units.val (hσlam h))
  let f : H₁ → Dy := fun h =>
    ⟨psl2QuotientMap K (burnsideAut_sl2DiagHom K (lam h)),
      Subgroup.mem_map_of_mem ((psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K))
        (hlam_mem h)⟩
  have huniq : ∀ {u u' d d' : PSL2 K}, u ∈ U → u' ∈ U → d ∈ D → d' ∈ D →
      u * d = u' * d' → d = d' ∧ u = u' := by
    intro u u' d d' hu hu' hd hd' heq
    have hmem : u'⁻¹ * u ∈ U ⊓ D := by
      constructor
      · exact Subgroup.mul_mem (H := U) (Subgroup.inv_mem (H := U) hu') hu
      · have hEq : u'⁻¹ * u = d' * d⁻¹ := by
          calc u'⁻¹ * u = u'⁻¹ * (u * d) * d⁻¹ := by group
            _ = u'⁻¹ * (u' * d') * d⁻¹ := by rw [heq]
            _ = d' * d⁻¹ := by group
        rw [hEq]
        exact Subgroup.mul_mem (H := D) hd' (Subgroup.inv_mem (H := D) hd)
    rw [hUD] at hmem
    have h1 : u'⁻¹ * u = 1 := by simpa using hmem
    have hu_eq : u = u' := by
      calc u = u' * (u'⁻¹ * u) := by group
        _ = u' * 1 := by rw [h1]
        _ = u' := mul_one _
    have hd_eq : d = d' := by
      have h := heq
      rw [hu_eq] at h
      exact mul_left_cancel h
    exact ⟨hd_eq, hu_eq⟩
  have hf_one : f 1 = 1 := by
    apply Subtype.ext
    change (f 1 : PSL2 K) = 1
    rw [show (f 1 : PSL2 K) = d 1 from hlam 1]
    have h_one : d 1 = 1 := by
      have heq : (1 : PSL2 K) * 1 = u 1 * d 1 := by
        simpa using (hud 1).symm
      exact ((huniq (Subgroup.one_mem _) (hu 1) (Subgroup.one_mem _) (hd 1) heq).1).symm
    rw [h_one]
  have hf_mul : ∀ h1 h2 : H₁, f (h1 * h2) = f h1 * f h2 := by
    intro h1 h2
    have hd_eq : d (h1 * h2) = d h1 * d h2 := by
      have heq : (u h1 * (d h1 * u h2 * (d h1)⁻¹)) * (d h1 * d h2) =
          u (h1 * h2) * d (h1 * h2) := by
        calc (u h1 * (d h1 * u h2 * (d h1)⁻¹)) * (d h1 * d h2)
            = (u h1 * d h1) * (u h2 * d h2) := by group
          _ = (h1 : PSL2 K) * (h2 : PSL2 K) := by rw [hud h1, hud h2]
          _ = ((h1 * h2 : H₁) : PSL2 K) := by rw [Subgroup.coe_mul]
          _ = u (h1 * h2) * d (h1 * h2) := (hud (h1 * h2)).symm
      have hu_mem : u h1 * (d h1 * u h2 * (d h1)⁻¹) ∈ U := by
        have h1' : d h1 * u h2 * (d h1)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp
            ((by
              rw [psl2UpperUnipotent_normalizer_eq_borel]
              exact burnsideAut_psl2Diag_le_borel (hd h1)) :
              d h1 ∈ Subgroup.normalizer (U : Set (PSL2 K))) (u h2)).1 (hu h2)
        exact Subgroup.mul_mem (H := U) (hu h1) h1'
      exact ((huniq hu_mem (hu (h1 * h2)) (Subgroup.mul_mem (H := D) (hd h1) (hd h2))
        (hd (h1 * h2)) heq).1).symm
    apply Subtype.ext
    change (f (h1 * h2) : PSL2 K) = (f h1 : PSL2 K) * (f h2 : PSL2 K)
    rw [show (f (h1 * h2) : PSL2 K) = d (h1 * h2) from hlam (h1 * h2),
      show (f h1 : PSL2 K) = d h1 from hlam h1,
      show (f h2 : PSL2 K) = d h2 from hlam h2, hd_eq]
  let fHom : H₁ →* Dy :=
    { toFun := f, map_one' := hf_one, map_mul' := hf_mul }
  have hf_inj : Function.Injective f := by
    intro h1 h2 heq
    have hd_eq : d h1 = d h2 := by
      have h := congrArg Subtype.val heq
      rwa [show (f h1 : PSL2 K) = d h1 from hlam h1,
        show (f h2 : PSL2 K) = d h2 from hlam h2] at h
    apply Subtype.ext
    have hmem : (h1 : PSL2 K) * (h2 : PSL2 K)⁻¹ ∈ H₁ ⊓ U := by
      constructor
      · exact H₁.mul_mem h1.2 (H₁.inv_mem h2.2)
      · have hprod : (h1 : PSL2 K) * (h2 : PSL2 K)⁻¹ = u h1 * (u h2)⁻¹ := by
          rw [← hud h1, ← hud h2, hd_eq]
          group
        rw [hprod]
        exact Subgroup.mul_mem (H := U) (hu h1) (Subgroup.inv_mem (H := U) (hu h2))
    rw [hH₁U] at hmem
    have h1eq : (h1 : PSL2 K) = h2 := by
      have h1' : (h1 : PSL2 K) * (h2 : PSL2 K)⁻¹ = 1 := by simpa using hmem
      exact mul_inv_eq_one.mp h1'
    exact h1eq
  have hcardim : Nat.card (MonoidHom.range fHom) = Nat.card H₁ :=
    (Nat.card_congr (MonoidHom.ofInjective hf_inj).toEquiv).symm
  have hdvd : Nat.card H₁ ∣ Nat.card Dy := by
    rw [← hcardim]
    exact Subgroup.card_subgroup_dvd_card (MonoidHom.range fHom)
  have hdy : 2 ^ m - 1 ∣ 2 ^ s - 1 := by
    rw [← hH₁card, ← hDycard]
    exact hdvd
  have hm_dvd_s : m ∣ s :=
    CFSG.ShultStronglyClosedTI.CyclicSemiregular.two_pow_sub_one_dvd_iff.mp hdy
  obtain ⟨t, ht⟩ := hm_dvd_s
  have hk_eq : k = s * orderOf σ := by
    rw [← hsdiv]
    exact (Nat.mul_div_cancel' hsdvd).symm
  have htd : orderOf σ ∣ 2 ^ e := by
    have h1 : m * 2 ^ e = m * (t * orderOf σ) := by
      calc m * 2 ^ e = 2 ^ e * m := by ring
        _ = k := hkm.symm
        _ = s * orderOf σ := hk_eq
        _ = (m * t) * orderOf σ := by rw [ht]
        _ = m * (t * orderOf σ) := by ring
    have h2 := Nat.eq_of_mul_eq_mul_left hmpos h1
    exact ⟨t, h2.trans (mul_comm t (orderOf σ))⟩
  have hd1 : orderOf σ = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hσodd)) htd
  have hσ1 : σ = 1 := orderOf_eq_one_iff.mp hd1
  have hθ₁inner : θ₁ ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range := by
    refine ⟨u₀ * d₀, ?_⟩
    rw [hfac, hσ1, map_one, mul_one, map_mul]
  obtain ⟨z, hz⟩ := hθ₁inner
  refine ⟨h₀ * z * h₀⁻¹, ?_⟩
  have hθeq : θ = MulAut.conj h₀ * θ₁ * (MulAut.conj h₀)⁻¹ := by
    simp only [θ₁]
    group
  rw [hθeq, map_mul, map_mul, map_inv, hz]

theorem kL2OddAutInner_holds :
    ∀ (X : Type) [Group X] [Finite X] (e m : ℕ), IsL2 X (2 ^ e * m) →
      ∀ (S : Sylow 2 X) (θ : MulAut X), Odd (orderOf θ) →
        (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
        ∀ H : Subgroup X, H ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) →
          Nat.card H = 2 ^ m - 1 → (∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup X)) →
          θ ∈ (MulAut.conj : X →* MulAut X).range := by
  intro X _ _ e m hX S θ hodd hθS H hH hHcard hfix
  have hk1 : 1 ≤ 2 ^ e * m := one_le_of_isL2 hX
  have hk2 : 2 ≤ 2 ^ e * m := two_le_of_isL2 hX
  obtain ⟨eX⟩ := CFSG.Quasithin.H13.nonempty_equiv_psl_of_lieModel hk1 hX
  let S' : Sylow 2 (PSL2 (GaloisField 2 (2 ^ e * m))) :=
    Sylow.mapSurjective (f := (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m))))
      eX.surjective S
  have hS'coe : (S' : Subgroup (PSL2 (GaloisField 2 (2 ^ e * m)))) =
      (S : Subgroup X).map (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m))) :=
    Sylow.coe_mapSurjective (f := (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m))))
      eX.surjective S
  let θ' : MulAut (PSL2 (GaloisField 2 (2 ^ e * m))) := MulAut.congr eX θ
  have hθ'odd : Odd (orderOf θ') := by
    rw [show θ' = MulAut.congr eX θ from rfl, MulEquiv.orderOf_eq]
    exact hodd
  have hθ'S : ∀ x ∈ (S' : Subgroup (PSL2 (GaloisField 2 (2 ^ e * m)))),
      θ' x ∈ (S' : Subgroup (PSL2 (GaloisField 2 (2 ^ e * m)))) := by
    intro x hx
    rw [hS'coe] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [θ', MulAut.congr_apply] using
      (Subgroup.mem_map_of_mem (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m)))
        (hθS y hy))
  let H' : Subgroup (PSL2 (GaloisField 2 (2 ^ e * m))) :=
    H.map (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m)))
  have hH'card : Nat.card H' = 2 ^ m - 1 := by
    rw [show Nat.card H' = Nat.card H from
      Subgroup.card_map_of_injective (f := (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m))))
        eX.injective, hHcard]
  have hH'N : H' ≤ Subgroup.normalizer
      ((S' : Subgroup (PSL2 (GaloisField 2 (2 ^ e * m)))) :
        Set (PSL2 (GaloisField 2 (2 ^ e * m)))) := by
    have h1 : H' ≤ (Subgroup.normalizer ((S : Subgroup X) : Set X)).map
        (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m))) := Subgroup.map_mono hH
    have h2 : (Subgroup.normalizer ((S : Subgroup X) : Set X)).map
        (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m))) ≤ Subgroup.normalizer
          (((S : Subgroup X).map (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m)))) :
            Set (PSL2 (GaloisField 2 (2 ^ e * m)))) := Subgroup.le_normalizer_map _
    rw [← hS'coe] at h2
    exact h1.trans h2
  have hH'fix : ∀ h ∈ H', θ' h * h⁻¹ ∈
      (S' : Subgroup (PSL2 (GaloisField 2 (2 ^ e * m)))) := by
    intro h hh
    rw [hS'coe]
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    simpa [θ', MulAut.congr_apply, map_mul, map_inv] using
      (Subgroup.mem_map_of_mem (eX : X →* PSL2 (GaloisField 2 (2 ^ e * m)))
        (hfix y hy))
  have hKcard : Nat.card (GaloisField 2 (2 ^ e * m)) = 2 ^ (2 ^ e * m) :=
    GaloisField.card 2 (2 ^ e * m) (by omega)
  have hinner := psl2_odd_aut_inner_of_fixed_torus hKcard hk2 rfl hθ'odd S' hθ'S H'
    hH'N hH'card hH'fix
  obtain ⟨z, hz⟩ := hinner
  refine ⟨eX.symm z, ?_⟩
  have hθ : θ = MulAut.congr eX.symm θ' := by
    ext x
    simp [θ', MulAut.congr_apply]
  rw [hθ, ← hz, CFSG.mulAut_congr_conj]

end CFSG.LocalAnalysis.UniquenessCase.UC22
