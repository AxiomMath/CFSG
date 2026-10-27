module

public import CFSG.Quasithin.EmptyFaithful.E22PTor
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IF
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3PGL
public import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
public import CFSG.Walter.Bender1970.S3.Tools
import CFSG.GroupTheory.SolvableTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.E22L2

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_normal
  pslRange_index_eq_two)

private theorem card_sup_zpowers_eq_two_mul {G : Type*} [Group G] {U : Subgroup G} {w : G}
    (hw2 : w * w = 1) (hwU : w ∉ U)
    (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) :
    Nat.card ↥(U ⊔ Subgroup.zpowers w) = Nat.card ↥U * 2 := by
  have hw1 : w ≠ 1 := by
    intro h
    exact hwU (h ▸ U.one_mem)
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hKcard : Nat.card ↥(Subgroup.zpowers w) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.zpowers_le_normalizer_of_inverting
      hw2 hwinv
  have hdisj : Disjoint U (Subgroup.zpowers w) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxU, hxK⟩ := hx
    rcases e22pl2pgl_mem_zpowers_involution hw2 hxK with h | h
    · exact h
    · exact absurd (h ▸ hxU) hwU
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U
    (Subgroup.zpowers w) hnorm hdisj, hKcard]

private theorem tauOf_eq_of_self_centralizer {G : Type*} [Group G] {T A : Subgroup G}
    (hTA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥)
    (hcent : Subgroup.centralizer (A : Set G) = A) :
    tauOf ⊤ T A = A := by
  apply le_antisymm
  · intro t ht
    rw [mem_tauOf_of_le le_top] at ht
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro a ha
    have hcomm : ⁅t, a⁆ ∈ pCoreOf 2 (⊤ : Subgroup G) := ht.2 a ha
    rw [hO2] at hcomm
    have h1 : t * a * t⁻¹ * a⁻¹ = 1 := by
      simpa [commutatorElement_def] using (Subgroup.mem_bot.mp hcomm)
    have h2 : t * a = a * t := by
      calc t * a = (t * a * t⁻¹ * a⁻¹) * (a * t) := by group
        _ = 1 * (a * t) := by rw [h1]
        _ = a * t := by group
    exact h2.symm
  · intro a ha
    rw [mem_tauOf_of_le le_top]
    refine ⟨hTA ha, ?_⟩
    intro a' ha'
    have hcomm : a * a' = a' * a :=
      congrArg Subtype.val (hAab.1.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨a', ha'⟩)
    have h1 : ⁅a, a'⁆ = 1 := by
      rw [commutatorElement_def, hcomm]
      group
    rw [h1, hO2]
    exact Subgroup.mem_bot.mpr rfl


private theorem pgl2_centralizer_inner_involution_isCoatom_all
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p) (hp : 5 < p)
    {z : PGL2 K} (hz : orderOf z = 2) (hzJ : z ∈ commutator (PGL2 K)) :
    IsCoatom (Subgroup.centralizer ({z} : Set (PGL2 K))) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hp_prime : p.Prime := Fact.out
  by_cases hp7 : p = 7
  · have hK7 : Nat.card K = 7 := by rw [hK, hp7]
    subst p
    exact pgl2_centralizer_inner_involution_isCoatom_seven hK7 hz hzJ
  · have hp11 : 11 ≤ p := by
      by_contra h
      have hp10 : p ≤ 10 := by omega
      interval_cases p <;> first | exact absurd rfl hp7 | norm_num at hp_prime
    have hp_mod8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
      have hlt : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
      omega
    rcases hp_mod8 with h1 | h3 | h5 | h7
    · have hp17 : 17 ≤ p := by
        by_contra h
        have hp16 : p ≤ 16 := by omega
        interval_cases p <;> first | omega | norm_num at hp_prime
      exact pgl2_centralizer_inner_involution_isCoatom hK (Or.inl h1) hp17 hz hzJ
    · exact CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.pgl2_centralizer_inner_involution_isCoatom_pm_three hK (Or.inl h3) hp11 hz hzJ
    · exact CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.pgl2_centralizer_inner_involution_isCoatom_pm_three hK (Or.inr h5) hp11 hz hzJ
    · have hp17 : 17 ≤ p := by
        by_contra h
        have hp16 : p ≤ 16 := by omega
        interval_cases p <;> first | omega | norm_num at hp_prime
      exact pgl2_centralizer_inner_involution_isCoatom hK (Or.inr h7) hp17 hz hzJ


private theorem int_modEq_neg_one_of_mod8_three {p : ℕ} (hp : p % 8 = 3) :
    (p : ℤ) ≡ -1 [ZMOD 4] := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 8 * k + 3 := ⟨p / 8, by omega⟩
  refine Int.modEq_iff_dvd.mpr ⟨-(2 * (k : ℤ) + 1), ?_⟩
  push_cast
  ring

private theorem int_modEq_one_of_mod8_five {p : ℕ} (hp : p % 8 = 5) :
    (p : ℤ) ≡ 1 [ZMOD 4] := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 8 * k + 5 := ⟨p / 8, by omega⟩
  refine Int.modEq_iff_dvd.mpr ⟨-(2 * (k : ℤ) + 1), ?_⟩
  push_cast
  ring

theorem pgl2_prime_sup_isE_one_and_eOne_eq_top
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p) (hp : 5 < p)
    {S B : Subgroup (PGL2 K)}
    (hS : Quasithin.IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hB : IsKleinFour ↥B) :
    S ⊔ (⨆ I ∈ {I : Subgroup (PGL2 K) |
      IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) = ⊤ := by
  classical
  let M : Subgroup (PGL2 K) :=
    S ⊔ (⨆ I ∈ {I : Subgroup (PGL2 K) |
      IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I)
  have hSM : S ≤ M := le_sup_left
  haveI : Finite (PGL2 K) := e22pl2pgl_finite K
  have hB4 : Nat.card ↥B = 4 := IsKleinFour.card_four
  haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB4]; norm_num)
  have hBab : IsElemAbelian 2 B := by
    refine ⟨IsKleinFour.isMulCommutative, ?_⟩
    intro x hx
    have hx2 : x ^ 2 = 1 := by
      have hExp : Monoid.exponent ↥B = 2 := IsKleinFour.exponent_two
      have hx' : (⟨x, hx⟩ : ↥B) ^ 2 = 1 := by
        have := Monoid.pow_exponent_eq_one (g := (⟨x, hx⟩ : ↥B))
        rwa [hExp] at this
      simpa using congrArg Subtype.val hx'
    simpa using hx2
  have hBne : B ≠ ⊥ := by
    intro hbot
    have : Nat.card ↥B = 1 := by rw [hbot]; simp
    omega
  have hcard3 : 3 < Nat.card K := by rw [hK]; omega
  have hp7 : 7 ≤ p := by
    by_contra h
    have hp6 : p ≤ 6 := by omega
    have hp_prime : p.Prime := Fact.out
    interval_cases p <;> norm_num at hp_prime
  have hodd : IsOddPrimePower (Nat.card K) := e22pl2pgl_isOddPrimePower hp7 hK
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h8 : 8 ∣ Nat.card (PGL2 K) := by
    rw [pgl2_card_formula, hK]
    exact dvd_mul_of_dvd_right (CFSG.GH74.GLS.IVK.Proofs2.eight_dvd_sq_sub_one hpodd) p
  have hindex : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hS.not_dvd_relIndex
  let Ss : Sylow 2 (PGL2 K) := hS.isPGroup.toSylow hindex
  obtain ⟨m, hm1, ⟨eSs⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hodd Ss
  have hST : (Ss : Subgroup (PGL2 K)) = S := rfl
  let e : ↥S ≃* DihedralGroup (2 ^ m) := (MulEquiv.subgroupCongr hST).symm.trans eSs
  have hm2 : 2 ≤ m := e22pl2pgl_param_ge (n := 2) h8 Ss eSs
  obtain ⟨z, hzS, hz2, hzc, hzV, hAV⟩ := dihedral_sylow_data hm2 e
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzB : z ∈ B := hzV B hBS hB
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  obtain ⟨t, -, htz⟩ := dihedral_central_involution_sq hm2 e hzS hz2 hzc
  have hzJ : z ∈ pslRange K := by
    rw [← htz]
    have := Subgroup.pow_index_mem (pslRange K) t
    rwa [pslRange_index_eq_two hodd] at this
  have hcomm : commutator (PGL2 K) = pslRange K :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hodd hcard3
  haveI : (pslRange K).Normal := pslRange_normal hodd hcard3
  haveI : IsSimpleGroup ↥(pslRange K) := e22pl2pgl_simple_J hcard3
  have hnc := e22pl2pgl_nonabelian_J hcard3
  have hCJ := e22pl2pgl_centralizer_J hodd hcard3
  have hO2 : pCoreOf 2 (⊤ : Subgroup (PGL2 K)) = ⊥ :=
    E1.pCoreOf_top_eq_bot_of_normal_simple (pslRange K) hnc hCJ
  have hcentB : Subgroup.centralizer (B : Set (PGL2 K)) = B :=
    pgl2_kleinFour_centralizer_eq_self K hodd B hB
  have hτB : tauOf ⊤ S B = B :=
    tauOf_eq_of_self_centralizer hBS hBab hO2 hcentB
  have hzJ' : z ∈ commutator (PGL2 K) := hcomm ▸ hzJ
  have hDmax : IsCoatom (Subgroup.centralizer ({z} : Set (PGL2 K))) :=
    pgl2_centralizer_inner_involution_isCoatom_all hK hp hz2 hzJ'
  have hzpow_card : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hz2]
  have hzBsub : Subgroup.zpowers z ≤ B := Subgroup.zpowers_le.mpr hzB
  have hbexists : ∃ b ∈ B, b ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    have hBle : B ≤ Subgroup.zpowers z := fun x hx => h x hx
    have hEq : B = Subgroup.zpowers z := le_antisymm hBle hzBsub
    have : Nat.card ↥B = Nat.card ↥(Subgroup.zpowers z) := by rw [hEq]
    omega
  obtain ⟨b, hbB, hbz⟩ := hbexists
  have hb2' : b ^ 2 = 1 := by
    have hExp : Monoid.exponent ↥B = 2 := IsKleinFour.exponent_two
    have hb' : (⟨b, hbB⟩ : ↥B) ^ 2 = 1 := by
      have := Monoid.pow_exponent_eq_one (g := (⟨b, hbB⟩ : ↥B))
      rwa [hExp] at this
    simpa using congrArg Subtype.val hb'
  have hb1 : b ≠ 1 := by
    intro h
    apply hbz
    rw [h]
    exact (Subgroup.zpowers z).one_mem
  have hb2 : orderOf b = 2 := orderOf_eq_prime hb2' hb1
  have hDle : Subgroup.centralizer ({z} : Set (PGL2 K)) ≤ M := by
    have hzInv : BenderSuzuki.PFAppendixIII.IsInvolution z :=
      ⟨hz1, by simpa [pow_two] using hz2'⟩
    obtain ⟨U, w, hUc, hzU, hww, hwU, hwinv, hD_eq, hUJ⟩ :=
      CFSG.Quasithin.H13.pgl2_involution_data614 hodd hcard3 hzInv
    let D : Subgroup (PGL2 K) := Subgroup.centralizer ({z} : Set (PGL2 K))
    have hDsplit : D = U ⊔ Subgroup.zpowers w := by simpa [D] using hD_eq
    have hSD : S ≤ D := by
      intro s hs
      rw [show D = Subgroup.centralizer ({z} : Set (PGL2 K)) from rfl]
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haz : a = z := by simpa using ha
      subst haz
      exact hzc s hs
    have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
      intro x hx y hy
      exact congrArg Subtype.val (hUc.commGroup.mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hbD : b ∈ D := hSD (hBS hbB)
    have hbUsup : b ∈ U ⊔ Subgroup.zpowers w := by
      rw [← hDsplit]
      exact hbD
    have hbU : b ∉ U := by
      intro hbU'
      have hzb : z = b :=
        e22pl2pgl_involution_unique hUc hzU hbU'
          (by simpa [pow_two] using hz2') (by simpa [pow_two] using hb2') hz1 hb1
      apply hbz
      rw [← hzb]
      exact Subgroup.mem_zpowers z
    rcases CFSG.Quasithin.H13.mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv hbUsup with
      hbU' | ⟨u, huU, hb_eq⟩
    · exact absurd hbU' hbU
    · have hbInv : ∀ x ∈ U, b * x * b⁻¹ = x⁻¹ := by
        intro x hx
        rw [hb_eq]
        calc (u * w) * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
          _ = u * x⁻¹ * u⁻¹ := by rw [hwinv x hx]
          _ = x⁻¹ := by
            have hcomm : u * x⁻¹ = x⁻¹ * u :=
              hUcomm u huU x⁻¹ (U.inv_mem hx)
            rw [hcomm]
            group
      have hDN : ∀ P : Subgroup (PGL2 K), P ≤ U →
          D ≤ Subgroup.normalizer (P : Set (PGL2 K)) := by
        intro P hPU
        rw [hDsplit]
        refine sup_le ?_ ?_
        · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (P : Set (PGL2 K)))
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (hUcomm x hx y (hPU hy)).symm
        · exact CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.zpowers_le_normalizer_of_inverting
            hww (fun x hx => hwinv x (hPU hx))
      have hτN : ∀ P : Subgroup (PGL2 K), P ≤ U →
          tauOf ⊤ S B ≤ Subgroup.normalizer (P : Set (PGL2 K)) := by
        intro P hPU
        rw [hτB]
        exact hBS.trans (hSD.trans (hDN P hPU))
      have hSylD : Quasithin.IsSylowIn 2 S D :=
        ⟨hSD, hS.isPGroup,
          fun hd => hindex (hd.trans (Subgroup.relIndex_dvd_index_of_le hSD))⟩
      have hUleM : U ≤ M := by
        have hsup : ((⨆ r ∈ (Nat.card ↥U).primeFactors,
            ((default : Sylow r ↥U) : Subgroup ↥U)) : Subgroup ↥U).map U.subtype = U := by
          rw [Sylow.iSup_sylow_eq_top (G := ↥U), ← MonoidHom.range_eq_map,
            Subgroup.range_subtype]
        rw [← hsup]
        simp_rw [Subgroup.map_iSup]
        refine iSup₂_le ?_
        intro r hr
        set P : Subgroup (PGL2 K) :=
          ((default : Sylow r ↥U) : Subgroup ↥U).map U.subtype with hP
        have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hr
        haveI : Fact r.Prime := ⟨hrprime⟩
        have hPU : P ≤ U := by
          rw [hP]
          exact Subgroup.map_subtype_le _
        have hPr : IsPGroup r P := by
          rw [hP]
          exact (default : Sylow r ↥U).isPGroup'.map U.subtype
        have hQne : ((default : Sylow r ↥U) : Subgroup ↥U) ≠ ⊥ :=
          (default : Sylow r ↥U).ne_bot_of_dvd_card (Nat.dvd_of_mem_primeFactors hr)
        have hPne : P ≠ ⊥ := by
          rw [hP]
          intro hbot
          exact hQne ((Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp hbot)
        by_cases hr2 : r = 2
        · subst r
          have hPD : P ≤ D := hPU.trans (by rw [hDsplit]; exact le_sup_left)
          have hPnorm : (P.subgroupOf D).Normal :=
            Subgroup.normal_subgroupOf_of_le_normalizer (hDN P hPU)
          exact (hSylD.le_of_normal hPD hPnorm hPr).trans hSM
        · have hPodd : Odd (Nat.card ↥P) := by
            obtain ⟨n, hn⟩ := hPr.exists_card_eq
            rw [hn]
            exact Odd.pow (hrprime.odd_of_ne_two hr2)
          have hBN : B ≤ Subgroup.normalizer (P : Set (PGL2 K)) := by
            rw [← hτB]
            exact hτN P hPU
          have hbN : b ∈ Subgroup.normalizer (P : Set (PGL2 K)) :=
            hDN P hPU (hSD (hBS hbB))
          have hbInvP : ∀ x ∈ P, b * x * b⁻¹ = x⁻¹ :=
            fun x hx => hbInv x (hPU hx)
          have hcomm_b : ⁅P, Subgroup.zpowers b⁆ = P :=
            CFSG.Walter.commutator_zpowers_eq_self_of_conj_eq_inv hbN hbInvP hPodd
          have hcomm_le : ⁅P, B⁆ ≤ P := E1.commutator_le_of_le_normalizer hBN
          have hcomm_ge : P ≤ ⁅P, B⁆ :=
            hcomm_b.ge.trans (Subgroup.commutator_mono_right (Subgroup.zpowers_le.mpr hbB))
          have hcomm : ⁅P, B⁆ = P := le_antisymm hcomm_le hcomm_ge
          have hHzB : Subgroup.zpowers z ≤ B := Subgroup.zpowers_le.mpr hzB
          have hHzcentral : Subgroup.zpowers z ≤ Subgroup.centralizer (P : Set (PGL2 K)) := by
            rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
            intro y hy
            exact (hUcomm z hzU y (hPU hy)).symm
          have hHzindex : (Subgroup.zpowers z).relIndex B ≤ 2 := by
            have hidx := Subgroup.relIndex_mul_card (H := Subgroup.zpowers z) (K := B)
            rw [inf_eq_left.mpr hHzB, Nat.card_zpowers, hz2, hB4] at hidx
            omega
          obtain ⟨hIsE, hEOne, -⟩ := E1.isE_one_sup hrprime hr2 hS hBS hBab hPr hPne
            (hτN P hPU) hcomm hHzB hHzcentral hHzindex
          have hIM' : P ⊔ tauOf ⊤ S B ≤ M :=
            (le_iSup₂_of_le (f := fun I (_ : IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)) => I)
              (P ⊔ tauOf ⊤ S B) ⟨hIsE, hEOne⟩ le_rfl).trans le_sup_right
          exact le_sup_left.trans hIM'
      have hwM : w ∈ M := by
        have huM : u ∈ M := hUleM huU
        have hbM : b ∈ M := hSM (hBS hbB)
        have hw_eq : w = u⁻¹ * b := by
          rw [hb_eq]
          group
        rw [hw_eq]
        exact M.mul_mem (M.inv_mem huM) hbM
      have hDleD : D ≤ M := by
        rw [hDsplit]
        exact sup_le hUleM (Subgroup.zpowers_le.mpr hwM)
      simpa [D] using hDleD
  have hOutside : ∃ I : Subgroup (PGL2 K), IsE 1 ⊤ S B I ∧
      EOne ↥I (B.subgroupOf I) ∧
      ¬ I ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := by
    by_cases hBJ : B ≤ pslRange K
    · have hp_mod8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
        have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
        have hlt : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
        omega
      have hpartner : p % 8 = 1 ∨ p % 8 = 7 →
          ∃ I : Subgroup (PGL2 K), IsE 1 ⊤ S B I ∧
            EOne ↥I (B.subgroupOf I) ∧
            ¬ I ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := by
        intro hp8'
        have hp8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7 := by rwa [hK]
        obtain ⟨m3, hm3, ⟨e3⟩⟩ := e22pl2pgl_sylow_dihedral_q hodd hp8 hS
        have hm2' : 2 ≤ m3 := by omega
        obtain ⟨V', hV'T, hV', hne, hV'N, hVN, hN8, hC', hcomm'⟩ :=
          dihedral_kleinFour_partner hm2' e3 hBS hB
        have hV'J : V' ≤ pslRange K := by
          have hT₀ := dihedral_normalizer_le_of_index_two (T₀ := S ⊓ pslRange K) hm3 e3
            inf_le_left (e22pl2pgl_relIndex_inf hodd hcard3 hS) (le_inf hBS hBJ) hB
            hV'T hV' hVN hV'N hne hN8
          exact ((le_inf hV'T Subgroup.le_normalizer).trans hT₀).trans inf_le_right
        have hcent : Subgroup.centralizer (V' : Set (PGL2 K)) = V' :=
          pgl2_kleinFour_centralizer_eq_self K hodd V' hV'
        have hsurj := e22pl2pgl_normalizer_surjective_q hodd hp8 (by rw [hK]; exact hp7) hV'J hV'
        have hIsE :=
          isE_one_normalizer_kleinFour hS hO2 hB hV' hBS hV'T hne hcent hsurj hN8 hVN hC' hcomm'
        have hNsolv : Group.IsSolvable ↥(Subgroup.normalizer (V' : Set (PGL2 K))) :=
          (e22pl2s_normalizer_pCore_solvable hV' hcent hsurj).2
        have hEOne := (E1.isE_eOne_of_isSolvable hIsE hNsolv).1
        exact ⟨Subgroup.normalizer (V' : Set (PGL2 K)), hIsE, hEOne,
          not_normalizer_le_centralizer hV' hsurj (hzV V' hV'T hV') hz1⟩
      have hinner35 : p % 8 = 3 ∨ p % 8 = 5 →
          ∃ I : Subgroup (PGL2 K), IsE 1 ⊤ S B I ∧
            EOne ↥I (B.subgroupOf I) ∧
            ¬ I ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := by
        intro hp35
        have hbJ : b ∈ pslRange K := hBJ hbB
        have hbz_zpow : z ∉ Subgroup.zpowers b := by
          intro hzpb
          rcases e22pl2pgl_mem_zpowers_involution (by simpa [pow_two] using hb2') hzpb with h | h
          · exact hz1 h
          · apply hbz
            rw [← h]
            exact Subgroup.mem_zpowers z
        have hbInv' : BenderSuzuki.PFAppendixIII.IsInvolution b :=
          ⟨hb1, by simpa [pow_two] using hb2'⟩
        obtain ⟨Ub, wb, hUbc, hbUb, hwb2, hwbU, hwbInv, hCb, _⟩ :=
          CFSG.Quasithin.H13.pgl2_involution_data614 hodd hcard3 hbInv'
        have hUbcomm : ∀ x ∈ Ub, ∀ y ∈ Ub, x * y = y * x := by
          intro x hx y hy
          exact congrArg Subtype.val (hUbc.commGroup.mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
        have hbz_comm : b * z = z * b :=
          congrArg Subtype.val (hBab.1.is_comm.comm (⟨b, hbB⟩ : ↥B) (⟨z, hzB⟩ : ↥B))
        have hzCb : z ∈ Subgroup.centralizer ({b} : Set (PGL2 K)) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hbz_comm.symm
        have hzUb : z ∉ Ub := by
          intro hzUb'
          have hzb : z = b :=
            e22pl2pgl_involution_unique hUbc hzUb' hbUb
              (by simpa [pow_two] using hz2') (by simpa [pow_two] using hb2') hz1 hb1
          apply hbz
          rw [← hzb]
          exact Subgroup.mem_zpowers z
        have hzUbsup : z ∈ Ub ⊔ Subgroup.zpowers wb := by
          rw [← hCb]
          exact hzCb
        rcases CFSG.Quasithin.H13.mem_or_mem_mul_of_mem_sup_zpowers614 hwb2 hwbInv hzUbsup with
          hzUb' | ⟨v, hvUb, hz_eq⟩
        · exact absurd hzUb' hzUb
        · have hzInvUb : ∀ x ∈ Ub, z * x * z⁻¹ = x⁻¹ := by
            intro x hx
            rw [hz_eq]
            calc (v * wb) * x * (v * wb)⁻¹ = v * (wb * x * wb⁻¹) * v⁻¹ := by group
              _ = v * x⁻¹ * v⁻¹ := by rw [hwbInv x hx]
              _ = x⁻¹ := by
                have hcomm : v * x⁻¹ = x⁻¹ * v :=
                  hUbcomm v hvUb x⁻¹ (Ub.inv_mem hx)
                rw [hcomm]
                group
          have hbUb_comm : ∀ x ∈ Ub, b * x = x * b := by
            intro x hx
            have hxC : x ∈ Subgroup.centralizer ({b} : Set (PGL2 K)) := by
              rw [hCb]
              exact Subgroup.mem_sup_left hx
            rw [Subgroup.mem_centralizer_singleton_iff] at hxC
            exact hxC.symm
          have hCbNorm : Subgroup.centralizer ({b} : Set (PGL2 K)) ≤
              Subgroup.normalizer (Ub : Set (PGL2 K)) := by
            rw [hCb]
            exact sup_le Subgroup.le_normalizer
              (CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.zpowers_le_normalizer_of_inverting
                hwb2 hwbInv)
          have hBCb : B ≤ Subgroup.centralizer ({b} : Set (PGL2 K)) := by
            intro x hx
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact congrArg Subtype.val (hBab.1.is_comm.comm (⟨x, hx⟩ : ↥B) (⟨b, hbB⟩ : ↥B))
          have hτUb : tauOf ⊤ S B ≤ Subgroup.normalizer (Ub : Set (PGL2 K)) := by
            rw [hτB]
            exact hBCb.trans hCbNorm
          have hcommon : ∀ (m : ℕ),
              Nat.card (Subgroup.centralizer ({b} : Set (PGL2 K))) = 2 * m →
              m % 8 = 4 → 12 ≤ m →
              ∃ I : Subgroup (PGL2 K), IsE 1 ⊤ S B I ∧
                EOne ↥I (B.subgroupOf I) ∧
                ¬ I ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := by
            intro m hcard hm8 hm12
            have hUbcard : Nat.card ↥Ub = m := by
              have hsup := card_sup_zpowers_eq_two_mul hwb2 hwbU hwbInv
              have hCbcard : Nat.card (Subgroup.centralizer ({b} : Set (PGL2 K))) =
                  Nat.card ↥Ub * 2 := by
                rw [hCb, hsup]
              omega
            have hn4 : (m / 2) % 4 = 2 := by omega
            have hn6 : 6 ≤ m / 2 := by omega
            obtain ⟨r, hrprime, hr2, hrdvdn⟩ := e22pl2pgl_exists_odd_prime hn4 hn6
            have hrdvdm : r ∣ m :=
              dvd_trans hrdvdn (Nat.div_dvd_of_dvd (by omega : 2 ∣ m))
            have hrUb : r ∣ Nat.card ↥Ub := by
              rw [hUbcard]
              exact hrdvdm
            obtain ⟨P0, hP0Ub, hP0ne, hP0grp, hIsE, hP0notCz⟩ :=
              isE_one_of_odd_torus (T := S) (A := B) (U := Ub) hS hBS hBab hB4
                hbB hzB hb2 hbz_zpow hUbc hbUb_comm hzInvUb hτUb hrprime hr2 hrUb
            have hUbτsolv : Group.IsSolvable ↥(Ub ⊔ tauOf ⊤ S B) :=
              CFSG.GroupTheory.isSolvable_sup_of_isPGroup_of_le_normalizer
                (Group.isSolvable_of_comm fun x y => Subtype.ext (hUbcomm x x.2 y y.2))
                (hS.isPGroup.to_le (tauOf_le ⊤ S B)) hτUb
            haveI : Group.IsSolvable ↥(Ub ⊔ tauOf ⊤ S B) := hUbτsolv
            have hP0le : P0 ⊔ tauOf ⊤ S B ≤ Ub ⊔ tauOf ⊤ S B :=
              sup_le (hP0Ub.trans le_sup_left) le_sup_right
            haveI : Group.IsSolvable
                ↥((P0 ⊔ tauOf ⊤ S B).subgroupOf (Ub ⊔ tauOf ⊤ S B)) := inferInstance
            have hsolv : Group.IsSolvable ↥(P0 ⊔ tauOf ⊤ S B) :=
              Group.isSolvable_of_isSolvable_injective
                (f := (Subgroup.subgroupOfEquivOfLe hP0le).symm.toMonoidHom)
                (Subgroup.subgroupOfEquivOfLe hP0le).symm.injective
            have hEOne := (E1.isE_eOne_of_isSolvable hIsE hsolv).1
            exact ⟨P0 ⊔ tauOf ⊤ S B, hIsE, hEOne,
              fun hle => hP0notCz (le_trans le_sup_left hle)⟩
          rcases hp35 with hp3 | hp5
          · have hε1 : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
            have hε : (p : ℤ) ≡ -1 [ZMOD 4] := int_modEq_neg_one_of_mod8_three hp3
            obtain ⟨m, hm, ⟨eD⟩⟩ :=
              (CFSG.GH74.GLS.IVK.pgl2_involution_centralizer_dihedral hodd hcard3 hε1 (by rwa [hK]) hb2).1 hbJ
            have hcard : Nat.card (Subgroup.centralizer ({b} : Set (PGL2 K))) = 2 * m := by
              rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
            have hm8 : m % 8 = 4 := by omega
            have hm12 : 12 ≤ m := by omega
            exact hcommon m hcard hm8 hm12
          · have hε1 : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
            have hε : (p : ℤ) ≡ 1 [ZMOD 4] := int_modEq_one_of_mod8_five hp5
            obtain ⟨m, hm, ⟨eD⟩⟩ :=
              (CFSG.GH74.GLS.IVK.pgl2_involution_centralizer_dihedral hodd hcard3 hε1 (by rwa [hK]) hb2).1 hbJ
            have hcard : Nat.card (Subgroup.centralizer ({b} : Set (PGL2 K))) = 2 * m := by
              rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
            have hm8 : m % 8 = 4 := by omega
            have hm12 : 12 ≤ m := by omega
            exact hcommon m hcard hm8 hm12
      rcases hp_mod8 with h1 | h3 | h5 | h7
      · exact hpartner (Or.inl h1)
      · exact hinner35 (Or.inl h3)
      · exact hinner35 (Or.inr h5)
      · exact hpartner (Or.inr h7)
    · exact e22pl2pgl_outer_member_eOne hodd hcard3 hS hBS hBab hB4 hO2 hzB hz2 hzJ hBJ
  obtain ⟨I, hI, hEOneI, hnotI⟩ := hOutside
  have hIle : I ≤ ⨆ I ∈ {I : Subgroup (PGL2 K) |
      IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I :=
    le_iSup_of_le I (le_iSup_of_le
      (show I ∈ {I : Subgroup (PGL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)} from ⟨hI, hEOneI⟩) le_rfl)
  have hIM : I ≤ M := hIle.trans le_sup_right
  have hDMne : Subgroup.centralizer ({z} : Set (PGL2 K)) ≠ M := by
    intro h
    exact hnotI (by simpa [h] using hIM)
  have hlt : Subgroup.centralizer ({z} : Set (PGL2 K)) < M := lt_of_le_of_ne hDle hDMne
  exact hDmax.2 M hlt

theorem pgl2_prime_sup_isE_one_eq_top
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p) (hp : 5 < p)
    {S B : Subgroup (PGL2 K)}
    (hS : Quasithin.IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hB : IsKleinFour ↥B) :
    S ⊔ (⨆ I ∈ {I : Subgroup (PGL2 K) | IsE 1 ⊤ S B I}, I) = ⊤ := by
  have hgen_le : (⨆ I ∈ {I : Subgroup (PGL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) ≤
      ⨆ I ∈ {I : Subgroup (PGL2 K) | IsE 1 ⊤ S B I}, I :=
    biSup_mono fun I hI => hI.1
  have hle : S ⊔ (⨆ I ∈ {I : Subgroup (PGL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) ≤
      S ⊔ (⨆ I ∈ {I : Subgroup (PGL2 K) | IsE 1 ⊤ S B I}, I) :=
    sup_le_sup le_rfl hgen_le
  have hnew := pgl2_prime_sup_isE_one_and_eOne_eq_top hK hp hS hBS hB
  exact top_le_iff.mp (hnew.symm.le.trans hle)


end CFSG.Quasithin.E22L2

end
