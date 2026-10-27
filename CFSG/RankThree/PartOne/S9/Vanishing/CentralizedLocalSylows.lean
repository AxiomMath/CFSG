module

public import CFSG.RankThree.PartOne.S9.Vanishing.Basic
public import CFSG.RankThree.PartOne.S9.Vanishing.ResidualBridge
public import CFSG.RankThree.GroupTheory.SteinbergBMResidualCommonPlaneSylowTwo
import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal
import CFSG.RankThree.PartOne.S9.Top.ThetaLocal
import CFSG.RankThree.PartOne.S9.Alpha.UniformVerification

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory Subgroup
open scoped commutatorElement

namespace Vanish

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem center_eq_bot_of_simple_nonabelian [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem not_dvd_card_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup G}
    (hU : IsPGroup 2 U) : ¬ p ∣ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  intro h
  rw [hk] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem exists_hyperplane_not_centralized {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A S : Subgroup G}
    (hchar : IsCharTwoType G) (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hSA : ⁅S, A⁆ = ⊥) :
    ∃ D : Subgroup G, D ≤ A ∧ Nat.card D = p ^ 2 ∧
      ⁅inSubgroup (pCore 2) (normalizer (S : Set G)) ⊓ centralizer (D : Set G), A⁆ ≠ ⊥ := by
  set N := normalizer (S : Set G) with hN
  set P := inSubgroup (pCore 2) N with hP
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 N
  have hASc : A ≤ centralizer (S : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hSA
  have hAN : A ≤ N := hASc.trans (Subgroup.centralizer_le_normalizer _)
  have hAP : A ≤ normalizer (P : Set G) :=
    hAN.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 N)
  have hNloc : IsTwoLocal N := ⟨S, hS1, hS2, rfl⟩
  have h := hchar N hNloc
  have e : CFSG.Assembly.pCoreOf 2 N = P := by
    simp only [CFSG.Assembly.pCoreOf, hP, inSubgroup]
  rw [e] at h
  have hApg : IsPGroup p A := IsPGroup.of_card hAcard
  have hPA : ⁅P, A⁆ ≠ ⊥ := by
    intro hPA
    have hAcP : A ≤ centralizer (P : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hPA
    have hAP' : A ≤ P := (le_inf hAN hAcP).trans h
    have hA2 : IsPGroup 2 A := hP2.to_le hAP'
    have := Subgroup.card_dvd_of_le hAP'
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hAcard, hk] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow ((dvd_pow_self p (by norm_num)).trans this)))
  by_contra hcon
  push Not at hcon
  apply hPA
  have hcent : P ≤ centralizer (A : Set G) := by
    refine le_of_forall_hyperplane_inf_centralizer_le hp hA hAcard hAP
      (not_dvd_card_of_isPGroup_two hp hp2 hP2) ?_
    intro D hDA hDcard
    have h1 := hcon D hDA hDcard
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at *
    exact h1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hcent

theorem exists_two_generators {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : Nat.card D = p ^ 2)
    (hexp : ∀ x ∈ D, x ^ p = 1) :
    ∃ c ∈ D, c ≠ 1 ∧ ∃ d ∈ D, d ∉ Subgroup.zpowers c := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have h1p2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
  obtain ⟨c, hcD, hc1⟩ : ∃ c ∈ D, c ≠ 1 := by
    by_contra h
    push Not at h
    have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [this, Subgroup.card_bot] at hD
    omega
  refine ⟨c, hcD, hc1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : D ≤ Subgroup.zpowers c := hcon
  have h1 := Subgroup.card_le_of_le hle
  have hord : orderOf c = p := orderOf_eq_prime (hexp c hcD) hc1
  rw [Nat.card_zpowers, hord, hD] at h1
  have : p ^ 2 = p * p := sq p
  have : p < p * p := Nat.lt_mul_self_iff.mpr hp1
  omega

theorem commutator_eq_bot_of_frattini {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A S : Subgroup G}
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hSA : ⁅S, A⁆ = ⊥)
    (hH : ∀ c : G, c ≠ 1 → normalizer (Subgroup.zpowers c : Set G) ≠ ⊤)
    (hres : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → ∀ K : Subgroup G, D ≤ K → K ≠ ⊤ →
      ∀ t ∈ D, t ≠ 1 → CFSG.Quasithin.twoPrimeResidual (residualGroup p K D t) ≤
        inSubgroup (aschbacherSolvableCore p) K)
    (hcent : ∀ c ∈ A, c ≠ 1 → ∀ U : Subgroup G,
      U ≤ inSubgroup (aschbacherSolvableCore p) (normalizer (Subgroup.zpowers c : Set G)) →
      IsPGroup 2 U → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = ⊥)
    {D : Subgroup G} (hDA : D ≤ A) (hDcard : Nat.card D = p ^ 2)
    (hfrat : inSubgroup (pCore 2) (normalizer (S : Set G)) ⊓ centralizer (D : Set G) ≤
      inSubgroup (aschbacherSolvableCore p) (centralizer (D : Set G))) :
    ⁅inSubgroup (pCore 2) (normalizer (S : Set G)) ⊓ centralizer (D : Set G), A⁆ = ⊥ := by
  have := hA
  set N := normalizer (S : Set G) with hN
  set P := inSubgroup (pCore 2) N with hP
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 N
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hASc : A ≤ centralizer (S : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hSA
  have hAN : A ≤ N := hASc.trans (Subgroup.centralizer_le_normalizer _)
  have hAP : A ≤ normalizer (P : Set G) :=
    hAN.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 N)
  have hApg : IsPGroup p A := IsPGroup.of_card hAcard
  have hAD : A ≤ centralizer (D : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun d hd => hcomm d (hDA hd) a ha
  set U := P ⊓ centralizer (D : Set G) with hU
  have hU2 : IsPGroup 2 U := hP2.to_le inf_le_left
  have hAU : A ≤ normalizer (U : Set G) := fun a ha =>
    SteinbergBY.mem_normalizer_inf (hAP ha) (Subgroup.le_normalizer (hAD ha))
  have hexp : ∀ x ∈ D, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x (hDA hx)
  obtain ⟨c, hcD, hc1, d, hdD, hdc⟩ := exists_two_generators hp hDcard hexp
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  have hcA : c ∈ A := hDA hcD
  have hdA : d ∈ A := hDA hdD
  have hDeq : D = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcD)
      (Subgroup.zpowers_le.mpr hdD)) ?_).symm
    rw [SteinbergBY.card_zpowers_sup_zpowers hp hAcard hcA hc1 hdA hdc, hDcard]
  set H := normalizer (Subgroup.zpowers c : Set G) with hHdef
  have hAH : A ≤ H := fun x hx =>
    Sec9Top.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx c hcA))
  have hHtop : H ≠ ⊤ := hH c hc1
  have hCDle : centralizer (D : Set G) ≤ H ⊓ centralizer ({d} : Set G) := fun x hx =>
    ⟨Sec9Top.centralizer_le_normalizer_zpowers c
        (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hx c hcD).symm),
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx d hdD).symm⟩
  have hCDnorm : H ⊓ centralizer ({d} : Set G) ≤ normalizer (centralizer (D : Set G) : Set G) := by
    intro h hh
    have h1 : h ∈ normalizer (Subgroup.zpowers c : Set G) := hh.1
    have h2 : h ∈ normalizer (Subgroup.zpowers d : Set G) :=
      Sec9Top.centralizer_le_normalizer_zpowers d hh.2
    have hhD : h ∈ normalizer (D : Set G) := by
      rw [hDeq]
      refine SteinbergBY.mem_normalizer_of_map_conj_eq ?_
      rw [Subgroup.map_sup, SteinbergBY.map_conj_eq_of_mem_normalizer h1,
        SteinbergBY.map_conj_eq_of_mem_normalizer h2]
    exact GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup _ hhD
  have hθle : inSubgroup (aschbacherSolvableCore p) (centralizer (D : Set G)) ≤
      inSubgroup (aschbacherSolvableCore p) (H ⊓ centralizer ({d} : Set G)) := by
    rw [CFSG.RankThree.LocalRank.inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
      CFSG.RankThree.LocalRank.inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact RankThreeEvenClassification.Helpers.thetaCoreOf_mono_of_normal p hp _ _ hCDle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCDle).mpr hCDnorm)
  have hUθ : U ≤ inSubgroup (aschbacherSolvableCore p) (H ⊓ centralizer ({d} : Set G)) :=
    hfrat.trans hθle
  have hUC : ∀ u ∈ U, ∀ x ∈ D, u * x = x * u := fun u hu x hx =>
    (Subgroup.mem_centralizer_iff.mp hu.2 x hx).symm
  have hcommθ : ∀ u ∈ U, ∀ a ∈ A, ⁅u, a⁆ ∈ inSubgroup (aschbacherSolvableCore p) H := by
    intro u hu a ha
    by_cases hadz : a ∈ Subgroup.zpowers d
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hadz
      have : ⁅u, d ^ k⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact ((Commute.zpow_right (show Commute u d from hUC u hu d hdD) k)).eq
      rw [this]
      exact Subgroup.one_mem _
    · set E := Subgroup.zpowers d ⊔ Subgroup.zpowers a with hE
      have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hdA) (Subgroup.zpowers_le.mpr ha)
      have hEcard : Nat.card E = p ^ 2 :=
        SteinbergBY.card_zpowers_sup_zpowers hp hAcard hdA hd1 ha hadz
      have hresE := hres E hEA hEcard H (hEA.trans hAH) hHtop d
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)) hd1
      have hxW : ⁅u, a⁆ ∈ residualGroup p H E d := by
        unfold residualGroup
        exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (hUθ hu)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
      have hxU : ⁅u, a⁆ ∈ U := by
        have hua : a * u⁻¹ * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hAU ha) u⁻¹).mp
          (inv_mem hu)
        have : ⁅u, a⁆ = u * (a * u⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact mul_mem hu hua
      have hX2 : IsPGroup 2 (Subgroup.zpowers ⁅u, a⁆) :=
        hU2.to_le (Subgroup.zpowers_le.mpr hxU)
      exact hresE (Sec9A.le_twoPrimeResidual hX2 (Subgroup.zpowers_le.mpr hxW)
        (Subgroup.mem_zpowers _))
  have hVθ : ⁅U, A⁆ ≤ inSubgroup (aschbacherSolvableCore p) H :=
    Subgroup.commutator_le.mpr hcommθ
  have hVU : ⁅U, A⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hAU
  have hAV : A ≤ normalizer ((⁅U, A⁆ : Subgroup G) : Set G) := fun g hg =>
    SteinbergBY.mem_normalizer_commutator (hAU hg) (Subgroup.le_normalizer hg)
  have h0 := hcent c hcA hc1 _ hVθ (hU2.to_le hVU) hAV
  have h1 := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A U hApg
    (not_dvd_card_of_isPGroup_two hp hp2 hU2) hAU
  rw [← h1]
  exact h0

end Vanish

theorem centralizedLocalSylowsOddIntersections :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      IsCharTwoType G → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ A : Subgroup G, IsElementaryAbelian p A →
      Nat.card A = p ^ 3 →
      (∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → ∀ K : Subgroup G, D ≤ K → K ≠ ⊤ →
        ∀ t ∈ D, t ≠ 1 → CFSG.Quasithin.twoPrimeResidual (residualGroup p K D t) ≤
          inSubgroup (aschbacherSolvableCore p) K) →
      (∀ c ∈ A, c ≠ 1 → ∃ T : Subgroup G,
        IsSylowOf 2 T (inSubgroup (aschbacherSolvableCore p)
          (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∧ ⁅T, A⁆ = ⊥) →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → Odd (Nat.card (thetaT p B)) := by
  intro G _ _ _ hnonab hchar p hp hp2 A hA hAcard hres hsyl B hBA hBcard
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center G = ⊥ := Vanish.center_eq_bot_of_simple_nonabelian hnonab
  have hres' : ∀ D : Subgroup G, D ≤ A → Nat.card D = p ^ 2 → ∀ K : Subgroup G, D ≤ K →
      K ≠ ⊤ → ∀ t : K, (t : G) ∈ D → t ≠ 1 →
        CFSG.Quasithin.twoPrimeResidual
            (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set K)),
              D.subgroupOf K⁆ ⊔ thetaT p (D.subgroupOf K)) ≤ aschbacherSolvableCore p K :=
    fun D hDA hDcard K hDK hKtop t htD ht1 =>
      Vanish.residual_inside_of_residual hp hDK t htD (fun h => ht1 (Subtype.ext h))
        (hres D hDA hDcard K hDK hKtop (t : G) htD (fun h => ht1 (Subtype.ext h)))
  have hsyl' : ∀ c ∈ A, c ≠ 1 → ∃ T : Subgroup G, ABGLocalTools.IsSylowOf 2 T
      (inSubgroup (aschbacherSolvableCore p) (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∧
        ⁅T, A⁆ = ⊥ := fun c hc hc1 => by
    obtain ⟨T, hT, hTA⟩ := hsyl c hc hc1
    exact ⟨T, Vanish.isSylowOf_iff_abg.mp hT, hTA⟩
  obtain ⟨hXD, hcentral, hSylBM⟩ :=
    SteinbergBM.residual_common_plane_core_sylow_two hZ hp hA hAcard hres' hsyl'
  by_contra hodd
  have heven : 2 ∣ Nat.card (thetaT p B) := by
    rcases Nat.even_or_odd (Nat.card (thetaT p B)) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  have hApg : IsPGroup p A := IsPGroup.of_card hAcard
  obtain ⟨hAXB, hsolvB, hXBC, hCXB, hpXB⟩ := hXD B hBA hBcard
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hAbot : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨S, hS, -, hAS⟩ := SteinbergBM.exists_isSylowOf_two_invariant_le hp hApg hpXB hAXB
    bot_le hbot2 hAbot
  obtain ⟨hSA, hSD⟩ := hSylBM B hBA hBcard S hS hAS
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hS1 : S ≠ ⊥ := by
    intro hSbot
    obtain ⟨-, -, hidx⟩ := ABGLocalTools.isSylowOf_iff.mp hS
    rw [hSbot, Subgroup.relIndex_bot_left] at hidx
    exact hidx heven
  obtain ⟨D, hDA, hDcard, hD⟩ :=
    Vanish.exists_hyperplane_not_centralized hp hp2 hchar hA hAcard hS2 hS1 hSA
  have hfrat : inSubgroup (pCore 2) (Subgroup.normalizer (S : Set G)) ⊓
      Subgroup.centralizer (D : Set G) ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer (D : Set G)) := by
    obtain ⟨hAXD, hsolvD, hXDC, hCXD, hpXD⟩ := hXD D hDA hDcard
    obtain ⟨Q, hQ⟩ := hSD D hDA hDcard
    have := SteinbergBM.frattini_normalizer_two_core_solvable_prime_complement_containment hp hp2
      hXDC ((Subgroup.normal_subgroupOf_iff_le_normalizer hXDC).mpr hCXD) hsolvD hpXD Q
    rwa [hQ] at this
  have hH : ∀ c : G, c ≠ 1 → Subgroup.normalizer (Subgroup.zpowers c : Set G) ≠ ⊤ :=
    fun c hc => AlphaTheory.normalizer_zpowers_ne_top hnonab hc
  exact hD (Vanish.commutator_eq_bot_of_frattini hp hp2 hA hAcard hSA hH hres
    (fun c hc hc1 U hU hU2 hAU => hcentral c hc hc1 U hU hU2 hAU) hDA hDcard hfrat)

end CFSG.RankThree.PartOne
