module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalCritical
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Sec9B
open scoped commutatorElement

namespace Sec9B

variable {G : Type*} [Group G]

theorem normalizer_zpowers_ne_top (hs : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a)
    {c : G} (hc1 : c ≠ 1) : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≠ ⊤ := by
  intro h
  have hn : (Subgroup.zpowers c).Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.zpowers c) with h1 | h1
  · exact hc1 (Subgroup.zpowers_eq_bot.mp h1)
  · obtain ⟨a, b, hab⟩ := hnon
    have ha : a ∈ Subgroup.zpowers c := h1 ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.zpowers c := h1 ▸ Subgroup.mem_top b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hab (Commute.zpow_zpow_self c i j).eq

end Sec9B

theorem Sec9B.commutator_two_core_le_theta (hPSR : ProperSubgroupResidual) {G : Type}
    [Group G] [Finite G] (hKP : KProper InCatalog G) (he : evenRank G ≤ 3) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {A : Subgroup G} (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card ↥A = p ^ 3) {H : Subgroup G} (hAH : A ≤ H) (hHtop : H ≠ ⊤) {b : G}
    (hbA : b ∈ A) (hb1 : b ≠ 1) :
    ⁅inSubgroup (pCore 2) (H ⊓ Subgroup.centralizer ({b} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore p) H := by
  have hp2 : p ≠ 2 := by omega
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := (isElementaryAbelian_iff_forall.mp hA).1
  set C := H ⊓ Subgroup.centralizer ({b} : Set G) with hC
  set V := inSubgroup (pCore 2) C with hV
  have hAC : A ≤ C := fun x hx =>
    ⟨hAH hx, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hbA)⟩
  have hV2 : IsPGroup 2 ↥V := SteinbergBY.isPGroup_inSubgroup_pCore 2 C
  have hVC : V ≤ C := SteinbergBY.inSubgroup_pCore_le 2 C
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hAC.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 C)
  have hVθ : V ≤ inSubgroup (aschbacherSolvableCore p) C :=
    Subgroup.map_mono ((solvable_prime_complement_core_characterization hp).2.2.2.2.2.2 2
      Nat.prime_two (Ne.symm hp2))
  rw [Subgroup.commutator_le]
  intro v hv x hx
  by_cases hxb : x ∈ Subgroup.zpowers b
  ·
    have hvb : v ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      rw [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
      exact (hVC hv).2
    have h1 : ⁅v, x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hvb x hxb).symm
    rw [h1]
    exact one_mem _
  · have : IsElementaryAbelian p A := hA
    set E := Subgroup.zpowers b ⊔ Subgroup.zpowers x with hE
    have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr hx)
    have hEcard : Nat.card ↥E = p ^ 2 :=
      SteinbergBY.card_zpowers_sup_zpowers hp hAcard hbA hb1 hx hxb
    have hEel : IsElementaryAbelian p E := SteinbergBM.isElementaryAbelian_of_le hA hEA
    have hbE : b ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    have hxE : x ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hres := hPSR G hKP he p hp hp3 E hEel hEcard H (hEA.trans hAH) hHtop b hbE hb1
    have hVE : ⁅V, E⁆ ≤ V := Subgroup.commutator_le.mpr fun v' hv' e he' => by
      have := (Subgroup.mem_normalizer_iff.mp (hAV (hEA he')) v'⁻¹).mp (V.inv_mem hv')
      have e1 : ⁅v', e⁆ = v' * (e * v'⁻¹ * e⁻¹) := by simp only [commutatorElement_def]; group
      rw [e1]
      exact V.mul_mem hv' this
    have hVE2 : IsPGroup 2 ↥⁅V, E⁆ := hV2.to_le hVE
    have hVEW : ⁅V, E⁆ ≤ residualGroup p H E b :=
      (Subgroup.commutator_mono hVθ le_rfl).trans le_sup_left
    exact hres (Sec9A.le_twoPrimeResidual hVE2 hVEW (Subgroup.commutator_mem_commutator hv hxE))

theorem centralizerTwoCoreCommutatorBound_of (hPSR : ProperSubgroupResidual)
    (hCCCA : CentralizerConstrainedCriticalAction)
    (hI1 : SelectedPrimeMinimalTwoActionReduction)
    (hSOCAL : SmallOddCoreActionLiftingInsideLocalGroup)
    (hESAE : ExceptionalSmallActionExclusion) : CentralizerTwoCoreCommutatorBound := by
  intro G _ _ p hG hgood A hA hAcard c hcA hc1 b hbA hb1
  have hp : p.Prime := hG.prime
  have hp3 : 3 < p := hG.three_lt
  have hp2 : p ≠ 2 := by omega
  have hsimple := hG.simple
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := (isElementaryAbelian_iff_forall.mp hA).1
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hAH : A ≤ H := fun x hx => mem_normalizer_zpowers_of_commute (hcomm x hx c hcA)
  have hHtop : H ≠ ⊤ := normalizer_zpowers_ne_top hsimple hG.nonabelian hc1
  have hS := commutator_two_core_le_theta hPSR hG.kProper hG.evenRank_eq.le hp hp3 hA hAcard hAH
    hHtop hbA hb1
  by_contra hJ
  obtain ⟨q, hq, hq2, hqp, R, Q, D, hRVS, hbR, hcrit⟩ :=
    relative_centralizerConstrainedCriticalAction hCCCA H A hp hp2 hAH hA hAcard hbA hb1 hS hJ
  set C := H ⊓ Subgroup.centralizer ({b} : Set G) with hC
  have hRV : R ≤ inSubgroup (pCore 2) C := hRVS.trans inf_le_left
  have hRθ : R ≤ inSubgroup (aschbacherSolvableCore p) H := hRVS.trans inf_le_right
  have hR2 : IsPGroup 2 ↥R := (SteinbergBY.isPGroup_inSubgroup_pCore 2 C).to_le hRV
  have hRH : R ≤ H := hRθ.trans (Subgroup.map_subtype_le _)
  have hQH : Q ≤ H := hcrit.sylow.1.trans (Subgroup.map_subtype_le _)
  have hDH : D ≤ H := hcrit.D_le_Q.trans hQH
  have hR1 : R ≠ ⊥ := fun h => hcrit.comm_D_ne (by rw [h, Subgroup.commutator_bot_left])
  have hND : ∀ g ∈ Subgroup.normalizer (Q : Set G), g ∈ Subgroup.normalizer (D : Set G) :=
    fun g hg => mem_normalizer_of_characteristic hcrit.D_le_Q hcrit.D_char hg
  have hRAD : R ⊔ A ≤ Subgroup.normalizer (D : Set G) :=
    sup_le (fun r hr => hND r (hcrit.R_normalizes_Q hr))
      (fun a ha => hND a (hcrit.A_normalizes_Q ha))
  have hDD : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.commutator_mono le_rfl hcrit.D_le_Q).trans
      (hcrit.comm_D_Q.trans inf_le_right)
  have hidx := relIndex_inf_centralizer_eq hp hAcard hcrit.card_B
  have hpB : p ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) := by
    rw [hcrit.card_B]; exact Nat.le_self_pow (by norm_num) p
  obtain ⟨-, hres⟩ := hI1 G hG.evenRank_eq p hp hG.mem_sigma hp3 q hq hq2 hqp A R D hA
    hcrit.A_normalizes hR2 hcrit.comm_eq hR1 hRAD (isPGroup_of_forall_pow_eq_one hcrit.D_exp)
    hcrit.D_exp hDD hcrit.comm_D_ne hidx hpB (fun U hU hAU hUA => (hcrit.minimal U hU hAU hUA).2)
    hgood
  have hcR : c ∈ Subgroup.centralizer (R : Set G) := by
    have hcn : ((Subgroup.zpowers c).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).mpr le_rfl
    exact (hcrit.normal_le (Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hcA) hcn)
      (Subgroup.mem_zpowers c) |>.2
  rcases hres with hBD | ⟨hp5, ⟨e⟩, hRC, hDR, hDB, hq1, hloc, hshape⟩
  ·
    have hbD : ∀ d ∈ D, b * d = d * b := by
      intro d hd
      have h1 : ⁅b, d⁆ ∈ ⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ :=
        Subgroup.commutator_mem_commutator ⟨hbA, hbR⟩ hd
      rw [hBD, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    apply hcrit.comm_D_ne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdC : d ∈ C := ⟨hDH hd, Subgroup.mem_centralizer_singleton_iff.mpr (hbD d hd).symm⟩
    have hdN : d ∈ Subgroup.normalizer (inSubgroup (pCore 2) C : Set G) :=
      SteinbergBY.le_normalizer_inSubgroup_pCore 2 C hdC
    have h1 : d * r⁻¹ * d⁻¹ ∈ inSubgroup (pCore 2) C :=
      (Subgroup.mem_normalizer_iff.mp hdN r⁻¹).mp (Subgroup.inv_mem _ (hRV hr))
    have h2 : r * d * r⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hRAD (Subgroup.mem_sup_left hr)) d).mp hd
    have hV : ⁅r, d⁆ ∈ inSubgroup (pCore 2) C := by
      have e1 : ⁅r, d⁆ = r * (d * r⁻¹ * d⁻¹) := by simp only [commutatorElement_def]; group
      rw [e1]
      exact Subgroup.mul_mem _ (hRV hr) h1
    have hD' : ⁅r, d⁆ ∈ D := by
      have e1 : ⁅r, d⁆ = (r * d * r⁻¹) * d⁻¹ := by simp only [commutatorElement_def]
      rw [e1]
      exact D.mul_mem h2 (D.inv_mem hd)
    have h3 : ⁅r, d⁆ = 1 :=
      Sec9B.eq_one_of_mem_isPGroup_of_ne Nat.prime_two hq (Ne.symm hq2)
        (SteinbergBY.isPGroup_inSubgroup_pCore 2 C)
        (isPGroup_of_forall_pow_eq_one hcrit.D_exp) hV hD'
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  ·
    subst hp5
    have hq5 : 5 < q := by have := hq.two_le; omega
    obtain ⟨a, haA, haC⟩ := exists_mem_not_mem_centralizer hp hAcard hcrit.card_B
    have ha1 : a ≠ 1 := fun h => haC (h ▸ Subgroup.one_mem _)
    have haH : a ∈ H := hAH haA
    have hzA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).mpr haA
    have hzH : Subgroup.zpowers a ≤ H := (Subgroup.zpowers_le).mpr haH
    have hA₀card : Nat.card ↥(Subgroup.zpowers a) = 5 := card_zpowers_eq hp hA haA ha1
    have hRA₀ : ⁅R, Subgroup.zpowers a⁆ = R :=
      commutator_zpowers_eq hp hA hAcard hcrit.A_normalizes hcrit.comm_eq hcrit.card_B haA haC
    have hRAQ : R ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (Q : Set G) :=
      sup_le hcrit.R_normalizes_Q (hzA.trans hcrit.A_normalizes_Q)
    obtain ⟨-, -, hDeq⟩ := hSOCAL G q hq hq5 hloc H (Subgroup.zpowers a) R Q D hzH hA₀card hRH
      (hzA.trans hcrit.A_normalizes) hR2 hRA₀ ⟨e⟩ hcrit.sylow hRAQ hcrit.D_le_Q hcrit.D_char
      hcrit.comm_D_ne hshape
    exact hESAE G hG.nonabelian hG.kProper hG.charTwo hG.evenRank_eq.le q hq hq5 hloc A R D c hcA
      hc1 ⟨hA, by simpa using hAcard, hRθ, hcrit.A_normalizes, hcrit.comm_eq, ⟨e⟩,
        by simpa using hcrit.card_B, hcR, hDeq, hRC, hshape⟩

end CFSG.RankThree.PartOne
