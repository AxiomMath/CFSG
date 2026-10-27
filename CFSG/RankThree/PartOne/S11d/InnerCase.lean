module

public import CFSG.RankThree.PartOne.S11d.InnerBasic
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.S11d.FactsInner
public import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S11b.Sec109Assembly
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.RankThreeEven
  CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.Planes
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

namespace Sec109

section Table

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem table123Generic_of_not_PSL (h107 : InSec10Seven)
    (hnot : ∀ m : ℕ, ¬ StatedClassicalModel ↥L .PSL m 2 1) (h : Sec12Hyp G p A c L E)
    (hG : Sec12TwoGeneric p c L E) : Table123Generic p L (A ⊓ L) (E ⊓ L) where
  prime := h.prime
  five_le := Sec12Three.five_le h
  quasisimple := hG.quasisimple
  evenLie := h107 G p A h.setup L (Sec12Three.L_mem_zeroStar h)
  evenRank_le := (Sec9A.evenRank_subgroup_le L).trans h.evenRank_eq.le
  center_pPrime := hG.center_pPrime
  localRank_eq := hG.localRank_eq
  not_PSL_two := hnot
  A₀_le := inf_le_right
  A₀_elem := CFSG.IsElementaryAbelian.of_le h.A_elem inf_le_left
  A₀_card := Sec12Three.card_A_inf_L h hG (Sec12Three.c_not_mem_L h hG.center_pPrime)
  A₀_invariant := Sec12Three.invariant_A_inf_L h hG
  F_le := inf_le_right
  F_elem := CFSG.IsElementaryAbelian.of_le h.E_elem inf_le_left
  A₀_le_F := inf_le_inf_right L h.A_le_E
  F_le_centralizer := fun f hf a ha => by
    have hfE := (Subgroup.mem_inf.1 hf).1
    have haA := (Subgroup.mem_inf.1 ha).1
    exact (Subgroup.mem_centralizer_iff.1 (h.E_le hfE) a haA)
  F_max := fun F' hF'L hF'el hF'c hFF' => Sec12Three.F_max_generic h hG F' hF'L hF'el hF'c hFF'

end Table

section Normalizer

variable {G : Type} [Group G]

theorem mem_normalizer_zpowers_of_zpow {b x : G} {lam : ℤ} (hx3 : x ^ 3 = 1)
    (hxb : x * b * x⁻¹ = b ^ lam) : x ∈ normalizer (zpowers b : Set G) := by
  have fwd : ∀ g ∈ zpowers b, x * g * x⁻¹ ∈ zpowers b := by
    intro g hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨lam * i, ?_⟩
    show b ^ (lam * i) = x * b ^ i * x⁻¹
    rw [zpow_mul, ← hxb, conj_zpow]
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fwd g, fun hg => ?_⟩
  have e : g = x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ := by
    have h3 : x * x * x = 1 := by rw [← pow_three']; exact hx3
    calc g = (x * x * x) * g * (x * x * x)⁻¹ := by rw [h3]; simp
      _ = x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ := by group
  rw [e]
  exact fwd _ (fwd _ hg)

end Normalizer

variable {G : Type} [Group G] [Finite G]

theorem innerCaseImpossible_of (hS : SchreierFor InCatalog) (h107 : InSec10Seven)
    (h108 : InSec10EightMoving) (hKF122 : KF122) (hKF : KF123) (hW : InnerWeylFact) :
    InnerCaseImpossible := by
  intro G _ _ p A c L B n h b S K hWit hK hSK hK1
  have hp7 : p = 7 := h.p_eq
  subst hp7
  have hsetup := h.setup
  have hp : (7 : ℕ).Prime := by norm_num
  have : Fact (7 : ℕ).Prime := ⟨hp⟩
  have hev : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hsetup).le
  have hbB : b ∈ B := hWit.b_mem
  have hbA : b ∈ A := h.B_le_A hbB
  have hb1 : b ≠ 1 := hWit.b_ne_one
  have hKz : K ∈ sectionTenZeroStar 7 A := hK.1
  have hKb : K ∈ thetaComponentsAt 7 b := hK.2
  have hn6 : 6 ≤ n := by rcases h.n_mem with rfl | rfl <;> norm_num
  have hH : Sec12Hyp G 7 A b K A :=
    { setup := hsetup
      c_mem := hbA
      c_ne_one := hb1
      L_mem := ⟨⟨hKz, hK1⟩, hKb⟩
      E_elem := h.A_elem
      E_le := fun a ha => mem_centralizer_iff.mpr fun g hg => h.A_comm g hg a ha
      E_max := fun F hF hFc hAF => by
        have := hF
        refine le_antisymm (fun f hf => ?_) hAF
        exact h.mem_of_mem_centralizer (hFc hf)
          (elemPow_eq_one_of_isElementaryAbelian (p := 7) (A := F) f hf) }
  obtain ⟨hKq, hAK, hker⟩ := moving_maximal_data_at hS hsetup hKz hbA hb1 hKb
  have hZ : ¬ 7 ∣ Nat.card (Subgroup.center ↥K) := by
    intro hdvd
    have hns := Sec12TwoAssembly.not_isSimpleGroup_quotient_theta hp hKq hdvd
    rcases h108 G 7 A hsetup b hbA hb1 K hK with hs | ⟨hp5, -⟩
    · exact hns hs
    · omega
  obtain ⟨hq', hrank, hCrank, hmem, hE⟩ := node122_of_prime_to_center hS twoActionInputs_of_S9
    selected_prime_elements_normalize_theta_components
    section_ten_maximal_component_quotient_actor_kernel_cyclic
    section_ten_maximal_moving_theta_components_quasisimple h107 hKF122 hH hZ
  have hG : Sec12TwoGeneric 7 b K A := ⟨hZ, hq', hrank, hCrank, hmem, hE⟩
  obtain ⟨x, lam, hxL, hx1, hxNB, hx3, hlam, hxB⟩ := h.exists_x3
  have hxc : x * c = c * x := h.mem_L_comm_c hxL
  have hxNA : x ∈ normalizer (A : Set G) := h.mem_normalizer_A hxNB hxc
  have hxb : x * b * x⁻¹ = b ^ lam := hxB b hbB
  have hxbN : x ∈ cNormalizer b := mem_normalizer_zpowers_of_zpow hx3 hxb
  have hxK : x ∈ normalizer (K : Set G) :=
    Sec12TwoAssembly.mem_normalizer_of_structure hH
      selected_prime_elements_normalize_theta_components hq' (B := A ⊓ K) inf_le_left
      inf_le_right hE.le (Sec12TwoAssembly.not_E_le_centralizer_of_generic hH hG) hxbN hxNA
  by_cases hLn : ∃ m : ℕ, StatedClassicalModel ↥K .PSL m 2 1
  ·
    obtain ⟨m, hm⟩ := hLn
    have hevK : evenRank ↥K ≤ 3 := (Sec9A.evenRank_subgroup_le K).trans hev
    have h2 : 2 ≤ localRank 7 ↥K := hrank.ge
    obtain ⟨-, hm67⟩ := Sec109.sec65LnTwo ↥K m 7 hm hp (by norm_num) hevK h2
    have hxKm : x ∈ K :=
      S11d.mem_of_pow_three hev hm (by omega) hxK (a := 1) (by simpa using hx3)
    have hxb' : x * b = b * x :=
      mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp hKb).1 hxKm)
    have h3 : x * b * x⁻¹ = b := by rw [hxb']; group
    exact h.zpow_ne_self hbA hb1 hlam (hxb.symm.trans h3)
  · push Not at hLn
    have hT := table123Generic_of_not_PSL h107 hLn hH hG
    obtain ⟨r, hr1, hr12, hr11, hrow⟩ := (hKF G 7 K (A ⊓ K) (A ⊓ K)).1 hT
    have hbK : b ∉ K := Sec12Three.c_not_mem_L hH hZ
    have hcardF : Nat.card ↥(A ⊓ K) = 7 ^ 2 := Sec12Three.card_A_inf_L hH hG hbK
    have hrk : RowRank r = 2 := by
      have h1 := hrow.2.1
      rw [hcardF] at h1
      exact (Nat.pow_right_injective hp.two_le h1).symm
    have hr8 : r ≤ 8 := by
      interval_cases r <;> first | omega | (exfalso; revert hrk; decide)
    have hxF : x ∈ normalizer ((A ⊓ K : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hxNA, hxK⟩
    have hbp : b ^ 7 = 1 := h.pow_p_eq_one hbA
    have hKb' : K ⊓ zpowers b = ⊥ := Sec12Two.inf_zpowers_eq_bot hp hbp hbK
    have hbord : orderOf b = 7 := orderOf_eq_prime hbp hb1
    have hcF : c ∈ A ⊓ K := by
      have hcdec : c ∈ (A ⊓ K) ⊔ zpowers b := hE ▸ h.c_mem
      have hcomm : ∀ β ∈ A ⊓ K, Commute β b := fun β hβ => h.A_comm β hβ.1 b hbA
      obtain ⟨f, hf, i, hfi⟩ := (S11d.mem_sup_zpowers_iff hcomm).mp hcdec
      set f' := x * f * x⁻¹ with hf'
      have hf'F : f' ∈ A ⊓ K := (mem_normalizer_iff.mp hxF f).mp hf
      have e1 : x * c * x⁻¹ = c := by rw [hxc]; group
      have e3 : x * b ^ i * x⁻¹ = b ^ (lam * i) := by
        rw [← conj_zpow, hxb, ← zpow_mul]
      have e2 : x * c * x⁻¹ = f' * b ^ (lam * i) := by
        calc x * c * x⁻¹ = x * (f * b ^ i) * x⁻¹ := by rw [← hfi]
          _ = (x * f * x⁻¹) * (x * b ^ i * x⁻¹) := by group
          _ = f' * b ^ (lam * i) := by rw [e3]
      have h1 : f * b ^ i = f' * b ^ (lam * i) := by
        calc f * b ^ i = c := hfi.symm
          _ = x * c * x⁻¹ := e1.symm
          _ = f' * b ^ (lam * i) := e2
      have h2 : f'⁻¹ * f = b ^ ((lam - 1) * i) := by
        calc f'⁻¹ * f = f'⁻¹ * (f * b ^ i) * (b ^ i)⁻¹ := by group
          _ = f'⁻¹ * (f' * b ^ (lam * i)) * (b ^ i)⁻¹ := by rw [h1]
          _ = b ^ (lam * i) * (b ^ i)⁻¹ := by group
          _ = b ^ ((lam - 1) * i) := by
            rw [← zpow_neg, ← zpow_add]
            congr 1
            ring
      have h3 : b ^ ((lam - 1) * i) ∈ K ⊓ zpowers b := by
        refine ⟨?_, ⟨(lam - 1) * i, rfl⟩⟩
        rw [← h2]
        exact K.mul_mem (K.inv_mem hf'F.2) hf.2
      rw [hKb', mem_bot] at h3
      have h4 : ((7 : ℕ) : ℤ) ∣ (lam - 1) * i := by
        have := orderOf_dvd_iff_zpow_eq_one.mpr h3
        rwa [hbord] at this
      have hpZ : Prime ((7 : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hlam' : ¬ ((7 : ℕ) : ℤ) ∣ lam - 1 := by exact_mod_cast hlam
      rcases hpZ.dvd_or_dvd h4 with h5 | h5
      · exact absurd h5 hlam'
      · have h6 : b ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hbord])
        rw [hfi, h6, mul_one]
        exact hf
    have hmove : ∃ f ∈ A ⊓ K, x * f * x⁻¹ ≠ f := by
      by_contra hno
      push Not at hno
      have hle : A ⊓ K ≤ zpowers c := by
        intro f hf
        obtain ⟨β, hβ, j, hj⟩ := h.exists_decomp hf.1
        have e3 : x * c ^ j * x⁻¹ = c ^ j := by
          rw [← conj_zpow]
          have e1 : x * c * x⁻¹ = c := by rw [hxc]; group
          rw [e1]
        have e1 : x * f * x⁻¹ = β ^ lam * c ^ j := by
          calc x * f * x⁻¹ = (x * β * x⁻¹) * (x * c ^ j * x⁻¹) := by rw [hj]; group
            _ = β ^ lam * c ^ j := by rw [hxB β hβ, e3]
        have e4 : β ^ lam = β := by
          have h1 := e1.symm.trans (hno f hf)
          rw [hj] at h1
          exact mul_right_cancel h1
        have hβ1 : β = 1 := by
          by_contra hne
          exact h.zpow_ne_self (h.B_le_A hβ) hne hlam e4
        rw [hj, hβ1, one_mul]
        exact zpow_mem (mem_zpowers c) j
      have hcard := Subgroup.card_le_of_le hle
      rw [hcardF, Nat.card_zpowers, orderOf_eq_prime (h.pow_p_eq_one h.c_mem) h.c_ne_one] at hcard
      norm_num at hcard
    obtain ⟨y, hyK, hyN, ⟨k, hyk⟩, hyc⟩ := hW G K (A ⊓ K) r inf_le_right hT.F_elem hr1 hr8 hrow c x
      hxK hxF hx3 hcF h.c_ne_one hxc hmove
    have hqL : CFSG.IsQuasisimple ↥L :=
      (moving_maximal_data_at hS hsetup h.L_mem.1 h.c_mem h.c_ne_one h.L_mem.2).1
    have hyb : y * b = b * y :=
      mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp hKb).1 hyK)
    have hyL : y ∈ normalizer (L : Set G) := h.mem_normalizer_L hqL hbB hb1 hyN hyb
    have hyLm : y ∈ L := S11d.mem_of_pow_three hev h.model hn6 hyL hyk
    exact hyc (by rw [h.mem_L_comm_c hyLm]; group)

end Sec109

end CFSG.RankThree.PartOne
