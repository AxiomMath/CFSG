module

public import CFSG.RankThree.PartOne.TAIL.Glue1
public import CFSG.RankThree.PartOne.S12.KF128Rank1
import CFSG.RankThree.PartOne.S11c.Sec66
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import CFSG.RankThree.PartOne.TAIL.Scheme

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem sectionTenOne_of_config (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G} {c : G}
    {L B : Subgroup G} {n : ℕ} (cfg : Sec109.Config p A c L B n) : L ∈ sectionTenOne p A := by
  obtain ⟨-, hAL, -⟩ := moving_maximal_data_at hS cfg.setup cfg.L_mem.1 cfg.c_mem cfg.c_ne_one
    cfg.L_mem.2
  rw [mem_sectionTenOne_iff]
  refine ⟨((sectionTenZeroStar_subset p A).1 cfg.L_mem.1).1, hAL, fun a => ?_⟩
  refine thetaQuotientAction_inner_of_mem_sup hAL a ?_
  obtain ⟨β, hβ, j, hj⟩ := cfg.exists_decomp a.2
  rw [hj]
  refine Subgroup.mul_mem_sup (cfg.B_le_L hβ) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := cfg.mem_L_comm_c hl
  exact (Commute.zpow_right (show Commute l c from this) j).eq

theorem pRank_centralizer_L_le_one (hS : SchreierFor InCatalog) (h107 : InSec10Seven)
    (hKF122 : KF122) {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ}
    (cfg : Sec109.Config 7 A c L B n) :
    CFSG.pRank 7 ↥(Subgroup.centralizer (L : Set G)) ≤ 1 := by
  have hsetup := cfg.setup
  have hbB : B ≤ A := cfg.B_le_A
  have hZL : ¬ 7 ∣ Nat.card (Subgroup.center ↥L) := by
    have := (Sec109.lnTwoOuter ↥L n cfg.model).1
    rw [this]
    simp
  have hH : Sec12Hyp G 7 A c L A :=
    { setup := hsetup
      c_mem := cfg.c_mem
      c_ne_one := cfg.c_ne_one
      L_mem := ⟨⟨cfg.L_mem.1, sectionTenOne_of_config hS cfg⟩, cfg.L_mem.2⟩
      E_elem := cfg.A_elem
      E_le := fun a ha => Subgroup.mem_centralizer_iff.mpr fun g hg => cfg.A_comm g hg a ha
      E_max := fun F hF hFc hAF => by
        refine le_antisymm (fun f hf => ?_) hAF
        exact cfg.mem_of_mem_centralizer (hFc hf)
          (elemPow_eq_one_of_isElementaryAbelian (p := 7) (A := F) f hf) }
  exact (node122_of_prime_to_center hS twoActionInputs_of_S9
    selected_prime_elements_normalize_theta_components
    section_ten_maximal_component_quotient_actor_kernel_cyclic
    section_ten_maximal_moving_theta_components_quasisimple h107 hKF122 hH hZL).2.2.1.le

theorem fusion_of_data {A B L K E S : Subgroup G} {c b d a : G} {n : ℕ}
    (F : MB3.FieldSetting 7 A c L B n b S K E a d) (hS : SchreierFor InCatalog)
    (hKd : KData G K c) (hLd : LData G L B) (hKF1 : KF128Rank1)
    (hAsyl : (A ≤ Subgroup.centralizer ({c} : Set G) ∧ IsPGroup 7 A ∧
        ¬ 7 ∣ A.relIndex (Subgroup.centralizer ({c} : Set G))) ∧
      (A ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
        ¬ 7 ∣ A.relIndex (Subgroup.normalizer (A : Set G) ⊓
          Subgroup.normalizer (Subgroup.zpowers c : Set G)))) :
    ∃ P Q : Subgroup G, (P ≤ ⊤ ∧ IsPGroup 7 P ∧ ¬ 7 ∣ P.relIndex ⊤) ∧ Q ≤ P ∧
      (Q.subgroupOf P).Normal ∧ (∀ x y : ↥P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P) ∧
      c ∈ P ∧ c ∉ Q ∧ ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q := by
  classical
  have cfg := F.config
  have hW := F.witness
  have hp : (7 : ℕ).Prime := by decide
  have hbB : b ∈ B := hW.b_mem
  have hbA : b ∈ A := cfg.B_le_A hbB
  have hb1 : b ≠ 1 := hW.b_ne_one
  have hdB : d ∈ B := F.d_mem_B
  have hdK : d ∈ K := F.d_mem_K
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) := F.K_le_centralizer
  have hAp : ∀ x ∈ A, x ^ 7 = 1 := fun x hx => cfg.pow_p_eq_one hx
  have hBcard : Nat.card B = 7 ^ 2 := by rw [cfg.B_card]; norm_num
  have hBsup : B = Subgroup.zpowers b ⊔ Subgroup.zpowers d :=
    B_eq_sup_of hAp cfg.B_le_A hBcard hbB hb1 hdB F.d_ne_one hdK hKb hKd.inf_centralizer
  have hev : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq cfg.setup).le
  obtain ⟨hqL, -, -⟩ := moving_maximal_data_at hS cfg.setup cfg.L_mem.1 cfg.c_mem cfg.c_ne_one
    cfg.L_mem.2
  have hbp : b ^ 7 = 1 := hAp b hbA
  have hdp : d ^ 7 = 1 := hAp d F.d_mem
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    (moving_maximal_data_at hS cfg.setup F.K_mem.1 hbA hb1 F.K_mem.2).2.1
  obtain ⟨y, hyK, ⟨k, hyord⟩, hyd, hya, hye⟩ := hKF1 G 7 K A a d hp (by norm_num) F.K_qs F.K_even
    ((Sec9A.evenRank_subgroup_le K).trans hev) hKd.rank_one F.K_center cfg.A_elem hAK F.a_mem
    F.d_mem hdK F.d_ne_one F.a_field
    ⟨S, F.S_le, hW.S_ne_bot, hW.S_two, hW.S_norm F.a_mem, hW.S_norm F.d_mem⟩
  have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp (hKb hyK)
  have hBy : B ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [hBsup]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyb.symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc d * y = (y * d * y⁻¹) * y := by rw [hyd]
        _ = y * d := by group
  have hyB : ∀ x ∈ B, y * x * y⁻¹ = x := by
    intro x hx
    have := Subgroup.mem_centralizer_singleton_iff.mp (hBy hx)
    rw [← this]
    group
  have hβmem : y * c * y⁻¹ * c⁻¹ ∈ B :=
    (Subgroup.zpowers_le.mpr hdB) (hye c cfg.c_mem)
  have hβ1 : y * c * y⁻¹ * c⁻¹ ≠ 1 := by
    intro hβ
    have hyc : y * c = c * y := by
      calc y * c = (y * c * y⁻¹ * c⁻¹) * (c * y) := by group
        _ = c * y := by rw [hβ, one_mul]
    have hAy : A ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [cfg.A_eq]
      refine sup_le hBy (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyc.symm
    apply hya
    have := Subgroup.mem_centralizer_singleton_iff.mp (hAy F.a_mem)
    calc y * a * y⁻¹ = (a * y) * y⁻¹ := by rw [this]
      _ = a := by group
  have hyc : ∃ β ∈ B, β ≠ 1 ∧ y * c * y⁻¹ = c * β := by
    refine ⟨y * c * y⁻¹ * c⁻¹, hβmem, hβ1, ?_⟩
    have hcβ : c * (y * c * y⁻¹ * c⁻¹) = (y * c * y⁻¹ * c⁻¹) * c :=
      cfg.A_comm c cfg.c_mem _ (cfg.B_le_A hβmem)
    calc y * c * y⁻¹ = (y * c * y⁻¹ * c⁻¹) * c := by group
      _ = c * (y * c * y⁻¹ * c⁻¹) := hcβ.symm
  have hSH : SchemeHyp G A B c b d y K (L ⊓ Subgroup.normalizer (B : Set G)) :=
    { A_elem := cfg.A_elem
      A_card := cfg.A_card
      B_le := cfg.B_le_A
      B_card := hBcard
      c_mem := cfg.c_mem
      c_notMem := cfg.c_notMem_B
      A_eq := cfg.A_eq
      b_mem := hbB
      b_ne := hb1
      d_mem := hdB
      d_ne := F.d_ne_one
      d_K := hdK
      K_cent_b := hKb
      A_sylow_cent := hAsyl.1
      A_sylow_NH := hAsyl.2
      K_data := hKd
      c_out := F.c_field.2.1
      P_normK := fun x hx hord => mem_normalizer_of_pow_order_thetaComponentsAt hp (by norm_num)
        hev F.K_mem.2 (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hx b hbB).symm) hord
      y₀_K := hyK
      y₀_ord := ⟨k, hyord⟩
      y₀_cB := hyB
      y₀_c := hyc
      M₀_cent := fun x hx => cfg.L_le_centralizer hx.1
      M₀_nrm := inf_le_right
      irr := hLd.irreducible }
  have hadj : ∀ n' ∈ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G),
      ∃ l ∈ L ⊓ Subgroup.normalizer (B : Set G), l * n' ∈ Subgroup.normalizer (K : Set G) := by
    intro n' hn'
    obtain ⟨hnA, hnc⟩ := Subgroup.mem_inf.mp hn'
    have hnB : n' ∈ Subgroup.normalizer (B : Set G) := hSH.normalizer_A_le_normalizer_B hnA
    have hnL : n' ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_L_of_normalizer_B cfg hqL hbB hb1 hnc hnB
    obtain ⟨l, hlM, hl⟩ := hLd.aut_pm n' hnL hnB
    refine ⟨l, hlM, ?_⟩
    refine normalizer_K_of_lines hp F.K_mem.2 F.K_qs F.K_center hdK F.d_ne_one hdp hb1 hbp ?_ ?_
    · rcases hl with h1 | h1
      · rw [h1 b hbB]
        exact Subgroup.mem_zpowers b
      · rw [h1 b hbB]
        exact (Subgroup.zpowers b).inv_mem (Subgroup.mem_zpowers b)
    · rcases hl with h1 | h1
      · rw [h1 d hdB]
        exact Subgroup.mem_zpowers d
      · rw [h1 d hdB]
        exact (Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d)
  exact hSH.scheme hadj

end CFSG.RankThree.PartOne.TAIL
