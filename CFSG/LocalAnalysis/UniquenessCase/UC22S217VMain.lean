module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VPair
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22S217JPair
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.CGT.PushingUpLit.Transport
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217v_false_of_ncard_two (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2)
    (hJ1 : IsJ1 (Bar2 L)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrJ : r ∣ 175560)
    (hnsp : ¬ IsStronglyPEmbedded r D.M) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hrσ : r ∉ D.sig := fun h => hnsp (UC6S846.sp_of_mem_sig hSg hns h)
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  obtain ⟨K, hK, hKL⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc2]; norm_num) L
  have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
  have hcK : (conjSetOf D.M K).ncard = 2 := by rwa [uc22p2214_conjSetOf_eq hK]
  have hJK := uc22s217v_isJ1_of_mem hJ1 hK
  obtain ⟨A₀, hA₀M, hA₀el, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpp (h4 p hp)
  have hA₀p : IsPGroup p A₀ := hA₀el.isPGroup
  have hodd : ∀ a ∈ A₀, Odd (orderOf a) := fun a ha => by
    obtain ⟨k, hk⟩ := hA₀p ⟨a, ha⟩
    exact uc22ine229_odd_orderOf hpp hp2 (k := k) (by simpa using congrArg Subtype.val hk)
  obtain ⟨A₁, hA₁A₀, hA₁c, hA₁L⟩ := uc22s217v_exists_centralizesBar_le hJ1 hpp hp2 hA₀p
    fun a ha => uc22p2214_mem_normalizer_of_odd hc2 (hA₀M ha) (hodd a ha)
  obtain ⟨A₂, hA₂A₁, hA₂c, hA₂K⟩ := uc22s217v_exists_centralizesBar_le hJK hpp hp2
    (hA₀p.to_le hA₁A₀) fun a ha =>
      uc22p2214_mem_normalizer_of_odd hcK (hA₀M (hA₁A₀ ha)) (hodd a (hA₁A₀ ha))
  have hA₂A₀ : A₂ ≤ A₀ := hA₂A₁.trans hA₁A₀
  have hA₂M : A₂ ≤ D.M := hA₂A₀.trans hA₀M
  have hZ : center (Bar2 L) = ⊥ := by
    haveI := (kJ1_holds _ hJ1).2.1
    exact uc22p21k_center_eq_bot hL.2.2
  have hW : ∀ X ∈ calC D.M, IsJ1 (Bar2 X) →
      CFSG.Open.pRank r (barImage D.M X) ≤ 1 ∧ r ∣ Nat.card (barImage D.M X) := by
    intro X hX hJX
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hX
    have hc : Nat.card (barImage D.M X) = 175560 := by
      rw [← Nat.card_congr e.toEquiv]
      exact (kJ1_holds _ hJX).1
    refine ⟨?_, by rw [hc]; exact hrJ⟩
    by_contra h
    obtain ⟨E, hEX, -, hEc⟩ := CFSG.SectionRank.exists_pRank hr.one_lt (barImage D.M X)
    have h1 : r ^ CFSG.Open.pRank r (barImage D.M X) ∣ 175560 := by
      rw [← hEc, ← hc]
      exact Subgroup.card_dvd_of_le hEX
    exact uc22s217v_not_sq_dvd hr hr2 ((pow_dvd_pow r (by omega)).trans h1)
  have hN : ∀ x : ↥D.M, Odd (orderOf x) → uc22p21cPi D.M x ∈
      normalizer (barImage D.M L : Set (Bar2 D.M)) ⊓
        normalizer (barImage D.M K : Set (Bar2 D.M)) := by
    intro x hx
    rw [← Subgroup.orderOf_coe] at hx
    exact ⟨uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hc2 x.2 hx),
      uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcK x.2 hx)⟩
  obtain ⟨E, hEM, hEel, hEcard, hA₂E, hEZ⟩ := uc22s217v_exists_elemAbelian_centralizer hpp hr hp2
    hr2 hpr (uc22p22l_barImage_commute hL hKC hKL.symm)
    (uc22s217j_barImage_inf_eq_bot hL hKC hKL.symm hZ) (hW L hL hJ1) (hW K hKC hJK) hN hA₂M
    (hA₀p.to_le hA₂A₀) fun a ha => ⟨uc22s217v_mem_centralizer_barImage hL _ (hA₁L a (hA₂A₁ ha)),
      uc22s217v_mem_centralizer_barImage hKC _ (hA₂K a ha)⟩
  obtain ⟨j, hj⟩ := (hA₀p.to_le hA₂A₀).exists_card_eq
  have hj2 : 2 ≤ j := by
    have h1 : p ^ 4 ≤ p ^ (j + 2) :=
      calc p ^ 4 = Nat.card A₀ := hA₀c.symm
        _ ≤ p * Nat.card A₁ := hA₁c
        _ ≤ p * (p * Nat.card A₂) := Nat.mul_le_mul_left _ hA₂c
        _ = p ^ (j + 2) := by rw [hj]; ring
    have := (pow_le_pow_iff_right₀ hpp.one_lt).1 h1
    omega
  have h2p : j ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hpp (le_inf hA₂M hA₂E) (hA₀el.mono hA₂A₀) hj
  have hΓ := h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp) r hr E hEM hEel hEcard (by omega)
    fun X hXE _ => by
      have := h2p.trans (CFSG.SectionRank.pRank_mono hpp.one_lt (inf_le_inf_left _
        ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hXE)).trans
          (Subgroup.centralizer_le_normalizer _))))
      omega
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  exact hnsp (h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E
    (le_inf hER (hEZ R hR.le hR.isPGroup hER)) hEel hEcard hΓ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
