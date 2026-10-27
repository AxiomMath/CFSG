module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Tor
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_modEq_of_dvd {p m : ℕ} (h : p ∣ 2 ^ m + 1) :
    (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have h1 : (p : ℤ) ∣ ((2 ^ m + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h
  push_cast at h1
  rw [show (-1 : ℤ) - 2 ^ m = -(2 ^ m + 1) by ring]
  exact dvd_neg.2 h1

theorem uc22ine229_exists_elemAbelian_of_ncard_two
    {M L A₀ : Subgroup G} (hL : L ∈ calC M) (hc2 : (conjSetOf M L).ncard = 2) {n p r : ℕ}
    (hLS : (IsL2 (Bar2 L) n ∧ ¬ p ∣ 2 ^ n + 1) ∨ (IsSz (Bar2 L) n ∧ ¬ p ∣ 2 ^ (2 * n) + 1))
    (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r)
    (hrn : r ∣ 2 ^ n - 1) (hA₀M : A₀ ≤ M) (hA₀ : IsPGroup p A₀) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      A₀ ≤ normalizer (E : Set G) ∧
      ∀ R : Subgroup G, R ≤ M → IsPGroup r R → E ≤ R → E ≤ centralizer (R : Set G) := by
  obtain ⟨t, htM, hne⟩ : ∃ t ∈ M, L ≠ L.map (MulAut.conj t).toMonoidHom := by
    by_contra h
    push Not at h
    have hsub : conjSetOf M L ⊆ {L} := by
      rintro K ⟨g, hg, rfl⟩
      exact (h g hg).symm
    have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton L)
    rw [Set.ncard_singleton, hc2] at h1
    omega
  obtain ⟨L', hL'⟩ : ∃ L', L' = L.map (MulAut.conj t).toMonoidHom := ⟨_, rfl⟩
  rw [← hL'] at hne
  have hL'S : L' ∈ conjSetOf M L := ⟨t, htM, hL'⟩
  have hL'C : L' ∈ calC M := by
    have h := uc22p22u_calC_conj (le_normalizer : M ≤ normalizer (M : Set G)) hL (M.inv_mem htM)
    rwa [show uniqueFourConj t⁻¹ L = L' by rw [hL']; simp [uniqueFourConj]] at h
  have hc2' : (conjSetOf M L').ncard = 2 := by rw [uc22p2214_conjSetOf_eq hL'S]; exact hc2
  have hW : ∀ W : Subgroup (Bar2 M), (Bar2 L ≃* ↥W) →
      CFSG.Open.pRank r W ≤ 1 ∧ r ∣ Nat.card W ∧ ¬ p ∣ Nat.card (Sylow r ↥W) := by
    intro W e
    have h := uc22ine229_rank_facts (X := ↥W) (n := n) (p := p) (r := r)
      (hLS.imp (fun h => ⟨CFSG.Blueprint.LieModel.of_mulEquiv e h.1, h.2⟩)
        (fun h => ⟨CFSG.Blueprint.LieModel.of_mulEquiv e h.1, h.2⟩)) hp hp2 hr hr2 hrn
    exact ⟨(CFSG.SectionRank.pRank_eq_pRank_top_subgroup W).trans_le h.1, h.2⟩
  obtain ⟨e₁, he₁⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨e₂, -⟩ := uc22p22l_barImage_equiv hL'C
  obtain ⟨f⟩ := uc22p20d_bar2_conj t L
  have hcj : uc22p20bCj t L = L' := hL'.symm
  rw [hcj] at f
  have hZ : center (Bar2 L) = ⊥ := by
    rcases hLS with ⟨hX, -⟩ | ⟨hX, -⟩
    · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
      exact uc22p21k_center_eq_bot hL.2.2
    · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
      exact uc22p21k_center_eq_bot hL.2.2
  have hint : barImage M L ⊓ barImage M L' = ⊥ := by
    refine eq_bot_iff.2 fun q hq => ?_
    obtain ⟨m, hmL, rfl⟩ := uc22p21c_mem_barImage.1 (mem_inf.1 hq).1
    have h1 := uc22ine229_mk_mem_center hL hL'C hne ⟨m, hmL⟩ (mem_inf.1 hq).2
    rw [hZ, mem_bot] at h1
    have h2 := he₁ ⟨m, hmL⟩
    rw [h1, map_one, OneMemClass.coe_one] at h2
    exact mem_bot.2 h2.symm
  have hN : ∀ x : ↥M, Odd (orderOf x) → uc22p21cPi M x ∈
      normalizer (barImage M L : Set (Bar2 M)) ⊓ normalizer (barImage M L' : Set (Bar2 M)) := by
    intro x hx
    rw [← Subgroup.orderOf_coe] at hx
    exact mem_inf.2 ⟨uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hc2 x.2 hx),
      uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hc2' x.2 hx)⟩
  exact uc22ine229_exists_elemAbelian_pair hp hr hp2 hr2 hpr
    (uc22p22l_barImage_commute hL hL'C hne) hint (hW _ e₁) (hW _ (f.trans e₂)) hN hA₀M hA₀

theorem uc22ine229_cong_of_ncard_two {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ n - 1) (hnse : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M) {p : ℕ}
    (hp : p ∈ D.sig) :
    (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]) := by
  by_contra hcon
  have hLS' : (IsL2 (Bar2 L) n ∧ ¬ p ∣ 2 ^ n + 1) ∨
      (IsSz (Bar2 L) n ∧ ¬ p ∣ 2 ^ (2 * n) + 1) :=
    hLS.imp (fun h => ⟨h, fun hd => hcon (Or.inl ⟨h, uc22ine229_modEq_of_dvd hd⟩)⟩)
      (fun h => ⟨h, fun hd => hcon (Or.inr ⟨h, uc22ine229_modEq_of_dvd hd⟩)⟩)
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hsig1 := UC6S846.sig_subset_sig1 hSg hns
  have hsp := UC6S846.sp_of_mem_sig hSg hns hp
  have hrs : r ∉ D.sig := fun h => hnse (UC6S846.sp_of_mem_sig hSg hns h)
  have hpr : p ≠ r := fun h => hrs (h ▸ hp)
  obtain ⟨A₀, hA₀M, hA₀el, hA₀card⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hp)
  obtain ⟨E, hEM, hEel, hEcard, hA₀E, hEZ⟩ := uc22ine229_exists_elemAbelian_of_ncard_two hL hc2
    hLS' hpp hr hp2 hr2 hpr hrn hA₀M hA₀el.isPGroup
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨R', hR'⟩ :=
    (hEel.isPGroup.comap_subtype : IsPGroup r (E.subgroupOf D.M)).exists_le_sylow
  let R : Subgroup G := (R' : Subgroup ↥D.M).map D.M.subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf r R D.M := ⟨R', rfl⟩
  have hRr : IsPGroup r R := R'.isPGroup'.map _
  have hER : E ≤ R := fun x hx => ⟨⟨x, hEM hx⟩, hR' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hEZ' : E ≤ R ⊓ centralizer (R : Set G) :=
    le_inf hER (hEZ R (Subgroup.map_subtype_le _) hRr hER)
  have hG : rankThreeGamma 1 r E ≤ D.M := by
    have h3 := UC6S846.le_pRank' hpp (le_inf hA₀M hA₀E) hA₀el hA₀card
    exact h77 hsig1 p hp hp2 hsp r hr hr2 hrs E hEM hEel hEcard (by omega)
  exact hnse (h614 hsig1 r hr hr2 hrs R hRsyl E hEZ' hEel hEcard hG)

end CFSG.LocalAnalysis.UniquenessCase.UC22
