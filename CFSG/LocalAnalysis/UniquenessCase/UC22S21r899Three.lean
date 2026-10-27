module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Tor
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r899_exists_elemAbelian_of_ncard_three
    {M L A₀ : Subgroup G} (hL : L ∈ calC M) (hc3 : (conjSetOf M L).ncard = 3) {n p r : ℕ}
    (hLS : (IsL2 (Bar2 L) n ∧ ¬ p ∣ 2 ^ n + 1) ∨ (IsSz (Bar2 L) n ∧ ¬ p ∣ 2 ^ (2 * n) + 1))
    (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hpr : p ≠ r)
    (hrn : r ∣ 2 ^ n - 1) (hA₀M : A₀ ≤ M) (hA₀ : IsPGroup p A₀)
    (hA₀N : ∀ a ∈ A₀, ∀ N ∈ conjSetOf M L, a ∈ normalizer (N : Set G)) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      A₀ ≤ normalizer (E : Set G) ∧
      ∀ R : Subgroup G, R ≤ M → IsPGroup r R → E ≤ R → E ≤ centralizer (R : Set G) := by
  have hLmem : L ∈ conjSetOf M L := ⟨1, M.one_mem, by ext x; simp⟩
  obtain ⟨t, htM, hne⟩ : ∃ t ∈ M, L ≠ L.map (MulAut.conj t).toMonoidHom := by
    by_contra h
    push Not at h
    have hsub : conjSetOf M L ⊆ {L} := by
      rintro K ⟨g, hg, rfl⟩
      exact (h g hg).symm
    have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton L)
    rw [Set.ncard_singleton, hc3] at h1
    omega
  obtain ⟨L', hL'⟩ : ∃ L', L' = L.map (MulAut.conj t).toMonoidHom := ⟨_, rfl⟩
  rw [← hL'] at hne
  have hL'S : L' ∈ conjSetOf M L := ⟨t, htM, hL'⟩
  have hL'C : L' ∈ calC M := by
    have h := uc22p22u_calC_conj (le_normalizer : M ≤ normalizer (M : Set G)) hL (M.inv_mem htM)
    rwa [show uniqueFourConj t⁻¹ L = L' by rw [hL']; simp [uniqueFourConj]] at h
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
  have hNp : ∀ x : ↥M, (x : G) ∈ A₀ → uc22p21cPi M x ∈
      normalizer (barImage M L : Set (Bar2 M)) ⊓ normalizer (barImage M L' : Set (Bar2 M)) :=
    fun x hx => mem_inf.2 ⟨uc22ine229_mk_mem_normalizer (hA₀N x hx L hLmem),
      uc22ine229_mk_mem_normalizer (hA₀N x hx L' hL'S)⟩
  have hNr : ∀ x : ↥M, (∃ k : ℕ, x ^ r ^ k = 1) → uc22p21cPi M x ∈
      normalizer (barImage M L : Set (Bar2 M)) ⊓ normalizer (barImage M L' : Set (Bar2 M)) := by
    rintro x ⟨k, hk⟩
    have hxk : (x : G) ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hall := uc22r899_mem_normalizer_of_fix hc3 x.2 hr hr2 hxk fun h => absurd h hr3
    exact mem_inf.2 ⟨uc22ine229_mk_mem_normalizer (hall L hLmem),
      uc22ine229_mk_mem_normalizer (hall L' hL'S)⟩
  exact uc22r899_exists_elemAbelian_pair hp hr hp2 hr2 hpr
    (uc22p22l_barImage_commute hL hL'C hne) hint (hW _ e₁) (hW _ (f.trans e₂)) hNp hNr hA₀M hA₀

theorem uc22r899_cong_of_ncard_three {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ} (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1)
    (hnse : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M) {p : ℕ} (hp : p ∈ D.sig) :
    (IsL2 (Bar2 L) n ∧ p ∣ 2 ^ n + 1) ∨ (IsSz (Bar2 L) n ∧ p ∣ 2 ^ (2 * n) + 1) := by
  by_contra hcon
  have hLS' : (IsL2 (Bar2 L) n ∧ ¬ p ∣ 2 ^ n + 1) ∨
      (IsSz (Bar2 L) n ∧ ¬ p ∣ 2 ^ (2 * n) + 1) :=
    hLS.imp (fun h => ⟨h, fun hd => hcon (Or.inl ⟨h, hd⟩)⟩)
      (fun h => ⟨h, fun hd => hcon (Or.inr ⟨h, hd⟩)⟩)
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hr3 : r ≠ 3 := fun h =>
    CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_three_dvd_pow_sub_one hs (h ▸ hrs)
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hsig1 := UC6S846.sig_subset_sig1 hSg hns
  have hsp := UC6S846.sp_of_mem_sig hSg hns hp
  have hrσ : r ∉ D.sig := fun h => hnse (UC6S846.sp_of_mem_sig hSg hns h)
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  obtain ⟨P, hPM, hPel, hPcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hfour p hp)
  obtain ⟨A₀, hA₀P, hA₀el, hA₀card, hA₀N⟩ :=
    uc22r899_exists_elemAbelian_stab hpp hp2 hc3 hPM hPel hPcard
  have hA₀M : A₀ ≤ D.M := hA₀P.trans hPM
  obtain ⟨E, hEM, hEel, hEcard, hA₀E, hEZ⟩ := uc22r899_exists_elemAbelian_of_ncard_three hL hc3
    hLS' hpp hr hp2 hr2 hr3 hpr hrn hA₀M hA₀el.isPGroup hA₀N
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
    exact h77 hsig1 p hp hp2 hsp r hr hr2 hrσ E hEM hEel hEcard (by omega)
  exact hnse (h614 hsig1 r hr hr2 hrσ R hRsyl E hEZ' hEel hEcard hG)

end CFSG.LocalAnalysis.UniquenessCase.UC22
