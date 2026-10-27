module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
import CFSG.Quasithin.Vol2.Ch4Sec2T425U
import CFSG.GroupTheory.PRankLeOneOfIsCyclic
public import CFSG.GroupTheory.CoprimeCentralizerRank
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Perm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua
public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem commutator_le_pCoreOf_of_barImage {M X Y : Subgroup G} (hXM : X ≤ M)
    (hYM : Y ≤ M) (h : ⁅barImage M X, barImage M Y⁆ = ⊥) : ⁅X, Y⁆ ≤ pCoreOf 2 M := by
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  have h1 := CFSG.Quasithin.C1Pack.commutator_mem_pCoreOf_of_barImage hXM hYM h x hx y hy
  simpa [commutatorElement_def] using h1

private theorem inf_sup_pCoreOf_eq_bot {M X Y : Subgroup G} (hXM : X ≤ M) (hYM : Y ≤ M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hXr : IsPGroup r ↥X)
    (hdisj : barImage M X ⊓ barImage M Y = ⊥) :
    X ⊓ (Y ⊔ pCoreOf 2 M) = ⊥ := by
  have hbar : barImage M (Y ⊔ pCoreOf 2 M) = barImage M Y := by
    rw [s13_barImage_sup hYM (CFSG.LieType.BorelTits.pCoreOf_le 2 M),
      uc22p22u_barImage_pCore, sup_bot_eq]
  have hle : X ⊓ (Y ⊔ pCoreOf 2 M) ≤ pCoreOf 2 M := by
    intro x hx
    have hxM : x ∈ M := hXM hx.1
    have hxX : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M X :=
      uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx.1, rfl⟩
    have hxY : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M Y := by
      have hx' : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M (Y ⊔ pCoreOf 2 M) :=
        uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx.2, rfl⟩
      rwa [hbar] at hx'
    have hone : uc22p21cPi M ⟨x, hxM⟩ = 1 := by
      have hmem : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M X ⊓ barImage M Y := ⟨hxX, hxY⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    exact (CFSG.mem_openPCoreOf_iff ⟨x, hxM⟩).2 ((QuotientGroup.eq_one_iff _).1 hone)
  have hXp : X ⊓ pCoreOf 2 M = ⊥ := by
    refine (IsPGroup.disjoint_of_coprime hXr
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ?_).eq_bot
    exact (Nat.coprime_primes hr Nat.prime_two).2 hr2
  have hsub : X ⊓ (Y ⊔ pCoreOf 2 M) ≤ X ⊓ pCoreOf 2 M := le_inf inf_le_left hle
  exact le_bot_iff.mp (hsub.trans (le_of_eq hXp))

omit [Finite G] in
private theorem inf_map_conj_eq_bot {M E₁ E₂ : Subgroup G} (hE₂M : E₂ ≤ M) {n : G}
    (hnO : n ∈ pCoreOf 2 M) (hdisj : E₁ ⊓ (E₂ ⊔ pCoreOf 2 M) = ⊥) :
    E₁ ⊓ E₂.map (MulAut.conj n).toMonoidHom = ⊥ := by
  have hMn : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M)
  have hle : E₂.map (MulAut.conj n).toMonoidHom ≤ E₂ ⊔ pCoreOf 2 M := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have hcommO : n * e * n⁻¹ * e⁻¹ ∈ pCoreOf 2 M := by
      have h2 : e * n * e⁻¹ * n⁻¹ ∈ pCoreOf 2 M :=
        (pCoreOf 2 M).mul_mem ((Subgroup.mem_normalizer_iff.mp (hMn (hE₂M he)) n).mp hnO)
          ((pCoreOf 2 M).inv_mem hnO)
      have h3 : n * e * n⁻¹ * e⁻¹ = (e * n * e⁻¹ * n⁻¹)⁻¹ := by group
      rw [h3]
      exact (pCoreOf 2 M).inv_mem h2
    have h4 : (MulEquiv.toMonoidHom (MulAut.conj n)) e = (n * e * n⁻¹ * e⁻¹) * e := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [h4]
    exact (E₂ ⊔ pCoreOf 2 M).mul_mem (Subgroup.mem_sup_right hcommO) (Subgroup.mem_sup_left he)
  exact le_bot_iff.mp ((inf_le_inf_left E₁ hle).trans hdisj.le)

theorem s136a_exists_conj_sup_permutes {D : Data G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {E₁ E₂ : Subgroup G} (hE₁M : E₁ ≤ D.M) (hE₂M : E₂ ≤ D.M)
    (hE₁ : IsElemAbelian r E₁) (hE₂ : IsElemAbelian r E₂)
    (hperm₁ : Permutes E₁ D.T) (hperm₂ : Permutes E₂ D.T)
    (hcomm : ⁅E₁, E₂⁆ ≤ pCoreOf 2 D.M) (hdisj : E₁ ⊓ (E₂ ⊔ pCoreOf 2 D.M) = ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank r E₁ + CFSG.Open.pRank r E₂) :
    ∃ n ∈ pCoreOf 2 D.M,
      IsElemAbelian r (E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) ∧
      2 ≤ CFSG.Open.pRank r (E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) ∧
      Permutes (E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) D.T := by
  have hMn : D.M ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M)
  have hpO : ¬ r ∣ Nat.card (pCoreOf 2 D.M) :=
    CFSG.Quasithin.H13.Ch4.T425.not_dvd_card_pCoreOf hr hr2 D.M
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hnO, hnle⟩ := CFSG.GroupTheory.exists_map_conj_le_centralizer_of_commutator_le
    (hE₂M.trans hMn) (hE₁M.trans hMn) hE₂.isPGroup hE₁.isPGroup hpO hpO
    (by rw [Subgroup.commutator_comm]; exact hcomm)
  set E₂' : Subgroup G := E₂.map (MulAut.conj n).toMonoidHom
  have hcomm' : ∀ a ∈ E₁, ∀ b ∈ E₂', a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hnle hb) a ha
  have hdisj' : E₁ ⊓ E₂' = ⊥ := inf_map_conj_eq_bot hE₂M hnO hdisj
  refine ⟨n, hnO, ?_, ?_, ?_⟩
  · exact IsElemAbelian.sup_of_commute hE₁ (hE₂.map _) hcomm'
  · show 2 ≤ CFSG.Open.pRank r (E₁ ⊔ E₂')
    have hle := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      (q := r) hr hcomm' hdisj'
    have hconj : CFSG.Open.pRank r E₂' = CFSG.Open.pRank r E₂ :=
      CFSG.LocalAnalysis.RankThreeUC.S15.exists_yComponent_dvd_aux_pRank_map_conj
        hr.one_lt E₂ n
    omega
  · show Permutes (E₁ ⊔ E₂') D.T
    have hnT : n ∈ D.T := CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM) hnO
    have hTn : (D.T.map (MulAut.conj n).toMonoidHom : Subgroup G) = D.T :=
      CFSG.LieType.Steinberg.map_conj_of_mem hnT
    have hperm₂' : Permutes E₂' D.T := by
      have h := CFSG.GroupTheory.map_permutes_map (MulAut.conj n).toMonoidHom hperm₂
      rwa [hTn] at h
    have hsup : ((E₁ ⊔ E₂' : Subgroup G) : Set G) = (E₁ : Set G) * (E₂' : Set G) :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Permutable.coe_sup
        (CFSG.HardMathSupport.Solomon.UniquenessMaximal.permutable_of_mul_subset
          (fun x hx => by
            obtain ⟨a, ha, b, hb, rfl⟩ := hx
            exact ⟨b, hb, a, ha, (hcomm' a ha b hb).symm⟩))
    rw [Permutes, hsup]
    rw [mul_assoc, hperm₂', ← mul_assoc, hperm₁, mul_assoc]

theorem s136a_exists_inP11 {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) {p : ℕ} (hp : p ∈ D.sig) {E₁ E₂ : Subgroup G}
    (hE₁M : E₁ ≤ D.M) (hE₂M : E₂ ≤ D.M) (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂)
    (hperm₁ : Permutes E₁ D.T) (hperm₂ : Permutes E₂ D.T)
    (hcomm : ⁅E₁, E₂⁆ ≤ pCoreOf 2 D.M) (hdisj : E₁ ⊓ (E₂ ⊔ pCoreOf 2 D.M) = ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank p E₁ + CFSG.Open.pRank p E₂) :
    ∃ X : Subgroup G, F11.InP11 D X := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨n, hn, hXeleb, hXrank, hXperm⟩ :=
    s136a_exists_conj_sup_permutes hpp hp2 hE₁M hE₂M hE₁ hE₂ hperm₁ hperm₂ hcomm hdisj hrank
  refine ⟨E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom, ?_⟩
  have hE₂'M : E₂.map (MulAut.conj n).toMonoidHom ≤ D.M := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    have hnM : n ∈ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M) hn
    exact D.M.mul_mem (D.M.mul_mem hnM (hE₂M he)) (D.M.inv_mem hnM)
  have hXM : E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom ≤ D.M := sup_le hE₁M hE₂'M
  have hXp : IsPGroup p ↥(E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) := hXeleb.isPGroup
  have hXexp : ∀ x ∈ E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom, x ^ p = 1 := hXeleb.2
  have hXnc : ¬ IsCyclic ↥(E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) := by
    intro hcyc
    have hle1 : CFSG.Open.pRank p
        (⊤ : Subgroup ↥(E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom)) ≤ 1 :=
      CFSG.pRank_le_one_of_isCyclic hpp hcyc
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hle1
    omega
  exact inP11_of_strongly hpp hp2 (UC6S846.sp_of_mem_sig hSg hns hp) hXM hXp hXexp hXnc hXperm

theorem s136a_indep_of_members (hThin : ThinList13) {D : Data G} (hS : Setting13 D)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hne : barImage D.M L ≠ barImage D.M K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {E₁ E₂ : Subgroup G} (hE₁ : E₁ ≤ L) (hE₂ : E₂ ≤ K) (hE₁r : IsPGroup r ↥E₁) :
    ⁅E₁, E₂⁆ ≤ pCoreOf 2 D.M ∧ E₁ ⊓ (E₂ ⊔ pCoreOf 2 D.M) = ⊥ := by
  have hns : s13_NormalSimple (Bar2 D.M) := s13_normalSimple hThin D hS
  have hLc : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent hL
  have hKc : CFSG.IsComponent (barImage D.M K) := s13_barImage_isComponent hK
  have hcomm : barImage D.M L ≤
      Subgroup.centralizer (barImage D.M K : Set (Bar2 D.M)) :=
    s13_components_commute hns hLc hKc hne
  have hLK : barImage D.M L ⊓ barImage D.M K = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hcomm).trans
      (le_of_eq ((inf_comm ..).trans (s13_Layer13_inf_centralizer_eq_bot hns hKc))))
  have hE₁M : E₁ ≤ D.M := hE₁.trans (s13_le_of_mem_calC hL)
  have hE₂M : E₂ ≤ D.M := hE₂.trans (s13_le_of_mem_calC hK)
  have hbar₁ : barImage D.M E₁ ≤ barImage D.M L := barImage_mono hE₁
  have hbar₂ : barImage D.M E₂ ≤ barImage D.M K := barImage_mono hE₂
  have hcent : barImage D.M E₁ ≤
      Subgroup.centralizer (barImage D.M E₂ : Set (Bar2 D.M)) :=
    (hbar₁.trans hcomm).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hbar₂))
  have hcommBot : ⁅barImage D.M E₁, barImage D.M E₂⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
  have hdisj : barImage D.M E₁ ⊓ barImage D.M E₂ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hbar₁ hbar₂).trans (le_of_eq hLK))
  exact ⟨commutator_le_pCoreOf_of_barImage hE₁M hE₂M hcommBot,
    inf_sup_pCoreOf_eq_bot hE₁M hE₂M hr hr2 hE₁r hdisj⟩

theorem s136a_barImage_Sp_le_centralizer (hThin : ThinList13) {D : Data G} (hS : Setting13 D)
    {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hpL : p ∣ Nat.card (barImage D.M L)) :
    barImage D.M (F13.Sp D.M p) ≤ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) := by
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  have hns : s13_NormalSimple (Bar2 D.M) := s13_normalSimple hThin D hS
  have hLleLp : barImage D.M L ≤ barImage D.M (F13.Lp D.M p) := by
    rw [s13_barImage_Lp D.M hpp, s13_pElementSubgroup_layer_eq hns hpp]
    exact le_iSup₂ (f := fun J (_ : J ∈ s13_compsP (Bar2 D.M) p) => J) _
      (s13_mem_compsP.mpr ⟨s13_barImage_isComponent hL, hpL⟩)
  refine le_trans ?_ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLleLp))
  rw [s13_barImage_Sp D.M hpp, ← s13_barImage_Lp D.M hpp]
  exact s13_Bar13_opp_le p _

theorem s136a_indep_of_Sp (hThin : ThinList13) {D : Data G} (hS : Setting13 D) {p : ℕ}
    (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hpL : p ∣ Nat.card (barImage D.M L)) {E₁ E₂ : Subgroup G} (hE₁ : E₁ ≤ L)
    (hE₂ : E₂ ≤ F13.Sp D.M p ⊔ pCoreOf 2 D.M) (hE₁r : IsPGroup p ↥E₁) :
    ⁅E₁, E₂⁆ ≤ pCoreOf 2 D.M ∧ E₁ ⊓ (E₂ ⊔ pCoreOf 2 D.M) = ⊥ := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns : s13_NormalSimple (Bar2 D.M) := s13_normalSimple hThin D hS
  have hLc : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent hL
  have hE₁M : E₁ ≤ D.M := hE₁.trans (s13_le_of_mem_calC hL)
  have hE₂M : E₂ ≤ D.M :=
    hE₂.trans (sup_le (s13_Sp_le D.M p) (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M))
  have hbar₂ : barImage D.M E₂ ≤ barImage D.M (F13.Sp D.M p) := by
    refine (barImage_mono hE₂).trans (le_of_eq ?_)
    rw [s13_barImage_sup (s13_Sp_le D.M p) (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M),
      uc22p22u_barImage_pCore, sup_bot_eq]
  have hbar₁ : barImage D.M E₁ ≤ barImage D.M L := barImage_mono hE₁
  have hE₂cent : barImage D.M E₂ ≤
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) :=
    hbar₂.trans (s136a_barImage_Sp_le_centralizer hThin hS hp hL hpL)
  have hcent : barImage D.M E₁ ≤
      Subgroup.centralizer (barImage D.M E₂ : Set (Bar2 D.M)) :=
    Subgroup.le_centralizer_iff.mpr
      (hE₂cent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hbar₁)))
  have hcommBot : ⁅barImage D.M E₁, barImage D.M E₂⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
  have hdisj : barImage D.M E₁ ⊓ barImage D.M E₂ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hbar₁ hE₂cent).trans
      (le_of_eq (s13_Layer13_inf_centralizer_eq_bot hns hLc)))
  exact ⟨commutator_le_pCoreOf_of_barImage hE₁M hE₂M hcommBot,
    inf_sup_pCoreOf_eq_bot hE₁M hE₂M hpp hp2 hE₁r hdisj⟩

theorem s136a_inP11_of_members (hThin : ThinList13) {D : Data G} (hS : Setting13 D)
    (hSg : UC6S846.SigmaStd D) {p : ℕ} (hp : p ∈ D.sig) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hEL : ∃ E ≤ L, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧ Permutes E D.T)
    (hEK : ∃ E ≤ K, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧ Permutes E D.T) :
    ∃ X : Subgroup G, F11.InP11 D X := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨E₁, hE₁L, hE₁, hr₁, hperm₁⟩ := hEL
  obtain ⟨E₂, hE₂K, hE₂, hr₂, hperm₂⟩ := hEK
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hc, hd⟩ := s136a_indep_of_members hThin hS hL hK hne hpp hp2 hE₁L hE₂K hE₁.isPGroup
  exact s136a_exists_inP11 hSg (UC6S846.not_solvable_of_mem_calC hL) hp (hE₁L.trans hLM)
    (hE₂K.trans hKM) hE₁ hE₂ hperm₁ hperm₂ hc hd (by omega)

theorem s136a_inP11_of_member_Sp (hThin : ThinList13) {D : Data G} (hS : Setting13 D)
    (hSg : UC6S846.SigmaStd D) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hpL : p ∣ Nat.card (barImage D.M L))
    (hEL : ∃ E ≤ L, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧ Permutes E D.T)
    (hES : ∃ E ≤ F13.Sp D.M p ⊔ pCoreOf 2 D.M, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧
      Permutes E D.T) :
    ∃ X : Subgroup G, F11.InP11 D X := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨E₁, hE₁L, hE₁, hr₁, hperm₁⟩ := hEL
  obtain ⟨E₂, hE₂S, hE₂, hr₂, hperm₂⟩ := hES
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hSM : F13.Sp D.M p ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le (s13_Sp_le D.M p) (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hc, hd⟩ := s136a_indep_of_Sp hThin hS hp hL hpL hE₁L hE₂S hE₁.isPGroup
  exact s136a_exists_inP11 hSg (UC6S846.not_solvable_of_mem_calC hL) hp (hE₁L.trans hLM)
    (hE₂S.trans hSM) hE₁ hE₂ hperm₁ hperm₂ hc hd (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
