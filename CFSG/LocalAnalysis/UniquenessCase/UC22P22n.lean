module

public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22nB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22nC
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22n_isTI_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {V X : Subgroup G} (hV : InCalV D.M V) (hXM : X ≤ D.M) (hXp : IsPGroup p X)
    (hXc : ¬ IsCyclic X) (hXV : X ≤ centralizer (V : Set G)) : IsTI V := by
  intro g
  by_cases hbot : V ⊓ conjSubgroup g V = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨⟨u, hu⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
  have huV : u ∈ V := hu.1
  have hsq : ∀ v ∈ V, ∃ n : ℕ, v ^ (2 ^ n) = 1 := fun v hv => ⟨1, by simpa using hV.2.2.2.2 v hv⟩
  have hXcent : ∀ v ∈ V, X ≤ centralizer ({v} : Set G) := by
    intro v hv x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp (hXV hx) v hv
  have hw : g⁻¹ * u * g ∈ V := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hu.2
  have hw1 : g⁻¹ * u * g ≠ 1 := by
    intro h
    apply hu1
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hCw : centralizer ({g⁻¹ * u * g} : Set G) ≤ D.M :=
    PartTwo.centralizer_le_of_noncyclic D h61 hp hXM hXp hXc hw1 (hsq _ hw) (hXcent _ hw)
  have hXM' : X ≤ uniqueFourConj g⁻¹ D.M := by
    intro x hx
    rw [UC6.mem_uniqueFourConj_iff]
    apply hCw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hxu : u * x = x * u := Subgroup.mem_centralizer_iff.mp (hXcent u huV hx) u rfl
    calc g⁻¹ * u * g * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * (u * x) * g := by group
      _ = g⁻¹ * (x * u) * g := by rw [hxu]
      _ = g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * u * g) := by group
  have hmem : uniqueFourConj g⁻¹ D.M ∈ calMOf X :=
    ⟨UC6.isMaxTwoLocal_conj D.maxLocal g⁻¹, hXM'⟩
  rw [h61 p hp X hXM hXp hXc] at hmem
  have hconj : uniqueFourConj g⁻¹ D.M = D.M := Set.mem_singleton_iff.mp hmem
  have hgN : g⁻¹ ∈ normalizer (D.M : Set G) := UC6.uniqueFourConj_eq_self_iff.mp hconj
  have hgM : g⁻¹ ∈ D.M := by
    rw [← UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal]
    exact hgN
  have hgV : g⁻¹ ∈ normalizer (V : Set G) := hV.2.2.1 hgM
  have hVg : uniqueFourConj g⁻¹ V = V := UC6.uniqueFourConj_eq_self_iff.mpr hgV
  have hVc : conjSubgroup g V = V := by
    unfold conjSubgroup
    simpa [uniqueFourConj] using hVg
  change V ⊓ conjSubgroup g V = V
  rw [hVc, inf_idem]

theorem uc22p22n_isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hFE : F ≤ E)
    (hE : IsElemAbelian p E) : IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (hE.comm (hFE a.2) (hFE b.2))⟩⟩, fun x hx => hE.2 x (hFE hx)⟩

theorem uc22p22n_not_isCyclic_of_card {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hP : IsElemAbelian p P) (h : p ^ 2 ≤ Nat.card P) : ¬ IsCyclic P := by
  intro hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hP)
  have hk2 : 2 ≤ k := by
    rw [hk] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have h1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hp hcyc
  have h2 := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hP hk
  omega

theorem uc22p22n_pRank_centralizer_le_one (D : Data G) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : ¬ IsTI V) :
    ∀ p ∈ D.sig, CFSG.Open.pRank p (D.M ⊓ centralizer (V : Set G)) ≤ 1 := by
  intro p hp
  have hpP : p.Prime := (D.sig_prime p hp).1
  by_contra hlt
  obtain ⟨E, hEC, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hpP.one_lt (D.M ⊓ centralizer (V : Set G))
  refine hTI (uc22p22n_isTI_of_noncyclic D h61 hp hV (hEC.trans inf_le_left)
    (uc22p22e_isPGroup_of_elem hEel) ?_ (hEC.trans inf_le_right))
  refine uc22p22n_not_isCyclic_of_card hpP hEel ?_
  rw [hEcard]
  exact Nat.pow_le_pow_right hpP.pos (by omega)

theorem uc22p22n_exists_good (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : ¬ IsTI V) {p : ℕ} (hp : p ∈ D.sig) :
    ∃ P : Subgroup G, P ≤ D.M ∧ IsElemAbelian p P ∧ P ⊓ centralizer (V : Set G) = ⊥ ∧
      p ^ 2 ≤ Nat.card P := by
  have hpP : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt D.M
  have hk3 : 3 ≤ CFSG.Open.pRank p D.M := hx.three_le p hp
  have hAel : IsElemAbelian p (E ⊓ centralizer (V : Set G)) :=
    uc22p22n_isElemAbelian_of_le inf_le_left hEel
  have hAcard : Nat.card ↥(E ⊓ centralizer (V : Set G)) ≤ p := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hAel)
    have h1 : j ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (V : Set G)) :=
      CFSG.SectionRank.le_pRank hpP.one_lt (le_inf (inf_le_left.trans hEM) inf_le_right) hAel hj
    have h2 := uc22p22n_pRank_centralizer_le_one D h61 hV hTI p hp
    rw [hj]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hpP.pos (by omega)
      _ = p := pow_one p
  obtain ⟨P, hPE, hPA, hcardP⟩ := uc22p22nb_exists_complement hpP hEel inf_le_left hAcard
  refine ⟨P, hPE.trans hEM, uc22p22n_isElemAbelian_of_le hPE hEel, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ P ⊓ (E ⊓ centralizer (V : Set G)) := ⟨hx.1, hPE hx.1, hx.2⟩
    rw [hPA] at hmem
    exact hmem
  · rw [hEcard] at hcardP
    have h3 : p ^ 3 ≤ p ^ CFSG.Open.pRank p D.M := Nat.pow_le_pow_right hpP.pos hk3
    have h4 : p * p ^ 2 ≤ p * Nat.card P := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ p * Nat.card P := h3.trans hcardP
    exact Nat.le_of_mul_le_mul_left h4 hpP.pos

theorem uc22p22n_one_lt_pRank_mbar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : InCalV D.M V) (hTI : ¬ IsTI V) :
    ∀ p ∈ D.sig, 1 < CFSG.pRank p (MBar D.M V) := by
  intro p hp
  have hpP : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨P, hPM, hPel, hPV, hP2⟩ := uc22p22n_exists_good D hx h61 hV hTI hp
  haveI : (kerAct D.M V).Normal := kerAct_normal D.M V hV.2.2.1
  let φ : ↥P →* MBar D.M V :=
    (QuotientGroup.mk' (kerAct D.M V).normalCore).comp (Subgroup.inclusion hPM)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    change (QuotientGroup.mk' (kerAct D.M V).normalCore) (Subgroup.inclusion hPM a) = 1 at ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self] at ha
    have hc : (a : G) ∈ centralizer (V : Set G) := Subgroup.mem_subgroupOf.mp ha
    have hmem : (a : G) ∈ P ⊓ centralizer (V : Set G) := ⟨a.2, hc⟩
    rw [hPV] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hPel)
  have hk2 : 2 ≤ k := by
    rw [hk] at hP2
    exact (Nat.pow_le_pow_iff_right hpP.one_lt).1 hP2
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hle := CFSG.SectionRank.le_pRank_of_injective hpP.one_lt
    (fun a b => Subtype.ext (hPel.comm a.2 b.2)) (fun a => Subtype.ext (hPel.2 a a.2)) hk φ hinj
    (H := ⊤) le_top
  omega

theorem uc22p22n_eight_le_card (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : ¬ IsTI V) : 8 ≤ Nat.card V := by
  by_contra hlt
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hpP : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hp3 : 3 ≤ p := by
    have h2 := hpP.two_le
    have h3 := (D.sig_prime p hp).2
    omega
  obtain ⟨P, hPM, hPel, hPV, hP2⟩ := uc22p22n_exists_good D hx h61 hV hTI hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hV.2.2.2)
  have h4 : Nat.card V ≤ 4 := by
    rw [hm] at hlt ⊢
    by_contra h5
    have h6 : 3 ≤ m := by
      by_contra h7
      have h8 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show m ≤ 2 by omega)
      omega
    have h9 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h6
    omega
  exact uc22p22nb_false_of_card_le_four (hPM.trans hV.2.2.1) hPV h4
    (le_trans (by nlinarith) hP2)

theorem uc22p22n_inCalV1_of_not_isTI (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V : Subgroup G} (hV : InCalV D.M V) (hTI : ¬ IsTI V) : InCalV1 D.M D.T V := by
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hpP : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨P, hPM, hPel, hPV, hP2⟩ := uc22p22n_exists_good D hx h61 hV hTI hp
  exact uc22p22nc_inCalV1_of_good D h61 hp hV hPM (uc22p22e_isPGroup_of_elem hPel)
    (uc22p22n_not_isCyclic_of_card hpP hPel hP2) hPV

end CFSG.LocalAnalysis.UniquenessCase.UC22
