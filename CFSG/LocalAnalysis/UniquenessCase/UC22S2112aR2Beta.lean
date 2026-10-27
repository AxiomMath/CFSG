module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r2_two_le_pRank {M L L' X X' C : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hZ : center (Bar2 L) = ⊥) (hXL : X ≤ L) (hX'L' : X' ≤ L') (hXel : IsElemAbelian q X)
    (hX'el : IsElemAbelian q X') (hXc : Nat.card X = q) (hX'c : Nat.card X' = q)
    (hXC : X ≤ C) (hX'C : X' ≤ C) (hCM : C ≤ M) : 2 ≤ Open.pRank q C := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hsn, hp, hqs, hcen⟩ := UC6S846.calC_subgroupOf hL
  obtain ⟨hsn', hp', hqs', -⟩ := UC6S846.calC_subgroupOf hL'
  have hLM : L ≤ M := hL.1.le
  have hL'M : L' ≤ M := hL'.1.le
  let π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hne' : (L.subgroupOf M).map π ≠ (L'.subgroupOf M).map π := by
    intro h
    apply hne
    have := congrArg (Subgroup.map M.subtype) (UC6S846.image_injective hsn hp hsn' hp' h)
    rwa [Subgroup.map_subgroupOf_eq_of_le hLM, Subgroup.map_subgroupOf_eq_of_le hL'M] at this
  have hcomm : ⁅(L.subgroupOf M).map π, (L'.subgroupOf M).map π⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute (UC6S846.isComponent_image hsn hqs)
      (UC6S846.isComponent_image hsn' hqs')).resolve_left hne'
  have hcent : (L.subgroupOf M).map π ≤
      Subgroup.centralizer (((L'.subgroupOf M).map π : Subgroup _) : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hZA : center ↥((L.subgroupOf M).map π) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← Nat.card_congr (Subgroup.centerCongr (UC6S846.barIso hsn)).toEquiv, hcen, hZ,
      Subgroup.card_bot]
  let ψ : ↥C →* ↥M ⧸ CFSG.pCore 2 ↥M := π.comp (Subgroup.inclusion hCM)
  have hkerEq : ψ.rangeRestrict.ker = (CFSG.pCore 2 ↥M).comap (Subgroup.inclusion hCM) := by
    rw [MonoidHom.ker_rangeRestrict]
    ext x
    show π (Subgroup.inclusion hCM x) = 1 ↔ Subgroup.inclusion hCM x ∈ CFSG.pCore 2 ↥M
    exact QuotientGroup.eq_one_iff (Subgroup.inclusion hCM x)
  have hker : IsPGroup 2 ψ.rangeRestrict.ker := by
    rw [hkerEq]
    exact IsPGroup.comap_of_injective CFSG.pCore_isPGroup _ (Subgroup.inclusion_injective hCM)
  have hdisj : ∀ {F : Subgroup ↥C}, IsElemAbelian q F → Disjoint F ψ.rangeRestrict.ker := by
    intro F hF
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    exact UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hF.isPGroup hker hx hxk
  have hcard : ∀ {Y : Subgroup G}, Y ≤ C → IsElemAbelian q Y → Nat.card Y = q →
      Nat.card ((Y.subgroupOf C).map ψ.rangeRestrict) = q ^ 1 := by
    intro Y hYC hYel hYc
    rw [UC6S846.card_map_of_disjoint_ker _ _ (hdisj (hYel.subgroupOf C)), pow_one, ← hYc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv
  have hmem : ∀ {Y K : Subgroup G}, Y ≤ K → ∀ x ∈ (Y.subgroupOf C).map ψ.rangeRestrict,
      (x : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ (K.subgroupOf M).map π := by
    rintro Y K hYK _ ⟨y, hy, rfl⟩
    exact ⟨Subgroup.inclusion hCM y,
      Subgroup.mem_subgroupOf.2 (hYK (Subgroup.mem_subgroupOf.1 hy)), rfl⟩
  have hFF : ∀ x ∈ (X.subgroupOf C).map ψ.rangeRestrict,
      ∀ y ∈ (X'.subgroupOf C).map ψ.rangeRestrict, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (hcent (hmem hXL x hx)) _ (hmem hX'L' y hy)).symm
  have hint : (X.subgroupOf C).map ψ.rangeRestrict ⊓ (X'.subgroupOf C).map ψ.rangeRestrict = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzA := hmem hXL z hz.1
    have hzA' := hmem hX'L' z hz.2
    have hzc : (⟨z, hzA⟩ : ↥((L.subgroupOf M).map π)) ∈ center ↥((L.subgroupOf M).map π) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 (hcent g.2) _ hzA').symm
    rw [hZA, Subgroup.mem_bot] at hzc
    have h1 : (z : ↥M ⧸ CFSG.pCore 2 ↥M) = 1 := congrArg Subtype.val hzc
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  obtain ⟨W, hWel, hWc⟩ := UC6S846.exists_elemAbelian_of_commute hq
    ((hXel.subgroupOf C).map ψ.rangeRestrict) ((hX'el.subgroupOf C).map ψ.rangeRestrict)
    (hcard hXC hXel hXc) (hcard hX'C hX'el hX'c) hFF hint
  have h2 : 2 ≤ CFSG.pRank q ↥ψ.range := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact UC6S846.le_pRank' hq le_top hWel hWc
  exact uc22s2112r2_le_pRank ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ) hker hq hq2 h2

theorem uc22s2112r2_sec7Hyp (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hMs : IsStronglyPEmbedded p D.M)
    (hX : LieModel (BarInf L) .PSL 2 p f) {b : G} (hbB : b ∈ c.B0)
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    F07.Sec7Hyp D p (normalizer ((zpowers b : Subgroup G) : Set G)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hrf, -, hfC, -⟩ := uc22s2112r2_setup hGA hL hp2 hX hb hr hr2 hbr hθ
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hrf' : r ≤ f := Nat.le_of_dvd (by omega) hrf
  have hfr0 : 0 < f / r := Nat.div_pos hrf' hr.pos
  have hLM : L ≤ D.M := hL.1.le
  have h1 : 1 ≤ Open.pRank p (L ⊓ centralizer ({b} : Set G)) := by omega
  obtain ⟨X, hXC, hXel, hXc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h1
  rw [pow_one] at hXc
  have hXL : X ≤ L := hXC.trans inf_le_left
  have hXb : X ≤ centralizer ({b} : Set G) := hXC.trans inf_le_right
  have hXM : X ≤ D.M := hXL.trans hLM
  have hXne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hp.one_lt.ne hXc
  have hXU : X ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded hp hMs hXM hXne hXel.isPGroup
  obtain ⟨hHne, hHM, hCN, -⟩ := uc22s2112r2_normalizer hH c hLM hbB (hbr ▸ hr)
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbr
    have := hr.two_le
    omega
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  obtain ⟨m, hmM, hm⟩ := s21_10 D Ch hH c₀ (zpowers b) (zpowers_ne_bot.2 hb1)
    (zpowers_le.2 hbB) X hXne ⟨p, hp, hXel.isPGroup⟩ (hXb.trans hCN) hXU
  have hinv : m * b * m⁻¹ = b⁻¹ := hm b (mem_zpowers b)
  have hbo : Odd (orderOf b) := by
    rw [hbr]
    exact hr.odd_of_ne_two hr2
  have hmN : m ∉ normalizer (L : Set G) := fun hmN => uc22s2112r2_not_inv hX hb hmN hbo hθ hinv
  have hMm : D.M.map (MulAut.conj m).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hL' : L.map (MulAut.conj m).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M (MulAut.conj m) hMm hL
  have hne : L ≠ L.map (MulAut.conj m).toMonoidHom := fun h =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 h.symm)
  have hX'L' : X.map (MulAut.conj m).toMonoidHom ≤ L.map (MulAut.conj m).toMonoidHom :=
    Subgroup.map_mono hXL
  have hX'c : Nat.card (X.map (MulAut.conj m).toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hXc]
  have hbinv : m * b⁻¹ * m⁻¹ = b := by
    calc m * b⁻¹ * m⁻¹ = (m * b * m⁻¹)⁻¹ := by group
      _ = b := by rw [hinv, inv_inv]
  have hX'b : X.map (MulAut.conj m).toMonoidHom ≤ centralizer ({b} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : Commute x b := Subgroup.mem_centralizer_singleton_iff.1 (hXb hx)
    have h2 := hc.inv_right.conj m
    rw [hbinv] at h2
    exact h2
  have hX'M : X.map (MulAut.conj m).toMonoidHom ≤ D.M := hX'L'.trans hL'.1.le
  have hZ : center (Bar2 L) = ⊥ :=
    uc22s2112r2_center_bar2_eq_bot hGA hL hp2 (fun _ => by omega) hX
  have hrank : 2 ≤ Open.pRank p (normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M) :=
    uc22s2112r2_two_le_pRank hp hp2 hL hL' hne hZ hXL hX'L' hXel (hXel.map _) hXc hX'c
      (le_inf (hXb.trans hCN) hXM) (le_inf (hX'b.trans hCN) hX'M) inf_le_right
  exact ⟨hp, hp2, hMs, hHne, hHM, by omega⟩

theorem uc22s2112r2_beta (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p f : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (hpσ : p ∈ D.sig) (hX : LieModel (BarInf L) .PSL 2 p f) {b : G} (hbB : b ∈ c.B0)
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hfr : f / r = 1) : False := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, hD0⟩ := uc22s2112r2_setup hGA hL hp2 hX hb hr hr2 hbr hθ
  have hMs : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  obtain ⟨-, -, -, hHne, hHM, hrank⟩ :=
    uc22s2112r2_sec7Hyp hGA hH c hL hp2 hMs hX hbB hb hr hr2 hbr hθ
  obtain ⟨-, -, -, hCH⟩ := uc22s2112r2_normalizer hH c hL.1.le hbB (hbr ▸ hr)
  have hq : 7 ≤ p ^ (f / r) := by
    rw [hfr, pow_one]
    exact hp7
  obtain ⟨D0, hD0C, hD0perf, f0, hf0⟩ := hD0 (by omega)
  obtain ⟨hS, hSns, -, hpS⟩ := uc22s2112r2_psl2_facts (k := f / r) hp2 (by omega) (by omega)
  haveI := hS
  exact uc22s2112r2_false_of_kf7 hKF7 hpσ hMs hHne hHM (by omega) (hD0C.trans hCH) hD0perf hSns
    f0 hf0 ((dvd_pow_self p (by omega)).trans hpS) (fun h5 => absurd h5 (by omega))

end CFSG.LocalAnalysis.UniquenessCase.UC22
