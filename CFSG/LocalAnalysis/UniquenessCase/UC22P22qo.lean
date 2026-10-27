module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qn
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qj
public import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qo_layer_conj {X : Subgroup G} {x y : G} (hx : x ∈ X) (hy : y ∈ rankThreeLayer X) :
    x * y * x⁻¹ ∈ rankThreeLayer X := by
  have hX : X.map (MulAut.conj x).toMonoidHom = X :=
    uc22p22qi_map_eq_of_conj_mem (M := X) (K := X)
      (fun k hk z hz => X.mul_mem (X.mul_mem hk hz) (X.inv_mem hk)) hx
  have h := uc22p22qj_layer_map x X
  rw [hX] at h
  have h1 : x * y * x⁻¹ ∈ (rankThreeLayer X).map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
  rwa [← h] at h1

theorem uc22p22qo_ident_pair (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hc2 : UC6.Clause2Print D p P P₀) :
    UC6.inftyOf (centralizer (P₀ : Set G)) = rankThreeLayer (centralizer (P₀ : Set G)) := by
  obtain ⟨h5, hsolv, hwc, ⟨hfact, n, hn2, ⟨e⟩⟩, -, -, -⟩ := hc2
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  haveI : Fact p.Prime := hfact
  have hpP : p.Prime := hfact.out
  have hp2 : p ≠ 2 := by omega
  set X : Subgroup G := centralizer (P₀ : Set G) with hX
  set E : Subgroup G := rankThreeLayer X with hE
  have hEX : E ≤ X := uc22p22q_layer_le X
  have hXE : X ≤ normalizer (E : Set G) := fun x hx =>
    uc22p22qk_mem_normalizer fun y hy => uc22p22qo_layer_conj hx hy
  haveI hEn : (E.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEX).2 hXE
  have h25 : 5 ≤ p ^ n := (by omega : 5 ≤ p).trans (Nat.le_self_pow (by omega) p)
  have hLie : LieModel ↥E .PSL 2 p n :=
    Or.inl ⟨by decide, CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ p n h25 e⟩
  have hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y :=
    uc22p22q_central_of_weaklyClosed hpP hH.sylow.isPGroup hH.le hH.card (uc22p22q_weak_elem hwc)
  have hPX : P ≤ X := fun y hy => Subgroup.mem_centralizer_iff.2 fun z hz => (hcen₀ y hy z hz).symm
  have hPG : IsSylowOf p P ⊤ := uc22p22q_isSylowOf_top D hstd hpσ hH.sylow
  have hSE : IsSylowOf p (P ⊓ E) E := (hPG.of_le hPX le_top).inf_of_le_normalizer hEX hXE
  have hle : P ⊓ E ≤ E := inf_le_right
  have hS' : IsSylowOf p ((P ⊓ E).subgroupOf E) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := p) E (A := (P ⊓ E).subgroupOf E) (B := ⊤)).1
    refine this ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top, Subgroup.range_subtype]
    exact hSE
  obtain ⟨hel, hcard⟩ := uc22p22q_psl2_sylow_elem hpP hp2 hLie hS'
  have helS : IsElemAbelian p (P ⊓ E) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport p _ (P ⊓ E)
      (Subgroup.subgroupOfEquivOfLe hle) hel
  have hcardS : Nat.card (P ⊓ E : Subgroup G) = p ^ n := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hcard
  have hnc : ¬ IsCyclic ↥(P ⊓ E) :=
    uc22p22n_not_isCyclic_of_card hpP helS (by rw [hcardS]; exact Nat.pow_le_pow_right hpP.pos hn2)
  have hSM : P ⊓ E ≤ D.M := inf_le_left.trans hH.sylow.le
  have hNS : normalizer ((P ⊓ E : Subgroup G) : Set G) ≤ D.M :=
    uc22p22q_normalizer_le_of_noncyclic D h61 hpσ hSM hH.sylow.isPGroup.to_inf_left hnc
  haveI := hsolv
  have hsolvN : Group.IsSolvable ↥(X ⊓ normalizer ((P ⊓ E : Subgroup G) : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_right.trans hNS))
      (Subgroup.inclusion_injective _)
  have hq : Group.IsSolvable (↥X ⧸ E.subgroupOf X) := uc22p22qn_quot_solvable hEX hSE hsolvN
  have hsimple : IsSimpleGroup ↥E := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hLie
  have hnc' : ¬ IsMulCommutative ↥E := by
    intro hcomm
    have hq' : (Nat.card ↥E).Prime := Group.is_simple_iff_prime_card.1 hsimple
    have hdvd : p ^ n ∣ Nat.card ↥E := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hp1 : p ∣ Nat.card ↥E := (dvd_pow_self p (by omega)).trans hdvd
    rcases (Nat.prime_dvd_prime_iff_eq hpP hq').1 hp1 with h
    have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hpP.pos hn2
    have h3 : p < p ^ 2 := by nlinarith [hpP.two_le]
    have h4 : p ^ n ≤ Nat.card ↥E := Nat.le_of_dvd hq'.pos hdvd
    omega
  haveI := uc22p22qn_isPerfect_of_simple hnc'
  have hperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 inferInstance
  exact le_antisymm (uc22p22qn_infty_le hq) (uc22p22qn_le_infty hEX hperf)

theorem uc22p22q_r613ident_of (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) (hsp : Sigma2Print D) :
    UC6.R613Ident D := by
  intro p P' P₀' hH'
  obtain ⟨P, P₀, hH, hc2⟩ := hsp p hH'.mem_sig2
  have hid := uc22p22qo_ident_pair D hstd h61 hH hc2
  obtain ⟨m, hm, rfl, rfl⟩ := uc22p22qi_pair_conj D hH hH' hc2.2.2.2.2.2.2
  rw [uc22p22qi_centralizer_map m P₀, uc22p22qi_inftyOf_map m, uc22p22qj_layer_map m, hid]

end CFSG.LocalAnalysis.UniquenessCase.UC22
