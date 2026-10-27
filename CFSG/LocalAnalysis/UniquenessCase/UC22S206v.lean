module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206o
public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC22S206r
import CFSG.LocalAnalysis.UniquenessCase.UC22S206q
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre ptCore ptHom)
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G]

theorem uc22s206v_ranks [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hk : (UC6.dataOfSetup4 hS hU S).k = 2) :
    CFSG.Open.pRank 3 S.M ≤ 3 ∧ S.p.Prime ∧ 5 ≤ S.p ∧ 4 ≤ CFSG.Open.pRank S.p S.M := by
  have h3 := three_not_mem_uniqueFourBeta hS hU S hσ hk
  have hp := S.hp.1.1
  exact ⟨UC6.pRank_le_three_of_not_mem_sigma hU S.maxLocal Nat.prime_three (by norm_num)
    fun h => h3 h.1, hp, hp.five_le_of_ne_two_of_ne_three S.hp.1.2.1 fun h => h3 (h ▸ S.hp.1),
    UC6.four_le_pRank_of_sigma S.hp⟩

theorem uc22s206v_pRank_bar [Finite G] {M : Subgroup G} (h3 : CFSG.Open.pRank 3 M ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 M)) ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥M)).exists_card_eq
    rw [hn]
    intro hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
  have h2 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) M.subtype M.subtype_injective ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact (CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥M) hO).le.trans (h2.trans h3)

theorem uc22s206v_disjoint {Y : Type*} [Group Y] {C : Subgroup Y}
    (hZ : Subgroup.center ↥C = ⊥) : Disjoint C (centralizer (C : Set Y)) := by
  rw [Subgroup.disjoint_def]
  intro x hxC hx
  have h : (⟨x, hxC⟩ : ↥C) ∈ Subgroup.center ↥C := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (mem_centralizer_iff.mp hx g g.2)
  rw [hZ, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem uc22s206v_false_of_commute {Y : Type*} [Group Y] [Finite Y]
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3) {C A B : Subgroup Y}
    (hd : Disjoint C (centralizer (C : Set Y))) (hAC : A ≤ C) (hBC : B ≤ centralizer (C : Set Y))
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 2) (hB : IsElemAbelian 3 B)
    (hBc : Nat.card B = 3 ^ 2) : False := by
  obtain ⟨hE, hEc⟩ := uc22s206p_elemAbelian_sup hA hB
    (fun a ha b hb => mem_centralizer_iff.mp (hBC hb) a (hAC ha)) (hd.mono hAC hBC) hAc hBc
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hE hEc
  omega

theorem uc22s206v_normal {Y : Type*} [Group Y] [Finite Y]
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3) {C A : Subgroup Y} (hC : IsComponentOf C ⊤)
    (hd : Disjoint C (centralizer (C : Set Y))) (hAC : A ≤ C) (hA : IsElemAbelian 3 A)
    (hAc : Nat.card A = 3 ^ 2) : C.Normal := by
  refine ⟨fun c hc g => ?_⟩
  by_contra hgc
  have hC' : IsComponentOf (C.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) C).mpr hC
  have hmem : g * c * g⁻¹ ∈ C.map (MulAut.conj g).toMonoidHom := ⟨c, hc, rfl⟩
  have hne : C.map (MulAut.conj g).toMonoidHom ≠ C := fun h => hgc (h ▸ hmem)
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ C hC' hC hne)
  exact uc22s206v_false_of_commute h3 hd hAC ((map_mono hAC).trans hle) hA hAc
    (hA.map _) (by rw [card_map_of_injective (MulAut.conj g).injective, hAc])

theorem uc22s206v_le_of_inner [Finite G] {L : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9}
    {Y : Type*} [Group Y] [Finite Y] (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3)
    {C A : Subgroup Y} (hd : Disjoint C (centralizer (C : Set Y))) (hAC : A ≤ C)
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 2) (φ ψ : ↥(ptCore α i) →* Y)
    (hψC : ∀ k, ψ k ∈ C) (hrel : ∀ k, ∀ m ∈ C, φ k * m * (φ k)⁻¹ = ψ k * m * (ψ k)⁻¹) :
    ∀ k, φ k ∈ C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let χ : ↥(ptCore α i) →* Y := MonoidHom.mk' (fun k => (ψ k)⁻¹ * φ k) fun a b => by
    have h := hrel a _ (C.inv_mem (hψC b))
    simp only [map_mul, mul_inv_rev]
    calc (ψ b)⁻¹ * (ψ a)⁻¹ * (φ a * φ b)
        = (ψ a)⁻¹ * (ψ a * (ψ b)⁻¹ * (ψ a)⁻¹) * φ a * φ b := by group
      _ = (ψ a)⁻¹ * (φ a * (ψ b)⁻¹ * (φ a)⁻¹) * φ a * φ b := by rw [h]
      _ = (ψ a)⁻¹ * φ a * ((ψ b)⁻¹ * φ b) := by group
  have hχ : ∀ k, χ k ∈ centralizer (C : Set Y) := fun k => mem_centralizer_iff.mpr fun m hm => by
    have h := hrel k m hm
    show m * ((ψ k)⁻¹ * φ k) = (ψ k)⁻¹ * φ k * m
    calc m * ((ψ k)⁻¹ * φ k) = (ψ k)⁻¹ * (ψ k * m * (ψ k)⁻¹) * φ k := by group
      _ = (ψ k)⁻¹ * (φ k * m * (φ k)⁻¹) * φ k := by rw [h]
      _ = (ψ k)⁻¹ * φ k * m := by group
  by_contra hne
  push Not at hne
  obtain ⟨k₀, hk₀⟩ := hne
  have hk₀' : χ k₀ ≠ 1 := fun h => hk₀ (by
    have h' : (ψ k₀)⁻¹ * φ k₀ = 1 := h
    rw [← inv_mul_eq_one.mp h']
    exact hψC k₀)
  have hle : ∀ k, χ k = 1 → ptHom α i k = 1 := fun k hk => by
    by_contra hk1
    apply hk₀'
    have htop := uc22s206l_eq_top_of_normal α hα hker χ.normal_ker (MonoidHom.mem_ker.mpr hk) hk1
    have hk₀m : k₀ ∈ χ.ker := by
      rw [htop]
      exact mem_top k₀
    exact MonoidHom.mem_ker.mp hk₀m
  obtain ⟨a, b, -, h₂, hab, ha3, hb3, -, -, h2a, h2b, ha1, hb1⟩ := uc22s206p_elements α hα hker i
  have hconj : ∀ {h x y : ↥(ptCore α i)}, h * x * h⁻¹ = y → χ h * χ x * (χ h)⁻¹ = χ y :=
    fun hxy => by rw [← map_inv, ← map_mul, ← map_mul, hxy]
  obtain ⟨hB, hBc⟩ := uc22s206q_E9 (by rw [← map_mul, ← map_mul, hab])
    (by rw [← map_pow, ha3, map_one]) (by rw [← map_pow, hb3, map_one])
    (fun h => ha1 (hle a h)) (fun h => hb1 (hle b h)) (hconj h2a)
    ((hconj h2b).trans (map_inv χ b))
  exact uc22s206v_false_of_commute h3 hd hAC
    (sup_le (zpowers_le.mpr (hχ a)) (zpowers_le.mpr (hχ b))) hA hAc hB hBc

theorem uc22s206v_component
    [Finite G] (D : Data G)
    (hK331 : InS3.K331) (hN : uc22p20rNativeGriess) (h82 : F08.R82 D) (hk : D.k = 2)
    (h3 : CFSG.Open.pRank 3 D.M ≤ 3) {L : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9}
    (hKM : ptCore α i ≤ D.M) {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T D.M)
    (hTK : T ≤ normalizer (ptCore α i : Set G))
    (hF : ⁅((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)),
      CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥)
    (hNc : ∀ J : Subgroup (Bar2 D.M), IsComponentOf J ⊤ →
      ((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ≤
        normalizer (J : Set (Bar2 D.M)))
    (hout : ∀ J : Subgroup (Bar2 D.M), IsComponentOf J ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (J ⧸ Subgroup.center J))) :
    ∃ C : Subgroup (Bar2 D.M), IsComponentOf C ⊤ ∧ C.Normal ∧ Subgroup.center ↥C = ⊥ ∧
      (IsAlt ↥C 8 ∨ LieModel ↥C .PSL 5 2 1 ∨ IsSpor ↥C .M24 ∨ IsSpor ↥C .J4) ∧
      ∀ k : ↥(ptCore α i),
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (Subgroup.inclusion hKM k) ∈ C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥(ptCore α i) →* Bar2 D.M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).comp (Subgroup.inclusion hKM)
  have hrange : ((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) =
      φ.range := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKM k, k.2, rfl⟩
  rw [hrange] at hF hNc
  haveI : Group.IsPerfect ↥(ptCore α i) :=
    Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect (ptPre α i))
  haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  obtain ⟨C, hC, hKC⟩ := uc22s206o_exists_component φ.range
    (uc22s206l_range_ne_bot α hα hker φ (uc22s206l_ker_le hKM)) hF hNc hout
  haveI : Group.IsPerfect C := ⟨hC.2.2.1⟩
  haveI := hout C hC
  haveI := CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient C
  obtain ⟨ψ, hψ⟩ := uc22s206o_exists_hom φ fun k =>
    CFSG.ComponentClassification.ComponentInnerActions.perfect_normalizer_action_inner
      φ.range C (hNc C hC) ⟨φ k, k, rfl⟩
  have hψ1 : ψ.range ≠ ⊥ := fun hbot => hKC (by
    rintro _ ⟨k, rfl⟩
    refine uc22s206o_mem_centralizer hψ ?_
    have hmem : ψ k ∈ ψ.range := ⟨k, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at hmem)
  obtain ⟨TS, hTS, hTSn⟩ := uc22s206o_sylow hKM hT hTK hC (fun _ => rfl) hψ
  haveI : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2
  obtain ⟨A, hA, ⟨e₁⟩⟩ := uc22s206r_calC D hC
  have h3C : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e₁]
    exact uc22s206r_pRank_le D h82 hk hA
  obtain ⟨e₈⟩ := uc22s206l_nonempty_range α hα hker ψ hψ1
  have hcase : IsAlt (↥C ⧸ Subgroup.center ↥C) 8 ∨
      LieModel (↥C ⧸ Subgroup.center ↥C) .PSL 5 2 1 ∨ IsSpor (↥C ⧸ Subgroup.center ↥C) .M24 ∨
      IsSpor (↥C ⧸ Subgroup.center ↥C) .J4 := by
    rcases hK331 (↥C ⧸ Subgroup.center ↥C) hC.2.2.2 (uc22s206r_isCatalogGroup D hC)
      (uc22s206q_pRank α hα hker ψ hψ1 h3C) TS hTS ψ.range ⟨e₈⟩ hTSn with hR | h
    · obtain ⟨-, -, -, ha1, -⟩ := uc22s206p_rel
      haveI : Nontrivial (alternatingGroup (Fin 8)) := ⟨⟨uc22s206pA0, 1, ha1⟩⟩
      exact Or.inl (uc22s206r_mulEquiv_of_top hR e₈)
    · exact Or.inr h
  have hodd : Odd (Nat.card (Subgroup.center ↥C)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₁).toEquiv]
    exact uc22p20p_odd_center_bar2 ↥A
  have hZ : Subgroup.center ↥C = ⊥ := by
    rcases hcase with h | h | h | h
    · exact uc22s206r_center_alt8 hC.2.2.1 hodd h
    · exact uc22s206r_center_psl52 hN hC.2.2.1 h
    · exact uc22s206r_center_m24 hC.2.2.1 hodd h
    · exact uc22s206r_center_j4 hC.2.2.1 hodd h
  let eC : ↥C ⧸ Subgroup.center ↥C ≃* ↥C :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have h2C : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eC]
    exact uc22s206q_pRank α hα hker ψ hψ1 h3C
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup ↥C)
  rw [h2C] at hEc
  have hY3 := uc22s206v_pRank_bar h3
  have hd := uc22s206v_disjoint hZ
  have hAc : Nat.card (E.map C.subtype) = 3 ^ 2 := by
    rw [card_map_of_injective C.subtype_injective, hEc]
  refine ⟨C, hC, uc22s206v_normal hY3 hC hd (map_subtype_le E) (hE.map _) hAc, hZ,
    uc22s206r_cases_congr eC hcase, uc22s206v_le_of_inner α hα hker hY3 hd (map_subtype_le E)
      (hE.map _) hAc φ (C.subtype.comp (eC.toMonoidHom.comp ψ)) (fun k => (eC (ψ k)).2) ?_⟩
  intro k m hm
  obtain ⟨c, hc, hcm⟩ := hψ k
  have hce : (eC (ψ k) : Bar2 D.M) = c := by
    rw [hc]
    rfl
  show φ k * m * (φ k)⁻¹ = (eC (ψ k) : Bar2 D.M) * m * ((eC (ψ k) : Bar2 D.M))⁻¹
  rw [hce]
  exact hcm m hm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
