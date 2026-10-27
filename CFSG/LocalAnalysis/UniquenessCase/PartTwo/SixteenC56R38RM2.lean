module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RGeoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLstar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38C
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RM2Steps
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RFLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RProp33
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RKerPrime
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RClaimA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RClaimD
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RMaxLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.WeakClosure81 (NOf)

variable {G : Type} [Group G] [Finite G]

private theorem card_map_eq_of_inf_ker_eq_bot {M H : Type*} [Group M] [Group H] (π : M →* H)
    {F : Subgroup M} (h : F ⊓ π.ker = ⊥) : Nat.card (F.map π) = Nat.card F := by
  have hinj : Function.Injective (π.domRestrict F) := by
    intro x y hxy
    have hmem : (x : M)⁻¹ * (y : M) ∈ F ⊓ π.ker := by
      refine ⟨F.mul_mem (F.inv_mem x.2) y.2, ?_⟩
      change π ((x : M)⁻¹ * (y : M)) = 1
      have hxy' : π (x : M) = π (y : M) := hxy
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    rw [h] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem))
  calc Nat.card (F.map π) = Nat.card (π.domRestrict F).range := by
        rw [MonoidHom.domRestrict_range]
    _ = Nat.card F := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem card_le_pow_of_pRank_le {M : Subgroup G} {p r : ℕ} (hp : p.Prime)
    (h : CFSG.Open.pRank p M ≤ r) {A : Subgroup ↥M} (hA : IsElemAbelian p A) :
    Nat.card A ≤ p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
  have hAM : A.map M.subtype ≤ M := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have hcard : Nat.card (A.map M.subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hk]
  have hkle : k ≤ CFSG.Open.pRank p M :=
    CFSG.SectionRank.le_pRank hp.one_lt hAM (hA.map M.subtype) hcard
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (hkle.trans h)

private theorem pRank_centralizer_le_pRank_inf {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (Q : Subgroup ↥M) :
    CFSG.Open.pRank p (centralizer (Q : Set ↥M)) ≤
      CFSG.Open.pRank p (M ⊓ centralizer ((Q.map M.subtype : Subgroup G) : Set G)) := by
  obtain ⟨A, hAC, hAel, hAcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (centralizer (Q : Set ↥M))
  refine CFSG.SectionRank.le_pRank hp.one_lt (E := A.map M.subtype) ?_ (hAel.map M.subtype)
    (by rw [Subgroup.card_map_of_injective M.subtype_injective, hAcard])
  rintro _ ⟨a, ha, rfl⟩
  refine Subgroup.mem_inf.2 ⟨a.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  have hqa := Subgroup.mem_centralizer_iff.1 (hAC ha) q hq
  exact congrArg Subtype.val hqa

theorem r16_38_m2Gap_holds
    (D : Data G) (h119 : F11.R119 D) (h127 : R127 D) (h63 : UC6.R6_3 D) :
    R16_38_m2Gap D := by
  classical
  intro hSg h1219 h21 h22 h61 hext h5 h76 h614 V₀ V L hV hS hc n hn g hO _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hm : Case1633 D V₀ V hV L 2 := Or.inl ⟨hc, rfl⟩
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  have hK : Nat.card S.K = 4 := by rw [hSK]; norm_num
  have hΩ : Nat.card S.omega = 3600 := by
    rw [hSω, Om8Excl.card_isOmegaPlus_four (by norm_num : 2 ≤ 2) hc.1]
    norm_num
  have h16 : Hyp16 D V₀ V := hS.setting.hyp16
  have hP : PairFacts D.M V₀ V := h16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have h5sig : 5 ∈ D.sig := by rw [hc.2.2]; exact Set.mem_singleton 5
  obtain ⟨y, hys, hyM, hy3', hCV, e, he1, heQ, hfix⟩ :=
    r38_geometry_lift D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO S hSω hSK
  have hy3 : y ^ 3 = 1 := by simpa using hy3'
  have haM : actTil V₀ V hV ⟨y, hys⟩ ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV hyM hys
  have haq : actTil V₀ V hV ⟨y, hys⟩ ^ (2 ^ 2 - 1) = 1 := by
    have h : (⟨y, hys⟩ : stabTil V₀ V) ^ (2 ^ 2 - 1) = 1 := Subtype.ext (by simpa using hy3')
    rw [← map_pow, h, map_one]
  have haN : actTil V₀ V hV ⟨y, hys⟩ ∈ Subgroup.normalizer (S.omega : Set _) :=
    Mbar_le_normalizer_lBar hS S hSω haM
  obtain ⟨E, haE, hEle, hcomm, hexp, hcard⟩ :=
    S.exists_elemAbelian_of_singular_fixed hSK (by norm_num) haN haq he1 heQ hfix
  have hE27 : Nat.card E = 3 ^ 3 := by rw [hcard]; norm_num
  have hEel : IsElemAbelian 3 E :=
    ⟨⟨⟨fun x z => Subtype.ext (hcomm x.1 x.2 z.1 z.2)⟩⟩, fun x hx => by simpa using hexp x hx⟩
  have hnot : actTil V₀ V hV ⟨y, hys⟩ ∉ S.omega := by
    intro haΩ
    have hle : E ≤ S.omega := hEle.trans (sup_le le_rfl ((Subgroup.zpowers_le).2 haΩ))
    have h27 : 3 ^ 3 ∣ 3600 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [hE27, hΩ] at this
    norm_num at h27
  obtain ⟨Lst, hLM, hLn, hLC, hbar⟩ := exists_Lstar_of_case1633 D h119 h127 hS hm
  have hLbar : barSub V₀ V hV Lst = S.omega := hbar.trans hSω.symm
  have hLC' : ¬ 3 ∣ Nat.card ↥(Lst ⊓ F11.CTilde D.M V₀ V) := by simpa using hLC
  let π : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMs
  have hπy : π ⟨y, hyM⟩ = actTil V₀ V hV ⟨y, hys⟩ := rfl
  obtain ⟨F, hFel, hyF, hFker, hFmap⟩ := exists_isElemAbelian_map_eq_of_Lstar hMs
    (q := 3) Nat.prime_three hLM hLn hLC' (a := ⟨y, hyM⟩) (Subtype.ext (by simpa using hy3))
    (by rw [hπy, hLbar]; exact hnot) hEel (by rw [hπy]; exact haE)
    (by rw [hπy, hLbar]; exact hEle)
  have hFcard : Nat.card F = 3 ^ 3 := by
    rw [← card_map_eq_of_inf_ker_eq_bot π hFker, hFmap, hE27]
  have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
    pRank_three_le_three_of_case167_5 D hext h61 h127 hS hc S hSω hK
  have hker3 : ¬ 3 ∣ Nat.card π.ker :=
    not_dvd_card_ker_of_isElemAbelian_card_pow_three π Nat.prime_three hFel hFcard hFker
      (fun A hA => card_le_pow_of_pRank_le Nat.prime_three hM3 hA)
  have hπrange : π.range ≤ OmegaModel.omegaNorm S := by
    rw [range_barHom V₀ V hV hMs]
    exact Mbar_le_normalizer_lBar hS S hSω
  have h81 : ¬ 3 ^ 4 ∣ Nat.card ↥D.M := by
    intro h
    have hrange_dvd : Nat.card π.range ∣ 43200 := by
      have h1 : Nat.card π.range ∣ Nat.card ↥(OmegaModel.omegaNorm S) :=
        Subgroup.card_dvd_of_le hπrange
      have h2 := S.card_omegaNorm_dvd_of_card_four hK
      exact h1.trans (by norm_num at h2 ⊢; exact h2)
    have h1 : 4 ≤ (Nat.card ↥D.M).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 h
    have h2 := factorization_card_le_of_ker_range π Nat.prime_three hker3 hrange_dvd
      (by norm_num : (43200 : ℕ) ≠ 0)
    have h3 : ¬ 4 ≤ (43200 : ℕ).factorization 3 := fun h4 => by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (by norm_num : (43200 : ℕ) ≠ 0)).2 h4
      norm_num at this
    omega
  let F' : Subgroup G := F.map D.M.subtype
  have hF'M : F' ≤ D.M := Subgroup.map_subtype_le F
  have hF'el : IsElemAbelian 3 F' := hFel.map D.M.subtype
  have hF'card : Nat.card F' = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective, hFcard]
  have hF'syl : CFSG.ABGLocalTools.IsSylowOf 3 F' D.M := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hF'M, hF'el.isPGroup, fun hdvd => h81 ?_⟩
    have hmul := Subgroup.relIndex_mul_card (H := F') (K := D.M)
    rw [inf_of_le_left hF'M, hF'card] at hmul
    rw [← hmul, show 3 ^ 4 = 3 * 3 ^ 3 by norm_num]
    exact Nat.mul_dvd_mul hdvd dvd_rfl
  obtain ⟨F₅, hF₅el, hF₅card⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank
    (M := D.M) (p := 5) (k := 3) (by norm_num) (hext.three_le 5 h5sig)
  have hC5 : CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D h61 (Hyp125.hyp11 h127 h16.hyp125)
      (Sixteen21.card_le_four_of_hyp16 h16) h5sig
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun x hx =>
    ((mem_cTilde_iff hV hP.le_normalizer).1 hx).1
  have hker5 : ∀ A : Subgroup ↥D.M, A ≤ π.ker → IsElemAbelian 5 A → Nat.card A ≤ 5 := by
    intro A hA hAel
    refine card_le_of_isElemAbelian_le_subgroupOf (by norm_num) hC5 hCM hAel ?_
    rw [← ker_barHom V₀ V hV hP.le_normalizer hMs]
    exact hA
  obtain ⟨Q, hQF, hQcard, hQrank⟩ := S.exists_subgroup_card_nine_two_le_pRank_five hK hΩ π
    hπrange hker3 hker5 hFel hFcard hyF (by rw [hπy]; exact hnot) hF₅el hF₅card
  have hA : ∃ R Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R D.M ∧
      Q ≤ R ⊓ centralizer (R : Set G) ∧ IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 2 ∧
      1 < CFSG.Open.pRank 5 (D.M ⊓ centralizer (Q : Set G)) := by
    refine ⟨F', Q.map D.M.subtype, hF'syl, ?_, (hFel.mono hQF).map D.M.subtype, ?_, ?_⟩
    · refine le_inf (Subgroup.map_mono hQF) ?_
      rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨f, hf, rfl⟩
      exact congrArg Subtype.val (hFel.comm hf (hQF hq))
    · rw [Subgroup.card_map_of_injective D.M.subtype_injective, hQcard]
    · exact lt_of_lt_of_le (by norm_num) ((hQrank).trans
        (pRank_centralizer_le_pRank_inf (by norm_num) Q))
  have hBC : IsStronglyPEmbedded 3 D.M →
      ∃ v ∈ NOf D.M V g, v ≠ 1 ∧ centralizer ({v} : Set G) ≤ D.M := by
    intro hsp3
    obtain ⟨v, hvN, hv1, hv2, hvrk⟩ := r38_exists_involution_two_le_pRank_of_fixed_line
      (M := D.M) (N := NOf D.M V g) (V₀ := V₀) (V := V) (F := F') (hV := hV)
      hP.le_normalizer (Sixteen21.card_le_four_of_hyp16 h16) hF'M hF'el hF'card
      (Subgroup.mem_map_of_mem D.M.subtype hyF) hys hy3 hCV S hK he1 hfix
    exact ⟨v, hvN, hv1, r38_centralizer_le_of_two_le_pRank D h63 hsp3 hv2 hv1 hvrk⟩
  exact r38_m2_false_of_steps' D hSg h1219 h76 h614 hc hO hA hBC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
