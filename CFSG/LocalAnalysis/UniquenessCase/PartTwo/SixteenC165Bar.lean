module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdA
public import CFSG.GroupTheory.MapJoinKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barHom (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {M : Subgroup G}
    (hM : M ≤ stabTil V₀ V) : ↥M →* MulAut (Vtil V₀ V hV) :=
  (actTil V₀ V hV).comp (Subgroup.inclusion hM)

theorem range_barHom (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {M : Subgroup G}
    (hM : M ≤ stabTil V₀ V) : (barHom V₀ V hV hM).range = barSub V₀ V hV M := by
  unfold barHom barSub
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem ker_barHom {G : Type} [Group G] (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {M : Subgroup G}
    (hMn : M ≤ normalizer (V : Set G)) (hM : M ≤ stabTil V₀ V) :
    (barHom V₀ V hV hM).ker = (F11.CTilde M V₀ V).subgroupOf M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hMn]
  constructor
  · intro h
    exact ⟨m.2, hM m.2, h⟩
  · rintro ⟨-, h, h1⟩
    show actTil V₀ V hV (Subgroup.inclusion hM m) = 1
    have : (Subgroup.inclusion hM m : stabTil V₀ V) = ⟨m, h⟩ := Subtype.ext rfl
    rw [this]
    exact h1

theorem map_subgroupOf_barHom {G : Type} [Group G] (V₀ V : Subgroup G)
    (hV : IsElemAbelian 2 V) {M : Subgroup G} (hM : M ≤ stabTil V₀ V) {Y : Subgroup G}
    (hYM : Y ≤ M) :
    (Y.subgroupOf M).map (barHom V₀ V hV hM) = barSub V₀ V hV Y := by
  ext φ
  rw [mem_barSub]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hM x.2⟩, hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.1, hYM hg⟩, hg, rfl⟩

theorem sup_inf_cTilde_eq_of_disjoint_barSub
    {G : Type} [Group G] {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {M : Subgroup G} (hMst : M ≤ stabTil V₀ V)
    {Y₁ Y₂ : Subgroup G} (hY₁M : Y₁ ≤ M) (hY₂M : Y₂ ≤ M)
    (hY₂N : (Y₂.subgroupOf M).Normal)
    {B₁ B₂ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hB₁ : barSub V₀ V hV Y₁ = B₁) (hB₂ : barSub V₀ V hV Y₂ = B₂)
    (hdisj : B₁ ⊓ B₂ = ⊥) :
    (Y₁ ⊔ Y₂) ⊓ F11.CTilde M V₀ V =
      (Y₁ ⊓ F11.CTilde M V₀ V) ⊔ (Y₂ ⊓ F11.CTilde M V₀ V) := by
  have hMn : M ≤ normalizer (V : Set G) := hMst.trans (stabTil_le_normalizer V₀ V)
  let f : ↥M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMst
  let P : Subgroup ↥M := Y₂.subgroupOf M
  let Q : Subgroup ↥M := Y₁.subgroupOf M
  have hPnorm : P.Normal := hY₂N
  have hQnormP : Q ≤ Subgroup.normalizer (P : Set ↥M) := by
    have htop : Subgroup.normalizer (P : Set ↥M) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hPnorm
    rw [htop]
    exact le_top
  have hmapP : P.map f = B₂ := by
    change (Y₂.subgroupOf M).map (barHom V₀ V hV hMst) = B₂
    rw [map_subgroupOf_barHom V₀ V hV hMst hY₂M, hB₂]
  have hmapQ : Q.map f = B₁ := by
    change (Y₁.subgroupOf M).map (barHom V₀ V hV hMst) = B₁
    rw [map_subgroupOf_barHom V₀ V hV hMst hY₁M, hB₁]
  have himg : P.map f ⊓ Q.map f = ⊥ := by
    rw [hmapP, hmapQ, inf_comm, hdisj]
  have hjoin := CFSG.GroupTheory.ker_sup_eq_of_normalizer f P Q hQnormP himg
  have hker : f.ker = (F11.CTilde M V₀ V).subgroupOf M :=
    ker_barHom V₀ V hV hMn hMst
  rw [hker] at hjoin
  have hCM : F11.CTilde M V₀ V ≤ M := fun g hg =>
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg 1) V.one_mem).1
  have hmapPQ : (P ⊔ Q).map M.subtype = Y₁ ⊔ Y₂ := by
    change ((Y₂.subgroupOf M) ⊔ (Y₁.subgroupOf M)).map M.subtype = Y₁ ⊔ Y₂
    rw [← Subgroup.subgroupOf_sup hY₂M hY₁M,
      Subgroup.map_subgroupOf_eq_of_le (sup_le hY₂M hY₁M), sup_comm]
  have hmapC : ((F11.CTilde M V₀ V).subgroupOf M).map M.subtype =
      F11.CTilde M V₀ V :=
    Subgroup.map_subgroupOf_eq_of_le hCM
  have hmap_lhs : ((P ⊔ Q) ⊓ (F11.CTilde M V₀ V).subgroupOf M).map M.subtype =
      (Y₁ ⊔ Y₂) ⊓ F11.CTilde M V₀ V := by
    rw [Subgroup.map_inf_eq _ _ M.subtype M.subtype_injective, hmapPQ, hmapC]
  have hmapPinf : (P ⊓ (F11.CTilde M V₀ V).subgroupOf M).map M.subtype =
      Y₂ ⊓ F11.CTilde M V₀ V := by
    rw [Subgroup.map_inf_eq _ _ M.subtype M.subtype_injective]
    change (Y₂.subgroupOf M).map M.subtype ⊓
      ((F11.CTilde M V₀ V).subgroupOf M).map M.subtype = _
    rw [Subgroup.map_subgroupOf_eq_of_le hY₂M, hmapC]
  have hmapQinf : (Q ⊓ (F11.CTilde M V₀ V).subgroupOf M).map M.subtype =
      Y₁ ⊓ F11.CTilde M V₀ V := by
    rw [Subgroup.map_inf_eq _ _ M.subtype M.subtype_injective]
    change (Y₁.subgroupOf M).map M.subtype ⊓
      ((F11.CTilde M V₀ V).subgroupOf M).map M.subtype = _
    rw [Subgroup.map_subgroupOf_eq_of_le hY₁M, hmapC]
  have hmap_rhs : (((P ⊓ (F11.CTilde M V₀ V).subgroupOf M) ⊔
      (Q ⊓ (F11.CTilde M V₀ V).subgroupOf M)).map M.subtype) =
      (Y₁ ⊓ F11.CTilde M V₀ V) ⊔ (Y₂ ⊓ F11.CTilde M V₀ V) := by
    rw [Subgroup.map_sup, hmapPinf, hmapQinf, sup_comm]
  have hmap_eq : ((P ⊔ Q) ⊓ (F11.CTilde M V₀ V).subgroupOf M).map M.subtype =
      (((P ⊓ (F11.CTilde M V₀ V).subgroupOf M) ⊔
        (Q ⊓ (F11.CTilde M V₀ V).subgroupOf M)).map M.subtype) := by
    rw [hjoin]
  rw [hmap_lhs, hmap_rhs] at hmap_eq
  exact hmap_eq

theorem barHom_fix_iff (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {M : Subgroup G}
    (hM : M ≤ stabTil V₀ V) (y : ↥M) (x : IntMod V hV) :
    barHom V₀ V hV hM y (mkTil V₀ V hV x) = mkTil V₀ V hV x ↔
      (y : G) * x.val * (y : G)⁻¹ * x.val⁻¹ ∈ V₀ := by
  show actTil V₀ V hV (Subgroup.inclusion hM y) (mkTil V₀ V hV x) = mkTil V₀ V hV x ↔ _
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
  exact Iff.rfl

theorem isPGroup_two_subgroupOf_sylow (D : Data G) :
    IsPGroup 2 ↥(D.T.subgroupOf D.M) ∧ ¬ 2 ∣ (D.T.subgroupOf D.M).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hP, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  exact ⟨hP.comap_subtype, hdvd⟩

theorem exists_omegaModel_bar {D : Data G} (h3 : R16_3_2 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) 4 3) :
    ∃ S : OmegaModel (Vtil V₀ V hV), Nat.card S.K = 8 ∧ Nat.card S.omega = 254016 ∧
      S.omega ≤ Mbar D.M V₀ V hV ∧ Mbar D.M V₀ V hV ≤ OmegaModel.omegaNorm S := by
  obtain ⟨S, hSω, hK⟩ := exists_omegaModel_of_omegaPlus_eight h3 hS hΩ
  have h2 : Case163_2 D V₀ V hV L := h3 V₀ V L hV hS.setting hS.ne_bot hS.conc hΩ
  have hs : s15 D.M V₀ V hV L = 1 := h2.2.2
  refine ⟨S, hK, ?_, ?_, ?_⟩
  · rw [hSω, Om8Excl.card_isOmegaPlus_four (by norm_num : 2 ≤ 3) hΩ]
    norm_num
  · rw [hSω]
    exact barSub_mono V₀ V hV hS.setting.hyp151.le
  · intro g hg
    rw [OmegaModel.omegaNorm, Subgroup.mem_normalizer_iff_map_conj_eq, hSω]
    exact lBar_conj_eq_of_s15_eq_one hs hg

theorem exists_isElemAbelian_subgroupOf_of_le_pRank {M : Subgroup G} {p k : ℕ} (hp : p.Prime)
    (h : k ≤ CFSG.Open.pRank p M) :
    ∃ E : Subgroup ↥M, IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAM, hAel, hAcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp M
  have hdvd : p ^ k ∣ Nat.card A := by
    rw [hAcard]
    exact pow_dvd_pow p h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  have hKM : K.map A.subtype ≤ M := (Subgroup.map_subtype_le K).trans hAM
  refine ⟨(K.map A.subtype).subgroupOf M, (hAel.mono (Subgroup.map_subtype_le K)).subgroupOf M, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv,
    Subgroup.card_map_of_injective A.subtype_injective, hK]

theorem card_le_of_isElemAbelian_le_subgroupOf {M C : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hC : CFSG.Open.pRank p C ≤ 1) (hCM : C ≤ M) {E : Subgroup ↥M} (hE : IsElemAbelian p E)
    (hEC : E ≤ C.subgroupOf M) : Nat.card E ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have hle : E.map M.subtype ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hEC hx)
  have hcard : Nat.card (E.map M.subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hk]
  have hkle : k ≤ CFSG.Open.pRank p C :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp C)
      ⟨_, hle, hE.map M.subtype, hcard⟩
  calc Nat.card E = p ^ k := hk
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (hkle.trans hC)
    _ = p := pow_one p

theorem exists_rank_data {D : Data G} (h115 : F11.R115 D)
    {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) (hc4 : Nat.card V₀ ≤ 4) {p : ℕ}
    (hp : p ∈ D.sig) :
    ∃ E : Subgroup ↥D.M, IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E ∧
      ∀ E' : Subgroup ↥D.M, IsElemAbelian p E' →
        E' ≤ (F11.CTilde D.M V₀ V).subgroupOf D.M → Nat.card E' ≤ p := by
  obtain ⟨hC, -, h2⟩ := h115 V₀ V hH hc4 p hp
  have hprime : p.Prime := (D.sig_prime p hp).1
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := by omega
  obtain ⟨E, hE, hEc⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank hprime h3
  refine ⟨E, hE, hEc.ge, fun E' hE' hE'C => ?_⟩
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg =>
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg 1) V.one_mem).1
  exact card_le_of_isElemAbelian_le_subgroupOf hprime hC hCM hE' hE'C

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
