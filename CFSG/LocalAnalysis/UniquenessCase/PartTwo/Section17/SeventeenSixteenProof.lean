module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieOddRankFourHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalAutPRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ReeSylowGenerationHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L2Over17
public import CFSG.GroupTheory.ReeCentralizerGeneration
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_barPreimage (L : Subgroup G) (K : Subgroup (Bar2 L)) :
    (barPreimage L K).subgroupOf L = K.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  ext z
  rw [Subgroup.mem_subgroupOf, barPreimage, Subgroup.mem_map]
  constructor
  · rintro ⟨z', hz', hz'z⟩
    have hz'z' : z' = z := L.subtype_injective hz'z
    subst hz'z'
    exact hz'
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem exists_elemAbelian_le_centOverO2 (D : Data G) (L : Subgroup G) (hLM : L ≤ D.M)
    (hLnorm : (L.subgroupOf D.M).Normal) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ CFSG.Open.pRank p D.M)
    (hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1) :
    ∃ P : Subgroup G, P ≤ D.M ∧ P ≤ F08.CentOverO2 D.M L ∧
      CFSG.Open.IsElemAbelian p P ∧ 2 ≤ CFSG.Open.pRank p P := by
  classical
  have hM : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  let ρ : D.M →* MulAut (Bar2 L) :=
    (UC6S846.rhoL L).comp (Subgroup.inclusion hM)
  have hker_le : ρ.ker ≤ (F08.CentOverO2 D.M L).subgroupOf D.M := by
    rw [← Subgroup.comap_subtype, centOverO2_eq_ker_map hM,
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective]
  have hρrank :=
    CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hp ρ (⊤ : Subgroup D.M)
  have htop : CFSG.Open.pRank p (⊤ : Subgroup D.M) = CFSG.Open.pRank p D.M :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M).symm
  have hp3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup D.M) := by rwa [htop]
  have hrange : CFSG.Open.pRank p ((⊤ : Subgroup D.M).map ρ) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt
      (le_top : ((⊤ : Subgroup D.M).map ρ : Subgroup (MulAut (Bar2 L))) ≤ ⊤)).trans hAut
  have hkerrank : 2 ≤ CFSG.Open.pRank p ((⊤ : Subgroup D.M) ⊓ ρ.ker) := by omega
  obtain ⟨P', hP'le, hP'el, hP'card⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt ((⊤ : Subgroup D.M) ⊓ ρ.ker)
  let P : Subgroup G := P'.map D.M.subtype
  have hP_el : CFSG.Open.IsElemAbelian p P := hP'el.map D.M.subtype
  have hPcard : Nat.card P = p ^ CFSG.Open.pRank p ((⊤ : Subgroup D.M) ⊓ ρ.ker) := by
    rw [show P = P'.map D.M.subtype from rfl,
      Subgroup.card_map_of_injective D.M.subtype_injective, hP'card]
  refine ⟨P, Subgroup.map_subtype_le _, ?_, hP_el, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hker_le (hP'le hy).2)
  · have hle := CFSG.SectionRank.le_pRank hp.one_lt (le_refl P) hP_el hPcard
    omega

theorem exists_centralized_elemAbelian_le_sup (D : Data G) (L : Subgroup G) (hLM : L ≤ D.M)
    (hLnorm : (L.subgroupOf D.M).Normal) {r p : ℕ}
    (K₁ K₂ : Subgroup (Bar2 L)) (E₀ : Subgroup G)
    (hE₀Y : E₀ ≤ barPreimage L K₁ ⊔ barPreimage L K₂)
    (hE₀el : CFSG.Open.IsElemAbelian r E₀) (hE₀card : Nat.card E₀ = r ^ 2)
    (P : Subgroup G) (hP_le_M : P ≤ D.M) (hP_cent : P ≤ F08.CentOverO2 D.M L)
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hPp : IsPGroup p P) :
    ∃ E : Subgroup G, E ≤ barPreimage L K₁ ⊔ barPreimage L K₂ ∧
      CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      E ≤ Subgroup.centralizer (P : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  let Y : Subgroup G := barPreimage L K₁ ⊔ barPreimage L K₂
  let O : Subgroup G := pCoreOf 2 L
  have hOY : O ≤ Y := by
    dsimp only [O, Y]
    exact (pCoreOf_le_barPreimage L K₁).trans le_sup_left
  have hYL : Y ≤ L := by
    dsimp only [Y]
    exact sup_le (uc22p21c_barPreimage_le L K₁) (uc22p21c_barPreimage_le L K₂)
  have hM : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hP_normL : P ≤ Subgroup.normalizer (L : Set G) := hP_le_M.trans hM
  have hP_normO : P ≤ Subgroup.normalizer (O : Set G) :=
    hP_normL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L)
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hO_p : ¬ p ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hO_r : ¬ r ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hstep : ∀ x ∈ P, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
    intro x hx y hy
    have hxO := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff).mp (hP_cent hx)
    have hcom : x * y * x⁻¹ * y⁻¹ ∈ O := hxO.2 y (hYL hy)
    have hxy : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [hxy]
    exact Y.mul_mem (hOY hcom) hy
  have hP_normY : P ≤ Subgroup.normalizer (Y : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hstep x hx y hy, fun hy => ?_⟩
    have h := hstep x⁻¹ (P.inv_mem hx) (x * y * x⁻¹) hy
    simpa [mul_assoc] using h
  have hcomm : ⁅Y, P⁆ ≤ O := by
    rw [Subgroup.commutator_comm]
    refine Subgroup.commutator_le.mpr ?_
    intro x hx y hy
    exact (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff).mp
      (hP_cent hx) |>.2 y (hYL hy)
  obtain ⟨S, hS_syl, hS_cent⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := p) (q := r) (X := Y) (N := O) (R := P)
      hOY hP_normY hP_normO hPp hO_p hcomm hO_r
  obtain ⟨S₀, hS₀⟩ := hS_syl
  let E₀Y : Subgroup ↥Y := E₀.subgroupOf Y
  have hE₀Yel : CFSG.Open.IsElemAbelian r E₀Y := hE₀el.subgroupOf Y
  obtain ⟨T, hE₀T⟩ := hE₀Yel.isPGroup.exists_le_sylow
  let e : (T : Subgroup ↥Y) ≃* (S₀ : Subgroup ↥Y) := Sylow.equiv T S₀
  let E₀T : Subgroup ↥T := E₀Y.subgroupOf T
  let E : Subgroup G := (E₀T.map e.toMonoidHom).map (Y.subtype.comp (S₀ : Subgroup ↥Y).subtype)
  have hEY : E ≤ Y := by
    rintro z ⟨w, _, rfl⟩
    exact ((S₀ : Subgroup ↥Y).subtype w).property
  have hES : E ≤ S := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hw
    rw [← hS₀]
    exact Subgroup.mem_map.mpr ⟨(S₀ : Subgroup ↥Y).subtype (e t), (e t).property, rfl⟩
  refine ⟨E, hEY, ?_, ?_, hES.trans hS_cent⟩
  · exact ((hE₀Yel.subgroupOf T).map e.toMonoidHom).map
      (Y.subtype.comp (S₀ : Subgroup ↥Y).subtype)
  · have hf_inj : Function.Injective
        (Y.subtype.comp (S₀ : Subgroup ↥Y).subtype) :=
      Y.subtype_injective.comp (S₀ : Subgroup ↥Y).subtype_injective
    rw [show E = (E₀T.map e.toMonoidHom).map
        (Y.subtype.comp (S₀ : Subgroup ↥Y).subtype) from rfl,
      Subgroup.card_map_of_injective hf_inj,
      Subgroup.card_map_of_injective e.injective,
      show E₀T = E₀Y.subgroupOf T from rfl,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀T).toEquiv,
      show E₀Y = E₀.subgroupOf Y from rfl]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀Y).toEquiv).trans hE₀card


theorem exists_sylow_syl2Bar (D : Data G) (L : Subgroup G)
    (hL : CFSG.Open.IsSubnormal L D.M) :
    ∃ P : Sylow 2 (Bar2 L), (P : Subgroup (Bar2 L)) = Syl2Bar D L := by
  classical
  have hsub : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn D.sylowM hL.le
      hL.subgroupOf
  have hNTL : NTL17 D L ⊓ L = D.T ⊓ L := by
    ext x
    constructor
    · rintro ⟨⟨hxT, hxN⟩, hxL⟩
      exact ⟨hxT, hxL⟩
    · rintro ⟨hxT, hxL⟩
      exact ⟨⟨hxT, Subgroup.le_normalizer hxL⟩, hxL⟩
  obtain ⟨Q, hQ⟩ := hsub.exists_sylow_eq_subgroupOf
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Qbar : Sylow 2 (Bar2 L) := Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective _) Q
  refine ⟨Qbar, ?_⟩
  unfold Syl2Bar
  rw [Sylow.coe_mapSurjective, hQ, hNTL]

theorem mem_delta_third
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h1 : ¬ P17_12_1 r q L) (h2 : ¬ P17_12_2 q L)
    (X : Subgroup G) (hXL : X ≤ L) (hO2 : pCoreOf 2 L ≤ X)
    (hfun : (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∈
      FunSet (fundPred q) (Bar2 L) (Syl2Bar D L)) :
    D.T ⊔ X ∈ Delta17_12 D (fundPred q) r q L := by
  have hconj1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
      ext l
      simp [MulAut.conj_apply], Subgroup.map_id]
  have hfun' : ((X.subgroupOf (L.map (MulAut.conj (1 : G)).toMonoidHom)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(L.map (MulAut.conj (1 : G)).toMonoidHom)))) ∈
      FunSet (fundPred q) (Bar2 (L.map (MulAut.conj (1 : G)).toMonoidHom))
        (((NTL17 D L ⊓ L.map (MulAut.conj (1 : G)).toMonoidHom).subgroupOf
          (L.map (MulAut.conj (1 : G)).toMonoidHom)).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(L.map (MulAut.conj (1 : G)).toMonoidHom)))) := by
    exact hconj1.symm ▸ hfun
  rw [Delta17_12, dif_neg h1, dif_neg h2]
  have hpc : pCoreOf 2 (L.map (MulAut.conj (1 : G)).toMonoidHom) = pCoreOf 2 L := by
    rw [hconj1]
  refine ⟨1, D.M.one_mem, X, ?_, ?_, rfl, hfun'⟩
  · rw [hconj1]; exact hXL
  · intro x hx
    rw [hpc] at hx
    exact hO2 hx



theorem exists_lift_barPreimage (L : Subgroup G) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (K₁ K₂ : Subgroup (Bar2 L)) (E : Subgroup (Bar2 L))
    (hE : E ≤ K₁ ⊔ K₂) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    ∃ E' : Subgroup G, E' ≤ barPreimage L K₁ ⊔ barPreimage L K₂ ∧
      IsElemAbelian r E' ∧ Nat.card E' = r ^ 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [show π.ker = CFSG.pCore 2 ↥L by
      simp [π, QuotientGroup.ker_mk']]
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    UC6S846.exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hr hr2 E hEel.isPGroup
  have hsup : barPreimage L (K₁ ⊔ K₂) = barPreimage L K₁ ⊔ barPreimage L K₂ := by
    unfold barPreimage
    rw [← Subgroup.comap_sup_eq (f := π) K₁ K₂ (QuotientGroup.mk'_surjective _),
      Subgroup.map_sup]
  refine ⟨Q.map L.subtype, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    have hqK : π q ∈ K₁ ⊔ K₂ := hE (by rw [← hQmap]; exact ⟨q, hq, rfl⟩)
    have hqpre : q ∈ ((barPreimage L (K₁ ⊔ K₂)).subgroupOf L) := by
      rw [subgroupOf_barPreimage]
      exact hqK
    rw [hsup] at hqpre
    exact Subgroup.mem_subgroupOf.mp hqpre
  · exact (UC6S846.isElemAbelian_of_disjoint_ker π Q hQdisj
      (by rw [hQmap]; exact hEel)).map L.subtype
  · rw [Subgroup.card_map_of_injective L.subtype_injective,
      ← UC6S846.card_map_of_disjoint_ker π Q hQdisj, hQmap, hEcard]



theorem exceptional_rank_two_data
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h1 : ¬ P17_12_1 r q L) (h2 : ¬ P17_12_2 q L)
    (hLnorm : (L.subgroupOf D.M).Normal)
    (hqr : q = r)
    (hexc : LieModel (BarInf L) .G2 0 r 1 ∨ LieModel (BarInf L) .PSp 2 r 1)
    (hq3 : 3 < q)
    (hKO1b : K_FunRankTwo)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    (hp3 : 3 ≤ CFSG.Open.pRank p D.M) (hpdvd : ¬ p ∣ r ^ 2 - 1) :
    ∃ X₁ X₂ E : Subgroup G,
      X₁ ≤ L ∧ X₂ ≤ L ∧ pCoreOf 2 L ≤ X₁ ∧ pCoreOf 2 L ≤ X₂ ∧
      ((X₁.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∈
        FunSet (fundPred q) (Bar2 L) (Syl2Bar D L)) ∧
      ((X₂.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∈
        FunSet (fundPred q) (Bar2 L) (Syl2Bar D L)) ∧
      E ≤ X₁ ⊔ X₂ ∧
      CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
      0 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) ∧
      (∀ X₀ : Subgroup G, X₀ ≤ E → Nat.card X₀ = r →
        1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X₀ : Set G))) := by
  have hOutRank := k_ExceptionalAutPRank_holds
  classical
  obtain ⟨hr, hr2, t, n, f, hadm, hq_eq, hm⟩ := hC.lie
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hC.memL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨eBar⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hC.memL
  have hmq : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t n r f := hm.of_mulEquiv eBar
  have hL2 : ¬ IsL2Over17 (Bar2 L ⧸ Subgroup.center (Bar2 L)) q := by
    intro hbad
    exact h1 (Or.inl (isL2Over17_of_mulEquiv (q := q) eBar hbad))
  have hL3 : ¬ IsL3EpsOdd17 (Bar2 L ⧸ Subgroup.center (Bar2 L)) r := by
    intro hbad
    rw [IsL3EpsOdd17] at hbad
    exact h1 (Or.inr (by
      rcases hbad with hbad | hbad
      · exact Or.inl (LieModel.of_mulEquiv eBar.symm hbad)
      · exact Or.inr (LieModel.of_mulEquiv eBar.symm hbad)))
  have hRee : ¬ IsReeOver17 (Bar2 L) q := h2
  obtain ⟨P, hPcoe⟩ := exists_sylow_syl2Bar D L hC.memL.1
  obtain ⟨E₀, K₁, K₂, hK₁, hK₂, hE₀el, hE₀card, hE₀sup⟩ :=
    (hKO1b (Bar2 L) r q hr hr2 ⟨t, n, f, hadm, hq_eq, hmq⟩ hq hodd (Or.inl hq3)
      hL2 hL3 hRee P).1
  obtain ⟨E', hE'le, hE'el, hE'card⟩ :=
    exists_lift_barPreimage L hr hr2 K₁ K₂ E₀ hE₀sup hE₀el hE₀card
  let X₁ : Subgroup G := barPreimage L K₁
  let X₂ : Subgroup G := barPreimage L K₂
  have hX₁L : X₁ ≤ L := uc22p21c_barPreimage_le L K₁
  have hX₂L : X₂ ≤ L := uc22p21c_barPreimage_le L K₂
  have hO₂X₁ : pCoreOf 2 L ≤ X₁ := pCoreOf_le_barPreimage L K₁
  have hO₂X₂ : pCoreOf 2 L ≤ X₂ := pCoreOf_le_barPreimage L K₂
  have hK₁' : ((X₁.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∈
      FunSet (fundPred q) (Bar2 L) (Syl2Bar D L)) := by
    change barImage L (barPreimage L K₁) ∈ _
    rw [barImage_barPreimage]
    simpa [hPcoe] using hK₁
  have hK₂' : ((X₂.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∈
      FunSet (fundPred q) (Bar2 L) (Syl2Bar D L)) := by
    change barImage L (barPreimage L K₂) ∈ _
    rw [barImage_barPreimage]
    simpa [hPcoe] using hK₂
  by_cases hpr : p = r
  · subst p
    have hE₀_CE : E' ≤ D.M ⊓ Subgroup.centralizer (E' : Set G) := by
      intro x hx
      refine ⟨(hE'le.trans (sup_le hX₁L hX₂L)).trans hC.memL.1.le hx, ?_⟩
      change x ∈ Subgroup.centralizer (E' : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hcomm : ∀ a b : G, a ∈ E' → b ∈ E' → a * b = b * a := by
        intro a b ha hb
        have h := hE'el.1.is_comm.comm (⟨a, ha⟩ : ↥E') (⟨b, hb⟩ : ↥E')
        simpa using congrArg Subtype.val h
      exact hcomm y x hy hx
    have hE₀_N : ∀ X₀ : Subgroup G, X₀ ≤ E' → Nat.card X₀ = r →
        E' ≤ D.M ⊓ Subgroup.normalizer (X₀ : Set G) := by
      intro X₀ hX₀ hcard₀
      have hCX₀ : E' ≤ Subgroup.centralizer (X₀ : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hcomm : ∀ a b : G, a ∈ E' → b ∈ E' → a * b = b * a := by
          intro a b ha hb
          have h := hE'el.1.is_comm.comm (⟨a, ha⟩ : ↥E') (⟨b, hb⟩ : ↥E')
          simpa using congrArg Subtype.val h
        exact hcomm y x (hX₀ hy) hx
      intro x hx
      exact ⟨(hE'le.trans (sup_le hX₁L hX₂L)).trans hC.memL.1.le hx,
        hCX₀.trans (Subgroup.centralizer_le_normalizer (X₀ : Set G)) hx⟩
    refine ⟨X₁, X₂, E', hX₁L, hX₂L, hO₂X₁, hO₂X₂, hK₁', hK₂', hE'le,
      hE'el, hE'card, ?_, ?_⟩
    · have hle := CFSG.SectionRank.le_pRank hr.one_lt hE₀_CE hE'el
        (by simpa using hE'card)
      omega
    · intro X₀ hX₀ hcard₀
      have hle := CFSG.SectionRank.le_pRank hr.one_lt (hE₀_N X₀ hX₀ hcard₀) hE'el
        (by simpa using hE'card)
      omega
  · have hexcBar : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .G2 0 r 1 ∨
        LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSp 2 r 1 := by
      rcases hexc with hbad | hbad
      · exact Or.inl (LieModel.of_mulEquiv eBar hbad)
      · exact Or.inr (LieModel.of_mulEquiv eBar hbad)
    have hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1 :=
      hOutRank (Bar2 L) r p hr hr2 hp hp2 hpr hq hexcBar hpdvd
    obtain ⟨Psub, hPsubM, hPsubCent, hPsubEl, hPsubRank⟩ :=
      exists_elemAbelian_le_centOverO2 D L hC.memL.1.le hLnorm hp hp3 hAut
    obtain ⟨E, hEY, hEel, hEcard, hEcent⟩ :=
      exists_centralized_elemAbelian_le_sup D L hC.memL.1.le hLnorm K₁ K₂ E' hE'le
        hE'el hE'card Psub hPsubM hPsubCent hp hp2 hr hr2 hPsubEl.isPGroup
    have hPsub_CE : Psub ≤ D.M ⊓ Subgroup.centralizer (E : Set G) := by
      intro x hx
      refine ⟨hPsubM hx, ?_⟩
      change x ∈ Subgroup.centralizer (E : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxy : x * y = y * x := by
        have := (Subgroup.mem_centralizer_iff.mp (hEcent hy)) x hx
        exact this
      exact hxy.symm
    have hPsub_N : ∀ X₀ : Subgroup G, X₀ ≤ E → Nat.card X₀ = r →
        Psub ≤ D.M ⊓ Subgroup.normalizer (X₀ : Set G) := by
      intro X₀ hX₀ hcard₀
      have hCX₀ : Psub ≤ Subgroup.centralizer (X₀ : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp (hEcent (hX₀ hy)) x hx).symm
      intro x hx
      exact ⟨hPsubM hx,
        hCX₀.trans (Subgroup.centralizer_le_normalizer (X₀ : Set G)) hx⟩
    refine ⟨X₁, X₂, E, hX₁L, hX₂L, hO₂X₁, hO₂X₂, hK₁', hK₂', hEY,
      hEel, hEcard, ?_, ?_⟩
    · have hle := CFSG.SectionRank.pRank_mono hp.one_lt hPsub_CE
      have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) :=
        hPsubRank.trans hle
      omega
    · intro X₀ hX₀ hcard₀
      have hle := CFSG.SectionRank.pRank_mono hp.one_lt (hPsub_N X₀ hX₀ hcard₀)
      omega

theorem seventeen_sixteen_case_three
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h17_7 : R17_7At D V₀ V L r q hC)
    (h17_9 : R17_9At D V₀ V L r q hC)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h76 : F07.R76 D)
    (hSg : SigmaStd D)
    (hKO1b : K_FunRankTwo) (hKO2 : K_LieOddRankFour)
    (h1 : ¬ P17_12_1 r q L) (h2 : ¬ P17_12_2 q L) :
    R17_16At D (fundPred q) V₀ V L r q hC := by
  classical
  have hq3 : 3 < q := h17_9
  obtain ⟨hr, hr2, t, n, f, hadm, hq_eq, hm⟩ := hC.lie
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hC.memL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨eBar⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hC.memL
  have hmq : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t n r f := hm.of_mulEquiv eBar
  have hL2 : ¬ IsL2Over17 (Bar2 L ⧸ Subgroup.center (Bar2 L)) q := by
    intro hbad
    exact h1 (Or.inl (isL2Over17_of_mulEquiv (q := q) eBar hbad))
  have hL3 : ¬ IsL3EpsOdd17 (Bar2 L ⧸ Subgroup.center (Bar2 L)) r := by
    intro hbad
    rw [IsL3EpsOdd17] at hbad
    exact h1 (Or.inr (by
      rcases hbad with hbad | hbad
      · exact Or.inl (LieModel.of_mulEquiv eBar.symm hbad)
      · exact Or.inr (LieModel.of_mulEquiv eBar.symm hbad)))
  have hRee : ¬ IsReeOver17 (Bar2 L) q := h2
  obtain ⟨P, hPcoe⟩ := exists_sylow_syl2Bar D L hC.memL.1
  have hsupM : (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) ≤ D.M :=
    SeventeenSixteen.delta_le_M D (fundPred q) V₀ V L r q hC
  have finish : ∀ E : Subgroup G, E ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) →
      UniqueMax D.M E → R17_16At D (fundPred q) V₀ V L r q hC := by
    intro E hE hU
    exact uc22p22u_uniqueMax_mono D hE hsupM hU
  obtain ⟨E, K₁, K₂, hK₁, hK₂, hEel, hEcard, hEsup⟩ :=
    (hKO1b (Bar2 L) r q hr hr2 ⟨t, n, f, hadm, hq_eq, hmq⟩ hq hodd (Or.inl hq3)
      hL2 hL3 hRee P).1
  obtain ⟨E', hE'le, hE'el, hE'card⟩ :=
    exists_lift_barPreimage L hr hr2 K₁ K₂ E hEsup hEel hEcard
  have hX₁L : barPreimage L K₁ ≤ L := uc22p21c_barPreimage_le L K₁
  have hX₂L : barPreimage L K₂ ≤ L := uc22p21c_barPreimage_le L K₂
  have hX₁delta : D.T ⊔ barPreimage L K₁ ∈ Delta17_12 D (fundPred q) r q L :=
    mem_delta_third D V₀ V L r q hC h1 h2 (barPreimage L K₁) hX₁L
      (pCoreOf_le_barPreimage L K₁) (by
        change barImage L (barPreimage L K₁) ∈ _
        rw [barImage_barPreimage]
        simpa [hPcoe] using hK₁)
  have hX₂delta : D.T ⊔ barPreimage L K₂ ∈ Delta17_12 D (fundPred q) r q L :=
    mem_delta_third D V₀ V L r q hC h1 h2 (barPreimage L K₂) hX₂L
      (pCoreOf_le_barPreimage L K₂) (by
        change barImage L (barPreimage L K₂) ∈ _
        rw [barImage_barPreimage]
        simpa [hPcoe] using hK₂)
  have hX₁S : barPreimage L K₁ ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
    (le_sup_right : barPreimage L K₁ ≤ D.T ⊔ barPreimage L K₁).trans
      (le_iSup₂_of_le (D.T ⊔ barPreimage L K₁) hX₁delta le_rfl)
  have hX₂S : barPreimage L K₂ ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
    (le_sup_right : barPreimage L K₂ ≤ D.T ⊔ barPreimage L K₂).trans
      (le_iSup₂_of_le (D.T ⊔ barPreimage L K₂) hX₂delta le_rfl)
  have hE'delta : E' ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
    hE'le.trans (sup_le hX₁S hX₂S)
  have hE'L : E' ≤ L := hE'le.trans (sup_le hX₁L hX₂L)
  have hE'nc : ¬ IsCyclic ↥E' := by
    intro hcyc
    have hlow : CFSG.Open.pRank r E' ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    have hhigh : 2 ≤ CFSG.Open.pRank r E' :=
      UC6S846.le_pRank' hr (le_refl E') hE'el hE'card
    omega
  by_cases h4 : 4 ≤ CFSG.Open.pRank r D.M
  · have hrsig : r ∈ D.sig := hSg.four_mem r hr hr2 h4
    have hE'M : E' ≤ D.M := hE'delta.trans hsupM
    exact finish E' hE'delta (h61 r hrsig E' hE'M hE'el.isPGroup hE'nc)
  · push Not at h4
    have hrank := hKO2 (Bar2 L) r q hr hr2 ⟨t, n, f, hadm, hq_eq, hmq⟩ hq hodd hL2 hL3 hRee
    rcases hrank with h4' | ⟨hqr, hexcBar, hZbar⟩
    · have hEq : CFSG.Open.pRank r (⊤ : Subgroup (Bar2 L)) = CFSG.Open.pRank r L :=
        UC22.pRank_bar2_eq_of_odd hr hr2
      have h4L : 4 ≤ CFSG.Open.pRank r D.M := by
        rw [hEq] at h4'
        exact h4'.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hC.memL.1.le)
      omega
    · have hexc : LieModel (BarInf L) .G2 0 r 1 ∨ LieModel (BarInf L) .PSp 2 r 1 := by
        rcases hexcBar with hbad | hbad
        · exact Or.inl (LieModel.of_mulEquiv eBar.symm hbad)
        · exact Or.inr (LieModel.of_mulEquiv eBar.symm hbad)
      have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hC.memL
      have hLnorm : (L.subgroupOf D.M).Normal := by
        by_contra hnN
        have hnN' : ¬ D.M ≤ Subgroup.normalizer (L : Set G) := by
          intro hle
          exact hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hC.memL.1.le).2 hle)
        have h4bad := UC6S846.calCRankTwice D.M L hC.memL hnN' r hr hr2 hZbar E'
          hE'L hE'el 2 hE'card
        omega
      by_cases hall : ∀ p ∈ D.sig, p ∣ r ^ 2 - 1
      · obtain ⟨p, hpσ⟩ := hSg.nonempty
        have hp : p.Prime := (D.sig_prime p hpσ).1
        have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
        have hdvd : p ∣ r ^ 2 - 1 := hall p hpσ
        obtain ⟨K₁', K₂', hK₁', hK₂', E'', hE''el, hE''card, hE''sup⟩ :=
          (hKO1b (Bar2 L) r q hr hr2 ⟨t, n, f, hadm, hq_eq, hmq⟩ hq hodd (Or.inl hq3)
            hL2 hL3 hRee P).2
            hqr hexcBar p hp hp2 hdvd
        obtain ⟨E''', hE'''le, hE'''el, hE'''card⟩ :=
          exists_lift_barPreimage L hp hp2 K₁' K₂' E'' hE''sup hE''el hE''card
        have hX₁'L : barPreimage L K₁' ≤ L := uc22p21c_barPreimage_le L K₁'
        have hX₂'L : barPreimage L K₂' ≤ L := uc22p21c_barPreimage_le L K₂'
        have hX₁'delta : D.T ⊔ barPreimage L K₁' ∈ Delta17_12 D (fundPred q) r q L :=
          mem_delta_third D V₀ V L r q hC h1 h2 (barPreimage L K₁') hX₁'L
            (pCoreOf_le_barPreimage L K₁') (by
              change barImage L (barPreimage L K₁') ∈ _
              rw [barImage_barPreimage]
              simpa [hPcoe] using hK₁')
        have hX₂'delta : D.T ⊔ barPreimage L K₂' ∈ Delta17_12 D (fundPred q) r q L :=
          mem_delta_third D V₀ V L r q hC h1 h2 (barPreimage L K₂') hX₂'L
            (pCoreOf_le_barPreimage L K₂') (by
              change barImage L (barPreimage L K₂') ∈ _
              rw [barImage_barPreimage]
              simpa [hPcoe] using hK₂')
        have hX₁'S : barPreimage L K₁' ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
          (le_sup_right : barPreimage L K₁' ≤ D.T ⊔ barPreimage L K₁').trans
            (le_iSup₂_of_le (D.T ⊔ barPreimage L K₁') hX₁'delta le_rfl)
        have hX₂'S : barPreimage L K₂' ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
          (le_sup_right : barPreimage L K₂' ≤ D.T ⊔ barPreimage L K₂').trans
            (le_iSup₂_of_le (D.T ⊔ barPreimage L K₂') hX₂'delta le_rfl)
        have hE'''delta : E''' ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
          hE'''le.trans (sup_le hX₁'S hX₂'S)
        have hE'''M : E''' ≤ D.M := hE'''delta.trans hsupM
        have hE'''nc : ¬ IsCyclic ↥E''' := by
          intro hcyc
          have hlow : CFSG.Open.pRank p E''' ≤ 1 :=
            CFSG.SectionRank.pRank_le_one_of_isCyclic hp hcyc
          have hhigh : 2 ≤ CFSG.Open.pRank p E''' :=
            UC6S846.le_pRank' hp (le_refl E''') hE'''el hE'''card
          omega
        exact finish E''' hE'''delta (h61 p hpσ E''' hE'''M hE'''el.isPGroup hE'''nc)
      · push Not at hall
        obtain ⟨p, hpσ, hpdvd⟩ := hall
        have hp : p.Prime := (D.sig_prime p hpσ).1
        have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
        obtain ⟨X₁, X₂, E, hX₁L, hX₂L, hO₂X₁, hO₂X₂, hK₁, hK₂, hEsup, hEel'', hEcard'',
          hcen, hNor⟩ :=
          exceptional_rank_two_data D V₀ V L r q hC h1 h2 hLnorm hqr hexc hq3 hKO1b
            p hp hp2 hpσ (hSg.three_le p hpσ) hpdvd
        have hX₁delta : D.T ⊔ X₁ ∈ Delta17_12 D (fundPred q) r q L :=
          mem_delta_third D V₀ V L r q hC h1 h2 X₁ hX₁L hO₂X₁ hK₁
        have hX₂delta : D.T ⊔ X₂ ∈ Delta17_12 D (fundPred q) r q L :=
          mem_delta_third D V₀ V L r q hC h1 h2 X₂ hX₂L hO₂X₂ hK₂
        have hX₁S : X₁ ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
          (le_sup_right : X₁ ≤ D.T ⊔ X₁).trans
            (le_iSup₂_of_le (D.T ⊔ X₁) hX₁delta le_rfl)
        have hX₂S : X₂ ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
          (le_sup_right : X₂ ≤ D.T ⊔ X₂).trans
            (le_iSup₂_of_le (D.T ⊔ X₂) hX₂delta le_rfl)
        have hEdelta : E ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
          hEsup.trans (sup_le hX₁S hX₂S)
        have hEM : E ≤ D.M := hEdelta.trans hsupM
        have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
          UC6S846.sp_of_mem_sig hSg hns hpσ
        have hgamma : rankThreeGamma 1 r E ≤ D.M :=
          h76 p hp hp2 hsp r hr E hEM hEel'' hEcard'' hcen hNor
        exact finish E hEdelta (h63 r hr hr2 E hEM hEel'' hEcard'' hgamma)


theorem bar2_barPreimage_mulEquiv (L : Subgroup G) (K : Subgroup (Bar2 L))
    (hK : CFSG.pCore 2 K = ⊥) : Nonempty (Bar2 (barPreimage L K) ≃* K) := by
  classical
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Y : Subgroup ↥L := K.comap π
  have hYmap : Y.map π = K := by
    rw [show Y = K.comap π from rfl, Subgroup.map_comap_eq_self]
    rw [show π.range = ⊤ from
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_top
  let πY : ↥Y →* K := (π.comp Y.subtype).codRestrict K (fun y => by
    rw [← hYmap]
    exact ⟨y, y.2, rfl⟩)
  have hπYsurj : Function.Surjective πY := by
    intro k
    have hk : (k : Bar2 L) ∈ Y.map π := by
      rw [hYmap]
      exact k.2
    obtain ⟨y, hy, hyk⟩ := hk
    exact ⟨⟨y, hy⟩, Subtype.ext hyk⟩
  have hker : πY.ker = (CFSG.pCore 2 ↥L).subgroupOf Y := by
    rw [MonoidHom.ker_codRestrict]
    rw [show (π.comp Y.subtype).ker = (π.ker).comap Y.subtype from rfl,
      QuotientGroup.ker_mk', Subgroup.comap_subtype]
  have hEq : CFSG.pCore 2 ↥Y = πY.ker := by
    apply le_antisymm
    · intro x hx
      have hle : (CFSG.pCore 2 ↥Y).map πY ≤ CFSG.pCore 2 K := by
        change _ ≤ sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup 2 N}
        exact le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥Y)).map πY hπYsurj,
          (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map πY⟩
      have hx' : πY x ∈ (CFSG.pCore 2 ↥Y).map πY := ⟨x, hx, rfl⟩
      have hmem : πY x ∈ CFSG.pCore 2 K := hle hx'
      rw [hK, Subgroup.mem_bot] at hmem
      simpa [MonoidHom.mem_ker] using hmem
    · rw [hker]
      intro x hx
      have hpcle : (CFSG.pCore 2 ↥L).subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
        change _ ≤ sSup {N : Subgroup ↥Y | N.Normal ∧ IsPGroup 2 N}
        exact le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥L)).comap Y.subtype,
          (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective Y.subtype
            Y.subtype_injective⟩
      exact hpcle hx
  have hYiso : Nonempty (Bar2 Y ≃* K) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hEq).trans
      ((QuotientGroup.quotientKerEquivRange πY).trans
        ((MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hπYsurj)).trans
          Subgroup.topEquiv))⟩
  obtain ⟨eY⟩ := hYiso
  let eX : ↥(barPreimage L K) ≃* ↥Y :=
    (Subgroup.subgroupOfEquivOfLe (uc22p21c_barPreimage_le L K)).symm.trans
      (MulEquiv.subgroupCongr (subgroupOf_barPreimage L K))
  exact ⟨(UC6S846.bar2Equiv eX).trans eY⟩

theorem seventeen_sixteen_case_two
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h17_7 : R17_7At D V₀ V L r q hC)
    (h17_9 : R17_9At D V₀ V L r q hC)
    (hRee : K_ReeSylowGeneration)
    (h1 : ¬ P17_12_1 r q L) (h2 : P17_12_2 q L) :
    R17_16At D (fundPred q) V₀ V L r q hC := by
  classical
  obtain ⟨n, hq_eq, hLie⟩ := h2
  have hq3 : 3 < q := h17_9
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hq_eq
    norm_num at hq_eq
    omega
  let S : Subgroup G := NTL17 D L
  have hS_le_N : S ≤ Subgroup.normalizer (L : Set G) := by
    intro s hs
    exact (Subgroup.mem_inf.mp hs).2
  have hS_le_T : S ≤ D.T := fun s hs => (Subgroup.mem_inf.mp hs).1
  have hS2 : IsPGroup 2 S := D.sylowM.isPGroup.to_le hS_le_T
  obtain ⟨P, hPcoe⟩ := exists_sylow_syl2Bar D L hC.memL.1
  obtain ⟨hZX, hOutOdd, hReePart⟩ := hRee (Bar2 L) q n ⟨n, hq_eq, hLie⟩ hq_eq hn1
  obtain ⟨hEel, hEcard8, x, y, hxP, hyP, hxy, hx2, hy2,
    hKxL2, hKyL2, hKxO2, hKyO2, hKyZ, hCxdec, hCydec, hCxcoat, hCycoat, hxKy⟩ :=
    hReePart P
  let Kx : Subgroup (Bar2 L) :=
    ⁅Subgroup.centralizer ({x} : Set (Bar2 L)), Subgroup.centralizer ({x} : Set (Bar2 L))⁆
  let Ky : Subgroup (Bar2 L) :=
    ⁅Subgroup.centralizer ({y} : Set (Bar2 L)), Subgroup.centralizer ({y} : Set (Bar2 L))⁆
  let ρ : S →* MulAut (Bar2 L) :=
    (UC6S846.rhoL L).comp (Subgroup.inclusion hS_le_N)
  let κ : S →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp ρ
  have hκbot : κ.range = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    refine MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ext fun s => ?_)
    exact CFSG.Semidihedral.KleinFourOddKernel.hom_eq_one_of_coprime_card κ
      (by rw [hk]; exact (Nat.coprime_two_left.mpr hOutOdd).pow_left k) s
  have hinner : ∀ s : S, ρ s ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
    intro s
    have hκs : κ s = 1 := by
      have : κ s ∈ κ.range := ⟨s, rfl⟩
      rw [hκbot] at this
      simpa using this
    exact (QuotientGroup.eq_one_iff (ρ s)).mp hκs
  choose b hb using hinner
  have hconj_inj : Function.Injective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.conj_injective_of_center_eq_bot hZX
  have hb_mul : ∀ s t : S, b (s * t) = b s * b t := by
    intro s t
    apply hconj_inj
    rw [hb (s * t), map_mul, map_mul, hb s, hb t]
  let B : S →* Bar2 L := MonoidHom.mk' b hb_mul
  have hB2 : IsPGroup 2 B.range := by
    have hS2' : IsPGroup 2 (⊤ : Subgroup S) := hS2.of_equiv Subgroup.topEquiv.symm
    rw [MonoidHom.range_eq_map]
    exact hS2'.map B
  have hE_le_B : Syl2Bar D L ≤ B.range := by
    rw [Syl2Bar]
    rintro z ⟨l, hl, rfl⟩
    have hlS : (l : G) ∈ S := (Subgroup.mem_subgroupOf.mp hl).1
    have hlL : (l : G) ∈ L := (Subgroup.mem_subgroupOf.mp hl).2
    refine ⟨⟨l, hlS⟩, ?_⟩
    apply hconj_inj
    change MulAut.conj (b ⟨l, hlS⟩) = MulAut.conj ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l)
    rw [hb]
    simpa [ρ, Subgroup.inclusion] using (UC6S846.rhoL_inner L (l : G) hlL)
  have hB_range : B.range = Syl2Bar D L := by
    have heq : B.range = (P : Subgroup (Bar2 L)) := P.3 hB2 (by rw [hPcoe]; exact hE_le_B)
    rwa [hPcoe] at heq
  have hfixx : ∀ s : S, ρ s x = x := by
    intro s
    have hBs : b s ∈ Syl2Bar D L := by rw [← hB_range]; exact ⟨s, rfl⟩
    have hxE : x ∈ Syl2Bar D L := by rw [← hPcoe]; exact hxP
    have hEelE : IsMulCommutative ↥(Syl2Bar D L) := hPcoe ▸ hEel.1
    have hcomm : (b s : Bar2 L) * x = x * b s := by
      have h := hEelE.is_comm.comm (⟨b s, hBs⟩ : ↥(Syl2Bar D L))
        (⟨x, hxE⟩ : ↥(Syl2Bar D L))
      exact congrArg Subtype.val h
    rw [← hb s, MulAut.conj_apply, hcomm]
    group
  have hfixy : ∀ s : S, ρ s y = y := by
    intro s
    have hBs : b s ∈ Syl2Bar D L := by rw [← hB_range]; exact ⟨s, rfl⟩
    have hyE : y ∈ Syl2Bar D L := by rw [← hPcoe]; exact hyP
    have hEelE : IsMulCommutative ↥(Syl2Bar D L) := hPcoe ▸ hEel.1
    have hcomm : (b s : Bar2 L) * y = y * b s := by
      have h := hEelE.is_comm.comm (⟨b s, hBs⟩ : ↥(Syl2Bar D L))
        (⟨y, hyE⟩ : ↥(Syl2Bar D L))
      exact congrArg Subtype.val h
    rw [← hb s, MulAut.conj_apply, hcomm]
    group
  have hKx_inv : ∀ s : S, Kx.map (ρ s).toMonoidHom = Kx := by
    intro s
    have hC : (Subgroup.centralizer ({x} : Set (Bar2 L))).map (ρ s).toMonoidHom =
        Subgroup.centralizer ({x} : Set (Bar2 L)) := by
      rw [CFSG.Walter.map_centralizer_singleton_mulEquiv, hfixx s]
    dsimp only [Kx]
    rw [Subgroup.map_commutator, hC]
  have hKy_inv : ∀ s : S, Ky.map (ρ s).toMonoidHom = Ky := by
    intro s
    have hC : (Subgroup.centralizer ({y} : Set (Bar2 L))).map (ρ s).toMonoidHom =
        Subgroup.centralizer ({y} : Set (Bar2 L)) := by
      rw [CFSG.Walter.map_centralizer_singleton_mulEquiv, hfixy s]
    dsimp only [Ky]
    rw [Subgroup.map_commutator, hC]
  have hgen : Kx ⊔ Ky = ⊤ :=
    CFSG.GroupTheory.sup_eq_top_of_isCoatom_centralizer hx2 hCxdec hCxcoat hxKy hKyZ
  let Xx : Subgroup G := barPreimage L Kx
  let Xy : Subgroup G := barPreimage L Ky
  have hXxL : Xx ≤ L := uc22p21c_barPreimage_le L Kx
  have hXyL : Xy ≤ L := uc22p21c_barPreimage_le L Ky
  have hXx_norm : S ≤ Subgroup.normalizer (Xx : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      dsimp only [Xx, Xy] at hz
      unfold barPreimage at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨l, hlK, rfl⟩ := hz
      refine Subgroup.mem_map.mpr ⟨Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hmem : (UC6S846.rhoL L ⟨s, hS_le_N hs⟩) (QuotientGroup.mk l) ∈ Kx :=
          hKx_inv ⟨s, hs⟩ ▸ (Subgroup.mem_map.mpr ⟨QuotientGroup.mk l, hlK, rfl⟩)
        have h1 : (UC6S846.rhoL L ⟨s, hS_le_N hs⟩) (QuotientGroup.mk l) =
            QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l) := rfl
        rwa [h1] at hmem
      · change ((Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l : ↥L) : G) =
            s * (l : G) * s⁻¹
        exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hS_le_N hs⟩ l
    · intro hz
      dsimp only [Xx, Xy] at hz
      unfold barPreimage at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨l, hlK, hzl⟩ := hz
      refine Subgroup.mem_map.mpr
        ⟨Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hmem : (UC6S846.rhoL L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩)
            (QuotientGroup.mk l) ∈ Kx :=
          hKx_inv ⟨s⁻¹, S.inv_mem hs⟩ ▸ (Subgroup.mem_map.mpr ⟨QuotientGroup.mk l, hlK, rfl⟩)
        have h1 : (UC6S846.rhoL L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩) (QuotientGroup.mk l) =
            QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l) := rfl
        rwa [h1] at hmem
      · change ((Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l : ↥L) : G) = z
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simp only [Subgroup.coe_inv, Subgroup.coe_mk, Subgroup.coe_subtype]
        have hzl' : (l : G) = s * z * s⁻¹ := hzl
        rw [hzl']
        group
  have hXy_norm : S ≤ Subgroup.normalizer (Xy : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      dsimp only [Xx, Xy] at hz
      unfold barPreimage at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨l, hlK, rfl⟩ := hz
      refine Subgroup.mem_map.mpr ⟨Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hmem : (UC6S846.rhoL L ⟨s, hS_le_N hs⟩) (QuotientGroup.mk l) ∈ Ky :=
          hKy_inv ⟨s, hs⟩ ▸ (Subgroup.mem_map.mpr ⟨QuotientGroup.mk l, hlK, rfl⟩)
        have h1 : (UC6S846.rhoL L ⟨s, hS_le_N hs⟩) (QuotientGroup.mk l) =
            QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l) := rfl
        rwa [h1] at hmem
      · change ((Subgroup.normalizerMonoidHom L ⟨s, hS_le_N hs⟩ l : ↥L) : G) =
            s * (l : G) * s⁻¹
        exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hS_le_N hs⟩ l
    · intro hz
      dsimp only [Xx, Xy] at hz
      unfold barPreimage at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨l, hlK, hzl⟩ := hz
      refine Subgroup.mem_map.mpr
        ⟨Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hmem : (UC6S846.rhoL L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩)
            (QuotientGroup.mk l) ∈ Ky :=
          hKy_inv ⟨s⁻¹, S.inv_mem hs⟩ ▸ (Subgroup.mem_map.mpr ⟨QuotientGroup.mk l, hlK, rfl⟩)
        have h1 : (UC6S846.rhoL L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩) (QuotientGroup.mk l) =
            QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l) := rfl
        rwa [h1] at hmem
      · change ((Subgroup.normalizerMonoidHom L ⟨s⁻¹, hS_le_N (S.inv_mem hs)⟩ l : ↥L) : G) = z
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simp only [Subgroup.coe_inv, Subgroup.coe_mk, Subgroup.coe_subtype]
        have hzl' : (l : G) = s * z * s⁻¹ := hzl
        rw [hzl']
        group
  have hXx_perm : Permutes Xx S :=
    (Subgroup.set_mul_normalizer_comm (S : Set G) Xx fun _ hx => hXx_norm hx).symm
  have hXy_perm : Permutes Xy S :=
    (Subgroup.set_mul_normalizer_comm (S : Set G) Xy fun _ hx => hXy_norm hx).symm
  have hXx_L2 : IsL2Over17 (Bar2 Xx) q := by
    obtain ⟨e⟩ := bar2_barPreimage_mulEquiv L Kx hKxO2
    exact isL2Over17_of_mulEquiv (q := q) e hKxL2
  have hXy_L2 : IsL2Over17 (Bar2 Xy) q := by
    obtain ⟨e⟩ := bar2_barPreimage_mulEquiv L Ky hKyO2
    exact isL2Over17_of_mulEquiv (q := q) e hKyL2
  have hXx_delta : D.T ⊔ Xx ∈ Delta17_12 D (fundPred q) r q L := by
    rw [Delta17_12, dif_neg h1, dif_pos (show P17_12_2 q L from ⟨n, hq_eq, hLie⟩)]
    exact ⟨Xx, hXxL, hXx_perm, hXx_L2, rfl⟩
  have hXy_delta : D.T ⊔ Xy ∈ Delta17_12 D (fundPred q) r q L := by
    rw [Delta17_12, dif_neg h1, dif_pos (show P17_12_2 q L from ⟨n, hq_eq, hLie⟩)]
    exact ⟨Xy, hXyL, hXy_perm, hXy_L2, rfl⟩
  have hXxS : Xx ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
    (le_sup_right : Xx ≤ D.T ⊔ Xx).trans (le_iSup₂_of_le (D.T ⊔ Xx) hXx_delta le_rfl)
  have hXyS : Xy ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
    (le_sup_right : Xy ≤ D.T ⊔ Xy).trans (le_iSup₂_of_le (D.T ⊔ Xy) hXy_delta le_rfl)
  have hpre_sup : barPreimage L (Kx ⊔ Ky) = Xx ⊔ Xy := by
    unfold Xx Xy barPreimage
    rw [← Subgroup.comap_sup_eq (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L)) Kx Ky
      (QuotientGroup.mk'_surjective _), Subgroup.map_sup]
  have hL_le : L ≤ Xx ⊔ Xy := by
    intro l hl
    have hl' : l ∈ barPreimage L (Kx ⊔ Ky) := by
      unfold barPreimage
      rw [Subgroup.mem_map]
      refine ⟨⟨l, hl⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, hgen]
      exact Subgroup.mem_top _
    rwa [hpre_sup] at hl'
  have hL_delta : L ≤ (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) :=
    hL_le.trans (sup_le hXxS hXyS)
  have hsupM : (⨆ H ∈ Delta17_12 D (fundPred q) r q L, H) ≤ D.M :=
    SeventeenSixteen.delta_le_M D (fundPred q) V₀ V L r q hC
  exact uc22p22u_uniqueMax_mono D hL_delta hsupM h17_7.1

theorem seventeen_sixteen
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h17_7 : R17_7At D V₀ V L r q hC)
    (h17_9 : R17_9At D V₀ V L r q hC)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h76 : F07.R76 D)
    (hSg : SigmaStd D) :
    R17_16At D (fundPred q) V₀ V L r q hC := by
  by_cases h1 : P17_12_1 r q L
  · exact seventeen_sixteen_case_one D (fundPred q) V₀ V L r q hC h1 h17_7
  · by_cases h2 : P17_12_2 q L
    · exact seventeen_sixteen_case_two D V₀ V L r q hC h17_7 h17_9
        k_ReeSylowGeneration_holds h1 h2
    · exact seventeen_sixteen_case_three D V₀ V L r q hC h17_7 h17_9 h61 h63 h76 hSg
        k_FunRankTwo_holds k_LieOddRankFour_holds h1 h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
