module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBNatOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeOm4Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.GroupTheory.ProductAutFactors
public import CFSG.GH74.GLS.Stage1.Main.P49HMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCLay
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCUp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaFstar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_om4_card_aut_five :
    Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

private theorem s168e3_om4_card_mulAut_square_dvd :
    Nat.card (MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) ∣
      2 * 120 ^ 2 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have h := CFSG.GroupTheory.card_mulAut_square_dvd (A := alternatingGroup (Fin 5))
    (fun N hN => by
      haveI := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N)
    (fun a ha => by
      have hc : a ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro c
        exact (ha c).symm
      rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
      exact hc)
    (exists_ne 1)
  rwa [s168e3_om4_card_aut_five] at h

theorem s168e3_om4_card_dvd [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsOmegaPlus ↥L 4 2)
    (hnat : NatOmegaPlus L (⊤ : Subgroup W) ⊥ 4 2) :
    Nat.card ↥A ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 := by
  have hnorm : A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLn g hg)
  let κ : ↥A →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hnorm)
  have hκ_apply : ∀ (t : ↥A) (x : ↥L),
      ((κ t) x : MulAut W) = (t : MulAut W) * (x : MulAut W) * (t : MulAut W)⁻¹ := by
    intro t x
    simpa only [κ, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
      Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hnorm t) x
  let ι : ↥κ.ker →* ↥(Subgroup.centralizer (L : Set (MulAut W))) :=
    MonoidHom.codRestrict (A.subtype.comp κ.ker.subtype) _ fun a => by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 : ((κ (a : ↥A)) ⟨x, hx⟩ : ↥L) = ⟨x, hx⟩ := by
        rw [MonoidHom.mem_ker.mp a.2]
        rfl
      have h3 := congrArg (fun y : ↥L => (y : MulAut W)) h2
      have h1 : ((A.subtype.comp κ.ker.subtype) a) * x *
          ((A.subtype.comp κ.ker.subtype) a)⁻¹ = x := by
        change ((a : ↥A) : MulAut W) * x * (((a : ↥A) : MulAut W))⁻¹ = x
        simpa only [hκ_apply, Subtype.coe_mk] using h3
      have h2' : ((A.subtype.comp κ.ker.subtype) a) * x =
          x * ((A.subtype.comp κ.ker.subtype) a) := by
        calc ((A.subtype.comp κ.ker.subtype) a) * x
            = (((A.subtype.comp κ.ker.subtype) a) * x *
                ((A.subtype.comp κ.ker.subtype) a)⁻¹) *
                ((A.subtype.comp κ.ker.subtype) a) := by group
          _ = x * ((A.subtype.comp κ.ker.subtype) a) := by rw [h1]
      exact h2'.symm
  have hι : Function.Injective ι := fun a b hab => by
    have h2 := congrArg
      (fun y : ↥(Subgroup.centralizer (L : Set (MulAut W))) => (y : MulAut W)) hab
    have h1 : κ.ker.subtype a = κ.ker.subtype b :=
      Subgroup.subtype_injective A
        (by simpa only [ι, MonoidHom.codRestrict_apply, MonoidHom.comp_apply] using h2)
    exact Subtype.ext h1
  have hker_dvd : Nat.card κ.ker ∣ 3 := by
    classical
    obtain ⟨K, hKf, hKfin, hK4, f, hf⟩ := s16e_omc_centralizer_embeds_units hnat
    letI := hKf
    haveI := Fintype.ofFinite K
    have hunits : Nat.card Kˣ = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK4]
    rw [← hunits]
    exact Subgroup.card_dvd_of_injective (f.comp ι) (hf.comp hι)
  have hrange_dvd : Nat.card κ.range ∣ 2 * 120 ^ 2 := by
    have h1 : Nat.card κ.range ∣ Nat.card (MulAut ↥L) := Subgroup.card_subgroup_dvd_card κ.range
    obtain ⟨e⟩ := s16e_omc_equiv_alt_five_of_isOmegaPlus hL
    have h2 : Nat.card (MulAut ↥L) =
        Nat.card (MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    rw [h2] at h1
    exact h1.trans s168e3_om4_card_mulAut_square_dvd
  have hcard := Subgroup.card_ker_mul_card_range κ
  rw [← hcard]
  exact (mul_dvd_mul hker_dvd hrange_dvd).trans
    (by norm_num : 3 * (2 * 120 ^ 2) ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2)

end Generic

theorem s168e3_om4_card_mbar_dvd {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) :
    Nat.card ↥(Mbar D.M V₀ V hV) ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 := by
  have hwT := s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne h.2.2
  have hnat : NatOmegaPlus (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 4 2 := by
    rw [← hwT]
    exact h.2.1
  have hsq : ∀ v : vStar D.M V₀ V hV L, v ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
  have hLΩ : IsOmegaPlus ↥(lStar D.M V₀ V hV L) 4 2 := by
    obtain ⟨he, K, hKf, hKfin, hKa, ⟨e1⟩⟩ := h.1
    obtain ⟨e⟩ := s16e_two_lStar_equiv D c.std.h1217 c.setting.hyp151 hV
    exact ⟨he, K, hKf, hKfin, hKa, ⟨e.trans e1⟩⟩
  have hleS : lStar D.M V₀ V hV L ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    barSub_mono _ V hV c.setting.hyp151.le
  haveI hNnorm : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (barSub_mono V₀ V hV c.setting.hyp151.le)).2
        (fun _ hg => Subgroup.mem_normalizer_iff_map_conj_eq.2
          (lBar_conj_eq_of_s15_eq_one h.2.2 hg))
  obtain ⟨ρ, -, hρL⟩ := s16e_star_equiv D c.std.h1217 c.setting.hyp151 hV
  haveI hSstar_normal : ((lStar D.M V₀ V hV L).subgroupOf
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)).Normal := by
    have hmap := hNnorm.map ρ.toMonoidHom ρ.surjective
    rwa [hρL] at hmap
  have hLn : ∀ g ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV,
      (lStar D.M V₀ V hV L).map (MulAut.conj g).toMonoidHom = lStar D.M V₀ V hV L := by
    intro g hg
    have hmem : g ∈ Subgroup.normalizer ((lStar D.M V₀ V hV L) :
        Set (MulAut (vStar D.M V₀ V hV L))) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hleS).1 hSstar_normal hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
  have hdvd := s168e3_om4_card_dvd (W := vStar D.M V₀ V hV L) hsq hleS hLn hLΩ hnat
  rwa [c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV] at hdvd

private theorem s168e3_om4_prime_dvd_201600 {q : ℕ} (hq : q.Prime)
    (h : q ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2) : q = 2 ∨ q = 3 ∨ q = 5 := by
  rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hq).1 h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
        (hq.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).1
      (hq.dvd_of_dvd_pow h1)))

private theorem s168e3_om4_sig_subset {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV)
    (h : Case162_7 D V₀ V hV L) {q : ℕ} (hq : q ∈ D.sig) : q = 2 ∨ q = 3 ∨ q = 5 := by
  have hqp := D.sig_prime q hq
  have h2 : q ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    obtain ⟨E, hE, -, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank hqp.1.one_lt (Mbar D.M V₀ V hV)
    have hE2 : q ^ 2 ∣ Nat.card ↥E := by
      rw [hEcard]
      exact pow_dvd_pow q (c.two_le_pRank_mbar hq)
    exact hE2.trans (Subgroup.card_dvd_of_le hE)
  exact s168e3_om4_prime_dvd_201600 hqp.1
    ((dvd_pow_self q (by norm_num : 2 ≠ 0)).trans (h2.trans (s168e3_om4_card_mbar_dvd c h)))

theorem s168e3_om4_sig_cases {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) :
    D.sig = {3} ∨ D.sig = {5} := by
  by_cases h3 : 3 ∈ D.sig
  · exact Or.inl (c.std.sig_eq_three_of_mem h3)
  · refine Or.inr ?_
    obtain ⟨q, hq⟩ := c.std.hx.sig_nonempty
    have hq5 : q = 5 := by
      rcases s168e3_om4_sig_subset c h hq with h | h | h
      · exact absurd h (D.sig_prime q hq).2
      · exact absurd (by rwa [h] at hq) h3
      · exact h
    have h5 : 5 ∈ D.sig := by rw [← hq5]; exact hq
    refine Set.eq_singleton_iff_unique_mem.2 ⟨h5, ?_⟩
    intro x hx
    rcases s168e3_om4_sig_subset c h hx with h | h | h
    · exact absurd h (D.sig_prime x hx).2
    · exact absurd (by rwa [h] at hx) h3
    · exact h

private theorem s168e3_om4_N_normal {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hle : L ≤ D.M) (hs : s15 D.M V₀ V hV L = 1) :
    ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (barSub_mono V₀ V hV hle)).2
    (fun _ hg => Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg))

private theorem s168e3_om4_comp_layer {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) :
    (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) ≤
      CFSG.layer ↥(Mbar D.M V₀ V hV) := by
  haveI := s168e3_om4_N_normal c.setting.hyp151.le h.2.2
  obtain ⟨e⟩ := s16e_omc_equiv_alt_five_of_isOmegaPlus h.1
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV c.setting.hyp151.le
  exact s16e_omc_le_layer_of_equiv_alt_five ((Subgroup.subgroupOfEquivOfLe hle).trans e)

private theorem s168e3_om4_embeds_units {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ f : ↥(Subgroup.centralizer
          ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) : Set ↥(Mbar D.M V₀ V hV))) →*
          Kˣ, Function.Injective f := by
  obtain ⟨ρ, -, hρL⟩ := s16e_star_equiv D c.std.h1217 c.setting.hyp151 hV
  have hW := s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne h.2.2
  have hnat : NatOmegaPlus (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 4 2 := by
    rw [← hW]
    exact h.2.1
  obtain ⟨K, hKf, hKfin, hK4, f, hf⟩ := s16e_omc_centralizer_embeds_units hnat
  refine ⟨K, hKf, hKfin, hK4, ?_⟩
  have hleS : lStar D.M V₀ V hV L ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    barSub_mono _ V hV c.setting.hyp151.le
  let φ : ↥(Subgroup.centralizer
        ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) : Set ↥(Mbar D.M V₀ V hV))) →*
      ↥(Subgroup.centralizer (lStar D.M V₀ V hV L : Set (MulAut (vStar D.M V₀ V hV L)))) :=
    MonoidHom.codRestrict
      ((Mbar D.M (v1Sub D.M V₀ V hV L) V hV).subtype.comp
        (ρ.toMonoidHom.comp (Subgroup.centralizer
          ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
            Set ↥(Mbar D.M V₀ V hV))).subtype)) _ (by
      intro c'
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem : (⟨l, hleS hl⟩ : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) ∈
          (lStar D.M V₀ V hV L).subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
        Subgroup.mem_subgroupOf.2 hl
      rw [← hρL] at hmem
      obtain ⟨n, hn, hnl⟩ := Subgroup.mem_map.1 hmem
      have hcomm : n * (c' : ↥(Mbar D.M V₀ V hV)) = (c' : ↥(Mbar D.M V₀ V hV)) * n :=
        Subgroup.mem_centralizer_iff.1 c'.2 n hn
      have h1 : ρ (n * (c' : ↥(Mbar D.M V₀ V hV))) = ρ ((c' : ↥(Mbar D.M V₀ V hV)) * n) := by
        rw [hcomm]
      rw [map_mul, map_mul] at h1
      have h2 := congrArg Subtype.val h1
      have hnl' : ((ρ n : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
          MulAut (vStar D.M V₀ V hV L)) = l := congrArg Subtype.val hnl
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hnl'] at h2
      exact h2)
  have hφ : Function.Injective φ := by
    intro c' c'' hcc'
    have h1 := congrArg Subtype.val hcc'
    exact Subtype.ext (ρ.injective (Subtype.ext h1))
  exact ⟨f.comp φ, hf.comp hφ⟩

private theorem s168e3_om4_comp_centralizer {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L)
    (h27 : 27 ∣ Nat.card ↥(Mbar D.M V₀ V hV)) :
    Group.IsNilpotent ↥(Subgroup.centralizer
        ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) : Set ↥(Mbar D.M V₀ V hV))) ∧
      Nonempty (↥(Subgroup.centralizer
          ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
            Set ↥(Mbar D.M V₀ V hV))) ≃* Multiplicative (ZMod 3)) := by
  haveI := s168e3_om4_N_normal c.setting.hyp151.le h.2.2
  obtain ⟨e⟩ := s16e_omc_equiv_alt_five_of_isOmegaPlus h.1
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV c.setting.hyp151.le
  have he : ↥((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) ≃*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans e
  have hne : Subgroup.centralizer
      ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
        Set ↥(Mbar D.M V₀ V hV)) ≠ ⊥ :=
    s16e_omc_centralizer_ne_bot he h27
  haveI : Nontrivial ↥(Subgroup.centralizer
      ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
        Set ↥(Mbar D.M V₀ V hV))) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨K, hKf, hKfin, hK4, f, hf⟩ := s168e3_om4_embeds_units c h
  exact s16e_omc_nilpotent_equiv_zmod_three hK4 f hf

private theorem s168e3_om4_comp_center_bot {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) :
    (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) ⊓ Subgroup.centralizer
        ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
          Set ↥(Mbar D.M V₀ V hV)) = ⊥ := by
  haveI := s168e3_om4_N_normal c.setting.hyp151.le h.2.2
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eΩ⟩⟩ := h.1
  letI := hKf
  letI := hKfin
  haveI hKchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  have h4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  obtain ⟨e4⟩ := nonempty_statedOmegaFour_mulEquiv_prod (K := K) h4
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV c.setting.hyp151.le
  let e : ↥((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) ≃*
      ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans
      (eΩ.trans ((statedProjStatedOmegaFourEquiv K).trans e4))
  have hSL : Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
    rw [CFSG.GH74.L5U5.center_statedSL_eq (F := K) 2]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  have hcX : Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) = ⊥ := by
    simp [Subgroup.center_prod (G := ↥(StatedSL 2 K)) (H := ↥(StatedSL 2 K)), hSL]
  have hcN : Subgroup.center ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hz' : e z ∈ Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.1 hz y'
    rw [hcX] at hz'
    have hz1 : e z = 1 := Subgroup.mem_bot.1 hz'
    have hzN : z = 1 := e.injective (by simpa using hz1)
    simpa using hzN
  rw [← CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H.map_center_eq_inf_centralizer
    ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)), hcN, Subgroup.map_bot]

theorem s168e3_om4_fstarBar_equiv {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L)
    (h27 : 27 ∣ Nat.card ↥(Mbar D.M V₀ V hV)) :
    Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L))) := by
  haveI hNnorm : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    s168e3_om4_N_normal c.setting.hyp151.le h.2.2
  obtain ⟨hCnil, hCiso⟩ := s168e3_om4_comp_centralizer c h h27
  have hFstar := s16e_omf_generalizedFitting_eq_sup_centralizer
    (s168e3_om4_comp_layer c h) hCnil
  obtain ⟨eF⟩ := s16e_omf_nonempty_mulEquiv_centralizer_prod hFstar
    (s168e3_om4_comp_center_bot c h)
  obtain ⟨eC⟩ := hCiso
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV c.setting.hyp151.le
  have hfb : fstarBar D.M V₀ V hV =
      (CFSG.generalizedFitting ↥(Mbar D.M V₀ V hV)).map (Mbar D.M V₀ V hV).subtype := by
    simp only [fstarBar, Fstar, CFSG.Adapters.genFittingFStar_eq_foundations]
  have e1 : ↥(fstarBar D.M V₀ V hV) ≃*
      ↥(CFSG.generalizedFitting ↥(Mbar D.M V₀ V hV)) := by
    rw [hfb]
    exact (Subgroup.equivMapOfInjective _ (Mbar D.M V₀ V hV).subtype
      (Mbar D.M V₀ V hV).subtype_injective).symm
  let eN : ↥((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) ≃* ↥(lBar V₀ V hV L) :=
    Subgroup.subgroupOfEquivOfLe hle
  exact ⟨e1.trans (eF.trans (MulEquiv.prodCongr eC eN))⟩

theorem s168e3_om4_false_of_not_dvd {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) (h3 : D.sig = {3})
    (h27 : ¬ 27 ∣ Nat.card ↥(Mbar D.M V₀ V hV)) : False := by
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV c.setting.hyp151.le
  refine s168e3_false_of_kernel c Nat.prime_three (by rw [h3]; exact Set.mem_singleton 3)
    (s168e3_kernel_of_cube Nat.prime_three _ (by simpa using h27) fun x hx => ?_)
  obtain ⟨ψ, hψ, hψo, hψx⟩ := s16n9b_natOmegaPlus_fix (s168e3_om4_natBar c h) hx
  exact ⟨ψ, hle hψ, hψo, hψx⟩

theorem s168e3_row162_7 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_7 D V₀ V hV L) : Final168F D V₀ V hV L := by
  have hwT := s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne h.2.2
  rcases s168e3_om4_sig_cases c h with h3 | h5
  · by_cases h27 : 27 ∣ Nat.card ↥(Mbar D.M V₀ V hV)
    · refine Final168F.of_case168_5Star ⟨s168e3_om4_fstarBar_equiv c h h27, h.1, ?_, h3⟩
      rw [← hwT]
      exact h.2.1
    · exact (s168e3_om4_false_of_not_dvd c h h3 h27).elim
  · exact Final168F.of_case167_5 ⟨h.1, s168e3_om4_natBar c h, h5⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
