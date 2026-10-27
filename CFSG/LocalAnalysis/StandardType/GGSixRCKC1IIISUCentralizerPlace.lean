module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIFixedUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
import CFSG.LocalAnalysis.StandardType.GGSixUnitaryTwoInnerDiag
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCore
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAut
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType.RCKC1

open Matrix Module CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.LieType.BorelTits
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCKK1IIISU

private theorem sucp_fourAt_coreCommAt_suV {k : ℕ} (hk : 4 ≤ k) :
    FourAt (⊤ : Subgroup (SUG k)) (suV hk) (suR hk) ∧
      CoreCommAt (⊤ : Subgroup (SUG k)) (suV hk) (suR hk) := by
  constructor
  · refine ⟨suR_mem_suV hk, le_top, isElemAbelian_suV hk, card_suV hk, suR_ne_one hk, ?_⟩
    intro v hv hv1
    obtain ⟨j, hj⟩ := suV_conj hk v hv hv1
    exact ⟨j, Subgroup.mem_top _, hj⟩
  · intro v hv y hy
    rw [top_inf_eq] at hy
    have hcomm : v * y = y * v :=
      (Subgroup.mem_centralizer_iff.mp (rckSU_core hk hy)) v (suV_le_suZ0 hk hv)
    have hone : v * y * v⁻¹ * y⁻¹ = 1 := by rw [hcomm]; group
    rw [hone]
    exact Subgroup.one_mem _

theorem fourAt_coreCommAt_conj_suV {k : ℕ} (hk : 4 ≤ k) (g : SUG k) :
    FourAt (⊤ : Subgroup (SUG k)) ((suV hk).map (MulAut.conj g).toMonoidHom)
        (g * suR hk * g⁻¹) ∧
      CoreCommAt (⊤ : Subgroup (SUG k)) ((suV hk).map (MulAut.conj g).toMonoidHom)
        (g * suR hk * g⁻¹) := by
  have hstd := sucp_fourAt_coreCommAt_suV hk
  let e : (⊤ : Subgroup (SUG k)) ≃* SUG k := Subgroup.topEquiv.trans (MulAut.conj g)
  have he : e ⟨suR hk, Subgroup.mem_top _⟩ = g * suR hk * g⁻¹ := by
    change g * suR hk * g⁻¹ = g * suR hk * g⁻¹
    rfl
  have hmap : ((suV hk).subgroupOf ⊤).map e.toMonoidHom =
      (suV hk).map (MulAut.conj g).toMonoidHom := by
    change ((suV hk).subgroupOf ⊤).map
        ((MulAut.conj g).toMonoidHom.comp (Subgroup.subtype ⊤)) =
      (suV hk).map (MulAut.conj g).toMonoidHom
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (le_top : suV hk ≤ ⊤)]
  constructor
  · rw [← he, ← hmap]
    exact fourAt_map_mulEquiv e (Subgroup.mem_top _) hstd.1
  · rw [← he, ← hmap]
    exact coreCommAt_map_mulEquiv e (Subgroup.mem_top _) hstd.2

theorem exists_conj_suV_of_unitary_linear_embedding {k n : ℕ} (hk : 4 ≤ k) (hn : 4 ≤ n)
    (ι : SUG k →* SUG n) (hι : Function.Injective ι)
    (E : (Fin k → SUF) →ₗ[SUF] (Fin n → SUF)) (hE : Function.Injective E)
    (W : Submodule SUF (Fin n → SUF))
    (hAct : ∀ g x, natRep (SU SUσ n) (ι g) (E x) = E (natRep (SU SUσ k) g x))
    (hFix : ∀ g w, w ∈ W → natRep (SU SUσ n) (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ W, z = E x + w) :
    ∃ g : SUG n, ι (suR hk) = g * suR hn * g⁻¹ ∧
      (suV hk).map ι = (suV hn).map (MulAut.conj g).toMonoidHom := by
  have hstd := sucp_fourAt_coreCommAt_suV hk
  have hFour : FourAt (⊤ : Subgroup (SUG n)) ((suV hk).map ι) (ι (suR hk)) := by
    refine ⟨Subgroup.mem_map_of_mem ι (suR_mem_suV hk), le_top,
      (isElemAbelian_suV hk).map ι, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective hι, card_suV hk]
    · intro h1
      exact suR_ne_one hk (hι (h1.trans (map_one ι).symm))
    · intro v hv hv1
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      have hu1 : u ≠ 1 := by
        intro h1
        exact hv1 (by rw [h1, map_one])
      obtain ⟨j, hj⟩ := suV_conj hk u hu hu1
      refine ⟨ι j, Subgroup.mem_top _, ?_⟩
      rw [hj, map_mul, map_mul, map_inv]
  have hRank : (mat SUσ n (ι (suR hk)) - 1).rank = 2 :=
    (rank_sub_one_of_unitary_linear_embedding ι E hE W hAct hFix hSplit
      (suR hk)).trans (rckSU_rank_suR_sub_one hk)
  have hFixK := rckSU_fixes_fixed_space_of_rank_two hk hstd.1 hstd.2
    (rckSU_rank_suR_sub_one hk)
  have hFix₁ := fixes_fixed_space_of_unitary_linear_embedding ι E hE W hAct hFix hSplit hFixK
  have hsq : ι (suR hk) ^ 2 = 1 := by
    rw [← map_pow, rckSU_suR_sq hk, map_one]
  have hne : ι (suR hk) ≠ 1 := by
    intro h1
    exact suR_ne_one hk (hι (h1.trans (map_one ι).symm))
  have hr : orderOf (ι (suR hk)) = 2 := orderOf_eq_prime hsq hne
  have hCoreLe := rckSU_core_le_centralizer_of_fix_fixed_space hn hr hRank hFix₁
  have hCore : CoreCommAt (⊤ : Subgroup (SUG n)) ((suV hk).map ι) (ι (suR hk)) := by
    intro v hv y hy
    rw [top_inf_eq] at hy
    have hcomm : v * y = y * v :=
      (Subgroup.mem_centralizer_iff.mp (hCoreLe hy)) v hv
    have hone : v * y * v⁻¹ * y⁻¹ = 1 := by rw [hcomm]; group
    rw [hone]
    exact Subgroup.one_mem _
  exact rckSU_exists_conj_suV_of_rank_two hn hFour hCore hRank

theorem ggSixRCKJRow_range_of_ker_le_center {X Y : Type} [Group X] [Group Y] {i : GGSixRCKRow}
    {J : Subgroup X} (hrow : GGSixRCKJRow i J) (ε : ↥J →* Y)
    (hεker : ε.ker ≤ Subgroup.center ↥J) : GGSixRCKJRow i ε.range := by
  change LargeEvenMarking ↥J (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = i) at hrow
  have hperfJ : Group.IsPerfect ↥J := Group.isPerfect_def.2 hrow.1
  have hsurj : Function.Surjective (ε.rangeRestrict : ↥J →* ↥ε.range) :=
    MonoidHom.rangeRestrict_surjective ε
  have hker : (ε.rangeRestrict : ↥J →* ↥ε.range).ker ≤ Subgroup.center ↥J := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hεker
  have hperfR : Group.IsPerfect ↥ε.range := Group.IsPerfect.ofSurjective hsurj
  have hc : Subgroup.center ↥J =
      ((QuotientGroup.mk' (Subgroup.center ↥ε.range)).comp
        (ε.rangeRestrict : ↥J →* ↥ε.range)).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hperfJ
      (ε.rangeRestrict : ↥J →* ↥ε.range) hsurj hker).symm
  let e : ↥J ⧸ Subgroup.center ↥J ≃* ↥ε.range ⧸ Subgroup.center ↥ε.range :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hsurj))
  exact CFSG.StandardType.SCFourCover.largeEvenMarking_centerQuot e.symm
    (Group.isPerfect_def.1 hperfR) (fun _ _ _ _ _ _ h => h) hrow


theorem eq_of_range_eq_of_central_ker_SUG {Y : Type} [Group Y] {m n : ℕ} (hm : 4 ≤ m)
    (hn : 4 ≤ n) (ψ : SUG m →* Y) (hψker : ψ.ker ≤ Subgroup.center (SUG m))
    (π : SUG n →* Y) (hπker : π.ker ≤ Subgroup.center (SUG n)) (h : π.range = ψ.range) :
    n = m := by
  have hadm : StatedLieAdmissible .PSU m 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by intro h; have := (Prod.mk.inj h).1; omega⟩
  have hrn : StatedLieAdmissible .PSU n 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by intro h; have := (Prod.mk.inj h).1; omega⟩
  have hrk : 2 ≤ (ggU .PSU m 1).D.rank := by
    rw [ggU_PSU_rank m 1 le_rfl]
    omega
  have hnrk : 2 ≤ (ggU .PSU n 1).D.rank := by
    rw [ggU_PSU_rank n 1 le_rfl]
    omega
  have hX := lieModel_range_centerQuot (G := Y) hadm hrk ψ hψker
  have hY := lieModel_range_centerQuot (G := Y) hrn hnrk π hπker
  have hY' : LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .PSU n 2 1 := h ▸ hY
  exact (CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq hm hX hY' rfl).2.1

theorem rckSU_exists_conj_suV_of_centralizer_component
    {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] {m : ℕ} (hm : 4 ≤ m)
    {J V : Subgroup X} {r : X} (hrow : GGSixRCKJRow .III J)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥J)))
    {D : Subgroup Y} (ψ : SUG m →* Y) (hψ : ψ.range = D)
    (hψker : ψ.ker ≤ Subgroup.center (SUG m))
    {d : Y} (hdD : d ∈ Subgroup.normalizer (D : Set Y)) (hd3 : d ^ 3 = 1)
    (ε : ↥J →* Y) (hεker : ε.ker ≤ Subgroup.center ↥J)
    (hcomp : CFSG.Assembly.IsComponentOf ε.range
      (D ⊓ Subgroup.centralizer ({d} : Set Y)))
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    ∃ (hrJ : r ∈ J) (g : SUG m), ε ⟨r, hrJ⟩ = ψ (g * suR hm * g⁻¹) ∧
      (V.subgroupOf J).map ε = (suV hm).map (ψ.comp (MulAut.conj g).toMonoidHom) := by
  subst hψ
  let Jy : Subgroup Y := ε.range
  have hJperf : Group.IsPerfect ↥J := ⟨hrow.1⟩
  have hJyD : Jy ≤ ψ.range := hcomp.1.trans inf_le_left
  have hrowY : GGSixRCKJRow .III Jy :=
    ggSixRCKJRow_range_of_ker_le_center hrow ε hεker
  have hBN : Subgroup.zpowers d ≤ Subgroup.normalizer (ψ.range : Set Y) :=
    Subgroup.zpowers_le.mpr hdD
  have hBpow : ∀ b ∈ Subgroup.zpowers d, b ^ 3 = 1 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    calc (d ^ k) ^ 3 = (d ^ k) ^ ((3 : ℕ) : ℤ) :=
          (_root_.zpow_natCast (d ^ k) 3).symm
      _ = d ^ (k * ((3 : ℕ) : ℤ)) := by rw [_root_.zpow_mul]
      _ = d ^ (((3 : ℕ) : ℤ) * k) := by rw [mul_comm k ((3 : ℕ) : ℤ)]
      _ = (d ^ ((3 : ℕ) : ℤ)) ^ k := by rw [_root_.zpow_mul]
      _ = (d ^ 3) ^ k := by rw [_root_.zpow_natCast]
      _ = 1 := by rw [hd3, _root_.one_zpow]
  have hAdm : StatedLieAdmissible .PSU m 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by
      intro h
      have := (Prod.mk.inj h).1
      omega⟩
  have hQ := isQuasisimple_SU rckSU_suF_card (by omega : 3 ≤ m) hAdm.2.2.2
  have hKperf : commutator ↥ψ.range = ⊤ :=
    (@Group.IsPerfect.range (SUG m) Y _ _ ψ hQ.1).commutator_eq_top
  have hcenmap : (Subgroup.center (SUG m)).map ψ.rangeRestrict =
      Subgroup.center ↥ψ.range :=
    @CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel (SUG m) ↥ψ.range
      _ _ hQ.1 ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ) (by
        rw [MonoidHom.ker_rangeRestrict]
        exact hψker)
  have hoddK : Odd (Nat.card (Subgroup.center ↥ψ.range)) := by
    rw [← hcenmap]
    exact Odd.of_dvd_nat (odd_natCard_of_le_center_SU SUσ le_rfl)
      (Subgroup.card_map_dvd _ _)
  have hrk : 2 ≤ (ggU .PSU m 1).D.rank := by
    rw [ggU_PSU_rank m 1 le_rfl]
    omega
  have hLM : LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .PSU m 2 1 :=
    lieModel_range_centerQuot hAdm hrk ψ hψker
  obtain ⟨φ, hφr, hφk, hφd⟩ :=
    exists_unitary_two_innerDiag_presentation hBN hBpow hKperf hoddK hm hLM
  have hBlock : FixedSUBlockAt ψ.range Jy :=
    fixedSUBlockAt_of_native_unitary_model (g := 0) Nat.prime_three (by norm_num) hd3
      φ hφr hφk hdD (hφd d (Subgroup.mem_zpowers d)) hcomp hrowY
  obtain ⟨n, π, hπ, hπker, S, e, J₀, hS, he, hadj, hdeg, hJ₀, hImage⟩ := hBlock
  obtain ⟨k, η₀, ι, E, W, hk, hn, hι, hComp, hE, hAct, hFix, hSplit⟩ :=
    exists_unitary_linear_block_model_at_two S hS he hadj hdeg hJ₀
  have hker' : (ψ.range.subtype.comp π).ker ≤ Subgroup.center (SUG n) := by
    intro x hx
    exact hπker (Subtype.ext hx)
  have hrange' : (ψ.range.subtype.comp π).range = ψ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hπ, Subgroup.map_top,
      Subgroup.range_subtype]
  have hnm : n = m :=
    eq_of_range_eq_of_central_ker_SUG hm hn ψ hψker (ψ.range.subtype.comp π) hker' hrange'
  subst n
  have hιJ : ∀ y : SUG k, ι y ∈ J₀ := by
    intro y
    rw [← η₀.apply_symm_apply y, hComp]
    exact (η₀.symm y).2
  let ψk : SUG k →* ↥Jy :=
    (((ψ.range.subtype.comp π).comp ι).codRestrict Jy) (fun y => by
      have hy : (π.comp ι) y ∈ J₀.map π := Subgroup.mem_map_of_mem π (hιJ y)
      rw [hImage] at hy
      exact Subgroup.mem_subgroupOf.mp hy)
  have hψk : Function.Surjective ψk := by
    intro j
    have hj : (⟨j, hJyD j.2⟩ : ↥ψ.range) ∈ Jy.subgroupOf ψ.range := by
      rw [Subgroup.mem_subgroupOf]
      exact j.2
    rw [← hImage] at hj
    obtain ⟨a, ha, haπ⟩ := Subgroup.mem_map.mp hj
    refine ⟨η₀ ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    change (π (ι (η₀ ⟨a, ha⟩)) : Y) = (j : Y)
    rw [hComp]
    exact congrArg Subtype.val haπ
  have hψkker : ψk.ker ≤ Subgroup.center (SUG k) := by
    intro y hy
    have hy1 : π (ι y) = 1 := by
      apply Subtype.ext
      have h : (ψk y : Y) = 1 := congrArg (fun z : ↥Jy => (z : Y)) hy
      change (π (ι y) : Y) = 1 at h
      exact h
    have hycen : ι y ∈ Subgroup.center (SUG m) := hπker hy1
    rw [Subgroup.mem_center_iff]
    intro z
    apply hι
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hycen (ι z)
  let ε' : ↥J →* ↥Jy := ε.rangeRestrict
  have hε' : Function.Surjective ε' := MonoidHom.rangeRestrict_surjective ε
  have hε'ker : ε'.ker ≤ Subgroup.center ↥J := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hεker
  obtain ⟨hrJ, g, hgr, hgV⟩ :=
    rckSU_exists_conj_suV_of_central_cover hk hJperf hoddJ ε' hε' hε'ker ψk hψk hψkker
      hFour hCore hShort
  obtain ⟨g₁, hg₁r, hg₁V⟩ :=
    exists_conj_suV_of_unitary_linear_embedding hk hm ι hι E hE W hAct hFix hSplit
  let g₂ : SUG m := ι g * g₁
  have hιg₂ : ι (g * suR hk * g⁻¹) = g₂ * suR hm * g₂⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg₁r]
    simp only [g₂]
    group
  have hcomm : ι.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (ι g)).toMonoidHom.comp ι := by
    apply MonoidHom.ext
    intro x
    change ι ((MulAut.conj g) x) = (MulAut.conj (ι g)) (ι x)
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hconjcomp (a b : SUG m) :
      ((suV hm).map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        (suV hm).map (MulAut.conj (a * b)).toMonoidHom := by
    have h : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (a * b)).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change (MulAut.conj a) ((MulAut.conj b) x) = (MulAut.conj (a * b)) x
      rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [Subgroup.map_map, h]
  have hιV : ((suV hk).map (MulAut.conj g).toMonoidHom).map ι =
      (suV hm).map (MulAut.conj g₂).toMonoidHom := by
    rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hg₁V]
    exact hconjcomp (ι g) g₁
  let r₁ : SUG m := g₂ * suR hm * g₂⁻¹
  let V₁ : Subgroup (SUG m) := (suV hm).map (MulAut.conj g₂).toMonoidHom
  have hFour₁ : FourAt (⊤ : Subgroup (SUG m)) V₁ r₁ :=
    (fourAt_coreCommAt_conj_suV hm g₂).1
  have hCore₁ : CoreCommAt (⊤ : Subgroup (SUG m)) V₁ r₁ :=
    (fourAt_coreCommAt_conj_suV hm g₂).2
  have hr₁2 : r₁ ^ 2 = 1 := hFour₁.2.2.1.2 r₁ hFour₁.1
  have hoddπ : Odd (Nat.card π.ker) := odd_natCard_of_le_center_SU SUσ hπker
  have hFourD : FourAt (⊤ : Subgroup ↥ψ.range) (V₁.map π) (π r₁) :=
    fourAt_map_of_odd_central_ker π hπ hπker hoddπ hFour₁
  have hCoreD : CoreCommAt (⊤ : Subgroup ↥ψ.range) (V₁.map π) (π r₁) :=
    coreCommAt_map_of_odd_central_ker π hπ hπker hoddπ hr₁2 hCore₁
  let ψD : SUG m →* ↥ψ.range := ψ.rangeRestrict
  have hψD : Function.Surjective ψD := MonoidHom.rangeRestrict_surjective ψ
  have hψDker : ψD.ker ≤ Subgroup.center (SUG m) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hψker
  have hoddψ : Odd (Nat.card ψD.ker) := odd_natCard_of_le_center_SU SUσ hψDker
  obtain ⟨VU, rU, hFourU, hCoreU, hmapU, hrU⟩ :=
    exists_fourAt_coreCommAt_comap_of_odd_central_ker ψD hψD hψDker hoddψ hFourD hCoreD
  have hrU2 : rU ^ 2 = 1 := hFourU.2.2.1.2 rU hFourU.1
  have hrank : (mat SUσ m r₁ - 1).rank = (mat SUσ m rU - 1).rank :=
    rank_sub_one_eq_of_central_covers hm π ψD hπ hψD hπker hψDker hr₁2 hrU2 hrU.symm
  have hr₁rank : (mat SUσ m r₁ - 1).rank = 2 := by
    have h1 : (mat SUσ m ((MulAut.conj g₂) (suR hm)) - 1).rank = 2 := by
      rw [rckSU_rank_mulAut_sub_one hm (MulAut.conj g₂) (suR hm),
        rckSU_rank_suR_sub_one hm]
    simpa [r₁, MulAut.conj_apply] using h1
  have hRankU : (mat SUσ m rU - 1).rank = 2 := by
    rw [← hrank, hr₁rank]
  obtain ⟨g', hg'r, hg'V⟩ := rckSU_exists_conj_suV_of_rank_two hm hFourU hCoreU hRankU
  refine ⟨hrJ, g', ?_, ?_⟩
  · calc ε ⟨r, hrJ⟩ = ↑(ε' ⟨r, hrJ⟩) := rfl
      _ = ↑(ψk (g * suR hk * g⁻¹)) := by rw [hgr]
      _ = ↑(π (ι (g * suR hk * g⁻¹))) := rfl
      _ = ↑(π r₁) := by rw [hιg₂]
      _ = ↑(ψD rU) := by rw [hrU]
      _ = ψ rU := rfl
      _ = ψ (g' * suR hm * g'⁻¹) := by rw [hg'r]
  · have hεeq : Jy.subtype.comp ε' = ε := MonoidHom.ext fun _ => rfl
    have hψkeq : Jy.subtype.comp ψk = (ψ.range.subtype.comp π).comp ι :=
      MonoidHom.ext fun _ => rfl
    have hψDeq : ψ.range.subtype.comp ψD = ψ := MonoidHom.ext fun _ => rfl
    have hV₁eq : ((suV hk).map (ψk.comp (MulAut.conj g).toMonoidHom)).map Jy.subtype =
        (((suV hk).map (MulAut.conj g).toMonoidHom).map ι).map
          (ψ.range.subtype.comp π) := by
      calc ((suV hk).map (ψk.comp (MulAut.conj g).toMonoidHom)).map Jy.subtype
          = (suV hk).map
              (Jy.subtype.comp (ψk.comp (MulAut.conj g).toMonoidHom)) :=
            Subgroup.map_map (suV hk) Jy.subtype
              (ψk.comp (MulAut.conj g).toMonoidHom)
        _ = (suV hk).map (((ψ.range.subtype.comp π).comp ι).comp
              (MulAut.conj g).toMonoidHom) := by
            rw [← MonoidHom.comp_assoc (MulAut.conj g).toMonoidHom ψk Jy.subtype,
              hψkeq]
        _ = ((suV hk).map (MulAut.conj g).toMonoidHom).map
              ((ψ.range.subtype.comp π).comp ι) :=
            (Subgroup.map_map (suV hk) ((ψ.range.subtype.comp π).comp ι)
              (MulAut.conj g).toMonoidHom).symm
        _ = (((suV hk).map (MulAut.conj g).toMonoidHom).map ι).map
              (ψ.range.subtype.comp π) :=
            (Subgroup.map_map ((suV hk).map (MulAut.conj g).toMonoidHom)
              (ψ.range.subtype.comp π) ι).symm
    calc (V.subgroupOf J).map ε
        = ((V.subgroupOf J).map ε').map Jy.subtype := by
          rw [Subgroup.map_map, hεeq]
      _ = ((suV hk).map (ψk.comp (MulAut.conj g).toMonoidHom)).map Jy.subtype := by
          rw [hgV]
      _ = (((suV hk).map (MulAut.conj g).toMonoidHom).map ι).map
            (ψ.range.subtype.comp π) := hV₁eq
      _ = V₁.map (ψ.range.subtype.comp π) := by rw [hιV]
      _ = (V₁.map π).map ψ.range.subtype :=
        (Subgroup.map_map V₁ ψ.range.subtype π).symm
      _ = (VU.map ψD).map ψ.range.subtype := by rw [← hmapU]
      _ = VU.map ψ := by
          rw [Subgroup.map_map, hψDeq]
      _ = (suV hm).map (ψ.comp (MulAut.conj g').toMonoidHom) := by
        rw [hg'V, Subgroup.map_map]

end CFSG.StandardType.RCKC1
