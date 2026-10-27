module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem s16w_isPGroup_ker_of_two_multiplier {Y : Type} [Group Y] [Finite Y]
    (hperf : Group.IsPerfect Y)
    (hlayer : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Y ⧸ CFSG.pCore 2 Y)) = ⊤)
    (N : Subgroup Y) [N.Normal] (hN : Group.IsSolvable ↥N) {X : Type} [Group X] [Finite X]
    (e : Y ⧸ N ≃* X) (hX : CFSG.Open.IsQuasisimple X)
    (hz : Odd (Nat.card (Subgroup.center X)))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 ^ k) :
    IsPGroup 2 ↥N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect Y := hperf
  haveI : Group.IsPerfect X := ⟨hX.1⟩
  let R : Subgroup Y := CFSG.pCore 2 Y
  let π : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  let f : Y →* X := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hfker : f.ker = N := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : QuotientGroup.mk' N y = 1 := by
        apply e.injective
        simpa [f] using h
      exact (QuotientGroup.eq_one_iff y).mp h1
    · intro h
      have h1 : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff y).mpr h
      show f y = 1
      rw [show f y = e (QuotientGroup.mk' N y) from rfl, h1, map_one]
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w, hw⟩ := e.surjective z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N w
    exact ⟨y, hw⟩
  have hP2 : IsPGroup 2 ↥(R.map f) := (CFSG.pCore_isPGroup (p := 2) (G := Y)).map f
  have hP2n : (R.map f).Normal :=
    Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := Y)) f hf
  have hRle : R ≤ N := by
    rcases CFSG.ASVolI.A129Aux.normal_eq_top_or_le_center hX hP2n with htop | hcen
    · exfalso
      have h2X : IsPGroup 2 X := by
        have htop' : IsPGroup 2 ↥(⊤ : Subgroup X) := htop ▸ hP2
        exact htop'.of_equiv Subgroup.topEquiv
      haveI : Nontrivial (X ⧸ Subgroup.center X) := hX.2.toNontrivial
      haveI : Nontrivial X := (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
      exact Group.IsPerfect.not_isNilpotent X h2X.isNilpotent
    · intro y hy
      have hmem : f y ∈ R.map f := Subgroup.mem_map_of_mem f hy
      have hcent : f y ∈ Subgroup.center X := hcen hmem
      have h1 : orderOf (f y) = 1 := by
        obtain ⟨c, hc⟩ := hP2.exists_orderOf_eq_pow ⟨f y, hmem⟩
        have hord2 : orderOf (f y) = 2 ^ c := by
          rw [← Subgroup.orderOf_mk (f y) hmem]
          exact hc
        have hordZ : orderOf (f y) ∣ Nat.card (Subgroup.center X) := by
          have := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hcent
          simpa using this
        have hcop : Nat.Coprime (2 ^ c) (Nat.card (Subgroup.center X)) :=
          hz.coprime_two_left.pow_left c
        have hdvd2 : orderOf (f y) ∣ 2 ^ c := by rw [hord2]
        exact Nat.eq_one_of_dvd_coprimes hcop hdvd2 hordZ
      have h1' : f y = 1 := orderOf_eq_one_iff.mp h1
      rw [← hfker, MonoidHom.mem_ker]
      exact h1'
  have hfR : ∀ y ∈ R, f y = 1 := by
    intro y hy
    have h1 : y ∈ f.ker := by
      rw [hfker]
      exact hRle hy
    exact (MonoidHom.mem_ker).mp h1
  let q : Y ⧸ R →* X := QuotientGroup.lift R f hfR
  have hqπ : ∀ y : Y, q (π y) = f y := fun y => rfl
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨y, hy⟩ := hf a
    exact ⟨π y, by rw [hqπ]; exact hy⟩
  have hkerS : q.ker = N.map π := by
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    rw [MonoidHom.mem_ker, hqπ, Subgroup.mem_map]
    constructor
    · intro hfx
      refine ⟨x, ?_, rfl⟩
      have h1 : QuotientGroup.mk' N x = 1 := by
        apply e.injective
        simpa [f] using hfx
      exact (QuotientGroup.eq_one_iff x).mp h1
    · rintro ⟨x', hx', hxx'⟩
      have hx'' : x'⁻¹ * x ∈ R := (QuotientGroup.eq).mp hxx'
      have hxN : x ∈ N := by
        have := N.mul_mem hx' (hRle hx'')
        simpa using this
      have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hxN
      simp only [f, MonoidHom.comp_apply, h1, map_one]
  have hSsolv : Group.IsSolvable ↥q.ker := by
    rw [hkerS]
    exact Group.isSolvable_of_surjective (f := π.subgroupMap N)
      (MonoidHom.subgroupMap_surjective π N)
  haveI : q.ker.Normal := MonoidHom.normal_ker q
  have hSc : q.ker ≤ Subgroup.center (Y ⧸ R) :=
    close16_le_center_of_isSolvable hlayer hSsolv
  haveI : Group.IsPerfect (Y ⧸ R) := Group.IsPerfect.ofSurjective hπ
  have hdvd : Nat.card q.ker ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
    obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
      CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_schur_multiplier
        q hq hSc
    rw [← Nat.card_congr e'.toEquiv]
    refine (Subgroup.card_quotient_dvd_card _).trans ?_
    rw [← Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv]
  obtain ⟨k, hk⟩ := hmult
  have h2ker : IsPGroup 2 ↥q.ker :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := k) (hk ▸ hdvd)
  have hπker : IsPGroup 2 ↥π.ker := by
    rw [show π.ker = R from QuotientGroup.ker_mk' R]
    exact CFSG.pCore_isPGroup (p := 2) (G := Y)
  have hcomap : q.ker.comap π = N := by
    ext y
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, hqπ, ← hfker, MonoidHom.mem_ker]
  have hNpg : IsPGroup 2 ↥N := by
    have h1 := IsPGroup.comap_of_ker_isPGroup (p := 2) h2ker π hπker
    rwa [hcomap] at h1
  exact hNpg

variable {G : Type} [Group G] [Finite G]

private theorem s16w_preBarSub_mono {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {Xbar Ybar : Subgroup (MulAut (Vtil V₀ V hV))} (h : Xbar ≤ Ybar) :
    preBarSub M V₀ V hV Xbar ≤ preBarSub M V₀ V hV Ybar := by
  unfold preBarSub
  exact inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

private theorem s16w_layer_barImage {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {X : Subgroup G} {Kb : Subgroup (MulAut (Vtil V₀ V hV))}
    (hMs : D.M ≤ stabTil V₀ V) (hKM : Kb ≤ Mbar D.M V₀ V hV) (hXM : X ≤ D.M)
    (hbar : barSub V₀ V hV X = Kb) (hKq : CFSG.Open.IsQuasisimple ↥Kb)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X := by
  set B : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V X with hBdef
  have hqB : CFSG.Open.IsQuasisimple ↥B := by
    obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
    have hmap : B.map e.toMonoidHom = Kb.subgroupOf (Mbar D.M V₀ V hV) := by
      rw [hBdef, he X hXM, hbar]
    let eB : ↥B ≃* ↥Kb :=
      ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans
        (Subgroup.subgroupOfEquivOfLe hKM)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eB hKq
  exact le_antisymm (sSup_le fun _ hK => hK.1)
    (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)

private theorem s16w_preBarSub_conj_mem {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hMs : D.M ≤ stabTil V₀ V) (Xbar : Subgroup (MulAut (Vtil V₀ V hV)))
    (hXbar_le : Xbar ≤ Mbar D.M V₀ V hV)
    (hXbarN : (Xbar.subgroupOf (Mbar D.M V₀ V hV)).Normal) {m x : G} (hm : m ∈ D.M) :
    x ∈ preBarSub D.M V₀ V hV Xbar ↔ m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV Xbar := by
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hXbar_le).1 hXbarN
  constructor
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M V₀ V hV Xbar).1 hx
    have hst : m * x * m⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem (hMs hm) hxs)
        ((stabTil V₀ V).inv_mem (hMs hm))
    refine (mem_preBarSub D.M V₀ V hV Xbar).2
      ⟨D.M.mul_mem (D.M.mul_mem hm hxM) (D.M.inv_mem hm), hst, ?_⟩
    have hact : actTil V₀ V hV ⟨m * x * m⁻¹, hst⟩ =
        actTil V₀ V hV ⟨m, hMs hm⟩ * actTil V₀ V hV ⟨x, hxs⟩ *
          (actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹ := by
      rw [show (⟨m * x * m⁻¹, hst⟩ : stabTil V₀ V) =
          ⟨m, hMs hm⟩ * ⟨x, hxs⟩ * (⟨m, hMs hm⟩ : stabTil V₀ V)⁻¹ from
        Subtype.ext (by simp [mul_assoc]), map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub V₀ V hV hm (hMs hm)))
    exact (hmem (actTil V₀ V hV ⟨x, hxs⟩)).1 hxXbar
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M V₀ V hV Xbar).1 hx
    have hx_eq : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    have hxM' : x ∈ D.M := by
      rw [hx_eq]
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hm) hxM) hm
    have hxs' : x ∈ stabTil V₀ V := by
      rw [hx_eq]
      exact (stabTil V₀ V).mul_mem
        ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem (hMs hm)) hxs) (hMs hm)
    refine (mem_preBarSub D.M V₀ V hV Xbar).2 ⟨hxM', hxs', ?_⟩
    have hmsi : m⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem (hMs hm)
    have hact : actTil V₀ V hV ⟨x, hxs'⟩ =
        actTil V₀ V hV ⟨m⁻¹, hmsi⟩ * actTil V₀ V hV ⟨m * x * m⁻¹, hxs⟩ *
          (actTil V₀ V hV ⟨m⁻¹, hmsi⟩)⁻¹ := by
      rw [show (⟨x, hxs'⟩ : stabTil V₀ V) =
          ⟨m⁻¹, hmsi⟩ * ⟨m * x * m⁻¹, hxs⟩ * (⟨m⁻¹, hmsi⟩ : stabTil V₀ V)⁻¹ from
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group),
          map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub V₀ V hV (D.M.inv_mem hm) hmsi))
    exact (hmem (actTil V₀ V hV ⟨m * x * m⁻¹, hxs⟩)).1 hxXbar

private theorem s16w_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
    CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
    QuotientGroup.mk'_surjective _
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hcomap : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    change F11.O2E Y = (⊤ : Subgroup ↥Y).map Y.subtype
    rw [hYE, hTop]
  have h := Subgroup.map_comap_eq_self_of_surjective hπ
    (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)))
  rw [hcomap, Subgroup.map_top_of_surjective _ hπ] at h
  exact h.symm

def S16wCover (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Xb : Subgroup (MulAut (Vtil V₀ V hV))) : Prop :=
  ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧ barSub V₀ V hV Y = Xb ∧
    IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V)

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.cover_of_simple (h : S16gRowCtx D V₀ V L hV)
    {Kb : Subgroup (MulAut (Vtil V₀ V hV))} (hKM : Kb ≤ Mbar D.M V₀ V hV)
    (hKN : (Kb.subgroupOf (Mbar D.M V₀ V hV)).Normal) (hKs : IsSimpleGroup ↥Kb)
    (hKnc : ¬ IsMulCommutative ↥Kb)
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥Kb) = 2 ^ k) :
    S16wCover D V₀ V hV Kb := by
  haveI : IsSimpleGroup ↥Kb := hKs
  have hKq : CFSG.Open.IsQuasisimple ↥Kb := by
    have hperf : Group.IsPerfect ↥Kb :=
      TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hKnc
    have hcenter : Subgroup.center ↥Kb = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc
    refine ⟨hperf.commutator_eq_top, ?_⟩
    let e' : ↥Kb ⧸ Subgroup.center ↥Kb ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact e'.isSimpleGroup
  have hcenterK : Subgroup.center ↥Kb = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc
  have hzK : Odd (Nat.card (Subgroup.center ↥Kb)) := by
    rw [hcenterK, Subgroup.card_bot]
    exact odd_one
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  set X : Subgroup G := preBarSub D.M V₀ V hV Kb with hXdef
  have hX_le : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M V₀ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV hMn]
    exact s16w_preBarSub_mono bot_le
  have hbarX : barSub V₀ V hV X = Kb := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 hKM
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hMs
  have hlayerim : rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X :=
    s16w_layer_barImage hMs hKM hX_le hbarX hKq
  have hXnormal : (X.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX_le]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change x ∈ preBarSub D.M V₀ V hV Kb ↔ m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV Kb
    exact s16w_preBarSub_conj_mem hMs Kb hKM hKN hm
  obtain ⟨Y, hY, -⟩ :=
    h.std.h119 V₀ V (Hyp125.hyp11 h.std.h127 h.setting.hyp16.hyp125) X hCX hX_le hlayerim
  have hY_le : Y ≤ D.M := hY.1.trans hX_le
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hbarY : barSub V₀ V hV Y = Kb := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hY_le, ← he X hX_le, hY.2.2.2.2.2]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hY_le),
      inf_eq_left.2 (barSub_mono V₀ V hV hX_le), hbarX] at h2
    exact h2
  have hYs : Y ≤ stabTil V₀ V := hY_le.trans hMs
  let φ : ↥Y →* ↥(barSub V₀ V hV Y) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hYs)) (barSub V₀ V hV Y)
      (fun g => actTil_mem_barSub V₀ V hV g.2 (hYs g.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV Y ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  let N : Subgroup ↥Y := φ.ker
  have hNker : N = (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y := by
    ext g
    rw [show N = φ.ker from rfl, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_cTilde_iff hV hMn]
    have hgY : (g : G) ∈ Y := g.2
    constructor
    · intro h1
      exact ⟨hgY, hY_le hgY, hYs hgY, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  haveI : N.Normal := MonoidHom.normal_ker φ
  have hNsolv : Group.IsSolvable ↥N := by
    rw [hNker]
    have hle : (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y ≤ CFSG.solvableRadical ↥Y := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hY.2.2.2.2.1 (Subgroup.mem_subgroupOf.mp hx)
      have hzx' : z = x := Subtype.ext hzx
      exact hzx' ▸ hz
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥Y)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hperfY : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY.2.1
  have hlayerY : CFSG.Open.rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊤ :=
    s16w_layer_top_of_O2E_eq hY.2.2.1
  let eQ : ↥Y ⧸ N ≃* ↥Kb :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans (MulEquiv.subgroupCongr hbarY)
  have hN2 : IsPGroup 2 ↥N :=
    s16w_isPGroup_ker_of_two_multiplier hperfY hlayerY N hNsolv eQ hKq hzK hmult
  have hY2 : IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    have hN2' : IsPGroup 2 ↥((Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y) := hNker ▸ hN2
    exact hN2'.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ F11.CTilde D.M V₀ V ≤ Y))
  have hXYC : X = Y ⊔ F11.CTilde D.M V₀ V := by
    refine le_antisymm (fun x hx => ?_) (sup_le hY.1 hCX)
    have hxs : x ∈ stabTil V₀ V := hMs (hX_le hx)
    have hxbar := actTil_mem_barSub V₀ V hV hx hxs
    rw [hbarX, ← hbarY] at hxbar
    obtain ⟨g, hgY, hg⟩ := (mem_barSub V₀ V hV Y _).1 hxbar
    have hxc : x * (g : G)⁻¹ ∈ F11.CTilde D.M V₀ V := by
      rw [mem_cTilde_iff hV hMn]
      refine ⟨D.M.mul_mem (hX_le hx) (D.M.inv_mem (hY_le hgY)),
        (stabTil V₀ V).mul_mem hxs ((stabTil V₀ V).inv_mem g.2), ?_⟩
      have h1 : (⟨x * (g : G)⁻¹, (stabTil V₀ V).mul_mem hxs ((stabTil V₀ V).inv_mem g.2)⟩ :
          ↥(stabTil V₀ V)) = ⟨x, hxs⟩ * g⁻¹ := rfl
      rw [h1, map_mul, map_inv, hg, mul_inv_cancel]
    have hmem := Subgroup.mul_mem_sup hxc hgY
    rw [inv_mul_cancel_right, sup_comm] at hmem
    exact hmem
  have hXs : X ≤ stabTil V₀ V := hX_le.trans hMs
  let φX : ↥X →* ↥(barSub V₀ V hV X) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hXs)) (barSub V₀ V hV X)
      (fun g => actTil_mem_barSub V₀ V hV g.2 (hXs g.2))
  have hφX : Function.Surjective φX := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV X ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hkerX : φX.ker = (X ⊓ F11.CTilde D.M V₀ V).subgroupOf X := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cTilde_iff hV hMn]
    have hgX : (g : G) ∈ X := g.2
    constructor
    · intro h1
      exact ⟨hgX, hX_le hgX, hXs hgX, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  haveI : IsSimpleGroup ↥(barSub V₀ V hV X) := by rw [hbarX]; exact hKs
  have hnc : ¬ IsMulCommutative ↥(barSub V₀ V hV X) := by rw [hbarX]; exact hKnc
  obtain ⟨hXC, hXab⟩ := close16_simple_of_hom hCX hnc φX hφX
    (by rw [hkerX, inf_eq_right.2 hCX])
  exact ⟨Y, hY_le, close16_normal_of_cover (s15_Three_cTilde_normal hV hMs) hX_le hXnormal hCX
    hY.1 hY.2.2.2.1 hY.2.1 hXYC hY2 hXC hXab, hbarY, hY2⟩

theorem S16gRowCtx.cover_lBar (h : S16gRowCtx D V₀ V L hV)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k) :
    S16wCover D V₀ V hV (lBar V₀ V hV L) := by
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.setting.hyp151.le
  refine h.cover_of_simple hLM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 h.mBar_le_normalizer) hsimple ?_ hmult
  intro hc
  exact CFSG.LocalAnalysis.GLTheoremA.SFM12.not_all_commute_of_quasisimple h.quasi
    fun a b => hc.is_comm.comm a b

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
