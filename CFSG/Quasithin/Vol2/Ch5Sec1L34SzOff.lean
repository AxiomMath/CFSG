module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsD38
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Comp
public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

section Module

variable {W : Type} [CommGroup W] [Finite W]

theorem qhatOf_autSub_top_le (hexp : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} {c : ℚ}
    (hq : qhatOf X ≤ (c : WithTop ℚ)) :
    qhatOf (autSub X (⊤ : Subgroup W)) ≤ (c : WithTop ℚ) := by
  obtain ⟨A, hA2, hAk, hAr⟩ := kq_le_iff.mp hq
  have hAst : A ≤ stabSub (⊤ : Subgroup W) := le_stabSub_top A
  have hAf : A ⊓ centSub (⊤ : Subgroup W) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨-, ha⟩
    rw [Subgroup.mem_bot]
    ext u
    simpa using ha u trivial
  have hAU : commSub (⊤ : Subgroup W) A ≠ ⊥ := by
    intro hbot
    apply hA2.ne_bot
    rw [commSub_eq_bot_iff] at hbot
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    ext u
    simpa using hbot (Subgroup.mem_top u) a ha
  exact kq_le_iff.mpr ⟨autSub A _, IsA2.autSub hA2 hAst hAU, commSeries_autSub_eq_bot hAst hAk,
    (rAV_autSub_le_of_faithful hexp hAst hAf).trans hAr⟩

omit [Finite W] in
theorem le_stabSub_orbSup {Y T : Subgroup (MulAut W)} {I : Subgroup W}
    (hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W))) (hIY : ∀ y ∈ Y, ∀ w ∈ I, y w ∈ I) :
    Y ≤ stabSub (orbSup T I) := by
  refine le_stabSub_of_forall_mem fun y hy w hw => ?_
  have hsub : orbSup T I ≤ (orbSup T I).comap y.toMonoidHom := by
    refine orbSup_le fun t ht => ?_
    rintro _ ⟨i, hi, rfl⟩
    show y (t i) ∈ orbSup T I
    have hyt : t⁻¹ * y * t ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hTY (T.inv_mem ht)) y).mp hy
      simpa using this
    have e : y (t i) = t ((t⁻¹ * y * t) i) := by simp [MulAut.mul_apply]
    rw [e]
    exact map_le_orbSup ht ⟨_, hIY _ hyt i hi, rfl⟩
  exact hsub hw

theorem d3Std_of_irrPlusOn (hexp : ∀ w : W, w ^ 2 = 1) {X T L : Subgroup (MulAut W)}
    {I : Subgroup W} (hXq : IsQuotientOfSQTKTC ↥X) (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X)
    (hLq : CFSG.IsQuasisimple ↥L) (hI : I ∈ IrrPlusOn (conjClosure L T) (orbSup T I) T)
    (hLU : ¬ L ≤ centSub (orbSup T I))
    (hq : qhatOf (autSub (conjClosure L T ⊔ T) (orbSup T I)) ≤ ((2 : ℚ) : WithTop ℚ)) :
    D3Std (autSub (conjClosure L T ⊔ T) (orbSup T I)) (autSub (conjClosure L T) (orbSup T I))
      (autSub T (orbSup T I)) (autSub L (orbSup T I)) (I.subgroupOf (orbSup T I)) := by
  set Y := conjClosure L T with hYdef
  set U := orbSup T I with hUdef
  have hTX : T ≤ X := hT.1
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hLY : L ≤ Y := le_conjClosure L T
  have hYX : Y ≤ X := conjClosure_le fun t ht l hl =>
    X.mul_mem (X.mul_mem (hTX ht) (hLX hl)) (X.inv_mem (hTX ht))
  have hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)) := le_normalizer_conjClosure L T
  have hIY : ∀ y ∈ Y, ∀ w ∈ I, y w ∈ I := fun y hy w hw => hI.1.2.1 ⟨y, hy⟩ w hw
  have hYs : Y ≤ stabSub U := le_stabSub_orbSup hTY hIY
  have hTs : T ≤ stabSub U :=
    le_stabSub_of_forall_mem fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have hIU : I ≤ U := le_orbSup T I
  set M := Y ⊔ T with hMdef
  have hMs : M ≤ stabSub U := sup_le hYs hTs
  have hMX : M ≤ X := sup_le hYX hTX
  have hLM : L ≤ M := hLY.trans le_sup_left
  have hLs : L ≤ stabSub U := hLM.trans hMs
  have hexpU : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hexp])
  have eY : autSub Y U = (Y.subgroupOf M).map (resHomOn U hMs) :=
    autSub_eq_map_resHomOn le_sup_left hMs
  have eT : autSub T U = (T.subgroupOf M).map (resHomOn U hMs) :=
    autSub_eq_map_resHomOn le_sup_right hMs
  have eL : autSub L U = (L.subgroupOf M).map (resHomOn U hMs) :=
    autSub_eq_map_resHomOn hLM hMs
  have eM : autSub M U = (M.subgroupOf M).map (resHomOn U hMs) :=
    autSub_eq_map_resHomOn le_rfl hMs
  have hsup : autSub Y U ⊔ autSub T U = autSub M U := by
    rw [eY, eT, eM, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
  have hLne : autSub L U ≠ ⊥ := by
    obtain ⟨l, hl, hlU⟩ := Set.not_subset.mp hLU
    obtain ⟨u, hu, hne⟩ : ∃ u ∈ U, l u ≠ u := by
      by_contra hall
      push Not at hall
      exact hlU hall
    exact autSub_ne_bot_of_exists hLs le_rfl ⟨l, hl, u, hu, hne⟩
  have hSylM : IsSylowTwoOf (autSub T U) (autSub M U) := by
    rw [eT, eM]
    exact isSylowTwoOf_map_subgroupOf (resHomOn U hMs)
      (F7.isSylowTwoOf_mono_right hT le_sup_right hMX)
  have hcomp : autSub L U ∈ cComp (autSub M U) := by
    rw [eL, eM]
    exact map_subgroupOf_mem_cComp (resHomOn U hMs) (cComp_mem_of_le hL hLM hMX)
      (by rw [← eL]; exact hLne)
  have hquasi : CFSG.IsQuasisimple ↥(autSub L U) := by
    rw [eL]
    exact isQuasisimple_map_subgroupOf_of_ne_bot hLM hLq (resHomOn U hMs)
      (by rw [← eL]; exact hLne)
  have hMpeq : autSub Y U = conjClosure (autSub L U) (autSub T U) := by
    rw [eY, eL, eT]
    exact map_subgroupOf_conjClosure (resHomOn U hMs) hLM le_sup_right
  have hMnorm : autSub M U ≤ Subgroup.normalizer (autSub Y U : Set (MulAut ↥U)) := by
    rw [eM, eY]
    exact map_le_normalizer_map_of_le_normalizer (resHomOn U hMs) le_sup_left
      (sup_le Subgroup.le_normalizer hTY)
  have hTnAut : autSub T U ≤ Subgroup.normalizer (autSub Y U : Set (MulAut ↥U)) :=
    (autSub_mono le_sup_right U).trans hMnorm
  have hYAC : ActCompat U.subtype (autSub Y U) Y :=
    actCompat_autSub hYs le_rfl (fun a ha => ⟨a, ha, fun u _ => rfl⟩)
  have hTAC : ActCompat U.subtype (autSub T U) T :=
    actCompat_autSub hTs le_rfl (fun a ha => ⟨a, ha, fun u _ => rfl⟩)
  have hmapI : (I.subgroupOf U).map U.subtype = I := Subgroup.map_subgroupOf_eq_of_le hIU
  have hVirr : XMod.IsIrrPlus ↥(autSub Y U) (I.subgroupOf U) :=
    (hYAC.isIrrPlus_map_iff U.subtype_injective (I.subgroupOf U)).mp
      (by rw [hmapI]; exact hI.1.2)
  have hWT : ∀ t ∈ T, ∀ w ∈ U, t • w ∈ U := fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have hirrT : I.subgroupOf U ∈
      IrrPlusOn (autSub Y U) (orbSup (autSub T U) (I.subgroupOf U)) (autSub T U) := by
    rw [orbSup_eq_biSup_smul]
    exact hYAC.mem_irrPlusOn_of_map U.subtype_injective hTAC hTnAut hTY (Wq := U) hWT
      (by rw [hmapI]; exact hI)
  have hcommO2 : ∀ g ∈ pCoreOf 2 (autSub Y U ⊔ autSub T U), ∀ m ∈ autSub Y U,
      g * m = m * g := by
    intro g hg m hm
    rw [hsup] at hg
    have hle : autSub Y U ≤ Subgroup.centralizer ({g} : Set (MulAut ↥U)) := by
      rw [hMpeq]
      refine conjClosure_le fun τ hτ l hl => ?_
      have hτM : τ ∈ autSub M U := (autSub_mono le_sup_right U) hτ
      have hcompτ : (autSub L U).map (MulAut.conj τ).toMonoidHom ∈ cComp (autSub M U) :=
        CFSG.Quasithin.map_conj_mem_cComp hcomp hτM
      have hqτ : CFSG.IsQuasisimple ↥((autSub L U).map (MulAut.conj τ).toMonoidHom) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj τ).subgroupMap _) hquasi
      have h1 := commute_of_mem_pCoreOf_of_mem_cComp hcompτ hqτ hg
        (k := τ * l * τ⁻¹) ⟨l, hl, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h1.symm
    have h2 := hle hm
    rw [Subgroup.mem_centralizer_singleton_iff] at h2
    exact h2.symm
  have hSylF : IsSylowTwoOf (autSub T U) (autSub Y U ⊔ autSub T U) := by rw [hsup]; exact hSylM
  have hWT' : ∀ t ∈ autSub T U, ∀ w ∈ orbSup (autSub T U) (I.subgroupOf U),
      t • w ∈ orbSup (autSub T U) (I.subgroupOf U) := fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have ho2 : ∀ g ∈ pCoreOf 2 (autSub Y U ⊔ autSub T U), ∀ v ∈ I.subgroupOf U,
      g v ∈ I.subgroupOf U := by
    intro g hg v hv
    have hgT : g ∈ autSub T U := F7.isSylowTwoOf_pCoreOf_le hSylF hg
    have hiso := iso_tilde_smul_of_commute hTnAut hWT' hgT (hcommO2 g hg) (I.subgroupOf U)
    have hstab := (forall_smul_eq_iff_mem_irrPlusOn hTnAut hWT' hirrT.1).mpr hirrT g ⟨hgT, hiso⟩
    have h2 : g • v ∈ g • (I.subgroupOf U) := Subgroup.smul_mem_pointwise_smul v g _ hv
    rw [hstab] at h2
    exact h2
  have htop : orbSup (autSub T U) (I.subgroupOf U) = ⊤ :=
    orbSup_autSub_subgroupOf_eq_top hIU hTs le_rfl
  have hgen : (⨆ m ∈ autSub M U, (I.subgroupOf U).map m.toMonoidHom) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup₂_le fun τ hτ => le_iSup₂_of_le τ ((autSub_mono le_sup_right U) hτ) le_rfl
  have hqhat : qhatOf (autSub (autSub Y U ⊔ autSub T U)
      (orbSup (autSub T U) (I.subgroupOf U))) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [qhatOf_autSub_congr htop, hsup]
    exact qhatOf_autSub_top_le hexpU hq
  exact ⟨⟨hexpU, isQuotientOfSQTK_autSub_aux hMX hXq, hSylM, hcomp, hquasi, hMpeq, hMnorm,
    ⟨le_top, hVirr⟩, ho2, hgen⟩, hqhat, hirrT⟩

theorem false_of_qhatStar_of_suzuki (h38 : D38Top) (hW : ∀ w : W, w ^ 2 = 1)
    {X A L : Subgroup (MulAut W)} {r : ℚ} (hXq : IsQuotientOfSQTKTC ↥X)
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r < 2) (hA : A ∈ QhatStar X)
    (hL : L ∈ cComp X) (hLq : CFSG.IsQuasisimple ↥L)
    (hSz : ∃ n : ℕ, SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n)
    (hLA : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAX : A ≤ X := hA2.1
  have hA2p : IsPGroup 2 ↥A := hA2.2.2.isPGroup
  obtain ⟨T, hT, hAT⟩ := A4.exists_isSylowTwoOf_ge hAX hA2p
  have hTX : T ≤ X := hT.1
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hLX : L ≤ X := le_of_mem_cComp hL
  set Y := conjClosure L T with hYdef
  have hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W)) := le_normalizer_conjClosure L T
  have hLY : L ≤ Y := le_conjClosure L T
  have hYperf : ⁅Y, Y⁆ = Y := A3.conjClosure_perfect (perfect_of_mem_cComp hL)
  have hYne : commV Y ≠ ⊥ := by
    intro h
    rw [commV_eq_commSub, commSub_eq_bot_iff] at h
    apply ne_bot_of_mem_cComp hL
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    ext w
    simpa using h (Subgroup.mem_top w) l (hLY hl)
  obtain ⟨I₀, hI₀⟩ := B1Red.exists_mem_irrPlus hYperf hYne
  obtain ⟨I, hI₁⟩ := irrPlusOn_nonempty hW hTY hT2 hI₀
  have hactY : ActCompat (MonoidHom.id W) Y Y :=
    ⟨fun b hb => ⟨b, hb, fun _ => rfl⟩, fun a ha => ⟨a, ha, fun _ => rfl⟩⟩
  have hactT : ActCompat (MonoidHom.id W) T T :=
    ⟨fun b hb => ⟨b, hb, fun _ => rfl⟩, fun a ha => ⟨a, ha, fun _ => rfl⟩⟩
  have hI' : I ∈ IrrPlusOn Y (⨆ y ∈ T, y • I) T :=
    hactY.mem_irrPlusOn_of_map (fun _ _ h => h) hactT hTY hTY (Wq := ⨆ y ∈ T, y • I₀)
      (fun t ht w hw => smul_mem_biSup_smul ht hw) (by rw [Subgroup.map_id]; exact hI₁)
  set U := orbSup T I with hUdef
  have hIU' : I ∈ IrrPlusOn Y U T := by rw [hUdef, orbSup_eq_biSup_smul]; exact hI'
  have hIU : I ≤ U := le_orbSup T I
  have hIY : ∀ y ∈ Y, ∀ w ∈ I, y w ∈ I := fun y hy w hw => hIU'.1.2.1 ⟨y, hy⟩ w hw
  have hYs : Y ≤ stabSub U := le_stabSub_orbSup hTY hIY
  have hTs : T ≤ stabSub U :=
    le_stabSub_of_forall_mem fun t ht w hw => mem_orbSup_of_mem_map ht hw
  have hLs : L ≤ stabSub U := hLY.trans hYs
  have hLnot : ¬ L ≤ centSub U := by
    intro hLU
    have hYU : Y ≤ centSub U := conjClosure_le fun t ht l hl u hu => by
      have htu : t⁻¹ u ∈ U := (hTs (T.inv_mem ht) u).mpr hu
      show (t * l * t⁻¹) u = u
      simp only [MulAut.mul_apply]
      rw [hLU hl _ htu]
      simp
    have hfix : XMod.fixed ↥Y I = I :=
      le_antisymm (XMod.fixed_le I) fun w hw => ⟨hw, fun y => hYU y.2 w (hIU hw)⟩
    have hlt := hIU'.1.2.2.2.1
    rw [hfix] at hlt
    exact lt_irrefl _ hlt
  have hAU : commSub U A ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hLA
    have haU : a ∈ centSub U := fun u hu => hbot hu a haA
    have hLa : L.map (MulAut.conj a).toMonoidHom ∈ cComp X :=
      CFSG.Quasithin.map_conj_mem_cComp hL (hAX haA)
    have hLaq : CFSG.IsQuasisimple ↥(L.map (MulAut.conj a).toMonoidHom) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv ((MulAut.conj a).subgroupMap L) hLq
    have hdich : L.map (MulAut.conj a).toMonoidHom = L ∨
        ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
      rcases cComp_eq_or_commutator_eq_bot_of_isQuasisimple hLa hL hLaq hLq with h | h
      · exact Or.inl h
      · right
        rw [Subgroup.commutator_comm]
        exact h
    exact hLnot (le_centSub_of_conj hLq hLs haU haL hdich)
  have h27 : qhatOf (autSub (Y ⊔ T) U) ≤ (r : WithTop ℚ) :=
    qhatOf_autSub_le_of_mem_QhatStar' hW hr hA (hAT.trans le_sup_right) (hAT.trans hTs) hAU
  have hr2' : (r : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := WithTop.coe_le_coe.mpr hr2.le
  have hstd := d3Std_of_irrPlusOn hW hXq hT hL hLq hIU' hLnot (h27.trans hr2')
  have hSz' : ∃ n : ℕ, SuzukiModel (↥(autSub L U) ⧸ Subgroup.center ↥(autSub L U)) 2 n := by
    obtain ⟨n, hn⟩ := hSz
    have hrange : autSub L U = (resHomOn U hLs).range := autSub_eq_range_resHomOn hLs
    let ψ : ↥L →* ↥(autSub L U) :=
      (MulEquiv.subgroupCongr hrange.symm).toMonoidHom.comp (resHomOn U hLs).rangeRestrict
    have hψs : Function.Surjective ψ :=
      (MulEquiv.subgroupCongr hrange.symm).surjective.comp
        (resHomOn U hLs).rangeRestrict_surjective
    have hψ1 : ∃ l, ψ l ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hLnot
      intro l hl u hu
      have h1 := congrArg (fun f : ↥(autSub L U) => (((f : MulAut ↥U) ⟨u, hu⟩ : ↥U) : W))
        (hall ⟨l, hl⟩)
      exact h1
    have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq hψ1
    have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hLq hψs hker
    exact ⟨n, suzukiModel_of_mulEquiv e.symm hn⟩
  have htop : orbSup (autSub T U) (I.subgroupOf U) = ⊤ :=
    orbSup_autSub_subgroupOf_eq_top hIU hTs le_rfl
  have h2 := h38 _ _ _ _ _ _ hstd htop hSz'
  have hsup : autSub Y U ⊔ autSub T U = autSub (Y ⊔ T) U := by
    rw [autSub_eq_map_resHomOn le_sup_left (sup_le hYs hTs),
      autSub_eq_map_resHomOn le_sup_right (sup_le hYs hTs),
      autSub_eq_map_resHomOn le_rfl (sup_le hYs hTs), ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
  have hexpU : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hW])
  have hle : qhatOf (autSub (autSub Y U ⊔ autSub T U)
      (orbSup (autSub T U) (I.subgroupOf U))) ≤ (r : WithTop ℚ) := by
    rw [qhatOf_autSub_congr htop, hsup]
    exact qhatOf_autSub_top_le hexpU h27
  rw [h2] at hle
  exact absurd (WithTop.coe_le_coe.mp hle) (not_le.mpr hr2)

end Module

end CFSG.Quasithin.H13
