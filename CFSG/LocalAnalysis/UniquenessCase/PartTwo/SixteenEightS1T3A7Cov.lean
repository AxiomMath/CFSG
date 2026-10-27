module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCCover
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7K1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16t3_cover_of_simple_odd (hset : Setting16 D V₀ V L) (h127 : R127 D)
    (h119 : F11.R119 D)
    {Kb : Subgroup (MulAut (Vtil V₀ V hV))} (hKM : Kb ≤ Mbar D.M V₀ V hV)
    (hKN : (Kb.subgroupOf (Mbar D.M V₀ V hV)).Normal) (hKs : IsSimpleGroup ↥Kb)
    (hKnc : ¬ IsMulCommutative ↥Kb) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧ barSub V₀ V hV Y = Kb ∧
      Group.IsPerfect ↥Y ∧ CFSG.pCore 2 ↥Y ≤ (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y ∧
      ((Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ≤
        Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x ∈ Y ⊓ F11.CTilde D.M V₀ V, ∀ n : ℕ, x ^ p ^ n = 1 →
        (¬ p ^ 2 ∣ Nat.card ↥Kb → x = 1) ∧ (¬ p ^ 3 ∣ Nat.card ↥Kb → x ^ p = 1) := by
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
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
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
    h119 V₀ V (Hyp125.hyp11 h127 hset.hyp16.hyp125) X hCX hX_le hlayerim
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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOleN : CFSG.pCore 2 ↥Y ≤ N := by
    let R : Subgroup ↥Y := CFSG.pCore 2 ↥Y
    let f : ↥Y →* ↥Kb := eQ.toMonoidHom.comp (QuotientGroup.mk' N)
    have hfker : f.ker = N := by
      ext y
      rw [MonoidHom.mem_ker]
      constructor
      · intro hh
        have h1 : QuotientGroup.mk' N y = 1 := by
          apply eQ.injective
          simpa [f] using hh
        exact (QuotientGroup.eq_one_iff y).mp h1
      · intro hh
        have h1 : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff y).mpr hh
        show f y = 1
        rw [show f y = eQ (QuotientGroup.mk' N y) from rfl, h1, map_one]
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨w, hw⟩ := eQ.surjective z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N w
      exact ⟨y, hw⟩
    have hP2 : IsPGroup 2 ↥(R.map f) := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map f
    have hP2n : (R.map f).Normal :=
      Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := ↥Y)) f hf
    rcases CFSG.ASVolI.A129Aux.normal_eq_top_or_le_center hKq hP2n with htop | hcen
    · exfalso
      have h2X : IsPGroup 2 ↥Kb := by
        have htop' : IsPGroup 2 ↥(⊤ : Subgroup ↥Kb) := htop ▸ hP2
        exact htop'.of_equiv Subgroup.topEquiv
      haveI : Nontrivial (↥Kb ⧸ Subgroup.center ↥Kb) := hKq.2.toNontrivial
      haveI : Nontrivial ↥Kb := (QuotientGroup.mk'_surjective (Subgroup.center ↥Kb)).nontrivial
      haveI : Group.IsPerfect ↥Kb := ⟨hKq.1⟩
      exact Group.IsPerfect.not_isNilpotent ↥Kb h2X.isNilpotent
    · intro y hy
      have hmem : f y ∈ R.map f := Subgroup.mem_map_of_mem f hy
      have hcent : f y ∈ Subgroup.center ↥Kb := hcen hmem
      have h1 : orderOf (f y) = 1 := by
        obtain ⟨c, hc⟩ := hP2.exists_orderOf_eq_pow ⟨f y, hmem⟩
        have hord2 : orderOf (f y) = 2 ^ c := by
          rw [← Subgroup.orderOf_mk (f y) hmem]
          exact hc
        have hordZ : orderOf (f y) ∣ Nat.card (Subgroup.center ↥Kb) := by
          have := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥Kb) hcent
          simpa using this
        have hcop : Nat.Coprime (2 ^ c) (Nat.card (Subgroup.center ↥Kb)) :=
          hzK.coprime_two_left.pow_left c
        have hdvd2 : orderOf (f y) ∣ 2 ^ c := by rw [hord2]
        exact Nat.eq_one_of_dvd_coprimes hcop hdvd2 hordZ
      have h1' : f y = 1 := orderOf_eq_one_iff.mp h1
      rw [← hfker, MonoidHom.mem_ker]
      exact h1'
  have hNcent : N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ≤
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    haveI : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).Normal :=
      Subgroup.Normal.map (inferInstance : N.Normal) _ (QuotientGroup.mk'_surjective _)
    have hsolv : Group.IsSolvable ↥(N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) :=
      Group.isSolvable_of_surjective
        (f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).subgroupMap N)
        (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) N)
    exact close16_le_center_of_isSolvable hlayerY hsolv
  haveI : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal (p := 2) (G := ↥Y)
  have hO2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup (p := 2) (G := ↥Y)
  have hbounds : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ x ∈ Y ⊓ F11.CTilde D.M V₀ V, ∀ n : ℕ, x ^ p ^ n = 1 →
        (¬ p ^ 2 ∣ Nat.card ↥Kb → x = 1) ∧ (¬ p ^ 3 ∣ Nat.card ↥Kb → x ^ p = 1) := by
    intro p hp hp2 x hx n hxpow
    haveI : Fact p.Prime := Fact.mk hp
    have hxN : (⟨x, hx.1⟩ : ↥Y) ∈ N := by
      rw [hNker]
      exact Subgroup.mem_subgroupOf.mpr hx
    have hxpowY : (⟨x, hx.1⟩ : ↥Y) ^ p ^ n = 1 := Subtype.ext (by simpa using hxpow)
    have hres := s16t3_kernel_pElement hperfY.commutator_eq_top N (CFSG.pCore 2 ↥Y)
      hO2 hOleN hNcent hp2 hxN hxpowY
    have hcard : Nat.card (↥Y ⧸ N) = Nat.card ↥Kb := Nat.card_congr eQ.toEquiv
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    · have h2' : ¬ p ^ 2 ∣ Nat.card (↥Y ⧸ N) := by rw [hcard]; exact h2
      have hx1 : (⟨x, hx.1⟩ : ↥Y) = 1 := hres.1 h2'
      exact congrArg Subtype.val hx1
    · have h3' : ¬ p ^ 3 ∣ Nat.card (↥Y ⧸ N) := by rw [hcard]; exact h3
      have hx1 : (⟨x, hx.1⟩ : ↥Y) ^ p = 1 := hres.2 h3'
      exact congrArg Subtype.val hx1
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
  have hYsolv : Group.IsSolvable ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    let hle : Y ⊓ F11.CTilde D.M V₀ V ≤ Y := inf_le_left
    haveI : Group.IsSolvable ↥((Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y) := hNker ▸ hNsolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.injective
  exact ⟨Y, hY_le,
    s16t3_normal_of_cover_of_isSolvable (s15_Three_cTilde_normal hV hMs) hX_le hXnormal hCX
      hY.1 hY.2.2.2.1 hY.2.1 hXYC hYsolv hXC hXab,
    hbarY, hperfY, hNker ▸ hOleN, hNker ▸ hNcent, hbounds⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
