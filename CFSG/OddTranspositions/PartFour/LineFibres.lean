module

public import CFSG.Timmesfeld.Bridge.OddTranspLocal
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PartFour.LineTransport
public import CFSG.OddTranspositions.PartThree.Statements

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

theorem pCore_quotient_pCore_eq_bot (p : ℕ) (X : Type*) [Group X] :
    CFSG.pCore p (X ⧸ CFSG.pCore p X) = ⊥ := by
  let f : X →* X ⧸ CFSG.pCore p X := QuotientGroup.mk' (CFSG.pCore p X)
  let K : Subgroup (X ⧸ CFSG.pCore p X) := CFSG.pCore p (X ⧸ CFSG.pCore p X)
  have hker : IsPGroup p f.ker := by
    have h : f.ker = CFSG.pCore p X := QuotientGroup.ker_mk' (CFSG.pCore p X)
    rw [h]
    exact CFSG.pCore_isPGroup
  have hK : IsPGroup p (K.comap f) :=
    (CFSG.pCore_isPGroup (G := X ⧸ CFSG.pCore p X) (p := p)).comap_of_ker_isPGroup f hker
  have hKn : (K.comap f).Normal :=
    (CFSG.pCore_normal (G := X ⧸ CFSG.pCore p X) (p := p)).comap f
  have hle : K.comap f ≤ CFSG.pCore p X := le_sSup ⟨hKn, hK⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore p X) z
  exact (QuotientGroup.eq_one_iff x).mpr (hle (Subgroup.mem_comap.mpr hz))

theorem eq_one_of_mem_center_of_sq_eq_one {X : Type*} [Group X] [Finite X]
    {y : X ⧸ CFSG.pCore 2 X} (hy : y ∈ Subgroup.center (X ⧸ CFSG.pCore 2 X))
    (hy2 : y ^ 2 = 1) : y = 1 := by
  let P : Subgroup X := CFSG.pCore 2 X
  let Y : Subgroup (X ⧸ P) := Subgroup.zpowers y
  have hYZ : Y ≤ Subgroup.center (X ⧸ P) := Subgroup.zpowers_le.mpr hy
  have hYn : Y.Normal := Subgroup.normal_of_le_center hYZ
  have hYp : IsPGroup 2 Y := by
    have hcard : Nat.card Y = orderOf y := Nat.card_zpowers (a := y)
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (p := 2) (n := 0) (by rw [hcard, h1, pow_zero])
    · exact IsPGroup.of_card (p := 2) (n := 1) (by rw [hcard, h2, pow_one])
  have hle : Y ≤ CFSG.pCore 2 (X ⧸ P) := le_sSup ⟨hYn, hYp⟩
  have hbot : CFSG.pCore 2 (X ⧸ P) = ⊥ := pCore_quotient_pCore_eq_bot 2 X
  rw [hbot] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers y))

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isNormalSet_DstarH (hC : HypothesisC D) : IsNormalSet (DstarH hC) := by
  intro g x hx
  exact DstarH_conj_mem hC hx

theorem mul_inv_mem_pCore_of_inv_mul_mem (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {b c : Halpha D hC.alpha} (hb : b ∈ DstarH hC) (hc : c ∈ DstarH hC)
    (hbc : b⁻¹ * c ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    c * b⁻¹ ∈ CFSG.pCore 2 (Halpha D hC.alpha) := by
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  have hodd : IsOddTransp (DstarH hC) := DstarH_isOddTransp hC
  have hb2 : b ^ 2 = 1 := by
    rw [← hodd.1 b hb]
    exact pow_orderOf_eq_one b
  have hc2 : c ^ 2 = 1 := by
    rw [← hodd.1 c hc]
    exact pow_orderOf_eq_one c
  set y : H := b⁻¹ * c with hy
  have hyR : y ∈ CFSG.solvableRadical (Halpha D hC.alpha) := hbc
  have hycenter : QuotientGroup.mk' Q y ∈ Subgroup.center (H ⧸ Q) := by
    have hmem : QuotientGroup.mk' Q y ∈
        (CFSG.solvableRadical (Halpha D hC.alpha)).map (QuotientGroup.mk' Q) :=
      Subgroup.mem_map.mpr ⟨y, hyR, rfl⟩
    exact h113 (G := G) (D := D) hC hrad hn3 ▸ hmem
  have hcomm : Commute (QuotientGroup.mk' Q b) (QuotientGroup.mk' Q y) :=
    Subgroup.mem_center_iff.mp hycenter (QuotientGroup.mk' Q b)
  have hbq : (QuotientGroup.mk' Q b) ^ 2 = 1 := by
    rw [← map_pow, hb2, map_one]
  have hcy : (QuotientGroup.mk' Q c) ^ 2 = 1 := by
    rw [← map_pow, hc2, map_one]
  have hceq : c = b * y := by
    rw [hy]
    group
  have h1 : (QuotientGroup.mk' Q b * QuotientGroup.mk' Q y) ^ 2 = 1 := by
    rw [← map_mul, ← hceq, ← map_pow, hc2, map_one]
  have hy2 : (QuotientGroup.mk' Q y) ^ 2 = 1 := by
    calc (QuotientGroup.mk' Q y) ^ 2
        = (QuotientGroup.mk' Q b) ^ 2 * (QuotientGroup.mk' Q y) ^ 2 := by rw [hbq, one_mul]
      _ = (QuotientGroup.mk' Q b * QuotientGroup.mk' Q y) ^ 2 := (hcomm.mul_pow 2).symm
      _ = 1 := h1
  have hy1 : QuotientGroup.mk' Q y = 1 := eq_one_of_mem_center_of_sq_eq_one hycenter hy2
  have hyQ : y ∈ Q := (QuotientGroup.eq_one_iff y).mp hy1
  have hsplit : c * b⁻¹ = b * y * b⁻¹ := by
    rw [hceq]
  rw [hsplit]
  exact Subgroup.Normal.conj_mem (CFSG.pCore_normal (G := H) (p := 2)) y hyQ b

theorem exists_mem_DstarH_not_commute_mk (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {b : Halpha D hC.alpha} (hb : b ∈ DstarH hC) :
    ∃ w ∈ DstarH hC,
      ¬ Commute (QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) b)
        (QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) w) := by
  classical
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  by_contra hno
  push Not at hno
  have hcenter : QuotientGroup.mk' Q b ∈ Subgroup.center (H ⧸ Q) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective Q g
    have hle : Subgroup.closure (DstarH hC) ≤
        (Subgroup.centralizer ({QuotientGroup.mk' Q b} : Set (H ⧸ Q))).comap
          (QuotientGroup.mk' Q) := by
      rw [Subgroup.closure_le]
      intro s hs
      exact Subgroup.mem_comap.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (hno s hs).symm.eq)
    have hg' : g' ∈ Subgroup.closure (DstarH hC) := by
      rw [DstarH_closure_eq_top hC]
      exact Subgroup.mem_top g'
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp (hle hg'))
  have hmem : QuotientGroup.mk' Q b ∈
      (CFSG.solvableRadical (Halpha D hC.alpha)).map (QuotientGroup.mk' Q) :=
    h113 (G := G) (D := D) hC hrad hn3 ▸ hcenter
  obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp hmem
  have hbR : b ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    have hq : r⁻¹ * b ∈ Q := (QuotientGroup.eq_one_iff (r⁻¹ * b)).mp
      (show QuotientGroup.mk' Q (r⁻¹ * b) = 1 by rw [map_mul, map_inv, hr, inv_mul_cancel])
    have hmemR : r * (r⁻¹ * b) ∈ CFSG.solvableRadical (Halpha D hC.alpha) :=
      (CFSG.solvableRadical (Halpha D hC.alpha)).mul_mem hrR
        ((CFSG.pCore_le_solvableRadical 2 H) hq)
    rwa [mul_inv_cancel_left] at hmemR
  have hb1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b = 1 :=
    (QuotientGroup.eq_one_iff b).mpr hbR
  have hord := imageClass_involutions hC hHns _
    (show QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈ imageClass hC
      from ⟨b, hb, rfl⟩)
  rw [hb1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem exists_pCore_conj_eq_of_inv_mul_mem (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {b c : Halpha D hC.alpha} (hb : b ∈ DstarH hC) (hc : c ∈ DstarH hC)
    (hbc : b⁻¹ * c ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    ∃ x ∈ CFSG.pCore 2 (Halpha D hC.alpha), x * b * x⁻¹ = c := by
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  obtain ⟨w, hw, hbw⟩ := exists_mem_DstarH_not_commute_mk h113 hC hrad hn3 hHns hb
  have hbcQ : c * b⁻¹ ∈ Q := mul_inv_mem_pCore_of_inv_mul_mem h113 hC hrad hn3 hb hc hbc
  have hcbw : ¬ Commute c w := by
    intro hcw
    apply hbw
    have hcbeq : QuotientGroup.mk' Q c = QuotientGroup.mk' Q b := by
      have h1 : QuotientGroup.mk' Q (c * b⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff (c * b⁻¹)).mpr hbcQ
      rw [map_mul, map_inv] at h1
      calc QuotientGroup.mk' Q c
          = QuotientGroup.mk' Q c * (QuotientGroup.mk' Q b)⁻¹ * QuotientGroup.mk' Q b := by
            group
        _ = 1 * QuotientGroup.mk' Q b := by rw [h1]
        _ = QuotientGroup.mk' Q b := one_mul _
    rw [← hcbeq]
    exact hcw.map (QuotientGroup.mk' Q)
  have hbw' : ¬ Commute b w := fun h => hbw (h.map (QuotientGroup.mk' Q))
  obtain ⟨x, hx, hxe⟩ :=
    CFSG.Timmesfeld.Bridge.OddTransp.exists_conj_of_mul_inv_mem
      (G := H) (D := DstarH hC) (Q := Q)
      (DstarH_isOddTransp hC) (isNormalSet_DstarH hC)
      (CFSG.pCore_isPGroup (G := H) (p := 2))
      hb hw hbw' hc hbcQ hcbw
  exact ⟨x, (Subgroup.commutator_le_left Q (Subgroup.zpowers w)) hx, hxe⟩

theorem exists_pCore_conj_eq_of_inv_mul_mem_Malpha (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {b c : G} (hb : b ∈ DalphaStar D hC.alpha) (hc : c ∈ DalphaStar D hC.alpha)
    (hbc : b⁻¹ * c ∈ Malpha D hC.alpha) :
    ∃ x ∈ CFSG.pCore 2 (Halpha D hC.alpha), (x : G) * b * (x : G)⁻¹ = c := by
  let H := Halpha D hC.alpha
  let bH : H := ⟨b, Subgroup.subset_closure hb⟩
  let cH : H := ⟨c, Subgroup.subset_closure hc⟩
  have hbcm : bH⁻¹ * cH ∈ CFSG.solvableRadical H := by
    obtain ⟨r, hrR, hre⟩ := Subgroup.mem_map.mp hbc
    have heq : bH⁻¹ * cH = r := by
      apply Subtype.ext
      show (b : G)⁻¹ * c = (r : G)
      exact hre.symm
    rw [heq]
    exact hrR
  obtain ⟨x, hx, hxe⟩ :=
    exists_pCore_conj_eq_of_inv_mul_mem h113 hC hrad hn3 hHns
      (b := bH) (c := cH) hb hc hbcm
  refine ⟨x, hx, ?_⟩
  simpa [bH, cH] using congrArg Subtype.val hxe

theorem exists_mem_pCore_cimg_eq (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {γ : Set G} (hγ : γ ∈ Dalpha D hC.alpha) {x : G} (hx : x ∈ Malpha D hC.alpha) :
    ∃ y ∈ CFSG.pCore 2 (Halpha D hC.alpha), cimg (y : G) γ = cimg x γ := by
  classical
  let H := Halpha D hC.alpha
  obtain ⟨xH, hxR, hxval⟩ := Subgroup.mem_map.mp hx
  have hxH : x ∈ Halpha D hC.alpha := by
    rw [← hxval]
    exact xH.2
  let xH' : H := ⟨x, hxH⟩
  have hxR' : xH' ∈ CFSG.solvableRadical H := by
    have heq : xH' = xH := Subtype.ext (by
      show x = (xH : G)
      exact hxval.symm)
    rw [heq]
    exact hxR
  obtain ⟨c, hcγ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
  have hcStar : c ∈ DalphaStar D hC.alpha := ⟨γ, hγ, hcγ⟩
  let cH : H := ⟨c, Subgroup.subset_closure hcStar⟩
  have hnorm : x ∈ Subgroup.normalizer (DalphaStar D hC.alpha) :=
    Halpha_le_normalizer hC.setup.normal xH'.2
  have hxcStar : x * c * x⁻¹ ∈ DalphaStar D hC.alpha := (hnorm c).mp hcStar
  have hmemR : cH⁻¹ * (xH' * cH * xH'⁻¹) ∈ CFSG.solvableRadical H := by
    have h1 : cH⁻¹ * xH' * cH ∈ CFSG.solvableRadical H := by
      simpa using (inferInstance : (CFSG.solvableRadical H).Normal).conj_mem xH' hxR' cH⁻¹
    have h2 : xH'⁻¹ ∈ CFSG.solvableRadical H := (CFSG.solvableRadical H).inv_mem hxR'
    have h3 : cH⁻¹ * xH' * cH * xH'⁻¹ ∈ CFSG.solvableRadical H :=
      (CFSG.solvableRadical H).mul_mem h1 h2
    simpa [mul_assoc] using h3
  have hcc' : c⁻¹ * (x * c * x⁻¹) ∈ Malpha D hC.alpha := by
    refine Subgroup.mem_map.mpr ⟨cH⁻¹ * (xH' * cH * xH'⁻¹), hmemR, ?_⟩
    rfl
  obtain ⟨y, hyQ, hye⟩ :=
    exists_pCore_conj_eq_of_inv_mul_mem_Malpha h113 hC hrad hn3 hHns hcStar hxcStar hcc'
  refine ⟨y, hyQ, ?_⟩
  have hclass1 : cimg (y : G) γ ∈ blockClass hC.alpha := cimg_mem_blockClass_iff.mpr hγ.1
  have hclass2 : cimg x γ ∈ blockClass hC.alpha := cimg_mem_blockClass_iff.mpr hγ.1
  have hmeet : (cimg (y : G) γ ∩ cimg x γ).Nonempty := by
    refine ⟨x * c * x⁻¹, ?_, ⟨c, hcγ, rfl⟩⟩
    rw [← hye]
    exact ⟨c, hcγ, rfl⟩
  exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hclass1 hclass2 hmeet

theorem eq_of_mem_of_inv_mul_mem_Malpha (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {γ : Set G} (hγ : γ ∈ Dalpha D hC.alpha) {c c' : G} (hc : c ∈ γ) (hc' : c' ∈ γ)
    (hcc' : c⁻¹ * c' ∈ Malpha D hC.alpha) : c = c' := by
  obtain ⟨x, hxQ, hxe⟩ :=
    exists_pCore_conj_eq_of_inv_mul_mem_Malpha h113 hC hrad hn3 hHns
      (b := c) (c := c') ⟨γ, hγ, hc⟩ ⟨γ, hγ, hc'⟩ hcc'
  have hmem : (x : G) * c * (x : G)⁻¹ ∈ γ := by
    rw [hxe]
    exact hc'
  have hfix := h89 (G := G) (D := D) hC hrad hW γ hγ c hc x hxQ hmem
  rw [hxe] at hfix
  exact hfix.symm

theorem conj_mem_Malpha_of_mem_normalizer (hN : IsNormalSet D) {α : Set G} {g x : G}
    (hg : g ∈ Subgroup.normalizer α) (hx : x ∈ Malpha D α) :
    g * x * g⁻¹ ∈ Malpha D α := by
  have h := Malpha_cimg hN g α
  rw [cimg_eq_self_of_mem_normalizer hg] at h
  rw [h]
  exact Subgroup.mem_map.mpr ⟨x, hx, by
    show (MulAut.conj g) x = g * x * g⁻¹
    rw [MulAut.conj_apply]⟩

theorem cimg_cimg_conj (g x : G) (S : Set G) :
    cimg g (cimg x S) = cimg (g * x * g⁻¹) (cimg g S) := by
  rw [← cimg_mul, ← cimg_mul]
  congr 1
  group

theorem ncard_orbit_Malpha_eq (hC : HypothesisC D) {β δ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hδ : δ ∈ Dalpha D hC.alpha) :
    ((fun x => cimg x δ) '' (Malpha D hC.alpha : Set G)).ncard =
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
  obtain ⟨g, hg, hgβ⟩ := hC.normalizer_transitive β hβ δ hδ
  have hg' : g⁻¹ ∈ Subgroup.normalizer hC.alpha := Subgroup.inv_mem _ hg
  have heq : (fun x => cimg x δ) '' (Malpha D hC.alpha : Set G) =
      (cimg g) '' ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)) := by
    rw [← hgβ, Set.image_image]
    ext S
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · simpa using conj_mem_Malpha_of_mem_normalizer hC.setup.normal hg' hx
      · show cimg g (cimg (g⁻¹ * x * g) β) = cimg x (cimg g β)
        rw [cimg_cimg_conj]
        congr 1
        group
    · rintro ⟨x, hx, rfl⟩
      refine ⟨g * x * g⁻¹, conj_mem_Malpha_of_mem_normalizer hC.setup.normal hg hx, ?_⟩
      show cimg (g * x * g⁻¹) (cimg g β) = cimg g (cimg x β)
      exact (cimg_cimg_conj g x β).symm
  rw [heq]
  exact Set.ncard_image_of_injective _ (cimg_injective g)

end CFSG.OddTranspositions.PartFour
