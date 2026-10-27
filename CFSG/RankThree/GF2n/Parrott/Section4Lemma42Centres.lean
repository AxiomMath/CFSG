module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Sylow
public import CFSG.RankThree.GF2n.Parrott.OddLiftCentralizer
public import CFSG.RankThree.GF2n.Parrott.ExtraspecialJ
public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardSigma
public import CFSG.RankThree.GF2n.Parrott.Section4FixDimBridge
public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem inf_centralizer_le_isSylowOf (h : Tim79a.ParrottHyp z) {σ : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({σ} : Set G))) :
    J z ⊓ centralizer ({σ} : Set G) ≤ T := by
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  refine le_isSylowOf_of_isPGroup_of_le_normalizer hT
    (fun j hj => mem_inf.mpr ⟨J_le_H hj.1, hj.2⟩) ?_ (isPGroup_J h).to_inf_left
  have key : ∀ c ∈ H z ⊓ centralizer ({σ} : Set G), ∀ j ∈ J z ⊓ centralizer ({σ} : Set G),
      c * j * c⁻¹ ∈ J z ⊓ centralizer ({σ} : Set G) := by
    intro c hc j hj
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hc.1) j).mp hj.1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hcσ : Commute c σ := mem_centralizer_singleton_iff.mp hc.2
    have hjσ : Commute j σ := mem_centralizer_singleton_iff.mp hj.2
    exact ((hcσ.mul_left hjσ).mul_left hcσ.inv_left).eq
  intro c hc
  rw [mem_normalizer_iff]
  intro j
  refine ⟨key c hc j, fun hj => ?_⟩
  have h1 := key c⁻¹ (inv_mem hc) _ hj
  simpa [mul_assoc] using h1

theorem mem_centerIn_J_of_commutes (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {s : G} (hsH : s ∈ H z) (hs3 : orderOf s = 3)
    {w : G} (hwJ : w ∈ J z) (hws : s * w * s⁻¹ = w)
    (hwC : ∀ c ∈ J z, s * c * s⁻¹ = c → c * w = w * c) : w ∈ centerIn (J z) := by
  have hs3' : s * s * s = 1 := by
    have h1 := pow_orderOf_eq_one s
    rw [hs3] at h1
    simpa [pow_succ, mul_assoc] using h1
  have hcent : ∀ e ∈ centerIn (J z), ∀ g ∈ H z, g * e = e * g := fun e he g hg =>
    mem_centralizer_iff.mp ((hZ ▸ he : e ∈ centerIn (H z))).2 g hg
  have hconjJ : ∀ x ∈ J z, s * x * s⁻¹ ∈ J z := fun x hx => H_conj_mem_J ⟨s, hsH⟩ hx
  refine Subgroup.mem_inf.mpr ⟨hwJ, mem_centralizer_iff.mpr fun j hj => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : G, u = s * j * s⁻¹ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : G, v = s * u * s⁻¹ := ⟨_, rfl⟩
  have huJ : u ∈ J z := hu ▸ hconjJ j hj
  have hvJ : v ∈ J z := hv ▸ hconjJ u huJ
  obtain ⟨n, hn⟩ : ∃ n : G, n = j * u * v := ⟨_, rfl⟩
  have hnJ : n ∈ J z := hn ▸ (J z).mul_mem ((J z).mul_mem hj huJ) hvJ
  have hsv : s * v * s⁻¹ = j := by
    have : s * v * s⁻¹ = (s * s * s) * j * (s * s * s)⁻¹ := by rw [hv, hu]; group
    rw [this, hs3']
    group
  have hsn : s * n * s⁻¹ = u * v * j := by
    rw [hn]
    calc s * (j * u * v) * s⁻¹ = (s * j * s⁻¹) * (s * u * s⁻¹) * (s * v * s⁻¹) := by group
      _ = u * v * j := by rw [← hu, ← hv, hsv]
  have hcoset : n⁻¹ * (s * n * s⁻¹) ∈ centerIn (J z) := by
    rw [hsn, hn]
    have hb : u * v ∈ J z := (J z).mul_mem huJ hvJ
    have := commutator_mem_centerIn_J h ((J z).inv_mem hb) ((J z).inv_mem hj)
    have e : (j * u * v)⁻¹ * (u * v * j) = ⁅(u * v)⁻¹, j⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact this
  have hN : ∀ x ∈ centerIn (J z), s * x * s⁻¹ ∈ centerIn (J z) := fun x hx => by
    have : s * x * s⁻¹ = x := by
      have := hcent x hx s hsH
      calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [this]
        _ = x := by group
    rw [this]
    exact hx
  have hcop : Nat.Coprime (orderOf s) (Nat.card (centerIn (J z))) := by
    rw [hs3, card_centerIn_J h]
    norm_num
  obtain ⟨e, heZ, hfix⟩ := exists_fixed_mem_coset_of_coprime (centerIn (J z)) hN hcoset hcop
  have hneJ : n * e ∈ J z := (J z).mul_mem hnJ heZ.1
  have hcw := hwC (n * e) hneJ hfix
  have hew : w * e = e * w := mem_centralizer_iff.mp heZ.2 w hwJ
  have hnw : n * w = w * n := by
    have h1 : n * w * e = w * n * e := by
      calc n * w * e = n * (w * e) := by rw [mul_assoc]
        _ = n * (e * w) := by rw [hew]
        _ = n * e * w := by rw [mul_assoc]
        _ = w * (n * e) := hcw
        _ = w * n * e := by rw [mul_assoc]
    exact mul_right_cancel h1
  obtain ⟨κ, hκ⟩ : ∃ κ : G, κ = w * j * w⁻¹ * j⁻¹ := ⟨_, rfl⟩
  have hκZ : κ ∈ centerIn (J z) := hκ ▸ commutator_mem_centerIn_J h hwJ hj
  have hκH : ∀ g ∈ H z, g * κ = κ * g := fun g hg => (hcent κ hκZ g hg)
  have hκs : s * κ * s⁻¹ = κ := by
    have := hκH s hsH
    calc s * κ * s⁻¹ = (κ * s) * s⁻¹ := by rw [this]
      _ = κ := by group
  have hwj : w * j * w⁻¹ = κ * j := by rw [hκ]; group
  have hconjκ : ∀ x : G, w * x * w⁻¹ = κ * x → w * (s * x * s⁻¹) * w⁻¹ = κ * (s * x * s⁻¹) := by
    intro x hx
    have h1 : w * (s * x * s⁻¹) * w⁻¹ = s * (w * x * w⁻¹) * s⁻¹ := by
      calc w * (s * x * s⁻¹) * w⁻¹ = (s * w * s⁻¹) * (s * x * s⁻¹) * (s * w * s⁻¹)⁻¹ := by
            rw [hws]
        _ = s * (w * x * w⁻¹) * s⁻¹ := by group
    rw [h1, hx]
    calc s * (κ * x) * s⁻¹ = (s * κ * s⁻¹) * (s * x * s⁻¹) := by group
      _ = κ * (s * x * s⁻¹) := by rw [hκs]
  have hwu : w * u * w⁻¹ = κ * u := by rw [hu]; exact hconjκ j hwj
  have hwv : w * v * w⁻¹ = κ * v := by rw [hv]; exact hconjκ u hwu
  have hwn : w * n * w⁻¹ = κ * κ * κ * n := by
    rw [hn]
    calc w * (j * u * v) * w⁻¹ = (w * j * w⁻¹) * (w * u * w⁻¹) * (w * v * w⁻¹) := by group
      _ = (κ * j) * (κ * u) * (κ * v) := by rw [hwj, hwu, hwv]
      _ = κ * κ * κ * (j * u * v) := by
          have hκj := hκH j (J_le_H hj)
          have hκu := hκH u (J_le_H huJ)
          calc (κ * j) * (κ * u) * (κ * v) = κ * (j * κ) * u * (κ * v) := by group
            _ = κ * (κ * j) * u * (κ * v) := by rw [← hκj]
            _ = κ * κ * (j * u) * (κ * v) := by group
            _ = κ * κ * (j * u * κ) * v := by group
            _ = κ * κ * (κ * (j * u)) * v := by
                rw [← hκH (j * u) (H z |>.mul_mem (J_le_H hj) (J_le_H huJ))]
            _ = κ * κ * κ * (j * u * v) := by group
  have hnn : w * n * w⁻¹ = n := by
    calc w * n * w⁻¹ = (n * w) * w⁻¹ := by rw [← hnw]
      _ = n := by group
  have hκ3 : κ * κ * κ = 1 := by
    have h1 : κ * κ * κ * n = n := by rw [← hwn, hnn]
    have : κ * κ * κ * n = 1 * n := by rw [h1, one_mul]
    exact mul_right_cancel this
  have hκ2 : κ * κ = 1 := centerIn_J_sq h hκZ
  have hκ1 : κ = 1 := by
    have : κ = κ * κ * κ * (κ * κ)⁻¹ := by group
    rw [this, hκ3, hκ2]
    group
  have : w * j * w⁻¹ * j⁻¹ = 1 := hκ ▸ hκ1
  calc j * w = (w * j * w⁻¹ * j⁻¹)⁻¹ * (w * j) := by group
    _ = w * j := by rw [this]; group

theorem mem_centerIn_J_of_mem_centre_sylow (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {σ : ↥(H z)} (hσ : orderOf σ = 3) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(σ : G)} : Set G))) {w : G}
    (hw : w ∈ T ⊓ centralizer (T : Set G)) (hwJ : w ∈ J z) : w ∈ centerIn (J z) := by
  obtain ⟨hwT, hwc⟩ := mem_inf.mp hw
  have hwσ : (σ : G) * w * (σ : G)⁻¹ = w := by
    have h1 : w * (σ : G) = (σ : G) * w := mem_centralizer_singleton_iff.mp (hT.le hwT).2
    calc (σ : G) * w * (σ : G)⁻¹ = (w * (σ : G)) * (σ : G)⁻¹ := by rw [h1]
      _ = w := by group
  refine mem_centerIn_J_of_commutes h hZ σ.2 (by rwa [Subgroup.orderOf_coe]) hwJ hwσ ?_
  intro c hc hcσ
  have hcσ' : c * (σ : G) = (σ : G) * c := (mul_inv_eq_iff_eq_mul.mp hcσ).symm
  have hcT : c ∈ T := inf_centralizer_le_isSylowOf h hT
    (mem_inf.mpr ⟨hc, mem_centralizer_singleton_iff.mpr hcσ'⟩)
  exact mem_centralizer_iff.mp hwc c hcT

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

omit hN in
theorem conjV_eq_of_mem_centre_sylow (h : Tim79a.ParrottHyp z)
    {σ : ↥(H z)} (hσ : orderOf σ = 3) (hZ : centerIn (J z) = centerIn (H z)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(σ : G)} : Set G))) {w : G}
    (hw : w ∈ T ⊓ centralizer (T : Set G)) (hwH : w ∈ H z) {v : QuotientV.V z}
    (hv : conjV h σ v = v) : conjV h ⟨w, hwH⟩ v = v := by
  obtain ⟨c₁, rfl⟩ := QuotientV.pi_surjective z v
  rw [conjV_mk] at hv
  have hcent : ∀ e ∈ centerIn (J z), ∀ g ∈ H z, g * e = e * g := fun e he g hg =>
    mem_centralizer_iff.mp ((hZ ▸ he : e ∈ centerIn (H z))).2 g hg
  have h1 : QuotientV.pi z ((c₁)⁻¹ * conjJ' z σ c₁) = 1 := by
    rw [map_mul, map_inv, hv, inv_mul_cancel]
  have hcoset : (c₁ : G)⁻¹ * ((σ : G) * (c₁ : G) * (σ : G)⁻¹) ∈ centerIn (J z) := by
    have h2 := (pi_eq_one_iff_mem_centerIn (z := z) (x := ((c₁)⁻¹ * conjJ' z σ c₁ : J z))
      ((c₁)⁻¹ * conjJ' z σ c₁).2).mp h1
    simpa [conjJ'_apply_coe] using h2
  have hN' : ∀ x ∈ centerIn (J z), (σ : G) * x * (σ : G)⁻¹ ∈ centerIn (J z) := fun x hx => by
    have : (σ : G) * x * (σ : G)⁻¹ = x := by
      have := hcent x hx σ σ.2
      calc (σ : G) * x * (σ : G)⁻¹ = (x * (σ : G)) * (σ : G)⁻¹ := by rw [this]
        _ = x := by group
    rw [this]
    exact hx
  have hcop : Nat.Coprime (orderOf (σ : G)) (Nat.card (centerIn (J z))) := by
    rw [Subgroup.orderOf_coe, hσ, card_centerIn_J h]
    norm_num
  obtain ⟨e, heZ, hfix⟩ := exists_fixed_mem_coset_of_coprime (centerIn (J z)) hN' hcoset hcop
  have hcJ : (c₁ : G) * e ∈ J z := (J z).mul_mem c₁.2 heZ.1
  have hcσ : (c₁ : G) * e * (σ : G) = (σ : G) * ((c₁ : G) * e) :=
    (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hcT : (c₁ : G) * e ∈ T := inf_centralizer_le_isSylowOf h hT
    (mem_inf.mpr ⟨hcJ, mem_centralizer_singleton_iff.mpr hcσ⟩)
  have hcw : (c₁ : G) * e * w = w * ((c₁ : G) * e) :=
    mem_centralizer_iff.mp (mem_inf.mp hw).2 _ hcT
  have hpi : QuotientV.pi z c₁ = QuotientV.pi z ⟨(c₁ : G) * e, hcJ⟩ := by
    have : QuotientV.pi z (⟨e, heZ.1⟩ : J z) = 1 := (pi_eq_one_iff_mem_centerIn heZ.1).mpr heZ
    have h3 : (⟨(c₁ : G) * e, hcJ⟩ : J z) = c₁ * ⟨e, heZ.1⟩ := rfl
    rw [h3, map_mul, this, mul_one]
  rw [hpi, conjV_mk]
  congr 1
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  calc w * ((c₁ : G) * e) * w⁻¹ = ((c₁ : G) * e * w) * w⁻¹ := by rw [hcw]
    _ = (c₁ : G) * e := by group

theorem card_centre_le_four_mul_card_map (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {σ : ↥(H z)} (hσ : orderOf σ = 3) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(σ : G)} : Set G))) :
    Nat.card ↥(T ⊓ centralizer (T : Set G)) ≤
      4 * Nat.card ↥(((T ⊓ centralizer (T : Set G)).subgroupOf (H z)).map (qH D)) := by
  set Z : Subgroup G := T ⊓ centralizer (T : Set G) with hZdef
  have hZH : Z ≤ H z := inf_le_left.trans (hT.le.trans inf_le_left)
  let f : ↥(Z.subgroupOf (H z)) →* QA45.originalSubgroup :=
    (qH D).comp (Z.subgroupOf (H z)).subtype
  have hmem : ∀ x : f.ker, (((x : ↥(Z.subgroupOf (H z))) : ↥(H z)) : G) ∈ centerIn (J z) := by
    intro x
    have hx1 : (((x : ↥(Z.subgroupOf (H z))) : ↥(H z)) : G) ∈ Z :=
      (x : ↥(Z.subgroupOf (H z))).2
    have hx2 : qH D ((x : ↥(Z.subgroupOf (H z))) : ↥(H z)) = 1 := x.2
    have hxJ : (((x : ↥(Z.subgroupOf (H z))) : ↥(H z)) : G) ∈ J z :=
      (J_mem_iff D _).mpr hx2
    exact mem_centerIn_J_of_mem_centre_sylow h hZ hσ hT hx1 hxJ
  have hker : Nat.card f.ker ≤ 4 := by
    let φ : f.ker → ↥(centerIn (J z)) := fun x =>
      ⟨(((x : ↥(Z.subgroupOf (H z))) : ↥(H z)) : G), hmem x⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    have := Nat.card_le_card_of_injective φ hφ
    rwa [card_centerIn_J h] at this
  have hrange : f.range = (Z.subgroupOf (H z)).map (qH D) := by
    ext a
    simp [f, MonoidHom.mem_range, Subgroup.mem_map]
  have hcard := Subgroup.card_ker_mul_card_range f
  have hZcard : Nat.card ↥(Z.subgroupOf (H z)) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
  rw [← hZcard, ← hcard, hrange]
  exact Nat.mul_le_mul_right _ hker

section ImageSylow

omit [Finite G] hN in
private theorem inf_centralizer_eq_map_centralizer' (y : H z) :
    H z ⊓ Subgroup.centralizer ({(y : G)} : Set G) =
      (Subgroup.centralizer ({y} : Set ↥(H z))).map (H z).subtype := by
  ext g
  constructor
  · rintro ⟨hgH, hgC⟩
    refine Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    simpa using Subgroup.mem_centralizer_singleton_iff.mp hgC
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hh))⟩

omit [Finite G] hN in
private theorem isSylowOf_map_hom' {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ}
    [Fact p.Prime]
    {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowOf_map_qH_centralizer {σ : ↥(H z)} (hσ : orderOf σ = 3) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(σ : G)} : Set G))) :
    IsSylowOf 2 ((T.subgroupOf (H z)).map (qH D))
      (centralizer ({qH D σ} : Set QA45.originalSubgroup)) := by
  have hTH : T ≤ H z := hT.le.trans inf_le_left
  have h1 : IsSylowOf 2 (T.subgroupOf (H z)) (centralizer ({σ} : Set ↥(H z))) := by
    rw [← isSylowOf_map_subtype_iff (H z), Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH,
      ← inf_centralizer_eq_map_centralizer']
    exact hT
  have h2 := isSylowOf_map_hom' h1 (qH D)
  have h3 : (centralizer ({σ} : Set ↥(H z))).map (qH D) =
      centralizer ({qH D σ} : Set QA45.originalSubgroup) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' := mem_centralizer_singleton_iff.mp hx
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx']
    · intro g hg
      obtain ⟨s, hs, hsσ⟩ := exists_lift_centralizer D hσ (mem_centralizer_singleton_iff.mp hg)
      exact ⟨s, mem_centralizer_singleton_iff.mpr hsσ, hs⟩
  rwa [h3] at h2

end ImageSylow

section ImageCentre

theorem card_map_centre_le_two {σ : ↥(H z)} (hσ : orderOf σ = 3) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(σ : G)} : Set G)))
    {S : Subgroup QA45.originalSubgroup}
    (hS : IsSylowOf 2 S (centralizer ({qH D σ} : Set QA45.originalSubgroup)))
    {e : QA45.originalSubgroup} (hSZ : ∀ x ∈ S, (∀ s ∈ S, s * x = x * s) → x = 1 ∨ x = e) :
    Nat.card ↥(((T ⊓ centralizer (T : Set G)).subgroupOf (H z)).map (qH D)) ≤ 2 := by
  have hTbar := isSylowOf_map_qH_centralizer D hσ hT
  obtain ⟨k, hk, hkx⟩ := hS.exists_mem_conj hTbar
  have hsub : ((((T ⊓ centralizer (T : Set G)).subgroupOf (H z)).map (qH D) :
      Subgroup QA45.originalSubgroup) : Set QA45.originalSubgroup) ⊆
      ({1, k * e * k⁻¹} : Set QA45.originalSubgroup) := by
    intro a ha
    obtain ⟨w', hw', rfl⟩ := ha
    have hwZ : (w' : G) ∈ T ⊓ centralizer (T : Set G) := hw'
    obtain ⟨hwT, hwC⟩ := mem_inf.mp hwZ
    have hmemT : qH D w' ∈ (T.subgroupOf (H z)).map (qH D) := ⟨w', hwT, rfl⟩
    have h1 : k⁻¹ * qH D w' * k ∈ S := (hkx _).mp hmemT
    have h2 : ∀ s ∈ S, s * (k⁻¹ * qH D w' * k) = (k⁻¹ * qH D w' * k) * s := by
      intro s hs
      have hks : k * s * k⁻¹ ∈ (T.subgroupOf (H z)).map (qH D) := by
        rw [hkx]
        have : k⁻¹ * (k * s * k⁻¹) * k = s := by group
        rw [this]
        exact hs
      obtain ⟨t', ht', ht'e⟩ := hks
      have hcomm : (t' : G) * (w' : G) = (w' : G) * (t' : G) :=
        mem_centralizer_iff.mp hwC (t' : G) ht'
      have hcomm' : t' * w' = w' * t' := Subtype.ext hcomm
      have hq : (k * s * k⁻¹) * qH D w' = qH D w' * (k * s * k⁻¹) := by
        rw [← ht'e, ← map_mul, ← map_mul, hcomm']
      calc s * (k⁻¹ * qH D w' * k) = k⁻¹ * ((k * s * k⁻¹) * qH D w') * k := by group
        _ = k⁻¹ * (qH D w' * (k * s * k⁻¹)) * k := by rw [hq]
        _ = (k⁻¹ * qH D w' * k) * s := by group
    rcases hSZ _ h1 h2 with h3 | h3
    · left
      have : qH D w' = k * (k⁻¹ * qH D w' * k) * k⁻¹ := by group
      rw [this, h3]
      group
    · right
      have : qH D w' = k * (k⁻¹ * qH D w' * k) * k⁻¹ := by group
      rw [this, h3]
      rfl
  calc Nat.card ↥(((T ⊓ centralizer (T : Set G)).subgroupOf (H z)).map (qH D))
      = Set.ncard ((((T ⊓ centralizer (T : Set G)).subgroupOf (H z)).map (qH D) :
        Subgroup QA45.originalSubgroup) : Set QA45.originalSubgroup) :=
        Nat.card_coe_set_eq _
    _ ≤ Set.ncard ({1, k * e * k⁻¹} : Set QA45.originalSubgroup) :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        simp

end ImageCentre

section Final


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

omit
  hN in
private theorem factorization_two_pow_mul_odd {k m : ℕ} (hm0 : m ≠ 0) (hm : ¬ 2 ∣ m) :
    Nat.factorization (2 ^ k * m) 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k (by norm_num)) hm0]
  change (Nat.factorization (2 ^ k) + Nat.factorization m) 2 = k
  rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

omit hN in
theorem isSylowOf_d8_centralizer_sigma1_mul :
    IsSylowOf 2 (Subgroup.closure ({tA, uA, vA * bA} : Set A45))
      (centralizer ({s1A * s2A} : Set A45)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hle3, hcard3, -, -⟩ := qa45_sigma_centralizer_sylow
  have hcentcard : Nat.card (centralizer ({s1A * s2A} : Set A45)) = 216 := by
    have hm : sigma1 * sigma2 ∈ QA45.originalSubgroup :=
      QA45.originalSubgroup.mul_mem sigma1_mem_A sigma2_mem_A
    exact (card_centralizer_QA45_eq_filter (sigma1 * sigma2) hm).trans
      Certificates.certificate946005.centralizer_sigma1sigma2
  refine isSylowOf_of_card hle3 ?_
  rw [hcard3, hcentcard]
  have h216 : (216 : ℕ) = 2 ^ 3 * 27 := by norm_num
  rw [h216, factorization_two_pow_mul_odd (by norm_num) (by norm_num)]
  norm_num

omit hN in
theorem isSylowOf_q8_centralizer_sigma1 :
    IsSylowOf 2 (Subgroup.closure ({a2A, b2A} : Set A45)) (centralizer ({s1A} : Set A45)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hSle, hScard, -⟩, -, -⟩ := qa45_sigma_centralizer_sylow
  refine isSylowOf_of_card hSle ?_
  rw [hScard, card_centralizer_sigma1_QA45]
  have h648 : (648 : ℕ) = 2 ^ 3 * 81 := by norm_num
  rw [h648, factorization_two_pow_mul_odd (by norm_num) (by norm_num)]
  norm_num


omit
  hN in
theorem four_dvd_card_centre (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    {σ : G} (hσH : σ ∈ H z) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({σ} : Set G))) :
    4 ∣ Nat.card ↥(T ⊓ centralizer (T : Set G)) := by
  have hZW := centerIn_J_le_inf_centralizer_of_isSylowOf h hZ
    (centerIn_J_le_centralizer_of_mem_H hZ hσH) hT
  have := Subgroup.card_dvd_of_le hZW
  rwa [card_centerIn_J h] at this

theorem card_centre_sylow_sigma1 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card ↥(T ⊓ centralizer (T : Set G)) = 4 ∨
      Nat.card ↥(T ⊓ centralizer (T : Set G)) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, -, ⟨e⟩⟩, -, -⟩ := qa45_sigma_centralizer_sylow
  have hS : IsSylowOf 2 (Subgroup.closure ({a2A, b2A} : Set A45))
      (centralizer ({qH D (sigma1Nine (z := z) D)} : Set A45)) := by
    rw [qH_sigma1Nine]
    exact isSylowOf_q8_centralizer_sigma1
  have hSZ : ∀ x ∈ Subgroup.closure ({a2A, b2A} : Set A45),
      (∀ s ∈ Subgroup.closure ({a2A, b2A} : Set A45), s * x = x * s) →
      x = 1 ∨ x = ((e.symm (QuaternionGroup.a 2) : ↥(Subgroup.closure ({a2A, b2A} : Set A45))) :
        A45) := by
    intro x hx hxc
    have hq8 : ∀ y : QuaternionGroup 2, (∀ y' : QuaternionGroup 2, y' * y = y * y') →
        y = 1 ∨ y = QuaternionGroup.a 2 := by decide +kernel
    have hy := hq8 (e ⟨x, hx⟩) (fun y' => by
      obtain ⟨s, rfl⟩ := e.surjective y'
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hxc s.1 s.2)))
    rcases hy with hy | hy
    · left
      have := e.injective (hy.trans (map_one e).symm)
      exact congrArg Subtype.val this
    · right
      have := e.injective (hy.trans (e.apply_symm_apply _).symm)
      exact congrArg Subtype.val this
  have hcard := card_map_centre_le_two D (sigma1Nine_order (z := z) D) hT hS hSZ
  have hle := card_centre_le_four_mul_card_map D h hZ (sigma1Nine_order (z := z) D) hT
  have hdvd := four_dvd_card_centre h hZ (sigma1Nine (z := z) D).2 hT
  have hpos : 0 < Nat.card ↥(T ⊓ centralizer (T : Set G)) := Nat.card_pos
  omega

end Final

section Final2


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

theorem card_centre_sylow_sigma1_mul (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T : Subgroup G}
    (hT : IsSylowOf 2 T
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G))) :
    Nat.card ↥(T ⊓ centralizer (T : Set G)) = 4 ∨
      Nat.card ↥(T ⊓ centralizer (T : Set G)) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ3 : orderOf (sigma1Nine (z := z) D * σ₂) = 3 := by
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂)]
    exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂
  have hqτ : qH D (sigma1Nine (z := z) D * σ₂) = s1A * s2A := by
    rw [map_mul, qH_sigma1Nine, hq₂]
  obtain ⟨-, -, -, -, -, hcen3⟩ := qa45_sigma_centralizer_sylow
  have hS : IsSylowOf 2 (Subgroup.closure ({tA, uA, vA * bA} : Set A45))
      (centralizer ({qH D (sigma1Nine (z := z) D * σ₂)} : Set A45)) := by
    rw [hqτ]
    exact isSylowOf_d8_centralizer_sigma1_mul
  have hA : Nat.card A45 = 51840 := card_QA45
  obtain ⟨hC1, hC2, hC3, hC4⟩ := qa45_involution_centralizers
  have hut1 : uA * tA ≠ 1 :=
    CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC2, hA]; omega)
  have hut2 : (uA * tA) * (uA * tA) = 1 := by
    have hcomm : Commute tA uA := Subtype.ext t_commute_u
    have htt : tA * tA = 1 := Subtype.ext t_sq
    have huu : uA * uA = 1 := Subtype.ext u_sq
    rw [Commute.mul_mul_mul_comm hcomm uA tA, huu, htt, one_mul]
  have hord : orderOf (uA * tA) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hut2) hut1
  have hSZ : ∀ x ∈ Subgroup.closure ({tA, uA, vA * bA} : Set A45),
      (∀ s ∈ Subgroup.closure ({tA, uA, vA * bA} : Set A45), s * x = x * s) →
      x = 1 ∨ x = uA * tA := by
    intro x hx hxc
    have hmem : x ∈ (Subgroup.center ↥(Subgroup.closure ({tA, uA, vA * bA} : Set A45))).map
        (Subgroup.closure ({tA, uA, vA * bA} : Set A45)).subtype :=
      ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hxc g.1 g.2), rfl⟩
    rw [hcen3] at hmem
    exact CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hord hmem
  have hcard := card_map_centre_le_two D hτ3 hT hS hSZ
  have hle := card_centre_le_four_mul_card_map D h hZ hτ3 hT
  have hdvd := four_dvd_card_centre h hZ (sigma1Nine (z := z) D * σ₂ : ↥(H z)).2 hT
  have hpos : 0 < Nat.card ↥(T ⊓ centralizer (T : Set G)) := Nat.card_pos
  omega

end Final2

section Final3


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

theorem eq_one_of_mem_map_centre_sigma1_mul_inv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T : Subgroup G}
    (hT : IsSylowOf 2 T
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)))
    {a : A45} (ha : a ∈ ((T ⊓ centralizer (T : Set G)).subgroupOf (H z)).map (qH D)) :
    a = 1 := by
  obtain ⟨w', hw', rfl⟩ := ha
  by_contra hne
  set ρ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hρ
  have hρ3 : orderOf ρ = 3 := by
    rw [← Subgroup.orderOf_coe ρ]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hqρ : qH D ρ = s1A * s2A⁻¹ := by
    rw [hρ, map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hwZ : (w' : G) ∈ T ⊓ centralizer (T : Set G) := hw'
  have hwT : (w' : G) ∈ T := (mem_inf.mp hwZ).1
  have hcomm : qH D w' ∈ centralizer ({s1A * s2A⁻¹} : Set A45) := by
    rw [← hqρ, mem_centralizer_singleton_iff]
    have h1 : (w' : G) * (ρ : G) = (ρ : G) * (w' : G) :=
      mem_centralizer_singleton_iff.mp (hT.le hwT).2
    have h2 : w' * ρ = ρ * w' := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  have h2el : ∃ k : ℕ, orderOf (qH D w') = 2 ^ k := by
    have hp := (IsPGroup.iff_orderOf.mp hT.isPGroup) ⟨(w' : G), hwT⟩
    obtain ⟨k, hk⟩ := hp
    have hdvd : orderOf (qH D w') ∣ 2 ^ k := by
      rw [← hk]
      have h3 : orderOf (qH D w') ∣ orderOf w' := orderOf_map_dvd _ _
      have h4 : orderOf w' = orderOf (⟨(w' : G), hwT⟩ : ↥T) := by
        rw [← Subgroup.orderOf_coe w', ← Subgroup.orderOf_coe (⟨(w' : G), hwT⟩ : ↥T)]
      exact h3.trans (h4 ▸ dvd_rfl)
    obtain ⟨k', -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k', hk'⟩
  obtain ⟨c, hcC, hcE⟩ := exists_conj_mem_closure_t_uv_of_mem_centralizer hcomm h2el
  have hb1 : c * qH D w' * c⁻¹ ≠ 1 := by
    intro h1
    apply hne
    have : qH D w' = c⁻¹ * (c * qH D w' * c⁻¹) * c := by group
    rw [this, h1]
    group
  have hfix4 := spinFixedCard_sigma1_mul_sigma2_inv_mul hcE hb1
  have hcr : c * (s1A * s2A⁻¹) = (s1A * s2A⁻¹) * c := mem_centralizer_singleton_iff.mp hcC
  have hconj : s1A * s2A⁻¹ * (c * qH D w' * c⁻¹) = c * (s1A * s2A⁻¹ * qH D w') * c⁻¹ := by
    calc s1A * s2A⁻¹ * (c * qH D w' * c⁻¹) = (s1A * s2A⁻¹ * c) * qH D w' * c⁻¹ := by group
      _ = (c * (s1A * s2A⁻¹)) * qH D w' * c⁻¹ := by rw [hcr]
      _ = c * (s1A * s2A⁻¹ * qH D w') * c⁻¹ := by group
  have hfixa : fixCard (((rhoA (s1A * s2A⁻¹ * qH D w') : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 4 := by
    rw [hconj, map_mul, map_mul, map_inv] at hfix4
    rw [← hfix4]
    exact (fixCard_conj (rhoA c) (rhoA (s1A * s2A⁻¹ * qH D w'))).symm.trans (by
      rw [map_mul, map_mul, map_inv])
  have hdim2 : fixDimV h (ρ * w') = 2 := by
    have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP (ρ * w')
    rw [map_mul, hqρ, hfixa] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))
  have hdim4 : fixDimV h ρ = 4 := by
    have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP ρ
    rw [hqρ, spinFixedCard_sigma1_mul_sigma2_inv] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))
  have hle : autFixedSubgroup (conjV h ρ) ≤ autFixedSubgroup (conjV h (ρ * w')) := by
    intro v hv
    rw [mem_autFixedSubgroup] at hv ⊢
    have hvw := conjV_eq_of_mem_centre_sylow h hρ3 hZ hT hwZ w'.2 hv
    rw [map_mul, MulAut.mul_apply, hvw, hv]
  have hcard := Subgroup.card_le_of_le hle
  rw [card_fix h ρ, card_fix h (ρ * w'), hdim4, hdim2] at hcard
  have : 2 ^ 4 ≤ 2 ^ 2 := hcard
  omega

theorem card_centre_sylow_sigma1_mul_inv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T : Subgroup G}
    (hT : IsSylowOf 2 T
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) :
    Nat.card ↥(T ⊓ centralizer (T : Set G)) = 4 := by
  have hρ3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 := by
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hbot : ((T ⊓ centralizer (T : Set G)).subgroupOf (H z)).map (qH D) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun a ha =>
      eq_one_of_mem_map_centre_sigma1_mul_inv D h hZ P hP hσ₂ hq₂ hc₂ hT ha
  have hle := card_centre_le_four_mul_card_map D h hZ hρ3 hT
  rw [hbot, Subgroup.card_bot] at hle
  have hdvd := four_dvd_card_centre h hZ (sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)).2 hT
  have hpos : 0 < Nat.card ↥(T ⊓ centralizer (T : Set G)) := Nat.card_pos
  omega

end Final3

section Star


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

omit [Finite G]
  hN in
private theorem conjugate_zpowers_eq (a g : G) :
    CFSG.conjugate (Subgroup.zpowers a) g = Subgroup.zpowers (g⁻¹ * a * g) := by
  rw [CFSG.conjugate, MonoidHom.map_zpowers]
  simp

omit
  hN in
private theorem conjugate_conjugate_eq (R : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate R a) b = CFSG.conjugate R (a * b) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  have : a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
  rw [this]

omit [Finite G]
  hN in
private theorem card_conjugate_eq (R : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate R g) = Nat.card R := by
  rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

omit [Finite G]
  hN in
private theorem card_centralizer_conj (a g : G) :
    Nat.card (centralizer ({g * a * g⁻¹} : Set G)) = Nat.card (centralizer ({a} : Set G)) := by
  have : centralizer ({g * a * g⁻¹} : Set G) =
      (centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [mem_centralizer_singleton_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [hx]
        _ = a * (g⁻¹ * x * g) := by group
    · rintro ⟨y, hy, rfl⟩
      calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
        _ = g * (a * y) * g⁻¹ := by rw [hy]
        _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  rw [this, Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G]
  hN in
private theorem centralizer_eq_of_zpowers_eq {a b : G}
    (hab : Subgroup.zpowers a = Subgroup.zpowers b) :
    centralizer ({a} : Set G) = centralizer ({b} : Set G) := by
  have key : ∀ {c d : G}, Subgroup.zpowers c = Subgroup.zpowers d →
      centralizer ({c} : Set G) ≤ centralizer ({d} : Set G) := by
    intro c d hcd x hx
    rw [mem_centralizer_singleton_iff] at hx ⊢
    have hd : d ∈ Subgroup.zpowers c := hcd ▸ Subgroup.mem_zpowers d
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ((show Commute x c from hx).zpow_right k).eq
  exact le_antisymm (key hab) (key hab.symm)


theorem star_of_card_three_of_spin (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (A0 : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) :
    ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∀ g : G, CFSG.conjugate R g ≤ H z →
        ∃ h' ∈ H z, CFSG.conjugate R g = CFSG.conjugate R h' := by
  classical
  obtain ⟨σ₂, hσ₂, hq₂, hc₂⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  have hE27 := e27LineCountData_of_not_equalityBranch D h hIII hσ₂ hq₂ hc₂
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  have hP' : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := fun a => by
    simpa [rhoA, toQAct] using hP a
  obtain ⟨T₁, hT₁⟩ := exists_isSylowOf 2
    (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))
  obtain ⟨T₂, hT₂⟩ := exists_isSylowOf 2
    (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
  obtain ⟨T₃, hT₃⟩ := exists_isSylowOf 2
    (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G))
  have hS₁ := isSylowOf_centralizer_of_centre_card h hZ A0 (sigma1Nine (z := z) D).2 hT₁
    (card_centre_sylow_sigma1 D h hZ hT₁)
  have hS₂ := isSylowOf_centralizer_of_centre_card h hZ A0
    (sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)).2 hT₂
    (Or.inl (card_centre_sylow_sigma1_mul_inv D h hZ P hP' hσ₂ hq₂ hc₂ hT₂))
  have hS₃ := isSylowOf_centralizer_of_centre_card h hZ A0
    (sigma1Nine (z := z) D * σ₂ : ↥(H z)).2 hT₃
    (card_centre_sylow_sigma1_mul D h hZ hσ₂ hq₂ hc₂ hT₃)
  have hc₁ : Nat.card T₁ = 2 ^ 7 := card_isSylowOf_centralizer_sigma1Nine D h hT₁
  have hc₂' : Nat.card T₂ = 2 ^ 8 :=
    card_isSylowOf_centralizer_sigma1Nine_mul_inv D h hIII hσ₂ hq₂ hc₂ hE27 hT₂
  have hc₃ : Nat.card T₃ = 2 ^ 5 :=
    card_isSylowOf_centralizer_sigma1Nine_mul D h hIII hσ₂ hq₂ hc₂ hE27 hT₃
  set a₁ : G := ((sigma1Nine (z := z) D : ↥(H z)) : G) with ha₁
  set a₂ : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) with ha₂
  set a₃ : G := ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) with ha₃
  let a : Fin 3 → G := ![a₁, a₂, a₃]
  let T : Fin 3 → Subgroup G := ![T₁, T₂, T₃]
  let c : Fin 3 → ℕ := ![2 ^ 7, 2 ^ 8, 2 ^ 5]
  have hTsyl : ∀ i, IsSylowOf 2 (T i) (centralizer ({a i} : Set G)) := by
    intro i
    fin_cases i
    · exact hS₁
    · exact hS₂
    · exact hS₃
  have hTc : ∀ i, Nat.card (T i) = c i := by
    intro i
    fin_cases i
    · exact hc₁
    · exact hc₂'
    · exact hc₃
  have hcls := orderThree_subgroup_classes_H D h hσ₂ hq₂ hc₂
  have hcls' : ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ g ∈ H z, ∃ i : Fin 3, CFSG.conjugate R g = Subgroup.zpowers (a i) := by
    intro R hRH hR3
    obtain ⟨g, hg, hR | hR | hR⟩ := hcls R hRH hR3
    · exact ⟨g, hg, 0, hR⟩
    · exact ⟨g, hg, 1, hR⟩
    · exact ⟨g, hg, 2, hR⟩
  have hne : ∀ (i j : Fin 3) (k : G),
      CFSG.conjugate (Subgroup.zpowers (a i)) k = Subgroup.zpowers (a j) → i = j := by
    intro i j k hk
    rw [conjugate_zpowers_eq] at hk
    have hcent : Nat.card (centralizer ({a i} : Set G)) =
        Nat.card (centralizer ({a j} : Set G)) := by
      rw [← centralizer_eq_of_zpowers_eq hk, ← card_centralizer_conj (a i) k⁻¹]
      simp
    have hcard : c i = c j := by
      rw [← hTc i, ← hTc j, (hTsyl i).card_eq, (hTsyl j).card_eq, hcent]
    fin_cases i <;> fin_cases j <;> simp [c] at hcard ⊢
  intro R hRH hR3 g hg
  obtain ⟨g₁, hg₁, i, hi⟩ := hcls' R hRH hR3
  have hR'3 : Nat.card (CFSG.conjugate R g) = 3 := by rw [card_conjugate_eq, hR3]
  obtain ⟨g₂, hg₂, j, hj⟩ := hcls' _ hg hR'3
  have hij : CFSG.conjugate (Subgroup.zpowers (a i)) (g₁⁻¹ * g * g₂) =
      Subgroup.zpowers (a j) := by
    rw [← hi, conjugate_conjugate_eq, ← hj, conjugate_conjugate_eq]
    congr 1
    group
  have hij' := hne i j _ hij
  subst hij'
  refine ⟨g₁ * g₂⁻¹, (H z).mul_mem hg₁ ((H z).inv_mem hg₂), ?_⟩
  have h1 : CFSG.conjugate R g₁ = CFSG.conjugate R (g * g₂) := by
    rw [hi, ← hj, conjugate_conjugate_eq]
  have h2 : CFSG.conjugate (CFSG.conjugate R (g * g₂)) g₂⁻¹ = CFSG.conjugate R g := by
    rw [conjugate_conjugate_eq]
    congr 1
    group
  rw [← h2, ← h1, conjugate_conjugate_eq]

end Star

end CFSG.RankThree.GF2n.Parrott
