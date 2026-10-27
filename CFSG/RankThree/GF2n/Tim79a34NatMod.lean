module

public import CFSG.RankThree.GF2n.Tim79a34TwLower
public import CFSG.RankThree.GF2n.Tim79a34TwZR
public import CFSG.RankThree.GF2n.Tim79a34IW

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem nm_two_elt {K : Subgroup G} (hK : Nat.card K = 2) :
    ∃ a ∈ K, a ≠ 1 ∧ ∀ b ∈ K, b = 1 ∨ b = a := by
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hK
  have hmem : ∀ b : ↥K, b = x ∨ b = y := fun b => by
    have hb : b ∈ ({x, y} : Set ↥K) := by rw [huniv]; exact Set.mem_univ b
    simpa using hb
  have key : ∃ a : ↥K, a ≠ 1 ∧ ∀ b : ↥K, b = 1 ∨ b = a := by
    rcases hmem 1 with h1 | h1
    · refine ⟨y, fun h => hxy (h1.symm.trans h.symm), fun b => ?_⟩
      rcases hmem b with hb | hb
      · left
        rw [hb]
        exact h1.symm
      · right
        rw [hb]
    · refine ⟨x, fun h => hxy (h.trans h1), fun b => ?_⟩
      rcases hmem b with hb | hb
      · right
        rw [hb]
      · left
        rw [hb]
        exact h1.symm
  obtain ⟨a, ha1, ha⟩ := key
  refine ⟨a, a.2, fun h => ha1 (Subtype.ext h), fun b hb => ?_⟩
  rcases ha ⟨b, hb⟩ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem nm_sq_eq_one {K : Subgroup G} {a : G} (ha : a ∈ K) (ha1 : a ≠ 1)
    (hK : ∀ b ∈ K, b = 1 ∨ b = a) : a * a = 1 := by
  rcases hK (a * a) (K.mul_mem ha ha) with h | h
  · exact h
  · exact absurd (mul_left_cancel (h.trans (mul_one a).symm)) ha1

theorem nm_coset [Finite G] {S U : Subgroup G} (hU : Nat.card U = 4)
    (hUS : Nat.card ↥(U ⊓ S) = 2) {y u : G} (hy : y ∈ U) (hu : u ∈ U) (hyS : y ∉ S)
    (huS : u ∉ S) : y⁻¹ * u ∈ S := by
  set K : Subgroup ↥U := (U ⊓ S).subgroupOf U with hK
  have hKcard : Nat.card ↥K = 2 := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hUS]
  have hidx : K.index = 2 := by
    have h := K.card_mul_index
    rw [hKcard, hU] at h
    omega
  obtain ⟨a, haK, hK2⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp hidx
  set yU : ↥U := ⟨y, hy⟩ with hyU
  set uU : ↥U := ⟨u, hu⟩ with huU
  have hyK : yU ∉ K := fun h => hyS (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2
  have huK : uU ∉ K := fun h => huS (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2
  have h1 : a * yU ∈ K := (hK2 yU).resolve_right hyK
  have h2 : a * uU ∈ K := (hK2 uU).resolve_right huK
  have h3 : (a * yU)⁻¹ * (a * uU) ∈ K := K.mul_mem (K.inv_mem h1) h2
  have e : (a * yU)⁻¹ * (a * uU) = yU⁻¹ * uU := by group
  rw [e] at h3
  have h4 := Subgroup.mem_subgroupOf.mp h3
  have h5 : y⁻¹ * u ∈ U ⊓ S := by simpa using h4
  exact (Subgroup.mem_inf.mp h5).2

theorem nm_wOf_le_normalizer [Finite G] {M Q P V H : Subgroup G} (hc : MinCex M V Q P H)
    {g : G} (hg : g ∈ H) : wOf V H ≤ Subgroup.normalizer (conjSubgroup g V : Set G) := by
  intro w hw
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hc.conj_inf_wOf_ne_bot hg)
  obtain ⟨haU, haW⟩ := Subgroup.mem_inf.mp ha
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have hcomm : w * a = a * w := hc.wOf_isElemAbelian.comm hw haW
  exact Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti g) haU ha1' hcomm

theorem nm_comm_mem [Finite G] {M Q P V H : Subgroup G} (hc : MinCex M V Q P H) {g : G}
    (hg : g ∈ H) {w u : G} (hw : w ∈ wOf V H) (hu : u ∈ conjSubgroup g V) :
    w * u * w⁻¹ * u⁻¹ ∈ conjSubgroup g V ⊓ wOf V H := by
  have huH : u ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hg hu
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : w * u * w⁻¹ ∈ conjSubgroup g V :=
      (Subgroup.mem_normalizer_iff.mp (nm_wOf_le_normalizer hc hg hw) u).mp hu
    exact (conjSubgroup g V).mul_mem h1 ((conjSubgroup g V).inv_mem hu)
  · have h2 : u * w⁻¹ * u⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H huH) w⁻¹).mp
        ((wOf V H).inv_mem hw)
    have h3 : w * u * w⁻¹ * u⁻¹ = w * (u * w⁻¹ * u⁻¹) := by group
    rw [h3]
    exact (wOf V H).mul_mem hw h2

theorem nm_not_conj_le_wOf [Finite G] {M Q P V H : Subgroup G} (hc : MinCex M V Q P H)
    {g : G} (hg : g ∈ H) : ¬ conjSubgroup g V ≤ wOf V H := by
  intro hle
  apply hc.not_V_le_wOf
  intro v hv
  have hmem : g * v * g⁻¹ ∈ conjSubgroup g V :=
    mem_conjSubgroup.mpr (by rw [show g⁻¹ * (g * v * g⁻¹) * g = v by group]; exact hv)
  exact (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hg) v).mpr (hle hmem)

theorem nm_card_omega [Finite G] {M Q P V H : Subgroup G} (hc : MinCex M V Q P H)
    (hV4 : Nat.card ↥V = 4) (hVW : Nat.card ↥(V ⊓ wOf V H) = 2) {U : Subgroup G}
    (hU : U ∈ omegaOf V H) : Nat.card ↥U = 4 ∧ Nat.card ↥(U ⊓ wOf V H) = 2 := by
  obtain ⟨g, hg, rfl⟩ := hU
  have hWc : conjSubgroup g (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hg)
  have e : conjSubgroup g V ⊓ wOf V H = conjSubgroup g (V ⊓ wOf V H) := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_inf, hWc]
  refine ⟨?_, ?_⟩
  · rw [CFSG.RankThree.GF2n.card_conjSubgroup, hV4]
  · rw [e, CFSG.RankThree.GF2n.card_conjSubgroup, hVW]

theorem nm_noCommute {M Q P V H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
    (hdat : Sec23Data V H) {n : ℕ} (Φ : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H)
    (hΦ : Function.Injective Φ) {v w : Fin n ⊕ Fin n → GaloisField 2 1} (hv : v ≠ 0)
    (hw : w ≠ 0) (hvw : CaseM.spForm v w ≠ 0)
    {hi hj : ↥(xOf V H)} {Ti Tj : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (hTi : CaseM.IsTransGroup v Ti) (hTj : CaseM.IsTransGroup w Tj)
    (ei : imgZ V H (conjSubgroup (hi : G) V) = Ti.map Φ)
    (ej : imgZ V H (conjSubgroup (hj : G) V) = Tj.map Φ)
    {y a : G} (hy : y ∈ conjSubgroup (hi : G) V) (hyW : y ∉ wOf V H)
    (ha : a ∈ conjSubgroup (hj : G) V) (ha1 : a ≠ 1) (hc' : y * a = a * y) : False := by
  have hVH : V ≤ H := hc.V_le_H
  have hhi : (hi : G) ∈ H := xOf_le_H hVH hi.2
  have hyX : y ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hhi) hy
  have hyN : y ∈ Subgroup.normalizer (conjSubgroup (hj : G) V : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI
      (CFSG.RankThree.GF2n.isTI_conjSubgroup hc.ti (hj : G)) ha ha1 hc'
  have hyN' : conjSubgroup y (conjSubgroup (hj : G) V) = conjSubgroup (hj : G) V :=
    mem_normalizer_iff_conjSubgroup_eq.mp hyN
  have hsN : xToZ hVH ⟨y, hyX⟩ ∈ Subgroup.normalizer
      ((imgZ V H (conjSubgroup (hj : G) V) : Subgroup (XbarZ V H)) : Set (XbarZ V H)) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have h1 := twl_imgZ_conj_gen hVH (conjSubgroup (hj : G) V) y hyX
    rw [hyN'] at h1
    exact h1.symm
  have hsU : xToZ hVH ⟨y, hyX⟩ ∈ imgZ V H (conjSubgroup (hi : G) V) :=
    twl_mem_imgZ hVH hy hyX
  rw [ei] at hsU
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hsU
  have hs1 : xToZ hVH ⟨y, hyX⟩ ≠ 1 :=
    twl_xToZ_ne_one hVH hdat (conjSubgroup_mem_omegaOf hhi) hy hyW hyX
  rcases twl_trans_cases hTi ht with ht1 | htm
  · exact hs1 (by rw [← hts, ht1, map_one])
  obtain ⟨t', ht't⟩ := hTj.2 1
  have ht'T : t' ∈ Tj := (hTj.1 t').2 ⟨1, ht't⟩
  have ht'1 : t' ≠ 1 := by
    intro h
    apply twl_spTrans_one_ne_one hw
    rw [← ht't, h, map_one]
  have hp : Φ t' ∈ imgZ V H (conjSubgroup (hj : G) V) := by
    rw [ej]
    exact Subgroup.mem_map.mpr ⟨t', ht'T, rfl⟩
  have hconj := (Subgroup.mem_normalizer_iff.mp hsN (Φ t')).mp hp
  rw [ej] at hconj
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hconj
  set s := xToZ hVH ⟨y, hyX⟩ with hsdef
  rcases twl_trans_cases hTj hu with hu1 | hum
  · rw [hu1, map_one] at hu'
    have h1' : Φ t' = 1 := by
      calc Φ t' = s⁻¹ * (s * Φ t' * s⁻¹) * s := by group
        _ = 1 := by rw [← hu']; group
    exact ht'1 (hΦ (show Φ t' = Φ 1 by rw [h1', map_one]))
  · have hut : u = t' := SpExtras.mat_injective (hum.trans ht't.symm)
    rw [hut] at hu'
    have hcomm2 : s * Φ t' = Φ t' * s := by
      calc s * Φ t' = (s * Φ t' * s⁻¹) * s := by group
        _ = Φ t' * s := by rw [← hu']
    have hcomm3 : Φ (t * t') = Φ (t' * t) := by
      rw [map_mul, map_mul, hts, hcomm2]
    have htt : t * t' = t' * t := hΦ hcomm3
    have hmat := congrArg (SpExtras.mat n (GaloisField 2 1)) htt
    rw [map_mul, map_mul, htm, ht't] at hmat
    rcases CaseM.spForm_eq_zero_of_commute hv hmat with h0 | ⟨l, hl⟩
    · exact hvw h0
    · apply hvw
      rw [hl, ModelRank.spForm_smul_right', CaseM.spForm_self, mul_zero]

theorem nm_sp_data [Finite G] {V H : Subgroup G} (hq : qBar V H = 2)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (h3 : Sec23Three V H) :
    ∃ (n : ℕ) (Φ : ↥(StatedSp n (GaloisField 2 1)) →* Xbar V H), 2 ≤ n ∧
      Function.Bijective Φ ∧ ∃ (a₀ : Fin n ⊕ Fin n → GaloisField 2 1)
        (T₀ : Subgroup ↥(StatedSp n (GaloisField 2 1))), a₀ ≠ 0 ∧
        CaseM.IsTransGroup a₀ T₀ ∧ T₀.map Φ = Vy V H := by
  obtain ⟨f, hf, h2f, n, hn, Φ₀, hΦ₀, hΔ⟩ := h3
  have hf1 : f = 1 := by
    have : 2 ^ f = 2 ^ 1 := by rw [h2f, hq]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hf1
  have hprojI : Function.Injective (projZ V H) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : a ∈ (QuotientGroup.mk' (Subgroup.center (Xbar V H)) :
        Xbar V H →* XbarZ V H).ker := ha
    rw [QuotientGroup.ker_mk', hZ] at h1
    exact Subgroup.mem_bot.mp h1
  have hprojB : Function.Bijective (projZ V H) := ⟨hprojI, QuotientGroup.mk'_surjective _⟩
  let e : Xbar V H ≃* XbarZ V H := MulEquiv.ofBijective (projZ V H) hprojB
  let Φ : ↥(StatedSp n (GaloisField 2 1)) →* Xbar V H := e.symm.toMonoidHom.comp Φ₀
  have hΦ : ∀ x, projZ V H (Φ x) = Φ₀ x := fun x => e.apply_symm_apply (Φ₀ x)
  have hΦb : Function.Bijective Φ := e.symm.bijective.comp hΦ₀
  have hVZ : VZ V H ∈ rootClassZ V H :=
    ⟨1, (CFSG.Timmesfeld.ARS.conjSub_one (VZ V H)).symm⟩
  obtain ⟨g, hg⟩ := (hΔ (VZ V H)).1 hVZ
  have hTg := (ModelRank.isTransGroup_rootGroup_last (K := GaloisField 2 1)
    (by omega : 1 ≤ n)).conjSub g
  have he0 : (Pi.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) (1 : GaloisField 2 1) :
      Fin n ⊕ Fin n → GaloisField 2 1) ≠ 0 := fun h => by
    simpa using congrFun h (Sum.inl ⟨n - 1, by omega⟩)
  refine ⟨n, Φ, hn, hΦb, _, _, ModelRank.mat_mulVec_ne_zero' g he0, hTg, ?_⟩
  apply Subgroup.map_injective hprojI
  rw [Subgroup.map_map]
  have hcomp : (projZ V H).comp Φ = Φ₀ := MonoidHom.ext hΦ
  rw [hcomp, ← hg]
  rfl

theorem nm_dy_iff [Finite G] {M Q P V H : Subgroup G} (hc : MinCex M V Q P H)
    (hdat : Sec23Data V H) {n : ℕ} {Φ : ↥(StatedSp n (GaloisField 2 1)) →* Xbar V H}
    (hΦ : Function.Bijective Φ) {a₀ : Fin n ⊕ Fin n → GaloisField 2 1}
    {T₀ : Subgroup ↥(StatedSp n (GaloisField 2 1))} (ha₀ : a₀ ≠ 0)
    (hT₀ : CaseM.IsTransGroup a₀ T₀) (hΦT : T₀.map Φ = Vy V H) (y : Xbar V H) :
    y ∈ Dy V H ↔ ∃ v : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 ∧
      ∃ t : ↥(StatedSp n (GaloisField 2 1)),
        SpExtras.mat n (GaloisField 2 1) t = CaseM.spTrans v 1 ∧ Φ t = y := by
  obtain ⟨d, hdV, hdD, hd1⟩ := hc.exists_vy_mem_Dy hdat
  have hdT : d ∈ T₀.map Φ := by rw [hΦT]; exact hdV
  obtain ⟨t₁, ht₁T, ht₁d⟩ := Subgroup.mem_map.mp hdT
  have hd1' : d ≠ 1 := fun h => hd1 (by rw [h, map_one])
  have ht₁mat : SpExtras.mat n (GaloisField 2 1) t₁ = CaseM.spTrans a₀ 1 := by
    rcases twl_trans_cases hT₀ ht₁T with h | h
    · exact absurd (by rw [← ht₁d, h, map_one]) hd1'
    · exact h
  obtain ⟨d₀, hd₀⟩ := hdat.isClass
  have hd0 : IsConj d₀ d := by
    have h := hdD
    rw [hd₀] at h
    exact h
  have hDy : ∀ g : Xbar V H, g ∈ Dy V H ↔ IsConj d g := by
    intro g
    rw [hd₀, Set.mem_setOf_eq]
    exact ⟨fun h => hd0.symm.trans h, fun h => hd0.trans h⟩
  constructor
  · intro hy
    obtain ⟨c, hc'⟩ := isConj_iff.mp ((hDy y).mp hy)
    obtain ⟨g, rfl⟩ := hΦ.2 c
    refine ⟨SpExtras.mat n (GaloisField 2 1) g *ᵥ a₀, ModelRank.mat_mulVec_ne_zero' g ha₀,
      g * t₁ * g⁻¹, CaseM.mat_conj_of_mat_eq ht₁mat g, ?_⟩
    rw [map_mul, map_mul, map_inv, ht₁d]
    exact hc'
  · rintro ⟨v, hv, t, htm, rfl⟩
    obtain ⟨h, hh⟩ := twZR_exists_mat_mulVec_eq ha₀ hv
    rw [hDy]
    refine isConj_iff.mpr ⟨Φ h, ?_⟩
    have hk : h * t₁ * h⁻¹ = t := by
      apply SpExtras.mat_injective
      rw [CaseM.mat_conj_of_mat_eq ht₁mat h, hh, htm]
    rw [← hk, map_mul, map_mul, map_inv, ht₁d]

theorem nm_point_of_dy [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    {y : Xbar V H} (hy : y ∈ Dy V H) :
    ∃ x : ↥(xOf V H), ∃ U ∈ omegaOf V H, (x : G) ∈ U ∧ (x : G) ∉ wOf V H ∧
      xToXbar hc.V_le_H x = y := by
  have hy' : (y : Hbar V H) ∈ dbarOf V H := hy
  obtain ⟨x, ⟨_, U, hU, hxU⟩, hxW, hxy⟩ := mem_dbarOf_iff.mp hy'
  have hxX : (x : G) ∈ xOf V H := le_xOf hU hxU
  refine ⟨⟨x, hxX⟩, U, hU, hxU, hxW, Subtype.ext ?_⟩
  rw [coe_xToXbar]
  exact hxy

theorem nm_exists_point [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    {U : Subgroup G} (hU : U ∈ omegaOf V H) :
    ∃ y : ↥(xOf V H), (y : G) ∈ U ∧ (y : G) ∉ wOf V H ∧ xToXbar hc.V_le_H y ∈ Dy V H := by
  obtain ⟨g, hg, rfl⟩ := hU
  obtain ⟨y0, hy0, hy0W⟩ := SetLike.not_le_iff_exists.mp (nm_not_conj_le_wOf hc hg)
  have hyX : y0 ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hg) hy0
  refine ⟨⟨y0, hyX⟩, hy0, hy0W, ?_⟩
  have hy1 : y0 ≠ 1 := fun h => hy0W (by rw [h]; exact one_mem _)
  show ((xToXbar hc.V_le_H ⟨y0, hyX⟩ : Xbar V H) : Hbar V H) ∈ dbarOf V H
  rw [coe_xToXbar]
  exact mem_dbarOf_iff.mpr ⟨⟨y0, xOf_le_H hc.V_le_H hyX⟩,
    ⟨hy1, conjSubgroup g V, ⟨g, hg, rfl⟩, hy0⟩, hy0W, rfl⟩

theorem nm_mem_W_of_xToXbar_eq {V H : Subgroup G} (hVH : V ≤ H) {a b : ↥(xOf V H)}
    (h : xToXbar hVH a = xToXbar hVH b) : (a : G)⁻¹ * (b : G) ∈ wOf V H := by
  have h1 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) a) =
      piBar V H (Subgroup.inclusion (xOf_le_H hVH) b) := by
    rw [← coe_xToXbar hVH, ← coe_xToXbar hVH, h]
  have h2 : piBar V H ((Subgroup.inclusion (xOf_le_H hVH) a)⁻¹ *
      Subgroup.inclusion (xOf_le_H hVH) b) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (piBar_eq_one_iff _).mp h2
  simpa using h3

theorem nm_conjX [Finite G] {M Q P V H : Subgroup G} (hH : TwoEndHyp M V Q P H) {U : Subgroup G}
    (hU : U ∈ omegaOf V H) : ∃ x : ↥(xOf V H), U = conjSubgroup (x : G) V := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  obtain ⟨h, hh, rfl⟩ := hU
  have hsup : h ∈ xOf V H ⊔ cPbar V H P := by
    rw [hH.concl.2.1]
    exact hh
  have hCP : cPbar V H P ≤ P := fun c hcC => (inf_le_left : P ⊓ cX V H ≤ P) hcC
  have hCN : cPbar V H P ≤ Subgroup.normalizer (xOf V H : Set G) := fun c hcC =>
    H_le_normalizer_xOf V H (hc.PleH (hCP hcC))
  obtain ⟨v, hv, c, hcC, hvc⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hCN hsup
  have hcV : conjSubgroup c V = V := by
    have hcQ : c ∈ Q ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← hc.hP]
      exact hCP hcC
    exact mem_normalizer_iff_conjSubgroup_eq.mp
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hcQ).2)
  refine ⟨⟨v, hv⟩, ?_⟩
  show conjSubgroup h V = conjSubgroup v V
  rw [hvc, ← conjSubgroup_conjSubgroup, hcV]

theorem nm_uniq [Finite G] {M V Q P H : Subgroup G} (hMU : MemberUniqueStatement)
    (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hV4 : Nat.card ↥V = 4) (hVW : Nat.card ↥(V ⊓ wOf V H) = 2) {U U' : Subgroup G}
    (hU : U ∈ omegaOf V H) (hU' : U' ∈ omegaOf V H) {y y' : G} (hy : y ∈ U)
    (hyW : y ∉ wOf V H) (hy' : y' ∈ U') (hy'W : y' ∉ wOf V H)
    (hyy : y⁻¹ * y' ∈ wOf V H) : U' = U := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hU'c := nm_card_omega hc hV4 hVW hU'
  have hle : U' ≤ U ⊔ wOf V H := by
    intro u' hu'
    by_cases hu'W : u' ∈ wOf V H
    · exact Subgroup.mem_sup_right hu'W
    · have hc2 : y'⁻¹ * u' ∈ wOf V H := nm_coset hU'c.1 hU'c.2 hy' hu' hy'W hu'W
      have e : u' = y * ((y⁻¹ * y') * (y'⁻¹ * u')) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hy ((wOf V H).mul_mem hyy hc2)
  exact hMU G M V Q P H hH hZ U hU U' hU' hle

theorem nm_imgZ_member [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) →* Xbar V H} {v : Fin n ⊕ Fin n → GaloisField 2 1}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 1))} (hT : CaseM.IsTransGroup v T)
    {t : ↥(StatedSp n (GaloisField 2 1))}
    (ht : SpExtras.mat n (GaloisField 2 1) t = CaseM.spTrans v 1)
    {x y : ↥(xOf V H)} (hyU : (y : G) ∈ conjSubgroup (x : G) V) (hyW : (y : G) ∉ wOf V H)
    (hyΦ : xToXbar hc.V_le_H y = Φ t) (hU4 : Nat.card ↥(conjSubgroup (x : G) V) = 4)
    (hU2 : Nat.card ↥(conjSubgroup (x : G) V ⊓ wOf V H) = 2) :
    imgZ V H (conjSubgroup (x : G) V) = T.map ((projZ V H).comp Φ) := by
  have hVH : V ≤ H := hc.V_le_H
  have hUX : conjSubgroup (x : G) V ≤ xOf V H :=
    le_xOf (conjSubgroup_mem_omegaOf (xOf_le_H hVH x.2))
  have hWone : ∀ w : G, ∀ hwX : w ∈ xOf V H, w ∈ wOf V H → xToZ hVH ⟨w, hwX⟩ = 1 := by
    intro w hwX hwW
    rw [xToZ_apply]
    have h1 : xToXbar hVH ⟨w, hwX⟩ = 1 := by
      apply Subtype.ext
      rw [coe_xToXbar]
      exact (piBar_eq_one_iff _).mpr hwW
    rw [h1, map_one]
  have key : ∀ u : G, u ∈ conjSubgroup (x : G) V → ∀ huX : u ∈ xOf V H,
      xToZ hVH ⟨u, huX⟩ = 1 ∨ xToZ hVH ⟨u, huX⟩ = xToZ hVH y := by
    intro u hu huX
    by_cases huW : u ∈ wOf V H
    · exact Or.inl (hWone u huX huW)
    · right
      have hcos := nm_coset hU4 hU2 hyU hu hyW huW
      have hwX : y⁻¹ * u ∈ xOf V H := (xOf V H).mul_mem ((xOf V H).inv_mem y.2) huX
      have e : (⟨u, huX⟩ : ↥(xOf V H)) = y * ⟨y⁻¹ * u, hwX⟩ := Subtype.ext (by simp)
      rw [e, map_mul, hWone _ hwX hcos, mul_one]
  ext s
  constructor
  · intro hs
    unfold imgZ at hs
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hs
    have hzU : (z : Hbar V H) ∈ barOf V H (conjSubgroup (x : G) V) := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨u, huU, huz⟩ := mem_barOf_iff.mp hzU
    have huX : (u : G) ∈ xOf V H := hUX huU
    have hzz : xToXbar hVH ⟨(u : G), huX⟩ = z := Subtype.ext (by rw [coe_xToXbar]; exact huz)
    have hs' : projZ V H z = xToZ hVH ⟨(u : G), huX⟩ := by rw [xToZ_apply, hzz]
    rw [hs']
    rcases key (u : G) huU huX with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      refine Subgroup.mem_map.mpr ⟨t, (hT.1 t).2 ⟨1, ht⟩, ?_⟩
      show projZ V H (Φ t) = xToZ hVH y
      rw [xToZ_apply, hyΦ]
  · intro hs
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp hs
    rcases twl_trans_cases hT ht' with h | h
    · rw [h, map_one]
      exact Subgroup.one_mem _
    · have ht'eq : t' = t := SpExtras.mat_injective (h.trans ht.symm)
      rw [ht'eq]
      have hm : projZ V H (Φ t) = xToZ hVH y := by rw [xToZ_apply, hyΦ]
      show projZ V H (Φ t) ∈ imgZ V H (conjSubgroup (x : G) V)
      rw [hm]
      exact twl_mem_imgZ hVH hyU y.2

theorem nm_comm_six {S : Subgroup G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    {A B C pA pB pC : G} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hpA : pA ∈ S) (hpB : pB ∈ S)
    (hpC : pC ∈ S) : (A * pA) * (B * pB) * (C * pC) = A * B * C * (pA * pB * pC) := by
  calc (A * pA) * (B * pB) * (C * pC) = A * (pA * B) * pB * C * pC := by group
    _ = A * (B * pA) * pB * C * pC := by rw [hS pA hpA B hB]
    _ = A * B * (pA * pB) * C * pC := by group
    _ = A * B * ((pA * pB) * C) * pC := by group
    _ = A * B * (C * (pA * pB)) * pC := by rw [hS (pA * pB) (S.mul_mem hpA hpB) C hC]
    _ = A * B * C * (pA * pB) * pC := by group
    _ = A * B * C * (pA * pB * pC) := by group

open _root_.Classical in
theorem nm_psi_prod {n : ℕ} {z v w : Fin n ⊕ Fin n → GaloisField 2 1} (A : G) (hA : A * A = 1) :
    (if CaseM.spForm z (v + w) = 0 then (1 : G) else A) *
      (if CaseM.spForm z v = 0 then (1 : G) else A) *
      (if CaseM.spForm z w = 0 then (1 : G) else A) = 1 := by
  rw [ModelRank.spForm_add_right]
  rcases twl_gf2 (CaseM.spForm z v) with h1 | h1 <;>
    rcases twl_gf2 (CaseM.spForm z w) with h2 | h2 <;>
    simp [h1, h2, hA, CharTwo.add_self_eq_zero]

theorem naturalModule_holds (hU : MemberUniqueStatement) : NaturalModuleStatement := by
  classical
  have hMU : MemberUniqueStatement := hU
  intro G _ _ M V Q P H hH hZ
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hdat : Sec23Data V H := hH.setup.data
  have hWc : ∀ x ∈ wOf V H, ∀ y ∈ wOf V H, x * y = y * x := fun x hx y hy =>
    hc.wOf_isElemAbelian.comm hx hy
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hV4 : Nat.card ↥V = 4 := by
    have h := twb_card_barOf_mul (V := V) (H := H) hVH
    have hq' : Nat.card ↥(barOf V H V) = 2 := hH.q_two
    rw [hq', hVW] at h
    omega
  obtain ⟨n, Φ, hn, hΦb, a₀, T₀, ha₀, hT₀, hΦT⟩ := nm_sp_data hH.q_two hZ hH.three
  have hΦinj : Function.Injective Φ := hΦb.1
  have hΦ' : Function.Injective ((projZ V H).comp Φ) := (iw_projZ_injective hZ).comp hΦinj
  choose tt htt using fun v : Fin n ⊕ Fin n → GaloisField 2 1 =>
    ModelRank.exists_mat_eq_spTrans v 1
  choose Tt hTt using fun v : Fin n ⊕ Fin n → GaloisField 2 1 => ModelRank.exists_isTransGroup v
  have hpt : ∀ v : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 → ∃ x y : ↥(xOf V H),
      (y : G) ∈ conjSubgroup (x : G) V ∧ (y : G) ∉ wOf V H ∧ xToXbar hVH y = Φ (tt v) := by
    intro v hv
    have hDy' : Φ (tt v) ∈ Dy V H :=
      (nm_dy_iff hc hdat hΦb ha₀ hT₀ hΦT _).mpr ⟨v, hv, tt v, htt v, rfl⟩
    obtain ⟨y, U, hU0, hyU, hyW, hyΦ⟩ := nm_point_of_dy hc hDy'
    obtain ⟨x, hx⟩ := nm_conjX hH hU0
    exact ⟨x, y, by rw [← hx]; exact hyU, hyW, hyΦ⟩
  choose! xs ys hysU hysW hysΦ using hpt
  have hxH : ∀ v, (xs v : G) ∈ H := fun v => xOf_le_H hVH (xs v).2
  have hA : ∀ v : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 → ∃ a : G,
      a ∈ conjSubgroup (xs v : G) V ⊓ wOf V H ∧ a ≠ 1 ∧
        ∀ b ∈ conjSubgroup (xs v : G) V ⊓ wOf V H, b = 1 ∨ b = a := by
    intro v _
    have hU := (nm_card_omega hc hV4 hVW (conjSubgroup_mem_omegaOf (hxH v))).2
    exact nm_two_elt hU
  choose! af hafmem hafne hafun using hA
  obtain ⟨aG, haG⟩ : ∃ aG : (Fin n ⊕ Fin n → GaloisField 2 1) → G,
      ∀ v, aG v = if v = 0 then 1 else af v := ⟨_, fun v => rfl⟩
  have haG0 : aG 0 = 1 := by rw [haG]; simp
  have haGne' : ∀ v, v ≠ 0 → aG v = af v := fun v hv => by rw [haG, if_neg hv]
  have haGmem : ∀ v, v ≠ 0 → aG v ∈ conjSubgroup (xs v : G) V ⊓ wOf V H := fun v hv => by
    rw [haGne' v hv]
    exact hafmem v hv
  have haGW : ∀ v, aG v ∈ wOf V H := fun v => by
    by_cases hv : v = 0
    · rw [hv, haG0]
      exact one_mem _
    · exact (Subgroup.mem_inf.mp (haGmem v hv)).2
  have haGne : ∀ v, v ≠ 0 → aG v ≠ 1 := fun v hv => by
    rw [haGne' v hv]
    exact hafne v hv
  have haGun : ∀ v, v ≠ 0 → ∀ b ∈ conjSubgroup (xs v : G) V ⊓ wOf V H, b = 1 ∨ b = aG v :=
    fun v hv b hb => by
      rw [haGne' v hv]
      exact hafun v hv b hb
  have haGsq : ∀ v, v ≠ 0 → aG v * aG v = 1 := fun v hv =>
    nm_sq_eq_one (haGmem v hv) (haGne v hv) (haGun v hv)
  have haGinv : ∀ v, v ≠ 0 → (aG v)⁻¹ = aG v := fun v hv =>
    inv_eq_of_mul_eq_one_right (haGsq v hv)
  have hD1 : ∀ v, v ≠ 0 → imgZ V H (conjSubgroup (xs v : G) V) =
      (Tt v).map ((projZ V H).comp Φ) := by
    intro v hv
    have hc4 := nm_card_omega hc hV4 hVW (conjSubgroup_mem_omegaOf (hxH v))
    exact nm_imgZ_member hc (hTt v) (htt v) (hysU v hv) (hysW v hv) (hysΦ v hv) hc4.1 hc4.2
  have hR1a : ∀ v w : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 → w ≠ 0 →
      CaseM.spForm v w = 0 → (ys v : G) * aG w = aG w * (ys v : G) := by
    intro v w hv hw hvw
    have hcomm := twl_commute hc ((projZ V H).comp Φ) (hTt v) (hTt w) hvw (hD1 v hv) (hD1 w hw)
    exact hcomm _ (hysU v hv) _ (Subgroup.mem_inf.mp (haGmem w hw)).1
  have hR1b : ∀ v w : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 → w ≠ 0 →
      CaseM.spForm v w ≠ 0 → (ys v : G) * aG w * (ys v : G)⁻¹ = aG v * aG w := by
    intro v w hv hw hvw
    have hyU : (ys v : G) ∈ conjSubgroup (xs v : G) V := hysU v hv
    have hyW : (ys v : G) ∉ wOf V H := hysW v hv
    have hcmem := nm_comm_mem hc (hxH v) (haGW w) hyU
    have hne : aG w * (ys v : G) * (aG w)⁻¹ * (ys v : G)⁻¹ ≠ 1 := by
      intro h1
      have h2 : (aG w) * (ys v : G) * (aG w)⁻¹ = (ys v : G) := by
        calc (aG w) * (ys v : G) * (aG w)⁻¹
            = (aG w * (ys v : G) * (aG w)⁻¹ * (ys v : G)⁻¹) * (ys v : G) := by group
          _ = (ys v : G) := by rw [h1, one_mul]
      have hcomm' : aG w * (ys v : G) = (ys v : G) * aG w := by
        calc aG w * (ys v : G) = (aG w * (ys v : G) * (aG w)⁻¹) * aG w := by group
          _ = (ys v : G) * aG w := by rw [h2]
      exact nm_noCommute hc hdat ((projZ V H).comp Φ) hΦ' hv hw hvw (hTt v) (hTt w)
        (hD1 v hv) (hD1 w hw) hyU hyW (Subgroup.mem_inf.mp (haGmem w hw)).1 (haGne w hw)
        hcomm'.symm
    rcases haGun v hv _ hcmem with h | h
    · exact absurd h hne
    · have i1 : (ys v : G) * (aG w)⁻¹ * (ys v : G)⁻¹ = (aG w)⁻¹ * aG v := by
        calc (ys v : G) * (aG w)⁻¹ * (ys v : G)⁻¹
            = (aG w)⁻¹ * (aG w * (ys v : G) * (aG w)⁻¹ * (ys v : G)⁻¹) := by group
          _ = (aG w)⁻¹ * aG v := by rw [h]
      calc (ys v : G) * aG w * (ys v : G)⁻¹
          = ((ys v : G) * (aG w)⁻¹ * (ys v : G)⁻¹)⁻¹ := by group
        _ = ((aG w)⁻¹ * aG v)⁻¹ := by rw [i1]
        _ = (aG v)⁻¹ * aG w := by group
        _ = aG v * aG w := by rw [haGinv v hv]
  have hpsiW : ∀ z u : Fin n ⊕ Fin n → GaloisField 2 1,
      (if CaseM.spForm z u = 0 then (1 : G) else aG z) ∈ wOf V H := by
    intro z u
    split_ifs
    · exact one_mem _
    · exact haGW z
  have hR1 : ∀ z u : Fin n ⊕ Fin n → GaloisField 2 1, z ≠ 0 →
      (ys z : G) * aG u * (ys z : G)⁻¹ =
        aG u * (if CaseM.spForm z u = 0 then (1 : G) else aG z) := by
    intro z u hz
    by_cases hu : u = 0
    · subst hu
      have h0 : CaseM.spForm z (0 : Fin n ⊕ Fin n → GaloisField 2 1) = 0 := by
        simp [CaseM.spForm]
      simp [haG0, h0]
    by_cases hzu : CaseM.spForm z u = 0
    · rw [if_pos hzu, mul_one, hR1a z u hz hu hzu, mul_assoc, mul_inv_cancel, mul_one]
    · rw [if_neg hzu, hR1b z u hz hu hzu, hWc _ (haGW z) _ (haGW u)]
  have hcover : ∀ U ∈ omegaOf V H, ∃ z : Fin n ⊕ Fin n → GaloisField 2 1,
      z ≠ 0 ∧ conjSubgroup (xs z : G) V = U := by
    intro U hU
    obtain ⟨y, hyU, hyW, hyD⟩ := nm_exists_point hc hU
    obtain ⟨z, hz, t, htm, htΦ⟩ := (nm_dy_iff hc hdat hΦb ha₀ hT₀ hΦT _).mp hyD
    have htz : tt z = t := SpExtras.mat_injective ((htt z).trans htm.symm)
    have hyz : (y : G)⁻¹ * ((ys z : ↥(xOf V H)) : G) ∈ wOf V H := by
      apply nm_mem_W_of_xToXbar_eq hVH
      rw [hysΦ z hz, htz, htΦ]
    exact ⟨z, hz, nm_uniq hMU hH hZ hV4 hVW hU (conjSubgroup_mem_omegaOf (hxH z)) hyU hyW
      (hysU z hz) (hysW z hz) hyz⟩
  have hEconj : ∀ v w z : Fin n ⊕ Fin n → GaloisField 2 1, z ≠ 0 →
      (ys z : G) * (aG (v + w) * aG v * aG w) = (aG (v + w) * aG v * aG w) * (ys z : G) := by
    intro v w z hz
    have hconj : (ys z : G) * (aG (v + w) * aG v * aG w) * (ys z : G)⁻¹ =
        aG (v + w) * aG v * aG w := by
      calc (ys z : G) * (aG (v + w) * aG v * aG w) * (ys z : G)⁻¹
          = ((ys z : G) * aG (v + w) * (ys z : G)⁻¹) * ((ys z : G) * aG v * (ys z : G)⁻¹) *
            ((ys z : G) * aG w * (ys z : G)⁻¹) := by group
        _ = (aG (v + w) * (if CaseM.spForm z (v + w) = 0 then (1 : G) else aG z)) *
            (aG v * (if CaseM.spForm z v = 0 then (1 : G) else aG z)) *
            (aG w * (if CaseM.spForm z w = 0 then (1 : G) else aG z)) := by
          rw [hR1 z (v + w) hz, hR1 z v hz, hR1 z w hz]
        _ = aG (v + w) * aG v * aG w * ((if CaseM.spForm z (v + w) = 0 then (1 : G) else aG z) *
            (if CaseM.spForm z v = 0 then (1 : G) else aG z) *
            (if CaseM.spForm z w = 0 then (1 : G) else aG z)) :=
          nm_comm_six hWc (haGW _) (haGW _) (haGW _) (hpsiW z _) (hpsiW z _) (hpsiW z _)
        _ = aG (v + w) * aG v * aG w := by rw [nm_psi_prod (aG z) (haGsq z hz), mul_one]
    have h3 := (mul_inv_eq_iff_eq_mul.mp hconj)
    exact h3
  have hEone : ∀ E : G, E ∈ wOf V H →
      (∀ z : Fin n ⊕ Fin n → GaloisField 2 1, z ≠ 0 → (ys z : G) * E = E * (ys z : G)) →
        E = 1 := by
    intro E hEW hEy
    have hXK : xOf V H ≤ Subgroup.centralizer ({E} : Set G) := by
      refine iSup₂_le fun U hU => ?_
      intro u hu0
      obtain ⟨z, hz, hUz⟩ := hcover U hU
      rw [← hUz] at hu0
      have hc4 := nm_card_omega hc hV4 hVW (conjSubgroup_mem_omegaOf (hxH z))
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      by_cases huW : u ∈ wOf V H
      · exact hWc E hEW u huW
      · have hw := nm_coset hc4.1 hc4.2 (hysU z hz) hu0 (hysW z hz) huW
        obtain ⟨w, hwdef⟩ : ∃ w, w = (ys z : G)⁻¹ * u := ⟨_, rfl⟩
        rw [← hwdef] at hw
        have hu_eq : u = (ys z : G) * w := by rw [hwdef]; group
        rw [hu_eq]
        calc E * ((ys z : G) * w) = (E * (ys z : G)) * w := by group
          _ = ((ys z : G) * E) * w := by rw [← hEy z hz]
          _ = (ys z : G) * (E * w) := by group
          _ = (ys z : G) * (w * E) := by rw [hWc E hEW w hw]
          _ = (ys z : G) * w * E := by group
    have hmem : E ∈ wOf V H ⊓ Subgroup.centralizer ((xOf V H : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hEW, Subgroup.mem_centralizer_iff.mpr fun x hx =>
        ((Subgroup.mem_centralizer_iff.mp (hXK hx)) E (Set.mem_singleton E)).symm⟩
    rw [hc.wOf_inf_centralizer_xOf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hadd : ∀ v w : Fin n ⊕ Fin n → GaloisField 2 1, aG (v + w) = aG v * aG w := by
    intro v w
    by_cases hv : v = 0
    · rw [hv, zero_add, haG0, one_mul]
    by_cases hw : w = 0
    · rw [hw, add_zero, haG0, mul_one]
    have hE : aG (v + w) * aG v * aG w = 1 :=
      hEone _ (mul_mem (mul_mem (haGW _) (haGW _)) (haGW _)) (fun z hz => hEconj v w z hz)
    have h1 : aG (v + w) * (aG v * aG w) = 1 := by rw [← mul_assoc]; exact hE
    have h2 : aG (v + w) = (aG v * aG w)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, _root_.mul_inv_rev, haGinv w hw, haGinv v hv, hWc _ (haGW w) _ (haGW v)]
  let ψ₀ : (Fin n ⊕ Fin n → GaloisField 2 1) →+ Additive ↥(wOf V H) :=
    AddMonoidHom.mk' (fun v => Additive.ofMul ⟨aG v, haGW v⟩) (fun v w =>
      congrArg Additive.ofMul (Subtype.ext (hadd v w)))
  have hψinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    have h3 : (⟨aG v, haGW v⟩ : ↥(wOf V H)) = 1 := congrArg Additive.toMul hv
    exact haGne v hv0 (congrArg Subtype.val h3)
  let Im : Subgroup G :=
    { carrier := {g | ∃ v, aG v = g}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨v, rfl⟩ := ha
        obtain ⟨w, rfl⟩ := hb
        exact ⟨v + w, hadd v w⟩
      one_mem' := ⟨0, haG0⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨v, rfl⟩ := ha
        by_cases hv : v = 0
        · exact ⟨0, by rw [hv, haG0, inv_one]⟩
        · exact ⟨v, (haGinv v hv).symm⟩ }
  have hWIm : wOf V H ≤ Im := by
    unfold wOf
    refine iSup₂_le fun U hU => ?_
    intro g hg
    obtain ⟨z, hz, hUz⟩ := hcover U hU
    have hgW : g ∈ wOf V H := inf_pCore_le_wOf hU hg
    have hgU : g ∈ conjSubgroup (xs z : G) V := by
      rw [hUz]
      exact (Subgroup.mem_inf.mp hg).1
    rcases haGun z hz g (Subgroup.mem_inf.mpr ⟨hgU, hgW⟩) with h | h
    · rw [h]
      exact one_mem _
    · exact ⟨z, h.symm⟩
  have hψsurj : Function.Surjective ψ₀ := by
    intro w
    obtain ⟨v, hv⟩ := hWIm (Additive.toMul w).2
    refine ⟨v, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext hv
  have hequiv : ∀ (s : ↥(StatedSp n (GaloisField 2 1))) (x : ↥(xOf V H)),
      Φ s = xToXbar hVH x → ∀ v : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 →
        (x : G) * aG v * (x : G)⁻¹ = aG (SpExtras.mat n (GaloisField 2 1) s *ᵥ v) := by
    intro s x hs v hv
    have hxH' : (x : G) ∈ H := xOf_le_H hVH x.2
    have hσv : SpExtras.mat n (GaloisField 2 1) s *ᵥ v ≠ 0 :=
      ModelRank.mat_mulVec_ne_zero' s hv
    have hUΩ : conjSubgroup (xs v : G) V ∈ omegaOf V H := conjSubgroup_mem_omegaOf (hxH v)
    have hgUΩ : conjSubgroup (x : G) (conjSubgroup (xs v : G) V) ∈ omegaOf V H :=
      conjSubgroup_mem_omegaOf_of_mem hUΩ hxH'
    have hUσΩ : conjSubgroup (xs (SpExtras.mat n (GaloisField 2 1) s *ᵥ v) : G) V ∈
        omegaOf V H := conjSubgroup_mem_omegaOf (hxH _)
    have hyX : (x : G) * (ys v : G) * (x : G)⁻¹ ∈ xOf V H :=
      (xOf V H).mul_mem ((xOf V H).mul_mem x.2 (ys v).2) ((xOf V H).inv_mem x.2)
    obtain ⟨Y, hYdef⟩ : ∃ Y : ↥(xOf V H), (Y : G) = (x : G) * (ys v : G) * (x : G)⁻¹ :=
      ⟨⟨_, hyX⟩, rfl⟩
    have hYe : Y = x * ys v * x⁻¹ := Subtype.ext (by rw [hYdef]; simp)
    have hy2W : (Y : G) ∉ wOf V H := fun h => hysW v hv
      ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hxH') (ys v : G)).mpr
        (by rw [← hYdef]; exact h))
    have hy2U : (Y : G) ∈ conjSubgroup (x : G) (conjSubgroup (xs v : G) V) := by
      rw [hYdef, mem_conjSubgroup, show (x : G)⁻¹ * ((x : G) * (ys v : G) * (x : G)⁻¹) *
        (x : G) = (ys v : G) by group]
      exact hysU v hv
    have hts : s * tt v * s⁻¹ = tt (SpExtras.mat n (GaloisField 2 1) s *ᵥ v) := by
      apply SpExtras.mat_injective
      rw [CaseM.mat_conj_of_mat_eq (htt v) s, htt]
    have hΦt : Φ (s * tt v * s⁻¹) = xToXbar hVH Y := by
      rw [hYe]
      simp only [map_mul, map_inv]
      rw [hs, hysΦ v hv]
    have hyy := nm_mem_W_of_xToXbar_eq hVH (a := Y)
      (b := ys (SpExtras.mat n (GaloisField 2 1) s *ᵥ v))
      (by rw [hysΦ _ hσv, ← hts, hΦt])
    have hEqσ := nm_uniq hMU hH hZ hV4 hVW hgUΩ hUσΩ hy2U hy2W (hysU _ hσv) (hysW _ hσv) hyy
    have hmemW : (x : G) * aG v * (x : G)⁻¹ ∈
        conjSubgroup (x : G) (conjSubgroup (xs v : G) V) := by
      rw [mem_conjSubgroup, show (x : G)⁻¹ * ((x : G) * aG v * (x : G)⁻¹) * (x : G) = aG v by
        group]
      exact (Subgroup.mem_inf.mp (haGmem v hv)).1
    have hmemW' : (x : G) * aG v * (x : G)⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hxH') (aG v)).mp (haGW v)
    have hne1 : (x : G) * aG v * (x : G)⁻¹ ≠ 1 := by
      intro h
      apply haGne v hv
      calc aG v = (x : G)⁻¹ * ((x : G) * aG v * (x : G)⁻¹) * (x : G) := by group
        _ = 1 := by rw [h]; group
    rw [← hEqσ] at hmemW
    rcases haGun _ hσv _ (Subgroup.mem_inf.mpr ⟨hmemW, hmemW'⟩) with h | h
    · exact absurd h hne1
    · exact h
  refine ⟨n, MulEquiv.ofBijective Φ hΦb, AddEquiv.ofBijective ψ₀ ⟨hψinj, hψsurj⟩, hn, ?_,
    ⟨a₀, T₀, ha₀, hT₀, hΦT⟩, ?_⟩
  · intro x v
    have hsΦ : Φ ((MulEquiv.ofBijective Φ hΦb).symm (xToXbar hVH x)) = xToXbar hVH x :=
      (MulEquiv.ofBijective Φ hΦb).apply_symm_apply _
    by_cases hv : v = 0
    · subst hv
      simp [haG0]
    · exact (hequiv _ x hsΦ v hv).symm
  · intro a T ha hT hTΦ
    obtain ⟨t, ht⟩ := hT.2 1
    have htT : t ∈ T := (hT.1 t).2 ⟨1, ht⟩
    have ht1 : t ≠ 1 := by
      intro h
      apply twl_spTrans_one_ne_one ha
      rw [← ht, h, map_one]
    have hΦtV : Φ t ∈ Vy V H := by
      rw [← hTΦ]
      exact Subgroup.mem_map_of_mem _ htT
    have hΦt1 : Φ t ≠ 1 := fun h => ht1 (hΦinj (h.trans (map_one Φ).symm))
    have hbar : ((Φ t : Xbar V H) : Hbar V H) ∈ barOf V H V := Subgroup.mem_subgroupOf.mp hΦtV
    obtain ⟨v0, hv0V, hv0⟩ := mem_barOf_iff.mp hbar
    have hv0W : (v0 : G) ∉ wOf V H := by
      intro h
      apply hΦt1
      apply Subtype.ext
      rw [← hv0]
      exact (piBar_eq_one_iff v0).mpr h
    have hv0X : (v0 : G) ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hv0V
    have hpΦ : xToXbar hVH (⟨(v0 : G), hv0X⟩ : ↥(xOf V H)) = Φ t := by
      apply Subtype.ext
      rw [coe_xToXbar]
      exact hv0
    have htt_eq : tt a = t := SpExtras.mat_injective ((htt a).trans ht.symm)
    have hyy := nm_mem_W_of_xToXbar_eq hVH (a := (⟨(v0 : G), hv0X⟩ : ↥(xOf V H)))
      (b := ys a) (by rw [hpΦ, hysΦ a ha, htt_eq])
    have hEqV := nm_uniq hMU hH hZ hV4 hVW (V_mem_omegaOf V H) (conjSubgroup_mem_omegaOf (hxH a))
      hv0V hv0W (hysU a ha) (hysW a ha) hyy
    have hmem := (Subgroup.mem_inf.mp (haGmem a ha)).1
    rw [hEqV] at hmem
    exact hmem

end CFSG.RankThree.GF2n.Tim79a
