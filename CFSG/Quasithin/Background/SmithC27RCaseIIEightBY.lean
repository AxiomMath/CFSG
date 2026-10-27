module

public import CFSG.Quasithin.Background.SmithC27RCaseIIEightBCore
public import CFSG.Quasithin.Background.SmithC27B51

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

namespace CaseIICtx

variable (C : CaseIICtx R K V 8) (hs : StarHyp R K V)

@[expose] noncomputable def yB8 : Subgroup G :=
  (s3B8.comap (C.phiB8 hs.le_normalizer_V)).map (K ⊔ R).subtype

omit [Finite G] in
theorem mem_yB8_iff {y : G} :
    y ∈ C.yB8 hs ↔ ∃ hy : y ∈ K ⊔ R, C.phiB8 hs.le_normalizer_V ⟨y, hy⟩ ∈ s3B8 := by
  unfold yB8
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

omit [Finite G] in
theorem yB8_le : C.yB8 hs ≤ K ⊔ R := Subgroup.map_subtype_le _

omit [Finite G] in
theorem R_le_yB8 (hR : C.bar R = Subgroup.zpowers (swap 0 1)) : R ≤ C.yB8 hs := by
  intro r hr
  refine (C.mem_yB8_iff hs).2 ⟨Subgroup.mem_sup_right hr, ?_⟩
  have h1 := C.phiB8_mem_bar hs.le_normalizer_V (x := ⟨r, Subgroup.mem_sup_right hr⟩) hr
  rw [hR] at h1
  exact zpowers_swap_le_s3B8 h1

theorem mem_R_of_phiB8 (hR : C.bar R = Subgroup.zpowers (swap 0 1)) {x : ↥(K ⊔ R)}
    (hx : C.phiB8 hs.le_normalizer_V x ∈ Subgroup.zpowers (swap 0 1)) : (x : G) ∈ R := by
  rw [← hR] at hx
  refine C.mem_of_phiB8_mem_bar hs.le_normalizer_V le_sup_right ?_ hx
  rw [C.inf_centralizer_eq_B8 hs]
  exact hs.core

theorem card_ker_phiB8 :
    Nat.card (C.phiB8 hs.le_normalizer_V).ker = Nat.card (pCoreOf 2 (K ⊔ R)) := by
  have hker : (C.phiB8 hs.le_normalizer_V).ker = (pCoreOf 2 (K ⊔ R)).subgroupOf (K ⊔ R) := by
    ext x
    rw [MonoidHom.mem_ker, C.phiB8_eq_one_iff, Subgroup.mem_subgroupOf,
      ← C.inf_centralizer_eq_B8 hs]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [hker]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (K ⊔ R))).toEquiv

theorem card_yB8 : Nat.card (C.yB8 hs) = 6 * Nat.card (pCoreOf 2 (K ⊔ R)) := by
  unfold yB8
  rw [Subgroup.card_map_of_injective (K ⊔ R).subtype_injective,
    card_comap_of_surjective' (C.phiB8_surjective hs.le_normalizer_V), card_s3B8,
    C.card_ker_phiB8 hs]

include hs in
theorem card_R_B8 (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    Nat.card R = 2 * Nat.card (pCoreOf 2 (K ⊔ R)) := by
  have hReq : R = ((Subgroup.zpowers (swap (0 : Fin 8) 1)).comap
      (C.phiB8 hs.le_normalizer_V)).map (K ⊔ R).subtype := by
    ext r
    constructor
    · intro hr
      refine ⟨⟨r, Subgroup.mem_sup_right hr⟩, ?_, rfl⟩
      have h1 := C.phiB8_mem_bar hs.le_normalizer_V (x := ⟨r, Subgroup.mem_sup_right hr⟩) hr
      rwa [hR] at h1
    · rintro ⟨x, hx, rfl⟩
      exact C.mem_R_of_phiB8 hs hR hx
  have h1 : Nat.card R = Nat.card (((Subgroup.zpowers (swap (0 : Fin 8) 1)).comap
      (C.phiB8 hs.le_normalizer_V)).map (K ⊔ R).subtype) := by
    rw [← hReq]
  rw [h1, Subgroup.card_map_of_injective (K ⊔ R).subtype_injective,
    card_comap_of_surjective' (C.phiB8_surjective hs.le_normalizer_V), card_zpowers_swap_B8,
    C.card_ker_phiB8 hs]

theorem isSylowTwoOf_yB8 (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    IsSylowTwoOf R (C.yB8 hs) := by
  refine ⟨C.R_le_yB8 hs hR, hs.pgroup, ?_⟩
  have hidx := (R.subgroupOf (C.yB8 hs)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (C.R_le_yB8 hs hR)).toEquiv,
    C.card_R_B8 hs hR, C.card_yB8 hs] at hidx
  have hQ : 0 < Nat.card (pCoreOf 2 (K ⊔ R)) := Nat.card_pos
  have h3 : (R.subgroupOf (C.yB8 hs)).index = 3 := by
    have : (R.subgroupOf (C.yB8 hs)).index * 2 * Nat.card (pCoreOf 2 (K ⊔ R)) =
        3 * 2 * Nat.card (pCoreOf 2 (K ⊔ R)) := by
      rw [mul_assoc, hidx]
    exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.eq_of_mul_eq_mul_right hQ this)
  rw [h3]
  decide

theorem pCore_le_pCore_yB8 (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 (C.yB8 hs) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hs.core.trans (C.R_le_yB8 hs hR))
    ((C.yB8_le hs).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R))

theorem charTwo_yB8 (hR : C.bar R = Subgroup.zpowers (swap 0 1)) : CharTwo (C.yB8 hs) := by
  have hQY := C.pCore_le_pCore_yB8 hs hR
  have hVQ : V ≤ pCoreOf 2 (K ⊔ R) := C124.le_pCoreOf_of_reduced hs.red
  intro y ⟨hyY, hyC⟩
  have hyV : y ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le (fun v hv => hQY (hVQ hv)) hyC
  have hyQ : y ∈ pCoreOf 2 (K ⊔ R) := by
    rw [← C.inf_centralizer_eq_B8 hs]
    exact ⟨C.yB8_le hs hyY, hyV⟩
  exact hQY hyQ

theorem phiB8_mem_bar_MK (h : Hyp27 H R M K) {z : ↥(K ⊔ R)} (hzM : (z : G) ∈ M)
    (hzA : C.phiB8 hs.le_normalizer_V z ∈ alternatingGroup (Fin 8)) :
    C.phiB8 hs.le_normalizer_V z ∈ C.bar (M ⊓ K) := by
  rw [mem_bar_iff, phiB8_apply, MulEquiv.symm_apply_apply, hs.autOn_inf_M h.R_le_M]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [coe_starB8]
    exact mem_autOn_iff'.2 ⟨⟨z, hs.le_normalizer_V z.2⟩, Subgroup.mem_inf.2 ⟨hzM, z.2⟩, rfl⟩
  · rw [C.mem_K]
    exact hzA

theorem cgsIn_yB8_le (h : Hyp27 H R M K) (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    cgsIn (C.yB8 hs) R ≤ R := by
  have hYH : C.yB8 hs ≤ H := (C.yB8_le hs).trans h.sup_le
  have hle : cgsIn (C.yB8 hs) R ≤ M ⊓ C.yB8 hs :=
    le_inf ((C2Nine.cgsIn_mono_left hYH R).trans h.hyp.cgs) (cgsIn_le _ R)
  refine hle.trans fun y hy => ?_
  obtain ⟨hyM, hyY⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨hyX, hyS⟩ := (C.mem_yB8_iff hs).1 hyY
  by_contra hyR
  have hnot : C.phiB8 hs.le_normalizer_V ⟨y, hyX⟩ ∉ Subgroup.zpowers (swap 0 1) :=
    fun h' => hyR (C.mem_R_of_phiB8 hs hR h')
  obtain ⟨t, htR, -, hφt, -, -, -⟩ := C.exists_t_B8 hs hR
  have hMK := C.bar_MK_B8 h hs hR
  rcases s3B8_cases hyS hnot with hc | hc
  · obtain ⟨hA, hne⟩ := c3B8_facts hc
    have h1 := C.phiB8_mem_bar_MK hs h (z := ⟨y, hyX⟩) hyM hA
    rw [hMK] at h1
    exact hne (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h1).2)
  · set z : ↥(K ⊔ R) := ⟨y, hyX⟩ * ⟨t, Subgroup.mem_sup_right htR⟩ with hzdef
    have hz : C.phiB8 hs.le_normalizer_V z =
        C.phiB8 hs.le_normalizer_V ⟨y, hyX⟩ * swap 0 1 := by
      rw [hzdef, map_mul, hφt]
    rw [← hz] at hc
    obtain ⟨hA, hne⟩ := c3B8_facts hc
    have hzM : (z : G) ∈ M := M.mul_mem hyM (h.R_le_M htR)
    have h1 := C.phiB8_mem_bar_MK hs h hzM hA
    rw [hMK] at h1
    exact hne (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h1).2)

omit [Finite G] in
theorem exists_mem_yB8_not_mem_R (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    ∃ y ∈ C.yB8 hs, y ∉ R := by
  obtain ⟨x, hx⟩ := C.phiB8_surjective hs.le_normalizer_V c3B8
  refine ⟨x, (C.mem_yB8_iff hs).2 ⟨x.2, ?_⟩, fun hxR => ?_⟩
  · show C.phiB8 hs.le_normalizer_V x ∈ s3B8
    rw [hx]
    exact c3B8_mem_s3B8
  · have h1 := C.phiB8_mem_bar hs.le_normalizer_V (x := x) hxR
    rw [hR, hx, mem_zpowers_swap_iff_B8] at h1
    rcases h1 with h1 | h1
    · exact c3B8_ne_one h1
    · exact absurd h1 (by decide)

theorem exists_chi0Block_B8 (hC129 : ASC129Statement G) (h : Hyp27 H R M K)
    (hR : C.bar R = Subgroup.zpowers (swap 0 1)) :
    ∃ L : Subgroup G, IsChi0Block (C.yB8 hs) L := by
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 (C.yB8 hs) R R
    (h.hyp.sqtk.mono ((C.yB8_le hs).trans h.sup_le)) (C.charTwo_yB8 hs hR)
    (C.isSylowTwoOf_yB8 hs hR) (C.cgsIn_yB8_le hs h hR) (C.R_le_yB8 hs hR)
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    obtain ⟨y, hyY, hyR⟩ := C.exists_mem_yB8_not_mem_R hs hR
    obtain ⟨m, hm, x, -, hyx⟩ := hprod y hyY
    have hym : y = m := by simpa using hyx
    exact hyR (hym ▸ hm)
  · exact ⟨Lb ⟨0, hr⟩, (hLb _).1⟩

theorem card_quot_pCore_le_six {L : Subgroup G} (hLY : L ≤ C.yB8 hs) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ K ⊔ R := hLY.trans (C.yB8_le hs)
  set φL : ↥L →* Perm (Fin 8) := (C.phiB8 hs.le_normalizer_V).comp (Subgroup.inclusion hLX)
    with hφL
  have hker : φL.ker ≤ CFSG.pCore 2 ↥L := by
    intro l hl
    have hlC : (l : G) ∈ Subgroup.centralizer (V : Set G) :=
      (C.phiB8_eq_one_iff hs.le_normalizer_V (Subgroup.inclusion hLX l)).1 hl
    have hlQ : (l : G) ∈ pCoreOf 2 (K ⊔ R) := by
      rw [← C.inf_centralizer_eq_B8 hs]
      exact ⟨hLX l.2, hlC⟩
    rw [mem_pCore_iff_mem_pCoreOf]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_left : L ⊓ pCoreOf 2 (K ⊔ R) ≤ L) (fun g hg => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_right) ⟨l.2, hlQ⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R) (hLX hg)⟩
  have hrange : φL.range ≤ s3B8 := by
    rintro _ ⟨l, rfl⟩
    exact ((C.mem_yB8_iff hs).1 (hLY l.2)).2
  calc Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = (CFSG.pCore 2 ↥L).index := rfl
    _ ≤ φL.ker.index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hker)
    _ = Nat.card φL.range := Subgroup.index_ker φL
    _ ≤ Nat.card s3B8 := Subgroup.card_le_of_le hrange
    _ = 6 := card_s3B8

theorem isAltType_three_B8 {L : Subgroup G} (hL : IsChi0Block (C.yB8 hs) L) :
    IsAltType L 3 := by
  have h6 := C.card_quot_pCore_le_six hs hL.1.2.1
  rcases hL.2 with ⟨n, hn, F, _, _, hF, α, hα, hαk, -⟩ | h3 | ⟨α, hα, hαk, -⟩
  · exfalso
    let e := (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_SL_two_pow
      (by rw [Nat.card_eq_fintype_card]; exact hF)] at h6
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h16 : 4 ^ 2 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h60 : 4 * 15 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul (by simpa using h4) (by omega)
    omega
  · exact h3
  · exfalso
    let e := (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h6
    exact absurd h6 (by decide)

end CaseIICtx

end CFSG.Quasithin.SmithC27
