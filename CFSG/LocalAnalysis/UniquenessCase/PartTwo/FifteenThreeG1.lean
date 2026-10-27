module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeLift
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Core

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

private noncomputable def s15_Three_barHom (D : Data G) {W₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil W₀ V) :
    ↥D.M →* ↥(Mbar D.M W₀ V hV) :=
  ((actTil W₀ V hV).comp (Subgroup.inclusion hMs)).codRestrict _
    (fun m => by
      change actTil W₀ V hV ⟨(m : G), hMs m.2⟩ ∈ Mbar D.M W₀ V hV
      exact actTil_mem_barSub W₀ V hV m.2 (hMs m.2))

private theorem s15_Three_barHom_surjective (D : Data G) {W₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil W₀ V) :
    Function.Surjective (s15_Three_barHom D hV hMs) := by
  intro y
  obtain ⟨g, hgM, hgy⟩ := (mem_barSub W₀ V hV D.M y).1 y.2
  refine ⟨⟨(g : G), hgM⟩, Subtype.ext ?_⟩
  show actTil W₀ V hV ⟨(g : G), hMs hgM⟩ = (y : MulAut (Vtil W₀ V hV))
  rw [show actTil W₀ V hV ⟨(g : G), hMs hgM⟩ = actTil W₀ V hV g from
    congrArg (actTil W₀ V hV) (Subtype.ext rfl)]
  exact hgy

private theorem s15_Three_barHom_ker (D : Data G) {W₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil W₀ V) :
    (s15_Three_barHom D hV hMs).ker = (F11.CTilde D.M W₀ V).subgroupOf D.M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer W₀ V))]
  constructor
  · intro hm
    refine ⟨m.2, hMs m.2, ?_⟩
    have h2 := congrArg Subtype.val hm
    change actTil W₀ V hV (Subgroup.inclusion hMs m) = 1 at h2
    rwa [show Subgroup.inclusion hMs m = (⟨(m : G), hMs m.2⟩ : stabTil W₀ V) from
      Subtype.ext rfl] at h2
  · rintro ⟨-, hst, hact⟩
    apply Subtype.ext
    show actTil W₀ V hV ⟨(m : G), hMs m.2⟩ = 1
    rw [show (⟨(m : G), hMs m.2⟩ : stabTil W₀ V) = ⟨(m : G), hst⟩ from Subtype.ext rfl]
    exact hact

private theorem s15_Three_cyclic_quotient {D : Data G} {V₀ V L : Subgroup G}
    (h61 : UC6.R6_1 D) (h : Hyp151 D V₀ V L) (h127 : R127 D)
    {p : ℕ} (hp : p ∈ D.sig) {X : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X)
    [((X ⊓ centralizer (V₀ : Set G)).subgroupOf X).Normal] :
    IsCyclic (↥X ⧸ (X ⊓ centralizer (V₀ : Set G)).subgroupOf X) :=
  ElevenFourteen.eleven_four_one_of_sig D h61 (Hyp125.hyp11 h127 h.hyp125) hp hXM hXp

private theorem s15_Three_inf_centralizer_le_centralizer {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {E : Subgroup G}
    (hEC : E ≤ F11.CTilde D.M V₀ V) (hE : CFSG.Open.IsElemAbelian 3 E) :
    (E ⊓ centralizer (V₀ : Set G)) ≤ centralizer (V : Set G) := by
  intro e he
  have hpf := h.hyp125.pairFacts
  have heE : e ∈ E := he.1
  have he0 : e ∈ centralizer (V₀ : Set G) := he.2
  rw [Subgroup.mem_centralizer_iff]
  intro v hvV
  have hce : e ∈ F11.CElt D.M V₀ v :=
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hEC heE) v)) hvV
  have hcomm : e * v * e⁻¹ * v⁻¹ ∈ V₀ := hce.2.2
  have hq1 : ∀ w ∈ V₀, e * w * e⁻¹ = w := by
    intro w hw
    have h1 : w * e = e * w := (Subgroup.mem_centralizer_iff.1 he0) w hw
    rw [← h1]
    group
  have hq3 : ∃ n : ℕ, e ^ (3 ^ n) = 1 := ⟨1, by simpa using hE.2 e heE⟩
  have hfix := s15_Three_cocycle_fixes hV hpf.le hq1 hq3 hcomm
  have hev : e * v = v * e := by
    calc e * v = (e * v * e⁻¹) * e := by group
      _ = v * e := by rw [hfix]
  exact hev.symm

private theorem s15_Three_not_three_sig_core_gap {D : Data G} {V₀ V L K₀ : Subgroup G}
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D) (h1111 : R1111_153 D)
    (hAut : RAutRank153) (hAbs : RAbsIrr153) (hT : RTable137) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hshape : s15Shape D V₀ V hV L K₀) (hrs : s15Rs D V₀ V hV L K₀ = 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) (hbig : 2 < mSub V₀) (h3 : 3 ∈ D.sig)
    {E : Subgroup G} (hEC : E ≤ F11.CTilde D.M V₀ V) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) (hne : E ⊓ centralizer (V₀ : Set G) ≠ ⊥)
    (hcentV : (E ⊓ centralizer (V₀ : Set G)) ≤ centralizer (V : Set G))
    (hnotin : ¬ E ≤ centralizer (V₀ : Set G))
    (hCV : CFSG.Open.pRank 3 (D.M ⊓ centralizer (V : Set G)) ≤ 1) :
    ∀ v ∈ V, v ≠ 1 → ¬ E ≤ centralizer ({v} : Set G) →
      1 < CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  intro v hvV hv1 hEv

  have hV0ne : V₀ ≠ ⊥ := by
    intro h0
    rw [h0, show mSub (⊥ : Subgroup G) = 0 from rk_bot] at hbig
    omega
  have hv1 : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV0ne

  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀

  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp125
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  have h3le : 3 ≤ CFSG.Open.pRank 3 D.M := by
    have := (h1111 V₀ V hH11 3 h3).2
    omega
  obtain ⟨E27, hE27M, hE27el, hE27card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := D.M) (k := 3) h3le

  haveI : IsMulCommutative ↥E27 := hE27el.1
  have hcyc := s15_Three_cyclic_quotient h61 h h127 h3 hE27M hE27el.isPGroup
  have hexp : ∀ q : ↥E27 ⧸ (E27 ⊓ centralizer (V₀ : Set G)).subgroupOf E27, q ^ 3 = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hE27el.2 (x : G) x.2
    calc (QuotientGroup.mk' _ x) ^ 3 = QuotientGroup.mk' _ (x ^ 3) := (map_pow _ x 3).symm
      _ = QuotientGroup.mk' _ (1 : ↥E27) := by rw [hx3]
      _ = 1 := map_one _
  have hqle : Nat.card (↥E27 ⧸ (E27 ⊓ centralizer (V₀ : Set G)).subgroupOf E27) ≤ 3 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α :=
      ↥E27 ⧸ (E27 ⊓ centralizer (V₀ : Set G)).subgroupOf E27)
    have h3dvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp g)
    rw [← hg]
    exact Nat.le_of_dvd (by norm_num) h3dvd
  have hcardabs := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((E27 ⊓ centralizer (V₀ : Set G)).subgroupOf E27)
  have hcard_s : Nat.card ((E27 ⊓ centralizer (V₀ : Set G)).subgroupOf E27) =
      Nat.card ↥(E27 ⊓ centralizer (V₀ : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : E27 ⊓ centralizer (V₀ : Set G) ≤ E27)).toEquiv
  have h9 : 9 ≤ Nat.card ↥(E27 ⊓ centralizer (V₀ : Set G)) := by
    set q := Nat.card (↥E27 ⧸ (E27 ⊓ centralizer (V₀ : Set G)).subgroupOf E27) with hqdef
    have h27 : 27 = q * Nat.card ↥(E27 ⊓ centralizer (V₀ : Set G)) := by
      rw [hcard_s, hE27card] at hcardabs
      rw [hqdef]; exact hcardabs
    have hqdvd : q ∣ 27 := ⟨_, h27⟩
    have hqle' : q ≤ 3 := by rw [hqdef]; exact hqle
    have hqpos : 1 ≤ q := by rw [hqdef]; exact Nat.card_pos
    interval_cases q <;> norm_num at hqdvd <;> omega
  have hE0el : IsElemAbelian 3 (E27 ⊓ centralizer (V₀ : Set G)) :=
    CFSG.Open.IsElemAbelian.mono hE27el
      (inf_le_left : E27 ⊓ centralizer (V₀ : Set G) ≤ E27)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE0el.isPGroup
  have hk2 : 2 ≤ k := by
    have hpow : 3 ^ 2 ≤ 3 ^ k := by rw [← hk]; exact h9
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hpow
  obtain ⟨X, hXle, hXel, hXcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card Nat.prime_three hE0el hk2 hk
  have hXM : X ≤ D.M := (hXle.trans inf_le_left).trans hE27M
  have hXleC : X ≤ centralizer (V₀ : Set G) := hXle.trans inf_le_right

  have hXNCV : X ⊓ F11.CTilde D.M V₀ V ≤ centralizer (V : Set G) := by
    have hEl : IsElemAbelian 3 (X ⊓ F11.CTilde D.M V₀ V) :=
      CFSG.Open.IsElemAbelian.mono hXel
        (inf_le_left : X ⊓ F11.CTilde D.M V₀ V ≤ X)
    have h := s15_Three_inf_centralizer_le_centralizer h hV inf_le_right hEl
    rwa [inf_eq_left.2 (le_trans inf_le_left hXleC)] at h
  have hXNelem : IsElemAbelian 3 (X ⊓ F11.CTilde D.M V₀ V) :=
    CFSG.Open.IsElemAbelian.mono hXel
      (inf_le_left : X ⊓ F11.CTilde D.M V₀ V ≤ X)
  have hpXN : CFSG.Open.pRank 3 (X ⊓ F11.CTilde D.M V₀ V) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
      (le_inf (le_trans inf_le_left hXM) hXNCV)).trans hCV
  have hcardXN : Nat.card ↥(X ⊓ F11.CTilde D.M V₀ V) ≤ 3 := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hXNelem.isPGroup
    have hjle : j ≤ 1 := by
      have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hXNelem hj
      omega
    rw [hj]
    interval_cases j <;> norm_num

  have hMs₁ : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  let φ₀ := s15_Three_barHom D hV hMs
  let φ₁ := s15_Three_barHom D hV hMs₁
  have hφ₀ : Function.Surjective φ₀ := s15_Three_barHom_surjective D hV hMs
  have hφ₁ : Function.Surjective φ₁ := s15_Three_barHom_surjective D hV hMs₁
  have hker₀ : φ₀.ker = (F11.CTilde D.M V₀ V).subgroupOf D.M :=
    s15_Three_barHom_ker D hV hMs
  have hker₁ : φ₁.ker = (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V).subgroupOf D.M :=
    s15_Three_barHom_ker D hV hMs₁
  have hker_eq : φ₀.ker = φ₁.ker := by
    rw [hker₀, hker₁, fifteen_two_cent D h1217 h hV]
  let e : ↥(Mbar D.M V₀ V hV) ≃* ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ₀ hφ₀).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ₁ hφ₁))
  have hbar₀ : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ≤ 1 :=
    (s15_Three_rank_ListTwo hAut hAbs D h1217 h hV hL hs hperf hL2).1 3
      Nat.prime_three (by norm_num)
  have hbar₁ : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) ≤ 1 := by
    have hΩ : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(Mbar D.M V₀ V hV),
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3
          ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)]
      exact CFSG.pRank_congr_of_mulEquiv e 3
    rw [← hΩ]; exact hbar₀
  have hconj3 := s15_Three_conj_order_three (H := ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) hbar₁

  have hV2 : ∀ w : vStar D.M V₀ V hV L, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
  have hwstar : wStar D.M V₀ V hV L = ⊤ := s15_Three_wStar_eq_top D h1217 h hV hL hs
  by_cases hv0 : v ∈ V₀
  ·
    have hle : X ≤ D.M ⊓ centralizer ({v} : Set G) := by
      refine le_inf hXM fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.1 (hXleC hx)) v hv0).symm
    have h2 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hle hXel hXcard
    omega
  ·
    let z : vStar D.M V₀ V hV L :=
      mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hvV⟩)
    have hzdef : z = mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨v, hvV⟩) := rfl
    have hzW : z ∈ wStar D.M V₀ V hV L := by
      rw [hwstar]; exact Subgroup.mem_top z
    have hrank : 1 ≤ CFSG.Open.pRank 3
        (lStar D.M V₀ V hV L ⊓
          MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z) :=
      (hT (vStar D.M V₀ V hV L) hV2 (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)
        ↥(lBar V₀ V hV L) hperf).1 z hzW
    obtain ⟨Y, hYle, hYel, hYcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
        (H := lStar D.M V₀ V hV L ⊓
          MulAction.stabilizer (MulAut (vStar D.M V₀ V hV L)) z) (k := 1) hrank
    have hYleM : Y ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
      (hYle.trans inf_le_left).trans (barSub_mono (v1Sub D.M V₀ V hV L) V hV h.le)
    let YH : Subgroup ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
      Y.subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
    have hYHel : IsElemAbelian 3 YH := CFSG.SectionRank.isElemAbelian_subgroupOf hYel _
    have hYHcard : Nat.card YH = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleM).toEquiv, hYcard]
      norm_num
    have hφ₁_apply : ∀ x : ↥D.M,
        ((φ₁ x : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
            MulAut (vStar D.M V₀ V hV L)) =
          actTil (v1Sub D.M V₀ V hV L) V hV ⟨(x : G), hMs₁ x.2⟩ := fun _ => rfl
    have hXel_sub : IsElemAbelian 3 (X.subgroupOf D.M) :=
      CFSG.Open.IsElemAbelian.subgroupOf hXel _
    have hEq : Nat.card (X.subgroupOf D.M) = 3 * 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hXcard]
      norm_num
    have hEN : Nat.card ↥((X.subgroupOf D.M) ⊓ φ₁.ker) ≤ 3 := by
      rw [hker₁, fifteen_two_cent D h1217 h hV]
      have hmap : (((X.subgroupOf D.M) ⊓
          (F11.CTilde D.M V₀ V).subgroupOf D.M).map D.M.subtype) =
          X ⊓ F11.CTilde D.M V₀ V := by
        ext g
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
          exact Subgroup.mem_inf.2
            ⟨Subgroup.mem_subgroupOf.1 hy1, Subgroup.mem_subgroupOf.1 hy2⟩
        · intro hg
          exact ⟨⟨(g : G), hXM hg.1⟩, Subgroup.mem_inf.2
            ⟨Subgroup.mem_subgroupOf.2 hg.1, Subgroup.mem_subgroupOf.2 hg.2⟩, rfl⟩
      rw [← Subgroup.card_map_of_injective (f := D.M.subtype) D.M.subtype_injective, hmap]
      exact hcardXN
    obtain ⟨F, m, hFel, hFcard, hFYH, hFE⟩ :=
      s15_Three_lift_nine (φ := φ₁) hφ₁ (E := X.subgroupOf D.M) hXel_sub hEq hEN
        (q := 3) hconj3.1 hconj3.2 (Y := YH) hYHel hYHcard
    have hXR : X ≤ D.M ⊓ centralizer (V₀ : Set G) := le_inf hXM hXleC
    have hconjXR : (X.subgroupOf D.M).map (MulAut.conj m).toMonoidHom ≤
        (D.M ⊓ centralizer (V₀ : Set G)).subgroupOf D.M := by
      intro y hy
      obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_subgroupOf.2 ?_
      have hxR : ((x : ↥D.M) : G) ∈ D.M ⊓ centralizer (V₀ : Set G) :=
        hXR (Subgroup.mem_subgroupOf.1 hxX)
      obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hxR
      refine Subgroup.mem_inf.2 ⟨D.M.mul_mem (D.M.mul_mem m.2 hxM) (D.M.inv_mem m.2), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro w hw
      have hm0 : (m : G) ∈ normalizer (V₀ : Set G) :=
        h.hyp125.pairFacts.le_normalizer₀ m.2
      have hw' : (m : G)⁻¹ * w * (m : G) ∈ V₀ :=
        (Subgroup.mem_normalizer_iff''.1 hm0 w).1 hw
      have h1 := hxC ((m : G)⁻¹ * w * (m : G)) hw'
      calc w * ((m : G) * ((x : ↥D.M) : G) * (m : G)⁻¹)
          = (m : G) * (((m : G)⁻¹ * w * (m : G)) * ((x : ↥D.M) : G)) * (m : G)⁻¹ := by
            group
        _ = (m : G) * (((x : ↥D.M) : G) * ((m : G)⁻¹ * w * (m : G))) * (m : G)⁻¹ := by
            rw [h1]
        _ = ((m : G) * ((x : ↥D.M) : G) * (m : G)⁻¹) * w := by group
    have hFR : F ≤ (D.M ⊓ centralizer (V₀ : Set G)).subgroupOf D.M := hFE.trans hconjXR
    have hfixf : ∀ f ∈ F, ((f : ↥D.M) : G) ∈ centralizer ({v} : Set G) := by
      intro f hf
      have hfR : ((f : ↥D.M) : G) ∈ D.M ⊓ centralizer (V₀ : Set G) :=
        Subgroup.mem_subgroupOf.1 (hFR hf)
      have hfC : ((f : ↥D.M) : G) ∈ centralizer (V₀ : Set G) := (Subgroup.mem_inf.1 hfR).2
      have hf3 : ((f : ↥D.M) : G) ^ 3 = 1 := by
        have h := hFel.2 f hf
        simpa using congrArg (fun z : ↥D.M => (z : G)) h
      have hYHf : (φ₁ f : MulAut (vStar D.M V₀ V hV L)) ∈ Y :=
        Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 (hFYH hf))
      have hzfix : (φ₁ f : MulAut (vStar D.M V₀ V hV L)) z = z :=
        MulAction.mem_stabilizer_iff.1 ((hYle hYHf).2)
      have h1 : actTil (v1Sub D.M V₀ V hV L) V hV
          ⟨((f : ↥D.M) : G), hMs₁ f.2⟩ z = z := by
        rw [← hφ₁_apply f]; exact hzfix
      rw [hzdef, actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
      have hq1 : ∀ w ∈ v1Sub D.M V₀ V hV L,
          ((f : ↥D.M) : G) * w * ((f : ↥D.M) : G)⁻¹ = w := by
        intro w hw
        have hw₀ : w ∈ V₀ := by rwa [hv1] at hw
        have h1 := (Subgroup.mem_centralizer_iff.1 hfC) w hw₀
        rw [← h1]; group
      have hq3 : ∃ n, ((f : ↥D.M) : G) ^ (3 ^ n) = 1 := ⟨1, by simpa using hf3⟩
      have hfixv : ((f : ↥D.M) : G) * v * ((f : ↥D.M) : G)⁻¹ = v :=
        s15_Three_cocycle_fixes hV (s15_Infra_v1Sub_le h.hyp125 hV) hq1 hq3 h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((f : ↥D.M) : G) * v
          = (((f : ↥D.M) : G) * v * ((f : ↥D.M) : G)⁻¹) * ((f : ↥D.M) : G) := by group
        _ = v * ((f : ↥D.M) : G) := by rw [hfixv]
    have hle : F.map D.M.subtype ≤ D.M ⊓ centralizer ({v} : Set G) := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hg
      exact Subgroup.mem_inf.2 ⟨f.2, hfixf f hf⟩
    have hFel_map : IsElemAbelian 3 (F.map D.M.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hFel D.M.subtype
    have hFcard_map : Nat.card (F.map D.M.subtype) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective D.M.subtype_injective, hFcard]; norm_num
    have h2 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hle hFel_map hFcard_map
    omega

theorem s15_Three_not_three_sig_core {D : Data G} {V₀ V L K₀ : Subgroup G}
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h127 : R127 D) (h1111 : R1111_153 D)
    (hAut : RAutRank153) (hAbs : RAbsIrr153) (hT : RTable137) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hshape : s15Shape D V₀ V hV L K₀) (hrs : s15Rs D V₀ V hV L K₀ = 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) (hbig : 2 < mSub V₀) (h3 : 3 ∈ D.sig)
    {E : Subgroup G} (hEC : E ≤ F11.CTilde D.M V₀ V) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) (hne : E ⊓ centralizer (V₀ : Set G) ≠ ⊥)
    (hcentV : (E ⊓ centralizer (V₀ : Set G)) ≤ centralizer (V : Set G))
    (hnotin : ¬ E ≤ centralizer (V₀ : Set G)) : s15O1a D V := by
  intro v hv hv1
  by_cases hEv : E ≤ centralizer ({v} : Set G)
  · have hEM : E ≤ D.M := hEC.trans (uc22p22q_ctilde_le (M := D.M) (V₀ := V₀) (V := V))
    have hle : E ≤ D.M ⊓ centralizer ({v} : Set G) := le_inf hEM hEv
    have h2 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hle hE hEcard
    omega
  · by_cases hCV : 2 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer (V : Set G))
    · have hleCV : D.M ⊓ centralizer (V : Set G) ≤ D.M ⊓ centralizer ({v} : Set G) := by
        refine le_inf inf_le_left fun x hx => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.1 hx.2) v hv).symm
      have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hleCV
      omega
    · exact s15_Three_not_three_sig_core_gap h61 h63 h127 h1111 hAut hAbs hT h1217 h hV hL
        hshape hrs hs hperf hL2 hbig h3 hEC hE hEcard hne hcentV hnotin (by omega) v hv hv1 hEv

end Core

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
