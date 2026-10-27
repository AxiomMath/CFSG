module

public import CFSG.Quasithin.MS93.S36SpLin
public import CFSG.Quasithin.MS93.S36SpBase
public import CFSG.Quasithin.MS93.S36Crit

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}

section Basic

variable (h)
include h

theorem tImage_le_M (χ : MulAut ↥T) (K : Subgroup G) : tImage χ K ≤ M :=
  (tImage_le χ K).trans h.le

theorem inf_centralizer_tImage_Z0q (χ : MulAut ↥T) :
    T ⊓ Subgroup.centralizer (tImage χ (Z0q M T) : Set G) = tImage χ (pCoreOf 2 M) := by
  rw [tImage_centralizer χ (S36.Z0q_le_T h), h.centralizer_Z0q]

theorem tImage_pCoreOf_le_centralizer (χ : MulAut ↥T) :
    tImage χ (pCoreOf 2 M) ≤ Subgroup.centralizer (tImage χ (Z0q M T) : Set G) := by
  rw [← inf_centralizer_tImage_Z0q h χ]
  exact inf_le_right

end Basic

structure PairHyp (d : SpFrame h) (χ : MulAut ↥T) : Prop where
  hV : Vq M L ≠ Uq M T L
  hXL : ⁅Xq M, L⁆ ≤ Uq M T L
  crit : ¬ tImage χ (Z0q M T) ≤ pCoreOf 2 M
  crit' : ¬ Z0q M T ≤ tImage χ (pCoreOf 2 M)
  idx : (pCoreOf 2 M).relIndex (tImage χ (Z0q M T)) = 2 ^ d.k
  idx' : (tImage χ (pCoreOf 2 M)).relIndex (Z0q M T) ≤ 2 ^ d.k

structure XData (d : SpFrame h) (E : Subgroup G) (v : V4 d.F) : Prop where
  ne : v ≠ 0
  all : ∀ c : d.F, ∃ e ∈ E, ActsMat d.vec e (transv v c)
  mem : ∀ e ∈ E, ∀ g, ActsMat d.vec e g → ∃ c : d.F, g = transv v c

section Standalone

variable {d : SpFrame h} {χ : MulAut ↥T}

theorem relIndex_centralizer_le_of
    (hidx' : (tImage χ (pCoreOf 2 M)).relIndex (Z0q M T) ≤ 2 ^ d.k) :
    (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L) ≤ 2 ^ d.k :=
  calc (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L)
      ≤ (tImage χ (pCoreOf 2 M)).relIndex (Uq M T L) :=
        Subgroup.relIndex_le_of_le_left (tImage_pCoreOf_le_centralizer h χ)
          Subgroup.index_ne_zero_of_finite
    _ ≤ (tImage χ (pCoreOf 2 M)).relIndex (Z0q M T) :=
        Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.index_ne_zero_of_finite
    _ ≤ 2 ^ d.k := hidx'

theorem actsMat_E_of
    (hidx' : (tImage χ (pCoreOf 2 M)).relIndex (Z0q M T) ≤ 2 ^ d.k) :
    ∀ e ∈ tImage χ (Z0q M T), ∃ g, ActsMat d.vec e g := by
  intro e he
  refine d.exists_actsMat_of_relIndex (tImage_le_M h χ _ he)
    (pow_eq_one_of_mem_T h (tImage_le χ _ he)) ?_
  calc (Subgroup.centralizer ({e} : Set G)).relIndex (Uq M T L)
      ≤ (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L) :=
        Subgroup.relIndex_le_of_le_left
          (Subgroup.centralizer_le (Set.singleton_subset_iff.2 he)) Subgroup.index_ne_zero_of_finite
    _ ≤ 2 ^ d.k := relIndex_centralizer_le_of hidx'

theorem not_tImage_inv_le_of (h : PUHyp M T L) (hcrit' : ¬ Z0q M T ≤ tImage χ (pCoreOf 2 M)) :
    ¬ tImage χ⁻¹ (Z0q M T) ≤ pCoreOf 2 M := by
  intro hle
  apply hcrit'
  have := (tImage_le_iff χ⁻¹ (S36.Z0q_le_T h) h.pCore_le).1 hle
  rwa [inv_inv] at this

theorem not_quadratic_of (hV : Vq M L ≠ Uq M T L) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hcrit' : ¬ Z0q M T ≤ tImage χ (pCoreOf 2 M)) {hPM : tImage χ (pCoreOf 2 M) ≤ M}
    {hP : ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g} :
    ¬ commSp (d.img _ hPM hP) ≤ fixSp (d.img _ hPM hP) := by
  intro hq
  apply hV
  set P := tImage χ (pCoreOf 2 M) with hPdef
  have hPT : P ≤ T := tImage_le χ _
  have hTP : T ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_tImage χ (h.le.trans (le_normalizer_pCoreOf M))
  have hUP : ⁅Uq M T L, P⁆ ≤ tImage χ (Xq M) := by
    rw [Subgroup.commutator_le]
    intro u hu x hx
    obtain ⟨g, hg⟩ := hP x hx
    have hxM : x ∈ M := hPM hx
    have hxu : x * u⁻¹ * x⁻¹ ∈ Uq M T L := conj_mem (d.normU hxM) ⟨u⁻¹, inv_mem hu⟩
    have hwU : ⁅u, x⁆ ∈ Uq M T L := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact mul_mem hu (by simpa [mul_assoc] using hxu)
    have hvec : Multiplicative.toAdd (d.vec ⟨⁅u, x⁆, hwU⟩) ∈ commSp (d.img _ hPM hP) := by
      have h1 := d.toAdd_vec_comm hxM hg ⟨u, hu⟩
      have e1 : (⟨⁅u, x⁆, hwU⟩ : ↥(Uq M T L)) = (⟨x * u * x⁻¹ * u⁻¹,
          mul_mem (conj_mem (d.normU hxM) ⟨u, hu⟩) (inv_mem hu)⟩ : ↥(Uq M T L))⁻¹ := by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_inv]
        group
      rw [e1, map_inv, toAdd_inv, h1]
      exact Submodule.neg_mem _ (sub_mem_commSp (d.actsMat_mem_img hPM hP hx hg) _)
    have hwC : ⁅u, x⁆ ∈ Subgroup.centralizer (P : Set G) :=
      (d.mem_centralizer_iff hPM hP ⟨_, hwU⟩).2 (hq hvec)
    have hwP : ⁅u, x⁆ ∈ P := by
      have hux : u * x * u⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.1 (hTP ((Uq_le_Z0q h.L_le).trans (S36.Z0q_le_T h) hu)) x).1 hx
      rw [commutatorElement_def]
      exact mul_mem hux (inv_mem hx)
    have hw2 : ⁅u, x⁆ ^ 2 = 1 := Sp4L.uq_sq h hwU
    obtain ⟨w, hwQ, hw⟩ := mem_tImage.1 hwP
    refine mem_tImage.2 ⟨w, ?_, hw⟩
    have hwcent : (w : G) ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyT : y ∈ T := h.pCore_le hy
      have h1 := Subgroup.mem_centralizer_iff.1 hwC (χ ⟨y, hyT⟩ : G)
        (apply_mem_tImage χ (t := ⟨y, hyT⟩) hy)
      rw [← hw] at h1
      have h2 : χ (⟨y, hyT⟩ * w) = χ (w * ⟨y, hyT⟩) := Subtype.ext (by simpa using h1)
      exact congrArg Subtype.val (χ.injective h2)
    have hwsq : (w : G) ^ 2 = 1 := by
      have h1 : (χ (w ^ 2) : G) = 1 := by
        rw [map_pow]
        simpa [hw] using hw2
      have h2 : χ (w ^ 2) = χ 1 := Subtype.ext (by rw [h1, map_one]; rfl)
      have := congrArg Subtype.val (χ.injective h2)
      simpa using this
    exact Subgroup.subset_closure ⟨⟨hwQ, hwcent⟩, hwsq⟩
  have hQZ : ⁅pCoreOf 2 M, tImage χ⁻¹ (Z0q M T)⁆ ≤ Xq M := by
    have hKT : ⁅pCoreOf 2 M, tImage χ⁻¹ (Z0q M T)⁆ ≤ T :=
      commutator_le_of_le h.pCore_le (tImage_le _ _)
    refine (tImage_le_tImage_iff χ hKT).1 ?_
    rw [tImage_commutator χ h.pCore_le (tImage_le _ _), tImage_tImage_inv χ (S36.Z0q_le_T h),
      Subgroup.commutator_comm, S33.commutator_Z0q_eq h hPT]
    exact hUP
  exact vq_eq_uq_of_le h (tImage_le _ _) (not_tImage_inv_le_of h hcrit') (Xq_le M)
    (h.le.trans (le_normalizer_Xq M)) hQZ (hXL.trans (Uq_le_Z0q h.L_le))

end Standalone

namespace PairHyp

variable {d : SpFrame h} {χ : MulAut ↥T} (hp : PairHyp d χ)
include hp

theorem relIndex_centralizer_le :
    (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L) ≤ 2 ^ d.k :=
  relIndex_centralizer_le_of hp.idx'

theorem actsMat_E : ∀ e ∈ tImage χ (Z0q M T), ∃ g, ActsMat d.vec e g :=
  actsMat_E_of hp.idx'

theorem exists_xData : ∃ v : V4 d.F, XData d (tImage χ (Z0q M T)) v := by
  have hEM : tImage χ (Z0q M T) ≤ M := tImage_le_M h χ _
  have hE := hp.actsMat_E
  have hcard : Nat.card (d.img _ hEM hE) = 2 ^ d.k := by
    rw [d.card_img hEM hE (tImage_le χ _)]
    exact hp.idx
  have hV4 := d.card_V4_eq hEM hE
  set r := Module.finrank d.F (fixSp (d.img _ hEM hE)) with hr
  have hfix : Nat.card (fixSp (d.img _ hEM hE)) = (2 ^ d.k) ^ r := by
    rw [card_fixSp, d.card_F]
  rw [card_V4, d.card_F, hfix] at hV4
  have hq : 1 < 2 ^ d.k := Nat.one_lt_two_pow (by have := d.one_le; omega)
  have hr3 : 3 ≤ r := by
    have h1 : (2 ^ d.k) ^ 4 ≤ (2 ^ d.k) ^ (r + 1) :=
      calc (2 ^ d.k) ^ 4 = (2 ^ d.k) ^ r *
            (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L) := hV4
        _ ≤ (2 ^ d.k) ^ r * 2 ^ d.k := Nat.mul_le_mul_left _ hp.relIndex_centralizer_le
        _ = (2 ^ d.k) ^ (r + 1) := by rw [pow_succ]
    have := (Nat.pow_le_pow_iff_right hq).1 h1
    omega
  have hr4 : r ≤ 4 := by
    have := Submodule.finrank_le (fixSp (d.img _ hEM hE))
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
  have hr' : r = 3 := by
    rcases (show r = 3 ∨ r = 4 by omega) with h3 | h4
    · exact h3
    · exfalso
      have htop : fixSp (d.img _ hEM hE) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [← hr, h4, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      rw [fixSp_eq_top_iff.1 htop, Subgroup.card_bot] at hcard
      omega
  obtain ⟨p, hp', hEp⟩ := eq_xPoint_of_finrank_fixSp_three hr' (by rw [hcard, d.card_F])
  obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_isPoint hp'
  refine ⟨v, hv, fun c => ?_, fun e he g hg => ?_⟩
  · have : transv v c ∈ d.img _ hEM hE := hEp ▸ (mem_xPoint_span hv).2 ⟨c, rfl⟩
    exact (d.mem_img hEM hE).1 this
  · have hg' : g ∈ d.img _ hEM hE := d.actsMat_mem_img hEM hE he hg
    rw [hEp] at hg'
    obtain ⟨c, hc⟩ := (mem_xPoint_span hv).1 hg'
    exact ⟨c, hc.symm⟩

omit hp in
theorem actsMat_P {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) :
    ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g := by
  intro x hxP
  refine d.exists_actsMat_of_commute (tImage_le_M h χ _ hxP)
    (pow_eq_one_of_mem_T h (tImage_le χ _ hxP)) hx.ne fun c => ?_
  obtain ⟨e, he, heg⟩ := hx.all c
  exact ⟨e, tImage_le_M h χ _ he, heg,
    (Subgroup.mem_centralizer_iff.1 (tImage_pCoreOf_le_centralizer h χ hxP) e he).symm⟩

omit hp in
theorem fix_P {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) {x : G}
    (hxP : x ∈ tImage χ (pCoreOf 2 M)) {g : Sp4 d.F} (hg : ActsMat d.vec x g) :
    mat g *ᵥ v = v := by
  obtain ⟨e, he, het⟩ := hx.all 1
  have heM := tImage_le_M h χ _ he
  have hxM := tImage_le_M h χ _ hxP
  have hxe : x * e = e * x :=
    (Subgroup.mem_centralizer_iff.1 (tImage_pCoreOf_le_centralizer h χ hxP) e he).symm
  have h1 : ActsMat d.vec (x * e) (g * transv v 1) := actsMat_mul (d.normU heM) hg het
  have h2 : ActsMat d.vec (e * x) (transv v 1 * g) := actsMat_mul (d.normU hxM) het hg
  rw [hxe] at h1
  have := actsMat_unique d.surj (d.normU (M.mul_mem heM hxM)) h1 h2
  exact mulVec_eq_of_commute_transv hx.ne this

theorem not_tImage_inv_le : ¬ tImage χ⁻¹ (Z0q M T) ≤ pCoreOf 2 M :=
  not_tImage_inv_le_of h hp.crit'

theorem not_quadratic {hPM : tImage χ (pCoreOf 2 M) ≤ M}
    {hP : ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g} :
    ¬ commSp (d.img _ hPM hP) ≤ fixSp (d.img _ hPM hP) :=
  not_quadratic_of hp.hV hp.hXL hp.crit'

theorem fixSp_P {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v)
    {hPM : tImage χ (pCoreOf 2 M) ≤ M}
    {hP : ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g} :
    fixSp (d.img _ hPM hP) = d.F ∙ v := by
  set H := d.img _ hPM hP with hH
  have hle : d.F ∙ v ≤ fixSp H := by
    rw [Submodule.span_singleton_le_iff_mem, mem_fixSp]
    intro g hg
    obtain ⟨x, hxP, hxg⟩ := (d.mem_img hPM hP).1 hg
    exact fix_P hx hxP hxg
  by_contra hne
  have h2 : 2 ≤ Module.finrank d.F (fixSp H) := by
    have h1 : Module.finrank d.F (d.F ∙ v) = 1 := finrank_span_singleton hx.ne
    have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle (Ne.symm hne))
    omega
  have hH2 : IsPGroup 2 H := d.isPGroup_img hPM hP (tImage_le χ _)
  have hH1 : H ≠ ⊥ := by
    intro hb
    apply hp.not_quadratic (hPM := hPM) (hP := hP)
    rw [← hH, hb, commSp_le_iff]
    intro a ha w
    rw [Subgroup.mem_bot.1 ha, mat_one, Matrix.one_mulVec, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨l, hl, hlfix, hHl⟩ := exists_line_of_two_le_finrank_fixSp hH2 hH1 h2
  exact hp.not_quadratic ((commSp_mono hHl).trans ((commSp_qLine_le hl).trans hlfix))

end PairHyp

end CFSG.Quasithin.MS93.S36SP
