module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FifteenOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c15t_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil ⊥ V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

private theorem s16c15t_fixV_barSub {W V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW : W ≤ stabTil ⊥ V) :
    fixV (barSub ⊥ V hV W) = imgTil ⊥ V hV (V ⊓ centralizer (W : Set G)) := by
  ext q
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
  rw [mem_fixV, mem_imgTil]
  constructor
  · intro h
    refine ⟨x, ⟨x.val_mem, ?_⟩, rfl⟩
    show ∀ m ∈ (W : Set G), m * x.val = x.val * m
    intro m hm
    have hms : m ∈ stabTil ⊥ V := hW hm
    have hfix := h (actTil ⊥ V hV ⟨m, hms⟩) (actTil_mem_barSub ⊥ V hV hm hms)
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot] at hfix
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hfix)
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := s16c15t_mkTil_bot_injective hV hyx
    rw [hyx'] at hy
    have hyC : x.val ∈ centralizer (W : Set G) := (Subgroup.mem_inf.1 hy).2
    intro φ hφ
    obtain ⟨m, hm, rfl⟩ := (mem_barSub ⊥ V hV W φ).1 hφ
    rw [actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    exact mul_inv_eq_iff_eq_mul.2 ((Subgroup.mem_centralizer_iff.1 hyC) m hm)

private theorem s16c15t_rkIdx_fixV_barSub {W V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW : W ≤ stabTil ⊥ V) :
    rkIdx (fixV (barSub ⊥ V hV W)) = E3.mQuot V (V ⊓ centralizer (W : Set G)) := by
  rw [s16c15t_fixV_barSub hV hW]
  have htop : imgTil ⊥ V hV V = ⊤ := by
    rw [← imgTil_preTil ⊥ V hV ⊤, preTil_top]
  have hmq := s16c167_mQuot_imgTil hV (I := V) (C := V ⊓ centralizer (W : Set G))
    le_rfl inf_le_left
  rw [← hmq, htop]
  unfold E3.mQuot rkIdx
  rw [Subgroup.relIndex_top_right]

theorem s16c15t_bridge (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) {A : Subgroup G} (hA : Choice1613 D ⊥ V hV L A) {g : G}
    (hAg : A ≤ conjSubgroup V g) (hVg : V ≤ conjSubgroup D.M g)
    (hrk : rk ↥(barSub ⊥ V hV A) ≤ 2) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V hV)), E ≤ Mbar D.M ⊥ V hV ∧ IsElemAbelian2 E ∧
      rkIdx (fixV E) ≤ D.k + 2 ∧
      E3.mQuot V (V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) = rk ↥E := by
  have hh : Hyp125 D ⊥ V := hC.setting.hyp16.hyp125
  have hP := hh.pairFacts
  have hAgs : A ∈ E3.gammaSet V D.k D.T := by
    unfold Choice1613 at hA
    exact hA.1
  have hAT : A ≤ D.T := (E3.mem_gammaSet_iff.1 hAgs).1
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hV'M : conjSubgroup V g⁻¹ ≤ D.M := by
    intro x hx
    have hxV : g⁻¹ * x * g ∈ V := E3.mem_conjSubgroup_inv_iff.1 hx
    have hxVg : g⁻¹ * x * g ∈ conjSubgroup D.M g := hVg hxV
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 hxVg
    simpa [mul_assoc] using h2
  have hV'st : conjSubgroup V g⁻¹ ≤ stabTil ⊥ V :=
    hV'M.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hV'ab : IsElemAbelian 2 (conjSubgroup V g⁻¹) := E3.isElemAbelian_conjSubgroup hV g⁻¹
  refine ⟨barSub ⊥ V hV (conjSubgroup V g⁻¹), barSub_mono ⊥ V hV hV'M, ?_, ?_, ?_⟩
  ·
    constructor
    · intro a ha b hb
      obtain ⟨m, hm, rfl⟩ := (mem_barSub ⊥ V hV (conjSubgroup V g⁻¹) a).1 ha
      obtain ⟨n, hn, rfl⟩ := (mem_barSub ⊥ V hV (conjSubgroup V g⁻¹) b).1 hb
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact B2F.isElemAbelian_comm hV'ab hm hn
    · intro a ha
      obtain ⟨m, hm, rfl⟩ := (mem_barSub ⊥ V hV (conjSubgroup V g⁻¹) a).1 ha
      have hm2 : m ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hV'ab.2 (m : G) hm
      rw [← map_pow, hm2, map_one]
  ·
    rw [s16c15t_rkIdx_fixV_barSub hV hV'st]
    have hconj : E3.mQuot V (V ⊓ centralizer (conjSubgroup V g⁻¹ : Set G)) =
        E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer (V : Set G)) := by
      have hc := E3.mQuot_conjSubgroup V (V ⊓ centralizer (conjSubgroup V g⁻¹ : Set G)) g
      rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, E3.conjSubgroup_inv_conj] at hc
      exact hc.symm
    rw [hconj]
    have hmQ : E3.mQuot (conjSubgroup V g) A = D.k := mQuot_eq_of_mem_gammaSet hAgs hAg
    have hCA : A ⊓ centralizer (V : Set G) ≤ A := inf_le_left
    have hCV : A ⊓ centralizer (V : Set G) ≤ conjSubgroup V g ⊓ centralizer (V : Set G) :=
      inf_le_inf_right _ hAg
    have hm : E3.mQuot (conjSubgroup V g) (A ⊓ centralizer (V : Set G)) ≤ D.k + 2 := by
      rw [E3.mQuot_add hCA hAg, hmQ, ← s16c167_rk_barSub_eq_mQuot hV hAst]
      omega
    exact (E3.mQuot_mono hCV).trans hm
  ·
    have hconj : E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) =
        E3.mQuot (conjSubgroup V g⁻¹) (conjSubgroup V g⁻¹ ⊓ centralizer (V : Set G)) := by
      have hc := E3.mQuot_conjSubgroup (conjSubgroup V g⁻¹)
        (conjSubgroup V g⁻¹ ⊓ centralizer (V : Set G)) g
      rw [E3.conjSubgroup_inv_conj, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
        E3.conjSubgroup_inv_conj] at hc
      exact hc
    rw [hconj]
    exact (s16c167_rk_barSub_eq_mQuot hV hV'st).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
