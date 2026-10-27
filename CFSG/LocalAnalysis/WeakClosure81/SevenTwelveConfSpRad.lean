module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpElt
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.CTP

variable {k : ℕ} {F : Type} [Field F]

@[expose] noncomputable def spConfRad (e : Fin k ⊕ Fin k → F) : Subgroup ↥(StatedSp k F) where
  carrier := {g | spEnd g e = e ∧ ∀ v, spForm k F v e = 0 → ∃ a : F, spEnd g v = v + a • e}
  mul_mem' := by
    rintro g h ⟨hge, hg⟩ ⟨hhe, hh⟩
    refine ⟨by rw [spEnd_mul, Module.End.mul_apply, hhe, hge], fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hh v hv
    obtain ⟨b, hb⟩ := hg v hv
    refine ⟨b + a, ?_⟩
    rw [spEnd_mul, Module.End.mul_apply, ha, map_add, map_smul, hge, hb]
    module
  one_mem' :=
    ⟨by rw [spEnd_one, Module.End.one_apply], fun v _ =>
      ⟨0, by rw [spEnd_one, Module.End.one_apply, zero_smul, add_zero]⟩⟩
  inv_mem' := by
    rintro g ⟨hge, hg⟩
    have hge' : spEnd g⁻¹ e = e := by
      conv_lhs => rw [← hge]
      rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
    refine ⟨hge', fun v hv => ?_⟩
    have hw : spForm k F (spEnd g⁻¹ v) e = 0 := by
      have h := spEnd_isometry g (spEnd g⁻¹ v) e
      rw [hge, spEnd_spEnd_inv] at h
      rw [← h, hv]
    obtain ⟨a, ha⟩ := hg (spEnd g⁻¹ v) hw
    rw [spEnd_spEnd_inv] at ha
    have h2 : spEnd g⁻¹ v = v - a • e := by
      rw [eq_sub_iff_add_eq]
      exact ha.symm
    exact ⟨-a, by rw [h2]; module⟩

private theorem spConfRad_ext {g h : ↥(StatedSp k F)} (hh : spEnd g = spEnd h) : g = h :=
  spLin_injective (Units.ext hh)

private theorem spConfRad_add_self [CharP F 2] (x : Fin k ⊕ Fin k → F) : x + x = 0 := by
  rw [← two_smul F x, CharTwo.two_eq_zero, zero_smul]

private theorem spConfRad_form_f_e [CharP F 2] {e f : Fin k ⊕ Fin k → F}
    (hef : spForm k F e f = 1) : spForm k F f e = 1 := by
  have h := (spForm_isAlt (r := k) (K := F)).neg_eq e f
  rw [hef, CharTwo.neg_eq] at h
  exact h.symm

private theorem spConfRad_form_e_of_form_e {e v : Fin k ⊕ Fin k → F}
    (hv : spForm k F v e = 0) : spForm k F e v = 0 := by
  have h := (spForm_isAlt (r := k) (K := F)).neg_eq v e
  rw [hv, neg_zero] at h
  exact h.symm

private theorem spConfRad_pow_four [CharP F 2] {e : Fin k ⊕ Fin k → F}
    {g : ↥(StatedSp k F)} (hg : g ∈ spConfRad e) : g ^ 4 = 1 := by
  have hge : spEnd g e = e := hg.1
  have hg2 := hg.2
  set A : Module.End F (Fin k ⊕ Fin k → F) := spEnd g - 1 with hA
  have hAe : A e = 0 := by
    simp only [hA, LinearMap.sub_apply, Module.End.one_apply, hge, sub_self]
  have hAorth : ∀ v, spForm k F (A v) e = 0 := by
    intro v
    have h : spForm k F (spEnd g v) e = spForm k F v e := by
      conv_lhs => rw [← hge]
      rw [spEnd_isometry]
    simp only [hA, LinearMap.sub_apply, Module.End.one_apply, map_sub, h, sub_self]
  have hA2 : ∀ v, ∃ a : F, A (A v) = a • e := by
    intro v
    obtain ⟨a, ha⟩ := hg2 (A v) (hAorth v)
    refine ⟨a, ?_⟩
    have h1 : A (A v) = spEnd g (A v) - A v := by
      simp only [hA, LinearMap.sub_apply, Module.End.one_apply]
    rw [h1, ha, add_sub_cancel_left]
  have hA3 : ∀ v, A (A (A v)) = 0 := by
    intro v
    obtain ⟨a, ha⟩ := hA2 v
    rw [ha, map_smul, hAe, smul_zero]
  have hsq : ∀ w, spEnd (g ^ 2) w = w + A (A w) := by
    intro w
    have hgw : spEnd g w = w + A w := by
      have h1 : A w = spEnd g w - w := by
        simp only [hA, LinearMap.sub_apply, Module.End.one_apply]
      rw [h1]; abel
    have hgw' : spEnd g (A w) = A w + A (A w) := by
      have h1 : A (A w) = spEnd g (A w) - A w := by
        simp only [hA, LinearMap.sub_apply, Module.End.one_apply]
      rw [h1]; abel
    rw [pow_two, spEnd_mul, Module.End.mul_apply]
    rw [hgw, map_add, hgw, hgw']
    rw [add_assoc w (A w) (A w + A (A w)), ← add_assoc (A w) (A w) (A (A w)),
      spConfRad_add_self (A w), zero_add]
  apply spConfRad_ext
  apply LinearMap.ext
  intro v
  rw [spEnd_one, Module.End.one_apply]
  have hp : (g : ↥(StatedSp k F)) ^ 4 = (g ^ 2) ^ 2 := pow_mul g 2 2
  rw [hp, pow_two, spEnd_mul, Module.End.mul_apply, hsq (spEnd (g ^ 2) v), hsq v,
    map_add, map_add, hA3 (A v), add_zero, add_assoc v (A (A v)) (A (A v)),
    spConfRad_add_self (A (A v)), add_zero]

variable (e : Fin k ⊕ Fin k → F)

theorem isPGroup_spConfRad [CharP F 2] : IsPGroup 2 (spConfRad e) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  refine ⟨2, ?_⟩
  rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
  exact Subtype.ext (by simpa using spConfRad_pow_four x.2)

theorem spTransvection_mem_spConfRad (a s : F) : spTransvection (a • e) s ∈ spConfRad e := by
  have hee : spForm k F e e = 0 := (spForm_isAlt (r := k) (K := F)).self_eq_zero e
  have hBe : spForm k F e (a • e) = 0 := by rw [map_smul, hee, smul_zero]
  refine ⟨?_, fun v hv => ⟨0, ?_⟩⟩
  · rw [spEnd_spTransvection, hBe, mul_zero, zero_smul, add_zero]
  · have hv' : spForm k F v (a • e) = 0 := by rw [map_smul, hv, smul_zero]
    rw [spEnd_spTransvection, hv', mul_zero, zero_smul, add_zero, zero_smul, add_zero]

theorem commute_spConfT_of_mem_spConfRad {g : ↥(StatedSp k F)} (hg : g ∈ spConfRad e) :
    g * spConfT e = spConfT e * g := by
  have h := commute_spTransvection (x := g) (u := e) hg.1 1
  show g * spTransvection e 1 = spTransvection e 1 * g
  exact h.symm

private theorem spConfRad_inv_smul {e : Fin k ⊕ Fin k → F} {g : ↥(StatedSp k F)} {a : F}
    (ha : a ≠ 0) (hg : spEnd g e = a • e) : spEnd g⁻¹ e = a⁻¹ • e := by
  have hcomp : spEnd g⁻¹ (spEnd g e) = e := by
    have h := spEnd_spEnd_inv g⁻¹ e
    simpa using h
  calc spEnd g⁻¹ e = spEnd g⁻¹ (a⁻¹ • (a • e)) := by rw [inv_smul_smul₀ ha]
    _ = spEnd g⁻¹ (a⁻¹ • spEnd g e) := by rw [← hg]
    _ = a⁻¹ • spEnd g⁻¹ (spEnd g e) := by rw [map_smul]
    _ = a⁻¹ • e := by rw [hcomp]

private theorem spConfRad_conj_mem {e : Fin k ⊕ Fin k → F} {g : ↥(StatedSp k F)} {a : F}
    (ha : a ≠ 0) (hg : spEnd g e = a • e) {q : ↥(StatedSp k F)} (hq : q ∈ spConfRad e) :
    g * q * g⁻¹ ∈ spConfRad e := by
  have hginv : spEnd g⁻¹ e = a⁻¹ • e := spConfRad_inv_smul ha hg
  refine ⟨?_, fun v hv => ?_⟩
  · rw [spEnd_mul, Module.End.mul_apply, spEnd_mul, Module.End.mul_apply, hginv, map_smul,
      hq.1, map_smul, hg, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · obtain ⟨b, hb⟩ := hq.2 (spEnd g⁻¹ v) (by
      rw [← spEnd_isometry g (spEnd g⁻¹ v) e, spEnd_spEnd_inv, hg, map_smul, hv, smul_zero])
    refine ⟨b * a, ?_⟩
    rw [spEnd_mul, Module.End.mul_apply, spEnd_mul, Module.End.mul_apply, hb, map_add,
      map_smul, hg, spEnd_spEnd_inv, smul_smul]

theorem mem_normalizer_spConfRad {g : ↥(StatedSp k F)} {a : F} (ha : a ≠ 0)
    (hg : spEnd g e = a • e) :
    g ∈ Subgroup.normalizer (spConfRad e : Set ↥(StatedSp k F)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · exact spConfRad_conj_mem ha hg
  · intro hh
    have hginv : spEnd g⁻¹ e = a⁻¹ • e := spConfRad_inv_smul ha hg
    have hconj := spConfRad_conj_mem (inv_ne_zero ha) hginv hh
    have heq : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
    rwa [heq] at hconj

variable {e}
variable {f : Fin k ⊕ Fin k → F} {c : F}

private theorem spConfRad_E_apply [CharP F 2] {e v : Fin k ⊕ Fin k → F}
    (hve : spForm k F v e = 0) (x : Fin k ⊕ Fin k → F) :
    spEnd (spTransvection (e + v) 1 * spTransvection v 1) x
      = x + (spForm k F x e) • (e + v) + (spForm k F x v) • e := by
  have hvv : spForm k F v v = 0 := (spForm_isAlt (r := k) (K := F)).self_eq_zero v
  have hinner : spForm k F (x + (spForm k F x v) • v) (e + v)
      = spForm k F x e + spForm k F x v := by
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hve, hvv,
      add_zero, smul_zero]
  rw [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, spEnd_spTransvection]
  simp only [one_mul]
  rw [hinner]
  simp only [add_smul, smul_add]
  have h2 : (spForm k F x v) • v + (spForm k F x v) • v = 0 :=
    spConfRad_add_self _
  calc (x + (spForm k F x v) • v) + (((spForm k F x e) • e + (spForm k F x v) • e) +
        ((spForm k F x e) • v + (spForm k F x v) • v))
      = x + ((spForm k F x e) • e + (spForm k F x e) • v) + (spForm k F x v) • e +
        ((spForm k F x v) • v + (spForm k F x v) • v) := by abel
    _ = x + ((spForm k F x e) • e + (spForm k F x e) • v) + (spForm k F x v) • e +
        (0 : Fin k ⊕ Fin k → F) := by rw [h2]
    _ = x + ((spForm k F x e) • e + (spForm k F x e) • v) + (spForm k F x v) • e := by
        rw [add_zero]

private theorem spConfRad_E_mem [CharP F 2] {e v : Fin k ⊕ Fin k → F}
    (hve : spForm k F v e = 0) :
    spTransvection (e + v) 1 * spTransvection v 1 ∈ spConfRad e := by
  have hev : spForm k F e v = 0 := spConfRad_form_e_of_form_e hve
  have hee : spForm k F e e = 0 := (spForm_isAlt (r := k) (K := F)).self_eq_zero e
  refine ⟨?_, fun x hx => ⟨spForm k F x v, ?_⟩⟩
  · rw [spConfRad_E_apply hve e, hee, hev, zero_smul, zero_smul, add_zero, add_zero]
  · rw [spConfRad_E_apply hve x, hx, zero_smul, add_zero]

private theorem spConfRad_E_apply_f [CharP F 2] {e f v : Fin k ⊕ Fin k → F}
    (hef : spForm k F e f = 1) (hve : spForm k F v e = 0) (hvf : spForm k F v f = 0) :
    spEnd (spTransvection (e + v) 1 * spTransvection v 1) f = f + e + v := by
  have hfe : spForm k F f e = 1 := spConfRad_form_f_e hef
  have hfv : spForm k F f v = 0 := by
    have h := (spForm_isAlt (r := k) (K := F)).neg_eq v f
    rw [hvf, neg_zero] at h
    exact h.symm
  rw [spConfRad_E_apply hve f, hfe, hfv, zero_smul, one_smul, add_zero, ← add_assoc]

theorem spConf_transCenter_f [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0)
    {H : Subgroup ↥(StatedSp k F)} (hn : spConfN e f c ∈ H) (he : TransCenter H e) :
    TransCenter H f := by
  have h1 : TransCenter H (spEnd (spConfN e f c) e) := he.map hn
  rw [(spConfN_apply hef hc).1] at h1
  have h2 := h1.smul c
  rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at h2

theorem spConf_transCenter_shift [CharP F 2] (hef : spForm k F e f = 1)
    {H : Subgroup ↥(StatedSp k F)} (hQ : spConfRad e ≤ H) (hf : TransCenter H f)
    {v : Fin k ⊕ Fin k → F} (hve : spForm k F v e = 0) (hvf : spForm k F v f = 0) (a : F) :
    TransCenter H (f + a • e + v) := by
  have hE : spTransvection (e + v) 1 * spTransvection v 1 ∈ spConfRad e :=
    spConfRad_E_mem hve
  have h1 : TransCenter H (f + e + v) := by
    have h := hf.map (hQ hE)
    rwa [spConfRad_E_apply_f hef hve hvf] at h
  have hB : spForm k F (f + e + v) e = 1 := by
    simp only [map_add, LinearMap.add_apply, spConfRad_form_f_e hef,
      (spForm_isAlt (r := k) (K := F)).self_eq_zero e, hve, add_zero]
  have hg : spTransvection e (a - 1) ∈ H := by
    simpa using hQ (spTransvection_mem_spConfRad e 1 (a - 1))
  have h2 : TransCenter H (spEnd (spTransvection e (a - 1)) (f + e + v)) :=
    h1.map hg
  rw [spEnd_spTransvection, hB, mul_one] at h2
  have hshift : (f + e + v) + (a - 1) • e = f + a • e + v := by
    have hcoef : e + (a - 1) • e = a • e := by
      nth_rewrite 1 [← one_smul F e]
      rw [← add_smul]
      congr 1
      ring
    calc (f + e + v) + (a - 1) • e
        = (f + (e + (a - 1) • e)) + v := by abel
      _ = (f + a • e) + v := by rw [hcoef]
      _ = f + a • e + v := rfl
  rwa [hshift] at h2

theorem spConf_transCenter_all [CharP F 2] (hef : spForm k F e f = 1)
    {H : Subgroup ↥(StatedSp k F)} (hQ : spConfRad e ≤ H) (he : TransCenter H e)
    (hf : TransCenter H f) : ∀ w, TransCenter H w := by
  have hfe : spForm k F f e = 1 := spConfRad_form_f_e hef
  have hee : spForm k F e e = 0 := (spForm_isAlt (r := k) (K := F)).self_eq_zero e
  have hff : spForm k F f f = 0 := (spForm_isAlt (r := k) (K := F)).self_eq_zero f
  intro w
  let α : F := spForm k F w f
  let β : F := spForm k F w e
  let v : Fin k ⊕ Fin k → F := w - α • e - β • f
  have hve : spForm k F v e = 0 := by
    dsimp only [v, α, β]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hee, hfe,
      smul_zero, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
  have hvf : spForm k F v f = 0 := by
    dsimp only [v, α, β]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hef, hff,
      smul_zero, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
  have hw : w = α • e + β • f + v := by
    dsimp only [v]
    abel
  rw [hw]
  by_cases hβ : β = 0
  · rw [hβ, zero_smul, add_zero]
    by_cases hv0 : v = 0
    · rw [hv0, add_zero]
      exact he.smul α
    · obtain ⟨x, hx⟩ : ∃ x, spForm k F v x ≠ 0 := by
        by_contra h
        refine hv0 ((spForm_nondegenerate (r := k) (K := F)).1 v fun y => ?_)
        by_contra hy
        exact h ⟨y, hy⟩
      let x₀ : Fin k ⊕ Fin k → F := x - (spForm k F x f) • e - (spForm k F x e) • f
      have hx₀e : spForm k F x₀ e = 0 := by
        dsimp only [x₀]
        simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hee, hfe,
          smul_zero, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
      have hx₀f : spForm k F x₀ f = 0 := by
        dsimp only [x₀]
        simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hef, hff,
          smul_zero, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
      have hvx₀ : spForm k F v x₀ = spForm k F v x := by
        dsimp only [x₀]
        simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hve, hvf,
          smul_zero, sub_zero, sub_self]
      let b₀ : Fin k ⊕ Fin k → F := ((α + 1) / spForm k F v x) • x₀
      have hb₀e : spForm k F b₀ e = 0 := by
        dsimp only [b₀]
        rw [map_smul, LinearMap.smul_apply, hx₀e, smul_zero]
      have hb₀f : spForm k F b₀ f = 0 := by
        dsimp only [b₀]
        rw [map_smul, LinearMap.smul_apply, hx₀f, smul_zero]
      have hvb₀ : spForm k F v b₀ = α + 1 := by
        dsimp only [b₀]
        rw [map_smul, hvx₀, smul_eq_mul, div_mul_cancel₀ (α + 1) hx]
      have hpe : spForm k F (b₀ + v) e = 0 := by
        rw [map_add, LinearMap.add_apply, hb₀e, hve, add_zero]
      have hpf : spForm k F (b₀ + v) f = 0 := by
        rw [map_add, LinearMap.add_apply, hb₀f, hvf, add_zero]
      have hp : TransCenter H (f + α • e + (b₀ + v)) :=
        spConf_transCenter_shift hef hQ hf hpe hpf α
      have hq : TransCenter H (f + b₀) := by
        simpa using spConf_transCenter_shift hef hQ hf hb₀e hb₀f (0 : F)
      have hf_b₀ : spForm k F f b₀ = 0 := by
        have h := (spForm_isAlt (r := k) (K := F)).neg_eq b₀ f
        rw [hb₀f, neg_zero] at h
        exact h.symm
      have he_b₀ : spForm k F e b₀ = 0 := by
        have h := (spForm_isAlt (r := k) (K := F)).neg_eq b₀ e
        rw [hb₀e, neg_zero] at h
        exact h.symm
      have hpq_eq : spForm k F (f + α • e + (b₀ + v)) (f + b₀) = 1 := by
        have hp' : f + α • e + (b₀ + v) = (f + b₀) + (α • e + v) := by abel
        rw [hp']
        have h1 : spForm k F ((f + b₀) + (α • e + v)) (f + b₀)
            = spForm k F (α • e + v) (f + b₀) := by
          rw [map_add (spForm k F) (f + b₀) (α • e + v), LinearMap.add_apply,
            (spForm_isAlt (r := k) (K := F)).self_eq_zero (f + b₀), zero_add]
        rw [h1]
        have h2 : spForm k F (α • e + v) (f + b₀) = α + (α + 1) := by
          rw [map_add (spForm k F) (α • e) v, LinearMap.add_apply,
            map_smul (spForm k F) α e, LinearMap.smul_apply,
            map_add (spForm k F e) f b₀, map_add (spForm k F v) f b₀,
            hef, he_b₀, hvf, hvb₀, add_zero, smul_eq_mul, mul_one, zero_add]
        rw [h2, CharTwo.add_cancel_left]
      have hpq : spForm k F (f + α • e + (b₀ + v)) (f + b₀) ≠ 0 := by
        rw [hpq_eq]
        exact one_ne_zero
      have hadd := TransCenter.add hp hq hpq
      have hsum : (f + α • e + (b₀ + v)) + (f + b₀) = α • e + v := by
        have hff' : f + f = 0 := spConfRad_add_self f
        have hbb : b₀ + b₀ = 0 := spConfRad_add_self b₀
        calc (f + α • e + (b₀ + v)) + (f + b₀)
            = (f + f) + α • e + (b₀ + b₀) + v := by abel
          _ = 0 + α • e + 0 + v := by rw [hff', hbb]
          _ = α • e + v := by simp
      rwa [hsum] at hadd
  · have hwu : β • (f + (α / β) • e + β⁻¹ • v) = α • e + β • f + v := by
      rw [smul_add, smul_add, smul_smul, smul_smul, mul_div_cancel₀ α hβ,
        mul_inv_cancel₀ hβ, one_smul]
      abel
    have hve' : spForm k F (β⁻¹ • v) e = 0 := by
      rw [map_smul, LinearMap.smul_apply, hve, smul_zero]
    have hvf' : spForm k F (β⁻¹ • v) f = 0 := by
      rw [map_smul, LinearMap.smul_apply, hvf, smul_zero]
    have hc := spConf_transCenter_shift hef hQ hf hve' hvf' (α / β)
    have hsm := hc.smul β
    rwa [hwu] at hsm

theorem spConf_gen [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0)
    (H : Subgroup ↥(StatedSp k F)) (hn : spConfN e f c ∈ H) (hQ : spConfRad e ≤ H) : H = ⊤ := by
  have he : TransCenter H e := fun s => by
    simpa using hQ (spTransvection_mem_spConfRad e 1 s)
  exact eq_top_of_transCenter
    (spConf_transCenter_all hef hQ he (spConf_transCenter_f hef hc hn he))

end CFSG.LocalAnalysis.WeakClosure81

end
