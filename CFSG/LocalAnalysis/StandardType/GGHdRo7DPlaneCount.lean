module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DKSqueezeDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.RankThree.GF2n.Stroth80.Sec3Action
import CFSG.ClassicalGroups.Orthogonal.Basic
import CFSG.CGT.Timmesfeld75.Forms
import CFSG.RankThree.GF2n.Stroth80.Anisotropic
import CFSG.RankThree.GF2n.Stroth80.FrobClause
import CFSG.RankThree.GF2n.Stroth80.GlobalModel
import CFSG.RankThree.GF2n.Stroth80.Sec36
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.StandardType.OmNsRootGen
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7DPCAux_pow_maps_to
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) (j : Fin k) :
    ∀ (m : ℕ) {z : V}, z ∈ U j → ((e j : V ≃ₗ[F] V) ^ m) z ∈ U j := by
  intro m
  induction m with
  | zero => intro z hz; simpa using hz
  | succ m ih =>
    intro z hz
    rw [pow_succ, LinearEquiv.mul_apply]
    exact ih (hframe.maps_to j z hz)

private theorem hdRo7DPCAux_maps_to_of_mem
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) {d : ↥(orthDerived Q)} (hd : d ∈ E) (j : Fin k) :
    ∀ x ∈ U j, (d : V ≃ₗ[F] V) x ∈ U j := by
  obtain ⟨m, hm⟩ := hframe.exists_pow_apply_eq hd j
  intro x hx
  rw [hm x hx]
  exact hdRo7DPCAux_pow_maps_to hframe j m hx

private theorem hdRo7DPCAux_ker_le_polarPerp
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) {t : ↥(orthDerived Q)} (ht : t ∈ E)
    {i : Fin k} (hfree : ∀ x ∈ U i, (t : V ≃ₗ[F] V) x = x → x = 0) :
    LinearMap.ker ((t : V ≃ₗ[F] V).toLinearMap - 1) ≤ polarPerp Q (U i) := by
  intro w hw
  have hwfix : (t : V ≃ₗ[F] V) w = w := mem_fixedSpace.mp hw
  rw [mem_polarPerp_iff]
  intro u hu
  have hmap : ∀ x ∈ U i, ((t : V ≃ₗ[F] V) : V →ₗ[F] V) x - x ∈ U i := by
    intro x hx
    exact Submodule.sub_mem (U i) (hdRo7DPCAux_maps_to_of_mem hframe ht i x hx) hx
  let φ : U i →ₗ[F] U i :=
    LinearMap.restrict (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) (p := U i) (q := U i) hmap
  have hker : LinearMap.ker φ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx0 : φ x = 0 := LinearMap.mem_ker.mp hx
    have hx1 : ((t : V ≃ₗ[F] V) : V →ₗ[F] V) (x : V) - (x : V) = 0 :=
      congrArg Subtype.val hx0
    have hxfix : (t : V ≃ₗ[F] V) (x : V) = (x : V) := sub_eq_zero.mp hx1
    exact Subtype.ext (hfree (x : V) x.2 hxfix)
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective).mp (LinearMap.ker_eq_bot.mp hker)
  obtain ⟨x, hx⟩ := hsurj ⟨u, hu⟩
  have hxval : ((t : V ≃ₗ[F] V) : V →ₗ[F] V) (x : V) - (x : V) = u :=
    congrArg Subtype.val hx
  rw [← hxval]
  have hTsymm : (t : V ≃ₗ[F] V).symm w = w := by
    rw [LinearEquiv.symm_apply_eq]
    exact hwfix.symm
  have hiso : (t : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup t.2
  have h1 : QuadraticMap.polar Q (((t : V ≃ₗ[F] V) : V →ₗ[F] V) (x : V)) w =
      QuadraticMap.polar Q (x : V) w := by
    calc QuadraticMap.polar Q (((t : V ≃ₗ[F] V) : V →ₗ[F] V) (x : V)) w
        = QuadraticMap.polar Q ((t : V ≃ₗ[F] V) (x : V))
            ((t : V ≃ₗ[F] V) ((t : V ≃ₗ[F] V).symm w)) := by simp
      _ = QuadraticMap.polar Q (x : V) ((t : V ≃ₗ[F] V).symm w) :=
          CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hiso _ _
      _ = QuadraticMap.polar Q (x : V) w := by rw [hTsymm]
  rw [QuadraticMap.polar_sub_left, h1, sub_self]

private theorem hdRo7DPCAux_fixes_ker
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) {t : ↥(orthDerived Q)} (ht : t ∈ E)
    {i : Fin k} (hfree : ∀ x ∈ U i, (t : V ≃ₗ[F] V) x = x → x = 0)
    {w : V} (hw : (t : V ≃ₗ[F] V) w = w) :
    (e i : V ≃ₗ[F] V) w = w := by
  have hker := hdRo7DPCAux_ker_le_polarPerp hframe ht hfree
  exact hframe.apply_of_perp i w (hker (mem_fixedSpace.mpr hw))

private theorem hdRo7DPCAux_range_preserved
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) {t : ↥(orthDerived Q)} (ht : t ∈ E) {i : Fin k} :
    ∀ r : V, r ∈ LinearMap.range (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) →
      (e i : V ≃ₗ[F] V) r ∈
        LinearMap.range (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) := by
  have hEt : (e i : V ≃ₗ[F] V) * (t : V ≃ₗ[F] V) =
      (t : V ≃ₗ[F] V) * (e i : V ≃ₗ[F] V) := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hframe.isElemAbelian.comm (hframe.mem i) ht)
    simpa [Subgroup.coe_mul] using h
  have hEt_apply : ∀ y : V, (e i : V ≃ₗ[F] V) ((t : V ≃ₗ[F] V) y) =
      (t : V ≃ₗ[F] V) ((e i : V ≃ₗ[F] V) y) := by
    intro y
    have h := congrFun (congrArg (fun z : V ≃ₗ[F] V => (z : V → V)) hEt) y
    simpa [LinearEquiv.mul_apply] using h
  rintro r ⟨u, hu⟩
  refine ⟨(e i : V ≃ₗ[F] V) u, ?_⟩
  have hL : (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) ((e i : V ≃ₗ[F] V) u) =
      (e i : V ≃ₗ[F] V) ((((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) u) := by
    change (t : V ≃ₗ[F] V) ((e i : V ≃ₗ[F] V) u) - (e i : V ≃ₗ[F] V) u =
      (e i : V ≃ₗ[F] V) ((t : V ≃ₗ[F] V) u - u)
    rw [map_sub, ← hEt_apply u]
  rw [hL, hu]

private theorem hdRo7DPCAux_cfix_range
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {t : ↥(orthDerived Q)}
    {C : Subgroup ↥(orthDerived Q)}
    (htriv : ∀ c ∈ C, ∀ v : V, ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        ((t : V ≃ₗ[F] V) v - v) = (t : V ≃ₗ[F] V) v - v)
    {c : ↥(orthDerived Q)} (hc : c ∈ C) :
    ∀ r : V, r ∈ LinearMap.range (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) →
      ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) r = r := by
  rintro r ⟨u, hu⟩
  have hu' : (t : V ≃ₗ[F] V) u - u = r := by
    simpa [LinearMap.sub_apply, Module.End.one_apply] using hu
  rw [← hu']
  exact htriv c hc u

private theorem hdRo7DPCAux_cfix_ker
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {t : ↥(orthDerived Q)}
    {C : Subgroup ↥(orthDerived Q)}
    (hC : C ≤ Subgroup.centralizer ({t} : Set ↥(orthDerived Q)))
    {c : ↥(orthDerived Q)} (hc : c ∈ C) :
    ∀ w : V, (t : V ≃ₗ[F] V) w = w →
      (t : V ≃ₗ[F] V) (((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) w) =
        ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) w := by
  have hCt : (t : V ≃ₗ[F] V) * ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) * (t : V ≃ₗ[F] V) := by
    have h := (Subgroup.mem_centralizer_iff.mp (hC hc)) t (by simp)
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) h
    simpa [Subgroup.coe_mul] using this
  have hCt_apply : ∀ y : V, (t : V ≃ₗ[F] V) (((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) y) =
      ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((t : V ≃ₗ[F] V) y) := by
    intro y
    have h := congrFun (congrArg (fun z : V ≃ₗ[F] V => (z : V → V)) hCt) y
    simpa [LinearEquiv.mul_apply] using h
  intro w hw
  rw [hCt_apply w, hw]

private theorem hdRo7DPCAux_rot_centralizes
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) {t : ↥(orthDerived Q)} (ht : t ∈ E)
    {i : Fin k} (hfree : ∀ x ∈ U i, (t : V ≃ₗ[F] V) x = x → x = 0)
    {C : Subgroup ↥(orthDerived Q)}
    (hC : C ≤ Subgroup.centralizer ({t} : Set ↥(orthDerived Q)))
    (htriv : ∀ c ∈ C, ∀ v : V, ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        ((t : V ≃ₗ[F] V) v - v) = (t : V ≃ₗ[F] V) v - v) :
    e i ∈ Subgroup.centralizer (C : Set ↥(orthDerived Q)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have ht3 : (t : V ≃ₗ[F] V) ^ 3 = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hframe.isElemAbelian.2 t ht)
    simpa using h
  have hT3 : (((t : V ≃ₗ[F] V) : V →ₗ[F] V) ^ 3) = 1 := by
    rw [← toLinearMap_pow, ht3]
    rfl
  have hsup : LinearMap.ker (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) ⊔
      LinearMap.range (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) = ⊤ :=
    CFSG.RankThree.GF2n.Stroth80.ker_sup_range_eq_top_of_pow_eq_one
      (by norm_num : Odd 3) hT3
  have hv : v ∈ LinearMap.ker (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) ⊔
      LinearMap.range (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨kk, hkk, rr, hrr, hkr⟩ := Submodule.mem_sup.mp hv
  rw [← hkr]
  have hkkfix : (t : V ≃ₗ[F] V) kk = kk := mem_fixedSpace.mp hkk
  have hrrmem : ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) rr = rr :=
    hdRo7DPCAux_cfix_range htriv hc rr hrr
  have hEkk : (e i : V ≃ₗ[F] V) kk = kk :=
    hdRo7DPCAux_fixes_ker hframe ht hfree hkkfix
  have hCkk : (t : V ≃ₗ[F] V) (((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) kk) =
      ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) kk :=
    hdRo7DPCAux_cfix_ker hC hc kk hkkfix
  have hECkk : (e i : V ≃ₗ[F] V) (((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) kk) =
      ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) kk :=
    hdRo7DPCAux_fixes_ker hframe ht hfree hCkk
  have hErr : (e i : V ≃ₗ[F] V) rr ∈
      LinearMap.range (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) :=
    hdRo7DPCAux_range_preserved hframe ht rr hrr
  have hCErr : ((c : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((e i : V ≃ₗ[F] V) rr) =
      (e i : V ≃ₗ[F] V) rr :=
    hdRo7DPCAux_cfix_range htriv hc _ hErr
  calc ((c * e i : ↥(orthDerived Q)) : V ≃ₗ[F] V) (kk + rr)
      = (c : V ≃ₗ[F] V) ((e i : V ≃ₗ[F] V) (kk + rr)) := by
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    _ = (c : V ≃ₗ[F] V) ((e i : V ≃ₗ[F] V) kk + (e i : V ≃ₗ[F] V) rr) := by
        simp only [map_add]
    _ = (c : V ≃ₗ[F] V) (kk + (e i : V ≃ₗ[F] V) rr) := by
        rw [hEkk]
    _ = (c : V ≃ₗ[F] V) kk + (c : V ≃ₗ[F] V) ((e i : V ≃ₗ[F] V) rr) := by
        simp only [map_add]
    _ = (c : V ≃ₗ[F] V) kk + (e i : V ≃ₗ[F] V) rr := by
        rw [hCErr]
    _ = (e i : V ≃ₗ[F] V) ((c : V ≃ₗ[F] V) kk) + (e i : V ≃ₗ[F] V) rr := by
        rw [hECkk]
    _ = (e i : V ≃ₗ[F] V) ((c : V ≃ₗ[F] V) kk + rr) := by
        simp only [map_add]
    _ = (e i : V ≃ₗ[F] V) ((c : V ≃ₗ[F] V) kk + (c : V ≃ₗ[F] V) rr) := by
        rw [hrrmem]
    _ = (e i : V ≃ₗ[F] V) ((c : V ≃ₗ[F] V) (kk + rr)) := by
        simp only [map_add]
    _ = ((e i * c : ↥(orthDerived Q)) : V ≃ₗ[F] V) (kk + rr) := by
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply]

private theorem hdRo7DPCAux_pow_apply_eq_of_perp
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) {a b : Fin k} (hab : a ≠ b) :
    ∀ (m : ℕ) {z : V}, z ∈ U b → ((e a : V ≃ₗ[F] V) ^ m) z = z := by
  have hfix : ∀ z ∈ U b, (e a : V ≃ₗ[F] V) z = z := by
    intro z hz
    refine hframe.apply_of_perp a z ?_
    rw [mem_polarPerp_iff]
    intro y hy
    rw [QuadraticMap.polar_comm]
    exact hframe.perp b a (fun h => hab h.symm) z hz y hy
  intro m
  induction m with
  | zero => intro z hz; rfl
  | succ m ih =>
    intro z hz
    rw [pow_succ, LinearEquiv.mul_apply, hfix z hz]
    exact ih hz

private theorem hdRo7DPCAux_pow_inj
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {k : ℕ} {U : Fin k → Submodule F V}
    {E : Subgroup ↥(orthDerived Q)} {e : Fin k → ↥(orthDerived Q)}
    (hframe : IsPlaneFrame Q 3 U e E) {i : Fin k}
    {x : V} (hx : x ∈ U i) (hx0 : x ≠ 0) {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (h : ((e i : V ≃ₗ[F] V) ^ a) x = ((e i : V ≃ₗ[F] V) ^ b) x) : a = b := by
  have hord : orderOf (e i : V ≃ₗ[F] V) = 3 :=
    (Subgroup.orderOf_coe (e i)).trans (hframe.orderOf_eq i)
  have key : ∀ m : ℕ, 0 < m → m < 3 → ((e i : V ≃ₗ[F] V) ^ m) x = x → False := by
    intro m hm0 hm3 hmx
    have hy1 : ((e i : V ≃ₗ[F] V) ^ m) ≠ 1 := by
      intro h1
      have hdvd : 3 ∣ m := by
        rw [← hord]
        exact orderOf_dvd_iff_pow_eq_one.mpr h1
      omega
    have hfs := fixedSpace_eq_of_mem_zpowers (p := 3) Nat.prime_three hord
      (Subgroup.npow_mem_zpowers (e i : V ≃ₗ[F] V) m) hy1
    have hxperp : x ∈ polarPerp Q (U i) := by
      have hxfs : x ∈ fixedSpace ((e i : V ≃ₗ[F] V) ^ m) := mem_fixedSpace.mpr hmx
      rw [hfs, hframe.fixedSpace_eq_polarPerp i] at hxfs
      exact hxfs
    have hbot : x ∈ (⊥ : Submodule F V) :=
      (isCompl_polarPerp (hframe.nondeg i)).disjoint.le_bot ⟨hx, hxperp⟩
    exact hx0 (by simpa using hbot)
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have hdx : ((e i : V ≃ₗ[F] V) ^ (b - a)) x = x := by
      have h2 : ((e i : V ≃ₗ[F] V) ^ a) x =
          ((e i : V ≃ₗ[F] V) ^ a) (((e i : V ≃ₗ[F] V) ^ (b - a)) x) := by
        rw [← LinearEquiv.mul_apply, ← pow_add, show a + (b - a) = b by omega]
        exact h
      exact (((e i : V ≃ₗ[F] V) ^ a).injective h2).symm
    exact key (b - a) (by omega) (by omega) hdx
  · have hdx : ((e i : V ≃ₗ[F] V) ^ (a - b)) x = x := by
      have h2 : ((e i : V ≃ₗ[F] V) ^ b) x =
          ((e i : V ≃ₗ[F] V) ^ b) (((e i : V ≃ₗ[F] V) ^ (a - b)) x) := by
        rw [← LinearEquiv.mul_apply, ← pow_add, show b + (a - b) = a by omega]
        exact h.symm
      exact (((e i : V ≃ₗ[F] V) ^ b).injective h2).symm
    exact key (a - b) (by omega) (by omega) hdx

theorem d_planeCount_holds : DPlaneCountLeaf := by
  intro F _ _ _ hF V _ _ _ Q hQ ℓ hdim hℓ E hE hsc t ht hdimt C hC htriv
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hpq : 3 ∣ Nat.card F + 1 := by
    simpa [hF] using (dvd_refl 3 : 3 ∣ 3)
  obtain ⟨k, U, e, hframe, hcase⟩ :=
    exists_planeFrame_of_selfCentralizing (p := 3) hQ Nat.prime_three (by norm_num) hpq hdim
      (by omega) hE hsc
  have hkℓ : k ≤ ℓ := by rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  let Z : Finset (Fin k) :=
    Finset.univ.filter (fun j => ∀ x ∈ U j, (t : V ≃ₗ[F] V) x = x)
  let M : Finset (Fin k) :=
    Finset.univ.filter (fun j => ¬ ∀ x ∈ U j, (t : V ≃ₗ[F] V) x = x)
  have hZker : (⨆ j ∈ Z, U j) ≤
      LinearMap.ker (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) := by
    refine iSup₂_le fun j hj x hx => ?_
    have hfix : (t : V ≃ₗ[F] V) x = x := (Finset.mem_filter.mp hj).2 x hx
    exact mem_fixedSpace.mpr hfix
  have hWker : polarPerp Q (⨆ j : Fin k, U j) ≤
      LinearMap.ker (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1) := by
    intro x hx
    exact mem_fixedSpace.mpr (hframe.apply_eq_of_mem_polarPerp_iSup ht hx)
  have hdisj : Disjoint (⨆ j ∈ Z, U j) (polarPerp Q (⨆ j : Fin k, U j)) := by
    refine disjoint_iff_inf_le.mpr ?_
    intro x hx
    have hxS : x ∈ (⨆ j : Fin k, U j) := (iSup₂_le fun j _ => le_iSup U j) hx.1
    have hxbot : x ∈ (⊥ : Submodule F V) := by
      have hinf : x ∈ (⨆ j : Fin k, U j) ⊓ polarPerp Q (⨆ j : Fin k, U j) :=
        ⟨hxS, hx.2⟩
      rwa [hframe.toIsPlaneSystem.isCompl_iSup.inf_eq_bot] at hinf
    exact hxbot
  have hS : (⨆ j : Fin k, U j) = ⨆ j ∈ (Finset.univ : Finset (Fin k)), U j := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_univ j) le_rfl)
    · exact iSup₂_le fun j _ => le_iSup U j
  have hfinS : Module.finrank F ↥(⨆ j : Fin k, U j) = 2 * k := by
    rw [hS, hframe.toIsPlaneSystem.finrank_biSup, Finset.card_univ, Fintype.card_fin]
  have hfinW : Module.finrank F ↥(polarPerp Q (⨆ j : Fin k, U j)) = 2 * ℓ - 2 * k := by
    rw [finrank_polarPerp hQ (⨆ j : Fin k, U j), hfinS, hdim]
  have hZfin : Module.finrank F ↥(⨆ j ∈ Z, U j) = 2 * Z.card :=
    hframe.toIsPlaneSystem.finrank_biSup Z
  have hdimSup : Module.finrank F ↥((⨆ j ∈ Z, U j) ⊔ polarPerp Q (⨆ j : Fin k, U j)) =
      2 * Z.card + (2 * ℓ - 2 * k) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (⨆ j ∈ Z, U j)
      (polarPerp Q (⨆ j : Fin k, U j))
    rw [disjoint_iff.1 hdisj, finrank_bot, add_zero, hZfin, hfinW] at h
    exact h
  have hmono : Module.finrank F ↥((⨆ j ∈ Z, U j) ⊔ polarPerp Q (⨆ j : Fin k, U j)) ≤
      Module.finrank F ↥(LinearMap.ker (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1)) :=
    Submodule.finrank_mono (sup_le hZker hWker)
  have hZcard : Z.card + M.card = k := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k)))
      (p := fun j => ∀ x ∈ U j, (t : V ≃ₗ[F] V) x = x)
    simpa [Z, M, Finset.card_univ, Fintype.card_fin] using h
  have hM2 : 2 ≤ M.card := by
    have hdimker : Module.finrank F
        ↥(LinearMap.ker (((t : V ≃ₗ[F] V) : V →ₗ[F] V) - 1)) = 2 * (ℓ - 2) := by
      simpa using hdimt
    omega
  obtain ⟨i, hiM, j, hjM, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < M.card)
  have hiM' : ¬ (∀ x ∈ U i, (t : V ≃ₗ[F] V) x = x) := (Finset.mem_filter.mp hiM).2
  have hjM' : ¬ (∀ x ∈ U j, (t : V ≃ₗ[F] V) x = x) := (Finset.mem_filter.mp hjM).2
  have hfree_i : ∀ x ∈ U i, (t : V ≃ₗ[F] V) x = x → x = 0 := by
    rcases hframe.apply_eq_or_eq_zero Nat.prime_three ht i with h | h
    · exact absurd h hiM'
    · exact h
  have hfree_j : ∀ x ∈ U j, (t : V ≃ₗ[F] V) x = x → x = 0 := by
    rcases hframe.apply_eq_or_eq_zero Nat.prime_three ht j with h | h
    · exact absurd h hjM'
    · exact h
  have hei : e i ∈ E ⊓ Subgroup.centralizer (C : Set ↥(orthDerived Q)) :=
    Subgroup.mem_inf.mpr
      ⟨hframe.mem i, hdRo7DPCAux_rot_centralizes hframe ht hfree_i hC htriv⟩
  have hej : e j ∈ E ⊓ Subgroup.centralizer (C : Set ↥(orthDerived Q)) :=
    Subgroup.mem_inf.mpr
      ⟨hframe.mem j, hdRo7DPCAux_rot_centralizes hframe ht hfree_j hC htriv⟩
  let g : Fin 3 × Fin 3 → ↥(E ⊓ Subgroup.centralizer (C : Set ↥(orthDerived Q))) :=
    fun p => ⟨(e i) ^ (p.1 : ℕ) * (e j) ^ (p.2 : ℕ), by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact E.mul_mem (E.pow_mem (hframe.mem i) _) (E.pow_mem (hframe.mem j) _)
      · exact (Subgroup.centralizer (C : Set ↥(orthDerived Q))).mul_mem
          ((Subgroup.centralizer (C : Set ↥(orthDerived Q))).pow_mem hei.2 _)
          ((Subgroup.centralizer (C : Set ↥(orthDerived Q))).pow_mem hej.2 _)⟩
  have hg_inj : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ heq
    have hw : (e i) ^ (a : ℕ) * (e j) ^ (b : ℕ) =
        (e i) ^ (a' : ℕ) * (e j) ^ (b' : ℕ) := by
      have := congrArg
        (fun z : ↥(E ⊓ Subgroup.centralizer (C : Set ↥(orthDerived Q))) =>
          (z : ↥(orthDerived Q))) heq
      simpa [g] using this
    obtain ⟨x, hxU, hx0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hframe.finrank_eq i)
    have hact : ((e i : V ≃ₗ[F] V) ^ (a : ℕ)) x = ((e i : V ≃ₗ[F] V) ^ (a' : ℕ)) x := by
      have h := congrArg (fun z : ↥(orthDerived Q) => ((z : V ≃ₗ[F] V)) x) hw
      have hxj : ∀ m : ℕ, ((e j : V ≃ₗ[F] V) ^ m) x = x :=
        fun m => hdRo7DPCAux_pow_apply_eq_of_perp hframe (Ne.symm hij) m hxU
      simpa [LinearEquiv.mul_apply, hxj b, hxj b'] using h
    have haeq : a = a' := Fin.ext (hdRo7DPCAux_pow_inj hframe hxU hx0 a.isLt a'.isLt hact)
    obtain ⟨y, hyU, hy0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j) (hframe.finrank_eq j)
    have hactj : ((e j : V ≃ₗ[F] V) ^ (b : ℕ)) y = ((e j : V ≃ₗ[F] V) ^ (b' : ℕ)) y := by
      have h := congrArg (fun z : ↥(orthDerived Q) => ((z : V ≃ₗ[F] V)) y) hw
      have hyb : ((e j : V ≃ₗ[F] V) ^ (b : ℕ)) y ∈ U j :=
        hdRo7DPCAux_pow_maps_to hframe j b hyU
      have hyb' : ((e j : V ≃ₗ[F] V) ^ (b' : ℕ)) y ∈ U j :=
        hdRo7DPCAux_pow_maps_to hframe j b' hyU
      have h1 : ((e i : V ≃ₗ[F] V) ^ (a : ℕ)) (((e j : V ≃ₗ[F] V) ^ (b : ℕ)) y) =
          ((e j : V ≃ₗ[F] V) ^ (b : ℕ)) y :=
        hdRo7DPCAux_pow_apply_eq_of_perp hframe hij a hyb
      have h2 : ((e i : V ≃ₗ[F] V) ^ (a' : ℕ)) (((e j : V ≃ₗ[F] V) ^ (b' : ℕ)) y) =
          ((e j : V ≃ₗ[F] V) ^ (b' : ℕ)) y :=
        hdRo7DPCAux_pow_apply_eq_of_perp hframe hij a' hyb'
      simpa [LinearEquiv.mul_apply, h1, h2] using h
    have hbeq : b = b' := Fin.ext (hdRo7DPCAux_pow_inj hframe hyU hy0 b.isLt b'.isLt hactj)
    exact Prod.ext haeq hbeq
  have h9 : Nat.card (Fin 3 × Fin 3) = 9 := by
    rw [Nat.card_prod]
    simp [Nat.card_eq_fintype_card]
  calc 9 = Nat.card (Fin 3 × Fin 3) := h9.symm
    _ ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (C : Set ↥(orthDerived Q))) :=
        Nat.card_le_card_of_injective g hg_inj


end CFSG.StandardType.HdRo7D
