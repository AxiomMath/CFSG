module

public import CFSG.LocalAnalysis.StandardType.GGNineDepCtxFacts
public import CFSG.LocalAnalysis.StandardType.GGSmallDepLeafDefs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.GGSmallDepE6Three
public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
  {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}

namespace GGNineDepCtx

theorem false_of_slpm (X : GGNineDepCtx h α r s x)
    (hsl : ∀ g : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s),
      g ∈ ggNineQ X ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) : False := by
  classical
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Module.Finite (ZMod p) ↥(ggFixLineT r s) := inferInstance
  let σ : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) := LinearEquiv.neg (ZMod p)
  have hσ2 : σ * σ = 1 := by
    ext v
    simp [σ, LinearEquiv.mul_apply]
  have hσdet : LinearEquiv.det σ = 1 ∨ LinearEquiv.det σ = -1 := by
    have h2 : ((LinearEquiv.det σ : ZMod p)) ^ 2 = 1 := by
      have h1 : LinearEquiv.det σ * LinearEquiv.det σ = 1 := by
        rw [← map_mul, hσ2, map_one]
      have h2' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h1
      simpa [pow_two] using h2'
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simpa using h))
  have hσQ : σ ∈ ggNineQ X := (hsl σ).mpr hσdet
  have htop : ggFixLineT r s = ⊤ :=
    X.extCtx.eq_top_of_neg_mem X.case.lin.p_ne_two hσQ
  have hmemT : ∀ v : V, v ∈ ggFixLineT r s := by
    intro v
    rw [htop]
    exact Submodule.mem_top
  have hd3 : 3 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by
    have h1 := X.d_ge
    have h2 := X.case.lin.N_ge
    omega
  let b : Module.Basis (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s))) (ZMod p)
      ↥(ggFixLineT r s) := Module.finBasis (ZMod p) _
  let i0 : Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s)) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s)) := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro hh
    have hval := congrArg Fin.val hh
    simp [i0, i1] at hval
  have hfv : b.coord i1 (b i0) = 0 := by
    simp [Ne.symm hi01, i0, i1]
  let t : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) := LinearEquiv.transvection hfv
  have ht_apply : ∀ y, t y = y + b.coord i1 y • b i0 :=
    fun y => LinearEquiv.transvection.apply hfv y
  have ht_det : LinearEquiv.det t = 1 := LinearEquiv.transvection.det_eq_one hfv
  have htQ : t ∈ ggNineQ X := (hsl t).mpr (Or.inl ht_det)
  obtain ⟨a, ha, harest⟩ := (X.extCtx.restr t).mp htQ
  have hdisp : ∀ y : ↥(ggFixLineT r s),
      a (y : V) - (y : V) = ((t y - y : ↥(ggFixLineT r s)) : V) := by
    intro y
    rw [Submodule.coe_sub, harest y]
  have hmoveT : ∀ y : ↥(ggFixLineT r s), t y - y = b.coord i1 y • b i0 := by
    intro y
    rw [ht_apply y, add_sub_cancel_left]
  have hfixT : ∀ y : ↥(ggFixLineT r s), t (t y - y) = t y - y := by
    intro y
    rw [hmoveT y, map_smul, ht_apply (b i0), hfv, zero_smul, add_zero]
  have hspan_mem : ∀ w : V,
      a w - w ∈ Submodule.span (ZMod p) {((b i0 : ↥(ggFixLineT r s)) : V)} := by
    intro w
    let y : ↥(ggFixLineT r s) := ⟨w, by rw [htop]; exact Submodule.mem_top⟩
    have h1 : a w - w = ((t y - y : ↥(ggFixLineT r s)) : V) := hdisp y
    rw [h1, hmoveT y]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hmem_range : ((b i0 : ↥(ggFixLineT r s)) : V) ∈ ggLinMove a := by
    refine ⟨((b i1 : ↥(ggFixLineT r s)) : V), ?_⟩
    change a ((b i1 : ↥(ggFixLineT r s)) : V) - ((b i1 : ↥(ggFixLineT r s)) : V) =
      ((b i0 : ↥(ggFixLineT r s)) : V)
    rw [hdisp (b i1)]
    have h1 : t (b i1) - b i1 = b i0 := by
      rw [hmoveT (b i1)]
      have hc : b.coord i1 (b i1) = 1 := by simp
      rw [hc, one_smul]
    rw [h1]
  have hmove : ggLinMove a = Submodule.span (ZMod p) {((b i0 : ↥(ggFixLineT r s)) : V)} := by
    apply le_antisymm
    · rw [ggLinMove]
      rintro y ⟨z, hz⟩
      rw [← hz]
      simpa using hspan_mem z
    · rw [Submodule.span_le]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hmem_range
  have hb0ne : ((b i0 : ↥(ggFixLineT r s)) : V) ≠ 0 := by
    intro h0
    exact b.ne_zero i0 (Subtype.ext (by simpa using h0))
  have hrank : Module.finrank (ZMod p) (ggLinMove a) = 1 := by
    rw [hmove, finrank_span_singleton hb0ne]
  have hfix : ∀ w, a (a w - w) = a w - w := by
    intro w
    let y : ↥(ggFixLineT r s) := ⟨w, by rw [htop]; exact Submodule.mem_top⟩
    have h1 : a w - w = ((t y - y : ↥(ggFixLineT r s)) : V) := hdisp y
    let z : ↥(ggFixLineT r s) :=
      ⟨((t y - y : ↥(ggFixLineT r s)) : V), hmemT _⟩
    have hz : z = t y - y := Subtype.ext rfl
    have h2 := hdisp z
    rw [hz] at h2
    have h3 : t z - z = 0 := by rw [hz, hfixT y, sub_self]
    rw [h3, Submodule.coe_zero, sub_eq_zero] at h2
    rw [h1]
    exact h2
  exact X.case.lin.no_transv a ha ⟨hrank, hfix⟩

theorem false_of_symSuccTwo (X : GGNineDepCtx h α r s x)
    (hdvd : p ∣ Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2)
    (e : ↥(ggNineQ X) ≃* Equiv.Perm (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2))) :
    False := by
  have hcard : Nat.card ↥(ggNineQ X) =
      (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2).factorial := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  have hdvdN : N.factorial ∣
      (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2).factorial := by
    rw [← hcard]
    exact X.factorial_dvd
  have hpos : 0 < (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2).factorial :=
    Nat.factorial_pos _
  have hle : N.factorial ≤
      (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2).factorial :=
    Nat.le_of_dvd hpos hdvdN
  have hNle : N ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2 := by
    by_contra hcon
    push Not at hcon
    have hlt : (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2).factorial <
        N.factorial :=
      Nat.factorial_lt_of_lt (by omega) hcon
    exact absurd hle (not_le.mpr hlt)
  have hne : N.factorial ≠
      (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2).factorial := by
    intro heq
    exact X.natCard_ne_factorial (by rw [hcard, heq])
  have hlt : N < Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2 := by
    rcases lt_or_eq_of_le hNle with h | h
    · exact h
    · exact absurd (congrArg Nat.factorial h) hne
  have hd2 : Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2 = N + 1 ∨
      Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2 = N + 2 := by
    have hdle := X.d_le
    omega
  rcases hd2 with hd2 | hd2
  · have hpd : p ∣ 1 := by
      have h1 : p ∣ N + 1 := by rwa [hd2] at hdvd
      have h2 : p ∣ N := X.case.lin.p_dvd
      simpa using Nat.dvd_sub h1 h2
    exact (Nat.Prime.ne_one Fact.out) (Nat.dvd_one.mp hpd)
  · have hpd : p ∣ 2 := by
      have h1 : p ∣ N + 2 := by rwa [hd2] at hdvd
      have h2 : p ∣ N := X.case.lin.p_dvd
      simpa using Nat.dvd_sub h1 h2
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpd
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact X.case.lin.p_ne_two (le_antisymm hple hpge)

theorem false_of_gmmn (X : GGNineDepCtx h α r s x) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) ↥(ggFixLineT r s)) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ)
    (hQ : ggNineQ X = ZS.gmmn p f i₀ i₁ ζ) : False := by
  have hd : Module.finrank (ZMod p) ↥(ggFixLineT r s) = n := by
    simpa using Module.finrank_eq_card_basis f
  have hn : 2 ≤ n := by
    have h1 := X.d_ge
    have h2 := X.case.lin.N_ge
    omega
  exact X.not_isImprimitiveOnV (hQ.symm ▸ ZS.isImprimitiveOnV_gmmn hn f i₀ i₁ ζ)

theorem false_of_g2mmn (X : GGNineDepCtx h α r s x) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) ↥(ggFixLineT r s)) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ)
    (hQ : ggNineQ X = ZS.g2mmn p f i₀ i₁ ζ) : False := by
  have hd : Module.finrank (ZMod p) ↥(ggFixLineT r s) = n := by
    simpa using Module.finrank_eq_card_basis f
  have hn : 2 ≤ n := by
    have h1 := X.d_ge
    have h2 := X.case.lin.N_ge
    omega
  exact X.not_isImprimitiveOnV (hQ.symm ▸ ZS.isImprimitiveOnV_g2mmn hn f i₀ i₁ ζ)

theorem false_of_exc (X : GGNineDepCtx h α r s x)
    (hcell : (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10))
    (k : ZS.ExcRow) (hk : k.admissible p)
    (hdeg : Module.finrank (ZMod p) ↥(ggFixLineT r s) = k.deg)
    (hord : Nat.card ↥(ggNineQ X) = k.ord)
    (hcen : Nat.card ↥(Subgroup.center ↥(ggNineQ X)) = k.cen) : False := by
  classical
  haveI : Module.Finite (ZMod p) V := X.finite
  haveI : Module.Finite (ZMod p) ↥(ggFixLineT r s) := inferInstance
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite ↥(ggFixLineT r s) := Subtype.finite
  haveI : Finite (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
    Finite.of_injective
      (fun g : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) =>
        (g : ↥(ggFixLineT r s) → ↥(ggFixLineT r s))) DFunLike.coe_injective
  haveI : Finite ↥(ggNineQ X) := Subtype.finite
  have hcen2 : 2 ∣ k.cen := by cases k <;> decide
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥(ggNineQ X)) := by
    rw [hcen]
    exact hcen2
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hzne : z ≠ 1 := by
    intro hz1
    rw [hz1, orderOf_one] at hzord
    omega
  let zg : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) := (z.1 : ↥(ggNineQ X))
  have hz2 : zg * zg = 1 := by
    have hz2c : z * z = 1 := by rw [← pow_two, ← hzord, pow_orderOf_eq_one]
    have hz2Q : (z.1 : ↥(ggNineQ X)) * (z.1 : ↥(ggNineQ X)) = 1 := by
      have h := congrArg (fun w : ↥(Subgroup.center ↥(ggNineQ X)) => (w : ↥(ggNineQ X))) hz2c
      simpa using h
    have h := congrArg (fun g : ↥(ggNineQ X) =>
      (g : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))) hz2Q
    simpa [zg] using h
  have hz1 : zg ≠ 1 := by
    intro hz1'
    apply hzne
    apply Subtype.ext
    apply Subtype.ext
    simpa [zg] using hz1'
  have hcomm : ∀ a ∈ ggNineQ X,
      (zg : Module.End (ZMod p) ↥(ggFixLineT r s)) *
          (a : Module.End (ZMod p) ↥(ggFixLineT r s)) =
        (a : Module.End (ZMod p) ↥(ggFixLineT r s)) *
          (zg : Module.End (ZMod p) ↥(ggFixLineT r s)) := by
    intro a ha
    have h := (Subgroup.mem_center_iff.mp z.2) (⟨a, ha⟩ : ↥(ggNineQ X))
    have h1 : a * zg = zg * a := by
      have h' := congrArg (fun g : ↥(ggNineQ X) =>
        (g : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))) h
      simpa [zg] using h'
    have h2 := congrArg (fun g : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) =>
      (g : Module.End (ZMod p) ↥(ggFixLineT r s))) h1
    simpa [LinearEquiv.coe_toLinearMap_mul] using h2.symm
  have hAI : ZS.AbsIrred p (ggNineQ X) := X.restr.2.1
  obtain ⟨c, hc⟩ :=
    hAI.2 (zg : Module.End (ZMod p) ↥(ggFixLineT r s)) hcomm
  have hc2 : c * c = 1 := by
    have hzz : (zg : Module.End (ZMod p) ↥(ggFixLineT r s)) *
        (zg : Module.End (ZMod p) ↥(ggFixLineT r s)) = LinearMap.id := by
      ext x
      have h := congrArg (fun g : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) => g x) hz2
      simpa [Module.End.mul_apply] using h
    rw [hc] at hzz
    let i : Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s)) :=
      ⟨0, by have h1 := X.d_ge; have h2 := X.case.lin.N_ge; omega⟩
    let b : Module.Basis (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s))) (ZMod p)
        ↥(ggFixLineT r s) := Module.finBasis (ZMod p) _
    have hcv : (c * c) • b i = b i := by
      have h := congrArg (fun e : Module.End (ZMod p) ↥(ggFixLineT r s) => e (b i)) hzz
      simpa [Module.End.mul_apply, smul_smul] using h
    have hbi : b.coord i (b i) = 1 := by simp
    have h := congrArg (b.coord i) hcv
    rw [map_smul, hbi] at h
    simpa using h
  have hcval : c = 1 ∨ c = -1 := by
    exact sq_eq_one_iff.mp (by rw [pow_two]; exact hc2)
  have hcne : c ≠ 1 := by
    intro hc1
    apply hz1
    apply LinearEquiv.ext
    intro x
    have h := congrArg (fun e : Module.End (ZMod p) ↥(ggFixLineT r s) => e x) hc
    rw [hc1] at h
    simpa using h
  have hcneg : c = -1 := by
    rcases hcval with h | h
    · exact absurd h hcne
    · exact h
  have hzgneg : zg = LinearEquiv.neg (ZMod p) := by
    apply LinearEquiv.ext
    intro x
    have h := congrArg (fun e : Module.End (ZMod p) ↥(ggFixLineT r s) => e x) hc
    rw [hcneg] at h
    rw [LinearEquiv.neg_apply]
    simpa using h
  have hnegQ : (LinearEquiv.neg (ZMod p) :
      ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) ∈ ggNineQ X := by
    rw [← hzgneg]
    simpa [zg] using z.1.2
  have hfinn : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N :=
    X.finrank_eq_of_neg_mem hnegQ
  have hdegN : k.deg = N := by rw [← hdeg, hfinn]
  rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hk5 : k = ZS.ExcRow.K5 := by
      cases k <;> simp_all [ZS.ExcRow.deg]
    subst hk5
    have hdim5 : Module.finrank (ZMod 5) ↥(ggFixLineT r s) = 5 := by
      simpa [ZS.ExcRow.deg] using hdeg
    let b : Module.Basis (Fin 5) (ZMod 5) ↥(ggFixLineT r s) :=
      (Module.finBasis (ZMod 5) ↥(ggFixLineT r s)).reindex (finCongr hdim5)
    have hcardGL : Nat.card (↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s)) =
        Nat.card (GL (Fin 5) (ZMod 5)) :=
      (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5)
          ↥(ggFixLineT r s))).toEquiv).symm
    have hdvd3 : 3 ^ 4 ∣ Nat.card ↥(ggNineQ X) := by
      rw [hord]
      norm_num [ZS.ExcRow.ord]
    have hdvdGL : 3 ^ 4 ∣
        Nat.card (↥(ggFixLineT r s) ≃ₗ[ZMod 5] ↥(ggFixLineT r s)) :=
      Nat.dvd_trans hdvd3 (Subgroup.card_subgroup_dvd_card (ggNineQ X))
    rw [hcardGL] at hdvdGL
    have hnot : ¬ 3 ^ 4 ∣ Nat.card (GL (Fin 5) (ZMod 5)) := by
      rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_five]
      norm_num
    exact hnot hdvdGL
  · cases k <;> simp_all [ZS.ExcRow.deg, ZS.ExcRow.admissible]
  · cases k <;> simp_all [ZS.ExcRow.deg]
  · cases k <;> simp_all [ZS.ExcRow.deg]

theorem false_of_h4 (X : GGNineDepCtx h α r s x)
    (hdim : Module.finrank (ZMod p) ↥(ggFixLineT r s) = 4)
    (hneg : (LinearEquiv.neg (ZMod p) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) ∈
      ggNineQ X) : False := by
  have hN := X.finrank_eq_of_neg_mem hneg
  have h5 := X.case.lin.N_ge
  omega

theorem false_of_heart (X : GGNineDepCtx h α r s x) (hp : p = 3) (hN : N = 6)
    (hd : Module.finrank (ZMod p) ↥(ggFixLineT r s) = 5)
    {Q : QuadraticForm (ZMod p) ↥(ggFixLineT r s)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (hcl : ggNineQ X = Subgroup.closure (ZS.ClassRefl p Q c)) : False := by
  subst hp
  subst hN
  haveI : Module.Finite (ZMod 3) V := X.finite
  by_cases hneg : (LinearEquiv.neg (ZMod 3) :
      ↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) ∈ ggNineQ X
  · have h := X.finrank_eq_of_neg_mem hneg
    omega
  · exact X.not_linearIndependent_α (ggSmallE6HeartInput_holds V (ggLargeGrp r s)
      (ggFixLineT r s) (ggNineQ X) Q c h α r X.finrank_eq hd X.extCtx.disp X.extCtx.fix
      X.extCtx.inj X.extCtx.restr hQ hc hcl hneg
      (fun i => Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self i)))
      X.case.lin.refl_form X.case.lin.pair)

end GGNineDepCtx

end CFSG.StandardType

end
