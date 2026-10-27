module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup Module QuadraticMap

private theorem orthFour_two_ne_zero {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  intro h
  have hchar : CharP K 2 := CFSG.GroupTheory.WeirSylow.charP_two_of_two_eq_zero h
  let hfin : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (n : ℕ) := by rwa [Nat.card_eq_fintype_card]
  exact hodd.not_two_dvd_nat (by rw [hcard']; exact dvd_pow_self 2 (PNat.pos n).ne')

private theorem orthFour_exists_anisotropic {K W : Type} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W = 4) :
    ∃ u : W, Q u ≠ 0 := by
  have hntriv : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  by_contra h
  push Not at h
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  refine hv (hQ.1 v fun w => ?_)
  have h1 : polar Q v w = 0 := by
    rw [QuadraticMap.polar, h (v + w), h v, h w]
    ring
  exact h1

private theorem orthFour_isCompl_span_orthogonal {K W : Type} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    {u : W} (hu : Q u ≠ 0) (h2 : (2 : K) ≠ 0) :
    IsCompl (K ∙ u) (LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ u)) := by
  have hNZ : NeZero (2 : K) := ⟨h2⟩
  have hB : LinearMap.BilinForm.IsRefl (polarBilin Q) := (QuadraticMap.isSymm_polarBilin Q).isRefl
  refine LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB ?_
  have hcu : polar Q u u ≠ 0 := by
    rw [QuadraticMap.polar_self, nsmul_eq_mul]
    exact mul_ne_zero two_ne_zero hu
  constructor
  · intro x hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
    have h1 : polar Q (x : W) u = 0 := by
      simpa [LinearMap.BilinForm.restrict_apply] using
        hx ⟨u, Submodule.mem_span_singleton_self u⟩
    rw [← hc] at h1
    rw [QuadraticMap.polar_smul_left, smul_eq_mul] at h1
    have hc0 : c = 0 := (mul_eq_zero.mp h1).resolve_right hcu
    rw [hc0, zero_smul] at hc
    exact Subtype.ext hc.symm
  · intro x hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
    have h1 : polar Q u (x : W) = 0 := by
      simpa [LinearMap.BilinForm.restrict_apply] using
        hx ⟨u, Submodule.mem_span_singleton_self u⟩
    rw [← hc] at h1
    rw [QuadraticMap.polar_smul_right, smul_eq_mul] at h1
    have hc0 : c = 0 := (mul_eq_zero.mp h1).resolve_right hcu
    rw [hc0, zero_smul] at hc
    exact Subtype.ext hc.symm

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

private theorem orthFour_prodSubgroup_centralizer (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W = 4)
    {u : W} (hu : Q u ≠ 0) [Invertible (Q u)] :
    ∃ P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      P ≤ Subgroup.centralizer {TauCeti.QuadraticMap.reflectionOrthogonal Q u} ∧
      Nat.card P = 4 * Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have h2 : (2 : K) ≠ 0 := orthFour_two_ne_zero hodd
  have hNZ : NeZero (2 : K) := ⟨h2⟩
  let r : TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflectionOrthogonal Q u
  let L : Submodule K W := K ∙ u
  let U : Submodule K W := LinearMap.BilinForm.orthogonal (polarBilin Q) L
  have hu0 : u ≠ 0 := fun h => hu (by rw [h]; exact QuadraticMap.map_zero Q)
  have hL : finrank K L = 1 := finrank_span_singleton hu0
  have hcompl : IsCompl L U := orthFour_isCompl_span_orthogonal hu h2
  have horth : ∀ x ∈ L, ∀ y ∈ U, polar Q x y = 0 := by
    intro x hx y hy
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) x hx
    rwa [polarBilin_apply_apply] at h
  have hfinU : finrank K U = 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl (K := K) (V := W) hcompl
    omega
  have hQU : (polarBilin (Q.restrict U)).Nondegenerate :=
    CFSG.ClassicalGroups.Orthogonal.Small.nondegenerate_comp_subtype
      (K := K) (V := W) (W := U) (W' := L) hQ hcompl.symm (by
        intro x hx y hy
        rw [polar_comm]
        exact horth y hy x hx)
  have hring : ringChar K ≠ 2 := by
    intro h
    have hchar : CharP K 2 := h ▸ ringChar.charP K
    exact h2 (CharP.cast_eq_zero K 2)
  have hOUL : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict L)) = 2 := by
    have hQLne : Q.restrict L ≠ 0 := by
      intro h
      have h' : Q u = 0 := by
        simpa [QuadraticMap.restrict] using congrArg (fun f : QuadraticMap K L K =>
          f ⟨u, Submodule.mem_span_singleton_self u⟩) h
      exact hu h'
    have h := TauCeti.QuadraticMap.card_orthogonalGroup_of_finrank_eq_one
      (Q := Q.restrict L) hQLne hL
    simpa using h
  have hOU : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U)) =
      2 * Nat.card K * (Nat.card K ^ 2 - 1) := by
    have hz : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U)) : ℤ) =
        2 * (Nat.card K : ℤ) * ((Nat.card K : ℤ) ^ 2 - 1) := by
      have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := K) hring
        (Q := Q.restrict U) hQU (n := 1) (by omega)
      simpa using h
    have hq1 : 1 ≤ Nat.card K ^ 2 := by
      have hq : 1 < Nat.card K := Finite.one_lt_card
      exact le_of_lt (Nat.one_lt_pow two_ne_zero hq)
    have hcast : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
    refine Nat.cast_injective (R := ℤ) ?_
    rw [hz]
    push_cast
    rw [hcast]
  let e : ((Q.restrict L).prod (Q.restrict U)).IsometryEquiv Q :=
    QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q L hcompl
  let φ : (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict L) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U)) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom.comp
      (QuadraticMap.orthogonalGroupProd (Q.restrict L) (Q.restrict U))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact (QuadraticMap.orthogonalGroupProd_injective (Q.restrict L) (Q.restrict U))
      ((TauCeti.QuadraticMap.orthogonalGroupCongr e).injective hxy)
  refine ⟨φ.range, ?_, ?_⟩
  · rintro g ⟨⟨a, b⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    have hφapp : ∀ z : L × U,
        ((φ (a, b) : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) (e z) =
          e ((a : L ≃ₗ[K] L) z.1, (b : U ≃ₗ[K] U) z.2) := by
      intro z
      change ((TauCeti.QuadraticMap.orthogonalGroupCongr e)
        ((QuadraticMap.orthogonalGroupProd (Q.restrict L) (Q.restrict U)) (a, b)) :
          W ≃ₗ[K] W) (e z) = e ((a : L ≃ₗ[K] L) z.1, (b : U ≃ₗ[K] U) z.2)
      rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply,
        QuadraticMap.coe_orthogonalGroupProd, LinearEquiv.prodCongr_apply]
      have h2 := QuadraticMap.IsometryEquiv.symm_apply_apply e z
      have h2fst : (e.symm (e z)).1 = z.1 := congrArg Prod.fst h2
      have h2snd : (e.symm (e z)).2 = z.2 := congrArg Prod.snd h2
      erw [h2fst, h2snd]
      simp
    have hLneg : ∀ l : L,
        (TauCeti.QuadraticMap.reflection Q u) (l : W) = -(l : W) := by
      intro l
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp l.2
      rw [← hc, map_smul, TauCeti.QuadraticMap.reflection_apply_self, smul_neg]
    have hUfix : ∀ w : U, (TauCeti.QuadraticMap.reflection Q u) (w : W) = w := by
      intro w
      have hp : polar Q u (w : W) = 0 := by
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) u
          (Submodule.mem_span_singleton_self u)
        rwa [polarBilin_apply_apply] at h
      rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div, hp, zero_div, zero_smul,
        sub_zero]
    have hrapp : ∀ z : L × U,
        ((r : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) (e z) =
          e (-z.1, z.2) := by
      intro z
      rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        QuadraticMap.IsometryEquiv.prodRestrictOrthogonal_apply, map_add, hLneg z.1,
        hUfix z.2]
      rw [QuadraticMap.IsometryEquiv.prodRestrictOrthogonal_apply]
      simp
    change ((φ (a, b) : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W)
        (((r : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) (e x)) =
      ((r : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W)
        (((φ (a, b) : TauCeti.QuadraticMap.orthogonalGroup Q) : W ≃ₗ[K] W) (e x))
    rw [hrapp x, hφapp (-x.1, x.2), hφapp x, hrapp ((a : L ≃ₗ[K] L) x.1, (b : U ≃ₗ[K] U) x.2)]
    simp
  · have hPcard : Nat.card (φ.range) =
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict L) ×
          TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U)) :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm
    rw [hPcard, Nat.card_prod, hOUL, hOU]
    ring

theorem exists_central_reflection_of_finrank_eq_four (hodd : Odd (Nat.card K))
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K W = 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (T : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ∃ (u : W) (_ : Invertible (Q u)),
      TauCeti.QuadraticMap.reflectionOrthogonal Q u ∈
        (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      ∀ t ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
        t * TauCeti.QuadraticMap.reflectionOrthogonal Q u =
          TauCeti.QuadraticMap.reflectionOrthogonal Q u * t := by
  classical
  have h2 : (2 : K) ≠ 0 := orthFour_two_ne_zero hodd
  have hNZ : NeZero (2 : K) := ⟨h2⟩
  obtain ⟨u, hu⟩ := orthFour_exists_anisotropic hQ hdim
  have hInv : Invertible (Q u) := invertibleOfNonzero hu
  obtain ⟨P, hPC, hPcard⟩ := orthFour_prodSubgroup_centralizer hodd hQ hdim hu
  let r : TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflectionOrthogonal Q u
  let C : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Subgroup.centralizer {r}
  have hOQ : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * Nat.card K ^ 2 * (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 - 1) := by
    have hz : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
        2 * (Nat.card K : ℤ) ^ 2 * ((Nat.card K : ℤ) ^ 2 + 1) *
          ((Nat.card K : ℤ) ^ 2 - 1) := by
      have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := K) hQ
        (m := 1) (by omega) (ε := -1) (Or.inr ⟨rfl, hminus⟩)
      simpa [sub_neg_eq_add] using h
    have hq1 : 1 ≤ Nat.card K ^ 2 := by
      have hq : 1 < Nat.card K := Finite.one_lt_card
      exact le_of_lt (Nat.one_lt_pow two_ne_zero hq)
    have hcast : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
    refine Nat.cast_injective (R := ℤ) ?_
    rw [hz]
    push_cast
    rw [hcast]
  have hPi : P.index * Nat.card P = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Subgroup.index_mul_card P
  have hP2 : 2 * P.index = Nat.card K * (Nat.card K ^ 2 + 1) := by
    refine Nat.eq_of_mul_eq_mul_right
      (m := 4 * Nat.card K * (Nat.card K ^ 2 - 1)) ?_ ?_
    · have hq : 1 < Nat.card K := Finite.one_lt_card
      have hq2 : 0 < Nat.card K ^ 2 - 1 := by
        have := Nat.one_lt_pow two_ne_zero hq
        omega
      positivity
    · calc (2 * P.index) * (4 * Nat.card K * (Nat.card K ^ 2 - 1))
          = 2 * (P.index * Nat.card P) := by rw [← hPcard]; ring
        _ = 2 * Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by rw [hPi]
        _ = (Nat.card K * (Nat.card K ^ 2 + 1)) *
              (4 * Nat.card K * (Nat.card K ^ 2 - 1)) := by rw [hOQ]; ring
  have h4 : ¬ 4 ∣ Nat.card K * (Nat.card K ^ 2 + 1) := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    intro h4dvd
    obtain ⟨m, hm⟩ := h4dvd
    have hfac : (2 * k + 1) * ((2 * k + 1) ^ 2 + 1) =
        2 * ((2 * k + 1) * (2 * k ^ 2 + 2 * k + 1)) := by ring
    have hoddO : Odd ((2 * k + 1) * (2 * k ^ 2 + 2 * k + 1)) := by
      have h1 : Odd (2 * k + 1) := ⟨k, by ring⟩
      have h2' : Odd (2 * k ^ 2 + 2 * k + 1) := ⟨k ^ 2 + k, by ring⟩
      exact h1.mul h2'
    obtain ⟨j, hj⟩ := hoddO
    rw [hfac] at hm
    omega
  have hPodd : Odd P.index := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp hev
    exact h4 ⟨m, by rw [← hP2, hm]; ring⟩
  have hCdiv : C.index ∣ P.index := by
    have h := Subgroup.relIndex_mul_index hPC
    exact ⟨P.relIndex C, by rw [mul_comm, h]⟩
  have hCodd : Odd C.index := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    exact hPodd.not_two_dvd_nat (dvd_trans (even_iff_two_dvd.mp hev) hCdiv)
  have hFW : Finite W := Module.finite_of_finite K
  have hFL : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun g : W ≃ₗ[K] W => g.toEquiv)
      (fun g h hgh => LinearEquiv.ext fun x => by
        simpa using congrArg (fun e : W ≃ W => e x) hgh)
  have hFG : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := inferInstance
  have hFC : Finite C := inferInstance
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFS : Finite (Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q)) := inferInstance
  let rC : C := ⟨r, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hu0 : u ≠ 0 := fun h => hu (by rw [h]; exact QuadraticMap.map_zero Q)
  have hr2 : r * r = 1 := by
    apply Subtype.ext
    change (r : W ≃ₗ[K] W) * (r : W ≃ₗ[K] W) = 1
    rw [show (r : W ≃ₗ[K] W) = TauCeti.QuadraticMap.reflection Q u from
      TauCeti.QuadraticMap.coe_reflectionOrthogonal Q u]
    exact TauCeti.QuadraticMap.reflection_mul_self Q u
  have hrne : r ≠ 1 := by
    intro h
    have h1 : (r : W ≃ₗ[K] W) u = u := by rw [h]; rfl
    have h1' : (TauCeti.QuadraticMap.reflection Q u) u = u := by
      simpa [r, TauCeti.QuadraticMap.coe_reflectionOrthogonal] using h1
    rw [TauCeti.QuadraticMap.reflection_apply_self] at h1'
    have h2u : (2 : K) • u = 0 := by
      have hsum : u + u = 0 := by
        nth_rewrite 2 [← h1']
        rw [add_neg_cancel]
      simpa [two_smul] using hsum
    exact hu0 ((smul_eq_zero.mp h2u).resolve_left h2)
  have hrC2 : rC * rC = 1 := Subtype.ext hr2
  have hrCne : rC ≠ 1 := fun h => hrne (congrArg Subtype.val h)
  have hord : orderOf rC = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hrCne
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers rC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hN : (Subgroup.zpowers rC).Normal := by
    apply Subgroup.normal_of_le_center
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp x.2) r (Set.mem_singleton r)).symm
  obtain ⟨R⟩ := Sylow.nonempty (p := 2) (G := C)
  have hNorm : (Subgroup.zpowers rC).Normal := hN
  have hzR : Subgroup.zpowers rC ≤ R := IsPGroup.le_sylow_of_normal hz2 R
  have hrR : rC ∈ R := hzR (Subgroup.mem_zpowers_iff.mpr ⟨1, pow_one rC⟩)
  let S : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) := R.map C.subtype
  have hSg : IsPGroup 2 ↥S := IsPGroup.map (Sylow.isPGroup' R) C.subtype
  have hSidx : S.index = R.index * C.index := Subgroup.index_map_subtype (H := C) R
  have hSnd : ¬ 2 ∣ S.index := by
    rw [hSidx, Nat.Prime.dvd_mul Nat.prime_two]
    push Not
    exact ⟨Sylow.not_dvd_index R, hCodd.not_two_dvd_nat⟩
  let Ssyl : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    IsPGroup.toSylow (P := S) hSg hSnd
  have hSsyl : (Ssyl : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) = S :=
    IsPGroup.toSylow_coe hSg hSnd
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M := TauCeti.QuadraticMap.orthogonalGroup Q) Ssyl T
  have hrS : r ∈ S := Subgroup.mem_map.mpr ⟨rC, hrR, rfl⟩
  have hTmem : ∀ y, y ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ↔
      ∃ x ∈ S, MulAut.conj g x = y := by
    intro y
    rw [← hg]
    change y ∈ ((g • Ssyl : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup Q)) : Set _) ↔
      ∃ x ∈ S, MulAut.conj g x = y
    have hSset : (Ssyl : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) =
        (S : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
      ext x
      change x ∈ (Ssyl : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) ↔ x ∈ S
      rw [hSsyl]
    rw [Sylow.coe_smul, hSset, Set.mem_smul_set]
    simp
  have hrT : g * r * g⁻¹ ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
    (hTmem _).mpr ⟨r, hrS, MulAut.conj_apply g r⟩
  have hcentral : ∀ t ∈ (T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
      t * (g * r * g⁻¹) = (g * r * g⁻¹) * t := by
    intro t ht
    obtain ⟨x, hxS, hxeq⟩ := (hTmem t).mp ht
    obtain ⟨xC, hxR, hxC⟩ := Subgroup.mem_map.mp hxS
    have hcomm : r * x = x * r := by
      rw [← hxC]
      exact (Subgroup.mem_centralizer_iff.mp xC.2) r (Set.mem_singleton r)
    rw [← hxeq]
    change g * x * g⁻¹ * (g * r * g⁻¹) = (g * r * g⁻¹) * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * r * g⁻¹)
        = g * (x * r) * g⁻¹ := by group
      _ = g * (r * x) * g⁻¹ := by rw [hcomm]
      _ = (g * r * g⁻¹) * (g * x * g⁻¹) := by group
  let hinst : Invertible (Q ((g : W ≃ₗ[K] W) u)) :=
    Invertible.copy (invertibleOfNonzero hu) _
      (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 u)
  let hInst := hinst
  have hfinal : g * r * g⁻¹ =
      TauCeti.QuadraticMap.reflectionOrthogonal Q ((g : W ≃ₗ[K] W) u) :=
    TauCeti.QuadraticMap.mul_reflectionOrthogonal_mul_inv Q g u
  refine ⟨(g : W ≃ₗ[K] W) u, hinst, ?_, ?_⟩
  · rw [← hfinal]
    exact hrT
  · intro t ht
    rw [← hfinal]
    exact hcentral t ht

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
