module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryInnTorus
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWitt
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelMono
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelCoords

public section

namespace CFSG.StandardType

namespace UModel

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU UCoord
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv)

section Coords

variable {K : Type} [Field K] {d p : ℕ} {u : Kˣ}

@[expose] noncomputable def uvec (hu : u ^ p = 1) : ↥(sumZero d p) →* (Fin d → Kˣ) :=
  (MonoidHom.compLeft (TableBSymp.zmodPowHom hu) (Fin d)).comp (sumZero d p).subtype

theorem uvec_apply [NeZero p] (hu : u ^ p = 1) (f : ↥(sumZero d p)) (k : Fin d) :
    uvec hu f k = u ^ (crd f k).val := by
  rw [uvec, MonoidHom.comp_apply, MonoidHom.compLeft_apply, Function.comp_apply,
    TableBSymp.zmodPowHom_apply]
  rfl

theorem uvec_pow_eq_one [NeZero p] (hu : u ^ p = 1) (f : ↥(sumZero d p)) (k : Fin d) :
    uvec hu f k ^ p = 1 := by
  rw [uvec_apply, ← pow_mul, mul_comm, pow_mul, hu, one_pow]

theorem uvec_pow_norm [NeZero p] (hu : u ^ p = 1) {q : ℕ} (huq : u ^ q = 1)
    (f : ↥(sumZero d p)) (k : Fin d) : uvec hu f k ^ q = 1 := by
  rw [uvec_apply, ← pow_mul, mul_comm, pow_mul, huq, one_pow]

theorem prod_uvec [NeZero p] (hu : u ^ p = 1) (hord : orderOf u = p) (f : ↥(sumZero d p)) :
    ∏ k, uvec hu f k = 1 := by
  simp only [uvec_apply]
  rw [Finset.prod_pow_eq_pow_sum, ← orderOf_dvd_iff_pow_eq_one, hord, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sum]
  simp only [ZMod.natCast_zmod_val]
  exact sum_crd f

theorem crd_eq_of_uvec_eq [NeZero p] (hu : u ^ p = 1) (hord : orderOf u = p)
    {f g : ↥(sumZero d p)} {k k' : Fin d} (h : uvec hu f k = uvec hu g k') :
    crd f k = crd g k' := by
  rw [uvec_apply, uvec_apply] at h
  have h2 := (pow_inj_mod (x := u)).mp h
  rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
  exact ZMod.val_injective p h2

theorem uvec_injective [NeZero p] (hu : u ^ p = 1) (hord : orderOf u = p) :
    Function.Injective (uvec (d := d) hu) :=
  fun _ _ hfg => ext_crd fun k => crd_eq_of_uvec_eq hu hord (congrFun hfg k)

theorem uvec_permAutV (hu : u ^ p = 1) (σ : Equiv.Perm (Fin d)) (f : ↥(sumZero d p)) :
    uvec hu (permAutV σ f) = uvec hu f ∘ ⇑σ.symm :=
  rfl

theorem exists_uvec_eq [NeZero p] (hu : u ^ p = 1) (hord : orderOf u = p) {t : Fin d → Kˣ}
    (ht : ∀ k, t k ^ p = 1) (hprod : ∏ k, t k = 1) : ∃ f, uvec hu f = t := by
  have hζ : IsPrimitiveRoot u p := IsPrimitiveRoot.iff_orderOf.mpr hord
  choose a ha using fun k => LinModel.exists_eq_pow_val hζ (ht k)
  have hsum : ∑ k, a k = 0 := by
    have h1 : u ^ (∑ k, (a k).val) = 1 := by
      rw [← Finset.prod_pow_eq_pow_sum]
      simp only [← ha]
      exact hprod
    rw [← orderOf_dvd_iff_pow_eq_one, hord, ← ZMod.natCast_eq_zero_iff, Nat.cast_sum] at h1
    simpa only [ZMod.natCast_zmod_val] using h1
  refine ⟨⟨fun k => Multiplicative.ofAdd (a k), hsum⟩, funext fun k => ?_⟩
  rw [uvec_apply, ha k]
  rfl

end Coords

section Mono

variable {K : Type} [Field K] {m : ℕ}

theorem eq_of_mul_diagonal {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    {t s : Fin (m + 1) → K} (h : Y * diagonal t = diagonal s * Y) {k l : Fin (m + 1)}
    (hkl : Y k l ≠ 0) : t l = s k := by
  have h1 := congrFun (congrFun h k) l
  rw [mul_diagonal, diagonal_mul] at h1
  exact mul_left_cancel₀ hkl (h1.trans (mul_comm _ _))

end Mono


theorem ggTorusPermEltSC_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 1 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGTorusPermEltSC p d (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  intro E hE h3 hscE
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  have : NeZero p := ⟨hp.ne_zero⟩
  have hnp : ∀ z ∈ (projU n (m + 1) K).ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    TableBUE.eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hAmap, -, hA, -⟩ :=
    TableBUE.exists_lift_of_noTorsion (projU n (m + 1) K) projU_surjective hp hnp hE
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h hp hpq hA
  obtain ⟨u, hord, huq⟩ : ∃ u : Kˣ, orderOf u = p ∧ u ^ (2 ^ n + 1) = 1 := by
    have := Fact.mk hp
    have hpK : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        have := Nat.sq_sub_sq (2 ^ n) 1
        rwa [one_pow] at this
      rw [e]
      exact Dvd.dvd.mul_right hpq _
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpK
    refine ⟨u, hu, ?_⟩
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, ← hu, pow_orderOf_eq_one, one_pow]
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  have hDmem : ∀ f : ↥(sumZero (m + 1) p), diagHom (m + 1) (uvec hu f) ∈
      unitarySU 2 n K (m + 1) := fun f =>
    TableBUE.diagHom_mem_unitarySU h (fun k => uvec_pow_norm hu huq f k) (prod_uvec hu hord f)
  set Dsu : ↥(sumZero (m + 1) p) →* ↥(unitarySU 2 n K (m + 1)) :=
    ((diagHom (m + 1)).comp (uvec hu)).codRestrict _ hDmem with hDsu
  have hDsu_coe : ∀ f, ((Dsu f : ↥(unitarySU 2 n K (m + 1))) : GL (Fin (m + 1)) K) =
      diagHom (m + 1) (uvec hu f) := fun f => rfl
  set τ : ↥(sumZero (m + 1) p) →* LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K (2 ^ n)) :=
    (frameMk h P hP).comp Dsu with hτ
  have hτapp : ∀ f, τ f = projU n (m + 1) K ((TableBUE.conjSU h P hP).symm (Dsu f)) :=
    fun f => rfl
  have hEA : ∀ e ∈ E, ∃ y ∈ A, projU n (m + 1) K y = e := by
    intro e he
    rw [← hAmap] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨y, hy, rfl⟩
  have hcommA : ∀ f, ∀ y ∈ A, τ f * projU n (m + 1) K y = projU n (m + 1) K y * τ f := by
    intro f y hy
    obtain ⟨σ, hσ⟩ := hPd y hy
    have hc : (TableBUE.conjSU h P hP).symm (Dsu f) * y =
        y * (TableBUE.conjSU h P hP).symm (Dsu f) := by
      apply (TableBUE.conjSU h P hP).injective
      apply Subtype.ext
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul, hσ,
        hDsu_coe, ← map_mul, ← map_mul, mul_comm]
    rw [hτapp, ← map_mul, hc, map_mul]
  have hτE1 : ∀ f, τ f ∈ E := by
    intro f
    refine hscE (τ f) (fun e he => ?_) (by rw [← map_pow, pow_p_eq_one, map_one])
    obtain ⟨y, hy, rfl⟩ := hEA e he
    exact hcommA f y hy
  have hτE2 : ∀ e ∈ E, ∃ f, τ f = e := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := hEA e he
    obtain ⟨σ, hσ⟩ := hPd y hy
    have hσp : ∀ k, σ k ^ p = 1 := by
      have h1 : (TableBUE.conjSU h P hP y) ^ p = 1 := by rw [← map_pow, hA.2 y hy, map_one]
      have h2 : diagHom (m + 1) (σ ^ p) = 1 := by
        rw [map_pow, ← hσ, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
      have h3 : σ ^ p = 1 := diagHom_injective (m + 1) (by rw [h2, map_one])
      intro k
      exact congrFun h3 k
    have hσprod : ∏ k, σ k = 1 := by
      have h1 := ((mem_unitarySU_iff h).mp (TableBUE.conjSU h P hP y).2).1
      rw [hσ, det_diagHom] at h1
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact h1)
    obtain ⟨f, hf⟩ := exists_uvec_eq hu hord hσp hσprod
    refine ⟨f, ?_⟩
    rw [hτapp]
    congr 1
    apply (TableBUE.conjSU h P hP).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hDsu_coe, hf, hσ]
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    rw [hτapp] at hf
    have h1 := hnp _ (MonoidHom.mem_ker.mpr hf)
      (by rw [← map_pow, ← map_pow, pow_p_eq_one, map_one, map_one])
    have h2 : Dsu f = 1 := by
      have := congrArg (TableBUE.conjSU h P hP) h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have h3 : uvec hu f = 1 := by
      apply diagHom_injective (m + 1)
      rw [map_one, ← hDsu_coe, h2, Subgroup.coe_one]
    apply uvec_injective hu hord
    rw [h3, map_one]
  have hτrange : τ.range = E := by
    ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE1 f
    · intro he
      exact hτE2 e he
  refine ⟨τ, hτinj, hτrange, fun σ => ?_, fun g hg => ?_⟩
  ·
    set M : ↥(unitarySU 2 n K (m + 1)) := ⟨permGL σ, SURep.permGL_mem_unitarySU h σ⟩ with hM
    refine ⟨frameMk h P hP M, fun f => ?_⟩
    have hMD : M * Dsu f * M⁻¹ = Dsu (permAutV σ f) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hDsu_coe, hDsu_coe,
        uvec_permAutV]
      exact permGL_mul_diagHom_mul_inv σ (uvec hu f)
    rw [hτ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, hMD]
  ·
    obtain ⟨y, rfl⟩ := frameMk_surjective h P hP g
    have hex : ∀ f, ∃ f', frameMk h P hP y * τ f * (frameMk h P hP y)⁻¹ = τ f' := by
      intro f
      obtain ⟨f', hf'⟩ := hτE2 _ (hg _ (hτE1 f))
      exact ⟨f', hf'.symm⟩
    choose F' hF' using hex
    have hF'inj : Function.Injective F' := by
      intro f₁ f₂ h12
      apply hτinj
      have h1 := (hF' f₁).trans (congrArg τ h12)
      rw [← hF' f₂] at h1
      exact mul_left_cancel (mul_right_cancel h1)
    have hF'surj : Function.Surjective F' := Finite.injective_iff_surjective.mp hF'inj
    have hrel : ∀ f, ∃ c : Kˣ,
        ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
            diagonal (fun k => ((uvec hu f k : Kˣ) : K)) =
          diagonal (fun k => (c : K) * ((uvec hu (F' f) k : Kˣ) : K)) *
            ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
      intro f
      have h1 : frameMk h P hP (y * Dsu f * y⁻¹) = frameMk h P hP (Dsu (F' f)) := by
        rw [map_mul, map_mul, map_inv]
        exact hF' f
      obtain ⟨c, hc⟩ := TableBUI.exists_scalar_of_frameMk_eq h P hP h1
      have hGL : (y : GL (Fin (m + 1)) K) * diagHom (m + 1) (uvec hu f) =
          Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * diagHom (m + 1) (uvec hu (F' f)) *
            (y : GL (Fin (m + 1)) K) := by
        rw [← hDsu_coe, ← hDsu_coe, hc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          map_inv]
        group
      refine ⟨c⁻¹, ?_⟩
      have h2 := congrArg (fun X : GL (Fin (m + 1)) K => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
        hGL
      simp only [Units.val_mul, coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar] at h2
      rw [Matrix.scalar_apply, diagonal_mul_diagonal] at h2
      exact h2
    have hcol : ∀ i l l' : Fin (m + 1),
        ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) l i ≠ 0 →
        ((y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) l' i ≠ 0 → l = l' := by
      intro i l l' hl hl'
      by_contra hne
      obtain ⟨f, hf⟩ := hF'surj (rootV l l')
      obtain ⟨c, hc⟩ := hrel f
      have e1 := eq_of_mul_diagonal hc hl
      have e2 := eq_of_mul_diagonal hc hl'
      simp only [hf] at e1 e2
      have e3 : ((uvec hu (rootV l l') l : Kˣ) : K) = ((uvec hu (rootV l l') l' : Kˣ) : K) :=
        mul_left_cancel₀ c.ne_zero (e1.symm.trans e2)
      have e4 := crd_eq_of_uvec_eq hu hord (Units.ext e3)
      rw [crd_rootV_left hne, crd_rootV_right hne] at e4
      exact SpCoord.coord_two_ne_zero hp hp2 (by
        rw [← one_add_one_eq_two]
        nth_rewrite 2 [e4]
        exact add_neg_cancel 1)
    obtain ⟨π, hπ⟩ := LinModel.exists_isPermOf hcol
    refine ⟨π, fun f => ?_⟩
    obtain ⟨c, hc⟩ := hrel f
    have hentU : ∀ i, uvec hu f i = c * uvec hu (F' f) (π i) := fun i =>
      Units.ext (by rw [Units.val_mul]; exact eq_of_mul_diagonal hc ((hπ i (π i)).mpr rfl))
    have hcp : c ^ p = 1 := by
      have h1 := congrArg (· ^ p) (hentU 0)
      simp only [mul_pow, uvec_pow_eq_one, mul_one] at h1
      exact h1.symm
    have hcd : c ^ (m + 1) = 1 := by
      have h1 : ∏ i, uvec hu f i = ∏ i, (c * uvec hu (F' f) (π i)) :=
        Finset.prod_congr rfl fun i _ => hentU i
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Equiv.prod_comp π (uvec hu (F' f)), prod_uvec hu hord, prod_uvec hu hord, mul_one] at h1
      exact h1.symm
    have hc1 : c = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hcp, hcd⟩
      rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd), pow_one] at h1
    have hF'f : F' f = permAutV π f := by
      refine ext_crd fun k => ?_
      rw [crd_permAutV]
      have h1 := hentU (π⁻¹ k)
      rw [hc1, one_mul, show π (π⁻¹ k) = k from Equiv.Perm.eq_inv_iff_eq.mp rfl] at h1
      exact (crd_eq_of_uvec_eq hu hord h1).symm
    rw [← hF'f]
    exact hF' f

end UModel

end CFSG.StandardType

end
