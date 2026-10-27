module

public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSL
public import CFSG.Quasithin.Vol2.Ch11SecS12ZI
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Tactic.Group
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Vol2.Ch11SecS12ZH
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized

public section

namespace CFSG.StandardType.TableCRes

section Idem

open CFSG.StandardType.ClassicalPosition Matrix

theorem exists_scalar_mul_pow_eq_one {F : Type} [Field F] [Finite F] {N p : ℕ}
    (hp : p.Prime) (hpF : ¬ p ∣ Nat.card Fˣ) (s : GL (Fin N) F) (u : Fˣ)
    (hs : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u) :
    ∃ w : Fˣ, (s * Matrix.GeneralLinearGroup.scalar (Fin N) w) ^ p = 1 := by
  have hcop : Nat.Coprime (Nat.card Fˣ) p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpF).symm
  obtain ⟨w, hw⟩ := (Nat.Coprime.pow_left_bijective hcop).2 u⁻¹
  have hw' : w ^ p = u⁻¹ := hw
  refine ⟨w, ?_⟩
  have hc : Commute s (Matrix.GeneralLinearGroup.scalar (Fin N) w) :=
    (Matrix.GeneralLinearGroup.scalar_commute w s).symm
  have hpow : (Matrix.GeneralLinearGroup.scalar (Fin N) w) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (w ^ p) :=
    (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) w p).symm
  rw [hc.mul_pow, hs, hpow, hw', ← map_mul (Matrix.GeneralLinearGroup.scalar (Fin N)),
    mul_inv_cancel, map_one]

theorem exists_avgIdem {F : Type} [Field F] [CharP F 2] {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (s : Matrix (Fin N) (Fin N) F) (hs : s ^ p = 1) :
    ∃ ε : Matrix (Fin N) (Fin N) F, ε ∈ Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F)) ∧
      IsIdempotentElem ε ∧ s * ε = ε ∧
      (∀ v : Fin N → F, ε *ᵥ v = v ↔ s *ᵥ v = v) ∧
      (∀ a ∈ Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F)), ∃ c : F, a * ε = c • ε) ∧
      (∀ e : Matrix (Fin N) (Fin N) F, s * e = e → ε * e = e) := by
  have hpF0 : (p : F) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hcp : (p : F)⁻¹ * (p : F) = 1 := inv_mul_cancel₀ hpF0
  have hcc : (p : F)⁻¹ * (p : F)⁻¹ * (p : F) = (p : F)⁻¹ := by
    rw [mul_assoc, hcp, mul_one]
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix (Fin N) (Fin N) F, T = ∑ i ∈ Finset.range p, s ^ i :=
    ⟨_, rfl⟩
  have hsT : s * T = T := by
    have h := mul_geom_sum s p
    rw [hs, ← hTdef, sub_self, sub_mul, one_mul, sub_eq_zero] at h
    exact h
  have hpow : ∀ i : ℕ, s ^ i * T = T := by
    intro i
    induction i with
    | zero => rw [pow_zero, one_mul]
    | succ k ih => rw [pow_succ, mul_assoc, hsT, ih]
  have hTT : T * T = (p : F) • T := by
    have h1 : T * T = (∑ i ∈ Finset.range p, s ^ i) * T := by rw [← hTdef]
    rw [h1, Finset.sum_mul]
    simp only [hpow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have hsmem : s ∈ Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F)) :=
    Algebra.subset_adjoin (Set.mem_singleton s)
  have hTmem : T ∈ Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F)) := by
    rw [hTdef]
    exact Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hsmem i)
  have hεmem : (p : F)⁻¹ • T ∈ Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F)) :=
    Subalgebra.smul_mem _ hTmem _
  have hεε : ((p : F)⁻¹ • T) * ((p : F)⁻¹ • T) = (p : F)⁻¹ • T := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hTT, smul_smul, smul_smul, hcc]
  have hsε : s * ((p : F)⁻¹ • T) = (p : F)⁻¹ • T := by
    rw [Matrix.mul_smul, hsT]
  have hiff : ∀ v : Fin N → F, ((p : F)⁻¹ • T) *ᵥ v = v ↔ s *ᵥ v = v := by
    intro v
    constructor
    · intro hv
      calc s *ᵥ v = s *ᵥ (((p : F)⁻¹ • T) *ᵥ v) := by rw [hv]
        _ = (s * ((p : F)⁻¹ • T)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
        _ = ((p : F)⁻¹ • T) *ᵥ v := by rw [hsε]
        _ = v := hv
    · intro hv
      have hpowv : ∀ i : ℕ, (s ^ i) *ᵥ v = v := by
        intro i
        induction i with
        | zero => rw [pow_zero, Matrix.one_mulVec]
        | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
      have hTv : T *ᵥ v = (p : F) • v := by
        rw [hTdef, Matrix.sum_mulVec]
        simp only [hpowv, Finset.sum_const, Finset.card_range]
        rw [Nat.cast_smul_eq_nsmul]
      rw [Matrix.smul_mulVec, hTv, smul_smul, hcp, one_smul]
  have hsc : ∀ a ∈ Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F)),
      ∃ c : F, a * ((p : F)⁻¹ • T) = c • ((p : F)⁻¹ • T) := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      refine ⟨1, ?_⟩
      rw [Set.mem_singleton_iff.mp hx, hsε, one_smul]
    | algebraMap r =>
      refine ⟨r, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
    | add x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      refine ⟨c + d, ?_⟩
      rw [add_mul, hc, hd, add_smul]
    | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      refine ⟨d * c, ?_⟩
      rw [mul_assoc, hd, Matrix.mul_smul, hc, smul_smul]
  have hεe : ∀ e : Matrix (Fin N) (Fin N) F, s * e = e → ((p : F)⁻¹ • T) * e = e := by
    intro e he
    have hpowe : ∀ i : ℕ, s ^ i * e = e := by
      intro i
      induction i with
      | zero => rw [pow_zero, one_mul]
      | succ k ih => rw [pow_succ, mul_assoc, he, ih]
    have hTe : T * e = (p : F) • e := by
      have h1 : T * e = (∑ i ∈ Finset.range p, s ^ i) * e := by rw [← hTdef]
      rw [h1, Finset.sum_mul]
      simp only [hpowe, Finset.sum_const, Finset.card_range]
      rw [Nat.cast_smul_eq_nsmul]
    rw [Matrix.smul_mul, hTe, smul_smul, hcp, one_smul]
  exact ⟨(p : F)⁻¹ • T, hεmem, hεε, hsε, hiff, hsc, hεe⟩

theorem isPrimIdemIn_of_smul_block {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (heA : e ∈ A)
    (hidem : IsIdempotentElem e) (hne : e ≠ 0) (hsc : ∀ a ∈ A, ∃ c : F, a * e = c • e) :
    IsPrimIdemIn A e ∧ blockDegree A e = 1 := by
  have hee : e * e = e := hidem
  refine ⟨?_, ?_⟩
  · unfold IsPrimIdemIn
    refine ⟨heA, hidem, hne, ?_⟩
    intro e' he'A he'idem he'e
    obtain ⟨c, hc⟩ := hsc e' he'A
    have he'eq : e' = c • e := by rw [← hc, he'e]
    have h2 : e' * e' = e' := he'idem
    rw [he'eq] at h2
    have h3 : (c * c) • e = c • e := by
      calc (c * c) • e = (c • e) * (c • e) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, hee, smul_smul]
        _ = c • e := h2
    have h4 : (c * c - c) • e = 0 := by
      rw [sub_smul, h3, sub_self]
    have hcc : c * c = c := by
      rcases smul_eq_zero.mp h4 with h5 | h5
      · exact sub_eq_zero.mp h5
      · exact absurd h5 hne
    have hc' : c * (c - 1) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp hc' with h6 | h6
    · left
      rw [he'eq, h6, zero_smul]
    · right
      rw [he'eq, sub_eq_zero.mp h6, one_smul]
  · have hM : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) = F ∙ e := by
      apply le_antisymm
      · rintro x ⟨a, ha, rfl⟩
        obtain ⟨c, hc⟩ := hsc a ha
        rw [LinearMap.mulRight_apply, hc]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
      · rw [Submodule.span_singleton_le_iff_mem]
        exact ⟨1, by simp, by rw [LinearMap.mulRight_apply, one_mul]⟩
    unfold blockDegree
    rw [hM]
    exact finrank_span_singleton hne

end Idem

section Scalar

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

theorem lift_pow_scalar_PSL (m f p : ℕ) {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {b : X} {s : GL (Fin (m + 1)) (GaloisField 2 f)}
    (hslift : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b) (hbp : b ^ p = 1) :
    ∃ u : (GaloisField 2 f)ˣ,
      s ^ p = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
  have hlift_one : IsGLLift Matrix.SpecialLinearGroup.toGL ψ
      (1 : GL (Fin (m + 1)) (GaloisField 2 f)) (1 : X) :=
    isGLLift_one (j := Matrix.SpecialLinearGroup.toGL) (ψ := ψ)
  have hslift_pow : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s ^ p) (b ^ p) :=
    hslift.pow p
  rw [hbp] at hslift_pow
  obtain ⟨c, hc⟩ :=
    isGLLift_unique_PSL m (GaloisField 2 f) ψ hψ hslift_pow hlift_one
  have hzmat : ((s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
      Matrix.scalar (Fin (m + 1)) c := by
    simpa using hc
  have hunit_sp : IsUnit (((s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) :=
    ⟨s ^ p, rfl⟩
  have hscalar : IsUnit (Matrix.scalar (Fin (m + 1)) c) := hzmat ▸ hunit_sp
  have hcne : c ≠ 0 := by
    have hdiag : IsUnit (fun _ : Fin (m + 1) => c) :=
      (Matrix.isUnit_diagonal (v := fun _ : Fin (m + 1) => c)).mp hscalar
    exact IsUnit.ne_zero ((Pi.isUnit_iff.mp hdiag) ⟨0, Nat.succ_pos m⟩)
  refine ⟨Units.mk0 c hcne, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, hzmat]
  simp

theorem isGLLift_mul_scalar {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι]
    [Field F] {j : U →* GL ι F} {ψ : U →* X} {s : GL ι F} {b : X} (hs : IsGLLift j ψ s b)
    (w : Fˣ) : IsGLLift j ψ (s * Matrix.GeneralLinearGroup.scalar ι w) b := by
  intro u
  obtain ⟨u', hj, hb⟩ := hs u
  refine ⟨u', ?_, hb⟩
  rw [hj]
  have hz : Commute (Matrix.GeneralLinearGroup.scalar ι w) (j u) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq
  have h1 : Matrix.GeneralLinearGroup.scalar ι w * j u *
      (Matrix.GeneralLinearGroup.scalar ι w)⁻¹ = j u := by
    rw [hz.eq]; group
  calc s * j u * s⁻¹ = s * (Matrix.GeneralLinearGroup.scalar ι w * j u *
        (Matrix.GeneralLinearGroup.scalar ι w)⁻¹) * s⁻¹ := by rw [h1]
    _ = (s * Matrix.GeneralLinearGroup.scalar ι w) * j u *
        (s * Matrix.GeneralLinearGroup.scalar ι w)⁻¹ := by group

theorem isGLLift_inj_centralizer {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι]
    [Field F] {j : U →* GL ι F} (hj : Function.Injective j) {ψ : U →* X} {s : GL ι F}
    {b b' : X} (hb : IsGLLift j ψ s b) (hb' : IsGLLift j ψ s b') :
    b' * b⁻¹ ∈ Subgroup.centralizer (ψ.range : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  obtain ⟨u₁, h₁j, h₁b⟩ := hb u
  obtain ⟨u₂, h₂j, h₂b⟩ := hb' u
  have hu : u₁ = u₂ := hj (h₁j.trans h₂j.symm)
  subst hu
  have h : b⁻¹ * ψ u * b = b'⁻¹ * ψ u * b' := h₁b.trans h₂b.symm
  calc ψ u * (b' * b⁻¹) = b' * (b'⁻¹ * ψ u * b') * b⁻¹ := by group
    _ = b' * (b⁻¹ * ψ u * b) * b⁻¹ := by rw [h]
    _ = b' * b⁻¹ * ψ u := by group

theorem exists_nonpow_lift {F : Type} [Field F] [Finite F] [CharP F 2] {N p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card Fˣ) {S : Set (GL (Fin N) F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix (Fin N) (Fin N) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hpow : ∀ s ∈ S, ∃ u : Fˣ, s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u) :
    ∃ s ∈ S, ∃ u : Fˣ, s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u ∧
      ∀ μ : F, μ ^ p ≠ (u : F) := by
  classical
  by_contra hcon
  have hcon' : ∀ s ∈ S, ∀ u : Fˣ, s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u →
      ∃ μ : F, μ ^ p = (u : F) := by
    intro s hs u hu
    by_contra hno
    exact hcon ⟨s, hs, u, hu, fun μ hμ => hno ⟨μ, hμ⟩⟩
  obtain ⟨K, instF, instA, instFin, π, hsurj, hker, hfin⟩ := exists_blockField hS hodd he
  have hrange : ∀ a : Algebra.adjoin F (Units.val '' S), π a ∈ (algebraMap F K).range := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨u, hu⟩ := hpow s hs
      obtain ⟨μ, hμ⟩ := hcon' s hs u hu
      have hpow' : (⟨(s : Matrix (Fin N) (Fin N) F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ :
          Algebra.adjoin F (Units.val '' S)) ^ p = algebraMap F _ (u : F) := by
        apply Subtype.ext
        have h1 : ((s ^ p : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) =
            (s : Matrix (Fin N) (Fin N) F) ^ p := Units.val_pow_eq_pow_val _ _
        rw [hu, Matrix.GeneralLinearGroup.coe_scalar] at h1
        show (s : Matrix (Fin N) (Fin N) F) ^ p = algebraMap F (Matrix (Fin N) (Fin N) F) u
        rw [← h1, Algebra.algebraMap_eq_smul_one]
        ext i j
        simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      have hπ : π (⟨(s : Matrix (Fin N) (Fin N) F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ ^ p) =
          algebraMap F K (u : F) := by
        rw [hpow']
        exact π.commutes _
      refine mem_range_algebraMap_of_pow_eq_pow (F := F) (K := K) hp hpF (μ := μ) ?_
      rw [← map_pow π, hπ, ← hμ, map_pow]
    | algebraMap r => exact ⟨r, (π.commutes r).symm⟩
    | add x y hx hy hx' hy' =>
      show π (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
      rw [map_add]
      exact add_mem hx' hy'
    | mul x y hx hy hx' hy' =>
      show π (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
      rw [map_mul]
      exact mul_mem hx' hy'
  have hone : Module.finrank F K = 1 := by
    rw [finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero]
    intro w
    obtain ⟨a, rfl⟩ := hsurj w
    obtain ⟨r, hr⟩ := hrange a
    exact ⟨r, by rw [Algebra.smul_def, mul_one]; exact hr⟩
  omega

end Scalar

section Card

open CFSG.Assembly CFSG.StandardType.ClassicalPosition

private lemma tcPSL_diag_pow_entry {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (m : ℕ)
    (h : (Matrix.diagonal d) ^ m = 1) (i : Fin n) : d i ^ m = 1 := by
  have h' := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) h
  simpa [Matrix.diagonal_pow] using h'

theorem dvd_card_specialLinear {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 2 ≤ n)
    (hpK : p ∣ Nat.card K - 1) :
    p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  obtain ⟨i0, i1, hi⟩ : ∃ i0 i1 : Fin n, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      have := congrArg Fin.val h
      simp at this⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin n → K,
      d = fun i => if i = i0 then (ζ : K) else if i = i1 then ((ζ⁻¹ : Kˣ) : K) else 1 :=
    ⟨_, rfl⟩
  have hfac : ∀ i, d i = (if i = i0 then (ζ : K) else 1) *
      (if i = i1 then ((ζ⁻¹ : Kˣ) : K) else 1) := by
    intro i
    by_cases h0 : i = i0
    · simp [hd, h0, hi]
    · by_cases h1 : i = i1
      · simp [hd, h1, Ne.symm hi]
      · simp [hd, h0, h1]
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    simp only [hfac]
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq']
  obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
    ⟨⟨Matrix.diagonal d, hdet⟩, rfl⟩
  have hdvd : orderOf ζ ∣ orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    have hpow : (Matrix.diagonal d) ^ orderOf g = 1 := by
      rw [← hg, ← Matrix.SpecialLinearGroup.coe_pow]
      simp only [pow_orderOf_eq_one, Matrix.SpecialLinearGroup.coe_one]
    have h0 := tcPSL_diag_pow_entry d (orderOf g) hpow i0
    apply Units.ext
    simpa [hd] using h0
  have hdvd' : Nat.card K - 1 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [← hord]
    exact dvd_trans hdvd (orderOf_dvd_natCard g)
  exact dvd_trans hpK hdvd'

end Card

section Comp

open CFSG.Assembly CFSG.StandardType.ClassicalPosition

private theorem tcPSL_gw_of_assembly {X : Type} [Group X] {Q K : Subgroup X}
    (h : IsComponentOf K Q) : CFSG.GorensteinWalter.IsComponentOf K Q := by
  obtain ⟨hle, hsub, hq⟩ := h
  have hquot : Nontrivial (K ⧸ Subgroup.center K) := hq.2.toNontrivial
  have hnt : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  exact ⟨hle, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hle).1 hsub, hnt, hq.1, hq.2⟩

private theorem tcPSL_mul_comm_of_ne {X : Type} [Group X] [Finite X] {Q K₁ K₂ : Subgroup X}
    (h₁ : IsComponentOf K₁ Q) (h₂ : IsComponentOf K₂ Q) (hne : K₁ ≠ K₂) {a b : X}
    (ha : a ∈ K₁) (hb : b ∈ K₂) : a * b = b * a := by
  have h := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.commutator_eq_bot_of_ne
    (tcPSL_gw_of_assembly h₁) (tcPSL_gw_of_assembly h₂) hne
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at hmem
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hmem, one_mul]

private theorem tcPSL_subsingleton_of_comm {G : Type*} [Group G] (hG : commutator G = ⊤)
    (hcomm : ∀ x y : G, x * y = y * x) : Subsingleton G := by
  have hbot : commutator G ≤ ⊥ := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm x y
  rw [hG] at hbot
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Subgroup G) := hbot (Subgroup.mem_top x)
  have hy : y ∈ (⊥ : Subgroup G) := hbot (Subgroup.mem_top y)
  rw [Subgroup.mem_bot] at hx hy
  rw [hx, hy]

theorem isComponentOf_map_of_normal {U X : Type} [Group U] [Group X] (ψ : U →* X)
    (hψ : ψ.ker ≤ Subgroup.center U) {C H : Subgroup U} (hHC : H ≤ C)
    (hnorm : (H.subgroupOf C).Normal) (hq : IsQuasisimple ↥H) :
    IsComponentOf (H.map ψ) (C.map ψ) := by
  have hle : H.map ψ ≤ C.map ψ := Subgroup.map_mono hHC
  have hnormMap : ((H.map ψ).subgroupOf (C.map ψ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ _ ⟨h, hh, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * h * c⁻¹, (Subgroup.normal_subgroupOf_iff hHC).mp hnorm h c hh hc, by simp⟩
  have hker : (ψ.subgroupMap H).ker ≤ Subgroup.center ↥H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (x : U) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hψ hx') (g : U)
  have hmap : CFSG.IsQuasisimple ↥(H.map ψ) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq (ψ.subgroupMap H)
      (ψ.subgroupMap_surjective H) hker
  exact ⟨hle, CFSG.Assembly.IsSubnormal.step hle hnormMap (CFSG.Assembly.IsSubnormal.refl _),
    ⟨hmap.1.commutator_eq_top, hmap.2.1⟩⟩

theorem eq_of_isComponentOf_of_le {X : Type} [Group X] [Finite X] {Q K₁ K₂ J : Subgroup X}
    (h₁ : IsComponentOf K₁ Q) (h₂ : IsComponentOf K₂ Q) (hJ : IsQuasisimple ↥J) (hJ₁ : J ≤ K₁)
    (hJ₂ : J ≤ K₂) : K₁ = K₂ := by
  by_contra hne
  have hcomm : ∀ x y : ↥J, x * y = y * x := by
    intro x y
    apply Subtype.ext
    exact tcPSL_mul_comm_of_ne h₁ h₂ hne (hJ₁ x.2) (hJ₂ y.2)
  have hsub : Subsingleton ↥J := tcPSL_subsingleton_of_comm hJ.1.commutator_eq_top hcomm
  have hquot : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.1.toNontrivial
  have hnt : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  obtain ⟨a, b, hab⟩ := hnt
  exact hab (Subsingleton.elim a b)

end Comp

section CentLift

open CFSG.Assembly CFSG.StandardType.ClassicalPosition

private lemma tcPSL_conj_pow {G : Type*} [Group G] (s g Z : G) (hZ : ∀ h : G, Commute h Z)
    (hsg : s * g * s⁻¹ = Z * g) (k : ℕ) : s ^ k * g * (s ^ k)⁻¹ = Z ^ k * g := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : s * Z ^ k * s⁻¹ = Z ^ k := by
      rw [((hZ s).pow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    calc s ^ (k + 1) * g * (s ^ (k + 1))⁻¹
        = s * (s ^ k * g * (s ^ k)⁻¹) * s⁻¹ := by group
      _ = s * (Z ^ k * g) * s⁻¹ := by rw [ih]
      _ = (s * Z ^ k * s⁻¹) * (s * g * s⁻¹) := by group
      _ = Z ^ k * (Z * g) := by rw [hc, hsg]
      _ = Z ^ (k + 1) * g := by rw [pow_succ, mul_assoc]

private lemma tcPSL_toGL_central {m f : ℕ}
    (z : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (h : Matrix.GeneralLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :
    Commute h (Matrix.SpecialLinearGroup.toGL z) := by
  obtain ⟨r, -, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hcoe : (Matrix.SpecialLinearGroup.toGL z :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = Matrix.scalar (Fin (m + 1)) r :=
    hzr.symm
  show h * Matrix.SpecialLinearGroup.toGL z = Matrix.SpecialLinearGroup.toGL z * h
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hcoe]
  exact ((Matrix.scalar_commute r (fun _ => Commute.all _ _) _).symm).eq

private lemma tcPSL_toGL_central_eq_one {m f p : ℕ} (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card (GaloisField 2 f)ˣ)
    (z : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hzp : Matrix.SpecialLinearGroup.toGL z ^ p = 1) :
    Matrix.SpecialLinearGroup.toGL z = 1 := by
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hcoe : (Matrix.SpecialLinearGroup.toGL z :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = Matrix.scalar (Fin (m + 1)) r :=
    hzr.symm
  have hrp : r ^ p = 1 := by
    have h1 := congrArg Units.val hzp
    rw [Units.val_pow_eq_pow_val, Units.val_one, hcoe,
      ← map_pow (Matrix.scalar (Fin (m + 1))) r p] at h1
    have h2 : Matrix.scalar (Fin (m + 1)) (r ^ p) = Matrix.scalar (Fin (m + 1)) 1 := by
      rw [h1, map_one]
    exact Matrix.scalar_inj.mp h2
  have hr0 : r ≠ 0 := by
    rintro rfl
    have hm : m + 1 ≠ 0 := by omega
    rw [Fintype.card_fin, zero_pow hm] at hr
    exact zero_ne_one hr
  obtain ⟨c, hc⟩ : ∃ c : (GaloisField 2 f)ˣ, (c : GaloisField 2 f) = r :=
    ⟨Units.mk0 r hr0, rfl⟩
  have hcp : c ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc, hrp, Units.val_one])
  have hord : orderOf c = 1 := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hcp) with h | h
    · exact h
    · have hpd : p ∣ Nat.card (GaloisField 2 f)ˣ := by
        rw [← h]
        exact orderOf_dvd_natCard c
      exact absurd hpd hpF
  have hr1 : r = 1 := by rw [← hc, orderOf_eq_one_iff.mp hord, Units.val_one]
  apply Units.ext
  rw [Units.val_one, hcoe, hr1, map_one]

theorem comap_centralizer_eq_of_lift (m f p : ℕ) (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card (GaloisField 2 f)ˣ) {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {y : X} {s : GL (Fin (m + 1)) (GaloisField 2 f)}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s y) (hsp : s ^ p = 1) :
    (Subgroup.centralizer ({y} : Set X)).comap ψ =
      (Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f)))).comap
        Matrix.SpecialLinearGroup.toGL := by
  ext u
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨u', hu1, hu2⟩ := hs u
  constructor
  · intro hcomm
    have hyψ : y⁻¹ * ψ u * y = ψ u :=
      calc y⁻¹ * ψ u * y = y⁻¹ * (ψ u * y) := mul_assoc _ _ _
        _ = y⁻¹ * (y * ψ u) := by rw [hcomm]
        _ = ψ u := inv_mul_cancel_left y (ψ u)
    have hψu' : ψ u' = ψ u := hu2.symm.trans hyψ
    have hker : u' * u⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψu', mul_inv_cancel]
    have hcen := hψ hker
    have hGL : Matrix.SpecialLinearGroup.toGL u' =
        Matrix.SpecialLinearGroup.toGL (u' * u⁻¹) * Matrix.SpecialLinearGroup.toGL u := by
      rw [← map_mul, inv_mul_cancel_right]
    have hsg : s * Matrix.SpecialLinearGroup.toGL u * s⁻¹ =
        Matrix.SpecialLinearGroup.toGL (u' * u⁻¹) * Matrix.SpecialLinearGroup.toGL u :=
      hu1.symm.trans hGL
    have hiter := tcPSL_conj_pow s (Matrix.SpecialLinearGroup.toGL u)
      (Matrix.SpecialLinearGroup.toGL (u' * u⁻¹)) (tcPSL_toGL_central _ hcen) hsg p
    rw [hsp, inv_one, one_mul, mul_one] at hiter
    have hzp : Matrix.SpecialLinearGroup.toGL (u' * u⁻¹) ^ p = 1 :=
      mul_right_cancel (hiter.symm.trans (one_mul (Matrix.SpecialLinearGroup.toGL u)).symm)
    have hZ1 := tcPSL_toGL_central_eq_one hp hpF _ hcen hzp
    have hcomm' : s * Matrix.SpecialLinearGroup.toGL u * s⁻¹ =
        Matrix.SpecialLinearGroup.toGL u := by
      rw [hsg, hZ1, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hcomm').symm
  · intro hcomm
    have hcomm' : s * Matrix.SpecialLinearGroup.toGL u * s⁻¹ =
        Matrix.SpecialLinearGroup.toGL u := by
      rw [← hcomm, mul_inv_cancel_right]
    have hu'u : u' = u := Matrix.SpecialLinearGroup.toGL_injective (hu1.trans hcomm')
    rw [hu'u] at hu2
    calc ψ u * y = y * (y⁻¹ * ψ u * y) := by group
      _ = y * ψ u := by rw [hu2]

end CentLift

section Zpowers

open CFSG.Assembly
open scoped commutatorElement

private theorem tcPSL_conj_central {U : Type} [Group U] {z : U} (hz : z ∈ Subgroup.center U)
    (w : U) : z * w * z⁻¹ = w := by
  rw [← Subgroup.mem_center_iff.mp hz w, mul_inv_cancel_right]

private theorem tcPSL_comm_central_left {U : Type} [Group U] {z : U} (hz : z ∈ Subgroup.center U)
    (a b : U) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  calc ⁅z * a, b⁆ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [tcPSL_conj_central hz]
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]

private theorem tcPSL_comm_central_right {U : Type} [Group U] {z : U} (hz : z ∈ Subgroup.center U)
    (a b : U) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  calc ⁅a, z * b⁆ = a * (z * (b * a⁻¹ * b⁻¹) * z⁻¹) := by
        rw [commutatorElement_def]; group
    _ = a * (b * a⁻¹ * b⁻¹) := by rw [tcPSL_conj_central hz]
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group

theorem exists_pow_eq_of_mem_zpowers {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {x g : G}
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hg1 : g ≠ 1) (hg : g ∈ Subgroup.zpowers x) :
    ∃ j : ℕ, x = g ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  have hordx : orderOf x = p := orderOf_eq_prime hxp hx1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hgp : g ^ p = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm k (p : ℤ), zpow_mul, zpow_natCast, hxp,
      one_zpow]
  have hordg : orderOf g = p := orderOf_eq_prime hgp hg1
  have hcard : Nat.card (Subgroup.zpowers g) = Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hordg, hordx]
  have hfin : Finite (Subgroup.zpowers x) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zpowers, hordx]
    exact hp.ne_zero
  have hle : Subgroup.zpowers g ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hg
  have heq : Subgroup.zpowers g = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hxg : x ∈ Subgroup.zpowers g := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxg
  have hmod : g ^ (m % (p : ℤ)) = g ^ m := by
    have h1 := zpow_mod_orderOf g m
    rw [hordg] at h1
    exact h1
  have hnn : 0 ≤ m % (p : ℤ) := Int.emod_nonneg m (by exact_mod_cast hp.ne_zero)
  refine ⟨(m % (p : ℤ)).toNat, ?_⟩
  rw [← hm, ← hmod, ← zpow_natCast, Int.toNat_of_nonneg hnn]

theorem le_of_map_le_of_perfect {U Y : Type} [Group U] [Group Y] (ψ : U →* Y)
    (hψ : ψ.ker ≤ Subgroup.center U) {H J' : Subgroup U} (hH : commutator ↥H = ⊤)
    (hmap : H.map ψ ≤ J'.map ψ) : H ≤ J' := by
  have key : ∀ h ∈ H, ∃ v ∈ J', ∃ z ∈ Subgroup.center U, h = z * v := by
    intro h hh
    obtain ⟨v, hv, hψv⟩ := Subgroup.mem_map.mp (hmap (Subgroup.mem_map_of_mem ψ hh))
    refine ⟨v, hv, h * v⁻¹, hψ ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψv, mul_inv_cancel]
  have hcomm : ⁅H, H⁆ ≤ J' := by
    rw [Subgroup.commutator_le]
    intro h₁ hh₁ h₂ hh₂
    obtain ⟨v₁, hv₁, z₁, hz₁, rfl⟩ := key h₁ hh₁
    obtain ⟨v₂, hv₂, z₂, hz₂, rfl⟩ := key h₂ hh₂
    rw [tcPSL_comm_central_left hz₁, tcPSL_comm_central_right hz₂, commutatorElement_def]
    exact J'.mul_mem (J'.mul_mem (J'.mul_mem hv₁ hv₂) (J'.inv_mem hv₁)) (J'.inv_mem hv₂)
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomm_map : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator, Subgroup.map_commutator, htop]
  have hHeq : H ≤ ⁅H, H⁆ := by
    intro h hh
    have hmem : (⟨h, hh⟩ : ↥H) ∈ commutator ↥H := by
      rw [hH]
      exact Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem H.subtype hmem
    rw [hcomm_map] at h2
    exact h2
  exact hHeq.trans hcomm

end Zpowers

section InnerDiag

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private def tcPSL_conjAut {Y : Type} [Group Y] (H : Subgroup Y) (b : Y)
    (h1 : ∀ y ∈ H, b⁻¹ * y * b ∈ H) (h2 : ∀ y ∈ H, b * y * b⁻¹ ∈ H) : MulAut ↥H where
  toFun y := ⟨b⁻¹ * (y : Y) * b, h1 y y.2⟩
  invFun y := ⟨b * (y : Y) * b⁻¹, h2 y y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private theorem tcPSL_conj_mem {m' f : ℕ} {Y : Type} [Group Y]
    (φ : Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f) →* Y) {c : Y}
    (hc : ∃ A : GL (Fin (m' + 1)) (GaloisField 2 f), ∀ u,
      c⁻¹ * φ u * c = φ (InnerDiagA.conjSL A u))
    {y : Y} (hy : y ∈ φ.range) : c⁻¹ * y * c ∈ φ.range := by
  obtain ⟨A, hA⟩ := hc
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy
  exact MonoidHom.mem_range.mpr ⟨InnerDiagA.conjSL A u, (hA u).symm⟩

private theorem tcPSL_le_normalizer {m' f : ℕ} {Y : Type} [Group Y]
    (φ : Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f) →* Y) (Bs : Subgroup Y)
    (hconj : ∀ b ∈ Bs, ∃ A : GL (Fin (m' + 1)) (GaloisField 2 f), ∀ u,
      b⁻¹ * φ u * b = φ (InnerDiagA.conjSL A u)) :
    Bs ≤ Subgroup.normalizer ((φ.range : Subgroup Y) : Set Y) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h' := tcPSL_conj_mem φ (hconj b⁻¹ (inv_mem hb)) hh
    rw [inv_inv] at h'
    exact h'
  · intro hh
    have h' := tcPSL_conj_mem φ (hconj b hb) hh
    have e : b⁻¹ * (b * h * b⁻¹) * b = h := by group
    rw [e] at h'
    exact h'

theorem ggInnerDiagOn_of_conj {m' f : ℕ} {Y : Type} [Group Y] (hm1 : 1 ≤ m') (hf : 1 ≤ f)
    (hm1' : m' = 1 → 2 ≤ f)
    (φ : Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f) →* Y)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f)))
    (Bs : Subgroup Y)
    (hconj : ∀ b ∈ Bs, ∃ A : GL (Fin (m' + 1)) (GaloisField 2 f), ∀ u,
      b⁻¹ * φ u * b = φ (InnerDiagA.conjSL A u)) :
    GGInnerDiagOn Bs φ.range := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hker' : φ.rangeRestrict.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f)) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hmark := CFSG.StandardType.KGND.largeEvenMarking_slConjSet
    (m := m') (F := GaloisField 2 f) hF hf hm1 hm1' φ.rangeRestrict
    (MonoidHom.rangeRestrict_surjective φ) hker'
  unfold GGInnerDiagOn
  refine CFSG.StandardType.largeEvenMarking_mono ?_ hmark
  rintro lab R _ I F θ ⟨-, hψ⟩
  refine ⟨tcPSL_le_normalizer φ Bs hconj, ?_⟩
  intro b hb
  have h1 : ∀ y ∈ φ.range, b⁻¹ * y * b ∈ φ.range := fun y hy =>
    tcPSL_conj_mem φ (hconj b hb) hy
  have h2 : ∀ y ∈ φ.range, b * y * b⁻¹ ∈ φ.range := fun y hy => by
    have h' := tcPSL_conj_mem φ (hconj b⁻¹ (inv_mem hb)) hy
    rw [inv_inv] at h'
    exact h'
  let α : MulAut ↥φ.range := tcPSL_conjAut φ.range b h1 h2
  have hα : α ∈ CFSG.StandardType.KGND.slConjSet φ.rangeRestrict := by
    obtain ⟨A, hA⟩ := hconj b hb
    refine ⟨A, fun B => Subtype.ext ?_⟩
    exact hA B
  obtain ⟨ψ, hψI, hψeq⟩ := hψ α hα
  refine ⟨ψ, hψI, ?_⟩
  intro l l' hll
  have hll' : (l' : Y) = b⁻¹ * (l : Y) * b := hll
  have hαl : α l = l' := Subtype.ext hll'.symm
  rw [hψeq l, hαl]

end InnerDiag

section QuotCenter

lemma quotCenter_mulEquiv_of_perfect {G Y : Type} [Group G] [Group Y] [Group.IsPerfect G]
    (θ : G →* Y) (hker : θ.ker ≤ Subgroup.center G) (H : Subgroup Y) (hH : θ.range = H) :
    Nonempty (↥H ⧸ Subgroup.center ↥H ≃* G ⧸ Subgroup.center G) := by
  subst hH
  let fmap : G →* ↥(θ.range) := θ.rangeRestrict
  have hf : Function.Surjective fmap := θ.rangeRestrict_surjective
  have hkerf : fmap.ker ≤ Subgroup.center G := (MonoidHom.ker_rangeRestrict θ).le.trans hker
  have hcen : Subgroup.center (G ⧸ fmap.ker) =
      (Subgroup.center G).map (QuotientGroup.mk' fmap.ker) :=
    (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' fmap.ker) (QuotientGroup.mk'_surjective fmap.ker)
      (by rwa [QuotientGroup.ker_mk'])).symm
  let e1 : G ⧸ fmap.ker ≃* ↥(θ.range) := QuotientGroup.quotientKerEquivOfSurjective fmap hf
  let e2 : ↥(θ.range) ⧸ Subgroup.center ↥(θ.range) ≃*
      (G ⧸ fmap.ker) ⧸ Subgroup.center (G ⧸ fmap.ker) :=
    QuotientGroup.congr (Subgroup.center ↥(θ.range)) (Subgroup.center (G ⧸ fmap.ker))
      e1.symm (Subgroup.map_center_eq e1.symm)
  exact ⟨e2.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hkerf))⟩

end QuotCenter

end CFSG.StandardType.TableCRes
