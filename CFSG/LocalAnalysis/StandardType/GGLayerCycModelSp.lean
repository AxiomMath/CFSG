module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresSp
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLabels
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.StandardType

namespace LayerCyc

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores

variable {m : ℕ} {K : Type} [Field K]

theorem scalar_eq_one_of_mem_statedSp [CharP K 2] (hm : 1 ≤ m) {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c ∈ StatedSp m K) : c = 1 := by
  have hJ := (mem_statedSp_iff_spJ (n := m) (F := K)).mp hc
  rw [GeneralLinearGroup.coe_scalar] at hJ
  have hentry := congrFun (congrFun hJ (.inl ⟨0, hm⟩)) (.inr ⟨0, hm⟩)
  simp [Matrix.scalar_apply, spJ] at hentry
  apply LayerFacts.eq_one_of_sq_eq_one_charTwo
  apply Units.ext
  simpa [sq] using hentry

theorem smul_mem_statedSp_of_gsp {A : GL (Fin m ⊕ Fin m) K} {l : Kˣ}
    (hA : (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * LargeEvenSpForm K m *
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = ((l : K) * l) • LargeEvenSpForm K m) :
    Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) l⁻¹ * A ∈ StatedSp m K := by
  have hA' : (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * spJ m K *
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = ((l : K) * l) • spJ m K := hA
  have hc : ((Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) l⁻¹ * A : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      ((l⁻¹ : Kˣ) : K) • (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hl : ((l⁻¹ : Kˣ) : K) * ((l⁻¹ : Kˣ) : K) * ((l : K) * l) = 1 := by
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  rw [mem_statedSp_iff_spJ, hc, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hA', smul_smul, hl, one_smul]

theorem ggModelLayerCyclic_gspConj [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hm : 1 ≤ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ Subgroup.normalizer (LargeEvenSpGroup K m : Set (GL (Fin m ⊕ Fin m) K)))
    (hAs : A ∈ LargeEvenGSpSet K m) : GGModelLayerCyclic p (ggMatConjAut hA) := by
  classical
  have := LayerCC.charP_two_of_natCard hK
  refine ggModelLayerCyclic_of_cycCoreFamily fun _ hαp => ?_
  set H := LargeEvenSpGroup K m with hHdef
  obtain ⟨μ, hμ, hAμ⟩ := hAs
  obtain ⟨l₀, hl₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) μ
  have hl₀0 : l₀ ≠ 0 := by
    rintro rfl
    exact hμ (by rw [hl₀, mul_zero])
  set l : Kˣ := Units.mk0 l₀ hl₀0 with hldef
  set z : GL (Fin m ⊕ Fin m) K := Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) l⁻¹ with hzdef
  set A' := z * A with hA'def
  have hA'sp : A' ∈ StatedSp m K := smul_mem_statedSp_of_gsp (l := l) (by rw [hAμ, hl₀]; rfl)
  have hz : z ∈ Subgroup.center (GL (Fin m ⊕ Fin m) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨l⁻¹, rfl⟩
  have hA'comm : ∀ g : GL (Fin m ⊕ Fin m) K, A' * g = g * A' ↔ A * g = g * A := by
    intro g
    have e1 : A' * g = z * (A * g) := by rw [hA'def, mul_assoc]
    have e2 : g * A' = z * (g * A) := by
      rw [hA'def, ← mul_assoc, Subgroup.mem_center_iff.mp hz g, mul_assoc]
    rw [e1, e2]
    exact (mul_right_injective z).eq_iff
  have hgen : ∀ (B : Subgroup.normalizer (H : Set (GL (Fin m ⊕ Fin m) K))) (h : H),
      ((H.normalizerMonoidHom B h : H) : GL (Fin m ⊕ Fin m) K) = B * h * B⁻¹ := fun _ _ => rfl
  have hpow : ∀ s ∈ H, A ^ p * s = s * A ^ p := by
    intro s hs
    have h1 := congrArg (fun φ : MulAut H => ((φ ⟨s, hs⟩ : H) : GL (Fin m ⊕ Fin m) K)) hαp
    simp only [MulAut.one_apply] at h1
    rw [ggMatConjAut, ← map_pow, hgen] at h1
    simp only [SubgroupClass.coe_pow, Subgroup.coe_inv] at h1
    rwa [mul_inv_eq_iff_eq_mul] at h1
  have hA'pow : ∀ s ∈ H, A' ^ p * s = s * A' ^ p := by
    intro s hs
    have hzA : Commute z A := (Subgroup.mem_center_iff.mp hz A).symm
    rw [hA'def, hzA.mul_pow, mul_assoc, hpow s hs, ← mul_assoc,
      ← Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz p) s, mul_assoc]
  have hA'p : A' ^ p = 1 := by
    have hmem : (⟨A' ^ p, Subgroup.pow_mem _ hA'sp p⟩ : StatedSp m K) ∈
        Subgroup.center (StatedSp m K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hA'pow g g.2).symm
    rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcsp : Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c ∈ StatedSp m K := by
      rw [hc]
      exact Subgroup.pow_mem _ hA'sp p
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c = A' ^ p := hc
    rw [← hc', scalar_eq_one_of_mem_statedSp hm hcsp, map_one]
  have hcard : (Nat.card (Subgroup.zpowers A') : K) ≠ 0 := by
    rw [Nat.card_zpowers, Ne, CharP.cast_eq_zero_iff K 2]
    intro h2
    have h2p : 2 ∣ p := h2.trans (orderOf_dvd_of_pow_eq_one hA'p)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  have hA₀sp : ∀ g ∈ Subgroup.zpowers A', g ∈ StatedSp m K := fun g hg =>
    (Subgroup.zpowers_le.mpr hA'sp) hg
  obtain ⟨β, S, hS⟩ := exists_cycCoreFamily_adjCent hcard isInvol_spAdj
    (fun X hX g hg => spAdj_mul_comm hA₀sp X hX hg) (exists_symd_spAdj hA₀sp hcard)
  have hcent : ∀ x : GL (Fin m ⊕ Fin m) K, x ∈ Subgroup.centralizer
      (Subgroup.zpowers A' : Set (GL (Fin m ⊕ Fin m) K)) ↔ A * x = x * A := by
    intro x
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff, eq_comm, hA'comm]
  have hle : adjCent (Subgroup.zpowers A') (isInvol_spAdj (n := m) (F := K)) ≤
      H.subtype.range := by
    intro g hg
    exact ⟨⟨g, mem_unitaryOf_spAdj_iff.mp (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
  have hC : (adjCent (Subgroup.zpowers A') (isInvol_spAdj (n := m) (F := K))).comap H.subtype =
      ggFix (ggMatConjAut hA) := by
    ext x
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, hcent, mem_ggFix]
    constructor
    · rintro ⟨hx, -⟩
      apply Subtype.ext
      rw [coe_ggMatConjAut]
      change A * (x : GL (Fin m ⊕ Fin m) K) = (x : GL (Fin m ⊕ Fin m) K) * A at hx
      rw [hx, mul_inv_cancel_right]
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [coe_ggMatConjAut, mul_inv_eq_iff_eq_mul] at h1
      exact ⟨h1, mem_unitaryOf_spAdj_iff.mpr x.2⟩
  have h := hS.comap H.subtype H.subtype_injective hle
  rw [hC] at h
  exact ⟨β, _, h⟩

end LayerCyc

open LayerCyc in
theorem ggLayerSymplecticModelInput_holds : GGLayerSymplecticModelInput := by
  intro m n K _ _ hK _ hm _ p hp hp2 A hA hAs
  exact ggModelLayerCyclic_gspConj hK (by omega) hp hp2 hA hAs

end CFSG.StandardType

end
