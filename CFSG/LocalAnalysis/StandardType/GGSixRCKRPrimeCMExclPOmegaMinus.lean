module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMExclusion
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftHomPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma rckPOmegaMinus_ker_centralizer {F : Type} [Field F] {n : ℕ} {bq cq : F}
    {X : Type} [Group X]
    {B₁ K : Subgroup X}
    {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    {s : spinGroup (Spin.quadMinus n F bq cq)}
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    {J' : Subgroup (spinGroup (Spin.quadMinus n F bq cq))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
      {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε)
    (hJ'K : J'.map ψ = K) {m Q : ℕ} {E : Type} [Field E]
    (Φ : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
        {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε) ≃*
      ↥(ClassicalBlocks.GUFull m Q E))
    (β : ↥B₁ →* ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
        {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε))
    (hβact : ∀ (b : ↥B₁) (y : spinGroup (Spin.quadMinus n F bq cq)),
      y ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
        {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε →
      (b : X) * ψ y * (b : X)⁻¹ =
        ψ ((β b : spinGroup (Spin.quadMinus n F bq cq)) * y *
          (β b : spinGroup (Spin.quadMinus n F bq cq))⁻¹)) :
    ∀ b : ↥B₁,
      ((QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
        (ClassicalBlocks.GUFull m Q E))).comp (Φ.toMonoidHom.comp β)) b = 1 →
      (b : X) ∈ Subgroup.centralizer (K : Set X) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨y, hyJ', hyk⟩ := Subgroup.mem_map.mp (by rwa [← hJ'K] at hk)
  let Gε := ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
    {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε)
  have hb' : ((Φ (β b) : ↥(ClassicalBlocks.GUFull m Q E)) :
      CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E)) = 1 := by
    simpa [MonoidHom.comp_apply, QuotientGroup.mk'_apply] using hb
  have hmem : Φ (β b) ∈ (CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E) :=
    (QuotientGroup.eq_one_iff (Φ (β b))).mp hb'
  have hscalar : (Φ (β b) : GL (Fin m) E) ∈ CFSG.Open.StatedScalars (Fin m) E :=
    Subgroup.mem_subgroupOf.mp hmem
  have hcenter : Φ (β b) ∈ Subgroup.center ↥(ClassicalBlocks.GUFull m Q E) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hgl : (Φ (β b) : GL (Fin m) E) ∈ Subgroup.center (GL (Fin m) E) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hscalar
    exact Subgroup.mem_center_iff.mp hgl (z : GL (Fin m) E)
  have hbc : β b ∈ Subgroup.center Gε :=
    (MulEquivClass.apply_mem_center_iff Φ).mp hcenter
  let yε : Gε := ⟨y, hJ'G hyJ'⟩
  have hcentral : (β b : Gε) * yε * (β b : Gε)⁻¹ = yε := by
    have hcomm : (β b : Gε) * yε = yε * (β b : Gε) :=
      (Subgroup.mem_center_iff.mp hbc yε).symm
    rw [hcomm]
    simp
  have hcentral' : ((β b : Gε) : spinGroup (Spin.quadMinus n F bq cq)) * y *
      (((β b : Gε) : spinGroup (Spin.quadMinus n F bq cq)))⁻¹ = y := by
    have h := congrArg (fun z : Gε =>
      (z : spinGroup (Spin.quadMinus n F bq cq))) hcentral
    simp only [yε, Gε, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hact := hβact b y (hJ'G hyJ')
  rw [hcentral'] at hact
  rw [← hyk]
  exact (mul_inv_eq_iff_eq_mul.mp hact).symm

theorem rckEq_of_block_unitarySmall_POmegaMinus {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B₁ D J K : Subgroup X} {d e : X}
    (hB₁ : IsElemAbelian p B₁) (hDcard : Nat.card D = p ^ 2)
    (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hp4 : p ^ 4 ≤ Nat.card B₁) (hJK : J ≤ K)
    (hK : IsQuasisimple ↥K) (hdD : d ∈ D) (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n F bq cq)))
    {s : spinGroup (Spin.quadMinus n F bq cq)}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F
        (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F
        (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε)
    {J' : Subgroup (spinGroup (Spin.quadMinus n F bq cq))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
      {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε) (hJ'K : J'.map ψ = K)
    (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ID : ∀ b ∈ B₁, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b)
    (hB₁e : ∀ b ∈ B₁, Commute b e) {m Q : ℕ} (hm : m ≤ 3) {E : Type} [Field E] [Finite E]
    [CharP E 2]
    (Φ : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
        {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε) ≃*
      ↥(ClassicalBlocks.GUFull m Q E)) :
    K = J := by
  obtain ⟨β, hβact⟩ := exists_rckRestrictLiftHom_POmegaMinus hirr hn hker hs hε
    (p := p) (hp.odd_of_ne_two hp2) (fun b hb => hB₁.2 b hb) hB₁N hB₁ID hB₁e
  let β' : ↥B₁ →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E) :=
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E))).comp (Φ.toMonoidHom.comp β)
  refine rckEq_of_blockAction hp hDcard hB₁J hp4 hJK hK hdD hJ β' ?_ ?_
  · exact rckPOmegaMinus_ker_centralizer hJ'G hJ'K Φ β hβact
  · have htop : IsElemAbelian p (⊤ : Subgroup ↥B₁) := by
      simpa using hB₁.subgroupOf B₁
    have hβel : IsElemAbelian p β'.range := by
      simpa [MonoidHom.range_eq_map] using htop.map β'
    have hpE : (p : E) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff E 2]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst m
      haveI : Subsingleton (GL (Fin 0) E) :=
        ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      haveI : Subsingleton (CFSG.Open.StatedProj (ClassicalBlocks.GUFull 0 Q E)) :=
        inferInstance
      have hle1 : Nat.card β'.range ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr inferInstance
      exact hle1.trans (Nat.one_le_pow 2 p hp.pos)
    · have hle := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_statedProj hp hp2 hpE hmpos
          (ClassicalBlocks.GUFull m Q E) β'.range hβel
      exact hle.trans (pow_le_pow_right₀ hp.one_le (by omega : m - 1 ≤ 2))

end CFSG.StandardType.RCKRP
