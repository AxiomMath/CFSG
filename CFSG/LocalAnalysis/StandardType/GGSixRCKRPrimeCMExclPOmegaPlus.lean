module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMExclusion
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftHomPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma rckPOmegaPlus_ker_centralizer {n f : ℕ} {X : Type} [Group X]
    {B₁ K : Subgroup X}
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {J' : Subgroup (spinGroup (Spin.quadPlus n (GaloisField 2 f)))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
      {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε)
    (hJ'K : J'.map ψ = K) {m Q : ℕ} {E : Type} [Field E]
    (Φ : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε) ≃*
      ↥(ClassicalBlocks.GUFull m Q E))
    (β : ↥B₁ →* ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε))
    (hβact : ∀ (b : ↥B₁) (y : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
      y ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε →
      (b : X) * ψ y * (b : X)⁻¹ =
        ψ ((β b : spinGroup (Spin.quadPlus n (GaloisField 2 f))) * y *
          (β b : spinGroup (Spin.quadPlus n (GaloisField 2 f)))⁻¹)) :
    ∀ b : ↥B₁,
      ((QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
        (ClassicalBlocks.GUFull m Q E))).comp (Φ.toMonoidHom.comp β)) b = 1 →
      (b : X) ∈ Subgroup.centralizer (K : Set X) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨y, hyJ', hyk⟩ := Subgroup.mem_map.mp (by rwa [← hJ'K] at hk)
  let Gε := ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
    {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε)
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
  have hcentral' : ((β b : Gε) : spinGroup (Spin.quadPlus n (GaloisField 2 f))) * y *
      (((β b : Gε) : spinGroup (Spin.quadPlus n (GaloisField 2 f))))⁻¹ = y := by
    have h := congrArg (fun z : Gε =>
      (z : spinGroup (Spin.quadPlus n (GaloisField 2 f)))) hcentral
    simp only [yε, Gε, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hact := hβact b y (hJ'G hyJ')
  rw [hcentral'] at hact
  rw [← hyk]
  exact (mul_inv_eq_iff_eq_mul.mp hact).symm

theorem rckEq_of_block_unitarySmall_POmegaPlus {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B₁ D J K : Subgroup X} {d e : X}
    (hB₁ : IsElemAbelian p B₁) (hDcard : Nat.card D = p ^ 2)
    (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hp4 : p ^ 4 ≤ Nat.card B₁) (hJK : J ≤ K)
    (hK : IsQuasisimple ↥K) (hdD : d ∈ D) (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))))
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s})) ε)
    {J' : Subgroup (spinGroup (Spin.quadPlus n (GaloisField 2 f)))}
    (hJ'G : J' ≤ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
      {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε) (hJ'K : J'.map ψ = K)
    (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ID : ∀ b ∈ B₁, GGPsiInnerDiag (Spin.plusDatum n (GaloisField 2 f) hn) ψ b)
    (hB₁e : ∀ b ∈ B₁, Commute b e) {m Q : ℕ} (hm : m ≤ 3) {E : Type} [Field E] [Finite E]
    [CharP E 2]
    (Φ : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε) ≃*
      ↥(ClassicalBlocks.GUFull m Q E)) :
    K = J := by
  obtain ⟨β, hβact⟩ := exists_rckRestrictLiftHom_POmegaPlus hn hker hs hε
    (p := p) (hp.odd_of_ne_two hp2) (fun b hb => hB₁.2 b hb) hB₁N hB₁ID hB₁e
  let β' : ↥B₁ →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E) :=
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E))).comp (Φ.toMonoidHom.comp β)
  refine rckEq_of_blockAction hp hDcard hB₁J hp4 hJK hK hdD hJ β' ?_ ?_
  · exact rckPOmegaPlus_ker_centralizer hJ'G hJ'K Φ β hβact
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
