module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMExclusion
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftHomPSp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma rckExclPSp_pow_le_sq_of_dvd_720 {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ j ∣ 720) : p ^ j ≤ p ^ 2 := by
  by_cases hj : j ≤ 2
  · exact pow_le_pow_right₀ hp.one_le hj
  · have hj3 : 3 ≤ j := by omega
    have h3 : p ^ 3 ∣ 720 := (pow_dvd_pow p hj3).trans h
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hcop : Nat.Coprime (p ^ 3) (2 ^ 4) :=
      (hpodd.coprime_two_right.pow_left 3).pow_right 4
    have h3' : p ^ 3 ∣ 45 := by
      have h720 : 720 = 2 ^ 4 * 45 := by norm_num
      rw [h720] at h3
      exact hcop.dvd_of_dvd_mul_left h3
    have h3le : p ^ 3 ≤ 45 := Nat.le_of_dvd (by norm_num) h3'
    have hp3le : p ≤ 3 := by
      by_contra hgt
      have h4 : 4 ≤ p := by omega
      have h64 : 4 ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by norm_num) h4 3
      norm_num at h64
      omega
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · exact absurd rfl hp2
    · norm_num at h3'

theorem rckEq_of_block_Sp4Two {n f : ℕ} {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B₁ D J K : Subgroup X} {d e : X} (hB₁ : IsElemAbelian p B₁)
    (hDcard : Nat.card D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hp4 : p ^ 4 ≤ Nat.card B₁) (hJK : J ≤ K) (hK : IsQuasisimple ↥K) (hdD : d ∈ D)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X} (hker : ψ.ker ≤ Subgroup.center _)
    {s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
          Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJ'G : J' ≤ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε) (hJ'K : J'.map ψ = K)
    (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ID : ∀ b ∈ B₁, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hB₁e : ∀ b ∈ B₁, Commute b e) (hF : Nat.card (GaloisField 2 f) = 2)
    (Φ : ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε) ≃*
      ↥(CFSG.Open.StatedSp 2 (GaloisField 2 f))) :
    K = J := by
  obtain ⟨β, hβact⟩ := exists_rckRestrictLiftHom_PSp hker hs hε hB₁N hB₁ID hB₁e
  refine rckEq_of_blockAction hp hDcard hB₁J hp4 hJK hK hdD hJ β ?_ ?_
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨y, hyJ', hyk⟩ := Subgroup.mem_map.mp (by rwa [← hJ'K] at hk)
    have hact := hβact b (y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) (hJ'G hyJ')
    rw [hb] at hact
    simp only [Subgroup.coe_one, one_mul, inv_one, mul_one] at hact
    rw [← hyk]
    exact (mul_inv_eq_iff_eq_mul.mp hact).symm
  · have htop : IsElemAbelian p (⊤ : Subgroup ↥B₁) := by
      simpa using hB₁.subgroupOf B₁
    have hβel : IsElemAbelian p β.range := by
      simpa [MonoidHom.range_eq_map] using htop.map β
    have hβp : IsPGroup p β.range := hβel.isPGroup
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hβp
    have hcardG : Nat.card ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε) = 720 := by
      rw [Nat.card_congr Φ.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hF]
      norm_num
    have hdvd : Nat.card β.range ∣ 720 := by
      have h := Subgroup.card_subgroup_dvd_card β.range
      rwa [hcardG] at h
    rw [hj]
    exact rckExclPSp_pow_le_sq_of_dvd_720 hp hp2 (by rwa [hj] at hdvd)

private lemma rckExclPSp_unitary_range_card_le {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B₁ : Subgroup X} (hB₁ : IsElemAbelian p B₁)
    {m Q : ℕ} (hm : m ≤ 3) {E : Type} [Field E] [Finite E] [CharP E 2]
    (β' : ↥B₁ →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E)) :
    Nat.card β'.range ≤ p ^ 2 := by
  have htop : IsElemAbelian p (⊤ : Subgroup ↥B₁) := by
    simpa using hB₁.subgroupOf B₁
  have hE : IsElemAbelian p β'.range := by
    simpa [MonoidHom.range_eq_map] using htop.map β'
  have hpE : (p : E) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff E 2]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst m
    haveI : Subsingleton (GL (Fin 0) E) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Subsingleton (CFSG.Open.StatedProj (ClassicalBlocks.GUFull 0 Q E)) := inferInstance
    have hle1 : Nat.card β'.range ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    exact hle1.trans (Nat.one_le_pow 2 p hp.pos)
  · have hle := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_statedProj hp hp2 hpE hmpos
        (ClassicalBlocks.GUFull m Q E) β'.range hE
    have hm2 : m - 1 ≤ 2 := by omega
    exact hle.trans (pow_le_pow_right₀ hp.one_le hm2)

theorem rckEq_of_block_unitarySmall {n f : ℕ} {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B₁ D J K : Subgroup X} {d e : X} (hB₁ : IsElemAbelian p B₁)
    (hDcard : Nat.card D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hp4 : p ^ 4 ≤ Nat.card B₁) (hJK : J ≤ K) (hK : IsQuasisimple ↥K) (hdD : d ∈ D)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    {ψ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X} (hker : ψ.ker ≤ Subgroup.center _)
    {s : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} :
          Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJ'G : J' ≤ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε) (hJ'K : J'.map ψ = K)
    (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ID : ∀ b ∈ B₁, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hB₁e : ∀ b ∈ B₁, Commute b e) {m Q : ℕ} (hm : m ≤ 3) {E : Type} [Field E] [Finite E]
    [CharP E 2]
    (Φ : ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε) ≃* ↥(ClassicalBlocks.GUFull m Q E)) :
    K = J := by
  obtain ⟨β, hβact⟩ := exists_rckRestrictLiftHom_PSp hker hs hε hB₁N hB₁ID hB₁e
  let Gε := ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
    {(s : GL (Fin n ⊕ Fin n) (GaloisField 2 f))} ε)
  let β' : ↥B₁ →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E) :=
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E))).comp (Φ.toMonoidHom.comp β)
  refine rckEq_of_blockAction hp hDcard hB₁J hp4 hJK hK hdD hJ β' ?_ ?_
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨y, hyJ', hyk⟩ := Subgroup.mem_map.mp (by rwa [← hJ'K] at hk)
    have hb' : ((Φ (β b) : ↥(ClassicalBlocks.GUFull m Q E)) :
        CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E)) = 1 := by
      simpa [β'] using hb
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
    have hcentral' : ((β b : Gε) : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) *
        (y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) *
        (((β b : Gε) : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))))⁻¹ =
        (y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) := by
      have h := congrArg (fun z : Gε =>
        (z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))) hcentral
      simp only [yε, Gε, Subgroup.coe_mul, Subgroup.coe_inv] at h
      exact h
    have hact := hβact b (y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) (hJ'G hyJ')
    rw [hcentral'] at hact
    rw [← hyk]
    exact (mul_inv_eq_iff_eq_mul.mp hact).symm
  · exact rckExclPSp_unitary_range_card_le hp hp2 hB₁ hm β'

end CFSG.StandardType.RCKRP
