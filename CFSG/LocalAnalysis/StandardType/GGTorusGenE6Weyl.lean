module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Defs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem mem_centralizer_of_mem_T
    {M : Type} [Group M] {L' E : Subgroup M}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {T : Subgroup L'}
    (hfix : ∀ a ∈ (ggGamma L' hE).range, ∀ t ∈ T, a t = t)
    {t : L'} (ht : t ∈ T) :
    ((t : L') : M) ∈ Subgroup.centralizer (E : Set M) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hmem : ggGamma L' hE ⟨e, he⟩ ∈ (ggGamma L' hE).range := ⟨⟨e, he⟩, rfl⟩
  have hfixe := hfix (ggGamma L' hE ⟨e, he⟩) hmem t ht
  have hcoe := ggGamma_coe L' hE ⟨e, he⟩ t
  have hval : ((ggGamma L' hE ⟨e, he⟩ t : L') : M) = ((t : L') : M) := by
    rw [hfixe]
  have hconj : (e : M) * ((t : L') : M) * (e : M)⁻¹ = ((t : L') : M) := by
    rw [← hcoe]
    exact hval
  calc (e : M) * ((t : L') : M) = ((e : M) * ((t : L') : M) * (e : M)⁻¹) * (e : M) := by
        group
    _ = ((t : L') : M) * (e : M) := by rw [hconj]

theorem center_pElts_centralize_twE6
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} {T : Subgroup L'} {w : Fin 6 → L'}
    (hT : GGE6ThreeStrongWitness (ggQuotHom θ).ker (ggGamma L' hE).range T w) :
    ∀ z ∈ L' ⊓ Subgroup.centralizer (L' : Set M), z ^ 3 = 1 →
      z ∈ Subgroup.centralizer (E : Set M) := by
  intro z hz hz3
  obtain ⟨-, hTodd, hTfix, -, -, -⟩ := hT
  have hzL : z ∈ L' := hz.1
  have hzc : z ∈ Subgroup.centralizer (L' : Set M) := hz.2
  let z' : L' := ⟨z, hzL⟩
  have hz'center : z' ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzc g g.2
  have hz'3 : z' ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hz3
  have hodd : Odd (orderOf z') := by
    have hdvd : orderOf z' ∣ 3 := orderOf_dvd_of_pow_eq_one hz'3
    have hpos : 0 < orderOf z' := orderOf_pos z'
    have hle : orderOf z' ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : orderOf z' ≠ 2 := by
      intro h
      rw [h] at hdvd
      norm_num at hdvd
    have hcases : orderOf z' = 1 ∨ orderOf z' = 3 := by omega
    rcases hcases with h | h <;> rw [h] <;> norm_num
  have hz'ker : z' ∈ (ggQuotHom θ).ker := by
    rw [ker_ggQuotHom]
    exact hz'center
  have hzT : z' ∈ T := hTodd z' hz'ker hodd
  have hcent := mem_centralizer_of_mem_T (T := T) hTfix hzT
  exact hcent

theorem torus_pTorsion_mem_E_twE6
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition 3 L' E I θ hE)
    {T : Subgroup L'} {w : Fin 6 → L'}
    (hT : GGE6ThreeStrongWitness (ggQuotHom θ).ker (ggGamma L' hE).range T w)
    {t : L'} (ht : t ∈ T) (ht3 : t ^ 3 = 1) : ((t : L') : M) ∈ E := by
  obtain ⟨-, -, hTfix, -, -, -⟩ := hT
  have hmem : ((t : L') : M) ∈ E ⊔ L' := Subgroup.mem_sup_right t.2
  have hcent : ((t : L') : M) ∈ Subgroup.centralizer (E : Set M) :=
    mem_centralizer_of_mem_T (T := T) hTfix ht
  have hpow : ((t : L') : M) ^ 3 = 1 := by
    calc ((t : L') : M) ^ 3 = (((t ^ 3 : L')) : M) := (map_pow L'.subtype t 3).symm
      _ = ((1 : L') : M) := by rw [ht3]
      _ = 1 := map_one L'.subtype
  exact hpos.2.2.2.2.2.1 _ hmem hcent hpow

theorem weylLift_mem_normalizer_twE6
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition 3 L' E I θ hE)
    {T : Subgroup L'} {w : Fin 6 → L'}
    (hT : GGE6ThreeStrongWitness (ggQuotHom θ).ker (ggGamma L' hE).range T w) (i : Fin 6) :
    ((w i : L') : M) ∈ Subgroup.normalizer (E : Set M) := by
  apply TableBBridge.mem_normalizer_of_conj_mem
  intro e he
  have hmemA : ggGamma L' hE ⟨e, he⟩ ∈ (ggGamma L' hE).range := ⟨⟨e, he⟩, rfl⟩
  obtain ⟨hmemT, hpow3⟩ := hT.2.2.2.1 i (ggGamma L' hE ⟨e, he⟩) hmemA
  have hcoe : (((ggGamma L' hE ⟨e, he⟩) (w i) : L') : M) =
      (e : M) * ((w i : L') : M) * (e : M)⁻¹ :=
    ggGamma_coe L' hE ⟨e, he⟩ (w i)
  have hg : (((w i * ((ggGamma L' hE ⟨e, he⟩) (w i))⁻¹ : L')) : M) =
      ((w i : L') : M) * e * ((w i : L') : M)⁻¹ * e⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
    group
  have hgt : (((w i * ((ggGamma L' hE ⟨e, he⟩) (w i))⁻¹ : L')) : M) ∈ E :=
    torus_pTorsion_mem_E_twE6 hpos hT hmemT hpow3
  rw [show ((w i : L') : M) * e * ((w i : L') : M)⁻¹ =
      (((w i * ((ggGamma L' hE ⟨e, he⟩) (w i))⁻¹ : L')) : M) * e by
    rw [hg]
    group]
  exact E.mul_mem hgt he

end CFSG.StandardType
