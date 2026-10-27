module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUCore
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusComp
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

namespace SUTorus

section Transfer

variable {U H : Type*} [Group U] [Group H] {G : Type*} [Group G]

theorem range_comp_symm (ψ : U →* G) (Φ : U ≃* H) :
    (ψ.comp Φ.symm.toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.symm.surjective,
    ← MonoidHom.range_eq_map]

theorem ker_comp_symm_le {ψ : U →* G} (hker : ψ.ker ≤ Subgroup.center U) (Φ : U ≃* H) :
    (ψ.comp Φ.symm.toMonoidHom).ker ≤ Subgroup.center H := by
  intro u hu
  have hz : Φ.symm u ∈ Subgroup.center U := hker hu
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro v
  have h1 := hz (Φ.symm v)
  rw [← map_mul, ← map_mul] at h1
  exact Φ.symm.injective h1

variable {F : Type} [Field F] {σ : F ≃+* F} {f n : ℕ}

theorem mem_suPairs_transfer {ψ : SU σ n →* G} (P : GL (Fin n) F)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (hSU : SUid σ n = unitarySU 2 f F n) {e : G} {A : GL (Fin n) F} (hA : IsJUnitary σ A)
    (hAc : ∀ u, e * ψ u * e⁻¹ = ψ (conjSU A hA u)) :
    (e, P * A * P⁻¹) ∈
      suPairs (ψ.comp ((conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU)).symm.toMonoidHom) := by
  refine ⟨?_, fun u v hv => ?_⟩
  · have h1 := mem_normalizer_SUid (isIdUnitary_conj hP hA)
    rwa [hSU] at h1
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hAc]
    congr 1
    apply Subtype.ext
    change A * (P⁻¹ * (u : GL (Fin n) F) * P) * A⁻¹ = P⁻¹ * (v : GL (Fin n) F) * P
    rw [hv]
    group

end Transfer

section Unitary

theorem mem_primeFormUnitary_of_isIdUnitary {F : Type} [Field F] [Finite F] {f n : ℕ}
    (h : UnitaryFieldData 2 f F) [Fact (Nat.Prime 2)] [CharP F 2] {B : GL (Fin n) F}
    (hB : IsIdUnitary (unitaryInvolution F 2 f) B) : B ∈ primeFormUnitary h (idGram F n) := by
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
  have hσ : (⇑(unitaryInvolution F 2 f) : F → F) = ⇑h.bar :=
    funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
  have h1 := hB
  unfold IsIdUnitary conjTr at h1
  rwa [hσ] at h1

theorem ggLinearTorusComponent_su {G : Type} [Group G] [Finite G] {p m f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hnp : m + 1 = p) (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ (p - 1))
    (hEdiag : ∀ e ∈ E,
      GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ e)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) {E₀ : Subgroup G} (hE₀ : E₀ ≤ E)
    {J : Subgroup G} (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E₀ : Set G)))
    (hidx : p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E) {e : G} (he : e ∈ E₀) :
    ∃ K : Subgroup G, IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {e}) ∧ J ≤ K ∧
      GGTypeAk f K := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ m + 1 := by omega
  have hq : 2 ^ f ≠ 2 := by
    intro h2
    rw [h2] at hpf
    have := Nat.le_of_dvd (by norm_num) hpf
    omega
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => hq (congrArg Prod.snd h')
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) =
      unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f (GaloisField 2 (2 * f)) (m + 1)) :=
    ker_comp_symm_le hker Φ
  have hEB : ∀ e ∈ E, ∃ B, B ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * f)) (m + 1)) ∧
      (e, B) ∈ suPairs ψ₁ := by
    intro e he
    obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF (by omega) G ψ hker e⁻¹ (hEdiag e⁻¹ (E.inv_mem he))
    refine ⟨P * A * P⁻¹, mem_primeFormUnitary_of_isIdUnitary h (isIdUnitary_conj hP hA),
      mem_suPairs_transfer P hP hSU hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ suPairs ψ₁ := fun e he => by
    obtain ⟨B, -, hB⟩ := hEB e he
    exact ⟨B, hB⟩
  have hEC₁ : E ⊓ Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by rw [hr₁]; exact hEC
  have hbig : p ^ ((m + 1) / p + 1) < Nat.card E := by
    rw [hcard, hnp, Nat.div_self hp.pos]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hT := isToral_inducedMatrices h hn3 hnq hp hp2 hpf hker₁ hE hbig hEA hEC₁
  obtain ⟨Q, hQ, hQd⟩ := exists_unitary_frame h hp hp2 hpf
    (isProjElem_inducedMatrices h hn3 hnq hp hpf hker₁ hE) hT
  set ψ₂ := ψ₁.comp (TableBUE.conjSU h Q hQ).symm.toMonoidHom with hψ₂
  have hr₂ : ψ₂.range = ψ.range := by rw [hψ₂, range_comp_conjSU_symm, hr₁]
  have hker₂ := ker_comp_conjSU_symm_le h hker₁ Q hQ
  have hδ' : ∀ e ∈ E, ∃ d : Fin (m + 1) → (GaloisField 2 (2 * f))ˣ,
      (e, diagHom (m + 1) d) ∈ suPairs ψ₂ := by
    intro e he
    obtain ⟨B, hBU, hB⟩ := hEB e he
    obtain ⟨d, hd⟩ := hQd B (mem_inducedMatrices.mpr ⟨e, he, hB⟩) hBU
    refine ⟨d, ?_⟩
    rw [← hd]
    exact mem_suPairs_frame h hQ hB
  choose! δ hδ using hδ'
  rw [← hr₂] at hJ ⊢
  exact exists_component_of_diag h hn3 hq hp hpf hker₂ hE.2 hδ hE₀ hJ hidx he

end Unitary

end SUTorus

section Input

theorem ggLinearTorusComponentTag_PSU : GGLinearTorusComponentTag .PSU := by
  intro G _ _ p n f
  by_cases hf : 1 ≤ f
  · have hU : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hU]
    intro ψ G₀ hpres hp hlin E hE hcard _ hEdiag hEC E₀ hE₀ J hJ hidx e he _
    obtain ⟨hp5, hnp, hcase⟩ := hlin
    have hpf : p ∣ 2 ^ f + 1 := by
      rcases hcase with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by decide)
      · exact h
    obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← hrange] at hJ hEC ⊢
    exact SUTorus.ggLinearTorusComponent_su hp hp5 hnp hf hpf hker hE hcard hEdiag hEC hE₀ hJ
      hidx he
  · intro ψ G₀ hpres
    exact absurd hpres.1.1.2.1 hf

theorem ggLinearTorusComponentInput_holds : GGLinearTorusComponentInput :=
  ggLinearTorusComponentInput_of_PSU ggLinearTorusComponentTag_PSU

theorem ggSixLinearJInput_holds : GGSixLinearJInput :=
  ggSixLinearJInput_of_PSU ggLinearTorusComponentTag_PSU

end Input

end CFSG.StandardType
