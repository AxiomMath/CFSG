module

public import CFSG.Quasithin.MS93.S512NSp
public import CFSG.Quasithin.MS93.S5B58Sp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_le_pCoreOf_of_le_normalizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₀ P₀ : Subgroup G} (hE₀M : E₀ ≤ M) (hE₀2 : IsPGroup 2 E₀) (hE₀O : ¬ E₀ ≤ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2 ^ k)
    (hP₀M : P₀ ≤ M) (hP₀2 : IsPGroup 2 P₀) (hPE : P₀ ≤ Subgroup.normalizer (E₀ : Set G)) :
    ⁅E₀, P₀⁆ ≤ pCoreOf 2 M := by
  have := S5B.charP_two_of_card hd.2.1
  obtain ⟨p, hp, hfix⟩ := (S5B.relIndex_centralizer_M h hd hE₀M hE₀2 hE₀O).2 hrel
  have key : ∀ y ∈ P₀, ∀ hy : y ∈ M,
      ((E₀.subgroupOf M).map a).map (MulAut.conj (a ⟨y, hy⟩)).toMonoidHom ≤
        (E₀.subgroupOf M).map a := by
    rintro y hyP hyM _ ⟨_, ⟨e', he', rfl⟩, rfl⟩
    have hc : y * (e' : G) * y⁻¹ ∈ E₀ :=
      (Subgroup.mem_normalizer_iff.1 (hPE hyP) e').1 (Subgroup.mem_subgroupOf.1 he')
    refine ⟨⟨y, hyM⟩ * e' * ⟨y, hyM⟩⁻¹, Subgroup.mem_subgroupOf.2 hc, ?_⟩
    simp [map_mul, map_inv]
  rw [Subgroup.commutator_le]
  intro e he x hx
  have hxM := hP₀M hx
  have heM := hE₀M he
  have hxn : a ⟨x, hxM⟩ ∈ Subgroup.normalizer
      (((E₀.subgroupOf M).map a : Subgroup _) : Set (MSP.Sp4 F)) := by
    refine mem_normalizer_of_map_conj_le (key x hx hxM) ?_
    have := key x⁻¹ (inv_mem hx) (inv_mem hxM)
    rwa [show (⟨x⁻¹, inv_mem hxM⟩ : ↥M) = (⟨x, hxM⟩ : ↥M)⁻¹ from rfl, map_inv] at this
  obtain ⟨n, hn⟩ := hP₀2 ⟨x, hx⟩
  have hn' : (a ⟨x, hxM⟩) ^ 2 ^ n = 1 := by
    have h1 : (⟨x, hxM⟩ : ↥M) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hn
    rw [← map_pow, h1, map_one]
  have hcomm := commute_of_le_normalizer hp hfix hn' hxn
    (t := a ⟨e, heM⟩) ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  have hcE : ⁅e, x⁆ ∈ E₀ := by
    have h1 : x * e⁻¹ * x⁻¹ ∈ E₀ := (Subgroup.mem_normalizer_iff.1 (hPE hx) e⁻¹).1 (inv_mem he)
    have e1 : ⁅e, x⁆ = e * (x * e⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact mul_mem he h1
  have hcM : ⁅e, x⁆ ∈ M := hE₀M hcE
  have ha1 : a ⟨⁅e, x⁆, hcM⟩ = 1 := by
    have e2 : (⟨⁅e, x⁆, hcM⟩ : ↥M) = ⁅(⟨e, heM⟩ : ↥M), ⟨x, hxM⟩⁆ := rfl
    rw [e2, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  obtain ⟨m, hm⟩ := hE₀2 ⟨_, hcE⟩
  exact S5B.mem_pCoreOf_of_ker h hd ha1 ⟨m, by simpa using congrArg Subtype.val hm⟩

omit [Finite G] in
theorem ofA_mem_imM_iff (hTM : T ≤ M) {K : Subgroup G} (m : ↥M) :
    (puAmalgam hTM).ofA m ∈ imM hTM K ↔ (m : G) ∈ K := by
  constructor
  · rintro ⟨m', hm', he⟩
    rw [(puAmalgam hTM).ofA_injective he] at hm'
    exact Subgroup.mem_subgroupOf.1 hm'
  · intro hm
    exact ⟨m, Subgroup.mem_subgroupOf.2 hm, rfl⟩

omit [Finite G] in
theorem le_normalizer_of_imM (hTM : T ≤ M) {E₀ P₀ : Subgroup G} (hE₀M : E₀ ≤ M) (hP₀M : P₀ ≤ M)
    (hPE : imM hTM P₀ ≤ Subgroup.normalizer (imM hTM E₀ : Set (puAmalgam hTM).Universal)) :
    P₀ ≤ Subgroup.normalizer (E₀ : Set G) := by
  have key : ∀ x ∈ P₀, ∀ e ∈ E₀, x * e * x⁻¹ ∈ E₀ := by
    intro x hx e he
    have hxM := hP₀M hx
    have hxP : (puAmalgam hTM).ofA ⟨x, hxM⟩ ∈ imM hTM P₀ := (ofA_mem_imM_iff hTM _).2 hx
    have heE : (puAmalgam hTM).ofA ⟨e, hE₀M he⟩ ∈ imM hTM E₀ := (ofA_mem_imM_iff hTM _).2 he
    have h1 := (Subgroup.mem_normalizer_iff.1 (hPE hxP) _).1 heE
    rw [← map_inv, ← map_mul, ← map_mul, ofA_mem_imM_iff] at h1
    exact h1
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨key x hx e, fun he => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ he
  simpa [mul_assoc] using this

theorem commutator_le_qv_of_le_normalizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E P : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) (hE2 : IsPGroup 2 E) (hEQ : ¬ E ≤ Qv _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) ≤ 2 ^ k)
    (hP : P ≤ stab _ δ) (hP2 : IsPGroup 2 P)
    (hPE : P ≤ Subgroup.normalizer (E : Set (puAmalgam h.le).Universal)) :
    ⁅E, P⁆ ≤ Qv _ δ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨P₀, hP₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hP
  obtain ⟨hE₀2, hE₀O⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  have hP₀2 : IsPGroup 2 P₀ := by
    have e1 : ↥P₀ ≃* ↥(imM h.le P₀) := by
      refine (Subgroup.subgroupOfEquivOfLe hP₀M).symm.trans ?_
      exact Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective
    have e2 : ↥(imM h.le P₀) ≃* ↥((imM h.le P₀).map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
    exact hP2.of_equiv (e1.trans e2).symm
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  have hPE₀ : P₀ ≤ Subgroup.normalizer (E₀ : Set G) := by
    refine le_normalizer_of_imM h.le hE₀M hP₀M ?_
    rw [le_normalizer_map_conj_iff, map_conj_inv_map_conj] at hPE
    exact hPE
  have key := commutator_le_pCoreOf_of_le_normalizer h hd hE₀M hE₀2 hE₀O hrel hP₀M hP₀2 hPE₀
  rw [← Subgroup.map_commutator, ← imM_commutator h.le hE₀M hP₀M, qv_smul, S5B.qv_baseA_eq h,
    map_conj_le_map_conj_iff]
  exact imM_mono h.le key

end S512N

end CFSG.Quasithin.MS93
