module

public import CFSG.RankThree.PartOne.FOCD.CompQuasi
public import CFSG.RankThree.PartOne.FOCD.G2OddCommon
public import CFSG.RankThree.Classical.SL2SemilinearRoots
import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne


section Data

variable {K : Type} [Field K] [Finite K] {K₂ : Type} [Field K₂] [Finite K₂]
  [Algebra K K₂] {p : ℕ}

omit [Finite K] [Finite K₂] in
theorem exists_equiv_sl2_of_comap (α : Fin Tag.G2.rank → ℤ) (P : GL (Fin 2) K₂)
    (Q' : Subgroup (ModGL .G2 K₂)) (hQle : Q' ≤ rootRankOneGroup .G2 K₂ α)
    (hcomap : Q'.comap (rootSL2 .G2 K₂ α) =
      (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map
        (CFSG.RankThree.Classical.conjSL P)) :
    Nonempty (SL2 K ≃* ↥Q') := by
  have hSLinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap K K₂)) := by
    intro A B hAB
    ext i j
    have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) K₂ =>
      (X : Matrix (Fin 2) (Fin 2) K₂) i j) hAB
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K K₂).injective h1
  have hPinj : Function.Injective (CFSG.RankThree.Classical.conjSL P) := fun A B hAB => by
    have h1 := congrArg (CFSG.RankThree.Classical.conjSL P⁻¹) hAB
    rwa [← CFSG.RankThree.Classical.conjSL_mul, ← CFSG.RankThree.Classical.conjSL_mul,
      inv_mul_cancel, CFSG.RankThree.Classical.conjSL_one,
      CFSG.RankThree.Classical.conjSL_one] at h1
  have hinj : Function.Injective (rootSL2 .G2 K₂ α) := rootSL2_injective_of_field α
  have hmap : (Q'.comap (rootSL2 .G2 K₂ α)).map (rootSL2 .G2 K₂ α) = Q' := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right hQle
  exact ⟨((((MonoidHom.ofInjective hSLinj).trans
    (Subgroup.equivMapOfInjective _ (CFSG.RankThree.Classical.conjSL P) hPinj)).trans
    (MulEquiv.subgroupCongr hcomap.symm)).trans
    (Subgroup.equivMapOfInjective _ (rootSL2 .G2 K₂ α) hinj)).trans (MulEquiv.subgroupCongr hmap)⟩

theorem compGoodZAt_of_qplus_data (hp : p.Prime) (hpodd : Odd p) (hpq : p ∣ Nat.card K + 1)
    (Γ : Subgroup (ModGL .G2 K₂)) (S : Sylow p ↥Γ)
    (hS : (S : Subgroup ↥Γ) ≤ (torusGroup .G2 K₂ ⊓ Γ).subgroupOf Γ)
    (hrank1 : ∀ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α → ∃ P : GL (Fin 2) K₂,
      (rootRankOneGroup .G2 K₂ α ⊓ Γ).comap (rootSL2 .G2 K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map
          (CFSG.RankThree.Classical.conjSL P) ∧
      CFSG.IsQuasisimple ↥(rootRankOneGroup .G2 K₂ α ⊓ Γ))
    (hunique : ∀ x ∈ torusGroup .G2 K₂ ⊓ Γ, ∃! a : Fin Tag.G2.rank → K₂ˣ,
      rootDiagUnit .G2 a = x)
    (hab : ∀ x ∈ torusGroup .G2 K₂, ∀ y ∈ torusGroup .G2 K₂, x * y = y * x)
    (hcent : ∀ a : Fin Tag.G2.rank → K₂ˣ, rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ Γ →
      orderOf (rootDiagUnit .G2 a) = p →
      (rootCharKernel a = ∅ →
        Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) =
          torusGroup .G2 K₂ ⊓ Γ) ∧
      (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
        ⁅Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)),
          Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂))⁆ =
          rootRankOneGroup .G2 K₂ α ⊓ Γ))
    (c : ↥Γ) (hcord : orderOf c = p) : CompGoodZAt p c := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL .G2 K₂) := finite_modGL
  have hcP : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcord, pow_one])
  obtain ⟨S', hS'⟩ := hcP.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥Γ S S'
  have hcmem : c ∈ (S' : Subgroup ↥Γ) := hS' (Subgroup.mem_zpowers c)
  rw [← hh, Sylow.coe_subgroup_smul] at hcmem
  have hcS : (MulAut.conj h)⁻¹ • c ∈ (S : Subgroup ↥Γ) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hcmem
  have hscdef : (MulAut.conj h)⁻¹ • c = h⁻¹ * c * h := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rw [hscdef] at hcS
  have hsT := hS hcS
  refine compGoodZAt_conj h⁻¹ ?_
  have hconj : h⁻¹ * c * h⁻¹⁻¹ = h⁻¹ * c * h := by simp
  rw [hconj]
  have hsord : orderOf (h⁻¹ * c * h) = p := by
    rw [← hconj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hcord
  have hsmem : (((h⁻¹ * c * h : ↥Γ)) : ModGL .G2 K₂) ∈ torusGroup .G2 K₂ ⊓ Γ :=
    ⟨(Subgroup.mem_subgroupOf.1 hsT).1, (h⁻¹ * c * h : ↥Γ).2⟩
  obtain ⟨a, ha, -⟩ := hunique _ hsmem
  have hdord : orderOf (rootDiagUnit .G2 a) = p := by
    rw [ha, Subgroup.orderOf_coe]
    exact hsord
  have hdmem : rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ Γ := ha ▸ hsmem
  have hdΓ : rootDiagUnit .G2 a ∈ Γ := hdmem.2
  have hseq : h⁻¹ * c * h = (⟨rootDiagUnit .G2 a, hdΓ⟩ : ↥Γ) := Subtype.ext ha.symm
  rw [hseq]
  by_cases hker : rootCharKernel a = ∅
  ·
    have hD := (hcent a hdmem hdord).1 hker
    refine compGoodZAt_of_comm fun x hx y hy => ?_
    have hx' : (x : ModGL .G2 K₂) ∈ Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    have hy' : (y : ModGL .G2 K₂) ∈ Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) :=
      ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy))⟩
    rw [hD] at hx' hy'
    exact Subtype.ext (hab _ hx'.1 _ hy'.1)
  · obtain ⟨α, hα, hcomm⟩ := (hcent a hdmem hdord).2 hker
    obtain ⟨P, hcomap, hqs⟩ := hrank1 α hα
    set D : Subgroup (ModGL .G2 K₂) :=
      Γ ⊓ Subgroup.centralizer ({rootDiagUnit .G2 a} : Set (ModGL .G2 K₂)) with hD
    set Q' : Subgroup (ModGL .G2 K₂) := rootRankOneGroup .G2 K₂ α ⊓ Γ with hQ'
    have hQD : Q' ≤ D := by
      rw [← hcomm]
      exact Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)
    have hDQ : ⁅D, D⁆ ≤ Q' := le_of_eq hcomm
    obtain ⟨e⟩ := exists_equiv_sl2_of_comap (K := K) α P Q' inf_le_left hcomap
    have hpQ : p ∣ Nat.card Q' := by
      rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
      refine Dvd.dvd.mul_left (hpq.trans ?_) _
      have hq1 : 1 ≤ Nat.card K := Nat.card_pos
      rw [show Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) by
        obtain ⟨w, hw⟩ : ∃ w, Nat.card K = w + 1 := ⟨Nat.card K - 1, by omega⟩
        rw [hw]; simp only [Nat.add_sub_cancel]; ring_nf; omega]
      exact Dvd.intro_left _ rfl
    exact compGoodZAt_of_quasisimple_layer hdΓ hqs hQD hDQ hpQ (hZ_of_equiv_sl2 hpodd e)

theorem pRankLeTwo_of_qplus_data (hp : p.Prime) (Γ : Subgroup (ModGL .G2 K₂)) (S : Sylow p ↥Γ)
    (hS : (S : Subgroup ↥Γ) ≤ (torusGroup .G2 K₂ ⊓ Γ).subgroupOf Γ) {G₁ G₂ : Type}
    [Group G₁] [Group G₂] [IsCyclic G₁] [IsCyclic G₂] [Finite G₁] [Finite G₂]
    (e : ↥(torusGroup .G2 K₂ ⊓ Γ) ≃* G₁ × G₂) : PRankLeTwo p ↥Γ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL .G2 K₂) := finite_modGL
  refine pRankLeTwo_of_conj_cyclic2 hp (H := (torusGroup .G2 K₂ ⊓ Γ).subgroupOf Γ) (G₁ := G₁)
    (G₂ := G₂) ((Subgroup.subgroupOfEquivOfLe inf_le_right).trans e) ?_
  intro P hP
  obtain ⟨g, hg⟩ := exists_conj_map_le_of_not_dvd_index (Sylow.not_dvd_index S) hP
  exact ⟨g, hg.trans hS⟩

end Data

theorem qext_data {K : Type} [Field K] [Finite K] :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : Algebra K K₂) (σ : K₂ ≃+* K₂),
      Module.finrank K K₂ = 2 ∧ ∀ c, σ c = c ^ Nat.card K := by
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.ringChar_ne_zero_of_finite K)⟩
  exact ⟨FiniteField.Extension K (ringChar K) 2, inferInstance, inferInstance, inferInstance,
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv,
    FiniteField.finrank_extension K (ringChar K) 2, fun c => by simp⟩

variable {K : Type} [Field K] [Finite K] {p : ℕ}

theorem pRankLeTwo_G2_oddqplus (hK : Odd (Nat.card K)) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1) : PRankLeTwo p (adjointGroup .G2 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := qext_data (K := K)
  obtain ⟨g, z, hg, hzC, hzdef, hz, hΓ, hF2, ⟨φ⟩, ⟨S, hS⟩, hE, hrank1, hunique, hcent⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers K hK hp hp3 hpq K₂ hdeg σ hσ
  let ψ : ModGL .G2 K →* ModGL .G2 (K₂) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K (K₂)))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp
      (baseChangeGL_injective (τ := .G2) (algebraMap K (K₂)))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    Subgroup.equivMapOfInjective (adjointGroup .G2 K) ψ hψ
  refine pRankLeTwo_of_mulEquiv ε ?_
  exact pRankLeTwo_of_qplus_data hp (conjEntrywiseImage K g) S hS φ

theorem compGoodZAt_G2_oddqplus (hK : Odd (Nat.card K)) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1) (b : adjointGroup .G2 K) (hb1 : b ≠ 1) (hbp : b ^ p = 1) :
    CompGoodZAt p b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := qext_data (K := K)
  obtain ⟨g, z, hg, hzC, hzdef, hz, hΓ, hF2, ⟨φ⟩, ⟨S, hS⟩, hE, hrank1, hunique, hcent⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers K hK hp hp3 hpq K₂ hdeg σ hσ
  let ψ : ModGL .G2 K →* ModGL .G2 (K₂) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K (K₂)))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp
      (baseChangeGL_injective (τ := .G2) (algebraMap K (K₂)))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    Subgroup.equivMapOfInjective (adjointGroup .G2 K) ψ hψ
  refine compGoodZAt_of_mulEquiv ε ?_
  have hcord : orderOf (ε b) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hbp hb1
  obtain ⟨e₂, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) (K₂)
  have hHcomm : ∀ x ∈ torusGroup .G2 (K₂),
      ∀ y ∈ torusGroup .G2 (K₂), x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu⟩ : ∃ u, e₂ u = ⟨x, hx⟩ := ⟨e₂.symm ⟨x, hx⟩, by simp⟩
    obtain ⟨v, hv⟩ : ∃ v, e₂ v = ⟨y, hy⟩ := ⟨e₂.symm ⟨y, hy⟩, by simp⟩
    have := congrArg Subtype.val
      (show e₂ u * e₂ v = e₂ v * e₂ u by rw [← map_mul, ← map_mul, mul_comm])
    rw [hu, hv] at this
    exact this
  refine compGoodZAt_of_qplus_data hp hpodd hpq (conjEntrywiseImage K g) S hS ?_ hunique hHcomm ?_
    (ε b) hcord
  · intro α hα
    obtain ⟨P, h1, h2⟩ := hrank1 α hα
    exact ⟨P, h1, h2⟩
  · intro a h1 h2
    obtain ⟨hA, hB⟩ := hcent a h1 h2
    refine ⟨fun hker => (hA hker).1, fun hne => ?_⟩
    obtain ⟨α, hα, -, hc, -⟩ := hB hne
    exact ⟨α, hα, hc⟩

end CFSG.RankThree.PartOne.FOCD
