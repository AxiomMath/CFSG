module

public import CFSG.Quasithin.Vol2.Ch11SecO1A
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartF
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4J
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.Open (pCoreOf)
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem exists_coord_sl3_syl [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I))) (f : ↥(fsuV T I) → (Fin 3 → K))
        (_ : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
        (g : SpecialLinearGroup (Fin 3) K),
        ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
          ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I))
    := by
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, hK, π, f, -, hf⟩ := SecO1.exists_coord_sl3 hS hk
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf (SecO1.isSylowTwoOf_P hS)
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf, g, hg⟩

section SL3

variable [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K]
  {π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 3 → K)}
  {g : SpecialLinearGroup (Fin 3) K}

theorem mem_V1_sl3 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    V₁.subgroupOf (fsuV T I) = hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
  have hU := SecO1.isFlagW_of_isVi hS hV₁
  rw [← hK] at hU
  exact eq_U1_of_isFlagW (SecO1.sq_eq_one hS) hf hg hU

theorem mem_V2_sl3 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₂ : Subgroup G} (hV₂ : IsVi T L I n 2 V₂) :
    V₂.subgroupOf (fsuV T I) = hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup := by
  have hU := SecO1.isFlagW_of_isVi hS hV₂
  rw [← hK] at hU
  exact eq_U2_of_isFlagW (SecO1.sq_eq_one hS) hf hg hU

theorem autOn_L1_sl3 [CharP K 2] (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    autOn (LOf L V₁) (fsuV T I) = (stabE0 K).map (psiW π g) := by
  have hSL := commutator_SL2_eq_top (four_le_card hS.one_lt hK)
  rw [SecS.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁), mem_V1_sl3 hS hK hf hg hV₁,
    gammaW_one_eq hSL hf g]

end SL3

theorem exists_coord_sp4_syl [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))) (f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π ∧
        ∃ (_ : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
          (g : StatedSp 2 K),
        ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
          ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, hK, π, f, hπ, hf⟩ := SecO1.exists_coord_sp4 hS hk
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf (SecO1.isSylowTwoOf_P hS)
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hπ, hf, g, hg⟩

section Sp4

variable [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K]
  {π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)}
  {g : StatedSp 2 K}

omit [Finite K] in
theorem exists_Vi_sp4 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {i : ℕ} {U : Subgroup G} (hU : IsVi T L I n i U) :
    ∃ S : Submodule K (Fin 2 ⊕ Fin 2 → K), UStableSp S ∧ Nat.card S = Nat.card K ^ i ∧
      U.subgroupOf (fsuV T I) = hf.pre (gmapSp g S).toAddSubgroup := by
  have hU' := SecO1.isFlagW_of_isVi hS hU
  rw [← hK] at hU'
  exact exists_eq_pre_of_isFlagW_sp (SecO1.sq_eq_one hS) hf hg hU'

theorem mem_V1_sp4 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup := by
  obtain ⟨S, hS', hc, hU⟩ := exists_Vi_sp4 hS hK hf hg hV₁
  rw [hU, (eq_std_of_stable_sp hS').1 (by rw [hc, pow_one])]

theorem mem_V2_sp4 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₂ : Subgroup G} (hV₂ : IsVi T L I n 2 V₂) :
    V₂.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spPlane K)).toAddSubgroup := by
  obtain ⟨S, hS', hc, hU⟩ := exists_Vi_sp4 hS hK hf hg hV₂
  rw [hU, (eq_std_of_stable_sp hS').2.1 hc]

theorem mem_V3_sp4 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₃ : Subgroup G} (hV₃ : IsVi T L I n 3 V₃) :
    V₃.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spHyp K)).toAddSubgroup := by
  obtain ⟨S, hS', hc, hU⟩ := exists_Vi_sp4 hS hK hf hg hV₃
  rw [hU, (eq_std_of_stable_sp hS').2.2 hc]

theorem autOn_L1_sp4 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    autOn (LOf L V₁) (fsuV T I) = (perfectCore (Q2 K 0)).map (psiSp π g) := by
  rw [SecS.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁), mem_V1_sp4 hS hK hf hg hV₁,
    gammaW_pre_eq hf g 0 _ flag_one_eq]

end Sp4

end CFSG.Quasithin.Vol2.Ch11.SecO1b
