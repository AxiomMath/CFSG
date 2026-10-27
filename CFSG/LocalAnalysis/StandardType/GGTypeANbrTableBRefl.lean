module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

namespace TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [CharP K 2]

private theorem actsDiag_mul_conj_perm_inv {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} {i j : Fin d}
    {a : MulAut L'} {t : Fin d → K} (hat : ActsDiag φ' a t) :
    ActsDiag φ' (a * (NbrInnerWeylA.permConj φ' (Equiv.swap i j) * a *
      (NbrInnerWeylA.permConj φ' (Equiv.swap i j))⁻¹)⁻¹)
      (fun k => t k * (t (Equiv.swap i j k))⁻¹) := by
  have hconj : ActsDiag φ' (MulAut.conj (φ' (permSL (Equiv.swap i j))) * a *
      (MulAut.conj (φ' (permSL (Equiv.swap i j))))⁻¹) (t ∘ Equiv.swap i j) :=
    hat.conj_perm (Equiv.swap i j)
  have hperm : NbrInnerWeylA.permConj φ' (Equiv.swap i j) =
      MulAut.conj (φ' (permSL (Equiv.swap i j))) := by
    show MulAut.conj (φ' (permSL (Equiv.swap i j)⁻¹)) =
      MulAut.conj (φ' (permSL (Equiv.swap i j)))
    rw [Equiv.swap_inv]
  rw [hperm]
  exact hat.mul hconj.inv

theorem permAut_swap_mem_reflSet [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 3 ≤ d) {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t)
    (hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    {i j : Fin d} (hij : i ≠ j) :
    permAut φ' A hN (Equiv.swap i j) ∈ ggTorusReflSet p A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  haveI : Finite ↥A := Subtype.finite
  have hc : ∀ a b : ↥A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  refine ⟨φ' (permSL (Equiv.swap i j)⁻¹), hN (Equiv.swap i j), ?_, rfl, ?_⟩
  · exact weyl_mul_apply_inv_diag hφker hdiag hA.2 _
      ⟨(Equiv.swap i j)⁻¹, rfl⟩
  · obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := K) hp hpK
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
    set t₁ : Fin d → K := ggPairVec i j ζ with ht₁
    have ht₁0 : ∀ k, t₁ k ≠ 0 := by
      intro k
      rw [ht₁, ggPairVec_apply]
      split_ifs <;> simp [hζ0]
    have ht₁p : ∀ k, t₁ k ^ p = 1 := fun k => by
      rw [ht₁]
      exact pow_ggPairVec hζ.pow_eq_one k
    have hprod₁ : ∏ k, t₁ k = 1 := by
      rw [ht₁]
      exact prod_ggPairVec ζ hζ0
    let D₁ : SpecialLinearGroup (Fin d) K :=
      ⟨diagonal t₁, by rw [Matrix.det_diagonal]; exact hprod₁⟩
    have hD₁mat : (D₁ : Matrix (Fin d) (Fin d) K) = diagonal t₁ := rfl
    have hD₁p : D₁ ^ p = 1 := pow_eq_one_of_diagonal hD₁mat ht₁p
    have hD₁p' : (φ' D₁) ^ p = 1 := by
      rw [← map_pow, hD₁p, map_one]
    have hD₁mem : MulAut.conj (φ' D₁) ∈ A := by
      refine hsc (φ' D₁) ?_ hD₁p'
      intro a ha
      obtain ⟨t, hat⟩ := hdiag a ha
      exact hat.apply_of_isDiag (by rw [hD₁mat]; exact Matrix.isDiag_diagonal _)
    have ht₁i : t₁ i = ζ := by
      rw [ht₁, ggPairVec_apply, ite_eq_left rfl, ite_eq_right hij]
      simp
    have ht₁j : t₁ j = ζ⁻¹ := by
      rw [ht₁, ggPairVec_apply, ite_eq_right hij.symm, ite_eq_left rfl]
      simp
    let a₁ : ↥A := ⟨MulAut.conj (φ' D₁), hD₁mem⟩
    have ha₁coe : (a₁ : MulAut L') = MulAut.conj (φ' D₁) := rfl
    have ha₁acts : ActsDiag φ' (a₁ : MulAut L') t₁ := actsDiag_conj hD₁mat
    have ha₁p : a₁ ^ p = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one, ha₁coe,
        ← map_pow (f := (MulAut.conj : L' →* MulAut L')), hD₁p', map_one]
    have hδ : ∀ a : ↥A, ∃ e : ℕ,
        a * ((permAut φ' A hN (Equiv.swap i j)) a)⁻¹ = a₁ ^ e := by
      intro a
      obtain ⟨t, hat⟩ := hdiag (a : MulAut L') a.2
      have hfa : (((permAut φ' A hN (Equiv.swap i j)) a : ↥A) : MulAut L') =
          NbrInnerWeylA.permConj φ' (Equiv.swap i j) * (a : MulAut L') *
            (NbrInnerWeylA.permConj φ' (Equiv.swap i j))⁻¹ :=
        ggConjAut_apply A (hN (Equiv.swap i j)) a
      have hprodacts : ActsDiag φ'
          ((a * ((permAut φ' A hN (Equiv.swap i j)) a)⁻¹ : ↥A) : MulAut L')
          (fun k => t k * (t (Equiv.swap i j k))⁻¹) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hfa]
        exact actsDiag_mul_conj_perm_inv hat
      have hfn : (fun k => t k * (t (Equiv.swap i j k))⁻¹) =
          ggPairVec i j (t i * (t j)⁻¹) :=
        mul_inv_comp_swap (fun k => hat.ne_zero k) hij
      have hμp : (t i * (t j)⁻¹) ^ p = 1 :=
        hat.ratio_pow hφker (hA.2 (a : MulAut L') a.2) i j
      obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hμp
      have hpowfn : (fun k => t₁ k ^ e) = ggPairVec i j (ζ ^ e) := by
        rw [ht₁]
        exact ggPairVec_pow i j ζ e
      have ha₁powacts : ActsDiag φ' ((a₁ ^ e : ↥A) : MulAut L')
          (ggPairVec i j (ζ ^ e)) := by
        rw [Subgroup.coe_pow]
        have h := ha₁acts.pow e
        rw [hpowfn] at h
        exact h
      have hprod' : ActsDiag φ'
          ((a * ((permAut φ' A hN (Equiv.swap i j)) a)⁻¹ : ↥A) : MulAut L')
          (ggPairVec i j (ζ ^ e)) := by
        have h := hprodacts
        rw [hfn, ← he] at h
        exact h
      exact ⟨e, Subtype.ext (ActsDiag.unique hφ's hprod' ha₁powacts)⟩
    have h₁ : a₁ * ((permAut φ' A hN (Equiv.swap i j)) a₁)⁻¹ ≠ 1 := by
      intro hcontra
      have hfa₁ : (((permAut φ' A hN (Equiv.swap i j)) a₁ : ↥A) : MulAut L') =
          NbrInnerWeylA.permConj φ' (Equiv.swap i j) * (a₁ : MulAut L') *
            (NbrInnerWeylA.permConj φ' (Equiv.swap i j))⁻¹ :=
        ggConjAut_apply A (hN (Equiv.swap i j)) a₁
      have hprodacts₁ : ActsDiag φ'
          ((a₁ * ((permAut φ' A hN (Equiv.swap i j)) a₁)⁻¹ : ↥A) : MulAut L')
          (fun k => t₁ k * (t₁ (Equiv.swap i j k))⁻¹) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hfa₁]
        exact actsDiag_mul_conj_perm_inv ha₁acts
      have hfn₁ : (fun k => t₁ k * (t₁ (Equiv.swap i j k))⁻¹) =
          ggPairVec i j (t₁ i * (t₁ j)⁻¹) :=
        mul_inv_comp_swap (fun k => ha₁acts.ne_zero k) hij
      have hζζ : t₁ i * (t₁ j)⁻¹ = ζ * ζ := by
        rw [ht₁i, ht₁j, inv_inv]
      have hprod₁' : ActsDiag φ'
          ((a₁ * ((permAut φ' A hN (Equiv.swap i j)) a₁)⁻¹ : ↥A) : MulAut L')
          (ggPairVec i j (ζ * ζ)) := by
        have h := hprodacts₁
        rw [hfn₁, hζζ] at h
        exact h
      have hcontra' : ((a₁ * ((permAut φ' A hN (Equiv.swap i j)) a₁)⁻¹ : ↥A) :
          MulAut L') = 1 := by
        simpa using congrArg Subtype.val hcontra
      have hdiag1 : ActsDiag φ' (1 : MulAut L') (ggPairVec i j (ζ * ζ)) :=
        hcontra' ▸ hprod₁'
      obtain ⟨m, hmi, hmj⟩ := exists_ne_of_two hd i j
      have hratio := hdiag1.ratio hφker actsDiag_one (k := i) (l := m) hmi.symm
      have hvi : ggPairVec i j (ζ * ζ) i = ζ * ζ := by
        rw [ggPairVec_apply, ite_eq_left rfl, ite_eq_right hij, mul_one]
      have hvm : ggPairVec i j (ζ * ζ) m = 1 := by
        rw [ggPairVec_apply, ite_eq_right hmi, ite_eq_right hmj, mul_one]
      rw [hvi, hvm] at hratio
      simp only [Pi.one_apply, inv_one, mul_one] at hratio
      exact hζinv (inv_eq_of_mul_eq_one_right hratio).symm
    constructor
    · rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]
    · exact card_fix_mul_of_le_zpowers hp hc (permAut φ' A hN (Equiv.swap i j))
        (a₁ := a₁) ha₁p hδ h₁

theorem ggAutomizer_le_closure_reflSet_of_model [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 3 ≤ d) {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      Subgroup.closure (ggTorusReflSet p A) := by
  have hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => permConj_mem_normalizer_of_selfCent hφ's hφker hA.2 hsc hdiag σ
  rw [ggAutomizer_eq_range_permAut hp hp2 hpK hφ's hφker hA hsc hdiag hN,
    MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨σ, ⟨i, j, hij, rfl⟩, rfl⟩
  exact permAut_swap_mem_reflSet hp hp2 hpK hd hφ's hφker hA hsc hdiag hN hij

end TypeANbrDvd

section ActualAction

open TypeANbrDvd

variable {G : Type} [Group G] [Finite G]

theorem ggAutomizerGammaHom_bijective_of_model
    {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ p)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {φ : Matrix.SpecialLinearGroup (Fin d) K →* J}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hdiag : ∀ a ∈ (ggGamma J hN).range, ∃ t : Fin d → K, ActsDiag φ a t)
    (hpK : p ∣ Nat.card K - 1) (hd : 3 ≤ d) :
    Function.Bijective (ggAutomizerGammaHom hN) := by
  classical
  have hA : IsElemAbelian p (ggGamma J hN).range := by
    have hBp : ∀ b : ↥Bs, b ^ p = 1 := fun b =>
      Subtype.ext (by simpa using hBs.2 b b.2)
    have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
      Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
    exact isElemAbelian_range hBc hBp (ggGamma J hN)
  have hscA : GGTorusSelfCent p (ggGamma J hN).range :=
    ggTorusSelfCent_ggGamma hN hSC
  have hW : ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range (ggGamma J hN).range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma J hN).range) :=
    TypeANbrDvd.ggAutomizer_le_closure_reflSet_of_model
      hp hp2 hpK hd hφs hφker hA hscA hdiag
  have hsurj : Function.Surjective (ggAutomizerGammaHom hN) := by
    intro a
    obtain ⟨c, hccl, hcov⟩ :=
      exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN hW a a.2
    have hc : c ∈ ggAutomizer J Bs :=
      (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1) hccl
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    exact GGOverGamma.unique (ggAutomizerGammaHom_overGamma hN ⟨c, hc⟩) hcov
  exact ⟨ggAutomizerGammaHom_injective hp hBs hNoTr hN hZ, hsurj⟩

theorem actual_card_ggAutomizer_eq_factorial_of_model
    {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ p)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {φ : Matrix.SpecialLinearGroup (Fin d) K →* J}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hdiag : ∀ a ∈ (ggGamma J hN).range, ∃ t : Fin d → K, ActsDiag φ a t)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) :
    Nat.card (ggAutomizer J Bs) = d.factorial := by
  have hA : IsElemAbelian p (ggGamma J hN).range := by
    have hBp : ∀ b : ↥Bs, b ^ p = 1 := fun b =>
      Subtype.ext (by simpa using hBs.2 b b.2)
    have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
      Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
    exact isElemAbelian_range hBc hBp (ggGamma J hN)
  have hscA : GGTorusSelfCent p (ggGamma J hN).range :=
    ggTorusSelfCent_ggGamma hN hSC
  calc
    Nat.card (ggAutomizer J Bs) =
        Nat.card (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range
          (ggGamma J hN).range) :=
      Nat.card_congr
        (MulEquiv.ofBijective (ggAutomizerGammaHom hN)
          (ggAutomizerGammaHom_bijective_of_model hp hp2 hBs hSC hNoTr hN hZ
            hφs hφker hdiag hpK (le_trans (by norm_num : 3 ≤ 4) hd))).toEquiv
    _ = d.factorial :=
      TypeANbrDvd.card_ggAutomizer_eq_factorial_of_model hp hp2 hpK hd
        hφs hφker hA hscA hdiag

theorem actual_card_ggAutomizer_eq_six_of_nine_le_card
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {Bs J : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3)
    {φ : Matrix.SpecialLinearGroup (Fin 3) K →* J}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars 3 K)
    (hdiag : ∀ a ∈ (ggGamma J hN).range, ∃ t : Fin 3 → K, ActsDiag φ a t)
    (h3K : 3 ∣ Nat.card K - 1)
    (h9 : 9 ≤ Nat.card ((ggGamma J hN).range)) :
    Nat.card (ggAutomizer J Bs) = 6 := by
  have hA : IsElemAbelian 3 (ggGamma J hN).range := by
    have hBp : ∀ b : ↥Bs, b ^ 3 = 1 := fun b =>
      Subtype.ext (by simpa using hBs.2 b b.2)
    have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
      Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
    exact isElemAbelian_range hBc hBp (ggGamma J hN)
  have hscA : GGTorusSelfCent 3 (ggGamma J hN).range :=
    ggTorusSelfCent_ggGamma hN hSC
  calc
    Nat.card (ggAutomizer J Bs) =
        Nat.card (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range
          (ggGamma J hN).range) :=
      Nat.card_congr
        (MulEquiv.ofBijective (ggAutomizerGammaHom hN)
          (ggAutomizerGammaHom_bijective_of_model (p := 3) (d := 3)
            (by norm_num) (by norm_num) hBs hSC hNoTr hN hZ
            hφs hφker hdiag h3K (by norm_num))).toEquiv
    _ = 6 :=
      TypeANbrDvd.ggAutomizer_card_six_of_nine_le_card hφs hφker hA hscA hdiag h3K h9

end ActualAction

end CFSG.StandardType
