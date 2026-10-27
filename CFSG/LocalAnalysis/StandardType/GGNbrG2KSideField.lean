module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffStd
public import CFSG.LocalAnalysis.StandardType.GGNbrG2KSideA2Cent
public import CFSG.LocalAnalysis.StandardType.GGNbrG2KSideA2Act

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (torusTorsion torusTorsion_le_torusGroup
  rootDiagUnit_mem_torusTorsion_iff)

namespace G2KAuxField

lemma torusTorsion_three_diag
    {K : Type} [Field K]
    {z : ModGL Tag.G2 K} (hz : z ∈ torusTorsion K 3) :
    ∃ c : Fin Tag.G2.rank → Kˣ, z = rootDiagUnit Tag.G2 c ∧ c ^ 3 = 1 := by
  have hH : z ∈ torusGroup Tag.G2 K := torusTorsion_le_torusGroup 3 hz
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
  refine ⟨c, hc, ?_⟩
  rw [hc] at hz
  exact (rootDiagUnit_mem_torusTorsion_iff 3 c).1 hz

lemma torusTorsion_commute
    {K : Type} [Field K]
    {a b : adjointGroup Tag.G2 K}
    (ha : (a : ModGL Tag.G2 K) ∈ torusTorsion K 3)
    (hb : (b : ModGL Tag.G2 K) ∈ torusTorsion K 3) : a * b = b * a := by
  obtain ⟨ca, hca, -⟩ := torusTorsion_three_diag ha
  obtain ⟨cb, hcb, -⟩ := torusTorsion_three_diag hb
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hca, hcb, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  exact mul_comm ca cb

end G2KAuxField

theorem ggNbrG2K_field_part
    {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (h6 : 6 ∣ n) (A : Subgroup (MulAut (adjointGroup Tag.G2 F))) (hA : IsElemAbelian 3 A)
    (h27 : 27 ≤ Nat.card A) {s : adjointGroup Tag.G2 F}
    (hsA : (MulAut.conj s : MulAut (adjointGroup Tag.G2 F)) ∈ A) (hs1 : s ≠ 1)
    (hcard : Nat.card ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) =
      ggG2SL3Card n)
    {α : MulAut (adjointGroup Tag.G2 F)} (hαA : α ∈ A)
    (hαInn : α ∉ (MulAut.conj : adjointGroup Tag.G2 F →*
      MulAut (adjointGroup Tag.G2 F)).range) :
    ∃ (e : ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) F) (σ : F ≃+* F)
      (d : Matrix.SpecialLinearGroup (Fin 3) F), σ ≠ 1 ∧
      ∀ g h : ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))),
        (h : adjointGroup Tag.G2 F) = α (g : adjointGroup Tag.G2 F) →
          e h = d * Matrix.SpecialLinearGroup.map σ.toRingHom (e g) * d⁻¹ := by
  classical
  let Γ := adjointGroup Tag.G2 F
  haveI : CharP F 2 := charP_two_of_card hF
  have hring : ringChar F = 2 := ringChar.eq F 2
  have hK3 : ringChar F ≠ 3 := by rw [hring]; norm_num
  have hK2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := h6
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        rw [hm, mul_zero, pow_zero] at hF
        omega
      · exact h
    rw [hm]
    omega
  have hK4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hconj_inj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) :=
    mulAut_conj_injective (center_adjointGroup_eq_bot (τ := Tag.G2) (K := F))
  obtain ⟨σ, x, _hσ, H⟩ := ggNbrG2Off_stdForm hF h6 A hA h27
  obtain ⟨z₁, j₁, hz₁T, _hz₁fix, h₁⟩ := H (MulAut.conj s) hsA
  have h₁' : MulAut.conj (x * s * x⁻¹) = MulAut.conj z₁ * (g2FieldHom F σ) ^ j₁ := by
    rw [← h₁]
    simp only [map_mul, map_inv]
  have hinner₁ : IsInnerAut ((g2FieldHom F σ) ^ j₁) := by
    have hEq : ((g2FieldHom F σ) ^ j₁) =
        (MulAut.conj z₁)⁻¹ * MulAut.conj (x * s * x⁻¹) := by
      rw [h₁']; group
    rw [hEq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (isInnerAut_conj z₁))
      (isInnerAut_conj (x * s * x⁻¹))
  have hσj₁ : σ ^ j₁ = 1 := by
    apply (g2_automorphism_normal_form (K := F) hK3 hK4).2 (σ ^ j₁)
    rw [map_pow]
    exact hinner₁
  have hφj₁ : (g2FieldHom F σ) ^ j₁ = 1 := by
    rw [← map_pow, hσj₁, map_one]
  have hs' : x * s * x⁻¹ = z₁ := by
    apply hconj_inj
    rw [h₁', hφj₁, mul_one]
  have hz₁1 : z₁ ≠ 1 := by
    intro hz
    apply hs1
    have : s = x⁻¹ * z₁ * x := by rw [← hs']; group
    rw [this, hz]; group
  have hcardz₁ : Nat.card ↥(Subgroup.centralizer ({z₁} : Set Γ)) = ggG2SL3Card n := by
    rw [← hs']
    rw [← Nat.card_congr
      (CFSG.RankThree.PartTwo.Sec4.E27.centralizerConjEquiv x s).toEquiv]
    exact hcard
  obtain ⟨ι, hιinj, hι_range, hι⟩ :=
    ggNbrG2K_a2_centralizer hF h6 hz₁T hz₁1 hcardz₁
  let C₁ : Subgroup Γ := Subgroup.centralizer ({s} : Set Γ)
  let C₂ : Subgroup Γ := Subgroup.centralizer ({x * s * x⁻¹} : Set Γ)
  have hmap : C₁.map (MulAut.conj x).toMonoidHom = C₂ :=
    CFSG.RankThree.PartTwo.Sec4.E27.map_centralizer_conj x s
  have hC₂ : C₂ = ι.range := by
    show Subgroup.centralizer ({x * s * x⁻¹} : Set Γ) = ι.range
    rw [hs']
    exact hι_range.symm
  have hfx : Function.Injective (MulAut.conj x : Γ →* Γ) := (MulAut.conj x).injective
  let cj : C₁ ≃* C₂ :=
    (C₁.equivMapOfInjective (MulAut.conj x : Γ →* Γ) hfx).trans
      (MulEquiv.subgroupCongr hmap)
  have cj_apply : ∀ g : C₁, ((cj g : C₂) : Γ) = x * (g : Γ) * x⁻¹ := by
    intro g
    change (MulAut.conj x) (g : Γ) = x * (g : Γ) * x⁻¹
    rw [MulAut.conj_apply]
  let E : Matrix.SpecialLinearGroup (Fin 3) F ≃* ι.range := MonoidHom.ofInjective hιinj
  let e : C₁ ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    cj.trans ((MulEquiv.subgroupCongr hC₂).trans E.symm)
  have he : ∀ g : C₁, ι (e g) = x * (g : Γ) * x⁻¹ := by
    intro g
    have h1 : ι (e g) = ((MulEquiv.subgroupCongr hC₂ (cj g) : ι.range) : Γ) := by
      exact MonoidHom.apply_ofInjective_symm hιinj _
    rw [h1, MulEquiv.subgroupCongr_apply, cj_apply g]
  obtain ⟨z₂, j₂, hz₂T, _hz₂fix, h₂⟩ := H α hαA
  let σ' : F ≃+* F := σ ^ j₂
  have hσ'1 : σ' ≠ 1 := by
    intro hσ'
    apply hαInn
    have hφj₂ : (g2FieldHom F σ) ^ j₂ = 1 := by
      rw [← map_pow, show σ ^ j₂ = 1 from hσ', map_one]
    have hinner : IsInnerAut (MulAut.conj x * α * (MulAut.conj x)⁻¹) := by
      rw [h₂, hφj₂, mul_one]
      exact isInnerAut_conj z₂
    exact (isInnerAut_conj_iff (MulAut.conj x) α).1 hinner
  have hz₂C : z₂ ∈ Subgroup.centralizer ({z₁} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact G2KAuxField.torusTorsion_commute hz₂T hz₁T
  have hz₂range : z₂ ∈ ι.range := by
    rw [hι_range]
    exact hz₂C
  obtain ⟨d, hd⟩ := hz₂range
  refine ⟨e, σ', d, hσ'1, ?_⟩
  intro g h hh
  have hLHS : (MulAut.conj x * α * (MulAut.conj x)⁻¹) (x * (g : Γ) * x⁻¹) =
      x * (h : Γ) * x⁻¹ := by
    have hinv : ((MulAut.conj x)⁻¹ : MulAut Γ) = MulAut.conj x⁻¹ := (map_inv _ x).symm
    rw [MulAut.mul_apply, MulAut.mul_apply, hinv, MulAut.conj_apply, MulAut.conj_apply]
    rw [show x⁻¹ * (x * (g : Γ) * x⁻¹) * (x⁻¹)⁻¹ = (g : Γ) by group]
    rw [← hh]
  have hRHS : (MulAut.conj z₂ * (g2FieldHom F σ) ^ j₂) (x * (g : Γ) * x⁻¹) =
      ι (d * Matrix.SpecialLinearGroup.map σ'.toRingHom (e g) * d⁻¹) := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
    have hpow : ((g2FieldHom F σ) ^ j₂ : MulAut Γ) = g2FieldHom F σ' := by
      show (g2FieldHom F σ) ^ j₂ = g2FieldHom F (σ ^ j₂)
      rw [← map_pow]
    rw [hpow, ← he g, ggNbrG2K_a2_fieldHom ι hι σ' (e g), ← hd]
    rw [← map_mul, ← map_inv, ← map_mul]
  have hval := DFunLike.congr_fun h₂ (x * (g : Γ) * x⁻¹)
  rw [hLHS, hRHS] at hval
  apply hιinj
  rw [he h]
  exact hval

end CFSG.StandardType

end
