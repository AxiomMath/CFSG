module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvAut
public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTvFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTvARatio
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThree
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Cover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCover
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcFlatDefs
public import CFSG.LocalAnalysis.StandardType.GGYardstoneLegacyImports

public section

namespace CFSG.StandardType.LinTwoTv

open Matrix CFSG CFSG.Assembly TableB TypeA TwoThree CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {d : ℕ} {L' : Type} [Group L'] {ψ : L' →* projectiveSL d K}

@[expose] def Ind (ψ : L' →* projectiveSL d K) (a : MulAut L') (B : GL (Fin d) K) : Prop :=
  ∀ l, conjAut d K B (ψ l) = ψ (a l)

theorem Ind.mul {a a' : MulAut L'} {B B' : GL (Fin d) K} (h : Ind ψ a B) (h' : Ind ψ a' B') :
    Ind ψ (a * a') (B * B') := by
  intro l
  rw [map_mul, MulAut.mul_apply, MulAut.mul_apply, h', h]

theorem Ind.inv {a : MulAut L'} {B : GL (Fin d) K} (h : Ind ψ a B) : Ind ψ a⁻¹ B⁻¹ := by
  intro l
  apply (conjAut d K B).injective
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply, h,
    MulAut.apply_inv_self]

theorem Ind.unique (hψ : Function.Surjective ψ) (hinj : Function.Injective (conjAut d K))
    {a : MulAut L'} {B₁ B₂ : GL (Fin d) K} (h₁ : Ind ψ a B₁) (h₂ : Ind ψ a B₂) : B₁ = B₂ :=
  hinj (induced_unique ψ hψ h₁ h₂)

theorem Ind.conj {α a : MulAut L'} {B : GL (Fin d) K} {φ : MulAut (projectiveSL d K)}
    (hφ : ∀ l, φ (ψ l) = ψ (α l)) (h : Ind ψ a B) {Θ : GL (Fin d) K →* GL (Fin d) K}
    (hΘ : ∀ B, φ * conjAut d K B * φ⁻¹ = conjAut d K (Θ B)) : Ind ψ (α * a * α⁻¹) (Θ B) := by
  intro l
  have h1 : φ⁻¹ (ψ l) = ψ (α⁻¹ l) := by
    apply φ.injective
    rw [MulAut.apply_inv_self, hφ, MulAut.apply_inv_self]
  rw [← hΘ B]
  change φ (conjAut d K B (φ⁻¹ (ψ l))) = ψ (α (a (α⁻¹ l)))
  rw [h1, h, hφ]

variable [Finite K]

theorem noTransvectionSCr_two (hK : Nat.card K = 2) (hd : 3 ≤ d) :
    GGNoTransvectionSCr 3 (d / 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 _ α hα hT
  obtain ⟨φ, hφ⟩ := hα
  set α' : MulAut L' := (α : MulAut L') with hα'
  have hA0 : 0 < Nat.card A := lt_of_lt_of_le (pow_pos (by norm_num) 3) h3
  obtain ⟨hT1, b₀, hb₀, hb₀ne⟩ := LinTvA.transvection_data Nat.prime_three hA0 hT
  have hαN : ∀ b ∈ A, α' * b * α'⁻¹ ∈ A := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp α.2 b).mp hb
  have hinj := conjAut_injective hK (d := d) (by omega)
  set X := inducedSub ψ A with hX
  have hXA : IsElemAbelian 3 X := isElemAbelian_inducedSub hψ hA
  have hAind : ∀ a ∈ A, ∃ φa : MulAut (projectiveSL d K), ∀ l, φa (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩
  have hcardX : Nat.card X = Nat.card A := card_inducedSub hψ hker hperf hAind
  have hXI : ∀ x ∈ X, ∃ B : GL (Fin d) K, conjAut d K B = x := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, induced_unique ψ hψ hφa hxa⟩
  set Xt := X.comap (conjAut d K) with hXt
  have hcardt : Nat.card Xt = Nat.card X := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun B : Xt => (⟨conjAut d K B, B.2⟩ : X)) ⟨?_, ?_⟩)
    · intro B C hBC
      exact Subtype.ext (hinj (congrArg Subtype.val hBC))
    · rintro ⟨x, hx⟩
      obtain ⟨B, rfl⟩ := hXI x hx
      exact ⟨⟨B, hx⟩, rfl⟩
  have hEt : IsElemAbelian 3 Xt := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hXA a.2 b.2
    · rw [map_pow, map_one]
      exact hXA.2 _ hx
  have hcardEt : 3 ^ (d / 2) ≤ Nat.card Xt := by
    rw [hcardt, hcardX]
    exact hr
  obtain ⟨Θ, hΘw, hΘ⟩ := exists_rank_pres_hom hK hd φ
  have hΘmem : ∀ b ∈ Xt, Θ b ∈ Xt := by
    intro b hb
    obtain ⟨a, ha, hba⟩ := mem_inducedSub.mp hb
    exact ⟨α' * a * α'⁻¹, hαN a ha, Ind.conj hφ (show Ind ψ a b from hba) hΘ⟩
  have hfix : ∀ B ∈ Xt, Θ B = B := by
    refine eq_of_rank_pres_sq hK hEt hcardEt Θ hΘw hΘmem (fun b hb => ?_)
    obtain ⟨a, ha, hba⟩ := mem_inducedSub.mp hb
    have hba' : Ind ψ a b := hba
    have h1 : Ind ψ (α' * a * α'⁻¹) (Θ b) := Ind.conj hφ hba' hΘ
    have h2 : Ind ψ (a⁻¹ * (α' * a * α'⁻¹)) (b⁻¹ * Θ b) := hba'.inv.mul h1
    have h3 : Ind ψ (α' * (a⁻¹ * (α' * a * α'⁻¹)) * α'⁻¹) (Θ (b⁻¹ * Θ b)) :=
      Ind.conj hφ h2 hΘ
    rw [hT1 a ha] at h3
    exact Ind.unique hψ hinj h3 h2
  apply hb₀ne
  obtain ⟨φ₀, ⟨B₀, rfl⟩, hφ₀⟩ := hAI b₀ hb₀
  have hB₀ : Ind ψ b₀ B₀ := hφ₀
  have h1 : Ind ψ (α' * b₀ * α'⁻¹) (Θ B₀) := Ind.conj hφ hB₀ hΘ
  rw [hfix B₀ ⟨b₀, hb₀, hB₀⟩] at h1
  exact mulAut_eq_of_forall ψ hker hperf fun l => (h1 l).symm.trans (hB₀ l)

end CFSG.StandardType.LinTwoTv

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_linTwo_tv {p : ℕ} {lab : LargeEvenLabel} (h : GGLinTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp⟩ := h
  dsimp only at ht hl hn hp
  subst ht hn hp
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', (l + 1) / 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TwoThree.ggTorusLift_two hK2 (by omega)),
    ggNoTransvectionSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinTwoTv.noTransvectionSCr_two hK2 (by omega))⟩

theorem ggLTransvectionCenterInputOn_linTwo_holds : GGLTransvectionCenterInputOn GGLinTwoLabel :=
  ggLTransvectionCenterInputOn_of_labelsSCr (fun _ _ h => Or.inl h.1)
    fun _ _ _ _ h => largeEvenLabelAll_linTwo_tv h

theorem ggLTransvectionCenterInputOn_of_not_linTwo {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGLTransvectionCenterInputOn S :=
  CorFourTwoVacMore.lTransvectionCenterInputOn_mono (fun p lab hlab => by
    by_cases hl : GGLinTwoLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩) (ggLTransvectionCenterInputOn_linTwo_holds.or h)

end CFSG.StandardType

end
