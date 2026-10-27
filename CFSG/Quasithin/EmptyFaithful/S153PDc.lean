module

public import CFSG.Quasithin.EmptyFaithful.S153PDb
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2
public import CFSG.Quasithin.Background.G2Omega4PlusQuot

public section

namespace CFSG.Quasithin

open scoped commutatorElement Pointwise MatrixGroups

namespace S153P

section Defs

variable {G : Type} [Group G]

namespace PD

theorem exists_factor {J R E : Subgroup G} (Q : QuotSetting J R E) [(E.subgroupOf R).Normal]
    (β : ↥J →* SL(2, ZMod 2)) (hβs : Function.Surjective β)
    (hβk : ∀ x : ↥J, β x = 1 ↔ (x : G) ∈ R) :
    ∃ ρ : SL(2, ZMod 2) →* MulAut (SecQuot R E), ∀ m : ↥J, ρ (β m) = Q.convAct m := by
  have hker : β.ker ≤ Q.convAct.ker := fun x hx => Q.convAct_ker x ((hβk x).1 hx)
  exact ⟨(MonoidHom.liftOfSurjective β hβs) ⟨Q.convAct, hker⟩, fun m =>
    MonoidHom.liftOfRightInverse_comp_apply β _ _ ⟨Q.convAct, hker⟩ m⟩

end PD

theorem exists_natSum [Finite G] {J R E F X : Subgroup G} {u₀ j : G}
    (β : ↥J →* SL(2, ZMod 2)) (hβs : Function.Surjective β)
    (hβk : ∀ x : ↥J, β x = 1 ↔ (x : G) ∈ R)
    (hRJ : R ≤ J) (hER : E ≤ R) (hFR : F ≤ R) (hXR : X ≤ R) (hFX : F ⊓ X = E)
    (hprod : ∀ r ∈ R, ∃ f ∈ F, ∃ x ∈ X, r = f * x)
    (hnR : ∀ a ∈ J, ∀ b ∈ R, a * b * a⁻¹ ∈ R) (hnE : ∀ a ∈ J, ∀ b ∈ E, a * b * a⁻¹ ∈ E)
    (hab : ∀ a ∈ R, ∀ b ∈ R, ⁅a, b⁆ ∈ E) (hsq : ∀ a ∈ R, a * a ∈ E)
    (hu₀ : u₀ ∈ J) (hj : j ∈ J)
    (hα1 : ∀ f ∈ F, ⁅u₀, f⁆ ∈ E) (hα2 : ∀ r ∈ R, ⁅u₀, r⁆ ∈ F)
    (hδ1 : ∀ x ∈ X, j * x * j⁻¹ ∈ F) (hδ2 : ∀ f ∈ F, j⁻¹ * f * j ∈ X)
    (hβu : β ⟨u₀, hu₀⟩ ≠ 1) (hβu2 : β ⟨u₀, hu₀⟩ * β ⟨u₀, hu₀⟩ = 1)
    (hβj : β ⟨j, hj⟩ ≠ 1) (hβj3 : β ⟨j, hj⟩ ^ 3 = 1) :
    ∃ r : ℕ, IsSumOfNatSL2ModulesN153 r J R R E := by
  classical
  have Q : QuotSetting J R E := ⟨hER, hRJ, hnR, hnE, hab, hsq⟩
  have : (E.subgroupOf R).Normal := Q.normal
  let _ : CommGroup (SecQuot R E) := Q.quotCommGroup
  have : Finite (SecQuot R E) := Finite.of_surjective (secMk R E) secMk_surjective
  obtain ⟨ρ, hρ⟩ := PD.exists_factor Q β hβs hβk
  have hrel : β ⟨u₀, hu₀⟩ * (β ⟨j, hj⟩)⁻¹ * β ⟨u₀, hu₀⟩ * β ⟨j, hj⟩ = (β ⟨j, hj⟩)⁻¹ := by
    rcases PD.sl2_rel_aux (β ⟨u₀, hu₀⟩) (β ⟨j, hj⟩) with h | h | h | h | h
    · exact absurd hβu2 h
    · exact absurd h hβu
    · exact absurd hβj3 h
    · exact absurd h hβj
    · exact h
  have hmk : ∀ (m : ↥J) (x : ↥R), ρ (β m) (secMk R E x) =
      secMk R E ⟨(m : G) * x * (m : G)⁻¹, hnR m m.2 x x.2⟩ := fun m x => by
    rw [hρ m]
    exact Q.convAct_mk m x
  have hEX : E ≤ X := hFX ▸ inf_le_right
  have hFXb : ∀ y ∈ secImg R E F, y ∈ secImg R E X → y = 1 := by
    intro y hyF hyX
    obtain ⟨x, hxF, rfl⟩ := mem_secImg.1 hyF
    obtain ⟨x', hx'X, hxx'⟩ := mem_secImg.1 hyX
    have h1 : (x' : G)⁻¹ * x ∈ E := secMk_eq_secMk_iff.1 hxx'
    have hxX : (x : G) ∈ X := by
      have : (x : G) = x' * ((x' : G)⁻¹ * x) := by group
      rw [this]
      exact X.mul_mem hx'X (hEX h1)
    have hxE : (x : G) ∈ F ⊓ X := ⟨hxF, hxX⟩
    rw [hFX] at hxE
    exact secMk_eq_one_iff.2 hxE
  have hprodb : ∀ y : SecQuot R E, ∃ f ∈ secImg R E F, ∃ x ∈ secImg R E X, y = f * x := by
    intro y
    obtain ⟨r, rfl⟩ := secMk_surjective (A := R) (B := E) y
    obtain ⟨f, hf, x, hx, hrfx⟩ := hprod r r.2
    refine ⟨secMk R E ⟨f, hFR hf⟩, secMk_mem_secImg hf, secMk R E ⟨x, hXR hx⟩,
      secMk_mem_secImg hx, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hrfx
  have hα1b : ∀ f ∈ secImg R E F, ρ (β ⟨u₀, hu₀⟩) f = f := by
    intro f hf
    obtain ⟨x, hxF, rfl⟩ := mem_secImg.1 hf
    rw [hmk ⟨u₀, hu₀⟩ x, secMk_eq_secMk_iff]
    have h := hα1 (x : G)⁻¹ (inv_mem hxF)
    have e : ((u₀ * (x : G) * u₀⁻¹)⁻¹ * x) = ⁅u₀, (x : G)⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    exact e ▸ h
  have hα2b : ∀ y : SecQuot R E, ρ (β ⟨u₀, hu₀⟩) y * y⁻¹ ∈ secImg R E F := by
    intro y
    obtain ⟨x, rfl⟩ := secMk_surjective (A := R) (B := E) y
    rw [hmk ⟨u₀, hu₀⟩ x, ← map_inv, ← map_mul]
    exact secMk_mem_secImg (hα2 x x.2)
  have hδ1b : ∀ x ∈ secImg R E X, ρ (β ⟨j, hj⟩) x ∈ secImg R E F := by
    intro x hx
    obtain ⟨x₀, hx₀X, rfl⟩ := mem_secImg.1 hx
    rw [hmk ⟨j, hj⟩ x₀]
    exact secMk_mem_secImg (hδ1 x₀ hx₀X)
  have hδ2b : ∀ f ∈ secImg R E F, ρ (β ⟨j, hj⟩)⁻¹ f ∈ secImg R E X := by
    intro f hf
    obtain ⟨f₀, hf₀F, rfl⟩ := mem_secImg.1 hf
    rw [← map_inv, hmk (⟨j, hj⟩ : ↥J)⁻¹ f₀]
    refine secMk_mem_secImg ?_
    simpa using hδ2 f₀ hf₀F
  have h2 : ∀ y : SecQuot R E, y * y = 1 := Q.quot_sq
  have hfpf : ∀ y : SecQuot R E, ρ (SL2Model.c3 (ZMod 2)) y = y → y = 1 := by
    have hcore := PD.fpf_mul h2 ρ (β ⟨u₀, hu₀⟩) (β ⟨j, hj⟩) hrel (secImg R E F) (secImg R E X)
      hFXb hprodb hα1b hα2b hδ1b hδ2b
    rcases PD.sl2_c3_aux (SL2Model.c3 (ZMod 2)) (β ⟨j, hj⟩) with h | h | h | h | h | h
    · exact absurd SL2Model.c3_pow_three h
    · exact absurd h SL2Model.c3_ne_one
    · exact absurd hβj3 h
    · exact absurd h hβj
    · rw [h]
      exact hcore
    · rw [h]
      intro y hy
      apply hcore y
      have h3 : ρ (β ⟨j, hj⟩) (ρ (β ⟨j, hj⟩)⁻¹ y) = y := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      rw [hy] at h3
      exact h3
  obtain ⟨s, e, he⟩ := PD.mul_natural_sum_of_fpf h2 ρ hfpf
  refine ⟨s, β, e.toMonoidHom.comp (secMk R E), hβs, hβk, ?_, ?_, ?_⟩
  · exact e.surjective.comp secMk_surjective
  · intro x
    show e (secMk R E x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, secMk_eq_one_iff]
  · intro m x y hy
    show e (secMk R E y) = _
    have h1 : secMk R E y = ρ (β m) (secMk R E x) := by
      rw [hmk m x]
      congr 1
      exact Subtype.ext hy
    rw [h1, he]
    rfl

end Defs

end S153P

end CFSG.Quasithin
