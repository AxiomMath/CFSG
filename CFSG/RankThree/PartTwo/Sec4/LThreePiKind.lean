module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open Matrix

section Perfect

variable {S : Type*} [Group S]

theorem mulAut_eq_of_inv_mul_mem_center [Group.IsPerfect S] {α β : MulAut S}
    (h : ∀ s, (β s)⁻¹ * α s ∈ Subgroup.center S) : α = β := by
  let z : S →* Subgroup.center S :=
    { toFun := fun s => ⟨(β s)⁻¹ * α s, h s⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h s) ((β t)⁻¹)
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        calc (β t)⁻¹ * (β s)⁻¹ * (α s * α t) = (β t)⁻¹ * ((β s)⁻¹ * α s) * α t := by group
          _ = (β s)⁻¹ * α s * (β t)⁻¹ * α t := by rw [hc]
          _ = (β s)⁻¹ * α s * ((β t)⁻¹ * α t) := by group }
  have hker : z.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := S)]
    exact Abelianization.commutator_subset_ker z
  ext s
  have hs : z s = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top s)
  have hs' : (β s)⁻¹ * α s = 1 := congrArg Subtype.val hs
  exact (inv_mul_eq_one.mp hs').symm

end Perfect

section Models

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def statedSLEquiv : StatedSL n K ≃* SpecialLinearGroup (Fin n) K :=
  (MulEquiv.subgroupCongr (statedSL_eq_range_toGL n K)).trans
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

variable {n K}

theorem coe_statedSLEquiv_symm (g : SpecialLinearGroup (Fin n) K) :
    (((statedSLEquiv n K).symm g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g := by
  change ((MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective g :
    GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = g
  rw [MonoidHom.ofInjective_apply]
  rfl

theorem coe_statedSLEquiv_symm_eq_toGL (g : SpecialLinearGroup (Fin n) K) :
    (((statedSLEquiv n K).symm g : StatedSL n K) : GL (Fin n) K) =
      Matrix.SpecialLinearGroup.toGL g :=
  Units.ext (coe_statedSLEquiv_symm g)

theorem toGL_statedSLEquiv (s : StatedSL n K) :
    Matrix.SpecialLinearGroup.toGL (statedSLEquiv n K s) = (s : GL (Fin n) K) := by
  conv_rhs => rw [← (statedSLEquiv n K).symm_apply_apply s]
  rw [coe_statedSLEquiv_symm_eq_toGL]

@[expose] noncomputable def slPiTrueEquiv (q : ℕ) (K : Type) [Field K] :
    slPi true 3 q K ≃* SpecialLinearGroup (Fin 3) K :=
  statedSLEquiv 3 K

theorem toGL_slPiTrueEquiv {q : ℕ} (s : slPi true 3 q K) :
    Matrix.SpecialLinearGroup.toGL (slPiTrueEquiv q K s) = (s : GL (Fin 3) K) :=
  toGL_statedSLEquiv (n := 3) s

end Models

section Theta

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def thetaBotEquiv (hθ : aschbacherSolvableCore 3 L = ⊥) :
    L ⧸ aschbacherSolvableCore 3 L ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot

theorem thetaBotEquiv_mk (hθ : aschbacherSolvableCore 3 L = ⊥) (l : L) :
    thetaBotEquiv hθ (l : L ⧸ aschbacherSolvableCore 3 L) = l :=
  rfl

theorem thetaBotEquiv_symm_apply (hθ : aschbacherSolvableCore 3 L = ⊥) (l : L) :
    (thetaBotEquiv hθ).symm l = (l : L ⧸ aschbacherSolvableCore 3 L) := by
  rw [MulEquiv.symm_apply_eq, thetaBotEquiv_mk]

end Theta

section Action

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {S : Type*} [Group S]

@[expose] noncomputable def slAct (e : L ≃* S) : Subgroup.normalizer (L : Set G) →* MulAut S :=
  (MulAut.congr e).toMonoidHom.comp L.normalizerMonoidHom

omit [Finite G] in
theorem slAct_apply (e : L ≃* S) (x : Subgroup.normalizer (L : Set G)) (s : S) :
    slAct e x s = e (L.normalizerMonoidHom x (e.symm s)) :=
  rfl

omit [Finite G] in
theorem coe_normalizerMonoidHom (x : Subgroup.normalizer (L : Set G)) (l : L) :
    ((L.normalizerMonoidHom x l : L) : G) = x * l * x⁻¹ :=
  rfl

theorem inducedAutHom_thetaBot {M : Type*} [Group M] (hθ : aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* S) (ψ : S ≃* M) (x : Subgroup.normalizer (L : Set G)) :
    inducedAutHom L ((thetaBotEquiv hθ).trans (e.trans ψ)) x = MulAut.congr ψ (slAct e x) := by
  ext m
  rw [inducedAutHom_apply]
  change ψ (e (thetaBotEquiv hθ (thetaQuotMulAut L (compAction L x)
    ((thetaBotEquiv hθ).symm (e.symm (ψ.symm m)))))) = ψ (e (L.normalizerMonoidHom x
      (e.symm (ψ.symm m))))
  rw [thetaBotEquiv_symm_apply, thetaQuotMulAut_mk, thetaBotEquiv_mk]
  rfl

end Action

section Linear

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {p f : ℕ}

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction

theorem toGL_slFieldAut (σ : K ≃+* K) (g : SpecialLinearGroup (Fin 3) K) :
    Matrix.SpecialLinearGroup.toGL (CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ g) =
      frobGL σ (Matrix.SpecialLinearGroup.toGL g) := by
  apply Units.ext
  ext i j
  rfl

theorem conj_frobGL_conj (H : GL (Fin 3) K) (σ : K ≃+* K) (s : GL (Fin 3) K) :
    H * frobGL σ (H⁻¹ * s * H) * H⁻¹ =
      (H * frobGL σ H⁻¹) * frobGL σ s * (H * frobGL σ H⁻¹)⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

theorem slAct_pgl_or_field_linear (hK : PiField true p f K) [Group.IsPerfect L]
    (hθ : aschbacherSolvableCore 3 L = ⊥) (e : L ≃* slPi true 3 (p ^ f) K)
    (x : Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    (∃ y ∈ glPi true 3 (p ^ f) K, ∀ s : slPi true 3 (p ^ f) K,
        (slAct e x s : GL (Fin 3) K) = y * s * y⁻¹) ∨
    (InducesStdKind L x .field ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard true (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard true (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi true 3 (p ^ f) K, ∀ s : slPi true 3 (p ^ f) K,
        (slAct e x s : GL (Fin 3) K) = g * frobGL σ s * g⁻¹) := by
  have := hK.finite
  set ψ : slPi true 3 (p ^ f) K ≃* SpecialLinearGroup (Fin 3) K := slPiTrueEquiv (p ^ f) K
    with hψ
  set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
  have hind := inducedAutHom_thetaBot hθ e ψ x
  set β := MulAut.congr ψ (slAct e x) with hβ
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    Group.IsPerfect.ofSurjective (f := (e.trans ψ).toMonoidHom) (e.trans ψ).surjective
  set α := descendAut 3 K β with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, hβ, ← map_pow, ← map_pow, hx3, map_one, map_one, map_one]
  have hlift : ∀ γ : MulAut (SpecialLinearGroup (Fin 3) K), descendAut 3 K γ = α → β = γ := by
    intro γ hγ
    apply mulAut_eq_of_inv_mul_mem_center
    intro g
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
      ← descendAut_proj, ← descendAut_proj, hγ]
  have hcoe : ∀ s : slPi true 3 (p ^ f) K, ((slAct e x s : slPi true 3 (p ^ f) K) :
      GL (Fin 3) K) = Matrix.SpecialLinearGroup.toGL (β (ψ s)) := by
    intro s
    have h1 : β (ψ s) = ψ (slAct e x s) := by
      rw [hβ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [h1, hψ, toGL_slPiTrueEquiv]
  by_cases hD : α ∈ linearAutGroup 3 K
  · left
    rw [linearAutGroup_eq_range] at hD
    obtain ⟨A, hA⟩ := hD
    have hβA := hlift (slConjugation 3 K A) hA
    refine ⟨A, mem_glPi_true _ _, fun s => ?_⟩
    rw [hcoe, hβA, toGL_slConjugation, hψ, toGL_slPiTrueEquiv]
  · right
    refine ⟨InducesStdKind.sl 3 K (le_refl 3) ⟨e', x.2, ?_⟩, ?_⟩
    · change (stdPinnedPSL 3 K).HasKind (descendAut 3 K (inducedAutHom L e' x)) .field
      rw [hind]
      exact isField_of_pow_three_eq_one le_rfl hα3 hD
    · obtain ⟨σ, hσ3, H, hαH⟩ := linear_order_three_field_descent le_rfl α hα3 hD
      have hβγ := hlift (slConjugation 3 K H * CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
        (slConjugation 3 K H)⁻¹) (by rw [hαH, map_mul, map_mul, map_inv]; rfl)
      obtain ⟨h3f, hσc⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime hK.one_le
        (hK.card : Nat.card K = p ^ f) hσ3
      obtain ⟨f₀, rfl⟩ := h3f
      have hf₀ : 3 * f₀ / 3 = f₀ := by omega
      have hf₀' : 2 * (3 * f₀) / 3 = 2 * f₀ := by omega
      refine ⟨f₀, rfl, σ, ?_, H * frobGL σ H⁻¹, mem_glPi_true _ _, fun s => ?_⟩
      · rcases hσc with h | h
        · exact Or.inl fun c => by rw [h, hf₀]; rfl
        · exact Or.inr fun c => by
            rw [h, hf₀']
            change c ^ p ^ (2 * f₀) = c ^ (p ^ f₀) ^ 2
            rw [← pow_mul, mul_comm]
      · rw [← conj_frobGL_conj, hcoe, hβγ, MulAut.mul_apply, MulAut.mul_apply,
          toGL_slConjugation, toGL_slFieldAut, ← map_inv, toGL_slConjugation, hψ,
          toGL_slPiTrueEquiv, inv_inv]

end Linear

section Unitary

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {p f : ℕ}

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

@[expose] def slPiFalseEquiv (p f : ℕ) (K : Type) [Field K] :
    slPi false 3 (p ^ f) K ≃* unitarySU p f K 3 :=
  MulEquiv.subgroupCongr rfl

theorem coe_slPiFalseEquiv (s : slPi false 3 (p ^ f) K) :
    ((slPiFalseEquiv p f K s : unitarySU p f K 3) : GL (Fin 3) K) = s :=
  rfl

theorem glAut_eq_frobGL (σ : K ≃+* K) (g : GL (Fin 3) K) : glAut σ g = frobGL σ g :=
  rfl

theorem congr_centerDescend_suConj (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (A : unitaryIsom3 h) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (suConj h A)) = psuConj h A := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

theorem congr_centerDescend_suField (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (σ : K ≃+* K) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (suField h σ)) = psuField h σ := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

theorem slAct_pgl_or_field_unitary (hK : PiField false p f K) (hq2 : 2 < p ^ f)
    [Group.IsPerfect L] (hθ : aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* slPi false 3 (p ^ f) K) (x : Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    (∃ y ∈ glPi false 3 (p ^ f) K, ∀ s : slPi false 3 (p ^ f) K,
        (slAct e x s : GL (Fin 3) K) = y * s * y⁻¹) ∨
    (InducesStdKind L x .field ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard false (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard false (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi false 3 (p ^ f) K, ∀ s : slPi false 3 (p ^ f) K,
        (slAct e x s : GL (Fin 3) K) = g * frobGL σ s * g⁻¹) := by
  have h := hK.unitary
  have := hK.finite
  set ψ := slPiFalseEquiv p f K with hψ
  set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
  have hind := inducedAutHom_thetaBot hθ e ψ x
  set β := MulAut.congr ψ (slAct e x) with hβ
  have : Group.IsPerfect (unitarySU p f K 3) :=
    Group.IsPerfect.ofSurjective (f := (e.trans ψ).toMonoidHom) (e.trans ψ).surjective
  set α := MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β) with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, ← map_pow, hβ, ← map_pow, ← map_pow, hx3, map_one, map_one, map_one,
      map_one]
  have hlift : ∀ γ : MulAut (unitarySU p f K 3),
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ) = α → β = γ := by
    intro γ hγ
    have hγ' : centerDescend _ γ = centerDescend _ β := (MulAut.congr _).injective hγ
    apply mulAut_eq_of_inv_mul_mem_center
    intro g
    have h1 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
      τ (g : unitarySU p f K 3 ⧸ Subgroup.center _)) hγ'
    simp only [centerDescend_mk] at h1
    exact QuotientGroup.eq.mp h1
  have hcoe : ∀ s : slPi false 3 (p ^ f) K, ((slAct e x s : slPi false 3 (p ^ f) K) :
      GL (Fin 3) K) = ((β (ψ s) : unitarySU p f K 3) : GL (Fin 3) K) := by
    intro s
    have h1 : β (ψ s) = ψ (slAct e x s) := by
      rw [hβ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [h1, hψ, coe_slPiFalseEquiv]
  by_cases hD : α ∈ (psuConj h).range
  · left
    obtain ⟨A, hA⟩ := hD
    have hβA := hlift (suConj h A) (by rw [congr_centerDescend_suConj, hA])
    refine ⟨A, (mem_glPi_false h).mpr A.2, fun s => ?_⟩
    rw [hcoe, hβA, coe_suConj, hψ, coe_slPiFalseEquiv]
    rfl
  · right
    refine ⟨InducesStdKind.su3 h hq2 ⟨e', x.2, ?_⟩, ?_⟩
    · change (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq2)
        (centerDescend _ (inducedAutHom L e' x))) .field
      rw [hind]
      exact isField_psu3_of_pow_three_eq_one hq2 hα3 hD
    · obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq2 α hα3 hD
      have hβγ := hlift (suConj h H * suField h σ * (suConj h H)⁻¹) (by
        rw [hαH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
          congr_centerDescend_suConj, congr_centerDescend_suField])
      have hcard : Nat.card K = p ^ (2 * f) := by
        rw [hK.card]
        change (p ^ f) ^ 2 = p ^ (2 * f)
        rw [← pow_mul, mul_comm]
      obtain ⟨h3f, hσc⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime (by
        have := hK.one_le; omega) hcard hσ3
      obtain ⟨f₀, rfl⟩ : 3 ∣ f := by
        have hc : Nat.Coprime 3 2 := by norm_num
        exact hc.dvd_of_dvd_mul_left h3f
      have hf₀ : 2 * (3 * f₀) / 3 = 2 * f₀ := by omega
      have hf₀' : 2 * (2 * (3 * f₀)) / 3 = 4 * f₀ := by omega
      have hH : (H : GL (Fin 3) K) * frobGL σ (H : GL (Fin 3) K)⁻¹ ∈
          glPi false 3 (p ^ (3 * f₀)) K := by
        refine (mem_glPi_false h).mpr ?_
        rw [← mem_unitaryIsom3]
        exact mul_mem H.2 (glAut_mem_unitaryIsom3 σ (inv_mem H.2))
      refine ⟨f₀, rfl, σ, ?_, _, hH, fun s => ?_⟩
      · rcases hσc with hc | hc
        · exact Or.inl fun c => by
            rw [hc, hf₀]
            change c ^ p ^ (2 * f₀) = c ^ (p ^ f₀) ^ 2
            rw [← pow_mul, mul_comm]
        · exact Or.inr fun c => by
            rw [hc, hf₀']
            change c ^ p ^ (4 * f₀) = c ^ ((p ^ f₀) ^ 2) ^ 2
            rw [← pow_mul, ← pow_mul]
            ring_nf
      · rw [← conj_frobGL_conj, hcoe, hβγ, MulAut.mul_apply, MulAut.mul_apply, coe_suConj,
          coe_suField, ← map_inv, coe_suConj, glAut_eq_frobGL, hψ, coe_slPiFalseEquiv]
        simp only [Subgroup.coe_inv, inv_inv]

end Unitary

section Both

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {p f : ℕ}
  {π : Bool}

theorem slAct_pgl_or_field (hK : PiField π p f K) (hq2 : 2 < p ^ f) [Group.IsPerfect L]
    (hθ : aschbacherSolvableCore 3 L = ⊥) (e : L ≃* slPi π 3 (p ^ f) K)
    (x : Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    (∃ y ∈ glPi π 3 (p ^ f) K, ∀ s : slPi π 3 (p ^ f) K,
        (slAct e x s : GL (Fin 3) K) = y * s * y⁻¹) ∨
    (InducesStdKind L x .field ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
      ((∀ c, σ c = c ^ piCard π (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi π 3 (p ^ f) K, ∀ s : slPi π 3 (p ^ f) K,
        (slAct e x s : GL (Fin 3) K) = g * frobGL σ s * g⁻¹) := by
  cases π
  · exact slAct_pgl_or_field_unitary hK hq2 hθ e x hx3
  · exact slAct_pgl_or_field_linear hK hθ e x hx3

end Both

section Model

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {p f : ℕ}
  {π : Bool}

theorem pow_three_eq_one_of_mem_center (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {z : slPi π 3 (p ^ f) K} (hz : z ∈ Subgroup.center (slPi π 3 (p ^ f) K)) : z ^ 3 = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hzZ : (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
    have := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨c, hc⟩ := hzZ
  have hdet : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    cases π
    · exact ((mem_slPi_false (hπ rfl)).mp z.2).1
    · exact (mem_slPi_true _).mp z.2
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc, ← map_pow]
  have hc3 : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  rw [hc3, map_one]

theorem aschbacherSolvableCore_eq_bot_of_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hLq : CFSG.IsQuasisimple L) (e : L ≃* slPi π 3 (p ^ f) K) :
    aschbacherSolvableCore 3 L = ⊥ := by
  have hchar := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have h3 := hchar.2.2.1
  have hZ : aschbacherSolvableCore 3 L ≤ Subgroup.center L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq
      (inferInstance : (aschbacherSolvableCore 3 L).Normal) with h | h
    · exfalso
      have hsol := hchar.1
      rw [h] at hsol
      have hsolL : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := L)).symm.injective
      have := hLq.1
      have := CFSG.LocalCores.isQuasisimple_nontrivial hLq
      exact Group.IsPerfect.not_isSolvable _ hsolL
    · exact h
  rw [eq_bot_iff]
  intro l hl
  have hlZ := hZ hl
  have hel : e l ∈ Subgroup.center (slPi π 3 (p ^ f) K) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨m, rfl⟩ := e.surjective s
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hlZ m)]
  have hl3 : l ^ 3 = 1 := e.injective (by rw [map_pow, map_one,
    pow_three_eq_one_of_mem_center hK hq hel])
  have hord3 : orderOf l ∣ 3 := orderOf_dvd_of_pow_eq_one hl3
  have hordθ : orderOf (⟨l, hl⟩ : aschbacherSolvableCore 3 L) ∣
      Nat.card (aschbacherSolvableCore 3 L) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hordθ
  have h1 : orderOf l ∣ Nat.gcd 3 (Nat.card (aschbacherSolvableCore 3 L)) :=
    Nat.dvd_gcd hord3 hordθ
  rw [(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  rw [h1]
  exact Subgroup.one_mem _

theorem exists_slPi_model (hL : IsSLThreePi L) (hLq : CFSG.IsQuasisimple L) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      2 < p ^ f ∧ Nonempty (L ≃* slPi π 3 (p ^ f) K) := by
  obtain ⟨q, K, _, _, hK⟩ := hL
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  set p := ringChar K
  have hcardK : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rcases hK with ⟨hq, hq3, ⟨e⟩⟩ | ⟨hq, hq3, ⟨e⟩⟩
  ·
    have hqn : q = p ^ (n : ℕ) := by rw [← hq, hcardK]
    subst hqn
    refine ⟨true, p, n, K, inferInstance, ⟨hp, n.pos, hcardK⟩, hq3, ?_, ⟨e⟩⟩
    have : 2 ≤ p ^ (n : ℕ) := le_trans hp.two_le (Nat.le_self_pow n.ne_zero _)
    omega
  ·
    have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hcardK, hq, sq]⟩
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hm : (n : ℕ) = 2 * m := by
      have h2 : p ^ (2 * m) = p ^ (n : ℕ) := by rw [pow_mul', ← hq, hcardK]
      exact (Nat.pow_right_injective hp.two_le h2).symm
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp at hq3
      · exact h0
    have hPi : PiField false p m K := ⟨hp, hm1, by rw [hq]; rfl⟩
    refine ⟨false, p, m, K, inferInstance, hPi, hq3, ?_, ⟨e⟩⟩
    by_contra h2
    have hpm : p ^ m = 2 := by
      have : 2 ≤ p ^ m := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have hp2 : p = 2 := by
      have := (Nat.prime_two.eq_one_or_self_of_dvd p ⟨p ^ (m - 1), by
        rw [← pow_succ', Nat.sub_add_cancel hm1, hpm]⟩)
      rcases this with h | h
      · exact absurd h hp.one_lt.ne'
      · exact h
    have hm1' : m = 1 := by
      rw [hp2] at hpm
      exact Nat.pow_right_injective le_rfl (show 2 ^ m = 2 ^ 1 by rw [hpm, pow_one])
    have hU : UnitaryFieldData 2 1 K := by
      have := hPi.unitary
      rw [hp2, hm1'] at this
      exact this
    have hcardL : Nat.card L = 216 := by
      rw [Nat.card_congr e.toEquiv]
      have := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
      rw [hp2, hm1']
      exact this
    have := Fintype.ofFinite L
    have hsolv : Group.IsSolvable L :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcardL]; norm_num)
    have : Group.IsPerfect L := hLq.1
    have hnt : Nontrivial L := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardL]
      norm_num
    exact Group.IsPerfect.not_isSolvable L hsolv

end Model

end CFSG.RankThree.PartTwo.Sec4
