module

public import CFSG.Quasithin.MS93.S5A53
public import CFSG.Quasithin.MS93.S512NMod

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open scoped commutatorElement Matrix

namespace S512N

section Rigid

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem sqf_mul (g g' : MSP.Sp4 F) :
    S5.sqf (MSP.mat (g * g')) = S5.sqf (MSP.mat g) + MSP.mat g *ᵥ S5.sqf (MSP.mat g') := by
  have hsp := S5.statedSp_eq_jpSp4 (F := F)
  let ι : MSP.Sp4 F → ↥(Explicit.sp4 F) := fun g => ⟨g, by rw [← hsp]; exact g.2⟩
  exact JonesParshall.spF0_mem (ι g) (ι g')

theorem cform_mul (B : F) (m : MSP.V4 F) (g g' : MSP.Sp4 F) :
    S5.cform B m (g * g') = S5.cform B m g + MSP.mat g *ᵥ S5.cform B m g' := by
  simp only [S5.cform, sqf_mul, MSP.mat_mul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_sub, smul_add]
  abel

@[expose] def Rigid (A : Subgroup (MSP.Sp4 F)) : Prop :=
  ∀ (B : F) (m : MSP.V4 F), (∀ x ∈ A, S5.cform B m x = 0) → B = 0

theorem Rigid.mono {A A' : Subgroup (MSP.Sp4 F)} (hA : Rigid A) (hAA' : A ≤ A') : Rigid A' :=
  fun B m h => hA B m fun x hx => h x (hAA' hx)

theorem Rigid.map_conj {A : Subgroup (MSP.Sp4 F)} (hA : Rigid A) (g₀ : MSP.Sp4 F) :
    Rigid (A.map (MulAut.conj g₀).toMonoidHom) := fun B m h =>
  hA B _ (S5.cform_vanish_of_conj (cform_mul B m) (fun _ => rfl) h)

theorem rigid_qPoint {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) : Rigid (MSP.qPoint p) := by
  obtain ⟨g₀, rfl⟩ := MSP.exists_map_pt₀_eq hp
  rw [MSP.qPoint_map_eq]
  exact Rigid.map_conj (fun _ _ h => S5.eq_zero_of_cform_Q₂ h) g₀

omit [Fintype F] [CharP F 2] in
private theorem eq_zero_of_sqrt_mul' [Fintype F] [CharP F 2] {B w : F} (hF : 2 < Nat.card F)
    (h : ∀ c : F, B * JonesParshall.sqrtF c + c * w = 0) : B = 0 := by
  obtain ⟨s, hs0, hs1⟩ := MSP.exists_ne_zero_ne_one hF
  have h1 := h 1
  rw [JonesParshall.sqrtF_one, mul_one, one_mul] at h1
  have h2 := h (s ^ 2)
  have hs : JonesParshall.sqrtF (s ^ 2) = s := by
    apply JonesParshall.sq_inj
    rw [JonesParshall.sqrtF_sq]
  rw [hs] at h2
  have hw : w = 0 := by
    have hB : B = -w := by linear_combination h1
    rw [hB] at h2
    have h3 : s * (s - 1) * w = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd h5 hs0
      · exact absurd (sub_eq_zero.1 h5) hs1
    · exact h4
  rw [hw, add_zero] at h1
  exact h1

private theorem cform_transv_e₁' (B : F) (m : MSP.V4 F) (c : F) :
    S5.cform B m (MSP.transv (MSP.e₁ F) c) =
      (B * JonesParshall.sqrtF c + c * m (.inr 0)) • MSP.e₁ F := by
  rw [MSP.transv_e₁]
  funext i
  rcases i with i | i <;> fin_cases i
  · show S5.cform B m (tau _) (.inl 0) = _
    rw [S5.cform_tau_inl0]
    simp [sym2, MSP.e₁]
  · show S5.cform B m (tau _) (.inl 1) = _
    rw [S5.cform_tau_inl1]
    simp [sym2, MSP.e₁, JonesParshall.sqrtF_zero]
  · show S5.cform B m (tau _) (.inr 0) = _
    rw [S5.cform_tau_inr]
    simp [MSP.e₁]
  · show S5.cform B m (tau _) (.inr 1) = _
    rw [S5.cform_tau_inr]
    simp [MSP.e₁]

theorem rigid_X₂ (hF : 2 < Nat.card F) : Rigid (MSP.X₂ F) := by
  intro B m h
  refine eq_zero_of_sqrt_mul' hF (w := m (.inr 0)) fun c => ?_
  have h1 := congrFun (h _ (MSP.mem_X₂_iff.2 ⟨c, rfl⟩)) (.inl 0)
  rw [cform_transv_e₁'] at h1
  simpa [MSP.e₁] using h1

theorem rigid_xPoint (hF : 2 < Nat.card F) {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) :
    Rigid (MSP.xPoint p) := by
  obtain ⟨g₀, rfl⟩ := MSP.exists_map_pt₀_eq hp
  rw [← MSP.X₂_map_conj]
  exact (rigid_X₂ hF).map_conj g₀

end Rigid

section JOff

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem rigid_jOffM (h51 : S51) (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hk : k = 1) :
    haveI := hd.charP
    Rigid (S5.imSp a (S5.jOffM M T L (2 ^ k))) := by
  have := hd.charP
  intro B m hvan
  rcases S5.sp4_54M h51 hd h hmin hb with ⟨A₀, l, hA, hl, -, hA₀l, hA₀card, hJA⟩ |
    ⟨p, hp, hTp, hJT⟩
  · have hA₀ : A₀ ∈ S5.candMax (S5.imSp a T) := hA ▸ rfl
    have himJ : S5.imSp a (S5.jOffM M T L (2 ^ k)) = A₀ := by
      rw [hJA]
      exact S5.imSp_liftT hA₀.1.1
    rw [himJ] at hvan
    obtain ⟨g₀, rfl⟩ := MSP.exists_map_ln₀_eq hl
    rw [MSP.qLine_map_eq] at hA₀l
    set J₀ := A₀.map (MulAut.conj g₀⁻¹).toMonoidHom with hJ₀
    have hA₀eq : J₀.map (MulAut.conj g₀).toMonoidHom = A₀ := by
      rw [hJ₀, Subgroup.map_map]
      have : ((MulAut.conj g₀).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom) =
          MonoidHom.id _ := by
        refine MonoidHom.ext fun y => ?_
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
          MonoidHom.id_apply]
        group
      rw [this, Subgroup.map_id]
    have hJ₀Q : J₀ ≤ MSP.Q₁ F := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have := hA₀l hz
      rw [MSP.mem_map_conj] at this
      simpa using this
    have hvan₀ := S5.cform_vanish_of_conj (cform_mul B m) (fun _ => rfl) (A := J₀) (g₀ := g₀)
      (by rw [hA₀eq]; exact hvan)
    by_contra hB0
    have hcJ : Nat.card J₀ = Nat.card A₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective
    subst hk
    have hF2 : Fintype.card F = 2 := by rw [hd.card_eq, pow_one]
    have h4 : 4 ≤ Nat.card J₀ := by
      rw [hcJ]
      rw [hd.nat_card_eq] at hA₀card
      simpa using hA₀card
    obtain ⟨y₁, y₂, hy₁, hy₂, -, -, -, hJ₀eq⟩ := S5.eq_xPoint_sup_of_cform hF2 hB0 hJ₀Q hvan₀ h4
    refine S5.jOffM_ne_xPoint_sup h51 hd h hmin hb
      (p₁ := (F ∙ y₁).map (Matrix.mulVecLin (MSP.mat g₀)))
      (p₂ := (F ∙ y₂).map (Matrix.mulVecLin (MSP.mat g₀))) ?_ ?_ ?_
    · have hp := MSP.isPoint_span hy₁
      unfold MSP.IsPoint at hp ⊢
      rw [← hp]
      exact (Submodule.equivMapOfInjective _ (MSP.mulVec_mat_injective g₀) _).finrank_eq.symm
    · have hp := MSP.isPoint_span hy₂
      unfold MSP.IsPoint at hp ⊢
      rw [← hp]
      exact (Submodule.equivMapOfInjective _ (MSP.mulVec_mat_injective g₀) _).finrank_eq.symm
    · rw [himJ, ← hA₀eq, hJ₀eq, Subgroup.map_sup, MSP.xPoint_map_conj, MSP.xPoint_map_conj]
  · have himJ : S5.imSp a (S5.jOffM M T L (2 ^ k)) = MSP.qPoint p := by rw [hJT, hTp]
    rw [himJ] at hvan
    exact rigid_qPoint hp B m hvan

end JOff

section Section

variable {Γ : Type*} [Group Γ] {S : Type} [CommGroup S] {ρ : Γ →* MulAut S}
  {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) {F : Type} [Field F] [Fintype F]

theorem mem_of_rigid {k : ℕ} (hF : Fintype.card F = 2 ^ k) (hk : 1 ≤ k)
    {a : Γ →* MSP.Sp4 F} (ha : Function.Surjective a)
    {θ : ↥S₀ ≃* Multiplicative (MSP.V4 F)}
    (hθ : ∀ (g : Γ) (s : ↥S₀), Multiplicative.toAdd (θ (restrict ρ hS₀ g s)) =
      MSP.mat (a g) *ᵥ Multiplicative.toAdd (θ s))
    (hfix : ∀ s : S, (∀ g, ρ g s = s) → s = 1)
    {w : S} (hw : ∀ g, ρ g w * w⁻¹ ∈ S₀) (hker : ∀ g, a g = 1 → ρ g w = w)
    {J : Subgroup Γ} (hJ : haveI := charP_of_card_eq_prime_pow hF; Rigid (J.map a))
    (hvan : ∀ j ∈ J, ρ j w = w) : w ∈ S₀ := by
  have := charP_of_card_eq_prime_pow hF
  set pre := Function.surjInv ha with hpre
  have hpre_a : ∀ x, a (pre x) = x := Function.surjInv_eq ha
  let d : Γ → ↥S₀ := fun g => ⟨ρ g w * w⁻¹, hw g⟩
  have hd_mul : ∀ g g', d (g * g') = restrict ρ hS₀ g (d g') * d g := by
    intro g g'
    apply Subtype.ext
    simp only [d, Subgroup.coe_mul, coe_restrict_apply, map_mul, MulAut.mul_apply, map_inv]
    group
  have hd_eq : ∀ g g', a g = a g' → d g = d g' := by
    intro g g' hgg'
    have h1 : a (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, hgg', inv_mul_cancel]
    have h2 := hker _ h1
    have h3 : ρ g w = ρ g' w := by
      have := congrArg (ρ g') h2
      rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left] at this
    apply Subtype.ext
    simp only [d, h3]
  let φ : MSP.Sp4 F → MSP.V4 F := fun x => Multiplicative.toAdd (θ (d (pre x)))
  have hφa : ∀ g, φ (a g) = Multiplicative.toAdd (θ (d g)) := fun g => by
    simp only [φ]
    rw [hd_eq _ _ (hpre_a (a g))]
  have hφ : ∀ x y, φ (x * y) = φ x + MSP.mat x *ᵥ φ y := by
    intro x y
    obtain ⟨g, rfl⟩ := ha x
    obtain ⟨g', rfl⟩ := ha y
    rw [← map_mul, hφa, hφa, hφa, hd_mul, map_mul, toAdd_mul, hθ, add_comm]
  obtain ⟨B, m, hBm⟩ := S5.exists_eq_sqf hF hk hφ
  have hB : B = 0 := hJ B m (by
    rintro _ ⟨j, hj, rfl⟩
    have h1 := hBm (a j)
    rw [hφa] at h1
    have h0 : d j = 1 := Subtype.ext (by simp [d, hvan j hj])
    rw [S5.cform, ← h1, h0, map_one, toAdd_one])
  set s₀ : ↥S₀ := θ.symm (Multiplicative.ofAdd m) with hs₀
  have hθs₀ : Multiplicative.toAdd (θ s₀) = m := by simp [s₀]
  have hfixw : ∀ g, ρ g (w * (s₀ : S)⁻¹) = w * (s₀ : S)⁻¹ := by
    intro g
    have h1 : d g = restrict ρ hS₀ g s₀ * s₀⁻¹ := by
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hθ, hθs₀, ← hφa, hBm, hB, zero_smul, zero_add,
        sub_eq_add_neg]
    have h2 := congrArg Subtype.val h1
    simp only [d, Subgroup.coe_mul, Subgroup.coe_inv, coe_restrict_apply] at h2
    rw [map_mul, map_inv]
    have h3 : ρ g w = ρ g (s₀ : S) * (s₀ : S)⁻¹ * w := by
      rw [← h2, inv_mul_cancel_right]
    rw [h3, mul_comm (ρ g (s₀ : S) * (s₀ : S)⁻¹) w, mul_assoc, mul_assoc,
      mul_comm ((s₀ : S)⁻¹) (ρ g (s₀ : S))⁻¹, mul_inv_cancel_left]
  have h1 := hfix _ hfixw
  rw [mul_inv_eq_one] at h1
  rw [h1]
  exact s₀.2

end Section

end S512N

end CFSG.Quasithin.MS93
