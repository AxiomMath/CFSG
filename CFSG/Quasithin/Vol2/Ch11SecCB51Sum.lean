module

public import CFSG.Quasithin.Background.InternalSecSum
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.Assembly.LowTwoRank

namespace B51

section Sum

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}

theorem secIsoL_of_realizesVia {D : FFModel} {π : D.Gam →* ↥H} {I₀ I₁ : Subgroup V}
    (h₀ : D.RealizesVia H I₀ ⊥ π) (h₁ : D.RealizesVia H I₁ ⊥ π) : SecIsoL H I₀ ⊥ I₁ ⊥ := by
  obtain ⟨hπ, -, -, hinv₀, -, hsec, -, β₀, hβs₀, hβk₀, hβe₀⟩ := h₀
  obtain ⟨-, -, -, hinv₁, -, -, -, β₁, hβs₁, hβk₁, hβe₁⟩ := h₁
  have hinj₀ : Function.Injective β₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk₀ u).1 hu))
  have hinj₁ : Function.Injective β₁ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk₁ u).1 hu))
  set e₀ := MulEquiv.ofBijective β₀ ⟨hinj₀, hβs₀⟩ with he₀
  set e₁ := MulEquiv.ofBijective β₁ ⟨hinj₁, hβs₁⟩ with he₁
  refine secIsoL_of_equiv (fun k hk w hw => hinv₀ ⟨k, hk⟩ w hw)
    (fun k hk w hw => hinv₁ ⟨k, hk⟩ w hw) (e₀.trans e₁.symm) ?_
  intro k w
  obtain ⟨γ, rfl⟩ := hπ k
  set w' : ↥I₁ := e₁.symm (e₀ w) with hw'
  have hβw' : β₁ w' = β₀ w := by
    show e₁ (e₁.symm (e₀ w)) = β₀ w
    rw [MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ w)
  have hm' := hsec γ m m.2
  have hx := hinv₀ (π γ) w w.2
  have h1 := hβe₀ γ w m hx hm' hm.symm
  have h2 := hβe₁ γ w' m (hinv₁ (π γ) w' w'.2) hm' (hβw'.trans hm.symm)
  have key : e₁.symm (e₀ ⟨((π γ : ↥H) : MulAut V) w, hx⟩) =
      ⟨((π γ : ↥H) : MulAut V) w', hinv₁ (π γ) w' w'.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    show β₀ _ = β₁ _
    rw [h1, h2]
  exact congrArg Subtype.val key

theorem eq_zero_of_forall_mulVec_eq {K : Type} [Field K] (x : Fin 3 → K)
    (h : ∀ g : ↥(StatedSL 3 K),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x = x) : x = 0 := by
  by_contra hx
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hx (funext h')
  obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
  have hA := h (specialLinearGroupEquivStatedSL 3 K (Matrix.SpecialLinearGroup.transvection hij 1))
  have hcoe : (((specialLinearGroupEquivStatedSL 3 K
      (Matrix.SpecialLinearGroup.transvection hij 1) : ↥(StatedSL 3 K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single i j 1 := rfl
  rw [hcoe] at hA
  have hi := congrFun hA i
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply,
    Function.update_self, one_mul, add_eq_left] at hi
  exact hj hi

theorem fixV_inf_eq_bot_of_nat {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥H}
    {I : Subgroup V} (h : (FFModel.nat (StatedSL 3 K)).RealizesVia H I ⊥ π) :
    fixV H ⊓ I = ⊥ := by
  obtain ⟨-, -, -, -, -, hsec, -, β, -, hβk, hβe⟩ := h
  rw [eq_bot_iff]
  rintro u ⟨hfix, huI⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, huI⟩)
  have hfixm : ∀ γ : ↥(StatedSL 3 K), natAct (StatedSL 3 K) γ m.1 = m.1 := by
    intro γ
    have hu' : ((π γ : ↥H) : MulAut V) ((⟨u, huI⟩ : ↥I) : V) ∈ I := by
      rw [hfix _ (π γ).2]
      exact huI
    have h1 := hβe γ ⟨u, huI⟩ m hu' (hsec γ m m.2) hm.symm
    have h2 : (⟨((π γ : ↥H) : MulAut V) ((⟨u, huI⟩ : ↥I) : V), hu'⟩ : ↥I) = ⟨u, huI⟩ :=
      Subtype.ext (hfix _ (π γ).2)
    have h1' := (congrArg β h2).symm.trans h1
    rw [← hm] at h1'
    have h3 := QuotientGroup.eq.mp h1'
    have h4 : (@id (Multiplicative (Fin 3 → K)) m.1)⁻¹ *
        natAct (StatedSL 3 K) γ (@id (Multiplicative (Fin 3 → K)) m.1) = 1 := h3
    exact (inv_mul_eq_one.mp h4).symm
  have hm0 : Multiplicative.toAdd (α := Fin 3 → K) m.1 = 0 := by
    refine eq_zero_of_forall_mulVec_eq _ fun g => ?_
    have := congrArg (Multiplicative.toAdd (α := Fin 3 → K)) (hfixm g)
    simpa [natAct] using this
  have hm1 : m = 1 := Subtype.ext (Multiplicative.toAdd.injective (hm0.trans toAdd_one.symm))
  have hβ1 : β ⟨u, huI⟩ = 1 := by
    rw [← hm, hm1]
    rfl
  exact (hβk ⟨u, huI⟩).1 hβ1

theorem fixV_inf_sup_eq_bot {I₀ I₁ : Subgroup V} (hinv₀ : ∀ σ ∈ H, ∀ u ∈ I₀, σ u ∈ I₀)
    (hinv₁ : ∀ σ ∈ H, ∀ u ∈ I₁, σ u ∈ I₁) (h₀ : fixV H ⊓ I₀ = ⊥) (h₁ : fixV H ⊓ I₁ = ⊥)
    (hinf : I₀ ⊓ I₁ = ⊥) : fixV H ⊓ (I₀ ⊔ I₁) = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hfix, hu⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
  have hab : ∀ σ ∈ H, σ a = a ∧ σ b = b := by
    intro σ hσ
    have h1 : σ a * σ b = a * b := by rw [← map_mul]; exact hfix σ hσ
    have h2 : σ a * a⁻¹ ∈ I₀ ⊓ I₁ := by
      refine ⟨I₀.mul_mem (hinv₀ σ hσ a ha) (I₀.inv_mem ha), ?_⟩
      have : σ a * a⁻¹ = b * (σ b)⁻¹ := by
        have h3 : σ a = a * b * (σ b)⁻¹ := eq_mul_inv_of_mul_eq h1
        rw [mul_inv_eq_iff_eq_mul, h3, mul_assoc, mul_comm a]
      rw [this]
      exact I₁.mul_mem hb (I₁.inv_mem (hinv₁ σ hσ b hb))
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h2
    refine ⟨h2, ?_⟩
    rw [h2] at h1
    exact mul_left_cancel h1
  have ha1 : a ∈ fixV H ⊓ I₀ := ⟨fun σ hσ => (hab σ hσ).1, ha⟩
  have hb1 : b ∈ fixV H ⊓ I₁ := ⟨fun σ hσ => (hab σ hσ).2, hb⟩
  rw [h₀, Subgroup.mem_bot] at ha1
  rw [h₁, Subgroup.mem_bot] at hb1
  rw [ha1, hb1, mul_one]
  exact Subgroup.one_mem _

end Sum

end B51

end CFSG.Quasithin.Vol2.Ch11.SecC
