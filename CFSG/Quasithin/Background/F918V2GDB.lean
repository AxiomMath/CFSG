module

public import CFSG.Quasithin.Background.F918V2GDA
public import CFSG.Quasithin.Background.F918V2E

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Z391

open CFSG.Quasithin CFSG.Quasithin.B5.Ln CFSG.Assembly.LowTwoRank Module Matrix
open scoped Matrix

section Irr

variable {X : Type} [CommGroup X]

theorem v2gd_mem_of_proj_eq_one {A B : Subgroup X} (hsup : A ⊔ B = ⊤) {T : X →* X}
    (h1 : ∀ a ∈ A, T a = a) (h2 : ∀ b ∈ B, T b = 1) {y : X} (hy : T y = 1) : y ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top y)
  rw [map_mul, h1 a ha, h2 b hb, mul_one] at hy
  rw [hy, one_mul]
  exact hb

theorem v2gd_irr_eq {n : ℕ} {Lb : Subgroup (MulAut X)} {π₀ : ↥(StatedSL n (ZMod 2)) →* ↥Lb}
    {U₁ U₂ : Subgroup X} (hn : 3 ≤ n) (hsup : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (h₁ : RealM Lb U₁ ⊥ π₀ mat) (h₂ : RealM Lb U₂ ⊥ π₀ dmat) {S : Subgroup X}
    (hSinv : ∀ l ∈ Lb, ∀ s ∈ S, l s ∈ S) (hS0 : S ≠ ⊥)
    (hSirr : ∀ J : Subgroup X, (∀ l ∈ Lb, ∀ x ∈ J, l x ∈ J) → J ≤ S → J = ⊥ ∨ J = S) :
    S = U₁ ∨ S = U₂ := by
  have hU₁inv : ∀ l ∈ Lb, ∀ x ∈ U₁, l x ∈ U₁ := fun l hl x hx => h₁.2.2.1 ⟨l, hl⟩ x hx
  have hU₂inv : ∀ l ∈ Lb, ∀ x ∈ U₂, l x ∈ U₂ := fun l hl x hx => h₂.2.2.1 ⟨l, hl⟩ x hx
  have hU₂ne : U₂ ≠ ⊥ := by
    intro h0
    obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := h₂
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd (Pi.single ⟨0, by omega⟩ 1))
    have h1 : β w = 1 := (hβk w).2 (by rw [← h0]; exact w.2)
    rw [h1] at hw
    have h2 := congrFun (Multiplicative.ofAdd.injective hw :
      (0 : Fin n → ZMod 2) = Pi.single ⟨0, by omega⟩ 1) ⟨0, by omega⟩
    simp at h2
  by_cases hA₁ : S ≤ U₁
  · left
    rcases RealM.eq_or_eq h₁ (Or.inl rfl) hSinv bot_le hA₁ with h | h
    · exact absurd h hS0
    · exact h
  by_cases hA₂ : S ≤ U₂
  · right
    rcases RealM.eq_or_eq h₂ (Or.inr rfl) hSinv bot_le hA₂ with h | h
    · exact absurd h hS0
    · exact h
  exfalso
  have hS1 : S ⊓ U₁ = ⊥ := by
    rcases hSirr (S ⊓ U₁) (fun l hl x hx => ⟨hSinv l hl x hx.1, hU₁inv l hl x hx.2⟩)
      inf_le_left with h | h
    · exact h
    · exact absurd (inf_eq_left.1 h) hA₁
  have hS2 : S ⊓ U₂ = ⊥ := by
    rcases hSirr (S ⊓ U₂) (fun l hl x hx => ⟨hSinv l hl x hx.1, hU₂inv l hl x hx.2⟩)
      inf_le_left with h | h
    · exact h
    · exact absurd (inf_eq_left.1 h) hA₂
  have hsup' : U₂ ⊔ U₁ = ⊤ := by rw [sup_comm]; exact hsup
  have hinf' : U₂ ⊓ U₁ = ⊥ := by rw [inf_comm]; exact hinf
  obtain ⟨T₁, hT₁U, hT₁a, hT₁b⟩ := v2e_exists_proj U₁ U₂ hsup hinf
  obtain ⟨T₂, hT₂U, hT₂a, hT₂b⟩ := v2e_exists_proj U₂ U₁ hsup' hinf'
  have hT₂S : ∀ u ∈ U₂, ∃ s ∈ S, T₂ s = u := by
    have hJinv : ∀ l ∈ Lb, ∀ x ∈ S.map T₂, l x ∈ S.map T₂ := by
      rintro l hl _ ⟨s, hs, rfl⟩
      exact ⟨l s, hSinv l hl s hs, v2e_proj_comm hsup' hT₂a hT₂b (hU₂inv l hl) (hU₁inv l hl) s⟩
    have hJle : S.map T₂ ≤ U₂ := by
      rintro _ ⟨s, -, rfl⟩
      exact hT₂U s
    rcases RealM.eq_or_eq h₂ (Or.inr rfl) hJinv bot_le hJle with h | h
    · exfalso
      apply hA₁
      intro s hs
      have : T₂ s ∈ S.map T₂ := ⟨s, hs, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact v2gd_mem_of_proj_eq_one hsup' hT₂a hT₂b this
    · intro u hu
      rw [← h] at hu
      obtain ⟨s, hs, hsu⟩ := hu
      exact ⟨s, hs, hsu⟩
  have hsupS : S ⊔ U₁ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs, hsx⟩ := hT₂S (T₂ x) (hT₂U x)
    refine Subgroup.mem_sup.2 ⟨s, hs, s⁻¹ * x, ?_, mul_inv_cancel_left s x⟩
    refine v2gd_mem_of_proj_eq_one hsup' hT₂a hT₂b ?_
    rw [map_mul, map_inv, hsx, inv_mul_cancel]
  obtain ⟨TS, hTSS, hTSa, hTSb⟩ := v2e_exists_proj S U₁ hsupS hS1
  have hTL : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : X),
      (T₁.comp TS) (((π₀ γ : ↥Lb) : MulAut X) w) = ((π₀ γ : ↥Lb) : MulAut X) ((T₁.comp TS) w) := by
    intro γ w
    have hl := (π₀ γ).2
    simp only [MonoidHom.comp_apply]
    rw [v2e_proj_comm hsupS hTSa hTSb (hSinv _ hl) (hU₁inv _ hl) w,
      v2e_proj_comm hsup hT₁a hT₁b (hU₁inv _ hl) (hU₂inv _ hl)]
  have h0 := v2e_hom_zero h₁ h₂ hn (T₁.comp TS) (fun w _ => hT₁U _) hTL
  apply hU₂ne
  rw [eq_bot_iff]
  intro w hw
  have h1 : T₁ (TS w) = 1 := h0 w hw
  have h2 : TS w ∈ U₂ := v2gd_mem_of_proj_eq_one hsup hT₁a hT₁b h1
  have h3 : TS w = 1 := by
    have : TS w ∈ S ⊓ U₂ := ⟨hTSS w, h2⟩
    rw [hS2, Subgroup.mem_bot] at this
    exact this
  have h4 : w ∈ U₁ := v2gd_mem_of_proj_eq_one hsupS hTSa hTSb h3
  have : w ∈ U₁ ⊓ U₂ := ⟨h4, hw⟩
  rw [hinf] at this
  exact this

end Irr

section Transport

variable {X : Type} [CommGroup X] {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
  [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} {n : ℕ} {Lb : Subgroup (MulAut X)}
  {π₀ : ↥(StatedSL n (ZMod 2)) →* ↥Lb}
  {M₀ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}

theorem v2gd_natRep_of_realM {S : Subgroup X} (hS : RealM Lb S ⊥ π₀ M₀) (θ : X →* Q)
    (hθ : Function.Injective θ) (res : ↥Λ →* ↥Lb) (σ : ↥Λ →* ↥(StatedSL n (ZMod 2)))
    (hσ : ∀ l, π₀ (σ l) = res l)
    (hθres : ∀ (l : ↥Λ) (x : X), θ (((res l : ↥Lb) : MulAut X) x) = l • θ x)
    {P : Subgroup Q} (hP : ∀ q, q ∈ P ↔ ∃ s ∈ S, θ s = q) : V2gdNatRep Λ P n M₀ σ := by
  obtain ⟨-, -, hLS, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hS
  let eθ : ↥S →* ↥P :=
    (θ.comp S.subtype).codRestrict P (fun s => (hP _).2 ⟨s, s.2, rfl⟩)
  have heθ : Function.Bijective eθ :=
    ⟨fun a b hab => Subtype.ext (hθ (congrArg Subtype.val hab)), fun p => by
      obtain ⟨s, hs, hsp⟩ := (hP _).1 p.2
      exact ⟨⟨s, hs⟩, Subtype.ext hsp⟩⟩
  let e : ↥S ≃* ↥P := MulEquiv.ofBijective eθ heθ
  have hβ₀inj : Function.Injective β₀ := fun a b hab => by
    have h1 : β₀ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥S) : X) ∈ (⊥ : Subgroup X) := (hβ₀k _).1 h1
    rw [Subgroup.mem_bot] at h2
    apply Subtype.ext
    exact mul_inv_eq_one.1 h2
  let e₀ : ↥S ≃* Multiplicative (Fin n → ZMod 2) := MulEquiv.ofBijective β₀ ⟨hβ₀inj, hβ₀s⟩
  refine ⟨fun l p hp => ?_, e.symm.trans e₀, fun l p hp => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := (hP p).1 hp
    exact (hP _).2 ⟨_, hLS (res l) s hs, hθres l s⟩
  · set s : ↥S := e.symm p with hs
    have hes : e s = p := e.apply_symm_apply p
    have hθs : θ (s : X) = (p : Q) := congrArg Subtype.val hes
    have hw : ((res l : ↥Lb) : MulAut X) (s : X) ∈ S := hLS (res l) s s.2
    have hlp : (⟨l • (p : Q), hp⟩ : ↥P) =
        e ⟨((res l : ↥Lb) : MulAut X) (s : X), hw⟩ := by
      apply Subtype.ext
      show l • (p : Q) = θ (((res l : ↥Lb) : MulAut X) (s : X))
      rw [hθres, hθs]
    have hw' : ((π₀ (σ l) : ↥Lb) : MulAut X) (s : X) ∈ S := by
      rw [hσ]
      exact hw
    have h1 := hβ₀e (σ l) s hw'
    have h2 : (⟨((π₀ (σ l) : ↥Lb) : MulAut X) (s : X), hw'⟩ : ↥S) =
        ⟨((res l : ↥Lb) : MulAut X) (s : X), hw⟩ :=
      Subtype.ext (congrArg (fun φ : ↥Lb => (φ : MulAut X) (s : X)) (hσ l))
    show Multiplicative.toAdd (e₀ (e.symm ⟨l • (p : Q), hp⟩)) = _
    rw [hlp, MulEquiv.symm_apply_apply, ← h2]
    exact h1

theorem v2gd_natRep_of_irr (hn : 3 ≤ n) {U₁ U₂ : Subgroup X} (hsup : U₁ ⊔ U₂ = ⊤)
    (hinf : U₁ ⊓ U₂ = ⊥) (h₁ : RealM Lb U₁ ⊥ π₀ mat) (h₂ : RealM Lb U₂ ⊥ π₀ dmat)
    (θ : X →* Q) (hθ : Function.Injective θ) (res : ↥Λ →* ↥Lb)
    (σ : ↥Λ →* ↥(StatedSL n (ZMod 2))) (hσ : ∀ l, π₀ (σ l) = res l)
    (hθres : ∀ (l : ↥Λ) (x : X), θ (((res l : ↥Lb) : MulAut X) x) = l • θ x)
    {S : Subgroup X} (hSinv : ∀ l ∈ Lb, ∀ s ∈ S, l s ∈ S) (hS0 : S ≠ ⊥)
    (hSirr : ∀ J : Subgroup X, (∀ l ∈ Lb, ∀ x ∈ J, l x ∈ J) → J ≤ S → J = ⊥ ∨ J = S)
    {P : Subgroup Q} (hP : ∀ q, q ∈ P ↔ ∃ s ∈ S, θ s = q) :
    ∃ M₁ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2),
      (M₁ = mat ∨ M₁ = dmat) ∧ V2gdNatRep Λ P n M₁ σ := by
  rcases v2gd_irr_eq hn hsup hinf h₁ h₂ hSinv hS0 hSirr with rfl | rfl
  · exact ⟨mat, Or.inl rfl, v2gd_natRep_of_realM h₁ θ hθ res σ hσ hθres hP⟩
  · exact ⟨dmat, Or.inr rfl, v2gd_natRep_of_realM h₂ θ hθ res σ hσ hθres hP⟩

end Transport

end CFSG.Quasithin.Z391
