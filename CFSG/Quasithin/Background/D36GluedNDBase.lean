module

public import CFSG.Quasithin.Background.D36GluedL27

public section

namespace CFSG.Quasithin

open scoped commutatorElement

section ND

variable {Y : Type} [CommGroup Y] [Finite Y]

structure NDSetup (X A L₀ : Subgroup (MulAut Y)) (U U' : Subgroup Y) : Prop where
  swap : GluedSwap X A U U'
  exp : ∀ y : Y, y ^ 2 = 1
  le_X : L₀ ≤ X
  cent : ∀ l ∈ L₀, ∀ u ∈ U', l u = u
  stab : L₀ ≤ stabSub U
  simple : IsSimpleGroup ↥L₀
  nonab : ∃ a b : ↥L₀, a * b ≠ b * a
  comm : commV L₀ = U
  norm : ∀ b ∈ A ⊓ stabSub U, ∀ l ∈ L₀, b * l * b⁻¹ ∈ L₀
  inner : ∀ b ∈ A ⊓ stabSub U, ∀ l₀ ∈ L₀,
    (∀ l ∈ L₀, b * l * b⁻¹ = l₀ * l * l₀⁻¹) → ∀ u ∈ U, b u = l₀ u
  nondiag : ¬ ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u

namespace NDSetup

variable {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y} (S : NDSetup X A L₀ U U')

include S

theorem perfect : commutator ↥L₀ = ⊤ := commutator_eq_top_of_simple S.simple S.nonab

theorem elemAb : IsElemAb2 (A ⊓ stabSub U) := by
  obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec S.swap.mem
  have hA2 : IsA2 X A := hAk.1.1
  have hAel : IsElemAbelian2 A := hA2.2.2
  exact ⟨fun a ha b hb => hAel.1 a ha.1 b hb.1, fun a ha => hAel.2 a ha.1⟩

theorem exists_swap : ∃ a : MulAut Y, a ∈ A ∧ a ∉ stabSub U ∧ U.map a.toMonoidHom = U' ∧
    a * a = 1 ∧ (∀ g ∈ A ⊓ stabSub U, g * a = a * g) := by
  obtain ⟨a, ha, haU, hmap, haa, hcomm, -, -⟩ :=
    glued_swap_decomp S.swap.pair S.swap.ne S.swap.mem S.swap.swaps
  exact ⟨a, ha, haU, hmap, haa, hcomm⟩

theorem eq_one_of_trivial {b : MulAut Y} (hb : b ∈ A ⊓ stabSub U) (h : ∀ u ∈ U, b u = u) :
    b = 1 := by
  obtain ⟨a, -, -, hmap, -, hcomm⟩ := S.exists_swap
  refine mulAut_eq_of_eqOn_sup S.swap.pair.sup_eq (fun u hu => by rw [h u hu]; rfl)
    (fun u' hu' => ?_)
  rw [← hmap] at hu'
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
  have hba : b * a = a * b := hcomm b hb
  have h1 : b (a u) = a (b u) := congrArg (fun φ : MulAut Y => φ u) hba
  show b (a u) = (1 : MulAut Y) (a u)
  rw [h1, h u hu]
  rfl

@[expose] noncomputable def thetaAut (b : MulAut Y) (hb : b ∈ A ⊓ stabSub U) : MulAut ↥L₀ where
  toFun l := ⟨b * l * b⁻¹, S.norm b hb l l.2⟩
  invFun l := ⟨b⁻¹ * l * b, by simpa using S.norm b⁻¹ (inv_mem hb) l l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' l₁ l₂ := Subtype.ext (by simp [mul_assoc])

@[expose] noncomputable def theta : ↥(A ⊓ stabSub U) →* MulAut ↥L₀ where
  toFun b := S.thetaAut b b.2
  map_one' := MulEquiv.ext fun l => Subtype.ext (by simp [thetaAut])
  map_mul' b₁ b₂ := MulEquiv.ext fun l => Subtype.ext (by
    show ((b₁ * b₂ : ↥(A ⊓ stabSub U)) : MulAut Y) * l * ((b₁ * b₂ : ↥(A ⊓ stabSub U)) :
      MulAut Y)⁻¹ = ((b₁ : MulAut Y) * ((b₂ : MulAut Y) * l * (b₂ : MulAut Y)⁻¹)) *
        (b₁ : MulAut Y)⁻¹
    simp [mul_assoc])

theorem theta_apply (b : ↥(A ⊓ stabSub U)) (l : ↥L₀) :
    ((S.theta b l : ↥L₀) : MulAut Y) = (b : MulAut Y) * l * (b : MulAut Y)⁻¹ := rfl

theorem theta_injective : Function.Injective S.theta := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hcent : ∀ l ∈ L₀,
      (b : MulAut Y) * l * (b : MulAut Y)⁻¹ = (1 : MulAut Y) * l * (1 : MulAut Y)⁻¹ :=
    fun l hl => by
      have := congrArg (fun φ : MulAut ↥L₀ => ((φ ⟨l, hl⟩ : ↥L₀) : MulAut Y)) hb
      simpa [theta_apply] using this
  have htriv := S.inner b b.2 1 (one_mem _) hcent
  exact Subtype.ext (S.eq_one_of_trivial b.2 (fun u hu => by simpa using htriv u hu))

theorem rk_le {m : ℕ} (hm : AutRankLe ↥L₀ m) : rk ↥(A ⊓ stabSub U) ≤ m := by
  have hE : IsElemAb2 S.theta.range := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩
      rw [← map_mul, ← map_mul, (S.elemAb.1 b₁ b₁.2 b₂ b₂.2 |> Subtype.ext : b₁ * b₂ = b₂ * b₁)]
    · rintro _ ⟨b, rfl⟩
      rw [← map_pow, (Subtype.ext (S.elemAb.2 b b.2) : b ^ 2 = 1), map_one]
  have h1 := hm _ hE
  have h2 : rk ↥(A ⊓ stabSub U) = rk ↥S.theta.range :=
    rk_eq_of_mulEquiv (MonoidHom.ofInjective S.theta_injective)
  omega

theorem exists_not_mem : ∃ l ∈ L₀, ∃ u ∈ U, l u * u⁻¹ ∉ U ⊓ U' := by
  by_contra hcon
  push Not at hcon
  have hD : U ⊓ U' ≤ fixV L₀ := fun d hd l hl => S.cent l hl d hd.2
  have hU : ∀ l ∈ L₀, ∀ y : Y, l y * y⁻¹ ∈ U := fun l hl y => by
    rw [← S.comm]
    exact Subgroup.subset_closure ⟨l, hl, y, rfl⟩
  have hN : ∀ l ∈ L₀, ∀ u ∈ U, l u * u⁻¹ ∈ (⊥ : Subgroup Y) := by
    intro l hl u hu
    have h1 := fixed_of_perfect S.perfect hD (x := u) (fun l' hl' => hcon l' hl' u hu) l hl
    rw [h1, mul_inv_cancel]
    exact Subgroup.one_mem _
  have h3 := perfect_comm_le S.perfect hU hN
  obtain ⟨a, b, hab⟩ := S.nonab
  apply hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  have ha : (a : MulAut Y) y = y := by
    have := h3 a a.2 y
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  have hb : (b : MulAut Y) y = y := by
    have := h3 b b.2 y
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  show (a : MulAut Y) ((b : MulAut Y) y) = (b : MulAut Y) ((a : MulAut Y) y)
  rw [ha, hb, ha]

theorem exists_gl : ∃ ρ : ↥L₀ →* Matrix.GeneralLinearGroup (Fin (rk ↥U - rk ↥(U ⊓ U'))) (ZMod 2),
    Function.Injective ρ := by
  have hcent : L₀ ≤ centSub (U ⊓ U') := fun l hl d hd => S.cent l hl d hd.2
  have hD : L₀ ≤ stabSub (U ⊓ U') := hcent.trans (centSub_le_stabSub _)
  have hinj := glueSecAct_injective S.stab hD S.simple S.exists_not_mem
  have hSec2 : ∀ a : Sec U (U ⊓ U'), a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H u =>
      have : u ^ 2 = 1 := Subtype.ext (S.exp u)
      rw [← QuotientGroup.mk_pow, this]
      rfl
  obtain ⟨ρ, hρ⟩ := exists_injective_GL_of_mulAut hSec2 (glueSecAct S.stab hD) hinj
  have hcard := card_sec_mul (V := Y) (W := U) (U := U ⊓ U') inf_le_left
  have h1 : rk (Sec U (U ⊓ U')) + rk ↥(U ⊓ U') = rk ↥U := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hcard]
  have h2 : rk (Sec U (U ⊓ U')) = rk ↥U - rk ↥(U ⊓ U') := by omega
  rw [← h2]
  exact ⟨ρ, hρ⟩

theorem ubar_le {m : ℕ} (hm : AutRankLe ↥L₀ m) : rk ↥U - rk ↥(U ⊓ U') ≤ 2 * m + 1 := by
  obtain ⟨hs1, -, hB⟩ := S.swap.shape_B S.exp
  have := S.rk_le hm
  omega

end NDSetup

end ND

end CFSG.Quasithin
