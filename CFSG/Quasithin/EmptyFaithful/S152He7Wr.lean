module

public import CFSG.Quasithin.EmptyFaithful.S152He6CaseB
public import CFSG.Quasithin.EmptyFaithful.S152He5Defs
public import CFSG.Quasithin.Background.I4Recognition

public section

namespace CFSG.Quasithin.He7

open CFSG.Quasithin CFSG.Quasithin.He6
open scoped commutatorElement

section Prod

variable {Ω : Type*} [Group Ω]

theorem eq_of_mul_eq_mul {A A' : Subgroup Ω} (hinf : A ⊓ A' = ⊥) {a a₁ b b₁ : Ω} (ha : a ∈ A)
    (ha₁ : a₁ ∈ A) (hb : b ∈ A') (hb₁ : b₁ ∈ A') (h : a * b = a₁ * b₁) : a = a₁ ∧ b = b₁ := by
  have h1 : a₁⁻¹ * a = b₁ * b⁻¹ := by
    calc a₁⁻¹ * a = a₁⁻¹ * (a * b) * b⁻¹ := by group
      _ = a₁⁻¹ * (a₁ * b₁) * b⁻¹ := by rw [h]
      _ = b₁ * b⁻¹ := by group
  have hmem : a₁⁻¹ * a ∈ A ⊓ A' :=
    ⟨A.mul_mem (A.inv_mem ha₁) ha, by rw [h1]; exact A'.mul_mem hb₁ (A'.inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  refine ⟨(inv_mul_eq_one.1 hmem).symm, ?_⟩
  rw [hmem] at h1
  exact (mul_inv_eq_one.1 h1.symm).symm

end Prod

section Wr

variable {W : Type} [CommGroup W]

@[expose] def sw (τ' : MulAut W) (q : Multiplicative (ZMod 2)) : MulAut W := if q = 1 then 1 else τ'

abbrev g2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem hQ (q : Multiplicative (ZMod 2)) : q = 1 ∨ q = g2 := by
  revert q
  decide

theorem hgg : g2 * g2 = 1 := by decide

theorem hg1 : g2 ≠ 1 := by decide

theorem hginv : g2⁻¹ = g2 := by decide

theorem sw_one (τ' : MulAut W) : sw τ' 1 = 1 := by simp [sw]

theorem sw_g (τ' : MulAut W) : sw τ' g2 = τ' := by
  simp [sw]

theorem sw_mul {τ' : MulAut W} (h2 : τ' * τ' = 1) (q q' : Multiplicative (ZMod 2)) :
    sw τ' (q * q') = sw τ' q * sw τ' q' := by
  rcases hQ q with rfl | rfl <;> rcases hQ q' with rfl | rfl
  · simp [sw_one]
  · simp [sw_one]
  · simp [sw_one]
  · rw [hgg, sw_one, sw_g, h2]

end Wr

section Main

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem wreath_of_noOuter (P : PairData W) {Tb : Subgroup (MulAut W)} {τ : MulAut W}
    (hAX : P.A ≤ P.Xb) (hA'X : P.A' ≤ P.Xb) (hTX : Tb ≤ P.Xb) (hT2 : IsPGroup 2 Tb)
    (hXKT : ∀ x ∈ P.Xb, ∃ k ∈ P.A ⊔ P.A', ∃ s ∈ Tb, x = k * s)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ P.Xb → (Q.subgroupOf P.Xb).Normal → IsPGroup 2 Q →
      Q = ⊥)
    (hτ : τ ∈ Tb) (hτA : ∀ x, x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A')
    (hτA' : ∀ x, x ∈ P.A' ↔ τ * x * τ⁻¹ ∈ P.A) (hA7 : IsL2Prime 7 ↥P.A)
    (hno : ∀ g ∈ P.Xb, (∀ x, x ∈ P.A ↔ g * x * g⁻¹ ∈ P.A) →
      ∃ l ∈ P.A, ∀ x ∈ P.A, g * x * g⁻¹ = l * x * l⁻¹) :
    Nonempty (↥P.Xb ≃* L32WrZ2) := by
  classical
  have hinf := P.inf_eq_bot
  have hτX : τ ∈ P.Xb := hTX hτ
  have hnK : ∀ x ∈ P.Xb, ∀ k ∈ P.A ⊔ P.A', x * k * x⁻¹ ∈ P.A ⊔ P.A' := fun x hx k hk =>
    P.sup_normal hx hk
  have hcentK : ∀ x ∈ P.Xb, (∀ k ∈ P.A ⊔ P.A', x * k = k * x) → x = 1 :=
    eq_one_of_commute_of_two_pow152 hO2 hnK
      (fun x hx => by
        obtain ⟨k, hk, s, hs, hxs⟩ := hXKT x hx
        exact PairData.exists_two_pow_mem (fun s hs k hk => hnK s (hTX hs) k hk) hT2 hk hs hxs)
      (fun k hk hc => P.central_eq_one hk hc)
  have hAne : P.A ≠ ⊥ := ne_bot_of_simple P.simpA
  have hno' : ∀ g ∈ P.Xb, (∀ x, x ∈ P.A' ↔ g * x * g⁻¹ ∈ P.A') →
      ∃ l ∈ P.A', ∀ x ∈ P.A', g * x * g⁻¹ = l * x * l⁻¹ := by
    intro g hg hgA'
    have hg'X : τ⁻¹ * g * τ ∈ P.Xb :=
      P.Xb.mul_mem (P.Xb.mul_mem (P.Xb.inv_mem hτX) hg) hτX
    have hg'A : ∀ x, x ∈ P.A ↔ (τ⁻¹ * g * τ) * x * (τ⁻¹ * g * τ)⁻¹ ∈ P.A := by
      intro x
      have e : g * (τ * x * τ⁻¹) * g⁻¹ = τ * ((τ⁻¹ * g * τ) * x * (τ⁻¹ * g * τ)⁻¹) * τ⁻¹ := by
        group
      calc x ∈ P.A ↔ τ * x * τ⁻¹ ∈ P.A' := hτA x
        _ ↔ g * (τ * x * τ⁻¹) * g⁻¹ ∈ P.A' := hgA' _
        _ ↔ (τ⁻¹ * g * τ) * x * (τ⁻¹ * g * τ)⁻¹ ∈ P.A := by rw [e]; exact (hτA _).symm
    obtain ⟨l, hl, hlg⟩ := hno _ hg'X hg'A
    refine ⟨τ * l * τ⁻¹, (hτA l).1 hl, fun y hy => ?_⟩
    have hy' : τ⁻¹ * y * τ ∈ P.A := by
      rw [hτA]
      rw [show τ * (τ⁻¹ * y * τ) * τ⁻¹ = y by group]
      exact hy
    have := hlg _ hy'
    calc g * y * g⁻¹ = τ * ((τ⁻¹ * g * τ) * (τ⁻¹ * y * τ) * (τ⁻¹ * g * τ)⁻¹) * τ⁻¹ := by group
      _ = τ * (l * (τ⁻¹ * y * τ) * l⁻¹) * τ⁻¹ := by rw [this]
      _ = (τ * l * τ⁻¹) * y * (τ * l * τ⁻¹)⁻¹ := by group
  have hC : ∀ c ∈ P.Xb, (∀ x ∈ P.A, c * x = x * c) → c ∈ P.A' := by
    intro c hc hcA
    rcases P.norm c hc with ⟨-, h2⟩ | ⟨h1, -⟩
    · obtain ⟨l', hl', hl'c⟩ := hno' c hc h2
      have hl'X : l' ∈ P.Xb := hA'X hl'
      have hc1 : l'⁻¹ * c = 1 := by
        refine hcentK _ (P.Xb.mul_mem (P.Xb.inv_mem hl'X) hc) ?_
        intro k hk
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute P.comm hk
        have h_cx : c * x = x * c := hcA x hx
        have h_cy : c * y = l' * y * l'⁻¹ * c := by
          have := hl'c y hy
          calc c * y = (c * y * c⁻¹) * c := by group
            _ = l' * y * l'⁻¹ * c := by rw [this]
        have h_lx : l'⁻¹ * x = x * l'⁻¹ := (P.comm x hx l'⁻¹ (P.A'.inv_mem hl')).symm
        calc l'⁻¹ * c * (x * y) = l'⁻¹ * (c * x) * y := by group
          _ = (l'⁻¹ * x) * (c * y) := by rw [h_cx]; group
          _ = (x * l'⁻¹) * (l' * y * l'⁻¹ * c) := by rw [h_lx, h_cy]
          _ = x * y * (l'⁻¹ * c) := by group
      have : l' = c := inv_mul_eq_one.1 hc1
      rw [← this]
      exact hl'
    · exfalso
      apply hAne
      rw [eq_bot_iff]
      intro x hx
      have h3 : x ∈ P.A ⊓ P.A' := by
        refine ⟨hx, ?_⟩
        have := (h1 x).1 hx
        rwa [show c * x * c⁻¹ = x by rw [hcA x hx]; group] at this
      rwa [hinf] at h3
  have hN : ∀ g ∈ P.Xb, (∀ x, x ∈ P.A ↔ g * x * g⁻¹ ∈ P.A) →
      ∃ l ∈ P.A, ∃ l' ∈ P.A', g = l * l' := by
    intro g hg hgA
    obtain ⟨l, hl, hlg⟩ := hno g hg hgA
    refine ⟨l, hl, l⁻¹ * g, hC (l⁻¹ * g) (P.Xb.mul_mem (P.Xb.inv_mem (hAX hl)) hg) ?_, by group⟩
    intro x hx
    have := hlg x hx
    calc l⁻¹ * g * x = l⁻¹ * (g * x * g⁻¹) * g := by group
      _ = l⁻¹ * (l * x * l⁻¹) * g := by rw [this]
      _ = x * (l⁻¹ * g) := by group
  have hτ2 : ∀ x, x ∈ P.A ↔ (τ * τ) * x * (τ * τ)⁻¹ ∈ P.A := by
    intro x
    have e : (τ * τ) * x * (τ * τ)⁻¹ = τ * (τ * x * τ⁻¹) * τ⁻¹ := by group
    rw [e]
    constructor
    · intro hx
      exact (hτA' _).1 ((hτA x).1 hx)
    · intro h
      exact (hτA x).2 ((hτA' _).2 h)
  obtain ⟨u, hu, v, hv, huv⟩ := hN (τ * τ) (P.Xb.mul_mem hτX hτX) hτ2
  obtain ⟨hτv, hτu⟩ : τ * v * τ⁻¹ = u ∧ τ * u * τ⁻¹ = v := by
    have h1 : τ * (u * v) * τ⁻¹ = u * v := by
      rw [← huv]
      group
    have h2 : (τ * v * τ⁻¹) * (τ * u * τ⁻¹) = u * v := by
      calc (τ * v * τ⁻¹) * (τ * u * τ⁻¹) = τ * (v * u) * τ⁻¹ := by group
        _ = τ * (u * v) * τ⁻¹ := by rw [P.comm u hu v hv]
        _ = u * v := h1
    exact eq_of_mul_eq_mul hinf ((hτA' v).1 hv) hu ((hτA u).1 hu) hv h2
  obtain ⟨τ', hτ'⟩ : ∃ τ' : MulAut W, τ' = τ * u⁻¹ := ⟨_, rfl⟩
  have hτ'2 : τ' * τ' = 1 := by
    have e1 : τ * u⁻¹ * τ⁻¹ = v⁻¹ := by
      rw [← hτu]
      group
    calc τ' * τ' = (τ * u⁻¹ * τ⁻¹) * (τ * τ) * u⁻¹ := by rw [hτ']; group
      _ = v⁻¹ * (u * v) * u⁻¹ := by rw [e1, huv]
      _ = v⁻¹ * (v * u) * u⁻¹ := by rw [P.comm u hu v hv]
      _ = 1 := by group
  have hτ'inv : τ'⁻¹ = τ' := inv_eq_of_mul_eq_one_right hτ'2
  have hτ'X : τ' ∈ P.Xb := by
    rw [hτ']
    exact P.Xb.mul_mem hτX (P.Xb.inv_mem (hAX hu))
  have hτ'A : ∀ x, x ∈ P.A ↔ τ' * x * τ'⁻¹ ∈ P.A' := by
    intro x
    have e : τ' * x * τ'⁻¹ = τ * (u⁻¹ * x * u) * τ⁻¹ := by rw [hτ']; group
    rw [e, ← hτA]
    constructor
    · intro hx
      exact P.A.mul_mem (P.A.mul_mem (P.A.inv_mem hu) hx) hu
    · intro h
      have := P.A.mul_mem (P.A.mul_mem hu h) (P.A.inv_mem hu)
      rwa [show u * (u⁻¹ * x * u) * u⁻¹ = x by group] at this
  have hτ'A' : ∀ x, x ∈ P.A' ↔ τ' * x * τ'⁻¹ ∈ P.A := by
    intro x
    have e : τ' * x * τ'⁻¹ = τ * (u⁻¹ * x * u) * τ⁻¹ := by rw [hτ']; group
    rw [e, ← hτA']
    constructor
    · intro hx
      have : u⁻¹ * x * u = x := by
        calc u⁻¹ * x * u = u⁻¹ * (x * u) := by group
          _ = u⁻¹ * (u * x) := by rw [P.comm u hu x hx]
          _ = x := by group
      rw [this]
      exact hx
    · intro h
      have : x = u⁻¹ * x * u := by
        calc x = u * (u⁻¹ * x * u) * u⁻¹ := by group
          _ = (u⁻¹ * x * u) * u * u⁻¹ := by rw [P.comm u hu _ h]
          _ = u⁻¹ * x * u := by group
      rw [this]
      exact h
  obtain ⟨e32⟩ := CFSG.Quasithin.I4.nonempty_psl3_two_equiv_psl2_seven
  obtain ⟨e7⟩ := hA7
  let eA : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥P.A := e32.trans e7.symm
  let ι₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) →* MulAut W :=
    P.A.subtype.comp eA.toMonoidHom
  let ι₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) →* MulAut W :=
    (MulAut.conj τ').toMonoidHom.comp ι₁
  have hι₁A : ∀ d, ι₁ d ∈ P.A := fun d => (eA d).2
  have hι₂def : ∀ d, ι₂ d = τ' * ι₁ d * τ'⁻¹ := fun d => rfl
  have hι₂A' : ∀ d, ι₂ d ∈ P.A' := fun d => by
    rw [hι₂def]
    exact (hτ'A _).1 (hι₁A d)
  have hι₁inj : Function.Injective ι₁ := P.A.subtype_injective.comp eA.injective
  have hι₂inj : Function.Injective ι₂ := (MulAut.conj τ').injective.comp hι₁inj
  have hc1 : ∀ d, τ' * ι₁ d = ι₂ d * τ' := fun d => by rw [hι₂def]; group
  have hc2 : ∀ d, τ' * ι₂ d = ι₁ d * τ' := fun d => by
    rw [hι₂def, show τ' * (τ' * ι₁ d * τ'⁻¹) = (τ' * τ') * ι₁ d * τ'⁻¹ by group, hτ'2, one_mul, hτ'inv]
  have hc3 : ∀ d d', ι₁ d * ι₂ d' = ι₂ d' * ι₁ d := fun d d' => P.comm _ (hι₁A d) _ (hι₂A' d')
  have hcomm2 : ∀ d d₁ d₂, ι₁ d * (ι₂ d₁ * ι₂ d₂) = (ι₂ d₁ * ι₂ d₂) * ι₁ d := fun d d₁ d₂ => by
    calc ι₁ d * (ι₂ d₁ * ι₂ d₂) = (ι₁ d * ι₂ d₁) * ι₂ d₂ := by group
      _ = (ι₂ d₁ * ι₁ d) * ι₂ d₂ := by rw [hc3]
      _ = ι₂ d₁ * (ι₁ d * ι₂ d₂) := by group
      _ = ι₂ d₁ * (ι₂ d₂ * ι₁ d) := by rw [hc3]
      _ = (ι₂ d₁ * ι₂ d₂) * ι₁ d := by group
  let Φ : L32WrZ2 → MulAut W := fun w => ι₁ (w.left 1) * ι₂ (w.left g2) * sw τ' w.right
  have hΦmul : ∀ w w' : L32WrZ2, Φ (w * w') = Φ w * Φ w' := by
    intro w w'
    obtain ⟨f, q⟩ := w
    obtain ⟨f', q'⟩ := w'
    show ι₁ ((f * fun x => f' (q⁻¹ * x)) 1) * ι₂ ((f * fun x => f' (q⁻¹ * x)) g2) *
        sw τ' (q * q') =
      ι₁ (f 1) * ι₂ (f g2) * sw τ' q * (ι₁ (f' 1) * ι₂ (f' g2) * sw τ' q')
    rcases hQ q with rfl | rfl
    · simp only [Pi.mul_apply, one_mul, map_mul, sw_one, mul_one]
      calc ι₁ (f 1) * ι₁ (f' 1) * (ι₂ (f g2) * ι₂ (f' g2)) * sw τ' q'
          = ι₁ (f 1) * (ι₁ (f' 1) * ι₂ (f g2)) * ι₂ (f' g2) * sw τ' q' := by group
        _ = ι₁ (f 1) * (ι₂ (f g2) * ι₁ (f' 1)) * ι₂ (f' g2) * sw τ' q' := by rw [hc3]
        _ = ι₁ (f 1) * ι₂ (f g2) * (ι₁ (f' 1) * ι₂ (f' g2) * sw τ' q') := by group
    · simp only [Pi.mul_apply, hginv, mul_one, map_mul, sw_mul hτ'2, sw_g]
      calc ι₁ (f 1) * ι₁ (f' g2) * (ι₂ (f g2) * ι₂ (f' 1)) * (τ' * sw τ' q')
          = ι₁ (f 1) * (ι₁ (f' g2) * (ι₂ (f g2) * ι₂ (f' 1))) * (τ' * sw τ' q') := by group
        _ = ι₁ (f 1) * ((ι₂ (f g2) * ι₂ (f' 1)) * ι₁ (f' g2)) * (τ' * sw τ' q') := by
            rw [hcomm2]
        _ = ι₁ (f 1) * ι₂ (f g2) * ι₂ (f' 1) * (ι₁ (f' g2) * τ') * sw τ' q' := by group
        _ = ι₁ (f 1) * ι₂ (f g2) * ι₂ (f' 1) * (τ' * ι₂ (f' g2)) * sw τ' q' := by rw [hc2]
        _ = ι₁ (f 1) * ι₂ (f g2) * (ι₂ (f' 1) * τ') * ι₂ (f' g2) * sw τ' q' := by group
        _ = ι₁ (f 1) * ι₂ (f g2) * (τ' * ι₁ (f' 1)) * ι₂ (f' g2) * sw τ' q' := by rw [hc1]
        _ = ι₁ (f 1) * ι₂ (f g2) * τ' * (ι₁ (f' 1) * ι₂ (f' g2) * sw τ' q') := by group
  have hΦX : ∀ w : L32WrZ2, Φ w ∈ P.Xb := by
    intro w
    refine P.Xb.mul_mem (P.Xb.mul_mem (hAX (hι₁A _)) (hA'X (hι₂A' _))) ?_
    show sw τ' w.right ∈ P.Xb
    rcases hQ w.right with h | h <;> rw [h]
    · rw [sw_one]
      exact P.Xb.one_mem
    · rw [sw_g]
      exact hτ'X
  let Ψ : L32WrZ2 →* ↥P.Xb :=
    MonoidHom.mk' (fun w => ⟨Φ w, hΦX w⟩) (fun w w' => Subtype.ext (hΦmul w w'))
  have hΨ : ∀ w, ((Ψ w : ↥P.Xb) : MulAut W) = Φ w := fun w => rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : Φ w = 1 := by rw [← hΨ, hw]; rfl
    obtain ⟨f, q⟩ := w
    have h1' : ι₁ (f 1) * ι₂ (f g2) * sw τ' q = 1 := h1
    rcases hQ q with rfl | rfl
    · rw [sw_one, mul_one] at h1'
      obtain ⟨ha, hb⟩ := eq_of_mul_eq_mul hinf (hι₁A (f 1)) P.A.one_mem (hι₂A' (f g2))
        P.A'.one_mem (by rw [h1', mul_one])
      have hf1 : f 1 = 1 := hι₁inj (by rw [ha, map_one])
      have hfg : f g2 = 1 := hι₂inj (by rw [hb, map_one])
      have hf : f = 1 := by
        funext x
        rcases hQ x with rfl | rfl
        · exact hf1
        · exact hfg
      subst hf
      rfl
    · exfalso
      rw [sw_g] at h1'
      obtain ⟨x, hxA, hx1⟩ := (Subgroup.bot_or_exists_ne_one P.A).resolve_left hAne
      have hτ'eq : τ' = (ι₁ (f 1) * ι₂ (f g2))⁻¹ := eq_inv_of_mul_eq_one_right h1'
      have hax : (ι₁ (f 1))⁻¹ * x * ι₁ (f 1) ∈ P.A :=
        P.A.mul_mem (P.A.mul_mem (P.A.inv_mem (hι₁A _)) hxA) (hι₁A _)
      have hconj : τ' * x * τ'⁻¹ = (ι₁ (f 1))⁻¹ * x * ι₁ (f 1) := by
        have hb : (ι₂ (f g2))⁻¹ * ((ι₁ (f 1))⁻¹ * x * ι₁ (f 1)) * ι₂ (f g2) =
            (ι₁ (f 1))⁻¹ * x * ι₁ (f 1) := by
          calc (ι₂ (f g2))⁻¹ * ((ι₁ (f 1))⁻¹ * x * ι₁ (f 1)) * ι₂ (f g2)
              = (ι₂ (f g2))⁻¹ * (((ι₁ (f 1))⁻¹ * x * ι₁ (f 1)) * ι₂ (f g2)) := by group
            _ = (ι₂ (f g2))⁻¹ * (ι₂ (f g2) * ((ι₁ (f 1))⁻¹ * x * ι₁ (f 1))) := by
                rw [P.comm _ hax _ (hι₂A' _)]
            _ = (ι₁ (f 1))⁻¹ * x * ι₁ (f 1) := by group
        rw [hτ'eq]
        rw [← hb]
        group
      have hmem : (ι₁ (f 1))⁻¹ * x * ι₁ (f 1) ∈ P.A ⊓ P.A' := ⟨hax, by
        rw [← hconj]
        exact (hτ'A x).1 hxA⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      apply hx1
      calc x = ι₁ (f 1) * ((ι₁ (f 1))⁻¹ * x * ι₁ (f 1)) * (ι₁ (f 1))⁻¹ := by group
        _ = 1 := by rw [hmem]; group
  have hbuild : ∀ l ∈ P.A, ∀ l' ∈ P.A', ∃ f : Multiplicative (ZMod 2) →
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2), ι₁ (f 1) = l ∧ ι₂ (f g2) = l' := by
    intro l hl l' hl'
    have hz : τ'⁻¹ * l' * τ' ∈ P.A := by
      rw [hτ'A, show τ' * (τ'⁻¹ * l' * τ') * τ'⁻¹ = l' by group]
      exact hl'
    refine ⟨fun q => if q = 1 then eA.symm ⟨l, hl⟩ else eA.symm ⟨τ'⁻¹ * l' * τ', hz⟩, ?_, ?_⟩
    · simp only [ite_true]
      show ((eA (eA.symm ⟨l, hl⟩) : ↥P.A) : MulAut W) = l
      rw [MulEquiv.apply_symm_apply]
    · simp only [hg1, ite_false]
      show τ' * ((eA (eA.symm ⟨τ'⁻¹ * l' * τ', hz⟩) : ↥P.A) : MulAut W) * τ'⁻¹ = l'
      rw [MulEquiv.apply_symm_apply]
      show τ' * (τ'⁻¹ * l' * τ') * τ'⁻¹ = l'
      group
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨x, hx⟩
    rcases P.norm x hx with ⟨h1, -⟩ | ⟨-, h2⟩
    · obtain ⟨l, hl, l', hl', hxll⟩ := hN x hx h1
      obtain ⟨f, hf1, hf2⟩ := hbuild l hl l' hl'
      refine ⟨⟨f, 1⟩, Subtype.ext ?_⟩
      show ι₁ (f 1) * ι₂ (f g2) * sw τ' 1 = x
      rw [hf1, hf2, sw_one, mul_one, hxll]
    ·
      have hy : ∀ z, z ∈ P.A ↔ (x * τ') * z * (x * τ')⁻¹ ∈ P.A := by
        intro z
        have e : (x * τ') * z * (x * τ')⁻¹ = x * (τ' * z * τ'⁻¹) * x⁻¹ := by group
        rw [e]
        exact (hτ'A z).trans (h2 _)
      obtain ⟨l, hl, l', hl', hxll⟩ := hN (x * τ') (P.Xb.mul_mem hx hτ'X) hy
      obtain ⟨f, hf1, hf2⟩ := hbuild l hl l' hl'
      refine ⟨⟨f, g2⟩, Subtype.ext ?_⟩
      show ι₁ (f 1) * ι₂ (f g2) * sw τ' g2 = x
      rw [hf1, hf2, sw_g, ← hxll]
      calc x * τ' * τ' = x * (τ' * τ') := by group
        _ = x := by rw [hτ'2, mul_one]
  exact ⟨(MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm⟩

end Main

end CFSG.Quasithin.He7
