module

public import CFSG.Monster.GMS.CoTwoAutSetup
public import CFSG.Monster.GMS.CoTwoAutNorm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

namespace CoTwoAutSetup

variable {G : Type} [Group G] {t x : G}

theorem AutOn.mem_Rsub
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) {Ψ : G → G}
    (hΨ : AutOn (Xsub x t) Ψ) (hΨt : Ψ t = t) {r : G} (hr : r ∈ Rsub x t) : Ψ r ∈ Rsub x t := by
  let N : Subgroup Co1 :=
    { carrier := {k | ∃ r ∈ Rsub x t, k = phiG L (Ψ r)}
      mul_mem' := by
        rintro _ _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, rfl⟩
        refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, ?_⟩
        rw [hΨ.mul r₁ (Rsub_le_Xsub L hr₁) r₂ (Rsub_le_Xsub L hr₂),
          phiG_mul L (Xsub_le_C (hΨ.mem _ (Rsub_le_Xsub L hr₁)))
            (Xsub_le_C (hΨ.mem _ (Rsub_le_Xsub L hr₂)))]
      one_mem' := ⟨1, one_mem _, by rw [hΨ.map_one', phiG_one]⟩
      inv_mem' := by
        rintro _ ⟨r, hr, rfl⟩
        refine ⟨r⁻¹, inv_mem hr, ?_⟩
        rw [hΨ.map_inv' (Rsub_le_Xsub L hr),
          phiG_inv L (Xsub_le_C (hΨ.mem _ (Rsub_le_Xsub L hr)))] }
  have hle : N ≤ co1Stab (L.vec x) := by
    rintro _ ⟨r, hr, rfl⟩
    exact phiG_mem_stab L hx (hΨ.mem _ (Rsub_le_Xsub L hr))
  have hnorm : ∀ h ∈ co1Stab (L.vec x), ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    rintro h hh _ ⟨r, hr, rfl⟩
    obtain ⟨c, hcX, rfl⟩ := exists_lift L hx hh
    obtain ⟨c', hc'X, hc'⟩ := hΨ.surj c hcX
    refine ⟨c' * r * c'⁻¹, conj_mem_Rsub L hc'X hr, ?_⟩
    have hcC := Xsub_le_C hcX
    have hΨrC := Xsub_le_C (hΨ.mem _ (Rsub_le_Xsub L hr))
    rw [hΨ.map_conj hc'X (Rsub_le_Xsub L hr), hc', phiG_mul L (mul_mem hcC hΨrC) (inv_mem hcC),
      phiG_mul L hcC hΨrC, phiG_inv L hcC]
  have hp : IsPGroup 2 N := by
    intro k
    refine ⟨1, ?_⟩
    obtain ⟨r, hr, hk⟩ := k.2
    have hsq : Ψ (r * r) = 1 ∨ Ψ (r * r) = t := by
      rcases L.extraspecial.sq r hr.1 with h | h
      · left
        rw [h, hΨ.map_one']
      · right
        rw [h, hΨt]
    have hrC := Xsub_le_C (hΨ.mem _ (Rsub_le_Xsub L hr))
    have hkk : phiG L (Ψ r) * phiG L (Ψ r) = 1 := by
      rw [← phiG_mul L hrC hrC, ← hΨ.mul r (Rsub_le_Xsub L hr) r (Rsub_le_Xsub L hr)]
      rcases hsq with h | h
      · rw [h, phiG_one]
      · rw [h]
        exact phiG_eq_one_of_mem L L.z_mem
    apply Subtype.ext
    show (k : Co1) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two, hk]
    exact hkk
  have hbot := co2StabFacts (L.vec x) hx.2 (co1Stab (L.vec x)) le_rfl (by omega) N hle hnorm hp
  have h1 : phiG L (Ψ r) ∈ N := ⟨r, hr, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have hΨrX := hΨ.mem r (Rsub_le_Xsub L hr)
  exact ⟨(phiG_eq_one_iff L (Xsub_le_C hΨrX)).1 h1, hΨrX.1⟩

open scoped Classical in
@[expose] noncomputable def fOf (L : LeechSystem t) (x : G) (Ψ : G → G)
    (w : Fin 24 → ZMod 2) : Fin 24 → ZMod 2 :=
  if h : ∃ r ∈ Rsub x t, L.vec r = w then L.vec (Ψ h.choose) else 0

theorem fOf_vec (L : LeechSystem t) (hx : x ∈ leechQ t) {Ψ : G → G} (hΨ : AutOn (Xsub x t) Ψ)
    (hΨt : Ψ t = t) (hR : ∀ r ∈ Rsub x t, Ψ r ∈ Rsub x t) {r : G} (hr : r ∈ Rsub x t) :
    fOf L x Ψ (L.vec r) = L.vec (Ψ r) := by
  have h : ∃ r' ∈ Rsub x t, L.vec r' = L.vec r := ⟨r, hr, rfl⟩
  have hf : fOf L x Ψ (L.vec r) = L.vec (Ψ h.choose) := by
    unfold fOf
    simp [h]
  rw [hf]
  obtain ⟨hr', hv'⟩ := h.choose_spec
  rcases L.eq_or_eq_mul_z hr'.1 hr.1 hv' with e | e
  · rw [e]
  · rw [e, hΨ.mul _ (Rsub_le_Xsub L hr) t (Rsub_le_Xsub L (t_mem_Rsub L hx)), hΨt]
    exact L.vec_mul_z (hR r hr).1

theorem exists_inner_correction
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0)
    (hnorm : Co2NormalizerFact) {Ψ : G → G} (hΨ : AutOn (Xsub x t) Ψ) (hΨx : Ψ x = x)
    (hΨt : Ψ t = t) :
    ∃ c ∈ Xsub x t, ∀ r ∈ Rsub x t,
      L.vec (c⁻¹ * Ψ r * c) + L.vec r = 0 ∨ L.vec (c⁻¹ * Ψ r * c) + L.vec r = L.vec x := by
  have hR := fun r (hr : r ∈ Rsub x t) => AutOn.mem_Rsub L hx hΨ hΨt hr
  have hxR := x_mem_Rsub (t := t) hx.1
  have htR := t_mem_Rsub L hx.1
  set f := fOf L x Ψ with hf
  have hfv : ∀ r ∈ Rsub x t, f (L.vec r) = L.vec (Ψ r) := fun r hr =>
    fOf_vec L hx.1 hΨ hΨt hR hr
  have hadd : ∀ a b, bil₀ a (L.vec x) = 0 → bil₀ b (L.vec x) = 0 → f (a + b) = f a + f b := by
    intro a b ha hb
    obtain ⟨r, hr, rfl⟩ := exists_mem_Rsub_vec L hx.1 ha
    obtain ⟨s, hs, rfl⟩ := exists_mem_Rsub_vec L hx.1 hb
    rw [← vec_mul_Rsub L hr hs, hfv _ (mul_mem hr hs), hfv r hr, hfv s hs,
      hΨ.mul r (Rsub_le_Xsub L hr) s (Rsub_le_Xsub L hs), vec_mul_Rsub L (hR r hr) (hR s hs)]
  have hperp : ∀ w, bil₀ w (L.vec x) = 0 → bil₀ (f w) (L.vec x) = 0 := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := exists_mem_Rsub_vec L hx.1 hw
    rw [hfv r hr]
    exact vec_perp_of_mem_Rsub L hx.1 (hR r hr)
  have hinj : ∀ a b, bil₀ a (L.vec x) = 0 → bil₀ b (L.vec x) = 0 → f a = f b → a = b := by
    intro a b ha hb hab
    obtain ⟨r, hr, rfl⟩ := exists_mem_Rsub_vec L hx.1 ha
    obtain ⟨s, hs, rfl⟩ := exists_mem_Rsub_vec L hx.1 hb
    rw [hfv r hr, hfv s hs] at hab
    rcases L.eq_or_eq_mul_z (hR r hr).1 (hR s hs).1 hab with e | e
    · rw [hΨ.inj r (Rsub_le_Xsub L hr) s (Rsub_le_Xsub L hs) e]
    · have e' : Ψ r = Ψ (s * t) := by
        rw [hΨ.mul s (Rsub_le_Xsub L hs) t (Rsub_le_Xsub L htR), hΨt]
        exact e
      rw [hΨ.inj r (Rsub_le_Xsub L hr) (s * t) (Rsub_le_Xsub L (mul_mem hs htR)) e']
      exact L.vec_mul_z hs.1
  have hfx : f (L.vec x) = L.vec x := by
    rw [hfv x hxR, hΨx]
  have hf1 : ∀ g ∈ co1Stab (L.vec x), ∃ h ∈ co1Stab (L.vec x),
      ∀ w, bil₀ w (L.vec x) = 0 → f (co1Act g w) = co1Act h (f w) := by
    intro g hg
    obtain ⟨c, hcX, rfl⟩ := exists_lift L hx hg
    refine ⟨phiG L (Ψ c), phiG_mem_stab L hx (hΨ.mem c hcX), fun w hw => ?_⟩
    obtain ⟨r, hr, rfl⟩ := exists_mem_Rsub_vec L hx.1 hw
    have hcr := conj_mem_Rsub L hcX hr
    rw [← vec_conj_phiG L (Xsub_le_C hcX) hr.1, hfv _ hcr, hfv r hr,
      hΨ.map_conj hcX (Rsub_le_Xsub L hr),
      vec_conj_phiG L (Xsub_le_C (hΨ.mem c hcX)) (hR r hr).1]
  have hf2 : ∀ h ∈ co1Stab (L.vec x), ∃ g ∈ co1Stab (L.vec x),
      ∀ w, bil₀ w (L.vec x) = 0 → f (co1Act g w) = co1Act h (f w) := by
    intro h hh
    obtain ⟨c', hc'X, rfl⟩ := exists_lift L hx hh
    obtain ⟨c, hcX, hc⟩ := hΨ.surj c' hc'X
    refine ⟨phiG L c, phiG_mem_stab L hx hcX, fun w hw => ?_⟩
    obtain ⟨r, hr, rfl⟩ := exists_mem_Rsub_vec L hx.1 hw
    have hcr := conj_mem_Rsub L hcX hr
    rw [← vec_conj_phiG L (Xsub_le_C hcX) hr.1, hfv _ hcr, hfv r hr,
      hΨ.map_conj hcX (Rsub_le_Xsub L hr), hc,
      vec_conj_phiG L (Xsub_le_C hc'X) (hR r hr).1]
  obtain ⟨h, hh, hmain⟩ := hnorm (L.vec x) hx.2 f hadd hperp hinj hfx hf1 hf2
  obtain ⟨c, hcX, rfl⟩ := exists_lift L hx hh
  refine ⟨c, hcX, fun r hr => ?_⟩
  have hcC := Xsub_le_C hcX
  have hw := vec_perp_of_mem_Rsub L hx.1 hr
  have h1 := hmain (L.vec r) hw
  rw [hfv r hr] at h1
  have h2 := CoTwoAutKer.smul01 (inv_mem hh) h1
  rw [map_add, CoTwoModule.co1Act_inv_apply] at h2
  have e : L.vec (c⁻¹ * Ψ r * c) = co1Act (phiG L c)⁻¹ (L.vec (Ψ r)) := by
    have := vec_conj_phiG L (inv_mem hcC) (hR r hr).1
    rw [phiG_inv L hcC, inv_inv] at this
    exact this
  rw [e]
  exact h2

end CoTwoAutSetup

end CFSG.Monster.GMS
