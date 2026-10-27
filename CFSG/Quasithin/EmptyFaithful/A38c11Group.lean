module

public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.A38c11

open CFSG.Open
open scoped Pointwise commutatorElement

section Group

variable {G : Type} [Group G]

theorem conj_mem_commutator {U K : Subgroup G} {y : G}
    (hU : y ∈ Subgroup.normalizer (U : Set G)) (hK : y ∈ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ ⁅U, K⁆, y * x * y⁻¹ ∈ ⁅U, K⁆ := by
  intro x hx
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
    have h1 : y * g₁ * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hU g₁).mp hg₁
    have h2 : y * g₂ * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hK g₂).mp hg₂
    have := Subgroup.commutator_mem_commutator h1 h2
    have e : y * ⁅g₁, g₂⁆ * y⁻¹ = ⁅y * g₁ * y⁻¹, y * g₂ * y⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact this
  | one => simp
  | mul x z _ _ ihx ihz =>
    have e : y * (x * z) * y⁻¹ = (y * x * y⁻¹) * (y * z * y⁻¹) := by group
    rw [e]
    exact (⁅U, K⁆).mul_mem ihx ihz
  | inv x _ ih =>
    have e : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    rw [e]
    exact (⁅U, K⁆).inv_mem ih

theorem exists_mul_of_sup {H Kp H' : Subgroup G} (hH'H : H' ≤ Subgroup.normalizer (Kp : Set G))
    (hHeq : H = Kp ⊔ H') : ∀ h ∈ H, ∃ y ∈ Kp, ∃ h' ∈ H', h = y * h' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ y ∈ Kp, ∃ h' ∈ H', x = y * h'}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, h₁, hh₁, rfl⟩ ⟨y₂, hy₂, h₂, hh₂, rfl⟩
        refine ⟨y₁ * (h₁ * y₂ * h₁⁻¹), Kp.mul_mem hy₁ ((Subgroup.mem_normalizer_iff.mp (hH'H hh₁) y₂).mp hy₂),
          h₁ * h₂, H'.mul_mem hh₁ hh₂, ?_⟩
        group
      one_mem' := ⟨1, Kp.one_mem, 1, H'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨y, hy, h, hh, rfl⟩
        refine ⟨h⁻¹ * y⁻¹ * h, ?_, h⁻¹, H'.inv_mem hh, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hH'H (H'.inv_mem hh)) y⁻¹).mp (Kp.inv_mem hy)
        simpa using this }
  have hle : Kp ⊔ H' ≤ P :=
    sup_le (fun y hy => ⟨y, hy, 1, H'.one_mem, by simp⟩) (fun h hh => ⟨1, Kp.one_mem, h, hh, by simp⟩)
  intro h hh
  exact hle (hHeq ▸ hh)

theorem commutator_le_of_invariant {H K Kp H' V W : Subgroup G} (hKpH : Kp ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hprod : ∀ h ∈ H, ∃ y ∈ Kp, ∃ h' ∈ H', h = y * h')
    (hUab : ∀ a ∈ conjClosure V H, ∀ b ∈ conjClosure V H, a * b = b * a)
    (hWU : W ≤ conjClosure V H) (hKpW : Kp ≤ Subgroup.normalizer (W : Set G))
    (hW : ⁅conjClosure V H', K⁆ ≤ W) : ⁅conjClosure V H, K⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    intro k hk
    obtain ⟨h, hh, v, hv, rfl⟩ := hx
    obtain ⟨y, hy, h', hh', rfl⟩ := hprod h hh
    have hu0 : h' * v * h'⁻¹ ∈ conjClosure V H' := mem_conjClosure hh' hv
    have hk' : y⁻¹ * k * y⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHK (hKpH (Kp.inv_mem hy))) k).mp hk
    have hcW : ⁅h' * v * h'⁻¹, y⁻¹ * k * y⁻¹⁻¹⁆ ∈ W :=
      hW (Subgroup.commutator_mem_commutator hu0 hk')
    have e : ⁅y * h' * v * (y * h')⁻¹, k⁆ = y * ⁅h' * v * h'⁻¹, y⁻¹ * k * y⁻¹⁻¹⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hKpW hy) _).mp hcW
    simpa using this
  | one =>
    intro k hk
    simp [commutatorElement_def]
  | mul x z hx hz ihx ihz =>
    intro k hk
    have e : ⁅x * z, k⁆ = x * ⁅z, k⁆ * x⁻¹ * ⁅x, k⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hzk : ⁅z, k⁆ ∈ W := ihz k hk
    have hcomm : x * ⁅z, k⁆ * x⁻¹ = ⁅z, k⁆ := by
      have := hUab x hx ⁅z, k⁆ (hWU hzk)
      rw [this]; group
    rw [hcomm]
    exact W.mul_mem hzk (ihx k hk)
  | inv x hx ih =>
    intro k hk
    have e : ⁅x⁻¹, k⁆ = x⁻¹ * (⁅x, k⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : (⁅x, k⁆)⁻¹ ∈ W := W.inv_mem (ih k hk)
    have h2 : x⁻¹ * (⁅x, k⁆)⁻¹ * x = (⁅x, k⁆)⁻¹ := by
      have := hUab x⁻¹ ((conjClosure V H).inv_mem hx) (⁅x, k⁆)⁻¹ (hWU h1)
      rw [this]; group
    rw [h2]
    exact h1

theorem commutator_eq_bot_of_perfect {H Kp X Z : Subgroup G} (hKpH : Kp ≤ H) (hXH : X ≤ H)
    (hperf : ⁅Kp, Kp⁆ = Kp) (hZc : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z) (hXZ : ⁅X, Kp⁆ ≤ Z) :
    ⁅X, Kp⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  have hg : ∀ a ∈ Kp, ⁅x, a⁆ ∈ Z := fun a ha => hXZ (Subgroup.commutator_mem_commutator hx ha)
  have hgH : ∀ a ∈ Kp, ⁅x, a⁆ ∈ H := fun a ha =>
    H.mul_mem (H.mul_mem (H.mul_mem (hXH hx) (hKpH ha)) (H.inv_mem (hXH hx))) (H.inv_mem (hKpH ha))
  have hmul : ∀ a ∈ Kp, ∀ b ∈ Kp, ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
    intro a ha b hb
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, hZc _ (hg b hb) a (hKpH ha)]
  have hinv : ∀ a ∈ Kp, ⁅x, a⁻¹⁆ = (⁅x, a⁆)⁻¹ := by
    intro a ha
    have h1 := hmul a ha a⁻¹ (Kp.inv_mem ha)
    rw [mul_inv_cancel] at h1
    have h0 : ⁅x, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  let D : Subgroup G :=
    { carrier := {c | c ∈ Kp ∧ ⁅x, c⁆ = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        exact ⟨Kp.mul_mem ha hb, by rw [hmul a ha b hb, ha1, hb1, one_mul]⟩
      one_mem' := ⟨Kp.one_mem, by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        exact ⟨Kp.inv_mem ha, by rw [hinv a ha, ha1, inv_one]⟩ }
  have hD : ⁅Kp, Kp⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hm : a * b * a⁻¹ * b⁻¹ ∈ Kp :=
      Kp.mul_mem (Kp.mul_mem (Kp.mul_mem ha hb) (Kp.inv_mem ha)) (Kp.inv_mem hb)
    refine ⟨by simpa [commutatorElement_def] using hm, ?_⟩
    have e1 := hmul (a * b * a⁻¹) (Kp.mul_mem (Kp.mul_mem ha hb) (Kp.inv_mem ha)) b⁻¹ (Kp.inv_mem hb)
    have e2 := hmul (a * b) (Kp.mul_mem ha hb) a⁻¹ (Kp.inv_mem ha)
    have e3 := hmul a ha b hb
    have hpq : ⁅x, a⁆ * ⁅x, b⁆ = ⁅x, b⁆ * ⁅x, a⁆ :=
      (mul_inv_eq_iff_eq_mul.mp (hZc _ (hg a ha) _ (hgH b hb))).symm
    have : ⁅x, ⁅a, b⁆⁆ = ⁅x, a⁆ * ⁅x, b⁆ * (⁅x, a⁆)⁻¹ * (⁅x, b⁆)⁻¹ := by
      rw [commutatorElement_def a b, e1, e2, e3, hinv a ha, hinv b hb]
    rw [this, hpq]
    group
  have : y ∈ D := by
    have h1 : Kp ≤ D := hperf ▸ hD
    exact h1 hy
  exact this.2

theorem case3_group {H K Kp H' V Z : Subgroup G} (hKH : K ≤ H) (hKpH : Kp ≤ H) (hH'H : H' ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hHKp : H ≤ Subgroup.normalizer (Kp : Set G))
    (hHeq : H = Kp ⊔ H') (hUH : conjClosure V H ≤ H) (hZV : Z ≤ V)
    (hZc : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z)
    (hUab : ∀ a ∈ conjClosure V H, ∀ b ∈ conjClosure V H, a * b = b * a) (hperf : ⁅Kp, Kp⁆ = Kp)
    (hdirect : (⁅conjClosure V H, K⁆ ⊔ Z) ⊓ (⁅conjClosure V H, Kp⁆ ⊔ Z) ≤ Z) :
    ⁅conjClosure V H, K⁆ ⊔ Z = ⁅conjClosure V H', K⁆ ⊔ Z ∧ ⁅⁅conjClosure V H, K⁆, Kp⁆ = ⊥ := by
  have hUN : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  have hU'U : conjClosure V H' ≤ conjClosure V H := conjClosure_mono le_rfl hH'H
  have hZU : Z ≤ conjClosure V H := hZV.trans (le_conjClosure V H)
  have hUKU : ⁅conjClosure V H, K⁆ ≤ conjClosure V H := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have : k * u⁻¹ * k⁻¹ ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff.mp (hUN (hKH hk)) u⁻¹).mp ((conjClosure V H).inv_mem hu)
    have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (conjClosure V H).mul_mem hu this
  have hAU : ⁅conjClosure V H, K⁆ ⊔ Z ≤ conjClosure V H := sup_le hUKU hZU
  have hconjA : ∀ y ∈ H, ∀ a ∈ ⁅conjClosure V H, K⁆ ⊔ Z, y * a * y⁻¹ ∈ ⁅conjClosure V H, K⁆ ⊔ Z := by
    intro y hy a ha
    have hle : ⁅conjClosure V H, K⁆ ⊔ Z ≤
        (⁅conjClosure V H, K⁆ ⊔ Z).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun z hz => ?_)
      · show y * x * y⁻¹ ∈ ⁅conjClosure V H, K⁆ ⊔ Z
        exact Subgroup.mem_sup_left (conj_mem_commutator (hUN hy) (hHK hy) x hx)
      · show y * z * y⁻¹ ∈ ⁅conjClosure V H, K⁆ ⊔ Z
        rw [hZc z hz y hy]
        exact Subgroup.mem_sup_right hz
    exact hle ha
  have hAcomm : ⁅⁅conjClosure V H, K⁆ ⊔ Z, Kp⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    have h1 : ⁅a, y⁆ ∈ ⁅conjClosure V H, K⁆ ⊔ Z := by
      have e : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (⁅conjClosure V H, K⁆ ⊔ Z).mul_mem ha
        (hconjA y (hKpH hy) a⁻¹ ((⁅conjClosure V H, K⁆ ⊔ Z).inv_mem ha))
    have h2 : ⁅a, y⁆ ∈ ⁅conjClosure V H, Kp⁆ ⊔ Z :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (hAU ha) hy)
    exact hdirect ⟨h1, h2⟩
  have hWA : ⁅conjClosure V H', K⁆ ⊔ Z ≤ ⁅conjClosure V H, K⁆ ⊔ Z :=
    sup_le_sup_right (Subgroup.commutator_mono hU'U le_rfl) Z
  have hconjW : ∀ y ∈ Kp, ∀ w ∈ ⁅conjClosure V H', K⁆ ⊔ Z, y * w * y⁻¹ ∈ ⁅conjClosure V H', K⁆ ⊔ Z := by
    intro y hy w hw
    have hc : ⁅w, y⁆ ∈ Z := hAcomm (Subgroup.commutator_mem_commutator (hWA hw) hy)
    have e : y * w * y⁻¹ = (⁅w, y⁆)⁻¹ * w := by simp only [commutatorElement_def]; group
    rw [e]
    exact (⁅conjClosure V H', K⁆ ⊔ Z).mul_mem ((⁅conjClosure V H', K⁆ ⊔ Z).inv_mem
      (Subgroup.mem_sup_right hc)) hw
  have hKpW : Kp ≤ Subgroup.normalizer ((⁅conjClosure V H', K⁆ ⊔ Z : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hconjW y hy w
    · intro hw
      have := hconjW y⁻¹ (Kp.inv_mem hy) _ hw
      simpa [mul_assoc] using this
  have hKL : ⁅conjClosure V H, K⁆ ≤ ⁅conjClosure V H', K⁆ ⊔ Z :=
    commutator_le_of_invariant hKpH hHK (exists_mul_of_sup (hH'H.trans hHKp) hHeq)
      hUab (hWA.trans hAU) hKpW le_sup_left
  refine ⟨le_antisymm (sup_le hKL le_sup_right) hWA, ?_⟩
  exact commutator_eq_bot_of_perfect hKpH (hUKU.trans hUH) hperf hZc
    ((Subgroup.commutator_mono le_sup_left le_rfl).trans hAcomm)

end Group

end CFSG.Quasithin.A38c11
