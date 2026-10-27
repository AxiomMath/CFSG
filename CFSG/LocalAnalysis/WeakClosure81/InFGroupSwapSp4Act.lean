module

public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Off
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Map
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.L436

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem map_sp4C_of_map_eq {x : Q} {P : Subgroup Q}
    (hx0 : P₀.map (MulAut.conj x).toMonoidHom = P) :
    (sp4C P₀ (pCoreOf 2 (perfectCore P₀))).map (MulAut.conj x).toMonoidHom =
      sp4C P (pCoreOf 2 (perfectCore P)) := by
  have hperf : (perfectCore P₀).map (MulAut.conj x).toMonoidHom = perfectCore P := by
    rw [map_perfectCore, hx0]
  have hpco : (pCoreOf 2 (perfectCore P₀)).map (MulAut.conj x).toMonoidHom =
      pCoreOf 2 (perfectCore P) := by
    rw [← hperf]
    exact (CFSG.Quasithin.Lie2Parabolic.pCoreOf_map_of_injective _
      (MulAut.conj x).injective (perfectCore P₀)).symm
  rw [map_sp4C (MulAut.conj x).toMonoidHom (MulAut.conj x).injective, hx0, hpco]

private theorem conj_mem_sp4C {x : Q} {P : Subgroup Q}
    (hx0 : P₀.map (MulAut.conj x).toMonoidHom = P)
    {y : Q} (hy : y ∈ sp4C P₀ (pCoreOf 2 (perfectCore P₀))) :
    x * y * x⁻¹ ∈ sp4C P (pCoreOf 2 (perfectCore P)) := by
  rw [← map_sp4C_of_map_eq hx0, ← MulAut.conj_apply]
  exact Subgroup.mem_map_of_mem _ hy

private theorem eq_zero_of_eq_mul_self {c y : F} (hc : c ≠ 1) (hy : y = c * y) : y = 0 := by
  have h : (c - 1) * y = 0 := by rw [sub_mul, one_mul, ← hy, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hc)

private theorem card_eq_one_of_stab_sigma_one {B : Subgroup Q} {a₁ a₂ t₂ : F}
    {τ : F ≃+* F} {x : ↥B → F × F} (hxw : ∀ b : ↥B, w (x b) = b)
    (ha1 : ∀ b : ↥B, (x b).1 = a₁ * (x b).1)
    (ha2 : ∀ b : ↥B, (x b).2 = a₂ * (x b).2)
    (ht2 : ∀ b : ↥B, (x b).2 = t₂ * τ (x b).1)
    (hne : a₁ ≠ 1 ∨ a₂ ≠ 1) (ht₂ : t₂ ≠ 0) (hw0 : w 0 = 1) :
    Nat.card ↥B = 1 := by
  have hzero : ∀ b : ↥B, x b = 0 := by
    intro b
    rcases hne with h1 | h2
    · have hx1 : (x b).1 = 0 := eq_zero_of_eq_mul_self h1 (ha1 b)
      refine Prod.ext hx1 ?_
      rw [ht2 b, hx1, map_zero, mul_zero, Prod.snd_zero]
    · have hx2 : (x b).2 = 0 := eq_zero_of_eq_mul_self h2 (ha2 b)
      have hx1 : (x b).1 = 0 := by
        have h0 : t₂ * τ (x b).1 = 0 := by rw [← ht2 b, hx2]
        exact τ.injective (by rw [(mul_eq_zero.mp h0).resolve_left ht₂, map_zero])
      exact Prod.ext hx1 hx2
  have hBbot : B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    change ((⟨b, hb⟩ : ↥B) : Q) = 1
    rw [← hxw ⟨b, hb⟩, hzero ⟨b, hb⟩, hw0]
  rw [hBbot, Subgroup.card_bot]

private theorem card_le_of_stab_sigma_ne {B : Subgroup Q} {a₁ t₂ : F}
    {σ τ : F ≃+* F} {x : ↥B → F × F} (hw : Function.Injective w)
    (hxw : ∀ b : ↥B, w (x b) = b)
    (ha1 : ∀ b : ↥B, (x b).1 = a₁ * σ (x b).1)
    (ht2 : ∀ b : ↥B, (x b).2 = t₂ * τ (x b).1)
    (hσ : σ ≠ 1) (ha₁ : a₁ ≠ 0) (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) :
    Nat.card ↥B ≤ 2 ^ (n / 2) := by
  have hinj : Function.Injective
      (fun b : ↥B => (⟨(x b).1, (ha1 b).symm⟩ : {y : F // a₁ * σ y = y})) := by
    intro b₁ b₂ h12
    have h12' : (x b₁).1 = (x b₂).1 := congrArg Subtype.val h12
    apply Subtype.ext
    have hpair : x b₁ = x b₂ := by
      refine Prod.ext h12' ?_
      rw [ht2 b₁, ht2 b₂, h12']
    rw [← hxw b₁, ← hxw b₂, hpair]
  calc Nat.card ↥B ≤ Nat.card {y : F // a₁ * σ y = y} :=
        Nat.card_le_card_of_injective _ hinj
    _ ≤ 2 ^ (n / 2) := Sp4.card_twistedFixed_le_sp4 hn hcard hσ ha₁

theorem eps_eq_false (h : Setting L T P₀ P₁ n w) {x : Q} (hx : x ∈ T)
    (hx0 : P₀.map (MulAut.conj x).toMonoidHom = P₀) {l₁ l₂ : F} {σ : F ≃+* F} {ε : Bool}
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hact : ∀ v : F × F, x * w v * x⁻¹ = w (Sp4.vAct l₁ l₂ σ ε v)) : ε = false := by
  by_contra hε
  have hε' : ε = true := by cases ε <;> simp_all
  have h0 : x * w (1, 0) * x⁻¹ = w (0, l₂) := by
    rw [hact (1, 0)]
    simp [Sp4.vAct, hε']
  have hC := conj_mem_sp4C hx0 (h.w_fst 1)
  rw [h0] at hC
  have hbot : w (0, l₂) ∈ (⊥ : Subgroup Q) := by
    rw [← sp4C_inf_sp4C h]
    exact ⟨hC, h.w_snd l₂⟩
  have h1 : w (0, l₂) = w 0 :=
    (Subgroup.mem_bot.mp hbot).trans (w_zero h).symm
  exact hl₂ (by simpa using congrArg Prod.snd (h.w_injective h1))

theorem eps_eq_true (h : Setting L T P₀ P₁ n w) {x : Q} (hx : x ∈ T)
    (hx0 : P₀.map (MulAut.conj x).toMonoidHom = P₁) {l₁ l₂ : F} {σ : F ≃+* F} {ε : Bool}
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hact : ∀ v : F × F, x * w v * x⁻¹ = w (Sp4.vAct l₁ l₂ σ ε v)) : ε = true := by
  by_contra hε
  have hε' : ε = false := by cases ε <;> simp_all
  have h0 : x * w (1, 0) * x⁻¹ = w (l₁, 0) := by
    rw [hact (1, 0)]
    simp [Sp4.vAct, hε']
  have hC : x * w (1, 0) * x⁻¹ ∈ sp4C P₁ (pCoreOf 2 (perfectCore P₁)) :=
    conj_mem_sp4C hx0 (h.w_fst 1)
  rw [h0] at hC
  have hbot : w (l₁, 0) ∈ (⊥ : Subgroup Q) := by
    rw [← sp4C_inf_sp4C h]
    exact ⟨h.w_fst l₁, hC⟩
  have h1 : w (l₁, 0) = w 0 :=
    (Subgroup.mem_bot.mp hbot).trans (w_zero h).symm
  exact hl₁ (by simpa using congrArg Prod.fst (h.w_injective h1))

theorem odd_of_swap (h : Setting L T P₀ P₁ n w) {a : Q} (ha : a ∈ T) (ha2 : a * a = 1)
    (hsw : P₀.map (MulAut.conj a).toMonoidHom = P₁) : Odd n := by
  obtain ⟨l₁, l₂, σ, ε, hl₁, hl₂, hact, -⟩ := h.act a ha
  have hε : ε = true := eps_eq_true h ha hsw hl₁ hl₂ hact
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hstep : ∀ v : F × F, a * (a * w v * a⁻¹) * a⁻¹ = w v := by
    intro v
    calc a * (a * w v * a⁻¹) * a⁻¹ = (a * a) * w v * (a * a) := by rw [hainv]; group
      _ = w v := by rw [ha2, one_mul, mul_one]
  have hvv : ∀ v : F × F, Sp4.vAct l₁ l₂ σ ε (Sp4.vAct l₁ l₂ σ ε v) = v := by
    intro v
    apply h.w_injective
    rw [← hact (Sp4.vAct l₁ l₂ σ ε v), ← hact v]
    exact hstep v
  rw [hε] at hvv
  have hfix : ∀ x : F, l₁ * σ (l₂ * σ x) ^ 2 = x := by
    intro x
    have hx := congrArg Prod.fst (hvv (x, 0))
    simpa [Sp4.vAct] using hx
  have h1 : l₁ * (σ l₂) ^ 2 = 1 := by simpa using hfix 1
  have h2 : ∀ x : F, (σ (σ x)) ^ 2 = x := by
    intro x
    have hx := hfix x
    rw [map_mul, mul_pow, ← mul_assoc, h1, one_mul] at hx
    exact hx
  obtain ⟨fr, hfr, hord, htop, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (p := 2) (n := n) Nat.prime_two (by have := h.two_le; omega) h.card_F
  have hcomp : fr * σ * σ = 1 := by
    ext x
    rw [RingAut.mul_apply, RingAut.mul_apply, RingAut.one_apply, hfr]
    exact h2 x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top σ)
  have hpow : fr ^ (2 * k + 1) = 1 := by
    have hcomp' : fr * fr ^ k * fr ^ k = 1 := by simpa [← hk] using hcomp
    calc fr ^ (2 * k + 1) = fr ^ (1 : ℤ) * fr ^ k * fr ^ k := by
          rw [show 2 * k + 1 = 1 + k + k by ring, zpow_add, zpow_add]
      _ = fr * fr ^ k * fr ^ k := by rw [zpow_one]
      _ = 1 := hcomp'
  have hdvd : (n : ℤ) ∣ 2 * k + 1 := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hpow
  exact Odd.of_dvd_nat (Odd.natAbs (⟨k, rfl⟩ : Odd (2 * k + 1 : ℤ))) (Int.natCast_dvd.mp hdvd)

theorem card_le_of_swap (h : Setting L T P₀ P₁ n w) {t : Q} (ht : t ∈ T)
    (hsw : P₀.map (MulAut.conj t).toMonoidHom = P₁) {B : Subgroup Q}
    (hB : B ≤ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁))
    (hBt : ∀ b ∈ B, t * b = b * t) : Nat.card ↥B ≤ 2 ^ n := by
  obtain ⟨l₁, l₂, σ, ε, hl₁, hl₂, hact, -⟩ := h.act t ht
  have hε : ε = true := eps_eq_true h ht hsw hl₁ hl₂ hact
  let x : ↥B → F × F := fun b => Classical.choose (exists_w_eq h (hB b.2))
  have hxw : ∀ b : ↥B, w (x b) = b :=
    fun b => Classical.choose_spec (exists_w_eq h (hB b.2))
  have hfix : ∀ b : ↥B, Sp4.vAct l₁ l₂ σ ε (x b) = x b := by
    intro b
    apply h.w_injective
    rw [← hact (x b), hxw b, hBt b b.2]
    group
  have hsnd : ∀ b : ↥B, (x b).2 = l₂ * σ (x b).1 := by
    intro b
    have hb := congrArg Prod.snd (hfix b)
    rw [hε] at hb
    simpa [Sp4.vAct] using hb.symm
  have hinj : Function.Injective (fun b : ↥B => (x b).1) := by
    intro b₁ b₂ h12
    apply Subtype.ext
    have h12' : (x b₁).1 = (x b₂).1 := h12
    have hpair : x b₁ = x b₂ := by
      refine Prod.ext h12' ?_
      rw [hsnd b₁, hsnd b₂, h12']
    rw [← hxw b₁, ← hxw b₂, hpair]
  calc Nat.card ↥B ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ n := h.card_F

theorem card_le_of_stab (h : Setting L T P₀ P₁ n w) {a : Q} (ha : a ∈ T) (haL : a ∉ L)
    (ha0 : P₀.map (MulAut.conj a).toMonoidHom = P₀) {t : Q} (ht : t ∈ T)
    (hsw : P₀.map (MulAut.conj t).toMonoidHom = P₁) {B : Subgroup Q}
    (hB : B ≤ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁))
    (hBa : ∀ b ∈ B, a * b = b * a) (hBt : ∀ b ∈ B, t * b = b * t) :
    Nat.card ↥B ≤ 2 ^ (n / 2) := by
  obtain ⟨a₁, a₂, σ, ε, ha₁, ha₂, hact, htriv⟩ := h.act a ha
  obtain ⟨t₁, t₂, τ, δ, ht₁, ht₂, hactt, -⟩ := h.act t ht
  have hε : ε = false := eps_eq_false h ha ha0 ha₁ ha₂ hact
  have hδ : δ = true := eps_eq_true h ht hsw ht₁ ht₂ hactt
  let x : ↥B → F × F := fun b => Classical.choose (exists_w_eq h (hB b.2))
  have hxw : ∀ b : ↥B, w (x b) = b :=
    fun b => Classical.choose_spec (exists_w_eq h (hB b.2))
  have hfixa : ∀ b : ↥B, Sp4.vAct a₁ a₂ σ ε (x b) = x b := by
    intro b
    apply h.w_injective
    rw [← hact (x b), hxw b, hBa b b.2]
    group
  have hfixt : ∀ b : ↥B, Sp4.vAct t₁ t₂ τ δ (x b) = x b := by
    intro b
    apply h.w_injective
    rw [← hactt (x b), hxw b, hBt b b.2]
    group
  have ha1 : ∀ b : ↥B, (x b).1 = a₁ * σ (x b).1 := by
    intro b
    have hb := congrArg Prod.fst (hfixa b)
    rw [hε] at hb
    simpa [Sp4.vAct] using hb.symm
  have ha2 : ∀ b : ↥B, (x b).2 = a₂ * σ (x b).2 := by
    intro b
    have hb := congrArg Prod.snd (hfixa b)
    rw [hε] at hb
    simpa [Sp4.vAct] using hb.symm
  have ht2 : ∀ b : ↥B, (x b).2 = t₂ * τ (x b).1 := by
    intro b
    have hb := congrArg Prod.snd (hfixt b)
    rw [hδ] at hb
    simpa [Sp4.vAct] using hb.symm
  by_cases hσ : σ = 1
  · have hne : a₁ ≠ 1 ∨ a₂ ≠ 1 := by
      have hnontriv : ¬ (∀ v : F × F, Sp4.vAct a₁ a₂ σ ε v = v) := fun hv => haL (htriv hv)
      by_contra hcon
      simp only [not_or, not_ne_iff] at hcon
      obtain ⟨h1, h2⟩ := hcon
      apply hnontriv
      intro v
      simp [Sp4.vAct, hε, hσ, h1, h2]
    have h1 := card_eq_one_of_stab_sigma_one hxw
      (fun b => (ha1 b).trans (by rw [hσ, RingAut.one_apply]))
      (fun b => (ha2 b).trans (by rw [hσ, RingAut.one_apply])) ht2 hne ht₂ (w_zero h)
    rw [h1]
    exact Nat.one_le_two_pow
  · exact card_le_of_stab_sigma_ne h.w_injective hxw ha1 ht2 hσ ha₁
      (by have := h.two_le; omega) h.card_F

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting
