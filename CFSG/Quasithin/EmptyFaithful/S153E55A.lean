module

public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

namespace S153E55

variable {W : Type*} [CommGroup W] [Finite W]

section Coprime

variable (hW : ∀ w : W, w ^ 2 = 1)
include hW

theorem decomp_top {y : MulAut W} (hy : Odd (orderOf y)) :
    fixV (Subgroup.zpowers y) ⊔ commV (Subgroup.zpowers y) = ⊤ ∧
      fixV (Subgroup.zpowers y) ⊓ commV (Subgroup.zpowers y) = ⊥ := by
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by rwa [Nat.card_zpowers]
  obtain ⟨h1, h2⟩ := B1.coprime_decomp hW hodd (M := ⊤) (fun g _ m _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub] at h1 h2
  simp only [top_inf_eq] at h1 h2
  exact ⟨h1, h2⟩

theorem le_commV_of_fpf {y : MulAut W} (hy : Odd (orderOf y)) {V : Subgroup W}
    (hVy : ∀ g ∈ Subgroup.zpowers y, ∀ v ∈ V, g v ∈ V) (hf : ∀ v ∈ V, y v = v → v = 1) :
    V ≤ commV (Subgroup.zpowers y) := by
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by rwa [Nat.card_zpowers]
  obtain ⟨h1, -⟩ := B1.coprime_decomp hW hodd hVy
  have h0 : V ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, hvf⟩
    exact Subgroup.mem_bot.2 (hf v hv (mem_fixV_zpowers_iff.mp hvf))
  rw [h0, bot_sup_eq] at h1
  rw [← h1, commV_eq_commSub]
  exact commSub_mono le_top le_rfl

theorem mem_of_commHom_mem {y : MulAut W} (hy : Odd (orderOf y)) {V : Subgroup W}
    (hVy : ∀ g ∈ Subgroup.zpowers y, ∀ v ∈ V, g v ∈ V) (hf : ∀ v ∈ V, y v = v → v = 1)
    {d : W} (hd : d ∈ commV (Subgroup.zpowers y)) (hdV : y d * d⁻¹ ∈ V) : d ∈ V := by
  have hVD := le_commV_of_fpf hW hy hVy hf
  have hmap_le : V.map (commHom y) ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    rw [commHom_apply]
    exact V.mul_mem (hVy y (Subgroup.mem_zpowers y) v hv) (V.inv_mem hv)
  have hinf : V ⊓ (commHom y).ker = ⊥ := by
    rw [ker_commHom, eq_bot_iff]
    rintro v ⟨hv, hvf⟩
    exact Subgroup.mem_bot.2 (hf v hv (mem_fixV_zpowers_iff.mp hvf))
  have hrk := rk_map_add_rk_inf_ker (commHom y) V
  rw [hinf, rk_bot, add_zero] at hrk
  have heq : V.map (commHom y) = V := eq_of_le_of_rk_le hW hmap_le hrk.ge
  have hdV' : commHom y d ∈ V.map (commHom y) := by
    rw [heq]
    exact hdV
  obtain ⟨v, hv, hvd⟩ := hdV'
  have hker : d * v⁻¹ ∈ (commHom y).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hvd, mul_inv_cancel]
  rw [ker_commHom] at hker
  have hmemD : d * v⁻¹ ∈ commV (Subgroup.zpowers y) :=
    Subgroup.mul_mem _ hd (Subgroup.inv_mem _ (hVD hv))
  obtain ⟨-, hi⟩ := decomp_top hW hy
  have : d * v⁻¹ ∈ fixV (Subgroup.zpowers y) ⊓ commV (Subgroup.zpowers y) := ⟨hker, hmemD⟩
  rw [hi, Subgroup.mem_bot, mul_inv_eq_one] at this
  rw [this]
  exact hv

end Coprime

section Decomp

variable (hW : ∀ w : W, w ^ 2 = 1)
include hW

theorem exists_fix_mul_comm {y : MulAut W} (hy : Odd (orderOf y)) (w : W) :
    ∃ f ∈ fixV (Subgroup.zpowers y), ∃ d ∈ commV (Subgroup.zpowers y), f * d = w := by
  have h := (decomp_top hW hy).1
  have hw : w ∈ fixV (Subgroup.zpowers y) ⊔ commV (Subgroup.zpowers y) := by
    rw [h]
    exact Subgroup.mem_top w
  exact Subgroup.mem_sup.mp hw

theorem exists_compl {V : Subgroup W} {y₁ y₂ : MulAut W} (hc : y₁ * y₂ = y₂ * y₁)
    (ho₁ : Odd (orderOf y₁)) (ho₂ : Odd (orderOf y₂))
    (hV₁ : ∀ g ∈ Subgroup.zpowers y₁, ∀ v ∈ V, g v ∈ V)
    (hf₁ : ∀ v ∈ V, y₁ v = v → v = 1) (hf₂ : ∀ v ∈ V, y₂ v = v → v = 1)
    (h3 : ∀ d ∈ commV (Subgroup.zpowers y₂), commHom y₁ d ∈ V) :
    V ⊓ (fixV (Subgroup.zpowers y₁) ⊔ fixV (Subgroup.zpowers y₂)) = ⊥ ∧
      V ⊔ (fixV (Subgroup.zpowers y₁) ⊔ fixV (Subgroup.zpowers y₂)) = ⊤ := by
  have hVD₁ := le_commV_of_fpf hW ho₁ hV₁ hf₁
  obtain ⟨-, hi₁⟩ := decomp_top hW ho₁
  have hcz : ∀ g ∈ Subgroup.zpowers y₁, ∀ b ∈ Subgroup.zpowers y₂, g * b = b * g := by
    intro g hg b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hc m n).eq
  have hD₁inv : ∀ b ∈ Subgroup.zpowers y₂, ∀ c ∈ commV (Subgroup.zpowers y₁),
      b c ∈ commV (Subgroup.zpowers y₁) := by
    have := B1.commSub_invariant_of_commute (V := W) (Y := Subgroup.zpowers y₁)
      (B := Subgroup.zpowers y₂) (M := ⊤) hcz (fun b _ m _ => Subgroup.mem_top _)
    intro b hb c hc'
    rw [commV_eq_commSub] at hc' ⊢
    exact this b hb c hc'
  have hF₁inv : ∀ f ∈ fixV (Subgroup.zpowers y₁), y₂ f ∈ fixV (Subgroup.zpowers y₁) := by
    intro f hf
    rw [mem_fixV_zpowers_iff] at hf ⊢
    have := congrArg (fun t : MulAut W => t f) hc
    simp only [MulAut.mul_apply] at this
    rw [this, hf]
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro z ⟨hzV, hz⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hz
    obtain ⟨c, hc', d, hd, hbcd⟩ := exists_fix_mul_comm hW ho₁ b
    have hac : a * c = 1 := by
      have h1 : a * c ∈ fixV (Subgroup.zpowers y₁) := Subgroup.mul_mem _ ha hc'
      have h2 : a * c ∈ commV (Subgroup.zpowers y₁) := by
        have e : a * c = (a * b) * d⁻¹ := by
          rw [← hbcd]
          simp [mul_assoc]
        rw [e]
        exact Subgroup.mul_mem _ (hVD₁ hzV) (Subgroup.inv_mem _ hd)
      have h4 : a * c ∈ fixV (Subgroup.zpowers y₁) ⊓ commV (Subgroup.zpowers y₁) := ⟨h1, h2⟩
      rwa [hi₁, Subgroup.mem_bot] at h4
    have hzd : a * b = d := by
      have e : a * b = (a * c) * d := by
        rw [← hbcd, mul_assoc]
      rw [e, hac, one_mul]
    have hy2b : y₂ b = b := mem_fixV_zpowers_iff.mp hb
    have hy2c : y₂ c ∈ fixV (Subgroup.zpowers y₁) := hF₁inv c hc'
    have hy2d : y₂ d ∈ commV (Subgroup.zpowers y₁) :=
      hD₁inv y₂ (Subgroup.mem_zpowers y₂) d hd
    have hdy : y₂ d = d := by
      have e : y₂ c * y₂ d = c * d := by rw [← map_mul, hbcd, hy2b]
      have h1 : y₂ c * c⁻¹ ∈ fixV (Subgroup.zpowers y₁) :=
        Subgroup.mul_mem _ hy2c (Subgroup.inv_mem _ hc')
      have h2 : y₂ c * c⁻¹ ∈ commV (Subgroup.zpowers y₁) := by
        have e2 : y₂ c * c⁻¹ = d * (y₂ d)⁻¹ := by
          have e3 : y₂ c = c * d * (y₂ d)⁻¹ := by rw [← e, mul_inv_cancel_right]
          rw [e3]
          have e4 : c * d * (y₂ d)⁻¹ * c⁻¹ = (c * c⁻¹) * (d * (y₂ d)⁻¹) := by ac_rfl
          rw [e4, mul_inv_cancel, one_mul]
        rw [e2]
        exact Subgroup.mul_mem _ hd (Subgroup.inv_mem _ hy2d)
      have h4 : y₂ c * c⁻¹ ∈ fixV (Subgroup.zpowers y₁) ⊓ commV (Subgroup.zpowers y₁) := ⟨h1, h2⟩
      rw [hi₁, Subgroup.mem_bot, mul_inv_eq_one] at h4
      rw [h4] at e
      exact mul_left_cancel e
    have hdV : d ∈ V := by rw [← hzd]; exact hzV
    have hd1 : d = 1 := hf₂ d hdV hdy
    rw [hzd, hd1]
    exact Subgroup.one_mem _
  · rw [eq_top_iff]
    intro w _
    obtain ⟨f₂, hf₂', d₂, hd₂, rfl⟩ := exists_fix_mul_comm hW ho₂ w
    obtain ⟨f₁, hf₁', d₁, hd₁, hd₂eq⟩ := exists_fix_mul_comm hW ho₁ d₂
    have hd₁V : d₁ ∈ V := by
      refine mem_of_commHom_mem hW ho₁ hV₁ hf₁ hd₁ ?_
      have e1 : d₁ = f₁⁻¹ * d₂ := by rw [← hd₂eq]; simp
      have hker : commHom y₁ f₁ = 1 := by
        have : f₁ ∈ (commHom y₁).ker := by rw [ker_commHom]; exact hf₁'
        exact this
      have : commHom y₁ d₁ = commHom y₁ d₂ := by
        rw [e1, map_mul, map_inv, hker, inv_one, one_mul]
      rw [← commHom_apply, this]
      exact h3 d₂ hd₂
    rw [Subgroup.mem_sup]
    refine ⟨d₁, hd₁V, f₁ * f₂, Subgroup.mul_mem_sup hf₁' hf₂', ?_⟩
    rw [← hd₂eq]
    ac_rfl

omit [Finite W] hW in
theorem mem_of_fixed {V C : Subgroup W} (hinf : V ⊓ C = ⊥) (hsup : V ⊔ C = ⊤) {y' : MulAut W}
    (hVy : ∀ v ∈ V, y' v ∈ V) (hCy : ∀ c ∈ C, y' c ∈ C) (hf : ∀ v ∈ V, y' v = v → v = 1)
    {w : W} (hw : y' w = w) : w ∈ C := by
  have hw' : w ∈ V ⊔ C := by rw [hsup]; exact Subgroup.mem_top w
  obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw'
  rw [map_mul] at hw
  have h1 : y' v * v⁻¹ ∈ V := V.mul_mem (hVy v hv) (V.inv_mem hv)
  have h2 : y' v * v⁻¹ ∈ C := by
    have e : y' v * v⁻¹ = c * (y' c)⁻¹ := by
      have e1 : y' v = v * c * (y' c)⁻¹ := by rw [← hw, mul_inv_cancel_right]
      have e2 : v * c * (y' c)⁻¹ * v⁻¹ = (v * v⁻¹) * (c * (y' c)⁻¹) := by ac_rfl
      rw [e1, e2, mul_inv_cancel, one_mul]
    rw [e]
    exact C.mul_mem hc (C.inv_mem (hCy c hc))
  have h3 : y' v * v⁻¹ ∈ V ⊓ C := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h3
  have h4 : v = 1 := hf v hv h3
  rw [h4, one_mul]
  exact hc

omit [Finite W] hW in
theorem invariant_sup_fixV {y₁ y₂ y' : MulAut W} (h₁ : y' * y₁ = y₁ * y') (h₂ : y' * y₂ = y₂ * y') :
    ∀ c ∈ fixV (Subgroup.zpowers y₁) ⊔ fixV (Subgroup.zpowers y₂),
      y' c ∈ fixV (Subgroup.zpowers y₁) ⊔ fixV (Subgroup.zpowers y₂) := by
  have key : ∀ (z : MulAut W), y' * z = z * y' → ∀ f ∈ fixV (Subgroup.zpowers z),
      y' f ∈ fixV (Subgroup.zpowers z) := by
    intro z hz f hf
    rw [mem_fixV_zpowers_iff] at hf ⊢
    have := congrArg (fun t : MulAut W => t f) hz
    simp only [MulAut.mul_apply] at this
    rw [← this, hf]
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hc
  rw [map_mul]
  exact Subgroup.mul_mem_sup (key y₁ h₁ a ha) (key y₂ h₂ b hb)

end Decomp

section FPF

@[expose] def trivMod (S : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ w : W, g w * w⁻¹ ∈ S}
  one_mem' := fun w => by simp
  mul_mem' := by
    intro g g' hg hg' w
    have e : (g * g') w * w⁻¹ = (g (g' w) * (g' w)⁻¹) * (g' w * w⁻¹) := by
      simp [MulAut.mul_apply]
    rw [e]
    exact S.mul_mem (hg _) (hg' w)
  inv_mem' := by
    intro g hg w
    have e : g⁻¹ w * w⁻¹ = (w * (g⁻¹ w)⁻¹)⁻¹ := by simp
    have h1 : g (g⁻¹ w) * (g⁻¹ w)⁻¹ ∈ S := hg (g⁻¹ w)
    have h2 : g (g⁻¹ w) = w := by simp
    rw [e]
    rw [h2] at h1
    exact S.inv_mem h1

private theorem perm_facts : ∀ p : Equiv.Perm (Fin 3), p ^ 3 = 1 → p ≠ 1 →
    (Equiv.swap (0 : Fin 3) 1 * p * (Equiv.swap (0 : Fin 3) 1)⁻¹ = p⁻¹) ∧
      ∀ q : Equiv.Perm (Fin 3), ∃ i : Fin 3, ∃ j : Fin 2,
        q = p ^ (i : ℕ) * Equiv.swap (0 : Fin 3) 1 ^ (j : ℕ) := by
  decide +kernel

variable (hW : ∀ w : W, w ^ 2 = 1)
include hW

theorem fixV_eq_bot_of_perm {N : Subgroup (MulAut W)} (e : ↥N ≃* Equiv.Perm (Fin 3))
    (hN : commV N = ⊤) {a : MulAut W} (haN : a ∈ N) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    fixV (Subgroup.zpowers a) = ⊥ := by
  have hea3 : (e ⟨a, haN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, haN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hea1 : e ⟨a, haN⟩ ≠ 1 := by
    intro h
    apply ha1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  obtain ⟨hconj, hgen⟩ := perm_facts (e ⟨a, haN⟩) hea3 hea1
  let σN : ↥N := e.symm (Equiv.swap (0 : Fin 3) 1)
  let σ : MulAut W := (σN : MulAut W)
  have hσσ : σ * σ = 1 := by
    have : σN * σN = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      simp [σN]
    exact congrArg Subtype.val this
  have hσa : σ * a * σ⁻¹ = a⁻¹ := by
    have : σN * ⟨a, haN⟩ * σN⁻¹ = ⟨a, haN⟩⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv]
      simpa [σN] using hconj
    exact congrArg Subtype.val this
  have hgen' : ∀ n ∈ N, ∃ (i j : ℕ), n = a ^ i * σ ^ j := by
    intro n hn
    obtain ⟨i, j, hij⟩ := hgen (e ⟨n, hn⟩)
    refine ⟨i, j, ?_⟩
    have : (⟨n, hn⟩ : ↥N) = ⟨a, haN⟩ ^ (i : ℕ) * σN ^ (j : ℕ) := by
      apply e.injective
      rw [map_mul, map_pow, map_pow]
      simpa [σN] using hij
    exact congrArg Subtype.val this
  have hao : Odd (orderOf a) := by
    have : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
    rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
    · rw [h]; exact ⟨0, rfl⟩
    · rw [h]; exact ⟨1, rfl⟩
  have hσ2 : ∀ w : W, σ (σ w) = w := fun w => by
    have := congrArg (fun t : MulAut W => t w) hσσ
    simpa [MulAut.mul_apply] using this
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hσa' : ∀ w : W, σ (a w) = a⁻¹ (σ w) := fun w => by
    have := congrArg (fun t : MulAut W => t (σ w)) hσa
    simp only [MulAut.mul_apply, hσinv, hσ2] at this
    exact this
  have hσa'' : ∀ w : W, a (σ w) = σ (a⁻¹ w) := fun w => by
    have h1 := hσa' (σ w)
    rw [hσ2] at h1
    have h2 := congrArg σ h1
    rw [hσ2] at h2
    exact h2
  have hinv : ∀ x : W, x⁻¹ = x := fun x => by
    have h := hW x
    rw [pow_two, mul_eq_one_iff_eq_inv] at h
    exact h.symm
  obtain ⟨hs, hi⟩ := decomp_top hW hao
  have hFinv : ∀ f ∈ fixV (Subgroup.zpowers a), σ f ∈ fixV (Subgroup.zpowers a) := by
    intro f hf
    rw [mem_fixV_zpowers_iff] at hf ⊢
    rw [hσa'']
    have : a⁻¹ f = f := by
      have h1 := congrArg (fun t : W => a⁻¹ t) hf
      simpa using h1.symm
    rw [this]
  have hσnorm : ∀ g ∈ Subgroup.zpowers a, σ * g * σ⁻¹ ∈ Subgroup.zpowers a := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← conj_zpow, hσa]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) k
  have hDinv : ∀ d ∈ commV (Subgroup.zpowers a), σ d ∈ commV (Subgroup.zpowers a) := by
    intro d hd
    refine Subgroup.closure_induction (p := fun d _ => σ d ∈ commV (Subgroup.zpowers a)) ?_ ?_ ?_ ?_ hd
    · rintro _ ⟨g, hg, w, rfl⟩
      have e1 : σ (g w * w⁻¹) = (σ * g * σ⁻¹) (σ w) * (σ w)⁻¹ := by
        simp [MulAut.mul_apply, hσinv, hσ2]
      rw [e1]
      exact Subgroup.subset_closure ⟨σ * g * σ⁻¹, hσnorm g hg, σ w, rfl⟩
    · rw [map_one]; exact Subgroup.one_mem _
    · intro x y _ _ hx hy
      rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      rw [map_inv]; exact Subgroup.inv_mem _ hx
  let F' : Subgroup W := (fixV (Subgroup.zpowers a)).map (commHom σ)
  have hF'F : F' ≤ fixV (Subgroup.zpowers a) := by
    rintro _ ⟨f, hf, rfl⟩
    rw [commHom_apply]
    exact Subgroup.mul_mem _ (hFinv f hf) (Subgroup.inv_mem _ hf)
  have haK : a ∈ trivMod (commV (Subgroup.zpowers a) ⊔ F') := fun w =>
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, w, rfl⟩)
  have hσK : σ ∈ trivMod (commV (Subgroup.zpowers a) ⊔ F') := by
    intro w
    obtain ⟨f, hf, d, hd, rfl⟩ := exists_fix_mul_comm hW hao w
    have e1 : σ (f * d) * (f * d)⁻¹ = (σ f * f⁻¹) * (σ d * d⁻¹) := by
      simp [map_mul, mul_comm, mul_left_comm, mul_assoc]
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨f, hf, rfl⟩) (Subgroup.mem_sup_left ?_)
    exact Subgroup.mul_mem _ (hDinv d hd) (Subgroup.inv_mem _ hd)
  have hNK : N ≤ trivMod (commV (Subgroup.zpowers a) ⊔ F') := by
    intro n hn
    obtain ⟨i, j, rfl⟩ := hgen' n hn
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ haK i) (Subgroup.pow_mem _ hσK j)
  have hStop : commV (Subgroup.zpowers a) ⊔ F' = ⊤ := by
    rw [eq_top_iff, ← hN]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    exact hNK hx v
  have hinf' : commV (Subgroup.zpowers a) ⊓ F' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxD, hxF'⟩
    have h1 : x ∈ fixV (Subgroup.zpowers a) ⊓ commV (Subgroup.zpowers a) := ⟨hF'F hxF', hxD⟩
    rw [hi] at h1
    exact h1
  have hr1 := rk_sup_add_rk_inf (commV (Subgroup.zpowers a)) F'
  rw [hinf', rk_bot, add_zero, hStop, rk_top] at hr1
  have hr2 := rk_sup_add_rk_inf (fixV (Subgroup.zpowers a)) (commV (Subgroup.zpowers a))
  rw [hi, rk_bot, add_zero, hs, rk_top] at hr2
  have hFF' : F' = fixV (Subgroup.zpowers a) := eq_of_le_of_rk_le hW hF'F (by omega)
  have hσfix : ∀ f ∈ fixV (Subgroup.zpowers a), σ f = f := by
    intro f hf
    have hf' : f ∈ F' := by rw [hFF']; exact hf
    obtain ⟨g, hg, hgf⟩ := hf'
    rw [← hgf, commHom_apply, map_mul, map_inv, hσ2, hinv (σ g), hinv g, mul_comm]
  have hF'bot : F' = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨f, hf, rfl⟩
    rw [commHom_apply, hσfix f hf, mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [← hFF']
  exact hF'bot

end FPF


end S153E55

end CFSG.Quasithin
