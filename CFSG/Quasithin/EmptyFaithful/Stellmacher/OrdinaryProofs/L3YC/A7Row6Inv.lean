module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6Inv

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6
open Equiv MulAction

theorem pw_inj {a b c d : Fin 3} (h : pw a b = pw c d) : a = c ∧ b = d := by
  have h2 := congrArg expo h
  rw [expo_pw, expo_pw] at h2
  simpa using h2

theorem indep_of_det_zero : ∀ a₁ a₂ b₁ b₂ : Fin 3, (a₁ ≠ 0 ∨ a₂ ≠ 0) →
    a₁ * b₂ - a₂ * b₁ = 0 → ∃ k : Fin 3, b₁ = k.val • a₁ ∧ b₂ = k.val • a₂ := by
  decide +kernel

theorem span_of_det_ne : ∀ a₁ a₂ b₁ b₂ u v : Fin 3, a₁ * b₂ - a₂ * b₁ ≠ 0 →
    ∃ α β : Fin 3, u = α.val • a₁ + β.val • b₁ ∧ v = α.val • a₂ + β.val • b₂ := by
  decide +kernel

theorem det_bridge : ∀ A B C D : Fin 3,
    ((A.val : ℕ) : ZMod 3) * ((D.val : ℕ) : ZMod 3) - ((B.val : ℕ) : ZMod 3) * ((C.val : ℕ) : ZMod 3)
      = 1 ↔ A * D - B * C = 1 := by
  decide +kernel

theorem core_false : ∀ A B C D a₁ a₂ b₁ b₂ : Fin 3,
    A * D - B * C = 1 → a₁ * b₂ - a₂ * b₁ ≠ 0 →
    a₁.val • A + a₂.val • B = -a₁ → a₁.val • C + a₂.val • D = -a₂ →
    b₁.val • A + b₂.val • B = b₁ → b₁.val • C + b₂.val • D = b₂ → False := by
  decide +kernel

theorem pw_pow (a b : Fin 3) (k : ℕ) : pw a b ^ k = pw (k • a) (k • b) := by
  induction k with
  | zero => simp [pw_zero_zero]
  | succ k ih => simp only [pow_succ, ih, pw_mul_pw, succ_nsmul]

theorem card_E9 : Nat.card E9 = 9 := by
  have hbij : Function.Bijective (fun p : Fin 3 × Fin 3 =>
      (⟨pw p.1 p.2, (mem_E9_iff _).2 ⟨p.1, p.2, rfl⟩⟩ : E9)) := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h' : pw a b = pw c d := congrArg Subtype.val h
      obtain ⟨rfl, rfl⟩ := pw_inj h'
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨a, b, rfl⟩ := (mem_E9_iff g).1 hg
      exact ⟨(a, b), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

theorem factorization_seven_three : (Nat.card (Perm (Fin 7))).factorization 3 = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [show (7 : ℕ).factorial = 3 ^ 2 * 560 by decide]
  rw [Nat.factorization_mul (by positivity) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_three]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 560 by norm_num)]

theorem exists_conj_le_E9 (H : Subgroup (Perm (Fin 7))) (hH : Nat.card H = 9) :
    ∃ g : Perm (Fin 7), ∀ x ∈ H, g * x * g⁻¹ ∈ E9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE9 : IsPGroup 3 E9 := IsPGroup.of_card (n := 2) (by rw [card_E9]; norm_num)
  have hH3 : IsPGroup 3 H := IsPGroup.of_card (n := 2) (by rw [hH]; norm_num)
  obtain ⟨R, hR⟩ := IsPGroup.exists_le_sylow hE9
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hH3
  have hRcard : Nat.card (R : Subgroup (Perm (Fin 7))) = 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_seven_three]; norm_num
  have hRE : (R : Subgroup (Perm (Fin 7))) = E9 :=
    (Subgroup.eq_of_le_of_card_ge hR (by rw [hRcard, card_E9])).symm
  obtain ⟨g, hg⟩ := exists_smul_eq (Perm (Fin 7)) Q R
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup (Perm (Fin 7))) := hQ hx
  have hmem : MulAut.conj g x ∈ ((g • Q : Sylow 3 (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
    rw [Sylow.coe_smul]
    exact Set.smul_mem_smul_set hxQ
  rw [hg] at hmem
  have hmem' : MulAut.conj g x ∈ (E9 : Set (Perm (Fin 7))) := by
    rw [← hRE]; exact hmem
  simpa [MulAut.conj_apply] using hmem'

theorem conj_mul' (n x y : Perm (Fin 7)) : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by
  group

theorem pw_eq_pow (u v : Fin 3) : pw u v = xP ^ u.val * yP ^ v.val := by
  have h1 : ∀ w : Fin 3, w.val • (1 : Fin 3) = w := by decide
  have hu : xP ^ u.val = pw u 0 := by
    rw [xP_eq_pw, pw_pow, h1 u]
    simp
  have hv : yP ^ v.val = pw 0 v := by
    rw [yP_eq_pw, pw_pow, h1 v]
    simp
  rw [hu, hv, pw_mul_pw]
  simp

theorem conj_pw (n : Perm (Fin 7)) (A B C D : Fin 3) (hx : n * xP * n⁻¹ = pw A C)
    (hy : n * yP * n⁻¹ = pw B D) (u v : Fin 3) :
    n * pw u v * n⁻¹ = pw (u.val • A + v.val • B) (u.val • C + v.val • D) := by
  rw [pw_eq_pow u v, conj_mul', ← conj_pow, ← conj_pow, hx, hy, pw_pow, pw_pow, pw_mul_pw]

theorem conj_mem_E9_of_basis (n : Perm (Fin 7)) (a₁ a₂ b₁ b₂ : Fin 3)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (ha : n * pw a₁ a₂ * n⁻¹ ∈ E9) (hb : n * pw b₁ b₂ * n⁻¹ ∈ E9) (u v : Fin 3) :
    n * pw u v * n⁻¹ ∈ E9 := by
  obtain ⟨α, β, hu, hv⟩ := span_of_det_ne a₁ a₂ b₁ b₂ u v hdet
  have hpw : pw u v = (pw a₁ a₂) ^ α.val * (pw b₁ b₂) ^ β.val := by
    rw [pw_pow, pw_pow, pw_mul_pw, hu, hv]
  rw [hpw, conj_mul', ← conj_pow, ← conj_pow]
  exact mul_mem (pow_mem ha _) (pow_mem hb _)

theorem mem_normalizer_E9_of_basis (n : Perm (Fin 7)) (a₁ a₂ b₁ b₂ : Fin 3)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (ha : n * pw a₁ a₂ * n⁻¹ ∈ E9) (hb : n * pw b₁ b₂ * n⁻¹ ∈ E9) :
    n ∈ Subgroup.normalizer E9 := by
  have hle : E9.map (MulAut.conj n).toMonoidHom ≤ E9 := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨u, v, rfl⟩ := (mem_E9_iff g).1 hg
    exact conj_mem_E9_of_basis n a₁ a₂ b₁ b₂ hdet ha hb u v
  have hinj : Function.Injective (MulAut.conj n).toMonoidHom :=
    fun x y h => (MulAut.conj n).injective h
  have hcard : Nat.card (E9.map (MulAut.conj n).toMonoidHom) = Nat.card E9 :=
    Subgroup.card_map_of_injective hinj
  have heq : E9.map (MulAut.conj n).toMonoidHom = E9 :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem det_of_mem (n : Perm (Fin 7)) (hn : n ∈ alternatingGroup (Fin 7))
    (hN : n ∈ Subgroup.normalizer E9) :
    ∃ A B C D : Fin 3, A * D - B * C = 1 ∧ n * xP * n⁻¹ = pw A C ∧ n * yP * n⁻¹ = pw B D := by
  obtain ⟨A, B, C, D, hdz, hx, hy⟩ := row6_normalizer_E9_det n hn hN
  exact ⟨A, B, C, D, (det_bridge A B C D).1 hdz, hx, hy⟩

theorem core_perm (n : Perm (Fin 7)) (hn : n ∈ alternatingGroup (Fin 7))
    (a₁ a₂ b₁ b₂ : Fin 3) (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (ha : n * pw a₁ a₂ * n⁻¹ = (pw a₁ a₂)⁻¹) (hb : n * pw b₁ b₂ * n⁻¹ = pw b₁ b₂) : False := by
  have hmemA : pw a₁ a₂ ∈ E9 := (mem_E9_iff _).2 ⟨a₁, a₂, rfl⟩
  have hmemB : pw b₁ b₂ ∈ E9 := (mem_E9_iff _).2 ⟨b₁, b₂, rfl⟩
  have ha' : n * pw a₁ a₂ * n⁻¹ ∈ E9 := by rw [ha]; exact inv_mem hmemA
  have hb' : n * pw b₁ b₂ * n⁻¹ ∈ E9 := by rw [hb]; exact hmemB
  have hN : n ∈ Subgroup.normalizer E9 := mem_normalizer_E9_of_basis n a₁ a₂ b₁ b₂ hdet ha' hb'
  obtain ⟨A, B, C, D, hdetF, hxAC, hyBD⟩ := det_of_mem n hn hN
  have hcA := conj_pw n A B C D hxAC hyBD a₁ a₂
  have hcB := conj_pw n A B C D hxAC hyBD b₁ b₂
  have e1 : pw (a₁.val • A + a₂.val • B) (a₁.val • C + a₂.val • D) = pw (-a₁) (-a₂) := by
    rw [← hcA, ha, pw_inv]
  have e2 : pw (b₁.val • A + b₂.val • B) (b₁.val • C + b₂.val • D) = pw b₁ b₂ := by
    rw [← hcB, hb]
  obtain ⟨e1a, e1b⟩ := pw_inj e1
  obtain ⟨e2a, e2b⟩ := pw_inj e2
  exact core_false A B C D a₁ a₂ b₁ b₂ hdetF hdet e1a e1b e2a e2b

theorem core_perm_of_not_zpowers (n a b : Perm (Fin 7)) (hn : n ∈ alternatingGroup (Fin 7))
    (ha : a ∈ E9) (hb : b ∈ E9) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a)
    (hna : n * a * n⁻¹ = a⁻¹) (hnb : n * b * n⁻¹ = b) : False := by
  obtain ⟨a₁, a₂, rfl⟩ := (mem_E9_iff a).1 ha
  obtain ⟨b₁, b₂, rfl⟩ := (mem_E9_iff b).1 hb
  have hdet : a₁ * b₂ - a₂ * b₁ ≠ 0 := by
    intro h0
    have hne : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
      by_contra hc
      simp only [not_or, not_not] at hc
      exact ha1 (by rw [hc.1, hc.2, pw_zero_zero])
    obtain ⟨k, hk1, hk2⟩ := indep_of_det_zero a₁ a₂ b₁ b₂ hne h0
    apply hba
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(k.val : ℤ), ?_⟩
    rw [zpow_natCast, pw_pow, hk1, hk2]
  exact core_perm n hn a₁ a₂ b₁ b₂ hdet hna hnb

theorem row6b_false : ∀ (X : Type) [Group X], CFSG.Quasithin.IsAlt 7 X → ∀ E : Subgroup X,
    Nat.card E = 9 → ∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ∉ Subgroup.zpowers a → ∀ n : X,
    n * a * n⁻¹ = a⁻¹ → n * b * n⁻¹ = b → False := by
  intro X _ hX E hE a ha b hb ha1 hba n hna hnb
  obtain ⟨f⟩ := hX
  let ψ : X →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp f.toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => f.injective (Subtype.ext h)
  have hcard : Nat.card (E.map ψ) = 9 := by
    rw [Subgroup.card_map_of_injective hψ, hE]
  obtain ⟨g, hg⟩ := exists_conj_le_E9 (E.map ψ) hcard
  have hmap : ∀ x ∈ E, g * ψ x * g⁻¹ ∈ E9 := fun x hx => hg (ψ x) (Subgroup.mem_map_of_mem ψ hx)
  have hψn : ∀ x : X, ψ x ∈ alternatingGroup (Fin 7) := fun x => (f x).2
  refine core_perm_of_not_zpowers (g * ψ n * g⁻¹) (g * ψ a * g⁻¹) (g * ψ b * g⁻¹)
    (Subgroup.Normal.conj_mem inferInstance (ψ n) (hψn n) g) (hmap a ha) (hmap b hb) ?_ ?_ ?_ ?_
  ·
    intro h
    apply ha1
    apply hψ
    rw [map_one]
    calc ψ a = g⁻¹ * (g * ψ a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  ·
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    apply hba
    rw [conj_zpow] at hk
    have h1 : ψ a ^ k = ψ b := by
      calc ψ a ^ k = g⁻¹ * (g * ψ a ^ k * g⁻¹) * g := by group
        _ = g⁻¹ * (g * ψ b * g⁻¹) * g := by rw [hk]
        _ = ψ b := by group
    refine Subgroup.mem_zpowers_iff.2 ⟨k, hψ ?_⟩
    rw [map_zpow]
    exact h1
  ·
    have h1 : ψ n * ψ a * (ψ n)⁻¹ = (ψ a)⁻¹ := by
      have := congrArg ψ hna
      simp only [map_mul, map_inv] at this
      exact this
    calc g * ψ n * g⁻¹ * (g * ψ a * g⁻¹) * (g * ψ n * g⁻¹)⁻¹
        = g * (ψ n * ψ a * (ψ n)⁻¹) * g⁻¹ := by group
      _ = g * (ψ a)⁻¹ * g⁻¹ := by rw [h1]
      _ = (g * ψ a * g⁻¹)⁻¹ := by group
  ·
    have h2 : ψ n * ψ b * (ψ n)⁻¹ = ψ b := by
      have := congrArg ψ hnb
      simp only [map_mul, map_inv] at this
      exact this
    calc g * ψ n * g⁻¹ * (g * ψ b * g⁻¹) * (g * ψ n * g⁻¹)⁻¹
        = g * (ψ n * ψ b * (ψ n)⁻¹) * g⁻¹ := by group
      _ = g * ψ b * g⁻¹ := by rw [h2]

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6Inv

end
