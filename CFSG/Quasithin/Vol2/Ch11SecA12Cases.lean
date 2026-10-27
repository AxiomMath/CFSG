module

public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedProj StatedScalars)
open scoped commutatorElement

section General

variable {X : Type*} [Group X]

theorem oPrimeResidualOf_top_normal (p : ℕ) : (oPrimeResidualOf p (⊤ : Subgroup X)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨-, k, hk⟩ := hy
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, k, ?_⟩
    rw [← MulAut.conj_apply]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).trans hk
  | one => simp
  | mul a b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    rwa [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group] at this
  | inv a _ ha =>
    have := Subgroup.inv_mem _ ha
    rwa [show (g * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ by group] at this

theorem mem_oPrimeResidualOf_top_of_pow {p : ℕ} (hp : p.Prime) {x : X} {m : ℕ}
    (hx : x ^ p ^ m = 1) : x ∈ oPrimeResidualOf p (⊤ : Subgroup X) := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hx)
  exact Subgroup.subset_closure ⟨Subgroup.mem_top _, k, hk⟩

theorem statedProj_top_mulEquiv (F : Type) [Field F] :
    Nonempty (StatedProj (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)) ≃*
      (Matrix.GeneralLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F))) := by
  refine ⟨QuotientGroup.congr _ _ Subgroup.topEquiv ?_⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩

end General

variable {H : Type} [Group H] [Finite H]

theorem card_map_three {A : Subgroup H} (hA : Nat.card A = 3) :
    Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f := (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp A.subtype with hf
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun a ha => ?_
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    have h2 : orderOf (a : H) ∣ 3 := hA ▸ Subgroup.orderOf_dvd_natCard A a.2
    have h3 : Nat.Coprime 3 (orderOf (a : H)) :=
      CFSG.pPrimeCore_coprime_card.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ ha)
    exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3.symm h2))
  have hrange : A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) = f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hA]

omit [Finite H] in
theorem not_map_le_starImage {K A : Subgroup H} (hO : CFSG.pPrimeCore 3 H ≤ K)
    (hAK : A ⊓ K = ⊥) (hA : A ≠ ⊥) :
    ¬ A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) ≤ starImage 3 K := by
  intro hle
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  obtain ⟨k, hk, hka⟩ := hle ⟨a, ha, rfl⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hka
  have haK : a ∈ K := by
    have := K.mul_mem hk (hO hka)
    rwa [mul_inv_cancel_left] at this
  have hbot : a ∈ A ⊓ K := ⟨ha, haK⟩
  rw [hAK, Subgroup.mem_bot] at hbot
  exact ha1 (Subtype.ext hbot)

theorem commutator_le_of_case3b {K A D : Subgroup H} (hO : CFSG.pPrimeCore 3 H ≤ K)
    (hA3 : Nat.card A = 3) (hAK : A ⊓ K = ⊥) (hDK : D ≤ K)
    (hDA : D ≤ Subgroup.centralizer (A : Set H)) (hb : A318Case3b (starImage 3 K)) :
    ⁅D, D⁆ ≤ CFSG.pPrimeCore 3 H := by
  obtain ⟨s, q, x, -, -, -, -, -, hcyc, -, hconj⟩ := hb
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ
  have hAne : A ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hA3
    norm_num at hA3
  obtain ⟨l, hl, hY⟩ := hconj (A.map π) (card_map_three hA3) (not_map_le_starImage hO hAK hAne)
  set C := starImage 3 K ⊓ Subgroup.centralizer ({x} : Set (PStar 3 H))
  have hcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    let _ := IsCyclic.commGroup (α := ↥C)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥C) ⟨b, hb⟩)
  have hmem : ∀ d ∈ D, l⁻¹ * π d * l ∈ C := by
    intro d hd
    refine ⟨(starImage 3 K).mul_mem ((starImage 3 K).mul_mem ((starImage 3 K).inv_mem hl)
      ⟨d, hDK hd, rfl⟩) hl, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro y rfl
    have hxY : l * y * l⁻¹ ∈ A.map π := by
      rw [hY, ← MulAut.conj_apply]
      exact ⟨y, Subgroup.mem_zpowers y, rfl⟩
    obtain ⟨a, ha, hax⟩ := hxY
    have hda : π a * π d = π d * π a := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hDA hd) a ha]
    rw [hax] at hda
    calc y * (l⁻¹ * π d * l) = l⁻¹ * ((l * y * l⁻¹) * π d) * l := by group
      _ = l⁻¹ * (π d * (l * y * l⁻¹)) * l := by rw [hda]
      _ = l⁻¹ * π d * l * y := by group
  rw [Subgroup.commutator_le]
  intro d₁ hd₁ d₂ hd₂
  have h1 := hcomm _ (hmem d₁ hd₁) _ (hmem d₂ hd₂)
  have h2 : π d₁ * π d₂ = π d₂ * π d₁ := by
    calc π d₁ * π d₂ = l * ((l⁻¹ * π d₁ * l) * (l⁻¹ * π d₂ * l)) * l⁻¹ := by group
      _ = l * ((l⁻¹ * π d₂ * l) * (l⁻¹ * π d₁ * l)) * l⁻¹ := by rw [h1]
      _ = π d₂ * π d₁ := by group
  have h3 : π ⁅d₁, d₂⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3

end CFSG.Quasithin.Vol2.Ch11.SecA
