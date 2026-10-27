module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSyl27
public import CFSG.RankThree.PartTwo.Sec12.Item123
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open Subgroup

section Dichotomy

variable {Y : Type} [Group Y] [Finite Y]

theorem eInvFour_of_conj_four {Ē : Subgroup (MulAut Y)} {g : Y} {B : Subgroup Y}
    (hrange : ∀ σ ∈ Ē, ∃ x : Y, MulAut.conj x = σ)
    (hBiff : ∀ x : Y, MulAut.conj x ∈ Ē ↔ g * x * g⁻¹ ∈ B) {W : Subgroup Y}
    (hWab : IsElemAbelian 2 W) (hW4 : Nat.card W = 4)
    (hWinv : ∀ b ∈ B, ∀ w ∈ W, b * w * b⁻¹ ∈ W) (hmove : ∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ ≠ w) :
    EInvFour Y Ē := by
  obtain ⟨b, hb, w, hw, hne⟩ := hmove
  set W' : Subgroup Y := W.map (MulAut.conj g⁻¹).toMonoidHom with hW'
  have hmem : ∀ v, v ∈ W' ↔ ∃ w ∈ W, g⁻¹ * w * g = v := by
    intro v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  refine ⟨W', CFSG.Open.IsElemAbelian.map hWab _, ?_, ?_, ?_⟩
  · rw [hW', Subgroup.card_map_of_injective (show Function.Injective
      (MulAut.conj g⁻¹).toMonoidHom from (MulAut.conj g⁻¹).injective), hW4]
  · intro σ hσ v hv
    obtain ⟨w', hw', rfl⟩ := (hmem v).mp hv
    obtain ⟨x, hx⟩ := hrange σ hσ
    have hxB : g * x * g⁻¹ ∈ B := (hBiff x).mp (hx ▸ hσ)
    rw [← hx]
    refine (hmem _).mpr ⟨(g * x * g⁻¹) * w' * (g * x * g⁻¹)⁻¹, hWinv _ hxB w' hw', ?_⟩
    simp only [MulAut.conj_apply]
    group
  · have hxB : g * (g⁻¹ * b * g) * g⁻¹ ∈ B := by
      have : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [this]
      exact hb
    refine ⟨MulAut.conj (g⁻¹ * b * g), (hBiff _).mpr hxB, g⁻¹ * w * g,
      (hmem _).mpr ⟨w, hw, rfl⟩, fun h => hne ?_⟩
    simp only [MulAut.conj_apply] at h
    have h2 : g * (g⁻¹ * b * g * (g⁻¹ * w * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
        g * (g⁻¹ * w * g) * g⁻¹ := by rw [h]
    calc b * w * b⁻¹ = g * (g⁻¹ * b * g * (g⁻¹ * w * g) * (g⁻¹ * b * g)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * w * g) * g⁻¹ := h2
      _ = w := by group

theorem eInvFour_of_bad_inner (hZ : Subgroup.center Y = ⊥) {Ē Ū : Subgroup (MulAut Y)}
    (hd : BarData Y Ē Ū) {g : Y} {B : Subgroup Y} {x y : Y} (hxB : x ∈ B) (hyB : y ∈ B)
    (hrange : ∀ σ ∈ Ē, ∃ x : Y, MulAut.conj x = σ)
    (hBiff : ∀ x : Y, MulAut.conj x ∈ Ē ↔ g * x * g⁻¹ ∈ B)
    (hUrange : Ū ≤ (MulAut.conj : Y →* MulAut Y).range)
    (hBad : ∀ u : Y, u * u = 1 → u ≠ 1 → ¬ (u * x = x * u ∧ u * y = y * u)) :
    EInvFour Y Ē := by
  have hconjinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    Item211LieProof.conj_injective_of_center_eq_bot hZ
  set U : Subgroup Y := Ū.comap (MulAut.conj : Y →* MulAut Y) with hU
  have hUcard : Nat.card U = Nat.card Ū := Item211LieProof.card_comap_conj hZ hUrange
  have hmemU : ∀ w : Y, w ∈ U ↔ MulAut.conj w ∈ Ū := fun w => Iff.rfl
  obtain ⟨w, hwU, hw1⟩ : ∃ w ∈ U, w ≠ 1 := by
    obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hd.ne_bot
    obtain ⟨w, hw⟩ := hUrange hσ
    refine ⟨w, ?_, fun h => hσ1 ?_⟩
    · rw [hmemU, hw]
      exact hσ
    · apply Subtype.ext
      change σ = 1
      rw [← hw, h, map_one]
  have hUsq : ∀ w ∈ U, w * w = 1 := by
    intro w hw
    apply hconjinj
    rw [map_mul, map_one, ← sq]
    exact hd.elem2.2 _ hw
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    apply hconjinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hd.elem2.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  have hUinv : ∀ σ ∈ Ē, ∀ v ∈ U, σ v ∈ U := by
    intro σ hσ v hv
    obtain ⟨x₀, rfl⟩ := hrange σ hσ
    have hnorm := (Subgroup.mem_normalizer_iff.mp (hd.norm hσ)) (MulAut.conj v)
    have := hnorm.mp hv
    rw [hmemU, MulAut.conj_apply]
    simpa [map_mul, map_inv] using this
  have hmoved : ∀ w' ∈ U, w' ≠ 1 → ∃ σ ∈ Ē, σ w' ≠ w' := by
    intro w' hw'U hw'1
    have hu2 : (g * w' * g⁻¹) * (g * w' * g⁻¹) = 1 := by
      calc (g * w' * g⁻¹) * (g * w' * g⁻¹) = g * (w' * w') * g⁻¹ := by group
        _ = 1 := by rw [hUsq w' hw'U]; group
    have hu1 : g * w' * g⁻¹ ≠ 1 := by
      intro h
      apply hw'1
      have : w' = g⁻¹ * (g * w' * g⁻¹) * g := by group
      rw [this, h]
      group
    have hnc := hBad _ hu2 hu1
    obtain ⟨z, hzB, hz⟩ : ∃ z ∈ B, (g * w' * g⁻¹) * z ≠ z * (g * w' * g⁻¹) := by
      by_contra hcon
      push Not at hcon
      exact hnc ⟨hcon x hxB, hcon y hyB⟩
    have hzB' : g * (g⁻¹ * z * g) * g⁻¹ ∈ B := by
      have : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rw [this]
      exact hzB
    refine ⟨MulAut.conj (g⁻¹ * z * g), (hBiff _).mpr hzB', fun h => hz ?_⟩
    simp only [MulAut.conj_apply] at h
    have hc : (g⁻¹ * z * g) * w' = w' * (g⁻¹ * z * g) := by
      calc (g⁻¹ * z * g) * w' = (g⁻¹ * z * g * w' * (g⁻¹ * z * g)⁻¹) * (g⁻¹ * z * g) := by
            group
        _ = w' * (g⁻¹ * z * g) := by rw [h]
    calc (g * w' * g⁻¹) * z = g * (w' * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * w') * g⁻¹ := by rw [hc]
      _ = z * (g * w' * g⁻¹) := by group
  obtain ⟨σ, hσ, hmv⟩ := hmoved w hwU hw1
  have hσwU : σ w ∈ U := hUinv σ hσ w hwU
  have hσw1 : σ w ≠ 1 := fun h => hw1 (σ.injective (h.trans (map_one σ).symm))
  have hUp : IsPGroup 2 U := fun u => ⟨1, Subtype.ext (by simpa [pow_two] using hUsq u.1 u.2)⟩
  have h3 : 3 ≤ Nat.card U := by
    let f : Fin 3 → U := ![1, ⟨w, hwU⟩, ⟨σ w, hσwU⟩]
    have h01 : (1 : U) ≠ ⟨w, hwU⟩ := fun h => hw1 (congrArg Subtype.val h).symm
    have h02 : (1 : U) ≠ ⟨σ w, hσwU⟩ := fun h => hσw1 (congrArg Subtype.val h).symm
    have h12 : (⟨w, hwU⟩ : U) ≠ ⟨σ w, hσwU⟩ := fun h => hmv (congrArg Subtype.val h).symm
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso; simp only [f] at hij; simp_all)
        | (exfalso; simp only [f] at hij; exact h01 hij)
        | (exfalso; simp only [f] at hij; exact h01 hij.symm)
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hU4 : Nat.card U = 4 := by
    obtain ⟨m, hm⟩ := hUp.exists_card_eq
    have hle : Nat.card U ≤ 4 := hUcard ▸ hd.card_le
    rw [hm] at h3 hle ⊢
    rcases m with _ | _ | _ | m
    · norm_num at h3
    · norm_num at h3
    · norm_num
    · exfalso
      have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
      have := Nat.one_le_two_pow (n := m)
      omega
  exact ⟨U, isElemAbelian_of_comm_exp hUcomm (fun x hx => by rw [pow_two]; exact hUsq x hx),
    hU4, hUinv, σ, hσ, w, hwU, hmv⟩

theorem eInvFourFact_of_sylow_dichotomy (hZ : Subgroup.center Y = ⊥)
    (hinn : ∀ α : MulAut Y, ∃ y : Y, α = MulAut.conj y) (P₀ : Sylow 3 Y)
    (H : ∀ x y : Y, x ∈ (P₀ : Subgroup Y) → y ∈ (P₀ : Subgroup Y) → x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x → x ≠ 1 → y ∉ zpowers x →
      FourDatum x y ∨ ∀ u : Y, u * u = 1 → u ≠ 1 → ¬ (u * x = x * u ∧ u * y = y * u)) :
    EInvFourFact Y := by
  intro Ē Ū hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, B, hBle, hBexp, hB9, hrange, hBiff⟩ :=
    exists_sylow_conj_inner hZ (fun α _ => hinn α) P₀ hd.elem3 hd.card9
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := B)
      (by rw [hB9]; norm_num)).is_comm.comm
    intro a ha b hb
    exact congrArg Subtype.val (this ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hcon
    rw [this, Subgroup.card_bot] at hB9
    omega
  have hxord : orderOf x = 3 := orderOf_eq_prime (hBexp x hxB) hx1
  obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ B, y ∉ zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ zpowers x := fun b hb => hcon b hb
    have := Subgroup.card_le_of_le hle
    rw [hB9, Nat.card_zpowers, hxord] at this
    omega
  have hKB := Sec12.closure_pair_eq_of_card_nine hBexp hB9 hxB hx1 hyB hyx
  rcases H x y (hBle hxB) (hBle hyB) (hBexp x hxB) (hBexp y hyB) (hBcomm x hxB y hyB) hx1 hyx
    with hF | hBad
  · obtain ⟨W, hWab, hW4, hWinv, e, he, w, hw, hne⟩ := hF.exists_four
    rw [hKB] at hWinv he
    exact eInvFour_of_conj_four hrange hBiff hWab hW4 hWinv ⟨e, he, w, hw, hne⟩
  · exact eInvFour_of_bad_inner hZ hd hxB hyB hrange hBiff
      (fun σ _ => by
        obtain ⟨y, hy⟩ := hinn σ
        exact ⟨y, hy.symm⟩) hBad

theorem mul_mul_inv_mem_range_conj {a c : MulAut Y}
    (hc : c ∈ (MulAut.conj : Y →* MulAut Y).range) :
    a * c * a⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨y, rfl⟩ := hc
  refine ⟨a y, ?_⟩
  ext z
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem le_range_conj_of_moved {Ē Ū : Subgroup (MulAut Y)} (hU2 : IsElemAbelian 2 Ū)
    (hne : Ū ≠ ⊥) (hle : Nat.card Ū ≤ 4) (hE : ∀ ε ∈ Ē, ∃ y : Y, MulAut.conj y = ε)
    (hnorm : ∀ ε ∈ Ē, ∀ σ ∈ Ū, ε * σ * ε⁻¹ ∈ Ū)
    (hmoved : ∀ σ ∈ Ū, σ ≠ 1 → ∃ ε ∈ Ē, ε * σ * ε⁻¹ ≠ σ) :
    Ū ≤ (MulAut.conj : Y →* MulAut Y).range := by
  set Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range with hInn
  have hEInn : ∀ ε ∈ Ē, ε ∈ Inn := fun ε hε => by
    obtain ⟨y, hy⟩ := hE ε hε
    exact ⟨y, hy⟩
  have hsq : ∀ σ ∈ Ū, σ * σ = 1 := fun σ hσ => by
    rw [← sq]
    exact hU2.2 σ hσ
  have hcomm : ∀ a ∈ Ū, ∀ b ∈ Ū, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hU2.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hconjsq : ∀ ε ∈ Ē, ∀ σ ∈ Ū, (ε * σ * ε⁻¹) * (ε * σ * ε⁻¹) = 1 := fun ε _ σ hσ => by
    calc (ε * σ * ε⁻¹) * (ε * σ * ε⁻¹) = ε * (σ * σ) * ε⁻¹ := by group
      _ = 1 := by rw [hsq σ hσ]; group
  obtain ⟨⟨σ₀, hσ₀⟩, hσ₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hσ₀1' : σ₀ ≠ 1 := fun h => hσ₀1 (Subtype.ext h)
  obtain ⟨ε₀, hε₀, hmv₀⟩ := hmoved σ₀ hσ₀ hσ₀1'
  set σ₁ : MulAut Y := ε₀ * σ₀ * ε₀⁻¹ with hσ₁
  have hσ₁U : σ₁ ∈ Ū := hnorm ε₀ hε₀ σ₀ hσ₀
  have hσ₁1 : σ₁ ≠ 1 := by
    intro h
    apply hσ₀1'
    have : σ₀ = ε₀⁻¹ * σ₁ * ε₀ := by rw [hσ₁]; group
    rw [this, h]
    group
  have hσ₀inv : σ₀⁻¹ = σ₀ := inv_eq_of_mul_eq_one_right (hsq σ₀ hσ₀)
  have hτInn : σ₀ * σ₁ ∈ Inn := by
    have hc : ε₀ * (σ₀ * ε₀⁻¹ * σ₀⁻¹) ∈ Inn :=
      Inn.mul_mem (hEInn ε₀ hε₀) (mul_mul_inv_mem_range_conj (Inn.inv_mem (hEInn ε₀ hε₀)))
    have := mul_mul_inv_mem_range_conj (a := σ₀) hc
    have heq : σ₀ * (ε₀ * (σ₀ * ε₀⁻¹ * σ₀⁻¹)) * σ₀⁻¹ = σ₀ * σ₁ := by
      calc σ₀ * (ε₀ * (σ₀ * ε₀⁻¹ * σ₀⁻¹)) * σ₀⁻¹
          = σ₀ * (ε₀ * σ₀ * ε₀⁻¹) * (σ₀⁻¹ * σ₀⁻¹) := by group
        _ = σ₀ * σ₁ := by rw [hσ₀inv, hsq σ₀ hσ₀, mul_one]
    rwa [heq] at this
  have hτU : σ₀ * σ₁ ∈ Ū := Ū.mul_mem hσ₀ hσ₁U
  have hτ1 : σ₀ * σ₁ ≠ 1 := by
    intro h
    apply hmv₀
    have : σ₁ = σ₀⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, hσ₀inv]
  obtain ⟨ε₃, hε₃, hmv₃⟩ := hmoved _ hτU hτ1
  set ρ : MulAut Y := ε₃ * (σ₀ * σ₁) * ε₃⁻¹ with hρ
  have hρU : ρ ∈ Ū := hnorm ε₃ hε₃ _ hτU
  have hρInn : ρ ∈ Inn := Inn.mul_mem (Inn.mul_mem (hEInn ε₃ hε₃) hτInn)
    (Inn.inv_mem (hEInn ε₃ hε₃))
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply hτ1
    have : σ₀ * σ₁ = ε₃⁻¹ * ρ * ε₃ := by rw [hρ]; group
    rw [this, h]
    group
  have hτsq : (σ₀ * σ₁) * (σ₀ * σ₁) = 1 := hsq _ hτU
  have hρsq : ρ * ρ = 1 := hconjsq ε₃ hε₃ _ hτU
  have hK4 : Nat.card (Subgroup.closure ({σ₀ * σ₁, ρ} : Set (MulAut Y))) = 4 :=
    card_closure_pair hτsq hρsq (hcomm _ hτU _ hρU) hτ1 hρ1 (Ne.symm hmv₃)
  have hKle : Subgroup.closure ({σ₀ * σ₁, ρ} : Set (MulAut Y)) ≤ Ū := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact hτU
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hρU
  have hKeq : Subgroup.closure ({σ₀ * σ₁, ρ} : Set (MulAut Y)) = Ū :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hK4]; exact hle)
  rw [← hKeq, Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | hz
  · exact hτInn
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hρInn

theorem eInvFourFact_of_sylow_dichotomy_aut (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y) (P₀ : Sylow 3 Y)
    (H : ∀ x y : Y, x ∈ (P₀ : Subgroup Y) → y ∈ (P₀ : Subgroup Y) → x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x → x ≠ 1 → y ∉ zpowers x →
      FourDatum x y ∨ ∀ τ : MulAut Y, τ * τ = 1 → τ ≠ 1 →
        ¬ (τ * MulAut.conj x = MulAut.conj x * τ ∧ τ * MulAut.conj y = MulAut.conj y * τ)) :
    EInvFourFact Y := by
  intro Ē Ū hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, B, hBle, hBexp, hB9, hrange, hBiff⟩ :=
    exists_sylow_conj_inner hZ hout P₀ hd.elem3 hd.card9
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := B)
      (by rw [hB9]; norm_num)).is_comm.comm
    intro a ha b hb
    exact congrArg Subtype.val (this ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hcon
    rw [this, Subgroup.card_bot] at hB9
    omega
  have hxord : orderOf x = 3 := orderOf_eq_prime (hBexp x hxB) hx1
  obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ B, y ∉ zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ zpowers x := fun b hb => hcon b hb
    have := Subgroup.card_le_of_le hle
    rw [hB9, Nat.card_zpowers, hxord] at this
    omega
  have hKB := Sec12.closure_pair_eq_of_card_nine hBexp hB9 hxB hx1 hyB hyx
  rcases H x y (hBle hxB) (hBle hyB) (hBexp x hxB) (hBexp y hyB) (hBcomm x hxB y hyB) hx1 hyx
    with hF | hBad
  · obtain ⟨W, hWab, hW4, hWinv, e, he, w, hw, hne⟩ := hF.exists_four
    rw [hKB] at hWinv he
    exact eInvFour_of_conj_four hrange hBiff hWab hW4 hWinv ⟨e, he, w, hw, hne⟩
  · have hconjinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
      Item211LieProof.conj_injective_of_center_eq_bot hZ
    have hmoved : ∀ τ ∈ Ū, τ ≠ 1 → ∃ ε ∈ Ē, ε * τ * ε⁻¹ ≠ τ := by
      intro τ hτ hτ1
      set cg : MulAut Y := MulAut.conj g with hcg
      have hτ2 : τ * τ = 1 := by rw [← sq]; exact hd.elem2.2 τ hτ
      have hu2 : (cg * τ * cg⁻¹) * (cg * τ * cg⁻¹) = 1 := by
        calc (cg * τ * cg⁻¹) * (cg * τ * cg⁻¹) = cg * (τ * τ) * cg⁻¹ := by group
          _ = 1 := by rw [hτ2]; group
      have hu1 : cg * τ * cg⁻¹ ≠ 1 := by
        intro h
        apply hτ1
        have : τ = cg⁻¹ * (cg * τ * cg⁻¹) * cg := by group
        rw [this, h]
        group
      have hnc := hBad _ hu2 hu1
      obtain ⟨z, hzB, hz⟩ : ∃ z ∈ B, (cg * τ * cg⁻¹) * MulAut.conj z ≠
          MulAut.conj z * (cg * τ * cg⁻¹) := by
        by_contra hcon
        push Not at hcon
        exact hnc ⟨hcon x hxB, hcon y hyB⟩
      have hzB' : g * (g⁻¹ * z * g) * g⁻¹ ∈ B := by
        have : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
        rw [this]
        exact hzB
      refine ⟨MulAut.conj (g⁻¹ * z * g), (hBiff _).mpr hzB', fun h => hz ?_⟩
      have hcz : MulAut.conj z = cg * MulAut.conj (g⁻¹ * z * g) * cg⁻¹ := by
        rw [hcg, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      have hc : MulAut.conj (g⁻¹ * z * g) * τ = τ * MulAut.conj (g⁻¹ * z * g) := by
        calc MulAut.conj (g⁻¹ * z * g) * τ
            = (MulAut.conj (g⁻¹ * z * g) * τ * (MulAut.conj (g⁻¹ * z * g))⁻¹) *
                MulAut.conj (g⁻¹ * z * g) := by group
          _ = τ * MulAut.conj (g⁻¹ * z * g) := by rw [h]
      rw [hcz]
      calc (cg * τ * cg⁻¹) * (cg * MulAut.conj (g⁻¹ * z * g) * cg⁻¹)
          = cg * (τ * MulAut.conj (g⁻¹ * z * g)) * cg⁻¹ := by group
        _ = cg * (MulAut.conj (g⁻¹ * z * g) * τ) * cg⁻¹ := by rw [hc]
        _ = (cg * MulAut.conj (g⁻¹ * z * g) * cg⁻¹) * (cg * τ * cg⁻¹) := by group
    have hUrange : Ū ≤ (MulAut.conj : Y →* MulAut Y).range :=
      le_range_conj_of_moved hd.elem2 hd.ne_bot hd.card_le hrange
        (fun ε hε τ hτ => (Subgroup.mem_normalizer_iff.mp (hd.norm hε) τ).mp hτ) hmoved
    refine eInvFour_of_bad_inner hZ hd hxB hyB hrange hBiff hUrange ?_
    intro u hu2 hu1 ⟨hux, huy⟩
    refine hBad (MulAut.conj u) (by rw [← map_mul, hu2, map_one])
      (fun h => hu1 (hconjinj (by rw [h, map_one]))) ⟨?_, ?_⟩
    · rw [← map_mul, ← map_mul, hux]
    · rw [← map_mul, ← map_mul, huy]

end Dichotomy

end CFSG.RankThree.PartTwo.Sec21.Hering214
