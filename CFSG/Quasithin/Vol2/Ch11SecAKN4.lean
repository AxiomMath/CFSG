module

public import CFSG.Quasithin.Vol2.Ch11SecAKN2
public import CFSG.Quasithin.Vol2.Ch11SecAKN3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.AKN

open Matrix CFSG.SL2MinimalFaithful
open scoped commutatorElement

theorem exists_two_element_centralizer {Y : Type*} [Group Y] {F : Type*} [Field F] [Finite F]
    [CharP F 2] (hF : 2 < Nat.card F) {B₁ : Subgroup Y} (e : ↥B₁ ≃* SpecialLinearGroup (Fin 2) F)
    {S₁ : Subgroup Y} (hS₁ : IsPGroup 2 S₁) (hSB : S₁ ≤ Subgroup.normalizer (B₁ : Set Y))
    (hD : Nat.card ↥(S₁ ⊓ B₁) = Nat.card F) {s : Y} (hs : s ∈ S₁) (hsD : s ∉ S₁ ⊓ B₁)
    (hsc : ∀ d ∈ S₁ ⊓ B₁, s * d = d * s) :
    ∃ c : Y, c ≠ 1 ∧ (∃ k : ℕ, c ^ 2 ^ k = 1) ∧ ∀ b ∈ B₁, c * b = b * c := by
  set D := S₁ ⊓ B₁ with hDdef
  have hDB : D ≤ B₁ := inf_le_right
  set D' : Subgroup (SpecialLinearGroup (Fin 2) F) := (D.subgroupOf B₁).map e.toMonoidHom with hD'
  have hD'card : Nat.card D' = Nat.card F := by
    rw [hD', Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv, hD]
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hf' : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  obtain ⟨g₀, hg₀⟩ := exists_conj_unipotent_mem Nat.prime_two hf' hD'card
  have hsN : s ∈ Subgroup.normalizer (B₁ : Set Y) := hSB hs
  let σ : ↥B₁ →* ↥B₁ :=
    { toFun := fun b => ⟨s * b * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN b).mp b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hσ : ∀ b : ↥B₁, ((σ b : ↥B₁) : Y) = s * b * s⁻¹ := fun b => rfl
  let α : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F :=
    (MulAut.conj g₀⁻¹).toMonoidHom.comp (e.toMonoidHom.comp (σ.comp
      (e.symm.toMonoidHom.comp (MulAut.conj g₀).toMonoidHom)))
  have hαapply : ∀ x, α x = g₀⁻¹ * e (σ (e.symm (g₀ * x * g₀⁻¹))) * g₀ := fun x => by
    simp [α, MulAut.conj_apply]
  have hmemD' : ∀ t : F, ∃ d : ↥B₁, (d : Y) ∈ D ∧ e d = g₀ * unipotent t * g₀⁻¹ := by
    intro t
    obtain ⟨d, hd, hde⟩ := hg₀ t
    exact ⟨d, hd, hde⟩
  have hα : ∀ t, α (unipotent t) = unipotent t := by
    intro t
    obtain ⟨d, hdD, hde⟩ := hmemD' t
    have hσd : σ d = d := Subtype.ext (by
      rw [hσ, hsc _ hdD, mul_inv_cancel_right])
    rw [hαapply, ← hde, MulEquiv.symm_apply_apply, hσd, hde]
    group
  obtain ⟨c₀, hc₀⟩ := exists_eq_conj_of_fix hF α hα
  obtain ⟨d₀, hd₀D, hd₀e⟩ := hmemD' c₀
  have hconj : ∀ b : ↥B₁, s * (b : Y) * s⁻¹ = (d₀ : Y) * b * (d₀ : Y)⁻¹ := by
    intro b
    have h1 := hc₀ (g₀⁻¹ * e b * g₀)
    rw [hαapply, show g₀ * (g₀⁻¹ * e b * g₀) * g₀⁻¹ = e b by group,
      MulEquiv.symm_apply_apply] at h1
    have h2 : e (σ b) = e (d₀ * b * d₀⁻¹) := by
      rw [map_mul, map_mul, map_inv, hd₀e]
      calc e (σ b) = g₀ * (g₀⁻¹ * e (σ b) * g₀) * g₀⁻¹ := by group
        _ = g₀ * unipotent c₀ * g₀⁻¹ * e b * (g₀ * unipotent c₀ * g₀⁻¹)⁻¹ := by rw [h1]; group
    have h3 := congrArg Subtype.val (e.injective h2)
    rw [hσ] at h3
    simpa using h3
  refine ⟨(d₀ : Y)⁻¹ * s, ?_, ?_, ?_⟩
  · intro h1
    apply hsD
    have : s = d₀ := by
      calc s = (d₀ : Y) * ((d₀ : Y)⁻¹ * s) := by group
        _ = d₀ := by rw [h1, mul_one]
    rw [this]
    exact hd₀D
  · have hmem : (d₀ : Y)⁻¹ * s ∈ S₁ := S₁.mul_mem (S₁.inv_mem hd₀D.1) hs
    obtain ⟨k, hk⟩ := hS₁ ⟨_, hmem⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro b hb
    have h1 := hconj ⟨b, hb⟩
    simp only at h1
    calc (d₀ : Y)⁻¹ * s * b = (d₀ : Y)⁻¹ * (s * b * s⁻¹) * s := by group
      _ = b * ((d₀ : Y)⁻¹ * s) := by rw [h1]; group

theorem false_of_centralizer {K : Type*} [Field K] [CharP K 2] {Y Ŷ : Type*} [Group Y] [Group Ŷ]
    [Finite Ŷ] (π : Ŷ →* Y) (hπ : Function.Surjective π)
    (hcent : ∀ z ∈ π.ker, ∀ g : Ŷ, z * g = g * z) (hodd : Odd (Nat.card π.ker))
    (ι : Ŷ →* GL (Fin 3) K) (hι : Function.Injective ι) {B₁ : Subgroup Y}
    (hperf : ⁅B₁, B₁⁆ = B₁) (hB2 : ¬ IsPGroup 2 B₁) {c : Y} (hc1 : c ≠ 1) {k : ℕ}
    (hck : c ^ 2 ^ k = 1) (hcB : ∀ b ∈ B₁, c * b = b * c) : False := by
  obtain ⟨ĉ₀, hĉ₀⟩ := hπ c
  set N₀ := Nat.card π.ker with hN₀
  have hcop : Nat.Coprime N₀ (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  set ĉ := ĉ₀ ^ N₀ with hĉ
  have hπĉ : π ĉ = c ^ N₀ := by rw [hĉ, map_pow, hĉ₀]
  have hcN : c ^ N₀ ≠ 1 := by
    intro h
    have h1 : orderOf c ∣ N₀ := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
    exact hc1 (orderOf_eq_one_iff.mp
      ((Nat.Coprime.coprime_dvd_left h2 hcop.symm).eq_one_of_dvd h1))
  have hĉ2 : ĉ ^ 2 ^ k = 1 := by
    have hz : ĉ₀ ^ 2 ^ k ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hĉ₀, hck]
    have hzN : (ĉ₀ ^ 2 ^ k) ^ N₀ = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := π.ker) (x := ⟨_, hz⟩))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    rw [hĉ, ← pow_mul, mul_comm, pow_mul, hzN]
  have hcB' : ∀ b ∈ B₁, c ^ N₀ * b = b * c ^ N₀ := fun b hb =>
    (Commute.pow_left (hcB b hb) N₀).eq
  set Bl := B₁.comap π with hBl
  have hĉB : ∀ b ∈ Bl, ĉ * b = b * ĉ := by
    intro b hb
    obtain ⟨z, hz⟩ : ∃ z, z = ĉ * b * ĉ⁻¹ * b⁻¹ := ⟨_, rfl⟩
    have hzk : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, hπĉ,
        hcB' _ hb]
      group
    have hzc : ∀ g : Ŷ, z * g = g * z := hcent z hzk
    have key : ∀ j : ℕ, ĉ ^ j * b * (ĉ ^ j)⁻¹ = z ^ j * b := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have e1 : ĉ * b * ĉ⁻¹ = z * b := by rw [hz]; group
        calc ĉ ^ (j + 1) * b * (ĉ ^ (j + 1))⁻¹ = ĉ * (ĉ ^ j * b * (ĉ ^ j)⁻¹) * ĉ⁻¹ := by group
          _ = ĉ * (z ^ j * b) * ĉ⁻¹ := by rw [ih]
          _ = z ^ j * (ĉ * b * ĉ⁻¹) := by
            rw [show ĉ * (z ^ j * b) * ĉ⁻¹ = ĉ * z ^ j * b * ĉ⁻¹ by group,
              (Commute.pow_right (Commute.symm (hzc ĉ)) j).eq]
            group
          _ = z ^ (j + 1) * b := by rw [e1, pow_succ, mul_assoc]
    have h1 := key (2 ^ k)
    rw [hĉ2, one_mul, inv_one, mul_one, right_eq_mul] at h1
    have hzN : z ^ N₀ = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := π.ker) (x := ⟨_, hzk⟩))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    have hdvd1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have hdvd2 : orderOf z ∣ N₀ := orderOf_dvd_of_pow_eq_one hzN
    have hz1' : z = 1 := orderOf_eq_one_iff.mp
      ((Nat.Coprime.coprime_dvd_left hdvd1 hcop.symm).eq_one_of_dvd hdvd2)
    calc ĉ * b = z * (b * ĉ) := by rw [hz]; group
      _ = b * ĉ := by rw [hz1', one_mul]
  set H := Bl.map ι with hH
  have hHc : ∀ h ∈ H, h * ι ĉ = ι ĉ * h := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hĉB b hb]
  have hιĉ1 : ι ĉ ≠ 1 := by
    intro h
    apply hcN
    rw [← hπĉ, hι (h.trans (map_one ι).symm), map_one]
  have hιĉ2 : ι ĉ ^ 2 ^ k = 1 := by rw [← map_pow, hĉ2, map_one]
  apply hB2
  intro b
  refine ⟨2, ?_⟩
  have hb : (b : Y) ∈ ⁅B₁, B₁⁆ := by rw [hperf]; exact b.2
  have hmap : ⁅B₁, B₁⁆ = (⁅Bl, Bl⁆).map π := by
    rw [Subgroup.map_commutator, hBl, Subgroup.map_comap_eq_self_of_surjective hπ]
  rw [hmap] at hb
  obtain ⟨x, hx, hxb⟩ := hb
  have hιx : ι x ∈ ⁅H, H⁆ := by
    rw [hH, ← Subgroup.map_commutator]
    exact ⟨x, hx, rfl⟩
  have h4 := pow_four_eq_one_of_mem_commutator hιĉ1 hιĉ2 hHc hιx
  have hx4 : x ^ 4 = 1 := hι (by rw [map_pow, h4, map_one])
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hxb, ← map_pow, show 2 ^ 2 = 4 from rfl, hx4, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecA.AKN
