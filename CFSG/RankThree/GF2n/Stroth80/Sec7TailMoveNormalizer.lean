module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrameAPI
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNormalizerBound

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] [Finite X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem natCard_conjSubgroup (g : X) (T : Subgroup X) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem MoveFrame.normalizer_move (F : MoveFrame B φ V L Nb Rb Tt q) (s g : X) (hs : s ∈ V)
    (hs1 : s ≠ 1) (ht : g * s * g⁻¹ ∈ L) (htV : g * s * g⁻¹ ∉ V)
    (hcomm : ∀ l ∈ L, ∀ v ∈ conjSubgroup g V, l * v = v * l)
    (hLNb : ∀ l ∈ L, l ∈ conjSubgroup g Nb) :
    ∃ n ∈ normalizer (L : Set X), n ∉ normalizer (V : Set X) := by
  have hVVg : V ⊓ conjSubgroup g V = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨a, ha, rfl⟩ := mem_conjSubgroup_iff'.mp hzC
    by_contra hne
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hne (by simp)
    have hgN := F.ti g a ha ha1 hzV
    exact htV ((Subgroup.mem_normalizer_iff.mp hgN s).mp hs)
  have hV1 : V ≠ ⊥ := by
    intro hV
    obtain ⟨a, ha, ha1⟩ := F.exists_ne_one
    rw [hV, Subgroup.mem_bot] at ha
    exact ha1 ha
  have hLN : L ≤ conjSubgroup g Nb := fun l hl => hLNb l hl
  have hVgN : conjSubgroup g V ≤ conjSubgroup g Nb := by
    intro z hz
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hz ⊢
    exact F.L_le_Nb (F.V_le_L hz)
  have hVgab : ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup g V, a * b = b * a := by
    intro a ha b hb
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at ha hb
    have h := F.V_comm _ ha _ hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = b * a := by group
  have hbound : ∀ A : Subgroup X, A ≤ conjSubgroup g Nb →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 5 := by
    intro A hA hAab
    have hA' : conjSubgroup g⁻¹ A ≤ Nb := by
      intro x hx
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv] at hx
      have h2 := hA hx
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at h2
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e] at h2
      exact h2
    have hab' : ∀ a ∈ conjSubgroup g⁻¹ A, ∀ b ∈ conjSubgroup g⁻¹ A, a * b = b * a := by
      intro a ha b hb
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, inv_inv] at ha hb
      have h := hAab _ ha _ hb
      calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
        _ = b * a := by group
    have h := F.Nb_bound _ hA' hab'
    rwa [natCard_conjSubgroup g⁻¹ A] at h
  have hZ : ∀ z ∈ conjSubgroup g Nb, (∀ n ∈ conjSubgroup g Nb, z * n = n * z) →
      z ∈ conjSubgroup g V := by
    intro z hz hcen
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hz ⊢
    refine F.Nb_center _ hz (fun n hn => ?_)
    have hn' : g * n * g⁻¹ ∈ conjSubgroup g Nb := by
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      have e : g⁻¹ * (g * n * g⁻¹) * g = n := by group
      rw [e]
      exact hn
    have h := hcen _ hn'
    calc g⁻¹ * z * g * n = g⁻¹ * (z * (g * n * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * n * g⁻¹) * z) * g := by rw [h]
      _ = n * (g⁻¹ * z * g) := by group
  have hcomm' : ∀ a ∈ conjSubgroup g Nb, ∀ b ∈ conjSubgroup g Nb,
      ⁅a, b⁆ ∈ conjSubgroup g V := by
    intro a ha b hb
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at ha hb ⊢
    have h := F.Nb_comm _ ha _ hb
    have e : g⁻¹ * ⁅a, b⁆ * g = ⁅g⁻¹ * a * g, g⁻¹ * b * g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h
  have hp : IsPGroup 2 ↥(conjSubgroup g Nb) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp F.Nb_pgroup
    exact IsPGroup.of_card (n := n) ((natCard_conjSubgroup g Nb).trans hn)
  have hnorm := normalizer_of_abelian_bound V L (conjSubgroup g Nb) (conjSubgroup g V) q
    hVVg hV1 F.L_comm F.L_card F.V_le_L hLN hVgN hcomm hVgab hbound hZ hcomm' hp
  obtain ⟨hpart2, hpart3⟩ := hnorm
  push Not at hpart3
  obtain ⟨n, hnNb, hnV⟩ := hpart3
  exact ⟨n, hpart2 n hnNb, hnV⟩

end CFSG.RankThree.GF2n.Stroth80
