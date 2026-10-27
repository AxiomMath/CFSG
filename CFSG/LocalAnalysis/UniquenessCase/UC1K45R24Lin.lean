module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45GenPair
public import CFSG.HardMathSupport.U4FF.SmallGL
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
variable {B : LinearMap.BilinForm (ZMod 2) W}

@[expose] noncomputable def fixedSpace (ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W))
    (g : ↥(alternatingGroup (Fin 5))) : Submodule (ZMod 2) W :=
  LinearMap.ker ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)

@[expose] noncomputable def commSpace (ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W))
    (g : ↥(alternatingGroup (Fin 5))) : Submodule (ZMod 2) W :=
  LinearMap.range ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)

theorem mem_fixedSpace {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    {g : ↥(alternatingGroup (Fin 5))} {w : W} :
    w ∈ fixedSpace ρ g ↔ ρ g w = w := by
  simp [fixedSpace, sub_eq_zero]

theorem mem_commSpace {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    {g : ↥(alternatingGroup (Fin 5))} {w : W} :
    w ∈ commSpace ρ g ↔ ∃ v, ρ g v - v = w := by
  simp [commSpace]

theorem fixedSpace_eq_orthogonal_commSpace {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    (hB : B.Nondegenerate) (hiso : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (g : ↥(alternatingGroup (Fin 5))) :
    fixedSpace ρ g = B.orthogonal (commSpace ρ g) := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_fixedSpace]
  constructor
  · intro hv n hn
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hn
    have h := hiso g y v
    rw [hv] at h
    rw [map_sub, LinearMap.sub_apply, h, sub_self]
  · intro hv
    refine sub_eq_zero.mp (hB.2 (ρ g v - v) fun w => ?_)
    have hmem : w - (ρ g).symm w ∈ commSpace ρ g := by
      rw [mem_commSpace]
      exact ⟨(ρ g).symm w, by simp⟩
    have hw : B (w - (ρ g).symm w) v = 0 := hv _ hmem
    have hwv : B w v = B ((ρ g).symm w) v := by
      have h : B w v - B ((ρ g).symm w) v = 0 := by simpa [map_sub] using hw
      exact sub_eq_zero.mp h
    have hisov : B w (ρ g v) = B ((ρ g).symm w) v := by
      have h := hiso g ((ρ g).symm w) v
      simpa using h
    rw [map_sub, hisov, hwv, sub_self]

theorem fixedSpace_inf_eq_bot_of_closure_eq_top
    {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    {a b : ↥(alternatingGroup (Fin 5))}
    (hgen : Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin 5))) = ⊤) :
    fixedSpace ρ a ⊓ fixedSpace ρ b = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace] at hw
  refine h0 w fun x => ?_
  let H : Subgroup ↥(alternatingGroup (Fin 5)) :=
    { carrier := {x | ρ x w = w}
      one_mem' := by
        show ρ 1 w = w
        rw [map_one]
        rfl
      mul_mem' := by
        intro x y hx hy
        show ρ (x * y) w = w
        calc ρ (x * y) w = (ρ x * ρ y) w := by rw [map_mul]
          _ = ρ x (ρ y w) := rfl
          _ = ρ x w := by rw [hy]
          _ = w := hx
      inv_mem' := by
        intro x hx
        show ρ x⁻¹ w = w
        calc ρ x⁻¹ w = ρ x⁻¹ (ρ x w) := by rw [hx]
          _ = (ρ x⁻¹ * ρ x) w := rfl
          _ = w := by rw [map_inv, inv_mul_cancel]; rfl }
  have hle : Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin 5))) ≤ H := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hw.1
    · exact hw.2
  have hx : x ∈ Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin 5))) := by
    rw [hgen]
    exact Subgroup.mem_top x
  exact hle hx

theorem finrank_le_four {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    (hB : B.Nondegenerate) (hiso : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (hdim : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Module.finrank (ZMod 2) ↥(LinearMap.range ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2) :
    Module.finrank (ZMod 2) W ≤ 4 := by
  have hA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h3 : 3 ∣ Nat.card ↥(alternatingGroup (Fin 5)) := by rw [hA]; norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, hg⟩ := a5_conj_gen a ha
  let b : ↥(alternatingGroup (Fin 5)) := g * a * g⁻¹
  have hb3 : orderOf b = 3 := by
    have hconj : orderOf (g * a * g⁻¹) = orderOf a :=
      (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm
    exact hconj.trans ha
  have hgen : Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin 5))) = ⊤ := by
    have hset : ({a, b} : Set ↥(alternatingGroup (Fin 5))) = {a, g * a * g⁻¹} := by
      simp [b]
    rw [hset, hg]
  have hbot : fixedSpace ρ a ⊓ fixedSpace ρ b = ⊥ :=
    fixedSpace_inf_eq_bot_of_closure_eq_top (ρ := ρ) h0 hgen
  have h1a := fixedSpace_eq_orthogonal_commSpace (ρ := ρ) hB hiso a
  have h1b := fixedSpace_eq_orthogonal_commSpace (ρ := ρ) hB hiso b
  have hortho : B.orthogonal (commSpace ρ a ⊔ commSpace ρ b) = ⊥ := by
    have hsup : B.orthogonal (commSpace ρ a ⊔ commSpace ρ b) =
        B.orthogonal (commSpace ρ a) ⊓ B.orthogonal (commSpace ρ b) :=
      Submodule.orthogonalBilin_sup (commSpace ρ a) (commSpace ρ b) (B := B)
    rw [hsup, ← h1a, ← h1b]
    exact hbot
  have hdimW : Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) ↥(commSpace ρ a ⊔ commSpace ρ b) := by
    have h := LinearMap.BilinForm.finrank_orthogonal (B := B) hB
      (commSpace ρ a ⊔ commSpace ρ b)
    rw [hortho, finrank_bot] at h
    have hle := Submodule.finrank_le (commSpace ρ a ⊔ commSpace ρ b)
    omega
  have hsum : Module.finrank (ZMod 2) ↥(commSpace ρ a ⊔ commSpace ρ b) ≤
      Module.finrank (ZMod 2) (commSpace ρ a) +
        Module.finrank (ZMod 2) (commSpace ρ b) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  rw [show Module.finrank (ZMod 2) ↥(commSpace ρ a) = 2 from hdim a ha,
    show Module.finrank (ZMod 2) ↥(commSpace ρ b) = 2 from hdim b hb3] at hsum
  omega

theorem finrank_eq_four {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    (hB : B.Nondegenerate) (hiso : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (hρ : Function.Injective ρ) (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (hdim : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Module.finrank (ZMod 2) ↥(LinearMap.range ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2) :
    Module.finrank (ZMod 2) W = 4 := by
  have hle := finrank_le_four (ρ := ρ) hB hiso h0 hdim
  have hA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h5 : 5 ∣ Nat.card ↥(alternatingGroup (Fin 5)) := by rw [hA]; norm_num
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hx5 : orderOf (ρ x) = 5 := (orderOf_injective ρ hρ x).trans hx
  have h5dvd : 5 ∣ Nat.card (W ≃ₗ[ZMod 2] W) := by
    rw [← hx5]
    exact orderOf_dvd_natCard (ρ x)
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank (ZMod 2) W = n := ⟨_, rfl⟩
  have hcardGL : Nat.card (W ≃ₗ[ZMod 2] W) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) :=
    CFSG.HardMathSupport.U4FF.card_linearEquiv_eq_prod hn
  rw [hcardGL] at h5dvd
  have hn4 : n ≤ 4 := by rw [← hn]; exact hle
  have hnot3 : ¬ n ≤ 3 := by
    intro h3
    have h : ¬ 5 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
      interval_cases n <;> decide
    exact h h5dvd
  have hn_eq : n = 4 := by omega
  rw [hn, hn_eq]

theorem finrank_fixedSpace {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    (hdim : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Module.finrank (ZMod 2) ↥(LinearMap.range ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2)
    (hfin : Module.finrank (ZMod 2) W = 4)
    (g : ↥(alternatingGroup (Fin 5))) (hg : orderOf g = 3) :
    Module.finrank (ZMod 2) (fixedSpace ρ g) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)
  rw [hdim g hg, hfin] at h
  have h2 : (2 : ℕ) + Module.finrank (ZMod 2)
      (LinearMap.ker ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 + 2 := by
    simpa using h
  change Module.finrank (ZMod 2)
    (LinearMap.ker ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2
  exact Nat.add_left_cancel h2

theorem card_fixedSpace {ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)}
    (hdim : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Module.finrank (ZMod 2) ↥(LinearMap.range ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2)
    (hfin : Module.finrank (ZMod 2) W = 4)
    (g : ↥(alternatingGroup (Fin 5))) (hg : orderOf g = 3) :
    Nat.card {w : W // ρ g w = w} = 4 := by
  have hfr := finrank_fixedSpace (ρ := ρ) hdim hfin g hg
  have heq : {w : W // ρ g w = w} ≃ ↥(fixedSpace ρ g) :=
    Equiv.subtypeEquivRight (fun w => (mem_fixedSpace (ρ := ρ) (g := g) (w := w)).symm)
  rw [Nat.card_congr heq,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixedSpace ρ g)), Nat.card_zmod, hfr]
  norm_num

theorem a5_module_card_sixteen (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.Nondegenerate) (hAlt : B.IsAlt)
    (ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ)
    (hiso : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (hdim : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Module.finrank (ZMod 2) ↥(LinearMap.range ((ρ g : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2) :
    Nat.card W = 16 ∧ ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Nat.card {w : W // ρ g w = w} = 4 := by
  have hfin : Module.finrank (ZMod 2) W = 4 :=
    finrank_eq_four (ρ := ρ) hB hiso hρ h0 hdim
  have hcardW : Nat.card W = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod, hfin]
    norm_num
  exact ⟨hcardW, fun g hg => card_fixedSpace (ρ := ρ) hdim hfin g hg⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

end
