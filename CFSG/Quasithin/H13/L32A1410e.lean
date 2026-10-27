module

public import CFSG.Quasithin.H13.L32A1410b
public import CFSG.Quasithin.H13.L32NLem144Bb

public section

namespace CFSG.Quasithin.H13.Q1410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B Mat8Cert G5ACert
  L1442M

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {b : Bool}

structure CtxA (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (b : Bool) : Prop where
  base : Base G T L V V₂ g
  imgH : img8 D e (l32nH T V) = g5 b false
  imgT : img8 D e T = PA5 b

theorem relIndex_PA5 (b : Bool) : (PA5 b).relIndex (g5 b false) = 45 := by
  have h := Subgroup.relIndex_mul_card (PA5 b) (g5 b false)
  rw [inf_eq_left.mpr (PA5_le b), card_PA5, card_gA5] at h
  cases b <;> simp only [nPA, nGA, Bool.false_eq_true, ↓reduceIte] at h <;> omega

theorem exists_ctxA (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11) (h12812 : Lemma12_8_12_two)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) {e₀ : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (hiso : IsModelIso D (l32nH T V) e₀ (q5 false) (g5 b false)) :
    ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), CtxA G T L V V₂ g D e b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have B := exists_base h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP hgH
  have himgH := img8_eq_of_iso hiso
  have hT := B.card_imgT e₀ himgH (m := if b then 4 else 3) (k := 45)
    (by rw [card_gA5]; cases b <;> rfl) (by decide)
  have hP2 : IsPGroup 2 ↥(PA5 b) := IsPGroup.of_card (n := if b then 4 else 3)
    (by rw [card_PA5]; cases b <;> rfl)
  obtain ⟨e, himgH', -, himgT⟩ := B.exists_normalized e₀ himgH
    (F := fun x y => D.B (e₀.symm x) (e₀.symm y)) (fun x y => by simp) (PA5_le b) hP2
    (by rw [relIndex_PA5]; decide) (by rw [hT, card_PA5]; cases b <;> rfl)
  exact ⟨e, B, himgH', himgT⟩

namespace CtxA

variable (C : CtxA G T L V V₂ g D e b)
include C

theorem e_pi_a {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) : e (D.π a) = vec8 vA := by
  rcases eq_of_fixed_PA5 b (e (D.π a))
      (fun γ hγ => C.base.T_fix e ha haV (by rw [C.imgT]; exact hγ)) with h | h
  · exact absurd ((map_eq_zero_iff e e.injective).mp h) (C.base.pi_a_ne D ha haV)
  · exact h

end CtxA

end CFSG.Quasithin.H13.Q1410

end
