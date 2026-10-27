module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cQ8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem mul_inv_mem_of_relIndex_two {H K : Subgroup D} (h2 : H.relIndex K = 2) {x y : D}
    (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x * y⁻¹ ∈ H := by
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff.mp h2
  have hxa : x * a ∈ H := by
    rcases ha x hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hxH
  have hya : y * a ∈ H := by
    rcases ha y hy with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hyH
  have e : x * y⁻¹ = (x * a) * (y * a)⁻¹ := by group
  rw [e]
  exact H.mul_mem hxa (H.inv_mem hya)

theorem comm_mem_of_relIndex_two {H K : Subgroup D} (h2 : H.relIndex K = 2) {g' : D}
    (hgH : g' ∈ Subgroup.normalizer (H : Set D)) (hgK : g' ∈ Subgroup.normalizer (K : Set D))
    {q : D} (hq : q ∈ K) : g' * q * g'⁻¹ * q⁻¹ ∈ H := by
  by_cases hqH : q ∈ H
  · exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp hgH q).mp hqH) (H.inv_mem hqH)
  · have hq' : g' * q * g'⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK q).mp hq
    have hq'H : g' * q * g'⁻¹ ∉ H := fun h => hqH ((Subgroup.mem_normalizer_iff.mp hgH q).mpr h)
    exact mul_inv_mem_of_relIndex_two h2 hq' hq hq'H hqH

structure AutCoh (A B T' : Subgroup D) : Prop where
  le : T' ≤ A ⊓ B
  idx : T'.relIndex (A ⊓ B) = 2
  not_le₁ : ¬ pCoreOf 2 A ≤ T'
  not_le₂ : ¬ pCoreOf 2 B ≤ T'
  norm₁ : A ≤ Subgroup.normalizer ((T' ⊓ pCoreOf 2 A : Subgroup D) : Set D)
  norm₂ : B ≤ Subgroup.normalizer ((T' ⊓ pCoreOf 2 B : Subgroup D) : Set D)

section CohG

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.card_QA' (hT : Nat.card ↥(A ⊓ B) = 128) : Nat.card ↥(pCoreOf 2 A) = 64 := by
  have h1 := card_eq_relIndex_mul g.hyp.gold.pCoreOf_left_le
  rw [g.hyp.gold.relIndex_pCoreOf_T_left, hT] at h1
  omega

theorem Gen3.card_QB' (hT : Nat.card ↥(A ⊓ B) = 128) : Nat.card ↥(pCoreOf 2 B) = 64 := by
  have h1 := card_eq_relIndex_mul g.hyp.gold.pCoreOf_right_le
  rw [g.hyp.gold.relIndex_pCoreOf_T_right, hT] at h1
  omega

theorem Gen3.card_R (hT : Nat.card ↥(A ⊓ B) = 128) :
    Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) = 32 := by
  have hRT : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ A ⊓ B := inf_le_left.trans g.hyp.gold.pCoreOf_left_le
  have h1 := card_eq_relIndex_mul hRT
  rw [g.hyp.relIndex_inf_pCoreOf_T, hT] at h1
  omega

end CohG

section Coh

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {T' : Subgroup D}
  (c : AutCoh A B T')

include g c

theorem AutCoh.relIndex_NA : (T' ⊓ pCoreOf 2 A).relIndex (pCoreOf 2 A) = 2 := by
  rw [Subgroup.inf_relIndex_right]
  have h1 : T'.relIndex (pCoreOf 2 A) ≤ T'.relIndex (A ⊓ B) :=
    Subgroup.relIndex_le_of_le_right g.hyp.gold.pCoreOf_left_le (relIndex_ne_zero_of_finite _ _)
  have h2 : T'.relIndex (pCoreOf 2 A) ≠ 1 := fun h => c.not_le₁ (Subgroup.relIndex_eq_one.mp h)
  have h3 : T'.relIndex (pCoreOf 2 A) ≠ 0 := relIndex_ne_zero_of_finite _ _
  rw [c.idx] at h1
  omega

theorem AutCoh.relIndex_NB : (T' ⊓ pCoreOf 2 B).relIndex (pCoreOf 2 B) = 2 := by
  rw [Subgroup.inf_relIndex_right]
  have h1 : T'.relIndex (pCoreOf 2 B) ≤ T'.relIndex (A ⊓ B) :=
    Subgroup.relIndex_le_of_le_right g.hyp.gold.pCoreOf_right_le (relIndex_ne_zero_of_finite _ _)
  have h2 : T'.relIndex (pCoreOf 2 B) ≠ 1 := fun h => c.not_le₂ (Subgroup.relIndex_eq_one.mp h)
  have h3 : T'.relIndex (pCoreOf 2 B) ≠ 0 := relIndex_ne_zero_of_finite _ _
  rw [c.idx] at h1
  omega

theorem AutCoh.card_NA (hT : Nat.card ↥(A ⊓ B) = 128) :
    Nat.card ↥(T' ⊓ pCoreOf 2 A) = 32 := by
  have h1 := card_eq_relIndex_mul (inf_le_right : T' ⊓ pCoreOf 2 A ≤ pCoreOf 2 A)
  rw [c.relIndex_NA g, g.card_QA' hT] at h1
  omega

theorem AutCoh.card_NB (hT : Nat.card ↥(A ⊓ B) = 128) :
    Nat.card ↥(T' ⊓ pCoreOf 2 B) = 32 := by
  have h1 := card_eq_relIndex_mul (inf_le_right : T' ⊓ pCoreOf 2 B ≤ pCoreOf 2 B)
  rw [c.relIndex_NB g, g.card_QB' hT] at h1
  omega

theorem AutCoh.not_R_le (hT : Nat.card ↥(A ⊓ B) = 128) :
    ¬ pCoreOf 2 A ⊓ pCoreOf 2 B ≤ T' := by
  intro hR
  have hRA : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ T' ⊓ pCoreOf 2 A := le_inf hR inf_le_left
  have hRB : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ T' ⊓ pCoreOf 2 B := le_inf hR inf_le_right
  have e1 : pCoreOf 2 A ⊓ pCoreOf 2 B = T' ⊓ pCoreOf 2 A :=
    Subgroup.eq_of_le_of_card_ge hRA (by rw [c.card_NA g hT, g.card_R hT])
  have e2 : pCoreOf 2 A ⊓ pCoreOf 2 B = T' ⊓ pCoreOf 2 B :=
    Subgroup.eq_of_le_of_card_ge hRB (by rw [c.card_NB g hT, g.card_R hT])
  have hAR : A ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
    rw [e1]; exact c.norm₁
  have hBR : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
    rw [e2]; exact c.norm₂
  have hRT : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ A ⊓ B := inf_le_left.trans g.hyp.gold.pCoreOf_left_le
  have hbot := g.hyp.gold.eq_bot_of_normalizes hAR hBR hRT
  have h1 : Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) = 1 := by rw [hbot]; simp
  rw [g.card_R hT] at h1
  omega

theorem AutCoh.card_inf (hT : Nat.card ↥(A ⊓ B) = 128) :
    Nat.card ↥((T' ⊓ pCoreOf 2 A) ⊓ (T' ⊓ pCoreOf 2 B)) = 16 := by
  have e : (T' ⊓ pCoreOf 2 A) ⊓ (T' ⊓ pCoreOf 2 B) = T' ⊓ (pCoreOf 2 A ⊓ pCoreOf 2 B) := by
    ext w
    simp only [Subgroup.mem_inf]
    tauto
  rw [e]
  have hRT : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ A ⊓ B := inf_le_left.trans g.hyp.gold.pCoreOf_left_le
  have h1 : (T' ⊓ (pCoreOf 2 A ⊓ pCoreOf 2 B)).relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) = 2 := by
    rw [Subgroup.inf_relIndex_right]
    have h1 : T'.relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) ≤ T'.relIndex (A ⊓ B) :=
      Subgroup.relIndex_le_of_le_right hRT (relIndex_ne_zero_of_finite _ _)
    have h2 : T'.relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) ≠ 1 := fun h =>
      c.not_R_le g hT (Subgroup.relIndex_eq_one.mp h)
    have h3 : T'.relIndex (pCoreOf 2 A ⊓ pCoreOf 2 B) ≠ 0 := relIndex_ne_zero_of_finite _ _
    rw [c.idx] at h1
    omega
  have h2 := card_eq_relIndex_mul (inf_le_right : T' ⊓ (pCoreOf 2 A ⊓ pCoreOf 2 B) ≤
    pCoreOf 2 A ⊓ pCoreOf 2 B)
  rw [h1, g.card_R hT] at h2
  omega

end Coh

section Coh2

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.exists_comm_rep {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) {v : D} (hv : v ∈ V) :
    ∃ w ∈ V, v = w * (y * w * y⁻¹)⁻¹ := by
  have hcomm : ∀ p q : D, p ∈ V → q ∈ V → p * q = q * p := fun p q hp hq =>
    g.U_comm (le_conjClosure V B hp) (le_conjClosure V B hq)
  let φ : ↥V →* ↥V :=
    { toFun := fun w => ⟨(w : D) * (y * (w : D) * y⁻¹)⁻¹,
        V.mul_mem w.2 (V.inv_mem (g.conj_mem_V hyA w.2))⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro w w'
        apply Subtype.ext
        have hp : (y * (w : D) * y⁻¹)⁻¹ ∈ V := V.inv_mem (g.conj_mem_V hyA w.2)
        have hq : (y * (w' : D) * y⁻¹)⁻¹ ∈ V := V.inv_mem (g.conj_mem_V hyA w'.2)
        have c1 := hcomm _ _ hq hp
        have c2 := hcomm (w' : D) _ w'.2 hp
        show (w : D) * (w' : D) * (y * ((w : D) * (w' : D)) * y⁻¹)⁻¹ =
          ((w : D) * (y * (w : D) * y⁻¹)⁻¹) * ((w' : D) * (y * (w' : D) * y⁻¹)⁻¹)
        calc (w : D) * (w' : D) * (y * ((w : D) * (w' : D)) * y⁻¹)⁻¹
            = (w : D) * (w' : D) * ((y * (w' : D) * y⁻¹)⁻¹ * (y * (w : D) * y⁻¹)⁻¹) := by group
          _ = (w : D) * ((w' : D) * ((y * (w' : D) * y⁻¹)⁻¹ * (y * (w : D) * y⁻¹)⁻¹)) := by group
          _ = (w : D) * ((w' : D) * ((y * (w : D) * y⁻¹)⁻¹ * (y * (w' : D) * y⁻¹)⁻¹)) := by
            rw [c1]
          _ = (w : D) * (((w' : D) * (y * (w : D) * y⁻¹)⁻¹) * (y * (w' : D) * y⁻¹)⁻¹) := by
            group
          _ = (w : D) * (((y * (w : D) * y⁻¹)⁻¹ * (w' : D)) * (y * (w' : D) * y⁻¹)⁻¹) := by
            rw [c2]
          _ = ((w : D) * (y * (w : D) * y⁻¹)⁻¹) * ((w' : D) * (y * (w' : D) * y⁻¹)⁻¹) := by
            group }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : D) * (y * (w : D) * y⁻¹)⁻¹ = 1 := congrArg Subtype.val hw
    have h2 : y * (w : D) * y⁻¹ = w := (mul_inv_eq_one.mp h1).symm
    by_contra hne
    exact g.conj_ne_of_ne_one hyA hy3 w.2 (fun h => hne (Subtype.ext h)) h2
  obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hinj) ⟨v, hv⟩
  exact ⟨w, w.2, (congrArg Subtype.val hw).symm⟩

end Coh2

section Coh3

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {T' : Subgroup D}
  (c : AutCoh A B T')

include g c

theorem AutCoh.V_le_NA {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) : V ≤ T' ⊓ pCoreOf 2 A := by
  intro v hv
  obtain ⟨w, hwV, rfl⟩ := g.exists_comm_rep hyA hy3 hv
  have hwQ : w ∈ pCoreOf 2 A := (g.hyp.natural.le_center hwV).1
  have h := comm_mem_of_relIndex_two (c.relIndex_NA g) (c.norm₁ hyA)
    (le_normalizer_pCoreOf 2 A hyA) hwQ
  have e : w * (y * w * y⁻¹)⁻¹ = (y * w * y⁻¹ * w⁻¹)⁻¹ := by group
  rw [e]
  exact (T' ⊓ pCoreOf 2 A).inv_mem h

theorem AutCoh.U_le (hU : Nat.card (conjClosure V B) = 8) {y : D} (hyA : y ∈ A)
    (hy3 : orderOf y = 3) :
    conjClosure V B ≤ T' ⊓ pCoreOf 2 A ∧ conjClosure V B ≤ T' ⊓ pCoreOf 2 B := by
  have hVA := c.V_le_NA g hyA hy3
  have hVB : V ≤ T' ⊓ pCoreOf 2 B := fun v hv =>
    ⟨(hVA hv).1, g.hyp.le_pCoreOf_right hv⟩
  have hUB : conjClosure V B ≤ T' ⊓ pCoreOf 2 B := by
    intro u hu
    rcases g.mem_U_cases hU hu with huV | ⟨v, hv, rfl⟩
    · exact hVB huV
    · refine (T' ⊓ pCoreOf 2 B).mul_mem (hVB hv) ?_
      have h := comm_mem_of_relIndex_two (c.relIndex_NB g) (c.norm₂ g.x_mem)
        (le_normalizer_pCoreOf 2 B g.x_mem) g.a_mem_QB
      have e : a₁ = (x * a * x⁻¹ * a⁻¹) * a := by rw [g.a₁_eq]; group
      rw [e]
      exact (T' ⊓ pCoreOf 2 B).mul_mem h (hVB g.a_mem)
  refine ⟨fun u hu => ⟨(hUB hu).1, g.hyp.conjClosure_le_pCoreOf_left hu⟩, hUB⟩

end Coh3

end GoldAmL3c

end F6

end CFSG.Quasithin
