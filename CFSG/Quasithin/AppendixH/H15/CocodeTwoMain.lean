module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffender
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoInduced
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoSurj
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoThree
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPair

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

theorem h152_main (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    ((H.IsFOneOffender ρ.range (rImg ρ (KY Γ (Yd d a b O))) ∧
        ∀ A : Subgroup (MulAut V), A ≤ rImg ρ (T₀ ⊓ Γ) → H.IsFOneOffender ρ.range A →
          A = rImg ρ (KY Γ (Yd d a b O))) ∧
      (rk ↥(fixV (rImg ρ (KY Γ (Yd d a b O)))) = (if d = 22 then 5 else 6) ∧
        (∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
          ((∀ u ∈ fixV (rImg ρ (KY Γ (Yd d a b O))), ρ g u = u) ↔ (g : S24) ∈ KY Γ (Yd d a b O))) ∧
        (d = 24 →
          InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (KY Γ (Yd d a b O)))) ⊥
            (Multiplicative (Fin 6 → ZMod 2)) (omegaN 6 qPlus6)) ∧
        (d = 23 → ∃ Γ₇ : Subgroup (MulAut (Multiplicative (Fin 6 → ZMod 2))), Γ₇ ≤ omegaN 6 qPlus6 ∧
          Nonempty (↥Γ₇ ≃* ↥(alternatingGroup (Fin 7))) ∧
          InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (KY Γ (Yd d a b O)))) ⊥
            (Multiplicative (Fin 6 → ZMod 2)) Γ₇) ∧
        (d = 22 → ∃ (w : Multiplicative (Fin 6 → ZMod 2)) (π : Multiplicative (Fin 6 → ZMod 2) →* V),
          qPlus6 (Multiplicative.toAdd w) = 1 ∧ π.range = fixV (rImg ρ (KY Γ (Yd d a b O))) ∧
          π.ker = Subgroup.zpowers w ∧
          (∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
            ∃ γ ∈ omegaN 6 qPlus6, γ w = w ∧ ∀ x, π (γ x) = ρ g (π x)) ∧
          (Γ ≠ M22g a b → ∀ γ ∈ omegaN 6 qPlus6, γ w = w →
            ∃ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) ∧ ∀ x, π (γ x) = ρ g (π x))) ∧
        (d = 23 → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 7)), Function.Surjective π ∧
          π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
        (d = 24 → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 8)), Function.Surjective π ∧
          π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
        (d = 22 → (Γ = M22g a b → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 6)),
            Function.Surjective π ∧ π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
          (Γ ≠ M22g a b → ∃ π : ↥(MY Γ (Yd d a b O)) →* Equiv.Perm (Fin 6),
            Function.Surjective π ∧
              π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O)))))) ∧
    (∀ I : Subgroup V, I ≤ fixV (rImg ρ (KY Γ (Yd d a b O))) → (∀ x ∈ I, ¬ IsO2Vec d a b Γ β x) →
      rk ↥I ≤ (if d = 24 then 3 else 4)) ∧
    rkIdx (xiSub (rImg ρ (KY Γ (Yd d a b O)))) = 1 ∧
    ((∀ z ∈ Γ, orderOf z = 2 → IsTwoCentralElt Γ z →
        cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf Γ) ∧
      (∀ A : Subgroup S24, A ≤ KY Γ (Yd d a b O) → ¬ IsCyclic ↥A →
        fixV (rImg ρ A) = fixV (rImg ρ (KY Γ (Yd d a b O))))) ∧
    FullTranspAxis (rImg ρ (MY Γ (Yd d a b O))) (rImg ρ (KY Γ (Yd d a b O)))
      (fixV (rImg ρ (KY Γ (Yd d a b O)))) (xiSub (rImg ρ (KY Γ (Yd d a b O)))) := by
  rw [mctx_kY_eq hM]
  refine ⟨⟨⟨kLayer_offender hM, fun A hAT hA => offender_unique hM hAT hA⟩,
    kLayer_rk_fixV hM, induced_2b hM, fun hd => induced_24 hM hd, fun hd => induced_23 hM hd,
    fun hd => induced_22 hM hd, fun hd => surj_23 hM hd, fun hd => surj_24 hM hd,
    fun hd => ⟨fun hΓ => surj_22a hM hd hΓ, fun hΓ => surj_22b hM hd hΓ⟩⟩,
    three_main hM, kLayer_rkIdx_xiSub hM, ⟨pair_main hM, fun A hA hnc => kLayer_noncyclic hM hA hnc⟩,
    kLayer_fullTransp hM⟩

end CFSG.ASVolI.AppH
