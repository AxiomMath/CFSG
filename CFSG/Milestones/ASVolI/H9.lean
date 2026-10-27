module

public import CFSG.Quasithin.AppendixH.H9.H91Assembly
public import CFSG.Quasithin.AppendixH.H9.H92.Assembly
public import CFSG.Quasithin.AppendixH.H9.H93.Assembly
public import CFSG.Quasithin.AppendixH.H9.FormUniqueness
public import CFSG.Quasithin.AppendixH.H9.OrbitsOnV

public section

open scoped commutatorElement Matrix

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_9_1 : Prop :=
  ∀ n : ℕ, (n = 4 ∨ n = 5) →
    (IsQuadFormN (pairQn n) ∧ IsNondegN (pairQn n) ∧ (∀ g ∈ Mg n, ∀ x, pairQn n (g x) = pairQn n x) ∧
      (∀ v ∈ V1n n, pairQn n v = 0) ∧
      ∀ q' : PairN n → ZMod 2, IsQuadFormN q' → IsNondegN q' → (∀ g ∈ Mg n, ∀ x, q' (g x) = q' x) →
        (∀ v ∈ V1n n, q' v = 0) → q' = pairQn n) ∧
    ((∀ i : Fin 3, ∀ x ∈ Oorb n i, ∀ g ∈ Mg n, g x ∈ Oorb n i) ∧
      (∀ i : Fin 3, ∀ x ∈ Oorb n i, ∀ y ∈ Oorb n i, ∃ g ∈ Mg n, g x = y) ∧
      (∀ x : PairN n, x ≠ 1 → ∃ i : Fin 3, x ∈ Oorb n i) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (Oorb n i) (Oorb n j)) ∧
      (∀ x ∈ Oorb n 0, pairQn n x = 0) ∧
      (∀ x : PairN n, x ≠ 1 → (IsTwoCentralVec (Mg n) x ↔ x ∈ Oorb n 1))) ∧
    ∀ T : Subgroup (MulAut (PairN n)), IsSylowIn 2 T (Mg n) →
    ∀ v₁ : PairN n, v₁ ∈ V1n n → fixV (T ⊓ stabSub (V1n n)) ⊓ V1n n = Subgroup.zpowers v₁ →
      (Mg n ⊓ centSub (Subgroup.zpowers v₁) = twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁)) ∧
        (∃ E : Subgroup (MulAut (PairN n)), CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (n - 1) ∧
          IsExtOf (Mg n ⊓ centSub (Subgroup.zpowers v₁)) E (GL (Fin (n - 1)) (ZMod 2))) ∧
        commOn (V1n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁))) = V1n n ∧
        commOn (V2n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁))) =
          V2n n ⊓ perpN n (Subgroup.zpowers v₁) ∧
        (V2n n ⊓ perpN n (Subgroup.zpowers v₁)).relIndex (V2n n) = 2 ∧
        InducesOn (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁)))
          (commOn (V2n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁)))) ⊥
          (Multiplicative (Fin (n - 1) → ZMod 2)) (natSub (n - 1) (ZMod 2) ⊤) ∧
        T ⊓ stabSub (V1n n) = T ⊓ centSub (Subgroup.zpowers v₁) ∧
        IsSylowIn 2 (T ⊓ stabSub (V1n n)) (Mg n ⊓ centSub (Subgroup.zpowers v₁))) ∧
      (∀ v₂ : PairN n, v₂ ∈ V2n n →
        v₂ ∉ commOn (V2n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁))) →
          v₁ * v₂ ∈ Oorb n 2 ∧
          (∃ S : Subgroup (MulAut (PairN n)),
            IsSylowIn 2 S (Mg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ∧
            S ⊓ Lg n = T ⊓ centSub (Subgroup.zpowers (v₁ * v₂)) ∧
            ∃ t ∈ S, t ∉ Lg n ∧ t ^ 2 = 1 ∧ t v₁ = v₂ ∧ t v₂ = v₁ ∧
            Mg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂)) =
              Subgroup.zpowers t ⊔ twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ∧
            Nonempty (↥(Mg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ≃*
              MulAut (GL (Fin (n - 1)) (ZMod 2))) ∧
            twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) =
              twoResidual (Mg n ⊓ centSub (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
            IsSylowIn 2 (T ⊓ centSub (Subgroup.zpowers (v₁ * v₂)))
              (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))))) ∧
          (V1n n = Subgroup.zpowers v₁ ⊔ (V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
            Subgroup.zpowers v₁ ⊓ (V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) = ⊥ ∧
            V2n n = Subgroup.zpowers v₂ ⊔ (V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
            Subgroup.zpowers v₂ ⊓ (V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) = ⊥) ∧
          InducesOn (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))))
            (V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ⊥
            (Multiplicative (Fin (n - 1) → ZMod 2)) (natSub (n - 1) (ZMod 2) ⊤) ∧
          ((∀ w ∈ V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), w ≠ 1 →
              ∃ w' ∈ V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), polarN n w w' ≠ 0) ∧
            (∀ w' ∈ V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), w' ≠ 1 →
              ∃ w ∈ V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), polarN n w w' ≠ 0)))

theorem as_H_9_1 : H_9_1 := by
  intro n hn
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  exact ⟨h91_clause1 n hn2, h91_clause2 n hn2, fun T hT v₁ _ hfix =>
    ⟨h91_clause3 n hn T hT v₁ hfix, fun v₂ hv₂ hv₂' =>
      h91_clause4 n hn T hT v₁ hfix v₂ hv₂ hv₂'⟩⟩

@[expose] def H_9_2 : Prop :=
  ((∀ t ∈ Mg 5, ∀ t' ∈ Mg 5, t ∉ Lg 5 → t' ∉ Lg 5 → orderOf t = 2 → orderOf t' = 2 →
      IsConjIn (Mg 5) t t') ∧
    (∀ t ∈ Mg 5, t ∉ Lg 5 → orderOf t = 2 →
      ThetaIso 5 t ∧
      G6.IsSymNatural (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))))
        (commOn (fixV (Subgroup.zpowers t))
          (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))))) 6 ∧
      ∃ v ∈ fixV (Subgroup.zpowers t), pairQn 5 v = 1 ∧
        (∀ g ∈ Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))), g v = v) ∧
        fixV (Subgroup.zpowers t) =
          Subgroup.zpowers v ⊔ commOn (fixV (Subgroup.zpowers t))
            (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5)))) ∧
        Subgroup.zpowers v ⊓ commOn (fixV (Subgroup.zpowers t))
            (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5)))) = ⊥)) ∧
  (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → 5 ≤ rk ↥A → A ≤ Lg 5) ∧
  ∀ T : Subgroup (MulAut (PairN 5)), IsSylowIn 2 T (Mg 5) →
  ∀ U : Subgroup (PairN 5), U ≤ V1n 5 → rk ↥U = 3 →
    (∀ g ∈ T ⊓ stabSub (V1n 5), ∀ u ∈ U, g u ∈ U) →
      ((∀ B : Subgroup (MulAut (PairN 5)),
          (∃ g ∈ Mg 5, B = conjAut g (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U))) ↔
            (B ≤ Mg 5 ∧ IsElemAbelian2 B ∧ Nat.card B = 64)) ∧
        (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → rk ↥A = 5 →
          ∃ g ∈ Mg 5, conjAut g A ≤ CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U) ∧
            Nat.card (conjAut g A) * 2 = Nat.card (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)))) ∧
      (∀ A : Subgroup (MulAut (PairN 5)), A ≤ CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U) →
        Nat.card A * 2 = Nat.card (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) →
          fixV A = commV A ∧ commV A = fixV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) ∧
          fixV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) = commV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) ∧
          commV (CFSG.Open.pCoreOf 2 (Lg 5 ⊓ stabSub U)) = U ⊔ (V2n 5 ⊓ perpN 5 U) ∧
          rk ↥(U ⊔ (V2n 5 ⊓ perpN 5 U)) = 5) ∧
      (∀ A : Subgroup (MulAut (PairN 5)), A ≤ Mg 5 → IsElemAbelian2 A → 5 ≤ rk ↥A →
        E3.gammaCheck 3 A = ⊤)

theorem as_H_9_2 : H_9_2 := h92_main

noncomputable def imgPerm8 (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) (A : Subgroup (MulAut (PairN 4))) :
    Subgroup (Equiv.Perm (Fin 8)) :=
  (A.subgroupOf (Mg 4)).map ψ.toMonoidHom

noncomputable def psiX (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) (t : MulAut (PairN 4)) :
    Equiv.Perm (Fin 8) :=
  open Classical in if h : t ∈ Mg 4 then ψ ⟨t, h⟩ else 1

open Classical in
noncomputable def orbitSizes8 (B : Subgroup (Equiv.Perm (Fin 8))) : Multiset ℕ :=
  (Finset.univ.image fun i : Fin 8 => (MulAction.orbit B i : Set (Fin 8))).val.map Set.ncard

@[expose] def H_9_3 : Prop :=
  ∀ ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8),
    ((∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 →
        ((psiX ψ t).cycleType = {2} ∨ (psiX ψ t).cycleType = {2, 2, 2})) ∧
      (∃ t ∈ Mg 4, t ∉ Lg 4 ∧ orderOf t = 2 ∧ (psiX ψ t).cycleType = {2}) ∧
      (∃ u ∈ Mg 4, u ∉ Lg 4 ∧ orderOf u = 2 ∧ (psiX ψ u).cycleType = {2, 2, 2}) ∧
      (∀ t ∈ Mg 4, ∀ u ∈ Mg 4, t ∉ Lg 4 → u ∉ Lg 4 → orderOf t = 2 → orderOf u = 2 →
        (psiX ψ t).cycleType = (psiX ψ u).cycleType → IsConjIn (Mg 4) t u) ∧
      (∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 → (psiX ψ t).cycleType = {2} →
        Nonempty (↥(Lg 4 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 4)))) ≃*
          Equiv.Perm (Fin 6))) ∧
      (∀ u ∈ Mg 4, u ∉ Lg 4 → orderOf u = 2 → (psiX ψ u).cycleType = {2, 2, 2} →
        Nonempty (↥(Lg 4 ⊓ Subgroup.centralizer ({u} : Set (MulAut (PairN 4)))) ≃*
          (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))))) ∧
    (∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 → ThetaIso 4 t) ∧
    ∀ T : Subgroup (MulAut (PairN 4)), IsSylowIn 2 T (Mg 4) →
      ∃ A₁ A₂ : Subgroup (MulAut (PairN 4)),
        (A₁ ≤ Mg 4 ∧ IsElemAbelian2 A₁ ∧ Nat.card A₁ = 16 ∧ ¬ A₁ ≤ Lg 4 ∧
          orbitSizes8 (imgPerm8 ψ A₁) = {2, 2, 2, 2}) ∧
        (A₂ ≤ Mg 4 ∧ IsElemAbelian2 A₂ ∧ Nat.card A₂ = 16 ∧ ¬ A₂ ≤ Lg 4 ∧
          orbitSizes8 (imgPerm8 ψ A₂) = {2, 2, 4}) ∧
        (thompsonJ (T ⊓ stabSub (V1n 4)) ≤ Mg 4 ∧ IsElemAbelian2 (thompsonJ (T ⊓ stabSub (V1n 4))) ∧
          Nat.card (thompsonJ (T ⊓ stabSub (V1n 4))) = 16 ∧
          orbitSizes8 (imgPerm8 ψ (thompsonJ (T ⊓ stabSub (V1n 4)))) = {4, 4}) ∧
        (∀ A : Subgroup (MulAut (PairN 4)), A ≤ Mg 4 → IsElemAbelian2 A → Nat.card A = 16 →
          (∃ g ∈ Mg 4, conjAut g (thompsonJ (T ⊓ stabSub (V1n 4))) = A) ∨ (∃ g ∈ Mg 4, conjAut g A₁ = A) ∨
            (∃ g ∈ Mg 4, conjAut g A₂ = A)) ∧
        (¬ ∃ g ∈ Mg 4, conjAut g (thompsonJ (T ⊓ stabSub (V1n 4))) = A₁) ∧
        (¬ ∃ g ∈ Mg 4, conjAut g (thompsonJ (T ⊓ stabSub (V1n 4))) = A₂) ∧
        (¬ ∃ g ∈ Mg 4, conjAut g A₁ = A₂) ∧
        (rk ↥(fixV (thompsonJ (T ⊓ stabSub (V1n 4)))) = 4 ∧
          E3.gammaCheck 2 (thompsonJ (T ⊓ stabSub (V1n 4))) = ⊤) ∧
        (rk ↥(fixV A₁) = 1 ∧
          ∃ r ∈ A₁, (r ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers r)) = 1) ∧
            (∀ r' ∈ A₁, (r' ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers r')) = 1) → r' = r) ∧
            E3.gammaCheck 2 A₁ = fixV (Subgroup.zpowers r) ∧ rk ↥(fixV (Subgroup.zpowers r)) = 6) ∧
        (∀ a ∈ A₂, a ∉ Lg 4 →
          ((fixV A₂ : Subgroup (PairN 4)) : Set (PairN 4)) =
              {x | ∃ w ∈ V1n 4 ⊓ fixV (A₂ ⊓ Lg 4), x = w * a w} ∧
            rk ↥(fixV A₂) = 2 ∧
            E3.gammaCheck 2 A₂ = fixV (A₂ ⊓ Lg 4) ⊔ fixV (Subgroup.zpowers a) ∧
            rk ↥(E3.gammaCheck 2 A₂) = 6)

theorem as_H_9_3 : H_9_3 := fun ψ => h93_main ψ

end CFSG.ASVolI
