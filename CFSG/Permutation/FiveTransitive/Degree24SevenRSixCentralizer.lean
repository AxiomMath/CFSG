module

public import CFSG.Permutation.FiveTransitive.Degree24SevenRSix
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

@[expose] def subgroupCentralizerToFixedPoints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (u : P) :
    Subgroup.centralizer ({u} : Set P) →*
      Equiv.Perm
        (Function.fixedPoints (u : Equiv.Perm X)) := by
  let g : Equiv.Perm X := u
  let D : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  let baseMap : D →* Equiv.Perm X :=
    P.subtype.comp D.subtype
  have hbaseMapMem :
      ∀ q : D, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp q.prop)
  let centMap :
      D →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  exact
    (Degree19.centralizerToFixedPoints g).comp centMap

theorem rSix_centralizer_five_transitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 13608 ∨
      Nat.card (fixingSubgroup P s) = 13063680)
    (u : fixingSubgroup P s)
    (hu : orderOf u = 7) :
    ∀ a b :
        Fin 5 →
          Function.fixedPoints
            ((((u : fixingSubgroup P s) : P) :
              Equiv.Perm X)),
      Function.Injective a →
      Function.Injective b →
      ∃ q :
          Subgroup.centralizer
            ({((u : fixingSubgroup P s) : P)} : Set P),
        ∀ i,
          subgroupCentralizerToFixedPoints
            P ((u : fixingSubgroup P s) : P) q (a i) =
              b i := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let uH : H := u
  let uP : P := uH
  let g : Equiv.Perm X := uP
  let D : Subgroup P :=
    Subgroup.centralizer ({uP} : Set P)
  let ρ := subgroupCentralizerToFixedPoints P uP
  intro a b ha hb
  let aX : Fin 5 ↪ X := {
    toFun := fun i => (a i).1
    inj' := fun i j hij =>
      ha (Subtype.ext hij) }
  let bX : Fin 5 ↪ X := {
    toFun := fun i => (b i).1
    inj' := fun i j hij =>
      hb (Subtype.ext hij) }
  obtain ⟨q, hq⟩ :=
    h5 aX bX aX.injective bX.injective
  let vP : P := q * uP * q⁻¹
  have hvOrderP : orderOf vP = 7 := by
    calc
      orderOf vP =
          orderOf ((MulAut.conj q) uP) := rfl
      _ = orderOf uP :=
        (MulAut.conj q).orderOf_eq uP
      _ = orderOf uH :=
        Subgroup.orderOf_coe _
      _ = orderOf u := rfl
      _ = 7 := hu
  let t : Set X := Set.range bX
  have ht : t.ncard = 5 := by
    rw [Set.ncard_range_of_injective bX.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hvFixes :
      ∀ x ∈ t, vP • x = x := by
    rintro _ ⟨i, rfl⟩
    have hua : uP • aX i = aX i := by
      have hai := (a i).prop
      change g (aX i) = aX i at hai
      simpa only [g, Subgroup.smul_def,
        Equiv.Perm.smul_def] using hai
    calc
      vP • bX i =
          q • (uP • (q⁻¹ • bX i)) := by
        simp only [vP, mul_smul]
      _ = q • (uP • aX i) := by
        rw [← hq i, inv_smul_smul]
      _ = q • aX i := by rw [hua]
      _ = bX i := hq i
  let vT : fixingSubgroup P t :=
    ⟨vP, (mem_fixingSubgroup_iff P).mpr hvFixes⟩
  let uT : fixingSubgroup P t :=
    ⟨uP, (mem_fixingSubgroup_iff P).mpr (by
      rintro _ ⟨i, rfl⟩
      have hbi := (b i).prop
      change g (bX i) = bX i at hbi
      simpa only [g, Subgroup.smul_def,
        Equiv.Perm.smul_def] using hbi)⟩
  have hvOrderT : orderOf vT = 7 := by
    calc
      orderOf vT = orderOf vP :=
        by simp only [vT, Subgroup.orderOf_mk]
      _ = 7 := hvOrderP
  have huOrderT : orderOf uT = 7 := by
    calc
      orderOf uT = orderOf uP :=
        by simp only [uT, Subgroup.orderOf_mk]
      _ = orderOf uH :=
        Subgroup.orderOf_coe _
      _ = orderOf u := rfl
      _ = 7 := hu
  have htCases :
      Nat.card (fixingSubgroup P t) = 13608 ∨
        Nat.card (fixingSubgroup P t) = 13063680 := by
    have heq :=
      five_point_stabilizers_have_equal_card
        X P h5 s t hs ht
    rcases hCases with hsCard | hsCard
    · left
      rw [← heq]
      exact hsCard
    · right
      rw [← heq]
      exact hsCard
  obtain ⟨k, hk⟩ :=
    rSix_orderSeven_elements_are_conjugate
      X P hcard h5 hnotAlt t ht htCases
        vT uT hvOrderT huOrderT
  let kP : P := k
  have hkP : kP * vP * kP⁻¹ = uP := by
    exact congrArg Subtype.val hk
  let cP : P := kP * q
  have hcConj : cP * uP * cP⁻¹ = uP := by
    calc
      cP * uP * cP⁻¹ =
          kP * vP * kP⁻¹ := by
        dsimp only [cP, vP]
        group
      _ = uP := hkP
  have hcCommute : Commute cP uP := by
    show cP * uP = uP * cP
    calc
      cP * uP = (cP * uP * cP⁻¹) * cP := by group
      _ = uP * cP := by rw [hcConj]
  let cD : D :=
    ⟨cP, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcCommute⟩
  refine ⟨cD, ?_⟩
  intro i
  apply Subtype.ext
  change cP • aX i = bX i
  calc
    cP • aX i = kP • (q • aX i) := by
      simp only [cP, mul_smul]
    _ = kP • bX i := by rw [hq i]
    _ = bX i := by
      exact
        (mem_fixingSubgroup_iff P).mp
          k.prop (bX i) ⟨i, rfl⟩

end FiveTransitive.Degree24

end CFSG
