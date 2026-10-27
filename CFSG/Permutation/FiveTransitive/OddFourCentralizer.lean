module

public import CFSG.Permutation.FiveTransitive.SharpFourCentralizer

public section

namespace CFSG

namespace FiveTransitive.Research.OddFourCentralizer

open MulAction
open Research.SharpFourDegreeCompletion

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

@[expose] def centralizingBaseStabilizer (e : Fin 4 ↪ X) (t : G) : Subgroup G :=
  MulAction.stabilizer G e ⊓ Subgroup.centralizer ({t} : Set G)

private def baseIntertwining (e : Fin 4 ↪ X) (t : G)
    (σ : Equiv.Perm (Fin 4))
    (hbase : ∀ i, t • e i = e (σ i)) :
    IntertwiningEmbeddings (X := X) t σ :=
  ⟨e, hbase⟩

private def centralizerIntertwiningMulAction (t : G)
    (σ : Equiv.Perm (Fin 4)) :
    MulAction (Subgroup.centralizer ({t} : Set G))
      (IntertwiningEmbeddings (X := X) t σ) where
  smul c a := ⟨(c : G) • a.1, by
    intro i
    have hc : (c : G) * t = t * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.property
    change t • ((c : G) • a.1 i) = (c : G) • a.1 (σ i)
    rw [← mul_smul, ← hc, mul_smul, a.property]⟩
  one_smul a := by
    apply Subtype.ext
    exact one_smul G a.1
  mul_smul c d a := by
    apply Subtype.ext
    exact mul_smul (c : G) (d : G) a.1

@[expose] def CentralizerCorrection (e : Fin 4 ↪ X) (t : G)
    (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ a : IntertwiningEmbeddings (X := X) t σ,
    ∃ c : G, c ∈ Subgroup.centralizer ({t} : Set G) ∧
      ∀ i, c • e i = a.1 i

@[expose] def SameBaseInvolutionConjugacy (e : Fin 4 ↪ X) : Prop :=
  ∀ u v : G, u ^ 2 = 1 → v ^ 2 = 1 →
    (∀ i, u • e i = v • e i) →
    ∃ h : G, h ∈ MulAction.stabilizer G e ∧ h * u * h⁻¹ = v

theorem centralizerCorrection_of_sameBaseInvolutionConjugacy
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) (t : G) (σ : Equiv.Perm (Fin 4))
    (htwo : t ^ 2 = 1)
    (hbase : ∀ i, t • e i = e (σ i))
    (hconj : SameBaseInvolutionConjugacy (G := G) e) :
    CentralizerCorrection (X := X) e t σ := by
  intro a
  obtain ⟨q, hq⟩ :=
    Research.SharpFourBound.exists_maps_embedding h4 e a.1
  let v : G := q⁻¹ * t * q
  have hvTwo : v ^ 2 = 1 := by
    calc
      v ^ 2 = q⁻¹ * (t ^ 2) * q := by
        dsimp only [v]
        rw [pow_two, pow_two]
        group
      _ = 1 := by rw [htwo]; simp
  have hvSame : ∀ i, v • e i = t • e i := by
    intro i
    calc
      v • e i = q⁻¹ • (t • (q • e i)) := by
        simp only [v, mul_smul]
      _ = q⁻¹ • (t • a.1 i) := by rw [hq]
      _ = q⁻¹ • a.1 (σ i) := by rw [a.property]
      _ = q⁻¹ • (q • e (σ i)) := by rw [hq]
      _ = e (σ i) := inv_smul_smul q _
      _ = t • e i := (hbase i).symm
  obtain ⟨h, hhstab, hht⟩ :=
    hconj t v htwo hvTwo (fun i => (hvSame i).symm)
  refine ⟨q * h, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (q * h) * t * (q * h)⁻¹ =
          q * (h * t * h⁻¹) * q⁻¹ := by group
      _ = q * v * q⁻¹ := by rw [hht]
      _ = t := by
        dsimp only [v]
        group
  · intro i
    rw [mul_smul]
    have hhfix := hhstab
    rw [MulAction.mem_stabilizer_iff] at hhfix
    have hi : h • e i = e i := by
      have := congrArg (fun b : Fin 4 ↪ X => b i) hhfix
      simpa [Function.Embedding.smul_apply] using this
    rw [hi]
    exact hq i

private theorem orbit_baseIntertwining_eq_univ
    (e : Fin 4 ↪ X) (t : G) (σ : Equiv.Perm (Fin 4))
    (hbase : ∀ i, t • e i = e (σ i))
    (hcorrect : CentralizerCorrection (X := X) e t σ) :
    letI := centralizerIntertwiningMulAction (X := X) t σ
    MulAction.orbit (Subgroup.centralizer ({t} : Set G))
      (baseIntertwining e t σ hbase) = Set.univ := by
  letI := centralizerIntertwiningMulAction (X := X) t σ
  apply Set.eq_univ_iff_forall.mpr
  intro a
  obtain ⟨c, hc, hce⟩ := hcorrect a
  refine ⟨⟨c, hc⟩, ?_⟩
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  exact hce i

private def centralizerBaseStabilizerEquiv
    (e : Fin 4 ↪ X) (t : G) (σ : Equiv.Perm (Fin 4))
    (hbase : ∀ i, t • e i = e (σ i)) :
    letI := centralizerIntertwiningMulAction (X := X) t σ
    MulAction.stabilizer (Subgroup.centralizer ({t} : Set G))
        (baseIntertwining e t σ hbase) ≃*
      centralizingBaseStabilizer e t := by
  letI := centralizerIntertwiningMulAction (X := X) t σ
  let C := Subgroup.centralizer ({t} : Set G)
  let b := baseIntertwining e t σ hbase
  let K := centralizingBaseStabilizer e t
  exact
    { toFun := fun c => ⟨(c.1 : G), by
        refine Subgroup.mem_inf.mpr ⟨?_, c.1.property⟩
        rw [MulAction.mem_stabilizer_iff]
        apply Function.Embedding.ext
        intro i
        have hc := c.property
        rw [MulAction.mem_stabilizer_iff] at hc
        have hi := congrArg
          (fun a : IntertwiningEmbeddings (X := X) t σ => a.1 i) hc
        exact hi⟩
      invFun := fun k => ⟨⟨(k : G), (Subgroup.mem_inf.mp k.property).2⟩, by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        apply Function.Embedding.ext
        intro i
        have hk := (Subgroup.mem_inf.mp k.property).1
        rw [MulAction.mem_stabilizer_iff] at hk
        exact congrArg (fun a : Fin 4 ↪ X => a i) hk⟩
      left_inv := fun c => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun k => by
        apply Subtype.ext
        rfl
      map_mul' := fun c d => by
        apply Subtype.ext
        rfl }

private theorem centralizer_card_eq_intertwining_mul_baseCentralizer
    (e : Fin 4 ↪ X) (t : G) (σ : Equiv.Perm (Fin 4))
    (hbase : ∀ i, t • e i = e (σ i))
    (hcorrect : CentralizerCorrection (X := X) e t σ) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) =
      Nat.card (IntertwiningEmbeddings (X := X) t σ) *
        Nat.card (centralizingBaseStabilizer e t) := by
  classical
  let C := Subgroup.centralizer ({t} : Set G)
  let I := IntertwiningEmbeddings (X := X) t σ
  let b := baseIntertwining e t σ hbase
  letI := centralizerIntertwiningMulAction (X := X) t σ
  letI : Fintype C := Fintype.ofFinite C
  letI : Finite I := Finite.of_injective
    (fun a : I => fun i => a.1 i) (by
      intro a d had
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      exact congrFun had i)
  letI : Fintype (MulAction.orbit C b) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer C b) := Fintype.ofFinite _
  have horbit : Nat.card (MulAction.orbit C b) = Nat.card I := by
    rw [orbit_baseIntertwining_eq_univ e t σ hbase hcorrect]
    exact Nat.card_congr (Equiv.Set.univ I)
  have hstab : Nat.card (MulAction.stabilizer C b) =
      Nat.card (centralizingBaseStabilizer e t) :=
    Nat.card_congr
      (centralizerBaseStabilizerEquiv e t σ hbase).toEquiv
  have hcard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group C b
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at hcard
  rw [horbit, hstab] at hcard
  exact hcard.symm

theorem singleSwap_centralizer_card
    (e : Fin 4 ↪ X) (t : G)
    (htwo : t ^ 2 = 1)
    (hbase : ∀ i, t • e i = e (Research.SharpFourBound.baseSingleSwap i))
    (hcorrect : CentralizerCorrection (X := X) e t
      Research.SharpFourBound.baseSingleSwap) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) =
      ((MulAction.fixedBy X t).ncard.descFactorial 2 *
        (Fintype.card X - (MulAction.fixedBy X t).ncard)) *
      Nat.card (centralizingBaseStabilizer e t) := by
  rw [centralizer_card_eq_intertwining_mul_baseCentralizer
    e t Research.SharpFourBound.baseSingleSwap hbase hcorrect,
    singleIntertwining_ncard t htwo]

theorem doubleSwap_centralizer_card
    (e : Fin 4 ↪ X) (t : G)
    (htwo : t ^ 2 = 1)
    (hbase : ∀ i, t • e i = e (Research.SharpFourBound.baseDoubleSwap i))
    (hcorrect : CentralizerCorrection (X := X) e t
      Research.SharpFourBound.baseDoubleSwap) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) =
      ((Fintype.card X - (MulAction.fixedBy X t).ncard) *
        (Fintype.card X - (MulAction.fixedBy X t).ncard - 2)) *
      Nat.card (centralizingBaseStabilizer e t) := by
  rw [centralizer_card_eq_intertwining_mul_baseCentralizer
    e t Research.SharpFourBound.baseDoubleSwap hbase hcorrect,
    doubleIntertwining_ncard t htwo]

end FiveTransitive.Research.OddFourCentralizer

end CFSG
