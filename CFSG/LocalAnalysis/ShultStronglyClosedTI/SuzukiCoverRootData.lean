module

public import CFSG.StronglyEmbedded.BenderSuzukiCenter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

@[expose] def suzukiCoverTits : K ≃+* K :=
  iterateFrobeniusEquiv K 2 (m + 1)

@[simp] theorem suzukiCoverTits_apply (a : K) :
    suzukiCoverTits m a = a ^ (2 ^ (m + 1)) :=
  iterateFrobeniusEquiv_def K 2 (m + 1) a

theorem suzukiCoverTits_square (a : K) :
    suzukiCoverTits m (suzukiCoverTits m a) = a ^ 2 :=
  binaryGaloisField_tits_formula_sq m (suzukiCoverTits m)
    (suzukiCoverTits_apply m) a

@[expose] def suzukiCoverRootGL : Subgroup (GL (Fin 4) K) :=
  Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}

theorem suzukiCoverRootGL_le : suzukiCoverRootGL m ≤ G := by
  rw [suzukiCoverRootGL, Subgroup.closure_le]
  intro A hA
  exact Subgroup.subset_closure (Or.inl hA)

@[expose] def suzukiCoverRoot : Subgroup G :=
  (suzukiCoverRootGL m).subgroupOf G

@[expose] def suzukiCoverRootBridge : suzukiCoverRoot m ≃* suzukiCoverRootGL m :=
  Subgroup.subgroupOfEquivOfLe (suzukiCoverRootGL_le m)

@[expose] def suzukiCoverRootElement (a b : K) : suzukiCoverRoot m :=
  ⟨⟨SuzukiRootGL m a b,
    suzukiCoverRootGL_le m (Subgroup.subset_closure ⟨a, b, rfl⟩)⟩,
    Subgroup.subset_closure ⟨a, b, rfl⟩⟩

@[simp] theorem suzukiCoverRootElement_coe (a b : K) :
    (((suzukiCoverRootElement m a b : suzukiCoverRoot m) : G) : GL (Fin 4) K) =
      SuzukiRootGL m a b := rfl

theorem suzukiCoverRootElement_injective (a b c d : K)
    (h : suzukiCoverRootElement m a b = suzukiCoverRootElement m c d) :
    a = c ∧ b = d := by
  constructor
  · have h01 := congrArg
      (fun z : suzukiCoverRoot m => (((z : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1) h
    simpa [suzukiCoverRootElement, SuzukiRootGL, SuzukiRootMatrix] using h01
  · have h02 := congrArg
      (fun z : suzukiCoverRoot m => (((z : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) h
    simpa [suzukiCoverRootElement, SuzukiRootGL, SuzukiRootMatrix] using h02

theorem suzukiCoverRootElement_surjective (z : suzukiCoverRoot m) :
    ∃ a b : K, suzukiCoverRootElement m a b = z := by
  obtain ⟨a, b, hab⟩ := (suzukiRootGL_mem_closure_iff m (suzukiCoverTits m)
    (suzukiCoverTits_square m) (suzukiCoverTits_apply m) ((z : G) : GL (Fin 4) K)).mp
      z.property
  refine ⟨a, b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hab.symm

theorem suzukiCoverRootElement_mul (hm : 0 < m) (a b c d : K) :
    suzukiCoverRootElement m a b * suzukiCoverRootElement m c d =
      suzukiCoverRootElement m (a + c) (b + d + a * suzukiCoverTits m c) := by
  rcases huppert_blackburn_XI_3_1 m hm (suzukiCoverTits m) (suzukiCoverTits_square m) with
    ⟨_, _, _, _, _, _, _, _, hmul, _⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hmul a b c d

@[simp] theorem suzukiCoverRootElement_zero_zero :
    suzukiCoverRootElement m 0 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact suzukiRootGL_zero_zero m

@[expose] def suzukiCoverFirstCoord (hm : 0 < m) :
    suzukiCoverRoot m →* Multiplicative K where
  toFun z := Multiplicative.ofAdd ((((z : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1)
  map_one' := by simp
  map_mul' z w := by
    obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m z
    obtain ⟨c, d, rfl⟩ := suzukiCoverRootElement_surjective m w
    rw [suzukiCoverRootElement_mul m hm]
    rfl

@[simp] theorem suzukiCoverFirstCoord_apply (hm : 0 < m) (a b : K) :
    suzukiCoverFirstCoord m hm (suzukiCoverRootElement m a b) =
      Multiplicative.ofAdd a := rfl

theorem suzukiCoverFirstCoord_surjective (hm : 0 < m) :
    Function.Surjective (suzukiCoverFirstCoord m hm) := by
  intro a
  exact ⟨suzukiCoverRootElement m a.toAdd 0, rfl⟩

theorem suzukiCoverRoot_structure (hm : 0 < m) :
    IsPGroup 2 (suzukiCoverRoot m) ∧
      Nat.card (suzukiCoverRoot m) = (2 ^ (2 * m + 1)) ^ 2 ∧
      commutator (suzukiCoverRoot m) = Subgroup.center (suzukiCoverRoot m) ∧
      (∀ z : suzukiCoverRoot m, z ∈ commutator (suzukiCoverRoot m) ↔
        ∃ b : K, z = suzukiCoverRootElement m 0 b) := by
  rcases huppert_blackburn_XI_3_1 m hm (suzukiCoverTits m) (suzukiCoverTits_square m) with
    ⟨_, _, hp, _, _, _, hcard, _, _, hcomm, hcoord, _⟩
  let e := suzukiCoverRootBridge m
  have hmap : (commutator (suzukiCoverRoot m)).map e.toMonoidHom =
      commutator (suzukiCoverRootGL m) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  refine ⟨hp.of_equiv e.symm, (Nat.card_congr e.toEquiv).trans hcard, ?_, ?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact hmap.trans (hcomm.trans (Subgroup.map_center_eq e).symm)
  · intro z
    have hmem : z ∈ commutator (suzukiCoverRoot m) ↔
        e z ∈ commutator (suzukiCoverRootGL m) := by
      rw [← hmap, Subgroup.mem_map_equiv]
      simp only [MulEquiv.symm_apply_apply]
    change (∀ x : suzukiCoverRootGL m, x ∈ commutator (suzukiCoverRootGL m) ↔
      ∃ b : K, (x : GL (Fin 4) K) = SuzukiRootGL m 0 b) at hcoord
    rw [hmem, hcoord (e z)]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hb
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩

theorem suzukiCoverFirstCoord_ker (hm : 0 < m) :
    (suzukiCoverFirstCoord m hm).ker = commutator (suzukiCoverRoot m) := by
  ext z
  obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m z
  rw [(suzukiCoverRoot_structure m hm).2.2.2]
  change a = 0 ↔ ∃ c : K, suzukiCoverRootElement m a b = suzukiCoverRootElement m 0 c
  constructor
  · rintro rfl
    exact ⟨b, rfl⟩
  · rintro ⟨c, hc⟩
    exact (suzukiCoverRootElement_injective m a b 0 c hc).1

@[expose] def suzukiCoverDerivedEquiv (hm : 0 < m) :
    commutator (suzukiCoverRoot m) ≃* Multiplicative K where
  toFun z := Multiplicative.ofAdd
    ((((z.val : suzukiCoverRoot m) : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2
  invFun b := ⟨suzukiCoverRootElement m 0 b.toAdd,
    ((suzukiCoverRoot_structure m hm).2.2.2 _).mpr ⟨b.toAdd, rfl⟩⟩
  left_inv z := by
    obtain ⟨b, hb⟩ := ((suzukiCoverRoot_structure m hm).2.2.2 z.val).mp z.property
    apply Subtype.ext
    change suzukiCoverRootElement m 0
      (((((z.val : suzukiCoverRoot m) : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) = z.val
    rw [hb]
    rfl
  right_inv _ := rfl
  map_mul' z w := by
    obtain ⟨b, hb⟩ := ((suzukiCoverRoot_structure m hm).2.2.2 z.val).mp z.property
    obtain ⟨d, hd⟩ := ((suzukiCoverRoot_structure m hm).2.2.2 w.val).mp w.property
    change Multiplicative.ofAdd
      (((((z.val * w.val : suzukiCoverRoot m) : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) = _
    rw [hb, hd, suzukiCoverRootElement_mul m hm]
    simp only [zero_mul, add_zero]
    rfl

theorem suzukiCoverDerivedEquiv_apply (hm : 0 < m)
    (z : commutator (suzukiCoverRoot m)) :
    (suzukiCoverDerivedEquiv m hm z).toAdd =
      (((((z.val : suzukiCoverRoot m) : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) := rfl

@[expose] def suzukiCoverAbelianEquiv (hm : 0 < m) :
    Abelianization (suzukiCoverRoot m) ≃* Multiplicative K :=
  QuotientGroup.liftEquiv (commutator (suzukiCoverRoot m))
    (suzukiCoverFirstCoord_surjective m hm) (suzukiCoverFirstCoord_ker m hm).symm

@[simp] theorem suzukiCoverAbelianEquiv_of (hm : 0 < m) (z : suzukiCoverRoot m) :
    suzukiCoverAbelianEquiv m hm (Abelianization.of z) = suzukiCoverFirstCoord m hm z :=
  QuotientGroup.liftEquiv_mk _ _ _ z

theorem suzukiCoverRoot_layers_elementary (hm : 0 < m) :
    IsElementaryAbelian 2 (commutator (suzukiCoverRoot m)) ∧
      IsElementaryAbelian 2 (Abelianization (suzukiCoverRoot m)) := by
  have elementary {A : Type} [Group A] (e : A ≃* Multiplicative K) :
      IsElementaryAbelian 2 A := by
    refine
      { toIsMulCommutative := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    apply e.injective
    rw [map_pow, map_one, pow_two]
    exact congrArg Multiplicative.ofAdd (CharTwo.add_self_eq_zero (e x).toAdd)
  exact ⟨elementary (suzukiCoverDerivedEquiv m hm), elementary (suzukiCoverAbelianEquiv m hm)⟩

theorem suzukiCover_native_card (hm : 0 < m) :
    Nat.card G = ((2 ^ (2 * m + 1)) ^ 2 + 1) *
      (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  rcases huppert_blackburn_XI_3_3 m hm (suzukiCoverTits m) (suzukiCoverTits_apply m) with
    ⟨_, _, _, _, _, _, hcard, _⟩
  exact hcard

theorem suzukiCoverRoot_index_odd (hm : 0 < m) :
    Odd (suzukiCoverRoot m).index := by
  let q := 2 ^ (2 * m + 1)
  have hqpos : 0 < q := by positivity
  have hqeven : Even q := by
    exact even_two.pow_of_ne_zero (by omega)
  have hindex : (suzukiCoverRoot m).index = (q ^ 2 + 1) * (q - 1) := by
    have h := (suzukiCoverRoot m).card_mul_index
    rw [(suzukiCoverRoot_structure m hm).2.1, suzukiCover_native_card m hm] at h
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hqpos 2)
    simpa only [q, mul_assoc, mul_left_comm, mul_comm] using h
  rw [hindex]
  exact ((hqeven.pow_of_ne_zero (by decide)).add_odd odd_one).mul
    (Nat.Even.sub_odd hqpos hqeven odd_one)

@[expose] def suzukiCoverSylow (hm : 0 < m) : Sylow 2 G :=
  (suzukiCoverRoot_structure m hm).1.toSylow
    (suzukiCoverRoot_index_odd m hm).not_two_dvd_nat

@[simp] theorem suzukiCoverSylow_coe (hm : 0 < m) :
    (suzukiCoverSylow m hm : Subgroup G) = suzukiCoverRoot m := rfl

theorem suzukiCoverDerived_card (hm : 0 < m) :
    Nat.card (commutator (suzukiCoverRoot m)) = 2 ^ (2 * m + 1) := by
  calc
    Nat.card (commutator (suzukiCoverRoot m)) = Nat.card (Multiplicative K) :=
      Nat.card_congr (suzukiCoverDerivedEquiv m hm).toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd
    _ = 2 ^ (2 * m + 1) := GaloisField.card 2 (2 * m + 1) (by omega)

theorem suzukiCoverDerived_ne_bot (hm : 0 < m) :
    commutator (suzukiCoverRoot m) ≠ ⊥ := by
  intro h
  have hcard := suzukiCoverDerived_card m hm
  rw [h, Subgroup.card_bot] at hcard
  have hlarge : 2 ≤ 2 ^ (2 * m + 1) := Nat.le_pow (by omega)
  omega

end CFSG.ShultStronglyClosedTI
