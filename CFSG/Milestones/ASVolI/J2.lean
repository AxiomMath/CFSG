module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.Milestones.ASVolI.I7
public import CFSG.Milestones.ASVolI.I8
public import CFSG.Milestones.ASVolI.J1
public import CFSG.Quasithin.Background.ASVolIRu.Bridge
public import CFSG.Quasithin.Background.ASVolIRu.StUnique
public import CFSG.Quasithin.Recognition.RuTypeJ29f
public import CFSG.Quasithin.Recognition.RuTypeJ210d
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.Quasithin.Recognition.RuTypeJ24
public import CFSG.Quasithin.Recognition.RuTypeJ25
public import CFSG.Quasithin.Recognition.RuTypeJ26b
public import CFSG.Quasithin.Recognition.RuTypeNorm2
public import CFSG.Quasithin.Recognition.RuTypeJ23d
public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.SuzukiTwoGroupsBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Diag

variable (K : Type) [Field K]

@[expose] noncomputable def conjSL (M : GL (Fin 2) K) : SL(2, K) →* SL(2, K) where
  toFun A := ⟨(M : Matrix (Fin 2) (Fin 2) K) * A *
    ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul]
    simp⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    have h : ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (M : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    show (M : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K) * B) *
        ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((M : Matrix (Fin 2) (Fin 2) K) * A * ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        ((M : Matrix (Fin 2) (Fin 2) K) * B * ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    simp only [mul_assoc]
    rw [← mul_assoc ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      (M : Matrix (Fin 2) (Fin 2) K), h, one_mul]

theorem conjSL_central (M : GL (Fin 2) K) (A : SL(2, K)) (hA : A ∈ Subgroup.center SL(2, K)) :
    conjSL K M A = A := by
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  apply Subtype.ext
  show (M : Matrix (Fin 2) (Fin 2) K) * A * ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A
  rw [← hr, ← (Matrix.scalar_commute r (fun _ => Commute.all _ _)
    (M : Matrix (Fin 2) (Fin 2) K)).eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_one]

@[expose] noncomputable def conjPSL (M : GL (Fin 2) K) : PSL(2, K) →* PSL(2, K) :=
  QuotientGroup.map (Subgroup.center SL(2, K)) (Subgroup.center SL(2, K)) (conjSL K M)
    (fun x hx => by rw [Subgroup.mem_comap, conjSL_central K M x hx]; exact hx)

end Diag

section Ru

variable {G : Type} [Group G]

@[expose] def S0Ru (L B7 : Subgroup G) : Subgroup G := SRu L ⊓ Subgroup.centralizer (B7 : Set G)

@[expose] def InducesTranspositionOn (g : G) (X : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (X : Set G) ∧
    ∃ (e : ↥X ⧸ Subgroup.center ↥X ≃* alternatingGroup (Fin 6)) (τ : Equiv.Perm (Fin 6)),
      τ.IsSwap ∧ ∀ x y : ↥X, (y : G) = g⁻¹ * x * g →
        ((e (y : ↥X ⧸ Subgroup.center ↥X) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
          τ * ((e (x : ↥X ⧸ Subgroup.center ↥X) : alternatingGroup (Fin 6)) :
            Equiv.Perm (Fin 6)) * τ⁻¹

@[expose] def InducesDiagonalOn (g : G) (X : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (X : Set G) ∧
    ∃ (e : ↥X ⧸ Subgroup.center ↥X ≃* PSL(2, GaloisField 3 2))
      (M : GL (Fin 2) (GaloisField 3 2)),
      ¬ IsSquare (Matrix.GeneralLinearGroup.det M) ∧
      ∀ x y : ↥X, (y : G) = g⁻¹ * x * g →
        e (y : ↥X ⧸ Subgroup.center ↥X) = conjPSL (GaloisField 3 2) M (e (x : ↥X ⧸ Subgroup.center ↥X))

end Ru

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def J_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    T ≤ L ∧
    (ZRu T = V ⊓ Subgroup.centralizer (T : Set G) ∧ Nat.card ↥(ZRu T) = 2)

section BurnsideJ1_2146

private theorem burnsideJ1_exists_M (hSt : CFSG.Quasithin.RuType.StUniqueStatement)
    {G : Type} [Group G] [Finite G] {L V T : Subgroup G} (h : CFSG.ASVolI.ChIJK.RuType G L V T) :
    ∃ M : CFSG.Quasithin.RuType.RuDataM G, M.L = L ∧ (M.T : Subgroup G) = T ∧
      V = CFSG.Quasithin.RuType.ruV M.L ∧
      CFSG.ASVolI.ChIJK.ZRu T = CFSG.Quasithin.RuType.ruZ M.T ∧
      CFSG.ASVolI.ChIJK.HRu T = CFSG.Quasithin.RuType.ruH M.T ∧
      CFSG.ASVolI.ChIJK.QRu T = CFSG.Quasithin.RuType.ruQ M.T ∧
      CFSG.ASVolI.ChIJK.URu V T = CFSG.Quasithin.RuType.ruU M.L M.T := by
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM hSt
  have hT : (M.T : Subgroup G) = T := by rw [hMT]; exact h.coe_sylowT
  have hV : V = CFSG.Quasithin.RuType.ruV M.L := by
    rw [hML]; exact CFSG.ASVolI.ChIJK.RuType.V_eq_ruV h
  refine ⟨M, hML, hT, hV, ?_, ?_, ?_, ?_⟩
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.ZRu_eq_ruZ h
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.HRu_eq_ruH h
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.QRu_eq_ruQ h
  · rw [hMT, hML]; exact CFSG.ASVolI.ChIJK.RuType.URu_eq_ruU h

private theorem burnsideJ1_J_2_1_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) :
    CFSG.ASVolI.J_2_1 := by
  intro G _ _ L V T h
  obtain ⟨M, hML, hMT, hV, hZ, -, -, -⟩ := burnsideJ1_exists_M hSt h
  subst hML
  subst hMT
  subst hV
  refine ⟨M.toRuData.T_le_L, ?_, ?_⟩
  · rw [hZ]
    exact M.toRuData.Z_eq
  · rw [hZ]
    exact M.toRuData.card_Z

private theorem burnsideJ1_odd_mem_of_index {G : Type} [Group G] {X : Subgroup G} {x : G} (hx :
    x ∈ X)
    (ho : Odd (orderOf x)) (N : Subgroup ↥X) [N.Normal] {n : ℕ} (hn : N.index = 2 ^ n) :
    (⟨x, hx⟩ : ↥X) ∈ N := by
  have h1 : (QuotientGroup.mk' N) ⟨x, hx⟩ ^ (2 ^ n) = 1 := by
    have h := pow_card_eq_one' (G := ↥X ⧸ N) (x := QuotientGroup.mk' N ⟨x, hx⟩)
    rwa [← Subgroup.index_eq_card, hn] at h
  have h2 : orderOf ((QuotientGroup.mk' N) ⟨x, hx⟩) ∣ orderOf x := by
    have := orderOf_map_dvd (QuotientGroup.mk' N) (⟨x, hx⟩ : ↥X)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf ((QuotientGroup.mk' N) ⟨x, hx⟩) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (orderOf x) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr ho)
  have h4 : orderOf ((QuotientGroup.mk' N) ⟨x, hx⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h3
  rw [orderOf_eq_one_iff] at h4
  exact (QuotientGroup.eq_one_iff _).mp h4

private theorem burnsideJ1_mem_twoResidual_of_odd {G : Type} [Group G] [Finite G] {X : Subgroup
    G} {x : G}
    (hx : x ∈ X) (ho : Odd (orderOf x)) : x ∈ CFSG.ASVolI.ChIJK.twoResidual X := by
  unfold CFSG.ASVolI.ChIJK.twoResidual
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  show (⟨x, hx⟩ : ↥X) ∈ sInf {N : Subgroup ↥X | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}
  rw [Subgroup.mem_sInf]
  rintro N ⟨hN, n, hn⟩
  exact burnsideJ1_odd_mem_of_index hx ho N hn

private theorem burnsideJ1_sylow_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X B₁ B₂ : Subgroup G} (h₁ : CFSG.ASVolI.ChIJK.IsSylowIn p B₁ X)
    (h₂ : CFSG.ASVolI.ChIJK.IsSylowIn p B₂ X) :
    ∃ l ∈ X, ∀ x : G, x ∈ B₂ ↔ l⁻¹ * x * l ∈ B₁ := by
  obtain ⟨hle₁, hp₁, hi₁⟩ := h₁
  obtain ⟨hle₂, hp₂, hi₂⟩ := h₂
  have hP₁ : IsPGroup p ↥(B₁.subgroupOf X) :=
    hp₁.of_equiv (Subgroup.subgroupOfEquivOfLe hle₁).symm
  have hP₂ : IsPGroup p ↥(B₂.subgroupOf X) :=
    hp₂.of_equiv (Subgroup.subgroupOfEquivOfLe hle₂).symm
  let S₁ : Sylow p ↥X := hP₁.toSylow hi₁
  let S₂ : Sylow p ↥X := hP₂.toSylow hi₂
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥X S₁ S₂
  have key : ∀ z : ↥X, z ∈ (S₂ : Subgroup ↥X) ↔ ∃ s ∈ (S₁ : Subgroup ↥X), y * s * y⁻¹ = z := by
    intro z
    rw [← hy, Sylow.coe_subgroup_smul]
    exact Iff.rfl
  refine ⟨y, y.2, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := (key ⟨x, hle₂ hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
    have : s = y⁻¹ * ⟨x, hle₂ hx⟩ * y := by rw [← hsx]; group
    rw [this] at hs
    exact Subgroup.mem_subgroupOf.mp hs
  · intro hx
    have hxX : x ∈ X := by
      have h3 : (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem y.2 (hle₁ hx)) (X.inv_mem y.2)
      have : (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ = x := by group
      rwa [this] at h3
    have hs : (⟨(y : G)⁻¹ * x * y, hle₁ hx⟩ : ↥X) ∈ (S₁ : Subgroup ↥X) :=
      Subgroup.mem_subgroupOf.mpr hx
    have := (key ⟨x, hxX⟩).mpr ⟨_, hs, Subtype.ext (by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group)⟩
    exact Subgroup.mem_subgroupOf.mp this

private theorem burnsideJ1_equiv_conj {G : Type} [Group G] {X₁ X₂ : Subgroup G} (l : G)
    (h : ∀ x : G, x ∈ X₂ ↔ l⁻¹ * x * l ∈ X₁) : Nonempty (↥X₁ ≃* ↥X₂) :=
  ⟨{ toFun := fun x => ⟨l * x * l⁻¹, (h _).mpr (by simpa [mul_assoc] using x.2)⟩
     invFun := fun y => ⟨l⁻¹ * y * l, (h _).mp y.2⟩
     left_inv := fun x => Subtype.ext (by simp [mul_assoc])
     right_inv := fun y => Subtype.ext (by simp [mul_assoc])
     map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }⟩

private theorem burnsideJ1_quotEquiv_conj {G : Type} [Group G] {C₁ C₂ A₁ A₂ : Subgroup G} (l : G)
    (hC : ∀ x : G, x ∈ C₂ ↔ l⁻¹ * x * l ∈ C₁) (hA : ∀ x : G, x ∈ A₂ ↔ l⁻¹ * x * l ∈ A₁)
    [(A₁.subgroupOf C₁).Normal] [(A₂.subgroupOf C₂).Normal] :
    Nonempty ((↥C₁ ⧸ A₁.subgroupOf C₁) ≃* (↥C₂ ⧸ A₂.subgroupOf C₂)) := by
  let e : ↥C₁ ≃* ↥C₂ :=
    { toFun := fun x => ⟨l * x * l⁻¹, (hC _).mpr (by simpa [mul_assoc] using x.2)⟩
      invFun := fun y => ⟨l⁻¹ * y * l, (hC _).mp y.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  refine ⟨QuotientGroup.congr (A₁.subgroupOf C₁) (A₂.subgroupOf C₂) e ?_⟩
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx
    refine (hA _).mpr ?_
    show l⁻¹ * (l * (x : G) * l⁻¹) * l ∈ A₁
    simpa [mul_assoc] using hx
  · intro hy
    refine ⟨e.symm y, Subgroup.mem_subgroupOf.mpr ((hA _).mp hy), e.apply_symm_apply y⟩

private theorem burnsideJ1_L1_le {G : Type} [Group G] (M : CFSG.Quasithin.RuType.RuDataM G) :
    CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) ≤ CFSG.Quasithin.RuType.ruH M.T ⊓ M.L := by
  have hZ : CFSG.ASVolI.ChIJK.ZRu (M.T : Subgroup G) = CFSG.Quasithin.RuType.ruZ M.T :=
    CFSG.ASVolI.ChIJK.RuType.BridgeTwo.centerOf_eq _
  refine (Subgroup.map_subtype_le _).trans (le_of_eq ?_)
  show Subgroup.centralizer (CFSG.ASVolI.ChIJK.ZRu (M.T : Subgroup G) : Set G) ⊓ M.L =
    CFSG.Quasithin.RuType.ruH M.T ⊓ M.L
  rw [hZ]

private theorem burnsideJ1_sylow3_conj {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) {B : Subgroup G}
    (hB : CFSG.ASVolI.ChIJK.IsSylowIn 3 B (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G))) :
    ∃ l ∈ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G), ∀ x : G, x ∈ B ↔ l⁻¹ * x * l ∈ M.B := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hL₁H : CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) ≤ CFSG.Quasithin.RuType.ruH M.T :=
    (burnsideJ1_L1_le M).trans inf_le_left
  have hbel : (M.bel : G) ∈ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) := by
    have hZ : CFSG.ASVolI.ChIJK.ZRu (M.T : Subgroup G) = CFSG.Quasithin.RuType.ruZ M.T :=
      CFSG.ASVolI.ChIJK.RuType.BridgeTwo.centerOf_eq _
    refine burnsideJ1_mem_twoResidual_of_odd ⟨?_, M.bel.2⟩ (by rw [M.orderOf_bel]; decide)
    show (M.bel : G) ∈ Subgroup.centralizer (CFSG.ASVolI.ChIJK.ZRu (M.T : Subgroup G) : Set G)
    rw [hZ]
    exact M.bel_mem_H
  have hSyl : CFSG.ASVolI.ChIJK.IsSylowIn 3 M.B
      (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G)) := by
    refine ⟨Subgroup.zpowers_le.mpr hbel, IsPGroup.of_card (n := 1) (by rw [M.card_B]; norm_num),
      ?_⟩
    rintro ⟨k, hk⟩
    have h1 := Subgroup.card_mul_index
      (M.B.subgroupOf (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G)))
    rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le (Subgroup.zpowers_le.mpr hbel), M.card_B, hk]
      at h1
    have h2 : Nat.card (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G)) ∣
        Nat.card (CFSG.Quasithin.RuType.ruH M.T) := Subgroup.card_dvd_of_le hL₁H
    rw [M.toRuData.card_H] at h2
    have h3 : 9 ∣ 2 ^ 11 * 120 := (Dvd.intro k (by omega)).trans (h1 ▸ h2)
    norm_num at h3
  exact burnsideJ1_sylow_conj hSyl hB

private theorem burnsideJ1_R0_prod :
    ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), g ∈ CFSG.Quasithin.RuType.SL3.R0 →
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      a ∈ CFSG.Quasithin.RuType.SL3.Stab0 ∧ a ^ 3 = 1 ∧
      a⁻¹ * g ∈ CFSG.Quasithin.RuType.SL3.Stab0 ∧ (a⁻¹ * g) ^ 3 = 1 := by
  decide +kernel

private theorem burnsideJ1_sigma_prod : ∀ X : CFSG.Quasithin.RuType.SigmaL2F4, X.right = 1 →
    ∃ a : CFSG.Quasithin.RuType.SigmaL2F4, a ^ 5 = 1 ∧ (a⁻¹ * X) ^ 5 = 1 := by
  decide +kernel

private theorem burnsideJ1_decomp : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.trace = 0 →
    B = (B 0 1).val • (!![0, 1, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      (B 0 2).val • (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      (B 1 0).val • (!![0, 0, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      (B 1 2).val • (!![0, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      (B 2 0).val • (!![0, 0, 0; 0, 0, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      (B 2 1).val • (!![0, 0, 0; 0, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      (B 0 0).val • (!![1, 0, 0; 0, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
      (B 1 1).val • (!![0, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  decide +kernel

private theorem burnsideJ1_span (E : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hE : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      g ∈ CFSG.Quasithin.RuType.SL3.Stab0 → g ^ 3 = 1 →
      ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), CFSG.Quasithin.RuType.IsTraceZero A →
        CFSG.Quasithin.RuType.stAct g A - A ∈ E) :
    ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), CFSG.Quasithin.RuType.IsTraceZero B → B ∈ E := by
  have key : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)), g ∈ CFSG.Quasithin.RuType.SL3.Stab0 →
      g ^ 3 = 1 → CFSG.Quasithin.RuType.IsTraceZero A →
      CFSG.Quasithin.RuType.stAct g A - A = B → B ∈ E :=
    fun g A B hg hg3 hA hB => hB ▸ hE g hg hg3 A hA
  have key2 : ∀ (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (A₁ A₂ B : Matrix (Fin 3) (Fin 3) (ZMod 2)), g₁ ∈ CFSG.Quasithin.RuType.SL3.Stab0 →
      g₁ ^ 3 = 1 → g₂ ∈ CFSG.Quasithin.RuType.SL3.Stab0 → g₂ ^ 3 = 1 →
      CFSG.Quasithin.RuType.IsTraceZero A₁ → CFSG.Quasithin.RuType.IsTraceZero A₂ →
      (CFSG.Quasithin.RuType.stAct g₁ A₁ - A₁) + (CFSG.Quasithin.RuType.stAct g₂ A₂ - A₂) = B →
      B ∈ E :=
    fun g₁ g₂ A₁ A₂ B h₁ h₁3 h₂ h₂3 hA₁ hA₂ hB => hB ▸ add_mem (hE g₁ h₁ h₁3 A₁ hA₁)
      (hE g₂ h₂ h₂3 A₂ hA₂)
  let g0 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩
  let g1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![1, 1, 0; 0, 0, 1; 0, 1, 1], by decide⟩
  let g2 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![1, 0, 1; 0, 0, 1; 0, 1, 1], by decide⟩
  have hg0 : g0 ∈ CFSG.Quasithin.RuType.SL3.Stab0 :=
    CFSG.Quasithin.RuType.SL3.mem_Stab0.mpr (by decide +kernel)
  have hg1 : g1 ∈ CFSG.Quasithin.RuType.SL3.Stab0 :=
    CFSG.Quasithin.RuType.SL3.mem_Stab0.mpr (by decide +kernel)
  have hg2 : g2 ∈ CFSG.Quasithin.RuType.SL3.Stab0 :=
    CFSG.Quasithin.RuType.SL3.mem_Stab0.mpr (by decide +kernel)
  have hg03 : g0 ^ 3 = 1 := by decide +kernel
  have hg13 : g1 ^ 3 = 1 := by decide +kernel
  have hg23 : g2 ^ 3 = 1 := by decide +kernel
  have e01 : (!![0, 1, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key g0 !![0, 1, 1; 0, 0, 0; 0, 0, 0] _ hg0 hg03 (by decide) (by decide +kernel)
  have e02 : (!![0, 0, 1; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key g0 !![0, 1, 0; 0, 0, 0; 0, 0, 0] _ hg0 hg03 (by decide) (by decide +kernel)
  have e10 : (!![0, 0, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key g0 !![0, 0, 0; 0, 0, 0; 1, 0, 0] _ hg0 hg03 (by decide) (by decide +kernel)
  have e20 : (!![0, 0, 0; 0, 0, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key g0 !![0, 0, 0; 1, 0, 0; 1, 0, 0] _ hg0 hg03 (by decide) (by decide +kernel)
  have e12 : (!![0, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key2 g0 g1 !![0, 0, 0; 0, 0, 0; 1, 0, 0] !![0, 1, 0; 0, 1, 1; 1, 1, 1] _ hg0 hg03 hg1 hg13
      (by decide) (by decide) (by decide +kernel)
  have e21 : (!![0, 0, 0; 0, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key2 g0 g1 !![0, 0, 0; 0, 0, 0; 1, 0, 0] !![0, 0, 0; 0, 0, 0; 1, 1, 0] _ hg0 hg03 hg1 hg13
      (by decide) (by decide) (by decide +kernel)
  have d0 : (!![1, 0, 0; 0, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key2 g0 g2 !![0, 0, 0; 0, 0, 0; 1, 0, 0] !![0, 0, 1; 0, 1, 1; 1, 1, 1] _ hg0 hg03 hg2 hg23
      (by decide) (by decide) (by decide +kernel)
  have d1 : (!![0, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ E :=
    key2 g0 g1 !![0, 0, 0; 0, 0, 0; 1, 0, 0] !![0, 1, 0; 0, 1, 1; 1, 0, 1] _ hg0 hg03 hg1 hg13
      (by decide) (by decide) (by decide +kernel)
  intro B hB
  rw [burnsideJ1_decomp B hB]
  exact add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (nsmul_mem e01 _)
    (nsmul_mem e02 _)) (nsmul_mem e10 _)) (nsmul_mem e12 _)) (nsmul_mem e20 _))
    (nsmul_mem e21 _)) (nsmul_mem d0 _)) (nsmul_mem d1 _)

private theorem burnsideJ1_lift3 {G : Type} [Group G] [Finite G] (M :
    CFSG.Quasithin.RuType.RuDataM G)
    (W : Subgroup G)
    (hWodd : ∀ x ∈ CFSG.Quasithin.RuType.ruH M.T, Odd (orderOf x) → x ∈ W)
    {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hg : g ∈ CFSG.Quasithin.RuType.SL3.Stab0) (hg3 : g ^ 3 = 1) :
    ∃ w : M.L, M.θ w = g ∧ (w : G) ∈ W := by
  obtain ⟨w, hwθ, hw3⟩ := M.exists_lift hg3 (by norm_num)
  have hwH : (w : G) ∈ CFSG.Quasithin.RuType.ruH M.T := by
    have h1 : (w : G) ∈ M.LT1 := CFSG.Quasithin.RuType.mem_pullL.mpr ⟨w.2, by
      rw [show (⟨(w : G), w.2⟩ : M.L) = w from rfl, hwθ]
      exact hg⟩
    exact M.LT1_le_H h1
  refine ⟨w, hwθ, hWodd _ hwH ?_⟩
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hw3)

private theorem burnsideJ1_S_le {G : Type} [Group G] [Finite G] (M :
    CFSG.Quasithin.RuType.RuDataM G)
    (W : Subgroup G)
    (hWn : ∀ h ∈ CFSG.Quasithin.RuType.ruH M.T, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hWodd : ∀ x ∈ CFSG.Quasithin.RuType.ruH M.T, Odd (orderOf x) → x ∈ W) :
    CFSG.Quasithin.RuType.ruS M.L ≤ W := by
  let E : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    { carrier := {B | ∃ y : CFSG.Quasithin.RuType.ruS M.L, (y : G) ∈ W ∧
        Multiplicative.toAdd (M.χ y) = B}
      add_mem' := by
        rintro _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ * y₂, W.mul_mem hy₁ hy₂, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, W.one_mem, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, W.inv_mem hy, by rw [map_inv, toAdd_inv] <;> rfl⟩ }
  have hE : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      g ∈ CFSG.Quasithin.RuType.SL3.Stab0 → g ^ 3 = 1 →
      ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), CFSG.Quasithin.RuType.IsTraceZero A →
        CFSG.Quasithin.RuType.stAct g A - A ∈ E := by
    intro g hg hg3 A hA
    obtain ⟨s, hs⟩ := M.χ_surj A hA
    obtain ⟨w, hwθ, hwW⟩ := burnsideJ1_lift3 M W hWodd hg hg3
    have hsH : (s : G) ∈ CFSG.Quasithin.RuType.ruH M.T :=
      M.toRuData.T_le_H (M.toRuData.S_le_T s.2)
    have hwsS : (w : G) * s * (w : G)⁻¹ ∈ CFSG.Quasithin.RuType.ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L w.2)
        s).mp s.2
    set t : CFSG.Quasithin.RuType.ruS M.L := ⟨(w : G) * s * (w : G)⁻¹, hwsS⟩ with ht
    have hχt : M.χ t = Multiplicative.ofAdd (CFSG.Quasithin.RuType.stAct g A) := by
      rw [M.χ_equiv w s t rfl, hwθ, hs, toAdd_ofAdd]
    refine ⟨t * s⁻¹, ?_, ?_⟩
    · have h1 : (s : G) * (w : G)⁻¹ * (s : G)⁻¹ ∈ W := hWn _ hsH _ (W.inv_mem hwW)
      have h2 : (w : G) * ((s : G) * (w : G)⁻¹ * (s : G)⁻¹) ∈ W := W.mul_mem hwW h1
      have e : ((t * s⁻¹ : CFSG.Quasithin.RuType.ruS M.L) : G) =
          (w : G) * ((s : G) * (w : G)⁻¹ * (s : G)⁻¹) := by
        simp only [ht, Subgroup.coe_mul, InvMemClass.coe_inv]
        group
      rw [e]
      exact h2
    · rw [map_mul, map_inv, hχt, hs, toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd]
      exact (sub_eq_add_neg _ _).symm
  have hspan := burnsideJ1_span E hE
  have hdec : ∀ s ∈ CFSG.Quasithin.RuType.ruS M.L, ∃ y ∈ CFSG.Quasithin.RuType.ruS M.L, y ∈ W ∧
      ∃ v ∈ CFSG.Quasithin.RuType.ruV M.L, s = y * v := by
    intro s hs
    obtain ⟨y, hyW, hy⟩ := hspan _ (M.χ_trace ⟨s, hs⟩)
    refine ⟨y, y.2, hyW, (y : G)⁻¹ * s, ?_, by group⟩
    have hk : y⁻¹ * ⟨s, hs⟩ ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.mpr (Multiplicative.toAdd.injective hy)
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hV : CFSG.Quasithin.RuType.ruV M.L ≤ W := by
    have hc : CFSG.Quasithin.RuType.ruV M.L =
        ⁅CFSG.Quasithin.RuType.ruS M.L, CFSG.Quasithin.RuType.ruS M.L⁆ :=
      M.one.center_eq_commutator
    rw [hc, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨y₁, hy₁S, hy₁W, v₁, hv₁, rfl⟩ := hdec a ha
    obtain ⟨y₂, hy₂S, hy₂W, v₂, hv₂, rfl⟩ := hdec b hb
    have hcomm : ∀ s ∈ CFSG.Quasithin.RuType.ruS M.L, ∀ v ∈ CFSG.Quasithin.RuType.ruV M.L,
        s * v = v * s := fun s hs v hv => (M.toRuData.mem_V_iff.mp hv).2 s hs
    have h1 : v₁ * y₂ = y₂ * v₁ := (hcomm y₂ hy₂S v₁ hv₁).symm
    have h2 : v₂ * y₁⁻¹ = y₁⁻¹ * v₂ :=
      (hcomm y₁⁻¹ ((CFSG.Quasithin.RuType.ruS M.L).inv_mem hy₁S) v₂ hv₂).symm
    have h3 : v₁ * v₂ = v₂ * v₁ := (hcomm v₂ (M.toRuData.V_le_S hv₂) v₁ hv₁).symm
    have e : y₁ * v₁ * (y₂ * v₂) * (y₁ * v₁)⁻¹ * (y₂ * v₂)⁻¹ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
      calc y₁ * v₁ * (y₂ * v₂) * (y₁ * v₁)⁻¹ * (y₂ * v₂)⁻¹
          = y₁ * (v₁ * y₂) * v₂ * v₁⁻¹ * y₁⁻¹ * v₂⁻¹ * y₂⁻¹ := by group
        _ = y₁ * (y₂ * v₁) * v₂ * v₁⁻¹ * y₁⁻¹ * v₂⁻¹ * y₂⁻¹ := by rw [h1]
        _ = y₁ * y₂ * (v₁ * v₂) * v₁⁻¹ * y₁⁻¹ * v₂⁻¹ * y₂⁻¹ := by group
        _ = y₁ * y₂ * (v₂ * v₁) * v₁⁻¹ * y₁⁻¹ * v₂⁻¹ * y₂⁻¹ := by rw [h3]
        _ = y₁ * y₂ * (v₂ * y₁⁻¹) * v₂⁻¹ * y₂⁻¹ := by group
        _ = y₁ * y₂ * (y₁⁻¹ * v₂) * v₂⁻¹ * y₂⁻¹ := by rw [h2]
        _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by group
    rw [commutatorElement_def, e]
    exact W.mul_mem (W.mul_mem (W.mul_mem hy₁W hy₂W) (W.inv_mem hy₁W)) (W.inv_mem hy₂W)
  intro s hs
  obtain ⟨y, -, hyW, v, hv, rfl⟩ := hdec s hs
  exact W.mul_mem hyW (hV hv)

private theorem burnsideJ1_Q_le {G : Type} [Group G] [Finite G] (M :
    CFSG.Quasithin.RuType.RuDataM G)
    (W : Subgroup G)
    (hWn : ∀ h ∈ CFSG.Quasithin.RuType.ruH M.T, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hWodd : ∀ x ∈ CFSG.Quasithin.RuType.ruH M.T, Odd (orderOf x) → x ∈ W) :
    CFSG.Quasithin.RuType.ruQ M.T ≤ W := by
  intro q hq
  have hqL : q ∈ M.L := M.Q_le_L hq
  have hθ : M.θ ⟨q, hqL⟩ ∈ CFSG.Quasithin.RuType.SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨q, hqL⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  obtain ⟨a, ha, ha3, ha', ha'3⟩ := burnsideJ1_R0_prod _ hθ
  obtain ⟨w₁, hw₁θ, hw₁W⟩ := burnsideJ1_lift3 M W hWodd ha ha3
  obtain ⟨w₂, hw₂θ, hw₂W⟩ := burnsideJ1_lift3 M W hWodd ha' ha'3
  have hk : (⟨q, hqL⟩ : M.L) * (w₁ * w₂)⁻¹ ∈ M.θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hw₁θ, hw₂θ,
      show a * (a⁻¹ * M.θ ⟨q, hqL⟩) = M.θ ⟨q, hqL⟩ by group, mul_inv_cancel]
  rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
  have hkW : q * ((w₁ : G) * w₂)⁻¹ ∈ W := burnsideJ1_S_le M W hWn hWodd hk
  have e : q = q * ((w₁ : G) * w₂)⁻¹ * ((w₁ : G) * w₂) := by group
  rw [e]
  exact W.mul_mem hkW (W.mul_mem hw₁W hw₂W)

private theorem burnsideJ1_K_le {G : Type} [Group G] [Finite G] (M :
    CFSG.Quasithin.RuType.RuDataM G)
    (W : Subgroup G)
    (hWn : ∀ h ∈ CFSG.Quasithin.RuType.ruH M.T, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hWodd : ∀ x ∈ CFSG.Quasithin.RuType.ruH M.T, Odd (orderOf x) → x ∈ W) :
    M.K ≤ W := by
  intro k hk
  obtain ⟨hkH, hk1⟩ := M.mem_K_iff.mp hk
  obtain ⟨a, ha5, hb5⟩ := burnsideJ1_sigma_prod (M.φ ⟨k, hkH⟩) hk1
  obtain ⟨c₁, hc₁φ, hc₁5⟩ := M.exists_lift_pow_five ha5
  obtain ⟨c₂, hc₂φ, hc₂5⟩ := M.exists_lift_pow_five hb5
  have hodd : ∀ c : CFSG.Quasithin.RuType.ruH M.T, (c : G) ^ 5 = 1 → (c : G) ∈ W := fun c hc5 =>
    hWodd c c.2 (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hc5))
  have hq : (⟨k, hkH⟩ : CFSG.Quasithin.RuType.ruH M.T) * (c₁ * c₂)⁻¹ ∈ M.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hc₁φ, hc₂φ,
      show a * (a⁻¹ * M.φ ⟨k, hkH⟩) = M.φ ⟨k, hkH⟩ by group, mul_inv_cancel]
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hq
  have hqW : k * ((c₁ : G) * c₂)⁻¹ ∈ W := burnsideJ1_Q_le M W hWn hWodd hq
  have e : k = k * ((c₁ : G) * c₂)⁻¹ * ((c₁ : G) * c₂) := by group
  rw [e]
  exact W.mul_mem hqW (W.mul_mem (hodd c₁ hc₁5) (hodd c₂ hc₂5))

private theorem burnsideJ1_twoResidual_eq_K {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) :
    CFSG.ASVolI.ChIJK.twoResidual (CFSG.Quasithin.RuType.ruH M.T) = M.K := by
  refine le_antisymm ?_ ?_
  ·
    have hker : M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T) =
        (SemidirectProduct.rightHom.comp M.φ).ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply,
        CFSG.Quasithin.RuType.RuDataN.mem_K_iff]
      constructor
      · rintro ⟨_, h1⟩
        exact h1
      · intro h1
        exact ⟨x.2, h1⟩
    have hKn : (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T)).Normal := by
      rw [hker]
      infer_instance
    have hKi : (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T)).index = 2 ^ 1 := by
      rw [hker, Subgroup.index_ker]
      have hr : (SemidirectProduct.rightHom.comp M.φ).range = ⊤ := by
        rw [MonoidHom.range_eq_top]
        exact SemidirectProduct.rightHom_surjective.comp M.φ_surj
      rw [hr, Subgroup.card_top, Nat.card_eq_fintype_card]
      rfl
    calc CFSG.ASVolI.ChIJK.twoResidual (CFSG.Quasithin.RuType.ruH M.T)
        = (sInf {N : Subgroup ↥(CFSG.Quasithin.RuType.ruH M.T) |
            N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}).map
              (CFSG.Quasithin.RuType.ruH M.T).subtype := rfl
      _ ≤ (M.K.subgroupOf (CFSG.Quasithin.RuType.ruH M.T)).map
            (CFSG.Quasithin.RuType.ruH M.T).subtype :=
          Subgroup.map_mono (sInf_le ⟨hKn, 1, hKi⟩)
      _ = M.K := Subgroup.map_subgroupOf_eq_of_le M.K_le_H
  · intro k hk
    have hkH : k ∈ CFSG.Quasithin.RuType.ruH M.T := M.K_le_H hk
    refine ⟨⟨k, hkH⟩, ?_, rfl⟩
    show (⟨k, hkH⟩ : ↥(CFSG.Quasithin.RuType.ruH M.T)) ∈
      sInf {N : Subgroup ↥(CFSG.Quasithin.RuType.ruH M.T) |
        N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}
    rw [Subgroup.mem_sInf]
    rintro N ⟨hN, n, hn⟩
    have hmem := burnsideJ1_K_le M (N.map (CFSG.Quasithin.RuType.ruH M.T).subtype)
      (by
        rintro h hh _ ⟨x, hx, rfl⟩
        exact ⟨⟨h, hh⟩ * x * ⟨h, hh⟩⁻¹, hN.conj_mem x hx _, rfl⟩)
      (fun x hx ho => ⟨⟨x, hx⟩, burnsideJ1_odd_mem_of_index hx ho N hn, rfl⟩) hk
    obtain ⟨y, hy, hyk⟩ := hmem
    have : y = ⟨k, hkH⟩ := Subtype.ext hyk
    rwa [this] at hy

private theorem burnsideJ1_mem_conjClass_iff {G : Type} [Group G] (z x : G) :
    x ∈ CFSG.ASVolI.ChIJK.conjClass z ↔ IsConj z x := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩

private theorem burnsideJ1_eq_z {G : Type} [Group G] [Finite G] (M :
    CFSG.Quasithin.RuType.RuDataM G)
    {z : G} (hz : Subgroup.zpowers z = CFSG.Quasithin.RuType.ruZ M.T) : z = M.z := by
  have hzmem : z ∈ CFSG.Quasithin.RuType.ruZ M.T := by
    rw [← hz]
    exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have h2 := M.toRuData.card_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h2
    omega
  · exact h1

end BurnsideJ1_2146

theorem as_J_2_1 : J_2_1 :=
  burnsideJ1_J_2_1_of_st CFSG.Quasithin.RuType.stUnique

@[expose] def J_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    (HRu T ⊓ L = L1Ru L T ⊔ T ∧ QRu T ⊔ SRu L = pCoreOf 2 (L1Ru L T ⊔ T) ∧
      pCoreOf 2 (L1Ru L T ⊔ T) = R1Ru L T ∧ QRu T ≤ KRu T) ∧
    (IsElemAbelian 2 (URu V T) ∧ Nat.card ↥(URu V T) = 32) ∧
    ((∀ x : G, x ∈ HCRu V T ↔
        (x ∈ QRu T ∧ ∀ k ∈ KRu T, x⁻¹ * k⁻¹ * x * k ∈ URu V T)) ∧
      ∃ (_ : ((QRu T).subgroupOf (KRu T)).Normal)
        (e : ↥(KRu T) ⧸ (QRu T).subgroupOf (KRu T) ≃* Matrix.SpecialLinearGroup (Fin 2) F4),
        IsConjModuleIso (KRu T) (QRu T) (HCRu V T) (Fin 2 → F4)
          (fun k v => ((e (k : ↥(KRu T) ⧸ (QRu T).subgroupOf (KRu T)) :
            Matrix.SpecialLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4).mulVec v)) ∧
    (∀ t : ↥(URu V T) ≃* ↥(URu V T),
      (∀ u : ↥(URu V T), (t u : G) * (u : G)⁻¹ ∈ ZRu T) ↔
        ∃ q ∈ QRu T, ∀ u : ↥(URu V T), (t u : G) = q⁻¹ * u * q) ∧
    (∀ l ∈ L, CFSG.conjugate (URu V T) l ≠ URu V T →
      Nat.card ↥(((CFSG.conjugate (URu V T) l).subgroupOf (HRu T)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(HRu T)))) = 2 ∧
        V = CFSG.conjugate (URu V T) l ⊓ HCRu V T)

@[expose] def J_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
        (S0Ru L B7 = ⁅S0Ru L B7, B⁆ ∧ IsElemAbelian 2 (S0Ru L B7) ∧
          Nat.card ↥(S0Ru L B7) = 4) ∧
        (∀ g : G, g⁻¹ * z * g ∉ S0Ru L B7) ∧
        (Subgroup.centralizer ({s} : Set G) ⊓ L =
            S0Ru L B7 ⊔ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ ⊔ B7 ∧
          IsDirectProductOf (S0Ru L B7) ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆
            (SRu L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
          IsSylowTwoIn (SRu L ⊓ Subgroup.centralizer ({s} : Set G))
            (Subgroup.centralizer ({s} : Set G) ⊓ L) ∧
          Nat.card ↥(SRu L ⊓ Subgroup.centralizer ({s} : Set G)) = 2 ^ 8 ∧
          Monoid.exponent ↥(SRu L ⊓ Subgroup.centralizer ({s} : Set G)) = 4) ∧
        (B ≤ Subgroup.normalizer ((SRu L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) ∧
          B ≤ Subgroup.normalizer ((S0Ru L B7 : Subgroup G) : Set G) ∧
          B ≤ Subgroup.normalizer
            ((⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ : Subgroup G) : Set G)) ∧
        (IsSuzukiTwoGroup ↥⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ ∧
          ∃ a ∈ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆,
            ∃ b ∈ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆, a * b ≠ b * a) ∧
        (∀ t ∈ SRu L, t ∉ V →
          ⁅Subgroup.zpowers t, SRu L⁆ = V ∧
          V.relIndex (SRu L ⊓ Subgroup.centralizer ({t} : Set G)) = 2 ^ 5) ∧
        Nonempty (↥(QRu T ⊓ Subgroup.centralizer (B : Set G)) ≃* QuaternionGroup 2) ∧
        (∀ x : G, x ∈ URu V T ↔ (x ∈ SRu L ∧ ∀ r ∈ R1Ru L T, x⁻¹ * r⁻¹ * x * r ∈ V)) ∧
        (∀ l ∈ L, l ∉ HRu T → URu V T ⊓ CFSG.conjugate (URu V T) l = V)

section BurnsideJ2b

private theorem burnsideJ2b_twoResidual_eq {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    CFSG.ASVolI.ChIJK.twoResidual X = CFSG.Quasithin.twoResidual X := by
  apply le_antisymm
  · refine le_iInf fun N => le_iInf fun hN => ?_
    obtain ⟨hNX, hXN, h2⟩ := hN
    have hnorm : (N.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN
    have hidx : ∃ n : ℕ, (N.subgroupOf X).index = 2 ^ n := by
      have hp : IsPGroup 2 (↥X ⧸ N.subgroupOf X) := by
        intro g
        induction g using QuotientGroup.induction_on with
        | H x =>
          obtain ⟨k, hk⟩ := h2 x x.2
          refine ⟨k, ?_⟩
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.2 (by simpa using hk)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
      exact ⟨n, by rw [Subgroup.index_eq_card, hn]⟩
    have h1 : sInf {N' : Subgroup ↥X | N'.Normal ∧ ∃ n : ℕ, N'.index = 2 ^ n} ≤
        N.subgroupOf X := sInf_le ⟨hnorm, hidx⟩
    have h3 := Subgroup.map_mono (f := X.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hNX] at h3
  · intro a ha
    rw [CFSG.Quasithin.mem_twoResidual_iff] at ha
    have haX : a ∈ X :=
      ha X le_rfl Subgroup.le_normalizer fun y hy => ⟨0, by simpa using hy⟩
    refine ⟨⟨a, haX⟩, ?_, rfl⟩
    show (⟨a, haX⟩ : ↥X) ∈ sInf {N' : Subgroup ↥X | N'.Normal ∧ ∃ n : ℕ, N'.index = 2 ^ n}
    rw [Subgroup.mem_sInf]
    rintro N' ⟨hN', n, hn⟩
    have h1 : a ∈ N'.map X.subtype := by
      refine ha (N'.map X.subtype) (Subgroup.map_subtype_le _) ?_ ?_
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹, hN'.conj_mem z hz _, rfl⟩
        · rintro ⟨z, hz, hzy⟩
          refine ⟨⟨x, hx⟩⁻¹ * z * ⟨x, hx⟩, by simpa using hN'.conj_mem z hz ⟨x, hx⟩⁻¹, ?_⟩
          have : (x : G)⁻¹ * (z : G) * x = x⁻¹ * (x * y * x⁻¹) * x := by rw [← hzy]; rfl
          show (x : G)⁻¹ * (z : G) * x = y
          rw [this]
          group
      · intro y hy
        refine ⟨n, ?_⟩
        have h2 : (QuotientGroup.mk (⟨y, hy⟩ : ↥X) : ↥X ⧸ N') ^ 2 ^ n = 1 := by
          have h := pow_card_eq_one' (G := ↥X ⧸ N') (x := QuotientGroup.mk ⟨y, hy⟩)
          rwa [← Subgroup.index_eq_card, hn] at h
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
        exact ⟨_, h2, rfl⟩
    obtain ⟨z, hz, hza⟩ := h1
    have : z = ⟨a, haX⟩ := Subtype.ext hza
    rwa [this] at hz

private theorem burnsideJ2b_twoResidual_mono {G : Type} [Group G] [Finite G] {X Y : Subgroup G}
    (h : X ≤ Y) : CFSG.Quasithin.twoResidual X ≤ CFSG.Quasithin.twoResidual Y := by
  refine le_trans (CFSG.Quasithin.twoResidual_le_of_isTwoQuotient
    (H := X) (N := CFSG.Quasithin.twoResidual Y ⊓ X) inf_le_right ?_ ?_) inf_le_left
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.Quasithin.le_normalizer_twoResidual Y (h hx), Subgroup.le_normalizer hx⟩
  · intro y hy
    obtain ⟨k, hk⟩ := CFSG.Quasithin.twoResidual_isTwoQuotient Y y (h hy)
    exact ⟨k, Subgroup.mem_inf.2 ⟨hk, X.pow_mem hy _⟩⟩

private theorem burnsideJ2b_lift {G : Type} [Group G] [Finite G] {X : Subgroup G} {B : Type}
    [Group B]
    (π : ↥X →* B) {b : B} {m : ℕ} (hm1 : 1 < m) (hmo : Odd m) (hb : b ^ m = 1) (l₀ : ↥X)
    (hl₀ : π l₀ = b) :
    ∃ l : ↥X, (l : G) ∈ CFSG.Quasithin.twoResidual X ∧ π l = b := by
  obtain ⟨a, ha⟩ := CFSG.Quasithin.twoResidual_isTwoQuotient X l₀ l₀.2
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hmo)
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm1
  refine ⟨l₀ ^ (2 ^ a * j), ?_, ?_⟩
  · have : ((l₀ ^ (2 ^ a * j) : ↥X) : G) = ((l₀ : G) ^ 2 ^ a) ^ j := by
      rw [Subgroup.coe_pow, pow_mul]
    rw [this]
    exact (CFSG.Quasithin.twoResidual X).pow_mem ha j
  · rw [map_pow, hl₀]
    have h1 : 2 ^ a * j = m * (2 ^ a * j / m) + 1 := by
      have := Nat.div_add_mod (2 ^ a * j) m
      omega
    rw [h1, pow_succ, pow_mul, hb, one_pow, one_mul]

private theorem burnsideJ2b_R0_prod : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
    g ∈ CFSG.Quasithin.RuType.SL3.R0 →
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), a ∈ CFSG.Quasithin.RuType.SL3.Stab0 ∧
      a ^ 3 = 1 ∧ a⁻¹ * g ∈ CFSG.Quasithin.RuType.SL3.Stab0 ∧ (a⁻¹ * g) ^ 3 = 1 := by
  decide +kernel

@[expose] def burnsideJ2b_g0 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

@[expose] def burnsideJ2b_g2 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 0, 1; 0, 1, 1], by decide⟩

@[expose] def burnsideJ2b_B1 : Fin 8 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![0, 0, 0; 1, 0, 0; 1, 0, 0], !![0, 0, 0; 0, 0, 0; 1, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
    !![0, 0, 0; 1, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0]]

@[expose] def burnsideJ2b_B2 : Fin 8 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![0, 0, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
    !![0, 0, 0; 1, 0, 1; 0, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 1],
    !![0, 0, 1; 0, 1, 0; 0, 0, 1], !![0, 0, 0; 0, 0, 1; 1, 1, 0]]

private theorem burnsideJ2b_g0_mem : burnsideJ2b_g0 ∈ CFSG.Quasithin.RuType.SL3.Stab0 := by
  decide +kernel

private theorem burnsideJ2b_g2_mem : burnsideJ2b_g2 ∈ CFSG.Quasithin.RuType.SL3.Stab0 := by
  decide +kernel

private theorem burnsideJ2b_g0_pow : burnsideJ2b_g0 ^ 3 = 1 := by
  decide +kernel

private theorem burnsideJ2b_g2_pow : burnsideJ2b_g2 ^ 3 = 1 := by
  decide +kernel

private theorem burnsideJ2b_B_trace : ∀ i : Fin 8,
    (burnsideJ2b_B1 i).trace = 0 ∧ (burnsideJ2b_B2 i).trace = 0 := by
  decide +kernel

private theorem burnsideJ2b_stBasis_decomp : ∀ i : Fin 8,
    CFSG.Quasithin.RuType.SL3.stBasis i =
      (CFSG.Quasithin.RuType.stAct burnsideJ2b_g0 (burnsideJ2b_B1 i) - burnsideJ2b_B1 i) +
      (CFSG.Quasithin.RuType.stAct burnsideJ2b_g2 (burnsideJ2b_B2 i) - burnsideJ2b_B2 i) := by
  decide +kernel

private theorem burnsideJ2b_lift_theta {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hg : g ∈ CFSG.Quasithin.RuType.SL3.Stab0) (h3 : g ^ 3 = 1) :
    ∃ l : G, l ∈ CFSG.Quasithin.twoResidual N.LT1 ∧ ∃ hl : l ∈ N.L, N.θ ⟨l, hl⟩ = g := by
  obtain ⟨l₀, hl₀⟩ := N.θ_surj g
  have hmem : (l₀ : G) ∈ N.LT1 :=
    CFSG.Quasithin.RuType.mem_pullL.mpr ⟨l₀.2, by
      rw [show (⟨(l₀ : G), l₀.2⟩ : ↥N.L) = l₀ from rfl, hl₀]
      exact hg⟩
  obtain ⟨l, hlK, hl⟩ := burnsideJ2b_lift (N.θ.comp (Subgroup.inclusion N.LT1_le_L))
    (b := g) (m := 3) (by norm_num) (by decide) h3 ⟨l₀, hmem⟩ hl₀
  exact ⟨l, hlK, N.LT1_le_L l.2, hl⟩

private theorem burnsideJ2b_S_le_L1 {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) :
    CFSG.Quasithin.RuType.ruS N.L ≤ CFSG.Quasithin.twoResidual N.LT1 := by
  set K1 := CFSG.Quasithin.twoResidual N.LT1 with hK1
  have hK1LT : K1 ≤ N.LT1 := CFSG.Quasithin.twoResidual_le _
  have hnorm : ∀ x ∈ N.LT1, ∀ y ∈ K1, x * y * x⁻¹ ∈ K1 := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.Quasithin.le_normalizer_twoResidual _ hx) y).mp hy
  let Y : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    { carrier := {A | ∃ w : CFSG.Quasithin.RuType.ruS N.L, (w : G) ∈ K1 ∧
        N.χ w = Multiplicative.ofAdd A}
      zero_mem' := ⟨1, K1.one_mem, by rw [map_one]; rfl⟩
      add_mem' := by
        rintro A B ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨w * w', K1.mul_mem hw hw', by rw [map_mul]; rfl⟩
      neg_mem' := by
        rintro A ⟨w, hw, hwA⟩
        refine ⟨w⁻¹, K1.inv_mem hw, ?_⟩
        rw [map_inv, hwA]
        rfl }
  have hcob : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      g ∈ CFSG.Quasithin.RuType.SL3.Stab0 → g ^ 3 = 1 →
      ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.trace = 0 →
        CFSG.Quasithin.RuType.stAct g B - B ∈ Y := by
    intro g hg h3 B hB
    obtain ⟨s, hs⟩ := N.χ_surj B hB
    obtain ⟨l, hlK, hlL, hθ⟩ := burnsideJ2b_lift_theta N hg h3
    have hconj : l * (s : G) * l⁻¹ ∈ CFSG.Quasithin.RuType.ruS N.L :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N.L hlL) s).mp s.2
    let t : CFSG.Quasithin.RuType.ruS N.L := ⟨l * s * l⁻¹, hconj⟩
    have ht : N.χ t = Multiplicative.ofAdd (CFSG.Quasithin.RuType.stAct g B) := by
      rw [N.χ_equiv ⟨l, hlL⟩ s t rfl, hθ, hs, toAdd_ofAdd]
    refine ⟨t * s⁻¹, ?_, ?_⟩
    · have e : ((t * s⁻¹ : CFSG.Quasithin.RuType.ruS N.L) : G) = l * ((s : G) * l⁻¹ * (s : G)⁻¹) := by
        show l * (s : G) * l⁻¹ * (s : G)⁻¹ = l * ((s : G) * l⁻¹ * (s : G)⁻¹)
        group
      rw [e]
      refine K1.mul_mem hlK ?_
      have hsLT : (s : G) ∈ N.LT1 := N.S_le_pullL _ s.2
      exact hnorm s hsLT l⁻¹ (K1.inv_mem hlK)
    · rw [map_mul, map_inv, ht, hs, ← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg]
  have hY : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → A ∈ Y := by
    intro A hA
    obtain ⟨c, rfl⟩ := CFSG.Quasithin.RuType.SL3.exists_stComb hA
    unfold CFSG.Quasithin.RuType.SL3.stComb
    refine AddSubgroup.sum_mem Y fun i _ => ?_
    have hMi : CFSG.Quasithin.RuType.SL3.stBasis i ∈ Y := by
      rw [burnsideJ2b_stBasis_decomp i]
      exact Y.add_mem
        (hcob _ burnsideJ2b_g0_mem burnsideJ2b_g0_pow _ (burnsideJ2b_B_trace i).1)
        (hcob _ burnsideJ2b_g2_mem burnsideJ2b_g2_pow _ (burnsideJ2b_B_trace i).2)
    have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hc (c i) with h | h
    · rw [h, zero_smul]
      exact Y.zero_mem
    · rw [h, one_smul]
      exact hMi
  have hdec : ∀ s : CFSG.Quasithin.RuType.ruS N.L, ∃ w : CFSG.Quasithin.RuType.ruS N.L,
      (w : G) ∈ K1 ∧ ((w⁻¹ * s : CFSG.Quasithin.RuType.ruS N.L) : G) ∈
        CFSG.Quasithin.RuType.ruV N.L := by
    intro s
    obtain ⟨w, hw, hws⟩ := hY _ (N.χ_trace s)
    refine ⟨w, hw, ?_⟩
    have hk : w⁻¹ * s ∈ N.χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hws, ofAdd_toAdd]
      exact inv_mul_cancel _
    rw [N.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hVK : CFSG.Quasithin.RuType.ruV N.L ≤ K1 := by
    rw [show CFSG.Quasithin.RuType.ruV N.L = ⁅CFSG.Quasithin.RuType.ruS N.L,
      CFSG.Quasithin.RuType.ruS N.L⁆ from N.one.center_eq_commutator, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨wa, hwaK, hva⟩ := hdec ⟨a, ha⟩
    obtain ⟨wb, hwbK, hvb⟩ := hdec ⟨b, hb⟩
    have hvaS := (N.toRuData.mem_V_iff.mp hva).2
    have hvbS := (N.toRuData.mem_V_iff.mp hvb).2
    have hvaS' := (N.toRuData.mem_V_iff.mp hva).1
    have hvbS' := (N.toRuData.mem_V_iff.mp hvb).1
    set va : G := ((wa⁻¹ * ⟨a, ha⟩ : CFSG.Quasithin.RuType.ruS N.L) : G) with hva_def
    set vb : G := ((wb⁻¹ * ⟨b, hb⟩ : CFSG.Quasithin.RuType.ruS N.L) : G) with hvb_def
    have hea : a = (wa : G) * va := by simp [va]
    have heb : b = (wb : G) * vb := by simp [vb]
    have h1 : va * (wb : G) = (wb : G) * va := (hvaS wb wb.2).symm
    have h2 : va * vb = vb * va := (hvaS vb hvbS').symm
    have h3 : vb * (wa : G)⁻¹ = (wa : G)⁻¹ * vb := (hvbS _ (inv_mem wa.2)).symm
    rw [commutatorElement_def]
    have key : a * b * a⁻¹ * b⁻¹ = (wa : G) * wb * (wa : G)⁻¹ * (wb : G)⁻¹ := by
      rw [hea, heb]
      calc ((wa : G) * va) * ((wb : G) * vb) * ((wa : G) * va)⁻¹ * ((wb : G) * vb)⁻¹
          = wa * (va * wb) * vb * va⁻¹ * (wa : G)⁻¹ * vb⁻¹ * (wb : G)⁻¹ := by group
        _ = wa * (wb * va) * vb * va⁻¹ * (wa : G)⁻¹ * vb⁻¹ * (wb : G)⁻¹ := by rw [h1]
        _ = wa * wb * (va * vb) * va⁻¹ * (wa : G)⁻¹ * vb⁻¹ * (wb : G)⁻¹ := by group
        _ = wa * wb * (vb * va) * va⁻¹ * (wa : G)⁻¹ * vb⁻¹ * (wb : G)⁻¹ := by rw [h2]
        _ = wa * wb * (vb * (wa : G)⁻¹) * vb⁻¹ * (wb : G)⁻¹ := by group
        _ = wa * wb * ((wa : G)⁻¹ * vb) * vb⁻¹ * (wb : G)⁻¹ := by rw [h3]
        _ = (wa : G) * wb * (wa : G)⁻¹ * (wb : G)⁻¹ := by group
    rw [key]
    exact K1.mul_mem (K1.mul_mem (K1.mul_mem hwaK hwbK) (K1.inv_mem hwaK)) (K1.inv_mem hwbK)
  intro s hs
  obtain ⟨w, hwK, hv⟩ := hdec ⟨s, hs⟩
  have : s = (w : G) * (((w⁻¹ * ⟨s, hs⟩ : CFSG.Quasithin.RuType.ruS N.L)) : G) := by simp
  rw [this]
  exact K1.mul_mem hwK (hVK hv)

private theorem burnsideJ2b_R1_le_L1 {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) :
    N.R1 ≤ CFSG.Quasithin.twoResidual N.LT1 := by
  intro r hr
  obtain ⟨hrL, hrR⟩ := CFSG.Quasithin.RuType.mem_pullL.mp hr
  obtain ⟨a, ha, ha3, hb, hb3⟩ := burnsideJ2b_R0_prod _ hrR
  obtain ⟨la, hlaK, hlaL, hθa⟩ := burnsideJ2b_lift_theta N ha ha3
  obtain ⟨lb, hlbK, hlbL, hθb⟩ := burnsideJ2b_lift_theta N hb hb3
  have hc : la * lb ∈ CFSG.Quasithin.twoResidual N.LT1 :=
    (CFSG.Quasithin.twoResidual N.LT1).mul_mem hlaK hlbK
  have hθc : N.θ ⟨la * lb, N.L.mul_mem hlaL hlbL⟩ = N.θ ⟨r, hrL⟩ := by
    rw [show (⟨la * lb, N.L.mul_mem hlaL hlbL⟩ : ↥N.L) = ⟨la, hlaL⟩ * ⟨lb, hlbL⟩ from rfl,
      map_mul, hθa, hθb, mul_inv_cancel_left]
  have hk : (⟨la * lb, N.L.mul_mem hlaL hlbL⟩ : ↥N.L)⁻¹ * ⟨r, hrL⟩ ∈ N.θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθc, inv_mul_cancel]
  rw [N.θ_ker, Subgroup.mem_subgroupOf] at hk
  have e : r = (la * lb) * ((la * lb)⁻¹ * r) := by group
  rw [e]
  exact (CFSG.Quasithin.twoResidual N.LT1).mul_mem hc (burnsideJ2b_S_le_L1 N hk)

private theorem burnsideJ2b_normal_two_le_R0
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) (hXp : IsPGroup 2 X)
    (hXle : X ≤ CFSG.Quasithin.RuType.SL3.Stab0)
    (hXnorm : ∀ g ∈ CFSG.Quasithin.RuType.SL3.Stab0, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    X ≤ CFSG.Quasithin.RuType.SL3.R0 := by
  intro x hx
  by_contra hxR
  have hx4 : x ^ 4 = 1 := by
    apply CFSG.Quasithin.RuType.SL3.pow_four_of_pow_eight
    obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk
      simpa using this)
    have hdvd' : orderOf x ∣ 168 := by
      rw [← CFSG.Quasithin.RuType.SL3.card_SL3]
      exact orderOf_dvd_natCard x
    have : orderOf x ∣ 8 := by
      have h1 : orderOf x ∣ Nat.gcd (2 ^ k) 168 := Nat.dvd_gcd hdvd hdvd'
      have h2 : Nat.gcd (2 ^ k) 168 ∣ 8 := by
        have : Nat.gcd (2 ^ k) 168 ∣ 2 ^ k := Nat.gcd_dvd_left _ _
        obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
        rw [hj']
        have : 2 ^ j ∣ 168 := hj' ▸ Nat.gcd_dvd_right _ _
        have hj3 : j ≤ 3 :=
          CFSG.Quasithin.RuType.RuDataN.le_of_two_pow_dvd (a := 3) (b := j) (c := 21)
            (by rw [show 2 ^ 3 * 21 = 168 by norm_num]; exact this) (by norm_num)
        exact Nat.pow_dvd_pow 2 hj3
      exact h1.trans h2
    exact orderOf_dvd_iff_pow_eq_one.mp this
  obtain ⟨g, hg, hne, h3⟩ :=
    CFSG.Quasithin.RuType.SL3.exists_comm_order_three x (hXle hx) hxR hx4
  have hmem : x * g * x⁻¹ * g⁻¹ ∈ X := by
    have := X.mul_mem hx (hXnorm g hg _ (X.inv_mem hx))
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hXp ⟨_, hmem⟩
  have hk' : (x * g * x⁻¹ * g⁻¹) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  apply hne
  have h1 : orderOf (x * g * x⁻¹ * g⁻¹) ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h3)
  have h2 : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.pow_left _ (by norm_num)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

private theorem burnsideJ2b_pCoreOf_LT1 {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) : pCoreOf 2 N.LT1 = N.R1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR1LT : N.R1 ≤ N.LT1 := fun r hr => by
    obtain ⟨h, hx⟩ := CFSG.Quasithin.RuType.mem_pullL.mp hr
    exact CFSG.Quasithin.RuType.mem_pullL.mpr ⟨h, CFSG.Quasithin.RuType.SL3.R0_le_Stab0 hx⟩
  have hkey : ∀ l ∈ N.LT1, ∀ x ∈ N.R1, l * x * l⁻¹ ∈ N.R1 := by
    intro l hl x hx
    obtain ⟨hlL, hlS⟩ := CFSG.Quasithin.RuType.mem_pullL.mp hl
    obtain ⟨hxL, hxR⟩ := CFSG.Quasithin.RuType.mem_pullL.mp hx
    refine CFSG.Quasithin.RuType.mem_pullL.mpr ⟨N.L.mul_mem (N.L.mul_mem hlL hxL) (N.L.inv_mem hlL), ?_⟩
    rw [show (⟨l * x * l⁻¹, N.L.mul_mem (N.L.mul_mem hlL hxL) (N.L.inv_mem hlL)⟩ : ↥N.L) =
      ⟨l, hlL⟩ * ⟨x, hxL⟩ * ⟨l, hlL⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
    exact CFSG.Quasithin.RuType.SL3.conj_mem_R0 _ hlS _ hxR
  apply le_antisymm
  · intro q hq
    have hPp : IsPGroup 2 (pCoreOf 2 N.LT1) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hPLT : pCoreOf 2 N.LT1 ≤ N.LT1 := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hPnorm : N.LT1 ≤ Subgroup.normalizer (pCoreOf 2 N.LT1 : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hPL : pCoreOf 2 N.LT1 ≤ N.L := hPLT.trans N.LT1_le_L
    set X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      ((pCoreOf 2 N.LT1).subgroupOf N.L).map N.θ with hX
    have hXp : IsPGroup 2 X :=
      (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm).map N.θ
    have hXle : X ≤ CFSG.Quasithin.RuType.SL3.Stab0 := by
      rintro _ ⟨⟨x, hxL⟩, hx, rfl⟩
      exact (CFSG.Quasithin.RuType.mem_pullL.mp (hPLT (Subgroup.mem_subgroupOf.mp hx))).2
    have hXnorm : ∀ g ∈ CFSG.Quasithin.RuType.SL3.Stab0, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
      rintro g hg _ ⟨⟨x, hxL⟩, hx, rfl⟩
      obtain ⟨⟨l, hlL⟩, rfl⟩ := N.θ_surj g
      have hlLT : l ∈ N.LT1 := CFSG.Quasithin.RuType.mem_pullL.mpr ⟨hlL, hg⟩
      have hx' : x ∈ pCoreOf 2 N.LT1 := Subgroup.mem_subgroupOf.mp hx
      have hmem : l * x * l⁻¹ ∈ pCoreOf 2 N.LT1 :=
        (Subgroup.mem_normalizer_iff.mp (hPnorm hlLT) x).mp hx'
      refine ⟨⟨l * x * l⁻¹, hPL hmem⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
      rw [show (⟨l * x * l⁻¹, hPL hmem⟩ : ↥N.L) = ⟨l, hlL⟩ * ⟨x, hxL⟩ * ⟨l, hlL⟩⁻¹ from rfl,
        map_mul, map_mul, map_inv]
    have hXR := burnsideJ2b_normal_two_le_R0 X hXp hXle hXnorm
    exact CFSG.Quasithin.RuType.mem_pullL.mpr ⟨hPL hq, hXR
      ⟨⟨q, hPL hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR1LT ?_
      (IsPGroup.of_card (n := 13) (by rw [N.card_R1]))
    exact fun l hl => CFSG.Quasithin.B6.mem_normalizer_of_forall_mem (hkey l hl)
      (fun x hx => by simpa using hkey l⁻¹ (N.LT1.inv_mem hl) x hx)

private theorem burnsideJ2b_T_sylow_LT1 {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) :
    CFSG.QuasithinUnique.IsSylowTwoOf (N.T : Subgroup G) N.LT1 := by
  have hT : (N.T : Subgroup G) ≤ N.LT1 := by
    rw [← N.L_inf_H]
    exact le_inf N.toRuData.T_le_L N.toRuData.T_le_H
  refine ⟨hT, N.T.isPGroup', ?_⟩
  have h1 := Subgroup.relIndex_mul_index hT
  intro h2
  apply N.T.not_dvd_index
  rw [← h1]
  exact dvd_mul_of_dvd_left h2 _

private theorem burnsideJ2b_part1 {G : Type} [Group G] [Finite G] (N :
    CFSG.Quasithin.RuType.RuDataN G) :
    (CFSG.Quasithin.RuType.ruH N.T ⊓ N.L =
        CFSG.Quasithin.twoResidual N.LT1 ⊔ (N.T : Subgroup G)) ∧
    (CFSG.Quasithin.RuType.ruQ N.T ⊔ CFSG.Quasithin.RuType.ruS N.L =
        pCoreOf 2 (CFSG.Quasithin.twoResidual N.LT1 ⊔ (N.T : Subgroup G))) ∧
    (pCoreOf 2 (CFSG.Quasithin.twoResidual N.LT1 ⊔ (N.T : Subgroup G)) =
        pCoreOf 2 (CFSG.Quasithin.twoResidual N.LT1)) ∧
    (CFSG.Quasithin.RuType.ruQ N.T ≤ CFSG.Quasithin.twoResidual (CFSG.Quasithin.RuType.ruH N.T)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : CFSG.Quasithin.twoResidual N.LT1 ⊔ (N.T : Subgroup G) = N.LT1 := by
    rw [sup_comm]
    exact CFSG.Quasithin.sup_twoResidual_eq (burnsideJ2b_T_sylow_LT1 N)
  have hHL : CFSG.Quasithin.RuType.ruH N.T ⊓ N.L = N.LT1 := by
    rw [inf_comm]
    exact N.L_inf_H
  have hR1 := burnsideJ2b_pCoreOf_LT1 N
  have hR1K : N.R1 ≤ CFSG.Quasithin.twoResidual N.LT1 := burnsideJ2b_R1_le_L1 N
  refine ⟨by rw [hsup, hHL], by rw [hsup, hR1, N.Q_sup_S], ?_, ?_⟩
  · rw [hsup, hR1]
    apply le_antisymm
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR1K ?_
        (IsPGroup.of_card (n := 13) (by rw [N.card_R1]))
      intro l hl
      have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N.LT1
        (CFSG.Quasithin.twoResidual_le _ hl)
      rwa [hR1] at this
    · rw [← hR1]
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (CFSG.Quasithin.twoResidual_le _)) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      exact (CFSG.Quasithin.le_normalizer_twoResidual N.LT1).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  · refine (N.Q_sup_S ▸ (le_sup_left : CFSG.Quasithin.RuType.ruQ N.T ≤
      CFSG.Quasithin.RuType.ruQ N.T ⊔ CFSG.Quasithin.RuType.ruS N.L)).trans ?_
    exact hR1K.trans (burnsideJ2b_twoResidual_mono N.LT1_le_H)

private theorem burnsideJ2b_K_eq {G : Type} [Group G] [Finite G] (N :
    CFSG.Quasithin.RuType.RuDataN G) :
    CFSG.Quasithin.twoResidual (CFSG.Quasithin.RuType.ruH N.T) = N.K := by
  apply le_antisymm
  · have hconj : ∀ x ∈ CFSG.Quasithin.RuType.ruH N.T, ∀ k ∈ N.K, x * k * x⁻¹ ∈ N.K := by
      intro x hx k hk
      obtain ⟨hkH, hk1⟩ := N.mem_K_iff.mp hk
      refine N.mem_K_iff.mpr ⟨mul_mem (mul_mem hx hkH) (inv_mem hx), ?_⟩
      have e : N.φ ⟨x * k * x⁻¹, mul_mem (mul_mem hx hkH) (inv_mem hx)⟩ =
          N.φ ⟨x, hx⟩ * N.φ ⟨k, hkH⟩ * (N.φ ⟨x, hx⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      show SemidirectProduct.rightHom (N.φ ⟨x, hx⟩ * N.φ ⟨k, hkH⟩ * (N.φ ⟨x, hx⟩)⁻¹) = 1
      rw [map_mul, map_mul, map_inv]
      show SemidirectProduct.rightHom (N.φ ⟨x, hx⟩) * (N.φ ⟨k, hkH⟩).right *
        (SemidirectProduct.rightHom (N.φ ⟨x, hx⟩))⁻¹ = 1
      rw [hk1, mul_one, mul_inv_cancel]
    refine CFSG.Quasithin.twoResidual_le_of_isTwoQuotient N.K_le_H ?_ ?_
    · intro x hx
      refine CFSG.Quasithin.B6.mem_normalizer_of_forall_mem (hconj x hx) (fun k hk => ?_)
      simpa using hconj x⁻¹ (inv_mem hx) k hk
    · intro y hy
      refine ⟨1, ?_⟩
      refine N.mem_K_iff.mpr ⟨by simpa using pow_mem hy 2, ?_⟩
      have e : N.φ ⟨y ^ 2 ^ 1, by simpa using pow_mem hy 2⟩ = (N.φ ⟨y, hy⟩) ^ 2 := by
        rw [← map_pow]
        rfl
      have h2 : ∀ r : Multiplicative (ZMod 2), r ^ 2 = 1 := by decide
      rw [e]
      show SemidirectProduct.rightHom ((N.φ ⟨y, hy⟩) ^ 2) = 1
      rw [map_pow]
      exact h2 _
  · intro k hk
    obtain ⟨hkH, hk1⟩ := N.mem_K_iff.mp hk
    set A := (N.φ ⟨k, hkH⟩).left with hA
    have hφk : N.φ ⟨k, hkH⟩ = SemidirectProduct.inl A := by
      ext
      · rfl
      · exact hk1
    obtain ⟨C, hC5, hD5⟩ := CFSG.Quasithin.RuType.Sigma.exists_mul_pow_five A
    obtain ⟨c₀, hc₀⟩ := N.φ_surj (SemidirectProduct.inl C)
    obtain ⟨c, hc, hφc⟩ := burnsideJ2b_lift N.φ (m := 5) (by norm_num) (by decide)
      (b := SemidirectProduct.inl C) (by rw [← map_pow, hC5, map_one]) c₀ hc₀
    obtain ⟨d₀, hd₀⟩ := N.φ_surj (SemidirectProduct.inl (C⁻¹ * A))
    obtain ⟨d, hd, hφd⟩ := burnsideJ2b_lift N.φ (m := 5) (by norm_num) (by decide)
      (b := SemidirectProduct.inl (C⁻¹ * A)) (by rw [← map_pow, hD5, map_one]) d₀ hd₀
    have hcd : N.φ (c * d) = N.φ ⟨k, hkH⟩ := by
      rw [map_mul, hφc, hφd, hφk, ← map_mul, mul_inv_cancel_left]
    have hq : (c * d)⁻¹ * ⟨k, hkH⟩ ∈ N.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcd, inv_mul_cancel]
    rw [N.φ_ker, Subgroup.mem_subgroupOf] at hq
    have hQK : (((c * d)⁻¹ * ⟨k, hkH⟩ : ↥(CFSG.Quasithin.RuType.ruH N.T)) : G) ∈
        CFSG.Quasithin.twoResidual (CFSG.Quasithin.RuType.ruH N.T) :=
      (burnsideJ2b_part1 N).2.2.2 hq
    have e : k = ((c * d : ↥(CFSG.Quasithin.RuType.ruH N.T)) : G) *
        (((c * d)⁻¹ * ⟨k, hkH⟩ : ↥(CFSG.Quasithin.RuType.ruH N.T)) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact mul_mem (mul_mem hc hd) hQK

private theorem burnsideJ2b_part3a {G : Type} [Group G] [Finite G] (N :
    CFSG.Quasithin.RuType.RuDataN G)
    (x : G) : x ∈ N.HC ↔ (x ∈ CFSG.Quasithin.RuType.ruQ N.T ∧
      ∀ k ∈ N.K, x⁻¹ * k⁻¹ * x * k ∈ CFSG.Quasithin.RuType.ruU N.L N.T) := by
  constructor
  · intro hx
    have hxQ := N.HC_le_Q hx
    refine ⟨hxQ, fun k hk => ?_⟩
    have h1 := (N.comm_K_mem_U_iff hxQ).mpr hx k⁻¹ (N.K.inv_mem hk)
    have hxH : x ∈ CFSG.Quasithin.RuType.ruH N.T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hxQ
    have h2 := N.conj_mem_U (inv_mem hxH) h1
    have e : x⁻¹ * k⁻¹ * x * k = x⁻¹ * (k⁻¹ * x * k⁻¹⁻¹ * x⁻¹) * x⁻¹⁻¹ := by group
    rw [e]
    exact h2
  · rintro ⟨hxQ, h⟩
    refine (N.comm_K_mem_U_iff hxQ).mp (fun k hk => ?_)
    have h1 := h k⁻¹ (N.K.inv_mem hk)
    have hxH : x ∈ CFSG.Quasithin.RuType.ruH N.T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hxQ
    have h2 := N.conj_mem_U hxH h1
    have e : k * x * k⁻¹ * x⁻¹ = x * (x⁻¹ * k⁻¹⁻¹ * x * k⁻¹) * x⁻¹ := by group
    rw [e]
    exact h2

private theorem burnsideJ2b_K_right {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) (k : ↥N.K) :
    (N.φ ⟨k, N.K_le_H k.2⟩).right = 1 :=
  (N.mem_K_iff.mp k.2).choose_spec

@[expose] noncomputable def burnsideJ2b_fK {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) :
    ↥N.K →* Matrix.SpecialLinearGroup (Fin 2) CFSG.ASVolI.ChIJK.F4 where
  toFun k := Matrix.SpecialLinearGroup.map
    ((CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4).symm :
      CFSG.Quasithin.RuType.F4 →+* CFSG.ASVolI.ChIJK.F4) (N.φ ⟨k, N.K_le_H k.2⟩).left
  map_one' := by
    have : (N.φ ⟨((1 : ↥N.K) : G), N.K_le_H (1 : ↥N.K).2⟩).left = 1 := by
      have e : (⟨((1 : ↥N.K) : G), N.K_le_H (1 : ↥N.K).2⟩ : ↥(CFSG.Quasithin.RuType.ruH N.T)) = 1 :=
        rfl
      rw [e, map_one]
      rfl
    rw [this, map_one]
  map_mul' k₁ k₂ := by
    have e : (⟨((k₁ * k₂ : ↥N.K) : G), N.K_le_H (k₁ * k₂ : ↥N.K).2⟩ :
        ↥(CFSG.Quasithin.RuType.ruH N.T)) =
        ⟨k₁, N.K_le_H k₁.2⟩ * ⟨k₂, N.K_le_H k₂.2⟩ := rfl
    have hr := burnsideJ2b_K_right N k₁
    rw [e, map_mul, SemidirectProduct.mul_left, hr, map_one, MulAut.one_apply, map_mul]

private theorem burnsideJ2b_fK_surj {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) : Function.Surjective (burnsideJ2b_fK N) := by
  intro A
  let Ac : Matrix.SpecialLinearGroup (Fin 2) CFSG.Quasithin.RuType.F4 :=
    Matrix.SpecialLinearGroup.map
      (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4 : CFSG.ASVolI.ChIJK.F4 →+* CFSG.Quasithin.RuType.F4) A
  obtain ⟨h, hh⟩ := N.φ_surj (SemidirectProduct.inl Ac)
  have hhK : (h : G) ∈ N.K := N.mem_K_iff.mpr ⟨h.2, by rw [show (⟨(h : G), h.2⟩ :
    ↥(CFSG.Quasithin.RuType.ruH N.T)) = h from rfl, hh]; rfl⟩
  refine ⟨⟨h, hhK⟩, ?_⟩
  show Matrix.SpecialLinearGroup.map _ (N.φ ⟨(h : G), N.K_le_H hhK⟩).left = A
  rw [show (⟨(h : G), N.K_le_H hhK⟩ : ↥(CFSG.Quasithin.RuType.ruH N.T)) = h from rfl, hh]
  ext i j
  simp [Ac]

private theorem burnsideJ2b_fK_ker {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) (k : ↥N.K) :
    burnsideJ2b_fK N k = 1 ↔ (k : G) ∈ CFSG.Quasithin.RuType.ruQ N.T := by
  have hr := burnsideJ2b_K_right N k
  constructor
  · intro h
    have hleft : (N.φ ⟨k, N.K_le_H k.2⟩).left = 1 := by
      have h1 : Matrix.SpecialLinearGroup.map
          (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4 : CFSG.ASVolI.ChIJK.F4 →+* CFSG.Quasithin.RuType.F4)
          (burnsideJ2b_fK N k) = 1 := by rw [h, map_one]
      have h2 : Matrix.SpecialLinearGroup.map
          (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4 : CFSG.ASVolI.ChIJK.F4 →+* CFSG.Quasithin.RuType.F4)
          (burnsideJ2b_fK N k) = (N.φ ⟨k, N.K_le_H k.2⟩).left := by
        ext i j
        simp [burnsideJ2b_fK]
      rw [← h2]
      exact h1
    have h1 : N.φ ⟨k, N.K_le_H k.2⟩ = 1 := SemidirectProduct.ext hleft hr
    have hk : (⟨k, N.K_le_H k.2⟩ : ↥(CFSG.Quasithin.RuType.ruH N.T)) ∈ N.φ.ker := h1
    rw [N.φ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  · intro hq
    have h1 : N.φ ⟨k, N.K_le_H k.2⟩ = 1 := by
      have hk : (⟨k, N.K_le_H k.2⟩ : ↥(CFSG.Quasithin.RuType.ruH N.T)) ∈ N.φ.ker := by
        rw [N.φ_ker, Subgroup.mem_subgroupOf]
        exact hq
      exact hk
    show Matrix.SpecialLinearGroup.map _ (N.φ ⟨k, N.K_le_H k.2⟩).left = 1
    rw [h1]
    exact map_one _

@[expose] noncomputable def burnsideJ2b_psiQ {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) :
    ↥(CFSG.Quasithin.RuType.ruQ N.T) →* Multiplicative (Fin 2 → CFSG.ASVolI.ChIJK.F4) where
  toFun q := Multiplicative.ofAdd
    (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4.symm (Multiplicative.toAdd (N.ψQ q)))
  map_one' := by simp
  map_mul' a b := by simp [map_add]

private theorem burnsideJ2b_E4_symm_mulVec
    (A : Matrix.SpecialLinearGroup (Fin 2) CFSG.Quasithin.RuType.F4)
    (w : Fin 2 → CFSG.Quasithin.RuType.F4) :
    CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4.symm
        ((A : Matrix (Fin 2) (Fin 2) CFSG.Quasithin.RuType.F4).mulVec w) =
      ((Matrix.SpecialLinearGroup.map
        (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4.symm :
          CFSG.Quasithin.RuType.F4 →+* CFSG.ASVolI.ChIJK.F4) A :
        Matrix.SpecialLinearGroup (Fin 2) CFSG.ASVolI.ChIJK.F4) :
          Matrix (Fin 2) (Fin 2) CFSG.ASVolI.ChIJK.F4).mulVec
        (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4.symm w) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  show CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4.symm (∑ j, (A : Matrix (Fin 2) (Fin 2) _) i j * w j) =
    ∑ j, CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4.symm ((A : Matrix (Fin 2) (Fin 2) _) i j) *
      CFSG.ASVolI.ChIJK.RuType.BridgeTwo.e4.symm (w j)
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]

private theorem burnsideJ2b_part3b {G : Type} [Group G] [Finite G]
    (N : CFSG.Quasithin.RuType.RuDataN G) :
    ∃ (_ : ((CFSG.Quasithin.RuType.ruQ N.T).subgroupOf N.K).Normal)
      (e : ↥N.K ⧸ (CFSG.Quasithin.RuType.ruQ N.T).subgroupOf N.K ≃*
        Matrix.SpecialLinearGroup (Fin 2) CFSG.ASVolI.ChIJK.F4),
      CFSG.ASVolI.ChIJK.IsConjModuleIso N.K (CFSG.Quasithin.RuType.ruQ N.T) N.HC
        (Fin 2 → CFSG.ASVolI.ChIJK.F4)
        (fun k v => ((e (k : ↥N.K ⧸ (CFSG.Quasithin.RuType.ruQ N.T).subgroupOf N.K) :
          Matrix.SpecialLinearGroup (Fin 2) CFSG.ASVolI.ChIJK.F4) :
            Matrix (Fin 2) (Fin 2) CFSG.ASVolI.ChIJK.F4).mulVec v) := by
  have hQK : CFSG.Quasithin.RuType.ruQ N.T ≤ N.K :=
    (burnsideJ2b_K_eq N) ▸ (burnsideJ2b_part1 N).2.2.2
  have hKnorm : N.K ≤ Subgroup.normalizer (CFSG.Quasithin.RuType.ruQ N.T : Set G) :=
    N.K_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hnormal : ((CFSG.Quasithin.RuType.ruQ N.T).subgroupOf N.K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).2 hKnorm
  have hker : (burnsideJ2b_fK N).ker = (CFSG.Quasithin.RuType.ruQ N.T).subgroupOf N.K := by
    ext k
    rw [MonoidHom.mem_ker, burnsideJ2b_fK_ker, Subgroup.mem_subgroupOf]
  let e : ↥N.K ⧸ (CFSG.Quasithin.RuType.ruQ N.T).subgroupOf N.K ≃*
      Matrix.SpecialLinearGroup (Fin 2) CFSG.ASVolI.ChIJK.F4 :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (burnsideJ2b_fK_surj N))
  have he : ∀ k : ↥N.K,
      e (k : ↥N.K ⧸ (CFSG.Quasithin.RuType.ruQ N.T).subgroupOf N.K) = burnsideJ2b_fK N k :=
    fun k => rfl
  refine ⟨hnormal, e, hKnorm, ?_, burnsideJ2b_psiQ N, ?_, ?_, ?_⟩
  · intro k hk
    refine CFSG.Quasithin.B6.mem_normalizer_of_forall_mem (fun x hx => ?_) (fun x hx => ?_)
    · exact N.conj_mem_HC (N.K_le_H hk) hx
    · simpa using N.conj_mem_HC (inv_mem (N.K_le_H hk)) hx
  · intro m
    obtain ⟨q, hq⟩ := N.ψQ_surjective (Multiplicative.ofAdd
      (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4 (Multiplicative.toAdd m)))
    refine ⟨q, ?_⟩
    show Multiplicative.ofAdd (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4.symm
      (Multiplicative.toAdd (N.ψQ q))) = m
    rw [hq, toAdd_ofAdd, AddEquiv.symm_apply_apply, ofAdd_toAdd]
  · ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hψ : burnsideJ2b_psiQ N q = 1 ↔ N.ψQ q = 1 := by
      constructor
      · intro h
        have h1 : CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4.symm (Multiplicative.toAdd (N.ψQ q)) = 0 := by
          have := congrArg Multiplicative.toAdd h
          simpa [burnsideJ2b_psiQ] using this
        have h2 : Multiplicative.toAdd (N.ψQ q) = 0 := by
          simpa using h1
        exact Multiplicative.toAdd.injective (by rw [h2, toAdd_one])
      · intro h
        simp [burnsideJ2b_psiQ, h]
    rw [hψ]
    have := N.ψQ_ker
    constructor
    · intro h
      have hmem : q ∈ N.ψQ.ker := h
      rw [N.ψQ_ker, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    · intro h
      have hmem : q ∈ N.ψQ.ker := by
        rw [N.ψQ_ker, Subgroup.mem_subgroupOf]
        exact h
      exact hmem
  · intro x p q hq
    have hxH : (x : G) ∈ CFSG.Quasithin.RuType.ruH N.T := N.K_le_H x.2
    have hqe : q = ⟨(x : G) * p * (x : G)⁻¹, hq ▸ q.2⟩ := Subtype.ext hq
    have h1 := N.ψQ_conj ⟨x, hxH⟩ p
    have hφx : N.φ ⟨x, hxH⟩ = SemidirectProduct.inl (N.φ ⟨x, hxH⟩).left :=
      SemidirectProduct.ext rfl (burnsideJ2b_K_right N x)
    have h2 : Multiplicative.toAdd (N.ψQ q) =
        ((N.φ ⟨x, hxH⟩).left : Matrix (Fin 2) (Fin 2) CFSG.Quasithin.RuType.F4).mulVec
          (Multiplicative.toAdd (N.ψQ p)) := by
      rw [hqe, h1, hφx]
      exact CFSG.Quasithin.RuType.Sigma.sigmaAct_inl _ _
    show Multiplicative.ofAdd (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4.symm
        (Multiplicative.toAdd (N.ψQ q))) =
      Multiplicative.ofAdd (((burnsideJ2b_fK N x : Matrix.SpecialLinearGroup (Fin 2)
        CFSG.ASVolI.ChIJK.F4) : Matrix (Fin 2) (Fin 2) CFSG.ASVolI.ChIJK.F4).mulVec
          (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.E4.symm (Multiplicative.toAdd (N.ψQ p))))
    congr 1
    rw [h2]
    exact burnsideJ2b_E4_symm_mulVec _ _

private theorem burnsideJ2b_part4 {G : Type} [Group G] [Finite G] (N :
    CFSG.Quasithin.RuType.RuDataN G)
    (t : ↥(CFSG.Quasithin.RuType.ruU N.L N.T) ≃* ↥(CFSG.Quasithin.RuType.ruU N.L N.T)) :
    (∀ u : ↥(CFSG.Quasithin.RuType.ruU N.L N.T),
        (t u : G) * (u : G)⁻¹ ∈ CFSG.Quasithin.RuType.ruZ N.T) ↔
      ∃ q ∈ CFSG.Quasithin.RuType.ruQ N.T,
        ∀ u : ↥(CFSG.Quasithin.RuType.ruU N.L N.T), (t u : G) = q⁻¹ * u * q := by
  constructor
  · intro h
    have hcomm : ∀ a b : ↥(CFSG.Quasithin.RuType.ruU N.L N.T), (a : G) * b = b * a := fun a b =>
      Subtype.ext_iff.mp (N.U_elem.1.1.1 a b)
    have hfixZ : ∀ w : ↥(CFSG.Quasithin.RuType.ruU N.L N.T),
        (w : G) ∈ CFSG.Quasithin.RuType.ruZ N.T → (t w : G) = w := by
      intro w hw
      rcases N.mem_Z_iff.mp hw with h1 | h1
      · have : w = 1 := Subtype.ext h1
        rw [this, map_one]
      · have htw : (t w : G) ∈ CFSG.Quasithin.RuType.ruZ N.T := by
          have e : (t w : G) = ((t w : G) * (w : G)⁻¹) * w := by group
          rw [e]
          exact mul_mem (h w) hw
        rcases N.mem_Z_iff.mp htw with h2 | h2
        · exfalso
          have : t w = 1 := Subtype.ext h2
          have : w = 1 := t.injective (by rw [this, map_one])
          exact N.z_ne_one (h1 ▸ congrArg Subtype.val this)
        · rw [h2, h1]
    set d : ↥(CFSG.Quasithin.RuType.ruU N.L N.T) → G := fun u => (t u : G) * (u : G)⁻¹ with hd
    have hdU : ∀ u, d u ∈ CFSG.Quasithin.RuType.ruU N.L N.T := fun u =>
      mul_mem (t u).2 (inv_mem u.2)
    have hdmul : ∀ u u' : ↥(CFSG.Quasithin.RuType.ruU N.L N.T), d (u * u') = d u * d u' := by
      intro u u'
      have h1 : (u : G)⁻¹ * (t u' : G) = (t u' : G) * (u : G)⁻¹ := by
        have := hcomm (u⁻¹) (t u')
        simpa using this
      have h2 : (u : G)⁻¹ * (u' : G)⁻¹ = (u' : G)⁻¹ * (u : G)⁻¹ := by
        have := hcomm (u⁻¹) (u'⁻¹)
        simpa using this
      show (t (u * u') : G) * ((u * u' : ↥(CFSG.Quasithin.RuType.ruU N.L N.T)) : G)⁻¹ =
        ((t u : G) * (u : G)⁻¹) * ((t u' : G) * (u' : G)⁻¹)
      rw [map_mul]
      simp only [Subgroup.coe_mul, mul_inv_rev]
      calc (t u : G) * (t u' : G) * ((u' : G)⁻¹ * (u : G)⁻¹)
          = (t u : G) * (t u' : G) * ((u : G)⁻¹ * (u' : G)⁻¹) := by rw [← h2]
        _ = (t u : G) * ((t u' : G) * (u : G)⁻¹) * (u' : G)⁻¹ := by group
        _ = (t u : G) * ((u : G)⁻¹ * (t u' : G)) * (u' : G)⁻¹ := by rw [h1]
        _ = ((t u : G) * (u : G)⁻¹) * ((t u' : G) * (u' : G)⁻¹) := by group
    have hdZ : ∀ w : ↥(CFSG.Quasithin.RuType.ruU N.L N.T),
        (w : G) ∈ CFSG.Quasithin.RuType.ruZ N.T → d w = 1 := by
      intro w hw
      show (t w : G) * (w : G)⁻¹ = 1
      rw [hfixZ w hw, mul_inv_cancel]
    have hdψ : ∀ u₁ u₂ : ↥(CFSG.Quasithin.RuType.ruU N.L N.T), N.ψU u₁ = N.ψU u₂ →
        d u₁ = d u₂ := by
      intro u₁ u₂ he
      have hw : N.ψU (u₁⁻¹ * u₂) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
      have hwZ := (N.ψU_eq_one_iff _).mp hw
      have e : u₂ = u₁ * (u₁⁻¹ * u₂) := by group
      rw [e, hdmul, hdZ _ hwZ, mul_one]
    have hzinj : ∀ a b : G, a ∈ CFSG.Quasithin.RuType.ruZ N.T → b ∈ CFSG.Quasithin.RuType.ruZ N.T →
        CFSG.Quasithin.RuType.zval a = CFSG.Quasithin.RuType.zval b → a = b := by
      intro a b ha hb hab
      by_cases h0 : CFSG.Quasithin.RuType.zval a = 0
      · have h1 := (CFSG.Quasithin.RuType.zval_eq_zero_iff a).mp h0
        have h2 := (CFSG.Quasithin.RuType.zval_eq_zero_iff b).mp (hab ▸ h0)
        rw [h1, h2]
      · have h1 : a ≠ 1 := fun e => h0 ((CFSG.Quasithin.RuType.zval_eq_zero_iff a).mpr e)
        have h2 : b ≠ 1 := fun e =>
          h0 (hab ▸ (CFSG.Quasithin.RuType.zval_eq_zero_iff b).mpr e)
        rcases N.mem_Z_iff.mp ha with e1 | e1
        · exact absurd e1 h1
        · rcases N.mem_Z_iff.mp hb with e2 | e2
          · exact absurd e2 h2
          · rw [e1, e2]
    let F : (Fin 2 → CFSG.Quasithin.RuType.F4) → CFSG.Quasithin.RuType.F4 := fun x =>
      CFSG.Quasithin.RuType.zval (d (N.uOf x))
    have hFadd : ∀ x y, F (x + y) = F x + F y := by
      intro x y
      have e : N.ψU (N.uOf (x + y)) = N.ψU (N.uOf x * N.uOf y) := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, toAdd_mul, N.ψU_uOf, N.ψU_uOf, N.ψU_uOf]
      show CFSG.Quasithin.RuType.zval (d (N.uOf (x + y))) =
        CFSG.Quasithin.RuType.zval (d (N.uOf x)) + CFSG.Quasithin.RuType.zval (d (N.uOf y))
      rw [hdψ _ _ e, hdmul]
      exact N.zval_mul_aux (h _) (h _)
    obtain ⟨w, hw⟩ := CFSG.Quasithin.RuType.Sigma.exists_formB_eq F hFadd
      (fun x => CFSG.Quasithin.RuType.zval_val _)
    obtain ⟨q, hq, hqu⟩ := N.exists_comm_eq w
    refine ⟨q⁻¹, inv_mem hq, fun u => ?_⟩
    have hz1 := hqu u
    rw [hw] at hz1
    have hz2 : CFSG.Quasithin.RuType.zval ((q : G) * u * q⁻¹ * (u : G)⁻¹) =
        CFSG.Quasithin.RuType.zval (d u) := by
      rw [hz1]
      show CFSG.Quasithin.RuType.zval (d (N.uOf (Multiplicative.toAdd (N.ψU u)))) = _
      exact congrArg CFSG.Quasithin.RuType.zval (hdψ _ _ (Multiplicative.toAdd.injective (by
        rw [N.ψU_uOf])))
    have hz3 := hzinj _ _ (N.comm_mem_Z hq u.2) (h u) hz2
    have hz4 : (q : G) * u * q⁻¹ = (t u : G) := by
      have : (q : G) * u * q⁻¹ * (u : G)⁻¹ = (t u : G) * (u : G)⁻¹ := hz3
      exact mul_right_cancel this
    rw [inv_inv]
    exact hz4.symm
  · rintro ⟨q, hq, h⟩ u
    rw [h u]
    have := N.comm_mem_Z (inv_mem hq) u.2
    simpa using this

private theorem burnsideJ2b_part5 {G : Type} [Group G] [Finite G] (N :
    CFSG.Quasithin.RuType.RuDataN G)
    {l : G} (hl : l ∈ N.L)
    (hne : CFSG.conjugate (CFSG.Quasithin.RuType.ruU N.L N.T) l ≠
      CFSG.Quasithin.RuType.ruU N.L N.T) :
    Nat.card ↥(((CFSG.conjugate (CFSG.Quasithin.RuType.ruU N.L N.T) l).subgroupOf
        (CFSG.Quasithin.RuType.ruH N.T)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.RuType.ruH N.T)))) = 2 ∧
      CFSG.Quasithin.RuType.ruV N.L =
        CFSG.conjugate (CFSG.Quasithin.RuType.ruU N.L N.T) l ⊓ N.HC := by
  have hconj : CFSG.conjugate (CFSG.Quasithin.RuType.ruU N.L N.T) l = N.conjU l⁻¹ := rfl
  rw [hconj] at hne ⊢
  have hl' : l⁻¹ ∈ N.L := N.L.inv_mem hl
  refine ⟨?_, (N.conjU_inf_HC hl' hne).symm⟩
  have hXH : N.conjU l⁻¹ ≤ CFSG.Quasithin.RuType.ruH N.T :=
    (N.conjU_le_S hl').trans (N.toRuData.S_le_T.trans N.toRuData.T_le_H)
  have hX32 : Nat.card ↥(N.conjU l⁻¹) = 32 := by
    rw [N.card_conjU, N.toRuData.card_U]
  have hXQ16 := N.card_conjU_inf_Q hl' hne
  have h1 := Subgroup.relIndex_ker (K := (N.conjU l⁻¹).subgroupOf (CFSG.Quasithin.RuType.ruH N.T))
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.RuType.ruH N.T)))
  have h2 := Subgroup.relIndex_mul_card
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.RuType.ruH N.T))).ker
    ((N.conjU l⁻¹).subgroupOf (CFSG.Quasithin.RuType.ruH N.T))
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.RuType.ruH N.T))).ker =
      (CFSG.Quasithin.RuType.ruQ N.T).subgroupOf (CFSG.Quasithin.RuType.ruH N.T) := by
    rw [QuotientGroup.ker_mk']
    exact (CFSG.ASVolI.ChIJK.RuType.BridgeTwo.subgroupOf_pCoreOf _).symm
  rw [hker] at h1 h2
  have hinf : (CFSG.Quasithin.RuType.ruQ N.T).subgroupOf (CFSG.Quasithin.RuType.ruH N.T) ⊓
      (N.conjU l⁻¹).subgroupOf (CFSG.Quasithin.RuType.ruH N.T) =
      (CFSG.Quasithin.RuType.ruQ N.T ⊓ N.conjU l⁻¹).subgroupOf
        (CFSG.Quasithin.RuType.ruH N.T) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [hinf,
    CFSG.Quasithin.RuType.card_subgroupOf_of_le
      (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)),
    CFSG.Quasithin.RuType.card_subgroupOf_of_le hXH, hX32, inf_comm, hXQ16] at h2
  rw [← h1]
  omega

private theorem burnsideJ2b_part2 {G : Type} [Group G] [Finite G] (N :
    CFSG.Quasithin.RuType.RuDataN G)
    {U : Subgroup G} (hU : U = CFSG.Quasithin.RuType.ruU N.L N.T) :
    IsElemAbelian 2 U ∧ Nat.card ↥U = 32 := by
  subst hU
  exact ⟨N.U_elem, N.toRuData.card_U⟩

private theorem burnsideJ2b_exists_M {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : CFSG.ASVolI.ChIJK.RuType G L V T) :
    ∃ M : CFSG.Quasithin.RuType.RuDataM G, M.L = L ∧ (M.T : Subgroup G) = T ∧
      V = CFSG.Quasithin.RuType.ruV M.L ∧
      CFSG.ASVolI.ChIJK.ZRu T = CFSG.Quasithin.RuType.ruZ M.T ∧
      CFSG.ASVolI.ChIJK.HRu T = CFSG.Quasithin.RuType.ruH M.T ∧
      CFSG.ASVolI.ChIJK.QRu T = CFSG.Quasithin.RuType.ruQ M.T ∧
      CFSG.ASVolI.ChIJK.URu V T = CFSG.Quasithin.RuType.ruU M.L M.T := by
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM CFSG.Quasithin.RuType.stUnique
  have hT : (M.T : Subgroup G) = T := by rw [hMT]; exact h.coe_sylowT
  have hV : V = CFSG.Quasithin.RuType.ruV M.L := by
    rw [hML]; exact CFSG.ASVolI.ChIJK.RuType.V_eq_ruV h
  refine ⟨M, hML, hT, hV, ?_, ?_, ?_, ?_⟩
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.ZRu_eq_ruZ h
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.HRu_eq_ruH h
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.QRu_eq_ruQ h
  · rw [hMT, hML]; exact CFSG.ASVolI.ChIJK.RuType.URu_eq_ruU h

end BurnsideJ2b

theorem as_J_2_2 : J_2_2 := by
  intro G _ _ L V T h
  obtain ⟨M, hML, hMT, hV, hZ, hH, hQ, hU⟩ := burnsideJ2b_exists_M h
  subst hML
  subst hMT
  subst hV
  have hK : CFSG.ASVolI.ChIJK.KRu (M.T : Subgroup G) = M.K := by
    unfold CFSG.ASVolI.ChIJK.KRu
    rw [hH, burnsideJ2b_twoResidual_eq]
    exact burnsideJ2b_K_eq M.toRuDataN
  have hHC : CFSG.ASVolI.ChIJK.HCRu (CFSG.Quasithin.RuType.ruV M.L) (M.T : Subgroup G) =
      M.HC := by
    unfold CFSG.ASVolI.ChIJK.HCRu
    rw [hH, hU]
  have hL1 : CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) =
      CFSG.Quasithin.twoResidual M.LT1 := by
    unfold CFSG.ASVolI.ChIJK.L1Ru
    rw [hZ, burnsideJ2b_twoResidual_eq]
    congr 1
    rw [inf_comm]
    exact M.toRuDataN.L_inf_H
  have hR1 : CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G) =
      pCoreOf 2 (CFSG.Quasithin.twoResidual M.LT1) := by
    unfold CFSG.ASVolI.ChIJK.R1Ru
    rw [hL1]
  have key3 : ∀ (K Q HC : Subgroup G), K = M.K → Q = CFSG.Quasithin.RuType.ruQ M.T →
      HC = M.HC →
      ∃ (_ : (Q.subgroupOf K).Normal)
        (e : ↥K ⧸ Q.subgroupOf K ≃*
          Matrix.SpecialLinearGroup (Fin 2) CFSG.ASVolI.ChIJK.F4),
        CFSG.ASVolI.ChIJK.IsConjModuleIso K Q HC (Fin 2 → CFSG.ASVolI.ChIJK.F4)
          (fun k v => ((e (k : ↥K ⧸ Q.subgroupOf K) :
            Matrix.SpecialLinearGroup (Fin 2) CFSG.ASVolI.ChIJK.F4) :
              Matrix (Fin 2) (Fin 2) CFSG.ASVolI.ChIJK.F4).mulVec v) := by
    intro K Q HC hK hQ hHC
    subst hK hQ hHC
    exact burnsideJ2b_part3b M.toRuDataN
  have key4 : ∀ (U Z Q : Subgroup G), U = CFSG.Quasithin.RuType.ruU M.L M.T →
      Z = CFSG.Quasithin.RuType.ruZ M.T → Q = CFSG.Quasithin.RuType.ruQ M.T →
      ∀ t : ↥U ≃* ↥U, (∀ u : ↥U, (t u : G) * (u : G)⁻¹ ∈ Z) ↔
        ∃ q ∈ Q, ∀ u : ↥U, (t u : G) = q⁻¹ * u * q := by
    intro U Z Q hU hZ hQ
    subst hU hZ hQ
    exact burnsideJ2b_part4 M.toRuDataN
  have key5 : ∀ (U H HC V' : Subgroup G), U = CFSG.Quasithin.RuType.ruU M.L M.T →
      H = CFSG.Quasithin.RuType.ruH M.T → HC = M.HC → V' = CFSG.Quasithin.RuType.ruV M.L →
      ∀ l ∈ M.L, CFSG.conjugate U l ≠ U →
        Nat.card ↥(((CFSG.conjugate U l).subgroupOf H).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) = 2 ∧ V' = CFSG.conjugate U l ⊓ HC := by
    intro U H HC V' hU hH hHC hV
    subst hU hH hHC hV
    intro l hl hne
    exact burnsideJ2b_part5 M.toRuDataN hl hne
  have p1 := burnsideJ2b_part1 M.toRuDataN
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hH, hL1]
    exact p1.1
  · rw [hQ, hL1]
    exact p1.2.1
  · rw [hL1, hR1]
    exact p1.2.2.1
  · rw [hQ, hK]
    exact (burnsideJ2b_K_eq M.toRuDataN) ▸ p1.2.2.2
  · exact burnsideJ2b_part2 M.toRuDataN hU
  · intro x
    rw [hHC, hQ, hK, hU]
    exact burnsideJ2b_part3a M.toRuDataN x
  · exact key3 _ _ _ hK hQ hHC
  · exact key4 _ _ _ hU hZ hQ
  · exact key5 _ _ _ _ hU hH hHC rfl


section BurnsideJ3b

section Transport

variable {G : Type} [Group G]

private theorem burnsideJ3b_mem_map_conj {g x : G} {X : Subgroup G} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem burnsideJ3b_map_centralizer (φ : G ≃* G) (S : Set G) :
    (Subgroup.centralizer S).map φ.toMonoidHom = Subgroup.centralizer (φ '' S) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have := congrArg φ (h y' hy')
    simpa using this
  · intro h y hy
    have := congrArg φ.symm (h (φ y) ⟨y, hy, rfl⟩)
    simpa using this

private theorem burnsideJ3b_map_centralizer_subgroup (φ : G ≃* G) (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((X.map φ.toMonoidHom : Subgroup G) : Set G) := by
  rw [burnsideJ3b_map_centralizer, Subgroup.coe_map]
  rfl

private theorem burnsideJ3b_map_centralizer_singleton (φ : G ≃* G) (s : G) :
    (Subgroup.centralizer ({s} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ s} : Set G) := by
  rw [burnsideJ3b_map_centralizer, Set.image_singleton]

private theorem burnsideJ3b_map_conj_eq_self {g : G} {X : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  ext x
  rw [burnsideJ3b_mem_map_conj]
  have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hg)) x
  simpa using h.symm

private theorem burnsideJ3b_isElemAbelian_map (φ : G ≃* G) {X : Subgroup G} (h : IsElemAbelian
    2 X) :
    IsElemAbelian 2 (X.map φ.toMonoidHom) := by
  obtain ⟨hc, hsq⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have hab : a' * b' = b' * a' := congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← ha, ← hb]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hab]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow, hsq x hx, map_one]

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_isSylowTwoIn_map (φ : G ≃* G) {Q M : Subgroup G} (h : IsSylowTwoIn
    Q M) :
    IsSylowTwoIn (Q.map φ.toMonoidHom) (M.map φ.toMonoidHom) := by
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨Subgroup.map_mono hle, ?_, ?_⟩
  · exact hp.of_equiv (Subgroup.equivMapOfInjective Q φ.toMonoidHom φ.injective)
  · have h2 : ((Q.map φ.toMonoidHom).subgroupOf (M.map φ.toMonoidHom)).index =
        (Q.subgroupOf M).index :=
      Subgroup.relIndex_map_map_of_injective Q M φ.injective
    rwa [h2]

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_isSylowTwoIn_of_sylow [Finite G] {C D : Subgroup G} (hle : D ≤ C)
    (h : ∃ P : Sylow 2 ↥C, (P : Subgroup ↥C) = D.subgroupOf C) : IsSylowTwoIn D C := by
  obtain ⟨P, hP⟩ := h
  refine ⟨hle, ?_, ?_⟩
  · have h1 : IsPGroup 2 ↥(D.subgroupOf C) := by
      rw [← hP]
      exact P.isPGroup'
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hle)
  · rw [← hP]
    exact P.not_dvd_index

private theorem burnsideJ3b_map_le_normalizer (φ : G ≃* G) {B X : Subgroup G}
    (h : B ≤ Subgroup.normalizer (X : Set G)) :
    B.map φ.toMonoidHom ≤ Subgroup.normalizer ((X.map φ.toMonoidHom : Subgroup G) : Set G) :=
  (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map _)

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_isDirectProductOf_map (φ : G ≃* G) {A B X : Subgroup G}
    (h : IsDirectProductOf A B X) :
    IsDirectProductOf (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) (X.map φ.toMonoidHom) := by
  obtain ⟨hc, hi, hs⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hc a' ha' b' hb']
  · rw [← Subgroup.map_inf A B φ.toMonoidHom φ.injective, hi, Subgroup.map_bot]
  · rw [← Subgroup.map_sup, hs]

private theorem burnsideJ3b_exponent_map (φ : G ≃* G) (X : Subgroup G) :
    Monoid.exponent ↥(X.map φ.toMonoidHom) = Monoid.exponent ↥X :=
  (Monoid.exponent_eq_of_mulEquiv (Subgroup.equivMapOfInjective X φ.toMonoidHom φ.injective)).symm

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_isSuzukiTwoGroup_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e :
    X ≃* Y)
    (h : IsSuzukiTwoGroup X) : IsSuzukiTwoGroup Y := by
  obtain ⟨hp, C, hC, htr⟩ := h
  have hmap : IsCyclic ↥(C.map (MulAut.congr e).toMonoidHom) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective C (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective)).mp hC
  refine ⟨hp.of_equiv e, C.map (MulAut.congr e).toMonoidHom, hmap, ?_⟩
  intro i j hi hi1 hj hj1
  have hi' : (e.symm i) ^ 2 = 1 := by rw [← map_pow, hi, map_one]
  have hj' : (e.symm j) ^ 2 = 1 := by rw [← map_pow, hj, map_one]
  have hi1' : e.symm i ≠ 1 := fun h => hi1 (by simpa using congrArg e h)
  have hj1' : e.symm j ≠ 1 := fun h => hj1 (by simpa using congrArg e h)
  obtain ⟨c, hc, hci⟩ := htr (e.symm i) (e.symm j) hi' hi1' hj' hj1'
  refine ⟨MulAut.congr e c, Subgroup.mem_map_of_mem _ hc, ?_⟩
  show e (c (e.symm i)) = j
  rw [hci, MulEquiv.apply_symm_apply]

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_isSuzukiTwoGroup_of_basic {X : Type} [Group X]
    (h : CFSG.GroupTheory.IsSuzukiTwoGroup X) : IsSuzukiTwoGroup X := by
  obtain ⟨-, hp, -, -, A, hA, htr⟩ := h
  refine ⟨hp, A, hA, fun i j hi hi1 hj hj1 => htr i j ?_ ?_⟩
  · exact orderOf_eq_prime hi hi1
  · exact orderOf_eq_prime hj hj1

end Transport

section TwoResidual

variable {G : Type} [Group G]

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_mem_twoResidual_iff {X : Subgroup G} {x : G} :
    x ∈ twoResidual X ↔ ∃ hx : x ∈ X, ∀ N : Subgroup X, N.Normal →
      (∃ n : ℕ, N.index = 2 ^ n) → (⟨x, hx⟩ : X) ∈ N := by
  unfold CFSG.ASVolI.ChIJK.twoResidual
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun N hN hn => Subgroup.mem_sInf.mp hy N ⟨hN, hn⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_sInf.mpr fun N hN => h N hN.1 hN.2, rfl⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_twoResidual_le (X : Subgroup G) : twoResidual X ≤ X :=
  Subgroup.map_subtype_le _

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_conj_mem_twoResidual {X : Subgroup G} {g x : G} (hg : g ∈ X)
    (hx : x ∈ twoResidual X) : g * x * g⁻¹ ∈ twoResidual X := by
  obtain ⟨hxX, h⟩ := burnsideJ3b_mem_twoResidual_iff.mp hx
  refine burnsideJ3b_mem_twoResidual_iff.mpr
    ⟨X.mul_mem (X.mul_mem hg hxX) (X.inv_mem hg), fun N hN hn => ?_⟩
  exact hN.conj_mem ⟨x, hxX⟩ (h N hN hn) ⟨g, hg⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_le_normalizer_twoResidual (X : Subgroup G) :
    X ≤ Subgroup.normalizer (twoResidual X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => burnsideJ3b_conj_mem_twoResidual hg hx, fun hx => ?_⟩
  have := burnsideJ3b_conj_mem_twoResidual (X.inv_mem hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ3b_mem_twoResidual_of_pow_three {X : Subgroup G} {x : G} (hx : x ∈ X)
    (h3 : x ^ 3 = 1) : x ∈ twoResidual X := by
  refine burnsideJ3b_mem_twoResidual_iff.mpr ⟨hx, fun N hN hn => ?_⟩
  obtain ⟨n, hn⟩ := hn
  have hq3 : (QuotientGroup.mk (s := N) (⟨x, hx⟩ : X)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : X) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this]
    rfl
  have hd1 : orderOf (QuotientGroup.mk (s := N) (⟨x, hx⟩ : X)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one hq3
  have hd2 : orderOf (QuotientGroup.mk (s := N) (⟨x, hx⟩ : X)) ∣ 2 ^ n := by
    rw [← hn]
    exact orderOf_dvd_natCard _
  have hd := Nat.dvd_gcd hd1 hd2
  have hg : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right _ (by norm_num)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact (QuotientGroup.eq_one_iff _).mp hd

end TwoResidual

section Sylow

variable {G : Type} [Group G]

private theorem burnsideJ3b_exists_conj_of_card_prime [Finite G] {p : ℕ} [Fact p.Prime]
    {K A B : Subgroup G} (hK : ¬ p ^ 2 ∣ Nat.card K) (hA : A ≤ K) (hB : B ≤ K)
    (hAc : Nat.card A = p) (hBc : Nat.card B = p) :
    ∃ k ∈ K, ∀ x : G, x ∈ A ↔ k⁻¹ * x * k ∈ B := by
  have hsyl : ∀ C : Subgroup G, C ≤ K → Nat.card C = p →
      ∃ P : Sylow p K, (P : Subgroup K) = C.subgroupOf K := by
    intro C hC hCc
    have hcard : Nat.card (C.subgroupOf K) = p := by
      rw [← hCc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
    have hp : IsPGroup p (C.subgroupOf K) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
    refine ⟨IsPGroup.toSylow hp ?_, rfl⟩
    have h := Subgroup.index_mul_card (C.subgroupOf K)
    rw [hcard] at h
    rintro ⟨c, hc⟩
    apply hK
    rw [← h, hc]
    exact ⟨c, by ring⟩
  obtain ⟨PA, hPA⟩ := hsyl A hA hAc
  obtain ⟨PB, hPB⟩ := hsyl B hB hBc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K PB PA
  have key : ∀ x' : K, (x' : G) ∈ A ↔ (g : G)⁻¹ * (x' : G) * (g : G) ∈ B := by
    intro x'
    have h1 : (x' : G) ∈ A ↔ x' ∈ (PA : Subgroup K) := by
      rw [hPA]
      exact Iff.rfl
    have h2 : x' ∈ (PA : Subgroup K) ↔ g⁻¹ * x' * g ∈ (PB : Subgroup K) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
    have h3 : g⁻¹ * x' * g ∈ (PB : Subgroup K) ↔ (g : G)⁻¹ * (x' : G) * (g : G) ∈ B := by
      rw [hPB]
      exact Iff.rfl
    exact h1.trans (h2.trans h3)
  refine ⟨(g : G), g.2, fun x => ?_⟩
  by_cases hxK : x ∈ K
  · exact key ⟨x, hxK⟩
  · refine ⟨fun hx => absurd (hA hx) hxK, fun hx => absurd ?_ hxK⟩
    have h1 : (g : G)⁻¹ * x * g ∈ K := hB hx
    have h2 : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem g.2 h1) (K.inv_mem g.2)
    have e : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x := by group
    rwa [e] at h2

private theorem burnsideJ3b_card_of_isSylowIn_three [Finite G] {K B : Subgroup G}
    (hK9 : ¬ 9 ∣ Nat.card K) (hK3 : 3 ∣ Nat.card K)
    (hB : CFSG.ASVolI.ChIJK.IsSylowIn 3 B K) : Nat.card B = 3 := by
  obtain ⟨hle, hp, hidx⟩ := hB
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcard : Nat.card (B.subgroupOf K) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h := Subgroup.card_mul_index (B.subgroupOf K)
  rw [hcard, hk] at h
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · exfalso
      rw [pow_zero, one_mul] at h
      exact hidx (by rw [h]; exact hK3)
    · rfl
    · exfalso
      apply hK9
      rw [← h]
      exact ⟨3 ^ k * (B.subgroupOf K).index, by ring⟩
  rw [hk, hk1, pow_one]

end Sylow

section Ident

variable {G : Type} [Group G]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_ZRu_eq (M : RuDataM G) :
    CFSG.ASVolI.ChIJK.ZRu (M.T : Subgroup G) = ruZ M.T :=
  CFSG.ASVolI.ChIJK.RuType.BridgeTwo.centerOf_eq _

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_HRu_eq (M : RuDataM G) :
    CFSG.ASVolI.ChIJK.HRu (M.T : Subgroup G) = ruH M.T := by
  unfold CFSG.ASVolI.ChIJK.HRu
  rw [burnsideJ3b_ZRu_eq]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_URu_eq (M : RuDataM G) :
    CFSG.ASVolI.ChIJK.URu (ruV M.L) (M.T : Subgroup G) = ruU M.L M.T := by
  unfold CFSG.ASVolI.ChIJK.URu
  rw [CFSG.ASVolI.ChIJK.RuType.BridgeTwo.conjClosure_eq, burnsideJ3b_HRu_eq]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_centralizer_inf_L [Finite G] (M : RuDataM G) :
    Subgroup.centralizer (CFSG.ASVolI.ChIJK.ZRu (M.T : Subgroup G) : Set G) ⊓ M.L = M.LT1 := by
  rw [burnsideJ3b_ZRu_eq, inf_comm]
  exact M.toRuDataN.L_inf_H

end Ident

section Pair

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_B_le_L1 (M : RuDataM G) :
    M.B ≤ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) := by
  show Subgroup.zpowers (M.bel : G) ≤ _
  rw [Subgroup.zpowers_le]
  unfold CFSG.ASVolI.ChIJK.L1Ru
  refine burnsideJ3b_mem_twoResidual_of_pow_three ?_ M.bel_pow_three
  rw [burnsideJ3b_centralizer_inf_L]
  exact mem_pullL.mpr ⟨M.bel.2, by rw [M.θ_bel]; exact SL3.b0_mem_Stab0⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_L1_le_L (M : RuDataM G) :
    CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) ≤ M.L :=
  (burnsideJ3b_twoResidual_le _).trans inf_le_right

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_not_dvd_of_le (M : RuDataM G) {K : Subgroup G} (hK : K ≤ M.L) {n : ℕ}
    (hn : ¬ n ∣ 2 ^ 11 * 168) : ¬ n ∣ Nat.card K := fun h =>
  hn (h.trans ((Subgroup.card_dvd_of_le hK).trans (by rw [M.toRuData.card_L])))

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_card_B_eq (M : RuDataM G) {B : Subgroup G}
    (hB : CFSG.ASVolI.ChIJK.IsSylowIn 3 B
      (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G))) : Nat.card B = 3 := by
  refine burnsideJ3b_card_of_isSylowIn_three ?_ ?_ hB
  · exact burnsideJ3b_not_dvd_of_le M (burnsideJ3b_L1_le_L M) (by norm_num)
  · have := Subgroup.card_dvd_of_le (burnsideJ3b_B_le_L1 M)
    rw [M.card_B] at this
    exact this

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_B7_le_L (M : RuDataM G) : M.B7 ≤ M.L :=
  Subgroup.zpowers_le.mpr M.cel.2

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_B_le_L (M : RuDataM G) : M.B ≤ M.L :=
  Subgroup.zpowers_le.mpr M.bel.2

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_B_le_normalizer_B7 (M : RuDataM G) :
    M.B ≤ Subgroup.normalizer (M.B7 : Set G) := by
  show Subgroup.zpowers (M.bel : G) ≤ _
  rw [Subgroup.zpowers_le]
  refine CFSG.Quasithin.RuType.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact M.bel_conj_cel k

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_exists_pair_conj (M : RuDataM G) {B B7 : Subgroup G}
    (hB : CFSG.ASVolI.ChIJK.IsSylowIn 3 B
      (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G)))
    (hB7L : B7 ≤ M.L) (hB7c : Nat.card B7 = 7)
    (hBn : B ≤ Subgroup.normalizer (B7 : Set G)) :
    ∃ g ∈ M.L, (∀ x, x ∈ B ↔ g⁻¹ * x * g ∈ M.B) ∧ (∀ x, x ∈ B7 ↔ g⁻¹ * x * g ∈ M.B7) := by
  have hBc : Nat.card B = 3 := burnsideJ3b_card_B_eq M hB
  have hBL : B ≤ M.L := hB.1.trans (burnsideJ3b_L1_le_L M)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨l, hlL, hl⟩ := burnsideJ3b_exists_conj_of_card_prime (p := 7) (K := M.L) (A := B7)
    (B := M.B7) (burnsideJ3b_not_dvd_of_le M le_rfl (by norm_num)) hB7L
    (burnsideJ3b_B7_le_L M) hB7c M.card_B7
  have hB''mem : ∀ x : G, x ∈ B.map (MulAut.conj l⁻¹).toMonoidHom ↔ l * x * l⁻¹ ∈ B := fun x => by
    rw [burnsideJ3b_mem_map_conj, inv_inv]
  have hB''c : Nat.card (B.map (MulAut.conj l⁻¹).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj l⁻¹).injective]
    exact hBc
  have hB''N : B.map (MulAut.conj l⁻¹).toMonoidHom ≤
      Subgroup.normalizer (M.B7 : Set G) ⊓ M.L := by
    intro x hx
    have hx' := (hB''mem x).mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have hb := Subgroup.mem_normalizer_iff.mp (hBn hx') (l * y * l⁻¹)
      have e1 : l⁻¹ * (l * y * l⁻¹) * l = y := by group
      have e2 : l⁻¹ * ((l * x * l⁻¹) * (l * y * l⁻¹) * (l * x * l⁻¹)⁻¹) * l = x * y * x⁻¹ := by
        group
      have h1 := hl (l * y * l⁻¹)
      have h2 := hl ((l * x * l⁻¹) * (l * y * l⁻¹) * (l * x * l⁻¹)⁻¹)
      rw [e1] at h1
      rw [e2] at h2
      exact h1.symm.trans (hb.trans h2)
    · have hxl : l⁻¹ * (l * x * l⁻¹) * l ∈ M.L :=
        M.L.mul_mem (M.L.mul_mem (M.L.inv_mem hlL) (hBL hx')) hlL
      have e : l⁻¹ * (l * x * l⁻¹) * l = x := by group
      rwa [e] at hxl
  have hMBN : M.B ≤ Subgroup.normalizer (M.B7 : Set G) ⊓ M.L :=
    le_inf (burnsideJ3b_B_le_normalizer_B7 M) (burnsideJ3b_B_le_L M)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨n, hnN, hn⟩ := burnsideJ3b_exists_conj_of_card_prime (p := 3)
    (K := Subgroup.normalizer (M.B7 : Set G) ⊓ M.L) (A := B.map (MulAut.conj l⁻¹).toMonoidHom)
    (B := M.B)
    (burnsideJ3b_not_dvd_of_le M inf_le_right (by norm_num)) hB''N hMBN hB''c M.card_B
  obtain ⟨hnNorm, hnL⟩ := hnN
  refine ⟨l * n, M.L.mul_mem hlL hnL, fun x => ?_, fun x => ?_⟩
  · have e : (l * n)⁻¹ * x * (l * n) = n⁻¹ * (l⁻¹ * x * l) * n := by group
    rw [e, ← hn, hB''mem]
    have e2 : l * (l⁻¹ * x * l) * l⁻¹ = x := by group
    rw [e2]
  · have e : (l * n)⁻¹ * x * (l * n) = n⁻¹ * (l⁻¹ * x * l) * n := by group
    rw [e, hl x]
    have := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (M.B7 : Set G)).inv_mem hnNorm)
      (l⁻¹ * x * l)
    rw [inv_inv] at this
    exact this

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_exists_conj_B (M : RuDataM G) {B : Subgroup G}
    (hB : CFSG.ASVolI.ChIJK.IsSylowIn 3 B
      (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G))) :
    ∃ m ∈ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G), ∀ x, x ∈ B ↔ m⁻¹ * x * m ∈ M.B := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact burnsideJ3b_exists_conj_of_card_prime (p := 3) (K := CFSG.ASVolI.ChIJK.L1Ru M.L
    (M.T : Subgroup G)) (A := B) (B := M.B)
    (burnsideJ3b_not_dvd_of_le M (burnsideJ3b_L1_le_L M) (by norm_num)) hB.1
    (burnsideJ3b_B_le_L1 M) (burnsideJ3b_card_B_eq M hB) M.card_B

end Pair

section Parts

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_pow_four_of_two_pow {x : Matrix.SpecialLinearGroup (Fin 3) (ZMod
    2)} {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ^ 4 = 1 := by
  apply SL3.pow_four_of_pow_eight
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hdvd' : orderOf x ∣ 168 := by
    rw [← SL3.card_SL3]
    exact orderOf_dvd_natCard x
  have : orderOf x ∣ 8 := by
    have h1 : orderOf x ∣ Nat.gcd (2 ^ k) 168 := Nat.dvd_gcd hdvd hdvd'
    have h2 : Nat.gcd (2 ^ k) 168 ∣ 8 := by
      have : Nat.gcd (2 ^ k) 168 ∣ 2 ^ k := Nat.gcd_dvd_left _ _
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
      rw [hj']
      have : 2 ^ j ∣ 168 := hj' ▸ Nat.gcd_dvd_right _ _
      have hj3 : j ≤ 3 :=
        RuDataN.le_of_two_pow_dvd (a := 3) (b := j) (c := 21)
          (by rw [show 2 ^ 3 * 21 = 168 by norm_num]; exact this) (by norm_num)
      exact Nat.pow_dvd_pow 2 hj3
    exact h1.trans h2
  exact orderOf_dvd_iff_pow_eq_one.mp this

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_L1_le_LT1 (M : RuDataM G) :
    CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) ≤ M.LT1 :=
  (burnsideJ3b_twoResidual_le _).trans (burnsideJ3b_centralizer_inf_L M).le

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_LT1_le_normalizer_R1Ru (M : RuDataM G) :
    M.LT1 ≤ Subgroup.normalizer (CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G) : Set G) := by
  have h1 := burnsideJ3b_le_normalizer_twoResidual
    (Subgroup.centralizer (CFSG.ASVolI.ChIJK.ZRu (M.T : Subgroup G) : Set G) ⊓ M.L)
  exact (burnsideJ3b_centralizer_inf_L M).symm.le.trans
    (h1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_R1Ru_le (M : RuDataM G) :
    CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G) ≤ M.R1 := by
  intro r hr
  have hrK : r ∈ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr
  obtain ⟨hrL, hrSt⟩ := mem_pullL.mp (burnsideJ3b_L1_le_LT1 M hrK)
  refine mem_pullL.mpr ⟨hrL, ?_⟩
  by_contra hxR
  have hp : IsPGroup 2 ↥(CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨k, hk⟩ := hp ⟨r, hr⟩
  have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hx4 : (M.θ ⟨r, hrL⟩) ^ 4 = 1 := by
    apply burnsideJ3b_pow_four_of_two_pow (k := k)
    have : (⟨r, hrL⟩ : M.L) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hrk)
    rw [← map_pow, this, map_one]
  obtain ⟨g, hg, hne, h3⟩ := SL3.exists_comm_order_three _ hrSt hxR hx4
  obtain ⟨⟨l, hlL⟩, hlg⟩ := M.θ_surj g
  have hlLT : l ∈ M.LT1 := mem_pullL.mpr ⟨hlL, by rw [hlg]; exact hg⟩
  have hl1 : l * r⁻¹ * l⁻¹ ∈ CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp (burnsideJ3b_LT1_le_normalizer_R1Ru M hlLT) r⁻¹).mp
      (Subgroup.inv_mem _ hr)
  have hc : r * l * r⁻¹ * l⁻¹ ∈ CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G) := by
    have := Subgroup.mul_mem _ hr hl1
    simpa [mul_assoc] using this
  have hcL : r * l * r⁻¹ * l⁻¹ ∈ M.L :=
    M.L.mul_mem (M.L.mul_mem (M.L.mul_mem hrL hlL) (M.L.inv_mem hrL)) (M.L.inv_mem hlL)
  obtain ⟨m, hm⟩ := hp ⟨_, hc⟩
  have hm' : (r * l * r⁻¹ * l⁻¹) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hθc : M.θ ⟨r * l * r⁻¹ * l⁻¹, hcL⟩ =
      (M.θ ⟨r, hrL⟩) * g * (M.θ ⟨r, hrL⟩)⁻¹ * g⁻¹ := by
    rw [← hlg]
    show M.θ (⟨r, hrL⟩ * ⟨l, hlL⟩ * ⟨r, hrL⟩⁻¹ * ⟨l, hlL⟩⁻¹) = _
    simp only [map_mul, map_inv]
  apply hne
  have h2 : (M.θ ⟨r * l * r⁻¹ * l⁻¹, hcL⟩) ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨r * l * r⁻¹ * l⁻¹, hcL⟩ : M.L) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm')
    rw [this, map_one]
  rw [hθc] at h2
  have hd1 : orderOf ((M.θ ⟨r, hrL⟩) * g * (M.θ ⟨r, hrL⟩)⁻¹ * g⁻¹) ∣ Nat.gcd (2 ^ m) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hd2 : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  rw [hd2, Nat.dvd_one, orderOf_eq_one_iff] at hd1
  exact hd1

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_R0_prod_order_three : ∀ g ∈ SL3.R0, ∃ a ∈ SL3.Stab0, ∃ b ∈ SL3.Stab0,
    a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = g := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_exists_mem_R1Ru (M : RuDataM G)
    {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (hg : g ∈ SL3.R0) :
    ∃ r, ∃ _ : r ∈ CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G), ∃ hrL : r ∈ M.L,
      M.θ ⟨r, hrL⟩ = g := by
  obtain ⟨a, ha, b, hb, ha3, hb3, hab⟩ := burnsideJ3b_R0_prod_order_three g hg
  obtain ⟨la, hla, hla3⟩ := M.exists_lift ha3 (by norm_num)
  obtain ⟨lb, hlb, hlb3⟩ := M.exists_lift hb3 (by norm_num)
  have hX := burnsideJ3b_centralizer_inf_L M
  have hlaX : (la : G) ∈ M.LT1 :=
    mem_pullL.mpr ⟨la.2, by rw [show (⟨(la : G), la.2⟩ : M.L) = la from rfl, hla]; exact ha⟩
  have hlbX : (lb : G) ∈ M.LT1 :=
    mem_pullL.mpr ⟨lb.2, by rw [show (⟨(lb : G), lb.2⟩ : M.L) = lb from rfl, hlb]; exact hb⟩
  have hlaK : (la : G) ∈ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) := by
    unfold CFSG.ASVolI.ChIJK.L1Ru
    refine burnsideJ3b_mem_twoResidual_of_pow_three ?_ hla3
    rw [hX]
    exact hlaX
  have hlbK : (lb : G) ∈ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) := by
    unfold CFSG.ASVolI.ChIJK.L1Ru
    refine burnsideJ3b_mem_twoResidual_of_pow_three ?_ hlb3
    rw [hX]
    exact hlbX
  have hrK : (la : G) * lb ∈ CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) :=
    Subgroup.mul_mem _ hlaK hlbK
  have hrL : (la : G) * lb ∈ M.L := M.L.mul_mem la.2 lb.2
  have hθ : M.θ ⟨(la : G) * lb, hrL⟩ = g := by
    show M.θ (la * lb) = g
    rw [map_mul, hla, hlb, hab]
  refine ⟨(la : G) * lb, ?_, hrL, hθ⟩
  have hmemR1 : (la : G) * lb ∈ M.R1 := mem_pullL.mpr ⟨hrL, by rw [hθ]; exact hg⟩
  have hN : CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G) ⊓ M.R1 ≤
      CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_ ?_
    · refine ⟨fun x hx k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxK, hxR⟩ := Subgroup.mem_inf.mp hx
      show (k : G) * (x : G) * (k : G)⁻¹ ∈ _
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ k.2 hxK)
        (Subgroup.inv_mem _ k.2), ?_⟩
      obtain ⟨hxL, hxθ⟩ := mem_pullL.mp hxR
      obtain ⟨hkL, hkθ⟩ := mem_pullL.mp (burnsideJ3b_L1_le_LT1 M k.2)
      have hkxL : (k : G) * x * (k : G)⁻¹ ∈ M.L :=
        M.L.mul_mem (M.L.mul_mem hkL hxL) (M.L.inv_mem hkL)
      refine mem_pullL.mpr ⟨hkxL, ?_⟩
      have : M.θ ⟨(k : G) * x * (k : G)⁻¹, hkxL⟩ =
          M.θ ⟨k, hkL⟩ * M.θ ⟨x, hxL⟩ * (M.θ ⟨k, hkL⟩)⁻¹ := by
        show M.θ (⟨k, hkL⟩ * ⟨x, hxL⟩ * ⟨k, hkL⟩⁻¹) = _
        simp only [map_mul, map_inv]
      rw [this]
      exact SL3.conj_mem_R0 _ hkθ _ hxθ
    · exact (IsPGroup.of_card (n := 13) M.card_R1).to_le inf_le_right
  exact hN ⟨hrK, hmemR1⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part8 (M : RuDataM G) :
    ∀ x : G, x ∈ CFSG.ASVolI.ChIJK.URu (ruV M.L) (M.T : Subgroup G) ↔
      (x ∈ CFSG.ASVolI.ChIJK.SRu M.L ∧
        ∀ r ∈ CFSG.ASVolI.ChIJK.R1Ru M.L (M.T : Subgroup G), x⁻¹ * r⁻¹ * x * r ∈ ruV M.L) := by
  intro x
  rw [burnsideJ3b_URu_eq]
  constructor
  · intro hx
    have hxS : x ∈ ruS M.L := M.U_le_S hx
    refine ⟨hxS, fun r hr => ?_⟩
    have hrR : r ∈ M.R1 := burnsideJ3b_R1Ru_le M hr
    have hc := M.comm_R1_U (M.R1.inv_mem hrR) hx
    have hcomm := M.V_comm_S hc hxS
    have e : x⁻¹ * r⁻¹ * x * r = x⁻¹ * (r⁻¹ * x * r⁻¹⁻¹ * x⁻¹) * x := by group
    have e2 : x⁻¹ * (r⁻¹ * x * r⁻¹⁻¹ * x⁻¹) * x = r⁻¹ * x * r⁻¹⁻¹ * x⁻¹ := by
      calc x⁻¹ * (r⁻¹ * x * r⁻¹⁻¹ * x⁻¹) * x = x⁻¹ * ((r⁻¹ * x * r⁻¹⁻¹ * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (r⁻¹ * x * r⁻¹⁻¹ * x⁻¹)) := by rw [hcomm]
        _ = r⁻¹ * x * r⁻¹⁻¹ * x⁻¹ := by group
    rw [e, e2]
    exact hc
  · rintro ⟨hxS, hxr⟩
    rw [M.mem_U_iff hxS]
    refine (SL3.fix_R0_iff _ (M.χ_trace _)).mp fun g hg => ?_
    obtain ⟨r, hr, hrL, hθ⟩ := burnsideJ3b_exists_mem_R1Ru M hg
    have hw := hxr r⁻¹ (Subgroup.inv_mem _ hr)
    rw [inv_inv] at hw
    have hryS : r * x * r⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hrL) x).mp hxS
    have hwS : x⁻¹ * r * x * r⁻¹ ∈ ruS M.L := M.toRuData.V_le_S hw
    have hker : M.χ ⟨x⁻¹ * r * x * r⁻¹, hwS⟩ = 1 := by
      have : (⟨x⁻¹ * r * x * r⁻¹, hwS⟩ : ruS M.L) ∈ M.χ.ker := by
        rw [M.χ_ker, Subgroup.mem_subgroupOf]
        exact hw
      exact this
    have hprod : (⟨r * x * r⁻¹, hryS⟩ : ruS M.L) = ⟨x, hxS⟩ * ⟨x⁻¹ * r * x * r⁻¹, hwS⟩ := by
      apply Subtype.ext
      show r * x * r⁻¹ = x * (x⁻¹ * r * x * r⁻¹)
      group
    have hχ : M.χ ⟨r * x * r⁻¹, hryS⟩ = M.χ ⟨x, hxS⟩ := by
      rw [hprod, map_mul, hker, mul_one]
    have e := M.χ_conj ⟨r, hrL⟩ ⟨x, hxS⟩
    rw [hθ] at e
    have e' : Multiplicative.toAdd (M.χ ⟨r * x * r⁻¹, hryS⟩) = stAct g
        (Multiplicative.toAdd (M.χ ⟨x, hxS⟩)) := e
    rw [hχ] at e'
    exact e'.symm

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part9 (M : RuDataM G) :
    ∀ l ∈ M.L, l ∉ CFSG.ASVolI.ChIJK.HRu (M.T : Subgroup G) →
      CFSG.ASVolI.ChIJK.URu (ruV M.L) (M.T : Subgroup G) ⊓
        CFSG.conjugate (CFSG.ASVolI.ChIJK.URu (ruV M.L) (M.T : Subgroup G)) l = ruV M.L := by
  intro l hl hlH
  rw [burnsideJ3b_URu_eq]
  have hl' : l⁻¹ ∈ M.L := M.L.inv_mem hl
  have hne : M.conjU l⁻¹ ≠ ruU M.L M.T := by
    intro he
    have h1 : l⁻¹ ∈ M.LT1 := (M.conjU_eq_U_iff hl').mp he
    rw [← M.L_inf_H] at h1
    apply hlH
    rw [burnsideJ3b_HRu_eq]
    have := (ruH M.T).inv_mem h1.2
    simpa using this
  exact M.toRuDataN.U_inf_conjU hl' hne

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part6 (M : RuDataM G) {t : G} (ht : t ∈ ruS M.L) (htV : t ∉ ruV M.L) :
    ⁅Subgroup.zpowers t, ruS M.L⁆ = ruV M.L ∧
      (ruV M.L).relIndex (ruS M.L ⊓ Subgroup.centralizer ({t} : Set G)) = 2 ^ 5 := by
  constructor
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hkS : t ^ k ∈ ruS M.L := Subgroup.zpow_mem _ ht k
      rw [commutatorElement_def]
      exact M.comm_mem_V hkS hb
    · intro v hv
      have hvS : v ∈ ruS M.L := M.toRuData.V_le_S hv
      have hAtr : IsTraceZero (Multiplicative.toAdd (M.χ ⟨t, ht⟩)) := M.χ_trace _
      have hA0 : Multiplicative.toAdd (M.χ ⟨t, ht⟩) ≠ 0 := by
        intro h0
        apply htV
        have hk : (⟨t, ht⟩ : ruS M.L) ∈ M.χ.ker := by
          rw [MonoidHom.mem_ker]
          exact Multiplicative.toAdd.injective (by rw [toAdd_one]; exact h0)
        rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      obtain ⟨B, hB, hBy⟩ := M.Wc_top hAtr hA0 (Multiplicative.toAdd (M.ψV ⟨v, hv⟩))
      obtain ⟨s, hs⟩ := M.χ_surj B hB
      have h1 := M.ψV_comm ⟨t, ht⟩ s
      rw [hs, toAdd_ofAdd, hBy] at h1
      have h2 : M.ψV ⟨t * s * t⁻¹ * (s : G)⁻¹, M.comm_mem_V ht s.2⟩ = M.ψV ⟨v, hv⟩ :=
        Multiplicative.toAdd.injective h1
      have h3 := M.ψV.injective h2
      have h4 : t * (s : G) * t⁻¹ * (s : G)⁻¹ = v := congrArg Subtype.val h3
      rw [← h4]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t) s.2
  · have hVle : ruV M.L ≤ ruS M.L ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine le_inf M.toRuData.V_le_S fun v hv => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (M.V_comm_S hv ht).symm
    have h := Subgroup.relIndex_mul_card (ruV M.L) (ruS M.L ⊓ Subgroup.centralizer ({t} : Set G))
    rw [inf_eq_left.mpr hVle, M.card_centralizer_S ht htV, M.toRuData.card_V] at h
    norm_num at h ⊢
    omega

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_eq_z (M : RuDataM G) {z : G} (hz : Subgroup.zpowers z = ruZ M.T) :
    z = M.z := by
  have hzmem : z ∈ ruZ M.T := by
    rw [← hz]
    exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have h2 := M.toRuData.card_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h2
    omega
  · exact h1

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part7 (M : RuDataM G) {B : Subgroup G}
    (hB : CFSG.ASVolI.ChIJK.IsSylowIn 3 B
      (CFSG.ASVolI.ChIJK.L1Ru M.L (M.T : Subgroup G))) :
    Nonempty (↥(CFSG.ASVolI.ChIJK.QRu (M.T : Subgroup G) ⊓
      Subgroup.centralizer (B : Set G)) ≃* QuaternionGroup 2) := by
  obtain ⟨m, hmL1, hm⟩ := burnsideJ3b_exists_conj_B M hB
  have hBeq : B = M.B.map (MulAut.conj m).toMonoidHom := by
    ext x
    rw [hm x, burnsideJ3b_mem_map_conj]
  have hmH : m ∈ ruH M.T := M.LT1_le_H (burnsideJ3b_L1_le_LT1 M hmL1)
  have hQ : (ruQ M.T).map (MulAut.conj m).toMonoidHom = ruQ M.T :=
    burnsideJ3b_map_conj_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hmH)
  have hY : CFSG.ASVolI.ChIJK.QRu (M.T : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) =
      (ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G)).map (MulAut.conj m).toMonoidHom := by
    have hQ' : CFSG.ASVolI.ChIJK.QRu (M.T : Subgroup G) = ruQ M.T := by
      unfold CFSG.ASVolI.ChIJK.QRu
      rw [burnsideJ3b_HRu_eq]
    rw [hQ', Subgroup.map_inf _ _ _ (MulAut.conj m).injective, hQ,
      burnsideJ3b_map_centralizer_subgroup, ← hBeq]
  obtain ⟨e⟩ := M.lemma_J23_7
  exact ⟨(MulEquiv.subgroupCongr hY).trans
    ((Subgroup.equivMapOfInjective _ (MulAut.conj m).toMonoidHom (MulAut.conj m).injective).symm.trans
      e)⟩

end Parts

section Conj

variable {G : Type} [Group G] [Finite G]

private theorem burnsideJ3b_map_inf (φ : G ≃* G) (X Y : Subgroup G) :
    (X ⊓ Y).map φ.toMonoidHom = X.map φ.toMonoidHom ⊓ Y.map φ.toMonoidHom :=
  Subgroup.map_inf X Y _ φ.injective

private theorem burnsideJ3b_eq_map_conj {g : G} {X Y : Subgroup G}
    (h : ∀ x, x ∈ X ↔ g⁻¹ * x * g ∈ Y) : X = Y.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [h x, burnsideJ3b_mem_map_conj]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_S0_conj (M : RuDataM G) {g : G} (hg : g ∈ M.L) :
    ruS M.L ⊓ Subgroup.centralizer ((M.B7.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      M.S0.map (MulAut.conj g).toMonoidHom := by
  have h1 : (ruS M.L).map (MulAut.conj g).toMonoidHom = ruS M.L :=
    burnsideJ3b_map_conj_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hg)
  show _ = (ruS M.L ⊓ Subgroup.centralizer (M.B7 : Set G)).map (MulAut.conj g).toMonoidHom
  rw [burnsideJ3b_map_inf, h1, burnsideJ3b_map_centralizer_subgroup]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_CS_conj (M : RuDataM G) {g : G} (hg : g ∈ M.L) (s0 : G) :
    ruS M.L ⊓ Subgroup.centralizer ({g * s0 * g⁻¹} : Set G) =
      (ruS M.L ⊓ Subgroup.centralizer ({s0} : Set G)).map (MulAut.conj g).toMonoidHom := by
  have h1 : (ruS M.L).map (MulAut.conj g).toMonoidHom = ruS M.L :=
    burnsideJ3b_map_conj_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hg)
  rw [burnsideJ3b_map_inf, h1, burnsideJ3b_map_centralizer_singleton]
  rfl

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_CL_conj (M : RuDataM G) {g : G} (hg : g ∈ M.L) (s0 : G) :
    Subgroup.centralizer ({g * s0 * g⁻¹} : Set G) ⊓ M.L =
      (M.L ⊓ Subgroup.centralizer ({s0} : Set G)).map (MulAut.conj g).toMonoidHom := by
  have h1 : M.L.map (MulAut.conj g).toMonoidHom = M.L :=
    burnsideJ3b_map_conj_eq_self (Subgroup.le_normalizer hg)
  rw [burnsideJ3b_map_inf, h1, burnsideJ3b_map_centralizer_singleton, inf_comm]
  rfl

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_conj_data (M : RuDataM G) {g : G} (hg : g ∈ M.L) {B7 : Subgroup G}
    (hB7 : ∀ x, x ∈ B7 ↔ g⁻¹ * x * g ∈ M.B7) {s : G}
    (hs : s ∈ ruS M.L ⊓ Subgroup.centralizer (B7 : Set G)) (hs1 : s ≠ 1) :
    ∃ s0 ∈ M.S0, s0 ≠ 1 ∧ s = g * s0 * g⁻¹ := by
  have hB7eq := burnsideJ3b_eq_map_conj hB7
  subst hB7eq
  rw [burnsideJ3b_S0_conj M hg] at hs
  obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
  refine ⟨s0, hs0, fun h => hs1 ?_, rfl⟩
  rw [h, map_one]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part1 (M : RuDataM G) {g : G} (hg : g ∈ M.L) {B B7 : Subgroup G}
    (hB : ∀ x, x ∈ B ↔ g⁻¹ * x * g ∈ M.B) (hB7 : ∀ x, x ∈ B7 ↔ g⁻¹ * x * g ∈ M.B7) :
    ruS M.L ⊓ Subgroup.centralizer (B7 : Set G) =
        ⁅ruS M.L ⊓ Subgroup.centralizer (B7 : Set G), B⁆ ∧
      IsElemAbelian 2 (ruS M.L ⊓ Subgroup.centralizer (B7 : Set G)) ∧
      Nat.card ↥(ruS M.L ⊓ Subgroup.centralizer (B7 : Set G)) = 4 := by
  have hBeq := burnsideJ3b_eq_map_conj hB
  have hB7eq := burnsideJ3b_eq_map_conj hB7
  subst hBeq hB7eq
  rw [burnsideJ3b_S0_conj M hg]
  obtain ⟨h1, h2, h3⟩ := M.lemma_J23_1
  refine ⟨?_, burnsideJ3b_isElemAbelian_map _ h3, ?_⟩
  · rw [← Subgroup.map_commutator, h1]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h2]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part2 (M : RuDataM G) {g : G} (hg : g ∈ M.L) {B7 : Subgroup G}
    (hB7 : ∀ x, x ∈ B7 ↔ g⁻¹ * x * g ∈ M.B7) {z : G} (hz : z = M.z) :
    ∀ g' : G, g'⁻¹ * z * g' ∉ ruS M.L ⊓ Subgroup.centralizer (B7 : Set G) := by
  have hB7eq := burnsideJ3b_eq_map_conj hB7
  subst hB7eq
  rw [burnsideJ3b_S0_conj M hg]
  intro g' h
  have h1 := burnsideJ3b_mem_map_conj.mp h
  have h2 := M.lemma_J23_2 (g' * g)⁻¹
  apply h2
  rw [hz] at h1
  have e : (g' * g)⁻¹ * M.z * ((g' * g)⁻¹)⁻¹ = g⁻¹ * (g'⁻¹ * M.z * g') * g := by group
  rw [e]
  exact h1

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part3 (M : RuDataM G) {g : G} (hg : g ∈ M.L) {B7 : Subgroup G}
    (hB7 : ∀ x, x ∈ B7 ↔ g⁻¹ * x * g ∈ M.B7) {s : G}
    (hs : s ∈ ruS M.L ⊓ Subgroup.centralizer (B7 : Set G)) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set G) ⊓ M.L =
        (ruS M.L ⊓ Subgroup.centralizer (B7 : Set G)) ⊔
          ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ ⊔ B7 ∧
      CFSG.ASVolI.ChIJK.IsDirectProductOf (ruS M.L ⊓ Subgroup.centralizer (B7 : Set G))
        ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆
        (ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      CFSG.ASVolI.ChIJK.IsSylowTwoIn (ruS M.L ⊓ Subgroup.centralizer ({s} : Set G))
        (Subgroup.centralizer ({s} : Set G) ⊓ M.L) ∧
      Nat.card ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) = 2 ^ 8 ∧
      Monoid.exponent ↥(ruS M.L ⊓ Subgroup.centralizer ({s} : Set G)) = 4 := by
  obtain ⟨s0, hs0, hs01, rfl⟩ := burnsideJ3b_conj_data M hg hB7 hs hs1
  have hB7eq := burnsideJ3b_eq_map_conj hB7
  subst hB7eq
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := M.lemma_J23_3 hs0 hs01
  rw [burnsideJ3b_S0_conj M hg, burnsideJ3b_CS_conj M hg, burnsideJ3b_CL_conj M hg,
    ← Subgroup.map_commutator]
  have hle : ruS M.L ⊓ Subgroup.centralizer ({s0} : Set G) ≤
      M.L ⊓ Subgroup.centralizer ({s0} : Set G) := inf_le_inf_right _ M.toRuData.S_le_L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [c1, Subgroup.map_sup, Subgroup.map_sup]
  · exact burnsideJ3b_isDirectProductOf_map _ ⟨c4, c3, c2.symm⟩
  · exact burnsideJ3b_isSylowTwoIn_map _ (burnsideJ3b_isSylowTwoIn_of_sylow hle c5)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, c6]
  · rw [burnsideJ3b_exponent_map, c7]

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part4 (M : RuDataM G) {g : G} (hg : g ∈ M.L) {B B7 : Subgroup G}
    (hB : ∀ x, x ∈ B ↔ g⁻¹ * x * g ∈ M.B) (hB7 : ∀ x, x ∈ B7 ↔ g⁻¹ * x * g ∈ M.B7) {s : G}
    (hs : s ∈ ruS M.L ⊓ Subgroup.centralizer (B7 : Set G)) (hs1 : s ≠ 1) :
    B ≤ Subgroup.normalizer
        ((ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        ((ruS M.L ⊓ Subgroup.centralizer (B7 : Set G) : Subgroup G) : Set G) ∧
      B ≤ Subgroup.normalizer
        ((⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ : Subgroup G) : Set G) := by
  obtain ⟨s0, hs0, hs01, rfl⟩ := burnsideJ3b_conj_data M hg hB7 hs hs1
  have hBeq := burnsideJ3b_eq_map_conj hB
  have hB7eq := burnsideJ3b_eq_map_conj hB7
  subst hBeq hB7eq
  obtain ⟨n1, n2, n3⟩ := M.lemma_J23_4 hs0 hs01
  rw [burnsideJ3b_S0_conj M hg, burnsideJ3b_CS_conj M hg, ← Subgroup.map_commutator]
  exact ⟨burnsideJ3b_map_le_normalizer _ n1, burnsideJ3b_map_le_normalizer _ n2,
    burnsideJ3b_map_le_normalizer _ n3⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ3b_part5 (M : RuDataM G) {g : G} (hg : g ∈ M.L) {B7 : Subgroup G}
    (hB7 : ∀ x, x ∈ B7 ↔ g⁻¹ * x * g ∈ M.B7) {s : G}
    (hs : s ∈ ruS M.L ⊓ Subgroup.centralizer (B7 : Set G)) (hs1 : s ≠ 1) :
    CFSG.ASVolI.ChIJK.IsSuzukiTwoGroup
        ↥⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ ∧
      ∃ a ∈ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆,
        ∃ b ∈ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆, a * b ≠ b * a := by
  obtain ⟨s0, hs0, hs01, rfl⟩ := burnsideJ3b_conj_data M hg hB7 hs hs1
  have hB7eq := burnsideJ3b_eq_map_conj hB7
  subst hB7eq
  rw [burnsideJ3b_CS_conj M hg, ← Subgroup.map_commutator]
  refine ⟨?_, ?_⟩
  · exact burnsideJ3b_isSuzukiTwoGroup_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective)
      (burnsideJ3b_isSuzukiTwoGroup_of_basic (M.lemma_J23_5 hs0 hs01))
  · have hnc := M.S1_not_comm
    push Not at hnc
    obtain ⟨y, hy, y', hy', hne⟩ := hnc
    rw [← M.commutator_eq_S1 hs0 hs01] at hy hy'
    refine ⟨(MulAut.conj g).toMonoidHom y, Subgroup.mem_map_of_mem _ hy,
      (MulAut.conj g).toMonoidHom y', Subgroup.mem_map_of_mem _ hy', fun h => hne ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact (MulAut.conj g).injective h

end Conj

end BurnsideJ3b

theorem as_J_2_3 : J_2_3 := by
  intro G _ _ L V T h B B7 hB hB7L hB7c hBn z s hz hs hs1
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM CFSG.Quasithin.RuType.stUnique
  have hV : V = CFSG.Quasithin.RuType.ruV L := h.V_eq_ruV
  have hT : T = (M.T : Subgroup G) := by
    rw [hMT]
    exact h.coe_sylowT.symm
  clear hMT
  subst hML
  subst hT
  subst hV
  obtain ⟨g, hgL, hBg, hB7g⟩ := burnsideJ3b_exists_pair_conj M hB hB7L hB7c hBn
  have hzM : z = M.z :=
    burnsideJ3b_eq_z M (by rw [← burnsideJ3b_ZRu_eq]; exact hz)
  refine ⟨burnsideJ3b_part1 M hgL hBg hB7g, burnsideJ3b_part2 M hgL hB7g hzM,
    burnsideJ3b_part3 M hgL hB7g hs hs1, burnsideJ3b_part4 M hgL hBg hB7g hs hs1,
    burnsideJ3b_part5 M hgL hB7g hs hs1, ?_, burnsideJ3b_part7 M hB, burnsideJ3b_part8 M,
    burnsideJ3b_part9 M⟩
  intro t ht htV
  exact burnsideJ3b_part6 M ht htV

@[expose] def J_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ h ∈ HCRu V T, h ∉ URu V T →
      ⁅Subgroup.zpowers h, QRu T⁆ ⊔ ZRu T = URu V T ∧
      ⁅Subgroup.zpowers h, QRu T⁆ = URu V T ∧
      QRu T ⊓ Subgroup.centralizer ({h} : Set G) = Subgroup.zpowers h ⊔ URu V T

private theorem burnsideJ1_J_2_4_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) :
    CFSG.ASVolI.J_2_4 := by
  intro G _ _ L V T h
  obtain ⟨M, hML, hMT, hV, hZ, hH, hQ, hU⟩ := burnsideJ1_exists_M hSt h
  subst hML
  subst hMT
  subst hV
  intro x hx hxU
  have hHC : CFSG.ASVolI.ChIJK.HCRu (CFSG.Quasithin.RuType.ruV M.L) (M.T : Subgroup G) =
      M.HC := by
    unfold CFSG.ASVolI.ChIJK.HCRu
    rw [hH, hU]
  rw [hHC] at hx
  rw [hU] at hxU
  obtain ⟨-, h2, h3⟩ := M.lemma_J24 hx hxU
  have hcomm : ⁅Subgroup.zpowers x, CFSG.Quasithin.RuType.ruQ M.T⁆ =
      CFSG.Quasithin.RuType.ruU M.L M.T := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact M.comm_HC_Q_mem_U ((Subgroup.zpowers_le.mpr hx) ha) hb
    · rw [← h2, Subgroup.closure_le]
      rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) hq
  rw [hQ, hU, hZ]
  refine ⟨?_, hcomm, h3⟩
  rw [hcomm]
  exact sup_eq_left.mpr M.two.Z_le_U

theorem as_J_2_4 : J_2_4 :=
  burnsideJ1_J_2_4_of_st CFSG.Quasithin.RuType.stUnique

@[expose] def J_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B : Subgroup G, IsSylowIn 3 B (L1Ru L T) →
      Nonempty (↥(QRu T ⊓ Subgroup.centralizer (B : Set G)) ≃* QuaternionGroup 2) ∧
      ∃ (_ : (B.subgroupOf (HRu T ⊓ Subgroup.centralizer (B : Set G))).Normal),
        Nonempty (↥(HRu T ⊓ Subgroup.centralizer (B : Set G)) ⧸
          B.subgroupOf (HRu T ⊓ Subgroup.centralizer (B : Set G)) ≃* SemidihedralGroup 4)

private theorem burnsideJ1_J_2_5_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) :
    CFSG.ASVolI.J_2_5 := by
  intro G _ _ L V T h B hB
  obtain ⟨M, hML, hMT, hV, -, hH, hQ, -⟩ := burnsideJ1_exists_M hSt h
  subst hML
  subst hMT
  subst hV
  obtain ⟨l, hl, hlB⟩ := burnsideJ1_sylow3_conj M hB
  have hlH : l ∈ CFSG.Quasithin.RuType.ruH M.T := (burnsideJ1_L1_le M hl).1
  have hHc : ∀ x : G, x ∈ CFSG.Quasithin.RuType.ruH M.T ↔
      l⁻¹ * x * l ∈ CFSG.Quasithin.RuType.ruH M.T := fun x =>
    ⟨fun hx => mul_mem (mul_mem (inv_mem hlH) hx) hlH, fun hx => by
      have := mul_mem (mul_mem hlH hx) (inv_mem hlH)
      simpa [mul_assoc] using this⟩
  have hQc : ∀ x : G, x ∈ CFSG.Quasithin.RuType.ruQ M.T ↔
      l⁻¹ * x * l ∈ CFSG.Quasithin.RuType.ruQ M.T := fun x =>
    ⟨fun hx => by
      have := M.conj_mem_Q (inv_mem hlH) hx
      simpa using this, fun hx => by
      have := M.conj_mem_Q hlH hx
      simpa [mul_assoc] using this⟩
  have hCc : ∀ x : G, x ∈ Subgroup.centralizer (B : Set G) ↔
      l⁻¹ * x * l ∈ Subgroup.centralizer (M.B : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx b hb
      have hb' : l * b * l⁻¹ ∈ B := (hlB _).mpr (by simpa [mul_assoc] using hb)
      have := hx _ hb'
      calc b * (l⁻¹ * x * l) = l⁻¹ * ((l * b * l⁻¹) * x) * l := by group
        _ = l⁻¹ * (x * (l * b * l⁻¹)) * l := by rw [this]
        _ = l⁻¹ * x * l * b := by group
    · intro hx b hb
      have hb' : l⁻¹ * b * l ∈ M.B := (hlB b).mp hb
      have := hx _ hb'
      calc b * x = l * ((l⁻¹ * b * l) * (l⁻¹ * x * l)) * l⁻¹ := by group
        _ = l * ((l⁻¹ * x * l) * (l⁻¹ * b * l)) * l⁻¹ := by rw [this]
        _ = x * b := by group
  rw [hQ, hH]
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := M.lemma_J25
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := burnsideJ1_equiv_conj
      (X₁ := CFSG.Quasithin.RuType.ruQ M.T ⊓ Subgroup.centralizer (M.B : Set G))
      (X₂ := CFSG.Quasithin.RuType.ruQ M.T ⊓ Subgroup.centralizer (B : Set G)) l
      (fun x => by rw [Subgroup.mem_inf, Subgroup.mem_inf, hQc x, hCc x])
    exact ⟨e.symm.trans e1⟩
  · haveI hN : (B.subgroupOf (CFSG.Quasithin.RuType.ruH M.T ⊓
        Subgroup.centralizer (B : Set G))).Normal :=
      ⟨fun x hx g => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        have hc : ((g : ↥(CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer (B : Set G))) : G) ∈
            Subgroup.centralizer (B : Set G) := (Subgroup.mem_inf.mp g.2).2
        have e : ((g * x * g⁻¹ : ↥(CFSG.Quasithin.RuType.ruH M.T ⊓
            Subgroup.centralizer (B : Set G))) : G) = x := by
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
          rw [← (Subgroup.mem_centralizer_iff.mp hc) x hx]
          group
        rw [e]
        exact hx⟩
    refine ⟨hN, ?_⟩
    obtain ⟨e⟩ := burnsideJ1_quotEquiv_conj
      (C₁ := CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer (M.B : Set G))
      (C₂ := CFSG.Quasithin.RuType.ruH M.T ⊓ Subgroup.centralizer (B : Set G))
      (A₁ := M.B) (A₂ := B) l
      (fun x => by rw [Subgroup.mem_inf, Subgroup.mem_inf, hHc x, hCc x]) hlB
    exact ⟨e.symm.trans e2⟩

theorem as_J_2_5 : J_2_5 :=
  burnsideJ1_J_2_5_of_st CFSG.Quasithin.RuType.stUnique

@[expose] def J_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      ((∀ i ∈ involutionsOf (HRu T), i ∉ KRu T → ∀ j ∈ involutionsOf (HRu T), j ∉ KRu T →
          ∃ h ∈ HRu T, j = h⁻¹ * i * h) ∧
        (involutionsOf (HRu T) \ (KRu T : Set G)).ncard = 640 ∧
        (∀ i ∈ involutionsOf (HRu T), i ∉ KRu T → i ∈ conjClass z)) ∧
      (∀ i ∈ involutionsOf L, i ∉ SRu L → i ∈ conjClass z) ∧
      (∀ i ∈ involutionsOf (QRu T), i ∈ conjClass z) ∧
      (URu V T = omegaOne (HCRu V T) ∧ ZRu T = frattiniOf (HCRu V T) ∧
        ∀ u ∈ URu V T, u ≠ 1 → u ∈ conjClass z)

private theorem burnsideJ1_J_2_6_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) :
    CFSG.ASVolI.J_2_6 := by
  intro G _ _ L V T h z hz
  obtain ⟨M, hML, hMT, hV, hZ, hH, hQ, hU⟩ := burnsideJ1_exists_M hSt h
  subst hML
  subst hMT
  subst hV
  have hK : CFSG.ASVolI.ChIJK.KRu (M.T : Subgroup G) = M.K := by
    unfold CFSG.ASVolI.ChIJK.KRu
    rw [hH]
    exact burnsideJ1_twoResidual_eq_K M
  have hHC : CFSG.ASVolI.ChIJK.HCRu (CFSG.Quasithin.RuType.ruV M.L) (M.T : Subgroup G) =
      M.HC := by
    unfold CFSG.ASVolI.ChIJK.HCRu
    rw [hH, hU]
  have hzz : z = M.z := burnsideJ1_eq_z M (hz.trans hZ)
  subst hzz
  obtain ⟨h1, hcard, h1z, h2, h3, hΩ, hΦ, hU1⟩ := M.lemma_J26
  rw [hK, hHC, hH, hQ, hU, hZ]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i ⟨hiH, hi2, -⟩ hiK j ⟨hjH, hj2, -⟩ hjK
    obtain ⟨g, hg, hgij⟩ := h1 i j ⟨hiH, hiK, hi2⟩ ⟨hjH, hjK, hj2⟩
    exact ⟨g⁻¹, inv_mem hg, by rw [inv_inv]; exact hgij.symm⟩
  · have hset : CFSG.ASVolI.ChIJK.involutionsOf (CFSG.Quasithin.RuType.ruH M.T) \ (M.K : Set G) =
        {i | i ∈ CFSG.Quasithin.RuType.ruH M.T ∧ i ∉ M.K ∧ i ^ 2 = 1} := by
      ext i
      constructor
      · rintro ⟨⟨hiH, hi2, -⟩, hiK⟩
        exact ⟨hiH, hiK, hi2⟩
      · rintro ⟨hiH, hiK, hi2⟩
        refine ⟨⟨hiH, hi2, ?_⟩, hiK⟩
        rintro rfl
        exact hiK M.K.one_mem
    rw [hset, ← Nat.card_coe_set_eq]
    exact hcard
  · rintro i ⟨hiH, hi2, -⟩ hiK
    exact (burnsideJ1_mem_conjClass_iff _ _).mpr (h1z i hiH hiK hi2)
  · rintro i ⟨hiL, hi2, -⟩ hiS
    exact (burnsideJ1_mem_conjClass_iff _ _).mpr (h2 i hiL hiS hi2)
  · rintro i ⟨hiQ, hi2, hi1⟩
    exact (burnsideJ1_mem_conjClass_iff _ _).mpr (h3 i hiQ hi2 hi1)
  · exact hΩ.symm
  · exact hΦ.symm
  · intro u hu hu1
    exact (burnsideJ1_mem_conjClass_iff _ _).mpr (hU1 u hu hu1)

theorem as_J_2_6 : J_2_6 :=
  burnsideJ1_J_2_6_of_st CFSG.Quasithin.RuType.stUnique

@[expose] def J_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
        IsHatCover ↥(LBRu B) (alternatingGroup (Fin 6)) ∧
        (∃ (_ : (B.subgroupOf (Subgroup.centralizer (B : Set G))).Normal),
          Nonempty (↥(Subgroup.centralizer (B : Set G)) ⧸
            B.subgroupOf (Subgroup.centralizer (B : Set G)) ≃*
            ↥(NativeSporadic.M11 ⊓
              MulAction.stabilizer (Equiv.Perm (Fin 11)) (0 : Fin 11)))) ∧
        (∃ (_ : (B.subgroupOf (Subgroup.normalizer (B : Set G))).Normal),
          Nonempty (↥(Subgroup.normalizer (B : Set G)) ⧸
            B.subgroupOf (Subgroup.normalizer (B : Set G)) ≃*
            MulAut (alternatingGroup (Fin 6)))) ∧
        ((∀ i ∈ involutionsOf (⊤ : Subgroup G), i ∈ conjClass s ∨ i ∈ conjClass z) ∧
          s ∉ conjClass z) ∧
        (∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) →
          Subgroup.centralizer (B5 : Set G) =
            pCoreOf 5 (Subgroup.centralizer (B5 : Set G)) ⊔
              (QRu T ⊓ Subgroup.centralizer (B5 : Set G)) ∧
          Nonempty (↥(QRu T ⊓ Subgroup.centralizer (B5 : Set G)) ≃* QuaternionGroup 2) ∧
          Nat.card ↥(pCoreOf 5 (Subgroup.centralizer (B5 : Set G))) = 5 ^ 3 ∧
          ∀ g : G, ¬ IsSylowIn 5 (CFSG.conjugate B5 g) (LBRu B)) ∧
        ((∀ i ∈ involutionsOf (LBRu B), i ∈ conjClass z) ∧
          (∀ i ∈ involutionsOf (⊤ : Subgroup G), InducesTranspositionOn i (LBRu B) →
            i ∈ conjClass z) ∧
          (∀ i ∈ involutionsOf (⊤ : Subgroup G), InducesDiagonalOn i (LBRu B) →
            i ∈ conjClass s)) ∧
        ((∃ a ∈ involutionsOf (KRu T), a ∉ QRu T ∧ ∃ b ∈ involutionsOf (KRu T), b ∉ QRu T ∧
            (∀ i ∈ involutionsOf (KRu T), i ∉ QRu T →
              (∃ h ∈ HRu T, i = h⁻¹ * a * h) ∨ (∃ h ∈ HRu T, i = h⁻¹ * b * h)) ∧
            (¬ ∃ h ∈ HRu T, b = h⁻¹ * a * h) ∧ a ∈ conjClass s ∧ b ∈ conjClass z) ∧
          (∀ x ∈ HRu T, x ∈ conjClass s → ∃ h ∈ HRu T, x = h⁻¹ * s * h) ∧
          (∀ x ∈ HRu T, x ∈ conjClass s → x ∈ KRu T ∧ x ∉ QRu T) ∧
          (conjClass z ∩ ((KRu T : Set G) \ (QRu T : Set G))).ncard = 480) ∧
        (∀ i ∈ involutionsOf (Subgroup.centralizer (B : Set G)), i ∈ conjClass z) ∧
        (S0Ru L B7 ⊔ ⁅SRu L ⊓ Subgroup.centralizer ({s} : Set G), B7⁆ =
            HRu T ⊓ Subgroup.centralizer ({s} : Set G) ∧
          IsSylowTwoIn (HRu T ⊓ Subgroup.centralizer ({s} : Set G))
            (Subgroup.centralizer ({s} : Set G))) ∧
        (∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, y = g⁻¹ * x * g)


@[expose] def J_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      ((∀ i ∈ involutionsOf (QRu T), i ∉ URu V T → ∀ j ∈ involutionsOf (QRu T), j ∉ URu V T →
          ∃ h ∈ HRu T, j = h⁻¹ * i * h) ∧
        (involutionsOf (QRu T) \ (URu V T : Set G)).ncard = 240 ∧
        (∀ i ∈ involutionsOf (QRu T), i ∉ URu V T → i ∈ conjClass z)) ∧
      (∀ i ∈ involutionsOf (SRu L ⊓ QRu T), ∃ l ∈ L, l⁻¹ * i * l ∈ URu V T) ∧
      (∀ u ∈ URu V T, u ∉ V →
        ∀ i ∈ involutionsOf (SRu L ⊓ Subgroup.centralizer ({u} : Set G)), i ∈ conjClass z)

section BurnsideJ28a

section BurnsideJ28Two8

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_exists_M (hSt : CFSG.Quasithin.RuType.StUniqueStatement)
    {G : Type} [Group G] [Finite G] {L V T : Subgroup G} (h : CFSG.ASVolI.ChIJK.RuType G L V T) :
    ∃ M : RuDataM G, M.L = L ∧ (M.T : Subgroup G) = T ∧ V = ruV M.L ∧
      CFSG.ASVolI.ChIJK.ZRu T = ruZ M.T ∧ CFSG.ASVolI.ChIJK.HRu T = ruH M.T ∧
      CFSG.ASVolI.ChIJK.QRu T = ruQ M.T ∧ CFSG.ASVolI.ChIJK.URu V T = ruU M.L M.T := by
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM hSt
  have hT : (M.T : Subgroup G) = T := by rw [hMT]; exact h.coe_sylowT
  have hV : V = ruV M.L := by
    rw [hML]; exact CFSG.ASVolI.ChIJK.RuType.V_eq_ruV h
  refine ⟨M, hML, hT, hV, ?_, ?_, ?_, ?_⟩
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.ZRu_eq_ruZ h
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.HRu_eq_ruH h
  · rw [hMT]; exact CFSG.ASVolI.ChIJK.RuType.QRu_eq_ruQ h
  · rw [hMT, hML]; exact CFSG.ASVolI.ChIJK.RuType.URu_eq_ruU h

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_comm_HC_mem_Z {G : Type} [Group G] [Finite G] (M : RuDataM G) {a b : G}
    (ha : a ∈ M.HC) (hb : b ∈ M.HC) : a * b * a⁻¹ * b⁻¹ ∈ ruZ M.T := by
  have hc : a ^ 2 ∈ ruZ M.T := M.sq_HC_mem_Z ha
  have hd : b ^ 2 ∈ ruZ M.T := M.sq_HC_mem_Z hb
  have he : (a * b) ^ 2 ∈ ruZ M.T := M.sq_HC_mem_Z (mul_mem ha hb)
  have hbH : b ∈ ruH M.T := (Subgroup.mem_inf.mp hb).1
  have hcomm : b * (a ^ 2)⁻¹ = (a ^ 2)⁻¹ * b := by
    have := M.Z_comm_H (inv_mem hc) hbH
    exact this.symm
  have e : a * b * a⁻¹ * b⁻¹ = (a * b) ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by
    calc a * b * a⁻¹ * b⁻¹ = a * b * a * ((a ^ 2)⁻¹ * b) * (b ^ 2)⁻¹ := by group
      _ = a * b * a * (b * (a ^ 2)⁻¹) * (b ^ 2)⁻¹ := by rw [hcomm]
      _ = (a * b) ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ := by rw [pow_two (a * b)]; group
  rw [e]
  exact mul_mem (mul_mem he (inv_mem hc)) (inv_mem hd)

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_mem_HC_of_comm_Z {G : Type} [Group G] [Finite G] (M : RuDataM G) {h w : G}
    (hh : h ∈ M.HC) (hU : h ∉ ruU M.L M.T) (hw : w ∈ ruQ M.T)
    (hz : h * w * h⁻¹ * w⁻¹ ∈ ruZ M.T) : w ∈ M.HC := by
  have hFh0 : ∀ q : ruQ M.T, h * (q : G) * h⁻¹ * (q : G)⁻¹ ∈ ruZ M.T → M.Fh h hh q = 0 := by
    intro q hq
    unfold RuDataM.Fh
    have : M.ψU ⟨_, M.comm_HC_Q_mem_U hh q.2⟩ = 1 := (M.ψU_eq_one_iff _).mpr hq
    rw [this, toAdd_one]
  let g := M.FhHom h hh
  have hsurj : Function.Surjective g := by
    intro v
    obtain ⟨q, hq⟩ := M.Fh_surj hh hU (Multiplicative.toAdd v)
    refine ⟨q, ?_⟩
    show Multiplicative.ofAdd (M.Fh h hh q) = v
    rw [hq, ofAdd_toAdd]
  have hle : M.HC.subgroupOf (ruQ M.T) ≤ g.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (M.Fh h hh q) = 1
    rw [hFh0 q (burnsideJ28_comm_HC_mem_Z M hh (Subgroup.mem_subgroupOf.mp hq))]
    rfl
  have hcard : Nat.card g.ker * 16 = 2 ^ 11 := by
    have := Subgroup.card_ker_mul_card_of_surjective hsurj
    rw [M.toRuData.card_Q, RuData.card_F4sq] at this
    exact this
  have heq : M.HC.subgroupOf (ruQ M.T) = g.ker := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_subgroupOf_of_le M.HC_le_Q, M.card_HC]
    omega
  have hwk : (⟨w, hw⟩ : ruQ M.T) ∈ g.ker := by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (M.Fh h hh ⟨w, hw⟩) = 1
    rw [hFh0 ⟨w, hw⟩ hz]
    rfl
  rw [← heq, Subgroup.mem_subgroupOf] at hwk
  exact hwk

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_sq_eq_z {G : Type} [Group G] [Finite G] (M : RuDataM G) {h : G}
    (hh : h ∈ M.HC) (hU : h ∉ ruU M.L M.T) : h ^ 2 = M.z := by
  rcases M.mem_Z_iff.mp (M.sq_HC_mem_Z hh) with h1 | h1
  · exact absurd (M.mem_U_of_HC_sq hh h1) hU
  · exact h1

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_inv_coset {G : Type} [Group G] [Finite G] (M : RuDataM G) {w c : G}
    (hwQ : w ∈ ruQ M.T) (hw2 : w ^ 2 = 1) (hwC : w ∉ M.HC) (hc : c ∈ M.HC) :
    (w * c) ^ 2 = 1 ↔ (c ∈ ruU M.L M.T ∧ w * c = c * w) := by
  have hww : w * w = 1 := by rw [← pow_two]; exact hw2
  constructor
  · intro h
    have h1 : w * c * w * c = 1 := by
      have : (w * c) ^ 2 = w * c * w * c := by rw [pow_two]; group
      rw [this] at h
      exact h
    have hcU : c ∈ ruU M.L M.T := by
      by_contra hcU
      have hc2 : c ^ 2 = M.z := burnsideJ28_sq_eq_z M hc hcU
      have hz1 : M.z ∈ ruZ M.T := M.z_mem_Z
      have hwH : w ∈ ruH M.T := pCoreOf_le 2 _ hwQ
      have hcm : Commute M.z w := M.Z_comm_H hz1 hwH
      have h2 : c * w * c = w⁻¹ := by
        calc c * w * c = w⁻¹ * (w * c * w * c) := by group
          _ = w⁻¹ := by rw [h1, mul_one]
      have h3 : c⁻¹ = c * (M.z)⁻¹ := by
        rw [← hc2]
        group
      have e : c * w * c⁻¹ * w⁻¹ = (M.z)⁻¹ := by
        calc c * w * c⁻¹ * w⁻¹ = (c * w * c) * ((M.z)⁻¹ * w⁻¹) := by rw [h3]; group
          _ = w⁻¹ * ((M.z)⁻¹ * w⁻¹) := by rw [h2]
          _ = w⁻¹ * (w⁻¹ * (M.z)⁻¹) := by rw [hcm.inv_inv.eq]
          _ = (w * w)⁻¹ * (M.z)⁻¹ := by group
          _ = (M.z)⁻¹ := by rw [hww]; simp
      have hcomm : c * w * c⁻¹ * w⁻¹ ∈ ruZ M.T := by
        rw [e]
        exact inv_mem hz1
      exact hwC (burnsideJ28_mem_HC_of_comm_Z M hc hcU hwQ hcomm)
    refine ⟨hcU, ?_⟩
    have hcc : c * c = 1 := by rw [← pow_two]; exact M.U_sq hcU
    have h4 : w * c * w = c := by
      calc w * c * w = w * c * w * (c * c) := by rw [hcc, mul_one]
        _ = (w * c * w * c) * c := by group
        _ = c := by rw [h1, one_mul]
    calc w * c = w * c * (w * w) := by rw [hww, mul_one]
      _ = (w * c * w) * w := by group
      _ = c * w := by rw [h4]
  · rintro ⟨hcU, hcomm⟩
    have hcc : c * c = 1 := by rw [← pow_two]; exact M.U_sq hcU
    rw [pow_two]
    calc w * c * (w * c) = w * (c * w) * c := by group
      _ = w * (w * c) * c := by rw [hcomm]
      _ = (w * w) * (c * c) := by group
      _ = 1 := by rw [hww, hcc, mul_one]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_card_centralizer_U {G : Type} [Group G] [Finite G] (M : RuDataM G) {w : G}
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) :
    Nat.card ↥(ruU M.L M.T ⊓ Subgroup.centralizer ({w} : Set G)) = 16 := by
  let g : ruU M.L M.T →* ruZ M.T :=
    { toFun := fun u => ⟨w * u * w⁻¹ * (u : G)⁻¹, M.comm_mem_Z hwQ u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u u' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact M.comm_mul_right hwQ u.2 u'.2) }
  have key : ∀ u : ruU M.L M.T, u ∈ g.ker ↔ (u : G) * w = w * u := by
    intro u
    rw [MonoidHom.mem_ker]
    constructor
    · intro hu
      have h1 : w * (u : G) * w⁻¹ * (u : G)⁻¹ = 1 := congrArg Subtype.val hu
      calc (u : G) * w = (w * (u : G) * w⁻¹ * (u : G)⁻¹)⁻¹ * (w * u) := by group
        _ = w * u := by rw [h1]; simp
    · intro hu
      apply Subtype.ext
      show w * (u : G) * w⁻¹ * (u : G)⁻¹ = 1
      calc w * (u : G) * w⁻¹ * (u : G)⁻¹ = (w * u) * w⁻¹ * (u : G)⁻¹ := by group
        _ = (u * w) * w⁻¹ * (u : G)⁻¹ := by rw [hu]
        _ = 1 := by group
  have hker : Nat.card g.ker = Nat.card ↥(ruU M.L M.T ⊓ Subgroup.centralizer ({w} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨u.1.1, u.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
          ((key u.1).mp u.2)⟩
        invFun := fun u => ⟨⟨u.1, (Subgroup.mem_inf.mp u.2).1⟩, (key _).mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp u.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hex : ∃ u : ruU M.L M.T, ¬ ((u : G) * w = w * u) := by
    by_contra hall
    push Not at hall
    apply hwC
    exact Subgroup.mem_inf.mpr ⟨pCoreOf_le 2 _ hwQ,
      Subgroup.mem_centralizer_iff.mpr fun u hu => hall ⟨u, hu⟩⟩
  have hrange : Nat.card g.range = 2 := by
    have hle : Nat.card g.range ≤ 2 := by
      rw [← M.toRuData.card_Z]
      exact Subgroup.card_le_card_group _
    have hne : Nat.card g.range ≠ 1 := by
      intro h1
      obtain ⟨u, hu⟩ := hex
      have hbot : g.range = ⊥ := Subgroup.card_eq_one.mp h1
      have : g u ∈ g.range := ⟨u, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hu ((key u).mp (MonoidHom.mem_ker.mpr this))
    have hpos : 0 < Nat.card g.range := Nat.card_pos
    omega
  have h := Subgroup.card_ker_mul_card_range g
  rw [hker, hrange, M.toRuData.card_U] at h
  omega

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_comm_Q_mem_HC {G : Type} [Group G] [Finite G] (M : RuDataM G) {a b : G}
    (ha : a ∈ ruQ M.T) (hb : b ∈ ruQ M.T) : a * b * a⁻¹ * b⁻¹ ∈ M.HC := by
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ ruQ M.T :=
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hk : (⟨a * b * a⁻¹ * b⁻¹, hmem⟩ : ruQ M.T) ∈ M.ψQ.ker := by
    rw [MonoidHom.mem_ker]
    have e : (⟨a * b * a⁻¹ * b⁻¹, hmem⟩ : ruQ M.T) =
        ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_exists_w {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ∃ l ∈ M.L, M.conjU l ≠ ruU M.L M.T ∧
      ∃ w ∈ M.conjU l, w ∈ ruQ M.T ∧ w ∉ M.HC ∧ w ^ 2 = 1 := by
  obtain ⟨l, hl, hQ⟩ := M.exists_conjU_not_le_Q
  have hne : M.conjU l ≠ ruU M.L M.T := fun e => hQ (e ▸ M.U_le_Q)
  have h := M.conjU_inf_Q_not_le_HC hl hne
  rw [SetLike.not_le_iff_exists] at h
  obtain ⟨w, hw, hwC⟩ := h
  obtain ⟨hwl, hwQ⟩ := Subgroup.mem_inf.mp hw
  refine ⟨l, hl, hne, w, hwl, hwQ, hwC, ?_⟩
  have h1 : l⁻¹ * w * l ∈ ruU M.L M.T := M.mem_conjU.mp hwl
  have h2 := M.U_sq h1
  have e : l * (l⁻¹ * w * l) ^ 2 * l⁻¹ = w ^ 2 := by
    rw [pow_two, pow_two]
    group
  rw [← e, h2]
  group

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_theta_mem {G : Type} [Group G] [Finite G] (M : RuDataM G) {w y : G}
    (hwQ : w ∈ ruQ M.T) (hw2 : w ^ 2 = 1) (hwC : w ∉ M.HC) (hy : y ∈ ruQ M.T) :
    w⁻¹ * (y * w * y⁻¹) ∈ ruU M.L M.T ∧ w * (w⁻¹ * (y * w * y⁻¹)) = (w⁻¹ * (y * w * y⁻¹)) * w := by
  have hc : w⁻¹ * (y * w * y⁻¹) ∈ M.HC := by
    have := burnsideJ28_comm_Q_mem_HC M (inv_mem hwQ) hy
    simpa [mul_assoc] using this
  have h2 : (w * (w⁻¹ * (y * w * y⁻¹))) ^ 2 = 1 := by
    rw [mul_inv_cancel_left, conj_pow, hw2]
    group
  exact (burnsideJ28_inv_coset M hwQ hw2 hwC hc).mp h2

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_theta_mul {G : Type} [Group G] [Finite G] (M : RuDataM G) {w h y : G}
    (hwQ : w ∈ ruQ M.T) (hw2 : w ^ 2 = 1) (hwC : w ∉ M.HC) (hh : h ∈ M.HC)
    (hy : y ∈ ruQ M.T) :
    w⁻¹ * (h * y * w * (h * y)⁻¹) =
      (w⁻¹ * (h * w * h⁻¹)) * (w⁻¹ * (y * w * y⁻¹)) := by
  obtain ⟨hcU, -⟩ := burnsideJ28_theta_mem M hwQ hw2 hwC hy
  have hcomm : (w⁻¹ * (y * w * y⁻¹)) * h = h * (w⁻¹ * (y * w * y⁻¹)) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2 _ hcU
  calc w⁻¹ * (h * y * w * (h * y)⁻¹)
      = w⁻¹ * h * (y * w * y⁻¹) * h⁻¹ := by group
    _ = w⁻¹ * h * (w * (w⁻¹ * (y * w * y⁻¹))) * h⁻¹ := by rw [mul_inv_cancel_left]
    _ = (w⁻¹ * (h * w * h⁻¹)) * (h * (w⁻¹ * (y * w * y⁻¹)) * h⁻¹) := by group
    _ = (w⁻¹ * (h * w * h⁻¹)) * (w⁻¹ * (y * w * y⁻¹)) := by
      rw [← hcomm, mul_inv_cancel_right]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_exists_y0 {G : Type} [Group G] [Finite G] (M : RuDataM G) {l w : G}
    (hl : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) (hwl : w ∈ M.conjU l)
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) (hw2 : w ^ 2 = 1) :
    ∃ y ∈ ruQ M.T, w⁻¹ * (y * w * y⁻¹) ∉ ruV M.L := by
  have hzV : l * M.z * l⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V hl M.z_mem_V
  have hzU : l * M.z * l⁻¹ ∈ ruU M.L M.T := M.V_le_U hzV
  have hzZ : l * M.z * l⁻¹ ∉ ruZ M.T := M.z_conj_not_mem_Z hl hne
  obtain ⟨y, hyQ, hyc⟩ : ∃ y ∈ ruQ M.T, ¬ (y * (l * M.z * l⁻¹) = (l * M.z * l⁻¹) * y) := by
    by_contra hall
    push Not at hall
    exact hzZ (M.mem_Z_of_comm_Q hzU fun q hq => hall q hq)
  refine ⟨y, hyQ, fun hV => ?_⟩
  obtain ⟨hΘU, -⟩ := burnsideJ28_theta_mem M hwQ hw2 hwC hyQ
  have hΘC : w⁻¹ * (y * w * y⁻¹) ∈ M.HC := M.U_le_HC hΘU
  set x := y * w * y⁻¹ with hx
  have hxe : x = w * (w⁻¹ * x) := by group
  have hxl : x ∈ M.conjU l := by
    rw [hxe]
    exact mul_mem hwl (M.V_le_conjU hl hV)
  have hyL : y ∈ M.L := M.Q_le_L hyQ
  have hl'L : l⁻¹ * y * l ∈ M.L := mul_mem (mul_mem (inv_mem hl) hyL) hl
  have hne' : M.conjU (l⁻¹ * y * l) ≠ ruU M.L M.T := by
    intro he
    have hLT := (M.conjU_eq_U_iff hl'L).mp he
    have hH : l⁻¹ * y * l ∈ ruH M.T := M.LT1_le_H hLT
    have hzc := M.mem_H_iff_comm.mp hH
    apply hyc
    calc y * (l * M.z * l⁻¹) = l * ((l⁻¹ * y * l) * M.z) * l⁻¹ := by group
      _ = l * (M.z * (l⁻¹ * y * l)) * l⁻¹ := by rw [hzc]
      _ = (l * M.z * l⁻¹) * y := by group
  have hxU : l⁻¹ * x * l ∈ ruU M.L M.T := M.mem_conjU.mp hxl
  have hxU' : l⁻¹ * x * l ∈ M.conjU (l⁻¹ * y * l) := by
    rw [M.mem_conjU]
    have e : (l⁻¹ * y * l)⁻¹ * (l⁻¹ * x * l) * (l⁻¹ * y * l) = l⁻¹ * w * l := by
      rw [hx]
      group
    rw [e]
    exact M.mem_conjU.mp hwl
  have hxV : l⁻¹ * x * l ∈ ruV M.L := by
    have := M.U_inf_conjU hl'L hne'
    rw [← this]
    exact Subgroup.mem_inf.mpr ⟨hxU, hxU'⟩
  have hxV' : x ∈ ruV M.L := by
    have := M.toRuData.conj_mem_V hl hxV
    simpa [mul_assoc] using this
  have hxC : x ∈ M.HC := M.U_le_HC (M.V_le_U hxV')
  apply hwC
  have e : w = x * (w⁻¹ * x)⁻¹ := by group
  rw [e]
  exact mul_mem hxC (inv_mem hΘC)

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_KC {G : Type} [Group G] [Finite G] (M : RuDataM G) {l w : G}
    (hl : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) (hwl : w ∈ M.conjU l)
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) (hw2 : w ^ 2 = 1) :
    ∀ c ∈ ruU M.L M.T, w * c = c * w → ∃ y ∈ ruQ M.T, y * w * y⁻¹ = w * c := by
  intro c hcU hcw
  set A : Subgroup G := ruU M.L M.T ⊓ Subgroup.centralizer ({w} : Set G) with hA
  have memA : ∀ x : G, x ∈ A ↔ x ∈ ruU M.L M.T ∧ w * x = x * w := by
    intro x
    rw [hA, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
  have hAcard : Nat.card A = 16 := burnsideJ28_card_centralizer_U M hwQ hwC
  have hΘA : ∀ y ∈ ruQ M.T, w⁻¹ * (y * w * y⁻¹) ∈ A := fun y hy =>
    (memA _).mpr (burnsideJ28_theta_mem M hwQ hw2 hwC hy)
  let Θ : M.HC →* G :=
    { toFun := fun h => w⁻¹ * ((h : G) * w * (h : G)⁻¹)
      map_one' := by simp
      map_mul' := fun h1 h2 => by
        have := burnsideJ28_theta_mul M hwQ hw2 hwC h1.2 (M.HC_le_Q h2.2)
        simp only [Subgroup.coe_mul]
        exact this }
  have hΘker : ∀ h : M.HC, Θ h = 1 ↔ (h : G) ∈ A := by
    intro h
    show w⁻¹ * ((h : G) * w * (h : G)⁻¹) = 1 ↔ _
    rw [memA]
    constructor
    · intro h1
      have hw' : w = (h : G) * w * (h : G)⁻¹ := inv_mul_eq_one.mp h1
      have hcomm : w * (h : G) = (h : G) * w := by
        calc w * (h : G) = ((h : G) * w * (h : G)⁻¹) * (h : G) := by rw [← hw']
          _ = (h : G) * w := by group
      have hU : (h : G) ∈ ruU M.L M.T := by
        by_contra hU
        refine hwC (burnsideJ28_mem_HC_of_comm_Z M h.2 hU hwQ ?_)
        have : (h : G) * w * (h : G)⁻¹ * w⁻¹ = 1 := by
          rw [← hw']
          group
        rw [this]
        exact one_mem _
      exact ⟨hU, hcomm⟩
    · rintro ⟨hU, hcomm⟩
      have : (h : G) * w * (h : G)⁻¹ = w := by
        calc (h : G) * w * (h : G)⁻¹ = (w * (h : G)) * (h : G)⁻¹ := by rw [← hcomm]
          _ = w := by group
      rw [this]
      group
  have hkerA : Nat.card Θ.ker = 16 := by
    rw [← hAcard]
    refine Nat.card_congr
      { toFun := fun h => ⟨(h.1 : G), (hΘker h.1).mp h.2⟩
        invFun := fun a => ⟨⟨a.1, M.U_le_HC ((memA a.1).mp a.2).1⟩, (hΘker _).mpr a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card Θ.range = 8 := by
    have h := Subgroup.card_ker_mul_card_range Θ
    rw [hkerA, M.card_HC] at h
    omega
  have hW0A : Θ.range ≤ A := by
    rintro _ ⟨h, rfl⟩
    exact hΘA _ (M.HC_le_Q h.2)
  have hwS : w ∈ ruS M.L := M.conjU_le_S hl hwl
  have hW0V : Θ.range ≤ ruV M.L := by
    rintro _ ⟨h, rfl⟩
    have hS : (h : G) ∈ ruS M.L := M.HC_le_S h.2
    have := M.comm_mem_V (inv_mem hwS) hS
    show w⁻¹ * ((h : G) * w * (h : G)⁻¹) ∈ ruV M.L
    simpa [mul_assoc] using this
  have hrel : Θ.range.relIndex A = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Θ.range) (K := A)
    rw [inf_eq_left.mpr hW0A, hrange, hAcard] at h
    omega
  obtain ⟨a, haA, hXor⟩ := Subgroup.relIndex_eq_two_iff.mp hrel
  obtain ⟨y0, hy0Q, hy0V⟩ := burnsideJ28_exists_y0 M hl hne hwl hwQ hwC hw2
  have ht0A : w⁻¹ * (y0 * w * y0⁻¹) ∈ A := hΘA y0 hy0Q
  have ht0 : w⁻¹ * (y0 * w * y0⁻¹) ∉ Θ.range := fun h => hy0V (hW0V h)
  have hcA : c ∈ A := (memA c).mpr ⟨hcU, hcw⟩
  by_cases hcW : c ∈ Θ.range
  · obtain ⟨h, hh⟩ := hcW
    refine ⟨(h : G), M.HC_le_Q h.2, ?_⟩
    have h1 : w⁻¹ * ((h : G) * w * (h : G)⁻¹) = c := hh
    calc (h : G) * w * (h : G)⁻¹ = w * (w⁻¹ * ((h : G) * w * (h : G)⁻¹)) := by group
      _ = w * c := by rw [h1]
  · set t := w⁻¹ * (y0 * w * y0⁻¹) with ht
    have h1 : c * a ∈ Θ.range := by
      rcases hXor c hcA with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hcW
    have h2 : t * a ∈ Θ.range := by
      rcases hXor t ht0A with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h ht0
    have hmem : c * t⁻¹ ∈ Θ.range := by
      have e : c * t⁻¹ = (c * a) * (t * a)⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem h2)
    obtain ⟨h, hh⟩ := hmem
    have h3 : w⁻¹ * ((h : G) * w * (h : G)⁻¹) = c * t⁻¹ := hh
    refine ⟨(h : G) * y0, mul_mem (M.HC_le_Q h.2) hy0Q, ?_⟩
    have h4 := burnsideJ28_theta_mul M hwQ hw2 hwC h.2 hy0Q
    rw [h3] at h4
    calc (h : G) * y0 * w * ((h : G) * y0)⁻¹
        = w * (w⁻¹ * ((h : G) * y0 * w * ((h : G) * y0)⁻¹)) := by group
      _ = w * ((c * t⁻¹) * t) := by rw [h4]
      _ = w * c := by group

theorem burnsideJ28_conj_comm {G : Type} [Group G] {a c : G} (h : G) (hac : a * c = c * a) :
    (h * a * h⁻¹) * (h * c * h⁻¹) = (h * c * h⁻¹) * (h * a * h⁻¹) := by
  calc (h * a * h⁻¹) * (h * c * h⁻¹) = h * (a * c) * h⁻¹ := by group
    _ = h * (c * a) * h⁻¹ := by rw [hac]
    _ = (h * c * h⁻¹) * (h * a * h⁻¹) := by group

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_conj_w_gen {G : Type} [Group G] [Finite G] (M : RuDataM G) {l w : G}
    (hl : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) (hwl : w ∈ M.conjU l)
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) (hw2 : w ^ 2 = 1) {h x : G} (hh : h ∈ ruH M.T)
    (hxQ : x ∈ ruQ M.T) (hx2 : x ^ 2 = 1)
    (hψ : M.ψQ ⟨x, hxQ⟩ = M.ψQ ⟨h * w * h⁻¹, M.conj_mem_Q hh hwQ⟩) :
    ∃ y ∈ ruQ M.T, x = (h * y) * w * (h * y)⁻¹ := by
  obtain ⟨w', hw'⟩ : ∃ w' : G, w' = h * w * h⁻¹ := ⟨_, rfl⟩
  have hw'Q : w' ∈ ruQ M.T := by rw [hw']; exact M.conj_mem_Q hh hwQ
  have hw'2 : w' ^ 2 = 1 := by
    rw [hw', conj_pow, hw2]
    group
  have e1 : w = h⁻¹ * w' * h := by rw [hw']; group
  have hw'C : w' ∉ M.HC := by
    intro hC
    apply hwC
    have := M.conj_mem_HC (inv_mem hh) hC
    rw [e1]
    simpa [mul_assoc] using this
  have hψ' : M.ψQ ⟨x, hxQ⟩ = M.ψQ ⟨w', hw'Q⟩ := by
    have e : (⟨w', hw'Q⟩ : ruQ M.T) = ⟨h * w * h⁻¹, M.conj_mem_Q hh hwQ⟩ := Subtype.ext hw'
    rw [e]
    exact hψ
  have hcHC : w'⁻¹ * x ∈ M.HC := by
    have hk : (⟨w', hw'Q⟩ : ruQ M.T)⁻¹ * ⟨x, hxQ⟩ ∈ M.ψQ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψ', inv_mul_cancel]
    rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hxw' : (w' * (w'⁻¹ * x)) ^ 2 = 1 := by
    rw [mul_inv_cancel_left]
    exact hx2
  obtain ⟨hcU, hcomm⟩ := (burnsideJ28_inv_coset M hw'Q hw'2 hw'C hcHC).mp hxw'
  have hc''U : h⁻¹ * (w'⁻¹ * x) * h ∈ ruU M.L M.T := by
    have := M.conj_mem_U (inv_mem hh) hcU
    simpa using this
  have hc''comm : w * (h⁻¹ * (w'⁻¹ * x) * h) = (h⁻¹ * (w'⁻¹ * x) * h) * w := by
    have := burnsideJ28_conj_comm h⁻¹ hcomm
    rw [e1]
    simpa [mul_assoc] using this
  obtain ⟨y, hyQ, hy⟩ := burnsideJ28_KC M hl hne hwl hwQ hwC hw2 _ hc''U hc''comm
  refine ⟨y, hyQ, ?_⟩
  calc x = w' * (w'⁻¹ * x) := by group
    _ = h * (w * (h⁻¹ * (w'⁻¹ * x) * h)) * h⁻¹ := by rw [hw']; group
    _ = h * (y * w * y⁻¹) * h⁻¹ := by rw [hy]
    _ = (h * y) * w * (h * y)⁻¹ := by group

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_psi_ne_one {G : Type} [Group G] [Finite G] (M : RuDataM G) {x : G}
    (hxQ : x ∈ ruQ M.T) (hxU : x ∉ ruU M.L M.T) (hx2 : x ^ 2 = 1) : M.ψQ ⟨x, hxQ⟩ ≠ 1 := by
  intro h1
  apply hxU
  have hk : (⟨x, hxQ⟩ : ruQ M.T) ∈ M.ψQ.ker := h1
  rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at hk
  exact M.mem_U_of_HC_sq hk hx2

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_conj_w {G : Type} [Group G] [Finite G] (M : RuDataM G) {l w : G}
    (hl : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) (hwl : w ∈ M.conjU l)
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) (hw2 : w ^ 2 = 1) {x : G} (hxQ : x ∈ ruQ M.T)
    (hxU : x ∉ ruU M.L M.T) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ ruH M.T, x = g * w * g⁻¹ := by
  have hψx := burnsideJ28_psi_ne_one M hxQ hxU hx2
  have hwU : w ∉ ruU M.L M.T := fun h => hwC (M.U_le_HC h)
  have hψw := burnsideJ28_psi_ne_one M hwQ hwU hw2
  obtain ⟨g0, hg0⟩ := Sigma.exists_sigmaAct_eq
    (v := Multiplicative.toAdd (M.ψQ ⟨w, hwQ⟩)) (w := Multiplicative.toAdd (M.ψQ ⟨x, hxQ⟩))
    (fun h => hψw (Multiplicative.toAdd.injective (by rw [h, toAdd_one])))
    (fun h => hψx (Multiplicative.toAdd.injective (by rw [h, toAdd_one])))
  obtain ⟨h, rfl⟩ := M.φ_surj g0
  have hψ : M.ψQ ⟨x, hxQ⟩ = M.ψQ ⟨h * w * (h : G)⁻¹, M.conj_mem_Q h.2 hwQ⟩ := by
    apply Multiplicative.toAdd.injective
    rw [M.ψQ_conj h ⟨w, hwQ⟩]
    exact hg0.symm
  obtain ⟨y, hyQ, hxy⟩ := burnsideJ28_conj_w_gen M hl hne hwl hwQ hwC hw2 h.2 hxQ hx2 hψ
  exact ⟨(h : G) * y, mul_mem h.2 (pCoreOf_le 2 _ hyQ), hxy⟩

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_psi_eq_iff {G : Type} [Group G] [Finite G] (M : RuDataM G) {a b : G}
    (ha : a ∈ ruQ M.T) (hb : b ∈ ruQ M.T) :
    M.ψQ ⟨a, ha⟩ = M.ψQ ⟨b, hb⟩ ↔ a⁻¹ * b ∈ M.HC := by
  have e : M.ψQ ⟨a, ha⟩ = M.ψQ ⟨b, hb⟩ ↔ (⟨a, ha⟩ : ruQ M.T)⁻¹ * ⟨b, hb⟩ ∈ M.ψQ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  rw [e, M.ψQ_ker, Subgroup.mem_subgroupOf]
  rfl

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_card_fiber {G : Type} [Group G] [Finite G] (M : RuDataM G) {x : G}
    (hxQ : x ∈ ruQ M.T) (hxU : x ∉ ruU M.L M.T) (hx2 : x ^ 2 = 1) :
    Nat.card {y : G // y ∈ ruQ M.T ∧ y ∉ ruU M.L M.T ∧ y ^ 2 = 1 ∧ x⁻¹ * y ∈ M.HC} = 16 := by
  have hxC : x ∉ M.HC := fun h => hxU (M.mem_U_of_HC_sq h hx2)
  rw [← burnsideJ28_card_centralizer_U M hxQ hxC]
  have hfwd : ∀ y : {y : G // y ∈ ruQ M.T ∧ y ∉ ruU M.L M.T ∧ y ^ 2 = 1 ∧ x⁻¹ * y ∈ M.HC},
      x⁻¹ * y.1 ∈ ruU M.L M.T ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro y
    obtain ⟨hyQ, hyU, hy2, hyc⟩ := y.2
    have h1 : (x * (x⁻¹ * y.1)) ^ 2 = 1 := by
      rw [mul_inv_cancel_left]
      exact hy2
    obtain ⟨hcU, hcomm⟩ := (burnsideJ28_inv_coset M hxQ hx2 hxC hyc).mp h1
    exact Subgroup.mem_inf.mpr ⟨hcU, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  have hbwd : ∀ c : ↥(ruU M.L M.T ⊓ Subgroup.centralizer ({x} : Set G)),
      x * c.1 ∈ ruQ M.T ∧ x * c.1 ∉ ruU M.L M.T ∧ (x * c.1) ^ 2 = 1 ∧ x⁻¹ * (x * c.1) ∈ M.HC := by
    intro c
    obtain ⟨hcU, hcx⟩ := Subgroup.mem_inf.mp c.2
    have hcomm : x * c.1 = c.1 * x := (Subgroup.mem_centralizer_singleton_iff.mp hcx).symm
    refine ⟨mul_mem hxQ (M.U_le_Q hcU), fun h => hxU ?_, ?_, ?_⟩
    · have := mul_mem h (inv_mem hcU)
      simpa using this
    · exact (burnsideJ28_inv_coset M hxQ hx2 hxC (M.U_le_HC hcU)).mpr ⟨hcU, hcomm⟩
    · rw [inv_mul_cancel_left]
      exact M.U_le_HC hcU
  exact Nat.card_congr
    { toFun := fun y => ⟨x⁻¹ * y.1, hfwd y⟩
      invFun := fun c => ⟨x * c.1, hbwd c⟩
      left_inv := fun y => Subtype.ext (mul_inv_cancel_left x y.1)
      right_inv := fun c => Subtype.ext (inv_mul_cancel_left x c.1) }

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_card_I {G : Type} [Group G] [Finite G] (M : RuDataM G) {w : G}
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) (hw2 : w ^ 2 = 1) :
    Nat.card {x : G // x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1} = 240 := by
  classical
  let I := {x : G // x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1}
  let g : I → Multiplicative (Fin 2 → Quasithin.RuType.F4) := fun x => M.ψQ ⟨x.1, x.2.1⟩
  have hsum : Nat.card I = ∑ v : Multiplicative (Fin 2 → Quasithin.RuType.F4), Nat.card {x : I // g x = v} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  have hwU : w ∉ ruU M.L M.T := fun h => hwC (M.U_le_HC h)
  have hfib : ∀ v : Multiplicative (Fin 2 → Quasithin.RuType.F4),
      Nat.card {x : I // g x = v} = if v = 1 then 0 else 16 := by
    intro v
    by_cases hv : v = 1
    · rw [if_pos hv]
      have : IsEmpty {x : I // g x = v} := ⟨fun x => by
        have h1 : g x.1 ≠ 1 := burnsideJ28_psi_ne_one M x.1.2.1 x.1.2.2.1 x.1.2.2.2
        exact h1 (x.2.trans hv)⟩
      exact Nat.card_of_isEmpty
    · rw [if_neg hv]
      have hψw := burnsideJ28_psi_ne_one M hwQ hwU hw2
      obtain ⟨g0, hg0⟩ := Sigma.exists_sigmaAct_eq
        (v := Multiplicative.toAdd (M.ψQ ⟨w, hwQ⟩)) (w := Multiplicative.toAdd v)
        (fun h => hψw (Multiplicative.toAdd.injective (by rw [h, toAdd_one])))
        (fun h => hv (Multiplicative.toAdd.injective (by rw [h, toAdd_one])))
      obtain ⟨h, rfl⟩ := M.φ_surj g0
      have hwvQ : (h : G) * w * (h : G)⁻¹ ∈ ruQ M.T := M.conj_mem_Q h.2 hwQ
      have hψv : M.ψQ ⟨(h : G) * w * (h : G)⁻¹, hwvQ⟩ = v := by
        apply Multiplicative.toAdd.injective
        rw [M.ψQ_conj h ⟨w, hwQ⟩]
        exact hg0
      have hwv2 : ((h : G) * w * (h : G)⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hw2]
        group
      have hwvU : (h : G) * w * (h : G)⁻¹ ∉ ruU M.L M.T := by
        intro hU
        apply hwU
        have := M.conj_mem_U (inv_mem h.2) hU
        simpa [mul_assoc] using this
      rw [← burnsideJ28_card_fiber M hwvQ hwvU hwv2]
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, ?_⟩
          invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1⟩, ?_⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      · exact (burnsideJ28_psi_eq_iff M hwvQ x.1.2.1).mp (hψv.trans x.2.symm)
      · exact hψv.symm ▸ ((burnsideJ28_psi_eq_iff M hwvQ y.2.1).mpr y.2.2.2.2).symm
  rw [hsum, Finset.sum_congr rfl (fun v _ => hfib v)]
  decide +kernel

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_centralizer_S_le_Q {G : Type} [Group G] [Finite G] (M : RuDataM G) {u : G}
    (hu : u ∈ ruU M.L M.T) (huV : u ∉ ruV M.L) :
    ruS M.L ⊓ Subgroup.centralizer ({u} : Set G) ≤ ruQ M.T := by
  have huS : u ∈ ruS M.L := M.U_le_S hu
  set P : Subgroup G := ruQ M.T ⊓ ruS M.L with hP
  let g : P →* ruZ M.T :=
    { toFun := fun p => ⟨p * u * p⁻¹ * u⁻¹, M.comm_mem_Z (Subgroup.mem_inf.mp p.2).1 hu⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p p' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact M.comm_mul_left (Subgroup.mem_inf.mp p.2).1 (Subgroup.mem_inf.mp p'.2).1 hu) }
  have key : ∀ p : P, p ∈ g.ker ↔ (p : G) * u = u * p := by
    intro p
    rw [MonoidHom.mem_ker]
    constructor
    · intro hp
      have h1 : (p : G) * u * (p : G)⁻¹ * u⁻¹ = 1 := congrArg Subtype.val hp
      calc (p : G) * u = ((p : G) * u * (p : G)⁻¹ * u⁻¹) * (u * p) := by group
        _ = u * p := by rw [h1, one_mul]
    · intro hp
      apply Subtype.ext
      show (p : G) * u * (p : G)⁻¹ * u⁻¹ = 1
      calc (p : G) * u * (p : G)⁻¹ * u⁻¹ = (u * p) * (p : G)⁻¹ * u⁻¹ := by rw [hp]
        _ = 1 := by group
  have hker : Nat.card g.ker = Nat.card ↥(P ⊓ Subgroup.centralizer ({u} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1, p.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
          ((key p.1).mp p.2)⟩
        invFun := fun p => ⟨⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩, (key _).mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp p.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card g.range ≤ 2 := by
    rw [← M.toRuData.card_Z]
    exact Subgroup.card_le_card_group _
  have h := Subgroup.card_ker_mul_card_range g
  have hPc : Nat.card ↥P = 2 ^ 9 := M.card_Q_inf_S
  rw [hPc] at h
  have hX : Nat.card ↥(ruS M.L ⊓ Subgroup.centralizer ({u} : Set G)) = 2 ^ 8 :=
    M.card_centralizer_S huS huV
  have hYX : P ⊓ Subgroup.centralizer ({u} : Set G) ≤
      ruS M.L ⊓ Subgroup.centralizer ({u} : Set G) :=
    inf_le_inf_right _ inf_le_right
  have hYcard : 2 ^ 8 ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [← hker]
    have hpos : 0 < Nat.card g.ker := Nat.card_pos
    nlinarith
  have heq := Subgroup.eq_of_le_of_card_ge hYX (by rw [hX]; exact hYcard)
  intro x hx
  have : x ∈ P ⊓ Subgroup.centralizer ({u} : Set G) := by rw [heq]; exact hx
  exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp this).1).1

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_sigma_orbit {g : SigmaL2F4} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {v : Fin 2 → Quasithin.RuType.F4} (hv : v ≠ 0) :
    sigmaAct g v ≠ v ∧ sigmaAct g (sigmaAct g v) ≠ v ∧
      sigmaAct g (sigmaAct g v) ≠ sigmaAct g v ∧ sigmaAct g v ≠ 0 ∧
      sigmaAct g (sigmaAct g v) ≠ 0 := by
  have inj0 : ∀ (x : SigmaL2F4) (w : Fin 2 → Quasithin.RuType.F4), sigmaAct x w = 0 → w = 0 := by
    intro x w h
    calc w = sigmaAct x⁻¹ (sigmaAct x w) := by
          rw [← Sigma.sigmaAct_mul, inv_mul_cancel, Sigma.sigmaAct_one]
      _ = 0 := by rw [h, Sigma.sigmaAct_zero]
  have h1 : sigmaAct g v ≠ v := fun h => hv (Sigma.fix_order_three g ⟨hg3, hg1⟩ v h)
  have hne0 : sigmaAct g v ≠ 0 := fun h => hv (inj0 g v h)
  refine ⟨h1, ?_, fun h => hne0 (Sigma.fix_order_three g ⟨hg3, hg1⟩ _ h), hne0,
    fun h => hne0 (inj0 g _ h)⟩
  have hg2 : (g * g) ^ 3 = 1 := by
    calc (g * g) ^ 3 = g ^ (2 * 3) := by rw [← pow_two, ← pow_mul]
      _ = (g ^ 3) ^ 2 := by rw [mul_comm, pow_mul]
      _ = 1 := by rw [hg3, one_pow]
  have hg2' : g * g ≠ 1 := by
    intro h
    apply hg1
    calc g = g * g * g := by rw [h, one_mul]
      _ = g ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := hg3
  intro h
  apply hv
  apply Sigma.fix_order_three (g * g) ⟨hg2, hg2'⟩ v
  rw [Sigma.sigmaAct_mul]
  exact h

theorem burnsideJ28_pigeon {X : Type*} [Group X] [Finite X] (Λ : Subgroup X)
    (hΛ : Nat.card Λ ≤ 4) {a b c u : X} (ha : a ∈ Λ) (hb : b ∈ Λ) (hc : c ∈ Λ) (hu : u ∈ Λ)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hu1 : u ≠ 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : u = a ∨ u = b ∨ u = c := by
  by_contra h
  push Not at h
  obtain ⟨hua, hub, huc⟩ := h
  have hle : 5 ≤ Nat.card Λ := by
    have n4 : c ∉ ({u} : Set X) := by
      simpa only [Set.mem_singleton_iff] using huc.symm
    have n3 : b ∉ ({c, u} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hbc, hub.symm⟩
    have n2 : a ∉ ({b, c, u} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, hac, hua.symm⟩
    have n1 : (1 : X) ∉ ({a, b, c, u} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hc1.symm, hu1.symm⟩
    have h5 : ({1, a, b, c, u} : Set X).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
        Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n4, Set.ncard_singleton]
    have hsub : ({1, a, b, c, u} : Set X) ⊆ (Λ : Set X) := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      exacts [one_mem _, ha, hb, hc, hu]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h5] at this
    exact this
  omega

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_card_range_le {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ∃ Λ : Subgroup (Multiplicative (Fin 2 → Quasithin.RuType.F4)), Nat.card Λ ≤ 4 ∧
      ∀ (q : G) (hq : q ∈ ruQ M.T), q ∈ ruS M.L → M.ψQ ⟨q, hq⟩ ∈ Λ := by
  let Pq : Subgroup (ruQ M.T) := (ruQ M.T ⊓ ruS M.L).subgroupOf (ruQ M.T)
  let f : Pq →* Multiplicative (Fin 2 → Quasithin.RuType.F4) := M.ψQ.comp Pq.subtype
  refine ⟨f.range, ?_, fun q hq hqS => ⟨⟨⟨q, hq⟩, Subgroup.mem_subgroupOf.mpr ⟨hq, hqS⟩⟩, rfl⟩⟩
  have hPq : Nat.card Pq = 2 ^ 9 := by
    show Nat.card ((ruQ M.T ⊓ ruS M.L).subgroupOf (ruQ M.T)) = 2 ^ 9
    rw [card_subgroupOf_of_le inf_le_left]
    exact M.card_Q_inf_S
  have hker : 2 ^ 7 ≤ Nat.card f.ker := by
    rw [← M.card_HC]
    refine Nat.card_le_card_of_injective (fun h => ⟨⟨⟨h.1, M.HC_le_Q h.2⟩,
      Subgroup.mem_subgroupOf.mpr ⟨M.HC_le_Q h.2, M.HC_le_S h.2⟩⟩, ?_⟩) ?_
    · have : (⟨h.1, M.HC_le_Q h.2⟩ : ruQ M.T) ∈ M.ψQ.ker := by
        rw [M.ψQ_ker, Subgroup.mem_subgroupOf]
        exact h.2
      exact this
    · intro a b hab
      exact Subtype.ext (congrArg (fun x => ((x.1 : Pq) : ruQ M.T).1) hab)
  have h := Subgroup.card_ker_mul_card_range f
  rw [hPq] at h
  by_contra hcon
  push Not at hcon
  have := Nat.mul_le_mul hker hcon
  omega

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_part2 {G : Type} [Group G] [Finite G] (M : RuDataM G) {l w : G}
    (hl : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) (hwl : w ∈ M.conjU l)
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) (hw2 : w ^ 2 = 1) {i : G}
    (hiS : i ∈ ruS M.L) (hiQ : i ∈ ruQ M.T) (hi2 : i ^ 2 = 1) :
    ∃ m ∈ M.L, m⁻¹ * i * m ∈ ruU M.L M.T := by
  by_cases hiU : i ∈ ruU M.L M.T
  · exact ⟨1, one_mem _, by simpa using hiU⟩
  obtain ⟨Λ, hΛ, hΛmem⟩ := burnsideJ28_card_range_le M
  have hbL : (M.bel : G) ∈ M.L := M.bel.2
  have hbH : (M.bel : G) ∈ ruH M.T := M.bel_mem_H
  have hwS : w ∈ ruS M.L := M.conjU_le_S hl hwl
  have hwU : w ∉ ruU M.L M.T := fun h => hwC (M.U_le_HC h)
  have hcb : ∀ x ∈ ruQ M.T, x ∈ ruS M.L →
      (M.bel : G) * x * (M.bel : G)⁻¹ ∈ ruQ M.T ∧ (M.bel : G) * x * (M.bel : G)⁻¹ ∈ ruS M.L :=
    fun x hxQ hxS => ⟨M.conj_mem_Q hbH hxQ,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hbL) x).mp hxS⟩
  obtain ⟨hw1Q, hw1S⟩ := hcb w hwQ hwS
  obtain ⟨hw2Q, hw2S⟩ := hcb _ hw1Q hw1S
  have e1 := M.ψQ_conj ⟨(M.bel : G), hbH⟩ ⟨w, hwQ⟩
  have e2 := M.ψQ_conj ⟨(M.bel : G), hbH⟩ ⟨_, hw1Q⟩
  have hv0 : Multiplicative.toAdd (M.ψQ ⟨w, hwQ⟩) ≠ 0 := fun h =>
    burnsideJ28_psi_ne_one M hwQ hwU hw2 (Multiplicative.toAdd.injective (by rw [h, toAdd_one]))
  obtain ⟨o1, o2, o3, o4, o5⟩ := burnsideJ28_sigma_orbit M.φ_bel.1 M.φ_bel.2 hv0
  have hne1 : ∀ x : Multiplicative (Fin 2 → Quasithin.RuType.F4), Multiplicative.toAdd x ≠ 0 → x ≠ 1 := by
    intro x hx h
    apply hx
    rw [h, toAdd_one]
  have t1 : Multiplicative.toAdd (M.ψQ ⟨(M.bel : G) * w * (M.bel : G)⁻¹, hw1Q⟩) =
      sigmaAct (M.φ ⟨(M.bel : G), hbH⟩) (Multiplicative.toAdd (M.ψQ ⟨w, hwQ⟩)) := e1
  have t2 : Multiplicative.toAdd (M.ψQ ⟨(M.bel : G) * ((M.bel : G) * w * (M.bel : G)⁻¹) *
      (M.bel : G)⁻¹, hw2Q⟩) = sigmaAct (M.φ ⟨(M.bel : G), hbH⟩)
        (sigmaAct (M.φ ⟨(M.bel : G), hbH⟩) (Multiplicative.toAdd (M.ψQ ⟨w, hwQ⟩))) := by
    rw [e2, t1]
  have hE0 : M.ψQ ⟨w, hwQ⟩ ≠ 1 := hne1 _ hv0
  have hE1 : M.ψQ ⟨(M.bel : G) * w * (M.bel : G)⁻¹, hw1Q⟩ ≠ 1 := hne1 _ (by rw [t1]; exact o4)
  have hE2 : M.ψQ ⟨(M.bel : G) * ((M.bel : G) * w * (M.bel : G)⁻¹) * (M.bel : G)⁻¹, hw2Q⟩ ≠ 1 :=
    hne1 _ (by rw [t2]; exact o5)
  have hE01 : M.ψQ ⟨w, hwQ⟩ ≠ M.ψQ ⟨(M.bel : G) * w * (M.bel : G)⁻¹, hw1Q⟩ := fun h =>
    o1 (by rw [← t1, ← h])
  have hE02 : M.ψQ ⟨w, hwQ⟩ ≠
      M.ψQ ⟨(M.bel : G) * ((M.bel : G) * w * (M.bel : G)⁻¹) * (M.bel : G)⁻¹, hw2Q⟩ := fun h =>
    o2 (by rw [← t2, ← h])
  have hE12 : M.ψQ ⟨(M.bel : G) * w * (M.bel : G)⁻¹, hw1Q⟩ ≠
      M.ψQ ⟨(M.bel : G) * ((M.bel : G) * w * (M.bel : G)⁻¹) * (M.bel : G)⁻¹, hw2Q⟩ := fun h => by
    have := congrArg Multiplicative.toAdd h
    rw [t1, t2] at this
    exact o3 this.symm
  have hu1 : M.ψQ ⟨i, hiQ⟩ ≠ 1 := burnsideJ28_psi_ne_one M hiQ hiU hi2
  have key : ∀ (h : G) (hh : h ∈ ruH M.T), h ∈ M.L →
      M.ψQ ⟨i, hiQ⟩ = M.ψQ ⟨h * w * h⁻¹, M.conj_mem_Q hh hwQ⟩ →
      ∃ m ∈ M.L, m⁻¹ * i * m ∈ ruU M.L M.T := by
    intro h hh hhL hψ
    obtain ⟨y, hyQ, hiy⟩ := burnsideJ28_conj_w_gen M hl hne hwl hwQ hwC hw2 hh hiQ hi2 hψ
    refine ⟨(h * y) * l, mul_mem (mul_mem hhL (M.Q_le_L hyQ)) hl, ?_⟩
    have : ((h * y) * l)⁻¹ * i * ((h * y) * l) = l⁻¹ * w * l := by
      rw [hiy]
      group
    rw [this]
    exact M.mem_conjU.mp hwl
  rcases burnsideJ28_pigeon Λ hΛ (hΛmem w hwQ hwS) (hΛmem _ hw1Q hw1S) (hΛmem _ hw2Q hw2S)
      (hΛmem i hiQ hiS) hE0 hE1 hE2 hu1 hE01 hE02 hE12 with h | h | h
  · refine key 1 (one_mem _) (one_mem _) ?_
    rw [h]
    congr 1
    exact Subtype.ext (by simp)
  · exact key (M.bel : G) hbH hbL h
  · refine key ((M.bel : G) * (M.bel : G)) (mul_mem hbH hbH) (mul_mem hbL hbL) ?_
    rw [h]
    congr 1
    exact Subtype.ext (by group)

theorem burnsideJ28_mem_conjClass_iff {G : Type} [Group G] (z x : G) :
    x ∈ CFSG.ASVolI.ChIJK.conjClass z ↔ IsConj z x := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem burnsideJ28_eq_z {G : Type} [Group G] [Finite G] (M : RuDataM G) {z : G}
    (hz : Subgroup.zpowers z = ruZ M.T) : z = M.z := by
  have hzmem : z ∈ ruZ M.T := by
    rw [← hz]
    exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have h2 := M.toRuData.card_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h2
    omega
  · exact h1

end BurnsideJ28Two8

end BurnsideJ28a

theorem as_J_2_8 : J_2_8 := by
  intro G _ _ L V T h z hz
  obtain ⟨M, hML, hMT, hV, hZ, hH, hQ, hU⟩ :=
    burnsideJ28_exists_M CFSG.Quasithin.RuType.stUnique h
  subst hML
  subst hMT
  subst hV
  have hzz : z = M.z := burnsideJ28_eq_z M (hz.trans hZ)
  subst hzz
  obtain ⟨l, hl, hne, w, hwl, hwQ, hwC, hw2⟩ := burnsideJ28_exists_w M
  rw [hH, hQ, hU]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro i ⟨hiQ, hi2, -⟩ hiU j ⟨hjQ, hj2, -⟩ hjU
    obtain ⟨gi, hgi, hi⟩ := burnsideJ28_conj_w M hl hne hwl hwQ hwC hw2 hiQ hiU hi2
    obtain ⟨gj, hgj, hj⟩ := burnsideJ28_conj_w M hl hne hwl hwQ hwC hw2 hjQ hjU hj2
    refine ⟨gi * gj⁻¹, mul_mem hgi (inv_mem hgj), ?_⟩
    rw [hi, hj]
    group
  · have hset : CFSG.ASVolI.ChIJK.involutionsOf (CFSG.Quasithin.RuType.ruQ M.T) \
        (CFSG.Quasithin.RuType.ruU M.L M.T : Set G) =
        {x | x ∈ CFSG.Quasithin.RuType.ruQ M.T ∧ x ∉ CFSG.Quasithin.RuType.ruU M.L M.T ∧
          x ^ 2 = 1} := by
      ext x
      constructor
      · rintro ⟨⟨hxQ, hx2, -⟩, hxU⟩
        exact ⟨hxQ, hxU, hx2⟩
      · rintro ⟨hxQ, hxU, hx2⟩
        refine ⟨⟨hxQ, hx2, ?_⟩, hxU⟩
        rintro rfl
        exact hxU (one_mem _)
    rw [hset, ← Nat.card_coe_set_eq]
    exact burnsideJ28_card_I M hwQ hwC hw2
  · rintro i ⟨hiQ, hi2, hi1⟩ -
    exact (burnsideJ28_mem_conjClass_iff _ _).mpr (M.lemma_J26.2.2.2.2.1 i hiQ hi2 hi1)
  · rintro i ⟨hiSQ, hi2, -⟩
    obtain ⟨hiS, hiQ⟩ := Subgroup.mem_inf.mp hiSQ
    exact burnsideJ28_part2 M hl hne hwl hwQ hwC hw2 hiS hiQ hi2
  · rintro u hu huV i ⟨hiSC, hi2, hi1⟩
    have hiQ := burnsideJ28_centralizer_S_le_Q M hu huV hiSC
    exact (burnsideJ28_mem_conjClass_iff _ _).mpr (M.lemma_J26.2.2.2.2.1 i hiQ hi2 hi1)

@[expose] def J_2_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
        (IsDirectProductOf (S0Ru L B7) (LsRu s) (Subgroup.centralizer ({s} : Set G)) ∧
          SuzukiModel ↥(LsRu s) 2 3) ∧
        (Subgroup.normalizer ((S0Ru L B7 : Subgroup G) : Set G) =
            Subgroup.centralizer ({s} : Set G) ⊔ B ∧
          InducesOuterAutomorphisms B (LsRu s)) ∧
        conjClass z ∩ (Subgroup.centralizer ({s} : Set G) : Set G) = involutionsOf (LsRu s)

section BurnsideJ4_2910

private theorem burnsideJ4_mem_conjugate {G : Type*} [Group G] {H : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate H g ↔ g * y * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_apply]

private theorem burnsideJ4_conjugate_conjugate {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate A g) h = CFSG.conjugate A (g * h) := by
  ext y
  rw [burnsideJ4_mem_conjugate, burnsideJ4_mem_conjugate, burnsideJ4_mem_conjugate]
  have : g * (h * y * h⁻¹) * g⁻¹ = (g * h) * y * (g * h)⁻¹ := by group
  rw [this]

private theorem burnsideJ4_conjugate_one {G : Type*} [Group G] (A : Subgroup G) :
    CFSG.conjugate A 1 = A := by
  ext y
  rw [burnsideJ4_mem_conjugate]
  simp

private theorem burnsideJ4_conjugate_conjugate_inv {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate A g) g⁻¹ = A := by
  rw [burnsideJ4_conjugate_conjugate, mul_inv_cancel, burnsideJ4_conjugate_one]

private theorem burnsideJ4_card_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate A g) = Nat.card A := by
  unfold CFSG.conjugate
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem burnsideJ4_conjugate_le {G : Type*} [Group G] {A N : Subgroup G} {g : G} (hA :
    A ≤ N)
    (hg : g ∈ N) : CFSG.conjugate A g ≤ N := by
  intro y hy
  rw [burnsideJ4_mem_conjugate] at hy
  have h1 := N.mul_mem (N.mul_mem (N.inv_mem hg) (hA hy)) hg
  simpa [mul_assoc] using h1

private theorem burnsideJ4_normalizer_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (Subgroup.normalizer (A : Set G)) g := by
  ext y
  rw [burnsideJ4_mem_conjugate, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have := h (g⁻¹ * a * g)
    rw [burnsideJ4_mem_conjugate, burnsideJ4_mem_conjugate] at this
    have e : g * (y * (g⁻¹ * a * g) * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ := by group
    simpa [e, mul_assoc] using this
  · intro h a
    rw [burnsideJ4_mem_conjugate, burnsideJ4_mem_conjugate]
    have := h (g * a * g⁻¹)
    have e : g * (y * a * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact this

private theorem burnsideJ4_centralizer_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.centralizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (Subgroup.centralizer (A : Set G)) g := by
  ext y
  rw [burnsideJ4_mem_conjugate, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (g⁻¹ * a * g) (by
      rw [SetLike.mem_coe, burnsideJ4_mem_conjugate]
      have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [e]; exact ha)
    have e : g * (g⁻¹ * a * g * y) * g⁻¹ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    calc a * (g * y * g⁻¹) = g * (g⁻¹ * a * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := e
      _ = g * y * g⁻¹ * a := by group
  · intro h a ha
    rw [SetLike.mem_coe, burnsideJ4_mem_conjugate] at ha
    have h1 := h (g * a * g⁻¹) ha
    calc a * y = g⁻¹ * (g * a * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * a * g⁻¹)) * g := by rw [h1]
      _ = y * a := by group

private theorem burnsideJ4_exists_conj_of_card {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact
    p.Prime]
    (hK : ¬ p ^ 2 ∣ Nat.card K) {A A' : Subgroup K} (hA : Nat.card A = p)
    (hA' : Nat.card A' = p) : ∃ g : K, A' = CFSG.conjugate A g⁻¹ := by
  have key : ∀ {C : Subgroup K}, Nat.card C = p → ∃ P : Sylow p K, (P : Subgroup K) = C := by
    intro C hC
    have hp : IsPGroup p C := IsPGroup.of_card (n := 1) (by simpa using hC)
    have hidx : ¬ p ∣ C.index := by
      intro hd
      apply hK
      rw [← Subgroup.card_mul_index C, hC, pow_two]
      exact Nat.mul_dvd_mul_left p hd
    exact ⟨hp.toSylow hidx, rfl⟩
  obtain ⟨P, hP⟩ := key hA
  obtain ⟨P', hP'⟩ := key hA'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P P'
  refine ⟨g, ?_⟩
  rw [← hP', ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, ← hP]
  unfold CFSG.conjugate
  simp only [inv_inv]
  rfl

private theorem burnsideJ4_conj_in_subgroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N B B' : Subgroup G} (hN : ¬ p ^ 2 ∣ Nat.card N) (hB : Nat.card B = p)
    (hB' : Nat.card B' = p) (hBN : B ≤ N) (hBN' : B' ≤ N) :
    ∃ n ∈ N, B' = CFSG.conjugate B n⁻¹ := by
  have e1 : Nat.card (B.subgroupOf N) = p := by
    rw [← hB]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have e2 : Nat.card (B'.subgroupOf N) = p := by
    rw [← hB']; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN').toEquiv
  obtain ⟨n, hn⟩ := burnsideJ4_exists_conj_of_card hN e1 e2
  refine ⟨(n : G), n.2, ?_⟩
  ext y
  rw [burnsideJ4_mem_conjugate]
  constructor
  · intro hy
    have hyN : y ∈ N := hBN' hy
    have h1 : (⟨y, hyN⟩ : N) ∈ B'.subgroupOf N := hy
    rw [hn, burnsideJ4_mem_conjugate, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · intro hy
    have hyN : y ∈ N := by
      have : (n : G)⁻¹ * y * ((n : G)⁻¹)⁻¹ ∈ B := hy
      have hb : (n : G)⁻¹ * y * ((n : G)⁻¹)⁻¹ ∈ N := hBN this
      have := N.mul_mem (N.mul_mem n.2 hb) (N.inv_mem n.2)
      simpa [mul_assoc] using this
    have h1 : (⟨y, hyN⟩ : N) ∈ CFSG.conjugate (B.subgroupOf N) n⁻¹ := by
      rw [burnsideJ4_mem_conjugate]
      exact hy
    rw [← hn] at h1
    exact h1

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_L1_eq {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) :
    L1Ru L T = CFSG.GorensteinWalter.pResidualOf M.LT1 2 := by
  have hZ : ZRu T = CFSG.Quasithin.RuType.ruZ M.T := by
    rw [hMT]; exact h.ZRu_eq_ruZ
  have h1 : Subgroup.centralizer (ZRu T : Set G) ⊓ L = M.LT1 := by
    rw [hZ, ← hML, inf_comm]
    exact M.L_inf_H
  unfold L1Ru
  rw [h1]
  rfl

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_L1_le {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) : L1Ru L T ≤ L := by
  rw [burnsideJ4_L1_eq h M hML hMT]
  exact (CFSG.GorensteinWalter.pResidualOf_le _ _).trans (hML ▸ M.LT1_le_L)

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_B_le_L1 {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) : M.B ≤ L1Ru L T := by
  rw [burnsideJ4_L1_eq h M hML hMT, Subgroup.zpowers_le]
  refine CFSG.GorensteinWalter.mem_pResidualOf_of_order_coprime _ 2 Nat.prime_two ?_ ?_
  · have : (M.bel : G) ∈ M.L ⊓ CFSG.Quasithin.RuType.ruH M.T := ⟨M.bel.2, M.bel_mem_H⟩
    rwa [M.L_inf_H] at this
  · rw [M.orderOf_bel]; norm_num

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_card_L1 {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) : 3 ∣ Nat.card (L1Ru L T) ∧ ¬ 9 ∣ Nat.card (L1Ru L T) := by
  constructor
  · have := Subgroup.card_dvd_of_le (burnsideJ4_B_le_L1 h M hML hMT)
    rwa [M.card_B] at this
  · intro hd
    have h1 : Nat.card (L1Ru L T) ∣ Nat.card M.LT1 :=
      Subgroup.card_dvd_of_le (by
        rw [burnsideJ4_L1_eq h M hML hMT]
        exact CFSG.GorensteinWalter.pResidualOf_le _ _)
    rw [M.card_LT1] at h1
    have := hd.trans h1
    norm_num at this

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_step_B {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) {B : Subgroup G} (hB : IsSylowIn 3 B (L1Ru L T)) :
    ∃ x ∈ L1Ru L T, B = CFSG.conjugate M.B x⁻¹ := by
  obtain ⟨hBle, hBp, hBidx⟩ := hB
  obtain ⟨h3, h9⟩ := burnsideJ4_card_L1 h M hML hMT
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcardB : Nat.card B = 3 := by
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    have hmul := Subgroup.card_mul_index (B.subgroupOf (L1Ru L T))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv, hk] at hmul
    rcases k with _ | _ | k
    · exact absurd (by rw [← hmul, pow_zero, one_mul] at h3; exact h3) hBidx
    · simpa using hk
    · exact absurd (by rw [← hmul]; exact Dvd.dvd.mul_right ⟨3 ^ k, by ring⟩ _) h9
  exact burnsideJ4_conj_in_subgroup (p := 3) (N := L1Ru L T) (B := M.B) (B' := B)
    (fun hd => h9 (by simpa using hd)) M.card_B hcardB (burnsideJ4_B_le_L1 h M hML hMT) hBle

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_reduce_aux {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hML : M.L = L)
    (hMT : M.T = h.sylowT) {B B7 : Subgroup G} (hB : IsSylowIn 3 B (L1Ru L T))
    (hB7L : B7 ≤ L) (hB7 : Nat.card B7 = 7) (hBN : B ≤ Subgroup.normalizer (B7 : Set G)) :
    ∃ x ∈ L, B = CFSG.conjugate M.B x⁻¹ ∧ B7 = CFSG.conjugate M.B7 x⁻¹ := by
  obtain ⟨x₁, hx₁X, hBx₁⟩ := burnsideJ4_step_B h M hML hMT hB
  have hXL := burnsideJ4_L1_le h M hML hMT
  have hx₁L : x₁ ∈ L := hXL hx₁X
  have hBL : B ≤ L := hB.1.trans hXL
  have hB3 : Nat.card B = 3 := by rw [hBx₁, burnsideJ4_card_conjugate, M.card_B]
  have hB7M : M.B7 ≤ L := hML ▸ (Subgroup.zpowers_le.mpr M.cel.2)
  have hBM : M.B ≤ Subgroup.normalizer (M.B7 : Set G) := by
    rw [Subgroup.zpowers_le]
    exact CFSG.Quasithin.RuType.mem_normalizer_of_conj_mem fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact M.bel_conj_cel k
  set C := CFSG.conjugate M.B7 x₁⁻¹ with hC
  have hCL : C ≤ L := burnsideJ4_conjugate_le hB7M (L.inv_mem hx₁L)
  have hCc : Nat.card C = 7 := by rw [hC, burnsideJ4_card_conjugate, M.card_B7]
  have hBC : B ≤ Subgroup.normalizer (C : Set G) := by
    rw [hC, burnsideJ4_normalizer_conjugate, hBx₁]
    exact Subgroup.map_mono hBM
  have hL49 : ¬ 7 ^ 2 ∣ Nat.card L := by
    rw [← hML, M.card_L]; norm_num
  have hL9 : ∀ N : Subgroup G, N ≤ L → ¬ 3 ^ 2 ∣ Nat.card N := fun N hN hd => by
    have := hd.trans (Subgroup.card_dvd_of_le hN)
    rw [← hML, M.card_L] at this
    norm_num at this
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, hgL, hg⟩ := burnsideJ4_conj_in_subgroup (p := 7) (N := L) (B := C) (B' := B7)
    hL49 hCc hB7 hCL hB7L
  have hB2 : CFSG.conjugate B g⁻¹ ≤ Subgroup.normalizer (B7 : Set G) := by
    rw [hg, burnsideJ4_normalizer_conjugate]
    exact Subgroup.map_mono hBC
  have hB2L : CFSG.conjugate B g⁻¹ ≤ L := burnsideJ4_conjugate_le hBL (L.inv_mem hgL)
  have hNL : Subgroup.normalizer (B7 : Set G) ⊓ L ≤ L := inf_le_right
  obtain ⟨n, hn, hBn⟩ := burnsideJ4_conj_in_subgroup (p := 3)
    (N := Subgroup.normalizer (B7 : Set G) ⊓ L) (B := B) (B' := CFSG.conjugate B g⁻¹)
    (hL9 _ hNL) hB3 (by rw [burnsideJ4_card_conjugate, hB3]) (le_inf hBN hBL) (le_inf hB2 hB2L)
  have hnN : n ∈ Subgroup.normalizer (B7 : Set G) := hn.1
  have hnL : n ∈ L := hn.2
  refine ⟨n⁻¹ * g * x₁, ?_, ?_, ?_⟩
  · exact L.mul_mem (L.mul_mem (L.inv_mem hnL) hgL) hx₁L
  · have e : (n⁻¹ * g * x₁)⁻¹ = x₁⁻¹ * (g⁻¹ * n) := by group
    rw [e, ← burnsideJ4_conjugate_conjugate, ← hBx₁, ← burnsideJ4_conjugate_conjugate, hBn,
      burnsideJ4_conjugate_conjugate, inv_mul_cancel, burnsideJ4_conjugate_one]
  · have e : (n⁻¹ * g * x₁)⁻¹ = x₁⁻¹ * (g⁻¹ * n) := by group
    rw [e, ← burnsideJ4_conjugate_conjugate, ← hC, ← burnsideJ4_conjugate_conjugate, ← hg]
    ext y
    rw [burnsideJ4_mem_conjugate]
    exact Subgroup.mem_normalizer_iff.mp hnN y

private theorem burnsideJ4_conjugate_inf {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊓ B) g = CFSG.conjugate A g ⊓ CFSG.conjugate B g := by
  ext y
  simp only [burnsideJ4_mem_conjugate, Subgroup.mem_inf]

private theorem burnsideJ4_conjugate_sup {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

private theorem burnsideJ4_conjugate_bot {G : Type*} [Group G] (g : G) :
    CFSG.conjugate (⊥ : Subgroup G) g = ⊥ := by
  unfold CFSG.conjugate
  exact Subgroup.map_bot _

private theorem burnsideJ4_cen_conjugate {G : Type*} [Group G] (s g : G) :
    Subgroup.centralizer ({g⁻¹ * s * g} : Set G) =
      CFSG.conjugate (Subgroup.centralizer ({s} : Set G)) g := by
  ext y
  rw [burnsideJ4_mem_conjugate, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * y * g⁻¹ * s = g * (y * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * y) * g⁻¹ := by rw [h]
      _ = s * (g * y * g⁻¹) := by group
  · intro h
    calc y * (g⁻¹ * s * g) = g⁻¹ * ((g * y * g⁻¹) * s) * g := by group
      _ = g⁻¹ * (s * (g * y * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * s * g) * y := by group

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_LsRu_conjugate {G : Type} [Group G] [Finite G] (s g : G) :
    LsRu (g⁻¹ * s * g) = CFSG.conjugate (LsRu s) g := by
  have e : ∀ t : G, LsRu t = Subgroup.closure
      {x | x ∈ CFSG.Quasithin.RuType.Cen t ∧ Odd (orderOf x)} := fun t =>
    CFSG.Quasithin.RuType.RuDataM.Ls_eq_closure t
  rw [e, e]
  unfold CFSG.conjugate
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  have hcen : ∀ y : G, y ∈ CFSG.Quasithin.RuType.Cen (g⁻¹ * s * g) ↔
      g * y * g⁻¹ ∈ CFSG.Quasithin.RuType.Cen s := fun y => by
    have := burnsideJ4_cen_conjugate s g
    have h2 : y ∈ Subgroup.centralizer ({g⁻¹ * s * g} : Set G) ↔
        y ∈ CFSG.conjugate (Subgroup.centralizer ({s} : Set G)) g := by rw [this]
    rw [burnsideJ4_mem_conjugate] at h2
    exact h2
  constructor
  · rintro ⟨hy, hodd⟩
    refine ⟨g * y * g⁻¹, ⟨(hcen y).mp hy, ?_⟩, ?_⟩
    · rwa [CFSG.Quasithin.RuType.orderOf_conj_eq]
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hcen]
      have e2 : g * ((MulAut.conj g⁻¹).toMonoidHom x) * g⁻¹ = x := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e2]; exact hx
    · have e2 : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g⁻¹⁻¹ := by
        simp [MulAut.conj_apply]
      rw [e2, CFSG.Quasithin.RuType.orderOf_conj_eq]; exact hodd

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_S0_conjugate {G : Type} [Group G] {L B7 : Subgroup G} {g : G} (hg :
    g ∈ L) :
    S0Ru L (CFSG.conjugate B7 g) = CFSG.conjugate (S0Ru L B7) g := by
  unfold S0Ru SRu
  have hS : CFSG.conjugate (pCoreOf 2 L) g = pCoreOf 2 L := by
    ext y
    rw [burnsideJ4_mem_conjugate]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hg) y).symm
  rw [burnsideJ4_conjugate_inf, hS, burnsideJ4_centralizer_conjugate]

open CFSG.ASVolI.ChIJK CFSG.Blueprint in
private theorem burnsideJ4_J29_core
    {G : Type} [Group G] [Finite G] (M : CFSG.Quasithin.RuType.RuDataM G) {s : G}
    (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    (IsDirectProductOf M.S0 (LsRu s) (Subgroup.centralizer ({s} : Set G)) ∧
        SuzukiModel ↥(LsRu s) 2 3) ∧
      (Subgroup.normalizer (M.S0 : Set G) = Subgroup.centralizer ({s} : Set G) ⊔ M.B ∧
        InducesOuterAutomorphisms M.B (LsRu s)) ∧
      conjClass M.z ∩ (Subgroup.centralizer ({s} : Set G) : Set G) = involutionsOf (LsRu s) := by
  obtain ⟨⟨⟨φ⟩, hinf, hsup, hcomm⟩, ⟨hnorm, hBLs, hout⟩, hconj⟩ := M.lemma_J29 hs hs1
  obtain ⟨E⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup 1
  have hCen : Subgroup.centralizer ({s} : Set G) = M.S0 ⊔ CFSG.Quasithin.RuType.Ls s :=
    hsup.symm
  refine ⟨⟨⟨hcomm, hinf, hsup⟩, rfl, 1, le_rfl, GaloisField 2 3, inferInstance, inferInstance,
    rfl, GaloisField.card 2 3 (by norm_num), ⟨φ.trans E⟩⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply le_antisymm
    · intro y hy
      have hyS : ∀ x ∈ M.S0, y * x * y⁻¹ ∈ M.S0 := fun x hx =>
        (Subgroup.mem_normalizer_iff.mp hy x).mp hx
      obtain ⟨c, hc, b, hb, rfl⟩ := hnorm y hyS
      exact Subgroup.mul_mem_sup hc hb
    · refine sup_le ?_ ?_
      · rw [hCen]
        refine le_trans (sup_le ?_ ?_) (Subgroup.centralizer_le_normalizer (M.S0 : Set G))
        · intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact (congrArg Subtype.val (M.S0_elem.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩))
        · intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact hcomm a ha y hy
      · rw [Subgroup.zpowers_le]
        exact CFSG.Quasithin.RuType.mem_normalizer_of_conj_mem fun x hx => M.bel_conj_S0 hx
  · rw [Subgroup.zpowers_le]
    exact CFSG.Quasithin.RuType.mem_normalizer_of_conj_mem fun x hx =>
      hBLs _ (Subgroup.mem_zpowers _) x hx
  · intro b hb hb1 l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have h3 : (M.bel : G) ^ 3 = 1 := M.bel_pow_three
    have e : (M.bel : G) ^ k = (M.bel : G) ^ (k % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact zpow_eq_zpow_emod' k h3
    have hcases : (k % 3).toNat = 0 ∨ (k % 3).toNat = 1 ∨ (k % 3).toNat = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exact absurd (by rw [e, h0, pow_zero]) hb1
    · rw [e, h1, pow_one]
      by_contra hno
      push Not at hno
      obtain ⟨x, hx, hne⟩ := hout l hl
      apply hne
      have hy := hno ((M.bel : G) * x * (M.bel : G)⁻¹) (hBLs _ (Subgroup.mem_zpowers _) x hx)
      have e2 : (M.bel : G)⁻¹ * ((M.bel : G) * x * (M.bel : G)⁻¹) * M.bel = x := by group
      rw [e2] at hy
      calc (M.bel : G) * x * (M.bel : G)⁻¹ = l * (l⁻¹ * ((M.bel : G) * x * (M.bel : G)⁻¹) * l) * l⁻¹ := by
            group
        _ = l * x * l⁻¹ := by rw [← hy]
    · have e3 : (M.bel : G) ^ 2 = (M.bel : G)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3]
      rw [e, h2, e3]
      obtain ⟨x, hx, hne⟩ := hout l⁻¹ (inv_mem hl)
      exact ⟨x, hx, by simpa using hne⟩
  · ext y
    constructor
    · rintro ⟨⟨c, hyc⟩, hy⟩
      have hzy : IsConj M.z y := isConj_iff.mpr ⟨c⁻¹, by rw [hyc]; group⟩
      exact (hconj y hy).mp hzy
    · rintro ⟨hyL, hy2, hy1⟩
      have hyC : y ∈ CFSG.Quasithin.RuType.Cen s := CFSG.Quasithin.RuType.Ls_le_Cen s hyL
      obtain ⟨c, hc⟩ := isConj_iff.mp ((hconj y hyC).mpr ⟨hyL, hy2, hy1⟩)
      exact ⟨⟨c⁻¹, by rw [← hc]; group⟩, hyC⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_reduce (hSt : CFSG.Quasithin.RuType.StUniqueStatement) {G : Type}
    [Group G]
    [Finite G] {L V T : Subgroup G} (h : RuType G L V T) {B B7 : Subgroup G}
    (hB : IsSylowIn 3 B (L1Ru L T)) (hB7L : B7 ≤ L) (hB7 : Nat.card B7 = 7)
    (hBN : B ≤ Subgroup.normalizer (B7 : Set G)) :
    ∃ (M : CFSG.Quasithin.RuType.RuDataM G) (g : G), M.L = L ∧ M.T = h.sylowT ∧ g ∈ L ∧
      B = CFSG.conjugate M.B g ∧ B7 = CFSG.conjugate M.B7 g := by
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM hSt
  obtain ⟨x, hxL, hBx, hB7x⟩ := burnsideJ4_reduce_aux h M hML hMT hB hB7L hB7 hBN
  exact ⟨M, x⁻¹, hML, hMT, L.inv_mem hxL, hBx, hB7x⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_z_eq {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : RuType G L V T) (M : CFSG.Quasithin.RuType.RuDataM G) (hMT : M.T = h.sylowT) {z : G}
    (hz : Subgroup.zpowers z = ZRu T) : z = M.z := by
  have hZ : ZRu T = CFSG.Quasithin.RuType.ruZ M.T := by
    rw [hMT]; exact h.ZRu_eq_ruZ
  have hzmem : z ∈ CFSG.Quasithin.RuType.ruZ M.T := by
    rw [← hZ, ← hz]; exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have hmz : M.z ∈ ZRu T := by rw [hZ]; exact M.z_mem_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmz
    exact M.z_ne_one hmz
  · exact h1

private theorem burnsideJ4_conjClass_conj {G : Type} [Group G] (z g y : G) :
    g * y * g⁻¹ ∈ CFSG.ASVolI.ChIJK.conjClass z ↔ y ∈ CFSG.ASVolI.ChIJK.conjClass z := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c * g, by
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * (c⁻¹ * z * c) * g := by rw [hc]
        _ = (c * g)⁻¹ * z * (c * g) := by group⟩
  · rintro ⟨c, hc⟩
    exact ⟨c * g⁻¹, by rw [hc]; group⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_isDirectProduct_conjugate {G : Type} [Group G] {A B X : Subgroup G}
    (g : G)
    (h : IsDirectProductOf A B X) :
    IsDirectProductOf (CFSG.conjugate A g) (CFSG.conjugate B g) (CFSG.conjugate X g) := by
  refine ⟨fun a ha b hb => ?_, ?_, ?_⟩
  · rw [burnsideJ4_mem_conjugate] at ha hb
    have h1 := h.1 _ ha _ hb
    have e1 : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    have e2 : g * b * g⁻¹ * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
    rw [e1, e2] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · rw [← burnsideJ4_conjugate_inf, h.2.1, burnsideJ4_conjugate_bot]
  · rw [← burnsideJ4_conjugate_sup, h.2.2]

open CFSG.Blueprint in
private theorem burnsideJ4_suzukiModel_conjugate {G : Type} [Group G] {B : Subgroup G} (g : G)
    {p f : ℕ}
    (h : SuzukiModel ↥B p f) : SuzukiModel ↥(CFSG.conjugate B g) p f := by
  obtain ⟨h2, a, ha, K, hK, hfin, hf, hcard, ⟨e⟩⟩ := h
  exact ⟨h2, a, ha, K, hK, hfin, hf, hcard, ⟨(Subgroup.equivMapOfInjective B
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm.trans e⟩⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_inducesOuter_conjugate {G : Type} [Group G] {X B : Subgroup G} (g : G)
    (h : InducesOuterAutomorphisms X B) :
    InducesOuterAutomorphisms (CFSG.conjugate X g) (CFSG.conjugate B g) := by
  refine ⟨?_, fun b hb hb1 l hl => ?_⟩
  · rw [burnsideJ4_normalizer_conjugate]
    exact Subgroup.map_mono h.1
  · rw [burnsideJ4_mem_conjugate] at hb hl
    have hb1' : g * b * g⁻¹ ≠ 1 := fun hc => hb1 (by
      have : b = g⁻¹ * (g * b * g⁻¹) * g := by group
      rw [this, hc]; group)
    obtain ⟨x, hx, hne⟩ := h.2 _ hb hb1' _ hl
    refine ⟨g⁻¹ * x * g, ?_, fun heq => hne ?_⟩
    · rw [burnsideJ4_mem_conjugate]
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [this]; exact hx
    · have e1 : (g * b * g⁻¹)⁻¹ * x * (g * b * g⁻¹) = g * (b⁻¹ * (g⁻¹ * x * g) * b) * g⁻¹ := by
        group
      have e2 : (g * l * g⁻¹)⁻¹ * x * (g * l * g⁻¹) = g * (l⁻¹ * (g⁻¹ * x * g) * l) * g⁻¹ := by
        group
      rw [e1, e2, heq]

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_conjClass_inter_conjugate {G : Type} [Group G] (z g : G) {X Y :
    Subgroup G}
    (h : conjClass z ∩ (X : Set G) = involutionsOf Y) :
    conjClass z ∩ ((CFSG.conjugate X g : Subgroup G) : Set G) =
      involutionsOf (CFSG.conjugate Y g) := by
  ext y
  have h1 := Set.ext_iff.mp h (g * y * g⁻¹)
  simp only [Set.mem_inter_iff, SetLike.mem_coe, involutionsOf, Set.mem_setOf_eq,
    burnsideJ4_conjClass_conj] at h1 ⊢
  rw [burnsideJ4_mem_conjugate, burnsideJ4_mem_conjugate]
  have hsq : (g * y * g⁻¹) ^ 2 = 1 ↔ y ^ 2 = 1 := by
    rw [conj_pow]
    simp [mul_inv_eq_one]
  have hne : g * y * g⁻¹ ≠ 1 ↔ y ≠ 1 := by simp [mul_inv_eq_one]
  rw [hsq, hne] at h1
  exact h1


open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_isSylowIn_conjugate {G : Type} [Group G] {p : ℕ} {B X : Subgroup G}
    (g : G)
    (h : IsSylowIn p B X) : IsSylowIn p (CFSG.conjugate B g) (CFSG.conjugate X g) := by
  obtain ⟨hle, hp, hidx⟩ := h
  refine ⟨Subgroup.map_mono hle, hp.of_equiv (Subgroup.equivMapOfInjective B
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective), ?_⟩
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) B X
    (MulAut.conj g⁻¹).injective
  unfold Subgroup.relIndex at this
  unfold CFSG.conjugate
  rwa [this]

private theorem burnsideJ4_aut_part {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hY : Nat.card Y = p)
    (hcard : Nat.card (Subgroup.normalizer (Y : Set G)) =
      Nat.card (Subgroup.centralizer (Y : Set G)) * (p - 1)) :
    ∃ (_ : ((Subgroup.centralizer (Y : Set G)).subgroupOf
          (Subgroup.normalizer (Y : Set G))).Normal),
      IsCyclic (↥(Subgroup.normalizer (Y : Set G)) ⧸
        (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G))) ∧
      Nat.card (↥(Subgroup.normalizer (Y : Set G)) ⧸
        (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G))) =
        p - 1 := by
  have hker : (CFSG.Quasithin.RuType.autNHom Y).ker =
      (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G)) := by
    ext g
    rw [CFSG.Quasithin.RuType.mem_ker_autNHom, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy; exact (h y hy).symm
    · intro h y hy; exact (h y hy).symm
  rw [← hker]
  refine ⟨inferInstance, ?_, ?_⟩
  · have := CFSG.Quasithin.RuType.RuDataM.isCyclic_autG_Y hp hY
    exact isCyclic_of_surjective
      (QuotientGroup.quotientKerEquivRange (CFSG.Quasithin.RuType.autNHom Y)).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange (CFSG.Quasithin.RuType.autNHom Y)).symm.surjective
  · rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (CFSG.Quasithin.RuType.autNHom Y)).toEquiv]
    have h1 := CFSG.Quasithin.RuType.card_normalizer_eq_mul Y
    rw [hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm

end BurnsideJ4_2910

section

open CFSG.ASVolI.ChIJK CFSG.Blueprint in
private theorem burnsideJ4_J_2_9_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) : J_2_9 := by
  intro G _ _ L V T h B B7 hB hB7L hB7 hBN z s hz hs hs1
  obtain ⟨M, g, hML, hMT, hgL, rfl, rfl⟩ := burnsideJ4_reduce hSt h hB hB7L hB7 hBN
  subst hML
  obtain rfl := burnsideJ4_z_eq h M hMT hz
  obtain ⟨s', rfl⟩ : ∃ s', s = g⁻¹ * s' * g := ⟨g * s * g⁻¹, by group⟩
  have hS0 : S0Ru M.L (CFSG.conjugate M.B7 g) = CFSG.conjugate M.S0 g :=
    burnsideJ4_S0_conjugate hgL
  have hs' : s' ∈ M.S0 := by
    rw [hS0, burnsideJ4_mem_conjugate] at hs
    have e : g * (g⁻¹ * s' * g) * g⁻¹ = s' := by group
    rw [e] at hs
    exact hs
  have hs1' : s' ≠ 1 := fun h1 => hs1 (by rw [h1]; group)
  obtain ⟨⟨hdp, hsz⟩, ⟨hN, hout⟩, hcl⟩ := burnsideJ4_J29_core M hs' hs1'
  rw [hS0, burnsideJ4_LsRu_conjugate, burnsideJ4_cen_conjugate]
  refine ⟨⟨burnsideJ4_isDirectProduct_conjugate g hdp, burnsideJ4_suzukiModel_conjugate g hsz⟩,
    ⟨?_, burnsideJ4_inducesOuter_conjugate g hout⟩,
    burnsideJ4_conjClass_inter_conjugate M.z g hcl⟩
  rw [burnsideJ4_normalizer_conjugate, hN, burnsideJ4_conjugate_sup]

theorem as_J_2_9 : J_2_9 :=
  burnsideJ4_J_2_9_of_st CFSG.Quasithin.RuType.stUnique

end

@[expose] def J_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B B7 : Subgroup G, IsSylowIn 3 B (L1Ru L T) → B7 ≤ L → Nat.card ↥B7 = 7 →
      B ≤ Subgroup.normalizer (B7 : Set G) →
      ∀ s : G, s ∈ S0Ru L B7 → s ≠ 1 →
        ∀ p : ℕ, (p = 7 ∨ p = 13) → ∀ Y : Subgroup G, IsSylowIn p Y (LsRu s) →
          (IsSylowIn p Y ⊤ ∧ Nat.card ↥Y = p) ∧
          Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer ((S0Ru L B7 : Subgroup G) : Set G) ∧
          (Y ⊔ S0Ru L B7 = Subgroup.centralizer (Y : Set G) ∧
            ∃ (_ : ((Subgroup.centralizer (Y : Set G)).subgroupOf
                (Subgroup.normalizer (Y : Set G))).Normal),
              IsCyclic (↥(Subgroup.normalizer (Y : Set G)) ⧸
                (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G))) ∧
              Nat.card (↥(Subgroup.normalizer (Y : Set G)) ⧸
                (Subgroup.centralizer (Y : Set G)).subgroupOf (Subgroup.normalizer (Y : Set G))) =
                p - 1)

section

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ4_J_2_10_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) :
    J_2_10 := by
  intro G _ _ L V T h B B7 hB hB7L hB7 hBN s hs hs1 p hp Y hY
  obtain ⟨M, g, hML, hMT, hgL, rfl, rfl⟩ := burnsideJ4_reduce hSt h hB hB7L hB7 hBN
  subst hML
  obtain ⟨s', rfl⟩ : ∃ s', s = g⁻¹ * s' * g := ⟨g * s * g⁻¹, by group⟩
  have hS0 : S0Ru M.L (CFSG.conjugate M.B7 g) = CFSG.conjugate M.S0 g :=
    burnsideJ4_S0_conjugate hgL
  have hs' : s' ∈ M.S0 := by
    rw [hS0, burnsideJ4_mem_conjugate] at hs
    have e : g * (g⁻¹ * s' * g) * g⁻¹ = s' := by group
    rw [e] at hs
    exact hs
  have hs1' : s' ≠ 1 := fun h1 => hs1 (by rw [h1]; group)
  obtain ⟨Y', hYY'⟩ : ∃ Y', Y = CFSG.conjugate Y' g :=
    ⟨CFSG.conjugate Y g⁻¹, by rw [burnsideJ4_conjugate_conjugate, inv_mul_cancel,
      burnsideJ4_conjugate_one]⟩
  have hY' : IsSylowIn p Y' (LsRu s') := by
    have := burnsideJ4_isSylowIn_conjugate g⁻¹ hY
    rwa [hYY', burnsideJ4_LsRu_conjugate, burnsideJ4_conjugate_conjugate_inv,
      burnsideJ4_conjugate_conjugate_inv] at this
  have hpp : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  obtain ⟨hYL, hYp, hYidx⟩ := hY'
  have hYQ : ∃ Q : Sylow p (CFSG.Quasithin.RuType.Ls s'),
      (Q : Subgroup (CFSG.Quasithin.RuType.Ls s')) =
        Y'.subgroupOf (CFSG.Quasithin.RuType.Ls s') :=
    ⟨IsPGroup.toSylow (P := Y'.subgroupOf (CFSG.Quasithin.RuType.Ls s'))
      (hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYL).symm) hYidx, rfl⟩
  obtain ⟨⟨⟨P, hP⟩, hY'card⟩, hNS0, hYS0, -, hrange⟩ := M.lemma_J210 hs' hs1' hp hYL hYQ
  have hcard' : Nat.card (Subgroup.normalizer (Y' : Set G)) =
      Nat.card (Subgroup.centralizer (Y' : Set G)) * (p - 1) := by
    rw [CFSG.Quasithin.RuType.card_normalizer_eq_mul, hrange]
  have hYc : Nat.card (CFSG.conjugate Y' g) = p := by
    rw [burnsideJ4_card_conjugate]; exact hY'card
  have hcardY : Nat.card (Subgroup.normalizer ((CFSG.conjugate Y' g : Subgroup G) : Set G)) =
      Nat.card (Subgroup.centralizer ((CFSG.conjugate Y' g : Subgroup G) : Set G)) * (p - 1) := by
    rw [burnsideJ4_normalizer_conjugate, burnsideJ4_centralizer_conjugate,
      burnsideJ4_card_conjugate, burnsideJ4_card_conjugate]
    exact hcard'
  rw [hS0, hYY']
  refine ⟨⟨?_, hYc⟩, ?_, ?_, burnsideJ4_aut_part hp hYc hcardY⟩
  · refine ⟨le_top, IsPGroup.of_card (n := 1) (by simpa using hYc), ?_⟩
    have h1 : ((CFSG.conjugate Y' g).subgroupOf ⊤).index = Y'.index := by
      rw [show ((CFSG.conjugate Y' g).subgroupOf ⊤).index = (CFSG.conjugate Y' g).index from
        Subgroup.relIndex_top_right _]
      exact Subgroup.index_map_equiv Y' (MulAut.conj g⁻¹)
    rw [h1, ← hP]
    exact P.not_dvd_index
  · rw [burnsideJ4_normalizer_conjugate, burnsideJ4_normalizer_conjugate]
    exact Subgroup.map_mono hNS0
  · rw [← burnsideJ4_conjugate_sup, hYS0, burnsideJ4_centralizer_conjugate]

theorem as_J_2_10 : J_2_10 :=
  burnsideJ4_J_2_10_of_st CFSG.Quasithin.RuType.stUnique

end

end CFSG.ASVolI
