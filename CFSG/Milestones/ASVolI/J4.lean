module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Milestones.ASVolI.I6
public import CFSG.Milestones.ASVolI.I7
public import CFSG.Milestones.ASVolI.I8
public import CFSG.Milestones.ASVolI.J1
public import CFSG.Milestones.ASVolI.J2
public import CFSG.Milestones.ASVolI.J3
public import CFSG.Quasithin.Background.ASVolIRu.Bridge
public import CFSG.Quasithin.Background.ASVolIRu.StUnique
public import CFSG.Quasithin.Recognition.RuTypeJ11c
public import CFSG.Quasithin.Recognition.RuTypeJ42
public import CFSG.Quasithin.Recognition.RuTypeJ47j
public import CFSG.Quasithin.Recognition.RuTypeJ47l
public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmFinal2
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuCert
public import CFSG.Quasithin.Vol2.TwoF4F48Cert
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Recognition.RuTypeJ45a
public import CFSG.Quasithin.Recognition.RuTypeQuasithin
public import CFSG.Quasithin.Recognition.CertTitsBridge
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.Co1.Module.TwoBCert
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section J4

variable {G : Type} [Group G]

@[expose] def IsV2 (V T V2 : Subgroup G) : Prop :=
  V2 ≤ V ∧ Nat.card ↥V2 = 4 ∧ T ≤ Subgroup.normalizer (V2 : Set G)

@[expose] def L2Ru (L V2 : Subgroup G) : Subgroup G := twoResidual (L ⊓ Subgroup.normalizer (V2 : Set G))

@[expose] def G2Ru (L V2 T : Subgroup G) : Subgroup G := L2Ru L V2 ⊔ T

@[expose] def R2Ru (L V2 T : Subgroup G) : Subgroup G := pCoreOf 2 (L2Ru L V2 ⊔ T)

@[expose] def Q0Ru (V T : Subgroup G) : Subgroup G :=
  Subgroup.closure {h | h ∈ HRu T ∧ ∀ x ∈ HRu T, h⁻¹ * x⁻¹ * h * x ∈ URu V T}

@[expose] def W0Ru (L V V2 T : Subgroup G) : Subgroup G := conjClosure (URu V T) (L2Ru L V2)

@[expose] def WRu (L V V2 T : Subgroup G) : Subgroup G := W0Ru L V V2 T ⊔ Q0Ru V T

@[expose] def Q5Ru (T B5 : Subgroup G) : Subgroup G := ⁅QRu T, B5⁆

@[expose] def S2Ru (L V V2 T : Subgroup G) : Subgroup G := ⁅SRu L, R2Ru L V2 T⁆ ⊔ V

@[expose] def IsAChoice (L V T V2 B5 : Subgroup G) (a : G) : Prop :=
  (Q5Ru T B5 ⊔ S2Ru L V V2 T) ⊓ R2Ru L V2 T = Subgroup.zpowers a ⊔ S2Ru L V V2 T ∧
    a ∉ S2Ru L V V2 T ∧ a ^ 2 ∈ S2Ru L V V2 T ∧ ∀ t ∈ T, a⁻¹ * t⁻¹ * a * t ∈ S2Ru L V V2 T

@[expose] def ARu (L V V2 T : Subgroup G) (a : G) : Subgroup G :=
  conjClosure (Subgroup.zpowers a) (G2Ru L V2 T) ⊔ S2Ru L V V2 T

@[expose] def TFRu (L V V2 T : Subgroup G) (a : G) (B5 : Subgroup G) : Subgroup G :=
  ARu L V V2 T a ⊔ Q5Ru T B5

@[expose] def F1Ru (L V V2 T : Subgroup G) (a : G) (B5 : Subgroup G) : Subgroup G :=
  TFRu L V V2 T a B5 ⊔ B5

@[expose] def F2Ru (L V V2 T : Subgroup G) (a : G) (B5 X : Subgroup G) : Subgroup G :=
  TFRu L V V2 T a B5 ⊔ X

@[expose] def FRu (L V V2 T : Subgroup G) (a : G) (B5 X : Subgroup G) : Subgroup G :=
  F1Ru L V V2 T a B5 ⊔ F2Ru L V V2 T a B5 X

@[expose] def starImg (T X : Subgroup G) : Subgroup (↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)) :=
  (X.subgroupOf (HRu T)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(HRu T)))

@[expose] def IsElemAbelianSection (P N : Subgroup G) (k : ℕ) : Prop :=
  N ≤ P ∧ (∀ x ∈ P, x ^ 2 ∈ N) ∧ (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N) ∧
    N.relIndex P = 2 ^ k

@[expose] def InvertsGroup (v : G) (B : Subgroup G) : Prop :=
  v ∈ Subgroup.normalizer (B : Set G) ∧ ∀ b ∈ B, v⁻¹ * b * v = b⁻¹

end J4

@[expose] def IsTwoF4TwoGroup (Y : Type) [Group Y] : Prop :=
  ∃ (Y0 : Type) (_ : Group Y0), ReeTitsModel Y0 .Tits 2 1 ∧ Nonempty (Y ≃* MulAut Y0)

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section J4b

variable {G : Type} [Group G]

structure RuFSetup (G : Type) [Group G] [Finite G] (L V T V2 B5 X : Subgroup G) (g v a : G) : Prop where
  ru : RuType G L V T
  v2 : IsV2 V T V2
  g_mem : g ∈ L2Ru L V2 ∧ g ∉ HRu T
  v_mem : v ∈ CFSG.conjugate (URu V T) g ∧ v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T
  b5 : IsSylowIn 5 B5 (HRu T) ∧ InvertsGroup v B5
  x3 : IsSylowIn 3 X (G2Ru L V2 T)
  a_choice : IsAChoice L V T V2 B5 a
  a_norm : ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G)
  q5_norm : Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G)

structure RuUSetup (G : Type) [Group G] [Finite G] (L V T V2 B5 X : Subgroup G) (g v a z u : G)
    (I : Subgroup G) : Prop where
  setup : RuFSetup G L V T V2 B5 X g v a
  z_gen : Subgroup.zpowers z = ZRu T
  u_x4 : ∃ h : ↥(FRu L V V2 T a B5 X),
    CFSG.Quasithin.CosetGeom.dist
        (CFSG.Quasithin.CosetGeom.γ₀ (FRu L V V2 T a B5 X) (F1Ru L V V2 T a B5) (F2Ru L V V2 T a B5 X))
        (Sum.inl (h : ↥(FRu L V V2 T a B5 X) ⧸ (F1Ru L V V2 T a B5).subgroupOf (FRu L V V2 T a B5 X))) = 4 ∧
      u = (h : G) * z * (h : G)⁻¹
  u_TF : u ∈ TFRu L V V2 T a B5
  u_inv : InvertsGroup u B5
  I_syl : IsSylowIn 2 I (F1Ru L V V2 T a B5 ⊓ Subgroup.normalizer (B5 : Set G)) ∧ u ∈ I

@[expose] def PFstar (B5 : Subgroup G) : Subgroup G :=
  (CFSG.generalizedFitting ↥(Subgroup.normalizer (B5 : Set G))).map
    (Subgroup.normalizer (B5 : Set G)).subtype

@[expose] def O5N (B : Subgroup G) : Subgroup G := pCoreOf 5 (Subgroup.normalizer (B : Set G))

@[expose] def BvRu (B5 : Subgroup G) (v : G) : Subgroup G :=
  PFstar B5 ⊓ Subgroup.centralizer ({v} : Set G)

@[expose] def BuzPRu (B5 : Subgroup G) (z u : G) : Subgroup G :=
  O5N (BvRu B5 u) ⊓ Subgroup.centralizer ({u * z} : Set G)

@[expose] def BuPRu (B5 : Subgroup G) (z u : G) : Subgroup G :=
  Subgroup.centralizer ({u} : Set G) ⊓ O5N (BvRu B5 (u * z))

@[expose] def BzPRu (B5 : Subgroup G) (z u : G) : Subgroup G :=
  O5N (BuPRu B5 z u) ⊓ Subgroup.centralizer ({z} : Set G)

@[expose] def BsetRu (B5 : Subgroup G) (z u : G) : Set (Subgroup G) :=
  {B5, BvRu B5 u, BvRu B5 (u * z), BzPRu B5 z u, BuPRu B5 z u, BuzPRu B5 z u}

@[expose] def commGraphOn (S : Set (Subgroup G)) : SimpleGraph ↥S :=
  SimpleGraph.fromRel (fun B1 B2 => ⁅(B1 : Subgroup G), (B2 : Subgroup G)⁆ = ⊥)

@[expose] def WBI (Bs : Set (Subgroup G)) (I : Subgroup G) : Subgroup G :=
  Subgroup.closure
    ({w | ∃ B1 ∈ Bs, w ∈ Subgroup.normalizer (I : Set G) ∧ w ∈ Subgroup.normalizer (B1 : Set G)} ∪
      {w | ∃ B1 ∈ Bs, ∃ B2 ∈ Bs, ⁅B1, B2⁆ = ⊥ ∧ w ∈ Subgroup.normalizer (I : Set G) ∧
        w ∈ Subgroup.normalizer ((B1 ⊔ B2 : Subgroup G) : Set G)})

@[expose] def FsetRu (F1 : Subgroup G) (z v : G) : Set (Subgroup G) :=
  {E | ∃ k : G, k⁻¹ * z * k = v ∧ E = CFSG.conjugate F1 k}

@[expose] def EvRu (F1 : Subgroup G) (z u v : G) : Set (Subgroup G) :=
  {E | E ∈ FsetRu F1 z v ∧ Subgroup.zpowers u ⊔ Subgroup.zpowers z ≤ E}

@[expose] def EInv5Ru (z u : G) : Set (Subgroup G) :=
  {X | Nat.card X = 5 ∧ Subgroup.zpowers u ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (X : Set G)}

@[expose] def CgonRu (B5 : Subgroup G) (z u : G) : Set (Subgroup G) :=
  {X | ∃ (hB : B5 ∈ EInv5Ru z u) (hX : X ∈ EInv5Ru z u),
    (commGraphOn (EInv5Ru z u)).Reachable ⟨B5, hB⟩ ⟨X, hX⟩}

@[expose] def EsetRu (F1 : Subgroup G) (z u : G) : Set (Subgroup G) :=
  EvRu F1 z u z ∪ EvRu F1 z u u ∪ EvRu F1 z u (u * z)

@[expose] def EgonGraph (Es : Set (Subgroup G)) (z u : G) : SimpleGraph ↥Es :=
  SimpleGraph.fromRel (fun E1 E2 => ∃ B1 B2 : Subgroup G,
    B1 ≤ (E1 : Subgroup G) ∧ B2 ≤ (E2 : Subgroup G) ∧ Nat.card ↥B1 = 5 ∧ Nat.card ↥B2 = 5 ∧
    Subgroup.zpowers u ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (B1 : Set G) ∧
    Subgroup.zpowers u ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (B2 : Set G) ∧ ⁅B1, B2⁆ = ⊥)

end J4b

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

section RuChoiceSec

open CFSG.Quasithin.RuType in
theorem RuChoice.exists_M {G : Type} [Group G] [Finite G] {L V T : Subgroup G}
    (h : ChIJK.RuType G L V T) :
    ∃ M : RuDataM G, M.L = L ∧ (M.T : Subgroup G) = T := by
  obtain ⟨M, hML, hMT⟩ := ChIJK.RuType.exists_ruDataM stUnique h
  exact ⟨M, hML, by rw [hMT]; rfl⟩

open CFSG.Quasithin.RuType in
def RuChoice.V2pl {G : Type} [Group G] (M : RuDataM G) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ruV M.L, (Multiplicative.toAdd (M.ψV ⟨x, hx⟩)) 2 = 0}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : (⟨a * b, mul_mem ha hb⟩ : ruV M.L) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, toAdd_mul]
    simp [ha2, hb2]
  one_mem' := ⟨(ruV M.L).one_mem, by
    have : (⟨1, (ruV M.L).one_mem⟩ : ruV M.L) = 1 := rfl
    rw [this, map_one, toAdd_one]
    rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    refine ⟨inv_mem ha, ?_⟩
    have : (⟨a⁻¹, inv_mem ha⟩ : ruV M.L) = (⟨a, ha⟩ : ruV M.L)⁻¹ := rfl
    rw [this, map_inv, toAdd_inv]
    have h2 : ∀ x : ZMod 2, -x = x := by decide
    simp [ha2]

open CFSG.Quasithin.RuType in
theorem RuChoice.card_V2pl {G : Type} [Group G] (M : RuDataM G) :
    Nat.card (RuChoice.V2pl M) = 4 := by
  have e : (RuChoice.V2pl M) ≃ {y : Fin 3 → ZMod 2 // y 2 = 0} :=
    { toFun := fun x => ⟨Multiplicative.toAdd (M.ψV ⟨x.1, x.2.1⟩), x.2.2⟩
      invFun := fun y => ⟨(M.ψV.symm (Multiplicative.ofAdd y.1) : G),
        ⟨(M.ψV.symm (Multiplicative.ofAdd y.1)).2, by simpa using y.2⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.exists_T_of_P0 {G : Type} [Group G] (M : RuDataM G) {p : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hp : p ∈ SL3.P0) :
    ∃ (t : G) (htL : t ∈ M.L), t ∈ (M.T : Subgroup G) ∧ M.θ ⟨t, htL⟩ = p := by
  rw [← M.hP0] at hp
  obtain ⟨t', ht', rfl⟩ := hp
  exact ⟨t'.1, t'.2, Subgroup.mem_subgroupOf.mp ht', rfl⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.p0p1 : ∀ y : Fin 3 → ZMod 2, y 2 = 1 →
    natAct3 (⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) y = y + ![1, 0, 0] ∧
    natAct3 (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) y = y + ![0, 1, 0] := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.p0p1_mem :
    (⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ SL3.P0 ∧
    (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ SL3.P0 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

theorem RuChoice.vec_cancel : ∀ y e : Fin 3 → ZMod 2, y + e + y = e := by
  decide +kernel

theorem RuChoice.decomp : ∀ y w : Fin 3 → ZMod 2, y 2 = 1 →
    ∃ a b c : Bool, w = (if a then ![1, 0, 0] else 0) + (if b then ![0, 1, 0] else 0) +
      (if c then y else 0) := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.V2_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) : V2 = RuChoice.V2pl M := by
  obtain ⟨hVle, hcard, hT⟩ := hV2
  have hle : V2 ≤ RuChoice.V2pl M := by
    intro x hx
    have hxV : x ∈ ruV M.L := hVle hx
    refine ⟨hxV, ?_⟩
    by_contra h2
    have hy2 : (Multiplicative.toAdd (M.ψV ⟨x, hxV⟩)) 2 = 1 := by
      rcases Quasithin.RuType.Sigma.zmod2_cases ((Multiplicative.toAdd (M.ψV ⟨x, hxV⟩)) 2) with h | h
      · exact absurd h h2
      · exact h
    set y := Multiplicative.toAdd (M.ψV ⟨x, hxV⟩) with hy
    have hconj : ∀ p : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), p ∈ SL3.P0 → ∃ z ∈ V2, ∃ hz : z ∈ ruV M.L,
        Multiplicative.toAdd (M.ψV ⟨z, hz⟩) = natAct3 p y := by
      intro p hp
      obtain ⟨t, htL, htT, hθ⟩ := RuChoice.exists_T_of_P0 M hp
      have hz : t * x * t⁻¹ ∈ V2 := (Subgroup.mem_normalizer_iff.mp (hT htT) x).mp hx
      have hzV : t * x * t⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V htL hxV
      refine ⟨t * x * t⁻¹, hz, hzV, ?_⟩
      have := M.ψV_equiv ⟨t, htL⟩ ⟨x, hxV⟩ ⟨t * x * t⁻¹, hzV⟩ rfl
      rw [this, toAdd_ofAdd, hθ]
    obtain ⟨z0, hz0, hz0V, hz0e⟩ := hconj _ RuChoice.p0p1_mem.1
    obtain ⟨z1, hz1, hz1V, hz1e⟩ := hconj _ RuChoice.p0p1_mem.2
    rw [(RuChoice.p0p1 y hy2).1] at hz0e
    rw [(RuChoice.p0p1 y hy2).2] at hz1e
    let Y : Set (Fin 3 → ZMod 2) := {w | ∃ z ∈ V2, ∃ hz : z ∈ ruV M.L,
      Multiplicative.toAdd (M.ψV ⟨z, hz⟩) = w}
    have hY0 : (0 : Fin 3 → ZMod 2) ∈ Y := ⟨1, V2.one_mem, (ruV M.L).one_mem, by
      have : (⟨1, (ruV M.L).one_mem⟩ : ruV M.L) = 1 := rfl
      rw [this, map_one, toAdd_one]⟩
    have hYadd : ∀ w1 ∈ Y, ∀ w2 ∈ Y, w1 + w2 ∈ Y := by
      rintro _ ⟨a, ha, haV, rfl⟩ _ ⟨b, hb, hbV, rfl⟩
      refine ⟨a * b, V2.mul_mem ha hb, mul_mem haV hbV, ?_⟩
      have : (⟨a * b, mul_mem haV hbV⟩ : ruV M.L) = ⟨a, haV⟩ * ⟨b, hbV⟩ := rfl
      rw [this, map_mul, toAdd_mul]
    have hYy : y ∈ Y := ⟨x, hx, hxV, rfl⟩
    have hYe0 : (![1, 0, 0] : Fin 3 → ZMod 2) ∈ Y := by
      have h := hYadd _ ⟨z0, hz0, hz0V, hz0e⟩ _ hYy
      rwa [RuChoice.vec_cancel] at h
    have hYe1 : (![0, 1, 0] : Fin 3 → ZMod 2) ∈ Y := by
      have h := hYadd _ ⟨z1, hz1, hz1V, hz1e⟩ _ hYy
      rwa [RuChoice.vec_cancel] at h
    have hVV2 : ruV M.L ≤ V2 := by
      intro v hv
      obtain ⟨a, b, c, hw⟩ := RuChoice.decomp y (Multiplicative.toAdd (M.ψV ⟨v, hv⟩)) hy2
      have hmem : Multiplicative.toAdd (M.ψV ⟨v, hv⟩) ∈ Y := by
        rw [hw]
        refine hYadd _ (hYadd _ ?_ _ ?_) _ ?_
        · split_ifs
          · exact hYe0
          · exact hY0
        · split_ifs
          · exact hYe1
          · exact hY0
        · split_ifs
          · exact hYy
          · exact hY0
      obtain ⟨z, hz, hzV, hze⟩ := hmem
      have : (⟨z, hzV⟩ : ruV M.L) = ⟨v, hv⟩ := M.ψV.injective (Multiplicative.toAdd.injective hze)
      have hzv : z = v := congrArg Subtype.val this
      rw [← hzv]
      exact hz
    have h8 : Nat.card (ruV M.L) = 8 := M.toRuData.card_V
    have h4 : Nat.card V2 = 4 := hcard
    have := Subgroup.card_le_of_le hVV2
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [RuChoice.card_V2pl, hcard])

open CFSG.Quasithin.RuType in
theorem RuChoice.conj_mem_V2pl {G : Type} [Group G] (M : RuDataM G) {g : G} (hgL : g ∈ M.L)
    (hθ : M.θ ⟨g, hgL⟩ ∈ SL3.Pl) {x : G} (hx : x ∈ RuChoice.V2pl M) :
    g * x * g⁻¹ ∈ RuChoice.V2pl M := by
  obtain ⟨hxV, hx2⟩ := hx
  have hgxV : g * x * g⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V hgL hxV
  refine ⟨hgxV, ?_⟩
  have := M.ψV_equiv ⟨g, hgL⟩ ⟨x, hxV⟩ ⟨g * x * g⁻¹, hgxV⟩ rfl
  rw [this, toAdd_ofAdd]
  exact SL3.Pl_plane _ hθ _ hx2

open CFSG.Quasithin.RuType in
theorem RuChoice.L_inf_normalizer {G : Type} [Group G] (M : RuDataM G) :
    M.L ⊓ Subgroup.normalizer (RuChoice.V2pl M : Set G) = M.G2 := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgN⟩
    refine mem_pullL.mpr ⟨hgL, ?_⟩
    have hcol : ∀ e : Fin 3 → ZMod 2, e 2 = 0 → (natAct3 (M.θ ⟨g, hgL⟩) e) 2 = 0 := by
      intro e he
      set x : ruV M.L := M.ψV.symm (Multiplicative.ofAdd e) with hxdef
      have hxV2 : (x : G) ∈ RuChoice.V2pl M := ⟨x.2, by simpa [hxdef] using he⟩
      have hgx : g * x * g⁻¹ ∈ RuChoice.V2pl M :=
        (Subgroup.mem_normalizer_iff.mp hgN x).mp hxV2
      obtain ⟨hgxV, hgx2⟩ := hgx
      have := M.ψV_equiv ⟨g, hgL⟩ x ⟨g * x * g⁻¹, hgxV⟩ rfl
      rw [this, toAdd_ofAdd] at hgx2
      simpa [hxdef] using hgx2
    have h0 := hcol ![1, 0, 0] rfl
    have h1 := hcol ![0, 1, 0] rfl
    refine ⟨?_, ?_⟩
    · simpa [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
    · simpa [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1
  · intro hg
    obtain ⟨hgL, hθ⟩ := mem_pullL.mp hg
    refine ⟨hgL, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => RuChoice.conj_mem_V2pl M hgL hθ hx
    · intro hx
      have hθ' : M.θ ⟨g⁻¹, inv_mem hgL⟩ ∈ SL3.Pl := by
        have : M.θ ⟨g⁻¹, inv_mem hgL⟩ = (M.θ ⟨g, hgL⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact inv_mem hθ
      have := RuChoice.conj_mem_V2pl M (inv_mem hgL) hθ' hx
      simpa [mul_assoc] using this

theorem RuChoice.twoResidual_le {G : Type} [Group G] (X : Subgroup G) :
    ChIJK.twoResidual X ≤ X :=
  Subgroup.map_subtype_le _

theorem RuChoice.mem_twoResidual_of_odd {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {x : G} (hx : x ∈ X) {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) :
    x ∈ ChIJK.twoResidual X := by
  unfold ChIJK.twoResidual
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_sInf]
  rintro N ⟨hN, k, hk⟩
  have hcard : Nat.card (↥X ⧸ N) = 2 ^ k := by
    rw [← Subgroup.index_eq_card]
    exact hk
  have h1 : ((⟨x, hx⟩ : X) : ↥X ⧸ N) ^ (2 ^ k) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h2 : ((⟨x, hx⟩ : X) : ↥X ⧸ N) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : X) ^ n = 1 := Subtype.ext (by simpa using hxn)
    rw [this]
    rfl
  have hcop : Nat.Coprime n (2 ^ k) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr hn
  have h3 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  rw [hcop, pow_one] at h3
  exact (QuotientGroup.eq_one_iff _).mp h3

@[expose] def RuChoice.a3mat : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.a3 :
    RuChoice.a3mat ∈ SL3.Pl ∧ RuChoice.a3mat ^ 3 = 1 ∧ RuChoice.a3mat ≠ 1 :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.exists_L2_lift3 {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (ha : a ∈ SL3.Pl) (ha3 : a ^ 3 = 1) :
    ∃ (l : G) (hl : l ∈ M.L), l ∈ ChIJK.twoResidual M.G2 ∧ M.θ ⟨l, hl⟩ = a ∧ l ^ 3 = 1 := by
  obtain ⟨l, hθ, hl3⟩ := M.exists_lift ha3 (by norm_num)
  have hlG : (l : G) ∈ M.G2 := mem_pullL.mpr ⟨l.2, by rw [hθ]; exact ha⟩
  exact ⟨l, l.2, RuChoice.mem_twoResidual_of_odd hlG (n := 3) (by decide) hl3, hθ, hl3⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.card_T {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
  rw [← M.toRuData.TL_eq, M.toRuData.card_TL]

open CFSG.Quasithin.RuType in
theorem RuChoice.L2_sup_T {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) = M.G2 := by
  have hle : ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) ≤ M.G2 :=
    sup_le (RuChoice.twoResidual_le _) M.T_le_G2
  obtain ⟨ha, ha3, ha1⟩ := RuChoice.a3
  obtain ⟨l, hl, hl2, hθ, hl3⟩ := RuChoice.exists_L2_lift3 M ha ha3
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply ha1
    rw [← hθ]
    exact map_one M.θ
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  set K := ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) with hK
  have h3 : 3 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K (x := l) (Subgroup.mem_sup_left hl2)
    rwa [hord] at this
  have h2 : 2 ^ 14 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le (le_sup_right : (M.T : Subgroup G) ≤ K)
    rwa [RuChoice.card_T] at this
  have h6 : 2 ^ 14 * 3 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hG : Nat.card M.G2 = 2 ^ 14 * 3 := by rw [M.card_G2]; norm_num
  have hKG : Nat.card K ∣ Nat.card M.G2 := Subgroup.card_dvd_of_le hle
  rw [hG] at hKG
  have heq : Nat.card K = 2 ^ 14 * 3 := Nat.dvd_antisymm hKG h6
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hG, heq])

open CFSG.Quasithin.RuType in
theorem RuChoice.inter_P0 : ∀ y ∈ SL3.Pl, (∀ p ∈ SL3.Pl, p⁻¹ * y * p ∈ SL3.P0) → y ∈ SL3.R2m := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.pCoreOf_G2 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    pCoreOf 2 M.G2 = M.R2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    have hn : (CFSG.pCore 2 ↥M.G2).Normal := CFSG.pCore_normal
    have hTp : IsPGroup 2 ((M.T : Subgroup G).subgroupOf M.G2) :=
      (M.T.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe M.T_le_G2).symm
    have hidx : ¬ 2 ∣ ((M.T : Subgroup G).subgroupOf M.G2).index := by
      have h1 := Subgroup.card_mul_index ((M.T : Subgroup G).subgroupOf M.G2)
      rw [card_subgroupOf_of_le M.T_le_G2, RuChoice.card_T, M.card_G2] at h1
      have : ((M.T : Subgroup G).subgroupOf M.G2).index = 3 := by omega
      rw [this]
      norm_num
    let P : Sylow 2 ↥M.G2 := hTp.toSylow hidx
    have hle : CFSG.pCore 2 ↥M.G2 ≤ (P : Subgroup ↥M.G2) :=
      (CFSG.pCore_isPGroup (G := ↥M.G2) (p := 2)).le_sylow_of_normal P
    rintro x ⟨y, hy, rfl⟩
    have hyG : (y : G) ∈ M.G2 := y.2
    obtain ⟨hyL, -⟩ := mem_pullL.mp hyG
    refine mem_pullL.mpr ⟨hyL, ?_⟩
    apply RuChoice.inter_P0
    · exact (mem_pullL.mp hyG).2
    · intro p hp
      obtain ⟨⟨g, hgL⟩, rfl⟩ := M.θ_surj p
      have hgG : g ∈ M.G2 := mem_pullL.mpr ⟨hgL, hp⟩
      have hmem : (⟨g, hgG⟩ : ↥M.G2)⁻¹ * y * ⟨g, hgG⟩ ∈ CFSG.pCore 2 ↥M.G2 := by
        have := hn.conj_mem y hy (⟨g, hgG⟩ : ↥M.G2)⁻¹
        simpa using this
      have hP : ((⟨g, hgG⟩ : ↥M.G2)⁻¹ * y * ⟨g, hgG⟩ : ↥M.G2) ∈ (P : Subgroup ↥M.G2) := hle hmem
      have hPT : g⁻¹ * y * g ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp hP
      have := M.θ_mem_P0 hPT
      have e : (⟨g⁻¹ * y * g, M.toRuData.T_le_L hPT⟩ : M.L) =
          (⟨g, hgL⟩ : M.L)⁻¹ * ⟨y, hyL⟩ * ⟨g, hgL⟩ := rfl
      rw [e, map_mul, map_mul, map_inv] at this
      exact this
  ·
    have hRn : (M.R2.subgroupOf M.G2).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxL, hxR⟩ := mem_pullL.mp hx
      obtain ⟨hgL, hgP⟩ := mem_pullL.mp g.2
      show (g : G) * x * (g : G)⁻¹ ∈ M.R2
      refine mem_pullL.mpr ⟨mul_mem (mul_mem hgL hxL) (inv_mem hgL), ?_⟩
      have e : (⟨(g : G) * x * (g : G)⁻¹, mul_mem (mul_mem hgL hxL) (inv_mem hgL)⟩ : M.L) =
          ⟨g, hgL⟩ * ⟨(x : G), hxL⟩ * (⟨g, hgL⟩ : M.L)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact SL3.conj_mem_R2m _ hgP _ hxR
    have hRp : IsPGroup 2 (M.R2.subgroupOf M.G2) := by
      rw [IsPGroup.iff_card, card_subgroupOf_of_le M.R2_le_G2, M.card_R2]
      exact ⟨13, rfl⟩
    have hle : M.R2.subgroupOf M.G2 ≤ CFSG.pCore 2 ↥M.G2 := le_sSup ⟨hRn, hRp⟩
    have := Subgroup.map_mono (f := M.G2.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le M.R2_le_G2] at this
    exact this

open CFSG.Quasithin.RuType in
theorem RuChoice.L2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.L2Ru M.L V2 = ChIJK.twoResidual M.G2 := by
  rw [ChIJK.L2Ru, RuChoice.V2_eq M hV2, RuChoice.L_inf_normalizer]

open CFSG.Quasithin.RuType in
theorem RuChoice.G2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.G2Ru M.L V2 (M.T : Subgroup G) = M.G2 := by
  rw [ChIJK.G2Ru, RuChoice.L2Ru_eq M hV2, RuChoice.L2_sup_T]

open CFSG.Quasithin.RuType in
theorem RuChoice.R2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.R2Ru M.L V2 (M.T : Subgroup G) = M.R2 := by
  rw [ChIJK.R2Ru, RuChoice.L2Ru_eq M hV2, RuChoice.L2_sup_T, RuChoice.pCoreOf_G2]

open CFSG.Quasithin.RuType in
def RuChoice.chiAdd {G : Type} [Group G] (M : RuDataM G) (X : Subgroup G) :
    AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) where
  carrier := {A | ∃ x ∈ X, ∃ hx : x ∈ ruS M.L, Multiplicative.toAdd (M.χ ⟨x, hx⟩) = A}
  zero_mem' := ⟨1, X.one_mem, (ruS M.L).one_mem, by
    have : (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 := rfl
    rw [this, map_one, toAdd_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, haS, rfl⟩ ⟨b, hb, hbS, rfl⟩
    refine ⟨a * b, X.mul_mem ha hb, mul_mem haS hbS, ?_⟩
    have : (⟨a * b, mul_mem haS hbS⟩ : ruS M.L) = ⟨a, haS⟩ * ⟨b, hbS⟩ := rfl
    rw [this, M.toAdd_χ_mul]
  neg_mem' := by
    rintro _ ⟨a, ha, haS, rfl⟩
    refine ⟨a⁻¹, X.inv_mem ha, inv_mem haS, ?_⟩
    have : (⟨a⁻¹, inv_mem haS⟩ : ruS M.L) = (⟨a, haS⟩ : ruS M.L)⁻¹ := rfl
    rw [this, M.toAdd_χ_inv]
    ext i j
    simp only [Matrix.neg_apply]
    have h2 : ∀ x : ZMod 2, x = -x := by decide
    exact h2 _

open CFSG.Quasithin.RuType in
theorem RuChoice.mem_of_chi {G : Type} [Group G] (M : RuDataM G) {X : Subgroup G}
    (hVX : ruV M.L ≤ X) {x : G} (hx : x ∈ ruS M.L)
    (h : Multiplicative.toAdd (M.χ ⟨x, hx⟩) ∈ RuChoice.chiAdd M X) : x ∈ X := by
  obtain ⟨y, hyX, hyS, hy⟩ := h
  have hk : (⟨y, hyS⟩ : ruS M.L)⁻¹ * ⟨x, hx⟩ ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Multiplicative.toAdd.injective hy]
    exact inv_mul_cancel _
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact X.mul_mem hyX (hVX hk)

open CFSG.Quasithin.RuType in
theorem RuChoice.W_le_of_chi {G : Type} [Group G] [Finite G] (M : RuDataM G) {X : Subgroup G}
    (hVX : ruV M.L ≤ X)
    (h : ∀ A, SL3.IsM2 A → IsTraceZero A → A ∈ RuChoice.chiAdd M X) : M.W ≤ X := by
  rintro x ⟨hx, hxM⟩
  exact RuChoice.mem_of_chi M hVX hx (h _ hxM (M.χ_trace _))

def RuChoice.inSpan :
    List (Matrix (Fin 3) (Fin 3) (ZMod 2)) → Matrix (Fin 3) (Fin 3) (ZMod 2) → Bool
  | [], A => decide (A = 0)
  | g :: gs, A => RuChoice.inSpan gs A || RuChoice.inSpan gs (A + g)

theorem RuChoice.mat_add_self : ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g + g = 0 := by
  decide +kernel

theorem RuChoice.mem_of_inSpan (P : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    ∀ («gens» : List (Matrix (Fin 3) (Fin 3) (ZMod 2))), (∀ g ∈ «gens», g ∈ P) →
      ∀ A, RuChoice.inSpan «gens» A = true → A ∈ P := by
  intro «gens»
  induction «gens» with
  | nil =>
    intro _ A h
    simp only [RuChoice.inSpan, decide_eq_true_eq] at h
    rw [h]
    exact P.zero_mem
  | cons g gs ih =>
    intro hg A h
    simp only [RuChoice.inSpan, Bool.or_eq_true] at h
    have hgs : ∀ x ∈ gs, x ∈ P := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    rcases h with h | h
    · exact ih hgs A h
    · have h1 := ih hgs (A + g) h
      have hgP := hg g List.mem_cons_self
      have : A = (A + g) + g := by
        rw [add_assoc, RuChoice.mat_add_self, add_zero]
      rw [this]
      exact P.add_mem h1 hgP

open CFSG.Quasithin.RuType in
theorem RuChoice.comm_mem_chiAdd {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {X : Subgroup G} (hX : ⁅ruS M.L, M.R2⁆ ≤ X) {r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hr : r ∈ SL3.R2m) {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) :
    stAct r A + A ∈ RuChoice.chiAdd M X := by
  obtain ⟨l, hθ⟩ := M.θ_surj r
  have hlR : (l : G) ∈ M.R2 := mem_pullL.mpr ⟨l.2, by rw [hθ]; exact hr⟩
  obtain ⟨s, hs⟩ := M.χ_surj A hA
  have hlS : (l : G) ∈ Subgroup.normalizer (ruS M.L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L l.2
  have ht : (l : G) * (s : G)⁻¹ * (l : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp hlS _).mp (inv_mem s.2)
  have hy : (s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹ ∈ ruS M.L := by
    have : (s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹ =
        (s : G) * ((l : G) * (s : G)⁻¹ * (l : G)⁻¹) := by group
    rw [this]
    exact mul_mem s.2 ht
  refine ⟨(s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹,
    hX (Subgroup.commutator_mem_commutator s.2 hlR), hy, ?_⟩
  have e : (⟨(s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹, hy⟩ : ruS M.L) =
      s * ⟨(l : G) * (s : G)⁻¹ * (l : G)⁻¹, ht⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  rw [e, M.toAdd_χ_mul]
  have h1 : Multiplicative.toAdd (M.χ ⟨(l : G) * (s : G)⁻¹ * (l : G)⁻¹, ht⟩) =
      stAct (M.θ l) (Multiplicative.toAdd (M.χ s⁻¹)) := M.χ_conj l s⁻¹
  rw [h1, M.toAdd_χ_inv, hs, toAdd_ofAdd, hθ, add_comm]

@[expose] def RuChoice.ra : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

@[expose] def RuChoice.rb : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def RuChoice.pairsR2 :
    List (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [(RuChoice.ra, !![1, 0, 0; 0, 0, 0; 0, 0, 1]),
   (RuChoice.ra, !![1, 0, 0; 0, 0, 0; 0, 1, 1]),
   (RuChoice.ra, !![0, 0, 0; 0, 0, 0; 1, 0, 0]),
   (RuChoice.ra, !![0, 1, 0; 0, 0, 0; 0, 0, 0]),
   (RuChoice.rb, !![0, 0, 0; 0, 0, 0; 0, 1, 0]),
   (RuChoice.rb, !![0, 0, 0; 0, 1, 0; 1, 0, 1])]

@[expose] def RuChoice.gensR2 : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![0, 0, 0; 0, 0, 1; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
   !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0; 0, 0, 1]]

open CFSG.Quasithin.RuType in
theorem RuChoice.gensR2_spec : ∀ g ∈ RuChoice.gensR2, ∃ p ∈ RuChoice.pairsR2,
    p.1 ∈ SL3.R2m ∧ IsTraceZero p.2 ∧ stAct p.1 p.2 + p.2 = g := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.span_M2 : ∀ A, SL3.IsM2 A → IsTraceZero A →
    RuChoice.inSpan RuChoice.gensR2 A = true := by
  decide +kernel

open CFSG.Quasithin.RuType in
theorem RuChoice.W_le_S2 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    M.W ≤ ⁅ruS M.L, M.R2⁆ ⊔ ruV M.L := by
  refine RuChoice.W_le_of_chi M le_sup_right fun A hA hAt => ?_
  refine RuChoice.mem_of_inSpan _ RuChoice.gensR2 ?_ A (RuChoice.span_M2 A hA hAt)
  intro g hg
  obtain ⟨p, -, hp1, hp2, rfl⟩ := RuChoice.gensR2_spec g hg
  exact RuChoice.comm_mem_chiAdd M le_sup_left hp1 hp2

open CFSG.Quasithin.RuType in
theorem RuChoice.comm_sup_V_eq_W {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ⁅ruS M.L, M.R2⁆ ⊔ ruV M.L = M.W := by
  refine le_antisymm (sup_le ?_ ?_) (RuChoice.W_le_S2 M)
  · rw [Subgroup.commutator_le]
    intro s hs r hr
    have := M.W.inv_mem (M.comm_mem_W hr hs)
    have e : s * r * s⁻¹ * r⁻¹ = (r * s * r⁻¹ * s⁻¹)⁻¹ := by group
    show s * r * s⁻¹ * r⁻¹ ∈ M.W
    rw [e]
    exact this
  · exact fun v hv => M.U_le_W (M.V_le_U hv)

open CFSG.Quasithin.RuType in
theorem RuChoice.S2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.S2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) = M.W := by
  rw [ChIJK.S2Ru, RuChoice.R2Ru_eq M hV2]
  exact RuChoice.comm_sup_V_eq_W M

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.frame {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    G2Ru M.L V2 (M.T : Subgroup G) = M.G2 ∧ R2Ru M.L V2 (M.T : Subgroup G) = M.R2 ∧
      S2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) = M.W :=
  ⟨RuChoice.G2Ru_eq M hV2, RuChoice.R2Ru_eq M hV2, RuChoice.S2Ru_eq M hV2⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.sylow5_swap :
    ∀ w ∈ Sigma.SP0, w * w = 1 → w ≠ 1 → w.right = 1 →
    ∀ b₁ : SigmaL2F4, b₁ ^ 5 = 1 → b₁ ≠ 1 → w * b₁ * w⁻¹ = b₁⁻¹ →
    ∀ b₂ : SigmaL2F4, b₂ ^ 5 = 1 → b₂ ≠ 1 → w * b₂ * w⁻¹ = b₂⁻¹ →
    ∃ s ∈ Sigma.SP0, ∃ k : Fin 5, s * b₂ * s⁻¹ = b₁ ^ (k : ℕ) := by
  decide +kernel

open scoped Pointwise in
theorem RuChoice.sylow_mod {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) {b c : G} (hb : orderOf b = 5) (hc : orderOf c = 5)
    (hbN : b ∈ Subgroup.normalizer (Q : Set G)) {k : ℕ} (hk : (b ^ k)⁻¹ * c ∈ Q) :
    ∃ q ∈ Q, Subgroup.zpowers b = Subgroup.zpowers (q * c * q⁻¹) := by
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hbQ : Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hbN
  set N : Subgroup G := Subgroup.zpowers b ⊔ Q with hN
  have hbN' : Subgroup.zpowers b ≤ N := le_sup_left
  have hQN : Q ≤ N := le_sup_right
  have hset : ((N : Subgroup G) : Set G) = (Subgroup.zpowers b : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbQ
  have hcN : c ∈ N := by
    have : c = b ^ k * ((b ^ k)⁻¹ * c) := by group
    rw [this]
    exact N.mul_mem (N.pow_mem (hbN' (Subgroup.mem_zpowers b)) k) (hQN hk)
  have hinf : Subgroup.zpowers b ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Subgroup.mem_bot]
    have h1 : orderOf x ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard _ hx1
      rwa [Nat.card_zpowers, hb] at this
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hQ2)
    have h2 : orderOf x ∣ 2 ^ m := by
      have := Subgroup.orderOf_dvd_natCard _ hx2
      rwa [hm] at this
    have hd := Nat.dvd_gcd h1 h2
    have : Nat.gcd 5 (2 ^ m) = 1 := by
      apply Nat.Coprime.pow_right
      norm_num
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hQ2)
  have hcardN : Nat.card N = 5 * 2 ^ m := by
    have h := CFSG.Quasithin.RuType.card_sup_mul_inf_of_normalizes hbQ
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hb, hm] at h
    exact h
  set P1 : Subgroup N := (Subgroup.zpowers b).subgroupOf N with hP1
  set P2 : Subgroup N := (Subgroup.zpowers c).subgroupOf N with hP2
  have hc' : Subgroup.zpowers c ≤ N := by
    rw [Subgroup.zpowers_le]
    exact hcN
  have hP1c : Nat.card P1 = 5 := by
    rw [hP1, CFSG.Quasithin.RuType.card_subgroupOf_of_le hbN', Nat.card_zpowers, hb]
  have hP2c : Nat.card P2 = 5 := by
    rw [hP2, CFSG.Quasithin.RuType.card_subgroupOf_of_le hc', Nat.card_zpowers, hc]
  have hidx1 : P1.index = 2 ^ m := by
    have h := Subgroup.card_mul_index P1
    rw [hP1c, hcardN] at h
    omega
  have hidx2 : P2.index = 2 ^ m := by
    have h := Subgroup.card_mul_index P2
    rw [hP2c, hcardN] at h
    omega
  have hnd : ¬ 5 ∣ 2 ^ m := by
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    omega
  let S1 : Sylow 5 N := (IsPGroup.of_card (n := 1) (by rw [hP1c]; norm_num)).toSylow
    (by rw [hidx1]; exact hnd)
  let S2 : Sylow 5 N := (IsPGroup.of_card (n := 1) (by rw [hP2c]; norm_num)).toSylow
    (by rw [hidx2]; exact hnd)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N S2 S1
  have hn' : (S1 : Subgroup N) = (S2 : Subgroup N).map (MulAut.conj n).toMonoidHom := by
    rw [← hn, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hnmem : (n : G) ∈ (Subgroup.zpowers b : Set G) * (Q : Set G) := by
    rw [← hset]
    exact n.2
  obtain ⟨y, hy, q, hq, hyq⟩ := Set.mem_mul.mp hnmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨q, hq, ?_⟩
  have hmapN : ∀ X : Subgroup N, X.map N.subtype = X.map N.subtype := fun _ => rfl
  have key : Subgroup.zpowers b = ((Subgroup.zpowers c).map (MulAut.conj (n : G)).toMonoidHom) := by
    ext x
    constructor
    · intro hx
      have hxN : x ∈ N := hbN' hx
      have : (⟨x, hxN⟩ : N) ∈ (S1 : Subgroup N) := by
        show (⟨x, hxN⟩ : N) ∈ P1
        exact hx
      rw [hn'] at this
      obtain ⟨z, hz, hzx⟩ := this
      have hz' : (z : G) ∈ Subgroup.zpowers c := hz
      refine ⟨z, hz', ?_⟩
      have := congrArg Subtype.val hzx
      simpa [MulAut.conj_apply] using this
    · rintro ⟨z, hz, rfl⟩
      have hzN : z ∈ N := hc' hz
      have : (⟨z, hzN⟩ : N) ∈ (S2 : Subgroup N) := by
        show (⟨z, hzN⟩ : N) ∈ P2
        exact hz
      have h2 : (MulAut.conj n) ⟨z, hzN⟩ ∈ (S1 : Subgroup N) := by
        rw [hn']
        exact ⟨⟨z, hzN⟩, this, rfl⟩
      have h3 : ((MulAut.conj n) ⟨z, hzN⟩ : N) ∈ P1 := h2
      have h4 : (((MulAut.conj n) ⟨z, hzN⟩ : N) : G) ∈ Subgroup.zpowers b := h3
      simpa [MulAut.conj_apply] using h4
  rw [show Subgroup.zpowers (q * c * q⁻¹) = (Subgroup.zpowers c).map (MulAut.conj q).toMonoidHom by
    rw [MonoidHom.map_zpowers]; rfl]
  have hmem : ∀ (A : Subgroup G) (g x : G),
      x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
    intro A g x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have key' : ∀ x : G, x ∈ Subgroup.zpowers b ↔ (b ^ i * q)⁻¹ * x * (b ^ i * q) ∈ Subgroup.zpowers c := by
    intro x
    rw [← hyq] at key
    rw [key, hmem]
  have hbi : ∀ x ∈ Subgroup.zpowers b, b ^ i * x * (b ^ i)⁻¹ ∈ Subgroup.zpowers b := fun x hx =>
    mul_mem (mul_mem (zpow_mem (Subgroup.mem_zpowers b) i) hx)
      (inv_mem (zpow_mem (Subgroup.mem_zpowers b) i))
  ext x
  rw [hmem]
  constructor
  · intro hx
    have h1 := (key' _).mp (hbi x hx)
    have e : (b ^ i * q)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * (b ^ i * q) = q⁻¹ * x * q := by group
    rwa [e] at h1
  · intro hx
    have e : (b ^ i * q)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * (b ^ i * q) = q⁻¹ * x * q := by group
    have h1 : b ^ i * x * (b ^ i)⁻¹ ∈ Subgroup.zpowers b := (key' _).mpr (by rw [e]; exact hx)
    have h2 : (b ^ i)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * b ^ i ∈ Subgroup.zpowers b :=
      mul_mem (mul_mem (inv_mem (zpow_mem (Subgroup.mem_zpowers b) i)) h1)
        (zpow_mem (Subgroup.mem_zpowers b) i)
    have e2 : (b ^ i)⁻¹ * (b ^ i * x * (b ^ i)⁻¹) * b ^ i = x := by group
    rwa [e2] at h2

open CFSG.Quasithin.RuType in
theorem RuChoice.ZRu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.ZRu (M.T : Subgroup G) = ruZ M.T :=
  ChIJK.RuType.BridgeTwo.centerOf_eq _

open CFSG.Quasithin.RuType in
theorem RuChoice.HRu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.HRu (M.T : Subgroup G) = ruH M.T :=
  congrArg (fun Z : Subgroup G => Subgroup.centralizer (Z : Set G)) (RuChoice.ZRu_eq M)

open CFSG.Quasithin.RuType in
theorem RuChoice.QRu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.QRu (M.T : Subgroup G) = ruQ M.T :=
  congrArg (pCoreOf 2) (RuChoice.HRu_eq M)

open CFSG.Quasithin.RuType in
theorem RuChoice.URu_eq {G : Type} [Group G] (M : RuDataM G) :
    ChIJK.URu (ruV M.L) (M.T : Subgroup G) = ruU M.L M.T :=
  (ChIJK.RuType.BridgeTwo.conjClosure_eq _ _).trans
    (congrArg (CFSG.Quasithin.conjClosure (ruV M.L)) (RuChoice.HRu_eq M))

open CFSG.Quasithin.RuType in
theorem RuChoice.conjugate_U_eq {G : Type} [Group G] (M : RuDataM G) (g : G) :
    CFSG.conjugate (ChIJK.URu (ruV M.L) (M.T : Subgroup G)) g = M.conjU g⁻¹ := by
  ext x
  rw [RuChoice.URu_eq, M.mem_conjU]
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

open CFSG.Quasithin.RuType in
theorem RuChoice.Ual_mul_mem_Q {G : Type} [Group G] [Finite G] (M : RuDataM G) {v : G}
    (hv : v ∈ M.Ual) (hvQ : v ∉ ruQ M.T) : v * M.vel⁻¹ ∈ ruQ M.T := by
  have hidx : ((M.Ual ⊓ ruQ M.T).subgroupOf M.Ual).index = 2 := by
    have h := Subgroup.card_mul_index ((M.Ual ⊓ ruQ M.T).subgroupOf M.Ual)
    rw [card_subgroupOf_of_le inf_le_left, M.card_Ual_inf_Q, M.card_Ual] at h
    omega
  have h1 : (⟨v, hv⟩ : M.Ual) * (⟨M.vel, M.vel_mem_Ual⟩ : M.Ual)⁻¹ ∈
      (M.Ual ⊓ ruQ M.T).subgroupOf M.Ual := by
    refine (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false ?_ ?_)
    · intro h
      exact hvQ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2
    · intro h
      have h' := inv_mem h
      rw [inv_inv] at h'
      exact M.vel_not_mem_Q (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h')).2
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).2

open CFSG.Quasithin.RuType in
theorem RuChoice.B5_core {G : Type} [Group G] [Finite G] (M : RuDataM G) {v b : G}
    (hvU : v ∈ M.Ual) (hvQ : v ∉ ruQ M.T) (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
    (hinv : v * b * v⁻¹ = b⁻¹) :
    ∃ s : G, s ∈ (M.T : Subgroup G) ∧
      Subgroup.zpowers b = Subgroup.zpowers (s * M.b5el * s⁻¹) := by
  have hvS : v ∈ ruS M.L := M.Ual_le_S hvU
  have hvH : v ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hvS)
  have hvq := RuChoice.Ual_mul_mem_Q M hvU hvQ
  have hker : (⟨v, hvH⟩ : ruH M.T) * (⟨M.vel, M.vel_mem_H⟩ : ruH M.T)⁻¹ ∈ M.φ.ker := by
    rw [M.φ_ker, Subgroup.mem_subgroupOf]
    exact hvq
  have hφv : M.φ ⟨v, hvH⟩ = M.φ ⟨M.vel, M.vel_mem_H⟩ := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
    exact hker
  set w : SigmaL2F4 := M.φ ⟨M.vel, M.vel_mem_H⟩ with hw
  have hwSP0 : w ∈ Sigma.SP0 := by
    rw [← M.hSP0]
    exact ⟨⟨M.vel, M.vel_mem_H⟩, Subgroup.mem_subgroupOf.mpr M.vel_mem_T, rfl⟩
  have hw2 : w * w = 1 := by
    rw [hw, ← map_mul]
    have : (⟨M.vel, M.vel_mem_H⟩ : ruH M.T) * ⟨M.vel, M.vel_mem_H⟩ = 1 :=
      Subtype.ext M.vel_mul_self
    rw [this, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    apply M.vel_not_mem_Q
    have : (⟨M.vel, M.vel_mem_H⟩ : ruH M.T) ∈ M.φ.ker := h
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
    exact this
  have hwr : w.right = 1 := by
    obtain ⟨hk, hk1⟩ := M.mem_K_iff.mp M.vel_mem_K
    exact hk1
  have hb5H : M.b5el ∈ ruH M.T := M.b5el_mem_H
  have hbQ : ∀ (x : G) (hx : x ∈ ruH M.T), orderOf x = 5 → M.φ ⟨x, hx⟩ ≠ 1 := by
    intro x hx hx5 h
    have : (⟨x, hx⟩ : ruH M.T) ∈ M.φ.ker := h
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
    have h1 := Subgroup.orderOf_dvd_natCard _ this
    rw [hx5, M.toRuData.card_Q] at h1
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h1
    omega
  have hord : ∀ (x : G) (hx : x ∈ ruH M.T), orderOf x = 5 → (M.φ ⟨x, hx⟩) ^ 5 = 1 := by
    intro x hx hx5
    rw [← map_pow]
    have : (⟨x, hx⟩ : ruH M.T) ^ 5 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hx5]
      exact pow_orderOf_eq_one x)
    rw [this, map_one]
  have hb₁inv : w * M.φ ⟨b, hbH⟩ * w⁻¹ = (M.φ ⟨b, hbH⟩)⁻¹ := by
    have h := congrArg M.φ (show (⟨v, hvH⟩ : ruH M.T) * ⟨b, hbH⟩ * ⟨v, hvH⟩⁻¹ = ⟨b, hbH⟩⁻¹ from
      Subtype.ext hinv)
    rw [map_mul, map_mul, map_inv, map_inv, hφv] at h
    exact h
  have hb₂inv : w * M.φ ⟨M.b5el, hb5H⟩ * w⁻¹ = (M.φ ⟨M.b5el, hb5H⟩)⁻¹ := by
    have h := congrArg M.φ (show (⟨M.vel, M.vel_mem_H⟩ : ruH M.T) * ⟨M.b5el, hb5H⟩ *
        ⟨M.vel, M.vel_mem_H⟩⁻¹ = ⟨M.b5el, hb5H⟩⁻¹ from Subtype.ext M.vel_inv_b5el)
    rw [map_mul, map_mul, map_inv, map_inv] at h
    exact h
  obtain ⟨s₀, hs₀, k, hk⟩ := RuChoice.sylow5_swap w hwSP0 hw2 hw1 hwr
    (M.φ ⟨b, hbH⟩) (hord b hbH hb5) (hbQ b hbH hb5) hb₁inv
    (M.φ ⟨M.b5el, hb5H⟩) (hord _ hb5H M.orderOf_b5el) (hbQ _ hb5H M.orderOf_b5el) hb₂inv
  have hs₀' := hs₀
  rw [← M.hSP0] at hs₀'
  obtain ⟨x₁, hx₁T, hx₁⟩ := hs₀'
  set s₁ : G := (x₁ : G) with hs₁
  have hs₁T : s₁ ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp hx₁T
  have hs₁H : s₁ ∈ ruH M.T := x₁.2
  set c : G := s₁ * M.b5el * s₁⁻¹ with hc
  have hcH : c ∈ ruH M.T := mul_mem (mul_mem hs₁H hb5H) (inv_mem hs₁H)
  have hcord : orderOf c = 5 := by
    rw [hc, CFSG.Quasithin.RuType.orderOf_conj_eq]
    exact M.orderOf_b5el
  have hφc : M.φ ⟨c, hcH⟩ = (M.φ ⟨b, hbH⟩) ^ (k : ℕ) := by
    rw [← hk, ← hx₁]
    have : (⟨c, hcH⟩ : ruH M.T) = x₁ * ⟨M.b5el, hb5H⟩ * x₁⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hker2 : ((⟨b, hbH⟩ : ruH M.T) ^ (k : ℕ))⁻¹ * ⟨c, hcH⟩ ∈ M.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hφc, inv_mul_cancel]
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hker2
  have hker3 : (b ^ (k : ℕ))⁻¹ * c ∈ ruQ M.T := hker2
  have hQ2 : IsPGroup 2 (ruQ M.T) := IsPGroup.of_card M.toRuData.card_Q
  have hbN : b ∈ Subgroup.normalizer ((ruQ M.T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact M.conj_mem_Q hbH hq
    · intro hq
      have := M.conj_mem_Q (inv_mem hbH) hq
      simpa [mul_assoc] using this
  obtain ⟨q, hq, hzq⟩ := RuChoice.sylow_mod hQ2 hb5 hcord hbN hker3
  refine ⟨q * s₁, mul_mem (M.toRuDataN.Q_le_T hq) hs₁T, ?_⟩
  rw [hzq]
  congr 1
  simp only [hc]
  group

open CFSG.Quasithin.RuType in
theorem RuChoice.sylow5_gen {G : Type} [Group G] [Finite G] (M : RuDataM G) {B5 : Subgroup G}
    (hB5 : ChIJK.IsSylowIn 5 B5 (ChIJK.HRu (M.T : Subgroup G))) :
    ∃ b : G, b ∈ ruH M.T ∧ orderOf b = 5 ∧ B5 = Subgroup.zpowers b := by
  rw [RuChoice.HRu_eq] at hB5
  obtain ⟨hle, hp, hidx⟩ := hB5
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have h := Subgroup.card_mul_index (B5.subgroupOf (ruH M.T))
  rw [card_subgroupOf_of_le hle, hn, M.toRuData.card_H] at h
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      apply hidx
      rw [pow_zero, one_mul] at h
      rw [h]
      norm_num
    · rfl
    · exfalso
      have h25 : 25 ∣ 2 ^ 11 * 120 := by
        rw [← h]
        exact Dvd.dvd.mul_right ⟨5 ^ n, by ring⟩ _
      norm_num at h25
  subst hn1
  have hcard : Nat.card B5 = 5 := by rw [hn]; norm_num
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B5, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : B5 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hord : orderOf b = 5 := by
    have h1 : orderOf b ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard B5 hbB
      rwa [hcard] at this
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  refine ⟨b, hle hbB, hord, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
    (by rw [Nat.card_zpowers, hord, hcard])).symm

theorem RuChoice.zpowers_conj {G : Type} [Group G] {b x : G}
    (h : Subgroup.zpowers b = Subgroup.zpowers x) (t : G) :
    Subgroup.zpowers (t * b * t⁻¹) = Subgroup.zpowers (t * x * t⁻¹) := by
  have := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) h
  simpa [MonoidHom.map_zpowers, MulAut.conj_apply] using this

open CFSG.Quasithin.RuType in
theorem RuChoice.plane :
    ∀ l ∈ SL3.Pl, natAct3 l SL3.e0 ≠ SL3.e0 →
      ∃ p ∈ SL3.P0, natAct3 p⁻¹ ![0, 1, 0] = natAct3 l SL3.e0 := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.B5_proof {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {g : G} (hg : g ∈ L2Ru M.L V2) (hgH : g ∉ HRu (M.T : Subgroup G))
    {v : G} (hv : v ∈ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g)
    (hvQ : v ∉ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g ⊓ QRu (M.T : Subgroup G))
    {B5 : Subgroup G} (hB5 : IsSylowIn 5 B5 (HRu (M.T : Subgroup G))) (hinv : InvertsGroup v B5) :
    ∃ t : G, t ∈ (M.T : Subgroup G) ∧ B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t := by
  obtain ⟨b, hbH, hb5, rfl⟩ := RuChoice.sylow5_gen M hB5
  have hgG2 : g ∈ M.G2 := by
    rw [RuChoice.L2Ru_eq M hV2] at hg
    exact RuChoice.twoResidual_le _ hg
  obtain ⟨hgL, hgPl⟩ := mem_pullL.mp hgG2
  rw [RuChoice.HRu_eq] at hgH
  have hθ : M.θ ⟨g, hgL⟩ ∉ SL3.Stab0 := by
    intro h
    apply hgH
    have : g ∈ M.LT1 := mem_pullL.mpr ⟨hgL, h⟩
    rw [← M.L_inf_H] at this
    exact this.2
  have hlL : g⁻¹ ∈ M.L := inv_mem hgL
  have hθl : M.θ ⟨g⁻¹, hlL⟩ = (M.θ ⟨g, hgL⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hlPl : M.θ ⟨g⁻¹, hlL⟩ ∈ SL3.Pl := by
    rw [hθl]
    exact inv_mem hgPl
  have hlSt : natAct3 (M.θ ⟨g⁻¹, hlL⟩) SL3.e0 ≠ SL3.e0 := by
    intro h
    apply hθ
    have h1 : M.θ ⟨g⁻¹, hlL⟩ ∈ SL3.Stab0 := h
    rw [hθl] at h1
    have := SL3.Stab0.inv_mem h1
    rwa [inv_inv] at this
  obtain ⟨p, hp0, hpe⟩ := RuChoice.plane _ hlPl hlSt
  obtain ⟨t', ht'L, ht'T, hθt'⟩ := RuChoice.exists_T_of_P0 M hp0
  have ht'H : t' ∈ ruH M.T := M.toRuData.T_le_H ht'T
  have hl'L : t'⁻¹ * (M.gel : G) ∈ M.L := mul_mem (inv_mem ht'L) M.gel.2
  have hcu : M.conjU g⁻¹ = M.conjU (t'⁻¹ * (M.gel : G)) := by
    refine (M.conjU_eq_conjU_iff ⟨g⁻¹, hlL⟩ ⟨t'⁻¹ * (M.gel : G), hl'L⟩).mpr ?_
    have e : (⟨t'⁻¹ * (M.gel : G), hl'L⟩ : M.L) = (⟨t', ht'L⟩ : M.L)⁻¹ * M.gel := rfl
    rw [e, map_mul, map_inv, hθt', M.θ_gel, SL3.natAct3_mul, SL3.natAct3_gpl_e0, ← hpe]
  have hv' : v ∈ M.conjU g⁻¹ := by
    rw [← RuChoice.conjugate_U_eq]
    exact hv
  rw [hcu] at hv'
  have hv1 := M.mem_conjU.mp hv'
  have hvU : t' * v * t'⁻¹ ∈ M.Ual := by
    show t' * v * t'⁻¹ ∈ M.conjU (M.gel : G)
    rw [M.mem_conjU]
    have e : (M.gel : G)⁻¹ * (t' * v * t'⁻¹) * (M.gel : G) =
        (t'⁻¹ * (M.gel : G))⁻¹ * v * (t'⁻¹ * (M.gel : G)) := by group
    rw [e]
    exact hv1
  have hvQ' : v ∉ ruQ M.T := by
    intro h
    apply hvQ
    rw [RuChoice.QRu_eq]
    exact Subgroup.mem_inf.mpr ⟨hv, h⟩
  have hvQ'' : t' * v * t'⁻¹ ∉ ruQ M.T := by
    intro h
    apply hvQ'
    have := M.conj_mem_Q (inv_mem ht'H) h
    simpa [mul_assoc] using this
  have hvb : v * b * v⁻¹ = b⁻¹ := by
    have h1 := hinv.2 b (Subgroup.mem_zpowers b)
    have h2 : v⁻¹ * b⁻¹ * v = b := by
      have := congrArg (fun x => x⁻¹) h1
      simpa [mul_assoc] using this
    calc v * b * v⁻¹ = v * (v⁻¹ * b⁻¹ * v) * v⁻¹ := by rw [h2]
      _ = b⁻¹ := by group
  have hb'H : t' * b * t'⁻¹ ∈ ruH M.T := mul_mem (mul_mem ht'H hbH) (inv_mem ht'H)
  have hb'5 : orderOf (t' * b * t'⁻¹) = 5 := by
    rw [CFSG.Quasithin.RuType.orderOf_conj_eq]
    exact hb5
  have hinv' : (t' * v * t'⁻¹) * (t' * b * t'⁻¹) * (t' * v * t'⁻¹)⁻¹ = (t' * b * t'⁻¹)⁻¹ := by
    calc (t' * v * t'⁻¹) * (t' * b * t'⁻¹) * (t' * v * t'⁻¹)⁻¹ = t' * (v * b * v⁻¹) * t'⁻¹ := by
          group
      _ = t' * b⁻¹ * t'⁻¹ := by rw [hvb]
      _ = (t' * b * t'⁻¹)⁻¹ := by group
  obtain ⟨s, hsT, hz⟩ := RuChoice.B5_core M hvU hvQ'' hb'H hb'5 hinv'
  refine ⟨s⁻¹ * t', mul_mem (inv_mem hsT) ht'T, ?_⟩
  have h3 := RuChoice.zpowers_conj hz t'⁻¹
  have e1 : t'⁻¹ * (t' * b * t'⁻¹) * t'⁻¹⁻¹ = b := by group
  rw [e1] at h3
  rw [h3]
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.B5 {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {g : G} (hg : g ∈ L2Ru M.L V2) (hgH : g ∉ HRu (M.T : Subgroup G))
    {v : G} (hv : v ∈ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g)
    (hvQ : v ∉ CFSG.conjugate (URu (ruV M.L) (M.T : Subgroup G)) g ⊓ QRu (M.T : Subgroup G))
    {B5 : Subgroup G} (hB5 : IsSylowIn 5 B5 (HRu (M.T : Subgroup G))) (hinv : InvertsGroup v B5) :
    ∃ t : G, t ∈ (M.T : Subgroup G) ∧ B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t :=
  RuChoice.B5_proof M hV2 hg hgH hv hvQ hB5 hinv

open CFSG.Quasithin.RuType in
open scoped commutatorElement in
theorem RuChoice.Q5_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {b : G}
    (hbH : b ∈ ruH M.T) :
    M.Q5 hbH = ⁅ruQ M.T, Subgroup.zpowers b⁆ ⊔ ruU M.L M.T := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxQ, a', ha'⟩ := (M.mem_Q5 hbH).mp hx
    induction a' using QuotientGroup.induction_on with
    | H a =>
    have ha'' : M.dQ ⟨b, hbH⟩ (a : M.Qbar) = ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) := ha'
    rw [M.dQ_apply, M.actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      M.mk_eq_mk_iff] at ha''
    have hc : ((M.conjQ ⟨b, hbH⟩ a * a⁻¹ : ruQ M.T) : G) = b * a * b⁻¹ * (a : G)⁻¹ := rfl
    rw [hc] at ha''
    have e : x = (b * a * b⁻¹ * (a : G)⁻¹) * ((b * a * b⁻¹ * (a : G)⁻¹)⁻¹ * x) := by group
    rw [e]
    refine Subgroup.mul_mem_sup ?_ ha''
    have h1 : ⁅(a : G), b⁆ ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_zpowers b)
    have h2 := inv_mem h1
    have e2 : b * a * b⁻¹ * (a : G)⁻¹ = ⁅(a : G), b⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact h2
  · refine sup_le ?_ (M.U_le_Q5 hbH)
    rw [Subgroup.commutator_le]
    intro q hq y hy
    have hyp : y ∈ Submonoid.powers b := (mem_powers_iff_mem_zpowers).mpr hy
    obtain ⟨j, rfl⟩ := hyp
    have hbj : b ^ j ∈ ruH M.T := pow_mem hbH j
    have hQ : ⁅q, b ^ j⁆ ∈ ruQ M.T := by
      have h1 := M.conj_mem_Q hbj (inv_mem hq)
      have e : ⁅q, b ^ j⁆ = q * (b ^ j * q⁻¹ * (b ^ j)⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hq h1
    refine (M.mem_Q5 hbH).mpr ⟨hQ, ?_⟩
    have key : ((⟨⁅q, b ^ j⁆, hQ⟩ : ruQ M.T) : M.Qbar) =
        (M.dQ (⟨b, hbH⟩ ^ j) ((⟨q, hq⟩ : ruQ M.T) : M.Qbar))⁻¹ := by
      rw [M.dQ_apply, M.actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv]
      congr 1
      apply Subtype.ext
      show ⁅q, b ^ j⁆ = (((b ^ j : G) * q * (b ^ j : G)⁻¹) * q⁻¹)⁻¹
      simp only [commutatorElement_def]
      group
    rw [key]
    exact inv_mem (M.dQ_pow_range_le ⟨b, hbH⟩ j ⟨_, rfl⟩)

theorem RuChoice.map_conj_eq {G : Type} [Group G] (A : Subgroup G) (c : G)
    (h : ∀ x ∈ A, c * x * c⁻¹ ∈ A) (h' : ∀ x ∈ A, c⁻¹ * x * c ∈ A) :
    A.map (MulAut.conj c).toMonoidHom = A := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have := h _ hx
    simpa [mul_assoc] using this
  · intro hx
    exact h' x hx

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.Q5_proof {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) :
    Q5Ru (M.T : Subgroup G) B5 ⊔ URu (ruV M.L) (M.T : Subgroup G) =
      CFSG.conjugate (M.Q5 M.b5el_mem_H) t := by
  have htH : t ∈ ruH M.T := M.toRuData.T_le_H ht
  have hQ : (ruQ M.T).map (MulAut.conj t⁻¹).toMonoidHom = ruQ M.T :=
    RuChoice.map_conj_eq _ _ (fun x hx => M.conj_mem_Q (inv_mem htH) hx)
      (fun x hx => by simpa using M.conj_mem_Q htH hx)
  have hU : (ruU M.L M.T).map (MulAut.conj t⁻¹).toMonoidHom = ruU M.L M.T :=
    RuChoice.map_conj_eq _ _ (fun x hx => M.conj_mem_U (inv_mem htH) hx)
      (fun x hx => by simpa using M.conj_mem_U htH hx)
  rw [RuChoice.Q5_eq M M.b5el_mem_H]
  unfold Q5Ru CFSG.conjugate
  rw [hB, RuChoice.QRu_eq, RuChoice.URu_eq, Subgroup.map_sup, Subgroup.map_commutator,
    hQ, hU]
  unfold CFSG.conjugate
  rfl

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.Q5 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) :
    Q5Ru (M.T : Subgroup G) B5 ⊔ URu (ruV M.L) (M.T : Subgroup G) =
      CFSG.conjugate (M.Q5 M.b5el_mem_H) t :=
  RuChoice.Q5_proof M ht hB

theorem RuChoice.mem_normalizer {G : Type} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := (MulAut.conj g).injective hyx
  rwa [← this]

theorem RuChoice.conjugate_sup {G : Type} [Group G] (A B : Subgroup G) (t : G) :
    CFSG.conjugate (A ⊔ B) t = CFSG.conjugate A t ⊔ CFSG.conjugate B t := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem RuChoice.conjugate_inf {G : Type} [Group G] (A B : Subgroup G) (t : G) :
    CFSG.conjugate (A ⊓ B) t = CFSG.conjugate A t ⊓ CFSG.conjugate B t := by
  unfold CFSG.conjugate
  exact Subgroup.map_inf _ _ _ (MulAut.conj t⁻¹).injective

theorem RuChoice.conjugate_zpowers {G : Type} [Group G] (x t : G) :
    CFSG.conjugate (Subgroup.zpowers x) t = Subgroup.zpowers (t⁻¹ * x * t) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem RuChoice.conjugate_eq_self {G : Type} [Group G] {A : Subgroup G} {t : G}
    (h : ∀ x ∈ A, t * x * t⁻¹ ∈ A) (h' : ∀ x ∈ A, t⁻¹ * x * t ∈ A) :
    CFSG.conjugate A t = A := by
  unfold CFSG.conjugate
  exact RuChoice.map_conj_eq A t⁻¹ (fun x hx => by simpa using h' x hx)
    (fun x hx => by simpa using h x hx)

theorem RuChoice.mem_conjugate {G : Type} [Group G] {A : Subgroup G} {t x : G} :
    x ∈ CFSG.conjugate A t ↔ t * x * t⁻¹ ∈ A := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

open scoped Pointwise in
open CFSG.Quasithin.RuType in
theorem RuChoice.Q5W_inf_R2
    {G : Type} [Group G] [Finite G] (M : CFSG.Quasithin.RuType.RuDataM G) :
    (M.Q5 M.b5el_mem_H ⊔ M.W) ⊓ M.R2 = Subgroup.zpowers M.ael ⊔ M.W := by
  apply le_antisymm
  · rintro x ⟨hx1, hxR⟩
    have hQT : M.Q5 M.b5el_mem_H ≤ (M.T : Subgroup G) :=
      (M.Q5_le_Q _).trans M.toRuDataN.Q_le_T
    have hnorm : M.Q5 M.b5el_mem_H ≤ Subgroup.normalizer (M.W : Set G) := fun p hp =>
      RuChoice.mem_normalizer fun w hw => M.conj_mem_W (M.T_le_G2 (hQT hp)) hw
    have hset : ((M.Q5 M.b5el_mem_H ⊔ M.W : Subgroup G) : Set G) =
        ((M.Q5 M.b5el_mem_H : Subgroup G) : Set G) * ((M.W : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
    have hx1' : x ∈ ((M.Q5 M.b5el_mem_H : Subgroup G) : Set G) * ((M.W : Subgroup G) : Set G) := by
      rw [← hset]
      exact hx1
    obtain ⟨p, hp, w, hw, rfl⟩ := Set.mem_mul.mp hx1'
    have hpL := M.Q5_le_L _ hp
    have hwS : w ∈ ruS M.L := M.W_le_S hw
    have hwL : w ∈ M.L := M.toRuData.S_le_L hwS
    have hwθ : M.θ ⟨w, hwL⟩ = 1 := (M.mem_S_iff_θ hwL).mp hwS
    have hθR0 : M.θ ⟨p, hpL⟩ ∈ SL3.R0 := by
      rw [← M.θQ_eq]
      exact ⟨⟨p, hpL⟩, Subgroup.mem_subgroupOf.mpr (M.Q5_le_Q _ hp), rfl⟩
    have hxL : p * w ∈ M.L := mul_mem hpL hwL
    have hθx : M.θ ⟨p * w, hxL⟩ = M.θ ⟨p, hpL⟩ := by
      have : (⟨p * w, hxL⟩ : M.L) = ⟨p, hpL⟩ * ⟨w, hwL⟩ := rfl
      rw [this, map_mul, hwθ, mul_one]
    have hθR2 : M.θ ⟨p, hpL⟩ ∈ SL3.R2m := by
      rw [← hθx]
      exact (mem_pullL.mp hxR).2
    have key : ∀ c ∈ M.Q5 M.b5el_mem_H, ∀ hc : c ∈ M.L, M.θ ⟨c, hc⟩ = M.θ ⟨p, hpL⟩ →
        c⁻¹ * p ∈ M.W := by
      intro c hc hcL hθc
      refine M.Q5_inf_S_le_W (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hc) hp, ?_⟩)
      rw [M.mem_S_iff_θ (mul_mem (inv_mem hcL) hpL)]
      have e : (⟨c⁻¹ * p, mul_mem (inv_mem hcL) hpL⟩ : M.L) = (⟨c, hcL⟩ : M.L)⁻¹ * ⟨p, hpL⟩ := rfl
      rw [e, map_mul, map_inv, hθc, inv_mul_cancel]
    rcases CFSG.Quasithin.RuType.SL3.R0_elems _ hθR0 with h | h | h | h
    ·
      have hpS : p ∈ ruS M.L := (M.mem_S_iff_θ hpL).mpr h
      have hpW : p ∈ M.W := M.Q5_inf_S_le_W (Subgroup.mem_inf.mpr ⟨hp, hpS⟩)
      exact Subgroup.mem_sup_right (mul_mem hpW hw)
    ·
      have h1 := key M.ael M.ael_mem_Q5 M.ael_mem_L (by rw [M.θ_ael, h])
      have e : p * w = M.ael * ((M.ael⁻¹ * p) * w) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) (mul_mem h1 hw)
    · exfalso
      rw [h] at hθR2
      exact CFSG.Quasithin.RuType.SL3.rr_not_mem_R2m hθR2
    · exfalso
      rw [h] at hθR2
      have hz : CFSG.Quasithin.RuType.SL3.zP0 ∈ CFSG.Quasithin.RuType.SL3.R2m :=
        CFSG.Quasithin.RuType.SL3.zP0_mem_R2m
      have := mul_mem hθR2 (inv_mem hz)
      rw [mul_inv_cancel_right] at this
      exact CFSG.Quasithin.RuType.SL3.rr_not_mem_R2m this
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left M.ael_mem_Q5, M.ael_mem_R2⟩
    · exact le_inf le_sup_right (M.W_le_S.trans M.S_le_R2)

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.A_proof {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a = M.Agrp := by
  obtain ⟨hG2, hR2, hS2⟩ := RuChoice.frame M hV2
  have htG : t ∈ M.G2 := M.T_le_G2 ht
  have htiG : t⁻¹ ∈ M.G2 := inv_mem htG
  have hWfix : ∀ g ∈ M.G2, CFSG.conjugate M.W g = M.W := fun g hg =>
    RuChoice.conjugate_eq_self (fun x hx => M.conj_mem_W hg hx)
      (fun x hx => by simpa using M.conj_mem_W (inv_mem hg) hx)
  have hR2fix : CFSG.conjugate M.R2 t = M.R2 :=
    RuChoice.conjugate_eq_self (fun x hx => M.conj_mem_R2 htG hx)
      (fun x hx => by simpa using M.conj_mem_R2 htiG hx)
  have hQ5 := RuChoice.Q5 M ht hB
  rw [RuChoice.URu_eq] at hQ5
  have hQW : Q5Ru (M.T : Subgroup G) B5 ⊔ M.W =
      CFSG.conjugate (M.Q5 M.b5el_mem_H ⊔ M.W) t := by
    rw [RuChoice.conjugate_sup, hWfix t htG, ← hQ5, sup_assoc,
      sup_eq_right.mpr M.U_le_W]
  set c : G := t⁻¹ * M.ael * t with hc
  have hIn : (Q5Ru (M.T : Subgroup G) B5 ⊔ M.W) ⊓ M.R2 = Subgroup.zpowers c ⊔ M.W := by
    rw [hQW]
    conv_lhs => rw [← hR2fix]
    rw [← RuChoice.conjugate_inf, RuChoice.Q5W_inf_R2, RuChoice.conjugate_sup,
      hWfix t htG, RuChoice.conjugate_zpowers]
  obtain ⟨ha1, -, -, -⟩ := ha
  rw [hS2, hR2] at ha1
  have hac : Subgroup.zpowers a ⊔ M.W = Subgroup.zpowers c ⊔ M.W := ha1.symm.trans hIn
  have hcA : c ∈ M.Agrp := by
    have := M.conj_mem_Agrp htiG M.ael_mem_Agrp
    simpa [hc] using this
  have haA : a ∈ M.Agrp := by
    have h1 : a ∈ Subgroup.zpowers a ⊔ M.W := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    rw [hac] at h1
    exact (sup_le (Subgroup.zpowers_le.mpr hcA) M.W_le_Agrp) h1
  unfold ARu
  rw [hG2, hS2]
  apply le_antisymm
  · refine sup_le ?_ M.W_le_Agrp
    unfold conjClosure
    refine iSup₂_le fun y hy => ?_
    intro z hz
    rw [RuChoice.mem_conjugate] at hz
    have h1 : y * z * y⁻¹ ∈ M.Agrp := (Subgroup.zpowers_le.mpr haA) hz
    have := M.conj_mem_Agrp (inv_mem hy) h1
    simpa [mul_assoc] using this
  · set Z : Subgroup G := conjClosure (Subgroup.zpowers a) M.G2 ⊔ M.W with hZ
    have hWZ : M.W ≤ Z := le_sup_right
    have hconjZ : ∀ g ∈ M.G2, g * M.ael * g⁻¹ ∈ Z := by
      intro g hg
      have hy : (g * t)⁻¹ ∈ M.G2 := inv_mem (mul_mem hg htG)
      have hmem : g * M.ael * g⁻¹ ∈ CFSG.conjugate (Subgroup.zpowers a ⊔ M.W) (g * t)⁻¹ := by
        rw [RuChoice.mem_conjugate, hac]
        refine Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨1, ?_⟩)
        simp only [hc, zpow_one]
        group
      rw [RuChoice.conjugate_sup, hWfix _ hy] at hmem
      have hle : CFSG.conjugate (Subgroup.zpowers a) (g * t)⁻¹ ≤
          conjClosure (Subgroup.zpowers a) M.G2 :=
        le_iSup₂ (f := fun y (_ : y ∈ M.G2) => CFSG.conjugate (Subgroup.zpowers a) y)
          (g * t)⁻¹ hy
      exact (sup_le_sup_right hle _) hmem
    have c0 : M.cak 0 ∈ Z := by
      rw [M.cak_zero]
      simpa using hconjZ 1 (one_mem _)
    have c1 : M.cak 1 ∈ Z := by
      have := hconjZ (M.xel : G) M.xel_mem_G2
      simpa [CFSG.Quasithin.RuType.RuDataM.cak] using this
    intro x hx
    obtain ⟨-, h | h | h | h⟩ := M.mem_Agrp_iff.mp hx
    · exact hWZ h
    · have e : x = M.cak 0 * ((M.cak 0)⁻¹ * x) := by group
      rw [e]
      exact mul_mem c0 (hWZ h)
    · have e : x = M.cak 1 * ((M.cak 1)⁻¹ * x) := by group
      rw [e]
      exact mul_mem c1 (hWZ h)
    · have e : x = (M.cak 0 * M.cak 1) * ((M.cak 0 * M.cak 1)⁻¹ * x) := by group
      rw [e]
      exact mul_mem (mul_mem c0 c1) (hWZ h)

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.TF_F1_proof {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF t ∧
      F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 t := by
  have hA := RuChoice.A_proof M hV2 ht hB ha
  have htG : t ∈ M.G2 := M.T_le_G2 ht
  have htiG : t⁻¹ ∈ M.G2 := inv_mem htG
  have hQ5 := RuChoice.Q5 M ht hB
  rw [RuChoice.URu_eq] at hQ5
  have hAfix : CFSG.conjugate M.Agrp t = M.Agrp :=
    RuChoice.conjugate_eq_self (fun x hx => M.conj_mem_Agrp htG hx)
      (fun x hx => by simpa using M.conj_mem_Agrp htiG hx)
  have hUA : ruU M.L M.T ≤ M.Agrp := M.U_le_W.trans M.W_le_Agrp
  have hTF : TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF t := by
    unfold TFRu
    rw [hA]
    show M.Agrp ⊔ Q5Ru (M.T : Subgroup G) B5 = CFSG.conjugate (M.Agrp ⊔ M.Q5 M.b5el_mem_H) t
    rw [RuChoice.conjugate_sup, hAfix, ← hQ5]
    exact le_antisymm (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
      (sup_le le_sup_left (sup_le le_sup_right (hUA.trans le_sup_left)))
  refine ⟨hTF, ?_⟩
  unfold F1Ru
  rw [hTF, hB, ← RuChoice.conjugate_sup]
  congr 1
  show M.Agrp ⊔ M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el =
    M.Agrp ⊔ (M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el)
  rw [sup_assoc]

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.A {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a = M.Agrp :=
  RuChoice.A_proof M hV2 ht hB ha

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.TF_F1 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a) :
    TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF t ∧
      F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 t :=
  RuChoice.TF_F1_proof M hV2 ht hB ha

theorem RuChoice.fx_mem_conjugate {G : Type*} [Group G] {H : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate H g ↔ g * y * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_apply]

theorem RuChoice.fx_conjugate_conjugate {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate A g) h = CFSG.conjugate A (g * h) := by
  ext y
  rw [RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate]
  have : g * (h * y * h⁻¹) * g⁻¹ = (g * h) * y * (g * h)⁻¹ := by group
  rw [this]

theorem RuChoice.fx_conjugate_one {G : Type*} [Group G] (A : Subgroup G) :
    CFSG.conjugate A 1 = A := by
  ext y
  rw [RuChoice.fx_mem_conjugate]
  simp

theorem RuChoice.fx_card_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate A g) = Nat.card A := by
  unfold CFSG.conjugate
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem RuChoice.fx_conjugate_le {G : Type*} [Group G] {A N : Subgroup G} {g : G} (hA : A ≤ N)
    (hg : g ∈ N) : CFSG.conjugate A g ≤ N := by
  intro y hy
  rw [RuChoice.fx_mem_conjugate] at hy
  have h1 := N.mul_mem (N.mul_mem (N.inv_mem hg) (hA hy)) hg
  simpa [mul_assoc] using h1

theorem RuChoice.fx_conjugate_mono {G : Type*} [Group G] {A B : Subgroup G} (g : G)
    (h : A ≤ B) : CFSG.conjugate A g ≤ CFSG.conjugate B g := by
  intro y hy
  rw [RuChoice.fx_mem_conjugate] at hy ⊢
  exact h hy

theorem RuChoice.fx_normalizer_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (Subgroup.normalizer (A : Set G)) g := by
  ext y
  rw [RuChoice.fx_mem_conjugate, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have := h (g⁻¹ * a * g)
    rw [RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate] at this
    have e : g * (y * (g⁻¹ * a * g) * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ := by group
    simpa [e, mul_assoc] using this
  · intro h a
    rw [RuChoice.fx_mem_conjugate, RuChoice.fx_mem_conjugate]
    have := h (g * a * g⁻¹)
    have e : g * (y * a * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact this

theorem RuChoice.fx_conjugate_sup {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem RuChoice.fx_conjugate_eq_self {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : CFSG.conjugate A g = A := by
  ext y
  rw [RuChoice.fx_mem_conjugate]
  exact (Subgroup.mem_normalizer_iff.mp hg y).symm

theorem RuChoice.fx_conjugate_zpowers {G : Type*} [Group G] (x g : G) :
    CFSG.conjugate (Subgroup.zpowers x) g = Subgroup.zpowers (g⁻¹ * x * g) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem RuChoice.fx_mem_normalizer {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (h1 : ∀ y ∈ K, g * y * g⁻¹ ∈ K) (h2 : ∀ y ∈ K, g⁻¹ * y * g ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h1 y
  · intro hy
    have := h2 _ hy
    simpa [mul_assoc] using this

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_G2_factor {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {g : G} (hg : g ∈ M.G2) :
    ∃ t ∈ (M.T : Subgroup G), ∃ x ∈ Subgroup.zpowers M.x2el, g = t * x := by
  classical
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  have hX0 : Nat.card (Subgroup.zpowers M.x2el) = 3 := by
    rw [Nat.card_zpowers, M.orderOf_x2el]
  have hinf : ∀ y : G, y ∈ (M.T : Subgroup G) → y ∈ Subgroup.zpowers M.x2el → y = 1 := by
    intro y hyT hyX
    have h1 : orderOf y ∣ 2 ^ 14 := by
      have := Subgroup.orderOf_dvd_natCard _ hyT
      rwa [hT] at this
    have h2 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard _ hyX
      rwa [hX0] at this
    have hd := Nat.dvd_gcd h1 h2
    have : Nat.gcd (2 ^ 14) 3 = 1 := by norm_num
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hXG : Subgroup.zpowers M.x2el ≤ M.G2 := (Subgroup.zpowers_le).mpr M.x2el_mem_G2
  let f : ↥(M.T : Subgroup G) × ↥(Subgroup.zpowers M.x2el) → ↥M.G2 := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem (M.T_le_G2 p.1.2) (hXG p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨t, ht⟩, ⟨x, hx⟩⟩ ⟨⟨t', ht'⟩, ⟨x', hx'⟩⟩ h
    have h' : t * x = t' * x' := congrArg Subtype.val h
    have h1 : t'⁻¹ * t = x' * x⁻¹ := by
      have : t'⁻¹ * (t * x) * x⁻¹ = t'⁻¹ * (t' * x') * x⁻¹ := by rw [h']
      simpa [mul_assoc] using this
    have hA : t'⁻¹ * t ∈ (M.T : Subgroup G) := mul_mem (inv_mem ht') ht
    have hB : x' * x⁻¹ ∈ Subgroup.zpowers M.x2el := mul_mem hx' (inv_mem hx)
    have h2 : t'⁻¹ * t = 1 := hinf _ hA (h1 ▸ hB)
    have h3 : t = t' := by
      have := congrArg (fun y => t' * y) h2
      simpa using this
    subst h3
    have h4 : x = x' := mul_left_cancel h'
    subst h4
    rfl
  have hcard : Nat.card ↥M.G2 ≤ Nat.card (↥(M.T : Subgroup G) × ↥(Subgroup.zpowers M.x2el)) := by
    rw [Nat.card_prod, hT, hX0, M.card_G2]
    norm_num
  obtain ⟨⟨t, x⟩, h⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨g, hg⟩
  exact ⟨t, t.2, x, x.2, (congrArg Subtype.val h).symm⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_exists_conj {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {X : Subgroup G} (hX : CFSG.ASVolI.ChIJK.IsSylowIn 3 X M.G2) :
    ∃ s ∈ (M.T : Subgroup G), X = CFSG.conjugate (Subgroup.zpowers M.x2el) s := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXG, hXp, hidx⟩ := hX
  have hG2 : Nat.card M.G2 = 2 ^ 14 * 3 := by rw [M.card_G2]; norm_num
  have hXcard : Nat.card X = 3 := by
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    have h := Subgroup.index_mul_card (X.subgroupOf M.G2)
    rw [card_subgroupOf_of_le hXG, hn, hG2] at h
    have hn1 : n = 1 := by
      rcases n with _ | _ | n
      · exfalso
        rw [pow_zero, mul_one] at h
        apply hidx
        rw [h]
        norm_num
      · rfl
      · exfalso
        have h9 : 9 ∣ (X.subgroupOf M.G2).index * 3 ^ (n + 2) :=
          Dvd.dvd.mul_left (by
            rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
            exact pow_dvd_pow 3 (by omega)) _
        rw [h] at h9
        norm_num at h9
    rw [hn1, pow_one] at hn
    exact hn
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hXcard])
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
  have hXz : Subgroup.zpowers (y : G) = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2) (by
      rw [hXcard, Nat.card_zpowers, hy3])
  have hK : ¬ 3 ^ 2 ∣ Nat.card M.G2 := by
    rw [hG2]
    norm_num
  obtain ⟨g, hgG, hyg⟩ := exists_conj_zpowers hK M.x2el_mem_G2 (hXG y.2) M.orderOf_x2el hy3
  have hz3 : (g * M.x2el * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, M.x2el_pow_three]
    group
  have hz1 : g * M.x2el * g⁻¹ ≠ 1 := by
    intro h1
    have : M.x2el = 1 := by
      calc M.x2el = g⁻¹ * (g * M.x2el * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have h3 := M.orderOf_x2el
    rw [this, orderOf_one] at h3
    norm_num at h3
  have hz : orderOf (g * M.x2el * g⁻¹) = 3 := orderOf_eq_prime hz3 hz1
  have hXeq : X = Subgroup.zpowers (g * M.x2el * g⁻¹) := by
    rw [← hXz]
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hyg) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hz, hy3]
  obtain ⟨t, htT, x', hx', rfl⟩ := RuChoice.fx_G2_factor M hgG
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
  refine ⟨t⁻¹, inv_mem htT, ?_⟩
  rw [RuChoice.fx_conjugate_zpowers, hXeq]
  congr 1
  group

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem RuChoice.fx_comm_isM2 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {l σ : G} (hl : l ∈ M.L) (hσS : σ ∈ ruS M.L)
    (hW : σ * l * σ⁻¹ * l⁻¹ ∈ M.W) :
    SL3.IsM2 (stAct (M.θ ⟨l, hl⟩) (Multiplicative.toAdd (M.χ ⟨σ, hσS⟩)) +
      Multiplicative.toAdd (M.χ ⟨σ, hσS⟩)) := by
  have hlσ : l * σ⁻¹ * l⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hl) σ⁻¹).mp (inv_mem hσS)
  obtain ⟨hcS, hM2⟩ := hW
  have hsplit : (⟨σ * l * σ⁻¹ * l⁻¹, hcS⟩ : ruS M.L) =
      (⟨σ, hσS⟩ : ruS M.L) * ⟨l * σ⁻¹ * l⁻¹, hlσ⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have hχ : Multiplicative.toAdd (M.χ ⟨l * σ⁻¹ * l⁻¹, hlσ⟩) =
      stAct (M.θ ⟨l, hl⟩) (Multiplicative.toAdd (M.χ ⟨σ, hσS⟩)) := by
    have h := M.χ_conj ⟨l, hl⟩ ⟨σ⁻¹, inv_mem hσS⟩
    have h2 : Multiplicative.toAdd (M.χ ⟨σ⁻¹, inv_mem hσS⟩) =
        Multiplicative.toAdd (M.χ ⟨σ, hσS⟩) := M.toAdd_χ_inv ⟨σ, hσS⟩
    rw [h2] at h
    exact h
  rw [hsplit, M.toAdd_χ_mul, hχ] at hM2
  rw [add_comm]
  exact hM2

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem RuChoice.fx_mem_W_of_normalizes {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {σ : G} (hσS : σ ∈ ruS M.L)
    (hσN : σ ∈ Subgroup.normalizer (M.XA : Set G)) : σ ∈ M.W := by
  have hxL : M.x2el ∈ M.L := M.x2el_mem_L
  have hxXA : M.x2el ∈ M.XA := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have h1 : σ * M.x2el * σ⁻¹ ∈ M.XA := (Subgroup.mem_normalizer_iff.mp hσN _).mp hxXA
  have hc : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ M.XA := mul_mem h1 (inv_mem hxXA)
  have hxσ : M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hxL) σ⁻¹).mp (inv_mem hσS)
  have hcS : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ ruS M.L := by
    have e : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ = σ * (M.x2el * σ⁻¹ * M.x2el⁻¹) := by group
    rw [e]
    exact mul_mem hσS hxσ
  have hcW : σ * M.x2el * σ⁻¹ * M.x2el⁻¹ ∈ M.W := by
    rw [← M.F2_inf_S]
    refine ⟨?_, hcS⟩
    rw [M.F2_eq]
    exact Subgroup.mem_sup_right hc
  have h := RuChoice.fx_comm_isM2 M hxL hσS hcW
  rw [M.θ_x2el] at h
  exact ⟨hσS, SL3.x0_fpf_M2 _ (M.χ_trace _) h⟩

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_inf_normalizer_XA {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.XA : Set G) = M.TF := by
  set N := (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.XA : Set G) with hN
  have hTFN : M.TF ≤ N := le_inf M.TF_le_T M.TF_le_normalizer_XA
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  have hR2A : M.R2 ⊓ N ≤ M.Agrp := by
    rintro r ⟨hrR, hrN⟩
    obtain ⟨hrL, hrP⟩ := mem_pullL.mp hrR
    obtain ⟨y, hyA, hyL, hθ⟩ := M.exists_Agrp_θ hrP
    have hσL : y⁻¹ * r ∈ M.L := mul_mem (inv_mem hyL) hrL
    have hσS : y⁻¹ * r ∈ ruS M.L := by
      rw [M.mem_S_iff_θ hσL]
      have e : (⟨y⁻¹ * r, hσL⟩ : M.L) = (⟨y, hyL⟩ : M.L)⁻¹ * ⟨r, hrL⟩ := rfl
      rw [e, map_mul, map_inv, hθ, inv_mul_cancel]
    have hyN : y ∈ Subgroup.normalizer (M.XA : Set G) :=
      Subgroup.le_normalizer (M.Agrp_le_XA hyA)
    have hσN : y⁻¹ * r ∈ Subgroup.normalizer (M.XA : Set G) :=
      mul_mem (inv_mem hyN) (Subgroup.mem_inf.mp hrN).2
    have hσW := RuChoice.fx_mem_W_of_normalizes M hσS hσN
    have e : r = y * (y⁻¹ * r) := by group
    rw [e]
    exact mul_mem hyA (M.W_le_Agrp hσW)
  have hc1 : Nat.card ↥(M.R2 ⊓ N) ≤ 2 ^ 11 := by
    have := Subgroup.card_le_of_le hR2A
    rwa [M.card_Agrp] at this
  have hNT : N ≤ (M.T : Subgroup G) := inf_le_left
  have hrel : M.R2.relIndex N ≤ 2 := by
    have h2 : M.R2.relIndex (M.T : Subgroup G) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := M.R2) (K := (M.T : Subgroup G))
      rw [inf_eq_left.mpr M.R2_le_T, M.card_R2, hT] at h
      have h' : M.R2.relIndex (M.T : Subgroup G) * 2 ^ 13 = 2 * 2 ^ 13 := by
        rw [h]
        norm_num
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
    have h1 : M.R2.relIndex N ≤ M.R2.relIndex (M.T : Subgroup G) :=
      Subgroup.relIndex_le_of_le_right hNT (by rw [h2]; norm_num)
    omega
  have hmul := Subgroup.relIndex_mul_card (H := M.R2) (K := N)
  have hcN : Nat.card N ≤ 2 ^ 12 := by
    rw [← hmul]
    calc M.R2.relIndex N * Nat.card ↥(M.R2 ⊓ N) ≤ 2 * 2 ^ 11 := Nat.mul_le_mul hrel hc1
      _ = 2 ^ 12 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hTFN (by rw [M.card_TF]; exact hcN)).symm

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_F1_inf_T {G : Type} [Group G] [Finite G]
    (M : RuDataM G) : M.F1 ⊓ (M.T : Subgroup G) = M.TF := by
  have hTF : M.TF ≤ M.F1 ⊓ (M.T : Subgroup G) := le_inf M.TF_le_F1 M.TF_le_T
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  obtain ⟨k, -, hcard⟩ := RuDataN.exists_card_eq_two_pow
    (inf_le_right : M.F1 ⊓ (M.T : Subgroup G) ≤ (M.T : Subgroup G)) hT
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left : M.F1 ⊓ (M.T : Subgroup G) ≤ M.F1)
  rw [hcard, M.card_F1] at hdvd
  have hk12 : k ≤ 12 := RuDataN.le_of_two_pow_dvd hdvd (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hTF (by
    rw [hcard, M.card_TF]
    exact Nat.pow_le_pow_right (by norm_num) hk12)).symm

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_Q_le_normalizer_F1 {G : Type} [Group G]
    [Finite G] (M : RuDataM G) : ruQ M.T ≤ Subgroup.normalizer (M.F1 : Set G) := by
  intro q hq
  exact RuChoice.fx_mem_normalizer (fun y hy => M.Q_conj_mem_F1 hq hy)
    (fun y hy => by simpa using M.Q_conj_mem_F1 (inv_mem hq) hy)

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_Q_le_normalizer_TF {G : Type} [Group G]
    [Finite G] (M : RuDataM G) : ruQ M.T ≤ Subgroup.normalizer (M.TF : Set G) := by
  intro q hq
  have hqT : q ∈ (M.T : Subgroup G) := M.Q_le_T hq
  have key : ∀ g : G, g ∈ ruQ M.T → ∀ y ∈ M.TF, g * y * g⁻¹ ∈ M.TF := by
    intro g hg y hy
    have hgT : g ∈ (M.T : Subgroup G) := M.Q_le_T hg
    have hyT : y ∈ (M.T : Subgroup G) := M.TF_le_T hy
    rw [← RuChoice.fx_F1_inf_T M]
    exact ⟨M.Q_conj_mem_F1 hg (M.TF_le_F1 hy),
      (M.T : Subgroup G).mul_mem ((M.T : Subgroup G).mul_mem hgT hyT)
        ((M.T : Subgroup G).inv_mem hgT)⟩
  exact RuChoice.fx_mem_normalizer (key q hq) (fun y hy => by simpa using key q⁻¹ (inv_mem hq) y hy)

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_card_Q_sup_TF {G : Type} [Group G]
    [Finite G] (M : RuDataM G) : Nat.card ↥(ruQ M.T ⊔ M.TF) = 2 ^ 13 := by
  have h := card_sup_mul_inf_of_normalizes (RuChoice.fx_Q_le_normalizer_TF M)
  rw [inf_comm, M.TF_inf_Q, M.card_Y, M.toRuData.card_Q, M.card_TF] at h
  have h' : Nat.card ↥(ruQ M.T ⊔ M.TF) * 2 ^ 10 = 2 ^ 13 * 2 ^ 10 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
theorem RuChoice.fx_exists_not_normalizes {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    ∃ σ ∈ (M.T : Subgroup G), σ ∉ Subgroup.normalizer (M.TF : Set G) := by
  let A0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 0, 0; 1, 0, 0]
  have hA0 : IsTraceZero A0 := by decide
  have hA0M : ¬ SL3.IsM2 (stAct SL3.rr A0 + A0) := by decide
  obtain ⟨σ', hσ'⟩ := M.χ_surj A0 hA0
  refine ⟨(σ' : G), M.toRuData.S_le_T σ'.2, fun hσN => hA0M ?_⟩
  have hql : M.qel ∈ M.L := M.qel_mem_L
  have hq : M.qel ∈ M.TF := M.qel_mem_TF
  have h1 : (σ' : G) * M.qel * (σ' : G)⁻¹ ∈ M.TF := (Subgroup.mem_normalizer_iff.mp hσN _).mp hq
  have hc : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ M.TF := mul_mem h1 (inv_mem hq)
  have hlσ : M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hql) _).mp (inv_mem σ'.2)
  have hcS : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ ruS M.L := by
    have e : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ =
        (σ' : G) * (M.qel * (σ' : G)⁻¹ * M.qel⁻¹) := by group
    rw [e]
    exact mul_mem σ'.2 hlσ
  have hcW : (σ' : G) * M.qel * (σ' : G)⁻¹ * M.qel⁻¹ ∈ M.W := by
    rw [← M.F2_inf_S]
    exact ⟨M.TF_le_F2 hc, hcS⟩
  have h := RuChoice.fx_comm_isM2 M hql σ'.2 hcW
  rw [M.θ_qel] at h
  have hA : Multiplicative.toAdd (M.χ ⟨(σ' : G), σ'.2⟩) = A0 := by
    have := congrArg Multiplicative.toAdd hσ'
    simpa using this
  rw [hA] at h
  exact h

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_normalizer_TF_le {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {n : G} (hnT : n ∈ (M.T : Subgroup G))
    (hn : n ∈ Subgroup.normalizer (M.TF : Set G)) : n ∈ Subgroup.normalizer (M.F1 : Set G) := by
  set N' := (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.TF : Set G) with hN'
  have hT : Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
    rw [← M.toRuData.TL_eq, M.toRuData.card_TL]
  have hle : ruQ M.T ⊔ M.TF ≤ N' :=
    sup_le (le_inf M.Q_le_T (RuChoice.fx_Q_le_normalizer_TF M))
      (le_inf M.TF_le_T Subgroup.le_normalizer)
  have hcard : Nat.card N' ≤ 2 ^ 13 := by
    obtain ⟨σ, hσT, hσ⟩ := RuChoice.fx_exists_not_normalizes M
    have hNT : N' ≤ (M.T : Subgroup G) := inf_le_left
    have hne : N'.relIndex (M.T : Subgroup G) ≠ 1 := by
      intro h1
      exact hσ (Subgroup.mem_inf.mp ((Subgroup.relIndex_eq_one.mp h1) hσT)).2
    have hmul := Subgroup.relIndex_mul_card (H := N') (K := (M.T : Subgroup G))
    rw [inf_eq_left.mpr hNT, hT] at hmul
    have hpos : 0 < N'.relIndex (M.T : Subgroup G) :=
      Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hmul; norm_num at hmul)
    have h2 : 2 ≤ N'.relIndex (M.T : Subgroup G) := by omega
    have h3 : 2 * Nat.card N' ≤ 2 ^ 14 := by
      calc 2 * Nat.card N' ≤ N'.relIndex (M.T : Subgroup G) * Nat.card N' :=
            Nat.mul_le_mul_right _ h2
        _ = 2 ^ 14 := hmul
    omega
  have heq : ruQ M.T ⊔ M.TF = N' :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [RuChoice.fx_card_Q_sup_TF M]; exact hcard)
  have hnN' : n ∈ N' := Subgroup.mem_inf.mpr ⟨hnT, hn⟩
  rw [← heq] at hnN'
  have hle2 : ruQ M.T ⊔ M.TF ≤ Subgroup.normalizer (M.F1 : Set G) :=
    sup_le (RuChoice.fx_Q_le_normalizer_F1 M) (M.TF_le_F1.trans Subgroup.le_normalizer)
  exact hle2 hnN'

open CFSG.Quasithin.RuType in
theorem RuChoice.fx_core {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {X : Subgroup G} {t₀ : G} (ht₀ : t₀ ∈ (M.T : Subgroup G))
    (hX : CFSG.ASVolI.ChIJK.IsSylowIn 3 X M.G2)
    (hN : CFSG.conjugate M.TF t₀ ≤ Subgroup.normalizer ((X ⊔ M.Agrp : Subgroup G) : Set G)) :
    ∃ s ∈ (M.T : Subgroup G), X = CFSG.conjugate (Subgroup.zpowers M.x2el) s ∧
      CFSG.conjugate M.TF s = CFSG.conjugate M.TF t₀ ∧
      CFSG.conjugate M.F1 s = CFSG.conjugate M.F1 t₀ := by
  obtain ⟨s, hsT, hXs⟩ := RuChoice.fx_exists_conj M hX
  have hAs : CFSG.conjugate M.Agrp s = M.Agrp :=
    RuChoice.fx_conjugate_eq_self (M.G2_le_normalizer_Agrp (M.T_le_G2 hsT))
  have hXA : X ⊔ M.Agrp = CFSG.conjugate M.XA s := by
    rw [hXs, RuChoice.fx_conjugate_sup, hAs]
  rw [hXA, RuChoice.fx_normalizer_conjugate] at hN
  have h1 := RuChoice.fx_conjugate_mono s⁻¹ hN
  rw [RuChoice.fx_conjugate_conjugate, RuChoice.fx_conjugate_conjugate, mul_inv_cancel,
    RuChoice.fx_conjugate_one] at h1
  have hw : t₀ * s⁻¹ ∈ (M.T : Subgroup G) := mul_mem ht₀ (inv_mem hsT)
  have h2 : CFSG.conjugate M.TF (t₀ * s⁻¹) ≤
      (M.T : Subgroup G) ⊓ Subgroup.normalizer (M.XA : Set G) :=
    le_inf (RuChoice.fx_conjugate_le M.TF_le_T hw) h1
  rw [RuChoice.fx_inf_normalizer_XA] at h2
  have h3 : CFSG.conjugate M.TF (t₀ * s⁻¹) = M.TF :=
    Subgroup.eq_of_le_of_card_ge h2 (RuChoice.fx_card_conjugate _ _).ge
  have hwN : t₀ * s⁻¹ ∈ Subgroup.normalizer (M.TF : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← RuChoice.fx_mem_conjugate, h3]
  have hwF1 : t₀ * s⁻¹ ∈ Subgroup.normalizer (M.F1 : Set G) :=
    RuChoice.fx_normalizer_TF_le M hw hwN
  have hs : s = (t₀ * s⁻¹)⁻¹ * t₀ := by group
  refine ⟨s, hsT, hXs, ?_, ?_⟩
  · rw [hs, ← RuChoice.fx_conjugate_conjugate, RuChoice.fx_conjugate_eq_self (inv_mem hwN)]
  · rw [hs, ← RuChoice.fx_conjugate_conjugate, RuChoice.fx_conjugate_eq_self (inv_mem hwF1)]

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.F {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {B5 X : Subgroup G} {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t)
    (hX : IsSylowIn 3 X (G2Ru M.L V2 (M.T : Subgroup G))) {a : G}
    (ha : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a)
    (hQ : Q5Ru (M.T : Subgroup G) B5 ≤
      Subgroup.normalizer ((X ⊔ ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a : Subgroup G) : Set G)) :
    ∃ y : G, y ∈ (M.T : Subgroup G) ∧
      TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF y ∧
      F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 y ∧
      F2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 X = CFSG.conjugate M.F2 y ∧
      FRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 X = CFSG.conjugate (M.F1 ⊔ M.F2) y := by
  obtain ⟨hG2, -, -⟩ := RuChoice.frame M hV2
  have hAeq := RuChoice.A M hV2 ht hB ha
  obtain ⟨hTF, hF1⟩ := RuChoice.TF_F1 M hV2 ht hB ha
  have hX' : IsSylowIn 3 X M.G2 := by
    rw [← hG2]
    exact hX
  have hN : CFSG.conjugate M.TF t ≤ Subgroup.normalizer ((X ⊔ M.Agrp : Subgroup G) : Set G) := by
    rw [← hTF, ← hAeq]
    exact sup_le (le_sup_right.trans Subgroup.le_normalizer) hQ
  obtain ⟨s, hsT, hXs, hTFs, hF1s⟩ := RuChoice.fx_core M ht hX' hN
  have hTFeq : TFRu M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.TF s := by
    rw [hTF, hTFs]
  have hF1eq : F1Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 = CFSG.conjugate M.F1 s := by
    rw [hF1, hF1s]
  have hF2eq : F2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) a B5 X = CFSG.conjugate M.F2 s := by
    unfold F2Ru
    rw [hTFeq, hXs, ← RuChoice.fx_conjugate_sup]
  refine ⟨s, hsT, hTFeq, hF1eq, hF2eq, ?_⟩
  unfold FRu
  rw [hF1eq, hF2eq, ← RuChoice.fx_conjugate_sup]

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem RuChoice.reduce
    {G : Type} [Group G] [Finite G] {L V T : Subgroup G} (h : RuType G L V T)
    {V2 : Subgroup G} (hV2 : IsV2 V T V2)
    {g : G} (hg : g ∈ L2Ru L V2) (hgH : g ∉ HRu T)
    {v : G} (hv : v ∈ CFSG.conjugate (URu V T) g)
    (hvQ : v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T)
    {B5 : Subgroup G} (hB5 : IsSylowIn 5 B5 (HRu T)) (hinv : InvertsGroup v B5)
    {X : Subgroup G} (hX : IsSylowIn 3 X (G2Ru L V2 T))
    {a : G} (ha : IsAChoice L V T V2 B5 a)
    (hA : ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G))
    (hQ : Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G)) :
    ∃ (M : RuDataM G) (y : G), M.L = L ∧ (M.T : Subgroup G) = T ∧ y ∈ T ∧
      G2Ru L V2 T = M.G2 ∧ R2Ru L V2 T = M.R2 ∧ S2Ru L V V2 T = M.W ∧ ARu L V V2 T a = M.Agrp ∧
      (∃ t : G, t ∈ T ∧ B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) ∧
      TFRu L V V2 T a B5 = CFSG.conjugate M.TF y ∧
      F1Ru L V V2 T a B5 = CFSG.conjugate M.F1 y ∧
      F2Ru L V V2 T a B5 X = CFSG.conjugate M.F2 y ∧
      FRu L V V2 T a B5 X = CFSG.conjugate (M.F1 ⊔ M.F2) y := by
  obtain ⟨M, hML, hMT⟩ := RuChoice.exists_M h
  have _ := hA
  subst hML
  subst hMT
  have hV : V = ruV M.L := h.V_eq_ruV
  subst hV
  obtain ⟨hG2, hR2, hS2⟩ := RuChoice.frame M hV2
  obtain ⟨t, ht, hBt⟩ := RuChoice.B5 M hV2 hg hgH hv hvQ hB5 hinv
  have hAeq := RuChoice.A M hV2 ht hBt ha
  obtain ⟨y, hy, hTF, hF1, hF2, hF⟩ := RuChoice.F M hV2 ht hBt hX ha hQ
  exact ⟨M, y, rfl, rfl, hy, hG2, hR2, hS2, hAeq, ⟨t, ht, hBt⟩, hTF, hF1, hF2, hF⟩

end RuChoiceSec

@[expose] def J_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : ↥(HRu T), (v : G) ∈ CFSG.conjugate (URu V T) g →
      (v : G) ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
      (starImg T (Subgroup.zpowers (v : G)) = starImg T (CFSG.conjugate (URu V T) g) ∧
        starImg T (CFSG.conjugate (URu V T) g) =
          (Subgroup.center ↥(starImg T T)).map (starImg T T).subtype ∧
        Nat.card ↥(starImg T (CFSG.conjugate (URu V T) g)) = 2) ∧
      ((∃ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) ∧ InvertsGroup (v : G) B5) ∧
        Set.ncard {P : Sylow 5 (↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)) |
          ∀ x ∈ (P : Subgroup (↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T))),
            ((v : ↥(HRu T)) : ↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T))⁻¹ * x *
              ((v : ↥(HRu T)) : ↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)) = x⁻¹} = 2) ∧
      (∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup (v : G) B5 →
        (URu V T ≤ Q5Ru T B5 ∧ IsElemAbelianSection (Q5Ru T B5) (URu V T) 4 ∧
          Nonempty (↥(QRu T ⊓ Subgroup.centralizer (B5 : Set G)) ≃* QuaternionGroup 2) ∧
          QRu T = (QRu T ⊓ Subgroup.centralizer (B5 : Set G)) ⊔ Q5Ru T B5 ∧
          ((QRu T ⊓ Subgroup.centralizer (B5 : Set G)) ⊔ URu V T) ⊓ Q5Ru T B5 = URu V T) ∧
        (CFSG.conjugate (URu V T) g ⊓ QRu T ⊔ URu V T =
            ⁅QRu T ⊓ Subgroup.centralizer (V2 : Set G), CFSG.conjugate (URu V T) g⁆ ⊔ URu V T ∧
          ⁅QRu T ⊓ Subgroup.centralizer (V2 : Set G), CFSG.conjugate (URu V T) g⁆ ⊔ URu V T ≤
            Q5Ru T B5 ∧
          (URu V T).relIndex (CFSG.conjugate (URu V T) g ⊓ QRu T ⊔ URu V T) = 2) ∧
        ⁅QRu T, CFSG.conjugate (URu V T) g⁆ ≤ Q5Ru T B5) ∧
      (∃ (_ : ((URu V T).subgroupOf (HRu T)).Normal),
        Nat.card (Subgroup.center (↥(HRu T) ⧸ (URu V T).subgroupOf (HRu T))) = 2) ∧
      V = CFSG.conjugate (URu V T) g ⊓ HCRu V T

section BurnsideJ7_fold

open CFSG.Quasithin.RuType in
def burnsideJ7_V2pl {G : Type} [Group G] (M : RuDataM G) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ruV M.L, (Multiplicative.toAdd (M.ψV ⟨x, hx⟩)) 2 = 0}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : (⟨a * b, mul_mem ha hb⟩ : ruV M.L) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, toAdd_mul]
    simp [ha2, hb2]
  one_mem' := ⟨(ruV M.L).one_mem, by
    have : (⟨1, (ruV M.L).one_mem⟩ : ruV M.L) = 1 := rfl
    rw [this, map_one, toAdd_one]
    rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    refine ⟨inv_mem ha, ?_⟩
    have : (⟨a⁻¹, inv_mem ha⟩ : ruV M.L) = (⟨a, ha⟩ : ruV M.L)⁻¹ := rfl
    rw [this, map_inv, toAdd_inv]
    have h2 : ∀ x : ZMod 2, -x = x := by decide
    simp [ha2]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_mem_V2pl {G : Type} [Group G] (M : RuDataM G) {x : G} :
    x ∈ burnsideJ7_V2pl M ↔ ∃ hx : x ∈ ruV M.L, (Multiplicative.toAdd (M.ψV ⟨x, hx⟩)) 2 = 0 :=
  Iff.rfl

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_card_V2pl {G : Type} [Group G] (M : RuDataM G) :
    Nat.card (burnsideJ7_V2pl M) = 4 := by
  have e : (burnsideJ7_V2pl M) ≃ {y : Fin 3 → ZMod 2 // y 2 = 0} :=
    { toFun := fun x => ⟨Multiplicative.toAdd (M.ψV ⟨x.1, x.2.1⟩), x.2.2⟩
      invFun := fun y => ⟨(M.ψV.symm (Multiplicative.ofAdd y.1) : G),
        ⟨(M.ψV.symm (Multiplicative.ofAdd y.1)).2, by simpa using y.2⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_exists_T_of_P0 {G : Type} [Group G] (M : RuDataM G) {p :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hp : p ∈ SL3.P0) :
    ∃ (t : G) (htL : t ∈ M.L), t ∈ (M.T : Subgroup G) ∧ M.θ ⟨t, htL⟩ = p := by
  rw [← M.hP0] at hp
  obtain ⟨t', ht', rfl⟩ := hp
  exact ⟨t'.1, t'.2, Subgroup.mem_subgroupOf.mp ht', rfl⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_p0p1 : ∀ y : Fin 3 → ZMod 2, y 2 = 1 →
    natAct3 (⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) y = y + ![1, 0, 0] ∧
    natAct3 (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) y = y + ![0, 1, 0] := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_p0p1_mem :
    (⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ SL3.P0 ∧
    (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ SL3.P0 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

private theorem burnsideJ7_vec_cancel : ∀ y e : Fin 3 → ZMod 2, y + e + y = e := by
  decide +kernel

private theorem burnsideJ7_decomp : ∀ y w : Fin 3 → ZMod 2, y 2 = 1 →
    ∃ a b c : Bool, w = (if a then ![1, 0, 0] else 0) + (if b then ![0, 1, 0] else 0) +
      (if c then y else 0) := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_V2_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) : V2 = burnsideJ7_V2pl M := by
  obtain ⟨hVle, hcard, hT⟩ := hV2
  have hle : V2 ≤ burnsideJ7_V2pl M := by
    intro x hx
    have hxV : x ∈ ruV M.L := hVle hx
    refine ⟨hxV, ?_⟩
    by_contra h2
    have hy2 : (Multiplicative.toAdd (M.ψV ⟨x, hxV⟩)) 2 = 1 := by
      rcases Quasithin.RuType.Sigma.zmod2_cases ((Multiplicative.toAdd (M.ψV ⟨x, hxV⟩)) 2) with h | h
      · exact absurd h h2
      · exact h
    set y := Multiplicative.toAdd (M.ψV ⟨x, hxV⟩) with hy
    have hconj : ∀ p : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), p ∈ SL3.P0 → ∃ z ∈ V2, ∃ hz : z ∈ ruV M.L,
        Multiplicative.toAdd (M.ψV ⟨z, hz⟩) = natAct3 p y := by
      intro p hp
      obtain ⟨t, htL, htT, hθ⟩ := burnsideJ7_exists_T_of_P0 M hp
      have hz : t * x * t⁻¹ ∈ V2 := (Subgroup.mem_normalizer_iff.mp (hT htT) x).mp hx
      have hzV : t * x * t⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V htL hxV
      refine ⟨t * x * t⁻¹, hz, hzV, ?_⟩
      have := M.ψV_equiv ⟨t, htL⟩ ⟨x, hxV⟩ ⟨t * x * t⁻¹, hzV⟩ rfl
      rw [this, toAdd_ofAdd, hθ]
    obtain ⟨z0, hz0, hz0V, hz0e⟩ := hconj _ burnsideJ7_p0p1_mem.1
    obtain ⟨z1, hz1, hz1V, hz1e⟩ := hconj _ burnsideJ7_p0p1_mem.2
    rw [(burnsideJ7_p0p1 y hy2).1] at hz0e
    rw [(burnsideJ7_p0p1 y hy2).2] at hz1e
    let Y : Set (Fin 3 → ZMod 2) := {w | ∃ z ∈ V2, ∃ hz : z ∈ ruV M.L,
      Multiplicative.toAdd (M.ψV ⟨z, hz⟩) = w}
    have hY0 : (0 : Fin 3 → ZMod 2) ∈ Y := ⟨1, V2.one_mem, (ruV M.L).one_mem, by
      have : (⟨1, (ruV M.L).one_mem⟩ : ruV M.L) = 1 := rfl
      rw [this, map_one, toAdd_one]⟩
    have hYadd : ∀ w1 ∈ Y, ∀ w2 ∈ Y, w1 + w2 ∈ Y := by
      rintro _ ⟨a, ha, haV, rfl⟩ _ ⟨b, hb, hbV, rfl⟩
      refine ⟨a * b, V2.mul_mem ha hb, mul_mem haV hbV, ?_⟩
      have : (⟨a * b, mul_mem haV hbV⟩ : ruV M.L) = ⟨a, haV⟩ * ⟨b, hbV⟩ := rfl
      rw [this, map_mul, toAdd_mul]
    have hYy : y ∈ Y := ⟨x, hx, hxV, rfl⟩
    have hYe0 : (![1, 0, 0] : Fin 3 → ZMod 2) ∈ Y := by
      have h := hYadd _ ⟨z0, hz0, hz0V, hz0e⟩ _ hYy
      rwa [burnsideJ7_vec_cancel] at h
    have hYe1 : (![0, 1, 0] : Fin 3 → ZMod 2) ∈ Y := by
      have h := hYadd _ ⟨z1, hz1, hz1V, hz1e⟩ _ hYy
      rwa [burnsideJ7_vec_cancel] at h
    have hVV2 : ruV M.L ≤ V2 := by
      intro v hv
      obtain ⟨a, b, c, hw⟩ := burnsideJ7_decomp y (Multiplicative.toAdd (M.ψV ⟨v, hv⟩)) hy2
      have hmem : Multiplicative.toAdd (M.ψV ⟨v, hv⟩) ∈ Y := by
        rw [hw]
        refine hYadd _ (hYadd _ ?_ _ ?_) _ ?_
        · split_ifs
          · exact hYe0
          · exact hY0
        · split_ifs
          · exact hYe1
          · exact hY0
        · split_ifs
          · exact hYy
          · exact hY0
      obtain ⟨z, hz, hzV, hze⟩ := hmem
      have : (⟨z, hzV⟩ : ruV M.L) = ⟨v, hv⟩ := M.ψV.injective (Multiplicative.toAdd.injective hze)
      have hzv : z = v := congrArg Subtype.val this
      rw [← hzv]
      exact hz
    have h8 : Nat.card (ruV M.L) = 8 := M.toRuData.card_V
    have h4 : Nat.card V2 = 4 := hcard
    have := Subgroup.card_le_of_le hVV2
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [burnsideJ7_card_V2pl, hcard])

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_conj_mem_V2pl {G : Type} [Group G] (M : RuDataM G) {g : G} (hgL : g
    ∈ M.L)
    (hθ : M.θ ⟨g, hgL⟩ ∈ SL3.Pl) {x : G} (hx : x ∈ burnsideJ7_V2pl M) :
    g * x * g⁻¹ ∈ burnsideJ7_V2pl M := by
  obtain ⟨hxV, hx2⟩ := hx
  have hgxV : g * x * g⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V hgL hxV
  refine ⟨hgxV, ?_⟩
  have := M.ψV_equiv ⟨g, hgL⟩ ⟨x, hxV⟩ ⟨g * x * g⁻¹, hgxV⟩ rfl
  rw [this, toAdd_ofAdd]
  exact SL3.Pl_plane _ hθ _ hx2

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_L_inf_normalizer {G : Type} [Group G] (M : RuDataM G) :
    M.L ⊓ Subgroup.normalizer (burnsideJ7_V2pl M : Set G) = M.G2 := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgN⟩
    refine mem_pullL.mpr ⟨hgL, ?_⟩
    have hcol : ∀ e : Fin 3 → ZMod 2, e 2 = 0 → (natAct3 (M.θ ⟨g, hgL⟩) e) 2 = 0 := by
      intro e he
      set x : ruV M.L := M.ψV.symm (Multiplicative.ofAdd e) with hxdef
      have hxV2 : (x : G) ∈ burnsideJ7_V2pl M := ⟨x.2, by simpa [hxdef] using he⟩
      have hgx : g * x * g⁻¹ ∈ burnsideJ7_V2pl M :=
        (Subgroup.mem_normalizer_iff.mp hgN x).mp hxV2
      obtain ⟨hgxV, hgx2⟩ := hgx
      have := M.ψV_equiv ⟨g, hgL⟩ x ⟨g * x * g⁻¹, hgxV⟩ rfl
      rw [this, toAdd_ofAdd] at hgx2
      simpa [hxdef] using hgx2
    have h0 := hcol ![1, 0, 0] rfl
    have h1 := hcol ![0, 1, 0] rfl
    refine ⟨?_, ?_⟩
    · simpa [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
    · simpa [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1
  · intro hg
    obtain ⟨hgL, hθ⟩ := mem_pullL.mp hg
    refine ⟨hgL, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => burnsideJ7_conj_mem_V2pl M hgL hθ hx
    · intro hx
      have hθ' : M.θ ⟨g⁻¹, inv_mem hgL⟩ ∈ SL3.Pl := by
        have : M.θ ⟨g⁻¹, inv_mem hgL⟩ = (M.θ ⟨g, hgL⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact inv_mem hθ
      have := burnsideJ7_conj_mem_V2pl M (inv_mem hgL) hθ' hx
      simpa [mul_assoc] using this

private theorem burnsideJ7_twoResidual_le {G : Type} [Group G] (X : Subgroup G) :
    ChIJK.twoResidual X ≤ X :=
  Subgroup.map_subtype_le _

private theorem burnsideJ7_mem_twoResidual_of_odd {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {x : G} (hx : x ∈ X) {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) :
    x ∈ ChIJK.twoResidual X := by
  unfold ChIJK.twoResidual
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_sInf]
  rintro N ⟨hN, k, hk⟩
  have hcard : Nat.card (↥X ⧸ N) = 2 ^ k := by
    rw [← Subgroup.index_eq_card]
    exact hk
  have h1 : ((⟨x, hx⟩ : X) : ↥X ⧸ N) ^ (2 ^ k) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h2 : ((⟨x, hx⟩ : X) : ↥X ⧸ N) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : X) ^ n = 1 := Subtype.ext (by simpa using hxn)
    rw [this]
    rfl
  have hcop : Nat.Coprime n (2 ^ k) := by
    apply Nat.Coprime.pow_right
    exact Nat.coprime_two_right.mpr hn
  have h3 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  rw [hcop, pow_one] at h3
  exact (QuotientGroup.eq_one_iff _).mp h3

@[expose] def burnsideJ7_a3mat : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_a3 :
    burnsideJ7_a3mat ∈ SL3.Pl ∧ burnsideJ7_a3mat ^ 3 = 1 ∧ burnsideJ7_a3mat ≠ 1 :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_exists_L2_lift3 {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (ha : a ∈ SL3.Pl) (ha3 : a ^ 3 = 1) :
    ∃ (l : G) (hl : l ∈ M.L), l ∈ ChIJK.twoResidual M.G2 ∧ M.θ ⟨l, hl⟩ = a ∧ l ^ 3 = 1 := by
  obtain ⟨l, hθ, hl3⟩ := M.exists_lift ha3 (by norm_num)
  have hlG : (l : G) ∈ M.G2 := mem_pullL.mpr ⟨l.2, by rw [hθ]; exact ha⟩
  exact ⟨l, l.2, burnsideJ7_mem_twoResidual_of_odd hlG (n := 3) (by decide) hl3, hθ, hl3⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_card_T {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card (M.T : Subgroup G) = 2 ^ 14 := by
  rw [← M.toRuData.TL_eq, M.toRuData.card_TL]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_L2_sup_T {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) = M.G2 := by
  have hle : ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) ≤ M.G2 :=
    sup_le (burnsideJ7_twoResidual_le _) M.T_le_G2
  obtain ⟨ha, ha3, ha1⟩ := burnsideJ7_a3
  obtain ⟨l, hl, hl2, hθ, hl3⟩ := burnsideJ7_exists_L2_lift3 M ha ha3
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply ha1
    rw [← hθ]
    exact map_one M.θ
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  set K := ChIJK.twoResidual M.G2 ⊔ (M.T : Subgroup G) with hK
  have h3 : 3 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K (x := l) (Subgroup.mem_sup_left hl2)
    rwa [hord] at this
  have h2 : 2 ^ 14 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le (le_sup_right : (M.T : Subgroup G) ≤ K)
    rwa [burnsideJ7_card_T] at this
  have h6 : 2 ^ 14 * 3 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hG : Nat.card M.G2 = 2 ^ 14 * 3 := by rw [M.card_G2]; norm_num
  have hKG : Nat.card K ∣ Nat.card M.G2 := Subgroup.card_dvd_of_le hle
  rw [hG] at hKG
  have heq : Nat.card K = 2 ^ 14 * 3 := Nat.dvd_antisymm hKG h6
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hG, heq])

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_inter_P0 : ∀ y ∈ SL3.Pl, (∀ p ∈ SL3.Pl, p⁻¹ * y * p ∈ SL3.P0) → y ∈
    SL3.R2m := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_pCoreOf_G2 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    pCoreOf 2 M.G2 = M.R2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    have hn : (CFSG.pCore 2 ↥M.G2).Normal := CFSG.pCore_normal
    have hTp : IsPGroup 2 ((M.T : Subgroup G).subgroupOf M.G2) :=
      (M.T.isPGroup').of_equiv (Subgroup.subgroupOfEquivOfLe M.T_le_G2).symm
    have hidx : ¬ 2 ∣ ((M.T : Subgroup G).subgroupOf M.G2).index := by
      have h1 := Subgroup.card_mul_index ((M.T : Subgroup G).subgroupOf M.G2)
      rw [card_subgroupOf_of_le M.T_le_G2, burnsideJ7_card_T, M.card_G2] at h1
      have : ((M.T : Subgroup G).subgroupOf M.G2).index = 3 := by omega
      rw [this]
      norm_num
    let P : Sylow 2 ↥M.G2 := hTp.toSylow hidx
    have hle : CFSG.pCore 2 ↥M.G2 ≤ (P : Subgroup ↥M.G2) :=
      (CFSG.pCore_isPGroup (G := ↥M.G2) (p := 2)).le_sylow_of_normal P
    rintro x ⟨y, hy, rfl⟩
    have hyG : (y : G) ∈ M.G2 := y.2
    obtain ⟨hyL, -⟩ := mem_pullL.mp hyG
    refine mem_pullL.mpr ⟨hyL, ?_⟩
    apply burnsideJ7_inter_P0
    · exact (mem_pullL.mp hyG).2
    · intro p hp
      obtain ⟨⟨g, hgL⟩, rfl⟩ := M.θ_surj p
      have hgG : g ∈ M.G2 := mem_pullL.mpr ⟨hgL, hp⟩
      have hmem : (⟨g, hgG⟩ : ↥M.G2)⁻¹ * y * ⟨g, hgG⟩ ∈ CFSG.pCore 2 ↥M.G2 := by
        have := hn.conj_mem y hy (⟨g, hgG⟩ : ↥M.G2)⁻¹
        simpa using this
      have hP : ((⟨g, hgG⟩ : ↥M.G2)⁻¹ * y * ⟨g, hgG⟩ : ↥M.G2) ∈ (P : Subgroup ↥M.G2) := hle hmem
      have hPT : g⁻¹ * y * g ∈ (M.T : Subgroup G) := Subgroup.mem_subgroupOf.mp hP
      have := M.θ_mem_P0 hPT
      have e : (⟨g⁻¹ * y * g, M.toRuData.T_le_L hPT⟩ : M.L) =
          (⟨g, hgL⟩ : M.L)⁻¹ * ⟨y, hyL⟩ * ⟨g, hgL⟩ := rfl
      rw [e, map_mul, map_mul, map_inv] at this
      exact this
  ·
    have hRn : (M.R2.subgroupOf M.G2).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxL, hxR⟩ := mem_pullL.mp hx
      obtain ⟨hgL, hgP⟩ := mem_pullL.mp g.2
      show (g : G) * x * (g : G)⁻¹ ∈ M.R2
      refine mem_pullL.mpr ⟨mul_mem (mul_mem hgL hxL) (inv_mem hgL), ?_⟩
      have e : (⟨(g : G) * x * (g : G)⁻¹, mul_mem (mul_mem hgL hxL) (inv_mem hgL)⟩ : M.L) =
          ⟨g, hgL⟩ * ⟨(x : G), hxL⟩ * (⟨g, hgL⟩ : M.L)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact SL3.conj_mem_R2m _ hgP _ hxR
    have hRp : IsPGroup 2 (M.R2.subgroupOf M.G2) := by
      rw [IsPGroup.iff_card, card_subgroupOf_of_le M.R2_le_G2, M.card_R2]
      exact ⟨13, rfl⟩
    have hle : M.R2.subgroupOf M.G2 ≤ CFSG.pCore 2 ↥M.G2 := le_sSup ⟨hRn, hRp⟩
    have := Subgroup.map_mono (f := M.G2.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le M.R2_le_G2] at this
    exact this

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_L2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.L2Ru M.L V2 = ChIJK.twoResidual M.G2 := by
  rw [ChIJK.L2Ru, burnsideJ7_V2_eq M hV2, burnsideJ7_L_inf_normalizer]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_R2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.R2Ru M.L V2 (M.T : Subgroup G) = M.R2 := by
  rw [ChIJK.R2Ru, burnsideJ7_L2Ru_eq M hV2, burnsideJ7_L2_sup_T, burnsideJ7_pCoreOf_G2]

open CFSG.Quasithin.RuType in
def burnsideJ7_chiAdd {G : Type} [Group G] (M : RuDataM G) (X : Subgroup G) :
    AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) where
  carrier := {A | ∃ x ∈ X, ∃ hx : x ∈ ruS M.L, Multiplicative.toAdd (M.χ ⟨x, hx⟩) = A}
  zero_mem' := ⟨1, X.one_mem, (ruS M.L).one_mem, by
    have : (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 := rfl
    rw [this, map_one, toAdd_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, haS, rfl⟩ ⟨b, hb, hbS, rfl⟩
    refine ⟨a * b, X.mul_mem ha hb, mul_mem haS hbS, ?_⟩
    have : (⟨a * b, mul_mem haS hbS⟩ : ruS M.L) = ⟨a, haS⟩ * ⟨b, hbS⟩ := rfl
    rw [this, M.toAdd_χ_mul]
  neg_mem' := by
    rintro _ ⟨a, ha, haS, rfl⟩
    refine ⟨a⁻¹, X.inv_mem ha, inv_mem haS, ?_⟩
    have : (⟨a⁻¹, inv_mem haS⟩ : ruS M.L) = (⟨a, haS⟩ : ruS M.L)⁻¹ := rfl
    rw [this, M.toAdd_χ_inv]
    ext i j
    simp only [Matrix.neg_apply]
    have h2 : ∀ x : ZMod 2, x = -x := by decide
    exact h2 _

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_mem_of_chi {G : Type} [Group G] (M : RuDataM G) {X : Subgroup G}
    (hVX : ruV M.L ≤ X) {x : G} (hx : x ∈ ruS M.L)
    (h : Multiplicative.toAdd (M.χ ⟨x, hx⟩) ∈ burnsideJ7_chiAdd M X) : x ∈ X := by
  obtain ⟨y, hyX, hyS, hy⟩ := h
  have hk : (⟨y, hyS⟩ : ruS M.L)⁻¹ * ⟨x, hx⟩ ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Multiplicative.toAdd.injective hy]
    exact inv_mul_cancel _
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact X.mul_mem hyX (hVX hk)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_W_le_of_chi {G : Type} [Group G] [Finite G] (M : RuDataM G) {X :
    Subgroup G}
    (hVX : ruV M.L ≤ X)
    (h : ∀ A, SL3.IsM2 A → IsTraceZero A → A ∈ burnsideJ7_chiAdd M X) : M.W ≤ X := by
  rintro x ⟨hx, hxM⟩
  exact burnsideJ7_mem_of_chi M hVX hx (h _ hxM (M.χ_trace _))

def burnsideJ7_inSpan :
    List (Matrix (Fin 3) (Fin 3) (ZMod 2)) → Matrix (Fin 3) (Fin 3) (ZMod 2) → Bool
  | [], A => decide (A = 0)
  | g :: gs, A => burnsideJ7_inSpan gs A || burnsideJ7_inSpan gs (A + g)

private theorem burnsideJ7_mat_add_self : ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g + g = 0 := by
  decide +kernel

private theorem burnsideJ7_mem_of_inSpan (P : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    ∀ («gens» : List (Matrix (Fin 3) (Fin 3) (ZMod 2))), (∀ g ∈ «gens», g ∈ P) →
      ∀ A, burnsideJ7_inSpan «gens» A = true → A ∈ P := by
  intro «gens»
  induction «gens» with
  | nil =>
    intro _ A h
    simp only [burnsideJ7_inSpan, decide_eq_true_eq] at h
    rw [h]
    exact P.zero_mem
  | cons g gs ih =>
    intro hg A h
    simp only [burnsideJ7_inSpan, Bool.or_eq_true] at h
    have hgs : ∀ x ∈ gs, x ∈ P := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    rcases h with h | h
    · exact ih hgs A h
    · have h1 := ih hgs (A + g) h
      have hgP := hg g List.mem_cons_self
      have : A = (A + g) + g := by
        rw [add_assoc, burnsideJ7_mat_add_self, add_zero]
      rw [this]
      exact P.add_mem h1 hgP

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_mem_chiAdd {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {X : Subgroup G} (hX : ⁅ruS M.L, M.R2⁆ ≤ X) {r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hr : r ∈ SL3.R2m) {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsTraceZero A) :
    stAct r A + A ∈ burnsideJ7_chiAdd M X := by
  obtain ⟨l, hθ⟩ := M.θ_surj r
  have hlR : (l : G) ∈ M.R2 := mem_pullL.mpr ⟨l.2, by rw [hθ]; exact hr⟩
  obtain ⟨s, hs⟩ := M.χ_surj A hA
  have hlS : (l : G) ∈ Subgroup.normalizer (ruS M.L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L l.2
  have ht : (l : G) * (s : G)⁻¹ * (l : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp hlS _).mp (inv_mem s.2)
  have hy : (s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹ ∈ ruS M.L := by
    have : (s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹ =
        (s : G) * ((l : G) * (s : G)⁻¹ * (l : G)⁻¹) := by group
    rw [this]
    exact mul_mem s.2 ht
  refine ⟨(s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹,
    hX (Subgroup.commutator_mem_commutator s.2 hlR), hy, ?_⟩
  have e : (⟨(s : G) * (l : G) * (s : G)⁻¹ * (l : G)⁻¹, hy⟩ : ruS M.L) =
      s * ⟨(l : G) * (s : G)⁻¹ * (l : G)⁻¹, ht⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  rw [e, M.toAdd_χ_mul]
  have h1 : Multiplicative.toAdd (M.χ ⟨(l : G) * (s : G)⁻¹ * (l : G)⁻¹, ht⟩) =
      stAct (M.θ l) (Multiplicative.toAdd (M.χ s⁻¹)) := M.χ_conj l s⁻¹
  rw [h1, M.toAdd_χ_inv, hs, toAdd_ofAdd, hθ, add_comm]

@[expose] def burnsideJ7_ra : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

@[expose] def burnsideJ7_rb : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def burnsideJ7_pairsR2 :
    List (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [(burnsideJ7_ra, !![1, 0, 0; 0, 0, 0; 0, 0, 1]),
   (burnsideJ7_ra, !![1, 0, 0; 0, 0, 0; 0, 1, 1]),
   (burnsideJ7_ra, !![0, 0, 0; 0, 0, 0; 1, 0, 0]),
   (burnsideJ7_ra, !![0, 1, 0; 0, 0, 0; 0, 0, 0]),
   (burnsideJ7_rb, !![0, 0, 0; 0, 0, 0; 0, 1, 0]),
   (burnsideJ7_rb, !![0, 0, 0; 0, 1, 0; 1, 0, 1])]

@[expose] def burnsideJ7_gensR2 : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![0, 0, 0; 0, 0, 1; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
   !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 1, 0; 0, 0, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0; 0, 0, 1]]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_gensR2_spec : ∀ g ∈ burnsideJ7_gensR2, ∃ p ∈ burnsideJ7_pairsR2,
    p.1 ∈ SL3.R2m ∧ IsTraceZero p.2 ∧ stAct p.1 p.2 + p.2 = g := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_span_M2 : ∀ A, SL3.IsM2 A → IsTraceZero A →
    burnsideJ7_inSpan burnsideJ7_gensR2 A = true := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_W_le_S2 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    M.W ≤ ⁅ruS M.L, M.R2⁆ ⊔ ruV M.L := by
  refine burnsideJ7_W_le_of_chi M le_sup_right fun A hA hAt => ?_
  refine burnsideJ7_mem_of_inSpan _ burnsideJ7_gensR2 ?_ A (burnsideJ7_span_M2 A hA hAt)
  intro g hg
  obtain ⟨p, -, hp1, hp2, rfl⟩ := burnsideJ7_gensR2_spec g hg
  exact burnsideJ7_comm_mem_chiAdd M le_sup_left hp1 hp2

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_sup_V_eq_W {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ⁅ruS M.L, M.R2⁆ ⊔ ruV M.L = M.W := by
  refine le_antisymm (sup_le ?_ ?_) (burnsideJ7_W_le_S2 M)
  · rw [Subgroup.commutator_le]
    intro s hs r hr
    have := M.W.inv_mem (M.comm_mem_W hr hs)
    have e : s * r * s⁻¹ * r⁻¹ = (r * s * r⁻¹ * s⁻¹)⁻¹ := by group
    show s * r * s⁻¹ * r⁻¹ ∈ M.W
    rw [e]
    exact this
  · exact fun v hv => M.U_le_W (M.V_le_U hv)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_S2Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.S2Ru M.L (ruV M.L) V2 (M.T : Subgroup G) = M.W := by
  rw [ChIJK.S2Ru, burnsideJ7_R2Ru_eq M hV2]
  exact burnsideJ7_comm_sup_V_eq_W M

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_center_sigma :
    ∀ g : SigmaL2F4, (∀ s : SigmaL2F4, s * g = g * s) → g = 1 := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_fix_sigma :
    ∀ w : Fin 2 → CFSG.Quasithin.RuType.F4, (∀ g : SigmaL2F4, sigmaAct g w = w) → w = 0 := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q0_set {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    {h : G | h ∈ ruH M.T ∧ ∀ x ∈ ruH M.T, h⁻¹ * x⁻¹ * h * x ∈ ruU M.L M.T} = (M.Q0 : Set G) := by
  ext h
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨hH, hc⟩
    have hφ1 : M.φ ⟨h, hH⟩ = 1 := by
      apply burnsideJ7_center_sigma
      intro s
      obtain ⟨x, hx⟩ := M.φ_surj s
      have hmem : h⁻¹ * (x : G)⁻¹ * h * x ∈ ruU M.L M.T := hc x x.2
      have hk : (⟨h⁻¹ * (x : G)⁻¹ * h * x, M.U_le_H hmem⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact M.U_le_Q hmem
      have e : (⟨h⁻¹ * (x : G)⁻¹ * h * x, M.U_le_H hmem⟩ : ruH M.T) =
          (⟨h, hH⟩ : ruH M.T)⁻¹ * x⁻¹ * ⟨h, hH⟩ * x := rfl
      rw [MonoidHom.mem_ker, e, map_mul, map_mul, map_mul, map_inv, map_inv, hx] at hk
      calc s * M.φ ⟨h, hH⟩ = s * M.φ ⟨h, hH⟩ * ((M.φ ⟨h, hH⟩)⁻¹ * s⁻¹ * M.φ ⟨h, hH⟩ * s) := by
            rw [hk, mul_one]
        _ = M.φ ⟨h, hH⟩ * s := by group
    have hQ : h ∈ ruQ M.T := by
      have : (⟨h, hH⟩ : ruH M.T) ∈ M.φ.ker := hφ1
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    have hfix : ∀ (k : G) (hk : k ∈ ruH M.T),
        M.actQ ⟨k, hk⟩ ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) = ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) := by
      intro k hk
      rw [M.actQ_mk, M.mk_eq_mk_iff]
      have h1 := inv_mem (hc k⁻¹ (inv_mem hk))
      have e : (k * h * k⁻¹)⁻¹ * h = (h⁻¹ * k⁻¹⁻¹ * h * k⁻¹)⁻¹ := by group
      show (k * h * k⁻¹)⁻¹ * h ∈ ruU M.L M.T
      rw [e]
      exact h1
    have hfixσ : ∀ g : SigmaL2F4, sigmaAct g (Multiplicative.toAdd (M.ψQbar ((⟨h, hQ⟩ : ruQ M.T) :
        M.Qbar))) = Multiplicative.toAdd (M.ψQbar ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar)) := by
      intro g
      obtain ⟨k, rfl⟩ := M.φ_surj g
      rw [← M.ψQbar_actQ, hfix k k.2]
    have hψ : M.ψQbar ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) = 1 :=
      Multiplicative.toAdd.injective (burnsideJ7_fix_sigma _ hfixσ)
    have hHCbar : ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) ∈ M.HCbar := by
      rw [← M.ker_ψQbar]
      exact hψ
    refine M.mem_Q0.mpr ⟨hQ, hHCbar, ?_⟩
    show M.dQ ⟨M.nel, M.nel_mem_H⟩ ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) = 1
    rw [M.dQ_apply, hfix M.nel M.nel_mem_H, mul_inv_cancel]
  · intro hx
    obtain ⟨hxQ, hx0⟩ := M.mem_Q0.mp hx
    have hxH : h ∈ ruH M.T := (Subgroup.mem_inf.mp (M.Q0_le_HC hx)).1
    refine ⟨hxH, fun k hk => ?_⟩
    have hfix : ∀ (k : G) (hk : k ∈ ruH M.T),
        M.actQ ⟨k, hk⟩ ((⟨h, hxQ⟩ : ruQ M.T) : M.Qbar) = ((⟨h, hxQ⟩ : ruQ M.T) : M.Qbar) := by
      intro k hk
      by_cases hK : k ∈ M.K
      · exact M.actQ_HCbar_of_mem_K hK hx0.1
      · rw [M.actQ_HCbar_of_not_mem_K hk hK hx0.1]
        have h2 : M.dQ ⟨M.nel, M.nel_mem_H⟩ ((⟨h, hxQ⟩ : ruQ M.T) : M.Qbar) = 1 := hx0.2
        rwa [M.dQ_apply, mul_inv_eq_one] at h2
    have := hfix k⁻¹ (inv_mem hk)
    rw [M.actQ_mk, M.mk_eq_mk_iff] at this
    have e : h⁻¹ * k⁻¹ * h * k = (((k⁻¹ * h * k⁻¹⁻¹)⁻¹ * h))⁻¹ := by group
    rw [e]
    exact inv_mem this

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q0_closure {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Subgroup.closure {h : G | h ∈ ruH M.T ∧ ∀ x ∈ ruH M.T, h⁻¹ * x⁻¹ * h * x ∈ ruU M.L M.T} =
      M.Q0 := by
  rw [burnsideJ7_Q0_set, Subgroup.closure_eq]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_conj_mem_W0 {G : Type} [Group G] (M : RuDataM G) {L2 : Subgroup G}
    {l u : G} (hl : l ∈ L2) (hu : u ∈ ruU M.L M.T) :
    l * u * l⁻¹ ∈ ChIJK.conjClosure (ruU M.L M.T) L2 := by
  have h1 : l * u * l⁻¹ ∈ CFSG.conjugate (ruU M.L M.T) l⁻¹ := by
    refine ⟨u, hu, ?_⟩
    simp [MulAut.conj_apply]
  exact (le_iSup₂ (f := fun y (_ : y ∈ L2) => CFSG.conjugate (ruU M.L M.T) y) l⁻¹
    (inv_mem hl)) h1

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_W0_le_W {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ≤ M.W := by
  refine iSup₂_le fun y hy => ?_
  rintro _ ⟨u, hu, rfl⟩
  have hyG : y ∈ M.G2 := by
    rw [burnsideJ7_L2Ru_eq M hV2] at hy
    exact burnsideJ7_twoResidual_le _ hy
  exact M.conj_mem_W (inv_mem hyG) (M.U_le_W hu)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_c_mem_Q0 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ M.Q0 := by
  set t := ((⟨M.t1el, M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)⟩ : ruQ M.T) : M.Qbar)
  set x0 := M.dQ ⟨M.nel, M.nel_mem_H⟩ t
  have htC : t ∈ M.HCbar := M.t1bar_mem_HCbar
  have hx0C : x0 ∈ M.HCbar := by
    show M.actQ _ t * t⁻¹ ∈ M.HCbar
    exact mul_mem (M.actQ_mem_HCbar _ htC) (inv_mem htC)
  have hx0 : x0 ∈ M.Q0bar := by
    refine ⟨hx0C, ?_⟩
    show M.dQ ⟨M.nel, M.nel_mem_H⟩ x0 = 1
    rw [M.dQ_apply, mul_inv_eq_one]
    show M.actQ _ (M.actQ _ t * t⁻¹) = M.actQ _ t * t⁻¹
    rw [map_mul, map_inv, M.actQ_nel_nel htC]
    have hsq : ∀ y : M.Qbar, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (M.Qbar_sq y)
    rw [hsq t, hsq (M.actQ _ t), M.Qbar_comm]
  have hcQ : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ ruQ M.T :=
    mul_mem (M.conj_mem_Q M.nel_mem_H (M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)))
      (inv_mem (M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)))
  exact M.mem_Q0.mpr ⟨hcQ, hx0⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_chi_c {G : Type} [Group G] [Finite G] (M : RuDataM G)
    (hc : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ ruS M.L) :
    Multiplicative.toAdd (M.χ ⟨(M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹, hc⟩) =
      !![0, 0, 0; 0, 1, 0; 0, 0, 1] := by
  have ht1S := M.t1el_mem_S
  have hnt : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L M.nel.2) _).mp ht1S
  rw [show (⟨(M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹, hc⟩ : ruS M.L) =
    ⟨_, hnt⟩ * (⟨M.t1el, ht1S⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv]
  have h := M.χ_conj M.nel ⟨M.t1el, ht1S⟩
  simp only at h
  rw [h, M.θ_nel, M.χ_t1el, SL3.n0_b0mat]
  decide +kernel

@[expose] def burnsideJ7_b3mat : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def burnsideJ7_pairsW :
    List (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [(1, !![0, 1, 0; 0, 0, 0; 0, 0, 0]), (1, !![0, 0, 1; 0, 0, 0; 0, 0, 0]),
   (burnsideJ7_a3mat, !![0, 1, 0; 0, 0, 0; 0, 0, 0]),
   (burnsideJ7_a3mat, !![0, 0, 1; 0, 0, 0; 0, 0, 0]),
   (burnsideJ7_b3mat, !![0, 1, 0; 0, 0, 0; 0, 0, 0])]

@[expose] def burnsideJ7_gensW : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
   !![0, 0, 0; 0, 0, 1; 0, 0, 0], !![1, 1, 0; 1, 1, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 1]]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_gensW_spec : ∀ g ∈ burnsideJ7_gensW, g = !![0, 0, 0; 0, 1, 0; 0, 0, 1] ∨
    ∃ p ∈ burnsideJ7_pairsW, p.1 ∈ SL3.Pl ∧ p.1 ^ 3 = 1 ∧ SL3.IsRow0 p.2 ∧ stAct p.1 p.2 = g := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_span_W : ∀ A, SL3.IsM2 A → IsTraceZero A →
    burnsideJ7_inSpan burnsideJ7_gensW A = true := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_stAct_mem_chiAdd {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {V2 : Subgroup G} (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) {X : Subgroup G}
    (hX : ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ≤ X)
    {a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (ha : a ∈ SL3.Pl) (ha3 : a ^ 3 = 1)
    {E : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hE : SL3.IsRow0 E) :
    stAct a E ∈ burnsideJ7_chiAdd M X := by
  obtain ⟨l, hlL, hl2, hθ, -⟩ := burnsideJ7_exists_L2_lift3 M ha ha3
  have hl2' : l ∈ ChIJK.L2Ru M.L V2 := by
    rw [burnsideJ7_L2Ru_eq M hV2]
    exact hl2
  obtain ⟨s, hs⟩ := M.χ_surj E (SL3.row0_trace E hE)
  have hsU : (s : G) ∈ ruU M.L M.T := by
    rw [M.mem_U_iff s.2, hs, toAdd_ofAdd]
    exact hE
  have hlS : l ∈ Subgroup.normalizer (ruS M.L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hlL
  have hy : l * (s : G) * l⁻¹ ∈ ruS M.L := (Subgroup.mem_normalizer_iff.mp hlS _).mp s.2
  refine ⟨l * (s : G) * l⁻¹, hX (burnsideJ7_conj_mem_W0 M hl2' hsU), hy, ?_⟩
  have h1 := M.χ_conj ⟨l, hlL⟩ s
  simp only at h1
  rw [h1, hθ, hs, toAdd_ofAdd]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_W_le_W0Q0 {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 :
    Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    M.W ≤ ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ⊔ M.Q0 := by
  have hW0 : ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ≤
      ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ⊔ M.Q0 := le_sup_left
  have hUW0 : ruU M.L M.T ≤ ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) := by
    intro u hu
    have := burnsideJ7_conj_mem_W0 M (L2 := ChIJK.L2Ru M.L V2) (l := 1) (u := u) (one_mem _) hu
    simpa using this
  have hVX : ruV M.L ≤ ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ⊔ M.Q0 :=
    (M.V_le_U.trans hUW0).trans hW0
  refine burnsideJ7_W_le_of_chi M hVX fun A hA hAt => ?_
  refine burnsideJ7_mem_of_inSpan _ burnsideJ7_gensW ?_ A (burnsideJ7_span_W A hA hAt)
  intro g hg
  rcases burnsideJ7_gensW_spec g hg with rfl | ⟨p, -, hp1, hp3, hp4, rfl⟩
  · have hcQ := burnsideJ7_c_mem_Q0 M
    have hcS : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ ruS M.L := by
      have hnt : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ ∈ ruS M.L :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L M.nel.2) _).mp M.t1el_mem_S
      exact mul_mem hnt (inv_mem M.t1el_mem_S)
    exact ⟨_, Subgroup.mem_sup_right hcQ, hcS, burnsideJ7_chi_c M hcS⟩
  · exact burnsideJ7_stAct_mem_chiAdd M hV2 hW0 hp1 hp3 hp4

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_HRu_eq {G : Type} [Group G] [Finite G] {M : RuDataM G}
    (h : ChIJK.RuType G M.L (ruV M.L) (M.T : Subgroup G)) (hMT : M.T = h.sylowT) :
    ChIJK.HRu (M.T : Subgroup G) = ruH M.T := by
  rw [ChIJK.RuType.HRu_eq_ruH h, ← hMT]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_QRu_eq {G : Type} [Group G] [Finite G] {M : RuDataM G}
    (h : ChIJK.RuType G M.L (ruV M.L) (M.T : Subgroup G)) (hMT : M.T = h.sylowT) :
    ChIJK.QRu (M.T : Subgroup G) = ruQ M.T := by
  rw [ChIJK.RuType.QRu_eq_ruQ h, ← hMT]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_URu_eq {G : Type} [Group G] [Finite G] {M : RuDataM G}
    (h : ChIJK.RuType G M.L (ruV M.L) (M.T : Subgroup G)) (hMT : M.T = h.sylowT) :
    ChIJK.URu (ruV M.L) (M.T : Subgroup G) = ruU M.L M.T := by
  rw [ChIJK.RuType.URu_eq_ruU h, ← hMT]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_HCRu_eq {G : Type} [Group G] [Finite G] {M : RuDataM G}
    (h : ChIJK.RuType G M.L (ruV M.L) (M.T : Subgroup G)) (hMT : M.T = h.sylowT) :
    ChIJK.HCRu (ruV M.L) (M.T : Subgroup G) = M.HC := by
  rw [ChIJK.HCRu, burnsideJ7_HRu_eq h hMT, burnsideJ7_URu_eq h hMT]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q0Ru_eq {G : Type} [Group G] [Finite G] {M : RuDataM G}
    (h : ChIJK.RuType G M.L (ruV M.L) (M.T : Subgroup G)) (hMT : M.T = h.sylowT) :
    ChIJK.Q0Ru (ruV M.L) (M.T : Subgroup G) = M.Q0 := by
  rw [ChIJK.Q0Ru, burnsideJ7_HRu_eq h hMT, burnsideJ7_URu_eq h hMT, burnsideJ7_Q0_closure]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_WRu_eq {G : Type} [Group G] [Finite G] {M : RuDataM G}
    (h : ChIJK.RuType G M.L (ruV M.L) (M.T : Subgroup G)) (hMT : M.T = h.sylowT)
    {V2 : Subgroup G} (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.WRu M.L (ruV M.L) V2 (M.T : Subgroup G) = M.W := by
  rw [ChIJK.WRu, ChIJK.W0Ru, burnsideJ7_URu_eq h hMT, burnsideJ7_Q0Ru_eq h hMT]
  exact le_antisymm (sup_le (burnsideJ7_W0_le_W M hV2) M.Q0_le_W) (burnsideJ7_W_le_W0Q0 M hV2)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_W_section {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ChIJK.IsElemAbelianSection M.W (ruV M.L) 6 := by
  refine ⟨fun v hv => M.U_le_W (M.V_le_U hv), fun x hx => M.sq_mem_V (M.W_le_S hx),
    fun x hx y hy => M.comm_mem_V (M.W_le_S hx) (M.W_le_S hy), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (ruV M.L) M.W
  rw [inf_eq_left.mpr (fun v hv => M.U_le_W (M.V_le_U hv)), M.toRuData.card_V, M.card_W] at h1
  omega

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_R0_Pl_isM2 : ∀ a ∈ SL3.Pl, ∀ r ∈ SL3.R0,
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), SL3.IsRow0 A →
      SL3.IsM2 (stAct r (stAct a A) + stAct a A) := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_Q_conjU_mem_W {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {l : G}
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) {q u : G} (hq : q ∈ ruQ M.T)
    (hu : u ∈ M.conjU l) : u * (q * u⁻¹ * q⁻¹) ∈ M.W := by
  have hqL : q ∈ M.L := (M.Q_le_LT1.trans M.LT1_le_L) hq
  have hqR0 : M.θ ⟨q, hqL⟩ ∈ SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨q, hqL⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have huS : u ∈ ruS M.L := M.conjU_le_S hlL hu
  have hu' : q * u⁻¹ * q⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hqL) _).mp (inv_mem huS)
  refine ⟨mul_mem huS hu', ?_⟩
  rw [show (⟨u * (q * u⁻¹ * q⁻¹), mul_mem huS hu'⟩ : ruS M.L) =
    ⟨u, huS⟩ * ⟨q * u⁻¹ * q⁻¹, hu'⟩ from rfl, M.toAdd_χ_mul]
  have h := M.χ_conj ⟨q, hqL⟩ ⟨u⁻¹, inv_mem huS⟩
  simp only at h
  rw [h, show (⟨u⁻¹, inv_mem huS⟩ : ruS M.L) = (⟨u, huS⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_inv]
  have h0 : l⁻¹ * u * l ∈ ruU M.L M.T := M.mem_conjU.mp hu
  have h0S := M.U_le_S h0
  have hrow := (M.mem_U_iff h0S).mp h0
  have hc := M.χ_conj ⟨l, hlL⟩ ⟨l⁻¹ * u * l, h0S⟩
  simp only at hc
  have hc' : Multiplicative.toAdd (M.χ ⟨u, huS⟩) =
      stAct (M.θ ⟨l, hlL⟩) (Multiplicative.toAdd (M.χ ⟨l⁻¹ * u * l, h0S⟩)) := by
    rw [← hc]
    congr 3
    group
  rw [hc', add_comm]
  exact burnsideJ7_comm_R0_Pl_isM2 _ hlPl _ hqR0 _ hrow

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q5_inf_S_le_W {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b v l : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) (hv : v ∈ M.conjU l) (hvQ : v ∉ ruQ M.T)
    (hvb : v * b * v⁻¹ = b ^ 4) : M.Q5 hbH ⊓ ruS M.L ≤ M.W := by
  have hvS : v ∈ ruS M.L := M.conjU_le_S hlL hv
  have hvH : v ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hvS)
  have hvK : v ∈ M.K := M.S_le_K hvS
  set X : Subgroup G := (((M.dQ ⟨v, hvH⟩).range).comap
    (QuotientGroup.mk' M.UQ)).map (ruQ M.T).subtype with hXdef
  have hvb' : v * b * v⁻¹ = b ^ 4 * 1 := by rw [hvb, mul_one]
  have hXQ5 : X ≤ M.Q5 hbH := by
    rintro _ ⟨x, hx, rfl⟩
    refine (M.mem_Q5 hbH).mpr ⟨x.2, ?_⟩
    have hrange := M.dQ_range_le_Q5bar hbH hb5 hvK (one_mem _) hvb'
    exact hrange hx
  have hXW : X ≤ M.W := by
    rintro _ ⟨x, ⟨a, ha⟩, rfl⟩
    induction a using QuotientGroup.induction_on with
    | H a =>
    have ha' : M.dQ ⟨v, hvH⟩ (a : M.Qbar) = (x : M.Qbar) := ha
    rw [M.dQ_apply, M.actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      M.mk_eq_mk_iff] at ha'
    have hc := burnsideJ7_comm_Q_conjU_mem_W M hlL hlPl a.2 hv
    have e : (x : G) = (v * (a * v⁻¹ * (a : G)⁻¹)) * ((v * a * v⁻¹ * (a : G)⁻¹)⁻¹ * x) := by
      group
    show (x : G) ∈ M.W
    rw [e]
    refine mul_mem hc (M.U_le_W ?_)
    have : ((M.conjQ ⟨v, hvH⟩ a * a⁻¹ : ruQ M.T) : G) = v * a * v⁻¹ * (a : G)⁻¹ := rfl
    rw [← this]
    exact ha'
  have hcard : 2 ^ 7 ≤ Nat.card X := by
    rw [Subgroup.card_map_of_injective (ruQ M.T).subtype_injective]
    have h := QuotientGroup.card_preimage_mk M.UQ
      ((M.dQ ⟨v, hvH⟩).range : Set M.Qbar)
    have hpre : (QuotientGroup.mk : ruQ M.T → M.Qbar) ⁻¹'
        ((M.dQ ⟨v, hvH⟩).range : Set M.Qbar) =
        ((((M.dQ ⟨v, hvH⟩).range).comap (QuotientGroup.mk' M.UQ)) :
          Set (ruQ M.T)) := rfl
    rw [hpre, card_subgroupOf_of_le M.U_le_Q, M.toRuData.card_U] at h
    have h4 := M.four_le_card_dQ_range hvH hvQ
    have h1 : Nat.card (((M.dQ ⟨v, hvH⟩).range : Set M.Qbar)) =
        Nat.card (M.dQ ⟨v, hvH⟩).range := rfl
    have h2 : Nat.card ((((M.dQ ⟨v, hvH⟩).range).comap
        (QuotientGroup.mk' M.UQ)) : Set (ruQ M.T)) =
        Nat.card (((M.dQ ⟨v, hvH⟩).range).comap (QuotientGroup.mk' M.UQ)) := rfl
    rw [h1, h2] at h
    rw [h]
    omega
  have hle : X ≤ M.Q5 hbH ⊓ ruS M.L := le_inf hXQ5 (hXW.trans M.W_le_S)
  have heq : X = M.Q5 hbH ⊓ ruS M.L :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [M.card_Q5_inf_S hbH hb5]; exact hcard)
  rw [← heq]
  exact hXW

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_surj_five : ∀ g : SigmaL2F4, g ^ 5 = 1 → g ≠ 1 →
    ∀ w : Fin 2 → CFSG.Quasithin.RuType.F4, ∃ v, v + sigmaAct g v = w := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_exists_formB : ∃ w : Fin 2 → CFSG.Quasithin.RuType.F4,
    Sigma.formB w ![1, 0] = 1 := by
  decide +kernel

private theorem burnsideJ7_comm_normalized {G : Type} [Group G] {Q B : Subgroup G} {q : G} (hq
    : q ∈ Q)
    {n : G} (hn : n ∈ ⁅Q, B⁆) : q * n * q⁻¹ ∈ ⁅Q, B⁆ := by
  rw [Subgroup.commutator_def] at hn
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, k, hk, rfl⟩ := hx
    have h1 : q * h * k * (q * h)⁻¹ * k⁻¹ ∈ ⁅Q, B⁆ :=
      Subgroup.commutator_mem_commutator (mul_mem hq hh) hk
    have h2 : q * k * q⁻¹ * k⁻¹ ∈ ⁅Q, B⁆ := Subgroup.commutator_mem_commutator hq hk
    have := mul_mem h1 (inv_mem h2)
    convert this using 1
    simp only [commutatorElement_def]
    group
  | one => simpa using (one_mem _)
  | mul x y _ _ hx hy =>
    have e : q * (x * y) * q⁻¹ = (q * x * q⁻¹) * (q * y * q⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : q * x⁻¹ * q⁻¹ = (q * x * q⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_U_le_comm {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ruU M.L M.T ≤ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
  set N := ⁅ruQ M.T, Subgroup.zpowers b⁆ with hN
  have hbB : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
  have hg5 := M.φ_b_props hbH hb5
  have hsurj := burnsideJ7_surj_five (M.φ ⟨b, hbH⟩) hg5.1 hg5.2
  have hcomm : ∀ w : Fin 2 → CFSG.Quasithin.RuType.F4, ∃ u' : ruU M.L M.T,
      ∃ hc : (u' : G) * (b * (u' : G)⁻¹ * b⁻¹) ∈ ruU M.L M.T,
      (u' : G) * (b * (u' : G)⁻¹ * b⁻¹) ∈ N ∧
      Multiplicative.toAdd (M.ψU ⟨(u' : G) * (b * (u' : G)⁻¹ * b⁻¹), hc⟩) = w := by
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    obtain ⟨u', hu'⟩ := M.ψU_surj (Multiplicative.ofAdd v)
    have hc : (u' : G) * (b * (u' : G)⁻¹ * b⁻¹) ∈ ruU M.L M.T :=
      mul_mem u'.2 (M.conj_mem_U hbH (inv_mem u'.2))
    refine ⟨u', hc, ?_, ?_⟩
    · have := Subgroup.commutator_mem_commutator (H₁ := ruQ M.T) (H₂ := Subgroup.zpowers b)
        (M.U_le_Q u'.2) hbB
      have e : (u' : G) * (b * (u' : G)⁻¹ * b⁻¹) = (u' : G) * b * (u' : G)⁻¹ * b⁻¹ := by group
      rw [e]
      exact this
    · have e : (⟨(u' : G) * (b * (u' : G)⁻¹ * b⁻¹), hc⟩ : ruU M.L M.T) =
          u' * ⟨b * (u' : G)⁻¹ * b⁻¹, M.conj_mem_U hbH (inv_mem u'.2)⟩ := rfl
      rw [e, map_mul, toAdd_mul]
      have h1 := M.ψU_conj ⟨b, hbH⟩ u'⁻¹
      have h2 : (⟨b * (u' : G)⁻¹ * b⁻¹, M.conj_mem_U hbH (inv_mem u'.2)⟩ : ruU M.L M.T) =
          ⟨(⟨b, hbH⟩ : ruH M.T) * ((u'⁻¹ : ruU M.L M.T) : G) * ((⟨b, hbH⟩ : ruH M.T) : G)⁻¹,
            M.conj_mem_U hbH (inv_mem u'.2)⟩ := rfl
      rw [h2, h1, M.toAdd_ψU_inv, hu', toAdd_ofAdd]
      exact hv
  have hzN : M.z ∈ N := by
    obtain ⟨u', hc, hcN, hψ⟩ := hcomm ![1, 0]
    obtain ⟨w₁, hw₁⟩ := burnsideJ7_exists_formB
    obtain ⟨q, hq, hqe⟩ := M.exists_comm_eq w₁
    set u0 : ruU M.L M.T := ⟨(u' : G) * (b * (u' : G)⁻¹ * b⁻¹), hc⟩ with hu0
    have hz := hqe u0
    rw [hψ, hw₁] at hz
    have hz1 : (q : G) * u0 * (q : G)⁻¹ * (u0 : G)⁻¹ ≠ 1 := by
      intro h1
      rw [h1] at hz
      have : zval (1 : G) = 0 := (zval_eq_zero_iff 1).mpr rfl
      rw [this] at hz
      exact zero_ne_one hz
    have hzmem : (q : G) * u0 * (q : G)⁻¹ * (u0 : G)⁻¹ ∈ ruZ M.T := M.comm_mem_Z hq u0.2
    have hzeq : (q : G) * u0 * (q : G)⁻¹ * (u0 : G)⁻¹ = M.z := by
      rcases M.mem_Z_iff.mp hzmem with h1 | h1
      · exact absurd h1 hz1
      · exact h1
    rw [← hzeq]
    exact mul_mem (burnsideJ7_comm_normalized hq hcN) (inv_mem hcN)
  intro u hu
  obtain ⟨u', hc, hcN, hψ⟩ := hcomm (Multiplicative.toAdd (M.ψU ⟨u, hu⟩))
  set u0 : ruU M.L M.T := ⟨(u' : G) * (b * (u' : G)⁻¹ * b⁻¹), hc⟩ with hu0
  have hψeq : M.ψU u0 = M.ψU ⟨u, hu⟩ := Multiplicative.toAdd.injective hψ
  have hzmem : (u0 : G)⁻¹ * u ∈ ruZ M.T := by
    have : M.ψU (u0⁻¹ * ⟨u, hu⟩) = 1 := by rw [map_mul, map_inv, hψeq, inv_mul_cancel]
    exact (M.ψU_eq_one_iff _).mp this
  have : u = (u0 : G) * ((u0 : G)⁻¹ * u) := by group
  rw [this]
  refine mul_mem hcN ?_
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · rw [h1]
    exact one_mem _
  · rw [h1]
    exact hzN

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_dQ_zpowers_range_le {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {b : G}
    (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) {y : G} (hy : y ∈ Subgroup.zpowers b)
    (hyH : y ∈ ruH M.T) : (M.dQ ⟨y, hyH⟩).range ≤ (M.dQ ⟨b, hbH⟩).range := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨m, hm⟩ := exists_nat_zpow (n := 5) (by norm_num) (pow_five_of_orderOf hb5) k
  have e : (⟨b ^ k, hyH⟩ : ruH M.T) = (⟨b, hbH⟩ : ruH M.T) ^ m := Subtype.ext (by simp [hm])
  rw [e]
  exact M.dQ_pow_range_le _ m

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_eq_Q5 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ⁅ruQ M.T, Subgroup.zpowers b⁆ = M.Q5 hbH := by
  have hbB : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro q hq y hy
    show q * y * q⁻¹ * y⁻¹ ∈ M.Q5 hbH
    have hyH : y ∈ ruH M.T := (Subgroup.zpowers_le.mpr hbH) hy
    have hQ : q * y * q⁻¹ * y⁻¹ ∈ ruQ M.T := by
      have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hq (M.conj_mem_Q hyH (inv_mem hq))
    refine (M.mem_Q5 hbH).mpr ⟨hQ, ?_⟩
    have hrange := burnsideJ7_dQ_zpowers_range_le M hbH hb5 hy hyH
    have e : ((⟨q * y * q⁻¹ * y⁻¹, hQ⟩ : ruQ M.T) : M.Qbar) =
        (M.dQ ⟨y, hyH⟩ ((⟨q, hq⟩ : ruQ M.T) : M.Qbar))⁻¹ := by
      rw [M.dQ_apply, M.actQ_mk]
      show ((⟨q * y * q⁻¹ * y⁻¹, hQ⟩ : ruQ M.T) : M.Qbar) = _
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show q * y * q⁻¹ * y⁻¹ = (((y * q * y⁻¹) * q⁻¹)⁻¹ : G)
      group
    rw [e]
    exact inv_mem (hrange ⟨_, rfl⟩)
  · intro x hx
    obtain ⟨hxQ, hxb⟩ := (M.mem_Q5 hbH).mp hx
    obtain ⟨c', hc'⟩ := hxb
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c'
    have hcQ : (c : G) ∈ ruQ M.T := c.2
    rw [M.dQ_apply, M.actQ_mk] at hc'
    have e1 : ((M.conjQ ⟨b, hbH⟩ c : ruQ M.T) : M.Qbar) * ((c : ruQ M.T) : M.Qbar)⁻¹ =
        (((M.conjQ ⟨b, hbH⟩ c) * c⁻¹ : ruQ M.T) : M.Qbar) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [e1, M.mk_eq_mk_iff] at hc'
    have hcomm : b * (c : G) * b⁻¹ * (c : G)⁻¹ ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
      have := Subgroup.commutator_mem_commutator (H₁ := Subgroup.zpowers b) (H₂ := ruQ M.T)
        hbB hcQ
      rw [Subgroup.commutator_comm] at this
      exact this
    have hU : (b * (c : G) * b⁻¹ * (c : G)⁻¹)⁻¹ * x ∈ ruU M.L M.T := hc'
    have : x = (b * (c : G) * b⁻¹ * (c : G)⁻¹) * ((b * (c : G) * b⁻¹ * (c : G)⁻¹)⁻¹ * x) := by
      group
    rw [this]
    exact mul_mem hcomm (burnsideJ7_U_le_comm M hbH hb5 hU)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_sylow5_cyclic {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {B5 : Subgroup G} (hB5 : ChIJK.IsSylowIn 5 B5 (ruH M.T)) :
    ∃ b : G, b ∈ ruH M.T ∧ orderOf b = 5 ∧ B5 = Subgroup.zpowers b := by
  obtain ⟨hle, hp, hidx⟩ := hB5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
  have h1 := Subgroup.card_mul_index (B5.subgroupOf (ruH M.T))
  rw [card_subgroupOf_of_le hle, hk, M.card_H] at h1
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exfalso
        apply hidx
        rw [pow_zero, one_mul] at h1
        rw [h1]
        norm_num
      · rfl
    · exfalso
      have : 5 ^ 2 ∣ 2 ^ 11 * 120 := by
        rw [← h1]
        exact Dvd.dvd.mul_right (pow_dvd_pow 5 hk2) _
      norm_num at this
  subst hk1
  have hcard : Nat.card B5 = 5 := by rw [hk]; norm_num
  have h5 : 1 < Nat.card B5 := by rw [hcard]; norm_num
  haveI : Nontrivial B5 := Finite.one_lt_card_iff_nontrivial.mp h5
  obtain ⟨⟨b, hb⟩, hb1⟩ := exists_ne (1 : B5)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hord : orderOf b = 5 := by
    have hd : orderOf b ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard B5 hb
      rwa [hcard] at this
    rcases (Nat.dvd_prime (by norm_num)).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1'
    · exact h
  refine ⟨b, hle hb, hord, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) ?_
  rw [Nat.card_zpowers, hord, hcard]

private theorem burnsideJ7_P0_eq_mul : ∀ p ∈ CFSG.Quasithin.RuType.SL3.P0,
    ∃ r ∈ CFSG.Quasithin.RuType.SL3.R2m, ∃ r' ∈ CFSG.Quasithin.RuType.SL3.R0, r * r' = p := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_T_eq_pullP0 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    (M.T : Subgroup G) = pullL M.L M.θ SL3.P0 := by
  have hle : (M.T : Subgroup G) ≤ pullL M.L M.θ SL3.P0 := fun t ht =>
    mem_pullL.mpr ⟨M.toRuData.T_le_L ht, M.θ_mem_P0 ht⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [burnsideJ7_card_T, M.card_pullL, SL3.card_P0]
    norm_num)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_T_eq_R2_sup_Q {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    (M.T : Subgroup G) = M.R2 ⊔ ruQ M.T := by
  apply le_antisymm
  · intro x hx
    rw [burnsideJ7_T_eq_pullP0] at hx
    obtain ⟨hxL, hxP⟩ := mem_pullL.mp hx
    obtain ⟨r, hr, r', hr', hrr⟩ := burnsideJ7_P0_eq_mul _ hxP
    obtain ⟨a, ha⟩ := M.θ_surj r
    have haR : (a : G) ∈ M.R2 := mem_pullL.mpr ⟨a.2, by rw [ha]; exact hr⟩
    have hr'Q : r' ∈ ((ruQ M.T).subgroupOf M.L).map M.θ := by rw [M.θQ_eq]; exact hr'
    obtain ⟨q, hq, hqθ⟩ := hr'Q
    have hqQ : (q : G) ∈ ruQ M.T := hq
    have hk : (a * q)⁻¹ * (⟨x, hxL⟩ : M.L) ∈ M.θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, ha, hqθ, hrr, inv_mul_cancel]
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
    have hS : (((a * q)⁻¹ * (⟨x, hxL⟩ : M.L) : M.L) : G) ∈ M.R2 := M.S_le_R2 hk
    have e : x = (a : G) * (q : G) * (((a * q)⁻¹ * (⟨x, hxL⟩ : M.L) : M.L) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left haR) (Subgroup.mem_sup_right hqQ))
      (Subgroup.mem_sup_left hS)
  · refine sup_le ?_ M.Q_le_T
    intro x hx
    rw [burnsideJ7_T_eq_pullP0]
    obtain ⟨hxL, hxR⟩ := mem_pullL.mp hx
    exact mem_pullL.mpr ⟨hxL, SL3.R2m_le_P0 hxR⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_W_section_U {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ChIJK.IsElemAbelianSection M.W (ruU M.L M.T) 4 := by
  have hUW := M.U_le_W
  refine ⟨hUW, fun x hx => M.V_le_U (M.sq_mem_V (M.W_le_S hx)),
    fun x hx y hy => M.V_le_U (M.comm_mem_V (M.W_le_S hx) (M.W_le_S hy)), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (ruU M.L M.T) M.W
  rw [inf_eq_left.mpr hUW, M.toRuData.card_U, M.card_W] at h1
  omega

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q5_section {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b v l : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) (hv : v ∈ M.conjU l) (hvQ : v ∉ ruQ M.T)
    (hvb : v * b * v⁻¹ = b ^ 4) :
    ChIJK.IsElemAbelianSection (M.Q5 hbH) (M.Q5 hbH ⊓ M.W) 2 := by
  have hUQ5 := M.U_le_Q5 hbH
  have hUW := M.U_le_W
  have hinf : M.Q5 hbH ⊓ M.W = M.Q5 hbH ⊓ ruS M.L :=
    le_antisymm (inf_le_inf_left _ M.W_le_S)
      (le_inf inf_le_left (burnsideJ7_Q5_inf_S_le_W M hbH hb5 hlL hlPl hv hvQ hvb))
  refine ⟨inf_le_left, fun x hx => ?_, fun x hx y hy => ?_, ?_⟩
  · have := (M.two.QU_elem x (M.Q5_le_Q hbH hx) x (M.Q5_le_Q hbH hx)).2
    exact ⟨hUQ5 this, hUW this⟩
  · have := (M.two.QU_elem x (M.Q5_le_Q hbH hx) y (M.Q5_le_Q hbH hy)).1
    exact ⟨hUQ5 this, hUW this⟩
  · have h1 := Subgroup.relIndex_mul_card (M.Q5 hbH ⊓ M.W) (M.Q5 hbH)
    have hc : Nat.card ↥(M.Q5 hbH ⊓ M.W) = 2 ^ 7 := by
      rw [hinf]
      exact M.card_Q5_inf_S hbH hb5
    rw [inf_eq_left.mpr (inf_le_left : M.Q5 hbH ⊓ M.W ≤ M.Q5 hbH), M.card_Q5 hbH hb5, hc] at h1
    omega

private theorem burnsideJ7_mul_mem_of_relIndex_two {G : Type} [Group G] {D K : Subgroup G}
    (hD : D.relIndex K = 2) {a b : G} (ha : a ∈ K) (hb : b ∈ K) (haD : a ∉ D) (hbD : b ∉ D) :
    a * b ∈ D := by
  have h := (Subgroup.mul_mem_iff_of_index_two (H := D.subgroupOf K) hD
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).mpr (by simp [Subgroup.mem_subgroupOf, haD, hbD])
  exact Subgroup.mem_subgroupOf.mp h

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_g_facts {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) {g : G} (hg : g ∈ ChIJK.L2Ru M.L V2)
    (hgH : g ∉ ruH M.T) :
    ∃ hlL : g⁻¹ ∈ M.L, M.θ ⟨g⁻¹, hlL⟩ ∈ SL3.Pl ∧ M.conjU g⁻¹ ≠ ruU M.L M.T := by
  have hgL2 : g ∈ ChIJK.twoResidual M.G2 := by
    rw [← burnsideJ7_L2Ru_eq M hV2]
    exact hg
  have hgG2 : g ∈ M.G2 := burnsideJ7_twoResidual_le _ hgL2
  obtain ⟨hgL, hgPl⟩ := mem_pullL.mp hgG2
  have hlL : g⁻¹ ∈ M.L := inv_mem hgL
  refine ⟨hlL, ?_, ?_⟩
  · have : M.θ ⟨g⁻¹, hlL⟩ = (M.θ ⟨g, hgL⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact inv_mem hgPl
  · intro heq
    have := (M.conjU_eq_U_iff hlL).mp heq
    rw [← M.L_inf_H] at this
    exact hgH (by simpa using inv_mem (Subgroup.mem_inf.mp this).2)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_clause5 {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) {g : G} (hg : g ∈ ChIJK.L2Ru M.L V2)
    (hgH : g ∉ ruH M.T) :
    ruV M.L = CFSG.conjugate (ruU M.L M.T) g ⊓ M.HC := by
  obtain ⟨hlL, -, hne⟩ := burnsideJ7_g_facts M hV2 hg hgH
  exact (M.conjU_inf_HC hlL hne).symm

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_relIndex_D {G : Type} [Group G] [Finite G] (M : RuDataM G) {l : G}
    (hlL : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) :
    (M.conjU l ⊓ ruQ M.T).relIndex (M.conjU l) = 2 := by
  have h1 := Subgroup.relIndex_mul_card (M.conjU l ⊓ ruQ M.T) (M.conjU l)
  rw [inf_eq_left.mpr (inf_le_left : M.conjU l ⊓ ruQ M.T ≤ M.conjU l),
    M.card_conjU_inf_Q hlL hne, M.card_conjU, M.toRuData.card_U] at h1
  omega

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q_normalizes_Q5 {G : Type} [Group G] [Finite G] (M : RuDataM G) {b : G}
    (hbH : b ∈ ruH M.T) {d x : G} (hd : d ∈ ruQ M.T) (hx : x ∈ M.Q5 hbH) :
    d * x * d⁻¹ ∈ M.Q5 hbH := by
  have h1 : d * x * d⁻¹ * x⁻¹ ∈ ruU M.L M.T :=
    (M.two.QU_elem d hd x (M.Q5_le_Q hbH hx)).1
  have : d * x * d⁻¹ = (d * x * d⁻¹ * x⁻¹) * x := by group
  rw [this]
  exact mul_mem (M.U_le_Q5 hbH h1) hx

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_class {G : Type} [Group G] [Finite G] (M : RuDataM G) {y q : G}
    (hyH : y ∈ ruH M.T) (hq : q ∈ ruQ M.T) (hQ : q * y * q⁻¹ * y⁻¹ ∈ ruQ M.T) :
    ((⟨q * y * q⁻¹ * y⁻¹, hQ⟩ : ruQ M.T) : M.Qbar) =
      (M.dQ ⟨y, hyH⟩ ((⟨q, hq⟩ : ruQ M.T) : M.Qbar))⁻¹ := by
  rw [M.dQ_apply, M.actQ_mk]
  show ((⟨q * y * q⁻¹ * y⁻¹, hQ⟩ : ruQ M.T) : M.Qbar) = _
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  show q * y * q⁻¹ * y⁻¹ = (((y * q * y⁻¹) * q⁻¹)⁻¹ : G)
  group

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_le_Q5 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b v l : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
    (hlL : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) (hv : v ∈ M.conjU l) (hvQ : v ∉ ruQ M.T)
    (hvb : v * b * v⁻¹ = b ^ 4) : ⁅ruQ M.T, M.conjU l⁆ ≤ M.Q5 hbH := by
  have hvS : v ∈ ruS M.L := M.conjU_le_S hlL hv
  have hvH : v ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hvS)
  have hvK : v ∈ M.K := M.S_le_K hvS
  have hvb' : v * b * v⁻¹ = b ^ 4 * 1 := by rw [hvb, mul_one]
  have hrange := M.dQ_range_le_Q5bar hbH hb5 hvK (one_mem _) hvb'
  have hqv : ∀ q ∈ ruQ M.T, q * v * q⁻¹ * v⁻¹ ∈ M.Q5 hbH := by
    intro q hq
    have hQ : q * v * q⁻¹ * v⁻¹ ∈ ruQ M.T := by
      have e : q * v * q⁻¹ * v⁻¹ = q * (v * q⁻¹ * v⁻¹) := by group
      rw [e]
      exact mul_mem hq (M.conj_mem_Q hvH (inv_mem hq))
    refine (M.mem_Q5 hbH).mpr ⟨hQ, ?_⟩
    rw [burnsideJ7_comm_class M hvH hq hQ]
    exact inv_mem (hrange ⟨_, rfl⟩)
  rw [Subgroup.commutator_le]
  intro q hq u hu
  show q * u * q⁻¹ * u⁻¹ ∈ M.Q5 hbH
  by_cases huQ : u ∈ ruQ M.T
  · exact M.U_le_Q5 hbH ((M.two.QU_elem q hq u huQ).1)
  · have hD := burnsideJ7_relIndex_D M hlL hne
    have hvinvQ : v⁻¹ ∉ M.conjU l ⊓ ruQ M.T := by
      intro h
      have h2 : v⁻¹ ∈ ruQ M.T := h.2
      have := (ruQ M.T).inv_mem h2
      exact hvQ (by simpa using this)
    have hd : u * v⁻¹ ∈ M.conjU l ⊓ ruQ M.T :=
      burnsideJ7_mul_mem_of_relIndex_two hD hu (inv_mem hv) (fun h => huQ h.2) hvinvQ
    have hdQ : u * v⁻¹ ∈ ruQ M.T := hd.2
    have e : q * u * q⁻¹ * u⁻¹ = (q * (u * v⁻¹) * q⁻¹ * (u * v⁻¹)⁻¹) *
        ((u * v⁻¹) * (q * v * q⁻¹ * v⁻¹) * (u * v⁻¹)⁻¹) := by group
    rw [e]
    exact mul_mem (M.U_le_Q5 hbH ((M.two.QU_elem q hq _ hdQ).1))
      (burnsideJ7_Q_normalizes_Q5 M hbH hdQ (hqv q hq))

private theorem burnsideJ7_centralizer_zpowers {G : Type} [Group G] (b : G) :
    Subgroup.centralizer (↑(Subgroup.zpowers b) : Set G) = Subgroup.centralizer ({b} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_HC_cover {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) {c : G} (hc : c ∈ M.HC) :
    ∃ n ∈ ruU M.L M.T, c * n ∈ M.T5 b := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbU : ∀ n ∈ ruU M.L M.T, b * n * b⁻¹ ∈ ruU M.L M.T := fun n hn => M.conj_mem_U hbH hn
  have hy : c⁻¹ * (b * c * b⁻¹) ∈ ruU M.L M.T :=
    M.conj_HC_of_mem_K (RuDataM.b_mem_K hbH hb5) hc
  have hU5 : ¬ 5 ∣ Nat.card (ruU M.L M.T) := by rw [M.toRuData.card_U]; norm_num
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset (pow_five_of_orderOf hb5) hbU hy hU5
  refine ⟨n, hn, ⟨mul_mem (M.HC_le_Q hc) (M.U_le_Q hn), mem_G5.mpr ?_⟩⟩
  calc c * n * b = b * (c * n) * b⁻¹ * b := by rw [hfix]
    _ = b * (c * n) := by group

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q_eq_sup {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ruQ M.T = ruQ M.T ⊓ Subgroup.centralizer (↑(Subgroup.zpowers b) : Set G) ⊔
      ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
  rw [burnsideJ7_comm_eq_Q5 M hbH hb5, burnsideJ7_centralizer_zpowers]
  apply le_antisymm
  · intro q hq
    obtain ⟨a, ha, c, hc, rfl⟩ := M.exists_Q5_mul_HC hbH hb5 hq
    obtain ⟨n, hn, hcn⟩ := burnsideJ7_HC_cover M hbH hb5 hc
    have e : a * c = a * (c * n) * n⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hcn))
      (Subgroup.mem_sup_right (M.U_le_Q5 hbH (inv_mem hn)))
  · exact sup_le inf_le_left (M.Q5_le_Q hbH)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_T5U_inf_Q5 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    (ruQ M.T ⊓ Subgroup.centralizer (↑(Subgroup.zpowers b) : Set G) ⊔ ruU M.L M.T) ⊓
      ⁅ruQ M.T, Subgroup.zpowers b⁆ = ruU M.L M.T := by
  rw [burnsideJ7_comm_eq_Q5 M hbH hb5, burnsideJ7_centralizer_zpowers]
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have hxHC : x ∈ M.HC := by
      refine (sup_le ?_ M.U_le_HC) hx1
      exact fun y hy => RuDataM.T5_le_HC hbH hb5 hy
    rw [← M.Q5_inf_HC hbH hb5]
    exact ⟨hx2, hxHC⟩
  · exact le_inf (le_sup_right) (M.U_le_Q5 hbH)

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_quaternion {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    Nonempty (↥(ruQ M.T ⊓ Subgroup.centralizer (↑(Subgroup.zpowers b) : Set G)) ≃*
      QuaternionGroup 2) := by
  obtain ⟨e⟩ := RuDataM.T5_quaternion (M := M) hbH hb5
  refine ⟨(MulEquiv.subgroupCongr ?_).trans e⟩
  rw [burnsideJ7_centralizer_zpowers]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_Q5_section_U {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ruU M.L M.T ≤ ⁅ruQ M.T, Subgroup.zpowers b⁆ ∧
      ChIJK.IsElemAbelianSection ⁅ruQ M.T, Subgroup.zpowers b⁆ (ruU M.L M.T) 4 := by
  rw [burnsideJ7_comm_eq_Q5 M hbH hb5]
  have hU := M.U_le_Q5 hbH
  refine ⟨hU, hU, fun x hx => (M.two.QU_elem x (M.Q5_le_Q hbH hx) x (M.Q5_le_Q hbH hx)).2,
    fun x hx y hy => (M.two.QU_elem x (M.Q5_le_Q hbH hx) y (M.Q5_le_Q hbH hy)).1, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (ruU M.L M.T) (M.Q5 hbH)
  rw [inf_eq_left.mpr hU, M.toRuData.card_U, M.card_Q5 hbH hb5] at h1
  omega

@[expose] def burnsideJ7_p0 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_p0_mem : burnsideJ7_p0 ∈ SL3.R0 := by
  decide

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_p0_fix : ∀ y : Fin 3 → ZMod 2, y 2 = 0 → natAct3 burnsideJ7_p0 y = y
    := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_D1 : ∀ a ∈ SL3.Pl, ∀ r ∈ SL3.R0,
    (∀ y : Fin 3 → ZMod 2, y 2 = 0 → natAct3 r y = y) →
    ∀ A₀ : Matrix (Fin 3) (Fin 3) (ZMod 2), SL3.IsRow0 A₀ →
      SL3.IsRow0 (stAct a⁻¹ (stAct r (stAct a A₀) + stAct a A₀)) := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_D2 : ∀ a ∈ SL3.Pl, a ∉ SL3.Stab0 →
    ∃ A₀ : Matrix (Fin 3) (Fin 3) (ZMod 2), SL3.IsRow0 A₀ ∧
      ¬ SL3.IsRow0 (stAct burnsideJ7_p0 (stAct a A₀) + stAct a A₀) := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_stAct_stAct_inv (a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : stAct a (stAct a⁻¹ A) = A := by
  rw [← SL3.stAct_mul, mul_inv_cancel, SL3.stAct_one]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_mem_conjU_iff {G : Type} [Group G] [Finite G] (M : RuDataM G) {l : G}
    (hlL : l ∈ M.L) {x : G} (hx : x ∈ ruS M.L) :
    x ∈ M.conjU l ↔
      SL3.IsRow0 (stAct (M.θ ⟨l, hlL⟩)⁻¹ (Multiplicative.toAdd (M.χ ⟨x, hx⟩))) := by
  have hlS : l⁻¹ ∈ Subgroup.normalizer (ruS M.L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L (inv_mem hlL)
  have hx' : l⁻¹ * x * l ∈ ruS M.L := by
    have := (Subgroup.mem_normalizer_iff.mp hlS x).mp hx
    simpa using this
  rw [M.mem_conjU, M.mem_U_iff hx']
  have h1 := M.χ_conj ⟨l⁻¹, inv_mem hlL⟩ ⟨x, hx⟩
  simp only [inv_inv] at h1
  have e : M.θ ⟨l⁻¹, inv_mem hlL⟩ = (M.θ ⟨l, hlL⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at h1
  rw [h1]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_C_fix {G : Type} [Group G] [Finite G] (M : RuDataM G) {c : G}
    (hc : c ∈ ruQ M.T ⊓ Subgroup.centralizer (↑(burnsideJ7_V2pl M) : Set G)) :
    ∃ hcL : c ∈ M.L, ∀ y : Fin 3 → ZMod 2, y 2 = 0 → natAct3 (M.θ ⟨c, hcL⟩) y = y := by
  have hcL : c ∈ M.L := M.Q_le_L hc.1
  refine ⟨hcL, fun y hy => ?_⟩
  set x : ruV M.L := M.ψV.symm (Multiplicative.ofAdd y) with hxdef
  have hxV2 : (x : G) ∈ burnsideJ7_V2pl M := ⟨x.2, by simpa [hxdef] using hy⟩
  have hcomm : (x : G) * c = c * x := Subgroup.mem_centralizer_iff.mp hc.2 _ hxV2
  have hconj : (x : G) = c * x * (c : G)⁻¹ := by
    calc (x : G) = ((x : G) * c) * c⁻¹ := by group
      _ = (c * (x : G)) * c⁻¹ := by rw [hcomm]
  have := M.ψV_equiv ⟨c, hcL⟩ x x hconj
  have h2 : M.ψV x = Multiplicative.ofAdd y := by simp [hxdef]
  rw [h2, toAdd_ofAdd] at this
  exact (Multiplicative.ofAdd.injective this).symm

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_comm_C_le_D {G : Type} [Group G] [Finite G] (M : RuDataM G) {l : G}
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) :
    ⁅ruQ M.T ⊓ Subgroup.centralizer (↑(burnsideJ7_V2pl M) : Set G), M.conjU l⁆ ≤
      M.conjU l ⊓ ruQ M.T := by
  rw [Subgroup.commutator_le]
  intro c hc u hu
  show c * u * c⁻¹ * u⁻¹ ∈ M.conjU l ⊓ ruQ M.T
  obtain ⟨hcL, hcfix⟩ := burnsideJ7_C_fix M hc
  have hcQ : c ∈ ruQ M.T := hc.1
  have huS : u ∈ ruS M.L := M.conjU_le_S hlL hu
  have huH : u ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T huS)
  have hcS : c * u * c⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hcL) u).mp huS
  have hxS : c * u * c⁻¹ * u⁻¹ ∈ ruS M.L := mul_mem hcS (inv_mem huS)
  have hθcR : M.θ ⟨c, hcL⟩ ∈ SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨c, hcL⟩, Subgroup.mem_subgroupOf.mpr hcQ, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [burnsideJ7_mem_conjU_iff M hlL hxS]
    have e : (⟨c * u * c⁻¹ * u⁻¹, hxS⟩ : ruS M.L) =
        ⟨c * u * c⁻¹, hcS⟩ * (⟨u, huS⟩ : ruS M.L)⁻¹ := rfl
    rw [e, M.toAdd_χ_mul, M.toAdd_χ_inv]
    have h1 := M.χ_conj ⟨c, hcL⟩ ⟨u, huS⟩
    simp only at h1
    rw [h1]
    have hu' := (burnsideJ7_mem_conjU_iff M hlL huS).mp hu
    have hD1 := burnsideJ7_D1 _ hlPl (M.θ ⟨c, hcL⟩) hθcR hcfix _ hu'
    rwa [burnsideJ7_stAct_stAct_inv] at hD1
  · have e : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem hcQ (M.conj_mem_Q huH (inv_mem hcQ))

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_exists_comm_not_U {G : Type} [Group G] [Finite G] (M : RuDataM G) {l : G}
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) (hne : M.conjU l ≠ ruU M.L M.T) :
    ∃ c ∈ ruQ M.T ⊓ Subgroup.centralizer (↑(burnsideJ7_V2pl M) : Set G), ∃ u ∈ M.conjU l,
      c * u * c⁻¹ * u⁻¹ ∉ ruU M.L M.T := by
  have hnot : M.θ ⟨l, hlL⟩ ∉ SL3.Stab0 := by
    intro hst
    exact hne ((M.conjU_eq_U_iff hlL).mpr (mem_pullL.mpr ⟨hlL, hst⟩))
  obtain ⟨A₀, hA₀, hnA⟩ := burnsideJ7_D2 _ hlPl hnot
  have hp0R : burnsideJ7_p0 ∈ ((ruQ M.T).subgroupOf M.L).map M.θ := by
    rw [M.θQ_eq]
    exact burnsideJ7_p0_mem
  obtain ⟨c', hc', hθc⟩ := hp0R
  have hcQ : (c' : G) ∈ ruQ M.T := hc'
  have hcL : (c' : G) ∈ M.L := c'.2
  have hcC : (c' : G) ∈ ruQ M.T ⊓ Subgroup.centralizer (↑(burnsideJ7_V2pl M) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hcQ, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    obtain ⟨hxV, hx2⟩ := (burnsideJ7_mem_V2pl M).mp hx
    have hconj : (c' : G) * x * (c' : G)⁻¹ ∈ ruV M.L := M.toRuData.conj_mem_V hcL hxV
    have h1 := M.ψV_equiv c' ⟨x, hxV⟩ ⟨(c' : G) * x * (c' : G)⁻¹, hconj⟩ rfl
    rw [hθc, burnsideJ7_p0_fix _ hx2, ofAdd_toAdd] at h1
    have h3 : (⟨(c' : G) * x * (c' : G)⁻¹, hconj⟩ : ruV M.L) = ⟨x, hxV⟩ :=
      M.ψV.injective h1
    have h4 : (c' : G) * x * (c' : G)⁻¹ = x := congrArg Subtype.val h3
    calc x * (c' : G) = ((c' : G) * x * (c' : G)⁻¹) * c' := by rw [h4]
      _ = c' * x := by group
  set a := M.θ ⟨l, hlL⟩ with ha
  have hAt : IsTraceZero (stAct a A₀) := by
    have := SL3.row0_trace A₀ hA₀
    unfold IsTraceZero
    rw [SL3.trace_stAct]
    exact this
  obtain ⟨s, hs⟩ := M.χ_surj _ hAt
  have hsc : stAct a⁻¹ (stAct a A₀) = A₀ := by
    rw [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one]
  have hsu : (s : G) ∈ M.conjU l := by
    rw [burnsideJ7_mem_conjU_iff M hlL s.2, hs, toAdd_ofAdd, hsc]
    exact hA₀
  refine ⟨c', hcC, s, hsu, fun hU => ?_⟩
  have huS : (s : G) ∈ ruS M.L := s.2
  have hcS : (c' : G) * s * (c' : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hcL) _).mp huS
  have hxS : (c' : G) * s * (c' : G)⁻¹ * (s : G)⁻¹ ∈ ruS M.L := mul_mem hcS (inv_mem huS)
  have hrow := (M.mem_U_iff hxS).mp hU
  have e : (⟨(c' : G) * s * (c' : G)⁻¹ * (s : G)⁻¹, hxS⟩ : ruS M.L) =
      ⟨(c' : G) * s * (c' : G)⁻¹, hcS⟩ * (s : ruS M.L)⁻¹ := rfl
  rw [e, M.toAdd_χ_mul, M.toAdd_χ_inv] at hrow
  have h1 := M.χ_conj c' s
  rw [h1, hθc, hs, toAdd_ofAdd] at hrow
  exact hnA hrow

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_relIndex_DU {G : Type} [Group G] [Finite G] (M : RuDataM G) {l : G}
    (hlL : l ∈ M.L) (hne : M.conjU l ≠ ruU M.L M.T) :
    (ruU M.L M.T).relIndex (M.conjU l ⊓ ruQ M.T ⊔ ruU M.L M.T) = 2 := by
  have hDQ : M.conjU l ⊓ ruQ M.T ≤ ruQ M.T := inf_le_right
  have hUQ : ruU M.L M.T ≤ ruQ M.T := M.U_le_Q
  haveI : ((ruU M.L M.T).subgroupOf (ruQ M.T)).Normal := M.UQ_normal
  have h1 := Subgroup.relIndex_sup_right (H := (M.conjU l ⊓ ruQ M.T).subgroupOf (ruQ M.T))
    (K := (ruU M.L M.T).subgroupOf (ruQ M.T))
  rw [← Subgroup.subgroupOf_sup hDQ hUQ, Subgroup.relIndex_subgroupOf (sup_le hDQ hUQ),
    Subgroup.relIndex_subgroupOf hDQ] at h1
  rw [h1]
  have h2 := Subgroup.relIndex_mul_card (ruU M.L M.T) (M.conjU l ⊓ ruQ M.T)
  have hVQ : ruV M.L ≤ ruQ M.T := M.V_le_U.trans hUQ
  have hinf : ruU M.L M.T ⊓ (M.conjU l ⊓ ruQ M.T) = ruV M.L := by
    rw [← inf_assoc, M.U_inf_conjU hlL hne]
    exact inf_eq_left.mpr hVQ
  rw [hinf, M.toRuData.card_V, M.card_conjU_inf_Q hlL hne] at h2
  omega

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_clause6 {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {V2 : Subgroup G} (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2)
    {b v l : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) (hne : M.conjU l ≠ ruU M.L M.T)
    (hv : v ∈ M.conjU l) (hvQ : v ∉ ruQ M.T) (hvb : v * b * v⁻¹ = b ^ 4) :
    (M.conjU l ⊓ ruQ M.T ⊔ ruU M.L M.T =
        ⁅ruQ M.T ⊓ Subgroup.centralizer (V2 : Set G), M.conjU l⁆ ⊔ ruU M.L M.T ∧
      ⁅ruQ M.T ⊓ Subgroup.centralizer (V2 : Set G), M.conjU l⁆ ⊔ ruU M.L M.T ≤
        ⁅ruQ M.T, Subgroup.zpowers b⁆ ∧
      (ruU M.L M.T).relIndex (M.conjU l ⊓ ruQ M.T ⊔ ruU M.L M.T) = 2) := by
  rw [burnsideJ7_V2_eq M hV2]
  have hY := burnsideJ7_relIndex_DU M hlL hne
  have hK := burnsideJ7_comm_C_le_D M hlL hlPl
  refine ⟨?_, ?_, hY⟩
  · set D := M.conjU l ⊓ ruQ M.T
    set K := ⁅ruQ M.T ⊓ Subgroup.centralizer (↑(burnsideJ7_V2pl M) : Set G), M.conjU l⁆
    have hUX : ruU M.L M.T ≤ K ⊔ ruU M.L M.T := le_sup_right
    have hXY : K ⊔ ruU M.L M.T ≤ D ⊔ ruU M.L M.T := sup_le_sup_right hK _
    have hmul := Subgroup.relIndex_mul_relIndex (ruU M.L M.T) (K ⊔ ruU M.L M.T)
      (D ⊔ ruU M.L M.T) hUX hXY
    rw [hY] at hmul
    obtain ⟨c, hc, u, hu, hcu⟩ := burnsideJ7_exists_comm_not_U M hlL hlPl hne
    have hmem : c * u * c⁻¹ * u⁻¹ ∈ K ⊔ ruU M.L M.T :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hc hu)
    have hne1 : (ruU M.L M.T).relIndex (K ⊔ ruU M.L M.T) ≠ 1 := by
      intro h1
      exact hcu (Subgroup.relIndex_eq_one.mp h1 hmem)
    have h2 : (K ⊔ ruU M.L M.T).relIndex (D ⊔ ruU M.L M.T) = 1 := by
      have hd : (ruU M.L M.T).relIndex (K ⊔ ruU M.L M.T) ∣ 2 := Dvd.intro _ hmul
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd h hne1
      · rw [h] at hmul
        omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hXY
  · have hcomm : ⁅ruQ M.T, M.conjU l⁆ ≤ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
      rw [burnsideJ7_comm_eq_Q5 M hbH hb5]
      exact burnsideJ7_comm_le_Q5 M hbH hb5 hlL hne hv hvQ hvb
    exact sup_le (le_trans (Subgroup.commutator_mono inf_le_left le_rfl) hcomm)
      (burnsideJ7_Q5_section_U M hbH hb5).1

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_clause4 {G : Type} [Group G] [Finite G] (M : RuDataM G) (H U₀ :
    Subgroup G)
    (hH : H = ruH M.T) (hU₀ : U₀ = ruU M.L M.T) :
    ∃ (_ : (U₀.subgroupOf H).Normal),
      Nat.card (Subgroup.center (↥H ⧸ U₀.subgroupOf H)) = 2 := by
  subst hH hU₀
  have hUn : ((ruU M.L M.T).subgroupOf (ruH M.T)).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact M.conj_mem_U g.2 hx⟩
  refine ⟨hUn, ?_⟩
  have hQ0H : M.Q0 ≤ ruH M.T := fun x hx => (Subgroup.mem_inf.mp (M.Q0_le_HC hx)).1
  set Z := Subgroup.center (↥(ruH M.T) ⧸ (ruU M.L M.T).subgroupOf (ruH M.T)) with hZ
  have hQ0 : ∀ x : G, x ∈ M.Q0 ↔ (x ∈ ruH M.T ∧ ∀ y ∈ ruH M.T, x⁻¹ * y⁻¹ * x * y ∈ ruU M.L M.T) := by
    intro x
    have := Set.ext_iff.mp (burnsideJ7_Q0_set M) x
    simpa using this.symm
  have hpre : (QuotientGroup.mk : ↥(ruH M.T) → ↥(ruH M.T) ⧸ (ruU M.L M.T).subgroupOf (ruH M.T)) ⁻¹'
      (Z : Set _) = ((M.Q0.subgroupOf (ruH M.T) : Subgroup ↥(ruH M.T)) : Set ↥(ruH M.T)) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf]
    rw [hQ0]
    constructor
    · intro hx
      refine ⟨x.2, fun y hy => ?_⟩
      have := Subgroup.mem_center_iff.mp hx (QuotientGroup.mk ⟨y, hy⟩)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at this
      have e : (((⟨y, hy⟩ : ↥(ruH M.T)) * x)⁻¹ * (x * ⟨y, hy⟩) : ↥(ruH M.T)) =
          x⁻¹ * (⟨y, hy⟩ : ↥(ruH M.T))⁻¹ * x * ⟨y, hy⟩ := by group
      rw [e] at this
      exact this
    · rintro ⟨-, hc⟩
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have e : (((y * x)⁻¹ * (x * y) : ↥(ruH M.T)) : G) = (x : G)⁻¹ * (y : G)⁻¹ * x * y := by
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
          group
        rw [e]
        exact hc y y.2
  have h := QuotientGroup.card_preimage_mk ((ruU M.L M.T).subgroupOf (ruH M.T))
    (Z : Set (↥(ruH M.T) ⧸ (ruU M.L M.T).subgroupOf (ruH M.T)))
  rw [hpre] at h
  have h1 : Nat.card ((M.Q0.subgroupOf (ruH M.T) : Subgroup ↥(ruH M.T)) : Set ↥(ruH M.T)) =
      2 ^ 6 := by
    show Nat.card (M.Q0.subgroupOf (ruH M.T)) = 2 ^ 6
    rw [card_subgroupOf_of_le hQ0H, M.card_Q0]
  rw [h1, card_subgroupOf_of_le M.U_le_H, M.toRuData.card_U] at h
  have h2 : Nat.card (↥(Z : Set (↥(ruH M.T) ⧸ (ruU M.L M.T).subgroupOf (ruH M.T)))) =
      Nat.card Z := rfl
  rw [h2] at h
  omega

open CFSG.Quasithin.RuType in
@[expose] def burnsideJ7_E (s x : SigmaL2F4) : Prop :=
  x ≠ 1 ∧ x ^ 5 = 1 ∧ s * x * s⁻¹ = x⁻¹

open CFSG.Quasithin.RuType in
instance burnsideJ7_E_decidable (s : SigmaL2F4) : DecidablePred (burnsideJ7_E s) := fun x =>
  inferInstanceAs (Decidable (x ≠ 1 ∧ x ^ 5 = 1 ∧ s * x * s⁻¹ = x⁻¹))

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_G1 : ∀ s : SigmaL2F4, s ^ 2 = 1 → s.right = 1 → s ≠ 1 →
    ∃ x₁, burnsideJ7_E s x₁ ∧ ∃ x₂, burnsideJ7_E s x₂ ∧
      (x₂ ≠ x₁ ∧ x₂ ≠ x₁ ^ 2 ∧ x₂ ≠ x₁ ^ 3 ∧ x₂ ≠ x₁ ^ 4) ∧
      ∀ z, burnsideJ7_E s z → (z = x₁ ∨ z = x₁ ^ 2 ∨ z = x₁ ^ 3 ∨ z = x₁ ^ 4) ∨
        (z = x₂ ∨ z = x₂ ^ 2 ∨ z = x₂ ^ 3 ∨ z = x₂ ^ 4) := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_zpowers_five {Y : Type} [Group Y] {X : Y} (hX : X ^ 5 = 1) {y : Y}
    (hy : y ∈ Subgroup.zpowers X) : ∃ m : ℕ, m < 5 ∧ y = X ^ m := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨m, hm⟩ := exists_nat_zpow (n := 5) (by norm_num) hX k
  exact ⟨m % 5, Nat.mod_lt _ (by norm_num), by rw [hm, ← pow_eq_pow_mod m hX]⟩

private theorem burnsideJ7_inverted_zpowers {Y : Type} [Group Y] {w X : Y} (hX : w⁻¹ * X * w = X⁻¹)
    {x : Y} (hx : x ∈ Subgroup.zpowers X) : w⁻¹ * x * w = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h := conj_zpow (a := w⁻¹) (b := X) (i := k)
  rw [inv_inv, hX, inv_zpow] at h
  exact h.symm

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_count_inverted {Y : Type} [Group Y] [Finite Y] (ι : Y ≃* SigmaL2F4)
    (w : Y)
    (hw2 : w ^ 2 = 1) (hwr : (ι w).right = 1) (hw1 : ι w ≠ 1) :
    Set.ncard {P : Sylow 5 Y | ∀ x ∈ (P : Subgroup Y), w⁻¹ * x * w = x⁻¹} = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hY : Nat.card Y = 120 := by
    rw [Nat.card_congr ι.toEquiv]
    exact Sigma.card_Sigma'
  have hfac : (Nat.card Y).factorization 5 = 1 := by
    rw [hY, show (120 : ℕ) = 5 ^ 1 * 24 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.Prime.factorization_pow (by norm_num)]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 24 by norm_num)]
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hw2)
  have hs2 : (ι w) ^ 2 = 1 := by rw [← map_pow, hw2, map_one]
  have hsinv : (ι w)⁻¹ = ι w := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs2)
  obtain ⟨x₁, hx₁, x₂, hx₂, ⟨hn1, hn2, hn3, hn4⟩, hcover⟩ := burnsideJ7_G1 (ι w) hs2 hwr hw1
  have hEY : ∀ x, burnsideJ7_E (ι w) x → ι.symm x ≠ 1 ∧ (ι.symm x) ^ 5 = 1 ∧
      w⁻¹ * ι.symm x * w = (ι.symm x)⁻¹ := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨fun h => h1 (by simpa using congrArg ι h), ?_, ?_⟩
    · apply ι.injective
      rw [map_pow, MulEquiv.apply_symm_apply, h2, map_one]
    · apply ι.injective
      rw [hwinv, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [hsinv] at h3
      exact h3
  have hYE : ∀ z : Y, z ≠ 1 → z ^ 5 = 1 → w⁻¹ * z * w = z⁻¹ → burnsideJ7_E (ι w) (ι z) := by
    intro z h1 h2 h3
    refine ⟨fun h => h1 (ι.injective (by simpa using h)), by rw [← map_pow, h2, map_one], ?_⟩
    have := congrArg ι h3
    rw [hwinv, map_mul, map_mul, map_inv] at this
    rw [hsinv]
    exact this
  have hEY1 := hEY x₁ hx₁
  have hEY2 := hEY x₂ hx₂
  have hX1ne := hEY1.1
  have hX15 := hEY1.2.1
  have hX1inv := hEY1.2.2
  have hX2ne := hEY2.1
  have hX25 := hEY2.2.1
  have hX2inv := hEY2.2.2
  have hord : ∀ X : Y, X ≠ 1 → X ^ 5 = 1 →
      Nat.card (Subgroup.zpowers X) = 5 ^ (Nat.card Y).factorization 5 := by
    intro X h1 h5
    rw [Nat.card_zpowers, orderOf_eq_prime h5 h1, hfac, pow_one]
  let P₁ : Sylow 5 Y := Sylow.ofCard (Subgroup.zpowers (ι.symm x₁)) (hord _ hX1ne hX15)
  let P₂ : Sylow 5 Y := Sylow.ofCard (Subgroup.zpowers (ι.symm x₂)) (hord _ hX2ne hX25)
  have hP₁ : (P₁ : Subgroup Y) = Subgroup.zpowers (ι.symm x₁) := Sylow.coe_ofCard _ _
  have hP₂ : (P₂ : Subgroup Y) = Subgroup.zpowers (ι.symm x₂) := Sylow.coe_ofCard _ _
  have hpowY : ∀ (x : SigmaL2F4) (k : ℕ) (z : Y), ι z = x ^ k →
      z ∈ Subgroup.zpowers (ι.symm x) := by
    intro x k z hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [zpow_natCast]
    apply ι.injective
    rw [map_pow, MulEquiv.apply_symm_apply, hz]
  have hne : P₁ ≠ P₂ := by
    intro heq
    have h12 : Subgroup.zpowers (ι.symm x₁) = Subgroup.zpowers (ι.symm x₂) := by
      rw [← hP₁, ← hP₂, heq]
    have hmem : ι.symm x₂ ∈ Subgroup.zpowers (ι.symm x₁) := by
      rw [h12]
      exact Subgroup.mem_zpowers _
    obtain ⟨m, hm5, hm⟩ := burnsideJ7_zpowers_five hX15 hmem
    have hx2 : x₂ = x₁ ^ m := by
      have := congrArg ι hm
      rw [map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
      exact this
    interval_cases m
    · exact hX2ne (by simpa using hm)
    · exact hn1 (by simpa using hx2)
    · exact hn2 hx2
    · exact hn3 hx2
    · exact hn4 hx2
  have hS : {P : Sylow 5 Y | ∀ x ∈ (P : Subgroup Y), w⁻¹ * x * w = x⁻¹} = {P₁, P₂} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hP
      have hPcard : Nat.card (P : Subgroup Y) = 5 := by
        rw [Sylow.card_eq_multiplicity, hfac, pow_one]
      have h5 : 1 < Nat.card (P : Subgroup Y) := by rw [hPcard]; norm_num
      haveI : Nontrivial (P : Subgroup Y) := Finite.one_lt_card_iff_nontrivial.mp h5
      obtain ⟨⟨z, hzP⟩, hz1⟩ := exists_ne (1 : (P : Subgroup Y))
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hz5 : z ^ 5 = 1 := by
        have := pow_card_eq_one' (G := (P : Subgroup Y)) (x := ⟨z, hzP⟩)
        rw [hPcard] at this
        simpa using congrArg Subtype.val this
      have hzE := hYE z hz1' hz5 (hP z hzP)
      have hcard_z : Nat.card (Subgroup.zpowers z) = 5 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hz5 hz1']
      have hzP' : Subgroup.zpowers z = (P : Subgroup Y) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzP) (by rw [hPcard, hcard_z])
      rcases hcover (ι z) hzE with h | h
      · left
        have hzX : z ∈ Subgroup.zpowers (ι.symm x₁) := by
          rcases h with h | h | h | h
          · exact hpowY x₁ 1 z (by rw [h, pow_one])
          · exact hpowY x₁ 2 z h
          · exact hpowY x₁ 3 z h
          · exact hpowY x₁ 4 z h
        apply Sylow.ext
        rw [hP₁, ← hzP']
        exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzX)
          (by rw [hcard_z, hord _ hX1ne hX15, hfac, pow_one])
      · right
        have hzX : z ∈ Subgroup.zpowers (ι.symm x₂) := by
          rcases h with h | h | h | h
          · exact hpowY x₂ 1 z (by rw [h, pow_one])
          · exact hpowY x₂ 2 z h
          · exact hpowY x₂ 3 z h
          · exact hpowY x₂ 4 z h
        apply Sylow.ext
        rw [hP₂, ← hzP']
        exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzX)
          (by rw [hcard_z, hord _ hX2ne hX25, hfac, pow_one])
    · rintro (rfl | rfl)
      · intro x hx
        rw [hP₁] at hx
        exact burnsideJ7_inverted_zpowers hX1inv hx
      · intro x hx
        rw [hP₂] at hx
        exact burnsideJ7_inverted_zpowers hX2inv hx
  rw [hS]
  exact Set.ncard_pair hne

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_clause2a {G : Type} [Group G] [Finite G] (M : RuDataM G) {v : G}
    (hvH : v ∈ ruH M.T) (hvK : v ∈ M.K) (hvQ : v ∉ ruQ M.T) (hv2 : v * v = 1) :
    ∃ B5 : Subgroup G, ChIJK.IsSylowIn 5 B5 (ruH M.T) ∧ ChIJK.InvertsGroup v B5 := by
  obtain ⟨x, hxH, hx5, hvx⟩ := M.exists_inv_five_of_K hvH hvK hvQ hv2
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hcard : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hx5]
  have hle : Subgroup.zpowers x ≤ ruH M.T := Subgroup.zpowers_le.mpr hxH
  have hinv : ∀ y ∈ Subgroup.zpowers x, v⁻¹ * y * v = y⁻¹ := by
    intro y hy
    have hx' : v⁻¹ * x * v = x⁻¹ := by rw [hvinv]; rw [hvinv] at hvx; exact hvx
    exact burnsideJ7_inverted_zpowers (w := v) (X := x) hx' hy
  refine ⟨Subgroup.zpowers x, ⟨hle, ?_, ?_⟩, ?_, hinv⟩
  · exact IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  · have h1 := Subgroup.card_mul_index ((Subgroup.zpowers x).subgroupOf (ruH M.T))
    rw [card_subgroupOf_of_le hle, hcard, M.card_H] at h1
    have : ((Subgroup.zpowers x).subgroupOf (ruH M.T)).index = 2 ^ 14 * 3 := by omega
    rw [this]
    norm_num
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have := hinv y hy
      have e : v * y * v⁻¹ = y⁻¹ := by rw [hvinv] at this ⊢; exact this
      rw [e]
      exact inv_mem hy
    · intro hy
      have h2 := hinv _ hy
      have e : v⁻¹ * (v * y * v⁻¹) * v = y := by group
      rw [e] at h2
      rw [h2]
      exact inv_mem hy

open CFSG.Quasithin.RuType in
@[expose] noncomputable def burnsideJ7_iota {G : Type} [Group G] (M : RuDataM G) :
    (↥(ruH M.T) ⧸ CFSG.pCore 2 ↥(ruH M.T)) ≃* SigmaL2F4 := by
  have hker : M.φ.ker = CFSG.pCore 2 ↥(ruH M.T) := by
    rw [M.φ_ker]
    exact Subgroup.comap_map_eq_self_of_injective (ruH M.T).subtype_injective _
  refine MulEquiv.ofBijective (QuotientGroup.lift (CFSG.pCore 2 ↥(ruH M.T)) M.φ
    (by rw [← hker])) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    induction a using QuotientGroup.induction_on with
    | H x =>
      have : x ∈ M.φ.ker := ha
      rw [hker] at this
      exact (QuotientGroup.eq_one_iff x).mpr this
  · intro g
    obtain ⟨x, hx⟩ := M.φ_surj g
    exact ⟨x, hx⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_iota_mk {G : Type} [Group G] (M : RuDataM G) (x : ↥(ruH M.T)) :
    burnsideJ7_iota M (x : ↥(ruH M.T) ⧸ CFSG.pCore 2 ↥(ruH M.T)) = M.φ x := rfl

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_clause2b {G : Type} [Group G] [Finite G] (M : RuDataM G) (H : Subgroup G)
    (hH : H = ruH M.T) (v : ↥H) (hvK : (v : G) ∈ M.K) (hvQ : (v : G) ∉ ruQ M.T)
    (hv2 : (v : G) ^ 2 = 1) :
    Set.ncard {P : Sylow 5 (↥H ⧸ CFSG.pCore 2 ↥H) |
      ∀ x ∈ (P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)),
        ((v : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * x * ((v : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = x⁻¹} = 2 := by
  subst hH
  have hv2' : ((v : ↥(ruH M.T)) : ↥(ruH M.T) ⧸ CFSG.pCore 2 ↥(ruH M.T)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (v : ↥(ruH M.T)) ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    rw [this]
    rfl
  refine burnsideJ7_count_inverted (burnsideJ7_iota M) _ hv2' ?_ ?_
  · rw [burnsideJ7_iota_mk]
    obtain ⟨hk, h1⟩ := M.mem_K_iff.mp hvK
    exact h1
  · rw [burnsideJ7_iota_mk]
    intro h1
    apply hvQ
    have hk : v ∈ M.φ.ker := h1
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_D3 : ∀ a ∈ SL3.Pl, a ∉ SL3.Stab0 → ∀ t ∈ SL3.P0,
    ∃ r ∈ SL3.R0, natAct3 (r * t * a) SL3.e0 = natAct3 a SL3.e0 := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_exists_stab {G : Type} [Group G] [Finite G] (M : RuDataM G) {l : G}
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) (hne : M.conjU l ≠ ruU M.L M.T) {t : G}
    (ht : t ∈ (M.T : Subgroup G)) :
    ∃ q ∈ ruQ M.T, (M.conjU l).map (MulAut.conj (q * t)).toMonoidHom = M.conjU l := by
  have htL : t ∈ M.L := M.toRuData.T_le_L ht
  have hnot : M.θ ⟨l, hlL⟩ ∉ SL3.Stab0 := by
    intro hst
    exact hne ((M.conjU_eq_U_iff hlL).mpr (mem_pullL.mpr ⟨hlL, hst⟩))
  obtain ⟨r, hr, hrr⟩ := burnsideJ7_D3 _ hlPl hnot (M.θ ⟨t, htL⟩) (M.θ_mem_P0 ht)
  have hrQ : r ∈ ((ruQ M.T).subgroupOf M.L).map M.θ := by
    rw [M.θQ_eq]
    exact hr
  obtain ⟨q', hq', hθq⟩ := hrQ
  have hqQ : (q' : G) ∈ ruQ M.T := hq'
  refine ⟨q', hqQ, ?_⟩
  have h1 := (M.conjU_eq_conjU_iff (q' * ⟨t, htL⟩ * ⟨l, hlL⟩) ⟨l, hlL⟩).mpr (by
    rw [map_mul, map_mul, hθq]
    exact hrr)
  have h1' : M.conjU ((q' : G) * t * l) = M.conjU l := h1
  rw [M.conjU_mul] at h1'
  exact h1'.symm.symm

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_v_central {G : Type} [Group G] [Finite G] (M : RuDataM G) {l v : G}
    (hlL : l ∈ M.L) (hlPl : M.θ ⟨l, hlL⟩ ∈ SL3.Pl) (hne : M.conjU l ≠ ruU M.L M.T)
    (hv : v ∈ M.conjU l) (hvQ : v ∉ ruQ M.T) {t : G} (ht : t ∈ (M.T : Subgroup G)) :
    t * v * t⁻¹ * v⁻¹ ∈ ruQ M.T := by
  obtain ⟨q, hq, hstab⟩ := burnsideJ7_exists_stab M hlL hlPl hne ht
  have hvS : v ∈ ruS M.L := M.conjU_le_S hlL hv
  have hvH : v ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hvS)
  have hqH : q ∈ ruH M.T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  have htH : t ∈ ruH M.T := M.toRuData.T_le_H ht
  set a := q * t * v * (q * t)⁻¹ with ha
  have haU : a ∈ M.conjU l := by
    rw [← hstab]
    exact ⟨v, hv, by rw [ha]; exact MulAut.conj_apply _ _⟩
  have haQ : a ∉ ruQ M.T := by
    intro h
    apply hvQ
    have h2 := M.conj_mem_Q (inv_mem (mul_mem hqH htH)) h
    have e : (q * t)⁻¹ * a * ((q * t)⁻¹)⁻¹ = v := by
      rw [ha]
      group
    rw [e] at h2
    exact h2
  have hD := burnsideJ7_relIndex_D M hlL hne
  have hvinvQ : v⁻¹ ∉ M.conjU l ⊓ ruQ M.T := by
    intro h
    have h2 : v⁻¹ ∈ ruQ M.T := h.2
    have := (ruQ M.T).inv_mem h2
    exact hvQ (by simpa using this)
  have hd : a * v⁻¹ ∈ M.conjU l ⊓ ruQ M.T :=
    burnsideJ7_mul_mem_of_relIndex_two hD haU (inv_mem hv) (fun h => haQ h.2) hvinvQ
  have hdQ : a * v⁻¹ ∈ ruQ M.T := hd.2
  have e : t * v * t⁻¹ * v⁻¹ =
      (q⁻¹ * (a * v⁻¹) * q) * (q⁻¹ * (v * q * v⁻¹)) := by
    rw [ha]
    group
  rw [e]
  exact mul_mem ((ruQ M.T).mul_mem ((ruQ M.T).mul_mem (inv_mem hq) hdQ) hq)
    ((ruQ M.T).mul_mem (inv_mem hq) (M.conj_mem_Q hvH hq))

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_SP0_center : ∀ z ∈ Sigma.SP0, ∀ z' ∈ Sigma.SP0,
    (∀ y ∈ Sigma.SP0, z * y = y * z) → (∀ y ∈ Sigma.SP0, z' * y = y * z') →
      z = 1 ∨ z' = 1 ∨ z = z' := by
  decide +kernel

@[expose] def burnsideJ7_starImg {G : Type} [Group G] (H X : Subgroup G) :
    Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

private theorem burnsideJ7_mem_pCore_iff {G : Type} [Group G] (H : Subgroup G) (y : ↥H) :
    y ∈ CFSG.pCore 2 ↥H ↔ (y : G) ∈ CFSG.Open.pCoreOf 2 H := by
  have : (CFSG.Open.pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [← this, Subgroup.mem_subgroupOf]

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_card_starImg {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {X : Subgroup G} (hX : X ≤ ruH M.T) :
    Nat.card ↥(burnsideJ7_starImg (ruH M.T) X) * Nat.card ↥(X ⊓ ruQ M.T) = Nat.card ↥X := by
  set f : ↥(X.subgroupOf (ruH M.T)) →* (↥(ruH M.T) ⧸ CFSG.pCore 2 ↥(ruH M.T)) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(ruH M.T))).comp (X.subgroupOf (ruH M.T)).subtype with hf
  have h := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = burnsideJ7_starImg (ruH M.T) X := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(X ⊓ ruQ M.T) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), Subgroup.mem_inf.mpr ⟨x.1.2, ?_⟩⟩
        invFun := fun y => ⟨⟨⟨y.1, hX (Subgroup.mem_inf.mp y.2).1⟩, (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have h1 : (x.1.1 : ↥(ruH M.T)) ∈ CFSG.pCore 2 ↥(ruH M.T) := (QuotientGroup.eq_one_iff _).mp hx
      exact (burnsideJ7_mem_pCore_iff (ruH M.T) _).mp h1
    · rw [MonoidHom.mem_ker]
      refine (QuotientGroup.eq_one_iff _).mpr ?_
      exact (burnsideJ7_mem_pCore_iff (ruH M.T) _).mpr (Subgroup.mem_inf.mp y.2).2
  rw [card_subgroupOf_of_le hX, hker, hrange] at h
  rw [mul_comm]
  exact h

private theorem burnsideJ7_mem_centerImg {Y : Type} [Group Y] (T' : Subgroup Y) {x : Y} :
    x ∈ (Subgroup.center ↥T').map T'.subtype ↔ ∃ hx : x ∈ T', ∀ d ∈ T', d * x = x * d := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun d hd => ?_⟩
    have := Subgroup.mem_center_iff.mp hc ⟨d, hd⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (h g.1 g.2), rfl⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ7_clause1 {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) (H U₀ : Subgroup G)
    (hH : H = ruH M.T) (hU₀ : U₀ = ruU M.L M.T) {g : G} (hg : g ∈ ChIJK.L2Ru M.L V2)
    (hgH : g ∉ H) (v : ↥H) (hv : (v : G) ∈ CFSG.conjugate U₀ g)
    (hvQ : (v : G) ∉ CFSG.conjugate U₀ g ⊓ CFSG.Open.pCoreOf 2 H) :
    burnsideJ7_starImg H (Subgroup.zpowers (v : G)) = burnsideJ7_starImg H (CFSG.conjugate U₀ g) ∧
      burnsideJ7_starImg H (CFSG.conjugate U₀ g) =
        (Subgroup.center ↥(burnsideJ7_starImg H (M.T : Subgroup G))).map
          (burnsideJ7_starImg H (M.T : Subgroup G)).subtype ∧
      Nat.card ↥(burnsideJ7_starImg H (CFSG.conjugate U₀ g)) = 2 := by
  subst hH hU₀
  obtain ⟨hlL, hlPl, hne⟩ := burnsideJ7_g_facts M hV2 hg hgH
  have hUα : CFSG.conjugate (ruU M.L M.T) g = M.conjU g⁻¹ := rfl
  rw [hUα] at hv hvQ ⊢
  have hvQ' : (v : G) ∉ ruQ M.T := fun h => hvQ ⟨hv, h⟩
  have hvS : (v : G) ∈ ruS M.L := M.conjU_le_S hlL hv
  have hvT : (v : G) ∈ (M.T : Subgroup G) := M.toRuData.S_le_T hvS
  have hUαH : M.conjU g⁻¹ ≤ ruH M.T :=
    (M.conjU_le_S hlL).trans (M.toRuData.S_le_T.trans M.toRuData.T_le_H)
  have hTH : (M.T : Subgroup G) ≤ ruH M.T := M.toRuData.T_le_H
  have hcard := burnsideJ7_card_starImg M hUαH
  rw [M.card_conjU_inf_Q hlL hne, M.card_conjU, M.toRuData.card_U] at hcard
  have hc2 : Nat.card ↥(burnsideJ7_starImg (ruH M.T) (M.conjU g⁻¹)) = 2 := by omega
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥(ruH M.T)) with hπ
  have hπv : π v ≠ 1 := by
    intro h
    exact hvQ' ((burnsideJ7_mem_pCore_iff (ruH M.T) v).mp ((QuotientGroup.eq_one_iff v).mp h))
  have h1a : burnsideJ7_starImg (ruH M.T) (Subgroup.zpowers (v : G)) =
      burnsideJ7_starImg (ruH M.T) (M.conjU g⁻¹) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.map_mono (fun x hx => (Subgroup.zpowers_le.mpr hv) hx)
    · rw [hc2]
      have hmem : π v ∈ burnsideJ7_starImg (ruH M.T) (Subgroup.zpowers (v : G)) :=
        ⟨v, Subgroup.mem_zpowers _, rfl⟩
      have hbot : burnsideJ7_starImg (ruH M.T) (Subgroup.zpowers (v : G)) ≠ ⊥ := by
        intro hb
        rw [hb] at hmem
        exact hπv (Subgroup.mem_bot.mp hmem)
      have := (Subgroup.one_lt_card_iff_ne_bot (burnsideJ7_starImg (ruH M.T)
        (Subgroup.zpowers (v : G)))).mpr hbot
      omega
  have hcentral : ∀ y : ↥(ruH M.T), (y : G) ∈ (M.T : Subgroup G) → π y * π v = π v * π y := by
    intro y hy
    show (QuotientGroup.mk y : ↥(ruH M.T) ⧸ _) * QuotientGroup.mk v =
      QuotientGroup.mk v * QuotientGroup.mk y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      burnsideJ7_mem_pCore_iff]
    have h1 := burnsideJ7_v_central M hlL hlPl hne hv hvQ' (t := (y : G)⁻¹) (inv_mem hy)
    have h2 := M.conj_mem_Q (inv_mem (v : ↥(ruH M.T)).2) h1
    have e : (((y * v)⁻¹ * (v * y) : ↥(ruH M.T)) : G) =
        (v : G)⁻¹ * ((y : G)⁻¹ * v * (y : G)⁻¹⁻¹ * (v : G)⁻¹) * ((v : G)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e]
    exact h2
  refine ⟨h1a, ?_, hc2⟩
  have hD := burnsideJ7_relIndex_D M hlL hne
  have hvinvQ : (v : G)⁻¹ ∉ M.conjU g⁻¹ ⊓ ruQ M.T := by
    intro h
    have h2 : (v : G)⁻¹ ∈ ruQ M.T := h.2
    have := (ruQ M.T).inv_mem h2
    exact hvQ' (by simpa using this)
  have hclass : ∀ u : ↥(ruH M.T), (u : G) ∈ M.conjU g⁻¹ → π u = 1 ∨ π u = π v := by
    intro u hu
    by_cases huQ : (u : G) ∈ ruQ M.T
    · left
      exact (QuotientGroup.eq_one_iff u).mpr ((burnsideJ7_mem_pCore_iff (ruH M.T) u).mpr huQ)
    · right
      have hd : (u : G) * (v : G)⁻¹ ∈ M.conjU g⁻¹ ⊓ ruQ M.T :=
        burnsideJ7_mul_mem_of_relIndex_two hD hu (inv_mem hv) (fun h => huQ h.2) hvinvQ
      have h1 : (u * v⁻¹ : ↥(ruH M.T)) ∈ CFSG.pCore 2 ↥(ruH M.T) :=
        (burnsideJ7_mem_pCore_iff (ruH M.T) _).mpr hd.2
      have h2 : π (u * v⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
  apply le_antisymm
  ·
    rintro x ⟨u, hu, rfl⟩
    rw [burnsideJ7_mem_centerImg]
    have huS : (u : G) ∈ ruS M.L := M.conjU_le_S hlL hu
    have huT : (u : G) ∈ (M.T : Subgroup G) := M.toRuData.S_le_T huS
    refine ⟨⟨u, huT, rfl⟩, ?_⟩
    rintro d ⟨y, hy, rfl⟩
    rcases hclass u hu with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact hcentral y hy
  ·
    intro x hx
    rw [burnsideJ7_mem_centerImg] at hx
    obtain ⟨⟨y, hy, rfl⟩, hcen⟩ := hx
    set ι := burnsideJ7_iota M with hι
    have hιπ : ∀ z : ↥(ruH M.T), ι (π z) = M.φ z := fun z => rfl
    have hSP : ∀ s ∈ Sigma.SP0, ∃ y' : ↥(ruH M.T), (y' : G) ∈ (M.T : Subgroup G) ∧ M.φ y' = s := by
      intro s hs
      rw [← M.hSP0] at hs
      obtain ⟨y', hy', hφ⟩ := hs
      exact ⟨y', hy', hφ⟩
    have hyT : (y : G) ∈ (M.T : Subgroup G) := hy
    have hφy : M.φ y ∈ Sigma.SP0 := M.φ_mem_SP0 hyT
    have hφv : M.φ v ∈ Sigma.SP0 := M.φ_mem_SP0 hvT
    have hcy : ∀ s ∈ Sigma.SP0, M.φ y * s = s * M.φ y := by
      intro s hs
      obtain ⟨y', hy', rfl⟩ := hSP s hs
      have := hcen (π y') ⟨y', hy', rfl⟩
      have h2 := congrArg ι this
      rw [map_mul, map_mul, hιπ, hιπ] at h2
      exact h2.symm
    have hcv : ∀ s ∈ Sigma.SP0, M.φ v * s = s * M.φ v := by
      intro s hs
      obtain ⟨y', hy', rfl⟩ := hSP s hs
      have := hcentral y' hy'
      have h2 := congrArg ι this
      rw [map_mul, map_mul, hιπ, hιπ] at h2
      exact h2.symm
    have hφv1 : M.φ v ≠ 1 := by
      intro h
      apply hπv
      apply ι.injective
      rw [hιπ, h, map_one]
    rcases burnsideJ7_SP0_center _ hφy _ hφv hcy hcv with h | h | h
    · have : π y = 1 := by
        apply ι.injective
        rw [hιπ, h, map_one]
      rw [this]
      exact one_mem _
    · exact absurd h hφv1
    · have : π y = π v := by
        apply ι.injective
        rw [hιπ, hιπ, h]
      rw [this]
      exact ⟨v, hv, rfl⟩

end BurnsideJ7_fold

section

theorem as_J_4_1 : J_4_1 := by
  have hSt : CFSG.Quasithin.RuType.StUniqueStatement := CFSG.Quasithin.RuType.stUnique
  intro G _ _ L V T h V2 hV2 g hg hgH
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM hSt
  subst hML
  have hVeq : V = CFSG.Quasithin.RuType.ruV M.L := ChIJK.RuType.V_eq_ruV h
  have hTeq : T = (M.T : Subgroup G) := by
    rw [hMT]
    exact (ChIJK.RuType.coe_sylowT h).symm
  subst hVeq hTeq
  have hHeq := burnsideJ7_HRu_eq h hMT
  have hQeq := burnsideJ7_QRu_eq h hMT
  have hUeq := burnsideJ7_URu_eq h hMT
  have hHCeq := burnsideJ7_HCRu_eq h hMT
  have hgH' : g ∉ CFSG.Quasithin.RuType.ruH M.T := by
    rw [← hHeq]
    exact hgH
  obtain ⟨hlL, hlPl, hne⟩ := burnsideJ7_g_facts M hV2 hg hgH'
  intro v hv hvQ
  have hv' : (v : G) ∈ M.conjU g⁻¹ := by
    rw [hUeq] at hv
    exact hv
  have hvQ' : (v : G) ∉ CFSG.Quasithin.RuType.ruQ M.T := by
    intro hq
    apply hvQ
    rw [hUeq, hQeq]
    exact Subgroup.mem_inf.mpr ⟨hv', hq⟩
  have hvS : (v : G) ∈ CFSG.Quasithin.RuType.ruS M.L := M.conjU_le_S hlL hv'
  have hvH : (v : G) ∈ CFSG.Quasithin.RuType.ruH M.T :=
    M.toRuData.T_le_H (M.toRuData.S_le_T hvS)
  have hvK : (v : G) ∈ M.K := M.S_le_K hvS
  have hv2 : (v : G) ^ 2 = 1 := by
    have h1 := M.U_sq (M.mem_conjU.mp hv')
    simp only [inv_inv] at h1
    rw [conj_pow] at h1
    have : (v : G) ^ 2 = g⁻¹ * (g * (v : G) ^ 2 * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hv2' : (v : G) * (v : G) = 1 := by rw [← pow_two]; exact hv2
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact burnsideJ7_clause1 M hV2 (ChIJK.HRu (M.T : Subgroup G))
      (ChIJK.URu (CFSG.Quasithin.RuType.ruV M.L) (M.T : Subgroup G)) hHeq hUeq hg hgH v hv hvQ
  · obtain ⟨B5, h1, h2⟩ := burnsideJ7_clause2a M hvH hvK hvQ' hv2'
    exact ⟨B5, by rw [hHeq]; exact h1, h2⟩
  · exact burnsideJ7_clause2b M (ChIJK.HRu (M.T : Subgroup G)) hHeq v hvK hvQ' hv2
  · intro B5 hB5 hinv
    rw [hHeq] at hB5
    obtain ⟨b, hbH, hb5, rfl⟩ := burnsideJ7_sylow5_cyclic M hB5
    have hvinv : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right hv2'
    have hb4 : b⁻¹ = b ^ 4 := by
      have h5 : b ^ 5 = 1 := CFSG.Quasithin.RuType.pow_five_of_orderOf hb5
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact h5
    have hvb : (v : G) * b * (v : G)⁻¹ = b ^ 4 := by
      have := hinv.2 b (Subgroup.mem_zpowers b)
      rw [hvinv, hb4] at this
      rw [hvinv]
      exact this
    rw [ChIJK.Q5Ru, hQeq, hUeq]
    refine ⟨⟨(burnsideJ7_Q5_section_U M hbH hb5).1, (burnsideJ7_Q5_section_U M hbH hb5).2,
      burnsideJ7_quaternion M hbH hb5, burnsideJ7_Q_eq_sup M hbH hb5,
      burnsideJ7_T5U_inf_Q5 M hbH hb5⟩,
      burnsideJ7_clause6 M hV2 hbH hb5 hlL hlPl hne hv' hvQ' hvb, ?_⟩
    rw [burnsideJ7_comm_eq_Q5 M hbH hb5]
    exact burnsideJ7_comm_le_Q5 M hbH hb5 hlL hne hv' hvQ' hvb
  · exact burnsideJ7_clause4 M (ChIJK.HRu (M.T : Subgroup G))
      (ChIJK.URu (CFSG.Quasithin.RuType.ruV M.L) (M.T : Subgroup G)) hHeq hUeq
  · rw [hHCeq, hUeq]
    exact burnsideJ7_clause5 M hV2 hg hgH'

end

@[expose] def J_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
      T = R2Ru L V2 T ⊔ QRu T ∧
      (IsElemAbelianSection (WRu L V V2 T) (URu V T) 4 ∧ Nat.card ↥(WRu L V V2 T) = 2 ^ 9) ∧
      IsElemAbelianSection (Q5Ru T B5) (Q5Ru T B5 ⊓ WRu L V V2 T) 2

section

theorem as_J_4_2 : J_4_2 := by
  have hSt : CFSG.Quasithin.RuType.StUniqueStatement := CFSG.Quasithin.RuType.stUnique
  intro G _ _ L V T h V2 hV2 g hg hgH v hv hvQ B5 hB5 hinv
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM hSt
  subst hML
  have hVeq : V = CFSG.Quasithin.RuType.ruV M.L := ChIJK.RuType.V_eq_ruV h
  have hTeq : T = (M.T : Subgroup G) := by
    rw [hMT]
    exact (ChIJK.RuType.coe_sylowT h).symm
  subst hVeq hTeq
  have hHeq := burnsideJ7_HRu_eq h hMT
  have hQeq := burnsideJ7_QRu_eq h hMT
  have hUeq := burnsideJ7_URu_eq h hMT
  rw [hHeq] at hgH hB5
  rw [hUeq] at hv hvQ
  rw [hQeq] at hvQ
  have hgL2 : g ∈ ChIJK.twoResidual M.G2 := by
    rw [← burnsideJ7_L2Ru_eq M hV2]
    exact hg
  have hgG2 : g ∈ M.G2 := burnsideJ7_twoResidual_le _ hgL2
  obtain ⟨hgL, hgPl⟩ := CFSG.Quasithin.RuType.mem_pullL.mp hgG2
  have hlL : g⁻¹ ∈ M.L := inv_mem hgL
  have hlPl : M.θ ⟨g⁻¹, hlL⟩ ∈ CFSG.Quasithin.RuType.SL3.Pl := by
    have : M.θ ⟨g⁻¹, hlL⟩ = (M.θ ⟨g, hgL⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact inv_mem hgPl
  have hv' : v ∈ M.conjU g⁻¹ := hv
  have hvQ' : v ∉ CFSG.Quasithin.RuType.ruQ M.T := fun hq => hvQ (Subgroup.mem_inf.mpr ⟨hv, hq⟩)
  obtain ⟨b, hbH, hb5, rfl⟩ := burnsideJ7_sylow5_cyclic M hB5
  have hv2 : v ^ 2 = 1 := by
    have h1 := M.U_sq (M.mem_conjU.mp hv')
    simp only [inv_inv] at h1
    rw [conj_pow] at h1
    have : v ^ 2 = g⁻¹ * (g * v ^ 2 * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)
  have hb4 : b⁻¹ = b ^ 4 := by
    have h5 : b ^ 5 = 1 := CFSG.Quasithin.RuType.pow_five_of_orderOf hb5
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact h5
  have hvb : v * b * v⁻¹ = b ^ 4 := by
    have := hinv.2 b (Subgroup.mem_zpowers b)
    rw [hvinv, hb4] at this
    rw [hvinv]
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [burnsideJ7_R2Ru_eq M hV2, hQeq]
    exact burnsideJ7_T_eq_R2_sup_Q M
  · rw [burnsideJ7_WRu_eq h hMT hV2, hUeq]
    exact ⟨burnsideJ7_W_section_U M, M.card_W⟩
  · rw [ChIJK.Q5Ru, hQeq, burnsideJ7_comm_eq_Q5 M hbH hb5, burnsideJ7_WRu_eq h hMT hV2]
    exact burnsideJ7_Q5_section M hbH hb5 hlL hlPl hv' hvQ' hvb

end

@[expose] def J_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
      IsElemAbelianSection (S2Ru L V V2 T) V 6 ∧ S2Ru L V V2 T = WRu L V V2 T

theorem as_J_4_3 : J_4_3 := by
  have hSt : CFSG.Quasithin.RuType.StUniqueStatement := CFSG.Quasithin.RuType.stUnique
  intro G _ _ L V T h V2 hV2
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM hSt
  subst hML
  have hVeq : V = CFSG.Quasithin.RuType.ruV M.L := ChIJK.RuType.V_eq_ruV h
  have hTeq : T = (M.T : Subgroup G) := by
    rw [hMT]
    exact (ChIJK.RuType.coe_sylowT h).symm
  subst hVeq hTeq
  have hS2 := burnsideJ7_S2Ru_eq M hV2
  have hW := burnsideJ7_WRu_eq h hMT hV2
  rw [hS2, hW]
  exact ⟨burnsideJ7_W_section M, rfl⟩

@[expose] def J_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
      ∃ a : G,
        (IsElemAbelianSection (Q5Ru T B5 ⊔ S2Ru L V V2 T) (S2Ru L V V2 T) 2 ∧
          IsAChoice L V T V2 B5 a) ∧
        (IsElemAbelianSection (ARu L V V2 T a) (S2Ru L V V2 T) 2 ∧
          ARu L V V2 T a ⊓ SRu L = S2Ru L V V2 T ∧ ARu L V V2 T a ⊔ SRu L = R2Ru L V2 T ∧
          ∀ B : Subgroup G, ARu L V V2 T a ≤ B → B ≤ R2Ru L V2 T →
            X ≤ Subgroup.normalizer (B : Set G) → B = ARu L V V2 T a ∨ B = R2Ru L V2 T) ∧
        (ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) ∧
          ARu L V V2 T a ≤ Subgroup.normalizer ((Q5Ru T B5 : Subgroup G) : Set G) ∧
          Nonempty (↥(ARu L V V2 T a ⊔ B5 ⊔ Q5Ru T B5) ⧸
            CFSG.pCore 2 ↥(ARu L V V2 T a ⊔ B5 ⊔ Q5Ru T B5) ≃* Sz 0)) ∧
        ARu L V V2 T a ⊔ Q5Ru T B5 ⊔ SRu L = T ∧
        (∃ X' : Subgroup G, IsSylowIn 3 X' (G2Ru L V2 T) ∧
          Q5Ru T B5 ≤ Subgroup.normalizer ((X' ⊔ ARu L V V2 T a : Subgroup G) : Set G) ∧
          ∃ (_ : ((ARu L V V2 T a).subgroupOf (Q5Ru T B5 ⊔ X' ⊔ ARu L V V2 T a)).Normal),
            Nonempty (↥(Q5Ru T B5 ⊔ X' ⊔ ARu L V V2 T a) ⧸
              (ARu L V V2 T a).subgroupOf (Q5Ru T B5 ⊔ X' ⊔ ARu L V V2 T a) ≃*
              Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))

section BurnsideJ8b

private theorem burnsideJ8b_exists_gen {G : Type} [Group G] [Finite G] {H B : Subgroup G}
    (hH : Nat.card H = 2 ^ 11 * 120) (hB : CFSG.ASVolI.ChIJK.IsSylowIn 5 B H) :
    ∃ b : G, orderOf b = 5 ∧ Subgroup.zpowers b = B := by
  obtain ⟨hBH, hBp, hidx⟩ := hB
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have h := Subgroup.index_mul_card (B.subgroupOf H)
  rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hBH, hn, hH] at h
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at h
      apply hidx
      rw [h]
      norm_num
    · rfl
    · exfalso
      have h25 : 25 ∣ (B.subgroupOf H).index * 5 ^ (n + 2) :=
        Dvd.dvd.mul_left (by
          rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
          exact pow_dvd_pow 5 (by omega)) _
      rw [h] at h25
      norm_num at h25
  rw [hn1, pow_one] at hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 (by rw [hn])
  refine ⟨(x : G), by rw [Subgroup.orderOf_coe, hx], ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_
  rw [hn, Nat.card_zpowers, Subgroup.orderOf_coe, hx]

open scoped commutatorElement in
private theorem burnsideJ8b_comm_conj_mem {G : Type*} [Group G] {A B : Subgroup G} {a k : G}
    (ha : a ∈ A) (hk : k ∈ ⁅A, B⁆) : a * k * a⁻¹ ∈ ⁅A, B⁆ := by
  rw [Subgroup.commutator_def] at hk ⊢
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
    have e : a * ⁅g₁, g₂⁆ * a⁻¹ = ⁅a * g₁, g₂⁆ * ⁅a, g₂⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a * g₁, A.mul_mem ha hg₁, g₂, hg₂, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨a, ha, g₂, hg₂, rfl⟩))
  | one => simp
  | mul x y _ _ hx hy =>
    have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

private theorem burnsideJ8b_mul_rotate5 {A : Type*} [CommGroup A] (a b c d e : A) :
    b * c * d * e * a = a * b * c * d * e := by
  simp only [mul_comm, mul_left_comm, mul_assoc]

private theorem burnsideJ8b_norm_identity {A : Type*} [CommGroup A] (u e1 e2 e3 e4 : A) (hu2 :
    u * u = 1) :
    u * (e1 * u) * (e2 * u) * (e3 * u) * (e4 * u) = u * (e1 * e2 * e3 * e4) := by
  have h5 : u * u * u * u * u = u := by
    have : u * u * u * u * u = (u * u) * (u * u) * u := by simp only [mul_assoc]
    rw [this, hu2, one_mul, one_mul]
  calc u * (e1 * u) * (e2 * u) * (e3 * u) * (e4 * u)
      = (u * u * u * u * u) * (e1 * e2 * e3 * e4) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = u * (e1 * e2 * e3 * e4) := by rw [h5]

open scoped commutatorElement in
open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_U_decomp {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) {u : G}
    (hu : u ∈ ruU M.L M.T) :
    ∃ n ∈ ruZ M.T, ∃ e ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆, e ∈ ruU M.L M.T ∧ u = n * e⁻¹ := by
  classical
  letI : CommGroup ↥(ruU M.L M.T) :=
    { (inferInstance : Group ↥(ruU M.L M.T)) with
      mul_comm := fun x y => M.U_elem.1.is_comm.comm x y }
  let u' : ↥(ruU M.L M.T) := ⟨u, hu⟩
  have hu2 : u' * u' = 1 := Subtype.ext (by
    have := M.U_sq hu
    simpa [pow_two] using this)
  let c : ℕ → ↥(ruU M.L M.T) := fun i =>
    ⟨b ^ i * u * (b ^ i)⁻¹, M.conj_mem_U (pow_mem hbH i) hu⟩
  have hc : ∀ i, (c i : G) = b ^ i * u * (b ^ i)⁻¹ := fun i => rfl
  have hc0 : c 0 = u' := Subtype.ext (by simp [hc, u'])
  have hc5 : c 5 = c 0 := Subtype.ext (by rw [hc, hc, pow_five_of_orderOf hb5]; simp)
  have hshift : ∀ i, b * (c i : G) * b⁻¹ = (c (i + 1) : G) := by
    intro i; rw [hc, hc, pow_succ']; group
  let N : ↥(ruU M.L M.T) := c 0 * c 1 * c 2 * c 3 * c 4
  have hNb : b * (N : G) * b⁻¹ = (N : G) := by
    have e1 : b * (N : G) * b⁻¹ = (c 1 : G) * c 2 * c 3 * c 4 * c 5 := by
      calc b * (N : G) * b⁻¹
          = (b * (c 0 : G) * b⁻¹) * (b * (c 1 : G) * b⁻¹) * (b * (c 2 : G) * b⁻¹) *
              (b * (c 3 : G) * b⁻¹) * (b * (c 4 : G) * b⁻¹) := by
            simp only [N, Subgroup.coe_mul]; group
        _ = _ := by rw [hshift, hshift, hshift, hshift, hshift]
    rw [e1, hc5]
    have e2 : ((c 1 * c 2 * c 3 * c 4 * c 0 : ↥(ruU M.L M.T)) : G) = (N : G) := by
      congr 1
      exact burnsideJ8b_mul_rotate5 (c 0) (c 1) (c 2) (c 3) (c 4)
    simpa only [Subgroup.coe_mul] using e2
  have hNZ : (N : G) ∈ ruZ M.T := by
    refine RuDataM.mem_Z_of_T5_U hbH hb5 (x := (N : G)) ⟨M.U_le_Q N.2, ?_⟩ N.2
    exact mem_G5.mpr (by
      calc (N : G) * b = b * (N : G) * b⁻¹ * b := by rw [hNb]
        _ = b * N := by group)
  obtain ⟨e, he1, he2⟩ : ∃ e : ℕ → ↥(ruU M.L M.T),
      (∀ i, c i = e i * u') ∧ (∀ i, (e i : G) = ⁅b ^ i, u⁆) := by
    refine ⟨fun i => c i * u'⁻¹, fun i => by simp, fun i => ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc, commutatorElement_def]
    rfl
  have hKe : ∀ i, (e i : G) ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
    intro i
    rw [he2]
    have h1 : ⁅u, b ^ i⁆ ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator (M.U_le_Q hu) (pow_mem (Subgroup.mem_zpowers b) i)
    have h2 : ⁅b ^ i, u⁆ = ⁅u, b ^ i⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact Subgroup.inv_mem _ h1
  let E : ↥(ruU M.L M.T) := e 1 * e 2 * e 3 * e 4
  have hNE : N = u' * E := by
    have h := burnsideJ8b_norm_identity u' (e 1) (e 2) (e 3) (e 4) hu2
    have hN' : N = u' * (e 1 * u') * (e 2 * u') * (e 3 * u') * (e 4 * u') := by
      simp only [N, hc0, he1 1, he1 2, he1 3, he1 4]
    rw [hN', h]
  have hEK : (E : G) ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
    simp only [E, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKe 1) (hKe 2)) (hKe 3))
      (hKe 4)
  refine ⟨(N : G), hNZ, (E : G), hEK, E.2, ?_⟩
  have h : (N : G) = u * (E : G) := by
    rw [hNE]; rfl
  rw [h]; group

open scoped commutatorElement in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_Z_le_comm {G : Type} [Group G]
    [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ruZ M.T ≤ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
  obtain ⟨q, hq, hnc⟩ := M.exists_Q_not_comm
  have hvU : (M.v1V : G) ∈ ruU M.L M.T := M.V_le_U M.v1V.2
  obtain ⟨n, hn, e, he, heU, hne⟩ := burnsideJ8b_U_decomp M hbH hb5 hvU
  set u : G := (M.v1V : G) with hu
  have hqH : q ∈ ruH M.T := pCoreOf_le 2 _ hq
  have heH : e ∈ ruH M.T := M.U_le_H heU
  have hcomm := M.two.UZ_central q hq u hvU
  have hne1 : q * u * q⁻¹ * u⁻¹ ≠ 1 := by
    intro h
    apply hnc
    have : q * u = u * q := by
      calc q * u = (q * u * q⁻¹ * u⁻¹) * (u * q) := by group
        _ = u * q := by rw [h, one_mul]
    exact this
  have hn1 : n * q = q * n := M.Z_comm_H hn hqH
  have hn2 : ∀ h ∈ ruH M.T, n * h = h * n := fun h hh => M.Z_comm_H hn hh
  have hform : q * u * q⁻¹ * u⁻¹ = (q * e⁻¹ * q⁻¹) * e := by
    rw [hne]
    have hq' : q * n * q⁻¹ = n := by rw [← hn1]; group
    have hcen : n * (q * e⁻¹ * q⁻¹ * e) = (q * e⁻¹ * q⁻¹ * e) * n :=
      hn2 _ (mul_mem (mul_mem (mul_mem hqH (inv_mem heH)) (inv_mem hqH)) heH)
    calc q * (n * e⁻¹) * q⁻¹ * (n * e⁻¹)⁻¹
        = (q * n * q⁻¹) * (q * e⁻¹ * q⁻¹ * e) * n⁻¹ := by group
      _ = n * (q * e⁻¹ * q⁻¹ * e) * n⁻¹ := by rw [hq']
      _ = (q * e⁻¹ * q⁻¹ * e) * n * n⁻¹ := by rw [hcen]
      _ = (q * e⁻¹ * q⁻¹) * e := by group
  have hK : (q * e⁻¹ * q⁻¹) * e ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ :=
    Subgroup.mul_mem _ (burnsideJ8b_comm_conj_mem hq (Subgroup.inv_mem _ he)) he
  rw [← hform] at hK
  have hzK : M.z ∈ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
    rcases M.mem_Z_iff.mp hcomm with h | h
    · exact absurd h hne1
    · rw [← h]; exact hK
  intro _ hx
  rcases M.mem_Z_iff.mp hx with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact hzK

open scoped commutatorElement in
open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_U_le_comm {G : Type} [Group G]
    [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ruU M.L M.T ≤ ⁅ruQ M.T, Subgroup.zpowers b⁆ := by
  intro u hu
  obtain ⟨_, hn, _, he, -, rfl⟩ := burnsideJ8b_U_decomp M hbH hb5 hu
  exact Subgroup.mul_mem _ (burnsideJ8b_Z_le_comm M hbH hb5 hn) (Subgroup.inv_mem _ he)

open scoped commutatorElement in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_Q5_eq {G : Type} [Group G] [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    ⁅ruQ M.T, Subgroup.zpowers b⁆ = M.Q5 hbH := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro q hq y hy
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hy
    have hbkH : b ^ k ∈ ruH M.T := pow_mem hbH k
    have hxQ : ⁅q, b ^ k⁆ ∈ ruQ M.T := by
      have e : ⁅q, b ^ k⁆ = q * (b ^ k * q⁻¹ * (b ^ k)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hq (M.conj_mem_Q hbkH (inv_mem hq))
    refine (M.mem_Q5 hbH).mpr ⟨hxQ, ?_⟩
    set hk : ruH M.T := ⟨b, hbH⟩ ^ k with hkdef
    have hkc : (hk : G) = b ^ k := rfl
    have hmem : (M.dQ hk ((⟨q, hq⟩ : ruQ M.T) : M.Qbar))⁻¹ ∈ M.Q5bar ⟨b, hbH⟩ :=
      inv_mem (M.dQ_pow_range_le ⟨b, hbH⟩ k ⟨_, rfl⟩)
    convert hmem using 1
    rw [M.dQ_apply, M.actQ_mk, mul_inv_rev, inv_inv]
    show ((⟨⁅q, b ^ k⁆, hxQ⟩ : ruQ M.T) : M.Qbar) =
      ((⟨q, hq⟩ : ruQ M.T) : M.Qbar) * ((M.conjQ hk ⟨q, hq⟩ : ruQ M.T) : M.Qbar)⁻¹
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show ⁅q, b ^ k⁆ = q * (hk * q * (hk : G)⁻¹)⁻¹
    rw [hkc]
    simp only [commutatorElement_def]
    group
  · intro x hx
    obtain ⟨hxQ, hxb⟩ := (M.mem_Q5 hbH).mp hx
    obtain ⟨ā, hā⟩ := hxb
    induction ā using QuotientGroup.induction_on with
    | H q =>
    rw [M.dQ_apply, M.actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, M.mk_eq_mk_iff] at hā
    have hU : (b * (q : G) * b⁻¹ * (q : G)⁻¹)⁻¹ * x ∈ ruU M.L M.T := hā
    have e : x = (b * (q : G) * b⁻¹ * (q : G)⁻¹) *
        ((b * (q : G) * b⁻¹ * (q : G)⁻¹)⁻¹ * x) := by group
    rw [e]
    refine Subgroup.mul_mem _ ?_ (burnsideJ8b_U_le_comm M hbH hb5 hU)
    have e2 : b * (q : G) * b⁻¹ * (q : G)⁻¹ = ⁅(q : G), b⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e2]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator q.2 (Subgroup.mem_zpowers b))

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_mem_Q_of_mul_zpow {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {b : G}
    (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) {y : G} (hyH : y ∈ ruH M.T) {m : ℕ}
    (hy2 : y ^ 2 ^ m = 1) {i : ℤ} (hQ : y * b ^ i ∈ ruQ M.T) : y ∈ ruQ M.T ∧ b ^ i = 1 := by
  have hbi : b ^ i ∈ ruH M.T := zpow_mem hbH i
  have hk : (⟨y * b ^ i, mul_mem hyH hbi⟩ : ruH M.T) ∈ M.σ5.ker := by
    rw [M.σ5_ker, Subgroup.mem_subgroupOf]
    exact hQ
  have hσ : M.σ5 ⟨y, hyH⟩ = (M.σ5 ⟨b ^ i, hbi⟩)⁻¹ := by
    have e : (⟨y * b ^ i, mul_mem hyH hbi⟩ : ruH M.T) = ⟨y, hyH⟩ * ⟨b ^ i, hbi⟩ := rfl
    rw [MonoidHom.mem_ker, e, map_mul] at hk
    exact eq_inv_of_mul_eq_one_left hk
  have hb5i : (b ^ i) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      pow_five_of_orderOf hb5, one_zpow]
  have h5 : (M.σ5 ⟨y, hyH⟩) ^ 5 = 1 := by
    rw [hσ, inv_pow, ← map_pow]
    have : (⟨b ^ i, hbi⟩ : ruH M.T) ^ 5 = 1 := Subtype.ext hb5i
    rw [this, map_one, inv_one]
  have h2 : (M.σ5 ⟨y, hyH⟩) ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨y, hyH⟩ : ruH M.T) ^ 2 ^ m = 1 := Subtype.ext hy2
    rw [this, map_one]
  have h1 : M.σ5 ⟨y, hyH⟩ = 1 := by
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one h2)
    have : Nat.gcd 5 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hyQ : y ∈ ruQ M.T := by
    have : (⟨y, hyH⟩ : ruH M.T) ∈ M.σ5.ker := h1
    rw [M.σ5_ker, Subgroup.mem_subgroupOf] at this
    exact this
  refine ⟨hyQ, ?_⟩
  have hbiQ : b ^ i ∈ ruQ M.T := by
    have e : b ^ i = y⁻¹ * (y * b ^ i) := by group
    rw [e]
    exact mul_mem (inv_mem hyQ) hQ
  have hd1 : orderOf (b ^ i) ∣ 5 := orderOf_dvd_of_pow_eq_one hb5i
  have hd2 : orderOf (b ^ i) ∣ 2 ^ 11 := by
    rw [← M.toRuData.card_Q]
    exact Subgroup.orderOf_dvd_natCard _ hbiQ
  have hd := Nat.dvd_gcd hd1 hd2
  have : Nat.gcd 5 (2 ^ 11) = 1 := by norm_num
  rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_zpowers_le_normalizer_Q5 {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {b : G} (hbH : b ∈ ruH M.T) :
    Subgroup.zpowers b ≤ Subgroup.normalizer (M.Q5 hbH : Set G) := by
  intro _ hg
  refine mem_normalizer_of_conj_mem fun _ hx => ?_
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hgb : b ^ i * b * (b ^ i)⁻¹ = b ^ 1 * 1 := by group
  exact M.conj_mem_Q5 hbH (zpow_mem hbH i) (one_mem _) hgb hx

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_mem_Q5_sup {G : Type} [Group G] [Finite G] (M : RuDataM G) {b : G}
    (hbH : b ∈ ruH M.T) {x : G} (hx : x ∈ M.Q5 hbH ⊔ Subgroup.zpowers b) :
    ∃ q ∈ M.Q5 hbH, ∃ i : ℤ, x = q * b ^ i := by
  have hx' : x ∈ ((M.Q5 hbH ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (burnsideJ8b_zpowers_le_normalizer_Q5 M hbH)] at hx'
  obtain ⟨q, hq, _, hz, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨q, hq, i, rfl⟩

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_F1_inf_Q_le {G : Type} [Group G]
    [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) {A : Subgroup G}
    (hA2 : IsPGroup 2 A) (hAH : A ≤ ruH M.T)
    (hAn : A ≤ Subgroup.normalizer ((M.Q5 hbH ⊔ Subgroup.zpowers b : Subgroup G) : Set G))
    {x : G} (hx : x ∈ (A ⊔ M.Q5 hbH) ⊔ Subgroup.zpowers b) (hxQ : x ∈ ruQ M.T) :
    x ∈ A ⊔ M.Q5 hbH := by
  have hx' : x ∈ ((A ⊔ (M.Q5 hbH ⊔ Subgroup.zpowers b) : Subgroup G) : Set G) := by
    have e : (A ⊔ M.Q5 hbH) ⊔ Subgroup.zpowers b = A ⊔ (M.Q5 hbH ⊔ Subgroup.zpowers b) :=
      sup_assoc _ _ _
    rw [← e]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAn] at hx'
  obtain ⟨y, hy, _, hz, rfl⟩ := hx'
  obtain ⟨q, hq, i, rfl⟩ := burnsideJ8b_mem_Q5_sup M hbH hz
  have hyH := hAH hy
  have hqQ := M.Q5_le_Q hbH hq
  have hyb : y * b ^ i ∈ ruQ M.T := by
    have e : y * b ^ i = (y * q * y⁻¹)⁻¹ * (y * (q * b ^ i)) := by group
    rw [e]
    exact mul_mem (inv_mem (M.conj_mem_Q hyH hqQ)) hxQ
  obtain ⟨m, hm⟩ := hA2 ⟨y, hy⟩
  have hy2 : y ^ 2 ^ m = 1 := congrArg Subtype.val hm
  obtain ⟨-, hbi⟩ := burnsideJ8b_mem_Q_of_mul_zpow M hbH hb5 hyH hy2 hyb
  have e : y * (q * b ^ i) = y * q := by rw [hbi, mul_one]
  show y * (q * b ^ i) ∈ A ⊔ M.Q5 hbH
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_center_le {G : Type} [Group G]
    [Finite G]
    (M : RuDataM G) {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) {TF : Subgroup G}
    (hTFH : TF ≤ ruH M.T) (hQ5 : M.Q5 hbH ≤ TF) {c : G} (hc : c ∈ TF)
    (hcc : ∀ x ∈ TF, x * c = c * x) : c ∈ ruZ M.T := by
  have hUTF : ruU M.L M.T ≤ TF := (M.U_le_Q5 hbH).trans hQ5
  have hcU : ∀ u ∈ ruU M.L M.T, u * c = c * u := fun u hu => hcc u (hUTF hu)
  have hcHC : c ∈ M.HC :=
    Subgroup.mem_inf.mpr ⟨hTFH hc, Subgroup.mem_centralizer_iff.mpr hcU⟩
  have hcUmem : c ∈ ruU M.L M.T := by
    by_contra hcU'
    have hcard := M.card_le_of_centralizes_HC hcHC hcU' (X := M.Q5 hbH ⊓ ruS M.L)
      (inf_le_left.trans (M.Q5_le_Q hbH)) (fun x hx => hcc x (hQ5 hx.1))
    rw [M.card_Q5_inf_S hbH hb5] at hcard
    norm_num at hcard
  refine M.mem_Z_of_comm_Q hcUmem fun _ hq => ?_
  obtain ⟨a, ha, h, hh, rfl⟩ := RuDataM.exists_Q5_mul_HC hbH hb5 hq
  have h1 := hcc a (hQ5 ha)
  have h2 : h * c = c * h :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2 c hcUmem)).symm
  calc a * h * c = a * (h * c) := mul_assoc _ _ _
    _ = a * (c * h) := by rw [h2]
    _ = (a * c) * h := (mul_assoc _ _ _).symm
    _ = (c * a) * h := by rw [h1]
    _ = c * (a * h) := mul_assoc _ _ _

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_pCoreOf_le_sylow {G : Type} [Group G] [Finite G] {T X : Subgroup G}
    (hTp : IsPGroup 2 T) (hTX : T ≤ X) (hidx : ¬ 2 ∣ T.relIndex X) : pCoreOf 2 X ≤ T := by
  have hS' : IsPGroup 2 (T.subgroupOf X) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  let P : Sylow 2 X := hS'.toSylow hidx
  have : (CFSG.Open.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : CFSG.Open.pCore 2 X ≤ (P : Subgroup X) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup 2) P
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  have h3 : (P : Subgroup X).map X.subtype = T := by
    change (T.subgroupOf X).map X.subtype = T
    rw [Subgroup.map_subgroupOf_eq_of_le hTX]
  change Subgroup.map X.subtype (CFSG.Open.pCore 2 X) ≤ T
  rw [← h3]
  exact h2

private theorem burnsideJ8b_mem_conjugate {G : Type*} [Group G] {H : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate H g ↔ g * y * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_apply]

private theorem burnsideJ8b_conjugate_one {G : Type*} [Group G] (A : Subgroup G) :
    CFSG.conjugate A 1 = A := by
  ext y
  rw [burnsideJ8b_mem_conjugate]
  simp

private theorem burnsideJ8b_conjugate_conjugate {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate A g) h = CFSG.conjugate A (g * h) := by
  ext y
  rw [burnsideJ8b_mem_conjugate, burnsideJ8b_mem_conjugate, burnsideJ8b_mem_conjugate]
  have : g * (h * y * h⁻¹) * g⁻¹ = (g * h) * y * (g * h)⁻¹ := by group
  rw [this]

private theorem burnsideJ8b_conjugate_le_iff {G : Type*} [Group G] {A B : Subgroup G} (g : G) :
    CFSG.conjugate A g ≤ CFSG.conjugate B g ↔ A ≤ B := by
  constructor
  · intro h x hx
    have h1 : g⁻¹ * x * g ∈ CFSG.conjugate A g := by
      rw [burnsideJ8b_mem_conjugate]
      have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [this]; exact hx
    have h2 := h h1
    rw [burnsideJ8b_mem_conjugate] at h2
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [this] at h2
  · intro h x hx
    rw [burnsideJ8b_mem_conjugate] at hx ⊢
    exact h hx

private theorem burnsideJ8b_conjugate_sup {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

private theorem burnsideJ8b_conjugate_inf {G : Type*} [Group G] (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊓ B) g = CFSG.conjugate A g ⊓ CFSG.conjugate B g := by
  ext y
  simp only [burnsideJ8b_mem_conjugate, Subgroup.mem_inf]

private theorem burnsideJ8b_conjugate_zpowers {G : Type*} [Group G] (x g : G) :
    CFSG.conjugate (Subgroup.zpowers x) g = Subgroup.zpowers (g⁻¹ * x * g) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

private theorem burnsideJ8b_conjugate_eq_self {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : CFSG.conjugate A g = A := by
  ext y
  rw [burnsideJ8b_mem_conjugate]
  exact ((Subgroup.mem_normalizer_iff.mp hg y).symm)

private theorem burnsideJ8b_card_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate A g) = Nat.card A := by
  unfold CFSG.conjugate
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem burnsideJ8b_normalizer_conjugate {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (Subgroup.normalizer (A : Set G)) g := by
  ext y
  rw [burnsideJ8b_mem_conjugate, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have := h (g⁻¹ * a * g)
    rw [burnsideJ8b_mem_conjugate, burnsideJ8b_mem_conjugate] at this
    have e : g * (y * (g⁻¹ * a * g) * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * a * (g * y * g⁻¹)⁻¹ := by group
    simpa [e, mul_assoc] using this
  · intro h a
    rw [burnsideJ8b_mem_conjugate, burnsideJ8b_mem_conjugate]
    have := h (g * a * g⁻¹)
    have e : g * (y * a * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact this

private theorem burnsideJ8b_conjugate_le_normalizer_iff {G : Type*} [Group G] {A B : Subgroup
    G} (g : G) :
    CFSG.conjugate A g ≤ Subgroup.normalizer ((CFSG.conjugate B g : Subgroup G) : Set G) ↔
      A ≤ Subgroup.normalizer (B : Set G) := by
  rw [burnsideJ8b_normalizer_conjugate, burnsideJ8b_conjugate_le_iff]

private theorem burnsideJ8b_oTwoQuot_congr {G : Type*} [Group G] {X Y : Subgroup G} (h : X = Y)
    {K : Type*} [Group K] (hY : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* K)) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* K) := by
  subst h; exact hY

private theorem burnsideJ8b_quot_congr {G : Type*} [Group G] {F F' A A' : Subgroup G} (hF : F = F')
    (hA : A = A') {K : Type*} [Group K] [(A.subgroupOf F).Normal] [(A'.subgroupOf F').Normal]
    (h : Nonempty (↥F' ⧸ A'.subgroupOf F' ≃* K)) : Nonempty (↥F ⧸ A.subgroupOf F ≃* K) := by
  subst hF; subst hA; exact h

private theorem burnsideJ8b_comm_of_sq {G : Type*} [Group G] {P N : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hsq : ∀ x ∈ P, x ^ 2 ∈ N) :
    ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N := by
  intro x hx y hy
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y⁻¹⁻¹) * (y ^ 2)⁻¹ := by
    simp only [pow_two]; group
  rw [e]
  refine N.mul_mem (N.mul_mem (hsq _ (P.mul_mem hx hy)) ?_) (N.inv_mem (hsq _ hy))
  exact (Subgroup.mem_normalizer_iff.mp (hPN (P.inv_mem hy)) _).mp (N.inv_mem (hsq _ hx))

private theorem burnsideJ8b_isElemAbelianSection_conjugate {G : Type} [Group G] [Finite G] {P N
    : Subgroup G}
    {k : ℕ} (t : G) :
    CFSG.ASVolI.ChIJK.IsElemAbelianSection (CFSG.conjugate P t) (CFSG.conjugate N t) k ↔
      CFSG.ASVolI.ChIJK.IsElemAbelianSection P N k := by
  unfold CFSG.ASVolI.ChIJK.IsElemAbelianSection
  have hrel : (CFSG.conjugate N t).relIndex (CFSG.conjugate P t) = N.relIndex P := by
    unfold CFSG.conjugate
    exact Subgroup.relIndex_map_map_of_injective N P (MulAut.conj t⁻¹).injective
  rw [hrel, burnsideJ8b_conjugate_le_iff]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ Iff.rfl))
  · constructor
    · intro h x hx
      have h1 : t⁻¹ * x * t ∈ CFSG.conjugate P t := by
        rw [burnsideJ8b_mem_conjugate]
        have : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
        rw [this]; exact hx
      have h2 := h _ h1
      rw [burnsideJ8b_mem_conjugate] at h2
      have e : t * ((t⁻¹ * x * t) ^ 2) * t⁻¹ = x ^ 2 := by
        have : (t⁻¹ * x * t) ^ 2 = t⁻¹ * x ^ 2 * t := by simp only [pow_two]; group
        rw [this]; group
      rwa [e] at h2
    · intro h x hx
      rw [burnsideJ8b_mem_conjugate] at hx ⊢
      have e : t * x ^ 2 * t⁻¹ = (t * x * t⁻¹) ^ 2 := by simp only [pow_two]; group
      rw [e]; exact h _ hx
  · constructor
    · intro h x hx y hy
      have hx' : t⁻¹ * x * t ∈ CFSG.conjugate P t := by
        rw [burnsideJ8b_mem_conjugate]
        have : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
        rw [this]; exact hx
      have hy' : t⁻¹ * y * t ∈ CFSG.conjugate P t := by
        rw [burnsideJ8b_mem_conjugate]
        have : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
        rw [this]; exact hy
      have h2 := h _ hx' _ hy'
      rw [burnsideJ8b_mem_conjugate] at h2
      have e : t * ((t⁻¹ * x * t) * (t⁻¹ * y * t) * (t⁻¹ * x * t)⁻¹ * (t⁻¹ * y * t)⁻¹) * t⁻¹ =
          x * y * x⁻¹ * y⁻¹ := by group
      rwa [e] at h2
    · intro h x hx y hy
      rw [burnsideJ8b_mem_conjugate] at hx hy ⊢
      have e : t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ =
          (t * x * t⁻¹) * (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * y * t⁻¹)⁻¹ := by group
      rw [e]; exact h _ hx _ hy

section MLevel

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK CFSG.LieType.BorelTits in
private theorem burnsideJ8b_R0_sq : ∀ g ∈ SL3.R0, g * g = 1 := by decide +kernel

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_θ_Q5_mem_R0 {G : Type} [Group G] [Finite G] (M : RuDataM G) {q : G}
    (hq : q ∈ M.Q5 M.b5el_mem_H) :
    ∃ hqL : q ∈ M.L, M.θ ⟨q, hqL⟩ ∈ SL3.R0 := by
  have hqL : q ∈ M.L := M.Q5_le_L M.b5el_mem_H hq
  refine ⟨hqL, ?_⟩
  rw [← M.θQ_eq]
  exact ⟨⟨q, hqL⟩, Subgroup.mem_subgroupOf.mpr (M.Q5_le_Q M.b5el_mem_H hq), rfl⟩

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_Q5_sq_mem_W {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {q : G}
    (hq : q ∈ M.Q5 M.b5el_mem_H) : q ^ 2 ∈ M.W := by
  obtain ⟨hqL, hθ⟩ := burnsideJ8b_θ_Q5_mem_R0 M hq
  have hS : q ^ 2 ∈ ruS M.L := by
    rw [M.mem_S_iff_θ (pow_mem hqL 2)]
    have : (⟨q ^ 2, pow_mem hqL 2⟩ : M.L) = ⟨q, hqL⟩ ^ 2 := rfl
    rw [this, map_pow, pow_two]
    exact burnsideJ8b_R0_sq _ hθ
  exact M.Q5_inf_S_le_W ⟨pow_mem hq 2, hS⟩

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK CFSG.LieType.BorelTits in
private theorem burnsideJ8b_Q5W_section {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    IsElemAbelianSection (M.Q5 M.b5el_mem_H ⊔ M.W) M.W 2 := by
  have hPN : (M.Q5 M.b5el_mem_H ⊔ M.W) ≤ Subgroup.normalizer (M.W : Set G) :=
    sup_le M.Q5_le_normalizer_W Subgroup.le_normalizer
  have hsq : ∀ x ∈ M.Q5 M.b5el_mem_H ⊔ M.W, x ^ 2 ∈ M.W := by
    intro x hx
    have hx' : x ∈ ((M.Q5 M.b5el_mem_H ⊔ M.W : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ M.Q5_le_normalizer_W] at hx'
    obtain ⟨q, hq, w, hw, rfl⟩ := hx'
    have e : (q * w) ^ 2 = q ^ 2 * (q⁻¹ * w * q⁻¹⁻¹) * w := by
      simp only [pow_two]; group
    show (q * w) ^ 2 ∈ M.W
    rw [e]
    refine M.W.mul_mem (M.W.mul_mem (burnsideJ8b_Q5_sq_mem_W M hq) ?_) hw
    exact (Subgroup.mem_normalizer_iff.mp
      (M.Q5_le_normalizer_W (inv_mem hq)) w).mp hw
  refine ⟨le_sup_right, hsq, burnsideJ8b_comm_of_sq hPN hsq, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := M.W) (K := M.Q5 M.b5el_mem_H ⊔ M.W)
  rw [inf_eq_left.mpr le_sup_right, M.card_W, M.card_Q5W] at h
  have h' : (M.W.relIndex (M.Q5 M.b5el_mem_H ⊔ M.W)) * 2 ^ 9 = 2 ^ 2 * 2 ^ 9 := by
    rw [h]; norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_Q5W_inf_R2 {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    (M.Q5 M.b5el_mem_H ⊔ M.W) ⊓ M.R2 = Subgroup.zpowers M.ael ⊔ M.W := by
  apply le_antisymm
  · rintro x ⟨hx, hxR⟩
    have hx' : x ∈ ((M.Q5 M.b5el_mem_H ⊔ M.W : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ M.Q5_le_normalizer_W] at hx'
    obtain ⟨q, hq, w, hw, rfl⟩ := hx'
    have hWR : M.W ≤ M.R2 := M.W_le_S.trans M.S_le_R2
    have hqR : q ∈ M.R2 := by
      have e : q = (q * w) * w⁻¹ := by group
      rw [e]
      exact M.R2.mul_mem hxR (M.R2.inv_mem (hWR hw))
    obtain ⟨hqL, hqP⟩ := mem_pullL.mp hqR
    obtain ⟨_, hθR0⟩ := burnsideJ8b_θ_Q5_mem_R0 M hq
    rcases SL3.R2m_inf_R0 _ hqP hθR0 with h1 | h1
    · have hqS : q ∈ ruS M.L := (M.mem_S_iff_θ hqL).mpr h1
      exact Subgroup.mem_sup_right (M.W.mul_mem (M.Q5_inf_S_le_W ⟨hq, hqS⟩) hw)
    · have hL : M.ael⁻¹ * q ∈ M.L := mul_mem (inv_mem M.ael_mem_L) hqL
      have hS : M.ael⁻¹ * q ∈ ruS M.L := by
        rw [M.mem_S_iff_θ hL]
        have : (⟨M.ael⁻¹ * q, hL⟩ : M.L) = (⟨M.ael, M.ael_mem_L⟩ : M.L)⁻¹ * ⟨q, hqL⟩ := rfl
        rw [this, map_mul, map_inv, h1, M.θ_ael, inv_mul_cancel]
      have hQ : M.ael⁻¹ * q ∈ M.Q5 M.b5el_mem_H := mul_mem (inv_mem M.ael_mem_Q5) hq
      have hW : M.ael⁻¹ * q ∈ M.W := M.Q5_inf_S_le_W ⟨hQ, hS⟩
      have e : q * w = M.ael * ((M.ael⁻¹ * q) * w) := by group
      show q * w ∈ Subgroup.zpowers M.ael ⊔ M.W
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (M.W.mul_mem hW hw))
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨Subgroup.mem_sup_left M.ael_mem_Q5, M.ael_mem_R2⟩
    · exact le_inf le_sup_right (M.W_le_S.trans M.S_le_R2)

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK CFSG.LieType.BorelTits in
private theorem burnsideJ8b_A_section {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    IsElemAbelianSection M.Agrp M.W 2 := by
  refine ⟨M.W_le_Agrp, fun _ hx => M.sq_mem_W_of_R2 (M.Agrp_le_R2 hx), fun _ hx _ hy =>
    M.comm_mem_W_of_R2 (M.Agrp_le_R2 hx) (M.Agrp_le_R2 hy), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := M.W) (K := M.Agrp)
  rw [inf_eq_left.mpr M.W_le_Agrp, M.card_W, M.card_Agrp] at h
  have h' : (M.W.relIndex M.Agrp) * 2 ^ 9 = 2 ^ 2 * 2 ^ 9 := by
    rw [h]; norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_A_sup_S {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    M.Agrp ⊔ ruS M.L = M.R2 := by
  apply le_antisymm (sup_le M.Agrp_le_R2 M.S_le_R2)
  intro r hr
  obtain ⟨hrL, hrP⟩ := mem_pullL.mp hr
  obtain ⟨a, ha, haL, haθ⟩ := M.exists_Agrp_θ hrP
  have hsL : a⁻¹ * r ∈ M.L := mul_mem (inv_mem haL) hrL
  have hsS : a⁻¹ * r ∈ ruS M.L := by
    rw [M.mem_S_iff_θ hsL]
    have : (⟨a⁻¹ * r, hsL⟩ : M.L) = (⟨a, haL⟩ : M.L)⁻¹ * ⟨r, hrL⟩ := rfl
    rw [this, map_mul, map_inv, haθ, inv_mul_cancel]
  have e : r = a * (a⁻¹ * r) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hsS)

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_A_Q5_S {G : Type} [Group G] [Finite
    G] (M : RuDataM G) :
    M.Agrp ⊔ M.Q5 M.b5el_mem_H ⊔ ruS M.L = (M.T : Subgroup G) := by
  apply le_antisymm (sup_le (sup_le M.Agrp_le_T M.Q5_le_T) M.toRuData.S_le_T)
  intro x hx
  have hxL : x ∈ M.L := M.toRuData.T_le_L hx
  obtain ⟨_, hr, _, hs, hrs⟩ := SL3.P0_eq_R0_mul_R2m _ (M.θ_mem_P0 hx)
  obtain ⟨q, hq, hqL, hqθ⟩ := M.exists_Q5_θ M.b5el_mem_H M.orderOf_b5el hr
  obtain ⟨a, ha, haL, haθ⟩ := M.exists_Agrp_θ hs
  have hzL : q * a ∈ M.L := mul_mem hqL haL
  have hS : (q * a)⁻¹ * x ∈ ruS M.L := by
    have hL : (q * a)⁻¹ * x ∈ M.L := mul_mem (inv_mem hzL) hxL
    rw [M.mem_S_iff_θ hL]
    have : (⟨(q * a)⁻¹ * x, hL⟩ : M.L) = (⟨q, hqL⟩ * ⟨a, haL⟩)⁻¹ * ⟨x, hxL⟩ := rfl
    rw [this, map_mul, map_inv, map_mul, hqθ, haθ, ← hrs, inv_mul_cancel]
  have e : x = (q * a) * ((q * a)⁻¹ * x) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hS)
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left ha)

private theorem burnsideJ8b_exists_gen3 {G : Type} [Group G] [Finite G] {H B : Subgroup G}
    (hH : Nat.card H = 2 ^ 11 * 24) (hB : CFSG.ASVolI.ChIJK.IsSylowIn 3 B H) :
    ∃ b : G, orderOf b = 3 ∧ Subgroup.zpowers b = B := by
  obtain ⟨hBH, hBp, hidx⟩ := hB
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have h := Subgroup.index_mul_card (B.subgroupOf H)
  rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hBH, hn, hH] at h
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at h
      apply hidx
      rw [h]
      norm_num
    · rfl
    · exfalso
      have h9 : 9 ∣ (B.subgroupOf H).index * 3 ^ (n + 2) :=
        Dvd.dvd.mul_left (by
          rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
          exact pow_dvd_pow 3 (by omega)) _
      rw [h] at h9
      norm_num at h9
  rw [hn1, pow_one] at hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hn])
  refine ⟨(x : G), by rw [Subgroup.orderOf_coe, hx], ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_
  rw [hn, Nat.card_zpowers, Subgroup.orderOf_coe, hx]

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_cover : ∀ y ∈ SL3.Pl, y ^ 3 = 1 → y ≠ 1 →
    ∀ A₁ : Matrix (Fin 3) (Fin 3) (ZMod 2), IsTraceZero A₁ → ¬ SL3.IsM2 A₁ →
      ∀ a b : ZMod 2, (a = 0 ∧ b = 0) ∨ (a = A₁ 2 0 ∧ b = A₁ 2 1) ∨
        (a = (stAct y A₁) 2 0 ∧ b = (stAct y A₁) 2 1) ∨
        (a = A₁ 2 0 + (stAct y A₁) 2 0 ∧ b = A₁ 2 1 + (stAct y A₁) 2 1) := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK CFSG.LieType.BorelTits in
private theorem burnsideJ8b_irreducible {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {X : Subgroup G}
    (hX : IsSylowIn 3 X M.G2) {B : Subgroup G} (hAB : M.Agrp ≤ B) (hBR : B ≤ M.R2)
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) : B = M.Agrp ∨ B = M.R2 := by
  have hcardG2 : Nat.card M.G2 = 2 ^ 11 * 24 := M.card_G2
  obtain ⟨x, hx3, hxX⟩ := burnsideJ8b_exists_gen3 hcardG2 hX
  have hxmem : x ∈ X := by rw [← hxX]; exact Subgroup.mem_zpowers x
  have hxG2 : x ∈ M.G2 := hX.1 hxmem
  obtain ⟨hxL, hxP⟩ := mem_pullL.mp hxG2
  have hxB : x ∈ Subgroup.normalizer (B : Set G) := hXB hxmem
  set y := M.θ ⟨x, hxL⟩ with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← map_pow]
    have : (⟨x, hxL⟩ : M.L) ^ 3 = 1 := Subtype.ext (by
      simpa using orderOf_dvd_iff_pow_eq_one.mp (by rw [hx3] : orderOf x ∣ 3))
    rw [this, map_one]
  have hy1 : y ≠ 1 := by
    intro h1
    have hxS : x ∈ ruS M.L := (M.mem_S_iff_θ hxL).mpr h1
    have hd := Subgroup.orderOf_dvd_natCard (ruS M.L) hxS
    rw [hx3, M.toRuData.card_S] at hd
    norm_num at hd
  have hSnorm : x ∈ Subgroup.normalizer ((ruS M.L : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 M.L hxL
  have hWB : M.W ≤ B := M.W_le_Agrp.trans hAB
  by_cases hD : ∀ s ∈ B ⊓ ruS M.L, s ∈ M.W
  · left
    apply le_antisymm _ hAB
    intro b hb
    have hbR := hBR hb
    obtain ⟨hbL, hbP⟩ := mem_pullL.mp hbR
    obtain ⟨a, ha, haL, haθ⟩ := M.exists_Agrp_θ hbP
    have hsL : a⁻¹ * b ∈ M.L := mul_mem (inv_mem haL) hbL
    have hsS : a⁻¹ * b ∈ ruS M.L := by
      rw [M.mem_S_iff_θ hsL]
      have : (⟨a⁻¹ * b, hsL⟩ : M.L) = (⟨a, haL⟩ : M.L)⁻¹ * ⟨b, hbL⟩ := rfl
      rw [this, map_mul, map_inv, haθ, inv_mul_cancel]
    have hsB : a⁻¹ * b ∈ B := mul_mem (inv_mem (hAB ha)) hb
    have e : b = a * (a⁻¹ * b) := by group
    rw [e]
    exact M.Agrp.mul_mem ha (M.W_le_Agrp (hD _ ⟨hsB, hsS⟩))
  · right
    push Not at hD
    obtain ⟨s₁, ⟨hs₁B, hs₁S⟩, hs₁W⟩ := hD
    apply le_antisymm hBR
    rw [← burnsideJ8b_A_sup_S M]
    refine sup_le hAB ?_
    have hnm1 : ¬ SL3.IsM2 (Multiplicative.toAdd (M.χ ⟨s₁, hs₁S⟩)) := fun h => hs₁W ⟨hs₁S, h⟩
    set A₁ := Multiplicative.toAdd (M.χ ⟨s₁, hs₁S⟩) with hA₁
    have hs₂S : x * s₁ * x⁻¹ ∈ ruS M.L :=
      (Subgroup.mem_normalizer_iff.mp hSnorm s₁).mp hs₁S
    have hs₂B : x * s₁ * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hxB s₁).mp hs₁B
    have hχ₂ : Multiplicative.toAdd (M.χ ⟨x * s₁ * x⁻¹, hs₂S⟩) = stAct y A₁ := by
      have := M.χ_conj ⟨x, hxL⟩ ⟨s₁, hs₁S⟩
      simpa [hy, hA₁] using this
    have hcov := burnsideJ8b_cover y hxP hy3 hy1 A₁ (M.χ_trace _) hnm1
    have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
    have hWmem : ∀ (u : G) (hu : u ∈ ruS M.L),
        SL3.IsM2 (Multiplicative.toAdd (M.χ ⟨u, hu⟩)) → u ∈ B := fun u hu h => hWB ⟨hu, h⟩
    intro s hs
    have hc := hcov (Multiplicative.toAdd (M.χ ⟨s, hs⟩) 2 0) (Multiplicative.toAdd (M.χ ⟨s, hs⟩) 2 1)
    rcases hc with ⟨h20, h21⟩ | ⟨h20, h21⟩ | ⟨h20, h21⟩ | ⟨h20, h21⟩
    · exact hWmem s hs ⟨h20, h21⟩
    ·
      have hq : s * s₁⁻¹ ∈ ruS M.L := mul_mem hs (inv_mem hs₁S)
      have hm : SL3.IsM2 (Multiplicative.toAdd (M.χ ⟨s * s₁⁻¹, hq⟩)) := by
        have : (⟨s * s₁⁻¹, hq⟩ : ruS M.L) = ⟨s, hs⟩ * ⟨s₁, hs₁S⟩⁻¹ := rfl
        rw [this, M.toAdd_χ_mul, M.toAdd_χ_inv]
        refine ⟨?_, ?_⟩
        · simp only [Matrix.add_apply]; rw [h20]; exact h2 _
        · simp only [Matrix.add_apply]; rw [h21]; exact h2 _
      have := hWmem _ hq hm
      have e : s = (s * s₁⁻¹) * s₁ := by group
      rw [e]; exact B.mul_mem this hs₁B
    · have hq : s * (x * s₁ * x⁻¹)⁻¹ ∈ ruS M.L := mul_mem hs (inv_mem hs₂S)
      have hm : SL3.IsM2 (Multiplicative.toAdd (M.χ ⟨s * (x * s₁ * x⁻¹)⁻¹, hq⟩)) := by
        have : (⟨s * (x * s₁ * x⁻¹)⁻¹, hq⟩ : ruS M.L) = ⟨s, hs⟩ * ⟨x * s₁ * x⁻¹, hs₂S⟩⁻¹ := rfl
        rw [this, M.toAdd_χ_mul, M.toAdd_χ_inv, hχ₂]
        refine ⟨?_, ?_⟩
        · simp only [Matrix.add_apply]; rw [h20]; exact h2 _
        · simp only [Matrix.add_apply]; rw [h21]; exact h2 _
      have := hWmem _ hq hm
      have e : s = (s * (x * s₁ * x⁻¹)⁻¹) * (x * s₁ * x⁻¹) := by group
      rw [e]; exact B.mul_mem this hs₂B
    · have hq : s * (s₁ * (x * s₁ * x⁻¹))⁻¹ ∈ ruS M.L :=
        mul_mem hs (inv_mem (mul_mem hs₁S hs₂S))
      have hm : SL3.IsM2 (Multiplicative.toAdd (M.χ ⟨s * (s₁ * (x * s₁ * x⁻¹))⁻¹, hq⟩)) := by
        have : (⟨s * (s₁ * (x * s₁ * x⁻¹))⁻¹, hq⟩ : ruS M.L) =
            ⟨s, hs⟩ * (⟨s₁, hs₁S⟩ * ⟨x * s₁ * x⁻¹, hs₂S⟩)⁻¹ := rfl
        rw [this, M.toAdd_χ_mul, M.toAdd_χ_inv, M.toAdd_χ_mul, hχ₂]
        refine ⟨?_, ?_⟩
        · simp only [Matrix.add_apply]; rw [h20]
          rw [← hA₁]; exact h2 _
        · simp only [Matrix.add_apply]; rw [h21]
          rw [← hA₁]; exact h2 _
      have := hWmem _ hq hm
      have e : s = (s * (s₁ * (x * s₁ * x⁻¹))⁻¹) * (s₁ * (x * s₁ * x⁻¹)) := by group
      rw [e]; exact B.mul_mem this (B.mul_mem hs₁B hs₂B)

private theorem burnsideJ8b_isSylow3_zpowers {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : Nat.card H = 2 ^ 11 * 24) {x : G} (hx : x ∈ H) (hx3 : orderOf x = 3) :
    CFSG.ASVolI.ChIJK.IsSylowIn 3 (Subgroup.zpowers x) H := by
  have hle : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hx
  refine ⟨hle, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num), ?_⟩
  have h := Subgroup.index_mul_card ((Subgroup.zpowers x).subgroupOf H)
  rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hle, Nat.card_zpowers, hx3, hH] at h
  intro hd
  have h' : ((Subgroup.zpowers x).subgroupOf H).index = 2 ^ 11 * 8 := by omega
  rw [h'] at hd
  norm_num at hd

@[expose] def burnsideJ8b_M3 (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j =>
    (![![1, 0, 1], ![0, 1, 1]] : Fin 2 → Fin 3 → ZMod 2) j (σ⁻¹ (Fin.castSucc i))

@[expose] def burnsideJ8b_s3Hom : Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun σ := ⟨burnsideJ8b_M3 σ, by revert σ; decide⟩
  map_one' := Subtype.ext (by decide)
  map_mul' σ τ := Subtype.ext (by revert σ τ; decide)

private theorem burnsideJ8b_nonempty_s3_sl2 :
    Nonempty (Equiv.Perm (Fin 3) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  refine ⟨MulEquiv.ofBijective burnsideJ8b_s3Hom ⟨fun σ τ h => ?_, fun A => ?_⟩⟩
  · have key : ∀ σ τ : Equiv.Perm (Fin 3), burnsideJ8b_M3 σ = burnsideJ8b_M3 τ → σ = τ := by
      decide
    exact key σ τ (congrArg Subtype.val h)
  · have key : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        ∃ σ : Equiv.Perm (Fin 3), burnsideJ8b_M3 σ = (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
      decide
    obtain ⟨σ, hσ⟩ := key A
    exact ⟨σ, Subtype.ext hσ⟩

@[expose] noncomputable def burnsideJ8b_conjEquiv {G : Type*} [Group G] (F : Subgroup G) (t : G) :
    ↥F ≃* ↥(CFSG.conjugate F t) :=
  (MulAut.conj t⁻¹).subgroupMap F

private theorem burnsideJ8b_conjEquiv_apply {G : Type*} [Group G] (F : Subgroup G) (t : G) (x :
    ↥F) :
    ((burnsideJ8b_conjEquiv F t x : ↥(CFSG.conjugate F t)) : G) = t⁻¹ * x * t := by
  show (((MulAut.conj t⁻¹).subgroupMap F x : ↥(F.map (MulAut.conj t⁻¹).toMonoidHom)) : G) = _
  rw [MulEquiv.coe_subgroupMap_apply]
  simp [MulAut.conj_apply]

private theorem burnsideJ8b_oTwoQuot_conj {G : Type*} [Group G] (F : Subgroup G) (t : G) {K : Type*}
    [Group K] (h : Nonempty (↥F ⧸ CFSG.pCore 2 ↥F ≃* K)) :
    Nonempty (↥(CFSG.conjugate F t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate F t) ≃* K) := by
  obtain ⟨f⟩ := h
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥(CFSG.conjugate F t)) (CFSG.pCore 2 ↥F)
    (burnsideJ8b_conjEquiv F t).symm
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (burnsideJ8b_conjEquiv F t).symm)).trans f⟩

private theorem burnsideJ8b_quot_conj {G : Type*} [Group G] (F A A' : Subgroup G) (t : G)
    (hA : CFSG.conjugate A t = A') {K : Type*} [Group K] [(A.subgroupOf F).Normal]
    [(A'.subgroupOf (CFSG.conjugate F t)).Normal]
    (h : Nonempty (↥F ⧸ A.subgroupOf F ≃* K)) :
    Nonempty (↥(CFSG.conjugate F t) ⧸ A'.subgroupOf (CFSG.conjugate F t) ≃* K) := by
  subst hA
  obtain ⟨f⟩ := h
  refine ⟨(QuotientGroup.congr ((CFSG.conjugate A t).subgroupOf (CFSG.conjugate F t))
    (A.subgroupOf F) (burnsideJ8b_conjEquiv F t).symm ?_).trans f⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, burnsideJ8b_mem_conjugate] at hy
    rw [Subgroup.mem_subgroupOf]
    have hy' : ((burnsideJ8b_conjEquiv F t).symm y : G) = t * y * t⁻¹ := by
      have := burnsideJ8b_conjEquiv_apply F t ((burnsideJ8b_conjEquiv F t).symm y)
      rw [MulEquiv.apply_symm_apply] at this
      have e : (y : G) = t⁻¹ * ((burnsideJ8b_conjEquiv F t).symm y : G) * t := this
      rw [e]; group
    show (((burnsideJ8b_conjEquiv F t).symm y : ↥F) : G) ∈ A
    rw [hy']; exact hy
  · intro hx
    refine ⟨burnsideJ8b_conjEquiv F t x, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf, burnsideJ8b_mem_conjugate, burnsideJ8b_conjEquiv_apply]
    have : t * (t⁻¹ * (x : G) * t) * t⁻¹ = x := by group
    rw [this]
    exact Subgroup.mem_subgroupOf.mp hx

end MLevel

section TFixes

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_conj_T_fixes {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {t : G}
    (ht : t ∈ (M.T : Subgroup G)) :
    CFSG.conjugate M.W t = M.W ∧ CFSG.conjugate M.R2 t = M.R2 ∧
      CFSG.conjugate M.Agrp t = M.Agrp ∧ CFSG.conjugate (ruS M.L) t = ruS M.L ∧
      CFSG.conjugate (M.T : Subgroup G) t = (M.T : Subgroup G) ∧
      CFSG.conjugate M.G2 t = M.G2 := by
  have htG2 : t ∈ M.G2 := M.T_le_G2 ht
  have htL : t ∈ M.L := M.toRuData.T_le_L ht
  refine ⟨burnsideJ8b_conjugate_eq_self (mem_normalizer_of_conj_mem fun x hx =>
      M.conj_mem_W htG2 hx), burnsideJ8b_conjugate_eq_self (mem_normalizer_of_conj_mem fun x hx =>
      M.conj_mem_R2 htG2 hx), burnsideJ8b_conjugate_eq_self (mem_normalizer_of_conj_mem fun x hx =>
      M.conj_mem_Agrp htG2 hx), burnsideJ8b_conjugate_eq_self
      (le_normalizer_pCoreOf 2 M.L htL), burnsideJ8b_conjugate_eq_self
      (Subgroup.le_normalizer ht), burnsideJ8b_conjugate_eq_self ?_⟩
  exact mem_normalizer_of_conj_mem fun x hx => by
    obtain ⟨hxL, hxP⟩ := mem_pullL.mp hx
    refine mem_pullL.mpr ⟨mul_mem (mul_mem htL hxL) (inv_mem htL), ?_⟩
    have e : (⟨t * x * t⁻¹, mul_mem (mul_mem htL hxL) (inv_mem htL)⟩ : M.L) =
        ⟨t, htL⟩ * ⟨x, hxL⟩ * ⟨t, htL⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (SL3.P0_le_Pl (M.θ_mem_P0 ht)) hxP) (inv_mem (SL3.P0_le_Pl (M.θ_mem_P0 ht)))

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
private theorem burnsideJ8b_Q5Ru_eq {G : Type} [Group G]
    [Finite G] (M : RuDataM G) {B5 : Subgroup G}
    {t : G} (ht : t ∈ (M.T : Subgroup G))
    (hB : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t) :
    Q5Ru (M.T : Subgroup G) B5 = CFSG.conjugate (M.Q5 M.b5el_mem_H) t := by
  have hZ : ZRu (M.T : Subgroup G) = ruZ M.T := RuType.BridgeTwo.centerOf_eq _
  have hH : HRu (M.T : Subgroup G) = ruH M.T := by unfold HRu; rw [hZ]
  have hQ : QRu (M.T : Subgroup G) = ruQ M.T := by unfold QRu; rw [hH]
  have hU : URu (ruV M.L) (M.T : Subgroup G) = ruU M.L M.T := by
    unfold URu; rw [hH]; exact RuType.BridgeTwo.conjClosure_eq _ _
  have hb'H : t⁻¹ * M.b5el * t ∈ ruH M.T := by
    have htH : t ∈ ruH M.T := M.toRuData.T_le_H ht
    exact mul_mem (mul_mem (inv_mem htH) M.b5el_mem_H) htH
  have hb'5 : orderOf (t⁻¹ * M.b5el * t) = 5 := by
    have := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective M.b5el
    rw [M.orderOf_b5el] at this
    simpa [MulAut.conj_apply] using this
  have hB' : B5 = Subgroup.zpowers (t⁻¹ * M.b5el * t) := by
    rw [hB, burnsideJ8b_conjugate_zpowers]
  have hQ5 : Q5Ru (M.T : Subgroup G) B5 = M.Q5 hb'H := by
    unfold Q5Ru; rw [hQ, hB']; exact burnsideJ8b_Q5_eq M hb'H hb'5
  have hUle : ruU M.L M.T ≤ Q5Ru (M.T : Subgroup G) B5 := by
    rw [hQ5]; exact M.U_le_Q5 hb'H
  have := RuChoice.Q5 M ht hB
  rw [hU, sup_eq_left.mpr hUle] at this
  exact this

end TFixes

section J45Lemmas

open CFSG.LieType.BorelTits in
private theorem burnsideJ8b_pCoreOf_conjugate {G : Type} [Group G] [Finite G] (X : Subgroup G)
    (t : G) :
    pCoreOf 2 (CFSG.conjugate X t) = CFSG.conjugate (pCoreOf 2 X) t := by
  have key : ∀ (X : Subgroup G) (t : G),
      CFSG.conjugate (pCoreOf 2 X) t ≤ pCoreOf 2 (CFSG.conjugate X t) := by
    intro X t
    refine le_pCoreOf_of_le_normalizer 2 ((burnsideJ8b_conjugate_le_iff t).mpr
      (pCoreOf_le 2 X)) ?_ ?_
    · rw [burnsideJ8b_normalizer_conjugate, burnsideJ8b_conjugate_le_iff]
      exact le_normalizer_pCoreOf 2 X
    · obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X).exists_card_eq
      exact IsPGroup.of_card (n := k) (by rw [burnsideJ8b_card_conjugate]; exact hk)
  apply le_antisymm _ (key X t)
  have h := key (CFSG.conjugate X t) t⁻¹
  rw [burnsideJ8b_conjugate_conjugate, mul_inv_cancel, burnsideJ8b_conjugate_one] at h
  rw [← burnsideJ8b_conjugate_le_iff t⁻¹, burnsideJ8b_conjugate_conjugate, mul_inv_cancel,
    burnsideJ8b_conjugate_one]
  exact h

@[expose] def burnsideJ8b_amIsoSymm {α β : CFSG.Quasithin.RankTwoAmalgam.{0}} (e : α.Iso β) :
    β.Iso α where
  φ1 := e.φ1.symm
  φ12 := e.φ12.symm
  φ2 := e.φ2.symm
  comm1 g := by
    apply e.φ1.injective
    rw [MulEquiv.apply_symm_apply, ← e.comm1, MulEquiv.apply_symm_apply]
  comm2 g := by
    apply e.φ2.injective
    rw [MulEquiv.apply_symm_apply, ← e.comm2, MulEquiv.apply_symm_apply]

@[expose] def burnsideJ8b_amIsoTrans {α β γ : CFSG.Quasithin.RankTwoAmalgam.{0}} (e : α.Iso β)
    (e' : β.Iso γ) : α.Iso γ where
  φ1 := e.φ1.trans e'.φ1
  φ12 := e.φ12.trans e'.φ12
  φ2 := e.φ2.trans e'.φ2
  comm1 g := by
    simp only [MulEquiv.trans_apply]
    rw [e'.comm1, e.comm1]
  comm2 g := by
    simp only [MulEquiv.trans_apply]
    rw [e'.comm2, e.comm2]

@[expose] def burnsideJ8b_ofSubgroupsMapIso {X X' : Type} [Group X] [Group X'] (f : X ≃* X')
    (A B : Subgroup X) :
    (CFSG.Quasithin.RankTwoAmalgam.ofSubgroups A B).Iso
      (CFSG.Quasithin.RankTwoAmalgam.ofSubgroups (A.map (f : X →* X')) (B.map (f : X →* X'))) where
  φ1 := f.subgroupMap A
  φ12 := (f.subgroupMap (A ⊓ B)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_inf_eq A B (f : X →* X') f.injective))
  φ2 := f.subgroupMap B
  comm1 _ := rfl
  comm2 _ := rfl

private theorem burnsideJ8b_isYAmalgam_conjugate {G Y : Type} [Group G] [Group Y] {T' : Subgroup Y}
    (F1 F2 : Subgroup G) (y : G)
    (h : CFSG.Quasithin.IsYAmalgam (CFSG.Quasithin.RankTwoAmalgam.ofSubgroups F1 F2) T') :
    CFSG.Quasithin.IsYAmalgam (CFSG.Quasithin.RankTwoAmalgam.ofSubgroups
      (CFSG.conjugate F1 y) (CFSG.conjugate F2 y)) T' := by
  obtain ⟨M₁, M₂, hpair, ⟨iso⟩⟩ := h
  exact ⟨M₁, M₂, hpair, ⟨burnsideJ8b_amIsoTrans
    (burnsideJ8b_amIsoSymm (burnsideJ8b_ofSubgroupsMapIso (MulAut.conj y⁻¹) F1 F2)) iso⟩⟩

private theorem burnsideJ8b_exists_reeTitsModel :
    ∃ (Y0 : Type) (_ : Group Y0), CFSG.Blueprint.ReeTitsModel Y0 .Tits 2 1 := by
  refine ⟨CFSG.Blueprint.DerivedCentralQuotient
    (CFSG.Blueprint.reeFixedGroup CFSG.Blueprint.Chevalley.Tag.F4 (ZMod 2)
      CFSG.Blueprint.reeF4Perm
      fun i => if i ∈ CFSG.Blueprint.reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)),
    inferInstance, ?_⟩
  refine ⟨⟨Nat.prime_two, le_refl _, rfl, rfl, rfl⟩, 0, rfl, ?_⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩

section

private theorem burnsideJ8b_isTwoF4TwoGroup_of_isTwistedF4Over {Y : Type} [Group Y]
    (h : CFSG.Quasithin.IsTwistedF4Over 1 Y) : CFSG.ASVolI.ChIJK.IsTwoF4TwoGroup Y := by
  obtain ⟨Y0, _, hY0⟩ := burnsideJ8b_exists_reeTitsModel
  obtain ⟨e2⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y0 2 1 hY0
  rcases h with ⟨-, ⟨e⟩⟩ | ⟨h3, -, -⟩
  · exact ⟨Y0, inferInstance, hY0, ⟨e.trans ((MulAut.congr
      CFSG.Quasithin.quasithinTitsEquivD).trans (MulAut.congr e2.symm))⟩⟩
  · omega

end

section J45M

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_exists_TF_θ {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    ∀ p ∈ SL3.P0, ∃ z ∈ M.TF, ∃ hz : z ∈ M.L, M.θ ⟨z, hz⟩ = p := by
  intro p hp
  obtain ⟨_, hr, _, hs, hrs⟩ := SL3.P0_eq_R0_mul_R2m _ hp
  obtain ⟨q, hq, hqL, hqθ⟩ := M.exists_Q5_θ M.b5el_mem_H M.orderOf_b5el hr
  obtain ⟨a, ha, haL, haθ⟩ := M.exists_Agrp_θ hs
  refine ⟨q * a, ?_, mul_mem hqL haL, ?_⟩
  · exact M.TF.mul_mem (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left ha)
  · have : (⟨q * a, mul_mem hqL haL⟩ : M.L) = ⟨q, hqL⟩ * ⟨a, haL⟩ := rfl
    rw [this, map_mul, hqθ, haθ, hrs]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ8b_F2_sup_S {G : Type} [Group G]
    [Finite G] (M : RuDataM G) :
    M.F2 ⊔ ruS M.L = M.G2 := by
  apply le_antisymm (sup_le M.F2_le_G2 (M.S_le_R2.trans M.R2_le_G2))
  intro g hg
  obtain ⟨hgL, hgP⟩ := mem_pullL.mp hg
  obtain ⟨t0, ht0, hk⟩ := SL3.Pl_eq _ hgP
  have key : ∀ k : ℕ, M.θ ⟨g, hgL⟩ = t0 * SL3.x0 ^ k → g ∈ M.F2 ⊔ ruS M.L := by
    intro k hk
    obtain ⟨z, hz, hzL, hzθ⟩ := burnsideJ8b_exists_TF_θ M t0 ht0
    set w := z * M.x2el ^ k with hw
    have hwF : w ∈ M.F2 := mul_mem (M.TF_le_F2 hz) (pow_mem M.x2el_mem_F2 k)
    have hwL : w ∈ M.L := mul_mem hzL (pow_mem M.x2el_mem_L k)
    have hS : w⁻¹ * g ∈ ruS M.L := by
      have hL : w⁻¹ * g ∈ M.L := mul_mem (inv_mem hwL) hgL
      rw [M.mem_S_iff_θ hL]
      have : (⟨w⁻¹ * g, hL⟩ : M.L) = (⟨z, hzL⟩ * ⟨M.x2el, M.x2el_mem_L⟩ ^ k)⁻¹ * ⟨g, hgL⟩ := rfl
      rw [this, map_mul, map_inv, map_mul, map_pow, hzθ, M.θ_x2el, hk, inv_mul_cancel]
    have e : g = w * (w⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwF) (Subgroup.mem_sup_right hS)
  rcases hk with hk | hk | hk
  · exact key 0 (by rw [hk, pow_zero, mul_one])
  · exact key 1 (by rw [hk, pow_one])
  · exact key 2 hk

end J45M

section J45Main

open CFSG.Quasithin.RuType in
def burnsideJ8b_chiAdd {G : Type} [Group G] (M : RuDataM G) (X : Subgroup G) :
    AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) where
  carrier := {A | ∃ x ∈ X, ∃ hx : x ∈ ruS M.L, Multiplicative.toAdd (M.χ ⟨x, hx⟩) = A}
  zero_mem' := ⟨1, X.one_mem, (ruS M.L).one_mem, by
    have : (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 := rfl
    rw [this, map_one, toAdd_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, haS, rfl⟩ ⟨b, hb, hbS, rfl⟩
    refine ⟨a * b, X.mul_mem ha hb, mul_mem haS hbS, ?_⟩
    have : (⟨a * b, mul_mem haS hbS⟩ : ruS M.L) = ⟨a, haS⟩ * ⟨b, hbS⟩ := rfl
    rw [this, M.toAdd_χ_mul]
  neg_mem' := by
    rintro _ ⟨a, ha, haS, rfl⟩
    refine ⟨a⁻¹, X.inv_mem ha, inv_mem haS, ?_⟩
    have : (⟨a⁻¹, inv_mem haS⟩ : ruS M.L) = (⟨a, haS⟩ : ruS M.L)⁻¹ := rfl
    rw [this, M.toAdd_χ_inv]
    ext i j
    simp only [Matrix.neg_apply]
    have h2 : ∀ x : ZMod 2, x = -x := by decide
    exact h2 _

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_mem_of_chi {G : Type} [Group G] (M : RuDataM G) {X : Subgroup G}
    (hVX : ruV M.L ≤ X) {x : G} (hx : x ∈ ruS M.L)
    (h : Multiplicative.toAdd (M.χ ⟨x, hx⟩) ∈ burnsideJ8b_chiAdd M X) : x ∈ X := by
  obtain ⟨y, hyX, hyS, hy⟩ := h
  have hk : (⟨y, hyS⟩ : ruS M.L)⁻¹ * ⟨x, hx⟩ ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Multiplicative.toAdd.injective hy]
    exact inv_mul_cancel _
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact X.mul_mem hyX (hVX hk)

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_W_le_of_chi {G : Type} [Group G] [Finite G] (M : RuDataM G) {X :
    Subgroup G}
    (hVX : ruV M.L ≤ X)
    (h : ∀ A, SL3.IsM2 A → IsTraceZero A → A ∈ burnsideJ8b_chiAdd M X) : M.W ≤ X := by
  rintro _ ⟨hx, hxM⟩
  exact burnsideJ8b_mem_of_chi M hVX hx (h _ hxM (M.χ_trace _))

def burnsideJ8b_inSpan :
    List (Matrix (Fin 3) (Fin 3) (ZMod 2)) → Matrix (Fin 3) (Fin 3) (ZMod 2) → Bool
  | [], A => decide (A = 0)
  | g :: gs, A => burnsideJ8b_inSpan gs A || burnsideJ8b_inSpan gs (A + g)

private theorem burnsideJ8b_mat_add_self : ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g + g = 0 := by
  decide +kernel

private theorem burnsideJ8b_mem_of_inSpan (P : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    ∀ («gens» : List (Matrix (Fin 3) (Fin 3) (ZMod 2))), (∀ g ∈ «gens», g ∈ P) →
      ∀ A, burnsideJ8b_inSpan «gens» A = true → A ∈ P := by
  intro «gens»
  induction «gens» with
  | nil =>
    intro _ A h
    simp only [burnsideJ8b_inSpan, decide_eq_true_eq] at h
    rw [h]
    exact P.zero_mem
  | cons g gs ih =>
    intro hg A h
    simp only [burnsideJ8b_inSpan, Bool.or_eq_true] at h
    have hgs : ∀ x ∈ gs, x ∈ P := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    rcases h with h | h
    · exact ih hgs A h
    · have h1 := ih hgs (A + g) h
      have hgP := hg g List.mem_cons_self
      have : A = (A + g) + g := by
        rw [add_assoc, burnsideJ8b_mat_add_self, add_zero]
      rw [this]
      exact P.add_mem h1 hgP

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_center_sigma :
    ∀ g : SigmaL2F4, (∀ s : SigmaL2F4, s * g = g * s) → g = 1 := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_fix_sigma :
    ∀ w : Fin 2 → CFSG.Quasithin.RuType.F4, (∀ g : SigmaL2F4, sigmaAct g w = w) → w = 0 := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_Q0_set {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    {h : G | h ∈ ruH M.T ∧ ∀ x ∈ ruH M.T, h⁻¹ * x⁻¹ * h * x ∈ ruU M.L M.T} = (M.Q0 : Set G) := by
  ext h
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨hH, hc⟩
    have hφ1 : M.φ ⟨h, hH⟩ = 1 := by
      apply burnsideJ8b_center_sigma
      intro s
      obtain ⟨x, hx⟩ := M.φ_surj s
      have hmem : h⁻¹ * (x : G)⁻¹ * h * x ∈ ruU M.L M.T := hc x x.2
      have hk : (⟨h⁻¹ * (x : G)⁻¹ * h * x, M.U_le_H hmem⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact M.U_le_Q hmem
      have e : (⟨h⁻¹ * (x : G)⁻¹ * h * x, M.U_le_H hmem⟩ : ruH M.T) =
          (⟨h, hH⟩ : ruH M.T)⁻¹ * x⁻¹ * ⟨h, hH⟩ * x := rfl
      rw [MonoidHom.mem_ker, e, map_mul, map_mul, map_mul, map_inv, map_inv, hx] at hk
      calc s * M.φ ⟨h, hH⟩ = s * M.φ ⟨h, hH⟩ * ((M.φ ⟨h, hH⟩)⁻¹ * s⁻¹ * M.φ ⟨h, hH⟩ * s) := by
            rw [hk, mul_one]
        _ = M.φ ⟨h, hH⟩ * s := by group
    have hQ : h ∈ ruQ M.T := by
      have : (⟨h, hH⟩ : ruH M.T) ∈ M.φ.ker := hφ1
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    have hfix : ∀ (k : G) (hk : k ∈ ruH M.T),
        M.actQ ⟨k, hk⟩ ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) = ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) := by
      intro k hk
      rw [M.actQ_mk, M.mk_eq_mk_iff]
      have h1 := inv_mem (hc k⁻¹ (inv_mem hk))
      have e : (k * h * k⁻¹)⁻¹ * h = (h⁻¹ * k⁻¹⁻¹ * h * k⁻¹)⁻¹ := by group
      show (k * h * k⁻¹)⁻¹ * h ∈ ruU M.L M.T
      rw [e]
      exact h1
    have hfixσ : ∀ g : SigmaL2F4, sigmaAct g (Multiplicative.toAdd (M.ψQbar ((⟨h, hQ⟩ : ruQ M.T) :
        M.Qbar))) = Multiplicative.toAdd (M.ψQbar ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar)) := by
      intro g
      obtain ⟨k, rfl⟩ := M.φ_surj g
      rw [← M.ψQbar_actQ, hfix k k.2]
    have hψ : M.ψQbar ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) = 1 :=
      Multiplicative.toAdd.injective (burnsideJ8b_fix_sigma _ hfixσ)
    have hHCbar : ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) ∈ M.HCbar := by
      rw [← M.ker_ψQbar]
      exact hψ
    refine M.mem_Q0.mpr ⟨hQ, hHCbar, ?_⟩
    show M.dQ ⟨M.nel, M.nel_mem_H⟩ ((⟨h, hQ⟩ : ruQ M.T) : M.Qbar) = 1
    rw [M.dQ_apply, hfix M.nel M.nel_mem_H, mul_inv_cancel]
  · intro hx
    obtain ⟨hxQ, hx0⟩ := M.mem_Q0.mp hx
    have hxH : h ∈ ruH M.T := (Subgroup.mem_inf.mp (M.Q0_le_HC hx)).1
    refine ⟨hxH, fun k hk => ?_⟩
    have hfix : ∀ (k : G) (hk : k ∈ ruH M.T),
        M.actQ ⟨k, hk⟩ ((⟨h, hxQ⟩ : ruQ M.T) : M.Qbar) = ((⟨h, hxQ⟩ : ruQ M.T) : M.Qbar) := by
      intro k hk
      by_cases hK : k ∈ M.K
      · exact M.actQ_HCbar_of_mem_K hK hx0.1
      · rw [M.actQ_HCbar_of_not_mem_K hk hK hx0.1]
        have h2 : M.dQ ⟨M.nel, M.nel_mem_H⟩ ((⟨h, hxQ⟩ : ruQ M.T) : M.Qbar) = 1 := hx0.2
        rwa [M.dQ_apply, mul_inv_eq_one] at h2
    have := hfix k⁻¹ (inv_mem hk)
    rw [M.actQ_mk, M.mk_eq_mk_iff] at this
    have e : h⁻¹ * k⁻¹ * h * k = (((k⁻¹ * h * k⁻¹⁻¹)⁻¹ * h))⁻¹ := by group
    rw [e]
    exact inv_mem this

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_Q0_closure {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Subgroup.closure {h : G | h ∈ ruH M.T ∧ ∀ x ∈ ruH M.T, h⁻¹ * x⁻¹ * h * x ∈ ruU M.L M.T} =
      M.Q0 := by
  rw [burnsideJ8b_Q0_set, Subgroup.closure_eq]

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_conj_mem_W0 {G : Type} [Group G] (M : RuDataM G) {L2 : Subgroup G}
    {l u : G} (hl : l ∈ L2) (hu : u ∈ ruU M.L M.T) :
    l * u * l⁻¹ ∈ ChIJK.conjClosure (ruU M.L M.T) L2 := by
  have h1 : l * u * l⁻¹ ∈ CFSG.conjugate (ruU M.L M.T) l⁻¹ := by
    refine ⟨u, hu, ?_⟩
    simp [MulAut.conj_apply]
  exact (le_iSup₂ (f := fun y (_ : y ∈ L2) => CFSG.conjugate (ruU M.L M.T) y) l⁻¹
    (inv_mem hl)) h1

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_W0_le_W {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 :
    Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ≤ M.W := by
  refine iSup₂_le fun y hy => ?_
  rintro _ ⟨_, hu, rfl⟩
  have hyG : y ∈ M.G2 := by
    rw [RuChoice.L2Ru_eq M hV2] at hy
    exact RuChoice.twoResidual_le _ hy
  exact M.conj_mem_W (inv_mem hyG) (M.U_le_W hu)

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_c_mem_Q0 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ M.Q0 := by
  set t := ((⟨M.t1el, M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)⟩ : ruQ M.T) : M.Qbar)
  set x0 := M.dQ ⟨M.nel, M.nel_mem_H⟩ t
  have htC : t ∈ M.HCbar := M.t1bar_mem_HCbar
  have hx0C : x0 ∈ M.HCbar := by
    show M.actQ _ t * t⁻¹ ∈ M.HCbar
    exact mul_mem (M.actQ_mem_HCbar _ htC) (inv_mem htC)
  have hx0 : x0 ∈ M.Q0bar := by
    refine ⟨hx0C, ?_⟩
    show M.dQ ⟨M.nel, M.nel_mem_H⟩ x0 = 1
    rw [M.dQ_apply, mul_inv_eq_one]
    show M.actQ _ (M.actQ _ t * t⁻¹) = M.actQ _ t * t⁻¹
    rw [map_mul, map_inv, M.actQ_nel_nel htC]
    have hsq : ∀ y : M.Qbar, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (M.Qbar_sq y)
    rw [hsq t, hsq (M.actQ _ t), M.Qbar_comm]
  have hcQ : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ ruQ M.T :=
    mul_mem (M.conj_mem_Q M.nel_mem_H (M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)))
      (inv_mem (M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)))
  exact M.mem_Q0.mpr ⟨hcQ, hx0⟩

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_chi_c {G : Type} [Group G] [Finite G] (M : RuDataM G)
    (hc : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ ruS M.L) :
    Multiplicative.toAdd (M.χ ⟨(M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹, hc⟩) =
      !![0, 0, 0; 0, 1, 0; 0, 0, 1] := by
  have ht1S := M.t1el_mem_S
  have hnt : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L M.nel.2) _).mp ht1S
  rw [show (⟨(M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹, hc⟩ : ruS M.L) =
    ⟨_, hnt⟩ * (⟨M.t1el, ht1S⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv]
  have h := M.χ_conj M.nel ⟨M.t1el, ht1S⟩
  simp only at h
  rw [h, M.θ_nel, M.χ_t1el, SL3.n0_b0mat]
  decide +kernel

@[expose] def burnsideJ8b_b3mat : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def burnsideJ8b_pairsW :
    List (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [(1, !![0, 1, 0; 0, 0, 0; 0, 0, 0]), (1, !![0, 0, 1; 0, 0, 0; 0, 0, 0]),
   (RuChoice.a3mat, !![0, 1, 0; 0, 0, 0; 0, 0, 0]),
   (RuChoice.a3mat, !![0, 0, 1; 0, 0, 0; 0, 0, 0]),
   (burnsideJ8b_b3mat, !![0, 1, 0; 0, 0, 0; 0, 0, 0])]

@[expose] def burnsideJ8b_gensW : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0],
   !![0, 0, 0; 0, 0, 1; 0, 0, 0], !![1, 1, 0; 1, 1, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 1]]

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_gensW_spec : ∀ g ∈ burnsideJ8b_gensW, g = !![0, 0, 0; 0, 1, 0; 0,
    0, 1] ∨
    ∃ p ∈ burnsideJ8b_pairsW, p.1 ∈ SL3.Pl ∧ p.1 ^ 3 = 1 ∧ SL3.IsRow0 p.2 ∧ stAct p.1 p.2 = g := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_span_W : ∀ A, SL3.IsM2 A → IsTraceZero A →
    burnsideJ8b_inSpan burnsideJ8b_gensW A = true := by
  decide +kernel

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_stAct_mem_chiAdd {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {V2 : Subgroup G} (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) {X : Subgroup G}
    (hX : ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ≤ X)
    {a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (ha : a ∈ SL3.Pl) (ha3 : a ^ 3 = 1)
    {E : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hE : SL3.IsRow0 E) :
    stAct a E ∈ burnsideJ8b_chiAdd M X := by
  obtain ⟨l, hlL, hl2, hθ, -⟩ := RuChoice.exists_L2_lift3 M ha ha3
  have hl2' : l ∈ ChIJK.L2Ru M.L V2 := by
    rw [RuChoice.L2Ru_eq M hV2]
    exact hl2
  obtain ⟨s, hs⟩ := M.χ_surj E (SL3.row0_trace E hE)
  have hsU : (s : G) ∈ ruU M.L M.T := by
    rw [M.mem_U_iff s.2, hs, toAdd_ofAdd]
    exact hE
  have hlS : l ∈ Subgroup.normalizer (ruS M.L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L hlL
  have hy : l * (s : G) * l⁻¹ ∈ ruS M.L := (Subgroup.mem_normalizer_iff.mp hlS _).mp s.2
  refine ⟨l * (s : G) * l⁻¹, hX (burnsideJ8b_conj_mem_W0 M hl2' hsU), hy, ?_⟩
  have h1 := M.χ_conj ⟨l, hlL⟩ s
  simp only at h1
  rw [h1, hθ, hs, toAdd_ofAdd]

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_W_le_W0Q0 {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 :
    Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    M.W ≤ ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ⊔ M.Q0 := by
  have hW0 : ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ≤
      ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ⊔ M.Q0 := le_sup_left
  have hUW0 : ruU M.L M.T ≤ ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) := by
    intro u hu
    have := burnsideJ8b_conj_mem_W0 M (L2 := ChIJK.L2Ru M.L V2) (l := 1) (u := u) (one_mem _) hu
    simpa using this
  have hVX : ruV M.L ≤ ChIJK.conjClosure (ruU M.L M.T) (ChIJK.L2Ru M.L V2) ⊔ M.Q0 :=
    (M.V_le_U.trans hUW0).trans hW0
  refine burnsideJ8b_W_le_of_chi M hVX fun A hA hAt => ?_
  refine burnsideJ8b_mem_of_inSpan _ burnsideJ8b_gensW ?_ A (burnsideJ8b_span_W A hA hAt)
  intro g hg
  rcases burnsideJ8b_gensW_spec g hg with rfl | ⟨p, -, hp1, hp3, hp4, rfl⟩
  · have hcQ := burnsideJ8b_c_mem_Q0 M
    have hcS : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ ruS M.L := by
      have hnt : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ ∈ ruS M.L :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L M.nel.2) _).mp M.t1el_mem_S
      exact mul_mem hnt (inv_mem M.t1el_mem_S)
    exact ⟨_, Subgroup.mem_sup_right hcQ, hcS, burnsideJ8b_chi_c M hcS⟩
  · exact burnsideJ8b_stAct_mem_chiAdd M hV2 hW0 hp1 hp3 hp4

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_Q0Ru_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ChIJK.Q0Ru (ruV M.L) (M.T : Subgroup G) = M.Q0 := by
  rw [ChIJK.Q0Ru, RuChoice.HRu_eq M, RuChoice.URu_eq M, burnsideJ8b_Q0_closure]

open CFSG.Quasithin.RuType in
private theorem burnsideJ8b_WRu_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) {V2 : Subgroup G}
    (hV2 : ChIJK.IsV2 (ruV M.L) (M.T : Subgroup G) V2) :
    ChIJK.WRu M.L (ruV M.L) V2 (M.T : Subgroup G) = M.W := by
  rw [ChIJK.WRu, ChIJK.W0Ru, RuChoice.URu_eq M, burnsideJ8b_Q0Ru_eq M]
  exact le_antisymm (sup_le (burnsideJ8b_W0_le_W M hV2) M.Q0_le_W) (burnsideJ8b_W_le_W0Q0 M hV2)

end J45Main

end J45Lemmas

end BurnsideJ8b

section

open scoped commutatorElement in
open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem as_J_4_4 : J_4_4 := by
  intro G _ _ _ V T h V2 hV2 g hg hgH v hv hvQ B5 hB5 hinv X hX
  obtain ⟨M, hML, hMT⟩ := RuChoice.exists_M h
  subst hML
  subst hMT
  have hV : V = ruV M.L := h.V_eq_ruV
  subst hV
  obtain ⟨hG2, hR2, hS2⟩ := RuChoice.frame M hV2
  obtain ⟨t, ht, hBt⟩ := RuChoice.B5 M hV2 hg hgH hv hvQ hB5 hinv
  obtain ⟨hCW, hCR, hCA, hCS, hCT, _⟩ := burnsideJ8b_conj_T_fixes M ht
  have hQ5ex := burnsideJ8b_Q5Ru_eq M ht hBt
  have htG2 : t ∈ M.G2 := M.T_le_G2 ht
  have hWn : ∀ g ∈ M.G2, ∀ w ∈ M.W, g * w * g⁻¹ ∈ M.W := fun g hg w hw => M.conj_mem_W hg hw
  have hWn' : ∀ g ∈ M.G2, ∀ w ∈ M.W, g⁻¹ * w * g ∈ M.W := fun g hg w hw => by
    have := M.conj_mem_W (inv_mem hg) hw
    simpa using this
  set a : G := t⁻¹ * M.ael * t with ha_def
  have hza : Subgroup.zpowers a = CFSG.conjugate (Subgroup.zpowers M.ael) t := by
    rw [burnsideJ8b_conjugate_zpowers]
  have hAC : IsAChoice M.L (ruV M.L) (M.T : Subgroup G) V2 B5 a := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hS2, hR2, hQ5ex, hza]
      have e1 : (CFSG.conjugate (M.Q5 M.b5el_mem_H) t ⊔ M.W) ⊓ M.R2 =
          CFSG.conjugate ((M.Q5 M.b5el_mem_H ⊔ M.W) ⊓ M.R2) t := by
        rw [burnsideJ8b_conjugate_inf, burnsideJ8b_conjugate_sup, hCW, hCR]
      rw [e1, burnsideJ8b_Q5W_inf_R2, burnsideJ8b_conjugate_sup, hCW]
    · rw [hS2]
      intro haW
      have h1 : M.ael ∈ M.W := by
        have := hWn t htG2 _ haW
        have e : t * a * t⁻¹ = M.ael := by simp only [ha_def]; group
        rwa [e] at this
      exact M.ael_not_mem_S (M.W_le_S h1)
    · rw [hS2]
      have e : a ^ 2 = t⁻¹ * M.ael ^ 2 * t := by simp only [ha_def, pow_two]; group
      rw [e]
      have := hWn' t htG2 _ M.ael_sq_mem_W
      exact this
    · rw [hS2]
      intro t' ht'
      have key := M.comm_ael_T_mem_W (t := t * t'⁻¹ * t⁻¹)
        (M.T.mul_mem (M.T.mul_mem ht (M.T.inv_mem ht')) (M.T.inv_mem ht))
      have hael : M.ael ∈ M.G2 := M.R2_le_G2 M.ael_mem_R2
      have h2 := hWn' M.ael hael _ key
      have h3 := hWn' t htG2 _ h2
      have e : t⁻¹ * (M.ael⁻¹ * (t * t'⁻¹ * t⁻¹ * M.ael * (t * t'⁻¹ * t⁻¹)⁻¹ * M.ael⁻¹) * M.ael) * t =
          a⁻¹ * t'⁻¹ * a * t' := by simp only [ha_def]; group
      rw [← e]; exact h3
  have hARu := RuChoice.A M hV2 ht hBt hAC
  have hB5eq : B5 = CFSG.conjugate (Subgroup.zpowers M.b5el) t := hBt
  have hAn : M.Agrp ≤ Subgroup.normalizer ((M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el :
      Subgroup G) : Set G) := M.Agrp_le_normalizer_B5Q5
  refine ⟨a, ⟨?_, hAC⟩, ?_, ?_, ?_, ?_⟩
  ·
    rw [hS2, hQ5ex]
    have h1 := (burnsideJ8b_isElemAbelianSection_conjugate (P := M.Q5 M.b5el_mem_H ⊔ M.W)
      (N := M.W) (k := 2) t).mpr (burnsideJ8b_Q5W_section M)
    rwa [burnsideJ8b_conjugate_sup, hCW] at h1
  ·
    rw [hARu, hS2, hR2]
    refine ⟨burnsideJ8b_A_section M, ?_, burnsideJ8b_A_sup_S M, ?_⟩
    · exact M.Agrp_inf_S
    · intro B hAB hBR hXB
      rw [hG2] at hX
      exact burnsideJ8b_irreducible M hX hAB hBR hXB
  ·
    refine ⟨?_, ?_, ?_⟩
    · rw [hARu, hQ5ex, hB5eq, ← burnsideJ8b_conjugate_sup, sup_comm]
      have := (burnsideJ8b_conjugate_le_normalizer_iff (A := M.Agrp)
        (B := M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el) t).mpr hAn
      rwa [hCA] at this
    · rw [hARu, hQ5ex]
      have := (burnsideJ8b_conjugate_le_normalizer_iff (A := M.Agrp)
        (B := M.Q5 M.b5el_mem_H) t).mpr M.Agrp_le_normalizer_Q5
      rwa [hCA] at this
    · have hF1c : ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a ⊔ B5 ⊔
          Q5Ru (M.T : Subgroup G) B5 = CFSG.conjugate M.F1 t := by
        rw [hARu, hQ5ex, hB5eq]
        unfold RuDataM.F1 RuDataM.B5Q5
        rw [burnsideJ8b_conjugate_sup, burnsideJ8b_conjugate_sup, hCA]
        ac_rfl
      exact burnsideJ8b_oTwoQuot_congr hF1c
        (burnsideJ8b_oTwoQuot_conj M.F1 t M.nonempty_oTwoQuot_F1)
  ·
    rw [hARu, hQ5ex]
    have e : M.Agrp ⊔ CFSG.conjugate (M.Q5 M.b5el_mem_H) t ⊔ SRu M.L =
        CFSG.conjugate (M.Agrp ⊔ M.Q5 M.b5el_mem_H ⊔ ruS M.L) t := by
      rw [burnsideJ8b_conjugate_sup, burnsideJ8b_conjugate_sup, hCA, hCS]
      rfl
    rw [e, burnsideJ8b_A_Q5_S M, hCT]
  ·
    have hx2 : M.x2el ∈ M.G2 := M.x2el_mem_G2
    have hX'z : CFSG.conjugate (Subgroup.zpowers M.x2el) t =
        Subgroup.zpowers (t⁻¹ * M.x2el * t) := burnsideJ8b_conjugate_zpowers _ _
    have hx'G2 : t⁻¹ * M.x2el * t ∈ M.G2 := mul_mem (mul_mem (inv_mem htG2) hx2) htG2
    have hx'3 : orderOf (t⁻¹ * M.x2el * t) = 3 := by
      have := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective M.x2el
      rw [M.orderOf_x2el] at this
      simpa [MulAut.conj_apply] using this
    have hF2c : Q5Ru (M.T : Subgroup G) B5 ⊔ CFSG.conjugate (Subgroup.zpowers M.x2el) t ⊔
        ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a = CFSG.conjugate M.F2 t := by
      rw [hARu, hQ5ex]
      unfold RuDataM.F2 RuDataM.TF
      rw [burnsideJ8b_conjugate_sup, burnsideJ8b_conjugate_sup, hCA]
      ac_rfl
    have hN' : (M.Agrp.subgroupOf (CFSG.conjugate M.F2 t)).Normal := by
      refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
      have := (burnsideJ8b_conjugate_le_normalizer_iff (A := M.F2) (B := M.Agrp) t).mpr
        (M.F2_le_G2.trans M.G2_le_normalizer_Agrp)
      rwa [hCA] at this
    refine ⟨CFSG.conjugate (Subgroup.zpowers M.x2el) t, ?_, ?_, ?_⟩
    · rw [hG2, hX'z]
      exact burnsideJ8b_isSylow3_zpowers M.card_G2 hx'G2 hx'3
    · rw [hQ5ex, hARu]
      have e : CFSG.conjugate (Subgroup.zpowers M.x2el) t ⊔ M.Agrp =
          CFSG.conjugate M.XA t := by
        unfold RuDataM.XA
        rw [burnsideJ8b_conjugate_sup, hCA]
      rw [e, burnsideJ8b_conjugate_le_normalizer_iff]
      exact (le_sup_right : M.Q5 M.b5el_mem_H ≤ M.TF).trans M.TF_le_normalizer_XA
    · have hN : ((ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a).subgroupOf
          (Q5Ru (M.T : Subgroup G) B5 ⊔ CFSG.conjugate (Subgroup.zpowers M.x2el) t ⊔
            ARu M.L (ruV M.L) V2 (M.T : Subgroup G) a)).Normal := by
        rw [hF2c, hARu]; exact hN'
      refine ⟨hN, ?_⟩
      obtain ⟨f⟩ := M.nonempty_F2_quot_perm3
      obtain ⟨s3⟩ := burnsideJ8b_nonempty_s3_sl2
      obtain ⟨g⟩ := burnsideJ8b_quot_conj M.F2 M.Agrp M.Agrp t hCA (K := Equiv.Perm (Fin 3)) ⟨f⟩
      exact burnsideJ8b_quot_congr hF2c hARu ⟨g.trans s3⟩

end

@[expose] def J_4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
      pCoreOf 2 (FRu L V V2 T a B5 X) = ⊥ ∧
      (F1Ru L V V2 T a B5 ⊓ F2Ru L V V2 T a B5 X = TFRu L V V2 T a B5 ∧
        (∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (T' : Subgroup Y), IsTwoF4TwoGroup Y ∧
          CFSG.Quasithin.IsYAmalgam
            (CFSG.Quasithin.RankTwoAmalgam.ofSubgroups (F1Ru L V V2 T a B5)
              (F2Ru L V V2 T a B5 X)) T') ∧
        (CFSG.Quasithin.RankTwoAmalgam.inclusionCompletion (F1Ru L V V2 T a B5)
          (F2Ru L V V2 T a B5 X) (FRu L V V2 T a B5 X) rfl).IsFaithful) ∧
      (pCoreOf 2 (F1Ru L V V2 T a B5) = Q5Ru T B5 ⊔ Q0Ru V T ∧
        Q5Ru T B5 ⊔ Q0Ru V T = F1Ru L V V2 T a B5 ⊓ QRu T) ∧
      (G2Ru L V2 T = F2Ru L V V2 T a B5 X ⊔ SRu L ∧
        pCoreOf 2 (F2Ru L V V2 T a B5 X) = ARu L V V2 T a ∧
        F2Ru L V V2 T a B5 X ⊓ SRu L = WRu L V V2 T ∧
        WRu L V V2 T = S2Ru L V V2 T ∧
        ∀ B : Subgroup G, ARu L V V2 T a ≤ B → B ≤ R2Ru L V2 T →
          F2Ru L V V2 T a B5 X ≤ Subgroup.normalizer (B : Set G) →
          B = ARu L V V2 T a ∨ B = R2Ru L V2 T)

section

open scoped commutatorElement in
open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
theorem as_J_4_5 : J_4_5 := by
  intro G _ _ _ V _ h _ hV2 _ hg hgH _ hv hvQ _ hB5 hinv _ hX _ ha hAN hQN
  obtain ⟨M, y, hML, hMT, hyT, hG2, hR2, hS2, hARu, ⟨t, ht, hBt⟩, hTF, hF1, hF2, hF⟩ :=
    RuChoice.reduce h hV2 hg hgH hv hvQ hB5 hinv hX ha hAN hQN
  subst hML
  subst hMT
  have hV : V = ruV M.L := h.V_eq_ruV
  subst hV
  have hF1t := (RuChoice.TF_F1 M hV2 ht hBt ha).2
  obtain ⟨hCW, _, hCA, hCS, _, hCG⟩ := burnsideJ8b_conj_T_fixes M hyT
  have hQ5ex := burnsideJ8b_Q5Ru_eq M ht hBt
  have htH : t ∈ ruH M.T := M.toRuData.T_le_H ht
  have hZ : ZRu (M.T : Subgroup G) = ruZ M.T := RuType.BridgeTwo.centerOf_eq _
  have hH : HRu (M.T : Subgroup G) = ruH M.T := by unfold HRu; rw [hZ]
  have hQ : QRu (M.T : Subgroup G) = ruQ M.T := by unfold QRu; rw [hH]
  have hCQ : CFSG.conjugate (ruQ M.T) t = ruQ M.T :=
    burnsideJ8b_conjugate_eq_self (RuChoice.mem_normalizer fun x hx => M.conj_mem_Q htH hx)
  have hCQ0 : CFSG.conjugate M.Q0 t = M.Q0 :=
    burnsideJ8b_conjugate_eq_self (RuChoice.mem_normalizer fun x hx => M.conj_mem_Q0 htH hx)
  have hQ0 := burnsideJ8b_Q0Ru_eq M
  have hWRu := burnsideJ8b_WRu_eq M hV2
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    rw [hF, burnsideJ8b_pCoreOf_conjugate]
    have h1 := M.pCoreOf_F_eq_bot
    rw [sup_eq_left.mpr (M.TF_le_F1.trans le_sup_left)] at h1
    rw [h1]
    unfold CFSG.conjugate
    exact Subgroup.map_bot _
  ·
    rw [hF1, hF2, hTF, ← burnsideJ8b_conjugate_inf, M.F1_inf_F2]
  ·
    obtain ⟨⟨Y, _, hY, T', hYam⟩, -, -, -, -⟩ := M.case2F4 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
      (CFSG.Quasithin.RuType.isQuasithinSub_of_isTypeRu (h.isTypeRu CFSG.Quasithin.RuType.stUnique) _)
    have hfin : Finite Y := by
      rcases hY with ⟨-, ⟨e⟩⟩ | ⟨h3, -, -⟩
      · exact Finite.of_equiv _ e.toEquiv.symm
      · omega
    exact ⟨Y, inferInstance, hfin, T', burnsideJ8b_isTwoF4TwoGroup_of_isTwistedF4Over hY, by
      rw [hF1, hF2]; exact burnsideJ8b_isYAmalgam_conjugate _ _ y hYam⟩
  ·
    exact CFSG.Quasithin.RankTwoAmalgam.inclusionCompletion_isFaithful _ _ _ rfl
  ·
    rw [hF1t, burnsideJ8b_pCoreOf_conjugate, M.pCoreOf_F1, hQ5ex, hQ0]
    unfold RuDataM.Ygrp
    rw [burnsideJ8b_conjugate_sup, hCQ0]
  · rw [hF1t, hQ5ex, hQ0, hQ]
    have e : CFSG.conjugate M.F1 t ⊓ ruQ M.T = CFSG.conjugate (M.F1 ⊓ ruQ M.T) t := by
      rw [burnsideJ8b_conjugate_inf, hCQ]
    rw [e, M.F1_inf_Q]
    unfold RuDataM.Ygrp
    rw [burnsideJ8b_conjugate_sup, hCQ0]
  ·
    rw [hG2, hF2]
    show M.G2 = CFSG.conjugate M.F2 y ⊔ ruS M.L
    rw [← hCS, ← burnsideJ8b_conjugate_sup, burnsideJ8b_F2_sup_S, hCG]
  · rw [hF2, burnsideJ8b_pCoreOf_conjugate, M.pCoreOf_F2, hCA, hARu]
  · rw [hF2, hWRu]
    show CFSG.conjugate M.F2 y ⊓ ruS M.L = M.W
    rw [← hCS, ← burnsideJ8b_conjugate_inf, M.F2_inf_S, hCW]
  · rw [hWRu, hS2]
  · intro B hAB hBR hXB
    rw [hARu] at hAB ⊢
    rw [hR2] at hBR ⊢
    rw [hG2] at hX
    exact burnsideJ8b_irreducible M hX hAB hBR (le_sup_right.trans hXB)

end

@[expose] def J_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
        centerOf (TFRu L V V2 T a B5) = ZRu T ∧ centerOf (F1Ru L V V2 T a B5) = ZRu T

section

open scoped commutatorElement in
open CFSG.ASVolI.ChIJK in
theorem as_J_4_6 : J_4_6 := by
  intro G _ _ _ V T h V2 _ _ _ _ _ _ _ _ hB5 _ _ _ a ha hA _
  obtain ⟨M, hML, hMT⟩ := h.exists_ruDataM CFSG.Quasithin.RuType.stUnique
  subst hML
  have hTM : (M.T : Subgroup G) = T := by rw [hMT]; exact h.coe_sylowT
  have hZ : ZRu T = CFSG.Quasithin.RuType.ruZ M.T := by
    have := h.ZRu_eq_ruZ
    rwa [← hMT] at this
  have hH : HRu T = CFSG.Quasithin.RuType.ruH M.T := by
    have := h.HRu_eq_ruH
    rwa [← hMT] at this
  have hQ' : QRu T = CFSG.Quasithin.RuType.ruQ M.T := by
    have := h.QRu_eq_ruQ
    rwa [← hMT] at this
  have hcardH : Nat.card (HRu T) = 2 ^ 11 * 120 := by rw [hH]; exact M.toRuData.card_H
  obtain ⟨b, hb5, hbB⟩ := burnsideJ8b_exists_gen hcardH hB5
  subst hbB
  have hbH : b ∈ CFSG.Quasithin.RuType.ruH M.T := by
    rw [← hH]; exact hB5.1 (Subgroup.mem_zpowers b)
  have hQ5 : Q5Ru T (Subgroup.zpowers b) = M.Q5 hbH := by
    unfold Q5Ru; rw [hQ']; exact burnsideJ8b_Q5_eq M hbH hb5
  have hTp : IsPGroup 2 T := hTM ▸ M.T.isPGroup'
  have hT2 : ¬ 2 ∣ T.index := by rw [← hTM]; exact M.T.not_dvd_index
  have hG2T : T ≤ G2Ru M.L V2 T := le_sup_right
  have hTrel : ¬ 2 ∣ T.relIndex (G2Ru M.L V2 T) := fun hd =>
    hT2 (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_index hG2T)))
  have hR2T : R2Ru M.L V2 T ≤ T := burnsideJ8b_pCoreOf_le_sylow hTp hG2T hTrel
  have hSle : SRu M.L ≤ T := CFSG.ASVolI.ChIJK.RuType.BridgeTwo.S_le_T h
  have hTH : T ≤ CFSG.Quasithin.RuType.ruH M.T := by rw [← hTM]; exact M.toRuData.T_le_H
  have hS2T : S2Ru M.L V V2 T ≤ T := by
    refine sup_le ?_ ((CFSG.ASVolI.ChIJK.RuType.BridgeTwo.V_le_S h).trans hSle)
    refine Subgroup.commutator_le.mpr fun s hs r hr => ?_
    have hsT := hSle hs
    have hrT := hR2T hr
    exact T.mul_mem (T.mul_mem (T.mul_mem hsT hrT) (T.inv_mem hsT)) (T.inv_mem hrT)
  have haR : a ∈ R2Ru M.L V2 T := by
    have h1 : a ∈ Subgroup.zpowers a ⊔ S2Ru M.L V V2 T :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    rw [← ha.1] at h1
    exact (Subgroup.mem_inf.mp h1).2
  have hAT : ARu M.L V V2 T a ≤ T := by
    refine sup_le ?_ hS2T
    unfold conjClosure
    refine iSup₂_le fun y hy => ?_
    rintro x ⟨z, hz, rfl⟩
    have hzR : z ∈ R2Ru M.L V2 T := Subgroup.zpowers_le.mpr haR hz
    have hyi : y⁻¹ ∈ G2Ru M.L V2 T := inv_mem hy
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (G2Ru M.L V2 T) hyi) z).mp hzR
    exact hR2T h1
  have hQ5T : M.Q5 hbH ≤ T := by
    rw [← hTM]; exact (M.Q5_le_Q hbH).trans M.Q_le_T
  have hAH : ARu M.L V V2 T a ≤ CFSG.Quasithin.RuType.ruH M.T := hAT.trans hTH
  have hbHle : Subgroup.zpowers b ≤ CFSG.Quasithin.RuType.ruH M.T :=
    Subgroup.zpowers_le.mpr hbH
  have hTFeq : TFRu M.L V V2 T a (Subgroup.zpowers b) = ARu M.L V V2 T a ⊔ M.Q5 hbH := by
    unfold TFRu; rw [hQ5]
  have hF1eq : F1Ru M.L V V2 T a (Subgroup.zpowers b) =
      (ARu M.L V V2 T a ⊔ M.Q5 hbH) ⊔ Subgroup.zpowers b := by
    unfold F1Ru; rw [hTFeq]
  have hTFT : ARu M.L V V2 T a ⊔ M.Q5 hbH ≤ T := sup_le hAT hQ5T
  have hTFH : ARu M.L V V2 T a ⊔ M.Q5 hbH ≤ CFSG.Quasithin.RuType.ruH M.T := hTFT.trans hTH
  have hF1H : (ARu M.L V V2 T a ⊔ M.Q5 hbH) ⊔ Subgroup.zpowers b ≤
      CFSG.Quasithin.RuType.ruH M.T := sup_le hTFH hbHle
  have hUQ5 : CFSG.Quasithin.RuType.ruU M.L M.T ≤ M.Q5 hbH := M.U_le_Q5 hbH
  have hZU : CFSG.Quasithin.RuType.ruZ M.T ≤ M.Q5 hbH :=
    M.two.Z_le_U.trans hUQ5
  have hAn : ARu M.L V V2 T a ≤
      Subgroup.normalizer ((M.Q5 hbH ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    have := hA
    rw [hQ5, sup_comm] at this
    exact this
  have hA2 : IsPGroup 2 (ARu M.L V V2 T a) := hTp.to_le hAT
  rw [hTFeq, hF1eq, hZ]
  refine ⟨?_, ?_⟩
  · ext c
    rw [CFSG.ASVolI.ChIJK.RuType.BridgeTwo.mem_centerOf_iff]
    constructor
    · rintro ⟨hc, hcc⟩
      exact burnsideJ8b_center_le M hbH hb5 hTFH le_sup_right hc hcc
    · intro hcZ
      refine ⟨Subgroup.mem_sup_right (hZU hcZ), fun x hx => ?_⟩
      exact (M.toRuData.mem_Z_iff.mp hcZ).2 x (by rw [hTM]; exact hTFT hx)
  · ext c
    rw [CFSG.ASVolI.ChIJK.RuType.BridgeTwo.mem_centerOf_iff]
    constructor
    · rintro ⟨hc, hcc⟩
      have hcH := hF1H hc
      have hcU : ∀ u ∈ CFSG.Quasithin.RuType.ruU M.L M.T, u * c = c * u := fun u hu =>
        hcc u (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hUQ5 hu)))
      have hcHC : c ∈ M.HC :=
        Subgroup.mem_inf.mpr ⟨hcH, Subgroup.mem_centralizer_iff.mpr hcU⟩
      have hcQ := M.HC_le_Q hcHC
      have hcTF := burnsideJ8b_F1_inf_Q_le M hbH hb5 hA2 hAH hAn hc hcQ
      exact burnsideJ8b_center_le M hbH hb5 hTFH le_sup_right hcTF
        (fun x hx => hcc x (Subgroup.mem_sup_left hx))
    · intro hcZ
      refine ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right (hZU hcZ)), fun x hx => ?_⟩
      exact (M.Z_comm_H hcZ (hF1H hx)).symm

end

@[expose] def J_4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ V2 : Subgroup G, IsV2 V T V2 →
    ∀ g ∈ L2Ru L V2, g ∉ HRu T →
    ∀ v : G, v ∈ CFSG.conjugate (URu V T) g → v ∉ CFSG.conjugate (URu V T) g ⊓ QRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) → InvertsGroup v B5 →
    ∀ X : Subgroup G, IsSylowIn 3 X (G2Ru L V2 T) →
    ∀ a : G, IsAChoice L V T V2 B5 a →
      ARu L V V2 T a ≤ Subgroup.normalizer ((B5 ⊔ Q5Ru T B5 : Subgroup G) : Set G) →
      Q5Ru T B5 ≤ Subgroup.normalizer ((X ⊔ ARu L V V2 T a : Subgroup G) : Set G) →
        IsTwoF4TwoGroup ↥(FRu L V V2 T a B5 X)

section BurnsideJ9b

private theorem burnsideJ9b_exists_reeTitsModel :
    ∃ (Y0 : Type) (_ : Group Y0), CFSG.Blueprint.ReeTitsModel Y0 .Tits 2 1 := by
  refine ⟨CFSG.Blueprint.DerivedCentralQuotient
    (CFSG.Blueprint.reeFixedGroup CFSG.Blueprint.Chevalley.Tag.F4 (ZMod 2)
      CFSG.Blueprint.reeF4Perm
      fun i => if i ∈ CFSG.Blueprint.reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)),
    inferInstance, ?_⟩
  refine ⟨⟨Nat.prime_two, le_refl _, rfl, rfl, rfl⟩, 0, rfl, ?_⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩

private theorem burnsideJ9b_isTwoF4TwoGroup_conjugate {G : Type} [Group G] {K : Subgroup G} (c : G)
    (h : CFSG.ASVolI.ChIJK.IsTwoF4TwoGroup ↥K) :
    CFSG.ASVolI.ChIJK.IsTwoF4TwoGroup ↥(CFSG.conjugate K c) := by
  obtain ⟨Y0, _, hY0, ⟨e⟩⟩ := h
  exact ⟨Y0, inferInstance, hY0, ⟨((MulAut.conj c⁻¹).subgroupMap K).symm.trans e⟩⟩

section

private theorem burnsideJ9b_isTwoF4TwoGroup_of_titsA {Y : Type} [Group Y]
    (e : Nonempty (Y ≃* ↥CFSG.Sporadic.Schreier.Tits.titsA)) :
    CFSG.ASVolI.ChIJK.IsTwoF4TwoGroup Y := by
  obtain ⟨Y0, _, hY0⟩ := burnsideJ9b_exists_reeTitsModel
  obtain ⟨e1⟩ := e
  obtain ⟨e2⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y0 2 1 hY0
  exact ⟨Y0, inferInstance, hY0,
    ⟨e1.trans (CFSG.Sporadic.Schreier.Tits.titsConjEquiv.trans (MulAut.congr e2.symm))⟩⟩

end

end BurnsideJ9b

section

theorem as_J_4_7 : J_4_7 := by
  intro G _ _ L V T h V2 hV2 g hg hgH v hv hvQ B5 hB5 hinv X hX a ha haN hQN
  obtain ⟨M, y, -, -, -, -, -, -, -, -, -, -, -, hF⟩ :=
    RuChoice.reduce h hV2 hg hgH hv hvQ hB5 hinv hX ha haN hQN
  have hJ := M.theorem_J47 CFSG.Quasithin.Fan86.hayashiFiveThree_proved'
    CFSG.Quasithin.H13.F45Ru.f45TwoF4 CFSG.Quasithin.H13.TwoF4F48.f48TwoF4
  rw [hF]
  exact burnsideJ9b_isTwoF4TwoGroup_conjugate y (burnsideJ9b_isTwoF4TwoGroup_of_titsA hJ)

end

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def J_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T V2 B5 X : Subgroup G) (g v a z u : G) (I : Subgroup G),
    RuUSetup G L V T V2 B5 X g v a z u I → (BsetRu B5 z u).ncard = 6

section BurnsideJ48

section BurnsideJ48Basic

variable {G : Type} [Group G]

private theorem burnsideJ48_pow_five {X : Subgroup G} (h : Nat.card X = 5) {x : G} (hx : x ∈ X) :
    x ^ 5 = 1 := by
  have h1 := Subgroup.orderOf_dvd_natCard X hx
  rw [h] at h1
  exact orderOf_dvd_iff_pow_eq_one.mp h1

private theorem burnsideJ48_eq_one_of_sq {x : G} (h5 : x ^ 5 = 1) (h2 : x * x = 1) : x = 1 := by
  have h2' : x ^ 2 = 1 := by rw [pow_two]; exact h2
  have := (pow_gcd_eq_one (a := x)).mpr ⟨h2', h5⟩
  rwa [show Nat.gcd 2 5 = 1 by norm_num, pow_one] at this

private theorem burnsideJ48_exists_ne_one {X : Subgroup G} (h : Nat.card X = 5) : ∃ x ∈ X, x ≠
    1 := by
  obtain ⟨x, hx, -, hx1, -⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five h
  exact ⟨x, hx, hx1⟩

private theorem burnsideJ48_comm_of_card_five {X : Subgroup G} (h : Nat.card X = 5) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  obtain ⟨x, -, -, -, hx⟩ := CFSG.Quasithin.RuType.exists_gen_of_card_five h
  intro a ha b hb
  obtain ⟨m, rfl⟩ := hx a ha
  obtain ⟨n, rfl⟩ := hx b hb
  exact ((Commute.refl x).pow_pow m n).eq

private theorem burnsideJ48_ne_of_cent_inv {X Y : Subgroup G} {a : G} (hX : Nat.card X = 5)
    (hXa : ∀ x ∈ X, a * x * a⁻¹ = x) (hYa : ∀ y ∈ Y, a * y * a⁻¹ = y⁻¹) : X ≠ Y := by
  intro hXY
  obtain ⟨x, hxX, hx1⟩ := burnsideJ48_exists_ne_one hX
  apply hx1
  have hxY : x ∈ Y := hXY ▸ hxX
  have h1 := hXa x hxX
  have h2 := hYa x hxY
  have h3 : x = x⁻¹ := h1.symm.trans h2
  refine burnsideJ48_eq_one_of_sq (burnsideJ48_pow_five hX hxX) ?_
  calc x * x = x * x⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel x

open scoped Pointwise in
private theorem burnsideJ48_mem_sup {S T : Subgroup G} (hST : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a)
    {g : G}
    (hg : g ∈ S ⊔ T) : ∃ s ∈ S, ∃ t ∈ T, s * t = g := by
  have hle : S ≤ Subgroup.normalizer (T : Set G) := fun s hs => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : s * h * s⁻¹ = h := by rw [hST s hs h hh]; group
      rw [this]; exact hh
    · intro hh
      have h1 : s⁻¹ * (s * h * s⁻¹) = (s * h * s⁻¹) * s⁻¹ := hST s⁻¹ (inv_mem hs) _ hh
      have : h = s * h * s⁻¹ := by
        calc h = s⁻¹ * (s * h * s⁻¹) * s := by group
          _ = ((s * h * s⁻¹) * s⁻¹) * s := by rw [h1]
          _ = s * h * s⁻¹ := by group
      rw [this]; exact hh
  have := Subgroup.coe_mul_of_left_le_normalizer_right S T hle
  have hg' : g ∈ ((S : Set G) * (T : Set G)) := by
    rw [← this]; exact hg
  obtain ⟨s, hs, t, ht, e⟩ := Set.mem_mul.mp hg'
  exact ⟨s, hs, t, ht, e⟩

private theorem burnsideJ48_comm_sup {S T : Subgroup G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hST : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) :
    ∀ g ∈ S ⊔ T, ∀ h ∈ S ⊔ T, g * h = h * g := by
  intro g hg h hh
  obtain ⟨s1, hs1, t1, ht1, rfl⟩ := burnsideJ48_mem_sup hST hg
  obtain ⟨s2, hs2, t2, ht2, rfl⟩ := burnsideJ48_mem_sup hST hh
  have e1 : t1 * s2 = s2 * t1 := (hST s2 hs2 t1 ht1).symm
  have e2 : t2 * s1 = s1 * t2 := (hST s1 hs1 t2 ht2).symm
  calc s1 * t1 * (s2 * t2) = s1 * (t1 * s2) * t2 := by group
    _ = s1 * (s2 * t1) * t2 := by rw [e1]
    _ = (s1 * s2) * (t1 * t2) := by group
    _ = (s2 * s1) * (t2 * t1) := by rw [hS s1 hs1 s2 hs2, hT t1 ht1 t2 ht2]
    _ = s2 * (s1 * t2) * t1 := by group
    _ = s2 * (t2 * s1) * t1 := by rw [e2]
    _ = s2 * t2 * (s1 * t1) := by group

private theorem burnsideJ48_card_25 {c : ℕ} (h5 : 5 ∣ c) (h125 : c ∣ 125) (hne5 : c ≠ 5)
    (hne125 : c ≠ 125) : c = 25 := by
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
    (show c ∣ 5 ^ 3 by simpa using h125)
  interval_cases k
  · rw [hk] at h5; norm_num at h5
  · exact absurd (by simpa using hk) hne5
  · simpa using hk
  · exact absurd (by simpa using hk) hne125

private theorem burnsideJ48_card_25' {c : ℕ} (h25 : 25 ∣ c) (h125 : c ∣ 125) (hne125 : c ≠ 125) :
    c = 25 := by
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
    (show c ∣ 5 ^ 3 by simpa using h125)
  interval_cases k
  · rw [hk] at h25; norm_num at h25
  · rw [hk] at h25; norm_num at h25
  · simpa using hk
  · exact absurd (by simpa using hk) hne125

private theorem burnsideJ48_nc [Finite G] {P Z X Y : Subgroup G} {t : G}
    (hP : Nat.card P = 125) (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hZP : Z ≤ P) (hZ : Nat.card Z = 5) (hZc : ∀ x ∈ P, ∀ y ∈ Z, x * y = y * x)
    (hXP : X ≤ P) (hYP : Y ≤ P) (hX : Nat.card X = 5) (hY : Nat.card Y = 5)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXZ : ∀ x ∈ X, x ∈ Z → x = 1) (hYZ : ∀ y ∈ Y, y ∈ Z → y = 1)
    (htZ : ∀ w ∈ Z, t * w * t⁻¹ ∈ Z) (htX : ∀ x ∈ X, t * x * t⁻¹ = x)
    (htY : ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) : False := by
  have hXYtriv : ∀ x ∈ X, x ∈ Y → x = 1 := by
    intro x hxX hxY
    have h3 : x = x⁻¹ := (htX x hxX).symm.trans (htY x hxY)
    refine burnsideJ48_eq_one_of_sq (burnsideJ48_pow_five hX hxX) ?_
    calc x * x = x * x⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel x
  have hAle : X ⊔ Y ≤ P := sup_le hXP hYP
  have hAcomm := burnsideJ48_comm_sup (burnsideJ48_comm_of_card_five hX)
    (burnsideJ48_comm_of_card_five hY) hXY
  have hdvdP : ∀ K : Subgroup G, K ≤ P → Nat.card K ∣ 125 := fun K hK => by
    have := Subgroup.card_dvd_of_le hK
    rwa [hP] at this
  have hne125 : ∀ K : Subgroup G, K ≤ P → (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) →
      Nat.card K ≠ 125 := by
    intro K hKP hKc hK125
    apply hnab
    have hKP' : K = P := Subgroup.eq_of_le_of_card_ge hKP (by rw [hK125, hP])
    rw [hKP'] at hKc
    exact hKc
  have hA25 : Nat.card (X ⊔ Y : Subgroup G) = 25 := by
    have h1 : 5 ∣ Nat.card (X ⊔ Y : Subgroup G) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : X ≤ X ⊔ Y)
      rwa [hX] at this
    have h3 : Nat.card (X ⊔ Y : Subgroup G) ≠ 5 := by
      intro h5
      have hXA : X = X ⊔ Y := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h5, hX])
      obtain ⟨y, hyY, hy1⟩ := burnsideJ48_exists_ne_one hY
      have hyA : y ∈ X ⊔ Y := Subgroup.mem_sup_right hyY
      rw [← hXA] at hyA
      exact hy1 (hXYtriv y hyA hyY)
    exact burnsideJ48_card_25 h1 (hdvdP _ hAle) h3 (hne125 _ hAle hAcomm)
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a (hZP ha) b hb
  have hAZ : ∀ a ∈ X ⊔ Y, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a (hAle ha) b hb
  have hA'le : (X ⊔ Y) ⊔ Z ≤ P := sup_le hAle hZP
  have hA'comm := burnsideJ48_comm_sup hAcomm hZcomm hAZ
  have hA'25 : Nat.card ((X ⊔ Y) ⊔ Z : Subgroup G) = 25 := by
    have h1 : 25 ∣ Nat.card ((X ⊔ Y) ⊔ Z : Subgroup G) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : (X ⊔ Y) ≤ (X ⊔ Y) ⊔ Z)
      rwa [hA25] at this
    exact burnsideJ48_card_25' h1 (hdvdP _ hA'le) (hne125 _ hA'le hA'comm)
  have hEq : X ⊔ Y = (X ⊔ Y) ⊔ Z :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hA25, hA'25])
  have hZA : Z ≤ X ⊔ Y := by
    have := le_sup_right (a := X ⊔ Y) (b := Z)
    rwa [← hEq] at this
  obtain ⟨b, hbZ, hb1⟩ := burnsideJ48_exists_ne_one hZ
  apply hb1
  obtain ⟨x, hx, y, hy, hxy⟩ := burnsideJ48_mem_sup hXY (hZA hbZ)
  have hw : t * b * t⁻¹ = x * y⁻¹ := by
    rw [← hxy]
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x * y⁻¹ := by rw [htX x hx, htY y hy]
  have hwZ : t * b * t⁻¹ ∈ Z := htZ b hbZ
  have hxy' : y * x = x * y := (hXY x hx y hy).symm
  have h1 : b * (t * b * t⁻¹) = x * x := by
    rw [hw, ← hxy]
    calc x * y * (x * y⁻¹) = x * (y * x) * y⁻¹ := by group
      _ = x * (x * y) * y⁻¹ := by rw [hxy']
      _ = x * x := by group
  have h2 : b * (t * b * t⁻¹)⁻¹ = y * y := by
    rw [hw, ← hxy]
    calc x * y * (x * y⁻¹)⁻¹ = x * y * (y * x⁻¹) := by group
      _ = x * (y * y) * x⁻¹ := by group
      _ = y * y := by
        have : x * (y * y) = (y * y) * x := by
          calc x * (y * y) = (x * y) * y := by group
            _ = (y * x) * y := by rw [hxy']
            _ = y * (x * y) := by group
            _ = y * (y * x) := by rw [hxy']
            _ = (y * y) * x := by group
        rw [this]; group
  have hxx : x * x ∈ Z := h1 ▸ mul_mem hbZ hwZ
  have hyy : y * y ∈ Z := h2 ▸ mul_mem hbZ (inv_mem hwZ)
  have hx1 : x = 1 := by
    have : x * x = 1 := hXZ _ (mul_mem hx hx) hxx
    exact burnsideJ48_eq_one_of_sq (burnsideJ48_pow_five hX hx) this
  have hy1 : y = 1 := by
    have : y * y = 1 := hYZ _ (mul_mem hy hy) hyy
    exact burnsideJ48_eq_one_of_sq (burnsideJ48_pow_five hY hy) this
  rw [← hxy, hx1, hy1, one_mul]

private theorem burnsideJ48_mem_map_conj (g : G) (K : Subgroup G) (x : G) :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

private theorem burnsideJ48_normalizer_conj (g : G) (K : Subgroup G) :
    Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (K : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [burnsideJ48_mem_map_conj, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    rw [burnsideJ48_mem_map_conj, burnsideJ48_mem_map_conj] at this
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * y * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1, e2] at this
    exact this
  · intro h y
    rw [burnsideJ48_mem_map_conj, burnsideJ48_mem_map_conj]
    have e2 : g⁻¹ * (x * y * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e2]
    exact h (g⁻¹ * y * g)

private theorem burnsideJ48_inSubgroup_map (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (A B : Type) [Group A] [Group B] (e : A ≃* B), (F A).map e.toMonoidHom = F B)
    (g : G) (N : Subgroup G) :
    (F ↥(N.map (MulAut.conj g).toMonoidHom)).map (N.map (MulAut.conj g).toMonoidHom).subtype =
      ((F ↥N).map N.subtype).map (MulAut.conj g).toMonoidHom := by
  let e : ↥N ≃* ↥(N.map (MulAut.conj g).toMonoidHom) := MulEquiv.subgroupMap (MulAut.conj g) N
  have h1 := hF ↥N ↥(N.map (MulAut.conj g).toMonoidHom) e
  have hcomp : (N.map (MulAut.conj g).toMonoidHom).subtype.comp e.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp N.subtype := by
    ext x
    rfl
  rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]

end BurnsideJ48Basic

section BurnsideJ48LS

open CFSG.Quasithin.RuType in
private theorem burnsideJ48_pCoreOf_NB5
    {G : Type} [Group G] [Finite G] {M : RuDataM G} {b : G} (hbH : b ∈ ruH M.T)
    (hb5 : orderOf b = 5) : pCoreOf 5 (NB5 b) = P5 b := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set N := NB5 b with hNdef
  set P' : Subgroup N := (P5 b).subgroupOf N with hP'
  have hPn : P'.Normal :=
    ⟨fun y hy g => by
      rw [hP', Subgroup.mem_subgroupOf] at hy ⊢
      exact conj_mem_P5_of_normalizes g.2 hy⟩
  have hN : Nat.card N = 4000 := RuDataM.card_normalizer_B5 hbH hb5
  have hPc : Nat.card P' = 125 := by
    rw [hP', card_subgroupOf_of_le RuDataM.P5_le_NB5, RuDataM.card_P5_eq_125 hbH hb5]
  have hPp : IsPGroup 5 P' := by
    rw [IsPGroup.iff_card, hPc]
    exact ⟨3, by norm_num⟩
  unfold pCoreOf
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    show CFSG.pCore 5 N ≤ P'
    let S : Sylow 5 N := Sylow.ofCard P' (by
      rw [hPc, hN, show (4000 : ℕ) = 5 ^ 3 * 32 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
        Nat.prime_five]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 32 by norm_num)])
    exact (CFSG.pCore_isPGroup (p := 5) (G := N)).le_sylow_of_normal S
  · have hle : P' ≤ CFSG.pCore 5 N := le_sSup ⟨hPn, hPp⟩
    have := Subgroup.map_mono (f := N.subtype) hle
    rwa [hP', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr RuDataM.P5_le_NB5] at this

open CFSG.ASVolI.ChIJK in
structure burnsideJ48_LS {G : Type} [Group G] (z c : G) (Bc : Subgroup G) : Prop where
  card_B : Nat.card Bc = 5
  cent : ∀ x ∈ Bc, c * x * c⁻¹ = x
  card_P : Nat.card (PFstar Bc) = 125
  exp : ∀ x ∈ PFstar Bc, x ^ 5 = 1
  le_P : Bc ≤ PFstar Bc
  central : ∀ x ∈ PFstar Bc, ∀ y ∈ Bc, x * y = y * x
  nonab : ¬ ∀ x ∈ PFstar Bc, ∀ y ∈ PFstar Bc, x * y = y * x
  norm : ∀ n ∈ Subgroup.normalizer (Bc : Set G), ∀ x ∈ PFstar Bc, n * x * n⁻¹ ∈ PFstar Bc
  pcore : pCoreOf 5 (Subgroup.normalizer (Bc : Set G)) = PFstar Bc
  inv_mod : ∀ x ∈ PFstar Bc, c * x * c⁻¹ * x ∈ Bc
  card_cent : ∀ i : G, IsConj z i → i * i = 1 → (∀ x ∈ Bc, i * x * i⁻¹ = x⁻¹) →
    Nat.card (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5
  mem_P : ∀ x : G, (∀ y ∈ Bc, x * y = y * x) → x ^ 5 = 1 → x ∈ PFstar Bc

open CFSG.Quasithin.RuType CFSG.ASVolI.ChIJK in
private theorem burnsideJ48_LS_of_isConj
    {G : Type} [Group G] [Finite G] (M : RuDataM G) {c : G} {Bc : Subgroup G}
    (hc : IsConj M.z c) (hB : Nat.card Bc = 5)
    (hBc : Bc ≤ Subgroup.centralizer ({c} : Set G)) : burnsideJ48_LS M.z c Bc := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  obtain ⟨x0, hx0B, hx05, hx01, -⟩ := exists_gen_of_card_five hB
  have hzp : Subgroup.zpowers x0 = Bc := zpowers_eq_of_card_five hB hx0B hx05 hx01
  set b : G := g⁻¹ * x0 * g with hb
  have hx0c : x0 * c = c * x0 := Subgroup.mem_centralizer_singleton_iff.mp (hBc hx0B)
  have hbz : M.z * b = b * M.z := by
    rw [← hg] at hx0c
    calc M.z * b = g⁻¹ * ((g * M.z * g⁻¹) * x0) * g := by rw [hb]; group
      _ = g⁻¹ * (x0 * (g * M.z * g⁻¹)) * g := by rw [← hx0c]
      _ = b * M.z := by rw [hb]; group
  have hbH : b ∈ ruH M.T := M.mem_H_iff_comm.mpr hbz
  have hb5pow : b ^ 5 = 1 := by
    have e : b ^ 5 = g⁻¹ * x0 ^ 5 * g := by
      rw [hb, show g⁻¹ * x0 * g = g⁻¹ * x0 * g⁻¹⁻¹ by group, conj_pow]; group
    rw [e, hx05]; group
  have hgbg : g * b * g⁻¹ = x0 := by rw [hb]; group
  have hb1 : b ≠ 1 := fun h => hx01 (by rw [← hgbg, h]; group)
  have hb5 : orderOf b = 5 := orderOf_eq_prime hb5pow hb1
  have hBeq : Bc = Subgroup.zpowers (g * b * g⁻¹) := by rw [hgbg, hzp]
  have hgbgB : g * b * g⁻¹ ∈ Bc := by rw [hBeq]; exact Subgroup.mem_zpowers _
  have hBmap : Bc = (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers, hBeq]
    simp [MulAut.conj_apply]
  have hNmap : Subgroup.normalizer (Bc : Set G) =
      (NB5 b).map (MulAut.conj g).toMonoidHom := by
    rw [hBmap]
    exact burnsideJ48_normalizer_conj g _
  have hPF : PFstar Bc = RuDataM.P5c b g := by
    have key := burnsideJ48_inSubgroup_map (fun K _ => CFSG.generalizedFitting K)
      (fun A B _ _ e => CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv e)
      g (NB5 b)
    have hbase := RuDataM.generalizedFitting_NB5 hbH hb5
    unfold PFstar
    rw [hNmap]
    rw [key, hbase]
  have hpc : pCoreOf 5 (Subgroup.normalizer (Bc : Set G)) = RuDataM.P5c b g := by
    have key := burnsideJ48_inSubgroup_map (fun K _ => CFSG.pCore 5 K)
      (fun A B _ _ e => CFSG.pCore_map_iso 5 e) g (NB5 b)
    have hbase := burnsideJ48_pCoreOf_NB5 hbH hb5
    unfold pCoreOf at hbase ⊢
    rw [hNmap]
    rw [key, hbase]
  refine ⟨hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hBc hx)
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [← h]
      _ = x := by group
  · rw [hPF]
    exact RuDataM.card_P5c hbH hb5 g
  · intro x hx
    rw [hPF] at hx
    exact RuDataM.pow_five_P5c hbH hb5 hx
  · rw [hPF, hBeq]
    exact Subgroup.zpowers_le.mpr (RuDataM.conj_mem_P5c (RuDataM.b_mem_P5 hb5))
  · intro x hx y hy
    rw [hPF] at hx
    rw [hBeq] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (RuDataM.comm_center_P5c hx) k).eq
  · rw [hPF]
    exact RuDataM.not_comm_P5c hbH hb5 g
  · intro n hn x hx
    rw [hPF] at hx ⊢
    rw [hNmap, burnsideJ48_mem_map_conj] at hn
    have h := conj_mem_P5_of_normalizes hn (RuDataM.mem_P5c.mp hx)
    rw [RuDataM.mem_P5c]
    have e : g⁻¹ * (n * x * n⁻¹) * g = (g⁻¹ * n * g) * (g⁻¹ * x * g) * (g⁻¹ * n * g)⁻¹ := by
      group
    rw [e]
    exact h
  · rw [hpc, hPF]
  · intro x hx
    rw [hPF] at hx
    obtain ⟨k, hk⟩ := RuDataM.z_conj_P5 hbH hb5 (RuDataM.mem_P5c.mp hx)
    have e1 : c * x * c⁻¹ = x⁻¹ * (g * b * g⁻¹) ^ k := by
      rw [← hg, conj_zpow]
      calc g * M.z * g⁻¹ * x * (g * M.z * g⁻¹)⁻¹
          = g * (M.z * (g⁻¹ * x * g) * M.z⁻¹) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g)⁻¹ * b ^ k) * g⁻¹ := by rw [hk]
        _ = x⁻¹ * (g * b ^ k * g⁻¹) := by group
    have hcomm : x * (g * b * g⁻¹) ^ k = (g * b * g⁻¹) ^ k * x :=
      (Commute.zpow_right (RuDataM.comm_center_P5c hx) k).eq
    have e2 : c * x * c⁻¹ * x = (g * b * g⁻¹) ^ k := by
      rw [e1]
      calc x⁻¹ * (g * b * g⁻¹) ^ k * x = x⁻¹ * ((g * b * g⁻¹) ^ k * x) := by group
        _ = x⁻¹ * (x * (g * b * g⁻¹) ^ k) := by rw [hcomm]
        _ = (g * b * g⁻¹) ^ k := by group
    rw [e2]
    exact Subgroup.zpow_mem _ hgbgB k
  · intro i hiz hi2 hinv
    rw [hPF]
    exact RuDataM.card_P5c_inf_centralizer hbH hb5 hiz hi2 (hinv _ hgbgB)
  · intro x hxc hx5
    rw [hPF]
    exact RuDataM.mem_P5c_of_pow_five hbH hb5 (hxc _ hgbgB) hx5

private theorem burnsideJ48_mem_normalizer_of_cent {G : Type} [Group G] {Bc : Subgroup G} {c : G}
    (h : ∀ x ∈ Bc, c * x * c⁻¹ = x) : c ∈ Subgroup.normalizer (Bc : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy]
    exact hy
  · intro hy
    have h2 := h (c * y * c⁻¹) hy
    have key : ∀ w : G, c * w * c⁻¹ = w → c⁻¹ * w * c = w := by
      intro w hw
      calc c⁻¹ * w * c = c⁻¹ * (c * w * c⁻¹) * c := by rw [hw]
        _ = w := by group
    have h4 : y = c * y * c⁻¹ := by
      calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
        _ = c * y * c⁻¹ := key _ h2
    rw [h4]
    exact hy

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ48_step {G : Type} [Group G] {z c i : G} {Bc : Subgroup G}
    (hLS : burnsideJ48_LS z c Bc) (hzi : IsConj z i) (hi2 : i * i = 1) (hci : c * i = i * c)
    (hinv : ∀ x ∈ Bc, i * x * i⁻¹ = x⁻¹) :
    Nat.card (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5 ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G), i * x * i⁻¹ = x) ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      c * x * c⁻¹ = x⁻¹) ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      (c * i) * x * (c * i)⁻¹ = x⁻¹) ∧
    (∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G), x ∈ Bc → x = 1) := by
  have hcent : ∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      i * x * i⁻¹ = x := by
    intro x hx
    have h : x * i = i * x := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    calc i * x * i⁻¹ = x * i * i⁻¹ := by rw [h]
      _ = x := by group
  have hcn : c ∈ Subgroup.normalizer (Bc : Set G) := burnsideJ48_mem_normalizer_of_cent hLS.cent
  have hci' : c⁻¹ * i = i * c⁻¹ := by
    calc c⁻¹ * i = c⁻¹ * (i * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * i) * c⁻¹ := by rw [hci]
      _ = i * c⁻¹ := by group
  have hcinv : ∀ x ∈ (PFstar Bc ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G),
      c * x * c⁻¹ = x⁻¹ := by
    intro x hx
    have hxP : x ∈ PFstar Bc := (Subgroup.mem_inf.mp hx).1
    have hxC : x * i = i * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    have hcxP : c * x * c⁻¹ ∈ PFstar Bc := hLS.norm c hcn x hxP
    have hcxC : (c * x * c⁻¹) * i = i * (c * x * c⁻¹) := by
      calc (c * x * c⁻¹) * i = c * x * (c⁻¹ * i) := by group
        _ = c * x * (i * c⁻¹) := by rw [hci']
        _ = c * (x * i) * c⁻¹ := by group
        _ = c * (i * x) * c⁻¹ := by rw [hxC]
        _ = (c * i) * x * c⁻¹ := by group
        _ = (i * c) * x * c⁻¹ := by rw [hci]
        _ = i * (c * x * c⁻¹) := by group
    set w : G := (c * x * c⁻¹) * x with hw
    have hwB : w ∈ Bc := hLS.inv_mod x hxP
    have hwC : w * i = i * w := by
      calc w * i = (c * x * c⁻¹) * (x * i) := by rw [hw]; group
        _ = (c * x * c⁻¹) * (i * x) := by rw [hxC]
        _ = ((c * x * c⁻¹) * i) * x := by group
        _ = (i * (c * x * c⁻¹)) * x := by rw [hcxC]
        _ = i * w := by rw [hw]; group
    have h1 : i * w * i⁻¹ = w := by
      calc i * w * i⁻¹ = w * i * i⁻¹ := by rw [hwC]
        _ = w := by group
    have h2 := hinv w hwB
    have h3 : w = w⁻¹ := h1.symm.trans h2
    have hw1 : w = 1 := by
      refine burnsideJ48_eq_one_of_sq (hLS.exp w (hLS.le_P hwB)) ?_
      calc w * w = w * w⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel w
    have : c * x * c⁻¹ * x = 1 := hw1
    exact eq_inv_of_mul_eq_one_left this
  refine ⟨hLS.card_cent i hzi hi2 hinv, hcent, hcinv, ?_, ?_⟩
  · intro x hx
    calc (c * i) * x * (c * i)⁻¹ = c * (i * x * i⁻¹) * c⁻¹ := by group
      _ = c * x * c⁻¹ := by rw [hcent x hx]
      _ = x⁻¹ := hcinv x hx
  · intro x hx hxB
    have h1 := hcent x hx
    have h2 := hinv x hxB
    have h3 : x = x⁻¹ := h1.symm.trans h2
    refine burnsideJ48_eq_one_of_sq (hLS.exp x (hLS.le_P hxB)) ?_
    calc x * x = x * x⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel x

open CFSG.ASVolI.ChIJK in
private theorem burnsideJ48_main {G : Type} [Group G] [Finite G] (z u : G) (B5 : Subgroup G)
    (hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
      Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc)
    (hz2 : z * z = 1) (hu2 : u * u = 1) (huz : u * z = z * u)
    (hzu : IsConj z u) (hzuz : IsConj z (u * z)) (hB5 : Nat.card B5 = 5)
    (hB5z : ∀ x ∈ B5, z * x * z⁻¹ = x) (hB5u : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹) :
    (BsetRu B5 z u).ncard = 6 := by
  classical
  have hcentral : ∀ {c : G} {B : Subgroup G}, (∀ x ∈ B, c * x * c⁻¹ = x) →
      B ≤ Subgroup.centralizer ({c} : Set G) := by
    intro c B h x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * c = (c * x * c⁻¹) * c := by rw [h x hx]
      _ = c * x := by group
  have hB5c : B5 ≤ Subgroup.centralizer ({z} : Set G) := hcentral hB5z
  have hLS5 : burnsideJ48_LS z z B5 := hLS z B5 (IsConj.refl z) hB5 hB5c
  have hzu' : z * u = u * z := huz.symm
  have hB5uz : ∀ x ∈ B5, (u * z) * x * (u * z)⁻¹ = x⁻¹ := by
    intro x hx
    calc (u * z) * x * (u * z)⁻¹ = u * (z * x * z⁻¹) * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hB5z x hx]
      _ = x⁻¹ := hB5u x hx
  have huz2 : (u * z) * (u * z) = 1 := by
    calc (u * z) * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hzu']
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [hu2, hz2]; group
  have hci_z_uz : z * (u * z) = (u * z) * z := by
    calc z * (u * z) = (z * u) * z := by group
      _ = (u * z) * z := by rw [hzu']
  have hzuz_eq : z * (u * z) = u := by
    calc z * (u * z) = (z * u) * z := by group
      _ = (u * z) * z := by rw [hzu']
      _ = u * (z * z) := by group
      _ = u := by rw [hz2]; group
  have huzu_eq : (u * z) * u = z := by
    calc (u * z) * u = (z * u) * u := by rw [huz]
      _ = z * (u * u) := by group
      _ = z := by rw [hu2]; group
  have huuz_eq : u * (u * z) = z := by
    calc u * (u * z) = (u * u) * z := by group
      _ = z := by rw [hu2]; group
  have hU := burnsideJ48_step hLS5 hzu hu2 hzu' hB5u
  set Bu : Subgroup G := PFstar B5 ⊓ Subgroup.centralizer ({u} : Set G)
  obtain ⟨cardU, centU, invU_z, invU_zu, trivU⟩ := hU
  have hUZ := burnsideJ48_step hLS5 hzuz huz2 hci_z_uz hB5uz
  set Buz : Subgroup G := PFstar B5 ⊓ Subgroup.centralizer ({u * z} : Set G)
  obtain ⟨cardUZ, centUZ, invUZ_z, invUZ_u', trivUZ⟩ := hUZ
  have invUZ_u : ∀ x ∈ Buz, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have := invUZ_u' x hx
    rwa [hzuz_eq] at this
  have invU_uz : ∀ x ∈ Bu, (u * z) * x * (u * z)⁻¹ = x⁻¹ := by
    intro x hx
    have := invU_zu x hx
    rwa [hzu'] at this
  have hLSu : burnsideJ48_LS z u Bu := hLS u Bu hzu cardU (hcentral centU)
  have hLSuz : burnsideJ48_LS z (u * z) Buz := hLS (u * z) Buz hzuz cardUZ (hcentral centUZ)
  have hci1 : u * (u * z) = (u * z) * u := by
    calc u * (u * z) = z := huuz_eq
      _ = (u * z) * u := huzu_eq.symm
  have hU'UZ := burnsideJ48_step hLSu hzuz huz2 hci1 invU_uz
  set Bp_uz : Subgroup G := PFstar Bu ⊓ Subgroup.centralizer ({u * z} : Set G)
  obtain ⟨cardPUZ, centPUZ, invPUZ_u, invPUZ_z', trivPUZ⟩ := hU'UZ
  have invPUZ_z : ∀ x ∈ Bp_uz, z * x * z⁻¹ = x⁻¹ := by
    intro x hx
    have := invPUZ_z' x hx
    rwa [huuz_eq] at this
  have hU'U := burnsideJ48_step hLSuz hzu hu2 hci1.symm invUZ_u
  set Bp_u : Subgroup G := PFstar Buz ⊓ Subgroup.centralizer ({u} : Set G)
  obtain ⟨cardPU, centPU, invPU_uz, invPU_z', trivPU⟩ := hU'U
  have invPU_z : ∀ x ∈ Bp_u, z * x * z⁻¹ = x⁻¹ := by
    intro x hx
    have := invPU_z' x hx
    rwa [huzu_eq] at this
  have hLSpu : burnsideJ48_LS z u Bp_u := hLS u Bp_u hzu cardPU (hcentral centPU)
  have hZp := burnsideJ48_step hLSpu (IsConj.refl z) hz2 huz invPU_z
  set Bp_z : Subgroup G := PFstar Bp_u ⊓ Subgroup.centralizer ({z} : Set G)
  obtain ⟨cardPZ, centPZ, invPZ_u, invPZ_uz, trivPZ⟩ := hZp
  have eBu : BvRu B5 u = Bu := rfl
  have eBuz : BvRu B5 (u * z) = Buz := rfl
  have eBp_uz : BuzPRu B5 z u = Bp_uz := by
    show O5N (BvRu B5 u) ⊓ Subgroup.centralizer ({u * z} : Set G) = _
    rw [eBu]
    unfold O5N
    rw [hLSu.pcore]
  have eBp_u : BuPRu B5 z u = Bp_u := by
    show Subgroup.centralizer ({u} : Set G) ⊓ O5N (BvRu B5 (u * z)) = _
    rw [eBuz]
    unfold O5N
    rw [hLSuz.pcore, inf_comm]
  have eBp_z : BzPRu B5 z u = Bp_z := by
    show O5N (BuPRu B5 z u) ⊓ Subgroup.centralizer ({z} : Set G) = _
    rw [eBp_u]
    unfold O5N
    rw [hLSpu.pcore]
  have hset : BsetRu B5 z u = {B5, Bu, Buz, Bp_z, Bp_u, Bp_uz} := by
    unfold BsetRu
    rw [eBu, eBuz, eBp_z, eBp_u, eBp_uz]
  have hBuP : Bu ≤ PFstar B5 := inf_le_left
  have hBuzP : Buz ≤ PFstar B5 := inf_le_left
  have hB5comm : ∀ x ∈ B5, ∀ y ∈ PFstar B5, x * y = y * x := fun x hx y hy =>
    (hLS5.central y hy x hx).symm
  have hB5_Pu : B5 ≤ PFstar Bu := by
    intro x hx
    refine hLSu.mem_P x (fun y hy => hB5comm x hx y (hBuP hy)) (burnsideJ48_pow_five hB5 hx)
  have hB5_Puz : B5 ≤ PFstar Buz := by
    intro x hx
    refine hLSuz.mem_P x (fun y hy => hB5comm x hx y (hBuzP hy)) (burnsideJ48_pow_five hB5 hx)
  have h14 : B5 ≠ Bp_z := by
    intro h
    refine burnsideJ48_nc (P := PFstar Buz) (Z := Buz) (X := B5) (Y := Bp_u) (t := z)
      hLSuz.card_P hLSuz.nonab hLSuz.le_P cardUZ hLSuz.central hB5_Puz inf_le_left hB5 cardPU
      ?_ ?_ ?_ ?_ hB5z invPU_z
    · intro x hx y hy
      have hxPu : x ∈ PFstar Bp_u := by
        have : x ∈ Bp_z := h ▸ hx
        exact (Subgroup.mem_inf.mp this).1
      exact hLSpu.central x hxPu y hy
    · exact fun x hx hxZ => trivUZ x hxZ hx
    · exact fun y hy hyZ => trivPU y hy hyZ
    · intro w hw
      rw [invUZ_z w hw]
      exact inv_mem hw
  have h25 : Bu ≠ Bp_u := by
    intro h
    refine burnsideJ48_nc (P := PFstar Buz) (Z := Buz) (X := B5) (Y := Bu) (t := z)
      hLSuz.card_P hLSuz.nonab hLSuz.le_P cardUZ hLSuz.central hB5_Puz ?_ hB5 cardU
      ?_ ?_ ?_ ?_ hB5z invU_z
    · rw [h]
      exact inf_le_left
    · intro x hx y hy
      exact hB5comm x hx y (hBuP hy)
    · exact fun x hx hxZ => trivUZ x hxZ hx
    · intro y hy hyZ
      have hy' : y ∈ Bp_u := h ▸ hy
      exact trivPU y hy' hyZ
    · intro w hw
      rw [invUZ_z w hw]
      exact inv_mem hw
  have h36 : Buz ≠ Bp_uz := by
    intro h
    refine burnsideJ48_nc (P := PFstar Bu) (Z := Bu) (X := B5) (Y := Buz) (t := z)
      hLSu.card_P hLSu.nonab hLSu.le_P cardU hLSu.central hB5_Pu ?_ hB5 cardUZ
      ?_ ?_ ?_ ?_ hB5z invUZ_z
    · rw [h]
      exact inf_le_left
    · intro x hx y hy
      exact hB5comm x hx y (hBuzP hy)
    · exact fun x hx hxZ => trivU x hxZ hx
    · intro y hy hyZ
      have hy' : y ∈ Bp_uz := h ▸ hy
      exact trivPUZ y hy' hyZ
    · intro w hw
      rw [invU_z w hw]
      exact inv_mem hw
  have h12 : B5 ≠ Bu := burnsideJ48_ne_of_cent_inv (a := z) hB5 hB5z invU_z
  have h13 : B5 ≠ Buz := burnsideJ48_ne_of_cent_inv (a := z) hB5 hB5z invUZ_z
  have h15 : B5 ≠ Bp_u := burnsideJ48_ne_of_cent_inv (a := z) hB5 hB5z invPU_z
  have h16 : B5 ≠ Bp_uz := burnsideJ48_ne_of_cent_inv (a := z) hB5 hB5z invPUZ_z
  have h23 : Bu ≠ Buz := burnsideJ48_ne_of_cent_inv (a := u) cardU centU invUZ_u
  have h24 : Bu ≠ Bp_z := burnsideJ48_ne_of_cent_inv (a := u) cardU centU invPZ_u
  have h26 : Bu ≠ Bp_uz := burnsideJ48_ne_of_cent_inv (a := u) cardU centU invPUZ_u
  have h34 : Buz ≠ Bp_z := burnsideJ48_ne_of_cent_inv (a := u * z) cardUZ centUZ invPZ_uz
  have h35 : Buz ≠ Bp_u := burnsideJ48_ne_of_cent_inv (a := u * z) cardUZ centUZ invPU_uz
  have h45 : Bp_z ≠ Bp_u := burnsideJ48_ne_of_cent_inv (a := z) cardPZ centPZ invPU_z
  have h46 : Bp_z ≠ Bp_uz := burnsideJ48_ne_of_cent_inv (a := z) cardPZ centPZ invPUZ_z
  have h56 : Bp_u ≠ Bp_uz := burnsideJ48_ne_of_cent_inv (a := u) cardPU centPU invPUZ_u
  have n1 : B5 ∉ ({Bu, Buz, Bp_z, Bp_u, Bp_uz} : Set (Subgroup G)) := by
    simp [h12, h13, h14, h15, h16]
  have n2 : Bu ∉ ({Buz, Bp_z, Bp_u, Bp_uz} : Set (Subgroup G)) := by
    simp [h23, h24, h25, h26]
  have n3 : Buz ∉ ({Bp_z, Bp_u, Bp_uz} : Set (Subgroup G)) := by
    simp [h34, h35, h36]
  have n4 : Bp_z ∉ ({Bp_u, Bp_uz} : Set (Subgroup G)) := by
    simp [h45, h46]
  have n5 : Bp_u ∉ ({Bp_uz} : Set (Subgroup G)) := by
    simp [h56]
  rw [hset, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
    Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n4, Set.ncard_insert_of_notMem n5,
    Set.ncard_singleton]

end BurnsideJ48LS

section BurnsideJ48Final

private theorem burnsideJ48_eq_z {G : Type} [Group G] [Finite G] (M :
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

private theorem burnsideJ48_mem_conjClass_iff {G : Type} [Group G] (z x : G) :
    x ∈ CFSG.ASVolI.ChIJK.conjClass z ↔ IsConj z x := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩

private theorem burnsideJ48_card_five {G : Type} [Group G] [Finite G] {H B : Subgroup G}
    (hH : Nat.card H = 2 ^ 11 * 120) (hB : CFSG.ASVolI.ChIJK.IsSylowIn 5 B H) :
    Nat.card B = 5 := by
  obtain ⟨hBH, hBp, hidx⟩ := hB
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have h := Subgroup.index_mul_card (B.subgroupOf H)
  rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hBH, hn, hH] at h
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at h
      apply hidx
      rw [h]
      norm_num
    · rfl
    · exfalso
      have h25 : 25 ∣ (B.subgroupOf H).index * 5 ^ (n + 2) :=
        Dvd.dvd.mul_left (by
          rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
          exact pow_dvd_pow 5 (by omega)) _
      rw [h] at h25
      norm_num at h25
  rw [hn, hn1, pow_one]

end BurnsideJ48Final

end BurnsideJ48

section

theorem as_J_4_8 : J_4_8 := by
  intro G _ _ L V T V2 B5 X g v a z u _ hS
  have hRu := hS.setup.ru
  obtain ⟨M, -, hMT⟩ := hRu.exists_ruDataM CFSG.Quasithin.RuType.stUnique
  have hH : Nat.card (CFSG.ASVolI.ChIJK.HRu T) = 2 ^ 11 * 120 := by
    rw [hRu.HRu_eq_ruH, ← hMT]
    exact M.toRuData.card_H
  have hzM : z = M.z := by
    refine burnsideJ48_eq_z M ?_
    rw [hMT, ← hRu.ZRu_eq_ruZ]
    exact hS.z_gen
  have hB5card : Nat.card B5 = 5 := burnsideJ48_card_five hH hS.setup.b5.1
  have hz2 : z * z = 1 := by rw [hzM]; exact M.z_mul_self
  have hB5z : ∀ x ∈ B5, z * x * z⁻¹ = x := by
    intro x hx
    have hxH : x ∈ CFSG.Quasithin.RuType.ruH M.T := by
      rw [hMT, ← hRu.HRu_eq_ruH]
      exact hS.setup.b5.1.1 hx
    have h1 := M.mem_H_iff_comm.mp hxH
    rw [hzM]
    calc M.z * x * M.z⁻¹ = (x * M.z) * M.z⁻¹ := by rw [h1]
      _ = x := by group
  obtain ⟨h, -, hu⟩ := hS.u_x4
  have hu2 : u * u = 1 := by
    rw [hu]
    have e : (h : G) * z * (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) =
        (h : G) * (z * z) * (h : G)⁻¹ := by group
    rw [e, hz2]
    group
  have hzu : IsConj z u := isConj_iff.mpr ⟨h, hu.symm⟩
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hB5u : ∀ x ∈ B5, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have h1 := hS.u_inv.2 x hx
    rw [hui] at h1 ⊢
    exact h1
  obtain ⟨-, hF1⟩ := as_J_4_6 G L V T hRu V2 hS.setup.v2 g hS.setup.g_mem.1 hS.setup.g_mem.2 v
    hS.setup.v_mem.1 hS.setup.v_mem.2 B5 hS.setup.b5.1 hS.setup.b5.2 X hS.setup.x3 a
    hS.setup.a_choice hS.setup.a_norm hS.setup.q5_norm
  have hzZ : z ∈ CFSG.ASVolI.ChIJK.ZRu T := by
    rw [← hS.z_gen]
    exact Subgroup.mem_zpowers z
  rw [← hF1] at hzZ
  have huF1 : u ∈ CFSG.ASVolI.ChIJK.F1Ru L V V2 T a B5 := by
    unfold CFSG.ASVolI.ChIJK.F1Ru
    exact Subgroup.mem_sup_left hS.u_TF
  have huz : u * z = z * u := by
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzZ
    have h1 := Subgroup.mem_center_iff.mp hw ⟨u, huF1⟩
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    have hwz' : (w : G) = z := hwz
    rw [hwz'] at h2
    exact h2
  have hzc : z ∈ CFSG.ASVolI.ChIJK.conjClass z := ⟨1, by group⟩
  have huc : u ∈ CFSG.ASVolI.ChIJK.conjClass z := (burnsideJ48_mem_conjClass_iff z u).mpr hzu
  have hne : u * z ≠ 1 := by
    intro h1
    have huz' : u = z := by
      calc u = u * (z * z) := by rw [hz2]; group
        _ = (u * z) * z := by group
        _ = z := by rw [h1]; group
    obtain ⟨x, hx, hx1⟩ := burnsideJ48_exists_ne_one hB5card
    apply hx1
    have e1 := hB5z x hx
    have e2 := hB5u x hx
    rw [huz'] at e2
    have h3 : x = x⁻¹ := e1.symm.trans e2
    refine burnsideJ48_eq_one_of_sq (burnsideJ48_pow_five hB5card hx) ?_
    calc x * x = x * x⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel x
  have hmem := as_J_3_2 G L V T hRu z hS.z_gen u huc z hzc huz hne
  have hzuz : IsConj z (u * z) := (burnsideJ48_mem_conjClass_iff z _).mp hmem
  have hLS : ∀ (c : G) (Bc : Subgroup G), IsConj z c → Nat.card Bc = 5 →
      Bc ≤ Subgroup.centralizer ({c} : Set G) → burnsideJ48_LS z c Bc := by
    intro c Bc hc hB hBc
    rw [hzM] at hc ⊢
    exact burnsideJ48_LS_of_isConj M hc hB hBc
  exact burnsideJ48_main z u B5 hLS hz2 hu2 huz hzu hzuz hB5card hB5z hB5u

end

@[expose] def J_4_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T V2 B5 X : Subgroup G) (g v a z u : G) (I : Subgroup G),
    RuUSetup G L V T V2 B5 X g v a z u I →
      (BzPRu B5 z u ≠ O5N (BuzPRu B5 z u) ⊓ Subgroup.centralizer ({z} : Set G) ∧
        BsetRu B5 z u ⊆ CgonRu B5 z u ∧
        Nonempty (commGraphOn (CgonRu B5 z u) ≃g SimpleGraph.cycleGraph 12) ∧
        ∀ B1 B2 : ↥(CgonRu B5 z u),
          ((commGraphOn (CgonRu B5 z u)).dist B1 B2 = 2 →
            IsPOnePlusTwoGroup 5 ↥((B1 : Subgroup G) ⊔ (B2 : Subgroup G))) ∧
          ((commGraphOn (CgonRu B5 z u)).dist B1 B2 = 3 →
            CFSG.Quasithin.IsSL2 5 ↥((B1 : Subgroup G) ⊔ (B2 : Subgroup G)))) ∧
      ((∀ w ∈ WBI (CgonRu B5 z u) I, ∀ B ∈ CgonRu B5 z u,
          CFSG.conjugate B w ∈ CgonRu B5 z u) ∧
        {w | w ∈ WBI (CgonRu B5 z u) I ∧ ∀ B ∈ CgonRu B5 z u, CFSG.conjugate B w = B} =
          (I : Set G) ∧
        ∀ σ : commGraphOn (CgonRu B5 z u) ≃g commGraphOn (CgonRu B5 z u),
          ∃ w ∈ WBI (CgonRu B5 z u) I,
            ∀ B : ↥(CgonRu B5 z u), (σ B : Subgroup G) = CFSG.conjugate (B : Subgroup G) w)

@[expose] def J_4_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T V2 B5 X : Subgroup G) (g v a z u : G) (I : Subgroup G),
    RuUSetup G L V T V2 B5 X g v a z u I →
      Nonempty (EgonGraph (EsetRu (F1Ru L V V2 T a B5) z u) z u ≃g SimpleGraph.cycleGraph 6)

end CFSG.ASVolI
