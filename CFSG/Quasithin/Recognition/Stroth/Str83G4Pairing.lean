module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Q1Nat2
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5Q
public import CFSG.RepresentationTheory.SzMartineau.LemmaSix3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open CFSG.QuasithinUnique.Setup.X7 CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open CFSG.CGT.PushingUpLit.SolKNA
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

private noncomputable def str83G4PairT {L1 L2 S : Subgroup G}
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (b c : ↥(Q1 L1 L2 S)) :
    Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)) :=
  Additive.ofMul (Ch3z.chiefIota hNL3 ⟨⁅(b : G), (c : G)⁆, hcomm b c⟩)

private theorem str83G4PairT_apply {L1 L2 S : Subgroup G}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (b c : ↥(Q1 L1 L2 S)) :
    str83G4PairT hNL3 hcomm b c =
      Additive.ofMul (Ch3z.chiefIota hNL3 ⟨⁅(b : G), (c : G)⁆, hcomm b c⟩) := rfl


private theorem str83G4PairT_zero_left {L1 L2 S : Subgroup G}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    {b : ↥(Q1 L1 L2 S)}
    (hb : b ∈ (str83X L1 L2 S).subgroupOf (Q1 L1 L2 S))
    (c : ↥(Q1 L1 L2 S)) :
    str83G4PairT hNL3 hcomm b c = 0 := by
  have hbz : ⁅(b : G), (c : G)⁆ ∈ Z1 L1 L2 S :=
    hQX (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hb) c.2)
  have hι : Ch3z.chiefIota hNL3 ⟨⁅(b : G), (c : G)⁆, hcomm b c⟩ = 1 :=
    (Ch3z.chiefIota_eq_one_iff hNL3 _).mpr hbz
  rw [str83G4PairT_apply, hι]
  rfl

private theorem str83G4PairT_zero_right {L1 L2 S : Subgroup G}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (b : ↥(Q1 L1 L2 S)) {c : ↥(Q1 L1 L2 S)}
    (hc : c ∈ (str83X L1 L2 S).subgroupOf (Q1 L1 L2 S)) :
    str83G4PairT hNL3 hcomm b c = 0 := by
  have hQX' : ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ ≤ Z1 L1 L2 S := by
    rwa [Subgroup.commutator_comm] at hQX
  have hbz : ⁅(b : G), (c : G)⁆ ∈ Z1 L1 L2 S :=
    hQX' (Subgroup.commutator_mem_commutator b.2 (Subgroup.mem_subgroupOf.mp hc))
  have hι : Ch3z.chiefIota hNL3 ⟨⁅(b : G), (c : G)⁆, hcomm b c⟩ = 1 :=
    (Ch3z.chiefIota_eq_one_iff hNL3 _).mpr hbz
  rw [str83G4PairT_apply, hι]
  rfl

private theorem str83G4PairT_add_right (L1 L2 S : Subgroup G)
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hNX : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (a b c : ↥(Q1 L1 L2 S)) :
    str83G4PairT hNL3 hcomm a (b * c) =
      str83G4PairT hNL3 hcomm a b + str83G4PairT hNL3 hcomm a c := by
  have hQX' : ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ ≤ Z1 L1 L2 S := by
    rwa [Subgroup.commutator_comm] at hQX
  have hbcX : (b : G) * ⁅(a : G), (c : G)⁆ * (b : G)⁻¹ ∈ str83X L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hNX b.2) _).mp (hcomm a c)
  have hι1 : Ch3z.chiefIota hNL3 ⟨⁅(a : G), ((b * c : ↥(Q1 L1 L2 S)) : G)⁆,
        hcomm a (b * c)⟩ =
      Ch3z.chiefIota hNL3 (⟨⁅(a : G), (b : G)⁆, hcomm a b⟩ *
        ⟨(b : G) * ⁅(a : G), (c : G)⁆ * (b : G)⁻¹, hbcX⟩) := by
    refine mul_inv_eq_one.mp ((map_mul_inv _ _ _).symm.trans
      ((Ch3z.chiefIota_eq_one_iff hNL3 _).mpr ?_))
    push_cast
    rw [commutatorElement_mul_right_eq_mul_conj]
    group
    exact (Z1 L1 L2 S).one_mem
  have hι2 : Ch3z.chiefIota hNL3
        ⟨(b : G) * ⁅(a : G), (c : G)⁆ * (b : G)⁻¹, hbcX⟩ =
      Ch3z.chiefIota hNL3 ⟨⁅(a : G), (c : G)⁆, hcomm a c⟩ := by
    refine mul_inv_eq_one.mp ((map_mul_inv _ _ _).symm.trans
      ((Ch3z.chiefIota_eq_one_iff hNL3 _).mpr ?_))
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hQX' (Subgroup.commutator_mem_commutator b.2 (hcomm a c))
  have hsplit : str83G4PairT hNL3 hcomm a (b * c) =
      Additive.ofMul (Ch3z.chiefIota hNL3 (⟨⁅(a : G), (b : G)⁆, hcomm a b⟩ *
        ⟨(b : G) * ⁅(a : G), (c : G)⁆ * (b : G)⁻¹, hbcX⟩)) := by
    rw [str83G4PairT_apply, hι1]
  rw [hsplit, map_mul,
    str83G4PairT_apply (hNL3 := hNL3) (hcomm := hcomm) a b,
    str83G4PairT_apply (hNL3 := hNL3) (hcomm := hcomm) a c, hι2]
  rfl

private theorem str83G4PairT_add_left (L1 L2 S : Subgroup G)
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hNX : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (hE3 : IsElemAbelian 2 (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)))
    (a b c : ↥(Q1 L1 L2 S)) :
    str83G4PairT hNL3 hcomm (a * b) c =
      str83G4PairT hNL3 hcomm a c + str83G4PairT hNL3 hcomm b c := by
  have hcommAdd : ∀ x y : Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)),
      x + y = y + x := by
    intro x y
    apply Additive.toMul.injective
    exact hE3.1.is_comm.comm (Additive.toMul x) (Additive.toMul y)
  have hQX' : ⁅Q1 L1 L2 S, str83X L1 L2 S⁆ ≤ Z1 L1 L2 S := by
    rwa [Subgroup.commutator_comm] at hQX
  have hacX : (a : G) * ⁅(b : G), (c : G)⁆ * (a : G)⁻¹ ∈ str83X L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hNX a.2) _).mp (hcomm b c)
  have hι1 : Ch3z.chiefIota hNL3 ⟨⁅((a * b : ↥(Q1 L1 L2 S)) : G), (c : G)⁆,
        hcomm (a * b) c⟩ =
      Ch3z.chiefIota hNL3 (⟨(a : G) * ⁅(b : G), (c : G)⁆ * (a : G)⁻¹, hacX⟩ *
        ⟨⁅(a : G), (c : G)⁆, hcomm a c⟩) := by
    refine mul_inv_eq_one.mp ((map_mul_inv _ _ _).symm.trans
      ((Ch3z.chiefIota_eq_one_iff hNL3 _).mpr ?_))
    push_cast
    rw [commutatorElement_mul_left_eq_conj_mul]
    group
    exact (Z1 L1 L2 S).one_mem
  have hι2 : Ch3z.chiefIota hNL3
        ⟨(a : G) * ⁅(b : G), (c : G)⁆ * (a : G)⁻¹, hacX⟩ =
      Ch3z.chiefIota hNL3 ⟨⁅(b : G), (c : G)⁆, hcomm b c⟩ := by
    refine mul_inv_eq_one.mp ((map_mul_inv _ _ _).symm.trans
      ((Ch3z.chiefIota_eq_one_iff hNL3 _).mpr ?_))
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hQX' (Subgroup.commutator_mem_commutator a.2 (hcomm b c))
  have hsplit : str83G4PairT hNL3 hcomm (a * b) c =
      Additive.ofMul (Ch3z.chiefIota hNL3 (⟨(a : G) * ⁅(b : G), (c : G)⁆ * (a : G)⁻¹,
        hacX⟩ * ⟨⁅(a : G), (c : G)⁆, hcomm a c⟩)) := by
    rw [str83G4PairT_apply, hι1]
  rw [hsplit, map_mul,
    str83G4PairT_apply (hNL3 := hNL3) (hcomm := hcomm) a c,
    str83G4PairT_apply (hNL3 := hNL3) (hcomm := hcomm) b c, hι2]
  exact hcommAdd _ _

private theorem str83G4PairIota_surjective {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G)) :
    Function.Surjective
      (fun a : ↥(Q1 L1 L2 S) =>
        Additive.ofMul (Ch3z.chiefIota hNL1 a)) := by
  intro v
  obtain ⟨a, ha⟩ := Ch3z.chiefIota_surjective hNL1 (Additive.toMul v)
  refine ⟨a, ?_⟩
  change Additive.ofMul (Ch3z.chiefIota hNL1 a) = v
  rw [ha]
  rfl

private noncomputable def str83G4PairPre {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (v : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    ↥(Q1 L1 L2 S) :=
  Function.surjInv (str83G4PairIota_surjective hNL1) v

private theorem str83G4PairPre_spec {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (v : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    Additive.ofMul (Ch3z.chiefIota hNL1 (str83G4PairPre hNL1 v)) = v :=
  Function.surjInv_eq (str83G4PairIota_surjective hNL1) v


private theorem str83G4PairPre_mul_mem {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (v w : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    (((str83G4PairPre hNL1 (v + w))⁻¹ *
        (str83G4PairPre hNL1 v * str83G4PairPre hNL1 w) : ↥(Q1 L1 L2 S)) : G) ∈
      str83X L1 L2 S := by
  have h1 : Ch3z.chiefIota hNL1 (str83G4PairPre hNL1 (v + w)) =
      Additive.toMul (v + w) :=
    congrArg Additive.toMul (str83G4PairPre_spec hNL1 (v + w))
  have h2 : Ch3z.chiefIota hNL1 (str83G4PairPre hNL1 v) = Additive.toMul v :=
    congrArg Additive.toMul (str83G4PairPre_spec hNL1 v)
  have h3 : Ch3z.chiefIota hNL1 (str83G4PairPre hNL1 w) = Additive.toMul w :=
    congrArg Additive.toMul (str83G4PairPre_spec hNL1 w)
  have hzero : Ch3z.chiefIota hNL1
      ((str83G4PairPre hNL1 (v + w))⁻¹ *
        (str83G4PairPre hNL1 v * str83G4PairPre hNL1 w)) = 1 := by
    rw [map_mul, map_inv, map_mul, h1, h2, h3]
    rw [show Additive.toMul (v + w) = Additive.toMul v * Additive.toMul w from rfl]
    group
  exact (Ch3z.chiefIota_eq_one_iff hNL1 _).mp hzero

private theorem str83G4PairT_eq_of_left_mem_X {L1 L2 S : Subgroup G}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hNX : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (hE3 : IsElemAbelian 2 (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)))
    {a a' : ↥(Q1 L1 L2 S)} {b : ↥(Q1 L1 L2 S)}
    (h : (((a⁻¹ * a' : ↥(Q1 L1 L2 S)) : G) ∈ str83X L1 L2 S)) :
    str83G4PairT hNL3 hcomm a' b = str83G4PairT hNL3 hcomm a b := by
  have ha' : a' = a * (a⁻¹ * a') := by
    apply Subtype.ext
    group
  rw [ha']
  calc str83G4PairT hNL3 hcomm (a * (a⁻¹ * a')) b
      = str83G4PairT hNL3 hcomm a b +
          str83G4PairT hNL3 hcomm (a⁻¹ * a') b :=
        str83G4PairT_add_left L1 L2 S hNL3 hcomm hQX hNX hE3 a (a⁻¹ * a') b
    _ = str83G4PairT hNL3 hcomm a b + 0 := by
        rw [str83G4PairT_zero_left hQX (Subgroup.mem_subgroupOf.mpr h) b]
    _ = str83G4PairT hNL3 hcomm a b := add_zero _

private theorem str83G4PairT_eq_of_right_mem_X {L1 L2 S : Subgroup G}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hNX : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    {a : ↥(Q1 L1 L2 S)} {b b' : ↥(Q1 L1 L2 S)}
    (h : (((b⁻¹ * b' : ↥(Q1 L1 L2 S)) : G) ∈ str83X L1 L2 S)) :
    str83G4PairT hNL3 hcomm a b' = str83G4PairT hNL3 hcomm a b := by
  have hb' : b' = b * (b⁻¹ * b') := by
    apply Subtype.ext
    group
  rw [hb']
  calc str83G4PairT hNL3 hcomm a (b * (b⁻¹ * b'))
      = str83G4PairT hNL3 hcomm a b +
          str83G4PairT hNL3 hcomm a (b⁻¹ * b') :=
        str83G4PairT_add_right L1 L2 S hNL3 hcomm hQX hNX a b (b⁻¹ * b')
    _ = str83G4PairT hNL3 hcomm a b + 0 := by
        rw [str83G4PairT_zero_right hQX a (Subgroup.mem_subgroupOf.mpr h)]
    _ = str83G4PairT hNL3 hcomm a b := add_zero _

private noncomputable def str83G4PairBarFun {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (v w : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)) :=
  str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v) (str83G4PairPre hNL1 w)

private theorem str83G4PairBarFun_apply {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (v w : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    str83G4PairBarFun hNL1 hNL3 hcomm v w =
      str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v) (str83G4PairPre hNL1 w) := rfl


private theorem str83G4PairBarFun_add_right {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (v w₁ w₂ : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    str83G4PairBarFun hNL1 hNL3 hcomm v (w₁ + w₂) =
      str83G4PairBarFun hNL1 hNL3 hcomm v w₁ +
        str83G4PairBarFun hNL1 hNL3 hcomm v w₂ := by
  have hpre := str83G4PairPre_mul_mem hNL1 w₁ w₂
  have hpre' : (((str83G4PairPre hNL1 w₁ * str83G4PairPre hNL1 w₂)⁻¹ *
      str83G4PairPre hNL1 (w₁ + w₂) : ↥(Q1 L1 L2 S)) : G) ∈ str83X L1 L2 S := by
    have h1 : ((str83G4PairPre hNL1 w₁ * str83G4PairPre hNL1 w₂)⁻¹ *
        str83G4PairPre hNL1 (w₁ + w₂) : ↥(Q1 L1 L2 S)) =
        ((str83G4PairPre hNL1 (w₁ + w₂))⁻¹ *
          (str83G4PairPre hNL1 w₁ * str83G4PairPre hNL1 w₂) : ↥(Q1 L1 L2 S))⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact (str83X L1 L2 S).inv_mem hpre
  calc str83G4PairBarFun hNL1 hNL3 hcomm v (w₁ + w₂)
      = str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v)
          (str83G4PairPre hNL1 (w₁ + w₂)) :=
        str83G4PairBarFun_apply hNL1 hNL3 hcomm v (w₁ + w₂)
    _ = str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v)
          (str83G4PairPre hNL1 w₁ * str83G4PairPre hNL1 w₂) :=
        str83G4PairT_eq_of_right_mem_X (hNL3 := hNL3) (hcomm := hcomm) hQX hNL1 hpre' 
    _ = str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v) (str83G4PairPre hNL1 w₁) +
          str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v) (str83G4PairPre hNL1 w₂) :=
        str83G4PairT_add_right L1 L2 S hNL3 hcomm hQX hNL1
          (str83G4PairPre hNL1 v) (str83G4PairPre hNL1 w₁) (str83G4PairPre hNL1 w₂)
    _ = str83G4PairBarFun hNL1 hNL3 hcomm v w₁ +
          str83G4PairBarFun hNL1 hNL3 hcomm v w₂ := by
        rw [str83G4PairBarFun_apply, str83G4PairBarFun_apply]

private theorem str83G4PairBarFun_add_left {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hE3 : IsElemAbelian 2 (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)))
    (v₁ v₂ w : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    str83G4PairBarFun hNL1 hNL3 hcomm (v₁ + v₂) w =
      str83G4PairBarFun hNL1 hNL3 hcomm v₁ w +
        str83G4PairBarFun hNL1 hNL3 hcomm v₂ w := by
  have hpre := str83G4PairPre_mul_mem hNL1 v₁ v₂
  have hpre' : (((str83G4PairPre hNL1 v₁ * str83G4PairPre hNL1 v₂)⁻¹ *
      str83G4PairPre hNL1 (v₁ + v₂) : ↥(Q1 L1 L2 S)) : G) ∈ str83X L1 L2 S := by
    have h1 : ((str83G4PairPre hNL1 v₁ * str83G4PairPre hNL1 v₂)⁻¹ *
        str83G4PairPre hNL1 (v₁ + v₂) : ↥(Q1 L1 L2 S)) =
        ((str83G4PairPre hNL1 (v₁ + v₂))⁻¹ *
          (str83G4PairPre hNL1 v₁ * str83G4PairPre hNL1 v₂) : ↥(Q1 L1 L2 S))⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact (str83X L1 L2 S).inv_mem hpre
  calc str83G4PairBarFun hNL1 hNL3 hcomm (v₁ + v₂) w
      = str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 (v₁ + v₂))
          (str83G4PairPre hNL1 w) :=
        str83G4PairBarFun_apply hNL1 hNL3 hcomm (v₁ + v₂) w
    _ = str83G4PairT hNL3 hcomm
          (str83G4PairPre hNL1 v₁ * str83G4PairPre hNL1 v₂)
          (str83G4PairPre hNL1 w) :=
        str83G4PairT_eq_of_left_mem_X (hNL3 := hNL3) (hcomm := hcomm) hQX hNL1 hE3 hpre' 
    _ = str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v₁) (str83G4PairPre hNL1 w) +
          str83G4PairT hNL3 hcomm (str83G4PairPre hNL1 v₂) (str83G4PairPre hNL1 w) :=
        str83G4PairT_add_left L1 L2 S hNL3 hcomm hQX hNL1 hE3
          (str83G4PairPre hNL1 v₁) (str83G4PairPre hNL1 v₂) (str83G4PairPre hNL1 w)
    _ = str83G4PairBarFun hNL1 hNL3 hcomm v₁ w +
          str83G4PairBarFun hNL1 hNL3 hcomm v₂ w := by
        rw [str83G4PairBarFun_apply, str83G4PairBarFun_apply]

private theorem str83G4PairBarFun_iota {L1 L2 S : Subgroup G}
    (hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G))
    (hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S)
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (hE3 : IsElemAbelian 2 (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)))
    (a b : ↥(Q1 L1 L2 S)) :
    str83G4PairBarFun hNL1 hNL3 hcomm
        (Additive.ofMul (Ch3z.chiefIota hNL1 a))
        (Additive.ofMul (Ch3z.chiefIota hNL1 b)) =
      str83G4PairT hNL3 hcomm a b := by
  have hpre1 := str83G4PairPre_spec hNL1
    (Additive.ofMul (Ch3z.chiefIota hNL1 a))
  have hpre2 := str83G4PairPre_spec hNL1
    (Additive.ofMul (Ch3z.chiefIota hNL1 b))
  have hι1 : Ch3z.chiefIota hNL1
      (str83G4PairPre hNL1 (Additive.ofMul (Ch3z.chiefIota hNL1 a))) =
      Ch3z.chiefIota hNL1 a := by
    have := congrArg Additive.toMul hpre1
    simpa using this
  have hι2 : Ch3z.chiefIota hNL1
      (str83G4PairPre hNL1 (Additive.ofMul (Ch3z.chiefIota hNL1 b))) =
      Ch3z.chiefIota hNL1 b := by
    have := congrArg Additive.toMul hpre2
    simpa using this
  have hx1 : (((str83G4PairPre hNL1
      (Additive.ofMul (Ch3z.chiefIota hNL1 a)))⁻¹ * a : ↥(Q1 L1 L2 S)) : G) ∈
      str83X L1 L2 S := by
    have h1 : Ch3z.chiefIota hNL1
        ((str83G4PairPre hNL1
          (Additive.ofMul (Ch3z.chiefIota hNL1 a)))⁻¹ * a) = 1 := by
      rw [map_mul, map_inv, hι1]
      simp
    exact (Ch3z.chiefIota_eq_one_iff hNL1 _).mp h1
  have hx2 : (((str83G4PairPre hNL1
      (Additive.ofMul (Ch3z.chiefIota hNL1 b)))⁻¹ * b : ↥(Q1 L1 L2 S)) : G) ∈
      str83X L1 L2 S := by
    have h1 : Ch3z.chiefIota hNL1
        ((str83G4PairPre hNL1
          (Additive.ofMul (Ch3z.chiefIota hNL1 b)))⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hι2]
      simp
    exact (Ch3z.chiefIota_eq_one_iff hNL1 _).mp h1
  rw [str83G4PairBarFun_apply,
    str83G4PairT_eq_of_left_mem_X (hNL3 := hNL3) (hcomm := hcomm) hQX hNL1 hE3 hx1,
    str83G4PairT_eq_of_right_mem_X (hNL3 := hNL3) (hcomm := hcomm) hQX hNL1 hx2]

private theorem str83G4PairT_conj {L1 L2 S : Subgroup G}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (hHN1 : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G))
    (hHN3 : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G))
    (h : ↥(L1 ⊔ S)) (u v : ↥(Q1 L1 L2 S)) :
    str83G4PairT hNL3 hcomm
        ⟨(h : G) * (u : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHN1 h.2) (u : G)).mp u.2⟩
        ⟨(h : G) * (v : G) * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHN1 h.2) (v : G)).mp v.2⟩ =
      Additive.ofMul (Ch3z.chiefIota hNL3
        ⟨(h : G) * ⁅(u : G), (v : G)⁆ * (h : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHN3 h.2) _).mp (hcomm u v)⟩) := by
  rw [str83G4PairT_apply]
  congr 1
  refine mul_inv_eq_one.mp ((map_mul_inv _ _ _).symm.trans
    ((Ch3z.chiefIota_eq_one_iff hNL3 _).mpr ?_))
  push_cast
  have hconj : (h : G) * (u : G) * (h : G)⁻¹ * ((h : G) * (v : G) * (h : G)⁻¹) *
        ((h : G) * (u : G) * (h : G)⁻¹)⁻¹ *
        ((h : G) * (v : G) * (h : G)⁻¹)⁻¹ =
      (h : G) * ⁅(u : G), (v : G)⁆ * (h : G)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [commutatorElement_def, hconj]
  convert (Z1 L1 L2 S).one_mem using 1
  group


private theorem str83G4PairBarFun_conj_iota {L1 L2 S : Subgroup G} {a : ℕ}
    {hHL1 : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G)}
    {hHN1 : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G)}
    {hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G)}
    {hE1 : IsElemAbelian 2
      (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))}
    {hO1 : pCoreOf 2 (L1 ⊔ S) ≤
      centralizerMod (str83X L1 L2 S) (L1 ⊔ S) (Q1 L1 L2 S)}
    {hHL3 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hHN3 : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G)}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hE3 : IsElemAbelian 2
      (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S))}
    {hO3 : pCoreOf 2 (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (h : ↥(L1 ⊔ S)) (u v : ↥(Q1 L1 L2 S)) :
    letI : CommGroup (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S)) :=
      l2ChiefSectionCommGroup hE1
    letI : Module (ZMod 2)
        (Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :=
      l2ChiefSectionModule hE1
    letI : CommGroup (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)) :=
      l2ChiefSectionCommGroup hE3
    letI : Module (ZMod 2)
        (Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S))) :=
      l2ChiefSectionModule hE3
    str83G4PairBarFun hNL1 hNL3 hcomm
        (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e (e (QuotientGroup.mk h))
          (Additive.ofMul (Ch3z.chiefIota hNL1 u)))
        (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e (e (QuotientGroup.mk h))
          (Additive.ofMul (Ch3z.chiefIota hNL1 v))) =
      sectionRep hHL3 hHN3 hNL3 hE3 hO3 e (e (QuotientGroup.mk h))
        (str83G4PairBarFun hNL1 hNL3 hcomm
          (Additive.ofMul (Ch3z.chiefIota hNL1 u))
          (Additive.ofMul (Ch3z.chiefIota hNL1 v))) := by
  letI : CommGroup (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S)) :=
    l2ChiefSectionCommGroup hE1
  letI : Module (ZMod 2)
      (Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :=
    l2ChiefSectionModule hE1
  letI : CommGroup (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)) :=
    l2ChiefSectionCommGroup hE3
  letI : Module (ZMod 2)
      (Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S))) :=
    l2ChiefSectionModule hE3
  have huQ : (h : G) * (u : G) * (h : G)⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hHN1 h.2) (u : G)).mp u.2
  have hvQ : (h : G) * (v : G) * (h : G)⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hHN1 h.2) (v : G)).mp v.2
  have huvX : (h : G) * ⁅(u : G), (v : G)⁆ * (h : G)⁻¹ ∈ str83X L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hHN3 h.2) _).mp (hcomm u v)
  rw [sectionRep_chiefIota hHL1 hHN1 hNL1 hE1 hO1 e h u huQ,
    sectionRep_chiefIota hHL1 hHN1 hNL1 hE1 hO1 e h v hvQ]
  rw [str83G4PairBarFun_iota hNL1 hNL3 hcomm hQX hE3
    ⟨(h : G) * (u : G) * (h : G)⁻¹, huQ⟩
    ⟨(h : G) * (v : G) * (h : G)⁻¹, hvQ⟩]
  rw [str83G4PairT_conj hHN1 hHN3 h u v]
  rw [str83G4PairBarFun_iota hNL1 hNL3 hcomm hQX hE3 u v]
  rw [str83G4PairT_apply]
  rw [sectionRep_chiefIota hHL3 hHN3 hNL3 hE3 hO3 e h ⟨⁅(u : G), (v : G)⁆, hcomm u v⟩ huvX]


private theorem str83G4PairBarFun_conj {L1 L2 S : Subgroup G} {a : ℕ}
    {hHL1 : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G)}
    {hHN1 : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G)}
    {hNL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G)}
    {hE1 : IsElemAbelian 2
      (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))}
    {hO1 : pCoreOf 2 (L1 ⊔ S) ≤
      centralizerMod (str83X L1 L2 S) (L1 ⊔ S) (Q1 L1 L2 S)}
    {hHL3 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hHN3 : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G)}
    {hNL3 : str83X L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)}
    {hE3 : IsElemAbelian 2
      (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S))}
    {hO3 : pCoreOf 2 (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S)}
    {hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S}
    (hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (h : ↥(L1 ⊔ S))
    (v w : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :
    letI : CommGroup (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S)) :=
      l2ChiefSectionCommGroup hE1
    letI : Module (ZMod 2)
        (Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :=
      l2ChiefSectionModule hE1
    letI : CommGroup (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)) :=
      l2ChiefSectionCommGroup hE3
    letI : Module (ZMod 2)
        (Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S))) :=
      l2ChiefSectionModule hE3
    str83G4PairBarFun hNL1 hNL3 hcomm
        (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e (e (QuotientGroup.mk h)) v)
        (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e (e (QuotientGroup.mk h)) w) =
      sectionRep hHL3 hHN3 hNL3 hE3 hO3 e (e (QuotientGroup.mk h))
        (str83G4PairBarFun hNL1 hNL3 hcomm v w) := by
  letI : CommGroup (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S)) :=
    l2ChiefSectionCommGroup hE1
  letI : Module (ZMod 2)
      (Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :=
    l2ChiefSectionModule hE1
  letI : CommGroup (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)) :=
    l2ChiefSectionCommGroup hE3
  letI : Module (ZMod 2)
      (Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S))) :=
    l2ChiefSectionModule hE3
  obtain ⟨u, rfl⟩ := str83G4PairIota_surjective hNL1 v
  obtain ⟨w, rfl⟩ := str83G4PairIota_surjective hNL1 w
  exact str83G4PairBarFun_conj_iota hQX e h u w


theorem str83G4_commutator_q1_le_z1_of_y_eq_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hYX : str83Y L1 L2 S = str83X L1 L2 S) :
    ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
  classical
  have hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S)
      (Z1 L1 L2 S) (str83X L1 L2 S) :=
    str83G4_isChiefStep_x_z1 hfr d hX hB
  have hXnc : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S) :=
    str83G4_not_twoResidual_le_centralizerMod_z1 hfr d hX hB
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hQ1H : Q1 L1 L2 S ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  have hXQ1 : str83X L1 L2 S ≤ Q1 L1 L2 S := str83X_le_q1 hfr
  have hXH : str83X L1 L2 S ≤ L1 ⊔ S := hXQ1.trans hQ1H
  have hstep1 : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S)
      (str83X L1 L2 S) (Q1 L1 L2 S) := by
    have h := str83G4_isChiefStep_q1_y hfr d hX hB
    rwa [hYX] at h
  have hquad1 : ⁅⁅Q1 L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆,
      CFSG.conjugate (str83X L1 L2 S) d.w⁆ ≤ str83X L1 L2 S := by
    have h := str83G4_commutator_commutator_q1_conjugate_x_le_y hfr d hX
    rwa [hYX] at h
  have hnc1 : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (str83X L1 L2 S) (L1 ⊔ S) (Q1 L1 L2 S) := by
    have h := str83G4_not_twoResidual_le_centralizerMod_y_q1 hfr d hX
    rwa [hYX] at h
  have hC : ∀ s : G, s ∈ CFSG.conjugate (str83X L1 L2 S) d.w ⊔ Q1 L1 L2 S ↔
      s ∈ S ∧ s ^ 2 ∈ Q1 L1 L2 S :=
    str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB
  obtain ⟨hHL1, hHN1, hNL1, hE1, hO1⟩ :=
    str83G4_sectionFacts_of_le_q1 hfr (le_rfl : Q1 L1 L2 S ≤ Q1 L1 L2 S) hstep1
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  letI : Fintype K := Fintype.ofFinite K
  have ha : 1 ≤ a := hfr.2.2.1
  obtain ⟨e, he⟩ := str83G4_exists_equiv_sylow hK hfr
  letI : CommGroup (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S)) :=
    l2ChiefSectionCommGroup hE1
  letI : Module (ZMod 2)
      (Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S))) :=
    l2ChiefSectionModule hE1
  have hnat1 : IsSzNatural
      (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e) :=
    sectionRep_isSzNatural_of_le_q1 hfr hC le_rfl hstep1 hquad1 hnc1
      hHL1 hHN1 hNL1 hE1 hO1 e he
  obtain ⟨c₁, φ₁, hφ₁⟩ := hnat1
  have hquad3 : ⁅⁅str83X L1 L2 S, CFSG.conjugate (str83X L1 L2 S) d.w⁆,
      CFSG.conjugate (str83X L1 L2 S) d.w⁆ ≤ Z1 L1 L2 S := by
    rw [str83G4_commutator_commutator_x_conjugate_eq_bot hfr d hX]
    exact bot_le
  obtain ⟨hHL3, hHN3, hNL3, hE3, hO3⟩ :=
    str83G4_sectionFacts_of_le_q1 hfr hXQ1 hXstep
  letI : CommGroup (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S)) :=
    l2ChiefSectionCommGroup hE3
  letI : Module (ZMod 2)
      (Additive (Ch3z.chiefMod (Z1 L1 L2 S) (str83X L1 L2 S))) :=
    l2ChiefSectionModule hE3
  have hnat3 : IsSzNatural
      (sectionRep hHL3 hHN3 hNL3 hE3 hO3 e) :=
    sectionRep_isSzNatural_of_le_q1 hfr hC hXQ1 hXstep hquad3 hXnc
      hHL3 hHN3 hNL3 hE3 hO3 e he
  obtain ⟨c₃, φ₃, hφ₃⟩ := hnat3
  have hcomm : ∀ b c : ↥(Q1 L1 L2 S), ⁅(b : G), (c : G)⁆ ∈ str83X L1 L2 S := by
    intro b c
    have h := str83G4_commutator_q1_q1_le_y hfr
    rw [hYX] at h
    exact h (Subgroup.commutator_mem_commutator b.2 c.2)
  have hQX : ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S :=
    str83G4_commutator_x_q1_le hfr
  let β' : (Fin 4 → K) →+ (Fin 4 → K) →+ (Fin 4 → K) :=
    AddMonoidHom.mk' (fun v =>
      AddMonoidHom.mk' (fun w =>
        φ₃ (str83G4PairBarFun hNL1 hNL3 hcomm (φ₁.symm v) (φ₁.symm w))) (by
          intro w₁ w₂
          rw [map_add (φ₁.symm),
            str83G4PairBarFun_add_right hNL1 hNL3 hcomm hQX, map_add]))
      (by
        intro v₁ v₂
        apply AddMonoidHom.ext
        intro w
        change φ₃ (str83G4PairBarFun hNL1 hNL3 hcomm
            (φ₁.symm (v₁ + v₂)) (φ₁.symm w)) =
          φ₃ (str83G4PairBarFun hNL1 hNL3 hcomm (φ₁.symm v₁) (φ₁.symm w)) +
            φ₃ (str83G4PairBarFun hNL1 hNL3 hcomm (φ₁.symm v₂) (φ₁.symm w))
        rw [map_add (φ₁.symm),
          str83G4PairBarFun_add_left hNL1 hNL3 hcomm hQX hE3, map_add])
  have hβ : ∀ (g : ↥(suzukiGroup a K)) (v w : Fin 4 → K),
      β' ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ v)
          ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ w) =
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₃)) *ᵥ β' v w := by
    intro g v w
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e.symm g)
    have hg : e (QuotientGroup.mk h) = g := by
      rw [hh, MulEquiv.apply_symm_apply]
    have hv : (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ v =
        φ₁ (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e g (φ₁.symm v)) := by
      calc (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ v
          = (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ
              φ₁ (φ₁.symm v) := by rw [AddEquiv.apply_symm_apply]
        _ = φ₁ (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e g (φ₁.symm v)) :=
            (hφ₁ g (φ₁.symm v)).symm
    have hw : (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ w =
        φ₁ (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e g (φ₁.symm w)) := by
      calc (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ w
          = (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ
              φ₁ (φ₁.symm w) := by rw [AddEquiv.apply_symm_apply]
        _ = φ₁ (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e g (φ₁.symm w)) :=
            (hφ₁ g (φ₁.symm w)).symm
    rw [hv, hw]
    change φ₃ (str83G4PairBarFun hNL1 hNL3 hcomm
        (φ₁.symm (φ₁ (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e g (φ₁.symm v))))
        (φ₁.symm (φ₁ (sectionRep hHL1 hHN1 hNL1 hE1 hO1 e g (φ₁.symm w))))) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₃)) *ᵥ
        φ₃ (str83G4PairBarFun hNL1 hNL3 hcomm (φ₁.symm v) (φ₁.symm w))
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    have hconj := str83G4PairBarFun_conj (hHL1 := hHL1) (hHN1 := hHN1) (hNL1 := hNL1)
      (hE1 := hE1) (hO1 := hO1) (hHL3 := hHL3) (hHN3 := hHN3) (hNL3 := hNL3)
      (hE3 := hE3) (hO3 := hO3) (hcomm := hcomm) hQX e h (φ₁.symm v) (φ₁.symm w)
    rw [hg] at hconj
    rw [hconj, hφ₃]
  have hβzero : β' = 0 :=
    CFSG.RepresentationTheory.SzMartineau.biadd_eq_zero_of_suzukiGroup_equivariant
      ha hK c₁ c₁ c₃ β' hβ
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  let vx : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S)) :=
    Additive.ofMul (Ch3z.chiefIota hNL1 ⟨x, hx⟩)
  let vy : Additive (Ch3z.chiefMod (str83X L1 L2 S) (Q1 L1 L2 S)) :=
    Additive.ofMul (Ch3z.chiefIota hNL1 ⟨y, hy⟩)
  have hzero : φ₃ (str83G4PairBarFun hNL1 hNL3 hcomm vx vy) = 0 := by
    have h := congrArg (fun f : (Fin 4 → K) →+ (Fin 4 → K) →+ (Fin 4 → K) =>
      f (φ₁ vx) (φ₁ vy)) hβzero
    simpa [β', vx, vy, AddEquiv.symm_apply_apply] using h
  have hpair : str83G4PairT hNL3 hcomm ⟨x, hx⟩ ⟨y, hy⟩ = 0 := by
    apply φ₃.injective
    rw [map_zero]
    have h := hzero
    rwa [str83G4PairBarFun_iota hNL1 hNL3 hcomm hQX hE3 ⟨x, hx⟩ ⟨y, hy⟩] at h
  have hι : Ch3z.chiefIota hNL3
      ⟨⁅x, y⁆, hcomm ⟨x, hx⟩ ⟨y, hy⟩⟩ = 1 := by
    have h := congrArg Additive.toMul hpair
    simpa [str83G4PairT_apply] using h
  exact (Ch3z.chiefIota_eq_one_iff hNL3 _).mp hι

theorem str83G4_y_ne_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    str83Y L1 L2 S ≠ str83X L1 L2 S := by
  intro hYX
  have hcomm : ⁅Q1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S :=
    str83G4_commutator_q1_le_z1_of_y_eq_x hfr d hX hB hYX
  refine str83G4_commutator_q1_not_le hfr d
    (str83G4_a0_sup_conjugate_q1 hfr d hX hB) ?_
  intro x hx
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    obtain ⟨hF, hBfr, ha, hSz, hL2, hZI⟩ := hfr
    exact (str83_caseI_basics hF hBfr ha hSz hL2 hZI).2.1
  have hSP2 : S ≤ P2 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hL2P2 : L2 ⊔ S ≤ P2 L1 L2 S := sup_le le_sup_left hSP2
  have hNZ2 : P2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)
  have hwz : d.w * x * d.w⁻¹ ∈ Z2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hNZ2 (hL2P2 d.hwH2)) x).mp (hZ1Z2 (hcomm hx))
  have hzQ : d.w * x * d.w⁻¹ ∈ Q1 L1 L2 S :=
    str83X_le_q1 hfr (z2_le_str83X L1 L2 S hwz)
  exact (CFSG.mem_conjugate_iff (Q1 L1 L2 S) d.w x).mpr hzQ

theorem str83G4_relIndex_x_y_eq_of_eq_one_or
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (h : (str83X L1 L2 S).relIndex (str83Y L1 L2 S) = 1 ∨
      (str83X L1 L2 S).relIndex (str83Y L1 L2 S) = 2 ^ (2 * a + 1)) :
    (str83X L1 L2 S).relIndex (str83Y L1 L2 S) = 2 ^ (2 * a + 1) := by
  rcases h with h1 | hq
  · exfalso
    have hYX : str83Y L1 L2 S = str83X L1 L2 S :=
      le_antisymm (Subgroup.relIndex_eq_one.mp h1) (str83X_le_str83Y hfr hX)
    exact str83G4_y_ne_x hfr d hX hB hYX
  · exact hq

end CFSG.Quasithin.Stroth

end
