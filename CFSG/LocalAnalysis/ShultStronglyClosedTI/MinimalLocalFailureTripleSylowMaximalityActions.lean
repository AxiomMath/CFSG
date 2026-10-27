module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]

@[expose] def actionCosetEquiv (htrans : MulAction.IsPretransitive G Ω) (alpha : Ω) :
    (G ⧸ MulAction.stabilizer G alpha) ≃ Ω :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer G alpha)
    ⟨MulAction.injective_ofQuotientStabilizer G alpha, fun omega => by
      obtain ⟨g, hg⟩ := htrans.exists_smul_eq alpha omega
      exact ⟨QuotientGroup.mk g, hg⟩⟩

theorem actionCosetEquiv_mk (htrans : MulAction.IsPretransitive G Ω)
    (alpha : Ω) (g : G) :
    actionCosetEquiv htrans alpha (QuotientGroup.mk g) = g • alpha := rfl

theorem actionCosetEquiv_smul (htrans : MulAction.IsPretransitive G Ω)
    (alpha : Ω) (g : G) (omega : G ⧸ MulAction.stabilizer G alpha) :
    actionCosetEquiv htrans alpha (g • omega) =
      g • actionCosetEquiv htrans alpha omega :=
  MulAction.ofQuotientStabilizer_smul G alpha g omega

theorem actionCosetEquiv_stabilizer (htrans : MulAction.IsPretransitive G Ω)
    (alpha : Ω) (omega : G ⧸ MulAction.stabilizer G alpha) :
    MulAction.stabilizer G omega =
      MulAction.stabilizer G (actionCosetEquiv htrans alpha omega) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rw [← actionCosetEquiv_smul]
  exact (actionCosetEquiv htrans alpha).injective.eq_iff.symm

def actionCosetFixedEquiv (htrans : MulAction.IsPretransitive G Ω)
    (alpha : Ω) (Q : Subgroup G) :
    {omega : G ⧸ MulAction.stabilizer G alpha //
      omega ∈ fixedPointsOfSubgroup G (G ⧸ MulAction.stabilizer G alpha) Q} ≃
      {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω Q} where
  toFun omega := ⟨actionCosetEquiv htrans alpha omega, by
    intro q hq
    rw [← actionCosetEquiv_smul, omega.property q hq]⟩
  invFun omega := ⟨(actionCosetEquiv htrans alpha).symm omega, by
    intro q hq
    apply (actionCosetEquiv htrans alpha).injective
    rw [actionCosetEquiv_smul, Equiv.apply_symm_apply, omega.property q hq]⟩
  left_inv omega := by
    apply Subtype.ext
    exact (actionCosetEquiv htrans alpha).symm_apply_apply omega
  right_inv omega := by
    apply Subtype.ext
    exact (actionCosetEquiv htrans alpha).apply_symm_apply omega

theorem actionCoset_two_pretransitive_iff
    (htrans : MulAction.IsPretransitive G Ω) (alpha : Ω) :
    MulAction.IsMultiplyPretransitive G (G ⧸ MulAction.stabilizer G alpha) 2 ↔
      MulAction.IsMultiplyPretransitive G Ω 2 := by
  let e := actionCosetEquiv htrans alpha
  constructor
  · intro htwo
    rw [MulAction.is_two_pretransitive_iff] at htwo ⊢
    intro a b c d hab hcd
    obtain ⟨g, hga, hgb⟩ := htwo
      (e.symm.injective.ne hab) (e.symm.injective.ne hcd)
    refine ⟨g, ?_, ?_⟩
    · have h := congrArg e hga
      simpa [e, actionCosetEquiv_smul] using h
    · have h := congrArg e hgb
      simpa [e, actionCosetEquiv_smul] using h
  · intro htwo
    rw [MulAction.is_two_pretransitive_iff] at htwo ⊢
    intro a b c d hab hcd
    obtain ⟨g, hga, hgb⟩ := htwo (e.injective.ne hab) (e.injective.ne hcd)
    refine ⟨g, e.injective ?_, e.injective ?_⟩
    · simpa [e, actionCosetEquiv_smul] using hga
    · simpa [e, actionCosetEquiv_smul] using hgb

def fixedConjEquiv (Q : Subgroup G) (g : G) :
    {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω Q} ≃
      {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω (Q.conjBy g)} where
  toFun omega := ⟨g • (omega : Ω), by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
    change (g * q * g⁻¹) • (g • (omega : Ω)) = g • (omega : Ω)
    simpa [mul_smul] using congrArg (fun a : Ω => g • a) (omega.property q hq)⟩
  invFun omega := ⟨g⁻¹ • (omega : Ω), by
    intro q hq
    have h := omega.property ((MulAut.conj g) q)
      (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hq)
    simpa [MulAut.conj_apply, mul_smul] using congrArg (fun a : Ω => g⁻¹ • a) h⟩
  left_inv omega := by apply Subtype.ext; exact inv_smul_smul g (omega : Ω)
  right_inv omega := by apply Subtype.ext; exact smul_inv_smul g (omega : Ω)

theorem exists_maximal_three_fixed_overgroup [Finite G]
    (p : ℕ) (P : Subgroup G) (hP : IsPGroup p P)
    (hthree : 2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P}) :
    ∃ Q : Subgroup G, P ≤ Q ∧
      Maximal (fun R : Subgroup G => IsPGroup p R ∧
        2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R}) Q := by
  let family : Set (Subgroup G) := {Q | P ≤ Q ∧ IsPGroup p Q ∧
    2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω Q}}
  obtain ⟨Q, hQ⟩ := (Set.toFinite family).exists_maximal
    (show family.Nonempty from ⟨P, le_rfl, hP, hthree⟩)
  refine ⟨Q, hQ.1.1, ⟨hQ.1.2, ?_⟩⟩
  intro R hR hQR
  exact hQ.2 ⟨hQ.1.1.trans hQR, hR⟩ hQR

theorem maximal_three_fixed_conj [Finite G] (p : ℕ) (P : Subgroup G) (g : G)
    (hmax : Maximal (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R}) P) :
    Maximal (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R})
        (P.conjBy g) := by
  have hcard (R : Subgroup G) (x : G) :
      Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω (R.conjBy x)} =
        Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R} :=
    (Nat.card_congr (fixedConjEquiv (Ω := Ω) R x)).symm
  refine ⟨⟨hmax.1.1.map (MulAut.conj g).toMonoidHom, ?_⟩, ?_⟩
  · rw [hcard]
    exact hmax.1.2
  · intro R hR hPR
    have hPback : P ≤ R.conjBy g⁻¹ := by
      have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hPR
      change (P.conjBy g).conjBy g⁻¹ ≤ R.conjBy g⁻¹ at h
      simpa [Subgroup.conjBy_conjBy, Subgroup.conjBy_one] using h
    have hRback : IsPGroup p (R.conjBy g⁻¹) ∧
        2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω (R.conjBy g⁻¹)} :=
      ⟨hR.1.map (MulAut.conj g⁻¹).toMonoidHom, by rw [hcard]; exact hR.2⟩
    have hback := hmax.2 hRback hPback
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hback
    change (R.conjBy g⁻¹).conjBy g ≤ P.conjBy g at h
    simpa [Subgroup.conjBy_conjBy, Subgroup.conjBy_one] using h

end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
