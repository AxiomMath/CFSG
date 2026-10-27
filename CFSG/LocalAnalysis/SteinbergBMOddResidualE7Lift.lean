module

public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBM

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_mulEquiv_E7_inner_diagonal_fixed
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ n)
    [CharP (AlgebraicClosure F) p] {α : MulAut (adjointGroup .E7 F)} {g : adjointGroup .E7 F}
    {a : Fin Tag.E7.rank → Fˣ}
    (hαg : ∀ h : adjointGroup .E7 F, (α h : ModGL .E7 F) =
      (g : ModGL .E7 F) * rootDiagUnit .E7 a * h * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 F)⁻¹)
    (hα : α ^ 2 = 1) :
    ∃ x ∈ fixedPointsIn (adjointGroup .E7 (AlgebraicClosure F))
        (frobTwistGL .E7 (AlgebraicClosure F) p n 1),
      x ^ 2 = 1 ∧
        Nonempty (↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 F))) ≃*
          ↥(⁅fixedPointsIn (adjointGroup .E7 (AlgebraicClosure F))
              (frobTwistGL .E7 (AlgebraicClosure F) p n 1),
            fixedPointsIn (adjointGroup .E7 (AlgebraicClosure F))
              (frobTwistGL .E7 (AlgebraicClosure F) p n 1)⁆ ⊓ Subgroup.centralizer {x})) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (Fact.out : p.Prime) hn hF
  have hK : Odd (Nat.card F) := by
    rw [hF]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  let L := AlgebraicClosure F
  let ι := algebraMap F L
  let Fr := iterateFrobenius L p n
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    change iterateFrobenius L p n c = _
    rw [iterateFrobenius_def, hF]
  have hFrι : ∀ c : F, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  let b : Fin Tag.E7.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i)
  set x := baseChangeGL ι (g : ModGL .E7 F) * rootDiagUnit .E7 b with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness .E7 F hK L ι
  have hgG : baseChangeGL ι (g : ModGL .E7 F) ∈ adjointGroup .E7 L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup .E7 L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift .E7 L b).1
  have hdb : baseChangeGL ι (rootDiagUnit .E7 a) = rootDiagUnit .E7 b :=
    baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup .E7 F,
      x * baseChangeGL ι (h : ModGL .E7 F) * x⁻¹ = baseChangeGL ι (α h : ModGL .E7 F) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E7 F hK L Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit .E7 b) = rootDiagUnit .E7 b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup .E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup .E7 F) => φ h) hα
    simpa [sq] using this
  have hx2 : x ^ 2 = 1 := by
    refine hfaith _ (pow_mem hxG 2) fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * baseChangeGL ι h * x⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * x * baseChangeGL ι h =
        (x * (x * baseChangeGL ι h * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = baseChangeGL ι h * (x * x) := by rw [h1, h2]
  have hF1 : frobTwistGL .E7 L p n 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hRR : fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p n 1) =
      adjointGroup .E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [hF1]
  have hY : ⁅fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p n 1),
      fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p n 1)⁆ ⊓
        Subgroup.centralizer {x} =
      (adjointGroup .E7 F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} := by
    rw [hRR, hder]
  let φ : adjointGroup .E7 F →* ModGL .E7 L := (baseChangeGL ι).comp (adjointGroup .E7 F).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 F))).map φ =
      (adjointGroup .E7 F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL .E7 F) * x = x * baseChangeGL ι (c : ModGL .E7 F)
      calc baseChangeGL ι (c : ModGL .E7 F) * x =
          (x * baseChangeGL ι (c : ModGL .E7 F) * x⁻¹) * x := by rw [h1]
        _ = x * baseChangeGL ι (c : ModGL .E7 F) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * baseChangeGL ι c * x⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  exact ⟨x, hRR ▸ hxR, hx2, ⟨(Subgroup.equivMapOfInjective _ φ hφ).trans
    (MulEquiv.subgroupCongr (hmap.trans hY.symm))⟩⟩

end CFSG.LocalAnalysis.SteinbergBM
