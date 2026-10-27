module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusA6Model
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly TableBSymp CFSG.StandardType.SpJoin CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

@[expose] def SympA6Frame {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ} {L' : Type}
    [Group L'] (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m))
    (σ : (Fin m → Multiplicative (ZMod p)) →* L') (J : Subgroup L')
    (f₀ : Fin m → Multiplicative (ZMod p)) : Prop :=
  ∃ (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (x : LargeEvenProj (LargeEvenSpGroup K m)) (J₀ : Subgroup (StatedSp m K)) (f : ℕ),
    (∀ g, ψ₀ (σ g) =
      x * LargeEvenProjMk (LargeEvenSpGroup K m) (spPlaneTorus m ζ g) * x⁻¹) ∧
    (J₀.map (LargeEvenProjMk (LargeEvenSpGroup K m))).map (MulAut.conj x).toMonoidHom =
      J.map ψ₀ ∧
    SpPrimaryBlocks 2 f p (spPlaneTorus m ζ f₀) (proj m K (spPlaneTorus m ζ f₀)) ∧
    spFixedDim (spPlaneTorus m ζ f₀) = 4 ∧
    J₀ = ⁅spFixedFactor (spPlaneTorus m ζ f₀), spFixedFactor (spPlaneTorus m ζ f₀)⁆

theorem sympMinusA6_quotCenter_equiv {X R : Type} [Group X] [Group R] (ψ : X →* R)
    (hker : ψ.ker ≤ Subgroup.center X) (J : Subgroup X) {A : Type} [Group A]
    (hA : Subgroup.center A = ⊥) (e : ↥(J.map ψ) ≃* A) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* A) := by
  let φ : ↥J →* ↥(J.map ψ) := ψ.subgroupMap J
  have hsurj : Function.Surjective φ := ψ.subgroupMap_surjective J
  have hcenterA : ∀ z : ↥(J.map ψ), (∀ w : ↥(J.map ψ), w * z = z * w) → z = 1 := by
    intro z hz
    have h : e z ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨w, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul, hz w]
    rw [hA, Subgroup.mem_bot] at h
    exact e.injective (by rw [h, map_one])
  have hker' : φ.ker = Subgroup.center ↥J := by
    apply le_antisymm
    · intro j hj
      rw [MonoidHom.mem_ker] at hj
      have h1 : ψ (j : X) = 1 := by
        have := congrArg Subtype.val hj
        simpa [φ] using this
      have hj' : (j : X) ∈ Subgroup.center X := hker h1
      rw [Subgroup.mem_center_iff] at hj' ⊢
      intro g
      apply Subtype.ext
      simpa using hj' g
    · intro z hz
      rw [MonoidHom.mem_ker]
      rw [Subgroup.mem_center_iff] at hz
      refine hcenterA _ fun w => ?_
      obtain ⟨j, rfl⟩ := hsurj w
      rw [← map_mul, ← map_mul, hz j]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hsurj).trans e)⟩

theorem sympMinusA6_frame_out {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} [NeZero m]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m))
    (hker : ψ₀.ker ≤ Subgroup.center L') (hK2 : Nat.card K = 2)
    (σ : (Fin m → Multiplicative (ZMod p)) →* L') (J : Subgroup L')
    (f₀ : Fin m → Multiplicative (ZMod p)) (hA6 : SympA6Frame ψ₀ σ J f₀) :
    Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep
        (Subgroup.zpowers (ψ₀ (σ f₀)))) = 4 ∧
      J.map ψ₀ =
        ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (ψ₀ (σ f₀)))),
          ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (ψ₀ (σ f₀))))⁆ ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨ζ, x, J₀, f, hψσ, hrel, blocks, hd, hJ₀⟩ := hA6
  obtain ⟨hdim, hmap⟩ := sympMinusA6_modelData hp hp2 ψ₀ σ ζ x hψσ f₀ J J₀ hrel blocks hd hJ₀
  refine ⟨hdim, hmap, ?_⟩
  obtain ⟨⟨e6⟩, -⟩ := spFixed_four_two_alt hK2 blocks hd
  have hMk : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) := by
    exact AutPSp.proj_injective (n := m) (K := K)
  let e1 : ↥J₀ ≃* ↥(J₀.map (LargeEvenProjMk (LargeEvenSpGroup K m))) :=
    J₀.equivMapOfInjective (LargeEvenProjMk (LargeEvenSpGroup K m)) hMk
  let e2 : ↥(J₀.map (LargeEvenProjMk (LargeEvenSpGroup K m))) ≃*
      ↥((J₀.map (LargeEvenProjMk (LargeEvenSpGroup K m))).map (MulAut.conj x).toMonoidHom) :=
    (J₀.map (LargeEvenProjMk (LargeEvenSpGroup K m))).equivMapOfInjective
      (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  let e3 : ↥J₀ ≃* ↥(J.map ψ₀) := (e1.trans e2).trans (MulEquiv.subgroupCongr hrel)
  have e4 : ↥J₀ ≃* alternatingGroup (Fin 6) := (MulEquiv.subgroupCongr hJ₀).trans e6
  exact sympMinusA6_quotCenter_equiv ψ₀ hker J
    CFSG.HardMathSupport.Solomon.Coordinator.center_alt_six (e3.symm.trans e4)

@[expose] def SympA6Out {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    [NeZero m] (X J : Subgroup G) (ψ : ↥X →* LargeEvenProj (LargeEvenSpGroup K m))
    (a : MulAut ↥X) : Prop :=
  Nat.card K = 2 ∧ ∃ g : LargeEvenProj (LargeEvenSpGroup K m),
    (∀ l : ↥X, ψ (a l) = g * ψ l * g⁻¹) ∧
    Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)) = 4 ∧
    (J.subgroupOf X).map ψ =
      ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)),
        ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g))⁆ ∧
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6))

theorem sympMinusA6_out {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    [NeZero m] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup G} (hJle : J ≤ X)
    (ψ₀ : ↥X →* LargeEvenProj (LargeEvenSpGroup K m)) (hker : ψ₀.ker ≤ Subgroup.center ↥X)
    (hK2 : Nat.card K = 2) (σ : (Fin m → Multiplicative (ZMod p)) →* ↥X)
    (f₀ : Fin m → Multiplicative (ZMod p)) {a : MulAut ↥X} (ha : a = MulAut.conj (σ f₀))
    (hA6 : SympA6Frame ψ₀ σ (J.subgroupOf X) f₀) : SympA6Out X J ψ₀ a := by
  obtain ⟨hdim, hmap, ⟨e⟩⟩ := sympMinusA6_frame_out hp hp2 ψ₀ hker hK2 σ (J.subgroupOf X) f₀ hA6
  refine ⟨hK2, ψ₀ (σ f₀), fun l => ?_, hdim, hmap, ?_⟩
  · rw [ha, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · have e' : ↥(J.subgroupOf X) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJle
    exact ⟨((QuotientGroup.congr (Subgroup.center ↥(J.subgroupOf X)) (Subgroup.center ↥J) e'
      (Subgroup.map_center_eq e')).symm.trans e)⟩

end CFSG.StandardType.SympMinus

end
