module

public import CFSG.LocalAnalysis.StandardType.GGF4PairRootLeviTransport
public import CFSG.LocalAnalysis.StandardType.GGF4SUShortA2
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross

public noncomputable section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem


theorem ggF4QGeFourA2_of_tableBPos_PSU
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .PSU 6 f X) (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hlabel : CoxeterMatrix.F₄ i j = 3) :
    ∃ W : Subgroup G, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair
      (GaloisField 2 (2 * f)) W
        (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
        (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs)) := by
  cases f with
  | zero => omega
  | succ t =>
    have hf1 : 1 ≤ t + 1 := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hF : Nat.card (GaloisField 2 (2 * (t + 1))) = (2 ^ (t + 1)) ^ 2 :=
      card_galoisField_two_mul 2 (t + 1) hf1
    let D := Unitary.rootDatum hF 6
    obtain ⟨ψG, hkerG, _, εG, hεreflG, hεleviG, _⟩ := hpos
    let ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (t + 1))) 2 (t + 1)) 6) →* G := ψG
    let ε : (coxeterMatrix D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs) := εG
    have hker : ψ.ker ≤ Subgroup.center _ := hkerG
    have hεrefl : ∀ k, GGIsReflection p (ε ((coxeterMatrix D.isFiniteType).simple k) : MulAut ↥Bs) :=
      hεreflG
    have hεlevi : ∀ w k,
        ggRankOneIn X Bs (ε (w * (coxeterMatrix D.isFiniteType).simple k * w⁻¹) : MulAut ↥Bs) =
          (ggRootLevi D (weylAction D.isFiniteType w (Pi.single k 1))).map ψ := hεleviG
    have hM_eq : coxeterMatrix D.isFiniteType = CoxeterMatrix.B 3 := by
      change coxeterMatrix (Symplectic.isFiniteType_cartanC 3) = _
      have hC : GGIntCartan (CoxeterMatrix.B 3) (Symplectic.cartanC 3) := by
        rw [cartanC_eq_cartanMatrixB]
        exact ggIntCartan_B 3
      exact coxeterMatrix_eq_of_ggIntCartan _ hC
    have hadm : StatedLieAdmissible .PSU 6 2 (t + 1) :=
      ⟨Nat.prime_two, hf1, by decide, by simp⟩
    obtain ⟨νG, hνG⟩ := (ggTagFacts_PSU hadm (by decide)).2.1
    let ν : (coxeterMatrix D.isFiniteType).Group →*
        ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (t + 1))) 2 (t + 1)) 6) := νG
    have hν : GGWeylLift D ν := hνG
    have hij : i ≠ j := by
      rintro rfl
      have hd : CoxeterMatrix.F₄ i i = 1 := CoxeterMatrix.F₄.diagonal i
      rw [hd] at hlabel
      omega
    obtain ⟨u, c, d, hSi, hSj, _, h3, _⟩ :=
      exists_f4_pair_rootLevi_transport D hp hp2 hEl hNT hAind hpres hXA ψ ε hεrefl hεlevi
        (Equiv.refl _) (fun k l => congrArg (fun M : CoxeterMatrix (Fin 3) => M k l) hM_eq)
        ν hν w i j hij hi hj
    let θ := (MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ
    have hθ : θ.ker ≤ Subgroup.center _ := by
      intro z hz
      apply hker
      have hz' := MonoidHom.mem_ker.mp hz
      rw [show θ = _ from rfl, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ (MulAut.conj (ψ (ν u))).injective] at hz'
      exact hz'
    obtain ⟨rfl, rfl⟩ := h3 hlabel
    obtain ⟨W, hW⟩ := F4KGPosition.exists_linearBlockStandardPair_rootLevi_PSU6 hF θ hθ
    refine ⟨W, ?_⟩
    rw [hSi, hSj]
    exact hW

theorem ggF4QGeFourPSUPairInput_holds : GGF4QGeFourPSUPairInput := by
  intro G _ _ p Bs hp hp2 hEl hNT A hAind e hpres X hXA f hf hpos w i j hlabel hi hj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := ggF4QGeFourA2_of_tableBPos_PSU hp hp2 hEl hNT hAind hpres hXA hf hpos
    w i j hi hj hlabel
  exact ⟨GaloisField 2 (2 * f), inferInstance, inferInstance, W, inferInstance, hW⟩

end CFSG.StandardType
