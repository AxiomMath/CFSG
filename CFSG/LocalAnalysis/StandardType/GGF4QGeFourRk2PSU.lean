module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourA2PSU
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourTwins
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary
public import Certificates.Certificate117
import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6SU6
import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModelEven
import CFSG.RankThree.PartOne.CTP.SU4EvenField
import CFSG.RankThree.PartOne.CTP.SU4EvenGen
import CFSG.ClassicalInvolution.Models.TwistedPairs

public noncomputable section

namespace CFSG.StandardType

namespace F4KGPosition

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

private theorem rk2psu_ker_comp_le_center {A B C : Type*} [Group A] [Group B] [Group C]
    (ψ : B →* C) (ι : A →* B) (hι : Function.Injective ι) (hψ : ψ.ker ≤ Subgroup.center B) :
    (ψ.comp ι).ker ≤ Subgroup.center A := by
  intro z hz
  have hz' : ι z ∈ Subgroup.center B := hψ hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply hι
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hz' (ι g)

private theorem rk2psu_eq_one_of_sq {K : Type} [Field K] [CharP K 2] {r : K} (h : r ^ 2 = 1) :
    r = 1 :=
  frobenius_inj K 2 (by rw [frobenius_def, h, frobenius_def, one_pow])

private theorem rk2psu_injective_SL2 {F : Type} [Field F] (hF : ∀ r : F, r ^ 2 = 1 → r = 1)
    {H : Type} [Group H] (φ : SL(2, F) →* H) (h : φ.ker ≤ Subgroup.center SL(2, F)) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (h hA)
  have hr1 : r = 1 := hF r (by simpa using hr)
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [← hrA, hr1]
  simp

theorem unitaryGroup_blocks_sup_eq_top_even
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθ : ∀ x, (unitaryInvolution K 2 f).toRingHom ((unitaryInvolution K 2 f).toRingHom x) = x) :
    (ulb (unitaryInvolution K 2 f).toRingHom hθ).range ⊔
      (usb (unitaryInvolution K 2 f).toRingHom hθ).range = ⊤ := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hirr := CFSG.LieType.Universal.minusCoeffs_irr 2 f
  have := CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  obtain ⟨inst, ⟨D⟩⟩ := CFSG.RankThree.PartOne.CTP.SU4Even.exists_kleinDataEven hF hK hirr
  obtain ⟨Θ, hl, hs⟩ := WeakCT.exists_spinMinus6_equiv_unitaryGroup_even D hK hirr hθ
  have htop := CFSG.RankThree.PartOne.CTP.SU4Even.spinMinus6_blocks_sup_eq_top_even hirr
  rw [← hl, ← hs, ← Subgroup.map_sup, htop]
  exact Subgroup.map_top_of_surjective _ Θ.surjective

theorem commute_rootLevi_PSU6_zero_two {E : Type} [Field E] [Finite E] [CharP E 2] {f : ℕ}
    (hE : Nat.card E = (2 ^ f) ^ 2) {G : Type} [Group G]
    (ψ : ↥(SU (unitaryInvolution E 2 f) 6) →* G) :
    ∀ a ∈ (ggRootLevi (rootDatum hE 6) (Pi.single (0 : Fin 3) 1)).map ψ,
      ∀ b ∈ (ggRootLevi (rootDatum hE 6) (Pi.single (2 : Fin 3) 1)).map ψ, a * b = b * a := by
  have hσ : ∀ c, unitaryInvolution E 2 f (unitaryInvolution E 2 f c) = c :=
    unitaryInvolution_involutive hE
  have hθ : ∀ c, (unitaryInvolution E 2 f).toRingHom
      ((unitaryInvolution E 2 f).toRingHom c) = c := hσ
  have hμ0 : (1 : E) ≠ 0 := one_ne_zero
  have hμ : unitaryInvolution E 2 f (1 : E) = -1 := by
    rw [map_one]
    exact (CharTwo.neg_eq (1 : E)).symm
  have hσθ : ∀ c, unitaryInvolution E 2 f c = (unitaryInvolution E 2 f).toRingHom c :=
    fun _ => rfl
  have hc := RouteD.commutes_node2_node0 hσ hθ hμ0 hμ hσθ
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hc b hb a ha]

theorem exists_unitaryB2BlockStandardPair_rootLevi_PSU6
    {E : Type} [Field E] [Finite E] [CharP E 2] {f : ℕ} (hf : 1 ≤ f)
    (hE : Nat.card E = (2 ^ f) ^ 2) {θ : E →+* E} (hθ : ∀ x, θ (θ x) = x)
    (hθf : ∀ x, θ x = x ^ 2 ^ f) {G : Type} [Group G]
    (ψ : ↥(SU (unitaryInvolution E 2 f) 6) →* G) (hψ : ψ.ker ≤ Subgroup.center _) :
    ∃ W : Subgroup G, UnitaryB2BlockStandardPair θ hθ W
        ((ggRootLevi (rootDatum hE 6) (Pi.single (2 : Fin 3) 1)).map ψ)
        ((ggRootLevi (rootDatum hE 6) (Pi.single (1 : Fin 3) 1)).map ψ) ∧
      W ≤ (ggRootLevi (rootDatum hE 6) (Pi.single (2 : Fin 3) 1)).map ψ ⊔
        (ggRootLevi (rootDatum hE 6) (Pi.single (1 : Fin 3) 1)).map ψ := by
  obtain rfl : θ = (unitaryInvolution E 2 f).toRingHom :=
    RingHom.ext fun x => (hθf x).trans (unitaryInvolution_apply E 2 f x).symm
  have hσ : ∀ c, unitaryInvolution E 2 f (unitaryInvolution E 2 f c) = c :=
    unitaryInvolution_involutive hE
  have hμ0 : (1 : E) ≠ 0 := one_ne_zero
  have hμ : unitaryInvolution E 2 f (1 : E) = -1 := by
    rw [map_one]
    exact (CharTwo.neg_eq (1 : E)).symm
  have hσθ : ∀ c, unitaryInvolution E 2 f c = (unitaryInvolution E 2 f).toRingHom c :=
    fun _ => rfl
  let ι := RouteD.iota4 hθ hμ0 hμ hσθ
  have hι : Function.Injective ι := RouteD.iota4_injective hθ hμ0 hμ hσθ
  have hlong : ((ulb (unitaryInvolution E 2 f).toRingHom hθ).range).map ι =
      RouteD.nodeSU hσ 2 :=
    le_antisymm (RouteD.iota4_ulb_le hσ hθ hμ0 hμ hσθ) (RouteD.iota4_ulb_ge hσ hθ hμ0 hμ hσθ)
  have hshort : ((usb (unitaryInvolution E 2 f).toRingHom hθ).range).map ι =
      RouteD.nodeSU hσ 1 := by
    rw [RouteD.iota4_usb_range hσ hθ hμ0 hμ hσθ]
    exact le_antisymm (RouteD.iota3_B23_le hσ) (RouteD.iota3_B23_ge hσ)
  let φ := ψ.comp ι
  have hker : φ.ker ≤ Subgroup.center _ := rk2psu_ker_comp_le_center ψ ι hι hψ
  have hF1 : ∀ r : fixedField (unitaryInvolution E 2 f).toRingHom, r ^ 2 = 1 → r = 1 := by
    intro r hr
    have hr' : ((r : E)) ^ 2 = 1 := by
      exact_mod_cast congrArg (fun s : fixedField (unitaryInvolution E 2 f).toRingHom => (s : E)) hr
    exact Subtype.ext (rk2psu_eq_one_of_sq hr')
  have hE1 : ∀ r : E, r ^ 2 = 1 → r = 1 := fun _ hr => rk2psu_eq_one_of_sq hr
  have hl : Function.Injective (φ.comp (ulb (unitaryInvolution E 2 f).toRingHom hθ)) :=
    rk2psu_injective_SL2 hF1 _ (by
      rw [MonoidHom.comp_assoc]
      exact rk2psu_ker_comp_le_center ψ _ (hι.comp (ulb_injective _ hθ)) hψ)
  have hs : Function.Injective (φ.comp (usb (unitaryInvolution E 2 f).toRingHom hθ)) :=
    rk2psu_injective_SL2 hE1 _ (by
      rw [MonoidHom.comp_assoc]
      exact rk2psu_ker_comp_le_center ψ _ (hι.comp (usb_injective _ hθ)) hψ)
  have hU : (ulb (unitaryInvolution E 2 f).toRingHom hθ).range.map φ =
      (ggRootLevi (rootDatum hE 6) (Pi.single (2 : Fin 3) 1)).map ψ := by
    rw [show φ = ψ.comp ι from rfl, ← Subgroup.map_map, hlong]
    rfl
  have hV : (usb (unitaryInvolution E 2 f).toRingHom hθ).range.map φ =
      (ggRootLevi (rootDatum hE 6) (Pi.single (1 : Fin 3) 1)).map ψ := by
    rw [show φ = ψ.comp ι from rfl, ← Subgroup.map_map, hshort]
    rfl
  refine ⟨φ.range, ⟨φ, rfl, hker, hl, hs, hU, hV⟩, ?_⟩
  have htop := unitaryGroup_blocks_sup_eq_top_even hf hE hθ
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, hU, hV]

end F4KGPosition

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.Exceptional (frobQ frobQ_apply frobQ_frobQ)


theorem ggF4QGeFourRk2_commute_of_tableBPosImage_PSU
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .PSU 6 f X) (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    CoxeterMatrix.F₄ i j = 2 →
      ∀ a ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs),
        ∀ b ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs),
          a * b = b * a := by
  intro hlabel
  cases f with
  | zero => omega
  | succ t =>
    have hf1 : 1 ≤ t + 1 := by omega
    have hF : Nat.card (GaloisField 2 (2 * (t + 1))) = (2 ^ (t + 1)) ^ 2 :=
      card_galoisField_two_mul 2 (t + 1) hf1
    let D := Unitary.rootDatum hF 6
    obtain ⟨ψG, _, _, εG, hεreflG, hεleviG, _⟩ := hpos
    let ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (t + 1))) 2 (t + 1)) 6) →* G := ψG
    let ε : (coxeterMatrix D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs) := εG
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
    obtain ⟨u, c, d, hSi, hSj, h2, _, _⟩ :=
      exists_f4_pair_rootLevi_transport D hp hp2 hEl hNT hAind hpres hXA ψ ε hεrefl hεlevi
        (Equiv.refl _) (fun k l => congrArg (fun M : CoxeterMatrix (Fin 3) => M k l) hM_eq)
        ν hν w i j hij hi hj
    have hcomm := F4KGPosition.commute_rootLevi_PSU6_zero_two hF
      ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ)
    rw [hSi, hSj]
    rcases h2 hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcomm
    · intro a ha b hb
      exact (hcomm b hb a ha).symm

theorem ggF4QGeFourRk2_bond_of_tableBPosImage_PSU
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .PSU 6 f X) (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    CoxeterMatrix.F₄ i j = 4 →
      GGF4QGeFourBond .S2 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs)) ∨
        GGF4QGeFourBond .S2 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs)) := by
  intro hlabel
  cases f with
  | zero => omega
  | succ t =>
    have hf1 : 1 ≤ t + 1 := by omega
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
    obtain ⟨u, c, d, hSi, hSj, _, _, h4⟩ :=
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
    obtain ⟨W, hW, hle⟩ := F4KGPosition.exists_unitaryB2BlockStandardPair_rootLevi_PSU6
      hf1 hF (frobQ_frobQ 2 (t + 1) hf1) (frobQ_apply 2 (t + 1)) θ hθ
    rw [hSi, hSj]
    rcases h4 hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨W, hW, hle⟩
    · exact Or.inr ⟨W, hW, hle⟩

end CFSG.StandardType

end
