module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C48PfFourModPf
public import CFSG.Quasithin.Background.CosetGraphCritical
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Mat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open CFSG.Quasithin.C48Pf.FMod CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement Pointwise

theorem mem_statedSL_zmod_two (n : ℕ) (g : GL (Fin n) (ZMod 2)) : g ∈ StatedSL n (ZMod 2) := by
  apply Subgroup.subset_closure
  show (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1
  have h : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det *
      ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
  exact key _ _ h

theorem exists_coords_of_directSum {G : Type} [Group G] [Finite G] {K U : Subgroup G}
    (hU : IsElemAbelian 2 U) (hKU : K ≤ Subgroup.normalizer (U : Set G)) {n j : ℕ} (hj : 1 ≤ j)
    (hds : @DirectSumOfCopies ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) ⊥
      (FFModel.nat (StatedSL n (ZMod 2))) j) :
    ∃ (α : ↥K →* GL (Fin n) (ZMod 2)) (β : ↥⁅U, K⁆ →* Multiplicative (Fin j → Fin n → ZMod 2)),
      Function.Surjective α ∧ α.ker = (InternalSec.autOnHom hKU).ker ∧ Function.Bijective β ∧
      (∀ (x : ↥K) (u v : ↥⁅U, K⁆), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
        Multiplicative.toAdd (β v) i =
          ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
            (Multiplicative.toAdd (β u) i)) ∧
      Nat.card ↥(autOn K U) = Nat.card ↥(StatedSL n (ZMod 2)) := by
  classical
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨I, π, hZI, hind, hsup, hreal⟩ := hds
  have hnat := fun i => natCoords (hreal i)
  choose β hβi hβs hβinv hβe hπs using hnat
  have hπb : Function.Bijective π :=
    ⟨injective_of_natCoords (β ⟨0, hj⟩) (hβs _) (hβinv _) (hβe _), hπs ⟨0, hj⟩⟩
  obtain ⟨c, hc⟩ := exists_compHom I hind
  have hUK : ⁅U, K⁆ ≤ U := commutator_le_of_le_normalizer hKU
  have hJ : (⨆ i, I i : Subgroup ↥U) = (⁅U, K⁆).subgroupOf U := by
    have : IsMulCommutative ↥U := hU.1
    rw [← commV_autOn_eq1527d hKU]
    exact ((bot_sup_eq _).symm.trans hsup)
  have hmemJ : ∀ v : ↥⁅U, K⁆, (⟨(v : G), hUK v.2⟩ : ↥U) ∈ (⨆ i, I i : Subgroup ↥U) := fun v => by
    rw [hJ]
    exact Subgroup.mem_subgroupOf.2 v.2
  let toJ : ↥⁅U, K⁆ → ↥(⨆ i, I i : Subgroup ↥U) := fun v => ⟨⟨(v : G), hUK v.2⟩, hmemJ v⟩
  let βtot : ↥⁅U, K⁆ →* Multiplicative (Fin j → Fin n → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd fun i => Multiplicative.toAdd (β i (c (toJ v) i))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        have h1 : toJ 1 = 1 := Subtype.ext (Subtype.ext rfl)
        simp [h1]
      map_mul' := fun u v => by
        apply Multiplicative.toAdd.injective
        funext i
        have h1 : toJ (u * v) = toJ u * toJ v := Subtype.ext (Subtype.ext rfl)
        simp [h1] }
  have hβtot : ∀ v i, Multiplicative.toAdd (βtot v) i =
      Multiplicative.toAdd (β i (c (toJ v) i)) := fun v i => rfl
  let e := specialLinearGroupEquivStatedSL n (ZMod 2)
  let E : SpecialLinearGroup (Fin n) (ZMod 2) ≃* ↥(autOn K U) :=
    e.trans (MulEquiv.ofBijective π hπb)
  let ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    E.symm.toMonoidHom.comp (InternalSec.autOnHom hKU)
  have hψE : ∀ k, E (ψ k) = InternalSec.autOnHom hKU k := fun k => E.apply_symm_apply _
  have hρ : ∀ (x : ↥K) (u : ↥U), ((FLc.rhoOf π (ψ x) u : ↥U) : G) = x * u * (x : G)⁻¹ := by
    intro x u
    have h1 : FLc.rhoOf π (ψ x) = ((InternalSec.autOnHom hKU x : ↥(autOn K U)) : MulAut ↥U) :=
      congrArg (fun y : ↥(autOn K U) => (y : MulAut ↥U)) (hψE x)
    rw [h1]
    exact Setup.rho_apply_coe hKU x u
  let α : ↥K →* GL (Fin n) (ZMod 2) := (StatedSL n (ZMod 2)).subtype.comp (e.toMonoidHom.comp ψ)
  have hαcoe : ∀ x, ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((ψ x : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) :=
    fun x => rfl
  refine ⟨α, βtot, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g
    have hψs : Function.Surjective ψ :=
      E.symm.surjective.comp (InternalSec.autOnHom_surjective hKU)
    obtain ⟨x, hx⟩ := hψs (e.symm ⟨g, mem_statedSL_zmod_two n g⟩)
    refine ⟨x, ?_⟩
    show (e (ψ x) : GL (Fin n) (ZMod 2)) = g
    rw [hx]
    simp
  ·
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e (ψ x) = 1 := Subtype.ext hx
      have h2 : ψ x = 1 := by simpa using h1
      have h3 : InternalSec.autOnHom hKU x = 1 := by rw [← hψE x, h2, map_one]
      exact h3
    · intro hx
      have h2 : ψ x = 1 := by
        have : E (ψ x) = 1 := by rw [hψE x, hx]
        simpa using this
      show ((e (ψ x) : ↥(StatedSL n (ZMod 2))) : GL (Fin n) (ZMod 2)) = 1
      rw [h2, map_one]
      rfl
  ·
    constructor
    · rw [injective_iff_map_eq_one]
      intro v hv
      have h0 : ∀ i, c (toJ v) i = 1 := by
        intro i
        apply hβi i
        rw [map_one]
        apply Multiplicative.toAdd.injective
        have := congrFun (congrArg Multiplicative.toAdd hv) i
        simpa [hβtot] using this
      have h1 : c (toJ v) = fun _ => 1 := funext h0
      have h2 := (hc (toJ v) (fun _ => 1)).2 h1
      have h3 : ((toJ v : ↥(⨆ i, I i : Subgroup ↥U)) : ↥U) = 1 := by
        rw [← h2]
        simp
      apply Subtype.ext
      have := congrArg Subtype.val h3
      simpa [toJ] using this
    · intro t
      choose u hu using fun i => hβs i (Multiplicative.ofAdd (t i))
      have hmem : (∏ i, (u i : ↥U)) ∈ (⨆ i, I i : Subgroup ↥U) :=
        Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (u i).2
      have hmem' : (∏ i, (u i : ↥U)) ∈ (⁅U, K⁆).subgroupOf U := by rw [← hJ]; exact hmem
      have hmemG : (((∏ i, (u i : ↥U)) : ↥U) : G) ∈ ⁅U, K⁆ := Subgroup.mem_subgroupOf.1 hmem'
      refine ⟨⟨_, hmemG⟩, ?_⟩
      have hcv : c (toJ ⟨_, hmemG⟩) = u := by
        rw [← hc]
      apply Multiplicative.toAdd.injective
      funext i
      rw [hβtot, hcv, hu i]
      rfl
  ·
    intro x u v huv i
    have hg1 : ∀ i, ∀ w ∈ I i, FLc.rhoOf π (ψ x) w ∈ I i := fun i => hβinv i (ψ x)
    have hgu : FLc.rhoOf π (ψ x) ((toJ u : ↥(⨆ i, I i : Subgroup ↥U)) : ↥U) =
        ((toJ v : ↥(⨆ i, I i : Subgroup ↥U)) : ↥U) := by
      apply Subtype.ext
      rw [hρ x _]
      simpa [toJ] using huv.symm
    have hmemv : FLc.rhoOf π (ψ x) ((toJ u : ↥(⨆ i, I i : Subgroup ↥U)) : ↥U) ∈
        (⨆ i, I i : Subgroup ↥U) := by
      rw [hgu]
      exact (toJ v).2
    have h1 := compHom_map hc (FLc.rhoOf π (ψ x)) hg1 (toJ u) hmemv i
    have h2 : c ⟨FLc.rhoOf π (ψ x) ((toJ u : ↥(⨆ i, I i : Subgroup ↥U)) : ↥U), hmemv⟩ = c (toJ v) :=
      congrArg c (Subtype.ext hgu)
    rw [h2] at h1
    have h3 := hβe i (ψ x) (c (toJ u) i) (hg1 i _ (c (toJ u) i).2)
    have h4 : (⟨FLc.rhoOf π (ψ x) ((c (toJ u) i : ↥(I i)) : ↥U), hg1 i _ (c (toJ u) i).2⟩ :
        ↥(I i)) = c (toJ v) i := Subtype.ext h1.symm
    rw [h4] at h3
    rw [hβtot, hβtot, h3, hαcoe]
  ·
    exact Nat.card_congr (MulEquiv.ofBijective π hπb).toEquiv.symm

end CFSG.Quasithin.H13.Ch4.NSB
