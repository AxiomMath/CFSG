module

public import CFSG.RankThree.PartOne.N143.Weyl613Small
import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.N143

@[expose] def OddRadConcl (T : Type) [Group T] (β : MulAut T) : Prop :=
  Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥((β : T →* T).eqLocus (MonoidHom.id T)))))

@[expose] def OddRadAt (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T →
    ∀ β : MulAut T, orderOf β = 5 → OddRadConcl T β

theorem OddRadAt.mono {P Q : (X : Type) → [Group X] → Prop}
    (hPQ : ∀ (X : Type) [Group X], P X → Q X) (h : OddRadAt Q) : OddRadAt P :=
  fun T _ _ hs hP β hβ => h T hs (hPQ T hP) β hβ

@[expose] def SmallModel (t : StatedLieTag) (X : Type) [Group X] : Prop :=
  ∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧ LieModel X t n 2 f ∧ SmallEvenParams t n f

theorem evenLieTypeSmall_iff_exists_smallModel (X : Type) [Group X] :
    EvenLieTypeSmall X ↔ ∃ t, SmallModel t X :=
  ⟨fun ⟨t, n, f, ha, hm, hs⟩ => ⟨t, n, f, ha, hm, hs⟩,
    fun ⟨t, n, f, ha, hm, hs⟩ => ⟨t, n, f, ha, hm, hs⟩⟩

theorem card_solvableRadical_perfectResidual_eq {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') :
    Nat.card ↥(solvableRadical ↥(perfectResidual G)) =
      Nat.card ↥(solvableRadical ↥(perfectResidual G')) := by
  have hD : (perfectResidual G).map e.toMonoidHom = perfectResidual G' :=
    CFSG.LieType.SteinbergBR.perfectResidual_map_equiv e
  let ε : ↥(perfectResidual G) ≃* ↥(perfectResidual G') :=
    (Subgroup.equivMapOfInjective (perfectResidual G) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hD)
  rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv ε,
    Subgroup.card_map_of_injective ε.injective]

theorem orderOf_mulAut_congr {T T' : Type*} [Group T] [Group T'] (e : T ≃* T')
    (β : MulAut T) : orderOf (MulAut.congr e β) = orderOf β :=
  MulEquiv.orderOf_eq (MulAut.congr e) β

theorem oddRadConcl_congr {T T' : Type} [Group T] [Group T'] (e : T ≃* T') (β : MulAut T) :
    OddRadConcl T' (MulAut.congr e β) ↔ OddRadConcl T β := by
  have hcongr : ∀ x : T, (MulAut.congr e β) (e x) = e (β x) := fun x => by
    simp [MulAut.congr_apply]
  have hfix : ((β : T →* T).eqLocus (MonoidHom.id T)).map e.toMonoidHom =
      ((MulAut.congr e β : MulAut T') : T' →* T').eqLocus (MonoidHom.id T') := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨z, hz, hzx⟩
      have hzx' : z = x := e.injective hzx
      subst hzx'
      show (MulAut.congr e β) (e z) = e z
      rw [hcongr]
      exact congrArg e (show β z = z from hz)
    · intro hx
      refine ⟨x, ?_, rfl⟩
      have h1 : (MulAut.congr e β) (e x) = e x := hx
      rw [hcongr] at h1
      exact e.injective h1
  let ι : ↥((β : T →* T).eqLocus (MonoidHom.id T)) ≃*
      ↥(((MulAut.congr e β : MulAut T') : T' →* T').eqLocus (MonoidHom.id T')) :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix)
  unfold OddRadConcl
  rw [← card_solvableRadical_perfectResidual_eq ι]

theorem oddRadConcl_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : ∀ β' : MulAut T', orderOf β' = 5 → OddRadConcl T' β') (β : MulAut T)
    (hβ : orderOf β = 5) : OddRadConcl T β :=
  (oddRadConcl_congr e β).mp (h _ (by rw [orderOf_mulAut_congr]; exact hβ))

end CFSG.RankThree.PartOne.F106
