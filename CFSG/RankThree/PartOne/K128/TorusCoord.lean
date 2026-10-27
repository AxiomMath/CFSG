module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_coord_embedding {τ : Tag} {L : Type} [Field L] {Q : Type*} [Group Q]
    (θ : Q →* ModGL τ L) (hθ : Function.Injective θ) (S : Subgroup (Fin τ.rank → Lˣ))
    (hQS : ∀ y, θ y ∈ S.map (rootDiagUnitHom τ L)) (i j : Fin τ.rank)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a i = b i → a j = b j → a = b) :
    ∃ Φ : Q →* Lˣ × Lˣ, Function.Injective Φ ∧ ∀ y, ∃ a ∈ S, θ y = rootDiagUnit τ a ∧
      (Φ y).1 = a i ∧ (Φ y).2 = a j := by
  classical
  have hex : ∀ y, ∃ a, a ∈ S ∧ rootDiagUnit τ a = θ y := fun y => by
    obtain ⟨a, ha, h⟩ := hQS y
    exact ⟨a, ha, h⟩
  choose a haS hax using hex
  have hmul : ∀ y z, a (y * z) = a y * a z := fun y z => by
    apply rootDiagUnit_injective
    rw [hax, rootDiagUnit_mul, hax, hax, map_mul]
  have hone : a 1 = 1 := by
    apply rootDiagUnit_injective
    rw [hax, map_one, rootDiagUnit_one]
  let Φ : Q →* Lˣ × Lˣ :=
    { toFun := fun y => (a y i, a y j)
      map_one' := by simp [hone]
      map_mul' := fun y z => by simp [hmul] }
  refine ⟨Φ, ?_, fun y => ⟨a y, haS y, (hax y).symm, rfl, rfl⟩⟩
  intro y z h
  have h1 : a y i = a z i := congrArg Prod.fst h
  have h2 : a y j = a z j := congrArg Prod.snd h
  have h3 := hS _ (haS y) _ (haS z) h1 h2
  apply hθ
  rw [← hax y, ← hax z, h3]

end CFSG.RankThree.PartOne.K128
