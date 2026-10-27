module

public import Certificates.Data.NT44Model

public section

namespace CFSG.GH74.GLS.NT44.PermutationNative

structure CommutatorWitness where
  sIndex : Fin 256
  aIndex : Fin 256
  cWord : List Int
  sign : Bool
deriving Inhabited, DecidableEq, Repr

@[expose] def actorSets (_ : Unit := ()) : Array (List (Fin 256)) := #[
  [⟨0, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨35, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨148, by decide⟩, ⟨150, by decide⟩, ⟨159, by decide⟩, ⟨214, by decide⟩],
  [⟨0, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨75, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨151, by decide⟩, ⟨153, by decide⟩, ⟨157, by decide⟩, ⟨216, by decide⟩],
  [⟨0, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨22, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨149, by decide⟩, ⟨152, by decide⟩, ⟨162, by decide⟩, ⟨213, by decide⟩, ⟨215, by decide⟩, ⟨246, by decide⟩],
]

@[expose] def witnesses (_ : Unit := ()) : Array CommutatorWitness := #[
  { sIndex := ⟨6, by decide⟩, aIndex := ⟨8, by decide⟩, cWord := [1, 5, 4], sign := false },
  { sIndex := ⟨6, by decide⟩, aIndex := ⟨25, by decide⟩, cWord := [-1, -1, -2], sign := false },
  { sIndex := ⟨6, by decide⟩, aIndex := ⟨8, by decide⟩, cWord := [1, 5, 4], sign := false },
]

end CFSG.GH74.GLS.NT44.PermutationNative
