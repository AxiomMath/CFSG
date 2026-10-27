module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.FLcFlag
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.SzC4

open Matrix CFSG.Quasithin.FLc

@[expose] def Cm : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 1]

theorem Cm_pow : Cm ^ 7 = 1 := by decide

theorem Cm_ne : Cm ≠ 1 := by decide

@[expose] def CmT : Matrix (Fin 3) (Fin 3) (ZMod 2) := (Cm ^ 6).transpose

@[expose] def r1M (v : Fin 3 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, v 0, v 1, v 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def s3M (u : Fin 3 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, u 0; 0, 1, 0, u 1; 0, 0, 1, u 2; 0, 0, 0, 1]

@[expose] def gb1M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 1]

@[expose] def gb3M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1]

@[expose] def wbM : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]

theorem r1M_det (v : Fin 3 → ZMod 2) : (r1M v).det = 1 := by
  revert v
  decide

theorem s3M_det (u : Fin 3 → ZMod 2) : (s3M u).det = 1 := by
  revert u
  decide

theorem gb1M_det : gb1M.det = 1 := by decide

theorem gb3M_det : gb3M.det = 1 := by decide

theorem wbM_det : wbM.det = 1 := by decide

@[expose] def r1 (v : Fin 3 → ZMod 2) : SLt 4 := ⟨r1M v, r1M_det v⟩

@[expose] def s3 (u : Fin 3 → ZMod 2) : SLt 4 := ⟨s3M u, s3M_det u⟩

@[expose] def gb1 : SLt 4 := ⟨gb1M, gb1M_det⟩

@[expose] def gb3 : SLt 4 := ⟨gb3M, gb3M_det⟩

@[expose] def wb : SLt 4 := ⟨wbM, wbM_det⟩

theorem r1_mul (v w : Fin 3 → ZMod 2) : r1 v * r1 w = r1 (v + w) := by
  apply Subtype.ext
  show r1M v * r1M w = r1M (v + w)
  revert v w
  decide

theorem s3_mul (u u' : Fin 3 → ZMod 2) : s3 u * s3 u' = s3 (u + u') := by
  apply Subtype.ext
  show s3M u * s3M u' = s3M (u + u')
  revert u u'
  decide

theorem r1_zero : r1 0 = 1 := by
  apply Subtype.ext
  show r1M 0 = 1
  decide

theorem s3_zero : s3 0 = 1 := by
  apply Subtype.ext
  show s3M 0 = 1
  decide

@[expose] def r1Hom : Multiplicative (Fin 3 → ZMod 2) →* SLt 4 where
  toFun v := r1 (Multiplicative.toAdd v)
  map_one' := r1_zero
  map_mul' _ _ := (r1_mul _ _).symm

@[expose] def s3Hom : Multiplicative (Fin 3 → ZMod 2) →* SLt 4 where
  toFun u := s3 (Multiplicative.toAdd u)
  map_one' := s3_zero
  map_mul' _ _ := (s3_mul _ _).symm

theorem r1_injective : Function.Injective r1 := by
  intro v w h
  have h1 := congrArg (fun x : SLt 4 => (x : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  funext i
  fin_cases i
  · exact congrFun (congrFun h1 0) 1
  · exact congrFun (congrFun h1 0) 2
  · exact congrFun (congrFun h1 0) 3

theorem s3_injective : Function.Injective s3 := by
  intro v w h
  have h1 := congrArg (fun x : SLt 4 => (x : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  funext i
  fin_cases i
  · exact congrFun (congrFun h1 0) 3
  · exact congrFun (congrFun h1 1) 3
  · exact congrFun (congrFun h1 2) 3

theorem r1Hom_injective : Function.Injective r1Hom := fun _ _ h => r1_injective h

theorem s3Hom_injective : Function.Injective s3Hom := fun _ _ h => s3_injective h

@[expose] def Rrad1 : Subgroup (SLt 4) := r1Hom.range

@[expose] def Rrad3 : Subgroup (SLt 4) := s3Hom.range

theorem mem_Rrad1_iff {x : SLt 4} : x ∈ Rrad1 ↔ ∃ v, x = r1 v := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.toAdd v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Multiplicative.ofAdd v, rfl⟩

theorem mem_Rrad3_iff {x : SLt 4} : x ∈ Rrad3 ↔ ∃ u, x = s3 u := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Multiplicative.toAdd u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Multiplicative.ofAdd u, rfl⟩

theorem r1_mem_Rrad1 (v : Fin 3 → ZMod 2) : r1 v ∈ Rrad1 := mem_Rrad1_iff.2 ⟨v, rfl⟩

theorem s3_mem_Rrad3 (u : Fin 3 → ZMod 2) : s3 u ∈ Rrad3 := mem_Rrad3_iff.2 ⟨u, rfl⟩

theorem card_vec3 : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_Rrad1 : Nat.card ↥Rrad1 = 8 := by
  have h := Nat.card_congr (MonoidHom.ofInjective r1Hom_injective).toEquiv
  exact h.symm.trans card_vec3

theorem card_Rrad3 : Nat.card ↥Rrad3 = 8 := by
  have h := Nat.card_congr (MonoidHom.ofInjective s3Hom_injective).toEquiv
  exact h.symm.trans card_vec3

end CFSG.Quasithin.SzC4
