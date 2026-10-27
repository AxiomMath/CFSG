module

public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3P5Act

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

namespace P5Quot

abbrev PQ : Type := ↥permQuot6Model.sec ⧸ permQuot6Model.ker.subgroupOf permQuot6Model.sec

@[expose] def amb (x : ↥permQuot6Model.sec) : G6.PermMod 6 := x.1

theorem amb_mul (x y : ↥permQuot6Model.sec) : amb (x * y) = amb x * amb y := rfl

theorem amb_one : amb 1 = 1 := rfl

@[expose] noncomputable def crdHom : PQ →* Multiplicative P5.Vec5 :=
  QuotientGroup.lift _
    { toFun := fun x => Multiplicative.ofAdd (P5.crd (Multiplicative.toAdd (amb x)))
      map_one' := by
        show Multiplicative.ofAdd (P5.crd 0) = 1
        rw [show P5.crd 0 = 0 from Matrix.mulVec_zero _]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (P5.crd (Multiplicative.toAdd (amb x) +
          Multiplicative.toAdd (amb y))) = _
        rw [P5.crd_add]
        rfl }
    (by
      intro z hz
      rw [MonoidHom.mem_ker]
      rw [Subgroup.mem_subgroupOf] at hz
      have hz' : amb z ∈ Subgroup.zpowers (G6.allOnes 6) := hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
      show Multiplicative.ofAdd (P5.crd (Multiplicative.toAdd (amb z))) = 1
      rw [← hk, toAdd_zpow]
      have e : k • Multiplicative.toAdd (G6.allOnes 6) = fun _ => (k : ZMod 2) := by
        funext i
        simp [G6.allOnes]
      rw [e, P5.crd_const]
      rfl)

theorem crdHom_mk (x : ↥permQuot6Model.sec) :
    Multiplicative.toAdd (crdHom (QuotientGroup.mk x)) =
      P5.crd (Multiplicative.toAdd (amb x)) := rfl

theorem crdHom_injective : Function.Injective crdHom := by
  rw [injective_iff_map_eq_one]
  intro m hm
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
  have h1 : P5.crd (Multiplicative.toAdd (amb x)) = 0 := by
    rw [← crdHom_mk, hm]
    rfl
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  show amb x ∈ Subgroup.zpowers (G6.allOnes 6)
  rw [Subgroup.mem_zpowers_iff]
  rcases P5.crd_eq_zero_aux _ h1 with h | h
  · refine ⟨0, ?_⟩
    rw [zpow_zero]
    exact Multiplicative.toAdd.injective (by rw [h]; rfl)
  · refine ⟨1, ?_⟩
    rw [zpow_one]
    exact Multiplicative.toAdd.injective (by rw [h]; rfl)

theorem crdHom_surjective : Function.Surjective crdHom := by
  intro v
  refine ⟨QuotientGroup.mk ⟨Multiplicative.ofAdd (P5.sec (Multiplicative.toAdd v)),
    Subgroup.mem_top _⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [crdHom_mk]
  exact P5.crd_sec _

end P5Quot

end CFSG.Quasithin.H13
