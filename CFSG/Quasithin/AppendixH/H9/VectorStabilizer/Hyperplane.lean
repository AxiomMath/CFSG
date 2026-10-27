module

public import CFSG.Quasithin.AppendixH.H9.SylowModel

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

open CFSG.Quasithin CFSG.Open

variable {m : ℕ}

private theorem polarN_mul_right {n : ℕ} (x y s : PairN n) :
    polarN n x (y * s) = polarN n x y + polarN n x s := by
  rw [polarN_comm x (y * s), polarN_mul_left, polarN_comm y x, polarN_comm s x]

private theorem polarN_inv_right {n : ℕ} (x s : PairN n) : polarN n x s⁻¹ = polarN n x s := by
  calc polarN n x s⁻¹ = polarN n s⁻¹ x := polarN_comm x s⁻¹
    _ = polarN n s x := polarN_inv_left s x
    _ = polarN n x s := polarN_comm s x

theorem mem_perpN_zpowers_iff {n : ℕ} {x v : PairN n} :
    x ∈ perpN n (Subgroup.zpowers v) ↔ polarN n x v = 0 := by
  rw [mem_perpN]
  constructor
  · intro h
    exact h v (Subgroup.mem_zpowers v)
  · intro h
    let T : Subgroup (PairN n) :=
      { carrier := {s | polarN n x s = 0}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [polarN_mul_right, ha, hb, add_zero]
        one_mem' := by simp [polarN]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          exact (polarN_inv_right x a).trans ha }
    have hle : Subgroup.zpowers v ≤ T := Subgroup.zpowers_le.mpr h
    exact fun s hs => hle hs

private theorem polarN_pairVec_ez (m : ℕ) (x : PairN (m + 1)) :
    polarN (m + 1) x (pairVec (ez m) 0) = (Multiplicative.toAdd x.2) 0 := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [polarN_pairVec, ez, dotProduct_zero, zero_add, single_one_dotProduct]
  rfl

theorem mem_V2n_perpN_iff (x : PairN (m + 1)) :
    x ∈ V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0)) ↔
      x.1 = 1 ∧ (Multiplicative.toAdd x.2) 0 = 0 := by
  rw [Subgroup.mem_inf, mem_V2n, mem_perpN_zpowers_iff, polarN_pairVec_ez]

private def hyperplaneHom (m : ℕ) : ↥(V2n (m + 1)) →* Multiplicative (ZMod 2) where
  toFun := fun x => Multiplicative.ofAdd ((Multiplicative.toAdd (x : PairN (m + 1)).2) 0)
  map_one' := by simp
  map_mul' := by
    intro x y
    apply Multiplicative.toAdd.injective
    simp only [Subgroup.coe_mul, Prod.snd_mul, toAdd_mul,
      toAdd_ofAdd, Pi.add_apply]

theorem relIndex_V2n_perpN (m : ℕ) :
    (V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))).relIndex (V2n (m + 1)) =
      2 := by
  have hker : (hyperplaneHom m).ker =
      (V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))).subgroupOf
        (V2n (m + 1)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_V2n_perpN_iff]
    constructor
    · intro h
      exact ⟨mem_V2n.mp x.property, by simpa [hyperplaneHom] using h⟩
    · rintro ⟨_, h2⟩
      simpa [hyperplaneHom] using h2
  have hsurj : Function.Surjective (hyperplaneHom m) := by
    intro z
    refine ⟨⟨pairVec 0 (Pi.single (0 : Fin (m + 1)) z.toAdd), pairVec_mem_V2n _⟩, ?_⟩
    simp [hyperplaneHom, pairVec, Pi.single_eq_same]
  have hrange : (hyperplaneHom m).range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  calc (V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))).relIndex
          (V2n (m + 1))
      = ((V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))).subgroupOf
          (V2n (m + 1))).index := rfl
    _ = (hyperplaneHom m).ker.index := by rw [hker]
    _ = Nat.card (hyperplaneHom m).range := Subgroup.index_ker _
    _ = Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2))) := by rw [hrange]
    _ = Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_top
    _ = 2 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end CFSG.ASVolI.ChH.VectorStabilizer
