module

public import CFSG.RankThree.PartOne.K1320.L4Transport
public import CFSG.RankThree.PartOne.K1327.StepA
public import CFSG.RankThree.PartOne.Q1327.QuasiAbs
public import CFSG.RankThree.PartOne.S12.ReflectionFacts
public import CFSG.RankThree.PartOne.S13K.Pair134Embed
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327
  CFSG.RankThree.PartOne.K1320 CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.Torsion37
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Generic

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E Jc : Subgroup G}

theorem card_sup_zpowers_le (hd : RefFacts.ElemData p E) (x y : E) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ p ^ 2 := by
  classical
  have hsurj : Function.Surjective (fun q : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y) =>
      (⟨q.1.1 * q.2.1, Subgroup.mul_mem_sup q.1.2 q.2.2⟩ :
        ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y))) := by
    rintro ⟨z, hz⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun k _ l _ => hd.comm k l) hz
    exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers] at h1
  have hx : orderOf x ≤ p := Nat.le_of_dvd hd.prime.pos (orderOf_dvd_of_pow_eq_one (hd.pow x))
  have hy : orderOf y ≤ p := Nat.le_of_dvd hd.prime.pos (orderOf_dvd_of_pow_eq_one (hd.pow y))
  calc _ ≤ orderOf x * orderOf y := h1
    _ ≤ p * p := Nat.mul_le_mul hx hy
    _ = p ^ 2 := (pow_two p).symm

omit [Finite G] in
theorem eq_top_of_torusImage_invariant
    (hirr : ∀ B : Subgroup G, B ≤ E → torusInvariant E Jc B → B = ⊥ ∨ B = E)
    {B : Subgroup E} (hB : ∀ g ∈ torusImage E Jc, ∀ b ∈ B, g b ∈ B) (hB1 : B ≠ ⊥) : B = ⊤ := by
  have hle : B.map E.subtype ≤ E := Subgroup.map_subtype_le B
  have hinv : torusInvariant E Jc (B.map E.subtype) := by
    intro w hw b hb
    obtain ⟨hwJ, hwN⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hb
    have hφ : E.normalizerMonoidHom ⟨w, hwN⟩ ∈ torusImage E Jc :=
      Sec12Three.mem_torusImage_iff.2 ⟨w, hwJ, hwN, rfl⟩
    refine ⟨E.normalizerMonoidHom ⟨w, hwN⟩ e, hB _ hφ e he, ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rcases hirr _ hle hinv with h0 | h1
  · exact absurd ((Subgroup.map_eq_bot_iff_of_injective B E.subtype_injective).1 h0) hB1
  · rw [eq_top_iff]
    intro e _
    have : (e : G) ∈ B.map E.subtype := by rw [h1]; exact e.2
    obtain ⟨e', he', he'e⟩ := this
    have : e' = e := Subtype.ext he'e
    rwa [← this]

end Generic

end CFSG.RankThree.PartOne.Q1327T
