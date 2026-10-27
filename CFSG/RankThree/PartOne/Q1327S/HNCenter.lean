module

public import CFSG.RankThree.PartOne.KS.HNFiveBasic

public section

namespace CFSG.RankThree.PartOne.Q1327S

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
  CFSG.RankThree.PartOne.KS.HNFive

variable {G : Type*} [Group G] [Finite G]

variable {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G} {M : Matrix (Fin 4) (Fin 4) (ZMod 5)}
  {XU : GL (Fin 4) (ZMod 5)} {cx : Fin 4 → ℕ} {BU : Fin k → GL (Fin 4) (ZMod 5)}
  {cr : Fin k → Fin 4 → ℕ} (hR : Rel q z x r M XU cx BU cr)

include hR

theorem ker_AU_P (hX : XU ≠ 1) :
    (hR.AU.comp (Subgroup.inclusion (Rel.P_le_H (q := q) (x := x) (r := r)))).ker =
      (QG q).subgroupOf (QG q ⊔ zpowers x) := by
  have := fact5
  set L := QG q
  set P := L ⊔ zpowers x
  let φ : ↥P →* GL (Fin 4) (ZMod 5) :=
    hR.AU.comp (Subgroup.inclusion (Rel.P_le_H (q := q) (x := x) (r := r)))
  have hLP : L ≤ P := le_sup_left
  have hxmem : x ∈ P := Subgroup.mem_sup_right (mem_zpowers x)
  have hφx : φ ⟨x, hxmem⟩ = XU := hR.AU_x
  have hcardP : Nat.card P = 5 ^ 6 := hR.card_P hX
  have hcardL : Nat.card (L.subgroupOf P) = 5 ^ 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLP).toEquiv]
    exact hR.card_Q
  have hle : L.subgroupOf P ≤ φ.ker := fun g hg => by
    rw [MonoidHom.mem_ker]
    exact hR.AU_of_mem_Q (mem_subgroupOf.1 hg)
  have hidxL : (L.subgroupOf P).index = 5 := by
    have h1 := Subgroup.index_mul_card (L.subgroupOf P)
    rw [hcardL, hcardP] at h1
    omega
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hidxL] at hdvd
  rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
  · exfalso
    have htop : φ.ker = ⊤ := Subgroup.index_eq_one.1 h
    have hmem : (⟨x, hxmem⟩ : P) ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top _
    exact hX (by rw [← hφx]; exact hmem)
  · have h1 := Subgroup.card_mul_index φ.ker
    rw [h, hcardP] at h1
    have hcardK : Nat.card φ.ker = 5 ^ 5 := by omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardK, hcardL])).symm

theorem card_central_le (hX : XU ≠ 1) {E : Subgroup G} (hEP : E ≤ QG q ⊔ zpowers x)
    (hEc : ∀ y ∈ E, ∀ w ∈ QG q ⊔ zpowers x, y * w = w * y) : Nat.card E ≤ 5 := by
  have := fact5
  set L := QG q
  set P := L ⊔ zpowers x
  have hLP : L ≤ P := le_sup_left
  have hPH : P ≤ HG q x r := Rel.P_le_H
  have hker := ker_AU_P hR hX
  have hEL : ∀ y ∈ E, y ∈ L := by
    intro y hy
    have hyP : y ∈ P := hEP hy
    have hcomm : ∀ i, y⁻¹ * q i * y = q i := fun i => by
      have h1 := hEc y hy (q i) (hLP (q_mem i))
      calc y⁻¹ * q i * y = y⁻¹ * (q i * y) := by rw [mul_assoc]
        _ = y⁻¹ * (y * q i) := by rw [h1]
        _ = q i := by group
    have hA : CommData.actMat 5 q z M y = 1 := by
      rw [← hR.commData.actMat_one]
      ext i j
      simp only [CommData.actMat, Matrix.of_apply, inv_one, one_mul, mul_one, hcomm i]
    have h2 : (hR.AU.comp (Subgroup.inclusion hPH)) ⟨y, hyP⟩ = 1 :=
      Units.ext (by rw [Units.val_one]; exact hA)
    have h3 : (⟨y, hyP⟩ : ↥P) ∈ (hR.AU.comp (Subgroup.inclusion hPH)).ker := h2
    rw [hker, mem_subgroupOf] at h3
    exact h3
  have hsub : E ≤ (center L).map L.subtype := by
    intro y hy
    refine ⟨⟨y, hEL y hy⟩, mem_center_iff.2 fun l => ?_, rfl⟩
    apply Subtype.ext
    exact (hEc y hy l (hLP l.2)).symm
  calc Nat.card E ≤ Nat.card ((center L).map L.subtype) := Subgroup.card_le_of_le hsub
    _ = Nat.card (center L) := Subgroup.card_map_of_injective (Subtype.val_injective)
    _ = 5 := hR.card_center_Q

end CFSG.RankThree.PartOne.Q1327S
