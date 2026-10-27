module

public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.Quasithin.H13.A5S136h
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316J

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.A5Model
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
  CFSG.QuasithinUnique.Vol2Native.A312L

section Offender

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_of_isMaxElemAbelian {R W A : Subgroup G} (hWR : W ≤ R)
    (hW : IsElemAbelian 2 W) (hA : IsMaxElemAbelian R A) :
    (W ⊓ Subgroup.centralizer (A : Set G)).relIndex W ≤
      (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A := by
  set H₁ := A ⊓ Subgroup.centralizer (W : Set G) with hH₁
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.2.1.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm : ∀ a ∈ H₁, ∀ w ∈ W, a * w = w * a := fun a ha w hw =>
    (Subgroup.mem_centralizer_iff.mp ha.2 w hw).symm
  have hH₁e : IsElemAbelian 2 H₁ :=
    ⟨⟨⟨fun x y => Subtype.ext (hAc _ x.2.1 _ y.2.1)⟩⟩, fun x hx => hA.2.1.2 x hx.1⟩
  have hB := CFSG.Quasithin.B2F.isElemAbelian_sup_of_commute hH₁e hW hcomm
  have hcard : Nat.card ↥(H₁ ⊔ W) ≤ Nat.card A :=
    hA.2.2 (H₁ ⊔ W) (sup_le (inf_le_left.trans hA.1) hWR) hB
  have hWN : W ≤ Subgroup.normalizer (H₁ : Set G) := fun w hw =>
    (Subgroup.centralizer_le_normalizer (H₁ : Set G))
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha w hw)
  have hsup := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hWN
  have hA1 := Subgroup.relIndex_mul_card (H := H₁) (K := A)
  rw [inf_eq_left.mpr inf_le_left] at hA1
  have hW1 := Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer (A : Set G)) (K := W)
  rw [inf_eq_left.mpr inf_le_left] at hW1
  have hle : Nat.card ↥(H₁ ⊓ W) ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => Subgroup.mem_inf.mpr ⟨hx.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => hAc a ha x hx.1.1
  have hpos1 : 0 < Nat.card H₁ := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have h1 : Nat.card H₁ * Nat.card W ≤ Nat.card A * Nat.card ↥(H₁ ⊓ W) := by
    rw [← hsup]
    exact Nat.mul_le_mul_right _ hcard
  rw [← hA1, ← hW1] at h1
  have h2 : (W ⊓ Subgroup.centralizer (A : Set G)).relIndex W *
      Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤
      H₁.relIndex A * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) := by
    have h3 : Nat.card H₁ * ((W ⊓ Subgroup.centralizer (A : Set G)).relIndex W *
        Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))) ≤
        Nat.card H₁ * (H₁.relIndex A * Nat.card ↥(H₁ ⊓ W)) := by
      calc Nat.card H₁ * ((W ⊓ Subgroup.centralizer (A : Set G)).relIndex W *
            Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)))
          ≤ H₁.relIndex A * Nat.card H₁ * Nat.card ↥(H₁ ⊓ W) := h1
        _ = Nat.card H₁ * (H₁.relIndex A * Nat.card ↥(H₁ ⊓ W)) := by ring
    have h4 := Nat.le_of_mul_le_mul_left h3 hpos1
    exact h4.trans (Nat.mul_le_mul_left _ hle)
  exact Nat.le_of_mul_le_mul_right h2 hpos2

end Offender

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem pact_E12_of_InD : ∀ σ : Equiv.Perm (Fin 5), InD σ →
    pact σ E12 = E12 ∨ pact σ E12 = E12 * W4 := by
  decide +kernel

theorem conj_v12_of_mem_T {t : G} (ht : t ∈ T) :
    t * S.v12 * t⁻¹ = S.v12 ∨ t * S.v12 * t⁻¹ = S.v12 * S.z := by
  have hpc := S.psi_conj ⟨t, S.frame.T_le ht⟩ ⟨S.v12, S.v12_mem_V⟩
  rw [S.psi_v12] at hpc
  rcases pact_E12_of_InD _ (S.frame.T_D ⟨t, S.frame.T_le ht⟩ ht) with h | h
  · left
    rw [h, ← S.psi_v12] at hpc
    exact congrArg Subtype.val (S.frame.ψ.injective hpc)
  · right
    have hvz : S.frame.ψ ⟨S.v12 * S.z, V.mul_mem S.v12_mem_V S.z_mem_V⟩ = E12 * W4 := by
      rw [show (⟨S.v12 * S.z, V.mul_mem S.v12_mem_V S.z_mem_V⟩ : ↥V) =
        ⟨S.v12, S.v12_mem_V⟩ * ⟨S.z, S.z_mem_V⟩ from rfl, map_mul, S.psi_v12, S.psi_z]
    rw [h, ← hvz] at hpc
    exact congrArg Subtype.val (S.frame.ψ.injective hpc)

theorem commute_conj_v12 {t c : G} (ht : t ∈ T) (hcv : c * S.v12 = S.v12 * c)
    (hcz : c * S.z = S.z * c) :
    c * (t * S.v12 * t⁻¹) = (t * S.v12 * t⁻¹) * c := by
  rcases S.conj_v12_of_mem_T ht with h | h
  · rw [h, hcv]
  · rw [h, ← mul_assoc, hcv, mul_assoc, hcz, ← mul_assoc]

theorem T_le_normalizer_centralizer_V2 :
    T ≤ Subgroup.normalizer ((Subgroup.centralizer ({S.v12} : Set G) ⊓
      Subgroup.centralizer ({S.z} : Set G) : Subgroup G) : Set G) := by
  intro t ht
  refine L3316.mem_normalizer_of_map_le ?_
  rintro _ ⟨c, hc, rfl⟩
  have hcv := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1
  have hcz := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
  have htz := S.conj_z_of_mem_T ht
  have hti : t⁻¹ ∈ T := T.inv_mem ht
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  ·
    have h1 := S.commute_conj_v12 hti hcv hcz
    rw [inv_inv] at h1
    show t * c * t⁻¹ * S.v12 = S.v12 * (t * c * t⁻¹)
    calc t * c * t⁻¹ * S.v12 = t * (c * (t⁻¹ * S.v12 * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * S.v12 * t) * c) * t⁻¹ := by rw [h1]
      _ = S.v12 * (t * c * t⁻¹) := by group
  · show t * c * t⁻¹ * S.z = S.z * (t * c * t⁻¹)
    calc t * c * t⁻¹ * S.z = t * c * (t⁻¹ * S.z * t) * t⁻¹ := by group
      _ = t * c * S.z * t⁻¹ := by
        have h := S.conj_z_of_mem_T hti
        rw [inv_inv] at h
        rw [h]
      _ = t * S.z * c * t⁻¹ := by rw [mul_assoc t c, hcz, ← mul_assoc]
      _ = S.z * (t * c * t⁻¹) := by
        calc t * S.z * c * t⁻¹ = (t * S.z * t⁻¹) * (t * c * t⁻¹) := by group
          _ = S.z * (t * c * t⁻¹) := by rw [htz]

theorem T_le_normalizer_Tv : T ≤ Subgroup.normalizer (S.Tv : Set G) := by
  intro t ht
  refine L3316.mem_normalizer_of_map_le ?_
  rintro _ ⟨s, hs, rfl⟩
  have hsT : s ∈ T := (Subgroup.mem_inf.mp hs).1
  have hsv := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs).2
  have hti : t⁻¹ ∈ T := T.inv_mem ht
  have hsz : s * S.z = S.z * s := by
    have := S.conj_z_of_mem_T hsT
    calc s * S.z = s * S.z * s⁻¹ * s := by group
      _ = S.z * s := by rw [this]
  have h1 := S.commute_conj_v12 hti hsv hsz
  rw [inv_inv] at h1
  refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht),
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  show t * s * t⁻¹ * S.v12 = S.v12 * (t * s * t⁻¹)
  calc t * s * t⁻¹ * S.v12 = t * (s * (t⁻¹ * S.v12 * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * S.v12 * t) * s) * t⁻¹ := by rw [h1]
    _ = S.v12 * (t * s * t⁻¹) := by group

end Setting

theorem mem_normalizer_oPrimeResidualOf {G : Type} [Group G] [Finite G] {p : ℕ}
    {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (oPrimeResidualOf p H : Set G) := by
  refine L3316.mem_normalizer_of_map_le ?_
  rw [oPrimeResidualOf, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxH, k, hk⟩, rfl⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxH, k, ?_⟩
  show orderOf ((MulAut.conj g) x) = p ^ k
  rw [MulEquiv.orderOf_eq, hk]

end CFSG.Quasithin.H13.A5
