module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4b
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4c
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4d

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter (PSL2)

variable {G : Type} [Group G] [Finite G]

theorem step4b_normalizes {y b : G} {L' Q : Subgroup G} (hL' : L' ∈ thetaComponentsAt 3 y)
    (hZ : Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') = ⊥) (hb : b ∈ L') (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) (hQ2 : IsPGroup 2 Q) (hQy : Q ≤ Subgroup.centralizer ({y} : Set G))
    (hbQ : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) : Q ≤ Subgroup.normalizer (L' : Set G) :=
  Hering611S3Step4bProof.normalizes hL' hZ hb hb3 hb1 hQ2 hQy hbQ

theorem step4c_faithful (hbig : NoBig3 G) {A L' Q : Subgroup G} {y d : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : 27 < Nat.card A)
    (hAL : A ≤ Subgroup.normalizer (L' : Set G)) (hQ2 : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (L' : Set G)) (hyQ : ∀ q ∈ Q, y * q = q * y)
    (hdQ : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hyA : y ∈ A) (hdA : d ∈ A)
    (hdec : A ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers d ⊔ (A ⊓ L')) :
    ∀ q ∈ Q, ∀ hq : q ∈ Subgroup.normalizer (L' : Set G),
      Sec12.thetaBarAct L' ⟨q, hq⟩ = 1 → q = 1 :=
  Hering611S3Step4cProof.faithful hbig hA hA81 hAL hQ2 hQN hyQ hdQ hyA hdA hdec

theorem step4d_commutes {L' Q : Subgroup G} {d b s : G}
    (e : L' ⧸ aschbacherSolvableCore 3 L' ≃* PSL2 (GaloisField 3 6))
    (hQ2 : IsPGroup 2 Q) (hQN : Q ≤ Subgroup.normalizer (L' : Set G))
    (hfaith : ∀ q ∈ Q, ∀ hq : q ∈ Subgroup.normalizer (L' : Set G),
      Sec12.thetaBarAct L' ⟨q, hq⟩ = 1 → q = 1)
    (hdN : d ∈ Subgroup.normalizer (L' : Set G)) (hd3 : d ^ 3 = 1) (hbL : b ∈ L')
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hdb : d * b = b * d)
    (hdQ : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hbQ : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hsQ : s ∈ Q)
    (hsd : d * s = s * d) (hsb : b * s ≠ s * b) : ∀ q ∈ Q, d * q = q * d :=
  Hering611S3Step4dProof.commutes e hQ2 hQN hfaith hdN hd3 hbL hb3 hb1 hdb hdQ hbQ hsQ hsd hsb

theorem step4_core (hbig : NoBig3 G) {A L' R : Subgroup G} {y d b s : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : 27 < Nat.card A)
    (hAL : A ≤ Subgroup.normalizer (L' : Set G)) (hyA : y ∈ A) (hdA : d ∈ A)
    (hbA : b ∈ A) (hL' : L' ∈ thetaComponentsAt 3 y)
    (e : L' ⧸ aschbacherSolvableCore 3 L' ≃* PSL2 (GaloisField 3 6))
    (hdec : A ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers d ⊔ (A ⊓ L')) (hbL : b ∈ L')
    (hb1 : b ≠ 1) (hy3 : y ^ 3 = 1) (hd3 : d ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hR2 : IsPGroup 2 R) (hRd : ∀ r ∈ R, d * r * d⁻¹ ∈ R) (hRb : ∀ r ∈ R, b * r * b⁻¹ ∈ R)
    (hsR : s ∈ R) (hsy : y * s = s * y) (hsd : d * s = s * d) (hsb : b * s ≠ s * b) :
    ∀ r ∈ R, y * r = r * y → d * r = r * d := by
  have hcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hZ : Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 6))
  set Q : Subgroup G := R ⊓ Subgroup.centralizer ({y} : Set G) with hQdef
  have hQ2 : IsPGroup 2 Q := hR2.to_le inf_le_left
  have hQy : Q ≤ Subgroup.centralizer ({y} : Set G) := inf_le_right
  have hyQ : ∀ q ∈ Q, y * q = q * y := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hQy hq)).symm
  have hQinv : ∀ x ∈ A, (∀ r ∈ R, x * r * x⁻¹ ∈ R) → ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := by
    intro x hx hxR q hq
    refine ⟨hxR q hq.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hcomm y hyA x hx
    have h2 := hyQ q hq
    calc x * q * x⁻¹ * y = x * q * (x⁻¹ * y) := by group
      _ = x * q * (y * x⁻¹) := by
          rw [show x⁻¹ * y = y * x⁻¹ from by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1]; group]
      _ = x * (q * y) * x⁻¹ := by group
      _ = x * (y * q) * x⁻¹ := by rw [h2]
      _ = y * (x * q * x⁻¹) := by
          rw [show x * (y * q) * x⁻¹ = (x * y) * q * x⁻¹ from by group, ← h1]; group
  have hdQ : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q := hQinv d hdA hRd
  have hbQ : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q := hQinv b hbA hRb
  have hQN : Q ≤ Subgroup.normalizer (L' : Set G) :=
    step4b_normalizes hL' hZ hbL hb3 hb1 hQ2 hQy hbQ
  have hfaith := step4c_faithful hbig hA hA81 hAL hQ2 hQN hyQ hdQ hyA hdA hdec
  have hsQ : s ∈ Q := ⟨hsR, Subgroup.mem_centralizer_singleton_iff.mpr hsy.symm⟩
  have hcd := step4d_commutes e hQ2 hQN hfaith (hAL hdA) hd3 hbL hb3 hb1
    (hcomm d hdA b hbA) hdQ hbQ hsQ hsd hsb
  intro r hr hry
  exact hcd r ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hry.symm⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
