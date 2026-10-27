module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardRes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSp6B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def H1SpSixNatural : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W), Z ≤ fixV H → commV H = ⊤ →
        (FFModel.nat (StatedSp 3 K)).Realizes H ⊤ Z →
          Z = ⊥ ∨ (Nat.card Z = 2 ∧
            ∃ Q : W → ZMod 2, IsQuadF2 Q ∧ QuadInvariant Q H ∧
              (∀ x : W, (∀ y : W, polarQ Q x y = 0) ↔ x ∈ Z) ∧
              (∀ z : W, z ∈ Z → z ≠ 1 → Q z ≠ 0))

theorem s16c11_v1_cover_sp_six (h : H1SpSixNatural) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W), Z ≤ fixV H → commV H = ⊤ →
        (FFModel.nat (StatedSp 3 K)).Realizes H ⊤ Z →
          Z = ⊥ ∨ (Nat.card Z = 2 ∧
            ∃ Q : W → ZMod 2, IsQuadF2 Q ∧ QuadInvariant Q H ∧
              (∀ x : W, (∀ y : W, polarQ Q x y = 0) ↔ x ∈ Z) ∧
              (∀ z : W, z ∈ Z → z ≠ 1 → Q z ≠ 0)) :=
  h K hK

theorem s16c11_v1_rf3_sp_six (h : H1SpSixNatural) (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (hsig : D.sig = {3})
    (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsSpn ↥L₀ 6 1) (hSp : IsSpn ↥(lBar ⊥ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    S16C11RF3 L₀ J₀ := by
  classical
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => NatSpn H U Z 6 1) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => NatSpn H U Z 6 1) :=
    s16e_two_fam_sp D hV hSp hsum'
  have hP : ∀ (H : Subgroup (MulAut (vStar D.M ⊥ V hV L)))
      (U Z : Subgroup (vStar D.M ⊥ V hV L)), NatSpn H U Z 6 1 →
        ∃ D' : FFModel, (∃ (K : Type) (_ : Field K) (_ : Finite K),
          Nat.card K = 2 ∧ D' = FFModel.nat (StatedSp 3 K)) ∧ D'.Realizes H U Z := by
    intro H U Z hN
    obtain ⟨-, K, hFld, hFin, hK1, hR⟩ := hN
    letI : Field K := hFld
    letI : Finite K := hFin
    have hK2 : Nat.card K = 2 := by rw [pow_one] at hK1; exact hK1
    refine ⟨FFModel.nat (StatedSp 3 K), ⟨K, hFld, hFin, hK2, rfl⟩, ?_⟩
    rw [← (show (6 : ℕ) / 2 = 3 by norm_num)]
    exact hR
  obtain ⟨φ, hφcoe, hcomm, hfixne, D', hQD', hRD'⟩ :=
    s16c11_v1_hard_nat_section D hin h1217 hc hs (P := fun H U Z => NatSpn H U Z 6 1)
      (Q := fun D' => ∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = 2 ∧ D' = FFModel.nat (StatedSp 3 K)) hF hP hV1 hM
  obtain ⟨K, hFld, hFin, hK2, hD'eq⟩ := hQD'
  letI : Field K := hFld
  letI : Finite K := hFin
  rw [hD'eq] at hRD'
  have hJ2 : ∀ w : ↥J₀, w ^ 2 = 1 := fun w => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact s15_Infra_vtil_sq_eq_one ⊥ V hV (w : Vtil ⊥ V hV))
  have hcov := s16c11_v1_cover_sp_six h (K := K) hK2 (↥J₀) hJ2 φ.range (fixV φ.range)
    le_rfl hcomm hRD'
  obtain ⟨-, Q, hQ, hQi, hQrad, hQZ⟩ := hcov.resolve_left hfixne
  have hrf3H : S16C11RF3 φ.range (⊤ : Subgroup ↥J₀) :=
    s16c11_v1_rf3_of_cover_quad (D := FFModel.nat (StatedSp 3 K))
      (FFModel.nat_faithful (StatedSp 3 K))
      (s16c11_modelRF3_statedSp (r := 3) hK2 (by norm_num)) hRD'
      ⟨Q, hQ, hQi, hQrad, hQZ⟩
  have hZ : ∀ k ∈ kBar D.M ⊥ V hV L,
      (∀ k' ∈ kBar D.M ⊥ V hV L, k * k' = k' * k) → k = 1 := by
    intro k hk hkc
    have h1 : (⟨k, hk⟩ : ↥(kBar D.M ⊥ V hV L)) = 1 :=
      s16c167_center_of_isSym_three hK ⟨k, hk⟩
        (fun y => Subtype.ext (hkc (y : MulAut (Vtil ⊥ V hV)) y.2).symm)
    exact congrArg Subtype.val h1
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hle : lBar ⊥ V hV L ≤ L₀ := by
    refine s16c1614_le_right_of_centralizes hdir hLM ?_ hZ
    intro n hn k hk
    exact (Subgroup.mem_centralizer_iff.1 hk.2) n hn
  have hLK : ∀ l ∈ lBar ⊥ V hV L, ∀ k ∈ kBar D.M ⊥ V hV L, l * k = k * l := by
    intro l hl k hk
    exact (s16c11_comm_of_isInternalDirect hdir k hk l (hle hl)).symm
  have hJ : ∀ l ∈ lBar ⊥ V hV L, ∀ j ∈ J₀, l j ∈ J₀ :=
    fun l hl j hj => s16c11_mem_of_model (s15_Infra_vtil_sq_eq_one ⊥ V hV) hM
      (hLM hl) (hLK l hl) hj
  have hinj : Function.Injective (CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ) :=
    s16c11_v1_resHom_injective hM hLM hLK hJ
  have hφeq : φ = CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro j
    apply Subtype.ext
    rw [hφcoe x j, CFSG.Quasithin.H13.VolI.coe_resHom_apply]
  have hrf3' : S16C11RF3 (CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ).range
      (⊤ : Subgroup ↥J₀) := by
    rw [← hφeq]
    exact hrf3H
  have hrf3l : S16C11RF3 (lBar ⊥ V hV L) J₀ :=
    s16c11_v1_rf3_of_resHom hJ hinj hrf3'
  have hleEq : lBar ⊥ V hV L = L₀ := s16c11_eq_of_isSpn_six_le hL₀ hSp hle
  rw [hleEq] at hrf3l
  exact hrf3l

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
