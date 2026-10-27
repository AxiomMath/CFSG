module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1421
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTransv
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

@[expose] noncomputable def Item1412NotPGLR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        ¬ Sec8.IsZ3PGLThreePi (lBarA c' L' A)

@[expose] noncomputable def Step1420A7TwoR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) →
        ((Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
            Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
          Nonempty (lBarA c' L' A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
          (omegaA A).ncard = 3 ∧
          (∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
            F = (Subgroup.zpowers c').map (MulAut.conj w).toMonoidHom) ∧
          ∃ t ∈ Subgroup.normalizer (A : Set G), t * c' * t⁻¹ = c'⁻¹ ∧
            ∃ (ht : t ∈ Subgroup.normalizer (L' : Set G))
              (e : L' ⧸ aschbacherSolvableCore 3 L' ≃* alternatingGroup (Fin 7))
              (τ : Equiv.Perm (Fin 7)), τ.IsSwap ∧ ∀ y : L' ⧸ aschbacherSolvableCore 3 L',
                ((e (Sec4.thetaQuotMulAut L' (L'.normalizerMonoidHom ⟨t, ht⟩) y) :
                    Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹) → False

namespace Proof1413Res2

variable {G : Type} [Group G] [Finite G]

theorem m12_of_fixed
    (h133 : Item133) (h1416 : Item1416R) (hPGL : Item1412NotPGLR)
    {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (hR : Sec15R G A c₀ L₀)
    (hfail : Fail1411 A (lB A)) {a : G} (ha : Subgroup.zpowers a ∈ omegaA A)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    (hmove : ∀ f ∈ A, f ≠ 1 → Subgroup.zpowers f ≠ Subgroup.zpowers a →
      ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G))
    {b : G} (hb : Subgroup.zpowers b ∈ gammaA A (lB A))
    (hba : Subgroup.zpowers b ≠ Subgroup.zpowers a) {Lb : Subgroup G} (hLb : Lb ∈ lA A b) :
    Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  have hSb := Proof1413.sec14Std_at hR.toSec14Std hb.1 hLb
  have hDb := hSb.toSec13Data
  rcases h133 G A b Lb hDb hSb.hypS_or_hypT with h1 | ⟨-, -, -, htr, -⟩ | h3 | hP | hM | hJ
  · exact absurd h1 (hmove b hDb.mem_A hDb.ne_one hba)
  · obtain ⟨w, hw, haw⟩ := htr _ ha
    exact absurd (eq_of_eq_map_conj_of_le_normalizer hW hw haw) hba
  · obtain ⟨w, hw, haw⟩ : Subgroup.zpowers a ∈
        orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers b) := by
      rw [← h3.2.2.2.2.2.1]
      exact ha
    exact absurd (eq_of_eq_map_conj_of_le_normalizer hW hw haw) hba
  · exact absurd hP (hPGL G A c₀ L₀ hR hfail b hb Lb hLb)
  · obtain ⟨ψ⟩ := hM
    exact Sec13.nonempty_thetaQuot_equiv hDb hM12p ψ
  · obtain ⟨ψ⟩ := hJ
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hDb hJ2p ψ
    exact ((h1416 G A c₀ L₀ hR hfail b hb.1 Lb hLb).false χ).elim

theorem false_of_case_three (h1419 : Item1419R) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) {c : G}
    (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A)) {L : Subgroup G} (hL : L ∈ lA A c)
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hcL : c ∉ L)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)))
    (hBW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    (hPe : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)) (hP9 : Nat.card (oThreeWStar A) = 9)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) : False := by
  have hS : Sec14Std G A c L := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hcA : c ∈ A := hD.mem_A
  have hperf : Group.IsPerfect (Sec12.lBar c L) := by
    obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    have := (Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt).1
    exact Group.IsPerfect.ofSurjective (f := η.toMonoidHom) η.surjective
  obtain ⟨ψ⟩ := hprod
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := Sec13.card_inf_eq_nine hD hperf ψ
  have htr := Proof1413.exists_transvection hS.isE27 hcA
    (fun h : c ∈ A ⊓ L => hcL (Subgroup.mem_inf.mp h).2) inf_le_left h9 hBW
    (inf_le_right : L ⊓ Subgroup.normalizer (A : Set G) ≤ _) hirr hPe hP9
  obtain ⟨R₀, hR₀⟩ := exists_mem_scriptQPiStar A L (lB A) (piOf 2)
  obtain ⟨-, hset⟩ := h1419 G A c₀ L₀ hR hfail c hcΓ L hL htype R₀ hR₀
  have hmem : A ⊓ Subgroup.centralizer (R₀ : Set G) ⊓ L ∈
      {F | F ∈ gammaA A (lB A) ∧ F ≤ A ⊓ Subgroup.centralizer (R₀ : Set G)} := by
    rw [hset]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨hzΓ, -⟩ := hmem
  obtain ⟨-, h3, z, hz, -⟩ := hzΓ.1
  have hzB : z ∈ A ⊓ Subgroup.centralizer (R₀ : Set G) ⊓ L := hz ▸ Subgroup.mem_zpowers z
  obtain ⟨w, hw, -, hwc⟩ := htr z ⟨hzB.1.1, hzB.2⟩
  have hczΓ : Subgroup.zpowers (c * z) ∈ gammaA A (lB A) := by
    have h1 := map_conj_mem_gammaA hw hcΓ
    rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc] at h1
  have hcR : c ∈ A ⊓ Subgroup.centralizer (R₀ : Set G) :=
    ⟨hcA, Subgroup.mem_centralizer_iff.mpr fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hR₀.prop.1.2 hr))⟩
  have hczB : Subgroup.zpowers (c * z) ≤ A ⊓ Subgroup.centralizer (R₀ : Set G) :=
    Subgroup.zpowers_le.mpr (mul_mem hcR hzB.1)
  rcases Proof1413.eq_or_eq_of_set_eq hset hczΓ hczB with h | h
  ·
    have h1 : c * z ∈ Subgroup.zpowers c := h ▸ Subgroup.mem_zpowers (c * z)
    have h2 : z ∈ L ⊓ Subgroup.zpowers c := by
      refine ⟨hzB.2, ?_⟩
      have h4 := mul_mem (inv_mem (Subgroup.mem_zpowers c)) h1
      rwa [inv_mul_cancel_left] at h4
    rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL,
      Subgroup.mem_bot] at h2
    rw [hz, h2, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    norm_num at h3
  ·
    have h1 : c * z ∈ L := (h ▸ Subgroup.mem_zpowers (c * z) :
      c * z ∈ A ⊓ Subgroup.centralizer (R₀ : Set G) ⊓ L).2
    apply hcL
    have h4 := mul_mem h1 (inv_mem hzB.2)
    rwa [mul_inv_cancel_right] at h4

end Proof1413Res2

end CFSG.RankThree.PartTwo.Sec14
