module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProofCore
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.CentralCover.FourGroupWitness

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem exists_coreData_of_l34 {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (hφ : Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)))
    (hEeq : E = Subgroup.zpowers c ⊔ (E ⊓ L)) (hdisj : Subgroup.zpowers c ⊓ (E ⊓ L) = ⊥) :
    ∃ X₁ X₂ M₁ M₂ : G, CoreData E (E ⊓ L) c X₁ X₂ M₁ M₂ ∧
      ∃ y ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G), y * c = c * y ∧
        (∀ b ∈ E ⊓ L, y ^ 3 * b * (y ^ 3)⁻¹ = b) ∧ ∃ b ∈ E ⊓ L, y * b * y⁻¹ ≠ b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hAE := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hctx.mem_partTwoE.1
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hst hctx.partTwoS_eq hEE (hA.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  have hFE : partTwoF G = partTwoE G :=
    (hctx.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hiso : Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) 2 2 := Or.inl ⟨by norm_num, hφ⟩
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  obtain ⟨hXs, -⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi (by norm_num) hiso
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
  have hisoθ : Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) 2 2 := by
    obtain ⟨φ⟩ := hφ
    exact Or.inl ⟨by norm_num, ⟨(QuotientGroup.quotientMulEquivOfEq hθeq).trans φ⟩⟩
  have h9 : ¬ (2 ^ 2 % 9 = 1 ∨ 2 ^ 2 % 9 = 8) := by norm_num
  have hB9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have hle : E ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      (inf_le_left.trans (le_centralizer_of_mem hE.1.1 hcE)).trans
        (centralizer_le_normalizer_zpowers c)
    have h1 := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj
    rw [← hEeq, hE.2, Nat.card_zpowers, hc3] at h1
    omega
  have hBab : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (congrArg (Subtype.val : E → G)
      (hE.1.1.is_comm.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩))⟩⟩, fun x hx => hE.1.2 x hx.1⟩
  obtain ⟨X₁, X₂, M₁, M₂, hX₁, hBX, hM₁L, hM₂L, hM₁B, hM₂B, R1, R2, R3, R4⟩ :=
    Item138Proof.exists_q8_lift inf_le_right hBab hB9 (by norm_num : 1 ≤ 2) hisoθ h9
  have hcore : CoreData E (E ⊓ L) c X₁ X₂ M₁ M₂ :=
    ⟨⟨hE.1, hE.2, hcE, hEeq, fun h => hcL h.2, hB9, hX₁, hBX⟩, hM₁B, hM₂B, hLc M₁ hM₁L,
      hLc M₂ hM₂L, R1, R2, R3, R4⟩
  refine ⟨X₁, X₂, M₁, M₂, hcore, ?_⟩
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hfacL : (Nat.card L).factorization 3 = 2 := by
    rw [(aschbacherSolvableCore 3 L).card_eq_card_quotient_mul_card_subgroup,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Item138Proof.factorization_card_three_eq_two (by norm_num) hisoθ h9,
      Nat.factorization_eq_zero_of_not_dvd hθ.2.2.1]
  set P := E ⊔ A with hP
  have hP3 : IsPGroup 3 P := hctx.isPGroup_sup
  have h3L : 3 ∣ Nat.card L :=
    (Step1914TriProof.three_dvd_card_of_isoLThreePi (by norm_num) hiso).trans
      (Subgroup.card_quotient_dvd_card _)
  have hEAH : E ⊔ A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    sup_le (hctx.le_centralizer.trans (centralizer_le_normalizer_zpowers c))
      ((le_centralizer_of_mem hA.1 hcA).trans (centralizer_le_normalizer_zpowers c))
  have hPN : P ≤ Subgroup.normalizer (L : Set G) :=
    hEAH.trans (Step1914TriProof.normalizer_zpowers_le_of_three_dvd hctx h3L)
  have hPL9 : Nat.card (P ⊓ L : Subgroup G) ≤ 9 := by
    have h1 := Item138Proof.card_le_of_isPGroup (p := 3) (inf_le_right : P ⊓ L ≤ L)
      (hP3.to_le inf_le_left)
    rwa [hfacL] at h1
  have hBPL : E ⊓ L = P ⊓ L :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right L le_sup_left) (by rw [hB9]; exact hPL9)
  have hAN : A ≤ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := by
    intro a ha
    have haP : a ∈ P := le_sup_right (a := E) ha
    rw [hBPL, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxP, hxL⟩
      exact ⟨P.mul_mem (P.mul_mem haP hxP) (P.inv_mem haP),
        (Subgroup.mem_normalizer_iff.mp (hPN haP) x).mp hxL⟩
    · rintro ⟨hxP, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hPN haP) x).mpr hxL⟩
      have h1 : a⁻¹ * (a * x * a⁻¹) * a ∈ P := P.mul_mem (P.mul_mem (P.inv_mem haP) hxP) haP
      simpa [mul_assoc] using h1
  have hAmax : ∀ B' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B' → A ≤ B' → B' = A :=
    hD.mem_partTwoF.2.1
  have hBA : ¬ E ⊓ L ≤ A := by
    intro hle
    have hEA : E ≤ A := hEeq ▸ sup_le (Subgroup.zpowers_le.mpr hcA) hle
    have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hE.2, hAE.2])
    exact hctx.not_mem_partTwoT (hEA' ▸ hctx.mem_partTwoT)
  obtain ⟨b, hbB, hbA⟩ := Set.not_subset.mp hBA
  have hex : ∃ a ∈ A, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have hab := Sec15.isElemAbelian_sup_zpowers hA (hE.1.2 b hbB.1) hall
    have heq := hAmax _ hab le_sup_left
    exact hbA (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  obtain ⟨a, haA, hab⟩ := hex
  refine ⟨a, hAN haA, congrArg Subtype.val (hA.1.is_comm.comm ⟨a, haA⟩ ⟨c, hcA⟩), ?_, b, hbB, ?_⟩
  · intro x _
    rw [hA.2 a haA, inv_one, one_mul, mul_one]
  · intro h1
    apply hab
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h1]

end CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof
