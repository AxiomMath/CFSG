module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofStatements
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
public import CFSG.RankThree.PartOne.KF.R7Levi2
public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.SP4C.WeylTorus
import CFSG.RankThree.PartTwo.Sec21.Item222ProofStar

public section

namespace CFSG.RankThree.PartTwo.Sec21.Sp4Lines

open Matrix CFSG CFSG.RankThree
open CFSG.Assembly.RankThreeEven (projSL projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor spRev b7 b7' coe_b7 coe_b7' spBlock spBlock'
  spBlock_injective spBlock'_injective perfectResidual_centralizer_b7
  perfectResidual_centralizer_b7' d8Vec_four exists_conj_into_d8Tor_sp)
open U4Lines (torusD torusD_apply line_cases weyl₁ weyl₂ conj_weyl₁ conj_weyl₂)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem lines_perfectResidual_sp {b : ℕ} (hb : 0 < b) (hbe : Even b) (hK : Nat.card K = 2 ^ b)
    {X : Subgroup ↥(spRev K)} (hX : X.map (spRev K).subtype ≤ d8Tor 3 K 4)
    (h3 : Nat.card X = 3) :
    Nonempty (inSubgroup perfectResidual ((⊤ : Subgroup ↥(spRev K)) ⊓
      Subgroup.centralizer (X : Set ↥(spRev K))) ≃* SpecialLinearGroup (Fin 2) K) := by
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb2
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact three_dvd_two_pow_sub_one hbe
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 := CFSG.LinearGroups.card_rootsOfUnity_of_dvd hdvd
  have : Nontrivial (rootsOfUnity 3 K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 K)
  set ζ : Kˣ := (ω : Kˣ) with hζ
  have hζ3 : ζ ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ω.2
  have hζ1 : ζ ≠ 1 := fun h => hω (Subtype.ext h)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply hζ1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hζ3, h, inv_one, one_mul]
  set w₁ : ↥(spRev K) := ⟨weyl₁, CFSG.RankThree.PartOne.SP4C.hP_spRev _ (by decide)⟩ with hw₁
  set w₂ : ↥(spRev K) := ⟨weyl₂, CFSG.RankThree.PartOne.SP4C.hP_spRev _ (by decide)⟩ with hw₂
  have e2 : torusD ((1, ω) : D8Mod 3 K) = ((b7 ζ : ↥(spRev K)) : GL (Fin 4) K) := by
    rw [coe_b7, torusD_apply, d8Vec_four]
    rfl
  have e3 : torusD ((ω, ω) : D8Mod 3 K) = ((b7' ζ : ↥(spRev K)) : GL (Fin 4) K) := by
    rw [coe_b7', torusD_apply, d8Vec_four]
  have e1 : torusD ((ω, 1) : D8Mod 3 K) = ((w₁ * b7 ζ * w₁⁻¹ : ↥(spRev K)) : GL (Fin 4) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← e2]
    exact (conj_weyl₁ ((1, ω) : D8Mod 3 K)).symm
  have e4 : torusD ((ω, ω⁻¹) : D8Mod 3 K) =
      ((w₂ * b7' ζ * w₂⁻¹ : ↥(spRev K)) : GL (Fin 4) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← e3]
    exact (conj_weyl₂ ((ω, ω) : D8Mod 3 K)).symm
  have key : ∀ y : ↥(spRev K), X.map (spRev K).subtype = Subgroup.zpowers (y : GL (Fin 4) K) →
      X = Subgroup.zpowers y := by
    intro y h
    apply Subgroup.map_injective (spRev K).subtype_injective
    rw [h, MonoidHom.map_zpowers]
    rfl
  have hC : ∀ y : ↥(spRev K), inSubgroup perfectResidual ((⊤ : Subgroup ↥(spRev K)) ⊓
      Subgroup.centralizer ((Subgroup.zpowers y : Subgroup ↥(spRev K)) : Set ↥(spRev K))) =
      inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set ↥(spRev K))) := by
    intro y
    rw [top_inf_eq, Item222Proof.centralizer_zpowers_eq]
  have hconj : ∀ (w y : ↥(spRev K)), Subgroup.zpowers (w * y * w⁻¹) =
      (Subgroup.zpowers y).map (MulAut.conj w).toMonoidHom := by
    intro w y
    rw [MonoidHom.map_zpowers]
    rfl
  have iso7 : Nonempty (inSubgroup perfectResidual
      (Subgroup.centralizer ({b7 ζ} : Set ↥(spRev K))) ≃* SpecialLinearGroup (Fin 2) K) := by
    rw [perfectResidual_centralizer_b7 hK4 hζ1 hζ2]
    exact ⟨(MonoidHom.ofInjective spBlock_injective).symm⟩
  have iso7' : Nonempty (inSubgroup perfectResidual
      (Subgroup.centralizer ({b7' ζ} : Set ↥(spRev K))) ≃* SpecialLinearGroup (Fin 2) K) := by
    rw [perfectResidual_centralizer_b7' hK4 hζ2]
    exact ⟨(MonoidHom.ofInjective spBlock'_injective).symm⟩
  have hX3 : Nat.card (X.map (spRev K).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (spRev K).subtype_injective, h3]
  rcases line_cases hμ hω hX hX3 with h | h | h | h
  · rw [e1] at h
    rw [key _ h, hconj, U4Lines.perfectResidual_conj (Subgroup.mem_top w₁), hC]
    obtain ⟨i⟩ := iso7
    exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj w₁).injective).symm.trans i⟩
  · rw [e2] at h
    rw [key _ h, hC]
    exact iso7
  · rw [e3] at h
    rw [key _ h, hC]
    exact iso7'
  · rw [e4] at h
    rw [key _ h, hconj, U4Lines.perfectResidual_conj (Subgroup.mem_top w₂), hC]
    obtain ⟨i⟩ := iso7'
    exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj w₂).injective).symm.trans i⟩

end CFSG.RankThree.PartTwo.Sec21.Sp4Lines

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree
open CFSG.Assembly.RankThreeEven (projSL projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open U4Lines (mapL card_mapL perfectResidualEquiv)

theorem ks222Sp4 : KS222Sp4 := by
  intro G _ _ L ℓ n hn he ⟨eL⟩ hℓL hℓ3
  set K := GaloisField 2 n with hKdef
  have hK : Nat.card K = 2 ^ n := GaloisField.card 2 n hn.ne'
  let e₀ : projSp 2 K ≃* ↥(CFSG.RankThree.PartOne.KFU.spRev K) :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 K)).symm.trans
      ((CFSG.RankThree.PartOne.KFU.spEquivProj (K := K) (by norm_num)).symm.trans
        (CFSG.RankThree.PartOne.KFU.spRevEquiv K))
  let e : L ≃* ↥(⊤ : Subgroup ↥(CFSG.RankThree.PartOne.KFU.spRev K)) :=
    (eL.trans e₀).trans Subgroup.topEquiv.symm
  set X := mapL e ℓ with hXdef
  have hX3 : Nat.card X = 3 := by rw [card_mapL e hℓL, hℓ3]
  have hXe : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
    rw [hX3] at h
    exact congrArg Subtype.val h
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact three_dvd_two_pow_sub_one he
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KFU.exists_conj_into_d8Tor_sp Nat.prime_three
    (by norm_num) hdvd X hXe
  set X' := X.map (MulAut.conj g).toMonoidHom with hX'def
  have hX' : X'.map (CFSG.RankThree.PartOne.KFU.spRev K).subtype ≤
      CFSG.RankThree.PartOne.KFU.d8Tor 3 K 4 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hg x hx
  have hX'3 : Nat.card X' = 3 := by
    rw [hX'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hX3]
  obtain ⟨eS⟩ := Sp4Lines.lines_perfectResidual_sp hn he hK hX' hX'3
  have hconj := U4Lines.perfectResidual_conj (Subgroup.mem_top g) X
  rw [hX'def.symm] at hconj
  refine ⟨(perfectResidualEquiv e hℓL).trans
    ((Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).trans
      ((MulEquiv.subgroupCongr hconj.symm).trans (eS.trans (projSLTwoEquivSL K).symm)))⟩

end CFSG.RankThree.PartTwo.Sec21
