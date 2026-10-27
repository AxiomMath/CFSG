module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspD4
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTriality
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlockMain
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Chevalley (torusTorsion)

private lemma conj_range_normal {G : Type*} [Group G] :
    ((MulAut.conj : G →* MulAut G).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  refine ⟨g y, ?_⟩
  ext z
  simp [MulAut.conj_apply]

private lemma isCyclic_quotient_inn_of_ggOutCyclic {G : Type*} [Group G] (h : GGOutCyclic G) :
    IsCyclic (MulAut G ⧸ (MulAut.conj : G →* MulAut G).range) := by
  let I : Subgroup (MulAut G) := (MulAut.conj : G →* MulAut G).range
  haveI : I.Normal := conj_range_normal (G := G)
  obtain ⟨φ₀, hφ₀⟩ := h
  refine isCyclic_of_surjective
    ((QuotientGroup.mk' I).comp (Subgroup.zpowers φ₀).subtype) ?_
  intro x
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective I x
  have hα := hφ₀ α
  rw [Subgroup.mem_sup_of_normal_left] at hα
  obtain ⟨i, hi, z, hz, rfl⟩ := hα
  refine ⟨⟨z, hz⟩, ?_⟩
  show (QuotientGroup.mk' I) z = (QuotientGroup.mk' I) (i * z)
  rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff (N := I) i).mpr hi, one_mul]

theorem ggNbrG2Off_elemAbelian_card
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (A : Subgroup (MulAut (adjointGroup Tag.G2 K)))
    (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) :
    Nat.card A = 27 ∧ Nat.card ↥(A ⊓
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range) = 9 := by
  classical
  let G := adjointGroup Tag.G2 K
  let I : Subgroup (MulAut G) := (MulAut.conj : G →* MulAut G).range
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hchar : CharP K 2 := charP_two_of_card hK
  have hcenter : Subgroup.center G = ⊥ := center_adjointGroup_eq_bot
  have hconj : Function.Injective (MulAut.conj : G →* MulAut G) := mulAut_conj_injective hcenter
  haveI hInorm : I.Normal := conj_range_normal (G := G)
  have hA3 : IsPGroup 3 ↥A := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using hA.2 (x : MulAut G) x.2)
  have hBcard : Nat.card ↥(A ⊓ I) ≤ 9 := by
    have hB3 : IsPGroup 3 ↥(A ⊓ I) := hA3.to_inf_left
    let E : Subgroup G := (A ⊓ I).comap (MulAut.conj : G →* MulAut G)
    have hmapE : Subgroup.map (MulAut.conj : G →* MulAut G) E = A ⊓ I :=
      Subgroup.map_comap_eq_self (f := MulAut.conj) (H := A ⊓ I) inf_le_right
    have hcardE : Nat.card ↥E = Nat.card ↥(A ⊓ I) := by
      rw [← hmapE, Subgroup.card_map_of_injective hconj]
    have hEabel : IsElemAbelian 3 E := by
      haveI : IsMulCommutative ↥A := hA.1
      refine ⟨?_, ?_⟩
      · rw [isMulCommutative_iff]
        intro x y
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        apply hconj
        rw [map_mul, map_mul]
        exact Subgroup.mul_comm_of_mem_isMulCommutative A
          (Subgroup.mem_comap.mp x.2).1 (Subgroup.mem_comap.mp y.2).1
      · intro x hx
        apply hconj
        rw [map_pow, map_one]
        exact hA.2 (MulAut.conj x) (Subgroup.mem_comap.mp hx).1
    have hElt : Nat.card ↥E < 27 := by
      have h := CFSG.StandardType.NbrInnerNine.card_lt_cube_G2_all (K := K) hK
        Nat.prime_three (by norm_num) hEabel
      norm_num at h
      exact h
    have hlt : Nat.card ↥(A ⊓ I) < 27 := by rw [hcardE] at hElt; exact hElt
    obtain ⟨j, hj⟩ := hB3.exists_card_eq
    have hj3 : j < 3 := by
      have h3 : (3 : ℕ) ^ j < 3 ^ 3 := by
        rw [← hj]
        norm_num
        exact hlt
      exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < (3 : ℕ))).mp h3
    calc Nat.card ↥(A ⊓ I) = 3 ^ j := hj
      _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  have hcyc : IsCyclic (MulAut G ⧸ I) :=
    isCyclic_quotient_inn_of_ggOutCyclic (G := G)
      (ggOutCyclic_chev (f := n) (by omega) K hK .G2 (Or.inl ⟨rfl, hn⟩))
  let ψ : ↥A →* MulAut G ⧸ I := (QuotientGroup.mk' I).comp A.subtype
  have hker : ψ.ker = I.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [ψ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff (x : MulAut G)
  haveI : IsCyclic (MulAut G ⧸ I) := hcyc
  haveI : IsCyclic ↥ψ.range := Subgroup.isCyclic _
  have hrange_dvd : Nat.card ↥ψ.range ∣ 3 := by
    have hexp : Monoid.exponent ↥ψ.range ∣ 3 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
      intro x
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← ha, ← map_pow]
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 (a : MulAut G) a.2)
      rw [ha3, map_one]
    rwa [IsCyclic.exponent_eq_card] at hexp
  have hrange_le : Nat.card ↥ψ.range ≤ 3 := Nat.le_of_dvd (by norm_num) hrange_dvd
  have hmapA : Subgroup.map A.subtype (I.subgroupOf A) = A ⊓ I := by
    rw [← Subgroup.comap_subtype (H := I) (K := A), Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hkcard : Nat.card ↥ψ.ker = Nat.card ↥(A ⊓ I) := by
    rw [hker, ← hmapA, Subgroup.card_subtype]
  have hkr : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card ↥A :=
    Subgroup.card_ker_mul_card_range ψ
  have hk_le : Nat.card ↥ψ.ker ≤ 9 := by
    rw [hkcard]
    exact hBcard
  have hA27 : Nat.card ↥A = 27 := by
    have hle : Nat.card ↥A ≤ 27 := by
      rw [← hkr]
      calc Nat.card ↥ψ.ker * Nat.card ↥ψ.range ≤ 9 * 3 := Nat.mul_le_mul hk_le hrange_le
        _ = 27 := by norm_num
    omega
  have hk9 : Nat.card ↥ψ.ker = 9 := by
    have hkr27 : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = 27 := by rw [hkr, hA27]
    have hk_ge : 9 ≤ Nat.card ↥ψ.ker := by
      by_contra h
      have hk8 : Nat.card ↥ψ.ker ≤ 8 := by omega
      have : Nat.card ↥ψ.ker * Nat.card ↥ψ.range ≤ 8 * 3 := Nat.mul_le_mul hk8 hrange_le
      omega
    omega
  exact ⟨hA27, by rw [← hkcard]; exact hk9⟩

end CFSG.StandardType

end
