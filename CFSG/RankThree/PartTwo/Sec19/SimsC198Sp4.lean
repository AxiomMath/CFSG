module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
import CFSG.RankThree.PartTwo.Sec19.SimsC198Crit
import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.RankThree.PartOne.LIT.RankProjective
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG.Assembly.LowTwoRank (StatedSp)

theorem isMulCommutative_of_isPGroup_three_sl2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hE : IsPGroup 3 E) :
    IsMulCommutative E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  obtain ⟨⟨f, hf0⟩, -, hf⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card, PNat.mk_coe] at hf
  by_cases h7 : 7 ≤ Nat.card K
  · let π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    have hπ : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', Item19Res2Proof.center_sl2_eq_bot]
    set E' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := E.map π
    have hpg : IsPGroup 3 ↥E' := hE.map π
    obtain ⟨R, hR⟩ := hpg.exists_le_sylow
    have hcop : Nat.Coprime 3 (Nat.card K) := by
      rw [hf]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hcyc : IsCyclic R :=
      CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K (p := 2) (f := f) hf h7
        3 (by norm_num) hcop R
    have hE'cyc : IsCyclic ↥E' := by
      have : IsCyclic ↥(E'.subgroupOf
          (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) :=
        Subgroup.isCyclic _
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hR).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hR).surjective
    have hEcyc : IsCyclic ↥E :=
      isCyclic_of_surjective (E.equivMapOfInjective π hπ).symm.toMonoidHom
        (E.equivMapOfInjective π hπ).symm.surjective
    exact hEcyc.isMulCommutative
  · have hf3 : f < 3 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 ∨
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hf]
      interval_cases f <;> norm_num
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE
    have hdvd : Nat.card E ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Subgroup.card_subgroup_dvd_card E
    rw [hk] at hdvd
    have hk1 : k ≤ 1 := by
      by_contra h
      have h9 : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
      have h9' := h9.trans hdvd
      rcases hSL with h6 | h60
      · rw [h6] at h9'
        norm_num at h9'
      · rw [h60] at h9'
        norm_num at h9'
    have hdvd3 : Nat.card E ∣ 3 := by
      rw [hk]
      interval_cases k <;> norm_num
    exact (isCyclic_of_card_dvd_prime hdvd3).isMulCommutative

theorem isMulCommutative_of_isPGroup_prod {G₁ G₂ : Type*} [Group G₁] [Group G₂] {p : ℕ}
    (h₁ : ∀ E : Subgroup G₁, IsPGroup p E → IsMulCommutative E)
    (h₂ : ∀ E : Subgroup G₂, IsPGroup p E → IsMulCommutative E)
    {Q : Subgroup (G₁ × G₂)} (hQ : IsPGroup p Q) : IsMulCommutative Q := by
  rw [isMulCommutative_iff]
  intro x y
  have c₁ := isMulCommutative_iff.mp (h₁ (Q.map (MonoidHom.fst G₁ G₂)) (hQ.map _))
    ⟨x.1.1, x.1, x.2, rfl⟩ ⟨y.1.1, y.1, y.2, rfl⟩
  have c₂ := isMulCommutative_iff.mp (h₂ (Q.map (MonoidHom.snd G₁ G₂)) (hQ.map _))
    ⟨x.1.2, x.1, x.2, rfl⟩ ⟨y.1.2, y.1, y.2, rfl⟩
  exact Subtype.ext (Prod.ext (congrArg Subtype.val c₁) (congrArg Subtype.val c₂))

theorem isMulCommutative_of_isPGroup_three_sp4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : Subgroup (StatedSp 2 K)} (hP : IsPGroup 3 P) : IsMulCommutative P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := Item19Res2Proof.exists_sylow_le_range_slPair (K := K)
  obtain ⟨c, hc⟩ := Item19Res2Proof.exists_conj_map_le_sylow' S hP
  set φ := Item19Res2Proof.slPair K
  set Q := P.map (MulAut.conj c).toMonoidHom
  have hQrange : Q ≤ φ.range := hc.trans hS
  have hQp : IsPGroup 3 Q := hP.map _
  have hQcomm : IsMulCommutative (Q.comap φ) :=
    isMulCommutative_of_isPGroup_prod (fun _ hE => isMulCommutative_of_isPGroup_three_sl2 hE)
      (fun _ hE => isMulCommutative_of_isPGroup_three_sl2 hE)
      (hQp.comap_of_injective φ Item19Res2Proof.slPair_injective)
  rw [isMulCommutative_iff]
  intro x y
  apply Subtype.ext
  apply (MulAut.conj c).injective
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  have hx : MulAut.conj c (x : StatedSp 2 K) ∈ Q := ⟨x, x.2, rfl⟩
  have hy : MulAut.conj c (y : StatedSp 2 K) ∈ Q := ⟨y, y.2, rfl⟩
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hQrange hx)
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp (hQrange hy)
  have hab := congrArg Subtype.val (isMulCommutative_iff.mp hQcomm
    ⟨a, by rw [Subgroup.mem_comap, ha]; exact hx⟩ ⟨b, by rw [Subgroup.mem_comap, hb]; exact hy⟩)
  have := congrArg φ hab
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ha, hb] at this
  exact this

theorem noLocalDatum_statedSp_two {K : Type} [Field K] [Finite K] [CharP K 2] :
    NoLocalDatum (StatedSp 2 K) := by
  intro c L hLD
  obtain ⟨P, -, hP3, hPnc⟩ := hLD.exists_nonabelian
  exact hPnc (isMulCommutative_of_isPGroup_three_sp4 hP3)

theorem noLocalDatum_projSp_two_even (n : ℕ) (hn : 1 ≤ n) :
    NoLocalDatum (CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 n)) :=
  NoLocalDatum.of_mulEquiv (KFacts.statedSpEquivProjSpOfCharTwo (GaloisField 2 n)).symm
    noLocalDatum_statedSp_two

end CFSG.RankThree.PartTwo.Sec19.SimsC198
