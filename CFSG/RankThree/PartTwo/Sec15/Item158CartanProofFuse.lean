module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof
import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofSW
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof158Cartan

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_elemAbelian_nine {L : Subgroup G} {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) {D : Subgroup G} (hDL : D ≤ L)
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) {y z : G} (hy : y ∈ D)
    (hy1 : y ≠ 1) (hz : z ∈ D) (hz1 : z ≠ 1) : ∃ l ∈ L, l * y * l⁻¹ = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := ↥L ⧸ aschbacherSolvableCore 3 ↥L
  set πL : ↥L →* X := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπL
  set DL : Subgroup ↥L := D.subgroupOf L with hDLdef
  have hDLcard : Nat.card DL = 9 := by
    rw [hDLdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv, hD9]
  have hDLp : IsPGroup 3 DL := IsPGroup.of_card (n := 2) (by rw [hDLcard]; norm_num)
  have hinj : Set.InjOn πL (DL : Set ↥L) := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hDLp
  set Db : Subgroup X := DL.map πL with hDb
  have hDb9 : Nat.card Db = 9 := by
    rw [← hDLcard, hDb]
    refine Nat.card_congr
      (Equiv.ofBijective (fun d : DL => (⟨πL d, d, d.2, rfl⟩ : Db)) ⟨?_, ?_⟩).symm
    · intro a b hab
      exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
    · rintro ⟨_, d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  have hX9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two he hiso h9
  set S : Sylow 3 X := Sylow.ofCard Db (by rw [hDb9, hX9]; norm_num) with hS
  have hSD : (S : Subgroup X) = Db := rfl
  set yL : ↥L := ⟨y, hDL hy⟩
  set zL : ↥L := ⟨z, hDL hz⟩
  have hyDL : yL ∈ DL := Subgroup.mem_subgroupOf.mpr hy
  have hzDL : zL ∈ DL := Subgroup.mem_subgroupOf.mpr hz
  have hyb1 : πL yL ≠ 1 := by
    intro h1
    have h2 := hinj hyDL DL.one_mem (by rw [h1, map_one])
    exact hy1 (congrArg Subtype.val h2)
  have hzb1 : πL zL ≠ 1 := by
    intro h1
    have h2 := hinj hzDL DL.one_mem (by rw [h1, map_one])
    exact hz1 (congrArg Subtype.val h2)
  obtain ⟨nb, hnb, hnbyz⟩ := Sec19.Item19ResProof.transitive_sylow he hiso
    (fun h => h9 (Or.inl h)) (fun h => h9 (Or.inr h)) S (πL yL) (hSD ▸ ⟨yL, hyDL, rfl⟩) hyb1
    (πL zL) (hSD ▸ ⟨zL, hzDL, rfl⟩) hzb1
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) nb
  set M : Subgroup ↥L := Db.comap πL with hM
  have hDLM : DL ≤ M := fun d hd => ⟨d, hd, rfl⟩
  have hnDL : DL.map (MulAut.conj n).toMonoidHom ≤ M := by
    rintro _ ⟨d, hd, rfl⟩
    change πL (n * d * n⁻¹) ∈ Db
    have hmem : πL d ∈ (S : Subgroup X) := hSD ▸ ⟨d, hd, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hnb (πL d)).mp hmem
    rw [hSD] at h1
    simpa only [map_mul, map_inv] using h1
  have hM27 : ¬ 27 ∣ Nat.card M := by
    intro h27
    have hθ := (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
    have hker : πL.ker ≤ M := fun k hk => by
      change πL k ∈ Db
      rw [MonoidHom.mem_ker.mp hk]
      exact Db.one_mem
    have hrange : M.map πL = Db := by
      rw [hM, Subgroup.map_comap_eq, inf_eq_right.mpr (fun x _ =>
        QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) x)]
    have h1 := Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf πL M
    rw [hrange, hDb9] at h1
    have h2 : Nat.card (πL.ker.subgroupOf M) = Nat.card (aschbacherSolvableCore 3 ↥L) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv, hπL,
        QuotientGroup.ker_mk']
    rw [h2] at h1
    rw [← h1] at h27
    have h3 : 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) := by
      rw [show (27 : ℕ) = 9 * 3 by norm_num] at h27
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h27
    exact hθ h3
  have hsyl1 : CFSG.ABGLocalTools.IsSylowOf 3 DL M :=
    Sec17.Proof1721.isSylowOf_of_card_nine hDLM hDLcard hM27
  have hsyl2 : CFSG.ABGLocalTools.IsSylowOf 3 (DL.map (MulAut.conj n).toMonoidHom) M :=
    Sec17.Proof1721.isSylowOf_of_card_nine hnDL
      (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hDLcard]) hM27
  obtain ⟨m, hmM, hmeq⟩ := Proof158Steps.exists_conj_of_isSylowOf hsyl2 hsyl1
  have hlD : (m * n) * yL * (m * n)⁻¹ ∈ DL := by
    rw [hmeq]
    refine ⟨n * yL * n⁻¹, ⟨yL, hyDL, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have himg : πL ((m * n) * yL * (m * n)⁻¹) = πL zL := by
    have hmD : πL m ∈ Db := hmM
    have hzD : πL zL ∈ Db := ⟨zL, hzDL, rfl⟩
    have hcomm : πL m * πL zL = πL zL * πL m := by
      obtain ⟨d₁, hd₁, h₁⟩ := hmD
      obtain ⟨d₂, hd₂, h₂⟩ := hzD
      rw [← h₁, ← h₂, ← map_mul, ← map_mul]
      congr 1
      have h3 : (d₁ : G) * (d₂ : G) = (d₂ : G) * (d₁ : G) :=
        congrArg Subtype.val (hD.1.is_comm.comm
          (⟨(d₁ : G), Subgroup.mem_subgroupOf.mp hd₁⟩ : ↥D)
          ⟨(d₂ : G), Subgroup.mem_subgroupOf.mp hd₂⟩)
      exact Subtype.ext h3
    rw [map_mul, map_mul, map_inv, map_mul]
    calc πL m * πL n * πL yL * (πL m * πL n)⁻¹ =
        πL m * (πL n * πL yL * (πL n)⁻¹) * (πL m)⁻¹ := by group
      _ = πL m * πL zL * (πL m)⁻¹ := by rw [show πL n * πL yL * (πL n)⁻¹ =
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) n) * πL yL *
            (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) n)⁻¹ from rfl, hnbyz]
      _ = πL zL := by rw [hcomm, mul_inv_cancel_right]
  have heq := hinj hlD hzDL himg
  refine ⟨((m * n : ↥L) : G), (m * n).2, ?_⟩
  have := congrArg Subtype.val heq
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

end CFSG.RankThree.PartTwo.Sec15.Proof158Cartan
