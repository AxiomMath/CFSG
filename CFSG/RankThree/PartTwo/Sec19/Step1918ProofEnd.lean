module

public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step1918Proof

variable {G : Type} [Group G] [Finite G] {A L E M K F : Subgroup G} {c : G}

theorem map_conj_eq_of_mem (hctx : Ctx1912 G A c L E M)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) (hFL : F ≤ L)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) {m : G} (hm : m ∈ M) :
    K.map (MulAut.conj m).toMonoidHom = K := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := hctx.toPartTwoStanding
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  have hLM : L ≤ M := hLK.trans hKM
  set J := K.map (MulAut.conj m).toMonoidHom with hJ
  have hJM : J ∈ oTwoComponentsIn M := Sec18.map_conj_mem_oTwoComponentsIn hK hm
  have hJK : J ≠ K := hne
  have hF₂ : CFSG.Assembly.IsElemAbelian 3 (F.map (MulAut.conj m).toMonoidHom) :=
    Sec13.isElemAbelian_map hF _
  have hF₂9 : Nat.card (F.map (MulAut.conj m).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hF9]
  have hF₂J : F.map (MulAut.conj m).toMonoidHom ≤ J :=
    Subgroup.map_mono (hFL.trans hLK)
  have h4 := four_le_localRank_of_pair hQ hQ2 hMQ (CFSG.LieType.BorelTits.pCoreOf_le 2 M) hQ2
    hMQ hF hF9 (hFL.trans hLM) hF₂ hF₂9 (hF₂J.trans (le_of_mem_oTwoComponentsIn hJM))
    (fun a ha b hb => Step1910Proof.commutator_mem_pCoreOf hK hJM (Ne.symm hJK)
      (hLK (hFL ha)) (hF₂J hb))
    (fun a ha b hb hab => by
      refine Step1916Proof2.eq_one_of_forall_commutator_mem hZ hLM (hFL ha) (k := 1)
        (by rw [pow_one]; exact hF.2 a ha) fun l hl => ?_
      exact commutator_mem_of_inv_mul_mem hab (hMQ (hLM (hFL ha))) (hMQ (hLM hl))
        (Step1910Proof.commutator_mem_pCoreOf hJM hK hJK (hF₂J hb) (hLK hl)))
  rw [hst.toTheoremFourHyp.localRank_three] at h4
  omega

theorem map_conj_eq_of_le (hctx : Ctx1912 G A c L E M)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) (hFL : F ≤ L)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) {g : G}
    (hKg : K ≤ M.map (MulAut.conj g).toMonoidHom) (hgK : K.map (MulAut.conj g).toMonoidHom ≤ M) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := hctx.toPartTwoStanding
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  set Mg := M.map (MulAut.conj g).toMonoidHom with hMg
  set Y := M ⊓ Mg with hY
  set J := K.map (MulAut.conj g).toMonoidHom with hJ
  have hJMg : J ∈ oTwoComponentsIn Mg := map_mem_oTwoComponentsIn (MulAut.conj g) hK
  have hKY' : K ≤ Y := le_inf hKM hKg
  have hJY' : J ≤ Y := le_inf hgK (le_of_mem_oTwoComponentsIn hJMg)
  have hKY : K ∈ oTwoComponentsIn Y := Sec18.mem_oTwoComponentsIn_of_le hK hKY'
    (Sec18.isSubnormal_subgroupOf_of_le (mem_oTwoComponentsIn_iff.mp hK).2.2.1 inf_le_left)
  have hJY : J ∈ oTwoComponentsIn Y := Sec18.mem_oTwoComponentsIn_of_le hJMg hJY'
    (Sec18.isSubnormal_subgroupOf_of_le (mem_oTwoComponentsIn_iff.mp hJMg).2.2.1 inf_le_right)
  have hLY : L ≤ Y := hLK.trans hKY'
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hF₂ : CFSG.Assembly.IsElemAbelian 3 (F.map (MulAut.conj g).toMonoidHom) :=
    Sec13.isElemAbelian_map hF _
  have hF₂9 : Nat.card (F.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hF9]
  have hF₂J : F.map (MulAut.conj g).toMonoidHom ≤ J := Subgroup.map_mono (hFL.trans hLK)
  have h4 := four_le_localRank_of_pair hQ hQ2 (inf_le_left.trans hMQ)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) hR2 hYR hF hF9 (hFL.trans hLY) hF₂ hF₂9
    (hF₂J.trans hJY')
    (fun a ha b hb => Step1910Proof.commutator_mem_pCoreOf hKY hJY (Ne.symm hne)
      (hLK (hFL ha)) (hF₂J hb))
    (fun a ha b hb hab => by
      refine Step1916Proof2.eq_one_of_forall_commutator_mem hZ hLY (hFL ha) (k := 1)
        (by rw [pow_one]; exact hF.2 a ha) fun l hl => ?_
      exact commutator_mem_of_inv_mul_mem hab (hYR (hLY (hFL ha))) (hYR (hLY hl))
        (Step1910Proof.commutator_mem_pCoreOf hJY hKY hne (hF₂J hb) (hLK hl)))
  rw [hst.toTheoremFourHyp.localRank_three] at h4
  omega

theorem mem_of_map_conj_eq (hctx : Ctx1912 G A c L E M) (hK : K ∈ oTwoComponentsIn M)
    (hKn : ∀ m ∈ M, K.map (MulAut.conj m).toMonoidHom = K) {g : G}
    (hg : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := hctx.mem_scriptM.1
  set O := CFSG.Open.pCoreOf 2 K with hO
  have hO1 : O ≠ ⊥ :=
    Late.pCoreOf_ne_bot_of_mem_oTwoComponentsIn hctx.toTheoremFourHyp.charTwoType hM.1 hK
  set N := Subgroup.normalizer (O : Set G) with hN
  have hKN : Subgroup.normalizer (K : Set G) ≤ N :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hMN : M ≤ N := fun m hm =>
    hKN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hKn m hm))
  have hloc : CFSG.Assembly.IsTwoLocal N :=
    ⟨O, hO1, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K, rfl⟩
  have hNM : N = M := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne hMN (Ne.symm hne)) hloc
  rw [← hNM]
  exact hKN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hg)

end Step1918Proof

end CFSG.RankThree.PartTwo.Sec19
