module

public import CFSG.Quasithin.Background.I4Dihedral
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.I4

open CFSG.Open CFSG.GorensteinWalter

theorem nonempty_psl3_two_equiv_psl2_seven :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₂ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  exact ⟨(e₁.trans e₂).trans e⟩

theorem nonempty_psl2_equiv_zmod {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime)
    (hK : Fintype.card K = p) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
  ⟨(psl2RingEquiv (ZMod.ringEquivOfPrime K hp hK)).symm⟩

theorem nonempty_psl2_equiv_alternating_six {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 9) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 6)) := by
  open CFSG.LocalAnalysis.ComponentInitial in
  exact unique_field_nine_projective_linear_alternating_six_isomorphism K hK

theorem index_ne_two_of_isConj {G : Type*} [Group G] [Finite G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (T : Sylow 2 G) {n : ℕ}
    (hn : 2 ≤ n) (e : (T : Subgroup G) ≃* DihedralGroup n) (M : Subgroup G) : M.index ≠ 2 := by
  intro hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMn : M.Normal := Subgroup.normal_of_index_eq_two hM
  obtain ⟨m, hm, rfl⟩ := exists_eq_two_pow_of_dihedral T hn e
  have hrel : M.relIndex T ∣ 2 := by
    have h := Subgroup.relIndex_dvd_index_of_normal M T
    rwa [hM] at h
  have hcardT : Nat.card (T : Subgroup G) = 2 * 2 ^ m :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hcardTM : 2 ∣ Nat.card (M.subgroupOf T) := by
    have h := (M.subgroupOf T).card_mul_index
    rw [hcardT] at h
    change Nat.card (M.subgroupOf T) * M.relIndex T = _ at h
    rcases (Nat.dvd_prime Nat.prime_two).mp hrel with h1 | h2
    · rw [h1, mul_one] at h
      rw [h]
      exact dvd_mul_right 2 _
    · rw [h2] at h
      have h' : Nat.card (M.subgroupOf T) = 2 ^ m := by omega
      rw [h']
      exact dvd_pow_self 2 (by omega)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hcardTM
  have hwM : ((w : T) : G) ∈ M := w.2
  have hwo : orderOf ((w : T) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hinvM : ∀ u : G, orderOf u = 2 → u ∈ M := by
    intro u hu
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hinv _ u hwo hu)
    exact hMn.conj_mem _ hwM c
  have hsr : ∀ i : ZMod (2 ^ m), ((e.symm (DihedralGroup.sr i) : T) : G) ∈ M := by
    intro i
    apply hinvM
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hTM : (T : Subgroup G) ≤ M := by
    intro t ht
    have ht' : (⟨t, ht⟩ : T) = e.symm (e ⟨t, ht⟩) := (e.symm_apply_apply _).symm
    have hval : t = ((e.symm (e ⟨t, ht⟩) : T) : G) := congrArg Subtype.val ht'
    rw [hval]
    rcases e ⟨t, ht⟩ with i | i
    · have hr : DihedralGroup.r i = DihedralGroup.sr 0 * DihedralGroup.sr i := by
        rw [DihedralGroup.sr_mul_sr, sub_zero]
      rw [hr, map_mul, Subgroup.coe_mul]
      exact M.mul_mem (hsr 0) (hsr i)
    · exact hsr i
  have hidx := Subgroup.relIndex_mul_index hTM
  rw [hM] at hidx
  exact T.not_dvd_index (hidx ▸ dvd_mul_left 2 _)

theorem psl2_of_isConj
    (G : Type) [Group G] [Finite G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {z : G} (hz : orderOf z = 2)
    {k : ℕ} (hk : 1 ≤ k)
    (hC : Nonempty (Subgroup.centralizer ({z} : Set G) ≃* DihedralGroup (2 ^ k))) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Odd (Fintype.card K) ∧
      (Fintype.card K + 1 = 2 ^ (k + 1) ∨ Fintype.card K = 2 ^ (k + 1) + 1) ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hC
  have hn : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hCp : IsPGroup 2 (Subgroup.centralizer ({z} : Set G)) := by
    refine IsPGroup.of_card (n := k + 1) ?_
    rw [Nat.card_congr e₀.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  obtain ⟨S, hCS⟩ := hCp.exists_le_sylow
  have : Nontrivial (S : Subgroup G) := by
    refine ⟨⟨⟨z, hCS (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩, 1, fun h => ?_⟩⟩
    have h' : z = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hz
    norm_num at hz
  obtain ⟨z₀, hz₀, hSz₀⟩ := exists_central_involution S
  obtain ⟨c, hc⟩ := isConj_iff.mp (hinv z z₀ hz hz₀)
  have hmap : (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer {z₀} := by
    rw [map_centralizer_singleton, ← hc]
    rfl
  have hCp₀ : IsPGroup 2 (Subgroup.centralizer ({z₀} : Set G)) :=
    hmap ▸ hCp.map (MulAut.conj c).toMonoidHom
  have hCS₀ : Subgroup.centralizer ({z₀} : Set G) = S := S.is_maximal' hCp₀ hSz₀
  let eS : (S : Subgroup G) ≃* DihedralGroup (2 ^ k) :=
    (MulEquiv.subgroupCongr (hCS₀.symm.trans hmap.symm)).trans
      ((((Subgroup.centralizer ({z} : Set G)).equivMapOfInjective (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective)).symm.trans e₀)
  have hG : ∀ M : Subgroup G, M.index ≠ 2 := index_ne_two_of_isConj hinv S hn eS
  obtain ⟨K, hK1, hK2, hodd, hq, he⟩ := dihedral_core G hG S hn ⟨eS⟩ hz₀ hSz₀ hCp₀
  refine ⟨K, hK1, hK2, hodd, ?_, he⟩
  rwa [pow_succ, mul_comm]

theorem lemma_I_4_1_two
    (G : Type) [Group G] [Finite G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {z : G} (hz : orderOf z = 2)
    (hC : Nonempty (Subgroup.centralizer ({z} : Set G) ≃* DihedralGroup 4)) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨K, _, _, -, hq, ⟨e⟩⟩ :=
    psl2_of_isConj G hinv hz (k := 2) (by norm_num) (by simpa using hC)
  norm_num at hq
  rcases hq with h7 | h9
  · obtain ⟨e7⟩ := nonempty_psl2_equiv_zmod (by norm_num : Nat.Prime 7) (by omega)
    obtain ⟨e32⟩ := nonempty_psl3_two_equiv_psl2_seven
    exact Or.inl ⟨(e.trans e7).trans e32.symm⟩
  · obtain ⟨e6⟩ := nonempty_psl2_equiv_alternating_six h9
    exact Or.inr ⟨e.trans e6⟩

end CFSG.Quasithin.I4
