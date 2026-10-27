module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aTrivialKernel
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.SylowIndex
public import CFSG.LocalAnalysis.SectionRank.OddCover.CyclicSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial

theorem exists_cyclic_le_centralizer_of_card_eq_mul {G : Type*} [Group G] [Finite G] {ℓ : ℕ}
    (hℓ : ℓ.Prime) {Z : Subgroup G} [IsCyclic Z] {k : ℕ} (hG : Nat.card G = Nat.card Z * k)
    (hk : ¬ ℓ ∣ k) {D : Subgroup G} (hD : IsPGroup ℓ D) :
    ∃ C : Subgroup G, D ≤ C ∧ C ≤ centralizer (D : Set G) ∧ IsCyclic C ∧
      Nat.card C = Nat.card Z := by
  have hidx : ¬ ℓ ∣ Z.index := by
    have h1 := Subgroup.card_mul_index Z
    rw [hG] at h1
    rwa [Nat.eq_of_mul_eq_mul_left Nat.card_pos h1]
  obtain ⟨x, hx⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_conj_le_of_not_dvd_index hℓ Z
      hidx D hD
  set c : G ≃* G := MulAut.conj x⁻¹
  have hDC : D ≤ Z.map c.toMonoidHom := fun d hd =>
    ⟨x * d * x⁻¹, hx d hd, by simp [c, mul_assoc]⟩
  have hC : IsCyclic (Z.map c.toMonoidHom) :=
    isCyclic_of_surjective (c.toMonoidHom.subgroupMap Z) (MonoidHom.subgroupMap_surjective _ _)
  exact ⟨Z.map c.toMonoidHom, hDC, (le_centralizer _).trans (centralizer_le hDC), hC,
    card_map_of_injective c.injective⟩

private theorem not_three_dvd_cube_mul_cube_sub_one {q : ℕ} (hq : q % 3 = 2) :
    ¬ 3 ∣ q ^ 3 * (q ^ 3 - 1) := by
  have h : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hq]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h' | h' <;> omega

private theorem not_three_dvd_cube_mul_cube_add_one {q : ℕ} (hq : q % 3 = 1) :
    ¬ 3 ∣ q ^ 3 * (q ^ 3 + 1) := by
  have h : q ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hq]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h' | h' <;> omega

private theorem exists_isCyclic_statedSL_card {K : Type} [Field K] [Finite K] :
    ∃ Z : Subgroup (StatedSL 3 K), IsCyclic Z ∧ Nat.card Z = Nat.card K ^ 2 - 1 := by
  obtain ⟨Z, hZ, hcard⟩ := CFSG.SectionRank.OddCover.exists_isCyclic_card_GL K 2
  let ψ : GL (Fin 2) K →* StatedSL 3 K := Lemma41aL3.blk.codRestrict (StatedSL 3 K) fun A =>
    (linConj_mem_statedSL _).2 (Lemma41aL3.det_blk A)
  have hψ : Function.Injective ψ := fun A B hAB =>
    Lemma41aL3.blk_injective (congrArg Subtype.val hAB)
  exact ⟨Z.map ψ, isCyclic_of_surjective (ψ.subgroupMap Z) (ψ.subgroupMap_surjective Z),
    by rw [card_map_of_injective hψ, hcard]⟩

private theorem exists_isCyclic_statedSU_card {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ Z : Subgroup (StatedSU 3 (p ^ f) K), IsCyclic Z ∧ Nat.card Z = (p ^ f) ^ 2 - 1 := by
  set e := CFSG.LieType.Universal.Unitary.equivStatedSU hK 3
  set T := CFSG.LieType.Universal.Unitary.levelTorus
    (CFSG.LieType.BorelTits.unitaryInvolution K p f) (0 : Fin (3 / 2))
  have : IsCyclic T := CFSG.SectionRank.OddCover.isCyclic_levelTorus_three
  exact ⟨T.map e.toMonoidHom, isCyclic_of_surjective (e.toMonoidHom.subgroupMap T)
    (MonoidHom.subgroupMap_surjective _ _),
    by rw [card_map_of_injective e.injective, CFSG.LieType.Steinberg.card_levelTorus_three hK]⟩

private theorem exists_cyclic_le_centralizer_of_statedProj {S : Type} [Group S] [Finite S]
    {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} (e : S ≃* StatedProj H)
    (hρ : Function.Injective (statedProjMk H)) {Z : Subgroup H} (hZ : IsCyclic Z) {k : ℕ}
    (hH : Nat.card H = Nat.card Z * k) (hk : ¬ 3 ∣ k) {D : Subgroup S} (hD : Nat.card D = 3) :
    ∃ C : Subgroup S, C ≤ centralizer (D : Set S) ∧ IsCyclic C ∧ Nat.card C = Nat.card Z := by
  let E : H ≃* S :=
    (MulEquiv.ofBijective (statedProjMk H) ⟨hρ, statedProjMk_surjective H⟩).trans e.symm
  have hZ' : IsCyclic (Z.map E.toMonoidHom) :=
    isCyclic_of_surjective (E.toMonoidHom.subgroupMap Z) (MonoidHom.subgroupMap_surjective _ _)
  have hcard : Nat.card (Z.map E.toMonoidHom) = Nat.card Z := card_map_of_injective E.injective
  obtain ⟨C, -, hC, hCcyc, hCcard⟩ := exists_cyclic_le_centralizer_of_card_eq_mul Nat.prime_three
    (Z := Z.map E.toMonoidHom) (k := k) (by rw [hcard, ← hH, Nat.card_congr E.toEquiv]) hk
    (IsPGroup.of_card (p := 3) (n := 1) (by rw [hD, pow_one]))
  exact ⟨C, hC, hCcyc, hCcard.trans hcard⟩

theorem exists_cyclic_le_centralizer_of_card_three {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hS : (p ^ f % 3 = 2 ∧ LieModel S .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel S .PSU 3 p f))
    {D : Subgroup S} (hD : Nat.card D = 3) :
    ∃ C : Subgroup S, C ≤ centralizer (D : Set S) ∧ IsCyclic C ∧
      Nat.card C = (p ^ f) ^ 2 - 1 := by
  rcases hS with ⟨hq, hL⟩ | ⟨hq, hU⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel_of_ne_zero (by norm_num)
    obtain ⟨Z, hZ, hZcard⟩ := exists_isCyclic_statedSL_card (K := K)
    rw [hK] at hZcard
    have h3 : ¬ 3 ∣ Nat.card K - 1 := by
      rw [hK]
      omega
    have hH : Nat.card (StatedSL 3 K) = Nat.card Z * ((p ^ f) ^ 3 * ((p ^ f) ^ 3 - 1)) := by
      rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK, hZcard]
      ring
    obtain ⟨C, hC, hCcyc, hCcard⟩ := exists_cyclic_le_centralizer_of_statedProj e
      (Lemma41aL3.statedProjMk_injective_of_not_dvd h3) hZ hH
      (not_three_dvd_cube_mul_cube_sub_one hq) hD
    exact ⟨C, hC, hCcyc, hCcard.trans hZcard⟩
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hU.statedClassicalModel_of_ne_zero (by norm_num)
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := h.charP
    obtain ⟨Z, hZ, hZcard⟩ := exists_isCyclic_statedSU_card hK
    have h3 : ¬ 3 ∣ p ^ f + 1 := by omega
    have hH : Nat.card (StatedSU 3 (p ^ f) K) =
        Nat.card Z * ((p ^ f) ^ 3 * ((p ^ f) ^ 3 + 1)) := by
      rw [CFSG.SectionRank.OddCover.card_statedSU_three hK, hZcard]
      ring
    obtain ⟨C, hC, hCcyc, hCcard⟩ := exists_cyclic_le_centralizer_of_statedProj e
      (Lemma41aU3.statedProjMk_injective_of_not_dvd h h3) hZ hH
      (not_three_dvd_cube_mul_cube_add_one hq) hD
    exact ⟨C, hC, hCcyc, hCcard.trans hZcard⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
