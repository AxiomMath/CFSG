module

public import CFSG.Quasithin.Background.ONanE68Lin3Conc
public import CFSG.Quasithin.Background.ONanE68Lin3Equiv
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.E6.E68Proof

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lin3

theorem exists_mulEquiv_map_eq_projUnitriangular {G : Type} [Group G] {K : Type} [Field K]
    [Finite K] [CharP K 2] (e₁ : G ≃* projectiveSL 3 K) {UL : Subgroup G} (hUL : IsPGroup 2 UL)
    (hULi : ¬ 2 ∣ UL.index) :
    ∃ e : G ≃* projectiveSL 3 K, UL.map e.toMonoidHom = projUnitriangular 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU1 : IsPGroup 2 (UL.map e₁.toMonoidHom) := hUL.map _
  have hU1i : ¬ 2 ∣ (UL.map e₁.toMonoidHom).index := by
    rw [show UL.map e₁.toMonoidHom = UL.map (e₁ : G →* projectiveSL 3 K) from rfl,
      Subgroup.index_map_equiv]
    exact hULi
  obtain ⟨S₀, hS₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) S₀ (hU1.toSylow hU1i)
  have hmem : ∀ z, z ∈ UL.map e₁.toMonoidHom ↔ g⁻¹ * z * g ∈ projUnitriangular 3 K := by
    intro z
    have h1 : UL.map e₁.toMonoidHom = ((g • S₀ : Sylow 2 (projectiveSL 3 K)) :
        Subgroup (projectiveSL 3 K)) := by
      rw [hg]
      rfl
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, hS₀]
  refine ⟨e₁.trans (MulAut.conj g⁻¹), ?_⟩
  have he : ∀ y : G, (e₁.trans (MulAut.conj g⁻¹)) y = g⁻¹ * e₁ y * g := fun y => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (e₁.trans (MulAut.conj g⁻¹)) y ∈ _
    rw [he]
    exact (hmem _).mp ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, hye⟩ := (hmem (g * x * g⁻¹)).mpr (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x
      by group])
    refine ⟨y, hy, ?_⟩
    change (e₁.trans (MulAut.conj g⁻¹)) y = x
    rw [he]
    change e₁ y = g * x * g⁻¹ at hye
    rw [hye]
    group

end Lin3

theorem e68Lin3Data_holds : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 2 ≤ n →
    StatedClassicalModel S .PSL 3 2 n → ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
      E68Lin3Data P n := by
  intro S _ _ n hn hS P hP
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  let e₁ : S ≃* projectiveSL 3 K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have hidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  obtain ⟨φ, hφ⟩ := Lin3.exists_mulEquiv_map_eq_projUnitriangular e₁ hP.2.1 hidx
  exact Lin3.e68Lin3Data_of_mulEquiv hφ (Lin3.e68Lin3Data_projectiveSL hn hK)

theorem e68PSL25_holds :
    ∀ (S : Type) [Group S], StatedClassicalModel S .PSL 2 5 1 →
      StatedClassicalModel S .PSL 2 2 2 := by
  intro S _ h
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have e' : S ≃* StatedProj (StatedSL 2 F) := e
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inr (by rw [hF]; norm_num))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hcard]; norm_num))
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hcard, ⟨(e'.trans e5).trans e4.symm⟩⟩

end CFSG.Quasithin.E6.E68Proof
