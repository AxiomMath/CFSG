module

public import CFSG.Quasithin.Vol2.E2SevenKG7Member
public import CFSG.Quasithin.Vol2.Ch3E213MP6D1
public import CFSG.Quasithin.Vol2.Ch3E213MP6BH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiUnipotent
  antiUnipotentCenter antiUnipotentCenter_comm)
open CFSG.GorensteinWalter (sl2UpperUnipotent sl2UpperUnipotentSubgroup
  mem_sl2UpperUnipotentSubgroup_iff)
open scoped MatrixGroups

namespace E2

open Ch3E213M

variable {G : Type} [Group G] [Finite G]

theorem exists_isInIHTVC_of_embed (hKG2L2 : KGBenderSubL2) (hKG2Sz : KGBenderSubSz)
    {X T M V : Subgroup G} {B : Type} [Group B] [Finite B] {ψ : B →* G}
    (hψ : Function.Injective ψ) (hψX : ψ.range ≤ X) {U₀ : Subgroup B} (hU₀ : IsPGroup 2 U₀)
    (hU₀i : ¬ 2 ∣ U₀.index) {m : ℕ} (hm2 : 2 ≤ m) (hB : IsPSL 2 2 m B ∨ IsSz m B)
    (hT : T.comap ψ = U₀) (hM : M.comap ψ = Subgroup.normalizer (U₀ : Set B))
    (hVU : V ≤ U₀.map ψ) (hVc : ∀ v ∈ V, ∀ u ∈ U₀, ψ u * v = v * ψ u)
    (hV : IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hmn : ∃ d : ℕ, E1.nParam X = ((m * d : ℕ) : ℕ∞)) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e : B ≃* ↥ψ.range := MonoidHom.ofInjective hψ
  have hL : IsPSL 2 2 m ↥ψ.range ∨ IsSz m ↥ψ.range := by
    rcases hB with ⟨hadm, K, hK, hKf, hcard, ⟨f⟩⟩ | ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨f⟩⟩
    · exact Or.inl ⟨hadm, K, hK, hKf, hcard, ⟨e.symm.trans f⟩⟩
    · exact Or.inr ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.symm.trans f⟩⟩
  have hTL : T ⊓ ψ.range = U₀.map ψ := by
    rw [inf_comm, ← Subgroup.map_comap_eq, hT]
  have hSL : IsSylowTwoOf (T ⊓ ψ.range) ψ.range := by
    rw [hTL, CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf, MonoidHom.range_eq_map]
    refine CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective ψ hψ ?_
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, hU₀, hU₀i⟩
  refine exists_isInIHTVC_of_bender_le hKG2L2 hKG2Sz hψX hm2 hL hSL (hTL ▸ hVU) ?_ ?_ hV hV4
    hmn
  · intro v hv
    rw [Subgroup.mem_centralizer_iff, hTL]
    rintro _ ⟨u, hu, rfl⟩
    exact hVc v hv u hu
  · rw [inf_comm M, ← Subgroup.map_comap_eq, hM, hTL, MonoidHom.range_eq_map,
      map_inf_normalizer_map hψ, top_inf_eq]

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem isPSL_sl2 {n : ℕ} (hk : Nat.card k = 2 ^ n) (hn : 2 ≤ n) : IsPSL 2 2 n SL(2, k) := by
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, k, inferInstance,
    inferInstance, hk, ⟨CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.sl2EquivPSL2.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k)⟩⟩
  · simp only [Prod.mk.injEq, true_and] at h
    omega
  · simp only [Prod.mk.injEq, true_and] at h
    omega

theorem exists_card_subfield {n : ℕ} (hk : Nat.card k = 2 ^ n)
    (F₀ : Subfield k) : ∃ m d : ℕ, 1 ≤ m ∧ Nat.card F₀ = 2 ^ m ∧ n = m * d := by
  have : CharP ↥F₀ 2 := (F₀.subtype : ↥F₀ →+* k).charP Subtype.val_injective 2
  have := Fintype.ofFinite ↥F₀
  have := Fintype.ofFinite k
  obtain ⟨m, -, hm⟩ := FiniteField.card ↥F₀ 2
  obtain ⟨d, hd⟩ := VectorSpace.card_fintype ↥F₀ k
  refine ⟨m, d, m.pos, by rw [Nat.card_eq_fintype_card, hm], ?_⟩
  rw [Nat.card_eq_fintype_card, hd, hm, ← pow_mul] at hk
  exact (Nat.pow_right_injective le_rfl hk).symm

theorem exists_isInIHTVC_of_diag (hKG2L2 : KGBenderSubL2) (hKG2Sz : KGBenderSubSz)
    {X T M V : Subgroup G} {φ : antiSp k →* G} (hφ : Function.Injective φ)
    (hφX : φ.range ≤ X) (hT : T.comap φ = antiUnipotent k)
    (hM : M.comap φ = Subgroup.normalizer (antiUnipotent k : Set (antiSp k)))
    (hVr : V ≤ φ.range) (hWZ : V.comap φ ≤ antiUnipotentCenter k) {n : ℕ}
    (hk : Nat.card k = 2 ^ n) (hn : 2 ≤ n) {μ : k} (hμ : μ ≠ 0)
    (hVμ : V.comap φ ≤ zLine 1 μ) (hV : IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hnX : E1.nParam X = n) : ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I := by
  set μ' : kˣ := Units.mk0 μ hμ
  have hδU : ∀ g, P6D.diagSLμ μ' g ∈ antiUnipotent k ↔ g ∈ sl2UpperUnipotentSubgroup k :=
    P6D.diagSLμ_mem_antiUnipotent_iff μ'
  have hD := H13.QRC.benderData_sl2 hk
  refine exists_isInIHTVC_of_embed hKG2L2 hKG2Sz (ψ := φ.comp (P6D.diagSLμ μ'))
    (hφ.comp (P6D.diagSLμ_injective μ')) (((MonoidHom.range_comp _ _).trans_le
      (Subgroup.map_le_range _ _)).trans hφX)
    hD.isPGroup hD.not_dvd_index hn (Or.inl (isPSL_sl2 hk hn)) ?_ ?_ ?_ ?_ hV hV4
    ⟨1, by rw [hnX, mul_one]⟩
  ·
    ext g
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, ← Subgroup.mem_comap, hT, hδU]
  ·
    ext g
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, ← Subgroup.mem_comap, hM]
    constructor
    · intro hg
      rw [Subgroup.mem_normalizer_iff]
      intro u
      rw [← hδU, ← hδU, map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp hg (P6D.diagSLμ μ' u)
    · intro hg
      rw [H13.QRC.sl2_normalizer_upperUnipotent] at hg
      exact P6D.diagSLμ_mem_normalizer μ' hg
  ·
    intro v hv
    obtain ⟨w, rfl⟩ := hVr hv
    obtain ⟨t, ht⟩ := hVμ (show w ∈ V.comap φ from hv)
    refine ⟨sl2UpperUnipotent t, (mem_sl2UpperUnipotentSubgroup_iff _).2 ⟨t, rfl⟩, ?_⟩
    change φ (P6D.diagSLμ μ' (sl2UpperUnipotent t)) = φ w
    rw [P6D.diagSLμ_upperUnipotent, ht]
    rfl
  ·
    intro v hv u hu
    obtain ⟨w, rfl⟩ := hVr hv
    change φ (P6D.diagSLμ μ' u) * φ w = φ w * φ (P6D.diagSLμ μ' u)
    rw [← map_mul, ← map_mul, antiUnipotentCenter_comm (hWZ hv) ((hδU u).mpr hu)]

theorem exists_isInIHTVC_of_sz (hKG2L2 : KGBenderSubL2)
    (hKG2Sz : KGBenderSubSz) {X T M V : Subgroup G} {φ : antiSp k →* G}
    (hφ : Function.Injective φ) (hφX : φ.range ≤ X) (hT : T.comap φ = antiUnipotent k)
    (hM : M.comap φ = Subgroup.normalizer (antiUnipotent k : Set (antiSp k)))
    (hVr : V ≤ φ.range) (hWZ : V.comap φ ≤ antiUnipotentCenter k) {F₀ : Subfield k} {a : ℕ}
    (ha : 1 ≤ a) (hcard : Nat.card F₀ = 2 ^ (2 * a + 1)) {d : antiSp k} (hd : IsUpper d)
    (hW : V.comap φ ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom)
    (hV : IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hmn : ∃ e : ℕ, E1.nParam X = (((2 * a + 1) * e : ℕ) : ℕ∞)) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC X T M V I := by
  have hD := H13.QRC.benderData_suzuki ha hcard
  refine exists_isInIHTVC_of_embed hKG2L2 hKG2Sz (ψ := φ.comp (P6B.szEmb F₀ a hcard d))
    (hφ.comp (P6B.szEmb_injective hcard)) (((MonoidHom.range_comp _ _).trans_le
      (Subgroup.map_le_range _ _)).trans hφX)
    hD.isPGroup hD.not_dvd_index (by omega)
    (Or.inr ⟨rfl, a, ha, ↥F₀, inferInstance, inferInstance, rfl, hcard, ⟨MulEquiv.refl _⟩⟩)
    ?_ ?_ ?_ ?_ hV hV4 hmn
  · rw [← Subgroup.comap_comap, hT, P6B.comap_szEmb_antiUnipotent hcard ha hd]
  · rw [← Subgroup.comap_comap, hM, P6B.comap_szEmb_normalizer hcard ha hd]
  · intro v hv
    obtain ⟨w, rfl⟩ := hVr hv
    obtain ⟨s, hs, hse⟩ := P6B.exists_szEmb_eq_of_mem hcard (hW hv)
    refine ⟨s, hs, ?_⟩
    change φ (P6B.szEmb F₀ a hcard d s) = φ w
    rw [hse]
  · intro v hv u hu
    obtain ⟨w, rfl⟩ := hVr hv
    have hιu : P6B.szEmb F₀ a hcard d u ∈ antiUnipotent k :=
      P6B.map_szEmb_suzukiU_le hcard hd ⟨u, hu, rfl⟩
    change φ (P6B.szEmb F₀ a hcard d u) * φ w = φ w * φ (P6B.szEmb F₀ a hcard d u)
    rw [← map_mul, ← map_mul, antiUnipotentCenter_comm (hWZ hv) hιu]

end E2

end CFSG.Quasithin
