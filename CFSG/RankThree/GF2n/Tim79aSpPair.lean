module

public import CFSG.RankThree.GF2n.Tim79aClassicalSp
public import CFSG.RankThree.GF2n.Tim79aSec33Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_isTransGroup_of_transvConclusionSp_two {K : Type} [Group K] {Δ : Set (Subgroup K)}
    {f : ℕ} (hf : 1 ≤ f) (h : TransvConclusionSp K Δ f) {A : Subgroup K} (hA : A ∈ Δ) :
    ∃ (n : ℕ) (Φ : StatedSp n (GaloisField 2 f) →* K) (a : Fin n ⊕ Fin n → GaloisField 2 f)
      (T : Subgroup (StatedSp n (GaloisField 2 f))),
      2 ≤ n ∧ Function.Bijective Φ ∧ a ≠ 0 ∧ CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T ∧
        A = T.map Φ := by
  obtain ⟨n, hn, Φ, hΦ, hΔ⟩ := h
  obtain ⟨g, rfl⟩ := (hΔ A).1 hA
  have hv : (Pi.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) 1 :
      Fin n ⊕ Fin n → GaloisField 2 f) ≠ 0 :=
    Pi.single_ne_zero_iff.2 one_ne_zero
  exact ⟨n, Φ, _, _, hn, hΦ, ModelRank.mat_mulVec_ne_zero' g hv,
    (ModelRank.isTransGroup_rootGroup_last (by omega)).conjSub g, rfl⟩

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic

variable {n : ℕ} {F : Type} [Field F]

theorem sp_conjSub_vec_not_smul {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) {g : StatedSp n F}
    (hg : conjSub T g ≠ T) : ∀ c : F, SpExtras.mat n F g *ᵥ a ≠ c • a := by
  intro c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact mat_mulVec_ne_zero' g ha (by rw [hc, zero_smul])
  have h1 := hT.conjSub g
  rw [hc] at h1
  exact hg ((h1.of_smul hc0).eq hT)

theorem spTransGroup_inf_spRad_eq_bot {a x : Fin n ⊕ Fin n → F} (hxa : ∀ c : F, x ≠ c • a)
    {X : Subgroup (StatedSp n F)} (hX : IsTransGroup x X) : X ⊓ spRad a = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨htX, -, htu⟩
  obtain ⟨c, hc⟩ := (hX.1 t).1 htX
  obtain ⟨u, hau, hxu⟩ := exists_perp_spForm_ne_zero hxa
  obtain ⟨d, hd⟩ := htu u hau
  rw [hc, spTrans_mulVec] at hd
  have h1 : (c * spForm x u) • x = d • a := add_left_cancel hd
  have hc0 : c = 0 := by
    by_contra hc0
    have hcx : c * spForm x u ≠ 0 := mul_ne_zero hc0 hxu
    apply hxa ((c * spForm x u)⁻¹ * d)
    rw [← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ hcx, one_smul]
  rw [Subgroup.mem_bot]
  apply SpExtras.mat_injective
  rw [hc, hc0, spTrans_zero, map_one]

theorem spModel_disjoint :
    ∀ (n : ℕ), 2 ≤ n → ∀ (F : Type) [Field F] [CharP F 2] [Finite F] (a : Fin n ⊕ Fin n → F)
      (T : Subgroup (StatedSp n F)), a ≠ 0 → IsTransGroup a T →
      ∀ g : StatedSp n F, conjSub T g ≤ Subgroup.centralizer (T : Set (StatedSp n F)) →
        conjSub T g ≠ T →
        conjSub T g ⊓ pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n F))) = ⊥ := by
  intro n _ F _ _ _ a T ha hT g _ hne
  rw [spCoreStmt_holds n F ha hT]
  exact spTransGroup_inf_spRad_eq_bot (sp_conjSub_vec_not_smul ha hT hne) (hT.conjSub g)

theorem exists_mem_spRad_of_perp [CharP F 2] {a w : Fin n ⊕ Fin n → F}
    (haw : spForm a w = 0) :
    ∃ z ∈ spRad a, ∀ v, SpExtras.mat n F z *ᵥ v = v + spForm a v • w + spForm w v • a := by
  have hwa : spForm w a = 0 := spForm_eq_zero_comm haw
  obtain ⟨t1, ht1⟩ := exists_mat_eq_spTrans (a + w) (1 : F)
  obtain ⟨t2, ht2⟩ := exists_mat_eq_spTrans w (1 : F)
  obtain ⟨t3, ht3⟩ := exists_mat_eq_spTrans a ((0 : F) + 1)
  have hact : ∀ v, SpExtras.mat n F (t1 * t2 * t3) *ᵥ v =
      v + spForm a v • w + spForm w v • a := by
    intro v
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ht1, ht2, ht3,
      mulVec_spTrans_prod haw 0 v, zero_mul, zero_smul, add_zero]
  refine ⟨t1 * t2 * t3, ⟨?_, fun u hu => ⟨spForm w u, ?_⟩⟩, hact⟩
  · rw [hact, spForm_self, hwa, zero_smul, zero_smul, add_zero, add_zero]
  · rw [hact, hu, zero_smul, add_zero]

theorem exists_perp_vec_not_smul (hn : 2 ≤ n) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) :
    ∃ x : Fin n ⊕ Fin n → F, x ≠ 0 ∧ spForm a x = 0 ∧ ∀ c : F, x ≠ c • a := by
  obtain ⟨v₀, hv₀⟩ := exists_spForm_eq_one ha
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, v₀]
    (by rw [Fintype.card_fin]; omega)
  have hax : spForm a x = 0 := hx 0
  have hv₀x : spForm v₀ x = 0 := hx 1
  refine ⟨x, hx0, hax, fun c hc => ?_⟩
  rw [hc, spForm_smul_right', spForm_comm a v₀, hv₀, mul_neg, mul_one, neg_eq_zero] at hv₀x
  exact hx0 (by rw [hc, hv₀x, zero_smul])

theorem exists_mat_mulVec_eq_of_ne_zero {a x : Fin n ⊕ Fin n → F} (ha : a ≠ 0) (hx : x ≠ 0) :
    ∃ g : StatedSp n F, SpExtras.mat n F g *ᵥ a = x := by
  obtain ⟨y, hay, hxy⟩ := exists_spForm_ne_zero_both ha hx
  obtain ⟨g₁, hg₁⟩ := exists_mat_mulVec_eq hay
  obtain ⟨g₂, hg₂⟩ := exists_mat_mulVec_eq (x := y) (y := x)
    (by rw [spForm_comm]; exact neg_ne_zero.2 hxy)
  exact ⟨g₂ * g₁, by rw [map_mul, ← mulVec_mulVec, hg₁, hg₂]⟩

theorem spModel_moves :
    ∀ (n : ℕ), 2 ≤ n → ∀ (F : Type) [Field F] [CharP F 2] [Finite F] (a : Fin n ⊕ Fin n → F)
      (T : Subgroup (StatedSp n F)), a ≠ 0 → IsTransGroup a T →
      ∃ g : StatedSp n F, conjSub T g ≤ Subgroup.centralizer (T : Set (StatedSp n F)) ∧
        conjSub T g ≠ T ∧
        ∃ x ∈ pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n F))),
          ∃ t ∈ conjSub T g, x * t ≠ t * x := by
  intro n hn F _ _ _ a T ha hT
  obtain ⟨x, hx0, hax, hxa⟩ := exists_perp_vec_not_smul hn ha
  obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero ha hx0
  have hTx : IsTransGroup x (conjSub T g) := hg ▸ hT.conjSub g
  obtain ⟨w, haw, hxw⟩ := exists_perp_spForm_ne_zero hxa
  obtain ⟨z, hz, hzv⟩ := exists_mem_spRad_of_perp haw
  obtain ⟨t, ht⟩ := hTx.2 1
  refine ⟨g, fun y hy => Subgroup.mem_centralizer_iff.2 fun s hs =>
      (hT.commuting hTx hax s hs y hy).eq, fun he => ?_, z, spRad_le_pCoreOf ha hT hz, t,
    (hTx.1 t).2 ⟨1, ht⟩, fun hzt => ?_⟩
  · rw [he] at hTx
    obtain ⟨μ, -, hμ⟩ := IsTransGroup.exists_eq_smul hTx hT hx0
    exact hxa μ hμ
  · have h1 : SpExtras.mat n F (z * t) *ᵥ w =
        w + spForm x w • x + (spForm x w * spForm w x) • a := by
      rw [map_mul, ← mulVec_mulVec, ht, spTrans_mulVec, one_mul, mulVec_add, mulVec_smul, hzv,
        hzv, haw, hax, spForm_self]
      module
    have h2 : SpExtras.mat n F (t * z) *ᵥ w = w + spForm x w • x := by
      rw [map_mul, ← mulVec_mulVec, hzv, haw, spForm_self, zero_smul, zero_smul, add_zero,
        add_zero, ht, spTrans_mulVec, one_mul]
    rw [hzt, h2] at h1
    have h3 : (spForm x w * spForm w x) • a = 0 := add_eq_left.1 h1.symm
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact mul_ne_zero hxw (by rw [spForm_comm]; exact neg_ne_zero.2 hxw) h4
    · exact ha h4

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection

variable {S K : Type} [Group S] [Group K]

theorem pCoreOf_normalizer_map_of_bijective_pair (Φ : S →* K) (hΦ : Function.Bijective Φ)
    (T : Subgroup S) :
    pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      (pCoreOf 2 (Subgroup.normalizer (T : Set S))).map Φ := by
  have h := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulEquiv.ofBijective Φ hΦ)
    (Subgroup.normalizer (T : Set S))
  have he : (MulEquiv.ofBijective Φ hΦ).toMonoidHom = Φ := MonoidHom.ext fun _ => rfl
  rw [he] at h
  rw [← Subgroup.map_normalizer_eq_of_bijective T hΦ, h]

theorem map_le_centralizer_map_iff_of_injective (Φ : S →* K) (hΦ : Function.Injective Φ)
    (A T : Subgroup S) :
    A.map Φ ≤ Subgroup.centralizer ((T.map Φ : Subgroup K) : Set K) ↔
      A ≤ Subgroup.centralizer (T : Set S) := by
  constructor
  · intro h y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply hΦ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_map_of_mem Φ hy)) (Φ s)
      (Subgroup.mem_map_of_mem Φ hs)
  · rintro h _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (h hy) s hs]

theorem pairFacts_map_of_bijective (Φ : S →* K) (hΦ : Function.Bijective Φ) (T : Subgroup S)
    (h : PairFacts S T) : PairFacts K (T.map Φ) := by
  refine ⟨rootIrrModel_map_of_bijective Φ hΦ h.irr, fun g hgc hgne => ?_, ?_⟩
  · obtain ⟨g', rfl⟩ := hΦ.2 g
    rw [ModelRank.conjSub_map] at hgc hgne ⊢
    rw [pCoreOf_normalizer_map_of_bijective_pair Φ hΦ, ← Subgroup.map_inf_eq _ _ Φ hΦ.1,
      h.disjoint g' ((map_le_centralizer_map_iff_of_injective Φ hΦ.1 _ T).1 hgc)
        (fun he => hgne (by rw [he])), Subgroup.map_bot]
  · obtain ⟨g, hgc, hgne, x, hx, t, ht, hxt⟩ := h.moves
    refine ⟨Φ g, ?_, ?_, Φ x, ?_, Φ t, ?_, ?_⟩
    · rw [ModelRank.conjSub_map]
      exact (map_le_centralizer_map_iff_of_injective Φ hΦ.1 _ T).2 hgc
    · rw [ModelRank.conjSub_map]
      exact fun he => hgne (Subgroup.map_injective hΦ.1 he)
    · rw [pCoreOf_normalizer_map_of_bijective_pair Φ hΦ]
      exact Subgroup.mem_map_of_mem Φ hx
    · rw [ModelRank.conjSub_map]
      exact Subgroup.mem_map_of_mem Φ ht
    · rw [← map_mul, ← map_mul]
      exact fun he => hxt (hΦ.1 he)

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

theorem spPairStatement_holds : ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRootSp K A → PairFacts K A := by
  rintro K _ _ A ⟨f, Δ, hf, hΔ, hA⟩
  obtain ⟨n, Φ, a, T, hn, hΦ, ha, hT, rfl⟩ :=
    exists_isTransGroup_of_transvConclusionSp_two hf hΔ hA
  exact pairFacts_map_of_bijective Φ hΦ T ⟨spModelIrr_holds n (GaloisField 2 f) a T ha hT,
    spModel_disjoint n hn _ a T ha hT, spModel_moves n hn _ a T ha hT⟩

end CFSG.RankThree.GF2n.Tim79a
