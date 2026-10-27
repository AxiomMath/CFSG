module

public import CFSG.Quasithin.EmptyFaithful.SBc17FixG1
public import CFSG.Quasithin.EmptyFaithful.SBc17FixRep
public import CFSG.Quasithin.EmptyFaithful.SBc16Theta
public import CFSG.Quasithin.EmptyFaithful.SBc14Top

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc17

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem lines_data (hdec : IsDecP T M H p H₀ H₁ H₂ t) :
    (oTwoUpper H₁ ≤ oTwoUpper H ∧ pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (oTwoUpper H₁ : Set G) ∧
      oTwoUpper (oTwoUpper H₁) = oTwoUpper H₁) ∧
    (oTwoUpper H₂ ≤ oTwoUpper H ∧ pCoreOf 2 (oTwoUpper H) ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) ∧
      oTwoUpper (oTwoUpper H₂) = oTwoUpper H₂) :=
  ⟨⟨oTwoUpper_mono (hdec.le₁.trans hdec.le), fun _ hx =>
      le_normalizer_oTwoUpper H₁ (hdec.Q₁ ((SBc16.mem_pCoreOf_oTwoUpper_iff H).mp hx).2),
      oTwoUpper_idem_P H₁⟩,
    ⟨oTwoUpper_mono (hdec.le₂.trans hdec.le), fun _ hx =>
      le_normalizer_oTwoUpper H₂ (hdec.Q₂ ((SBc16.mem_pCoreOf_oTwoUpper_iff H).mp hx).2),
      oTwoUpper_idem_P H₂⟩⟩

theorem gap3Fix_of_noFive (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hno : ∀ α ∈ (psiHom hKG).range, orderOf α ≠ 5) :
    Gap3Fix T (oTwoUpper H₁) (oTwoUpper H₂) := by
  obtain ⟨σ, τ, hσA, hτA, hσ₂, hσ₁, hτ₁, hτ₂⟩ := exists_sigma_tau S hp5 hred hdec hKG
  obtain ⟨⟨hX₁, hO₁, hP₁⟩, ⟨hX₂, hO₂, hP₂⟩⟩ := lines_data hdec
  subst hp5
  intro x hx hxN
  have hmap₂ : (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)).map
      (psiHom hKG ⟨x, hx⟩).toMonoidHom = imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂) :=
    (map_actHom_eq_iff hX₂ hO₂ hP₂ (hKG hx)).mpr hxN
  have hmap₁ := fix_of_noFive_apply (SBc16.mul_comm_OTwoQuot_K S rfl hred hdec)
    (SBc16.card_OTwoQuot_K S rfl hred hdec) (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁))
    (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)) (SBc16.card_imageOTwoQuot_K hred hdec)
    (SBc16.card_imageOTwoQuot_K hred hdec.swap)
    (disjoint_iff.mp (SBc16.disjoint_imageOTwoQuot_K hdec)) (SBc16.imageOTwoQuot_sup_eq_top S hred hdec)
    (psiHom hKG).range σ hσA hσ₂ hσ₁ hno (psiHom hKG ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ hmap₂
  exact (map_actHom_eq_iff hX₁ hO₁ hP₁ (hKG hx)).mp hmap₁

theorem noFive_of_gap3Fix (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hfix : Gap3Fix T (oTwoUpper H₁) (oTwoUpper H₂)) :
    ∀ α ∈ (psiHom hKG).range, orderOf α ≠ 5 := by
  obtain ⟨σ, τ, hσA, hτA, hσ₂, hσ₁, hτ₁, hτ₂⟩ := exists_sigma_tau S hp5 hred hdec hKG
  obtain ⟨⟨hX₁, hO₁, hP₁⟩, ⟨hX₂, hO₂, hP₂⟩⟩ := lines_data hdec
  subst hp5
  intro α hαA hα5
  obtain ⟨β, hβA, hβ₂, hβ₁⟩ := exists_moves_of_five_apply (SBc16.mul_comm_OTwoQuot_K S rfl hred hdec)
    (SBc16.card_OTwoQuot_K S rfl hred hdec) (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁))
    (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)) (SBc16.card_imageOTwoQuot_K hred hdec)
    (SBc16.card_imageOTwoQuot_K hred hdec.swap)
    (disjoint_iff.mp (SBc16.disjoint_imageOTwoQuot_K hdec)) (SBc16.imageOTwoQuot_sup_eq_top S hred hdec)
    (psiHom hKG).range σ hσA hσ₂ hσ₁ τ hτA hτ₁ hτ₂ α hαA hα5
  obtain ⟨⟨y, hy⟩, rfl⟩ := hβA
  have hyN₂ : y ∈ Subgroup.normalizer (oTwoUpper H₂ : Set G) :=
    (map_actHom_eq_iff hX₂ hO₂ hP₂ (hKG hy)).mp hβ₂
  exact hβ₁ ((map_actHom_eq_iff hX₁ hO₁ hP₁ (hKG hy)).mpr (hfix y hy hyN₂))

omit [Finite G] in
theorem five_mem_kerAct_of_noFive (hKG : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hno : ∀ α ∈ (psiHom hKG).range, orderOf α ≠ 5) :
    ∀ x ∈ mcOf T, orderOf x = 5 →
      x ∈ SBc14.kerAct (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) := by
  intro x hx hx5
  have hKO : x ∈ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H) (hKG hx)
  refine SBc14.mem_kerAct.mpr ⟨hKO, ?_⟩
  have hα : orderOf (psiHom hKG ⟨x, hx⟩) = 1 := by
    have hdvd : orderOf (psiHom hKG ⟨x, hx⟩) ∣ 5 := by
      have := orderOf_map_dvd (psiHom hKG) ⟨x, hx⟩
      rwa [Subgroup.orderOf_mk, hx5] at this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact h1
    · exact absurd h5 (hno _ ⟨⟨x, hx⟩, rfl⟩)
  have h1 : SBc16.actHom (oTwoUpper H) ⟨x, hKG hx⟩ = 1 := by
    rw [← psiHom_apply hKG x hx]
    exact orderOf_eq_one_iff.mp hα
  exact (SBc16.actHom_eq_one_iff _ (hKG hx)).mp h1

theorem gap3Fix_of_relIndex_two (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) (hidx : H₀.relIndex H = 2) :
    Gap3Fix T (oTwoUpper H₁) (oTwoUpper H₂) :=
  gap3Fix_of_noFive S hp5 hred hdec (mcOf_le_normalizer_oTwoUpper hCz)
    (noFive_range_of_relIndex_two S hp5 hred hdec (mcOf_le_normalizer_oTwoUpper hCz) hidx)

theorem gap3Theta_of_gap3Fix (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H)
    (hfix : Gap3Fix T (oTwoUpper H₁) (oTwoUpper H₂)) :
    Gap3Theta T (oTwoUpper H₁) (oTwoUpper H₂) :=
  SBc16.gap3Theta_of_kerAct S hp5 hred hdec rfl rfl (hdec.setup14615_of_C1 S hred hCz)
    (five_mem_kerAct_of_noFive (mcOf_le_normalizer_oTwoUpper hCz)
      (noFive_of_gap3Fix S hp5 hred hdec (mcOf_le_normalizer_oTwoUpper hCz) hfix))

@[expose] def Input14615FixR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H → ¬ H₀.relIndex H = 2 →
          Gap3Fix T (oTwoUpper H₁) (oTwoUpper H₂)

theorem gap3Fix_of_FixR (h : Input14615FixR) (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hctx : Ctx15 T M H p H₁)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) :
    Gap3Fix T (oTwoUpper H₁) (oTwoUpper H₂) := by
  by_cases hidx : H₀.relIndex H = 2
  · exact gap3Fix_of_relIndex_two S hctx.1 hred hdec hCz hidx
  · exact h G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx hCz hidx

theorem input14615Theta_of_FixR (h : Input14615FixR) : SBc14.Input14615Theta := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx hCz
  exact gap3Theta_of_gap3Fix S hctx.1 hred hdec hCz (gap3Fix_of_FixR h S hred hmax hdec hctx hCz)

theorem gap3Fix_of_ctx {K₁ K₂ : Subgroup G} {s : G} (h : Input14615FixR) (S : Setting146 G T M)
    {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hctx : Ctx15 T M H p H₁)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : Gap3Fix T K₁ K₂ := by
  rcases hset.shape with ⟨hc₁, hc₂, -, -⟩ | ⟨hK₁, hK₂⟩
  · exact gap3Fix_of_gap3Pair S hset (SBc13.gap3Pair_of_shapeOne hset hc₁ hc₂)
  · have hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H := by
      rw [hset.kz, hK₁, hK₂]
      exact (hdec.oTwoUpper_eq S hred).symm
    rw [hK₁, hK₂]
    exact gap3Fix_of_FixR h S hred hmax hdec hctx hCz

end SBc17

end CFSG.Quasithin
