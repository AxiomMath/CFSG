module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Timmesfeld.Transvection.ModelSUQuotient
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank

theorem rootS1Model_su_of_involutive {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {m : ℕ} (hP : SUPerpStmt σ m) {K : Type} [Group K]
    {Φ : SU σ m →* K} (hΦ : Function.Surjective Φ) (hker : Φ.ker ≤ Subgroup.center (SU σ m))
    {a : Fin m → F} (ha : a ≠ 0) (haa : uForm σ a a = 0) {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ a T)
    (hS : ∀ {g : SU σ m}, ¬ Commuting T (conjSub T g) → ∀ {x : SU σ m}, x ∈ conjSub T g →
      x ≠ 1 → uRad σ a ⊔ Subgroup.zpowers x = ⊤) :
    RootS1Model K (T.map Φ) := by
  intro g' hg' x' hx' hx'1
  obtain ⟨g, rfl⟩ := hΦ g'
  rw [conjSub_map] at hx'
  obtain ⟨x, hx, rfl⟩ := hx'
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx'1 (map_one Φ)
  have hnc : ¬ Commuting T (conjSub T g) := by
    intro h
    apply hg'
    have h' := commuting_map Φ h
    rw [← conjSub_map] at h'
    exact fun y hy z hz => (h' y hy z hz).eq
  have htop : (uRad σ a).map Φ ⊔ Subgroup.zpowers (Φ x) = ⊤ := by
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup, hS hnc hx hx1,
      Subgroup.map_top_of_surjective Φ hΦ]
  have hle : (uRad σ a).map Φ ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ ((isPGroup_uRad (σ := σ) a).map Φ)
    · refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map Φ)
      rw [normalizer_eq_uLine hσ ha hT]
      exact uRad_le_uLine a
    · intro k hk
      obtain ⟨g₁, hg₁, rfl⟩ :=
        exists_mem_uLine_of_mem_normalizer_map_of_involutive hσ hP hΦ hker ha haa hT hk
      exact Subgroup.le_normalizer_map Φ
        (Subgroup.mem_map_of_mem Φ (uLine_le_normalizer_uRad a hg₁))
  rw [eq_top_iff, ← htop]
  exact sup_le_sup_right hle _

theorem rootS1Model_su {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hP : SUPerpStmt (unitaryInvolution F 2 f) m)
    {K : Type} [Group K] {Φ : SU (unitaryInvolution F 2 f) m →* K}
    (hΦ : Function.Surjective Φ)
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m)) {a : Fin m → F}
    (ha : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    {T : Subgroup (SU (unitaryInvolution F 2 f) m)}
    (hT : IsUTransGroup (unitaryInvolution F 2 f) a T)
    (hS : ∀ {g : SU (unitaryInvolution F 2 f) m}, ¬ Commuting T (conjSub T g) →
      ∀ {x : SU (unitaryInvolution F 2 f) m}, x ∈ conjSub T g → x ≠ 1 →
        uRad (unitaryInvolution F 2 f) a ⊔ Subgroup.zpowers x = ⊤) :
    RootS1Model K (T.map Φ) :=
  rootS1Model_su_of_involutive (unitaryInvolution_involutive hF) hP hΦ hker ha haa hT hS

end CFSG.RankThree.GF2n.Tim79a
