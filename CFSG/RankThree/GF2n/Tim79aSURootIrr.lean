module

public import CFSG.Timmesfeld.Transvection.ModelSURadical
public import CFSG.RankThree.GF2n.Tim79aSec24CoreQuotient
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Timmesfeld.Transvection.ModelRankBasic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Centre

variable {F : Type} [Field F]

theorem center_le_uLine [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {m : ℕ}
    {a : Fin m → F} (ha : a ≠ 0) (haa : uForm σ a a = 0) {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ a T) : Subgroup.center (SU σ m) ≤ uLine σ a := by
  rw [← normalizer_eq_uLine hσ ha hT]
  exact Subgroup.center_le_normalizer _

end Centre

theorem pCoreOf_normalizer_map_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} {K : Type} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) m →* K} (hΦ : Function.Surjective Φ)
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m)) {a : Fin m → F}
    (ha : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    {T : Subgroup (SU (unitaryInvolution F 2 f) m)}
    (hT : IsUTransGroup (unitaryInvolution F 2 f) a T)
    (hnorm : ∀ {k : K}, k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) →
      ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k)
    (hcore : pCoreOf 2 (Subgroup.normalizer (T : Set (SU (unitaryInvolution F 2 f) m))) =
      uRad (unitaryInvolution F 2 f) a) :
    pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      (uRad (unitaryInvolution F 2 f) a).map Φ := by
  have hσ := unitaryInvolution_involutive hF
  haveI : Finite (SU (unitaryInvolution F 2 f) m) := Finite.of_injective _ Subtype.val_injective
  have hNT := normalizer_eq_uLine hσ ha hT
  have hcomap : (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)).comap Φ =
      uLine (unitaryInvolution F 2 f) a := by
    refine le_antisymm (fun g hg => ?_) ?_
    · obtain ⟨g', hg', hgg'⟩ := hnorm (Subgroup.mem_comap.1 hg)
      have hk : g'⁻¹ * g ∈ Φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hgg', inv_mul_cancel]
      have h1 := (uLine (unitaryInvolution F 2 f) a).mul_mem hg'
        (center_le_uLine hσ ha haa hT (hker hk))
      rwa [mul_inv_cancel_left] at h1
    · rw [← hNT, ← Subgroup.map_le_iff_le_comap]
      exact Subgroup.le_normalizer_map Φ
  rw [← map_pCoreOf_comap_eq_of_ker_le_center Φ hΦ hker, hcomap, ← hNT, hcore]

theorem rootIrrModel_su {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} {K : Type} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) m →* K} (hΦ : Function.Surjective Φ)
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m)) {a : Fin m → F}
    (ha : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    {T : Subgroup (SU (unitaryInvolution F 2 f) m)}
    (hT : IsUTransGroup (unitaryInvolution F 2 f) a T)
    (hnorm : ∀ {k : K}, k ∈ Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K) →
      ∃ g ∈ uLine (unitaryInvolution F 2 f) a, Φ g = k)
    (hcore : pCoreOf 2 (Subgroup.normalizer (T : Set (SU (unitaryInvolution F 2 f) m))) =
      uRad (unitaryInvolution F 2 f) a)
    (hirr : ∀ R : Subgroup (SU (unitaryInvolution F 2 f) m), T ≤ R →
      R ≤ uRad (unitaryInvolution F 2 f) a →
      (∀ b ∈ uLine (unitaryInvolution F 2 f) a, ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
        R = T ∨ R = uRad (unitaryInvolution F 2 f) a) :
    RootIrrModel K (T.map Φ) := by
  have hσ := unitaryInvolution_involutive hF
  have hNT := normalizer_eq_uLine hσ ha hT
  intro R hTR hRP hRn
  rw [pCoreOf_normalizer_map_eq hF hΦ hker ha haa hT hnorm hcore] at hRP ⊢
  have hRmap : (R.comap Φ ⊓ uRad (unitaryInvolution F 2 f) a).map Φ = R := by
    refine le_antisymm ((Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le Φ R)) ?_
    intro r hr
    obtain ⟨u, hu, rfl⟩ := hRP hr
    exact ⟨u, Subgroup.mem_inf.2 ⟨hr, hu⟩, rfl⟩
  have hn : ∀ b ∈ uLine (unitaryInvolution F 2 f) a,
      ∀ r ∈ R.comap Φ ⊓ uRad (unitaryInvolution F 2 f) a,
        b * r * b⁻¹ ∈ R.comap Φ ⊓ uRad (unitaryInvolution F 2 f) a := by
    intro b hb r hr
    obtain ⟨hrR, hru⟩ := Subgroup.mem_inf.1 hr
    refine Subgroup.mem_inf.2 ⟨?_, conj_mem_uRad hb hru⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    refine hRn (Φ b) (Subgroup.le_normalizer_map Φ ⟨b, ?_, rfl⟩) (Φ r) hrR
    rw [hNT]
    exact hb
  rcases hirr _ (le_inf (Subgroup.map_le_iff_le_comap.1 hTR) (le_uRad_of_isUTransGroup haa hT))
    inf_le_right hn with h | h
  · exact Or.inl (by rw [← hRmap, h])
  · exact Or.inr (by rw [← hRmap, h])

end CFSG.RankThree.GF2n.Tim79a
