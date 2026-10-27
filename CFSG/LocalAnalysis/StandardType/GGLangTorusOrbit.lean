module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusMem
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count
public import CFSG.RankThree.PartOne.KE.CTTorus

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut

private theorem torOrb_rootChar_corootPair
    {τ : Tag} {L : Type} [Field L] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {ζ : Lˣ}
    (v : Fin τ.rank → ℤ) :
    rootChar (fun j => ζ ^ corootPair α (Pi.single j 1)) v = ζ ^ corootPair α v := by
  rw [rootChar_zpow]
  congr 1
  rw [dotProduct]
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv, corootPair_sum hα Finset.univ v (fun i => (Pi.single i 1 : Fin τ.rank → ℤ))]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem torOrb_corootPair_smul_of_rho_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hρβ : S.ρ β = ε • α) :
    ∀ γ, IsRoot τ γ → corootPair α (S.ρ γ) = ε * corootPair β γ := by
  intro γ hγ
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hnorm : iform α α = iform β β := by
    have h1 := S.frob.iform_eq β β
    rw [hρβ, iform_smul_left, iform_smul_right, ← mul_assoc, hεε, one_mul] at h1
    exact h1
  have hform : iform α (S.ρ γ) = ε * iform β γ := by
    have h1 := S.frob.iform_eq β γ
    rw [hρβ, iform_smul_left] at h1
    have h2 : ε * (ε * iform α (S.ρ γ)) = ε * iform β γ := by rw [h1]
    rwa [← mul_assoc, hεε, one_mul] at h2
  apply mul_right_cancel₀ (iform_self_pos_of_isRoot hβ).ne'
  calc corootPair α (S.ρ γ) * iform β β
      = corootPair α (S.ρ γ) * iform α α := by rw [hnorm]
    _ = 2 * iform α (S.ρ γ) := corootPair_mul hα (S.ρ γ)
    _ = ε * (2 * iform β γ) := by rw [hform]; ring
    _ = ε * (corootPair β γ * iform β β) := by rw [corootPair_mul hβ γ]
    _ = (ε * corootPair β γ) * iform β β := by ring

private theorem torOrb_zpow_eq_pow_of_dvd
    {L : Type} [DivisionRing L] {q p : ℕ} {ε c : ℤ} {ζ : Lˣ}
    (hpq : (p : ℤ) ∣ (q : ℤ) - ε) (hζ : ζ ^ p = 1) :
    ζ ^ (ε * c) = (ζ ^ c) ^ q := by
  obtain ⟨k, hk⟩ := hpq
  have hq : (q : ℤ) = ε + p * k := by linarith
  rw [← zpow_natCast (ζ ^ c) q, ← zpow_mul]
  conv_rhs => rw [hq, show c * (ε + p * k) = p * (c * k) + ε * c by ring, zpow_add, zpow_mul,
    zpow_natCast, hζ, one_zpow, one_mul]

private theorem torOrb_mem_torus_single
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hpq : (p : ℤ) ∣ (S.D.q : ℤ) - ε) {ζ : Lˣ} (hζ : ζ ^ p = 1)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hρα : S.ρ α = ε • α) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) ∈ S.D.torus := by
  apply rootDiagUnit_mem_torus_of_rootChar S hτ
  intro γ hγ
  rw [torOrb_rootChar_corootPair hα (S.ρ γ),
    torOrb_corootPair_smul_of_rho_eq S hα hα hε hρα γ hγ,
    torOrb_zpow_eq_pow_of_dvd (q := S.D.q) (p := p) (ε := ε) (c := corootPair α γ) hpq hζ,
    torOrb_rootChar_corootPair hα γ]

private theorem torOrb_mem_torus_pair
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hpq : (p : ℤ) ∣ (S.D.q : ℤ) - ε) {ζ : Lˣ} (hζ : ζ ^ p = 1)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hρα : S.ρ α = ε • β) (hρβ : S.ρ β = ε • α) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1) *
      ζ ^ corootPair β (Pi.single j 1)) ∈ S.D.torus := by
  have hroot : ∀ v, rootChar (fun j => ζ ^ corootPair α (Pi.single j 1) *
      ζ ^ corootPair β (Pi.single j 1)) v = ζ ^ corootPair α v * ζ ^ corootPair β v := by
    intro v
    rw [show (fun j => ζ ^ corootPair α (Pi.single j 1) * ζ ^ corootPair β (Pi.single j 1)) =
        (fun j => ζ ^ corootPair α (Pi.single j 1)) *
          (fun j => ζ ^ corootPair β (Pi.single j 1)) from rfl, CTTorus.rootChar_mul,
      torOrb_rootChar_corootPair hα v, torOrb_rootChar_corootPair hβ v]
  apply rootDiagUnit_mem_torus_of_rootChar S hτ
  intro γ hγ
  rw [hroot (S.ρ γ),
    torOrb_corootPair_smul_of_rho_eq S hβ hα hε hρα γ hγ,
    torOrb_corootPair_smul_of_rho_eq S hα hβ hε hρβ γ hγ,
    torOrb_zpow_eq_pow_of_dvd (q := S.D.q) (p := p) (ε := ε) (c := corootPair β γ) hpq hζ,
    torOrb_zpow_eq_pow_of_dvd (q := S.D.q) (p := p) (ε := ε) (c := corootPair α γ) hpq hζ,
    ← mul_pow, hroot γ]
  congr 1
  exact mul_comm _ _

theorem langCorootFactor_mem_torus
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hpq : (p : ℤ) ∣ (S.D.q : ℤ) - ε) {ζ : Lˣ} (hζ : ζ ^ p = 1) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hρα : S.ρ α = ε • α) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) ∈ S.D.torus :=
  torOrb_mem_torus_single S hτ hε hpq hζ hα hρα

theorem langCorootPairFactor_mem_torus
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ) (hpq : (p : ℤ) ∣ (S.D.q : ℤ) - ε)
    {ζ : Lˣ} (hζ : ζ ^ p = 1) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hπα : latPerm π α ≠ α) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1) *
      ζ ^ corootPair (latPerm π α) (Pi.single j 1)) ∈ S.D.torus := by
  obtain ⟨hρρ, -, -, -⟩ := rho_orthogonal_of_latPerm_ne S hτ π hπ hε hρ hα hπα
  have hrρ : IsRoot τ (S.ρ α) := (S.frob.isRoot_iff α).2 hα
  rcases hε with hε1 | hε1
  · subst hε1
    have hρα : S.ρ α = (1 : ℤ) • latPerm π α := hρ α hα
    have hβroot : IsRoot τ (latPerm π α) := by
      have h1 : S.ρ α = latPerm π α := by simpa using hρα
      rw [← h1]
      exact hrρ
    have hρβ : S.ρ (latPerm π α) = (1 : ℤ) • α := by
      have h1 : latPerm π α = S.ρ α := by simpa using hρα.symm
      rw [h1, hρρ, one_smul]
    exact torOrb_mem_torus_pair S hτ (Or.inl rfl) hpq hζ hα hβroot hρα hρβ
  · subst hε1
    have hρα : S.ρ α = ((-1 : ℤ)) • latPerm π α := hρ α hα
    have hβeq : latPerm π α = - S.ρ α := by
      rw [hρα, neg_one_smul, neg_neg]
    have hβroot : IsRoot τ (latPerm π α) := by
      rw [hβeq]
      exact IsRoot.neg hrρ
    have hρβ : S.ρ (latPerm π α) = ((-1 : ℤ)) • α := by
      rw [hβeq, S.frob.neg_eq, hρρ, neg_one_smul]
    exact torOrb_mem_torus_pair S hτ (Or.inr rfl) hpq hζ hα hβroot hρα hρβ

end CFSG.StandardType.LangRat
