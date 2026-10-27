module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcNCRoots
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType.LieKnownR2.E6

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.Blueprint.Chevalley

theorem odd_card_ker_e6Isogeny
    {K : Type} [Field K] [Finite K] [CharP K 2] : Odd (Nat.card (e6Isogeny K).ker) := by
  have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker (p := 2) K
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)

theorem center_le_ker_e6Isogeny
    {K : Type} [Field K] [Finite K] :
    Subgroup.center ↥(e6Data_valid.minGroup K) ≤ (e6Isogeny K).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hc : e6Isogeny K z ∈ Subgroup.center ↥(adjointGroup .E6 K) := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨g, rfl⟩ := e6Isogeny_surjective K c
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz g)]
  rw [center_adjointGroup_eq_bot (τ := .E6) (K := K)] at hc
  exact (Subgroup.mem_bot.1 hc)

theorem ggRootNoCentral_e6
    {n f : ℕ}
    {β : Fin (ggU .E6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E6 n f).D.roots)
    (u : (ggU .E6 n f).K) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .E6 n f).K)
      (ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) β u) := by
  haveI : Finite ↥(e6Data_valid.minGroup (GaloisField 2 f)) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid (GaloisField 2 f)
  have hβ' : IsRoot .E6 β := by
    have h : β ∈ (e6Datum (GaloisField 2 f)).roots := hβ
    rw [MinData.Valid.minDatum_roots] at h
    exact h
  have hadj := ExcNC.rootNoCentral_adj_simplyLaced .E6 (Or.inl rfl) (GaloisField 2 f)
    (β := β) (mem_adjDatum_roots.2 hβ')
  have hX : GGRootNoCentralAt (⊤ : Subgroup ↥(e6Data_valid.minGroup (GaloisField 2 f)))
      ((e6Datum (GaloisField 2 f)).rootGroup β) := by
    refine Cover.ggRootNoCentralAt_top_of_map_surjective (e6Isogeny (GaloisField 2 f))
      (e6Isogeny_surjective (GaloisField 2 f))
      (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f))
      odd_card_ker_e6Isogeny
      (isPGroup_two_range_of_charTwo (e6Data_valid.xHom (GaloisField 2 f) β)) ?_
    rw [CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := GaloisField 2 f) hβ']
    exact hadj
  have h := ggRootNoCentralAt_top_map_mulEquiv (MulAut.conj u) hX
  rw [ggRootSub, Subgroup.map_id]
  exact h

theorem ggRootNoCentralAt_ggU_e6
    {n f : ℕ} {X : Type} [Group X] [Finite X]
    (φ : (ggU .E6 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    {β : Fin (ggU .E6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E6 n f).D.roots)
    (u : (ggU .E6 n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .E6 n f).D φ β u) := by
  have hodd : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat (odd_card_ker_e6Isogeny (K := GaloisField 2 f))
      (Subgroup.card_dvd_of_le (hker.trans center_le_ker_e6Isogeny))
  have hR : IsPGroup 2 (ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) β u) :=
    rootGroup_isPGroup_E6 u rfl
  have hbase : GGRootNoCentralAt (⊤ : Subgroup (ggU .E6 n f).K)
      (ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) β u) :=
    ggRootNoCentral_e6 hβ u
  have h := SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker φ hker hodd hR hbase
  have hgoal : (ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) β u).map φ =
      ggRootSub (ggU .E6 n f).D φ β u :=
    (Short.ggRootSub_eq_map (ggU .E6 n f).D φ β u).symm
  rwa [hgoal] at h

end CFSG.StandardType.LieKnownR2.E6
