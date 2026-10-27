module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin

@[expose] def Rank2Levi {Y : Type} [Group Y] (P : Subgroup Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (n : ℕ),
    Nat.card K = 2 ^ n ∧ 2 ≤ n ∧
      ∃ g : ↥(perfectCore P) →* Matrix.SpecialLinearGroup (Fin 2) K,
        Function.Surjective g ∧ IsPGroup 2 g.ker

structure Rank2Pkg (Y : Type) [Group Y] (U : Subgroup Y) (P : Fin 2 → Subgroup Y) : Prop where
  res : ResidualOvergroupsAt Y U P
  norm : ∀ j, Subgroup.normalizer (U : Set Y) ≤ P j
  levi : ∀ j, Rank2Levi (P j)
  charTwo : ∀ j, CharTwo (perfectCore (P j))

theorem charTwo_of_equiv {G G' : Type*} [Group G] [Group G'] {X : Subgroup G} {X' : Subgroup G'}
    (e : ↥X ≃* ↥X') (h : CharTwo X) : CharTwo X' := by
  rw [charTwo_iff_internal] at h ⊢
  exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2 e h

theorem Rank2Levi.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {P : Subgroup Y}
    (h : Rank2Levi P) (e : Y ≃* Y') : Rank2Levi (P.map e.toMonoidHom) := by
  obtain ⟨K, hF, hFin, hCh, n, hK, hn, g, hg, hker⟩ := h
  let eP : ↥(perfectCore (P.map e.toMonoidHom)) ≃* ↥(perfectCore P) :=
    (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom P).symm).trans
      (Subgroup.equivMapOfInjective (perfectCore P) e.toMonoidHom e.injective).symm
  refine ⟨K, hF, hFin, hCh, n, hK, hn, g.comp eP.toMonoidHom, hg.comp eP.surjective, ?_⟩
  intro x
  have hx : (eP x.1 : ↥(perfectCore P)) ∈ g.ker := x.2
  obtain ⟨k, hk⟩ := hker ⟨eP x.1, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (eP x.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : eP (x.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact eP.injective (h2.trans (map_one eP).symm)

theorem Rank2Pkg.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {U : Subgroup Y}
    {P : Fin 2 → Subgroup Y} (h : Rank2Pkg Y U P) (e : Y ≃* Y') :
    Rank2Pkg Y' (U.map e.toMonoidHom) (fun j => (P j).map e.toMonoidHom) where
  res := h.res.map e
  norm j := by
    rw [← Subgroup.map_equiv_normalizer_eq U e]
    exact Subgroup.map_mono (h.norm j)
  levi j := (h.levi j).map e
  charTwo j := by
    have h1 := CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv e (h.charTwo j)
    rwa [map_perfectCore e.toMonoidHom (P j)] at h1

end CFSG.Quasithin.Rk2
