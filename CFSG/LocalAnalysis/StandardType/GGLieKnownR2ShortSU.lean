module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSUShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUNorm
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUPCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUGen
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUCent
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUIrr
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.StandardType.GGOppRadSpU
  CFSG.QuasithinUnique.B113Lie.Sp CFSG.LieType.Universal.Unitary.SUExtras
open scoped commutatorElement

private lemma natRep_mem_span_of_mem_normalizer {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {g : ↥(SU (unitaryInvolution F 2 f) n)}
    (hg : g ∈ Subgroup.normalizer
      (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {a : Fin n → F} (ha : a ∈ Submodule.span F {v, w}) :
    natRep (SU (unitaryInvolution F 2 f) n) g a ∈ Submodule.span F {v, w} := by
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp ha
  have hv : v ∈ Submodule.span F {v, w} := Submodule.subset_span (by simp)
  have hw : w ∈ Submodule.span F {v, w} := Submodule.subset_span (by simp)
  rw [map_add, map_smul, map_smul]
  rcases (mem_normalizer_suPair_iff hfr).1 hg with ⟨a₁, d₁, h1, h2⟩ | ⟨a₁, d₁, h1, h2⟩
  · rw [h1, h2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hv))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw))
  · rw [h1, h2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hv))

theorem shortCores_SU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {n : ℕ}
    {β : Fin (Unitary.rootDatum hc n).rank → ℤ} (hβ : β ∈ (Unitary.rootDatum hc n).roots)
    (hs : ¬ GGLongRoot (Unitary.rootDatum hc n) β)
    (h2β : 2 • β ∉ (Unitary.rootDatum hc n).roots)
    (u : ↥(SU (unitaryInvolution F 2 f) n))
    {Rr Rm Q : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hRr : Rr = ((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom)
    (hRm : Rm = ((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set ↥(SU (unitaryInvolution F 2 f) n)))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ ∧
      ∀ V : Subgroup ↥(SU (unitaryInvolution F 2 f) n), ggCenterOf Q ≤ V → V ≤ Q →
        Subgroup.normalizer (Rr : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
          Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)) →
        V = ggCenterOf Q ∨ V = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, w, v', w', hfr, hA, hB⟩ :=
    Geo.exists_unitPairGroup_eq_conj_rootGroup_SU hc n hβ hs h2β u
  have hRr' : Rr = suPair (unitaryInvolution F 2 f) n v w := hRr.trans hA
  have hRm' : Rm = suPair (unitaryInvolution F 2 f) n v' w' := hRm.trans hB
  have hQ' : Q = suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) := by
    rw [hQ, hRr']
    refine le_antisymm (pCoreOf_normalizer_suPair_le_suStabRad hfr) ?_
    refine GGRootNorm.le_pCoreOf_of_normalized (suStabRad_le_normalizer_suPair hfr)
      (rad_isPGroup (isIsometric_natRep_SU (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hc) n) (natRep_injective _) 2
        (suFrame_isTotallyIsotropic hfr)) ?_
    intro m hm t ht
    exact rad_conj_mem (isIsometric_natRep_SU (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hc) n)
      (fun a ha => natRep_mem_span_of_mem_normalizer hfr hm ha)
      (fun a ha => natRep_mem_span_of_mem_normalizer hfr (inv_mem hm) ha) ht
  subst hRr' hRm' hQ'
  refine ⟨suStabRad_sup_suPair_eq_top hfr, fun V hZV hVQ hNV => ?_⟩
  rw [ggCenterOf_suStabRad_eq hfr] at hZV ⊢
  exact suStabRad_irreducible hf hfr hZV hVQ hNV

private theorem isPGroup_rootSub_PSU_of_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (L : LieUniversal)
    (hL : L = ⟨↥(SU (unitaryInvolution F 2 f) n), Unitary.rootDatum hc n⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (u : L.K) {Rr : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u) : IsPGroup 2 Rr := by
  subst hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : Nonempty (Fin n) := by
    by_contra h0
    have hn : n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · exact absurd ⟨⟨0, h⟩⟩ h0
    subst hn
    exact SUExtras.toStd_ne_zero_of_mem_roots hβ (funext fun i => i.elim0)
  have h : IsPGroup 2 ((Unitary.rootDatum hc n).rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_rootGroup (unitaryInvolution_involutive hc)
      (SUExtras.toStd_ne_zero_of_mem_roots hβ)
  subst hRr
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

private theorem false_of_mem_roots_trivialUniversal (L : LieUniversal) (hL : L = trivialUniversal)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) : False := by
  subst hL
  rcases hβ with ⟨w, i, -⟩ | ⟨w, i, -, -⟩ <;> exact i.elim0

private theorem shortCores_PSU_of_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {n : ℕ} (L : LieUniversal)
    (hL : L = ⟨↥(SU (unitaryInvolution F 2 f) n), Unitary.rootDatum hc n⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (hs : ¬ GGLongRoot L.D β)
    (h2β : 2 • β ∉ L.D.roots) (u : L.K) {Rr Rm Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hRm : Rm = ggRootSub L.D (MonoidHom.id L.K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ ∧ ∀ V : Subgroup L.K, ggCenterOf Q ≤ V → V ≤ Q →
      Subgroup.normalizer (Rr : Set L.K) ≤ Subgroup.normalizer (V : Set L.K) →
        V = ggCenterOf Q ∨ V = Q := by
  subst hL
  exact shortCores_SU hc hf hβ hs h2β u (hRr.trans (Subgroup.map_id _))
    (hRm.trans (Subgroup.map_id _)) hQ

theorem rootGroup_isPGroup_PSU
    {n f : ℕ}
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (u : (ggU .PSU n f).K) {Rr : Subgroup (ggU .PSU n f).K}
    (hRr : Rr = ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) β u) :
    IsPGroup 2 Rr := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hf1 : 1 ≤ f
  · have e : ggU .PSU n f = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf1) n⟩ := by
      simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
    exact isPGroup_rootSub_PSU_of_eq (card_galoisField_two_mul 2 f hf1) _ e hβ u hRr
  · exfalso
    have e : ggU .PSU n f = trivialUniversal := by
      simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
    exact false_of_mem_roots_trivialUniversal _ e hβ

theorem coreOne_PSU
    {n f : ℕ}
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSU n f).D β)
    (hf : 2 ≤ f) (h2β : 2 • β ∉ (ggU .PSU n f).D.roots)
    (u : (ggU .PSU n f).K) {Rr Rm Q : Subgroup (ggU .PSU n f).K}
    (hRr : Rr = ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSU n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by omega
  have e : ggU .PSU n f = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
      Unitary.rootDatum (card_galoisField_two_mul 2 f hf1) n⟩ := by
    simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
  exact (shortCores_PSU_of_eq (card_galoisField_two_mul 2 f hf1) hf _ e hβ hs h2β u hRr hRm
    hQ).1

theorem coreFourIrred_PSU
    {n f : ℕ}
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSU n f).D β)
    (hf : 2 ≤ f) (h2β : 2 • β ∉ (ggU .PSU n f).D.roots)
    (u : (ggU .PSU n f).K) {Rr Rm Q : Subgroup (ggU .PSU n f).K}
    (hRr : Rr = ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSU n f).K))) :
    ∀ V : Subgroup (ggU .PSU n f).K, ggCenterOf Q ≤ V → V ≤ Q →
      Subgroup.normalizer (Rr : Set (ggU .PSU n f).K) ≤
        Subgroup.normalizer (V : Set (ggU .PSU n f).K) →
      V = ggCenterOf Q ∨ V = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by omega
  have e : ggU .PSU n f = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
      Unitary.rootDatum (card_galoisField_two_mul 2 f hf1) n⟩ := by
    simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
  exact (shortCores_PSU_of_eq (card_galoisField_two_mul 2 f hf1) hf _ e hβ hs h2β u hRr hRm
    hQ).2

theorem itemOne_PSU
    {n f : ℕ}
    {X : Type} [Group X] [Finite X] (ψ : (ggU .PSU n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSU n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSU n f).D β)
    (hf : 2 ≤ f) (h2β : 2 • β ∉ (ggU .PSU n f).D.roots)
    (u : (ggU .PSU n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .PSU n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .PSU n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    Q ⊔ (R ⊔ Rm) = ψ.range := by
  obtain rfl : R = (ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemOne_of_core hker hodd (rootGroup_isPGroup_PSU hβ u rfl)
    (coreOne_PSU hβ hs hf h2β u rfl rfl rfl)

theorem itemFourIrred_PSU
    {n f : ℕ}
    {X : Type} [Group X] [Finite X] (ψ : (ggU .PSU n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSU n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSU n f).D β)
    (hf : 2 ≤ f) (h2β : 2 • β ∉ (ggU .PSU n f).D.roots)
    (u : (ggU .PSU n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .PSU n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .PSU n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    ∀ V : Subgroup X, ggCenterOf Q ≤ V → V ≤ Q → V ≠ ggCenterOf Q → V ≠ Q →
      ¬ (ψ.range ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (V : Set X)) := by
  obtain rfl : R = (ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemFourIrred_of_core hker hodd (rootGroup_isPGroup_PSU hβ u rfl)
    (coreFourIrred_PSU hβ hs hf h2β u rfl rfl rfl)

end CFSG.StandardType.LieKnownR2.Short
