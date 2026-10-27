module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Conj
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Gen
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Norm
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Center
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Irr
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootCores

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

private lemma ggCenterOf_map_mulAut {K : Type} [Group K] (e : MulAut K) (X : Subgroup K) :
    ggCenterOf (X.map e.toMonoidHom) = (ggCenterOf X).map e.toMonoidHom := by
  apply le_antisymm
  · rintro z hz
    obtain ⟨hzX, hzc⟩ := (mem_ggCenterOf_iff (X.map e.toMonoidHom) z).mp hz
    obtain ⟨y, hyX, rfl⟩ := Subgroup.mem_map.mp hzX
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    refine (mem_ggCenterOf_iff X y).mpr ⟨hyX, fun v hv => ?_⟩
    have h := hzc (e v) (Subgroup.mem_map.mpr ⟨v, hv, rfl⟩)
    have h' : e (v * y) = e (y * v) := by
      rw [map_mul, map_mul]; exact h
    exact e.injective h'
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨hyX, hyc⟩ := (mem_ggCenterOf_iff X y).mp hy
    refine (mem_ggCenterOf_iff (X.map e.toMonoidHom) (e y)).mpr
      ⟨Subgroup.mem_map.mpr ⟨y, hyX, rfl⟩, fun w hw => ?_⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    have h := congrArg e (hyc v hv)
    rw [map_mul, map_mul] at h
    exact h

private lemma irreducibility_map_mulAut {K : Type} [Group K] (e : MulAut K)
    {R Q : Subgroup K}
    (h : ∀ V : Subgroup K, ggCenterOf Q ≤ V → V ≤ Q →
      Subgroup.normalizer (R : Set K) ≤ Subgroup.normalizer (V : Set K) →
      V = ggCenterOf Q ∨ V = Q) :
    ∀ V : Subgroup K, ggCenterOf (Q.map e.toMonoidHom) ≤ V → V ≤ Q.map e.toMonoidHom →
      Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup K) : Set K) ≤
        Subgroup.normalizer (V : Set K) →
      V = ggCenterOf (Q.map e.toMonoidHom) ∨ V = Q.map e.toMonoidHom := by
  intro V hZV hVQ hNV
  have hcen : ggCenterOf (Q.map e.toMonoidHom) = (ggCenterOf Q).map e.toMonoidHom :=
    ggCenterOf_map_mulAut e Q
  have hVcen : ggCenterOf Q ≤ V.map e.symm.toMonoidHom := by
    have h1 : (ggCenterOf Q).map e.toMonoidHom ≤ V := by rw [← hcen]; exact hZV
    have h2 := Subgroup.map_mono (f := e.symm.toMonoidHom) h1
    rwa [GGRootNorm.map_symm_map e (ggCenterOf Q)] at h2
  have hVle : V.map e.symm.toMonoidHom ≤ Q := by
    have h2 := Subgroup.map_mono (f := e.symm.toMonoidHom) hVQ
    rwa [GGRootNorm.map_symm_map e Q] at h2
  have hVnorm : Subgroup.normalizer (R : Set K) ≤
      Subgroup.normalizer ((V.map e.symm.toMonoidHom : Subgroup K) : Set K) := by
    have h1 : (Subgroup.normalizer (R : Set K)).map e.toMonoidHom ≤
        Subgroup.normalizer (V : Set K) := by
      rw [← GGRootNorm.normalizer_map_mulEquiv e R]
      exact hNV
    have h2 := Subgroup.map_mono (f := e.symm.toMonoidHom) h1
    rw [GGRootNorm.map_symm_map e (Subgroup.normalizer (R : Set K)),
        ← GGRootNorm.normalizer_map_mulEquiv e.symm V] at h2
    exact h2
  have hV' := h (V.map e.symm.toMonoidHom) hVcen hVle hVnorm
  have hVmap : (V.map e.symm.toMonoidHom).map e.toMonoidHom = V :=
    GGRootNorm.map_map_symm e V
  rcases hV' with h' | h'
  · left
    rw [← hVmap, h', hcen]
  · right
    rw [← hVmap, h']

theorem rootGroup_isPGroup_twistedE6
    {n f : ℕ}
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (u : (ggU .twistedE6 n f).K) {Rr : Subgroup (ggU .twistedE6 n f).K}
    (hRr : Rr = ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u) :
    IsPGroup 2 Rr := by
  subst hRr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : IsPGroup 2 ((twistedE6Datum 2 f).rootGroup β) :=
    isPGroup_two_twistedRootGroup (frobQ 2 f) hβ
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

private theorem coreOne_twistedE6_of_eq
    {f : ℕ} (L : LieUniversal)
    (hL : L = ⟨twistedE6Group 2 f, twistedE6Datum 2 f⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (hs : ¬ GGLongRoot L.D β)
    (hf : 2 ≤ f) (u : L.K) {Rr Rm Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hRm : Rm = ggRootSub L.D (MonoidHom.id L.K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  subst hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ : ∀ c : GaloisField 2 (2 * f), frobQ 2 f (frobQ 2 f c) = c :=
    frobQ_frobQ 2 f (by omega)
  have hct := twistedDatum_isCTGroupDatum (frobQ 2 f) hθ
    (iSup_twistedDatum_rootGroup (frobQ 2 f) hθ)
  obtain ⟨w, hw⟩ := twE6_exists_weyl_of_not_long (frobQ 2 f) hβ hs
  obtain ⟨g, hgR, hgRm⟩ := exists_conj_ggRootSub_of_weylAction
    (D := twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f))
    (n := nHat (frobQ 2 f)) (H := hHat (GaloisField 2 (2 * f)) (frobQ 2 f))
    hct (twE6_alpha_mem_roots (frobQ 2 f)) w hw u
  let S : Subgroup (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup twE6Alpha
  have hRr' : Rr = S.map (MulAut.conj g).toMonoidHom := hRr.trans hgR
  have hRm' : Rm = ((twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup
      (-twE6Alpha)).map (MulAut.conj g).toMonoidHom := hRm.trans hgRm
  have hQmap : Q = (pCoreOf 2 (Subgroup.normalizer (S : Set _))).map
      (MulAut.conj g).toMonoidHom := by
    rw [hQ, hRr']
    exact (map_pCoreOf_normalizer_mulEquiv (MulAut.conj g) S).symm
  have hQ0le : twE6Rad (frobQ 2 f) ≤ pCoreOf 2 (Subgroup.normalizer (S : Set _)) := by
    refine GGRootNorm.le_pCoreOf_of_normalized ?_ ?_ ?_
    · exact (twE6Rad_le_centralizer_alpha (frobQ 2 f) hθ).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact isPGroup_two_twE6Rad (frobQ 2 f) hθ
    · exact Subgroup.le_normalizer_iff.mp (twE6_normalizer_le_normalizer_rad f hf)
  have hk : 4 ≤ Nat.card (GaloisField 2 (2 * f)) := by
    rw [GaloisField.card 2 (2 * f) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htop : twE6Rad (frobQ 2 f) ⊔ (S ⊔
      ((twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup (-twE6Alpha))) = ⊤ :=
    twE6_rad_sup_rankOne_eq_top (frobQ 2 f) hθ hk
  have hsup : pCoreOf 2 (Subgroup.normalizer (S : Set _)) ⊔ (S ⊔
      ((twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup (-twE6Alpha))) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le_sup_right hQ0le _
  rw [hQmap, hRr', hRm']
  rw [← Subgroup.map_sup, ← Subgroup.map_sup]
  rw [hsup, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

theorem coreOne_twistedE6
    {n f : ℕ}
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .twistedE6 n f).D β)
    (hf : 2 ≤ f)
    (u : (ggU .twistedE6 n f).K) {Rr Rm Q : Subgroup (ggU .twistedE6 n f).K}
    (hRr : Rr = ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .twistedE6 n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  have e : ggU .twistedE6 n f = ⟨twistedE6Group 2 f, twistedE6Datum 2 f⟩ := by
    simp only [ggU, lieUniversal]
  exact coreOne_twistedE6_of_eq _ e hβ hs hf u hRr hRm hQ

private theorem coreFourIrred_twistedE6_of_eq
    {f : ℕ} (L : LieUniversal)
    (hL : L = ⟨twistedE6Group 2 f, twistedE6Datum 2 f⟩)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (hs : ¬ GGLongRoot L.D β)
    (hf : 2 ≤ f) (u : L.K) {Rr Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    ∀ V : Subgroup L.K, ggCenterOf Q ≤ V → V ≤ Q →
      Subgroup.normalizer (Rr : Set L.K) ≤ Subgroup.normalizer (V : Set L.K) →
      V = ggCenterOf Q ∨ V = Q := by
  subst hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ : ∀ c : GaloisField 2 (2 * f), frobQ 2 f (frobQ 2 f c) = c :=
    frobQ_frobQ 2 f (by omega)
  have hct := twistedDatum_isCTGroupDatum (frobQ 2 f) hθ
    (iSup_twistedDatum_rootGroup (frobQ 2 f) hθ)
  obtain ⟨w, hw⟩ := twE6_exists_weyl_of_not_long (frobQ 2 f) hβ hs
  obtain ⟨g, hgR, -⟩ := exists_conj_ggRootSub_of_weylAction
    (D := twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f))
    (n := nHat (frobQ 2 f)) (H := hHat (GaloisField 2 (2 * f)) (frobQ 2 f))
    hct (twE6_alpha_mem_roots (frobQ 2 f)) w hw u
  let S : Subgroup (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).rootGroup twE6Alpha
  have hRr' : Rr = S.map (MulAut.conj g).toMonoidHom := hRr.trans hgR
  have hQmap : Q = (pCoreOf 2 (Subgroup.normalizer (S : Set _))).map
      (MulAut.conj g).toMonoidHom := by
    rw [hQ, hRr']
    exact (map_pCoreOf_normalizer_mulEquiv (MulAut.conj g) S).symm
  have hQ0 : pCoreOf 2 (Subgroup.normalizer (S : Set _)) = twE6Rad (frobQ 2 f) := by
    apply le_antisymm
    · exact twE6_pCoreOf_normalizer_le_rad f hf
    · refine GGRootNorm.le_pCoreOf_of_normalized ?_ ?_ ?_
      · exact (twE6Rad_le_centralizer_alpha (frobQ 2 f) hθ).trans
          (Subgroup.centralizer_le_normalizer _)
      · exact isPGroup_two_twE6Rad (frobQ 2 f) hθ
      · exact Subgroup.le_normalizer_iff.mp (twE6_normalizer_le_normalizer_rad f hf)
  have hbase : ∀ V : Subgroup (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)),
      ggCenterOf (pCoreOf 2 (Subgroup.normalizer (S : Set _))) ≤ V →
      V ≤ pCoreOf 2 (Subgroup.normalizer (S : Set _)) →
      Subgroup.normalizer (S : Set (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) ≤
        Subgroup.normalizer (V : Set (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f))) →
      V = ggCenterOf (pCoreOf 2 (Subgroup.normalizer (S : Set _))) ∨
        V = pCoreOf 2 (Subgroup.normalizer (S : Set _)) := by
    intro V h1 h2 h3
    have hcen0 : ggCenterOf (pCoreOf 2 (Subgroup.normalizer (S : Set _))) =
        twE6Cen (frobQ 2 f) :=
      (congrArg ggCenterOf hQ0).trans (twE6_ggCenterOf_rad (frobQ 2 f) hθ)
    have h4 : V = twE6Cen (frobQ 2 f) ∨ V = twE6Rad (frobQ 2 f) :=
      twE6_rad_irreducible f hf V (hcen0.symm.trans_le h1) (h2.trans hQ0.le) h3
    rcases h4 with h | h
    · left; exact h.trans hcen0.symm
    · right; exact h.trans hQ0.symm
  rw [hQmap, hRr']
  exact irreducibility_map_mulAut (MulAut.conj g) hbase

theorem coreFourIrred_twistedE6
    {n f : ℕ}
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .twistedE6 n f).D β)
    (hf : 2 ≤ f)
    (u : (ggU .twistedE6 n f).K) {Rr Q : Subgroup (ggU .twistedE6 n f).K}
    (hRr : Rr = ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .twistedE6 n f).K))) :
    ∀ V : Subgroup (ggU .twistedE6 n f).K, ggCenterOf Q ≤ V → V ≤ Q →
      Subgroup.normalizer (Rr : Set (ggU .twistedE6 n f).K) ≤
        Subgroup.normalizer (V : Set (ggU .twistedE6 n f).K) →
      V = ggCenterOf Q ∨ V = Q := by
  have e : ggU .twistedE6 n f = ⟨twistedE6Group 2 f, twistedE6Datum 2 f⟩ := by
    simp only [ggU, lieUniversal]
  exact coreFourIrred_twistedE6_of_eq _ e hβ hs hf u hRr hQ

theorem itemOne_twistedE6
    {n f : ℕ}
    {X : Type} [Group X] [Finite X] (ψ : (ggU .twistedE6 n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .twistedE6 n f).D β)
    (hf : 2 ≤ f)
    (u : (ggU .twistedE6 n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .twistedE6 n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .twistedE6 n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    Q ⊔ (R ⊔ Rm) = ψ.range := by
  obtain rfl : R = (ggRootSub (ggU .twistedE6 n f).D
      (MonoidHom.id (ggU .twistedE6 n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .twistedE6 n f).D
      (MonoidHom.id (ggU .twistedE6 n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemOne_of_core hker hodd (rootGroup_isPGroup_twistedE6 hβ u rfl)
    (coreOne_twistedE6 hβ hs hf u rfl rfl rfl)

theorem itemFourIrred_twistedE6
    {n f : ℕ}
    {X : Type} [Group X] [Finite X] (ψ : (ggU .twistedE6 n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .twistedE6 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .twistedE6 n f).D β)
    (hf : 2 ≤ f)
    (u : (ggU .twistedE6 n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .twistedE6 n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .twistedE6 n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    ∀ V : Subgroup X, ggCenterOf Q ≤ V → V ≤ Q → V ≠ ggCenterOf Q → V ≠ Q →
      ¬ (ψ.range ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (V : Set X)) := by
  obtain rfl : R = (ggRootSub (ggU .twistedE6 n f).D
      (MonoidHom.id (ggU .twistedE6 n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .twistedE6 n f).D
      (MonoidHom.id (ggU .twistedE6 n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemFourIrred_of_core hker hodd (rootGroup_isPGroup_twistedE6 hβ u rfl)
    (coreFourIrred_twistedE6 hβ hs hf u rfl rfl)

end CFSG.StandardType.LieKnownR2.Short
