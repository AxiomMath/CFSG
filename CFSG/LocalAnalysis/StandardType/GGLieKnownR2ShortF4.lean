module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4Iso
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open scoped commutatorElement

private lemma map_ggRootSub_mulAut {U : Type} [Group U] (φ : MulAut U)
    (Δ : UniversalRootDatum U) {β β' : Fin Δ.rank → ℤ}
    (h : (Δ.rootGroup β).map φ.toMonoidHom = Δ.rootGroup β') (u : U) :
    (ggRootSub Δ (MonoidHom.id U) β u).map φ.toMonoidHom =
      ggRootSub Δ (MonoidHom.id U) β' (φ u) := by
  simp only [ggRootSub, Subgroup.map_id]
  have hcomp : (MulAut.conj (φ u)).toMonoidHom.comp φ.toMonoidHom =
      φ.toMonoidHom.comp (MulAut.conj u).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, h]

theorem coreOne_F4
    {n f : ℕ} (hadm : StatedLieAdmissible .F4 n 2 f)
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .F4 n f).D β)
    (u : (ggU .F4 n f).K) {Rr Rm Q : Subgroup (ggU .F4 n f).K}
    (hRr : Rr = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .F4 n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  haveI : NeZero f := ⟨by omega⟩
  haveI : CharP (GaloisField 2 f) ReeTag.F4.prime :=
    inferInstanceAs (CharP (GaloisField 2 f) 2)
  let φ : MulAut (ggU .F4 n f).K := ReeTag.F4.finiteExceptionalAut (GaloisField 2 f)
  obtain ⟨β', hβ', hXβ', hXmβ', hlong⟩ :=
    finiteExceptionalAut_F4_map_rootGroup (K := GaloisField 2 f) (β := β) hβ
  have hl' : GGLongRoot (ggU .F4 n f).D β' := hlong.mpr hs
  have hRr' : Rr.map φ.toMonoidHom =
      ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) := by
    rw [hRr]
    exact map_ggRootSub_mulAut φ (ggU .F4 n f).D hXβ' u
  have hRm' : Rm.map φ.toMonoidHom =
      ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β') (φ u) := by
    rw [hRm]
    exact map_ggRootSub_mulAut φ (ggU .F4 n f).D hXmβ' u
  have hQmap : Q.map φ.toMonoidHom = pCoreOf 2 (Subgroup.normalizer
      (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
        Set (ggU .F4 n f).K)) := by
    rw [hQ, map_pCoreOf_normalizer_mulEquiv φ Rr, hRr']
  have hlong_one : pCoreOf 2 (Subgroup.normalizer
      (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
        Set (ggU .F4 n f).K)) ⊔
      (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) ⊔
        ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β') (φ u)) = ⊤ :=
    coreOne_F4_long hl' (φ u) rfl rfl rfl
  have htop : (Q ⊔ (Rr ⊔ Rm)).map φ.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hQmap, hRr', hRm']
    exact hlong_one
  have hle : (⊤ : Subgroup (ggU .F4 n f).K).map φ.toMonoidHom ≤
      (Q ⊔ (Rr ⊔ Rm)).map φ.toMonoidHom := by
    rw [htop]
    exact le_top
  exact eq_top_iff.mpr
    ((Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mp hle)

theorem coreFour_F4
    {n f : ℕ} (hadm : StatedLieAdmissible .F4 n 2 f)
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .F4 n f).D β)
    (u : (ggU .F4 n f).K) {Rr Rm Q : Subgroup (ggU .F4 n f).K}
    (hRr : Rr = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .F4 n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .F4 n f).K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  haveI : NeZero f := ⟨by omega⟩
  haveI : CharP (GaloisField 2 f) ReeTag.F4.prime :=
    inferInstanceAs (CharP (GaloisField 2 f) 2)
  let φ : MulAut (ggU .F4 n f).K := ReeTag.F4.finiteExceptionalAut (GaloisField 2 f)
  obtain ⟨β', hβ', hXβ', hXmβ', hlong⟩ :=
    finiteExceptionalAut_F4_map_rootGroup (K := GaloisField 2 f) (β := β) hβ
  have hl' : GGLongRoot (ggU .F4 n f).D β' := hlong.mpr hs
  have hRr' : Rr.map φ.toMonoidHom =
      ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) := by
    rw [hRr]
    exact map_ggRootSub_mulAut φ (ggU .F4 n f).D hXβ' u
  have hRm' : Rm.map φ.toMonoidHom =
      ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β') (φ u) := by
    rw [hRm]
    exact map_ggRootSub_mulAut φ (ggU .F4 n f).D hXmβ' u
  have hQmap : Q.map φ.toMonoidHom = pCoreOf 2 (Subgroup.normalizer
      (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
        Set (ggU .F4 n f).K)) := by
    rw [hQ, map_pCoreOf_normalizer_mulEquiv φ Rr, hRr']
  have hlong_four : ⁅pCoreOf 2 (Subgroup.normalizer
        (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
          Set (ggU .F4 n f).K)),
        pCoreOf 2 (Subgroup.normalizer
          (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
            Set (ggU .F4 n f).K))⁆ ≤
      ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) ∧
      pCoreOf 2 (Subgroup.normalizer
          (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
            Set (ggU .F4 n f).K)) ≤
        Subgroup.centralizer
          (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
            Set (ggU .F4 n f).K) :=
    coreFour_F4_long hl' (φ u) rfl rfl
  refine ⟨?_, ?_⟩
  · refine (Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mp ?_
    rw [Subgroup.map_commutator Q Q φ.toMonoidHom, hQmap, hRr']
    exact hlong_four.1
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : φ x ∈ pCoreOf 2 (Subgroup.normalizer
        (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) :
          Set (ggU .F4 n f).K)) := by
      rw [← hQmap]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
    have hy' : φ y ∈ ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β' (φ u) := by
      rw [← hRr']
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hy
    have hc : φ y * φ x = φ x * φ y :=
      (Subgroup.mem_centralizer_iff.mp (hlong_four.2 hx')) (φ y) hy'
    exact φ.injective (by rw [map_mul, map_mul, hc])

theorem itemOne_F4
    {n f : ℕ} (hadm : StatedLieAdmissible .F4 n 2 f)
    {X : Type} [Group X] [Finite X] (ψ : (ggU .F4 n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .F4 n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .F4 n f).D β)
    (u : (ggU .F4 n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .F4 n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .F4 n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    Q ⊔ (R ⊔ Rm) = ψ.range := by
  obtain rfl : R = (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemOne_of_core hker hodd (rootGroup_isPGroup_F4 hβ u rfl)
    (coreOne_F4 hadm hβ hs u rfl rfl rfl)

theorem itemFour_F4
    {n f : ℕ} (hadm : StatedLieAdmissible .F4 n 2 f)
    {X : Type} [Group X] [Finite X] (ψ : (ggU .F4 n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .F4 n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .F4 n f).D β)
    (u : (ggU .F4 n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .F4 n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .F4 n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    ⁅Q, Q⁆ ≤ R ∧ Q ≤ Subgroup.centralizer (R : Set X) := by
  obtain rfl : R = (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemFour_of_core hker hodd (rootGroup_isPGroup_F4 hβ u rfl)
    (coreFour_F4 hadm hβ hs u rfl rfl rfl).1 (coreFour_F4 hadm hβ hs u rfl rfl rfl).2

end CFSG.StandardType.LieKnownR2.Short
