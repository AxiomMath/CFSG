module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGRCKoneHyps
public import CFSG.LocalAnalysis.StandardType.GGRCSmallOfCard
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCClassify
public import CFSG.LocalAnalysis.StandardType.GGRCScalarsPm1
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGRCCardJoin
public import CFSG.LocalAnalysis.StandardType.GGRCWeylOfPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResCaseILargeInput_of_inputs
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) : GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K => GGResLeviDatum p Bs L J K ggSelI (ggTypRankGe 8) := by
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := hP
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hxB : x ∈ B := hH.1.1.2.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hH.1.2.1.1 hxB
  have h8 : 8 ≤ Fintype.card Λ := by
    have hh := htyp
    rw [ggTypRankGe] at hh
    rwa [Nat.card_eq_fintype_card] at hh
  have hind : LinearIndependent (ZMod p) h := by simpa [ggSelI] using hsel
  have hrk : 3 ≤ Fintype.card Λ := by omega
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hA' : A' = Subgroup.closure (Set.range φ) := by
    dsimp [A']
    rw [hAL, hAK, ← Subgroup.closure_union]
    congr 1
    ext γ
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl)
      · exact ⟨some i, rfl⟩
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr (Or.inr rfl)
      | some i => exact Or.inl ⟨i, rfl⟩
  have hA : A = Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)) := by
    dsimp [A]
    rw [hA', MonoidHom.map_closure, ← Set.range_comp]
    rfl
  obtain ⟨hspan, hker, hconn⟩ :=
    ggRC_kone_hyps hFix hFixK hp2 hH hWL hCL hWK hCK hrk hφ hL hK hind hAL hAK
  have hα : ∀ o : Option Λ, α o (h o) = 2 := by
    intro o
    cases o with
    | none =>
      have h1 := hK none none
      rw [hCK.1 none] at h1
      simpa using h1
    | some i =>
      have h1 := hL i i
      rw [hCL.1 i] at h1
      simpa using h1
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let bV : Module.Basis (Option Λ) (ZMod p) V :=
    Module.Basis.mk hind (by rw [hspan])
  have hn : Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
    rw [Module.finrank_eq_card_basis bV, Fintype.card_option]
  have h9 : 9 ≤ Fintype.card Λ + 1 := by omega
  have hirr : ZS.AbsIrred p A :=
    ggRC_absIrred_of_connected (p := p) (V := V) hp2 (fun o => ggLin (p := p) ι (φ o)) h α
      hφ hα hspan hker hconn A hA
  have hreflLin : ∀ o, GGLinRefl (ggLin (p := p) ι (φ o)) :=
    fun o => (ggRC_isReflection_iff_linRefl (p := p) ι (φ o)).mp (hrefl o)
  have hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} := by
    rw [hA]
    apply le_antisymm
    · apply Subgroup.closure_mono
      intro x hx
      obtain ⟨o, rfl⟩ := hx
      exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hreflLin o⟩
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  have hcardA : Nat.card A = Nat.card A' := by
    change Nat.card ↥(A'.map (ggLin (p := p) ι)) = Nat.card ↥A'
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv).symm
  have hWcard : Nat.card ↥(ggAutomizer L Bs) = Nat.card ML.Group :=
    (Nat.card_congr fL.toEquiv).symm
  have hjoin : Nat.card A' ≤
      Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
    ggRC_card_join_le hOrb hH hxBs
  have hNB : Nat.card ↥Bs = p ^ (Fintype.card Λ + 1) := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
      _ = p ^ (Fintype.card Λ + 1) := by rw [hn]
  have hsmall' : 8 * Nat.card A' < p ^ ((Fintype.card Λ + 1) * Fintype.card Λ / 2) :=
    ggRC_small_of_card (Fact.out : p.Prime) hp2 ML hWL h8 hNB (by rw [← hWcard]; exact hjoin)
  have hsmall : 8 * Nat.card A <
      p ^ ((Fintype.card Λ + 1) * ((Fintype.card Λ + 1) - 1) / 2) := by
    rw [hcardA, Nat.add_sub_cancel]
    exact hsmall'
  have hpm1 : 5 ≤ p → ∀ f : Module.Basis (Fin (Fintype.card Λ + 1)) (ZMod p) V,
      (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin (Fintype.card Λ + 1)))
          (c : Fin (Fintype.card Λ + 1) → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) →
      ∃ b' : Module.Basis (Fin (Fintype.card Λ + 1)) (ZMod p) V, ∀ a ∈ A,
        ∃ (σ : Equiv.Perm (Fin (Fintype.card Λ + 1)))
            (c : Fin (Fintype.card Λ + 1) → ZMod p),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i) := by
    intro hp5 f hmon
    have hmon' : ∀ a ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
        ∃ (σ : Equiv.Perm (Fin (Fintype.card Λ + 1)))
          (c : Fin (Fintype.card Λ + 1) → ZMod p),
          (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i) :=
      fun a ha => hmon a (hA ▸ ha)
    obtain ⟨b', hb'⟩ :=
      ggRC_scalars_pm1 hJr hPump hLB hSP hp5 hH hWL hCL h8 hφ hrefl hL hind hAL hAK hJ f
        (hA ▸ hirr) hmon'
    exact ⟨b', fun a ha => hb' a (hA ▸ ha)⟩
  obtain hclass | ⟨N, hN, e, he⟩ :=
    ggRC_classify hKG hp2 hn h9 A hirr hgen hsmall hpm1
  ·
    exact ggRC_weylReflGroup_of_linWeyl ι A' hclass
  ·
    let e' : A' ≃* Equiv.Perm (Fin N) :=
      (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)).trans e
    have hrefl' : ∀ r : A', GGIsReflection p (r : MulAut ↥Bs) →
        ∃ i j, i ≠ j ∧ e' r = Equiv.swap i j := by
      intro r hr
      have hrlin : GGLinRefl (ggLin (p := p) ι (r : MulAut ↥Bs)) :=
        (ggRC_isReflection_iff_linRefl (p := p) ι (r : MulAut ↥Bs)).mp hr
      obtain ⟨i, j, hij, heij⟩ :=
        he (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι) r) hrlin
      exact ⟨i, j, hij, heij⟩
    have hgen' : GGReflGenerated p A' := by
      rw [GGReflGenerated, hA']
      apply le_antisymm
      · apply Subgroup.closure_mono
        intro x hx
        obtain ⟨o, rfl⟩ := hx
        exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hrefl o⟩
      · rw [Subgroup.closure_le]
        intro x hx
        exact hx.1
    exact ggRC_weyl_of_perm A' hN e' hrefl' hgen'

end CFSG.StandardType
