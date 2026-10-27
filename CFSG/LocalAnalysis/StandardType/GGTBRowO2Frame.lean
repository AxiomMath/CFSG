module

public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
public import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative

@[expose] def GGTorusDBFrameW (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∃ k : ℕ, 4 ≤ k ∧ Nat.card ↥A = p ^ k ∧
        (GGWeylFrame p A (ggCoxeterMatrixD k) ∨ GGWeylFrame p A (CoxeterMatrix.B k))

theorem ggO2Row_automizer_eq_evenSigned {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L' : Type}
    [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hD : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j))
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)))
    (i₀ : Fin k)
    (hno : MulAut.congr Θ (sgnAut i₀) ∉ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      (DScalarTorus.evenSignedGroup (p := p) (N := k)).map (MulAut.congr Θ).toMonoidHom := by
  set Aut := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hAutDef
  set H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    Aut.comap (MulAut.congr Θ).toMonoidHom with hH
  have hHsp : ∀ u ∈ H, IsSignedPerm ⇑u := by
    intro u hu
    have huW : MulAut.congr Θ u ∈ Aut := Subgroup.mem_comap.mp hu
    obtain ⟨_, ⟨n, rfl⟩, hmn, hmu⟩ := mem_ggAutomizer_iff.mp huW
    have hcu : MulAut.congr Θ u = ggConjAut A hmn := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      exact (hmu b).trans (ggConjAut_apply A hmn b).symm
    have hu' : u = (MulAut.congr Θ).symm (ggConjAut A hmn) := by
      rw [← hcu, MulEquiv.symm_apply_apply]
    rw [hu']
    exact hN n hmn
  have hdH : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H := by
    intro i j hij
    obtain ⟨n, hn, hnD⟩ := hD i j hij
    refine Subgroup.mem_comap.mpr ?_
    change MulAut.congr Θ (sgnAut i * sgnAut j) ∈ Aut
    rw [← hnD]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hpH : ∀ σ : Equiv.Perm (Fin k), permAut σ ∈ H := by
    intro σ
    obtain ⟨n, hn, hnP⟩ := hP σ
    refine Subgroup.mem_comap.mpr ?_
    change MulAut.congr Θ (permAut σ) ∈ Aut
    rw [← hnP]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hle : DScalarTorus.evenSignedGroup (p := p) (N := k) ≤ H :=
    DScalarTorus.evenSignedGroup_le hp2 hdH hpH
  have hge : H ≤ DScalarTorus.evenSignedGroup (p := p) (N := k) := by
    intro u hu
    rcases OrthExcEven.mem_or_mul_mem_of_isSignedPerm
        (fun i j hij => DScalarTorus.sgnAut_pair_mem_evenSignedGroup hij)
        (fun a b _ => DScalarTorus.permAut_mem_evenSignedGroup _) i₀ (hHsp u hu) with h1 | h1
    · exact h1
    · exfalso
      apply hno
      have h2 : u * sgnAut i₀ ∈ H := hle h1
      have h3 := H.mul_mem (H.inv_mem hu) h2
      rw [inv_mul_cancel_left] at h3
      exact Subgroup.mem_comap.mp h3
  have hHeq : H = DScalarTorus.evenSignedGroup (p := p) (N := k) := le_antisymm hge hle
  rw [← hHeq]
  exact (Subgroup.map_comap_eq_self_of_surjective (f := (MulAut.congr Θ).toMonoidHom)
    (MulAut.congr Θ).surjective Aut).symm

theorem ggO2Row_weylFrame_D_of_evenModel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L' : Type}
    [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (hk : 4 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hW : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hST : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j * permAut (Equiv.swap i j)))
    (hAut : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      (DScalarTorus.evenSignedGroup (p := p) (N := k)).map (MulAut.congr Θ).toMonoidHom) :
    GGWeylFrame p A (ggCoxeterMatrixD k) := by
  classical
  have hp : p.Prime := Fact.out
  have hab : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  have hdata : ∀ i : Fin k, ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (DScalarTorus.simpleReflection hk i) := by
    intro i
    by_cases h : i.val + 1 < k
    · obtain ⟨n, hn, he⟩ := hP (Equiv.swap i ⟨i.val + 1, h⟩)
      refine ⟨n, hn, ?_⟩
      rw [he, DScalarTorus.simpleReflection, dif_pos h]
    · obtain ⟨n, hn, he⟩ := hST _ _ hab
      refine ⟨n, hn, ?_⟩
      rw [he, DScalarTorus.simpleReflection, dif_neg h]
  choose n hn heq using hdata
  have hrefl : ∀ i, GGIsReflection p (ggConjAut A (hn i)) := by
    intro i
    rw [heq i]
    by_cases h : i.val + 1 < k
    · have hne : i ≠ (⟨i.val + 1, h⟩ : Fin k) := by
        intro hh
        have : i.val = i.val + 1 := congrArg Fin.val hh
        omega
      rw [DScalarTorus.simpleReflection, dif_pos h]
      exact ggSpSigned_ggIsReflection_congr hp hp2 Θ (SpCoord.permAut_swap_sq _ _)
        (SpCoord.card_fix_permAut_swap hp hp2 hne)
    · rw [DScalarTorus.simpleReflection, dif_neg h]
      exact ggSpSigned_ggIsReflection_congr hp hp2 Θ (OrthExcEven.sgnTransp_sq hab)
        (OrthExcEven.card_fix_sgnTransp hp hp2 hab)
  obtain ⟨eS, heS⟩ := DScalarTorus.exists_evenSignedCoxeterEquiv (p := p) hp2 hk
  let Φ : ↥(DScalarTorus.evenSignedGroup (p := p) (N := k)) ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    ((DScalarTorus.evenSignedGroup (p := p) (N := k)).equivMapOfInjective
      (MulAut.congr Θ).toMonoidHom (MulAut.congr Θ).injective).trans
      (MulEquiv.subgroupCongr hAut.symm)
  refine ⟨n, hn, fun i => hW (n i) (hn i), hrefl, eS.trans Φ, fun i => ?_⟩
  rw [heq i, ← heS i]
  rfl

theorem ggO2Row_weylFrame_B_of_evenModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type}
    [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (hk : 3 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hW : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    (hD : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j))
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)))
    (i₀ : Fin k)
    (hyes : MulAut.congr Θ (sgnAut i₀) ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :
    GGWeylFrame p A (CoxeterMatrix.B k) := by
  have hmem : ∀ i : Fin k, MulAut.congr Θ (sgnAut i) ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      exact hyes
    · obtain ⟨n, hn, he⟩ := hD i i₀ hi
      have h1 : MulAut.congr Θ (sgnAut i * sgnAut i₀) ∈
          ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
        rw [← he]
        exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
      have h2 := Subgroup.mul_mem _ h1 hyes
      rwa [← map_mul (MulAut.congr Θ), mul_assoc, OrthExcEven.sgnAut_mul_self, mul_one] at h2
  refine ggWeylFrame_of_signedModel hp hp2 hk Θ hW (fun i => ?_) hP hN
  obtain ⟨_, ⟨n, rfl⟩, hn, hφ⟩ := mem_ggAutomizer_iff.mp (hmem i)
  refine ⟨n, hn, MulEquiv.ext fun b => Subtype.ext ?_⟩
  exact (ggConjAut_apply A hn b).trans (hφ b).symm

theorem ggO2Row_weylFrame_of_evenModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type}
    [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (hk : 4 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hW : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    (hD : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j))
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hST : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j * permAut (Equiv.swap i j)))
    (hN : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    GGWeylFrame p A (ggCoxeterMatrixD k) ∨ GGWeylFrame p A (CoxeterMatrix.B k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hs : MulAut.congr Θ (sgnAut (⟨0, by omega⟩ : Fin k)) ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  · exact Or.inr (ggO2Row_weylFrame_B_of_evenModel hp hp2 (by omega) Θ hW hD hP hN _ hs)
  · exact Or.inl (ggO2Row_weylFrame_D_of_evenModel hp2 hk Θ hW hP hST
      (ggO2Row_automizer_eq_evenSigned hp2 Θ hD hP hN _ hs))

theorem ggO2Row_dbFrameW_of_evenSignedPermEltSC {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {kP : ℕ → Prop} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (hkP : ∀ k, kP k → 4 ≤ k)
    (h : GGTorusEvenSignedPermEltSC p R kP) : GGTorusDBFrameW p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAab, hAI, -, h3, hsc⟩ := hA
  obtain ⟨k, Θ, -, hkp, hW, hD, hP, hST, hN⟩ :=
    OrthExcEven.exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hAab hAI h3 hsc
  have hk4 : 4 ≤ k := hkP k hkp
  refine ⟨k, hk4, ?_, ggO2Row_weylFrame_of_evenModel hp hp2 hk4 Θ hW hD hP hST hN⟩
  have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
    rw [Nat.card_fun, Nat.card_fin]
    congr 1
    exact Nat.card_zmod p
  have hcard : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card ↥A :=
    Nat.card_congr Θ.toEquiv
  rw [← hcard, hcV]

end CFSG.StandardType

end
