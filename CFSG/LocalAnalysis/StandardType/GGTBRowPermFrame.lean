module

public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameW
public import CFSG.LocalAnalysis.StandardType.GGTBRowPermFrameAux
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTorusPermFrameW (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∃ k : ℕ, 3 ≤ k ∧ ¬ p ∣ k + 1 ∧ Nat.card ↥A = p ^ k ∧
        GGWeylFrame p A (CoxeterMatrix.A k)

theorem ggTorusPermFrameW_of_permEltSC {p r d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (hpd : ¬ p ∣ d) (h : GGTorusPermEltSC p d R) :
    GGTorusPermFrameW p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAab, hAI, -, h3, hsc⟩ := hA
  obtain ⟨Θ, hW, hP, hN⟩ := exists_permModel hp hZ hIp hcp h hψ hker hperf hAab hAI h3 hsc
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd4 : 4 ≤ d := by
    have hcard : Nat.card ↥A = p ^ (d - 1) := by
      rw [← Nat.card_congr Θ.toEquiv, ggTBRowPerm_card_sumZero' d p]
    have h3d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans (le_of_eq hcard))
    omega
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn3 : 3 ≤ n := by omega
  let Φ : Equiv.Perm (Fin (n + 1)) →* MulAut ↥A :=
    ((MulAut.congr Θ : MulAut ↥(UCoord.sumZero (n + 1) p) →* MulAut ↥A)).comp
      (UCoord.permAutVHom (n + 1) p)
  have hΦapply : ∀ σ : Equiv.Perm (Fin (n + 1)),
      Φ σ = MulAut.congr Θ (UCoord.permAutV σ) := fun _ => rfl
  have hrange : Φ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨σ, rfl⟩
      obtain ⟨m, hm, hmα⟩ := hP σ
      rw [hΦapply σ, ← hmα]
      exact ggConjAut_mem_ggAutomizer
        (H := (MulAut.conj : L' →* MulAut L').range) (MonoidHom.mem_range.mpr ⟨m, rfl⟩) hm
    · intro v hv
      obtain ⟨g, hg, hgN, hgv⟩ := mem_ggAutomizer_iff.mp hv
      obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hg
      have hveq : v = ggConjAut A hgN :=
        MulEquiv.ext fun b => Subtype.ext ((hgv b).trans (ggConjAut_apply A hgN b).symm)
      obtain ⟨π, hπ⟩ := hN m hgN
      exact MonoidHom.mem_range.mpr ⟨π, by rw [hΦapply, ← hπ, hveq]⟩
  have hΦinj : Function.Injective Φ := by
    intro σ τ hστ
    have h' : MulAut.congr Θ (UCoord.permAutV σ) =
        MulAut.congr Θ (UCoord.permAutV τ) := by
      simpa only [hΦapply] using hστ
    exact UCoord.permAutV_injective hp hp2 ((MulAut.congr Θ).injective h')
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm n
  let eΦ : Equiv.Perm (Fin (n + 1)) ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hΦinj).trans (MulEquiv.subgroupCongr hrange)
  let f : (CoxeterMatrix.A n).Group ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := e0.trans eΦ
  have hgen : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ((eΦ σ : ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) =
        MulAut.congr Θ (UCoord.permAutV σ) := by
    intro σ
    dsimp only [eΦ]
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
    exact hΦapply σ
  choose m hm hmα using fun i : Fin n => hP (Equiv.swap i.castSucc i.succ)
  have hweyl : ∀ i : Fin n, GGTorusWeylElt p A (m i) := fun i => hW (m i) (hm i)
  have hrefl : ∀ i : Fin n, GGIsReflection p (ggConjAut A (hm i)) := by
    intro i
    have hk : i.castSucc ≠ i.succ := ne_of_lt (Fin.castSucc_lt_succ (i := i))
    obtain ⟨hpow, hfix⟩ := UCoord.isPseudoReflection_permAutV_swap (d := n + 1) hp hp2 hk
    rw [hmα i]
    refine ⟨?_, (ggIsPseudoReflection_congr Θ hpow hfix).2⟩
    rw [sq, ← map_mul, ← UCoord.permAutV_mul, Equiv.swap_mul_self, UCoord.permAutV_one,
      map_one]
  have he : ∀ i : Fin n,
      (f ((CoxeterMatrix.A n).simple i) : MulAut ↥A) = ggConjAut A (hm i) := by
    intro i
    have hfk : (f ((CoxeterMatrix.A n).simple i) :
        ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) =
        eΦ (Equiv.swap i.castSucc i.succ) := by
      dsimp only [f]
      rw [MulEquiv.trans_apply, he0 i]
    rw [hfk, hgen (Equiv.swap i.castSucc i.succ)]
    exact (hmα i).symm
  refine ⟨n, hn3, hpd, ?_, m, hm, hweyl, hrefl, f, he⟩
  rw [← Nat.card_congr Θ.toEquiv]
  simpa using ggTBRowPerm_card_sumZero' (n + 1) p

end CFSG.StandardType

end

