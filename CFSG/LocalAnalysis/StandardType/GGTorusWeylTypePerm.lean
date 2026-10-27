module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13PermConv

import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private lemma ggWTPerm_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma ggWTPerm_card_sumZero_le (d p : ℕ) [NeZero p] :
    Nat.card ↥(UCoord.sumZero d p) ≤ p ^ (d - 1) := by
  rcases d with _ | m
  · rw [Nat.zero_sub, pow_zero]
    refine le_of_eq ?_
    have htop : UCoord.sumZero 0 p = ⊤ := by
      rw [eq_top_iff]
      intro f _
      rw [UCoord.mem_sumZero]
      simp
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_fin, pow_zero]
  · simpa using UCoord.card_sumZero_le m p

theorem ggTorusWeylTypeW_of_permEltSC {p r d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) : GGTorusWeylTypeW p r R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAab, hAI, -, h3, hsc⟩ := hA
  obtain ⟨Θ, hW, hP, hN⟩ := exists_permModel hp hZ hIp hcp h hψ hker hperf hAab hAI h3 hsc
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd4 : 4 ≤ d := by
    have hle := ggWTPerm_card_sumZero_le d p
    rw [Nat.card_congr Θ.toEquiv] at hle
    have h3d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
    omega
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
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
  have hcard12 : Nat.card
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≠ 12 := by
    have hcard : Nat.card
        ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = (n + 1).factorial := by
      rw [← Nat.card_congr f.toEquiv, Nat.card_congr e0.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_perm, Fintype.card_fin]
    rw [hcard]
    have h4 : 4 ≤ n + 1 := by omega
    have hf : 24 ≤ (n + 1).factorial := by
      have := Nat.factorial_le h4
      norm_num at this
      exact this
    omega
  refine ⟨Fin n, CoxeterMatrix.A n, f,
    Or.inl ⟨n, Equiv.refl (Fin n), hn1, Or.inl (ggWTPerm_reindex_refl _).symm⟩,
    hcard12, ?_⟩
  intro k
  have hfk : (f ((CoxeterMatrix.A n).simple k) :
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) =
      eΦ (Equiv.swap k.castSucc k.succ) := by
    dsimp only [f]
    rw [MulEquiv.trans_apply, he0 k]
  rw [hfk, hgen (Equiv.swap k.castSucc k.succ)]
  obtain ⟨m, hm, hmα⟩ := hP (Equiv.swap k.castSucc k.succ)
  have hk : k.castSucc ≠ k.succ := ne_of_lt (Fin.castSucc_lt_succ (i := k))
  obtain ⟨hpow, hfix⟩ := UCoord.isPseudoReflection_permAutV_swap hp hp2 hk
  refine ⟨m, hm, hW m hm, hmα.symm, ?_, ?_⟩
  · rw [← map_pow, sq, ← UCoord.permAutV_mul, Equiv.swap_mul_self, UCoord.permAutV_one,
      map_one]
  · exact (ggIsPseudoReflection_congr Θ hpow hfix).2

end CFSG.StandardType

end
