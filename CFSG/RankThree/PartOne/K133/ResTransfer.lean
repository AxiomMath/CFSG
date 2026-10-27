module

public import CFSG.RankThree.PartOne.K133.ResData

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree.GroupTheory

theorem GoodRes.of_mulEquiv {p : ℕ} (hp : p.Prime) {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : GoodRes p Y) : GoodRes p X := by
  classical
  intro Ē hE hc hRes
  have : Fact p.Prime := ⟨hp⟩
  set Φ : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom with hΦ
  set Ψ : MulAut Y →* MulAut X := (MulAut.congr e).symm.toMonoidHom with hΨ
  have hΦinj : Function.Injective Φ := (MulAut.congr e).injective
  have hΨinj : Function.Injective Ψ := (MulAut.congr e).symm.injective
  have hΦapp : ∀ (ψ : MulAut X) (y : Y), Φ ψ y = e (ψ (e.symm y)) := fun ψ y => rfl
  have hΨΦ : ∀ ψ : MulAut X, Ψ (Φ ψ) = ψ := fun ψ => (MulAut.congr e).symm_apply_apply ψ
  have hΦΨ : ∀ ψ : MulAut Y, Φ (Ψ ψ) = ψ := fun ψ => (MulAut.congr e).apply_symm_apply ψ
  have hΨapp : ∀ (ψ : MulAut Y) (x : X), Ψ ψ x = e.symm (ψ (e x)) := by
    intro ψ x
    have := hΦapp (Ψ ψ) (e x)
    rw [hΦΨ, e.symm_apply_apply] at this
    rw [this, e.symm_apply_apply]
  have hE' : IsElementaryAbelian p (Ē.map Φ) := by
    have := hE
    exact IsElementaryAbelian.map Φ
  have hc' : Nat.card (Ē.map Φ) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hΦinj, hc]
  obtain ⟨C, hCĒ, hCc, Kb, hKs, hKn, hpK, hfix⟩ := hRes
  have eK : ↥Kb ≃* ↥(Kb.map e.toMonoidHom) := Subgroup.equivMapOfInjective Kb e.toMonoidHom e.injective
  have hRes' : ResConfig p Y (Ē.map Φ) := by
    refine ⟨C.map Φ, Subgroup.map_mono hCĒ, by rw [Subgroup.card_map_of_injective hΦinj, hCc],
      Kb.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · have := hKs
      exact eK.symm.isSimpleGroup
    · obtain ⟨a, b, hab⟩ := hKn
      exact ⟨eK a, eK b, fun h => hab (eK.injective (by rw [map_mul, map_mul]; exact h))⟩
    · rw [← Nat.card_congr eK.toEquiv]
      exact hpK
    · rintro _ ⟨ψ, hψ, rfl⟩ _ ⟨k, hk, rfl⟩
      show Φ ψ (e k) = e k
      rw [hΦapp, e.symm_apply_apply, hfix ψ hψ k hk]
  rcases h _ hE' hc' hRes' with ⟨S, hS1, hS2, hSst⟩ | ⟨P, hPĒ, hPc, S, hS2, hSst, φ, hφP, s, hsS, hφs⟩
  · left
    refine ⟨S.map e.symm.toMonoidHom, ?_, hS2.map _, ?_⟩
    · intro hbot
      exact hS1 ((Subgroup.map_eq_bot_iff_of_injective S e.symm.injective).1 hbot)
    · intro ψ hψ s' hs'
      obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.1 hs'
      refine Subgroup.mem_map.2 ⟨Φ ψ s₀, hSst _ (Subgroup.mem_map_of_mem Φ hψ) s₀ hs₀, ?_⟩
      show e.symm (Φ ψ s₀) = ψ (e.symm s₀)
      rw [hΦapp, e.symm_apply_apply]
  · right
    refine ⟨P.map Ψ, ?_, ?_, S.map e.symm.toMonoidHom, hS2.map _, ?_, Ψ φ, Subgroup.mem_map_of_mem Ψ hφP,
      e.symm s, Subgroup.mem_map_of_mem _ hsS, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (hPĒ hx)
      rw [hΨΦ]
      exact hy
    · rw [Subgroup.card_map_of_injective hΨinj, hPc]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨s₀, hs₀, rfl⟩
      refine Subgroup.mem_map.2 ⟨x s₀, hSst x hx s₀ hs₀, ?_⟩
      show e.symm (x s₀) = Ψ x (e.symm s₀)
      rw [hΨapp, e.apply_symm_apply]
    · intro hfix'
      apply hφs
      have h1 : Ψ φ (e.symm s) = e.symm (φ s) := by
        rw [hΨapp, e.apply_symm_apply]
      rw [h1] at hfix'
      exact e.symm.injective hfix'

end CFSG.RankThree.PartOne.K133
