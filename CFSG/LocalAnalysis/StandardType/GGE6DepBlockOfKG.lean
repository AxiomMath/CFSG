module

public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockFrame
public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Helpers

variable {L' R : Type} [Group L'] [Group R]

private theorem exists_aut_of_mem {I : Set (MulAut R)} {A : Subgroup (MulAut L')} {ψ : L' →* R}
    (hind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l)) {F : Set (MulAut L')}
    (hFA : ∀ f ∈ F, f ∈ A) : ∀ f ∈ F, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (f l) := by
  intro f hf
  obtain ⟨φ, -, hφ⟩ := hind f (hFA f hf)
  exact ⟨φ, hφ⟩

private theorem mem_ggFix_single_iff (f : MulAut L') (l : L') :
    l ∈ ggFix f ↔ ∀ g ∈ ({f} : Set (MulAut L')), g l = l := by
  constructor
  · intro h g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact h
  · intro h
    exact h f rfl

private theorem mem_inf_ggFix_pair_iff (f g : MulAut L') (l : L') :
    l ∈ ggFix f ⊓ ggFix g ↔ ∀ k ∈ ({f, g} : Set (MulAut L')), k l = l := by
  constructor
  · rintro ⟨hf, hg⟩ k hk
    rcases hk with rfl | hk
    · exact hf
    · rw [Set.mem_singleton_iff.mp hk]
      exact hg
  · intro h
    exact ⟨h f (Set.mem_insert _ _), h g (Set.mem_insert_of_mem _ rfl)⟩

private theorem commutator_eq_of_isComponentOf {C N : Subgroup L'} (hN : IsComponentOf N C) :
    ⁅N, N⁆ = N :=
  Subgroup.isPerfect_iff.mp (⟨hN.2.2.1⟩ : Group.IsPerfect ↥N)

private theorem le_ggFix_mul (a b : MulAut L') : ggFix a ⊓ ggFix b ≤ ggFix (a * b) := by
  rintro x ⟨ha, hb⟩
  change a x = x at ha
  change b x = x at hb
  change (a * b) x = x
  rw [MulAut.mul_apply, hb, ha]

end Helpers

theorem ggE6DepBlocks_of_kgLayers {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGE6KGLayers R I) : GGE6DepBlocks R I := by
  intro L' _ _ ψ A hTB h35 hNT
  obtain ⟨hK1, hK2⟩ := h L' ψ A hTB h35
  obtain ⟨hψ, hker, -, hAel, hind, -⟩ := hTB
  refine ⟨?_, ?_⟩
  · intro c hc P hP hPperf
    obtain ⟨ER, hER⟩ := hK1 c hc
    obtain ⟨E, hE, -, hEmax, -⟩ := ggLayerOf_lift ψ hψ hker {(c : MulAut L')}
      (exists_aut_of_mem hind (by simp)) (ggFix (c : MulAut L')) (mem_ggFix_single_iff _) hER
    exact (hEmax P hP hPperf).trans (le_iSup₂_of_le E hE le_rfl)
  · intro a b hab
    obtain ⟨Ev, Eab, hEv, hEab, hL3, hL4, hM⟩ := hK2 a b hab
    obtain ⟨Dv, hDv, hDvu, hDvmax, hDvmap⟩ := ggLayerOf_lift ψ hψ hker
      {(a : MulAut L') * (b : MulAut L')}
      (exists_aut_of_mem hind (by
        intro f hf
        rw [Set.mem_singleton_iff.mp hf]
        exact A.mul_mem a.2 b.2))
      (ggFix ((a : MulAut L') * (b : MulAut L'))) (mem_ggFix_single_iff _) hEv
    obtain ⟨N, hN, hNu, -, hNmap⟩ := ggLayerOf_lift ψ hψ hker {(a : MulAut L'), (b : MulAut L')}
      (exists_aut_of_mem hind (by
        intro f hf
        rcases hf with rfl | hf
        · exact a.2
        · rw [Set.mem_singleton_iff.mp hf]
          exact b.2))
      (ggFix (a : MulAut L') ⊓ ggFix (b : MulAut L')) (mem_inf_ggFix_pair_iff _ _) hEab
    have hNDv : N ≤ Dv :=
      hDvmax N (hN.1.trans (le_ggFix_mul _ _)) (commutator_eq_of_isComponentOf hN)
    refine ⟨Dv, N, hDv, hDvu, hN, hNu, hNDv, ?_, ?_, ?_, ?_⟩
    ·
      let π : ↥N →* ↥Eab := (ψ.comp N.subtype).codRestrict Eab fun n => by
        rw [← hNmap]
        exact Subgroup.mem_map.mpr ⟨n.1, n.2, rfl⟩
      refine hM ↥N π ?_ ?_ hN.2.2.1
      · intro e
        have he : (e : R) ∈ N.map ψ := by
          rw [hNmap]
          exact e.2
        obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp he
        exact ⟨⟨n, hn⟩, Subtype.ext hne⟩
      · intro n hn
        have hn1 : ψ n = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
        have hc : (n : L') ∈ Subgroup.center L' := hker hn1
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.mp hc g)
    · exact three_pow_three_le_card_ggFixedByCentres hAel h35 hNT hab
    · intro u hu
      obtain ⟨l, hl, hlu⟩ := hL3 u hu
      obtain ⟨n, hn, hnl⟩ := exists_mem_conj_eq_of_map_eq ψ hker hNmap hl
      exact ⟨n, hn, hnl.trans hlu⟩
    · obtain ⟨l, hl, hnorm, hmove⟩ := hL4
      obtain ⟨n, hn, hnl⟩ := exists_mem_conj_eq_of_map_eq ψ hker hDvmap hl
      refine ⟨n, hn, ?_, ?_⟩
      · rw [hnl]
        exact hnorm
      · rw [hnl]
        exact hmove

theorem ggE6DepBlockKnown_of_kgLayers (h : GGE6KGLayerInput) : GGE6DepBlockKnown := by
  intro lab hlab hΛ Q hQ
  exact largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hq, hp⟩ => ⟨hq, fun hs hna => ggE6DepBlocks_of_kgLayers (hp hs hna)⟩)
    (h lab hlab hΛ Q hQ)

end CFSG.StandardType

end
