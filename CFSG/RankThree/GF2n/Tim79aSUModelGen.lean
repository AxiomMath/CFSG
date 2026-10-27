module

public import CFSG.RankThree.GF2n.Tim79aSUGenSteps
public import CFSG.RankThree.GF2n.Tim79a33

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.Timmesfeld.LieEmbed

@[expose] def SUFrameGenAll : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    ∀ m : ℕ, 4 ≤ m → SUFrameGen (unitaryInvolution F 2 f) m (2 * m - 3)

theorem suModelGen_of_frameGen (h : SUFrameGenAll) : SUModelGen := by
  intro m F _ _ _ f hF hm K _ Φ hΦ _ a T ha haa hT
  classical
  obtain ⟨U, hUlen, hUiso, hUgen⟩ := h F f hF m hm
  have hγ : ∀ u : {u // u ∈ U}, ∃ γ : SU (unitaryInvolution F 2 f) m,
      suMat (unitaryInvolution F 2 f) m γ *ᵥ a = u.1 := fun u =>
    exists_suMat_mulVec_eq_of_iso hF (by omega) ha haa (hUiso u.1 u.2).1 (hUiso u.1 u.2).2
  choose γ hγ using hγ
  have hLtop : (⨆ u : {u // u ∈ U}, conjSub T (γ u)) = ⊤ := by
    refine hUgen _ fun u hu => ?_
    have hX := hT.conjSub (γ ⟨u, hu⟩)
    rw [hγ ⟨u, hu⟩] at hX
    exact (uTransLe_iff hX).2 (le_iSup (fun u : {u // u ∈ U} => conjSub T (γ u)) ⟨u, hu⟩)
  refine ⟨(U.attach.map fun u => Φ (γ u)).toFinset, ?_, ?_⟩
  · calc _ ≤ (U.attach.map fun u => Φ (γ u)).length := List.toFinset_card_le _
      _ = U.length := by simp
      _ ≤ 2 * m - 3 := hUlen
  · rw [eq_top_iff]
    intro k _
    obtain ⟨x, rfl⟩ := hΦ k
    have hx : x ∈ ⨆ u : {u // u ∈ U}, conjSub T (γ u) := by rw [hLtop]; trivial
    refine (iSup_le fun u => ?_ : (⨆ u : {u // u ∈ U}, conjSub T (γ u)) ≤
      (⨆ g ∈ (U.attach.map fun u => Φ (γ u)).toFinset, conjSub (T.map Φ) g).comap Φ) hx
    rw [← Subgroup.map_le_iff_le_comap, ← ModelRank.conjSub_map]
    refine le_biSup (fun g => conjSub (T.map Φ) g) ?_
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map, List.mem_attach, true_and]
    exact ⟨u, rfl⟩

theorem suFrameGen_mono {F : Type} [Field F] {σ : F ≃+* F} {m k k' : ℕ} (hk : k ≤ k')
    (h : SUFrameGen σ m k) : SUFrameGen σ m k' := by
  obtain ⟨U, hU, h1, h2⟩ := h
  exact ⟨U, hU.trans hk, h1, h2⟩

theorem suFrameGenAll_holds : SUFrameGenAll := by
  intro F _ _ _ f hF m hm
  revert hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · by_cases h4 : m = 4
      · subst h4
        exact suFrameGen_mono (by norm_num) (suFrameGen_four hF)
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
        exact suFrameGen_mono (by omega)
          (suFrameGen_add_two hF (by omega) (ih m' (by omega) (by omega)))
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hp : Fin.rev (⟨j, by omega⟩ : Fin (n + 1)) = ⟨j, by omega⟩ := by
        ext
        simp only [Fin.val_rev]
        omega
      exact suFrameGen_mono (by omega)
        (suFrameGen_succ hF (by omega) hp (ih n (by omega) (by omega)))

theorem suModelGen_holds : SUModelGen :=
  suModelGen_of_frameGen suFrameGenAll_holds

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

theorem tim79a33TildeStatement_holds : Tim79a33TildeStatement :=
  tim79a33TildeStatement_of_gen suModelGen_holds

end CFSG.RankThree.GF2n.Tim79a
