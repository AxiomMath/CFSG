module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubExcl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4MaxEx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Sing

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem hasRightSingular_of_leftSingular {k : ℕ} (hk : 1 ≤ k) (P : Arc Γ k)
    (h : LeftSingular Γ G P.vert 0 k) : HasRightSingular Γ G k := by
  obtain ⟨w, hw, hne, hfix⟩ := h
  refine ⟨P.rev, w, ?_, ?_, ?_⟩
  · rwa [Arc.rev_vert_last]
  · rw [Arc.rev_vert, show k - (k - 1) = 0 + 1 by omega]
    exact hne
  · intro g hg
    refine hfix g ?_
    rw [mem_stabRange] at hg ⊢
    intro m h0 hm
    have := hg (k - m) (Nat.zero_le _) (Nat.sub_le _ _)
    rwa [Arc.rev_vert, Nat.sub_sub_self hm] at this

theorem fan40_lineSingLe {F : FanTree Γ G} (h40 : Fan40 F) {ℓ : Line Γ} {n : ℕ}
    (h : LineSingLe Γ G ℓ n) : 4 ≤ n := by
  obtain ⟨k, a', hk1, hkn, hsing⟩ := h
  by_contra hlt
  refine h40 k hk1 (by omega) ?_
  rcases hsing with h | h
  · exact ⟨ℓ.arc a' k, h⟩
  · exact hasRightSingular_of_leftSingular hk1 _ h

theorem Track.valence_vert_add_two (T : Track Γ G) (F : FanTree Γ G) (i : ℤ) :
    valence Γ (T.line.vert (i + 2)) = valence Γ (T.line.vert i) := by
  have h1 := F.alternating _ _ (T.line.adj i)
  have h2 := F.alternating _ _ (T.line.adj (i + 1))
  have h3 := F.valence (T.line.vert i)
  have h4 := F.valence (T.line.vert (i + 1))
  have h5 := F.valence (T.line.vert (i + 1 + 1))
  have e : T.line.vert (i + 1 + 1) = T.line.vert (i + 2) := by rw [show i + 1 + 1 = i + 2 by omega]
  rw [e] at h2 h5
  show Nat.card (Γ.neighborSet (T.line.vert (i + 2))) = Nat.card (Γ.neighborSet (T.line.vert i))
  omega

theorem Track.valence_vert_zpow (T : Track Γ G) (F : FanTree Γ G) (i k : ℤ) :
    valence Γ (T.line.vert (i + 2 * k)) = valence Γ (T.line.vert i) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show i + 2 * ((n : ℤ) + 1) = (i + 2 * n) + 2 by omega, T.valence_vert_add_two F, ih]
  | pred n ih =>
    have := T.valence_vert_add_two F (i + 2 * (-(n : ℤ) - 1))
    rw [show i + 2 * (-(n : ℤ) - 1) + 2 = i + 2 * (-(n : ℤ)) by omega] at this
    exact this.symm.trans ih

theorem fan47 (T : Track Γ G) (F : FanTree Γ G) (h40 : Fan40 F) (hPi : TrackInPi T) {a b c : ℤ}
    (hθ : IsTArc T a b) (hc : c = a ∨ c = b) : valence Γ (T.line.vert c) = 3 := by
  obtain ⟨a₀, b₀, hmax⟩ := fan42_2a_max T F h40
  have hev₀ := fan_4_3_2 T F hPi hmax.1
  obtain ⟨k, hk⟩ : ∃ k : ℤ, c = a₀ + 2 * k := by
    obtain ⟨k, hk⟩ := fan_4_3_2_transitive T F hPi (T.line.vert c) (T.line.vert a₀)
      ⟨a, b, hθ, by rcases hc with rfl | rfl <;> simp⟩ ⟨a₀, b₀, hmax.1, Or.inl rfl⟩
    rw [T.zpow_smul_vert] at hk
    have := Line.vert_injective F.isTree T.line hk
    exact ⟨-k, by omega⟩
  rw [hk, T.valence_vert_zpow F]
  by_contra hne
  have hval : ∀ v, valence Γ v = 3 ∨ valence Γ v = 5 := fun v => F.valence v
  have h5 : valence Γ (T.line.vert a₀) = 5 := by
    have := hval (T.line.vert a₀)
    omega
  have hab : Γ.Adj (T.line.vert a₀) (T.line.vert (a₀ + 1)) := T.line.adj a₀
  have hβ3 : valence Γ (T.line.vert (a₀ + 1)) = 3 := by
    have h1 : valence Γ (T.line.vert a₀) ≠ valence Γ (T.line.vert (a₀ + 1)) :=
      F.alternating _ _ hab
    have := hval (T.line.vert (a₀ + 1))
    omega
  obtain ⟨hLam, -⟩ := fan45_2_lam T F hPi.1 hPi.2 hmax.1 (c := a₀) (Or.inl rfl)
  have hLam' := hLam
  obtain ⟨Q, hQ0, hQ, hLQ, hloc, ⟨g₀, hg₀, hg₀a⟩⟩ := hLam
  set L := Subgroup.normalizer (omega1 T.fixer : Set G) with hL
  set H : Subgroup G := Subgroup.closure ((↑(L ⊓ MulAction.stabilizer G (T.line.vert a₀)) : Set G) ∪
    ↑(L ⊓ MulAction.stabilizer G (T.line.vert (a₀ + 1)))) with hH
  have hHL : H ≤ L := by
    rw [hH, Subgroup.closure_le]
    rintro g (hg | hg)
    · exact hg.1
    · exact hg.1
  have hmemα : ∀ g ∈ L ⊓ MulAction.stabilizer G (T.line.vert a₀), g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inl hg)
  have hmemβ : ∀ g ∈ L ⊓ MulAction.stabilizer G (T.line.vert (a₀ + 1)), g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inr hg)
  have hHα : H ⊓ MulAction.stabilizer G (T.line.vert a₀) =
      L ⊓ MulAction.stabilizer G (T.line.vert a₀) :=
    le_antisymm (fun g hg => ⟨hHL hg.1, hg.2⟩) (fun g hg => ⟨hmemα g hg, hg.2⟩)
  have hHβ : H ⊓ MulAction.stabilizer G (T.line.vert (a₀ + 1)) =
      L ⊓ MulAction.stabilizer G (T.line.vert (a₀ + 1)) :=
    le_antisymm (fun g hg => ⟨hHL hg.1, hg.2⟩) (fun g hg => ⟨hmemβ g hg, hg.2⟩)
  have hτL : T.τ ∈ L := by simpa using T.zpow_mem_normalizer 1
  have hS : SubgraphProp T a₀ b₀ H := by
    refine ⟨hmax.1, ⟨L, hLam', hHL⟩, ?_, ?_, ?_, ?_⟩
    ·
      intro h hh hβh
      by_contra hcon
      push Not at hcon
      have hγ : Γ.Adj (T.line.vert (a₀ + 1)) (h • T.line.vert a₀) := by
        have := (F.adj_smul h _ _).2 hab.symm
        rwa [hβh] at this
      have hα₂adj : Γ.Adj (T.line.vert (a₀ + 1)) (T.line.vert (a₀ + 2)) := by
        have := T.line.adj (a₀ + 1)
        rwa [show a₀ + 1 + 1 = a₀ + 2 by omega] at this
      have hthree : ({T.line.vert a₀, T.line.vert (a₀ + 2), h • T.line.vert a₀} : Set V) =
          Γ.neighborSet (T.line.vert (a₀ + 1)) := by
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ (F.ncard_neighborSet_le _).2
        · rintro x (rfl | rfl | rfl)
          · exact hab.symm
          · exact hα₂adj
          · exact hγ
        · rw [Set.ncard_eq_three.2 ⟨T.line.vert a₀, T.line.vert (a₀ + 2), h • T.line.vert a₀,
            T.line.nb a₀, hcon.1.symm, hcon.2.symm, rfl⟩, ← Nat.card_coe_set_eq]
          exact hβ3.le
      refine fan41_nt F hab hLam' ?_
      intro u w hu hw
      have key : ∀ x, Γ.Adj (T.line.vert (a₀ + 1)) x → ∃ l ∈ L ⊓ MulAction.stabilizer G
          (T.line.vert (a₀ + 1)), l • T.line.vert a₀ = x := by
        intro x hx
        have : x ∈ ({T.line.vert a₀, T.line.vert (a₀ + 2), h • T.line.vert a₀} : Set V) := by
          rw [hthree]
          exact hx
        rcases this with rfl | rfl | rfl
        · exact ⟨1, (L ⊓ _).one_mem, one_smul _ _⟩
        · exact ⟨g₀, hg₀, hg₀a⟩
        · exact ⟨h, ⟨hHL hh, MulAction.mem_stabilizer_iff.2 hβh⟩, rfl⟩
      obtain ⟨l₁, hl₁, rfl⟩ := key u hu
      obtain ⟨l₂, hl₂, rfl⟩ := key w hw
      exact ⟨l₂ * l₁⁻¹, (L ⊓ _).mul_mem hl₂ ((L ⊓ _).inv_mem hl₁), by rw [mul_smul, inv_smul_smul]⟩
    ·
      intro g hg
      refine hmemα g ⟨(IsQuasiTArc.fixer_normal T F (hmax.1.isQuasi T)).2 hg,
        MulAction.mem_stabilizer_iff.2 ((T.mem_subFixer).1 hg a₀ le_rfl hmax.1.1.le)⟩
    ·
      have h1 : g₀⁻¹ * T.τ ∈ L ⊓ MulAction.stabilizer G (T.line.vert a₀) := by
        refine ⟨L.mul_mem (L.inv_mem hg₀.1) hτL, MulAction.mem_stabilizer_iff.2 ?_⟩
        rw [mul_smul, T.trans a₀, inv_smul_eq_iff]
        exact hg₀a.symm
      have := H.mul_mem (hmemβ g₀ hg₀) (hmemα _ h1)
      rwa [mul_inv_cancel_left] at this
    · rw [hHα, hHβ]
  have h4 := fan46_five hS F hPi h5
  have h6 := fan40_lineSingLe h40 (fan44_3 T F h40 hPi.1 hPi.2 hmax)
  omega

end CFSG.Quasithin.Fan86
