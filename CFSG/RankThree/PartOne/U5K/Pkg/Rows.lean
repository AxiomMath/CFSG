module

public import CFSG.RankThree.PartOne.U5K.Pkg.Fixed

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem c_mem_fixedIn (h : Sec12Hyp G p A c L E) :
    c ∈ fixedIn E (torusImage E L : Set (MulAut E)) :=
  ⟨h.A_le_E h.c_mem, fun _ hx => torusImage_fixes_c h hx⟩

theorem fixedIn_reflectionGroup_eq_bot (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hX : reflectionGroup p E ≠ ⊥) (hL : torusImage E L ≠ ⊥) :
    fixedIn E (reflectionGroup p E : Set (MulAut E)) = ⊥ := by
  have hp := h.prime
  set C := fixedIn E (reflectionGroup p E : Set (MulAut E)) with hCdef
  by_contra hC
  have hLX := torusImage_le_reflectionGroup hF
  have hinv : torusInvariant E L C := by
    intro w hw b hb
    obtain ⟨hbE, hbf⟩ := hb
    have hwN : w ∈ Subgroup.normalizer (E : Set G) := hw.2
    have hmem : conjAut E w hwN ∈ reflectionGroup p E :=
      hLX (conjAut_mem_torusImage hwN hw.1)
    have h2 := congrArg (fun z : E => (z : G)) (hbf _ hmem)
    simp only [coe_conjAut_apply hwN] at h2
    show w * b * w⁻¹ ∈ C
    rw [h2]
    exact ⟨hbE, hbf⟩
  by_cases hCE : C = E
  · exact hX ((Subgroup.eq_bot_iff_forall _).2 (eq_one_of_fixedIn_eq hCE))
  rcases hF.four.1 C (fixedIn_le _) hinv hC hCE with hCc | hC0
  · refine hF.five (torusNormalizer_le_of_stable fun w hw b hb => ?_)
    rw [← hCc] at hb ⊢
    exact fixedIn_stable hp hw hb
  · rcases hF.four.2 with ⟨hsup, -⟩ | ⟨-, hB0⟩
    · have hLfix : fixedIn E (torusImage E L : Set (MulAut E)) = E := by
        refine le_antisymm (fixedIn_le _) (hsup.le.trans ?_)
        rw [← hC0]
        refine sup_le (Subgroup.zpowers_le.2 (c_mem_fixedIn h)) ?_
        exact fixedIn_anti (fun x hx => hLX hx)
      exact hL ((Subgroup.eq_bot_iff_forall _).2 (eq_one_of_fixedIn_eq hLfix))
    · exact hCE (hC0.trans hB0)

theorem card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]; decide

theorem rows (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    Nat.card (torusImage E L) = 24 ∧ RowModel p L 9 ∧
      (E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ ∧
        Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥) := by
  have h := h15.h12
  obtain ⟨-, r, hr1, hr12, hmodel, hweyl, hr8, hr9⟩ := hF.three
  obtain ⟨f₀, -, -, -, ⟨ψ⟩, hcardE, hEA, -⟩ := hout
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hr8 (by omega))
  have hLX := torusImage_le_reflectionGroup hF
  have hX120 : Nat.card (reflectionGroup p E) = 120 := by
    rw [Nat.card_congr ψ.toEquiv, card_perm_five]
  have hdvd : Nat.card (torusImage E L) ∣ 120 := hX120 ▸ Subgroup.card_dvd_of_le hLX
  have hXne : reflectionGroup p E ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hX120
    omega
  have hc1 : c ≠ 1 := h.c_ne_one
  have hcard5 : ∀ (hw : Nonempty (↥(torusImage E L) ≃* Equiv.Perm (Fin 5))),
      Nat.card (torusImage E L) = 120 := fun ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, card_perm_five]
  have hcard4 : ∀ (hw : Nonempty (↥(torusImage E L) ≃* Equiv.Perm (Fin 4))),
      Nat.card (torusImage E L) = 24 := fun ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]; decide
  have hX5 : ∀ (hw : Nonempty (↥(torusImage E L) ≃* Equiv.Perm (Fin 5))), False := by
    intro hw
    have h120 := hcard5 hw
    have hLX' : torusImage E L = reflectionGroup p E :=
      Subgroup.eq_of_le_of_card_ge hLX (by rw [hX120, h120])
    have hLne : torusImage E L ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at h120
      omega
    have hbot := fixedIn_reflectionGroup_eq_bot h hF hXne hLne
    have hc : c ∈ fixedIn E (reflectionGroup p E : Set (MulAut E)) := by
      have := c_mem_fixedIn h
      rwa [hLX'] at this
    rw [hbot] at hc
    exact hc1 (Subgroup.mem_bot.1 hc)
  interval_cases r
  · have h24 := hcard4 hweyl
    refine ⟨h24, hmodel, ?_⟩
    rcases hF.four.2 with h4 | ⟨⟨-, hw11⟩, -⟩
    · exact h4
    · exfalso
      have := hcard5 hw11
      omega
  · exfalso
    obtain ⟨e⟩ := hweyl
    have h48 : Nat.card (torusImage E L) = 48 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
      have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      rw [this]; decide
    rw [h48] at hdvd
    exact absurd hdvd (by decide)
  · exact (hX5 hweyl).elim
  · exact (hX5 hweyl).elim

end CFSG.RankThree.PartOne.U5K.Pkg
