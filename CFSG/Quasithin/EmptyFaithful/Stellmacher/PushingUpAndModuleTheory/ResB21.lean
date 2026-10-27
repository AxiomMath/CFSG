module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB20

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem eq_of_card_two_sub {A B C : Subgroup G} (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hC : C ≠ ⊥) (hCA : C ≤ A) (hCB : C ≤ B) : A = B := by
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC
  have hc1' : (c : G) ≠ 1 := fun e => hc1 (Subtype.ext e)
  have key : ∀ {A B : Subgroup G}, Nat.card A = 2 → C ≤ A → C ≤ B → A ≤ B := by
    intro A B hA hCA hCB a ha
    by_cases h1 : a = 1
    · rw [h1]; exact B.one_mem
    · have := eq_of_card_two hA ha (hCA c.2) h1 hc1'
      rw [this]; exact hCB c.2
  exact le_antisymm (key hA hCA hCB) (key hB hCB hCA)

theorem fix_third {μ : Geo H M} {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab μ) {a b c : Geo H M}
    (hc : c ∈ nbrs μ) (hall : ∀ x ∈ nbrs μ, x = a ∨ x = b ∨ x = c) (hca : c ≠ a) (hcb : c ≠ b)
    (hab : g • a = b) (hba : g • b = a) : g • c = c := by
  rcases hall _ (smul_mem_nbrs hg hc) with e | e | e
  · exact absurd (smul_left_cancel g (e.trans hba.symm)) hcb
  · exact absurd (smul_left_cancel g (e.trans hab.symm)) hca
  · exact e

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem conj_V0_le (hA : F53Amalgam H M S) (h : ConfR δ μ U) {V₀ : Subgroup G}
    (hVO : V₀ ≤ OoOf δ) {k : ↥(H ⊔ M)} (hk : (k : G) ∈ stab μ) :
    conjSub (k : G) V₀ ≤ Qv μ := by
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  have := h.Oo_le_Qv_mu_at hA (smul_mem_nbrs hk hδ)
  rw [OoOf_smul] at this
  exact (conjSub_mono (k : G) hVO).trans this

theorem false_of_a4 (hA : F53Amalgam H M S) (h : ConfR δ μ U)
    (h4 : ∀ n ∈ nbrs μ, n ≠ δ → aZ δ n = 4) : False := by
  obtain ⟨fr⟩ := h.exists_frame hA
  obtain ⟨c, hcU, V₀, hc3, hVO, -, -, -, hcyc, hV⟩ := h.rplane hA fr
  have hVZ := h.V0_le_ZU fr hcU hcyc hV hA
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  have hPF : Qv μ ≤ stab δ := by
    have := h.sig.P_le_edge hA
    rw [h.inf_eq] at this
    exact this.trans inf_le_left
  have hM2 := card_comm_P fr hcyc hV hPF
  obtain ⟨n, n', hn, hn', hnδ, hn'δ, hnn', hall⟩ := nbrs_three hA (h.vtype_mu hA) hδ
  obtain ⟨yA, hyA, hyAδ, hAe⟩ := h.exists_edge hA fr hcyc hV h4 hn hnδ
  obtain ⟨yB, hyB, hyBδ, hBe⟩ := h.exists_edge hA fr hcyc hV h4 hn' hn'δ
  obtain ⟨-, hA2⟩ := h.edge_swap hA hVO hVZ hyA hAe
  obtain ⟨-, hB2⟩ := h.edge_swap hA hVO hVZ hyB hBe
  rw [hyAδ] at hA2
  rw [hyBδ] at hB2
  have hyAn' : yA • n' = n' :=
    fix_third hyA hn' (a := δ) (b := n) (fun x hx => by
      rcases hall x hx with e | e | e <;> simp [e]) hn'δ (Ne.symm hnn') hyAδ hA2
  have hyBn : yB • n = n :=
    fix_third hyB hn (a := δ) (b := n') (fun x hx => by
      rcases hall x hx with e | e | e <;> simp [e]) hnδ hnn' hyBδ hB2
  set g : ↥(H ⊔ M) := yA * yB * yA with hg
  have hgμ : (g : G) ∈ stab μ := (stab μ).mul_mem ((stab μ).mul_mem hyA hyB) hyA
  have hgδ : g • δ = δ := by
    rw [hg, mul_smul, mul_smul, hyAδ, hyBn, hA2]
  have hgn : g • n = n' := by
    rw [hg, mul_smul, mul_smul, hA2, hyBδ, hyAn']
  have hgP : (g : G) ∉ Qv μ := fun hmem => hnn' (by
    have := smul_eq_of_mem_stab (g := g) (Qv_le_stab_of_mem_nbrs hA hn hmem)
    rw [hgn] at this; exact this.symm)
  have hmQ : ∀ k : ↥(H ⊔ M), (k : G) ∈ stab μ →
      ⁅Qv μ, conjSub (k : G) V₀⁆ = conjSub (k : G) ⁅Qv μ, V₀⁆ := by
    intro k hk
    rw [← conjSub_commutator, conjSub_Qv_mu hk]
  have hcard : ∀ k : ↥(H ⊔ M), (k : G) ∈ stab μ → Nat.card (⁅Qv μ, conjSub (k : G) V₀⁆ : Subgroup G) = 2 := by
    intro k hk
    rw [hmQ k hk]
    exact (Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj (k : G)))).trans hM2
  have hMeq : ∀ k k' : ↥(H ⊔ M), (k : G) ∈ stab μ → (k' : G) ∈ stab μ →
      ⁅conjSub (k : G) V₀, conjSub (k' : G) V₀⁆ ≠ ⊥ →
      ⁅Qv μ, conjSub (k : G) V₀⁆ = ⁅Qv μ, conjSub (k' : G) V₀⁆ := by
    intro k k' hk hk' hed
    refine eq_of_card_two_sub (hcard k hk) (hcard k' hk') hed ?_ ?_
    · have := Subgroup.commutator_mono (le_refl (conjSub (k : G) V₀)) (h.conj_V0_le hA hVO hk')
      rw [Subgroup.commutator_comm (conjSub (k : G) V₀) (Qv μ)] at this
      exact this
    · rw [Subgroup.commutator_comm (conjSub (k : G) V₀) (conjSub (k' : G) V₀)]
      have := Subgroup.commutator_mono (le_refl (conjSub (k' : G) V₀)) (h.conj_V0_le hA hVO hk)
      rw [Subgroup.commutator_comm (conjSub (k' : G) V₀) (Qv μ)] at this
      exact this
  have hedge : ∀ k x : ↥(H ⊔ M), ⁅V₀, conjSub (x : G) V₀⁆ ≠ ⊥ →
      ⁅conjSub (k : G) V₀, conjSub ((k * x : ↥(H ⊔ M)) : G) V₀⁆ ≠ ⊥ := by
    intro k x hx hbot
    apply hx
    have e : conjSub ((k * x : ↥(H ⊔ M)) : G) V₀ = conjSub (k : G) (conjSub (x : G) V₀) :=
      conjSub_mul (k : G) (x : G) V₀
    rw [e, conjSub_commutator, conjSub_eq_bot_iff] at hbot
    exact hbot
  have E1 : ⁅conjSub ((1 : ↥(H ⊔ M)) : G) V₀, conjSub (yA : G) V₀⁆ ≠ ⊥ := by
    simpa [conjSub_one] using hAe
  have E2 := hedge yA yB hBe
  have E3 := hedge (yA * yB) yA hAe
  have m1 := hMeq 1 yA (stab μ).one_mem hyA E1
  have m2 := hMeq yA (yA * yB) hyA ((stab μ).mul_mem hyA hyB) E2
  have m3 := hMeq (yA * yB) (yA * yB * yA) ((stab μ).mul_mem hyA hyB) hgμ E3
  have hfin : conjSub (g : G) ⁅Qv μ, V₀⁆ = ⁅Qv μ, V₀⁆ := by
    rw [← hmQ g hgμ]
    have : ⁅Qv μ, conjSub ((1 : ↥(H ⊔ M)) : G) V₀⁆ = ⁅Qv μ, V₀⁆ := by simp [conjSub_one]
    rw [this] at m1
    exact (m1.trans (m2.trans m3)).symm
  exact h.conj_comm_P_ne fr hcyc hV hPF (h.sig.le_stab hcU |> fun _ =>
    (mem_stab_of_smul_eq hgδ)) hgμ hgP hfin

end ConfR

end CFSG.Quasithin.F53
