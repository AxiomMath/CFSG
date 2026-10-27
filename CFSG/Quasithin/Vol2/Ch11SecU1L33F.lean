module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33B
public import CFSG.Quasithin.Vol2.Ch11SecU1L33E
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.LieType.BorelTits
  CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

variable {G : Type} [Group G] {L : Subgroup G}

theorem le_normalizer_of_conj {K Q : Subgroup G} (h : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) :
    K ≤ Subgroup.normalizer (Q : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨h k hk q, fun hq => ?_⟩
  have := h k⁻¹ (K.inv_mem hk) _ hq
  simpa [mul_assoc] using this

namespace Model

variable (M : Model L)

@[expose] noncomputable def subOf (l : List Code) {n : Nat} (h : SubFacts l n) : Subgroup G :=
  M.sub l h.1 h.2.1 h.2.2.1 (fun a ha => mem_nL.mpr (h.2.2.2.1 a ha))

theorem mem_subOf {l : List Code} {n : Nat} {h : SubFacts l n} {g : G} :
    g ∈ M.subOf l h ↔ M.code g ∈ l := Iff.rfl

theorem card_subOf {l : List Code} {n : Nat} (h : SubFacts l n) : Nat.card (M.subOf l h) = n := by
  rw [subOf, M.card_sub h.2.2.2.2.1, h.2.2.2.2.2]

theorem exists_mem {l : List Code} {n : Nat} (h : SubFacts l n) {c : Code} (hc : c ∈ l) :
    ∃ g, g ∈ M.subOf l h ∧ M.code g = c := by
  obtain ⟨g, hg⟩ := M.exists_code (mem_nL.mpr (h.2.2.2.1 c hc))
  exact ⟨g, by rw [mem_subOf, hg]; exact hc, hg⟩

theorem commute_of_code {g h : G} (e : cmul (M.code g) (M.code h) = cmul (M.code h) (M.code g)) :
    g * h = h * g :=
  (M.commute_iff g h).mpr e

noncomputable abbrev T0 : Subgroup G := M.subOf tl tl_facts

noncomputable abbrev K0 : Subgroup G := M.subOf k0l k0l_facts

noncomputable abbrev Q0 : Subgroup G := M.subOf q0l q0l_facts

noncomputable abbrev R0 : Subgroup G := M.subOf r0l r0l_facts

noncomputable abbrev TK0 : Subgroup G := M.subOf tk0l tk0l_facts

include M in
theorem card_G : Nat.card G = 11232 := by
  have hL : Nat.card L = 5616 := by
    rw [← card_S3]
    have hr : M.f.range = L := by
      ext g
      exact ⟨fun ⟨x, hx⟩ => (M.mem_iff g).mpr ⟨x, hx⟩, fun h => (M.mem_iff g).mp h⟩
    rw [← hr]
    exact (Nat.card_congr (MonoidHom.ofInjective M.f_inj).toEquiv).symm
  have hi : L.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨M.t, fun b => ?_⟩
    rw [M.mem_iff_code, M.mem_iff_code, code_mul, code_t]
    simp only [cmul, cdelta]
    cases (M.code b).2 <;> decide
  rw [← L.card_mul_index, hL, hi]

theorem isSylow_T0 : IsSylowIn 2 M.T0 ⊤ := by
  have hc : Nat.card M.T0 = 32 := M.card_subOf tl_facts
  refine ⟨le_top, IsPGroup.of_card (n := 5) (by rw [hc]; norm_num), ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := M.T0.card_mul_index
  rw [hc, M.card_G] at h
  have h' : M.T0.index = 351 := by omega
  rw [h']
  decide

theorem inf_T0_K0 : M.T0 ⊓ M.K0 = M.TK0 := by
  ext g
  rw [Subgroup.mem_inf, mem_subOf, mem_subOf, mem_subOf]
  exact ⟨fun h => tk0l_check.1 _ h.1 h.2, fun h => tk0l_check.2 _ h⟩

theorem TK0_le_K0 : M.TK0 ≤ M.K0 := fun _ hg => (tk0l_check.2 _ hg).2

theorem isSylow_TK0 : IsSylowIn 2 M.TK0 M.K0 := by
  have hc : Nat.card M.TK0 = 16 := M.card_subOf tk0l_facts
  refine ⟨M.TK0_le_K0, IsPGroup.of_card (n := 4) (by rw [hc]; norm_num), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := M.TK0) (K := M.K0)
  rw [inf_eq_left.mpr M.TK0_le_K0, hc, M.card_subOf k0l_facts] at h
  have h' : M.TK0.relIndex M.K0 = 3 := by omega
  rw [h']
  decide

theorem conj_mem_of_check {l₁ l₂ : List Code} {n₁ n₂ : Nat} (h₁ : SubFacts l₁ n₁)
    (h₂ : SubFacts l₂ n₂) (hc : ∀ k ∈ l₁, ∀ q ∈ l₂, ∃ q' ∈ l₂, cmul k q = cmul q' k) :
    ∀ k ∈ M.subOf l₁ h₁, ∀ q ∈ M.subOf l₂ h₂, k * q * k⁻¹ ∈ M.subOf l₂ h₂ := by
  intro k hk q hq
  obtain ⟨q', hq', he⟩ := hc _ hk _ hq
  obtain ⟨g, hg, hgc⟩ := M.exists_mem h₂ hq'
  have h1 : k * q = g * k := M.code_inj (by rw [code_mul, code_mul, hgc]; exact he)
  rw [h1, mul_inv_cancel_right]
  exact hg

theorem K0_le_normalizer_Q0 : M.K0 ≤ Subgroup.normalizer (M.Q0 : Set G) :=
  le_normalizer_of_conj (M.conj_mem_of_check k0l_facts q0l_facts normal_check.1)

theorem K0_le_normalizer_R0 : M.K0 ≤ Subgroup.normalizer (M.R0 : Set G) :=
  le_normalizer_of_conj (M.conj_mem_of_check k0l_facts r0l_facts normal_check.2)

theorem Q0_le_K0 : M.Q0 ≤ M.K0 := fun _ hg => (tk0l_check.2 _ (sub_check.1 _ hg).1).2

theorem code_pow16 (g : G) : M.code (g ^ 16) = cpow16 (M.code g) := by
  have h : g ^ 16 = (((g * g) * (g * g)) * ((g * g) * (g * g))) *
      (((g * g) * (g * g)) * ((g * g) * (g * g))) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h]
  simp only [code_mul]
  rfl

variable [Finite G]

theorem pcore_K0 : pCoreOf 2 M.K0 = M.Q0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hP : pCoreOf 2 M.K0 ≤ M.TK0 := M.isSylow_TK0.le_of_normal (pCoreOf_le 2 _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
        (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    intro w hw
    by_contra hwQ
    obtain ⟨e, -, he1, hc, hy, hcy, hpow⟩ := pcore_check _ (hP hw) hwQ
    obtain ⟨c, hcK, hcc⟩ := M.exists_mem k0l_facts hc
    obtain ⟨y, -, hyc⟩ := M.exists_mem k0l_facts hy
    have h1 : c * w = y * c := M.code_inj (by rw [code_mul, code_mul, hcc, hyc]; exact hcy)
    have hyP : y ∈ pCoreOf 2 M.K0 := by
      have h2 : y = c * w * c⁻¹ := by rw [h1, mul_inv_cancel_right]
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.K0 hcK) w).mp hw
    have hwy := (pCoreOf 2 M.K0).mul_mem hw hyP
    have h16 : (w * y) ^ 16 = 1 := by
      have h3 := (Subgroup.orderOf_dvd_natCard _ hwy).trans (Subgroup.card_dvd_of_le hP)
      rw [M.card_subOf tk0l_facts] at h3
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    have h4 := M.code_pow16 (w * y)
    rw [h16, code_one, code_mul, hyc] at h4
    exact hpow h4.symm
  · refine le_pCoreOf 2 M.Q0_le_K0 ((Subgroup.normal_subgroupOf_iff_le_normalizer M.Q0_le_K0).mpr
      M.K0_le_normalizer_Q0) (IsPGroup.of_card (n := 3) ?_)
    rw [M.card_subOf q0l_facts]
    norm_num

end Model

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
